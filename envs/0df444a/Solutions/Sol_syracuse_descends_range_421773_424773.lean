-- Prove2me | solution 1 for syracuse_descends_range_421773_424773
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:52.710506+00:00
-- url     : https://prove2.me/submissions/871f7981-7be2-45e1-8ebe-308d5cc2cb41

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


theorem B1204229 : Blo 421773 1204229 := bbase (se 4 (by rfl) ⟨112896, by rfl⟩ : syracuseStep 1204229 = 225793) (by norm_num)
theorem B475141 : Blo 421773 475141 := bbase (se 4 (by rfl) ⟨44544, by rfl⟩ : syracuseStep 475141 = 89089) (by norm_num)
theorem B1605653 : Blo 421773 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B950309 : Blo 421773 950309 := bbase (se 4 (by rfl) ⟨89091, by rfl⟩ : syracuseStep 950309 = 178183) (by norm_num)
theorem B1073189 : Blo 421773 1073189 := bbase (se 4 (by rfl) ⟨100611, by rfl⟩ : syracuseStep 1073189 = 201223) (by norm_num)
theorem B475177 : Blo 421773 475177 := bbase (se 2 (by rfl) ⟨178191, by rfl⟩ : syracuseStep 475177 = 356383) (by norm_num)
theorem B3293237 : Blo 421773 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B901181 : Blo 421773 901181 := bbase (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) (by norm_num)
theorem B434245 : Blo 421773 434245 := bbase (se 4 (by rfl) ⟨40710, by rfl⟩ : syracuseStep 434245 = 81421) (by norm_num)
theorem B475213 : Blo 421773 475213 := bbase (se 3 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 475213 = 178205) (by norm_num)
theorem B950381 : Blo 421773 950381 := bbase (se 3 (by rfl) ⟨178196, by rfl⟩ : syracuseStep 950381 = 356393) (by norm_num)
theorem B712813 : Blo 421773 712813 := bbase (se 3 (by rfl) ⟨133652, by rfl⟩ : syracuseStep 712813 = 267305) (by norm_num)
theorem B475249 : Blo 421773 475249 := bbase (se 2 (by rfl) ⟨178218, by rfl⟩ : syracuseStep 475249 = 356437) (by norm_num)
theorem B450689 : Blo 421773 450689 := bbase (se 2 (by rfl) ⟨169008, by rfl⟩ : syracuseStep 450689 = 338017) (by norm_num)
theorem B475285 : Blo 421773 475285 := bbase (se 6 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 475285 = 22279) (by norm_num)
theorem B950453 : Blo 421773 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B475321 : Blo 421773 475321 := bbase (se 2 (by rfl) ⟨178245, by rfl⟩ : syracuseStep 475321 = 356491) (by norm_num)
theorem B712901 : Blo 421773 712901 := bbase (se 4 (by rfl) ⟨66834, by rfl⟩ : syracuseStep 712901 = 133669) (by norm_num)
theorem B475357 : Blo 421773 475357 := bbase (se 3 (by rfl) ⟨89129, by rfl⟩ : syracuseStep 475357 = 178259) (by norm_num)
theorem B1425653 : Blo 421773 1425653 := bbase (se 5 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 1425653 = 133655) (by norm_num)
theorem B950525 : Blo 421773 950525 := bbase (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) (by norm_num)
theorem B475393 : Blo 421773 475393 := bbase (se 2 (by rfl) ⟨178272, by rfl⟩ : syracuseStep 475393 = 356545) (by norm_num)
theorem B1802533 : Blo 421773 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B475429 : Blo 421773 475429 := bbase (se 4 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 475429 = 89143) (by norm_num)
theorem B950597 : Blo 421773 950597 := bbase (se 4 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 950597 = 178237) (by norm_num)
theorem B713029 : Blo 421773 713029 := bbase (se 4 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 713029 = 133693) (by norm_num)
theorem B475465 : Blo 421773 475465 := bbase (se 2 (by rfl) ⟨178299, by rfl⟩ : syracuseStep 475465 = 356599) (by norm_num)
theorem B2146661 : Blo 421773 2146661 := bbase (se 4 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 2146661 = 402499) (by norm_num)
theorem B475501 : Blo 421773 475501 := bbase (se 3 (by rfl) ⟨89156, by rfl⟩ : syracuseStep 475501 = 178313) (by norm_num)
theorem B1073533 : Blo 421773 1073533 := bbase (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) (by norm_num)
theorem B1286533 : Blo 421773 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B950669 : Blo 421773 950669 := bbase (se 3 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 950669 = 356501) (by norm_num)
theorem B475537 : Blo 421773 475537 := bbase (se 2 (by rfl) ⟨178326, by rfl⟩ : syracuseStep 475537 = 356653) (by norm_num)
theorem B713117 : Blo 421773 713117 := bbase (se 3 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 713117 = 267419) (by norm_num)
theorem B475573 : Blo 421773 475573 := bbase (se 5 (by rfl) ⟨22292, by rfl⟩ : syracuseStep 475573 = 44585) (by norm_num)
theorem B688589 : Blo 421773 688589 := bbase (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) (by norm_num)
theorem B950741 : Blo 421773 950741 := bbase (se 7 (by rfl) ⟨11141, by rfl⟩ : syracuseStep 950741 = 22283) (by norm_num)
theorem B475609 : Blo 421773 475609 := bbase (se 2 (by rfl) ⟨178353, by rfl⟩ : syracuseStep 475609 = 356707) (by norm_num)
theorem B1073645 : Blo 421773 1073645 := bbase (se 3 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 1073645 = 402617) (by norm_num)
theorem B475645 : Blo 421773 475645 := bbase (se 3 (by rfl) ⟨89183, by rfl⟩ : syracuseStep 475645 = 178367) (by norm_num)
theorem B950813 : Blo 421773 950813 := bbase (se 3 (by rfl) ⟨178277, by rfl⟩ : syracuseStep 950813 = 356555) (by norm_num)
theorem B713245 : Blo 421773 713245 := bbase (se 3 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 713245 = 267467) (by norm_num)
theorem B475681 : Blo 421773 475681 := bbase (se 2 (by rfl) ⟨178380, by rfl⟩ : syracuseStep 475681 = 356761) (by norm_num)
theorem B475717 : Blo 421773 475717 := bbase (se 4 (by rfl) ⟨44598, by rfl⟩ : syracuseStep 475717 = 89197) (by norm_num)
theorem B1016405 : Blo 421773 1016405 := bbase (se 8 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 1016405 = 11911) (by norm_num)
theorem B950885 : Blo 421773 950885 := bbase (se 4 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 950885 = 178291) (by norm_num)
theorem B475753 : Blo 421773 475753 := bbase (se 2 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 475753 = 356815) (by norm_num)
theorem B508529 : Blo 421773 508529 := bbase (se 2 (by rfl) ⟨190698, by rfl⟩ : syracuseStep 508529 = 381397) (by norm_num)
theorem B713333 : Blo 421773 713333 := bbase (se 5 (by rfl) ⟨33437, by rfl⟩ : syracuseStep 713333 = 66875) (by norm_num)
theorem B574085 : Blo 421773 574085 := bbase (se 4 (by rfl) ⟨53820, by rfl⟩ : syracuseStep 574085 = 107641) (by norm_num)
theorem B475789 : Blo 421773 475789 := bbase (se 3 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 475789 = 178421) (by norm_num)
theorem B1426085 : Blo 421773 1426085 := bbase (se 4 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 1426085 = 267391) (by norm_num)
theorem B1204901 : Blo 421773 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B950957 : Blo 421773 950957 := bbase (se 3 (by rfl) ⟨178304, by rfl⟩ : syracuseStep 950957 = 356609) (by norm_num)
theorem B1073837 : Blo 421773 1073837 := bbase (se 3 (by rfl) ⟨201344, by rfl⟩ : syracuseStep 1073837 = 402689) (by norm_num)
theorem B475825 : Blo 421773 475825 := bbase (se 2 (by rfl) ⟨178434, by rfl⟩ : syracuseStep 475825 = 356869) (by norm_num)
theorem B4063925 : Blo 421773 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B803533 : Blo 421773 803533 := bbase (se 3 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 803533 = 301325) (by norm_num)
theorem B475861 : Blo 421773 475861 := bbase (se 7 (by rfl) ⟨5576, by rfl⟩ : syracuseStep 475861 = 11153) (by norm_num)
theorem B951029 : Blo 421773 951029 := bbase (se 5 (by rfl) ⟨44579, by rfl⟩ : syracuseStep 951029 = 89159) (by norm_num)
theorem B713461 : Blo 421773 713461 := bbase (se 5 (by rfl) ⟨33443, by rfl⟩ : syracuseStep 713461 = 66887) (by norm_num)
theorem B475897 : Blo 421773 475897 := bbase (se 2 (by rfl) ⟨178461, by rfl⟩ : syracuseStep 475897 = 356923) (by norm_num)
theorem B828157 : Blo 421773 828157 := bbase (se 3 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 828157 = 310559) (by norm_num)
theorem B2138885 : Blo 421773 2138885 := bbase (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) (by norm_num)
theorem B3605269 : Blo 421773 3605269 := bbase (se 6 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 3605269 = 168997) (by norm_num)
theorem B1016597 : Blo 421773 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B475933 : Blo 421773 475933 := bbase (se 3 (by rfl) ⟨89237, by rfl⟩ : syracuseStep 475933 = 178475) (by norm_num)
theorem B901925 : Blo 421773 901925 := bbase (se 4 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 901925 = 169111) (by norm_num)
theorem B508717 : Blo 421773 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B951101 : Blo 421773 951101 := bbase (se 3 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 951101 = 356663) (by norm_num)
theorem B475969 : Blo 421773 475969 := bbase (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) (by norm_num)
theorem B713549 : Blo 421773 713549 := bbase (se 3 (by rfl) ⟨133790, by rfl⟩ : syracuseStep 713549 = 267581) (by norm_num)
theorem B803677 : Blo 421773 803677 := bbase (se 3 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 803677 = 301379) (by norm_num)
theorem B476005 : Blo 421773 476005 := bbase (se 4 (by rfl) ⟨44625, by rfl⟩ : syracuseStep 476005 = 89251) (by norm_num)
theorem B451441 : Blo 421773 451441 := bbase (se 2 (by rfl) ⟨169290, by rfl⟩ : syracuseStep 451441 = 338581) (by norm_num)
theorem B2417525 : Blo 421773 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B951173 : Blo 421773 951173 := bbase (se 4 (by rfl) ⟨89172, by rfl⟩ : syracuseStep 951173 = 178345) (by norm_num)
theorem B476041 : Blo 421773 476041 := bbase (se 2 (by rfl) ⟨178515, by rfl⟩ : syracuseStep 476041 = 357031) (by norm_num)
theorem B476077 : Blo 421773 476077 := bbase (se 3 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 476077 = 178529) (by norm_num)
theorem B451513 : Blo 421773 451513 := bbase (se 2 (by rfl) ⟨169317, by rfl⟩ : syracuseStep 451513 = 338635) (by norm_num)
theorem B951245 : Blo 421773 951245 := bbase (se 3 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 951245 = 356717) (by norm_num)
theorem B713677 : Blo 421773 713677 := bbase (se 3 (by rfl) ⟨133814, by rfl⟩ : syracuseStep 713677 = 267629) (by norm_num)
theorem B476113 : Blo 421773 476113 := bbase (se 2 (by rfl) ⟨178542, by rfl⟩ : syracuseStep 476113 = 357085) (by norm_num)
theorem B1713109 : Blo 421773 1713109 := bbase (se 7 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 1713109 = 40151) (by norm_num)
theorem B2040805 : Blo 421773 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B476149 : Blo 421773 476149 := bbase (se 5 (by rfl) ⟨22319, by rfl⟩ : syracuseStep 476149 = 44639) (by norm_num)
theorem B803837 : Blo 421773 803837 := bbase (se 3 (by rfl) ⟨150719, by rfl⟩ : syracuseStep 803837 = 301439) (by norm_num)
theorem B508933 : Blo 421773 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B1074181 : Blo 421773 1074181 := bbase (se 4 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 1074181 = 201409) (by norm_num)
theorem B951317 : Blo 421773 951317 := bbase (se 6 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 951317 = 44593) (by norm_num)
theorem B476185 : Blo 421773 476185 := bbase (se 2 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 476185 = 357139) (by norm_num)
theorem B713765 : Blo 421773 713765 := bbase (se 4 (by rfl) ⟨66915, by rfl⟩ : syracuseStep 713765 = 133831) (by norm_num)
theorem B476221 : Blo 421773 476221 := bbase (se 3 (by rfl) ⟨89291, by rfl⟩ : syracuseStep 476221 = 178583) (by norm_num)
theorem B1426517 : Blo 421773 1426517 := bbase (se 8 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 1426517 = 16717) (by norm_num)
theorem B951389 : Blo 421773 951389 := bbase (se 3 (by rfl) ⟨178385, by rfl⟩ : syracuseStep 951389 = 356771) (by norm_num)
theorem B476257 : Blo 421773 476257 := bbase (se 2 (by rfl) ⟨178596, by rfl⟩ : syracuseStep 476257 = 357193) (by norm_num)
theorem B517217 : Blo 421773 517217 := bbase (se 2 (by rfl) ⟨193956, by rfl⟩ : syracuseStep 517217 = 387913) (by norm_num)
theorem B451693 : Blo 421773 451693 := bbase (se 3 (by rfl) ⟨84692, by rfl⟩ : syracuseStep 451693 = 169385) (by norm_num)
theorem B1074293 : Blo 421773 1074293 := bbase (se 5 (by rfl) ⟨50357, by rfl⟩ : syracuseStep 1074293 = 100715) (by norm_num)
theorem B476293 : Blo 421773 476293 := bbase (se 4 (by rfl) ⟨44652, by rfl⟩ : syracuseStep 476293 = 89305) (by norm_num)
theorem B803981 : Blo 421773 803981 := bbase (se 3 (by rfl) ⟨150746, by rfl⟩ : syracuseStep 803981 = 301493) (by norm_num)
theorem B951461 : Blo 421773 951461 := bbase (se 4 (by rfl) ⟨89199, by rfl⟩ : syracuseStep 951461 = 178399) (by norm_num)
theorem B713893 : Blo 421773 713893 := bbase (se 4 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 713893 = 133855) (by norm_num)
theorem B476329 : Blo 421773 476329 := bbase (se 2 (by rfl) ⟨178623, by rfl⟩ : syracuseStep 476329 = 357247) (by norm_num)
theorem B1606837 : Blo 421773 1606837 := bbase (se 5 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 1606837 = 150641) (by norm_num)
theorem B476365 : Blo 421773 476365 := bbase (se 3 (by rfl) ⟨89318, by rfl⟩ : syracuseStep 476365 = 178637) (by norm_num)
theorem B4809941 : Blo 421773 4809941 := bbase (se 7 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 4809941 = 112733) (by norm_num)
theorem B2286805 : Blo 421773 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B951533 : Blo 421773 951533 := bbase (se 3 (by rfl) ⟨178412, by rfl⟩ : syracuseStep 951533 = 356825) (by norm_num)
theorem B476401 : Blo 421773 476401 := bbase (se 2 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 476401 = 357301) (by norm_num)
theorem B2032885 : Blo 421773 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B713981 : Blo 421773 713981 := bbase (se 3 (by rfl) ⟨133871, by rfl⟩ : syracuseStep 713981 = 267743) (by norm_num)
theorem B722197 : Blo 421773 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B1525013 : Blo 421773 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B476437 : Blo 421773 476437 := bbase (se 6 (by rfl) ⟨11166, by rfl⟩ : syracuseStep 476437 = 22333) (by norm_num)
theorem B509221 : Blo 421773 509221 := bbase (se 4 (by rfl) ⟨47739, by rfl⟩ : syracuseStep 509221 = 95479) (by norm_num)
theorem B951605 : Blo 421773 951605 := bbase (se 5 (by rfl) ⟨44606, by rfl⟩ : syracuseStep 951605 = 89213) (by norm_num)
theorem B1074485 : Blo 421773 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B476473 : Blo 421773 476473 := bbase (se 2 (by rfl) ⟨178677, by rfl⟩ : syracuseStep 476473 = 357355) (by norm_num)
theorem B476509 : Blo 421773 476509 := bbase (se 3 (by rfl) ⟨89345, by rfl⟩ : syracuseStep 476509 = 178691) (by norm_num)
theorem B533881 : Blo 421773 533881 := bbase (se 2 (by rfl) ⟨200205, by rfl⟩ : syracuseStep 533881 = 400411) (by norm_num)
theorem B951677 : Blo 421773 951677 := bbase (se 3 (by rfl) ⟨178439, by rfl⟩ : syracuseStep 951677 = 356879) (by norm_num)
theorem B714109 : Blo 421773 714109 := bbase (se 3 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 714109 = 267791) (by norm_num)
theorem B476545 : Blo 421773 476545 := bbase (se 2 (by rfl) ⟨178704, by rfl⟩ : syracuseStep 476545 = 357409) (by norm_num)
theorem B476581 : Blo 421773 476581 := bbase (se 4 (by rfl) ⟨44679, by rfl⟩ : syracuseStep 476581 = 89359) (by norm_num)
theorem B804269 : Blo 421773 804269 := bbase (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) (by norm_num)
theorem B1140149 : Blo 421773 1140149 := bbase (se 5 (by rfl) ⟨53444, by rfl⟩ : syracuseStep 1140149 = 106889) (by norm_num)
theorem B951749 : Blo 421773 951749 := bbase (se 4 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 951749 = 178453) (by norm_num)
theorem B476617 : Blo 421773 476617 := bbase (se 2 (by rfl) ⟨178731, by rfl⟩ : syracuseStep 476617 = 357463) (by norm_num)
theorem B714197 : Blo 421773 714197 := bbase (se 7 (by rfl) ⟨8369, by rfl⟩ : syracuseStep 714197 = 16739) (by norm_num)
theorem B1926629 : Blo 421773 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B1607141 : Blo 421773 1607141 := bbase (se 4 (by rfl) ⟨150669, by rfl⟩ : syracuseStep 1607141 = 301339) (by norm_num)
theorem B476653 : Blo 421773 476653 := bbase (se 3 (by rfl) ⟨89372, by rfl⟩ : syracuseStep 476653 = 178745) (by norm_num)
theorem B1934837 : Blo 421773 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B1426949 : Blo 421773 1426949 := bbase (se 4 (by rfl) ⟨133776, by rfl⟩ : syracuseStep 1426949 = 267553) (by norm_num)
theorem B951821 : Blo 421773 951821 := bbase (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) (by norm_num)
theorem B476689 : Blo 421773 476689 := bbase (se 2 (by rfl) ⟨178758, by rfl⟩ : syracuseStep 476689 = 357517) (by norm_num)
theorem B902677 : Blo 421773 902677 := bbase (se 6 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 902677 = 42313) (by norm_num)
theorem B5416469 : Blo 421773 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B1017365 : Blo 421773 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B534053 : Blo 421773 534053 := bbase (se 4 (by rfl) ⟨50067, by rfl⟩ : syracuseStep 534053 = 100135) (by norm_num)
theorem B452137 : Blo 421773 452137 := bbase (se 2 (by rfl) ⟨169551, by rfl⟩ : syracuseStep 452137 = 339103) (by norm_num)
theorem B1525301 : Blo 421773 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B476725 : Blo 421773 476725 := bbase (se 5 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 476725 = 44693) (by norm_num)
theorem B804421 : Blo 421773 804421 := bbase (se 4 (by rfl) ⟨75414, by rfl⟩ : syracuseStep 804421 = 150829) (by norm_num)
theorem B951893 : Blo 421773 951893 := bbase (se 8 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 951893 = 11155) (by norm_num)
theorem B714325 : Blo 421773 714325 := bbase (se 8 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 714325 = 8371) (by norm_num)
theorem B476761 : Blo 421773 476761 := bbase (se 2 (by rfl) ⟨178785, by rfl⟩ : syracuseStep 476761 = 357571) (by norm_num)
theorem B534109 : Blo 421773 534109 := bbase (se 3 (by rfl) ⟨100145, by rfl⟩ : syracuseStep 534109 = 200291) (by norm_num)
theorem B542317 : Blo 421773 542317 := bbase (se 3 (by rfl) ⟨101684, by rfl⟩ : syracuseStep 542317 = 203369) (by norm_num)
theorem B2147957 : Blo 421773 2147957 := bbase (se 5 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 2147957 = 201371) (by norm_num)
theorem B476797 : Blo 421773 476797 := bbase (se 3 (by rfl) ⟨89399, by rfl⟩ : syracuseStep 476797 = 178799) (by norm_num)
theorem B1074829 : Blo 421773 1074829 := bbase (se 3 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 1074829 = 403061) (by norm_num)
theorem B951965 : Blo 421773 951965 := bbase (se 3 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 951965 = 356987) (by norm_num)
theorem B476833 : Blo 421773 476833 := bbase (se 2 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 476833 = 357625) (by norm_num)
theorem B902821 : Blo 421773 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B452261 : Blo 421773 452261 := bbase (se 4 (by rfl) ⟨42399, by rfl⟩ : syracuseStep 452261 = 84799) (by norm_num)
theorem B714413 : Blo 421773 714413 := bbase (se 3 (by rfl) ⟨133952, by rfl⟩ : syracuseStep 714413 = 267905) (by norm_num)
theorem B534205 : Blo 421773 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B476869 : Blo 421773 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B952037 : Blo 421773 952037 := bbase (se 4 (by rfl) ⟨89253, by rfl⟩ : syracuseStep 952037 = 178507) (by norm_num)
theorem B476905 : Blo 421773 476905 := bbase (se 2 (by rfl) ⟨178839, by rfl⟩ : syracuseStep 476905 = 357679) (by norm_num)
theorem B927485 : Blo 421773 927485 := bbase (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) (by norm_num)
theorem B1074941 : Blo 421773 1074941 := bbase (se 3 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 1074941 = 403103) (by norm_num)
theorem B476941 : Blo 421773 476941 := bbase (se 3 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 476941 = 178853) (by norm_num)
theorem B952109 : Blo 421773 952109 := bbase (se 3 (by rfl) ⟨178520, by rfl⟩ : syracuseStep 952109 = 357041) (by norm_num)
theorem B714541 : Blo 421773 714541 := bbase (se 3 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 714541 = 267953) (by norm_num)
theorem B476977 : Blo 421773 476977 := bbase (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) (by norm_num)
theorem B1206085 : Blo 421773 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B2705237 : Blo 421773 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B477013 : Blo 421773 477013 := bbase (se 9 (by rfl) ⟨1397, by rfl⟩ : syracuseStep 477013 = 2795) (by norm_num)
theorem B632669 : Blo 421773 632669 := bbase (se 3 (by rfl) ⟨118625, by rfl⟩ : syracuseStep 632669 = 237251) (by norm_num)
theorem B1140581 : Blo 421773 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B534377 : Blo 421773 534377 := bbase (se 2 (by rfl) ⟨200391, by rfl⟩ : syracuseStep 534377 = 400783) (by norm_num)
theorem B632693 : Blo 421773 632693 := bbase (se 5 (by rfl) ⟨29657, by rfl⟩ : syracuseStep 632693 = 59315) (by norm_num)
theorem B952181 : Blo 421773 952181 := bbase (se 5 (by rfl) ⟨44633, by rfl⟩ : syracuseStep 952181 = 89267) (by norm_num)
theorem B804725 : Blo 421773 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B477049 : Blo 421773 477049 := bbase (se 2 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 477049 = 357787) (by norm_num)
theorem B714629 : Blo 421773 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B632717 : Blo 421773 632717 := bbase (se 3 (by rfl) ⟨118634, by rfl⟩ : syracuseStep 632717 = 237269) (by norm_num)
theorem B427933 : Blo 421773 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B477085 : Blo 421773 477085 := bbase (se 3 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 477085 = 178907) (by norm_num)
theorem B534433 : Blo 421773 534433 := bbase (se 2 (by rfl) ⟨200412, by rfl⟩ : syracuseStep 534433 = 400825) (by norm_num)
theorem B452513 : Blo 421773 452513 := bbase (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) (by norm_num)
theorem B632741 : Blo 421773 632741 := bbase (se 4 (by rfl) ⟨59319, by rfl⟩ : syracuseStep 632741 = 118639) (by norm_num)
theorem B1427381 : Blo 421773 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B632765 : Blo 421773 632765 := bbase (se 3 (by rfl) ⟨118643, by rfl⟩ : syracuseStep 632765 = 237287) (by norm_num)
theorem B952253 : Blo 421773 952253 := bbase (se 3 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 952253 = 357095) (by norm_num)
theorem B477121 : Blo 421773 477121 := bbase (se 2 (by rfl) ⟨178920, by rfl⟩ : syracuseStep 477121 = 357841) (by norm_num)
theorem B1075133 : Blo 421773 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B632789 : Blo 421773 632789 := bbase (se 7 (by rfl) ⟨7415, by rfl⟩ : syracuseStep 632789 = 14831) (by norm_num)
theorem B1206245 : Blo 421773 1206245 := bbase (se 4 (by rfl) ⟨113085, by rfl⟩ : syracuseStep 1206245 = 226171) (by norm_num)
theorem B477157 : Blo 421773 477157 := bbase (se 4 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 477157 = 89467) (by norm_num)
theorem B1452005 : Blo 421773 1452005 := bbase (se 4 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 1452005 = 272251) (by norm_num)
theorem B632813 : Blo 421773 632813 := bbase (se 3 (by rfl) ⟨118652, by rfl⟩ : syracuseStep 632813 = 237305) (by norm_num)
theorem B1927157 : Blo 421773 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B534529 : Blo 421773 534529 := bbase (se 2 (by rfl) ⟨200448, by rfl⟩ : syracuseStep 534529 = 400897) (by norm_num)
theorem B632837 : Blo 421773 632837 := bbase (se 4 (by rfl) ⟨59328, by rfl⟩ : syracuseStep 632837 = 118657) (by norm_num)
theorem B952325 : Blo 421773 952325 := bbase (se 4 (by rfl) ⟨89280, by rfl⟩ : syracuseStep 952325 = 178561) (by norm_num)
theorem B714757 : Blo 421773 714757 := bbase (se 4 (by rfl) ⟨67008, by rfl⟩ : syracuseStep 714757 = 134017) (by norm_num)
theorem B477193 : Blo 421773 477193 := bbase (se 2 (by rfl) ⟨178947, by rfl⟩ : syracuseStep 477193 = 357895) (by norm_num)
theorem B2140181 : Blo 421773 2140181 := bbase (se 6 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 2140181 = 100321) (by norm_num)
theorem B632861 : Blo 421773 632861 := bbase (se 3 (by rfl) ⟨118661, by rfl⟩ : syracuseStep 632861 = 237323) (by norm_num)
theorem B903197 : Blo 421773 903197 := bbase (se 3 (by rfl) ⟨169349, by rfl⟩ : syracuseStep 903197 = 338699) (by norm_num)
theorem B477229 : Blo 421773 477229 := bbase (se 3 (by rfl) ⟨89480, by rfl⟩ : syracuseStep 477229 = 178961) (by norm_num)
theorem B632885 : Blo 421773 632885 := bbase (se 5 (by rfl) ⟨29666, by rfl⟩ : syracuseStep 632885 = 59333) (by norm_num)
theorem B632909 : Blo 421773 632909 := bbase (se 3 (by rfl) ⟨118670, by rfl⟩ : syracuseStep 632909 = 237341) (by norm_num)
theorem B952397 : Blo 421773 952397 := bbase (se 3 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 952397 = 357149) (by norm_num)
theorem B477265 : Blo 421773 477265 := bbase (se 2 (by rfl) ⟨178974, by rfl⟩ : syracuseStep 477265 = 357949) (by norm_num)
theorem B714845 : Blo 421773 714845 := bbase (se 3 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 714845 = 268067) (by norm_num)
theorem B632933 : Blo 421773 632933 := bbase (se 4 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 632933 = 118675) (by norm_num)
theorem B764005 : Blo 421773 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B477301 : Blo 421773 477301 := bbase (se 5 (by rfl) ⟨22373, by rfl⟩ : syracuseStep 477301 = 44747) (by norm_num)
theorem B632957 : Blo 421773 632957 := bbase (se 3 (by rfl) ⟨118679, by rfl⟩ : syracuseStep 632957 = 237359) (by norm_num)
theorem B1812613 : Blo 421773 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B632981 : Blo 421773 632981 := bbase (se 6 (by rfl) ⟨14835, by rfl⟩ : syracuseStep 632981 = 29671) (by norm_num)
theorem B952469 : Blo 421773 952469 := bbase (se 6 (by rfl) ⟨22323, by rfl⟩ : syracuseStep 952469 = 44647) (by norm_num)
theorem B477337 : Blo 421773 477337 := bbase (se 2 (by rfl) ⟨179001, by rfl⟩ : syracuseStep 477337 = 358003) (by norm_num)
theorem B633005 : Blo 421773 633005 := bbase (se 3 (by rfl) ⟨118688, by rfl⟩ : syracuseStep 633005 = 237377) (by norm_num)
theorem B534701 : Blo 421773 534701 := bbase (se 3 (by rfl) ⟨100256, by rfl⟩ : syracuseStep 534701 = 200513) (by norm_num)
theorem B477373 : Blo 421773 477373 := bbase (se 3 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 477373 = 179015) (by norm_num)
theorem B633029 : Blo 421773 633029 := bbase (se 4 (by rfl) ⟨59346, by rfl⟩ : syracuseStep 633029 = 118693) (by norm_num)
theorem B1206485 : Blo 421773 1206485 := bbase (se 7 (by rfl) ⟨14138, by rfl⟩ : syracuseStep 1206485 = 28277) (by norm_num)
theorem B633053 : Blo 421773 633053 := bbase (se 3 (by rfl) ⟨118697, by rfl⟩ : syracuseStep 633053 = 237395) (by norm_num)
theorem B952541 : Blo 421773 952541 := bbase (se 3 (by rfl) ⟨178601, by rfl⟩ : syracuseStep 952541 = 357203) (by norm_num)
theorem B714973 : Blo 421773 714973 := bbase (se 3 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 714973 = 268115) (by norm_num)
theorem B477409 : Blo 421773 477409 := bbase (se 2 (by rfl) ⟨179028, by rfl⟩ : syracuseStep 477409 = 358057) (by norm_num)
theorem B534757 : Blo 421773 534757 := bbase (se 4 (by rfl) ⟨50133, by rfl⟩ : syracuseStep 534757 = 100267) (by norm_num)
theorem B633077 : Blo 421773 633077 := bbase (se 5 (by rfl) ⟨29675, by rfl⟩ : syracuseStep 633077 = 59351) (by norm_num)
theorem B764149 : Blo 421773 764149 := bbase (se 5 (by rfl) ⟨35819, by rfl⟩ : syracuseStep 764149 = 71639) (by norm_num)
theorem B428293 : Blo 421773 428293 := bbase (se 4 (by rfl) ⟨40152, by rfl⟩ : syracuseStep 428293 = 80305) (by norm_num)
theorem B477445 : Blo 421773 477445 := bbase (se 4 (by rfl) ⟨44760, by rfl⟩ : syracuseStep 477445 = 89521) (by norm_num)
theorem B633101 : Blo 421773 633101 := bbase (se 3 (by rfl) ⟨118706, by rfl⟩ : syracuseStep 633101 = 237413) (by norm_num)
theorem B3352853 : Blo 421773 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B633125 : Blo 421773 633125 := bbase (se 4 (by rfl) ⟨59355, by rfl⟩ : syracuseStep 633125 = 118711) (by norm_num)
theorem B952613 : Blo 421773 952613 := bbase (se 4 (by rfl) ⟨89307, by rfl⟩ : syracuseStep 952613 = 178615) (by norm_num)
theorem B477481 : Blo 421773 477481 := bbase (se 2 (by rfl) ⟨179055, by rfl⟩ : syracuseStep 477481 = 358111) (by norm_num)
theorem B715061 : Blo 421773 715061 := bbase (se 5 (by rfl) ⟨33518, by rfl⟩ : syracuseStep 715061 = 67037) (by norm_num)
theorem B633149 : Blo 421773 633149 := bbase (se 3 (by rfl) ⟨118715, by rfl⟩ : syracuseStep 633149 = 237431) (by norm_num)
theorem B534853 : Blo 421773 534853 := bbase (se 4 (by rfl) ⟨50142, by rfl⟩ : syracuseStep 534853 = 100285) (by norm_num)
theorem B477517 : Blo 421773 477517 := bbase (se 3 (by rfl) ⟨89534, by rfl⟩ : syracuseStep 477517 = 179069) (by norm_num)
theorem B633173 : Blo 421773 633173 := bbase (se 10 (by rfl) ⟨927, by rfl⟩ : syracuseStep 633173 = 1855) (by norm_num)
theorem B452957 : Blo 421773 452957 := bbase (se 3 (by rfl) ⟨84929, by rfl⟩ : syracuseStep 452957 = 169859) (by norm_num)
theorem B1427813 : Blo 421773 1427813 := bbase (se 4 (by rfl) ⟨133857, by rfl⟩ : syracuseStep 1427813 = 267715) (by norm_num)
theorem B633197 : Blo 421773 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B952685 : Blo 421773 952685 := bbase (se 3 (by rfl) ⟨178628, by rfl⟩ : syracuseStep 952685 = 357257) (by norm_num)
theorem B477553 : Blo 421773 477553 := bbase (se 2 (by rfl) ⟨179082, by rfl⟩ : syracuseStep 477553 = 358165) (by norm_num)
theorem B633221 : Blo 421773 633221 := bbase (se 4 (by rfl) ⟨59364, by rfl⟩ : syracuseStep 633221 = 118729) (by norm_num)
theorem B903565 : Blo 421773 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B1526165 : Blo 421773 1526165 := bbase (se 6 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 1526165 = 71539) (by norm_num)
theorem B1206677 : Blo 421773 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B477589 : Blo 421773 477589 := bbase (se 6 (by rfl) ⟨11193, by rfl⟩ : syracuseStep 477589 = 22387) (by norm_num)
theorem B633245 : Blo 421773 633245 := bbase (se 3 (by rfl) ⟨118733, by rfl⟩ : syracuseStep 633245 = 237467) (by norm_num)
theorem B633269 : Blo 421773 633269 := bbase (se 5 (by rfl) ⟨29684, by rfl⟩ : syracuseStep 633269 = 59369) (by norm_num)
theorem B952757 : Blo 421773 952757 := bbase (se 5 (by rfl) ⟨44660, by rfl⟩ : syracuseStep 952757 = 89321) (by norm_num)
theorem B715189 : Blo 421773 715189 := bbase (se 5 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 715189 = 67049) (by norm_num)
theorem B477625 : Blo 421773 477625 := bbase (se 2 (by rfl) ⟨179109, by rfl⟩ : syracuseStep 477625 = 358219) (by norm_num)
theorem B633293 : Blo 421773 633293 := bbase (se 3 (by rfl) ⟨118742, by rfl⟩ : syracuseStep 633293 = 237485) (by norm_num)
theorem B477661 : Blo 421773 477661 := bbase (se 3 (by rfl) ⟨89561, by rfl⟩ : syracuseStep 477661 = 179123) (by norm_num)
theorem B633317 : Blo 421773 633317 := bbase (se 4 (by rfl) ⟨59373, by rfl⟩ : syracuseStep 633317 = 118747) (by norm_num)
theorem B535025 : Blo 421773 535025 := bbase (se 2 (by rfl) ⟨200634, by rfl⟩ : syracuseStep 535025 = 401269) (by norm_num)
theorem B633341 : Blo 421773 633341 := bbase (se 3 (by rfl) ⟨118751, by rfl⟩ : syracuseStep 633341 = 237503) (by norm_num)
theorem B952829 : Blo 421773 952829 := bbase (se 3 (by rfl) ⟨178655, by rfl⟩ : syracuseStep 952829 = 357311) (by norm_num)
theorem B477697 : Blo 421773 477697 := bbase (se 2 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 477697 = 358273) (by norm_num)
theorem B813581 : Blo 421773 813581 := bbase (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) (by norm_num)
theorem B715277 : Blo 421773 715277 := bbase (se 3 (by rfl) ⟨134114, by rfl⟩ : syracuseStep 715277 = 268229) (by norm_num)
theorem B633365 : Blo 421773 633365 := bbase (se 6 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 633365 = 29689) (by norm_num)
theorem B477733 : Blo 421773 477733 := bbase (se 4 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 477733 = 89575) (by norm_num)
theorem B535081 : Blo 421773 535081 := bbase (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) (by norm_num)
theorem B633389 : Blo 421773 633389 := bbase (se 3 (by rfl) ⟨118760, by rfl⟩ : syracuseStep 633389 = 237521) (by norm_num)
theorem B633413 : Blo 421773 633413 := bbase (se 4 (by rfl) ⟨59382, by rfl⟩ : syracuseStep 633413 = 118765) (by norm_num)
theorem B952901 : Blo 421773 952901 := bbase (se 4 (by rfl) ⟨89334, by rfl⟩ : syracuseStep 952901 = 178669) (by norm_num)
theorem B477769 : Blo 421773 477769 := bbase (se 2 (by rfl) ⟨179163, by rfl⟩ : syracuseStep 477769 = 358327) (by norm_num)
theorem B453205 : Blo 421773 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B633437 : Blo 421773 633437 := bbase (se 3 (by rfl) ⟨118769, by rfl⟩ : syracuseStep 633437 = 237539) (by norm_num)
theorem B805477 : Blo 421773 805477 := bbase (se 4 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 805477 = 151027) (by norm_num)
theorem B477805 : Blo 421773 477805 := bbase (se 3 (by rfl) ⟨89588, by rfl⟩ : syracuseStep 477805 = 179177) (by norm_num)
theorem B633461 : Blo 421773 633461 := bbase (se 5 (by rfl) ⟨29693, by rfl⟩ : syracuseStep 633461 = 59387) (by norm_num)
theorem B535177 : Blo 421773 535177 := bbase (se 2 (by rfl) ⟨200691, by rfl⟩ : syracuseStep 535177 = 401383) (by norm_num)
theorem B633485 : Blo 421773 633485 := bbase (se 3 (by rfl) ⟨118778, by rfl⟩ : syracuseStep 633485 = 237557) (by norm_num)
theorem B952973 : Blo 421773 952973 := bbase (se 3 (by rfl) ⟨178682, by rfl⟩ : syracuseStep 952973 = 357365) (by norm_num)
theorem B715405 : Blo 421773 715405 := bbase (se 3 (by rfl) ⟨134138, by rfl⟩ : syracuseStep 715405 = 268277) (by norm_num)
theorem B477841 : Blo 421773 477841 := bbase (se 2 (by rfl) ⟨179190, by rfl⟩ : syracuseStep 477841 = 358381) (by norm_num)
theorem B1370789 : Blo 421773 1370789 := bbase (se 4 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 1370789 = 257023) (by norm_num)
theorem B633509 : Blo 421773 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B1067701 : Blo 421773 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B633533 : Blo 421773 633533 := bbase (se 3 (by rfl) ⟨118787, by rfl⟩ : syracuseStep 633533 = 237575) (by norm_num)
theorem B1829573 : Blo 421773 1829573 := bbase (se 4 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 1829573 = 343045) (by norm_num)
theorem B3607253 : Blo 421773 3607253 := bbase (se 7 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 3607253 = 84545) (by norm_num)
theorem B633557 : Blo 421773 633557 := bbase (se 7 (by rfl) ⟨7424, by rfl⟩ : syracuseStep 633557 = 14849) (by norm_num)
theorem B953045 : Blo 421773 953045 := bbase (se 7 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 953045 = 22337) (by norm_num)
theorem B715493 : Blo 421773 715493 := bbase (se 4 (by rfl) ⟨67077, by rfl⟩ : syracuseStep 715493 = 134155) (by norm_num)
theorem B633581 : Blo 421773 633581 := bbase (se 3 (by rfl) ⟨118796, by rfl⟩ : syracuseStep 633581 = 237593) (by norm_num)
theorem B805621 : Blo 421773 805621 := bbase (se 5 (by rfl) ⟨37763, by rfl⟩ : syracuseStep 805621 = 75527) (by norm_num)
theorem B633605 : Blo 421773 633605 := bbase (se 4 (by rfl) ⟨59400, by rfl⟩ : syracuseStep 633605 = 118801) (by norm_num)
theorem B1428245 : Blo 421773 1428245 := bbase (se 6 (by rfl) ⟨33474, by rfl⟩ : syracuseStep 1428245 = 66949) (by norm_num)
theorem B633629 : Blo 421773 633629 := bbase (se 3 (by rfl) ⟨118805, by rfl⟩ : syracuseStep 633629 = 237611) (by norm_num)
theorem B953117 : Blo 421773 953117 := bbase (se 3 (by rfl) ⟨178709, by rfl⟩ : syracuseStep 953117 = 357419) (by norm_num)
theorem B1067813 : Blo 421773 1067813 := bbase (se 4 (by rfl) ⟨100107, by rfl⟩ : syracuseStep 1067813 = 200215) (by norm_num)
theorem B633653 : Blo 421773 633653 := bbase (se 5 (by rfl) ⟨29702, by rfl⟩ : syracuseStep 633653 = 59405) (by norm_num)
theorem B535349 : Blo 421773 535349 := bbase (se 5 (by rfl) ⟨25094, by rfl⟩ : syracuseStep 535349 = 50189) (by norm_num)
theorem B633677 : Blo 421773 633677 := bbase (se 3 (by rfl) ⟨118814, by rfl⟩ : syracuseStep 633677 = 237629) (by norm_num)
theorem B633701 : Blo 421773 633701 := bbase (se 4 (by rfl) ⟨59409, by rfl⟩ : syracuseStep 633701 = 118819) (by norm_num)
theorem B953189 : Blo 421773 953189 := bbase (se 4 (by rfl) ⟨89361, by rfl⟩ : syracuseStep 953189 = 178723) (by norm_num)
theorem B715621 : Blo 421773 715621 := bbase (se 4 (by rfl) ⟨67089, by rfl⟩ : syracuseStep 715621 = 134179) (by norm_num)
theorem B535405 : Blo 421773 535405 := bbase (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) (by norm_num)
theorem B633725 : Blo 421773 633725 := bbase (se 3 (by rfl) ⟨118823, by rfl⟩ : syracuseStep 633725 = 237647) (by norm_num)
theorem B2149253 : Blo 421773 2149253 := bbase (se 4 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 2149253 = 402985) (by norm_num)
theorem B633749 : Blo 421773 633749 := bbase (se 6 (by rfl) ⟨14853, by rfl⟩ : syracuseStep 633749 = 29707) (by norm_num)
theorem B805781 : Blo 421773 805781 := bbase (se 6 (by rfl) ⟨18885, by rfl⟩ : syracuseStep 805781 = 37771) (by norm_num)
theorem B633773 : Blo 421773 633773 := bbase (se 3 (by rfl) ⟨118832, by rfl⟩ : syracuseStep 633773 = 237665) (by norm_num)
theorem B953261 : Blo 421773 953261 := bbase (se 3 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 953261 = 357473) (by norm_num)
theorem B715709 : Blo 421773 715709 := bbase (se 3 (by rfl) ⟨134195, by rfl⟩ : syracuseStep 715709 = 268391) (by norm_num)
theorem B633797 : Blo 421773 633797 := bbase (se 4 (by rfl) ⟨59418, by rfl⟩ : syracuseStep 633797 = 118837) (by norm_num)
theorem B535501 : Blo 421773 535501 := bbase (se 3 (by rfl) ⟨100406, by rfl⟩ : syracuseStep 535501 = 200813) (by norm_num)
theorem B1526741 : Blo 421773 1526741 := bbase (se 7 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 1526741 = 35783) (by norm_num)
theorem B633821 : Blo 421773 633821 := bbase (se 3 (by rfl) ⟨118841, by rfl⟩ : syracuseStep 633821 = 237683) (by norm_num)
theorem B1068005 : Blo 421773 1068005 := bbase (se 4 (by rfl) ⟨100125, by rfl⟩ : syracuseStep 1068005 = 200251) (by norm_num)
theorem B633845 : Blo 421773 633845 := bbase (se 5 (by rfl) ⟨29711, by rfl⟩ : syracuseStep 633845 = 59423) (by norm_num)
theorem B953333 : Blo 421773 953333 := bbase (se 5 (by rfl) ⟨44687, by rfl⟩ : syracuseStep 953333 = 89375) (by norm_num)
theorem B633869 : Blo 421773 633869 := bbase (se 3 (by rfl) ⟨118850, by rfl⟩ : syracuseStep 633869 = 237701) (by norm_num)
theorem B764957 : Blo 421773 764957 := bbase (se 3 (by rfl) ⟨143429, by rfl⟩ : syracuseStep 764957 = 286859) (by norm_num)
theorem B633893 : Blo 421773 633893 := bbase (se 4 (by rfl) ⟨59427, by rfl⟩ : syracuseStep 633893 = 118855) (by norm_num)
theorem B805925 : Blo 421773 805925 := bbase (se 4 (by rfl) ⟨75555, by rfl⟩ : syracuseStep 805925 = 151111) (by norm_num)
theorem B633917 : Blo 421773 633917 := bbase (se 3 (by rfl) ⟨118859, by rfl⟩ : syracuseStep 633917 = 237719) (by norm_num)
theorem B953405 : Blo 421773 953405 := bbase (se 3 (by rfl) ⟨178763, by rfl⟩ : syracuseStep 953405 = 357527) (by norm_num)
theorem B715837 : Blo 421773 715837 := bbase (se 3 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 715837 = 268439) (by norm_num)
theorem B633941 : Blo 421773 633941 := bbase (se 8 (by rfl) ⟨3714, by rfl⟩ : syracuseStep 633941 = 7429) (by norm_num)
theorem B1208773 : Blo 421773 1208773 := bbase (se 4 (by rfl) ⟨113322, by rfl⟩ : syracuseStep 1208773 = 226645) (by norm_num)
theorem B633965 : Blo 421773 633965 := bbase (se 3 (by rfl) ⟨118868, by rfl⟩ : syracuseStep 633965 = 237737) (by norm_num)
theorem B535673 : Blo 421773 535673 := bbase (se 2 (by rfl) ⟨200877, by rfl⟩ : syracuseStep 535673 = 401755) (by norm_num)
theorem B633989 : Blo 421773 633989 := bbase (se 4 (by rfl) ⟨59436, by rfl⟩ : syracuseStep 633989 = 118873) (by norm_num)
theorem B953477 : Blo 421773 953477 := bbase (se 4 (by rfl) ⟨89388, by rfl⟩ : syracuseStep 953477 = 178777) (by norm_num)
theorem B642197 : Blo 421773 642197 := bbase (se 6 (by rfl) ⟨15051, by rfl⟩ : syracuseStep 642197 = 30103) (by norm_num)
theorem B715925 : Blo 421773 715925 := bbase (se 6 (by rfl) ⟨16779, by rfl⟩ : syracuseStep 715925 = 33559) (by norm_num)
theorem B634013 : Blo 421773 634013 := bbase (se 3 (by rfl) ⟨118877, by rfl⟩ : syracuseStep 634013 = 237755) (by norm_num)
theorem B642221 : Blo 421773 642221 := bbase (se 3 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 642221 = 240833) (by norm_num)
theorem B535729 : Blo 421773 535729 := bbase (se 2 (by rfl) ⟨200898, by rfl⟩ : syracuseStep 535729 = 401797) (by norm_num)
theorem B634037 : Blo 421773 634037 := bbase (se 5 (by rfl) ⟨29720, by rfl⟩ : syracuseStep 634037 = 59441) (by norm_num)
theorem B1428677 : Blo 421773 1428677 := bbase (se 4 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 1428677 = 267877) (by norm_num)
theorem B634061 : Blo 421773 634061 := bbase (se 3 (by rfl) ⟨118886, by rfl⟩ : syracuseStep 634061 = 237773) (by norm_num)
theorem B953549 : Blo 421773 953549 := bbase (se 3 (by rfl) ⟨178790, by rfl⟩ : syracuseStep 953549 = 357581) (by norm_num)
theorem B634085 : Blo 421773 634085 := bbase (se 4 (by rfl) ⟨59445, by rfl⟩ : syracuseStep 634085 = 118891) (by norm_num)
theorem B765173 : Blo 421773 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B634109 : Blo 421773 634109 := bbase (se 3 (by rfl) ⟨118895, by rfl⟩ : syracuseStep 634109 = 237791) (by norm_num)
theorem B601357 : Blo 421773 601357 := bbase (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) (by norm_num)
theorem B535825 : Blo 421773 535825 := bbase (se 2 (by rfl) ⟨200934, by rfl⟩ : syracuseStep 535825 = 401869) (by norm_num)
theorem B634133 : Blo 421773 634133 := bbase (se 6 (by rfl) ⟨14862, by rfl⟩ : syracuseStep 634133 = 29725) (by norm_num)
theorem B953621 : Blo 421773 953621 := bbase (se 6 (by rfl) ⟨22350, by rfl⟩ : syracuseStep 953621 = 44701) (by norm_num)
theorem B716053 : Blo 421773 716053 := bbase (se 6 (by rfl) ⟨16782, by rfl⟩ : syracuseStep 716053 = 33565) (by norm_num)
theorem B2141477 : Blo 421773 2141477 := bbase (se 4 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 2141477 = 401527) (by norm_num)
theorem B634157 : Blo 421773 634157 := bbase (se 3 (by rfl) ⟨118904, by rfl⟩ : syracuseStep 634157 = 237809) (by norm_num)
theorem B1068349 : Blo 421773 1068349 := bbase (se 3 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 1068349 = 400631) (by norm_num)
theorem B765245 : Blo 421773 765245 := bbase (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) (by norm_num)
theorem B552253 : Blo 421773 552253 := bbase (se 3 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 552253 = 207095) (by norm_num)
theorem B634181 : Blo 421773 634181 := bbase (se 4 (by rfl) ⟨59454, by rfl⟩ : syracuseStep 634181 = 118909) (by norm_num)
theorem B806213 : Blo 421773 806213 := bbase (se 4 (by rfl) ⟨75582, by rfl⟩ : syracuseStep 806213 = 151165) (by norm_num)
theorem B634205 : Blo 421773 634205 := bbase (se 3 (by rfl) ⟨118913, by rfl⟩ : syracuseStep 634205 = 237827) (by norm_num)
theorem B953693 : Blo 421773 953693 := bbase (se 3 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 953693 = 357635) (by norm_num)
theorem B716141 : Blo 421773 716141 := bbase (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) (by norm_num)
theorem B634229 : Blo 421773 634229 := bbase (se 5 (by rfl) ⟨29729, by rfl⟩ : syracuseStep 634229 = 59459) (by norm_num)
theorem B1207669 : Blo 421773 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B634253 : Blo 421773 634253 := bbase (se 3 (by rfl) ⟨118922, by rfl⟩ : syracuseStep 634253 = 237845) (by norm_num)
theorem B765325 : Blo 421773 765325 := bbase (se 3 (by rfl) ⟨143498, by rfl⟩ : syracuseStep 765325 = 286997) (by norm_num)
theorem B773525 : Blo 421773 773525 := bbase (se 6 (by rfl) ⟨18129, by rfl⟩ : syracuseStep 773525 = 36259) (by norm_num)
theorem B634277 : Blo 421773 634277 := bbase (se 4 (by rfl) ⟨59463, by rfl⟩ : syracuseStep 634277 = 118927) (by norm_num)
theorem B953765 : Blo 421773 953765 := bbase (se 4 (by rfl) ⟨89415, by rfl⟩ : syracuseStep 953765 = 178831) (by norm_num)
theorem B1068461 : Blo 421773 1068461 := bbase (se 3 (by rfl) ⟨200336, by rfl⟩ : syracuseStep 1068461 = 400673) (by norm_num)
theorem B634301 : Blo 421773 634301 := bbase (se 3 (by rfl) ⟨118931, by rfl⟩ : syracuseStep 634301 = 237863) (by norm_num)
theorem B535997 : Blo 421773 535997 := bbase (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) (by norm_num)
theorem B765389 : Blo 421773 765389 := bbase (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) (by norm_num)
theorem B634325 : Blo 421773 634325 := bbase (se 7 (by rfl) ⟨7433, by rfl⟩ : syracuseStep 634325 = 14867) (by norm_num)
theorem B806365 : Blo 421773 806365 := bbase (se 3 (by rfl) ⟨151193, by rfl⟩ : syracuseStep 806365 = 302387) (by norm_num)
theorem B634349 : Blo 421773 634349 := bbase (se 3 (by rfl) ⟨118940, by rfl⟩ : syracuseStep 634349 = 237881) (by norm_num)
theorem B953837 : Blo 421773 953837 := bbase (se 3 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 953837 = 357689) (by norm_num)
theorem B716269 : Blo 421773 716269 := bbase (se 3 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 716269 = 268601) (by norm_num)
theorem B536053 : Blo 421773 536053 := bbase (se 5 (by rfl) ⟨25127, by rfl⟩ : syracuseStep 536053 = 50255) (by norm_num)
theorem B634373 : Blo 421773 634373 := bbase (se 4 (by rfl) ⟨59472, by rfl⟩ : syracuseStep 634373 = 118945) (by norm_num)
theorem B634397 : Blo 421773 634397 := bbase (se 3 (by rfl) ⟨118949, by rfl⟩ : syracuseStep 634397 = 237899) (by norm_num)
theorem B1609253 : Blo 421773 1609253 := bbase (se 4 (by rfl) ⟨150867, by rfl⟩ : syracuseStep 1609253 = 301735) (by norm_num)
theorem B634421 : Blo 421773 634421 := bbase (se 5 (by rfl) ⟨29738, by rfl⟩ : syracuseStep 634421 = 59477) (by norm_num)
theorem B953909 : Blo 421773 953909 := bbase (se 5 (by rfl) ⟨44714, by rfl⟩ : syracuseStep 953909 = 89429) (by norm_num)
theorem B1019461 : Blo 421773 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B716357 : Blo 421773 716357 := bbase (se 4 (by rfl) ⟨67158, by rfl⟩ : syracuseStep 716357 = 134317) (by norm_num)
theorem B634445 : Blo 421773 634445 := bbase (se 3 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 634445 = 237917) (by norm_num)
theorem B536149 : Blo 421773 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B634469 : Blo 421773 634469 := bbase (se 4 (by rfl) ⟨59481, by rfl⟩ : syracuseStep 634469 = 118963) (by norm_num)
theorem B1068653 : Blo 421773 1068653 := bbase (se 3 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 1068653 = 400745) (by norm_num)
theorem B1429109 : Blo 421773 1429109 := bbase (se 5 (by rfl) ⟨66989, by rfl⟩ : syracuseStep 1429109 = 133979) (by norm_num)
theorem B634493 : Blo 421773 634493 := bbase (se 3 (by rfl) ⟨118967, by rfl⟩ : syracuseStep 634493 = 237935) (by norm_num)
theorem B953981 : Blo 421773 953981 := bbase (se 3 (by rfl) ⟨178871, by rfl⟩ : syracuseStep 953981 = 357743) (by norm_num)
theorem B634517 : Blo 421773 634517 := bbase (se 6 (by rfl) ⟨14871, by rfl⟩ : syracuseStep 634517 = 29743) (by norm_num)
theorem B634541 : Blo 421773 634541 := bbase (se 3 (by rfl) ⟨118976, by rfl⟩ : syracuseStep 634541 = 237953) (by norm_num)
theorem B634565 : Blo 421773 634565 := bbase (se 4 (by rfl) ⟨59490, by rfl⟩ : syracuseStep 634565 = 118981) (by norm_num)
theorem B954053 : Blo 421773 954053 := bbase (se 4 (by rfl) ⟨89442, by rfl⟩ : syracuseStep 954053 = 178885) (by norm_num)
theorem B716485 : Blo 421773 716485 := bbase (se 4 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 716485 = 134341) (by norm_num)
theorem B634589 : Blo 421773 634589 := bbase (se 3 (by rfl) ⟨118985, by rfl⟩ : syracuseStep 634589 = 237971) (by norm_num)
theorem B634613 : Blo 421773 634613 := bbase (se 5 (by rfl) ⟨29747, by rfl⟩ : syracuseStep 634613 = 59495) (by norm_num)
theorem B536321 : Blo 421773 536321 := bbase (se 2 (by rfl) ⟨201120, by rfl⟩ : syracuseStep 536321 = 402241) (by norm_num)
theorem B634637 : Blo 421773 634637 := bbase (se 3 (by rfl) ⟨118994, by rfl⟩ : syracuseStep 634637 = 237989) (by norm_num)
theorem B954125 : Blo 421773 954125 := bbase (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) (by norm_num)
theorem B1142549 : Blo 421773 1142549 := bbase (se 6 (by rfl) ⟨26778, by rfl⟩ : syracuseStep 1142549 = 53557) (by norm_num)
theorem B716573 : Blo 421773 716573 := bbase (se 3 (by rfl) ⟨134357, by rfl⟩ : syracuseStep 716573 = 268715) (by norm_num)
theorem B634661 : Blo 421773 634661 := bbase (se 4 (by rfl) ⟨59499, by rfl⟩ : syracuseStep 634661 = 118999) (by norm_num)
theorem B536377 : Blo 421773 536377 := bbase (se 2 (by rfl) ⟨201141, by rfl⟩ : syracuseStep 536377 = 402283) (by norm_num)
theorem B634685 : Blo 421773 634685 := bbase (se 3 (by rfl) ⟨119003, by rfl⟩ : syracuseStep 634685 = 238007) (by norm_num)
theorem B1609541 : Blo 421773 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B634709 : Blo 421773 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B954197 : Blo 421773 954197 := bbase (se 9 (by rfl) ⟨2795, by rfl⟩ : syracuseStep 954197 = 5591) (by norm_num)
theorem B601949 : Blo 421773 601949 := bbase (se 3 (by rfl) ⟨112865, by rfl⟩ : syracuseStep 601949 = 225731) (by norm_num)
theorem B634733 : Blo 421773 634733 := bbase (se 3 (by rfl) ⟨119012, by rfl⟩ : syracuseStep 634733 = 238025) (by norm_num)
theorem B905069 : Blo 421773 905069 := bbase (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) (by norm_num)
theorem B634757 : Blo 421773 634757 := bbase (se 4 (by rfl) ⟨59508, by rfl⟩ : syracuseStep 634757 = 119017) (by norm_num)
theorem B1699717 : Blo 421773 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B536473 : Blo 421773 536473 := bbase (se 2 (by rfl) ⟨201177, by rfl⟩ : syracuseStep 536473 = 402355) (by norm_num)
theorem B634781 : Blo 421773 634781 := bbase (se 3 (by rfl) ⟨119021, by rfl⟩ : syracuseStep 634781 = 238043) (by norm_num)
theorem B954269 : Blo 421773 954269 := bbase (se 3 (by rfl) ⟨178925, by rfl⟩ : syracuseStep 954269 = 357851) (by norm_num)
theorem B716701 : Blo 421773 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B602029 : Blo 421773 602029 := bbase (se 3 (by rfl) ⟨112880, by rfl⟩ : syracuseStep 602029 = 225761) (by norm_num)
theorem B634805 : Blo 421773 634805 := bbase (se 5 (by rfl) ⟨29756, by rfl⟩ : syracuseStep 634805 = 59513) (by norm_num)
theorem B1068997 : Blo 421773 1068997 := bbase (se 4 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 1068997 = 200437) (by norm_num)
theorem B1601477 : Blo 421773 1601477 := bbase (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) (by norm_num)
theorem B634829 : Blo 421773 634829 := bbase (se 3 (by rfl) ⟨119030, by rfl⟩ : syracuseStep 634829 = 238061) (by norm_num)
theorem B634853 : Blo 421773 634853 := bbase (se 4 (by rfl) ⟨59517, by rfl⟩ : syracuseStep 634853 = 119035) (by norm_num)
theorem B954341 : Blo 421773 954341 := bbase (se 4 (by rfl) ⟨89469, by rfl⟩ : syracuseStep 954341 = 178939) (by norm_num)
theorem B716789 : Blo 421773 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B634877 : Blo 421773 634877 := bbase (se 3 (by rfl) ⟨119039, by rfl⟩ : syracuseStep 634877 = 238079) (by norm_num)
theorem B905213 : Blo 421773 905213 := bbase (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) (by norm_num)
theorem B634901 : Blo 421773 634901 := bbase (se 6 (by rfl) ⟨14880, by rfl⟩ : syracuseStep 634901 = 29761) (by norm_num)
theorem B602149 : Blo 421773 602149 := bbase (se 4 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 602149 = 112903) (by norm_num)
theorem B1429541 : Blo 421773 1429541 := bbase (se 4 (by rfl) ⟨134019, by rfl⟩ : syracuseStep 1429541 = 268039) (by norm_num)
theorem B634925 : Blo 421773 634925 := bbase (se 3 (by rfl) ⟨119048, by rfl⟩ : syracuseStep 634925 = 238097) (by norm_num)
theorem B954413 : Blo 421773 954413 := bbase (se 3 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 954413 = 357905) (by norm_num)
theorem B1069109 : Blo 421773 1069109 := bbase (se 5 (by rfl) ⟨50114, by rfl⟩ : syracuseStep 1069109 = 100229) (by norm_num)
theorem B634949 : Blo 421773 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B536645 : Blo 421773 536645 := bbase (se 4 (by rfl) ⟨50310, by rfl⟩ : syracuseStep 536645 = 100621) (by norm_num)
theorem B3223637 : Blo 421773 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B634973 : Blo 421773 634973 := bbase (se 3 (by rfl) ⟨119057, by rfl⟩ : syracuseStep 634973 = 238115) (by norm_num)
theorem B2199653 : Blo 421773 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B634997 : Blo 421773 634997 := bbase (se 5 (by rfl) ⟨29765, by rfl⟩ : syracuseStep 634997 = 59531) (by norm_num)
theorem B954485 : Blo 421773 954485 := bbase (se 5 (by rfl) ⟨44741, by rfl⟩ : syracuseStep 954485 = 89483) (by norm_num)
theorem B536701 : Blo 421773 536701 := bbase (se 3 (by rfl) ⟨100631, by rfl⟩ : syracuseStep 536701 = 201263) (by norm_num)
theorem B602245 : Blo 421773 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B635021 : Blo 421773 635021 := bbase (se 3 (by rfl) ⟨119066, by rfl⟩ : syracuseStep 635021 = 238133) (by norm_num)
theorem B635045 : Blo 421773 635045 := bbase (se 4 (by rfl) ⟨59535, by rfl⟩ : syracuseStep 635045 = 119071) (by norm_num)
theorem B1020077 : Blo 421773 1020077 := bbase (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) (by norm_num)
theorem B635069 : Blo 421773 635069 := bbase (se 3 (by rfl) ⟨119075, by rfl⟩ : syracuseStep 635069 = 238151) (by norm_num)
theorem B954557 : Blo 421773 954557 := bbase (se 3 (by rfl) ⟨178979, by rfl⟩ : syracuseStep 954557 = 357959) (by norm_num)
theorem B635093 : Blo 421773 635093 := bbase (se 7 (by rfl) ⟨7442, by rfl⟩ : syracuseStep 635093 = 14885) (by norm_num)
theorem B536797 : Blo 421773 536797 := bbase (se 3 (by rfl) ⟨100649, by rfl⟩ : syracuseStep 536797 = 201299) (by norm_num)
theorem B1601765 : Blo 421773 1601765 := bbase (se 4 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 1601765 = 300331) (by norm_num)
theorem B1061093 : Blo 421773 1061093 := bbase (se 4 (by rfl) ⟨99477, by rfl⟩ : syracuseStep 1061093 = 198955) (by norm_num)
theorem B1020133 : Blo 421773 1020133 := bbase (se 4 (by rfl) ⟨95637, by rfl⟩ : syracuseStep 1020133 = 191275) (by norm_num)
theorem B635117 : Blo 421773 635117 := bbase (se 3 (by rfl) ⟨119084, by rfl⟩ : syracuseStep 635117 = 238169) (by norm_num)
theorem B1069301 : Blo 421773 1069301 := bbase (se 5 (by rfl) ⟨50123, by rfl⟩ : syracuseStep 1069301 = 100247) (by norm_num)
theorem B635141 : Blo 421773 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B954629 : Blo 421773 954629 := bbase (se 4 (by rfl) ⟨89496, by rfl⟩ : syracuseStep 954629 = 178993) (by norm_num)
theorem B913685 : Blo 421773 913685 := bbase (se 6 (by rfl) ⟨21414, by rfl⟩ : syracuseStep 913685 = 42829) (by norm_num)
theorem B676117 : Blo 421773 676117 := bbase (se 6 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 676117 = 31693) (by norm_num)
theorem B635165 : Blo 421773 635165 := bbase (se 3 (by rfl) ⟨119093, by rfl⟩ : syracuseStep 635165 = 238187) (by norm_num)
theorem B635189 : Blo 421773 635189 := bbase (se 5 (by rfl) ⟨29774, by rfl⟩ : syracuseStep 635189 = 59549) (by norm_num)
theorem B635213 : Blo 421773 635213 := bbase (se 3 (by rfl) ⟨119102, by rfl⟩ : syracuseStep 635213 = 238205) (by norm_num)
theorem B954701 : Blo 421773 954701 := bbase (se 3 (by rfl) ⟨179006, by rfl⟩ : syracuseStep 954701 = 358013) (by norm_num)
theorem B635237 : Blo 421773 635237 := bbase (se 4 (by rfl) ⟨59553, by rfl⟩ : syracuseStep 635237 = 119107) (by norm_num)
theorem B905573 : Blo 421773 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B635261 : Blo 421773 635261 := bbase (se 3 (by rfl) ⟨119111, by rfl⟩ : syracuseStep 635261 = 238223) (by norm_num)
theorem B536969 : Blo 421773 536969 := bbase (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) (by norm_num)
theorem B741773 : Blo 421773 741773 := bbase (se 3 (by rfl) ⟨139082, by rfl⟩ : syracuseStep 741773 = 278165) (by norm_num)
theorem B635285 : Blo 421773 635285 := bbase (se 6 (by rfl) ⟨14889, by rfl⟩ : syracuseStep 635285 = 29779) (by norm_num)
theorem B954773 : Blo 421773 954773 := bbase (se 6 (by rfl) ⟨22377, by rfl⟩ : syracuseStep 954773 = 44755) (by norm_num)
theorem B635309 : Blo 421773 635309 := bbase (se 3 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 635309 = 238241) (by norm_num)
theorem B537025 : Blo 421773 537025 := bbase (se 2 (by rfl) ⟨201384, by rfl⟩ : syracuseStep 537025 = 402769) (by norm_num)
theorem B1716677 : Blo 421773 1716677 := bbase (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) (by norm_num)
theorem B635333 : Blo 421773 635333 := bbase (se 4 (by rfl) ⟨59562, by rfl⟩ : syracuseStep 635333 = 119125) (by norm_num)
theorem B1429973 : Blo 421773 1429973 := bbase (se 7 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 1429973 = 33515) (by norm_num)
theorem B913885 : Blo 421773 913885 := bbase (se 3 (by rfl) ⟨171353, by rfl⟩ : syracuseStep 913885 = 342707) (by norm_num)
theorem B635357 : Blo 421773 635357 := bbase (se 3 (by rfl) ⟨119129, by rfl⟩ : syracuseStep 635357 = 238259) (by norm_num)
theorem B954845 : Blo 421773 954845 := bbase (se 3 (by rfl) ⟨179033, by rfl⟩ : syracuseStep 954845 = 358067) (by norm_num)
theorem B3215861 : Blo 421773 3215861 := bbase (se 5 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 3215861 = 301487) (by norm_num)
theorem B635381 : Blo 421773 635381 := bbase (se 5 (by rfl) ⟨29783, by rfl⟩ : syracuseStep 635381 = 59567) (by norm_num)
theorem B635405 : Blo 421773 635405 := bbase (se 3 (by rfl) ⟨119138, by rfl⟩ : syracuseStep 635405 = 238277) (by norm_num)
theorem B537121 : Blo 421773 537121 := bbase (se 2 (by rfl) ⟨201420, by rfl⟩ : syracuseStep 537121 = 402841) (by norm_num)
theorem B635429 : Blo 421773 635429 := bbase (se 4 (by rfl) ⟨59571, by rfl⟩ : syracuseStep 635429 = 119143) (by norm_num)
theorem B954917 : Blo 421773 954917 := bbase (se 4 (by rfl) ⟨89523, by rfl⟩ : syracuseStep 954917 = 179047) (by norm_num)
theorem B2142773 : Blo 421773 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B635453 : Blo 421773 635453 := bbase (se 3 (by rfl) ⟨119147, by rfl⟩ : syracuseStep 635453 = 238295) (by norm_num)
theorem B733765 : Blo 421773 733765 := bbase (se 4 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 733765 = 137581) (by norm_num)
theorem B1069645 : Blo 421773 1069645 := bbase (se 3 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 1069645 = 401117) (by norm_num)
theorem B4887125 : Blo 421773 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B635477 : Blo 421773 635477 := bbase (se 8 (by rfl) ⟨3723, by rfl⟩ : syracuseStep 635477 = 7447) (by norm_num)
theorem B856669 : Blo 421773 856669 := bbase (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) (by norm_num)
theorem B635501 : Blo 421773 635501 := bbase (se 3 (by rfl) ⟨119156, by rfl⟩ : syracuseStep 635501 = 238313) (by norm_num)
theorem B954989 : Blo 421773 954989 := bbase (se 3 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 954989 = 358121) (by norm_num)
theorem B602741 : Blo 421773 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B635525 : Blo 421773 635525 := bbase (se 4 (by rfl) ⟨59580, by rfl⟩ : syracuseStep 635525 = 119161) (by norm_num)
theorem B635549 : Blo 421773 635549 := bbase (se 3 (by rfl) ⟨119165, by rfl⟩ : syracuseStep 635549 = 238331) (by norm_num)
theorem B635573 : Blo 421773 635573 := bbase (se 5 (by rfl) ⟨29792, by rfl⟩ : syracuseStep 635573 = 59585) (by norm_num)
theorem B955061 : Blo 421773 955061 := bbase (se 5 (by rfl) ⟨44768, by rfl⟩ : syracuseStep 955061 = 89537) (by norm_num)
theorem B1069757 : Blo 421773 1069757 := bbase (se 3 (by rfl) ⟨200579, by rfl⟩ : syracuseStep 1069757 = 401159) (by norm_num)
theorem B725701 : Blo 421773 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B635597 : Blo 421773 635597 := bbase (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) (by norm_num)
theorem B537293 : Blo 421773 537293 := bbase (se 3 (by rfl) ⟨100742, by rfl⟩ : syracuseStep 537293 = 201485) (by norm_num)
theorem B635621 : Blo 421773 635621 := bbase (se 4 (by rfl) ⟨59589, by rfl⟩ : syracuseStep 635621 = 119179) (by norm_num)
theorem B3764981 : Blo 421773 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B635645 : Blo 421773 635645 := bbase (se 3 (by rfl) ⟨119183, by rfl⟩ : syracuseStep 635645 = 238367) (by norm_num)
theorem B955133 : Blo 421773 955133 := bbase (se 3 (by rfl) ⟨179087, by rfl⟩ : syracuseStep 955133 = 358175) (by norm_num)
theorem B537349 : Blo 421773 537349 := bbase (se 4 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 537349 = 100753) (by norm_num)
theorem B635669 : Blo 421773 635669 := bbase (se 6 (by rfl) ⟨14898, by rfl⟩ : syracuseStep 635669 = 29797) (by norm_num)
theorem B2036501 : Blo 421773 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B635693 : Blo 421773 635693 := bbase (se 3 (by rfl) ⟨119192, by rfl⟩ : syracuseStep 635693 = 238385) (by norm_num)
theorem B635717 : Blo 421773 635717 := bbase (se 4 (by rfl) ⟨59598, by rfl⟩ : syracuseStep 635717 = 119197) (by norm_num)
theorem B1528645 : Blo 421773 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B955205 : Blo 421773 955205 := bbase (se 4 (by rfl) ⟨89550, by rfl⟩ : syracuseStep 955205 = 179101) (by norm_num)
theorem B3674965 : Blo 421773 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B635741 : Blo 421773 635741 := bbase (se 3 (by rfl) ⟨119201, by rfl⟩ : syracuseStep 635741 = 238403) (by norm_num)
theorem B537445 : Blo 421773 537445 := bbase (se 4 (by rfl) ⟨50385, by rfl⟩ : syracuseStep 537445 = 100771) (by norm_num)
theorem B3855221 : Blo 421773 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B635765 : Blo 421773 635765 := bbase (se 5 (by rfl) ⟨29801, by rfl⟩ : syracuseStep 635765 = 59603) (by norm_num)
theorem B1069949 : Blo 421773 1069949 := bbase (se 3 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 1069949 = 401231) (by norm_num)
theorem B914309 : Blo 421773 914309 := bbase (se 4 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 914309 = 171433) (by norm_num)
theorem B1430405 : Blo 421773 1430405 := bbase (se 4 (by rfl) ⟨134100, by rfl⟩ : syracuseStep 1430405 = 268201) (by norm_num)
theorem B635789 : Blo 421773 635789 := bbase (se 3 (by rfl) ⟨119210, by rfl⟩ : syracuseStep 635789 = 238421) (by norm_num)
theorem B955277 : Blo 421773 955277 := bbase (se 3 (by rfl) ⟨179114, by rfl⟩ : syracuseStep 955277 = 358229) (by norm_num)
theorem B3208085 : Blo 421773 3208085 := bbase (se 6 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 3208085 = 150379) (by norm_num)
theorem B643997 : Blo 421773 643997 := bbase (se 3 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 643997 = 241499) (by norm_num)
theorem B635813 : Blo 421773 635813 := bbase (se 4 (by rfl) ⟨59607, by rfl⟩ : syracuseStep 635813 = 119215) (by norm_num)
theorem B635837 : Blo 421773 635837 := bbase (se 3 (by rfl) ⟨119219, by rfl⟩ : syracuseStep 635837 = 238439) (by norm_num)
theorem B644045 : Blo 421773 644045 := bbase (se 3 (by rfl) ⟨120758, by rfl⟩ : syracuseStep 644045 = 241517) (by norm_num)
theorem B635861 : Blo 421773 635861 := bbase (se 7 (by rfl) ⟨7451, by rfl⟩ : syracuseStep 635861 = 14903) (by norm_num)
theorem B6116309 : Blo 421773 6116309 := bbase (se 7 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 6116309 = 143351) (by norm_num)
theorem B955349 : Blo 421773 955349 := bbase (se 7 (by rfl) ⟨11195, by rfl⟩ : syracuseStep 955349 = 22391) (by norm_num)
theorem B1610725 : Blo 421773 1610725 := bbase (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) (by norm_num)
theorem B635885 : Blo 421773 635885 := bbase (se 3 (by rfl) ⟨119228, by rfl⟩ : syracuseStep 635885 = 238457) (by norm_num)
theorem B635909 : Blo 421773 635909 := bbase (se 4 (by rfl) ⟨59616, by rfl⟩ : syracuseStep 635909 = 119233) (by norm_num)
theorem B1356821 : Blo 421773 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B635933 : Blo 421773 635933 := bbase (se 3 (by rfl) ⟨119237, by rfl⟩ : syracuseStep 635933 = 238475) (by norm_num)
theorem B955421 : Blo 421773 955421 := bbase (se 3 (by rfl) ⟨179141, by rfl⟩ : syracuseStep 955421 = 358283) (by norm_num)
theorem B1143845 : Blo 421773 1143845 := bbase (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) (by norm_num)
theorem B635957 : Blo 421773 635957 := bbase (se 5 (by rfl) ⟨29810, by rfl⟩ : syracuseStep 635957 = 59621) (by norm_num)
theorem B635981 : Blo 421773 635981 := bbase (se 3 (by rfl) ⟨119246, by rfl⟩ : syracuseStep 635981 = 238493) (by norm_num)
theorem B439393 : Blo 421773 439393 := bbase (se 2 (by rfl) ⟨164772, by rfl⟩ : syracuseStep 439393 = 329545) (by norm_num)
theorem B636005 : Blo 421773 636005 := bbase (se 4 (by rfl) ⟨59625, by rfl⟩ : syracuseStep 636005 = 119251) (by norm_num)
theorem B955493 : Blo 421773 955493 := bbase (se 4 (by rfl) ⟨89577, by rfl⟩ : syracuseStep 955493 = 179155) (by norm_num)
theorem B636029 : Blo 421773 636029 := bbase (se 3 (by rfl) ⟨119255, by rfl⟩ : syracuseStep 636029 = 238511) (by norm_num)
theorem B1201301 : Blo 421773 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B963733 : Blo 421773 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B636053 : Blo 421773 636053 := bbase (se 6 (by rfl) ⟨14907, by rfl⟩ : syracuseStep 636053 = 29815) (by norm_num)
theorem B603293 : Blo 421773 603293 := bbase (se 3 (by rfl) ⟨113117, by rfl⟩ : syracuseStep 603293 = 226235) (by norm_num)
theorem B636077 : Blo 421773 636077 := bbase (se 3 (by rfl) ⟨119264, by rfl⟩ : syracuseStep 636077 = 238529) (by norm_num)
theorem B955565 : Blo 421773 955565 := bbase (se 3 (by rfl) ⟨179168, by rfl⟩ : syracuseStep 955565 = 358337) (by norm_num)
theorem B1807541 : Blo 421773 1807541 := bbase (se 5 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 1807541 = 169457) (by norm_num)
theorem B636101 : Blo 421773 636101 := bbase (se 4 (by rfl) ⟨59634, by rfl⟩ : syracuseStep 636101 = 119269) (by norm_num)
theorem B1070293 : Blo 421773 1070293 := bbase (se 7 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 1070293 = 25085) (by norm_num)
theorem B636125 : Blo 421773 636125 := bbase (se 3 (by rfl) ⟨119273, by rfl⟩ : syracuseStep 636125 = 238547) (by norm_num)
theorem B906461 : Blo 421773 906461 := bbase (se 3 (by rfl) ⟨169961, by rfl⟩ : syracuseStep 906461 = 339923) (by norm_num)
theorem B1373429 : Blo 421773 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B636149 : Blo 421773 636149 := bbase (se 5 (by rfl) ⟨29819, by rfl⟩ : syracuseStep 636149 = 59639) (by norm_num)
theorem B955637 : Blo 421773 955637 := bbase (se 5 (by rfl) ⟨44795, by rfl⟩ : syracuseStep 955637 = 89591) (by norm_num)
theorem B963845 : Blo 421773 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B636173 : Blo 421773 636173 := bbase (se 3 (by rfl) ⟨119282, by rfl⟩ : syracuseStep 636173 = 238565) (by norm_num)
theorem B1611029 : Blo 421773 1611029 := bbase (se 6 (by rfl) ⟨37758, by rfl⟩ : syracuseStep 1611029 = 75517) (by norm_num)
theorem B636197 : Blo 421773 636197 := bbase (se 4 (by rfl) ⟨59643, by rfl⟩ : syracuseStep 636197 = 119287) (by norm_num)
theorem B1430837 : Blo 421773 1430837 := bbase (se 5 (by rfl) ⟨67070, by rfl⟩ : syracuseStep 1430837 = 134141) (by norm_num)
theorem B636221 : Blo 421773 636221 := bbase (se 3 (by rfl) ⟨119291, by rfl⟩ : syracuseStep 636221 = 238583) (by norm_num)
theorem B955709 : Blo 421773 955709 := bbase (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) (by norm_num)
theorem B1070405 : Blo 421773 1070405 := bbase (se 4 (by rfl) ⟨100350, by rfl⟩ : syracuseStep 1070405 = 200701) (by norm_num)
theorem B636245 : Blo 421773 636245 := bbase (se 13 (by rfl) ⟨116, by rfl⟩ : syracuseStep 636245 = 233) (by norm_num)
theorem B11621717 : Blo 421773 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B636269 : Blo 421773 636269 := bbase (se 3 (by rfl) ⟨119300, by rfl⟩ : syracuseStep 636269 = 238601) (by norm_num)
theorem B1602949 : Blo 421773 1602949 := bbase (se 4 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 1602949 = 300553) (by norm_num)
theorem B636293 : Blo 421773 636293 := bbase (se 4 (by rfl) ⟨59652, by rfl⟩ : syracuseStep 636293 = 119305) (by norm_num)
theorem B636317 : Blo 421773 636317 := bbase (se 3 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 636317 = 238619) (by norm_num)
theorem B636341 : Blo 421773 636341 := bbase (se 5 (by rfl) ⟨29828, by rfl⟩ : syracuseStep 636341 = 59657) (by norm_num)
theorem B636365 : Blo 421773 636365 := bbase (se 3 (by rfl) ⟨119318, by rfl⟩ : syracuseStep 636365 = 238637) (by norm_num)
theorem B1807829 : Blo 421773 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B906709 : Blo 421773 906709 := bbase (se 7 (by rfl) ⟨10625, by rfl⟩ : syracuseStep 906709 = 21251) (by norm_num)
theorem B636389 : Blo 421773 636389 := bbase (se 4 (by rfl) ⟨59661, by rfl⟩ : syracuseStep 636389 = 119323) (by norm_num)
theorem B636413 : Blo 421773 636413 := bbase (se 3 (by rfl) ⟨119327, by rfl⟩ : syracuseStep 636413 = 238655) (by norm_num)
theorem B1218053 : Blo 421773 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1070597 : Blo 421773 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B636437 : Blo 421773 636437 := bbase (se 6 (by rfl) ⟨14916, by rfl⟩ : syracuseStep 636437 = 29833) (by norm_num)
theorem B1087013 : Blo 421773 1087013 := bbase (se 4 (by rfl) ⟨101907, by rfl⟩ : syracuseStep 1087013 = 203815) (by norm_num)
theorem B1529381 : Blo 421773 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B636461 : Blo 421773 636461 := bbase (se 3 (by rfl) ⟨119336, by rfl⟩ : syracuseStep 636461 = 238673) (by norm_num)
theorem B636485 : Blo 421773 636485 := bbase (se 4 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 636485 = 119341) (by norm_num)
theorem B636509 : Blo 421773 636509 := bbase (se 3 (by rfl) ⟨119345, by rfl⟩ : syracuseStep 636509 = 238691) (by norm_num)
theorem B636533 : Blo 421773 636533 := bbase (se 5 (by rfl) ⟨29837, by rfl⟩ : syracuseStep 636533 = 59675) (by norm_num)
theorem B677501 : Blo 421773 677501 := bbase (se 3 (by rfl) ⟨127031, by rfl⟩ : syracuseStep 677501 = 254063) (by norm_num)
theorem B636557 : Blo 421773 636557 := bbase (se 3 (by rfl) ⟨119354, by rfl⟩ : syracuseStep 636557 = 238709) (by norm_num)
theorem B2717333 : Blo 421773 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B636581 : Blo 421773 636581 := bbase (se 4 (by rfl) ⟨59679, by rfl⟩ : syracuseStep 636581 = 119359) (by norm_num)
theorem B1603253 : Blo 421773 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B636605 : Blo 421773 636605 := bbase (se 3 (by rfl) ⟨119363, by rfl⟩ : syracuseStep 636605 = 238727) (by norm_num)
theorem B1717957 : Blo 421773 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B636629 : Blo 421773 636629 := bbase (se 7 (by rfl) ⟨7460, by rfl⟩ : syracuseStep 636629 = 14921) (by norm_num)
theorem B1431269 : Blo 421773 1431269 := bbase (se 4 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 1431269 = 268363) (by norm_num)
theorem B636653 : Blo 421773 636653 := bbase (se 3 (by rfl) ⟨119372, by rfl⟩ : syracuseStep 636653 = 238745) (by norm_num)
theorem B3847925 : Blo 421773 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B636677 : Blo 421773 636677 := bbase (se 4 (by rfl) ⟨59688, by rfl⟩ : syracuseStep 636677 = 119377) (by norm_num)
theorem B2414357 : Blo 421773 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B636701 : Blo 421773 636701 := bbase (se 3 (by rfl) ⟨119381, by rfl⟩ : syracuseStep 636701 = 238763) (by norm_num)
theorem B2029349 : Blo 421773 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B636725 : Blo 421773 636725 := bbase (se 5 (by rfl) ⟨29846, by rfl⟩ : syracuseStep 636725 = 59693) (by norm_num)
theorem B677693 : Blo 421773 677693 := bbase (se 3 (by rfl) ⟨127067, by rfl⟩ : syracuseStep 677693 = 254135) (by norm_num)
theorem B2144069 : Blo 421773 2144069 := bbase (se 4 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 2144069 = 402013) (by norm_num)
theorem B636749 : Blo 421773 636749 := bbase (se 3 (by rfl) ⟨119390, by rfl⟩ : syracuseStep 636749 = 238781) (by norm_num)
theorem B1070941 : Blo 421773 1070941 := bbase (se 3 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 1070941 = 401603) (by norm_num)
theorem B636773 : Blo 421773 636773 := bbase (se 4 (by rfl) ⟨59697, by rfl⟩ : syracuseStep 636773 = 119395) (by norm_num)
theorem B636797 : Blo 421773 636797 := bbase (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) (by norm_num)
theorem B1202053 : Blo 421773 1202053 := bbase (se 4 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 1202053 = 225385) (by norm_num)
theorem B604045 : Blo 421773 604045 := bbase (se 3 (by rfl) ⟨113258, by rfl⟩ : syracuseStep 604045 = 226517) (by norm_num)
theorem B2406293 : Blo 421773 2406293 := bbase (se 6 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 2406293 = 112795) (by norm_num)
theorem B1357717 : Blo 421773 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B645013 : Blo 421773 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B636821 : Blo 421773 636821 := bbase (se 6 (by rfl) ⟨14925, by rfl⟩ : syracuseStep 636821 = 29851) (by norm_num)
theorem B636845 : Blo 421773 636845 := bbase (se 3 (by rfl) ⟨119408, by rfl⟩ : syracuseStep 636845 = 238817) (by norm_num)
theorem B636869 : Blo 421773 636869 := bbase (se 4 (by rfl) ⟨59706, by rfl⟩ : syracuseStep 636869 = 119413) (by norm_num)
theorem B1071053 : Blo 421773 1071053 := bbase (se 3 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 1071053 = 401645) (by norm_num)
theorem B636893 : Blo 421773 636893 := bbase (se 3 (by rfl) ⟨119417, by rfl⟩ : syracuseStep 636893 = 238835) (by norm_num)
theorem B636917 : Blo 421773 636917 := bbase (se 5 (by rfl) ⟨29855, by rfl⟩ : syracuseStep 636917 = 59711) (by norm_num)
theorem B636941 : Blo 421773 636941 := bbase (se 3 (by rfl) ⟨119426, by rfl⟩ : syracuseStep 636941 = 238853) (by norm_num)
theorem B636965 : Blo 421773 636965 := bbase (se 4 (by rfl) ⟨59715, by rfl⟩ : syracuseStep 636965 = 119431) (by norm_num)
theorem B636989 : Blo 421773 636989 := bbase (se 3 (by rfl) ⟨119435, by rfl⟩ : syracuseStep 636989 = 238871) (by norm_num)
theorem B800837 : Blo 421773 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B637013 : Blo 421773 637013 := bbase (se 8 (by rfl) ⟨3732, by rfl⟩ : syracuseStep 637013 = 7465) (by norm_num)
theorem B637037 : Blo 421773 637037 := bbase (se 3 (by rfl) ⟨119444, by rfl⟩ : syracuseStep 637037 = 238889) (by norm_num)
theorem B3479669 : Blo 421773 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B1423493 : Blo 421773 1423493 := bbase (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) (by norm_num)
theorem B637061 : Blo 421773 637061 := bbase (se 4 (by rfl) ⟨59724, by rfl⟩ : syracuseStep 637061 = 119449) (by norm_num)
theorem B1071245 : Blo 421773 1071245 := bbase (se 3 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 1071245 = 401717) (by norm_num)
theorem B1431701 : Blo 421773 1431701 := bbase (se 6 (by rfl) ⟨33555, by rfl⟩ : syracuseStep 1431701 = 67111) (by norm_num)
theorem B637085 : Blo 421773 637085 := bbase (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) (by norm_num)
theorem B637109 : Blo 421773 637109 := bbase (se 5 (by rfl) ⟨29864, by rfl⟩ : syracuseStep 637109 = 59729) (by norm_num)
theorem B1808581 : Blo 421773 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B735437 : Blo 421773 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B637133 : Blo 421773 637133 := bbase (se 3 (by rfl) ⟨119462, by rfl⟩ : syracuseStep 637133 = 238925) (by norm_num)
theorem B2136293 : Blo 421773 2136293 := bbase (se 4 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 2136293 = 400555) (by norm_num)
theorem B637157 : Blo 421773 637157 := bbase (se 4 (by rfl) ⟨59733, by rfl⟩ : syracuseStep 637157 = 119467) (by norm_num)
theorem B5773589 : Blo 421773 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B1358117 : Blo 421773 1358117 := bbase (se 4 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 1358117 = 254647) (by norm_num)
theorem B571717 : Blo 421773 571717 := bbase (se 4 (by rfl) ⟨53598, by rfl⟩ : syracuseStep 571717 = 107197) (by norm_num)
theorem B760141 : Blo 421773 760141 := bbase (se 3 (by rfl) ⟨142526, by rfl⟩ : syracuseStep 760141 = 285053) (by norm_num)
theorem B1628549 : Blo 421773 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B612749 : Blo 421773 612749 := bbase (se 3 (by rfl) ⟨114890, by rfl⟩ : syracuseStep 612749 = 229781) (by norm_num)
theorem B3627413 : Blo 421773 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B481717 : Blo 421773 481717 := bbase (se 5 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 481717 = 45161) (by norm_num)
theorem B481721 : Blo 421773 481721 := bbase (se 2 (by rfl) ⟨180645, by rfl⟩ : syracuseStep 481721 = 361291) (by norm_num)
theorem B1071589 : Blo 421773 1071589 := bbase (se 4 (by rfl) ⟨100461, by rfl⟩ : syracuseStep 1071589 = 200923) (by norm_num)
theorem B1161733 : Blo 421773 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B3619349 : Blo 421773 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B1423925 : Blo 421773 1423925 := bbase (se 5 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 1423925 = 133493) (by norm_num)
theorem B1432133 : Blo 421773 1432133 := bbase (se 4 (by rfl) ⟨134262, by rfl⟩ : syracuseStep 1432133 = 268525) (by norm_num)
theorem B1071701 : Blo 421773 1071701 := bbase (se 8 (by rfl) ⟨6279, by rfl⟩ : syracuseStep 1071701 = 12559) (by norm_num)
theorem B2038405 : Blo 421773 2038405 := bbase (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) (by norm_num)
theorem B2038421 : Blo 421773 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B465569 : Blo 421773 465569 := bbase (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) (by norm_num)
theorem B940709 : Blo 421773 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B965285 : Blo 421773 965285 := bbase (se 4 (by rfl) ⟨90495, by rfl⟩ : syracuseStep 965285 = 180991) (by norm_num)
theorem B1522357 : Blo 421773 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B949013 : Blo 421773 949013 := bbase (se 6 (by rfl) ⟨22242, by rfl⟩ : syracuseStep 949013 = 44485) (by norm_num)
theorem B1071893 : Blo 421773 1071893 := bbase (se 6 (by rfl) ⟨25122, by rfl⟩ : syracuseStep 1071893 = 50245) (by norm_num)
theorem B1530661 : Blo 421773 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B801589 : Blo 421773 801589 := bbase (se 5 (by rfl) ⟨37574, by rfl⟩ : syracuseStep 801589 = 75149) (by norm_num)
theorem B2292533 : Blo 421773 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B760661 : Blo 421773 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B949085 : Blo 421773 949085 := bbase (se 3 (by rfl) ⟨177953, by rfl⟩ : syracuseStep 949085 = 355907) (by norm_num)
theorem B949157 : Blo 421773 949157 := bbase (se 4 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 949157 = 177967) (by norm_num)
theorem B1809317 : Blo 421773 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B2415541 : Blo 421773 2415541 := bbase (se 5 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 2415541 = 226457) (by norm_num)
theorem B801733 : Blo 421773 801733 := bbase (se 4 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 801733 = 150325) (by norm_num)
theorem B1391573 : Blo 421773 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B1424357 : Blo 421773 1424357 := bbase (se 4 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 1424357 = 267067) (by norm_num)
theorem B949229 : Blo 421773 949229 := bbase (se 3 (by rfl) ⟨177980, by rfl⟩ : syracuseStep 949229 = 355961) (by norm_num)
theorem B1432565 : Blo 421773 1432565 := bbase (se 5 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 1432565 = 134303) (by norm_num)
theorem B859133 : Blo 421773 859133 := bbase (se 3 (by rfl) ⟨161087, by rfl⟩ : syracuseStep 859133 = 322175) (by norm_num)
theorem B2178085 : Blo 421773 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B916525 : Blo 421773 916525 := bbase (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) (by norm_num)
theorem B949301 : Blo 421773 949301 := bbase (se 5 (by rfl) ⟨44498, by rfl⟩ : syracuseStep 949301 = 88997) (by norm_num)
theorem B457813 : Blo 421773 457813 := bbase (se 8 (by rfl) ⟨2682, by rfl⟩ : syracuseStep 457813 = 5365) (by norm_num)
theorem B2145365 : Blo 421773 2145365 := bbase (se 8 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 2145365 = 25141) (by norm_num)
theorem B801893 : Blo 421773 801893 := bbase (se 4 (by rfl) ⟨75177, by rfl⟩ : syracuseStep 801893 = 150355) (by norm_num)
theorem B679013 : Blo 421773 679013 := bbase (se 4 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 679013 = 127315) (by norm_num)
theorem B1072237 : Blo 421773 1072237 := bbase (se 3 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 1072237 = 402089) (by norm_num)
theorem B1055861 : Blo 421773 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B949373 : Blo 421773 949373 := bbase (se 3 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 949373 = 356015) (by norm_num)
theorem B711821 : Blo 421773 711821 := bbase (se 3 (by rfl) ⟨133466, by rfl⟩ : syracuseStep 711821 = 266933) (by norm_num)
theorem B949445 : Blo 421773 949445 := bbase (se 4 (by rfl) ⟨89010, by rfl⟩ : syracuseStep 949445 = 178021) (by norm_num)
theorem B679109 : Blo 421773 679109 := bbase (se 4 (by rfl) ⟨63666, by rfl⟩ : syracuseStep 679109 = 127333) (by norm_num)
theorem B1072349 : Blo 421773 1072349 := bbase (se 3 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 1072349 = 402131) (by norm_num)
theorem B679141 : Blo 421773 679141 := bbase (se 4 (by rfl) ⟨63669, by rfl⟩ : syracuseStep 679141 = 127339) (by norm_num)
theorem B1015021 : Blo 421773 1015021 := bbase (se 3 (by rfl) ⟨190316, by rfl⟩ : syracuseStep 1015021 = 380633) (by norm_num)
theorem B802037 : Blo 421773 802037 := bbase (se 5 (by rfl) ⟨37595, by rfl⟩ : syracuseStep 802037 = 75191) (by norm_num)
theorem B507145 : Blo 421773 507145 := bbase (se 2 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 507145 = 380359) (by norm_num)
theorem B711949 : Blo 421773 711949 := bbase (se 3 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 711949 = 266981) (by norm_num)
theorem B949517 : Blo 421773 949517 := bbase (se 3 (by rfl) ⟨178034, by rfl⟩ : syracuseStep 949517 = 356069) (by norm_num)
theorem B752933 : Blo 421773 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B687421 : Blo 421773 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B949589 : Blo 421773 949589 := bbase (se 11 (by rfl) ⟨695, by rfl⟩ : syracuseStep 949589 = 1391) (by norm_num)
theorem B712037 : Blo 421773 712037 := bbase (se 4 (by rfl) ⟨66753, by rfl⟩ : syracuseStep 712037 = 133507) (by norm_num)
theorem B1424789 : Blo 421773 1424789 := bbase (se 6 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 1424789 = 66787) (by norm_num)
theorem B4078997 : Blo 421773 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B949661 : Blo 421773 949661 := bbase (se 3 (by rfl) ⟨178061, by rfl⟩ : syracuseStep 949661 = 356123) (by norm_num)
theorem B1072541 : Blo 421773 1072541 := bbase (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) (by norm_num)
theorem B474529 : Blo 421773 474529 := bbase (se 2 (by rfl) ⟨177948, by rfl⟩ : syracuseStep 474529 = 355897) (by norm_num)
theorem B1432997 : Blo 421773 1432997 := bbase (se 4 (by rfl) ⟨134343, by rfl⟩ : syracuseStep 1432997 = 268687) (by norm_num)
theorem B474565 : Blo 421773 474565 := bbase (se 4 (by rfl) ⟨44490, by rfl⟩ : syracuseStep 474565 = 88981) (by norm_num)
theorem B712165 : Blo 421773 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B949733 : Blo 421773 949733 := bbase (se 4 (by rfl) ⟨89037, by rfl⟩ : syracuseStep 949733 = 178075) (by norm_num)
theorem B474601 : Blo 421773 474601 := bbase (se 2 (by rfl) ⟨177975, by rfl⟩ : syracuseStep 474601 = 355951) (by norm_num)
theorem B2137589 : Blo 421773 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B474637 : Blo 421773 474637 := bbase (se 3 (by rfl) ⟨88994, by rfl⟩ : syracuseStep 474637 = 177989) (by norm_num)
theorem B802325 : Blo 421773 802325 := bbase (se 6 (by rfl) ⟨18804, by rfl⟩ : syracuseStep 802325 = 37609) (by norm_num)
theorem B949805 : Blo 421773 949805 := bbase (se 3 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 949805 = 356177) (by norm_num)
theorem B474673 : Blo 421773 474673 := bbase (se 2 (by rfl) ⟨178002, by rfl⟩ : syracuseStep 474673 = 356005) (by norm_num)
theorem B3055157 : Blo 421773 3055157 := bbase (se 5 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 3055157 = 286421) (by norm_num)
theorem B712253 : Blo 421773 712253 := bbase (se 3 (by rfl) ⟨133547, by rfl⟩ : syracuseStep 712253 = 267095) (by norm_num)
theorem B474709 : Blo 421773 474709 := bbase (se 8 (by rfl) ⟨2781, by rfl⟩ : syracuseStep 474709 = 5563) (by norm_num)
theorem B949877 : Blo 421773 949877 := bbase (se 5 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 949877 = 89051) (by norm_num)
theorem B474745 : Blo 421773 474745 := bbase (se 2 (by rfl) ⟨178029, by rfl⟩ : syracuseStep 474745 = 356059) (by norm_num)
theorem B474781 : Blo 421773 474781 := bbase (se 3 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 474781 = 178043) (by norm_num)
theorem B802477 : Blo 421773 802477 := bbase (se 3 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 802477 = 300929) (by norm_num)
theorem B712381 : Blo 421773 712381 := bbase (se 3 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 712381 = 267143) (by norm_num)
theorem B949949 : Blo 421773 949949 := bbase (se 3 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 949949 = 356231) (by norm_num)
theorem B474817 : Blo 421773 474817 := bbase (se 2 (by rfl) ⟨178056, by rfl⟩ : syracuseStep 474817 = 356113) (by norm_num)
theorem B1711813 : Blo 421773 1711813 := bbase (se 4 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 1711813 = 320965) (by norm_num)
theorem B474853 : Blo 421773 474853 := bbase (se 4 (by rfl) ⟨44517, by rfl⟩ : syracuseStep 474853 = 89035) (by norm_num)
theorem B1605365 : Blo 421773 1605365 := bbase (se 5 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 1605365 = 150503) (by norm_num)
theorem B1072885 : Blo 421773 1072885 := bbase (se 5 (by rfl) ⟨50291, by rfl⟩ : syracuseStep 1072885 = 100583) (by norm_num)
theorem B950021 : Blo 421773 950021 := bbase (se 4 (by rfl) ⟨89064, by rfl⟩ : syracuseStep 950021 = 178129) (by norm_num)
theorem B474889 : Blo 421773 474889 := bbase (se 2 (by rfl) ⟨178083, by rfl⟩ : syracuseStep 474889 = 356167) (by norm_num)
theorem B712469 : Blo 421773 712469 := bbase (se 6 (by rfl) ⟨16698, by rfl⟩ : syracuseStep 712469 = 33397) (by norm_num)
theorem B474925 : Blo 421773 474925 := bbase (se 3 (by rfl) ⟨89048, by rfl⟩ : syracuseStep 474925 = 178097) (by norm_num)
theorem B1425221 : Blo 421773 1425221 := bbase (se 4 (by rfl) ⟨133614, by rfl⟩ : syracuseStep 1425221 = 267229) (by norm_num)
theorem B950093 : Blo 421773 950093 := bbase (se 3 (by rfl) ⟨178142, by rfl⟩ : syracuseStep 950093 = 356285) (by norm_num)
theorem B474961 : Blo 421773 474961 := bbase (se 2 (by rfl) ⟨178110, by rfl⟩ : syracuseStep 474961 = 356221) (by norm_num)
theorem B1433429 : Blo 421773 1433429 := bbase (se 9 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 1433429 = 8399) (by norm_num)
theorem B1072997 : Blo 421773 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B474997 : Blo 421773 474997 := bbase (se 5 (by rfl) ⟨22265, by rfl⟩ : syracuseStep 474997 = 44531) (by norm_num)
theorem B712597 : Blo 421773 712597 := bbase (se 6 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 712597 = 33403) (by norm_num)
theorem B950165 : Blo 421773 950165 := bbase (se 6 (by rfl) ⟨22269, by rfl⟩ : syracuseStep 950165 = 44539) (by norm_num)
theorem B475033 : Blo 421773 475033 := bbase (se 2 (by rfl) ⟨178137, by rfl⟩ : syracuseStep 475033 = 356275) (by norm_num)
theorem B1089445 : Blo 421773 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B901037 : Blo 421773 901037 := bbase (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) (by norm_num)
theorem B475069 : Blo 421773 475069 := bbase (se 3 (by rfl) ⟨89075, by rfl⟩ : syracuseStep 475069 = 178151) (by norm_num)
theorem B450505 : Blo 421773 450505 := bbase (se 2 (by rfl) ⟨168939, by rfl⟩ : syracuseStep 450505 = 337879) (by norm_num)
theorem B950237 : Blo 421773 950237 := bbase (se 3 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 950237 = 356339) (by norm_num)
theorem B802781 : Blo 421773 802781 := bbase (se 3 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 802781 = 301043) (by norm_num)
theorem B475105 : Blo 421773 475105 := bbase (se 2 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 475105 = 356329) (by norm_num)
theorem B712685 : Blo 421773 712685 := bbase (se 3 (by rfl) ⟨133628, by rfl⟩ : syracuseStep 712685 = 267257) (by norm_num)
theorem B1351669 : Blo 421773 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B712705 : Blo 421773 712705 := bstep (se 2 (by rfl) ⟨267264, by rfl⟩ : syracuseStep 712705 = 534529) B534529
theorem B802819 : Blo 421773 802819 := bstep (se 1 (by rfl) ⟨602114, by rfl⟩ : syracuseStep 802819 = 1204229) B1204229
theorem B712739 : Blo 421773 712739 := bstep (se 1 (by rfl) ⟨534554, by rfl⟩ : syracuseStep 712739 = 1069109) B1069109
theorem B802865 : Blo 421773 802865 := bstep (se 2 (by rfl) ⟨301074, by rfl⟩ : syracuseStep 802865 = 602149) B602149
theorem B1466435 : Blo 421773 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B2408525 : Blo 421773 2408525 := bstep (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) B903197
theorem B680051 : Blo 421773 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B475267 : Blo 421773 475267 := bstep (se 1 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 475267 = 712901) B712901
theorem B8781965 : Blo 421773 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B950417 : Blo 421773 950417 := bstep (se 2 (by rfl) ⟨356406, by rfl⟩ : syracuseStep 950417 = 712813) B712813
theorem B950435 : Blo 421773 950435 := bstep (se 1 (by rfl) ⟨712826, by rfl⟩ : syracuseStep 950435 = 1425653) B1425653
theorem B712867 : Blo 421773 712867 := bstep (se 1 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 712867 = 1069301) B1069301
theorem B2416817 : Blo 421773 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B475411 : Blo 421773 475411 := bstep (se 1 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 475411 = 713117) B713117
theorem B713009 : Blo 421773 713009 := bstep (se 2 (by rfl) ⟨267378, by rfl⟩ : syracuseStep 713009 = 534757) B534757
theorem B459059 : Blo 421773 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B901489 : Blo 421773 901489 := bstep (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) B676117
theorem B475555 : Blo 421773 475555 := bstep (se 1 (by rfl) ⟨356666, by rfl⟩ : syracuseStep 475555 = 713333) B713333
theorem B950705 : Blo 421773 950705 := bstep (se 2 (by rfl) ⟨356514, by rfl⟩ : syracuseStep 950705 = 713029) B713029
theorem B713137 : Blo 421773 713137 := bstep (se 2 (by rfl) ⟨267426, by rfl⟩ : syracuseStep 713137 = 534853) B534853
theorem B950723 : Blo 421773 950723 := bstep (se 1 (by rfl) ⟨713042, by rfl⟩ : syracuseStep 950723 = 1426085) B1426085
theorem B803267 : Blo 421773 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B1425869 : Blo 421773 1425869 := bstep (se 3 (by rfl) ⟨267350, by rfl⟩ : syracuseStep 1425869 = 534701) B534701
theorem B713171 : Blo 421773 713171 := bstep (se 1 (by rfl) ⟨534878, by rfl⟩ : syracuseStep 713171 = 1069757) B1069757
theorem B1425923 : Blo 421773 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B1810957 : Blo 421773 1810957 := bstep (se 3 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 1810957 = 679109) B679109
theorem B1204753 : Blo 421773 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B475699 : Blo 421773 475699 := bstep (se 1 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 475699 = 713549) B713549
theorem B713299 : Blo 421773 713299 := bstep (se 1 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 713299 = 1069949) B1069949
theorem B2138723 : Blo 421773 2138723 := bstep (se 1 (by rfl) ⟨1604042, by rfl⟩ : syracuseStep 2138723 = 3208085) B3208085
theorem B2040461 : Blo 421773 2040461 := bstep (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) B765173
theorem B1548977 : Blo 421773 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B475843 : Blo 421773 475843 := bstep (se 1 (by rfl) ⟨356882, by rfl⟩ : syracuseStep 475843 = 713765) B713765
theorem B762563 : Blo 421773 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B3211973 : Blo 421773 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B950993 : Blo 421773 950993 := bstep (se 2 (by rfl) ⟨356622, by rfl⟩ : syracuseStep 950993 = 713245) B713245
theorem B713441 : Blo 421773 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B951011 : Blo 421773 951011 := bstep (se 1 (by rfl) ⟨713258, by rfl⟩ : syracuseStep 951011 = 1426517) B1426517
theorem B1426193 : Blo 421773 1426193 := bstep (se 2 (by rfl) ⟨534822, by rfl⟩ : syracuseStep 1426193 = 1069645) B1069645
theorem B1205027 : Blo 421773 1205027 := bstep (se 1 (by rfl) ⟨903770, by rfl⟩ : syracuseStep 1205027 = 1807541) B1807541
theorem B1073969 : Blo 421773 1073969 := bstep (se 2 (by rfl) ⟨402738, by rfl⟩ : syracuseStep 1073969 = 805477) B805477
theorem B2040653 : Blo 421773 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B475987 : Blo 421773 475987 := bstep (se 1 (by rfl) ⟨356990, by rfl⟩ : syracuseStep 475987 = 713981) B713981
theorem B713569 : Blo 421773 713569 := bstep (se 2 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 713569 = 535177) B535177
theorem B1016675 : Blo 421773 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B1074019 : Blo 421773 1074019 := bstep (se 1 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 1074019 = 1611029) B1611029
theorem B713603 : Blo 421773 713603 := bstep (se 1 (by rfl) ⟨535202, by rfl⟩ : syracuseStep 713603 = 1070405) B1070405
theorem B967601 : Blo 421773 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B8119237 : Blo 421773 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B476131 : Blo 421773 476131 := bstep (se 1 (by rfl) ⟨357098, by rfl⟩ : syracuseStep 476131 = 714197) B714197
theorem B1205219 : Blo 421773 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B951281 : Blo 421773 951281 := bstep (se 2 (by rfl) ⟨356730, by rfl⟩ : syracuseStep 951281 = 713461) B713461
theorem B1074161 : Blo 421773 1074161 := bstep (se 2 (by rfl) ⟨402810, by rfl⟩ : syracuseStep 1074161 = 805621) B805621
theorem B812035 : Blo 421773 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B951299 : Blo 421773 951299 := bstep (se 1 (by rfl) ⟨713474, by rfl⟩ : syracuseStep 951299 = 1426949) B1426949
theorem B713731 : Blo 421773 713731 := bstep (se 1 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 713731 = 1070597) B1070597
theorem B1016867 : Blo 421773 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B2040881 : Blo 421773 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B451667 : Blo 421773 451667 := bstep (se 1 (by rfl) ⟨338750, by rfl⟩ : syracuseStep 451667 = 677501) B677501
theorem B1811555 : Blo 421773 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B4899953 : Blo 421773 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B476275 : Blo 421773 476275 := bstep (se 1 (by rfl) ⟨357206, by rfl⟩ : syracuseStep 476275 = 714413) B714413
theorem B713873 : Blo 421773 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B2565283 : Blo 421773 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1352899 : Blo 421773 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B5440709 : Blo 421773 5440709 := bstep (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) B1020133
theorem B2041037 : Blo 421773 2041037 := bstep (se 3 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 2041037 = 765389) B765389
theorem B1803491 : Blo 421773 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B3220721 : Blo 421773 3220721 := bstep (se 2 (by rfl) ⟨1207770, by rfl⟩ : syracuseStep 3220721 = 2415541) B2415541
theorem B476419 : Blo 421773 476419 := bstep (se 1 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 476419 = 714629) B714629
theorem B951569 : Blo 421773 951569 := bstep (se 2 (by rfl) ⟨356838, by rfl⟩ : syracuseStep 951569 = 713677) B713677
theorem B714001 : Blo 421773 714001 := bstep (se 2 (by rfl) ⟨267750, by rfl⟩ : syracuseStep 714001 = 535501) B535501
theorem B951587 : Blo 421773 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B1426733 : Blo 421773 1426733 := bstep (se 3 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 1426733 = 535025) B535025
theorem B2147633 : Blo 421773 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B714035 : Blo 421773 714035 := bstep (se 1 (by rfl) ⟨535526, by rfl⟩ : syracuseStep 714035 = 1071053) B1071053
theorem B2721073 : Blo 421773 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B804163 : Blo 421773 804163 := bstep (se 1 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 804163 = 1206245) B1206245
theorem B968003 : Blo 421773 968003 := bstep (se 1 (by rfl) ⟨726002, by rfl⟩ : syracuseStep 968003 = 1452005) B1452005
theorem B1426787 : Blo 421773 1426787 := bstep (se 1 (by rfl) ⟨1070090, by rfl⟩ : syracuseStep 1426787 = 2140181) B2140181
theorem B533891 : Blo 421773 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B2139533 : Blo 421773 2139533 := bstep (se 3 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 2139533 = 802325) B802325
theorem B1222033 : Blo 421773 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B476563 : Blo 421773 476563 := bstep (se 1 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 476563 = 714845) B714845
theorem B2319779 : Blo 421773 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B714163 : Blo 421773 714163 := bstep (se 1 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 714163 = 1071245) B1071245
theorem B3851717 : Blo 421773 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B804323 : Blo 421773 804323 := bstep (se 1 (by rfl) ⟨603242, by rfl⟩ : syracuseStep 804323 = 1206485) B1206485
theorem B476707 : Blo 421773 476707 := bstep (se 1 (by rfl) ⟨357530, by rfl⟩ : syracuseStep 476707 = 715061) B715061
theorem B951857 : Blo 421773 951857 := bstep (se 2 (by rfl) ⟨356946, by rfl⟩ : syracuseStep 951857 = 713893) B713893
theorem B714305 : Blo 421773 714305 := bstep (se 2 (by rfl) ⟨267864, by rfl⟩ : syracuseStep 714305 = 535729) B535729
theorem B951875 : Blo 421773 951875 := bstep (se 1 (by rfl) ⟨713906, by rfl⟩ : syracuseStep 951875 = 1427813) B1427813
theorem B1017443 : Blo 421773 1017443 := bstep (se 1 (by rfl) ⟨763082, by rfl⟩ : syracuseStep 1017443 = 1526165) B1526165
theorem B2418275 : Blo 421773 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B1427057 : Blo 421773 1427057 := bstep (se 2 (by rfl) ⟨535146, by rfl⟩ : syracuseStep 1427057 = 1070293) B1070293
theorem B3049073 : Blo 421773 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B1607309 : Blo 421773 1607309 := bstep (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) B602741
theorem B1353361 : Blo 421773 1353361 := bstep (se 2 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 1353361 = 1015021) B1015021
theorem B716755 : Blo 421773 716755 := bstep (se 1 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 716755 = 1075133) B1075133
theorem B542387 : Blo 421773 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B476851 : Blo 421773 476851 := bstep (se 1 (by rfl) ⟨357638, by rfl⟩ : syracuseStep 476851 = 715277) B715277
theorem B4966069 : Blo 421773 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B714433 : Blo 421773 714433 := bstep (se 2 (by rfl) ⟨267912, by rfl⟩ : syracuseStep 714433 = 535825) B535825
theorem B3049157 : Blo 421773 3049157 := bstep (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) B571717
theorem B714467 : Blo 421773 714467 := bstep (se 1 (by rfl) ⟨535850, by rfl⟩ : syracuseStep 714467 = 1071701) B1071701
theorem B1206029 : Blo 421773 1206029 := bstep (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) B452261
theorem B476995 : Blo 421773 476995 := bstep (se 1 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 476995 = 715493) B715493
theorem B952145 : Blo 421773 952145 := bstep (se 2 (by rfl) ⟨357054, by rfl⟩ : syracuseStep 952145 = 714109) B714109
theorem B632675 : Blo 421773 632675 := bstep (se 1 (by rfl) ⟨474506, by rfl⟩ : syracuseStep 632675 = 949013) B949013
theorem B952163 : Blo 421773 952163 := bstep (se 1 (by rfl) ⟨714122, by rfl⟩ : syracuseStep 952163 = 1428245) B1428245
theorem B714595 : Blo 421773 714595 := bstep (se 1 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 714595 = 1071893) B1071893
theorem B632705 : Blo 421773 632705 := bstep (se 2 (by rfl) ⟨237264, by rfl⟩ : syracuseStep 632705 = 474529) B474529
theorem B632723 : Blo 421773 632723 := bstep (se 1 (by rfl) ⟨474542, by rfl⟩ : syracuseStep 632723 = 949085) B949085
theorem B632753 : Blo 421773 632753 := bstep (se 2 (by rfl) ⟨237282, by rfl⟩ : syracuseStep 632753 = 474565) B474565
theorem B632771 : Blo 421773 632771 := bstep (se 1 (by rfl) ⟨474578, by rfl⟩ : syracuseStep 632771 = 949157) B949157
theorem B1206211 : Blo 421773 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B477139 : Blo 421773 477139 := bstep (se 1 (by rfl) ⟨357854, by rfl⟩ : syracuseStep 477139 = 715709) B715709
theorem B1075153 : Blo 421773 1075153 := bstep (se 2 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 1075153 = 806365) B806365
theorem B632801 : Blo 421773 632801 := bstep (se 2 (by rfl) ⟨237300, by rfl⟩ : syracuseStep 632801 = 474601) B474601
theorem B1017827 : Blo 421773 1017827 := bstep (se 1 (by rfl) ⟨763370, by rfl⟩ : syracuseStep 1017827 = 1526741) B1526741
theorem B714737 : Blo 421773 714737 := bstep (se 2 (by rfl) ⟨268026, by rfl⟩ : syracuseStep 714737 = 536053) B536053
theorem B632819 : Blo 421773 632819 := bstep (se 1 (by rfl) ⟨474614, by rfl⟩ : syracuseStep 632819 = 949229) B949229
theorem B632849 : Blo 421773 632849 := bstep (se 2 (by rfl) ⟨237318, by rfl⟩ : syracuseStep 632849 = 474637) B474637
theorem B509971 : Blo 421773 509971 := bstep (se 1 (by rfl) ⟨382478, by rfl⟩ : syracuseStep 509971 = 764957) B764957
theorem B632867 : Blo 421773 632867 := bstep (se 1 (by rfl) ⟨474650, by rfl⟩ : syracuseStep 632867 = 949301) B949301
theorem B632897 : Blo 421773 632897 := bstep (se 2 (by rfl) ⟨237336, by rfl⟩ : syracuseStep 632897 = 474673) B474673
theorem B534595 : Blo 421773 534595 := bstep (se 1 (by rfl) ⟨400946, by rfl⟩ : syracuseStep 534595 = 801893) B801893
theorem B452675 : Blo 421773 452675 := bstep (se 1 (by rfl) ⟨339506, by rfl⟩ : syracuseStep 452675 = 679013) B679013
theorem B632915 : Blo 421773 632915 := bstep (se 1 (by rfl) ⟨474686, by rfl⟩ : syracuseStep 632915 = 949373) B949373
theorem B428131 : Blo 421773 428131 := bstep (se 1 (by rfl) ⟨321098, by rfl⟩ : syracuseStep 428131 = 642197) B642197
theorem B477283 : Blo 421773 477283 := bstep (se 1 (by rfl) ⟨357962, by rfl⟩ : syracuseStep 477283 = 715925) B715925
theorem B632945 : Blo 421773 632945 := bstep (se 2 (by rfl) ⟨237354, by rfl⟩ : syracuseStep 632945 = 474709) B474709
theorem B952433 : Blo 421773 952433 := bstep (se 2 (by rfl) ⟨357162, by rfl⟩ : syracuseStep 952433 = 714325) B714325
theorem B428147 : Blo 421773 428147 := bstep (se 1 (by rfl) ⟨321110, by rfl⟩ : syracuseStep 428147 = 642221) B642221
theorem B714865 : Blo 421773 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B632963 : Blo 421773 632963 := bstep (se 1 (by rfl) ⟨474722, by rfl⟩ : syracuseStep 632963 = 949445) B949445
theorem B952451 : Blo 421773 952451 := bstep (se 1 (by rfl) ⟨714338, by rfl⟩ : syracuseStep 952451 = 1428677) B1428677
theorem B1427597 : Blo 421773 1427597 := bstep (se 3 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 1427597 = 535349) B535349
theorem B723089 : Blo 421773 723089 := bstep (se 2 (by rfl) ⟨271158, by rfl⟩ : syracuseStep 723089 = 542317) B542317
theorem B714899 : Blo 421773 714899 := bstep (se 1 (by rfl) ⟨536174, by rfl⟩ : syracuseStep 714899 = 1072349) B1072349
theorem B632993 : Blo 421773 632993 := bstep (se 2 (by rfl) ⟨237372, by rfl⟩ : syracuseStep 632993 = 474745) B474745
theorem B534691 : Blo 421773 534691 := bstep (se 1 (by rfl) ⟨401018, by rfl⟩ : syracuseStep 534691 = 802037) B802037
theorem B633011 : Blo 421773 633011 := bstep (se 1 (by rfl) ⟨474758, by rfl⟩ : syracuseStep 633011 = 949517) B949517
theorem B501955 : Blo 421773 501955 := bstep (se 1 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 501955 = 752933) B752933
theorem B1427651 : Blo 421773 1427651 := bstep (se 1 (by rfl) ⟨1070738, by rfl⟩ : syracuseStep 1427651 = 2141477) B2141477
theorem B633041 : Blo 421773 633041 := bstep (se 2 (by rfl) ⟨237390, by rfl⟩ : syracuseStep 633041 = 474781) B474781
theorem B633059 : Blo 421773 633059 := bstep (se 1 (by rfl) ⟨474794, by rfl⟩ : syracuseStep 633059 = 949589) B949589
theorem B477427 : Blo 421773 477427 := bstep (se 1 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 477427 = 716141) B716141
theorem B633089 : Blo 421773 633089 := bstep (se 2 (by rfl) ⟨237408, by rfl⟩ : syracuseStep 633089 = 474817) B474817
theorem B3041549 : Blo 421773 3041549 := bstep (se 3 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 3041549 = 1140581) B1140581
theorem B633107 : Blo 421773 633107 := bstep (se 1 (by rfl) ⟨474830, by rfl⟩ : syracuseStep 633107 = 949661) B949661
theorem B715027 : Blo 421773 715027 := bstep (se 1 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 715027 = 1072541) B1072541
theorem B633137 : Blo 421773 633137 := bstep (se 2 (by rfl) ⟨237426, by rfl⟩ : syracuseStep 633137 = 474853) B474853
theorem B633155 : Blo 421773 633155 := bstep (se 1 (by rfl) ⟨474866, by rfl⟩ : syracuseStep 633155 = 949733) B949733
theorem B633185 : Blo 421773 633185 := bstep (se 2 (by rfl) ⟨237444, by rfl⟩ : syracuseStep 633185 = 474889) B474889
theorem B633203 : Blo 421773 633203 := bstep (se 1 (by rfl) ⟨474902, by rfl⟩ : syracuseStep 633203 = 949805) B949805
theorem B477571 : Blo 421773 477571 := bstep (se 1 (by rfl) ⟨358178, by rfl⟩ : syracuseStep 477571 = 716357) B716357
theorem B2402693 : Blo 421773 2402693 := bstep (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) B450505
theorem B633233 : Blo 421773 633233 := bstep (se 2 (by rfl) ⟨237462, by rfl⟩ : syracuseStep 633233 = 474925) B474925
theorem B952721 : Blo 421773 952721 := bstep (se 2 (by rfl) ⟨357270, by rfl⟩ : syracuseStep 952721 = 714541) B714541
theorem B715169 : Blo 421773 715169 := bstep (se 2 (by rfl) ⟨268188, by rfl⟩ : syracuseStep 715169 = 536377) B536377
theorem B633251 : Blo 421773 633251 := bstep (se 1 (by rfl) ⟨474938, by rfl⟩ : syracuseStep 633251 = 949877) B949877
theorem B952739 : Blo 421773 952739 := bstep (se 1 (by rfl) ⟨714554, by rfl⟩ : syracuseStep 952739 = 1429109) B1429109
theorem B1206701 : Blo 421773 1206701 := bstep (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) B452513
theorem B1608113 : Blo 421773 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B633281 : Blo 421773 633281 := bstep (se 2 (by rfl) ⟨237480, by rfl⟩ : syracuseStep 633281 = 474961) B474961
theorem B1427921 : Blo 421773 1427921 := bstep (se 2 (by rfl) ⟨535470, by rfl⟩ : syracuseStep 1427921 = 1070941) B1070941
theorem B633299 : Blo 421773 633299 := bstep (se 1 (by rfl) ⟨474974, by rfl⟩ : syracuseStep 633299 = 949949) B949949
theorem B633329 : Blo 421773 633329 := bstep (se 2 (by rfl) ⟨237498, by rfl⟩ : syracuseStep 633329 = 474997) B474997
theorem B633347 : Blo 421773 633347 := bstep (se 1 (by rfl) ⟨475010, by rfl⟩ : syracuseStep 633347 = 950021) B950021
theorem B805393 : Blo 421773 805393 := bstep (se 2 (by rfl) ⟨302022, by rfl⟩ : syracuseStep 805393 = 604045) B604045
theorem B477715 : Blo 421773 477715 := bstep (se 1 (by rfl) ⟨358286, by rfl⟩ : syracuseStep 477715 = 716573) B716573
theorem B633377 : Blo 421773 633377 := bstep (se 2 (by rfl) ⟨237516, by rfl⟩ : syracuseStep 633377 = 475033) B475033
theorem B715297 : Blo 421773 715297 := bstep (se 2 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 715297 = 536473) B536473
theorem B1452593 : Blo 421773 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B633395 : Blo 421773 633395 := bstep (se 1 (by rfl) ⟨475046, by rfl⟩ : syracuseStep 633395 = 950093) B950093
theorem B715331 : Blo 421773 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B633425 : Blo 421773 633425 := bstep (se 2 (by rfl) ⟨237534, by rfl⟩ : syracuseStep 633425 = 475069) B475069
theorem B633443 : Blo 421773 633443 := bstep (se 1 (by rfl) ⟨475082, by rfl⟩ : syracuseStep 633443 = 950165) B950165
theorem B600691 : Blo 421773 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B633473 : Blo 421773 633473 := bstep (se 2 (by rfl) ⟨237552, by rfl⟩ : syracuseStep 633473 = 475105) B475105
theorem B1067651 : Blo 421773 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B5139085 : Blo 421773 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B633491 : Blo 421773 633491 := bstep (se 1 (by rfl) ⟨475118, by rfl⟩ : syracuseStep 633491 = 950237) B950237
theorem B535187 : Blo 421773 535187 := bstep (se 1 (by rfl) ⟨401390, by rfl⟩ : syracuseStep 535187 = 802781) B802781
theorem B477859 : Blo 421773 477859 := bstep (se 1 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 477859 = 716789) B716789
theorem B633521 : Blo 421773 633521 := bstep (se 2 (by rfl) ⟨237570, by rfl⟩ : syracuseStep 633521 = 475141) B475141
theorem B953009 : Blo 421773 953009 := bstep (se 2 (by rfl) ⟨357378, by rfl⟩ : syracuseStep 953009 = 714757) B714757
theorem B633539 : Blo 421773 633539 := bstep (se 1 (by rfl) ⟨475154, by rfl⟩ : syracuseStep 633539 = 950309) B950309
theorem B953027 : Blo 421773 953027 := bstep (se 1 (by rfl) ⟨714770, by rfl⟩ : syracuseStep 953027 = 1429541) B1429541
theorem B2714309 : Blo 421773 2714309 := bstep (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) B508933
theorem B715459 : Blo 421773 715459 := bstep (se 1 (by rfl) ⟨536594, by rfl⟩ : syracuseStep 715459 = 1073189) B1073189
theorem B600787 : Blo 421773 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B633569 : Blo 421773 633569 := bstep (se 2 (by rfl) ⟨237588, by rfl⟩ : syracuseStep 633569 = 475177) B475177
theorem B2149091 : Blo 421773 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B633587 : Blo 421773 633587 := bstep (se 1 (by rfl) ⟨475190, by rfl⟩ : syracuseStep 633587 = 950381) B950381
theorem B633617 : Blo 421773 633617 := bstep (se 2 (by rfl) ⟨237606, by rfl⟩ : syracuseStep 633617 = 475213) B475213
theorem B633635 : Blo 421773 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B1018673 : Blo 421773 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B633665 : Blo 421773 633665 := bstep (se 2 (by rfl) ⟨237624, by rfl⟩ : syracuseStep 633665 = 475249) B475249
theorem B1067843 : Blo 421773 1067843 := bstep (se 1 (by rfl) ⟨800882, by rfl⟩ : syracuseStep 1067843 = 1601765) B1601765
theorem B707395 : Blo 421773 707395 := bstep (se 1 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 707395 = 1061093) B1061093
theorem B715601 : Blo 421773 715601 := bstep (se 2 (by rfl) ⟨268350, by rfl⟩ : syracuseStep 715601 = 536701) B536701
theorem B633683 : Blo 421773 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B633713 : Blo 421773 633713 := bstep (se 2 (by rfl) ⟨237642, by rfl⟩ : syracuseStep 633713 = 475285) B475285
theorem B633731 : Blo 421773 633731 := bstep (se 1 (by rfl) ⟨475298, by rfl⟩ : syracuseStep 633731 = 950597) B950597
theorem B633761 : Blo 421773 633761 := bstep (se 2 (by rfl) ⟨237660, by rfl⟩ : syracuseStep 633761 = 475321) B475321
theorem B2411441 : Blo 421773 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B494515 : Blo 421773 494515 := bstep (se 1 (by rfl) ⟨370886, by rfl⟩ : syracuseStep 494515 = 741773) B741773
theorem B633779 : Blo 421773 633779 := bstep (se 1 (by rfl) ⟨475334, by rfl⟩ : syracuseStep 633779 = 950669) B950669
theorem B633809 : Blo 421773 633809 := bstep (se 2 (by rfl) ⟨237678, by rfl⟩ : syracuseStep 633809 = 475357) B475357
theorem B953297 : Blo 421773 953297 := bstep (se 2 (by rfl) ⟨357486, by rfl⟩ : syracuseStep 953297 = 714973) B714973
theorem B715729 : Blo 421773 715729 := bstep (se 2 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 715729 = 536797) B536797
theorem B633827 : Blo 421773 633827 := bstep (se 1 (by rfl) ⟨475370, by rfl⟩ : syracuseStep 633827 = 950741) B950741
theorem B953315 : Blo 421773 953315 := bstep (se 1 (by rfl) ⟨714986, by rfl⟩ : syracuseStep 953315 = 1429973) B1429973
theorem B1428461 : Blo 421773 1428461 := bstep (se 3 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 1428461 = 535673) B535673
theorem B1018865 : Blo 421773 1018865 := bstep (se 2 (by rfl) ⟨382074, by rfl⟩ : syracuseStep 1018865 = 764149) B764149
theorem B715763 : Blo 421773 715763 := bstep (se 1 (by rfl) ⟨536822, by rfl⟩ : syracuseStep 715763 = 1073645) B1073645
theorem B633857 : Blo 421773 633857 := bstep (se 2 (by rfl) ⟨237696, by rfl⟩ : syracuseStep 633857 = 475393) B475393
theorem B633875 : Blo 421773 633875 := bstep (se 1 (by rfl) ⟨475406, by rfl⟩ : syracuseStep 633875 = 950813) B950813
theorem B1428515 : Blo 421773 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B2403377 : Blo 421773 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B633905 : Blo 421773 633905 := bstep (se 2 (by rfl) ⟨237714, by rfl⟩ : syracuseStep 633905 = 475429) B475429
theorem B633923 : Blo 421773 633923 := bstep (se 1 (by rfl) ⟨475442, by rfl⟩ : syracuseStep 633923 = 950885) B950885
theorem B1608781 : Blo 421773 1608781 := bstep (se 3 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 1608781 = 603293) B603293
theorem B633953 : Blo 421773 633953 := bstep (se 2 (by rfl) ⟨237732, by rfl⟩ : syracuseStep 633953 = 475465) B475465
theorem B633971 : Blo 421773 633971 := bstep (se 1 (by rfl) ⟨475478, by rfl⟩ : syracuseStep 633971 = 950957) B950957
theorem B715891 : Blo 421773 715891 := bstep (se 1 (by rfl) ⟨536918, by rfl⟩ : syracuseStep 715891 = 1073837) B1073837
theorem B634001 : Blo 421773 634001 := bstep (se 2 (by rfl) ⟨237750, by rfl⟩ : syracuseStep 634001 = 475501) B475501
theorem B634019 : Blo 421773 634019 := bstep (se 1 (by rfl) ⟨475514, by rfl⟩ : syracuseStep 634019 = 951029) B951029
theorem B634049 : Blo 421773 634049 := bstep (se 2 (by rfl) ⟨237768, by rfl⟩ : syracuseStep 634049 = 475537) B475537
theorem B601283 : Blo 421773 601283 := bstep (se 1 (by rfl) ⟨450962, by rfl⟩ : syracuseStep 601283 = 901925) B901925
theorem B1961165 : Blo 421773 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B634067 : Blo 421773 634067 := bstep (se 1 (by rfl) ⟨475550, by rfl⟩ : syracuseStep 634067 = 951101) B951101
theorem B634097 : Blo 421773 634097 := bstep (se 2 (by rfl) ⟨237786, by rfl⟩ : syracuseStep 634097 = 475573) B475573
theorem B953585 : Blo 421773 953585 := bstep (se 2 (by rfl) ⟨357594, by rfl⟩ : syracuseStep 953585 = 715189) B715189
theorem B609539 : Blo 421773 609539 := bstep (se 1 (by rfl) ⟨457154, by rfl⟩ : syracuseStep 609539 = 914309) B914309
theorem B634115 : Blo 421773 634115 := bstep (se 1 (by rfl) ⟨475586, by rfl⟩ : syracuseStep 634115 = 951173) B951173
theorem B953603 : Blo 421773 953603 := bstep (se 1 (by rfl) ⟨715202, by rfl⟩ : syracuseStep 953603 = 1430405) B1430405
theorem B716033 : Blo 421773 716033 := bstep (se 2 (by rfl) ⟨268512, by rfl⟩ : syracuseStep 716033 = 537025) B537025
theorem B429331 : Blo 421773 429331 := bstep (se 1 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 429331 = 643997) B643997
theorem B634145 : Blo 421773 634145 := bstep (se 2 (by rfl) ⟨237804, by rfl⟩ : syracuseStep 634145 = 475609) B475609
theorem B1428785 : Blo 421773 1428785 := bstep (se 2 (by rfl) ⟨535794, by rfl⟩ : syracuseStep 1428785 = 1071589) B1071589
theorem B634163 : Blo 421773 634163 := bstep (se 1 (by rfl) ⟨475622, by rfl⟩ : syracuseStep 634163 = 951245) B951245
theorem B634193 : Blo 421773 634193 := bstep (se 2 (by rfl) ⟨237822, by rfl⟩ : syracuseStep 634193 = 475645) B475645
theorem B535891 : Blo 421773 535891 := bstep (se 1 (by rfl) ⟨401918, by rfl⟩ : syracuseStep 535891 = 803837) B803837
theorem B634211 : Blo 421773 634211 := bstep (se 1 (by rfl) ⟨475658, by rfl⟩ : syracuseStep 634211 = 951317) B951317
theorem B904547 : Blo 421773 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B634241 : Blo 421773 634241 := bstep (se 2 (by rfl) ⟨237840, by rfl⟩ : syracuseStep 634241 = 475681) B475681
theorem B716161 : Blo 421773 716161 := bstep (se 2 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 716161 = 537121) B537121
theorem B2436493 : Blo 421773 2436493 := bstep (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) B913685
theorem B634259 : Blo 421773 634259 := bstep (se 1 (by rfl) ⟨475694, by rfl⟩ : syracuseStep 634259 = 951389) B951389
theorem B716195 : Blo 421773 716195 := bstep (se 1 (by rfl) ⟨537146, by rfl⟩ : syracuseStep 716195 = 1074293) B1074293
theorem B634289 : Blo 421773 634289 := bstep (se 2 (by rfl) ⟨237858, by rfl⟩ : syracuseStep 634289 = 475717) B475717
theorem B978353 : Blo 421773 978353 := bstep (se 2 (by rfl) ⟨366882, by rfl⟩ : syracuseStep 978353 = 733765) B733765
theorem B535987 : Blo 421773 535987 := bstep (se 1 (by rfl) ⟨401990, by rfl⟩ : syracuseStep 535987 = 803981) B803981
theorem B634307 : Blo 421773 634307 := bstep (se 1 (by rfl) ⟨475730, by rfl⟩ : syracuseStep 634307 = 951461) B951461
theorem B1142225 : Blo 421773 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B634337 : Blo 421773 634337 := bstep (se 2 (by rfl) ⟨237876, by rfl⟩ : syracuseStep 634337 = 475753) B475753
theorem B3206627 : Blo 421773 3206627 := bstep (se 1 (by rfl) ⟨2404970, by rfl⟩ : syracuseStep 3206627 = 4809941) B4809941
theorem B634355 : Blo 421773 634355 := bstep (se 1 (by rfl) ⟨475766, by rfl⟩ : syracuseStep 634355 = 951533) B951533
theorem B642563 : Blo 421773 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B2149901 : Blo 421773 2149901 := bstep (se 3 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 2149901 = 806213) B806213
theorem B634385 : Blo 421773 634385 := bstep (se 2 (by rfl) ⟨237894, by rfl⟩ : syracuseStep 634385 = 475789) B475789
theorem B953873 : Blo 421773 953873 := bstep (se 2 (by rfl) ⟨357702, by rfl⟩ : syracuseStep 953873 = 715405) B715405
theorem B634403 : Blo 421773 634403 := bstep (se 1 (by rfl) ⟨475802, by rfl⟩ : syracuseStep 634403 = 951605) B951605
theorem B953891 : Blo 421773 953891 := bstep (se 1 (by rfl) ⟨715418, by rfl⟩ : syracuseStep 953891 = 1430837) B1430837
theorem B716323 : Blo 421773 716323 := bstep (se 1 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 716323 = 1074485) B1074485
theorem B634433 : Blo 421773 634433 := bstep (se 2 (by rfl) ⟨237912, by rfl⟩ : syracuseStep 634433 = 475825) B475825
theorem B1207885 : Blo 421773 1207885 := bstep (se 3 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 1207885 = 452957) B452957
theorem B634451 : Blo 421773 634451 := bstep (se 1 (by rfl) ⟨475838, by rfl⟩ : syracuseStep 634451 = 951677) B951677
theorem B634481 : Blo 421773 634481 := bstep (se 2 (by rfl) ⟨237930, by rfl⟩ : syracuseStep 634481 = 475861) B475861
theorem B634499 : Blo 421773 634499 := bstep (se 1 (by rfl) ⟨475874, by rfl⟩ : syracuseStep 634499 = 951749) B951749
theorem B634529 : Blo 421773 634529 := bstep (se 2 (by rfl) ⟨237948, by rfl⟩ : syracuseStep 634529 = 475897) B475897
theorem B1289891 : Blo 421773 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B716465 : Blo 421773 716465 := bstep (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) B537349
theorem B634547 : Blo 421773 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B5516981 : Blo 421773 5516981 := bstep (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) B517217
theorem B724675 : Blo 421773 724675 := bstep (se 1 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 724675 = 1087013) B1087013
theorem B1019587 : Blo 421773 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B1633997 : Blo 421773 1633997 := bstep (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) B612749
theorem B634577 : Blo 421773 634577 := bstep (se 2 (by rfl) ⟨237966, by rfl⟩ : syracuseStep 634577 = 475933) B475933
theorem B634595 : Blo 421773 634595 := bstep (se 1 (by rfl) ⟨475946, by rfl⟩ : syracuseStep 634595 = 951893) B951893
theorem B1068785 : Blo 421773 1068785 := bstep (se 2 (by rfl) ⟨400794, by rfl⟩ : syracuseStep 1068785 = 801589) B801589
theorem B634625 : Blo 421773 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B634643 : Blo 421773 634643 := bstep (se 1 (by rfl) ⟨475982, by rfl⟩ : syracuseStep 634643 = 951965) B951965
theorem B1068835 : Blo 421773 1068835 := bstep (se 1 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 1068835 = 1603253) B1603253
theorem B634673 : Blo 421773 634673 := bstep (se 2 (by rfl) ⟨238002, by rfl⟩ : syracuseStep 634673 = 476005) B476005
theorem B954161 : Blo 421773 954161 := bstep (se 2 (by rfl) ⟨357810, by rfl⟩ : syracuseStep 954161 = 715621) B715621
theorem B716593 : Blo 421773 716593 := bstep (se 2 (by rfl) ⟨268722, by rfl⟩ : syracuseStep 716593 = 537445) B537445
theorem B601921 : Blo 421773 601921 := bstep (se 2 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 601921 = 451441) B451441
theorem B634691 : Blo 421773 634691 := bstep (se 1 (by rfl) ⟨476018, by rfl⟩ : syracuseStep 634691 = 952037) B952037
theorem B954179 : Blo 421773 954179 := bstep (se 1 (by rfl) ⟨715634, by rfl⟩ : syracuseStep 954179 = 1431269) B1431269
theorem B1429325 : Blo 421773 1429325 := bstep (se 3 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 1429325 = 535997) B535997
theorem B618323 : Blo 421773 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B716627 : Blo 421773 716627 := bstep (se 1 (by rfl) ⟨537470, by rfl⟩ : syracuseStep 716627 = 1074941) B1074941
theorem B634721 : Blo 421773 634721 := bstep (se 2 (by rfl) ⟨238020, by rfl⟩ : syracuseStep 634721 = 476041) B476041
theorem B1609571 : Blo 421773 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B634739 : Blo 421773 634739 := bstep (se 1 (by rfl) ⟨476054, by rfl⟩ : syracuseStep 634739 = 952109) B952109
theorem B1429379 : Blo 421773 1429379 := bstep (se 1 (by rfl) ⟨1072034, by rfl⟩ : syracuseStep 1429379 = 2144069) B2144069
theorem B634769 : Blo 421773 634769 := bstep (se 2 (by rfl) ⟨238038, by rfl⟩ : syracuseStep 634769 = 476077) B476077
theorem B421779 : Blo 421773 421779 := bstep (se 1 (by rfl) ⟨316334, by rfl⟩ : syracuseStep 421779 = 632669) B632669
theorem B421795 : Blo 421773 421795 := bstep (se 1 (by rfl) ⟨316346, by rfl⟩ : syracuseStep 421795 = 632693) B632693
theorem B634787 : Blo 421773 634787 := bstep (se 1 (by rfl) ⟨476090, by rfl⟩ : syracuseStep 634787 = 952181) B952181
theorem B536483 : Blo 421773 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B1068977 : Blo 421773 1068977 := bstep (se 2 (by rfl) ⟨400866, by rfl⟩ : syracuseStep 1068977 = 801733) B801733
theorem B421811 : Blo 421773 421811 := bstep (se 1 (by rfl) ⟨316358, by rfl⟩ : syracuseStep 421811 = 632717) B632717
theorem B634817 : Blo 421773 634817 := bstep (se 2 (by rfl) ⟨238056, by rfl⟩ : syracuseStep 634817 = 476113) B476113
theorem B421827 : Blo 421773 421827 := bstep (se 1 (by rfl) ⟨316370, by rfl⟩ : syracuseStep 421827 = 632741) B632741
theorem B421843 : Blo 421773 421843 := bstep (se 1 (by rfl) ⟨316382, by rfl⟩ : syracuseStep 421843 = 632765) B632765
theorem B634835 : Blo 421773 634835 := bstep (se 1 (by rfl) ⟨476126, by rfl⟩ : syracuseStep 634835 = 952253) B952253
theorem B421859 : Blo 421773 421859 := bstep (se 1 (by rfl) ⟨316394, by rfl⟩ : syracuseStep 421859 = 632789) B632789
theorem B634865 : Blo 421773 634865 := bstep (se 2 (by rfl) ⟨238074, by rfl⟩ : syracuseStep 634865 = 476149) B476149
theorem B421875 : Blo 421773 421875 := bstep (se 1 (by rfl) ⟨316406, by rfl⟩ : syracuseStep 421875 = 632813) B632813
theorem B421891 : Blo 421773 421891 := bstep (se 1 (by rfl) ⟨316418, by rfl⟩ : syracuseStep 421891 = 632837) B632837
theorem B634883 : Blo 421773 634883 := bstep (se 1 (by rfl) ⟨476162, by rfl⟩ : syracuseStep 634883 = 952325) B952325
theorem B421907 : Blo 421773 421907 := bstep (se 1 (by rfl) ⟨316430, by rfl⟩ : syracuseStep 421907 = 632861) B632861
theorem B634913 : Blo 421773 634913 := bstep (se 2 (by rfl) ⟨238092, by rfl⟩ : syracuseStep 634913 = 476185) B476185
theorem B421923 : Blo 421773 421923 := bstep (se 1 (by rfl) ⟨316442, by rfl⟩ : syracuseStep 421923 = 632885) B632885
theorem B2904113 : Blo 421773 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B421939 : Blo 421773 421939 := bstep (se 1 (by rfl) ⟨316454, by rfl⟩ : syracuseStep 421939 = 632909) B632909
theorem B634931 : Blo 421773 634931 := bstep (se 1 (by rfl) ⟨476198, by rfl⟩ : syracuseStep 634931 = 952397) B952397
theorem B421955 : Blo 421773 421955 := bstep (se 1 (by rfl) ⟨316466, by rfl⟩ : syracuseStep 421955 = 632933) B632933
theorem B634961 : Blo 421773 634961 := bstep (se 2 (by rfl) ⟨238110, by rfl⟩ : syracuseStep 634961 = 476221) B476221
theorem B421971 : Blo 421773 421971 := bstep (se 1 (by rfl) ⟨316478, by rfl⟩ : syracuseStep 421971 = 632957) B632957
theorem B954449 : Blo 421773 954449 := bstep (se 2 (by rfl) ⟨357918, by rfl⟩ : syracuseStep 954449 = 715837) B715837
theorem B421987 : Blo 421773 421987 := bstep (se 1 (by rfl) ⟨316490, by rfl⟩ : syracuseStep 421987 = 632981) B632981
theorem B634979 : Blo 421773 634979 := bstep (se 1 (by rfl) ⟨476234, by rfl⟩ : syracuseStep 634979 = 952469) B952469
theorem B954467 : Blo 421773 954467 := bstep (se 1 (by rfl) ⟨715850, by rfl⟩ : syracuseStep 954467 = 1431701) B1431701
theorem B610417 : Blo 421773 610417 := bstep (se 2 (by rfl) ⟨228906, by rfl⟩ : syracuseStep 610417 = 457813) B457813
theorem B422003 : Blo 421773 422003 := bstep (se 1 (by rfl) ⟨316502, by rfl⟩ : syracuseStep 422003 = 633005) B633005
theorem B585857 : Blo 421773 585857 := bstep (se 2 (by rfl) ⟨219696, by rfl⟩ : syracuseStep 585857 = 439393) B439393
theorem B635009 : Blo 421773 635009 := bstep (se 2 (by rfl) ⟨238128, by rfl⟩ : syracuseStep 635009 = 476257) B476257
theorem B422019 : Blo 421773 422019 := bstep (se 1 (by rfl) ⟨316514, by rfl⟩ : syracuseStep 422019 = 633029) B633029
theorem B602257 : Blo 421773 602257 := bstep (se 2 (by rfl) ⟨225846, by rfl⟩ : syracuseStep 602257 = 451693) B451693
theorem B1429649 : Blo 421773 1429649 := bstep (se 2 (by rfl) ⟨536118, by rfl⟩ : syracuseStep 1429649 = 1072237) B1072237
theorem B422035 : Blo 421773 422035 := bstep (se 1 (by rfl) ⟨316526, by rfl⟩ : syracuseStep 422035 = 633053) B633053
theorem B635027 : Blo 421773 635027 := bstep (se 1 (by rfl) ⟨476270, by rfl⟩ : syracuseStep 635027 = 952541) B952541
theorem B422051 : Blo 421773 422051 := bstep (se 1 (by rfl) ⟨316538, by rfl⟩ : syracuseStep 422051 = 633077) B633077
theorem B635057 : Blo 421773 635057 := bstep (se 2 (by rfl) ⟨238146, by rfl⟩ : syracuseStep 635057 = 476293) B476293
theorem B422067 : Blo 421773 422067 := bstep (se 1 (by rfl) ⟨316550, by rfl⟩ : syracuseStep 422067 = 633101) B633101
theorem B422083 : Blo 421773 422083 := bstep (se 1 (by rfl) ⟨316562, by rfl⟩ : syracuseStep 422083 = 633125) B633125
theorem B635075 : Blo 421773 635075 := bstep (se 1 (by rfl) ⟨476306, by rfl⟩ : syracuseStep 635075 = 952613) B952613
theorem B905411 : Blo 421773 905411 := bstep (se 1 (by rfl) ⟨679058, by rfl⟩ : syracuseStep 905411 = 1358117) B1358117
theorem B422099 : Blo 421773 422099 := bstep (se 1 (by rfl) ⟨316574, by rfl⟩ : syracuseStep 422099 = 633149) B633149
theorem B635105 : Blo 421773 635105 := bstep (se 2 (by rfl) ⟨238164, by rfl⟩ : syracuseStep 635105 = 476329) B476329
theorem B422115 : Blo 421773 422115 := bstep (se 1 (by rfl) ⟨316586, by rfl⟩ : syracuseStep 422115 = 633173) B633173
theorem B2142449 : Blo 421773 2142449 := bstep (se 2 (by rfl) ⟨803418, by rfl⟩ : syracuseStep 2142449 = 1606837) B1606837
theorem B422131 : Blo 421773 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B635123 : Blo 421773 635123 := bstep (se 1 (by rfl) ⟨476342, by rfl⟩ : syracuseStep 635123 = 952685) B952685
theorem B422147 : Blo 421773 422147 := bstep (se 1 (by rfl) ⟨316610, by rfl⟩ : syracuseStep 422147 = 633221) B633221
theorem B1085699 : Blo 421773 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B635153 : Blo 421773 635153 := bstep (se 2 (by rfl) ⟨238182, by rfl⟩ : syracuseStep 635153 = 476365) B476365
theorem B422163 : Blo 421773 422163 := bstep (se 1 (by rfl) ⟨316622, by rfl⟩ : syracuseStep 422163 = 633245) B633245
theorem B422179 : Blo 421773 422179 := bstep (se 1 (by rfl) ⟨316634, by rfl⟩ : syracuseStep 422179 = 633269) B633269
theorem B635171 : Blo 421773 635171 := bstep (se 1 (by rfl) ⟨476378, by rfl⟩ : syracuseStep 635171 = 952757) B952757
theorem B1356077 : Blo 421773 1356077 := bstep (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) B508529
theorem B905521 : Blo 421773 905521 := bstep (se 2 (by rfl) ⟨339570, by rfl⟩ : syracuseStep 905521 = 679141) B679141
theorem B422195 : Blo 421773 422195 := bstep (se 1 (by rfl) ⟨316646, by rfl⟩ : syracuseStep 422195 = 633293) B633293
theorem B635201 : Blo 421773 635201 := bstep (se 2 (by rfl) ⟨238200, by rfl⟩ : syracuseStep 635201 = 476401) B476401
theorem B422211 : Blo 421773 422211 := bstep (se 1 (by rfl) ⟨316658, by rfl⟩ : syracuseStep 422211 = 633317) B633317
theorem B422227 : Blo 421773 422227 := bstep (se 1 (by rfl) ⟨316670, by rfl⟩ : syracuseStep 422227 = 633341) B633341
theorem B635219 : Blo 421773 635219 := bstep (se 1 (by rfl) ⟨476414, by rfl⟩ : syracuseStep 635219 = 952829) B952829
theorem B676193 : Blo 421773 676193 := bstep (se 2 (by rfl) ⟨253572, by rfl⟩ : syracuseStep 676193 = 507145) B507145
theorem B422243 : Blo 421773 422243 := bstep (se 1 (by rfl) ⟨316682, by rfl⟩ : syracuseStep 422243 = 633365) B633365
theorem B2412899 : Blo 421773 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B635249 : Blo 421773 635249 := bstep (se 2 (by rfl) ⟨238218, by rfl⟩ : syracuseStep 635249 = 476437) B476437
theorem B954737 : Blo 421773 954737 := bstep (se 2 (by rfl) ⟨358026, by rfl⟩ : syracuseStep 954737 = 716053) B716053
theorem B422259 : Blo 421773 422259 := bstep (se 1 (by rfl) ⟨316694, by rfl⟩ : syracuseStep 422259 = 633389) B633389
theorem B422275 : Blo 421773 422275 := bstep (se 1 (by rfl) ⟨316706, by rfl⟩ : syracuseStep 422275 = 633413) B633413
theorem B635267 : Blo 421773 635267 := bstep (se 1 (by rfl) ⟨476450, by rfl⟩ : syracuseStep 635267 = 952901) B952901
theorem B954755 : Blo 421773 954755 := bstep (se 1 (by rfl) ⟨716066, by rfl⟩ : syracuseStep 954755 = 1432133) B1432133
theorem B422291 : Blo 421773 422291 := bstep (se 1 (by rfl) ⟨316718, by rfl⟩ : syracuseStep 422291 = 633437) B633437
theorem B635297 : Blo 421773 635297 := bstep (se 2 (by rfl) ⟨238236, by rfl⟩ : syracuseStep 635297 = 476473) B476473
theorem B422307 : Blo 421773 422307 := bstep (se 1 (by rfl) ⟨316730, by rfl⟩ : syracuseStep 422307 = 633461) B633461
theorem B422323 : Blo 421773 422323 := bstep (se 1 (by rfl) ⟨316742, by rfl⟩ : syracuseStep 422323 = 633485) B633485
theorem B635315 : Blo 421773 635315 := bstep (se 1 (by rfl) ⟨476486, by rfl⟩ : syracuseStep 635315 = 952973) B952973
theorem B913859 : Blo 421773 913859 := bstep (se 1 (by rfl) ⟨685394, by rfl⟩ : syracuseStep 913859 = 1370789) B1370789
theorem B422339 : Blo 421773 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B627139 : Blo 421773 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B643523 : Blo 421773 643523 := bstep (se 1 (by rfl) ⟨482642, by rfl⟩ : syracuseStep 643523 = 965285) B965285
theorem B635345 : Blo 421773 635345 := bstep (se 2 (by rfl) ⟨238254, by rfl⟩ : syracuseStep 635345 = 476509) B476509
theorem B422355 : Blo 421773 422355 := bstep (se 1 (by rfl) ⟨316766, by rfl⟩ : syracuseStep 422355 = 633533) B633533
theorem B2404835 : Blo 421773 2404835 := bstep (se 1 (by rfl) ⟨1803626, by rfl⟩ : syracuseStep 2404835 = 3607253) B3607253
theorem B422371 : Blo 421773 422371 := bstep (se 1 (by rfl) ⟨316778, by rfl⟩ : syracuseStep 422371 = 633557) B633557
theorem B635363 : Blo 421773 635363 := bstep (se 1 (by rfl) ⟨476522, by rfl⟩ : syracuseStep 635363 = 953045) B953045
theorem B1610225 : Blo 421773 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B422387 : Blo 421773 422387 := bstep (se 1 (by rfl) ⟨316790, by rfl⟩ : syracuseStep 422387 = 633581) B633581
theorem B635393 : Blo 421773 635393 := bstep (se 2 (by rfl) ⟨238272, by rfl⟩ : syracuseStep 635393 = 476545) B476545
theorem B422403 : Blo 421773 422403 := bstep (se 1 (by rfl) ⟨316802, by rfl⟩ : syracuseStep 422403 = 633605) B633605
theorem B1020433 : Blo 421773 1020433 := bstep (se 2 (by rfl) ⟨382662, by rfl⟩ : syracuseStep 1020433 = 765325) B765325
theorem B422419 : Blo 421773 422419 := bstep (se 1 (by rfl) ⟨316814, by rfl⟩ : syracuseStep 422419 = 633629) B633629
theorem B635411 : Blo 421773 635411 := bstep (se 1 (by rfl) ⟨476558, by rfl⟩ : syracuseStep 635411 = 953117) B953117
theorem B422435 : Blo 421773 422435 := bstep (se 1 (by rfl) ⟨316826, by rfl⟩ : syracuseStep 422435 = 633653) B633653
theorem B1528355 : Blo 421773 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B635441 : Blo 421773 635441 := bstep (se 2 (by rfl) ⟨238290, by rfl⟩ : syracuseStep 635441 = 476581) B476581
theorem B422451 : Blo 421773 422451 := bstep (se 1 (by rfl) ⟨316838, by rfl⟩ : syracuseStep 422451 = 633677) B633677
theorem B422467 : Blo 421773 422467 := bstep (se 1 (by rfl) ⟨316850, by rfl⟩ : syracuseStep 422467 = 633701) B633701
theorem B635459 : Blo 421773 635459 := bstep (se 1 (by rfl) ⟨476594, by rfl⟩ : syracuseStep 635459 = 953189) B953189
theorem B422483 : Blo 421773 422483 := bstep (se 1 (by rfl) ⟨316862, by rfl⟩ : syracuseStep 422483 = 633725) B633725
theorem B635489 : Blo 421773 635489 := bstep (se 2 (by rfl) ⟨238308, by rfl⟩ : syracuseStep 635489 = 476617) B476617
theorem B422499 : Blo 421773 422499 := bstep (se 1 (by rfl) ⟨316874, by rfl⟩ : syracuseStep 422499 = 633749) B633749
theorem B537187 : Blo 421773 537187 := bstep (se 1 (by rfl) ⟨402890, by rfl⟩ : syracuseStep 537187 = 805781) B805781
theorem B1208945 : Blo 421773 1208945 := bstep (se 2 (by rfl) ⟨453354, by rfl⟩ : syracuseStep 1208945 = 906709) B906709
theorem B422515 : Blo 421773 422515 := bstep (se 1 (by rfl) ⟨316886, by rfl⟩ : syracuseStep 422515 = 633773) B633773
theorem B635507 : Blo 421773 635507 := bstep (se 1 (by rfl) ⟨476630, by rfl⟩ : syracuseStep 635507 = 953261) B953261
theorem B422531 : Blo 421773 422531 := bstep (se 1 (by rfl) ⟨316898, by rfl⟩ : syracuseStep 422531 = 633797) B633797
theorem B10039949 : Blo 421773 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B635537 : Blo 421773 635537 := bstep (se 2 (by rfl) ⟨238326, by rfl⟩ : syracuseStep 635537 = 476653) B476653
theorem B422547 : Blo 421773 422547 := bstep (se 1 (by rfl) ⟨316910, by rfl⟩ : syracuseStep 422547 = 633821) B633821
theorem B955025 : Blo 421773 955025 := bstep (se 2 (by rfl) ⟨358134, by rfl⟩ : syracuseStep 955025 = 716269) B716269
theorem B422563 : Blo 421773 422563 := bstep (se 1 (by rfl) ⟨316922, by rfl⟩ : syracuseStep 422563 = 633845) B633845
theorem B635555 : Blo 421773 635555 := bstep (se 1 (by rfl) ⟨476666, by rfl⟩ : syracuseStep 635555 = 953333) B953333
theorem B955043 : Blo 421773 955043 := bstep (se 1 (by rfl) ⟨716282, by rfl⟩ : syracuseStep 955043 = 1432565) B1432565
theorem B1430189 : Blo 421773 1430189 := bstep (se 3 (by rfl) ⟨268160, by rfl⟩ : syracuseStep 1430189 = 536321) B536321
theorem B422579 : Blo 421773 422579 := bstep (se 1 (by rfl) ⟨316934, by rfl⟩ : syracuseStep 422579 = 633869) B633869
theorem B635585 : Blo 421773 635585 := bstep (se 2 (by rfl) ⟨238344, by rfl⟩ : syracuseStep 635585 = 476689) B476689
theorem B422595 : Blo 421773 422595 := bstep (se 1 (by rfl) ⟨316946, by rfl⟩ : syracuseStep 422595 = 633893) B633893
theorem B537283 : Blo 421773 537283 := bstep (se 1 (by rfl) ⟨402962, by rfl⟩ : syracuseStep 537283 = 805925) B805925
theorem B6861509 : Blo 421773 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B422611 : Blo 421773 422611 := bstep (se 1 (by rfl) ⟨316958, by rfl⟩ : syracuseStep 422611 = 633917) B633917
theorem B635603 : Blo 421773 635603 := bstep (se 1 (by rfl) ⟨476702, by rfl⟩ : syracuseStep 635603 = 953405) B953405
theorem B602849 : Blo 421773 602849 := bstep (se 2 (by rfl) ⟨226068, by rfl⟩ : syracuseStep 602849 = 452137) B452137
theorem B422627 : Blo 421773 422627 := bstep (se 1 (by rfl) ⟨316970, by rfl⟩ : syracuseStep 422627 = 633941) B633941
theorem B1430243 : Blo 421773 1430243 := bstep (se 1 (by rfl) ⟨1072682, by rfl⟩ : syracuseStep 1430243 = 2145365) B2145365
theorem B635633 : Blo 421773 635633 := bstep (se 2 (by rfl) ⟨238362, by rfl⟩ : syracuseStep 635633 = 476725) B476725
theorem B422643 : Blo 421773 422643 := bstep (se 1 (by rfl) ⟨316982, by rfl⟩ : syracuseStep 422643 = 633965) B633965
theorem B422659 : Blo 421773 422659 := bstep (se 1 (by rfl) ⟨316994, by rfl⟩ : syracuseStep 422659 = 633989) B633989
theorem B635651 : Blo 421773 635651 := bstep (se 1 (by rfl) ⟨476738, by rfl⟩ : syracuseStep 635651 = 953477) B953477
theorem B422675 : Blo 421773 422675 := bstep (se 1 (by rfl) ⟨317006, by rfl⟩ : syracuseStep 422675 = 634013) B634013
theorem B635681 : Blo 421773 635681 := bstep (se 2 (by rfl) ⟨238380, by rfl⟩ : syracuseStep 635681 = 476761) B476761
theorem B422691 : Blo 421773 422691 := bstep (se 1 (by rfl) ⟨317018, by rfl⟩ : syracuseStep 422691 = 634037) B634037
theorem B422707 : Blo 421773 422707 := bstep (se 1 (by rfl) ⟨317030, by rfl⟩ : syracuseStep 422707 = 634061) B634061
theorem B635699 : Blo 421773 635699 := bstep (se 1 (by rfl) ⟨476774, by rfl⟩ : syracuseStep 635699 = 953549) B953549
theorem B422723 : Blo 421773 422723 := bstep (se 1 (by rfl) ⟨317042, by rfl⟩ : syracuseStep 422723 = 634085) B634085
theorem B1807181 : Blo 421773 1807181 := bstep (se 3 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 1807181 = 677693) B677693
theorem B635729 : Blo 421773 635729 := bstep (se 2 (by rfl) ⟨238398, by rfl⟩ : syracuseStep 635729 = 476797) B476797
theorem B422739 : Blo 421773 422739 := bstep (se 1 (by rfl) ⟨317054, by rfl⟩ : syracuseStep 422739 = 634109) B634109
theorem B422755 : Blo 421773 422755 := bstep (se 1 (by rfl) ⟨317066, by rfl⟩ : syracuseStep 422755 = 634133) B634133
theorem B635747 : Blo 421773 635747 := bstep (se 1 (by rfl) ⟨476810, by rfl⟩ : syracuseStep 635747 = 953621) B953621
theorem B422771 : Blo 421773 422771 := bstep (se 1 (by rfl) ⟨317078, by rfl⟩ : syracuseStep 422771 = 634157) B634157
theorem B635777 : Blo 421773 635777 := bstep (se 2 (by rfl) ⟨238416, by rfl⟩ : syracuseStep 635777 = 476833) B476833
theorem B422787 : Blo 421773 422787 := bstep (se 1 (by rfl) ⟨317090, by rfl⟩ : syracuseStep 422787 = 634181) B634181
theorem B1069969 : Blo 421773 1069969 := bstep (se 2 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 1069969 = 802477) B802477
theorem B422803 : Blo 421773 422803 := bstep (se 1 (by rfl) ⟨317102, by rfl⟩ : syracuseStep 422803 = 634205) B634205
theorem B635795 : Blo 421773 635795 := bstep (se 1 (by rfl) ⟨476846, by rfl⟩ : syracuseStep 635795 = 953693) B953693
theorem B422819 : Blo 421773 422819 := bstep (se 1 (by rfl) ⟨317114, by rfl⟩ : syracuseStep 422819 = 634229) B634229
theorem B2282417 : Blo 421773 2282417 := bstep (se 2 (by rfl) ⟨855906, by rfl⟩ : syracuseStep 2282417 = 1711813) B1711813
theorem B2290609 : Blo 421773 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B422835 : Blo 421773 422835 := bstep (se 1 (by rfl) ⟨317126, by rfl⟩ : syracuseStep 422835 = 634253) B634253
theorem B635825 : Blo 421773 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B955313 : Blo 421773 955313 := bstep (se 2 (by rfl) ⟨358242, by rfl⟩ : syracuseStep 955313 = 716485) B716485
theorem B422851 : Blo 421773 422851 := bstep (se 1 (by rfl) ⟨317138, by rfl⟩ : syracuseStep 422851 = 634277) B634277
theorem B635843 : Blo 421773 635843 := bstep (se 1 (by rfl) ⟨476882, by rfl⟩ : syracuseStep 635843 = 953765) B953765
theorem B2569157 : Blo 421773 2569157 := bstep (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) B481717
theorem B955331 : Blo 421773 955331 := bstep (se 1 (by rfl) ⟨716498, by rfl⟩ : syracuseStep 955331 = 1432997) B1432997
theorem B422867 : Blo 421773 422867 := bstep (se 1 (by rfl) ⟨317150, by rfl⟩ : syracuseStep 422867 = 634301) B634301
theorem B635873 : Blo 421773 635873 := bstep (se 2 (by rfl) ⟨238452, by rfl⟩ : syracuseStep 635873 = 476905) B476905
theorem B422883 : Blo 421773 422883 := bstep (se 1 (by rfl) ⟨317162, by rfl⟩ : syracuseStep 422883 = 634325) B634325
theorem B1430513 : Blo 421773 1430513 := bstep (se 2 (by rfl) ⟨536442, by rfl⟩ : syracuseStep 1430513 = 1072885) B1072885
theorem B422899 : Blo 421773 422899 := bstep (se 1 (by rfl) ⟨317174, by rfl⟩ : syracuseStep 422899 = 634349) B634349
theorem B635891 : Blo 421773 635891 := bstep (se 1 (by rfl) ⟨476918, by rfl⟩ : syracuseStep 635891 = 953837) B953837
theorem B422915 : Blo 421773 422915 := bstep (se 1 (by rfl) ⟨317186, by rfl⟩ : syracuseStep 422915 = 634373) B634373
theorem B635921 : Blo 421773 635921 := bstep (se 2 (by rfl) ⟨238470, by rfl⟩ : syracuseStep 635921 = 476941) B476941
theorem B422931 : Blo 421773 422931 := bstep (se 1 (by rfl) ⟨317198, by rfl⟩ : syracuseStep 422931 = 634397) B634397
theorem B422947 : Blo 421773 422947 := bstep (se 1 (by rfl) ⟨317210, by rfl⟩ : syracuseStep 422947 = 634421) B634421
theorem B2036771 : Blo 421773 2036771 := bstep (se 1 (by rfl) ⟨1527578, by rfl⟩ : syracuseStep 2036771 = 3055157) B3055157
theorem B635939 : Blo 421773 635939 := bstep (se 1 (by rfl) ⟨476954, by rfl⟩ : syracuseStep 635939 = 953909) B953909
theorem B422963 : Blo 421773 422963 := bstep (se 1 (by rfl) ⟨317222, by rfl⟩ : syracuseStep 422963 = 634445) B634445
theorem B635969 : Blo 421773 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B422979 : Blo 421773 422979 := bstep (se 1 (by rfl) ⟨317234, by rfl⟩ : syracuseStep 422979 = 634469) B634469
theorem B422995 : Blo 421773 422995 := bstep (se 1 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 422995 = 634493) B634493
theorem B635987 : Blo 421773 635987 := bstep (se 1 (by rfl) ⟨476990, by rfl⟩ : syracuseStep 635987 = 953981) B953981
theorem B423011 : Blo 421773 423011 := bstep (se 1 (by rfl) ⟨317258, by rfl⟩ : syracuseStep 423011 = 634517) B634517
theorem B636017 : Blo 421773 636017 := bstep (se 2 (by rfl) ⟨238506, by rfl⟩ : syracuseStep 636017 = 477013) B477013
theorem B423027 : Blo 421773 423027 := bstep (se 1 (by rfl) ⟨317270, by rfl⟩ : syracuseStep 423027 = 634541) B634541
theorem B423043 : Blo 421773 423043 := bstep (se 1 (by rfl) ⟨317282, by rfl⟩ : syracuseStep 423043 = 634565) B634565
theorem B636035 : Blo 421773 636035 := bstep (se 1 (by rfl) ⟨477026, by rfl⟩ : syracuseStep 636035 = 954053) B954053
theorem B423059 : Blo 421773 423059 := bstep (se 1 (by rfl) ⟨317294, by rfl⟩ : syracuseStep 423059 = 634589) B634589
theorem B636065 : Blo 421773 636065 := bstep (se 2 (by rfl) ⟨238524, by rfl⟩ : syracuseStep 636065 = 477049) B477049
theorem B1070243 : Blo 421773 1070243 := bstep (se 1 (by rfl) ⟨802682, by rfl⟩ : syracuseStep 1070243 = 1605365) B1605365
theorem B423075 : Blo 421773 423075 := bstep (se 1 (by rfl) ⟨317306, by rfl⟩ : syracuseStep 423075 = 634613) B634613
theorem B1602737 : Blo 421773 1602737 := bstep (se 2 (by rfl) ⟨601026, by rfl⟩ : syracuseStep 1602737 = 1202053) B1202053
theorem B2266289 : Blo 421773 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B423091 : Blo 421773 423091 := bstep (se 1 (by rfl) ⟨317318, by rfl⟩ : syracuseStep 423091 = 634637) B634637
theorem B636083 : Blo 421773 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B423107 : Blo 421773 423107 := bstep (se 1 (by rfl) ⟨317330, by rfl⟩ : syracuseStep 423107 = 634661) B634661
theorem B1717453 : Blo 421773 1717453 := bstep (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) B644045
theorem B570577 : Blo 421773 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B423123 : Blo 421773 423123 := bstep (se 1 (by rfl) ⟨317342, by rfl⟩ : syracuseStep 423123 = 634685) B634685
theorem B636113 : Blo 421773 636113 := bstep (se 2 (by rfl) ⟨238542, by rfl⟩ : syracuseStep 636113 = 477085) B477085
theorem B955601 : Blo 421773 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B423139 : Blo 421773 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B636131 : Blo 421773 636131 := bstep (se 1 (by rfl) ⟨477098, by rfl⟩ : syracuseStep 636131 = 954197) B954197
theorem B955619 : Blo 421773 955619 := bstep (se 1 (by rfl) ⟨716714, by rfl⟩ : syracuseStep 955619 = 1433429) B1433429
theorem B423155 : Blo 421773 423155 := bstep (se 1 (by rfl) ⟨317366, by rfl⟩ : syracuseStep 423155 = 634733) B634733
theorem B603379 : Blo 421773 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B636161 : Blo 421773 636161 := bstep (se 2 (by rfl) ⟨238560, by rfl⟩ : syracuseStep 636161 = 477121) B477121
theorem B423171 : Blo 421773 423171 := bstep (se 1 (by rfl) ⟨317378, by rfl⟩ : syracuseStep 423171 = 634757) B634757
theorem B423187 : Blo 421773 423187 := bstep (se 1 (by rfl) ⟨317390, by rfl⟩ : syracuseStep 423187 = 634781) B634781
theorem B636179 : Blo 421773 636179 := bstep (se 1 (by rfl) ⟨477134, by rfl⟩ : syracuseStep 636179 = 954269) B954269
theorem B423203 : Blo 421773 423203 := bstep (se 1 (by rfl) ⟨317402, by rfl⟩ : syracuseStep 423203 = 634805) B634805
theorem B636209 : Blo 421773 636209 := bstep (se 2 (by rfl) ⟨238578, by rfl⟩ : syracuseStep 636209 = 477157) B477157
theorem B423219 : Blo 421773 423219 := bstep (se 1 (by rfl) ⟨317414, by rfl⟩ : syracuseStep 423219 = 634829) B634829
theorem B423235 : Blo 421773 423235 := bstep (se 1 (by rfl) ⟨317426, by rfl⟩ : syracuseStep 423235 = 634853) B634853
theorem B636227 : Blo 421773 636227 := bstep (se 1 (by rfl) ⟨477170, by rfl⟩ : syracuseStep 636227 = 954341) B954341
theorem B2413901 : Blo 421773 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B423251 : Blo 421773 423251 := bstep (se 1 (by rfl) ⟨317438, by rfl⟩ : syracuseStep 423251 = 634877) B634877
theorem B636257 : Blo 421773 636257 := bstep (se 2 (by rfl) ⟨238596, by rfl⟩ : syracuseStep 636257 = 477193) B477193
theorem B1070435 : Blo 421773 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B423267 : Blo 421773 423267 := bstep (se 1 (by rfl) ⟨317450, by rfl⟩ : syracuseStep 423267 = 634901) B634901
theorem B423283 : Blo 421773 423283 := bstep (se 1 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 423283 = 634925) B634925
theorem B636275 : Blo 421773 636275 := bstep (se 1 (by rfl) ⟨477206, by rfl⟩ : syracuseStep 636275 = 954413) B954413
theorem B423299 : Blo 421773 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B636305 : Blo 421773 636305 := bstep (se 2 (by rfl) ⟨238614, by rfl⟩ : syracuseStep 636305 = 477229) B477229
theorem B423315 : Blo 421773 423315 := bstep (se 1 (by rfl) ⟨317486, by rfl⟩ : syracuseStep 423315 = 634973) B634973
theorem B423331 : Blo 421773 423331 := bstep (se 1 (by rfl) ⟨317498, by rfl⟩ : syracuseStep 423331 = 634997) B634997
theorem B636323 : Blo 421773 636323 := bstep (se 1 (by rfl) ⟨477242, by rfl⟩ : syracuseStep 636323 = 954485) B954485
theorem B578993 : Blo 421773 578993 := bstep (se 2 (by rfl) ⟨217122, by rfl⟩ : syracuseStep 578993 = 434245) B434245
theorem B423347 : Blo 421773 423347 := bstep (se 1 (by rfl) ⟨317510, by rfl⟩ : syracuseStep 423347 = 635021) B635021
theorem B636353 : Blo 421773 636353 := bstep (se 2 (by rfl) ⟨238632, by rfl⟩ : syracuseStep 636353 = 477265) B477265
theorem B423363 : Blo 421773 423363 := bstep (se 1 (by rfl) ⟨317522, by rfl⟩ : syracuseStep 423363 = 635045) B635045
theorem B423379 : Blo 421773 423379 := bstep (se 1 (by rfl) ⟨317534, by rfl⟩ : syracuseStep 423379 = 635069) B635069
theorem B636371 : Blo 421773 636371 := bstep (se 1 (by rfl) ⟨477278, by rfl⟩ : syracuseStep 636371 = 954557) B954557
theorem B423395 : Blo 421773 423395 := bstep (se 1 (by rfl) ⟨317546, by rfl⟩ : syracuseStep 423395 = 635093) B635093
theorem B636401 : Blo 421773 636401 := bstep (se 2 (by rfl) ⟨238650, by rfl⟩ : syracuseStep 636401 = 477301) B477301
theorem B423411 : Blo 421773 423411 := bstep (se 1 (by rfl) ⟨317558, by rfl⟩ : syracuseStep 423411 = 635117) B635117
theorem B423427 : Blo 421773 423427 := bstep (se 1 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 423427 = 635141) B635141
theorem B636419 : Blo 421773 636419 := bstep (se 1 (by rfl) ⟨477314, by rfl⟩ : syracuseStep 636419 = 954629) B954629
theorem B1431053 : Blo 421773 1431053 := bstep (se 3 (by rfl) ⟨268322, by rfl⟩ : syracuseStep 1431053 = 536645) B536645
theorem B423443 : Blo 421773 423443 := bstep (se 1 (by rfl) ⟨317582, by rfl⟩ : syracuseStep 423443 = 635165) B635165
theorem B636449 : Blo 421773 636449 := bstep (se 2 (by rfl) ⟨238668, by rfl⟩ : syracuseStep 636449 = 477337) B477337
theorem B423459 : Blo 421773 423459 := bstep (se 1 (by rfl) ⟨317594, by rfl⟩ : syracuseStep 423459 = 635189) B635189
theorem B423475 : Blo 421773 423475 := bstep (se 1 (by rfl) ⟨317606, by rfl⟩ : syracuseStep 423475 = 635213) B635213
theorem B10851893 : Blo 421773 10851893 := bstep (se 5 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 10851893 = 1017365) B1017365
theorem B636467 : Blo 421773 636467 := bstep (se 1 (by rfl) ⟨477350, by rfl⟩ : syracuseStep 636467 = 954701) B954701
theorem B423491 : Blo 421773 423491 := bstep (se 1 (by rfl) ⟨317618, by rfl⟩ : syracuseStep 423491 = 635237) B635237
theorem B603715 : Blo 421773 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B1431107 : Blo 421773 1431107 := bstep (se 1 (by rfl) ⟨1073330, by rfl⟩ : syracuseStep 1431107 = 2146661) B2146661
theorem B636497 : Blo 421773 636497 := bstep (se 2 (by rfl) ⟨238686, by rfl⟩ : syracuseStep 636497 = 477373) B477373
theorem B423507 : Blo 421773 423507 := bstep (se 1 (by rfl) ⟨317630, by rfl⟩ : syracuseStep 423507 = 635261) B635261
theorem B423523 : Blo 421773 423523 := bstep (se 1 (by rfl) ⟨317642, by rfl⟩ : syracuseStep 423523 = 635285) B635285
theorem B636515 : Blo 421773 636515 := bstep (se 1 (by rfl) ⟨477386, by rfl⟩ : syracuseStep 636515 = 954773) B954773
theorem B423539 : Blo 421773 423539 := bstep (se 1 (by rfl) ⟨317654, by rfl⟩ : syracuseStep 423539 = 635309) B635309
theorem B636545 : Blo 421773 636545 := bstep (se 2 (by rfl) ⟨238704, by rfl⟩ : syracuseStep 636545 = 477409) B477409
theorem B1144451 : Blo 421773 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B423555 : Blo 421773 423555 := bstep (se 1 (by rfl) ⟨317666, by rfl⟩ : syracuseStep 423555 = 635333) B635333
theorem B423571 : Blo 421773 423571 := bstep (se 1 (by rfl) ⟨317678, by rfl⟩ : syracuseStep 423571 = 635357) B635357
theorem B636563 : Blo 421773 636563 := bstep (se 1 (by rfl) ⟨477422, by rfl⟩ : syracuseStep 636563 = 954845) B954845
theorem B2143907 : Blo 421773 2143907 := bstep (se 1 (by rfl) ⟨1607930, by rfl⟩ : syracuseStep 2143907 = 3215861) B3215861
theorem B423587 : Blo 421773 423587 := bstep (se 1 (by rfl) ⟨317690, by rfl⟩ : syracuseStep 423587 = 635381) B635381
theorem B1201837 : Blo 421773 1201837 := bstep (se 3 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 1201837 = 450689) B450689
theorem B571057 : Blo 421773 571057 := bstep (se 2 (by rfl) ⟨214146, by rfl⟩ : syracuseStep 571057 = 428293) B428293
theorem B423603 : Blo 421773 423603 := bstep (se 1 (by rfl) ⟨317702, by rfl⟩ : syracuseStep 423603 = 635405) B635405
theorem B636593 : Blo 421773 636593 := bstep (se 2 (by rfl) ⟨238722, by rfl⟩ : syracuseStep 636593 = 477445) B477445
theorem B423619 : Blo 421773 423619 := bstep (se 1 (by rfl) ⟨317714, by rfl⟩ : syracuseStep 423619 = 635429) B635429
theorem B636611 : Blo 421773 636611 := bstep (se 1 (by rfl) ⟨477458, by rfl⟩ : syracuseStep 636611 = 954917) B954917
theorem B423635 : Blo 421773 423635 := bstep (se 1 (by rfl) ⟨317726, by rfl⟩ : syracuseStep 423635 = 635453) B635453
theorem B636641 : Blo 421773 636641 := bstep (se 2 (by rfl) ⟨238740, by rfl⟩ : syracuseStep 636641 = 477481) B477481
theorem B677603 : Blo 421773 677603 := bstep (se 1 (by rfl) ⟨508202, by rfl⟩ : syracuseStep 677603 = 1016405) B1016405
theorem B3258083 : Blo 421773 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B423651 : Blo 421773 423651 := bstep (se 1 (by rfl) ⟨317738, by rfl⟩ : syracuseStep 423651 = 635477) B635477
theorem B423667 : Blo 421773 423667 := bstep (se 1 (by rfl) ⟨317750, by rfl⟩ : syracuseStep 423667 = 635501) B635501
theorem B636659 : Blo 421773 636659 := bstep (se 1 (by rfl) ⟨477494, by rfl⟩ : syracuseStep 636659 = 954989) B954989
theorem B423683 : Blo 421773 423683 := bstep (se 1 (by rfl) ⟨317762, by rfl⟩ : syracuseStep 423683 = 635525) B635525
theorem B1013521 : Blo 421773 1013521 := bstep (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) B760141
theorem B636689 : Blo 421773 636689 := bstep (se 2 (by rfl) ⟨238758, by rfl⟩ : syracuseStep 636689 = 477517) B477517
theorem B423699 : Blo 421773 423699 := bstep (se 1 (by rfl) ⟨317774, by rfl⟩ : syracuseStep 423699 = 635549) B635549
theorem B2709283 : Blo 421773 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B423715 : Blo 421773 423715 := bstep (se 1 (by rfl) ⟨317786, by rfl⟩ : syracuseStep 423715 = 635573) B635573
theorem B636707 : Blo 421773 636707 := bstep (se 1 (by rfl) ⟨477530, by rfl⟩ : syracuseStep 636707 = 955061) B955061
theorem B423731 : Blo 421773 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B636737 : Blo 421773 636737 := bstep (se 2 (by rfl) ⟨238776, by rfl⟩ : syracuseStep 636737 = 477553) B477553
theorem B423747 : Blo 421773 423747 := bstep (se 1 (by rfl) ⟨317810, by rfl⟩ : syracuseStep 423747 = 635621) B635621
theorem B1431377 : Blo 421773 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B423763 : Blo 421773 423763 := bstep (se 1 (by rfl) ⟨317822, by rfl⟩ : syracuseStep 423763 = 635645) B635645
theorem B636755 : Blo 421773 636755 := bstep (se 1 (by rfl) ⟨477566, by rfl⟩ : syracuseStep 636755 = 955133) B955133
theorem B677731 : Blo 421773 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B423779 : Blo 421773 423779 := bstep (se 1 (by rfl) ⟨317834, by rfl⟩ : syracuseStep 423779 = 635669) B635669
theorem B1357667 : Blo 421773 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B423795 : Blo 421773 423795 := bstep (se 1 (by rfl) ⟨317846, by rfl⟩ : syracuseStep 423795 = 635693) B635693
theorem B636785 : Blo 421773 636785 := bstep (se 2 (by rfl) ⟨238794, by rfl⟩ : syracuseStep 636785 = 477589) B477589
theorem B423811 : Blo 421773 423811 := bstep (se 1 (by rfl) ⟨317858, by rfl⟩ : syracuseStep 423811 = 635717) B635717
theorem B636803 : Blo 421773 636803 := bstep (se 1 (by rfl) ⟨477602, by rfl⟩ : syracuseStep 636803 = 955205) B955205
theorem B423827 : Blo 421773 423827 := bstep (se 1 (by rfl) ⟨317870, by rfl⟩ : syracuseStep 423827 = 635741) B635741
theorem B636833 : Blo 421773 636833 := bstep (se 2 (by rfl) ⟨238812, by rfl⟩ : syracuseStep 636833 = 477625) B477625
theorem B2570147 : Blo 421773 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B423843 : Blo 421773 423843 := bstep (se 1 (by rfl) ⟨317882, by rfl⟩ : syracuseStep 423843 = 635765) B635765
theorem B1611683 : Blo 421773 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B1611697 : Blo 421773 1611697 := bstep (se 2 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 1611697 = 1208773) B1208773
theorem B423859 : Blo 421773 423859 := bstep (se 1 (by rfl) ⟨317894, by rfl⟩ : syracuseStep 423859 = 635789) B635789
theorem B636851 : Blo 421773 636851 := bstep (se 1 (by rfl) ⟨477638, by rfl⟩ : syracuseStep 636851 = 955277) B955277
theorem B423875 : Blo 421773 423875 := bstep (se 1 (by rfl) ⟨317906, by rfl⟩ : syracuseStep 423875 = 635813) B635813
theorem B636881 : Blo 421773 636881 := bstep (se 2 (by rfl) ⟨238830, by rfl⟩ : syracuseStep 636881 = 477661) B477661
theorem B423891 : Blo 421773 423891 := bstep (se 1 (by rfl) ⟨317918, by rfl⟩ : syracuseStep 423891 = 635837) B635837
theorem B423907 : Blo 421773 423907 := bstep (se 1 (by rfl) ⟨317930, by rfl⟩ : syracuseStep 423907 = 635861) B635861
theorem B4077539 : Blo 421773 4077539 := bstep (se 1 (by rfl) ⟨3058154, by rfl⟩ : syracuseStep 4077539 = 6116309) B6116309
theorem B636899 : Blo 421773 636899 := bstep (se 1 (by rfl) ⟨477674, by rfl⟩ : syracuseStep 636899 = 955349) B955349
theorem B423923 : Blo 421773 423923 := bstep (se 1 (by rfl) ⟨317942, by rfl⟩ : syracuseStep 423923 = 635885) B635885
theorem B636929 : Blo 421773 636929 := bstep (se 2 (by rfl) ⟨238848, by rfl⟩ : syracuseStep 636929 = 477697) B477697
theorem B423939 : Blo 421773 423939 := bstep (se 1 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 423939 = 635909) B635909
theorem B423955 : Blo 421773 423955 := bstep (se 1 (by rfl) ⟨317966, by rfl⟩ : syracuseStep 423955 = 635933) B635933
theorem B636947 : Blo 421773 636947 := bstep (se 1 (by rfl) ⟨477710, by rfl⟩ : syracuseStep 636947 = 955421) B955421
theorem B423971 : Blo 421773 423971 := bstep (se 1 (by rfl) ⟨317978, by rfl⟩ : syracuseStep 423971 = 635957) B635957
theorem B636977 : Blo 421773 636977 := bstep (se 2 (by rfl) ⟨238866, by rfl⟩ : syracuseStep 636977 = 477733) B477733
theorem B423987 : Blo 421773 423987 := bstep (se 1 (by rfl) ⟨317990, by rfl⟩ : syracuseStep 423987 = 635981) B635981
theorem B424003 : Blo 421773 424003 := bstep (se 1 (by rfl) ⟨318002, by rfl⟩ : syracuseStep 424003 = 636005) B636005
theorem B636995 : Blo 421773 636995 := bstep (se 1 (by rfl) ⟨477746, by rfl⟩ : syracuseStep 636995 = 955493) B955493
theorem B424019 : Blo 421773 424019 := bstep (se 1 (by rfl) ⟨318014, by rfl⟩ : syracuseStep 424019 = 636029) B636029
theorem B637025 : Blo 421773 637025 := bstep (se 2 (by rfl) ⟨238884, by rfl⟩ : syracuseStep 637025 = 477769) B477769
theorem B800867 : Blo 421773 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B424035 : Blo 421773 424035 := bstep (se 1 (by rfl) ⟨318026, by rfl⟩ : syracuseStep 424035 = 636053) B636053
theorem B604273 : Blo 421773 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B424051 : Blo 421773 424051 := bstep (se 1 (by rfl) ⟨318038, by rfl⟩ : syracuseStep 424051 = 636077) B636077
theorem B637043 : Blo 421773 637043 := bstep (se 1 (by rfl) ⟨477782, by rfl⟩ : syracuseStep 637043 = 955565) B955565
theorem B424067 : Blo 421773 424067 := bstep (se 1 (by rfl) ⟨318050, by rfl⟩ : syracuseStep 424067 = 636101) B636101
theorem B637073 : Blo 421773 637073 := bstep (se 2 (by rfl) ⟨238902, by rfl⟩ : syracuseStep 637073 = 477805) B477805
theorem B424083 : Blo 421773 424083 := bstep (se 1 (by rfl) ⟨318062, by rfl⟩ : syracuseStep 424083 = 636125) B636125
theorem B604307 : Blo 421773 604307 := bstep (se 1 (by rfl) ⟨453230, by rfl⟩ : syracuseStep 604307 = 906461) B906461
theorem B915619 : Blo 421773 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B424099 : Blo 421773 424099 := bstep (se 1 (by rfl) ⟨318074, by rfl⟩ : syracuseStep 424099 = 636149) B636149
theorem B637091 : Blo 421773 637091 := bstep (se 1 (by rfl) ⟨477818, by rfl⟩ : syracuseStep 637091 = 955637) B955637
theorem B2717873 : Blo 421773 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B424115 : Blo 421773 424115 := bstep (se 1 (by rfl) ⟨318086, by rfl⟩ : syracuseStep 424115 = 636173) B636173
theorem B637121 : Blo 421773 637121 := bstep (se 2 (by rfl) ⟨238920, by rfl⟩ : syracuseStep 637121 = 477841) B477841
theorem B424131 : Blo 421773 424131 := bstep (se 1 (by rfl) ⟨318098, by rfl⟩ : syracuseStep 424131 = 636197) B636197
theorem B424147 : Blo 421773 424147 := bstep (se 1 (by rfl) ⟨318110, by rfl⟩ : syracuseStep 424147 = 636221) B636221
theorem B637139 : Blo 421773 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B424163 : Blo 421773 424163 := bstep (se 1 (by rfl) ⟨318122, by rfl⟩ : syracuseStep 424163 = 636245) B636245
theorem B7747811 : Blo 421773 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B1423601 : Blo 421773 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B424179 : Blo 421773 424179 := bstep (se 1 (by rfl) ⟨318134, by rfl⟩ : syracuseStep 424179 = 636269) B636269
theorem B424195 : Blo 421773 424195 := bstep (se 1 (by rfl) ⟨318146, by rfl⟩ : syracuseStep 424195 = 636293) B636293
theorem B1071377 : Blo 421773 1071377 := bstep (se 2 (by rfl) ⟨401766, by rfl⟩ : syracuseStep 1071377 = 803533) B803533
theorem B424211 : Blo 421773 424211 := bstep (se 1 (by rfl) ⟨318158, by rfl⟩ : syracuseStep 424211 = 636317) B636317
theorem B760099 : Blo 421773 760099 := bstep (se 1 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 760099 = 1140149) B1140149
theorem B424227 : Blo 421773 424227 := bstep (se 1 (by rfl) ⟨318170, by rfl⟩ : syracuseStep 424227 = 636341) B636341
theorem B424243 : Blo 421773 424243 := bstep (se 1 (by rfl) ⟨318182, by rfl⟩ : syracuseStep 424243 = 636365) B636365
theorem B1284419 : Blo 421773 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B1071427 : Blo 421773 1071427 := bstep (se 1 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 1071427 = 1607141) B1607141
theorem B424259 : Blo 421773 424259 := bstep (se 1 (by rfl) ⟨318194, by rfl⟩ : syracuseStep 424259 = 636389) B636389
theorem B1104209 : Blo 421773 1104209 := bstep (se 2 (by rfl) ⟨414078, by rfl⟩ : syracuseStep 1104209 = 828157) B828157
theorem B424275 : Blo 421773 424275 := bstep (se 1 (by rfl) ⟨318206, by rfl⟩ : syracuseStep 424275 = 636413) B636413
theorem B3610979 : Blo 421773 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B424291 : Blo 421773 424291 := bstep (se 1 (by rfl) ⟨318218, by rfl⟩ : syracuseStep 424291 = 636437) B636437
theorem B1431917 : Blo 421773 1431917 := bstep (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) B536969
theorem B4807025 : Blo 421773 4807025 := bstep (se 2 (by rfl) ⟨1802634, by rfl⟩ : syracuseStep 4807025 = 3605269) B3605269
theorem B424307 : Blo 421773 424307 := bstep (se 1 (by rfl) ⟨318230, by rfl⟩ : syracuseStep 424307 = 636461) B636461
theorem B424323 : Blo 421773 424323 := bstep (se 1 (by rfl) ⟨318242, by rfl⟩ : syracuseStep 424323 = 636485) B636485
theorem B3217805 : Blo 421773 3217805 := bstep (se 3 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 3217805 = 1206677) B1206677
theorem B678289 : Blo 421773 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B424339 : Blo 421773 424339 := bstep (se 1 (by rfl) ⟨318254, by rfl⟩ : syracuseStep 424339 = 636509) B636509
theorem B1431971 : Blo 421773 1431971 := bstep (se 1 (by rfl) ⟨1073978, by rfl⟩ : syracuseStep 1431971 = 2147957) B2147957
theorem B424355 : Blo 421773 424355 := bstep (se 1 (by rfl) ⟨318266, by rfl⟩ : syracuseStep 424355 = 636533) B636533
theorem B2038193 : Blo 421773 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B424371 : Blo 421773 424371 := bstep (se 1 (by rfl) ⟨318278, by rfl⟩ : syracuseStep 424371 = 636557) B636557
theorem B424387 : Blo 421773 424387 := bstep (se 1 (by rfl) ⟨318290, by rfl⟩ : syracuseStep 424387 = 636581) B636581
theorem B2144717 : Blo 421773 2144717 := bstep (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) B804269
theorem B1071569 : Blo 421773 1071569 := bstep (se 2 (by rfl) ⟨401838, by rfl⟩ : syracuseStep 1071569 = 803677) B803677
theorem B424403 : Blo 421773 424403 := bstep (se 1 (by rfl) ⟨318302, by rfl⟩ : syracuseStep 424403 = 636605) B636605
theorem B424419 : Blo 421773 424419 := bstep (se 1 (by rfl) ⟨318314, by rfl⟩ : syracuseStep 424419 = 636629) B636629
theorem B1284589 : Blo 421773 1284589 := bstep (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) B481721
theorem B424435 : Blo 421773 424435 := bstep (se 1 (by rfl) ⟨318326, by rfl⟩ : syracuseStep 424435 = 636653) B636653
theorem B424451 : Blo 421773 424451 := bstep (se 1 (by rfl) ⟨318338, by rfl⟩ : syracuseStep 424451 = 636677) B636677
theorem B424467 : Blo 421773 424467 := bstep (se 1 (by rfl) ⟨318350, by rfl⟩ : syracuseStep 424467 = 636701) B636701
theorem B424483 : Blo 421773 424483 := bstep (se 1 (by rfl) ⟨318362, by rfl⟩ : syracuseStep 424483 = 636725) B636725
theorem B424499 : Blo 421773 424499 := bstep (se 1 (by rfl) ⟨318374, by rfl⟩ : syracuseStep 424499 = 636749) B636749
theorem B424515 : Blo 421773 424515 := bstep (se 1 (by rfl) ⟨318386, by rfl⟩ : syracuseStep 424515 = 636773) B636773
theorem B424531 : Blo 421773 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B1604195 : Blo 421773 1604195 := bstep (se 1 (by rfl) ⟨1203146, by rfl⟩ : syracuseStep 1604195 = 2406293) B2406293
theorem B424547 : Blo 421773 424547 := bstep (se 1 (by rfl) ⟨318410, by rfl⟩ : syracuseStep 424547 = 636821) B636821
theorem B2284145 : Blo 421773 2284145 := bstep (se 2 (by rfl) ⟨856554, by rfl⟩ : syracuseStep 2284145 = 1713109) B1713109
theorem B424563 : Blo 421773 424563 := bstep (se 1 (by rfl) ⟨318422, by rfl⟩ : syracuseStep 424563 = 636845) B636845
theorem B424579 : Blo 421773 424579 := bstep (se 1 (by rfl) ⟨318434, by rfl⟩ : syracuseStep 424579 = 636869) B636869
theorem B424595 : Blo 421773 424595 := bstep (se 1 (by rfl) ⟨318446, by rfl⟩ : syracuseStep 424595 = 636893) B636893
theorem B424611 : Blo 421773 424611 := bstep (se 1 (by rfl) ⟨318458, by rfl⟩ : syracuseStep 424611 = 636917) B636917
theorem B1432241 : Blo 421773 1432241 := bstep (se 2 (by rfl) ⟨537090, by rfl⟩ : syracuseStep 1432241 = 1074181) B1074181
theorem B424627 : Blo 421773 424627 := bstep (se 1 (by rfl) ⟨318470, by rfl⟩ : syracuseStep 424627 = 636941) B636941
theorem B424643 : Blo 421773 424643 := bstep (se 1 (by rfl) ⟨318482, by rfl⟩ : syracuseStep 424643 = 636965) B636965
theorem B424659 : Blo 421773 424659 := bstep (se 1 (by rfl) ⟨318494, by rfl⟩ : syracuseStep 424659 = 636989) B636989
theorem B424675 : Blo 421773 424675 := bstep (se 1 (by rfl) ⟨318506, by rfl⟩ : syracuseStep 424675 = 637013) B637013
theorem B424691 : Blo 421773 424691 := bstep (se 1 (by rfl) ⟨318518, by rfl⟩ : syracuseStep 424691 = 637037) B637037
theorem B948995 : Blo 421773 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B424707 : Blo 421773 424707 := bstep (se 1 (by rfl) ⟨318530, by rfl⟩ : syracuseStep 424707 = 637061) B637061
theorem B1424141 : Blo 421773 1424141 := bstep (se 3 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 1424141 = 534053) B534053
theorem B424723 : Blo 421773 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B424739 : Blo 421773 424739 := bstep (se 1 (by rfl) ⟨318554, by rfl⟩ : syracuseStep 424739 = 637109) B637109
theorem B424755 : Blo 421773 424755 := bstep (se 1 (by rfl) ⟨318566, by rfl⟩ : syracuseStep 424755 = 637133) B637133
theorem B1424195 : Blo 421773 1424195 := bstep (se 1 (by rfl) ⟨1068146, by rfl⟩ : syracuseStep 1424195 = 2136293) B2136293
theorem B424771 : Blo 421773 424771 := bstep (se 1 (by rfl) ⟨318578, by rfl⟩ : syracuseStep 424771 = 637157) B637157
theorem B3849059 : Blo 421773 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B2235235 : Blo 421773 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B1284977 : Blo 421773 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B2710513 : Blo 421773 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B1530893 : Blo 421773 1530893 := bstep (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) B574085
theorem B949265 : Blo 421773 949265 := bstep (se 2 (by rfl) ⟨355974, by rfl⟩ : syracuseStep 949265 = 711949) B711949
theorem B801809 : Blo 421773 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B949283 : Blo 421773 949283 := bstep (se 1 (by rfl) ⟨711962, by rfl⟩ : syracuseStep 949283 = 1423925) B1423925
theorem B678961 : Blo 421773 678961 := bstep (se 2 (by rfl) ⟨254610, by rfl⟩ : syracuseStep 678961 = 509221) B509221
theorem B1424465 : Blo 421773 1424465 := bstep (se 2 (by rfl) ⟨534174, by rfl⟩ : syracuseStep 1424465 = 1068349) B1068349
theorem B916561 : Blo 421773 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B736337 : Blo 421773 736337 := bstep (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) B552253
theorem B1358947 : Blo 421773 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B1219715 : Blo 421773 1219715 := bstep (se 1 (by rfl) ⟨914786, by rfl⟩ : syracuseStep 1219715 = 1829573) B1829573
theorem B711841 : Blo 421773 711841 := bstep (se 2 (by rfl) ⟨266940, by rfl⟩ : syracuseStep 711841 = 533881) B533881
theorem B2137265 : Blo 421773 2137265 := bstep (se 2 (by rfl) ⟨801474, by rfl⟩ : syracuseStep 2137265 = 1602949) B1602949
theorem B711875 : Blo 421773 711875 := bstep (se 1 (by rfl) ⟨533906, by rfl⟩ : syracuseStep 711875 = 1067813) B1067813
theorem B1432781 : Blo 421773 1432781 := bstep (se 3 (by rfl) ⟨268646, by rfl⟩ : syracuseStep 1432781 = 537293) B537293
theorem B507107 : Blo 421773 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B1432835 : Blo 421773 1432835 := bstep (se 1 (by rfl) ⟨1074626, by rfl⟩ : syracuseStep 1432835 = 2149253) B2149253
theorem B949553 : Blo 421773 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B712003 : Blo 421773 712003 := bstep (se 1 (by rfl) ⟨534002, by rfl⟩ : syracuseStep 712003 = 1068005) B1068005
theorem B949571 : Blo 421773 949571 := bstep (se 1 (by rfl) ⟨712178, by rfl⟩ : syracuseStep 949571 = 1424357) B1424357
theorem B572755 : Blo 421773 572755 := bstep (se 1 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 572755 = 859133) B859133
theorem B1203569 : Blo 421773 1203569 := bstep (se 2 (by rfl) ⟨451338, by rfl⟩ : syracuseStep 1203569 = 902677) B902677
theorem B703907 : Blo 421773 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B1072561 : Blo 421773 1072561 := bstep (se 2 (by rfl) ⟨402210, by rfl⟩ : syracuseStep 1072561 = 804421) B804421
theorem B1359281 : Blo 421773 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B474547 : Blo 421773 474547 := bstep (se 1 (by rfl) ⟨355910, by rfl⟩ : syracuseStep 474547 = 711821) B711821
theorem B3440069 : Blo 421773 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B712145 : Blo 421773 712145 := bstep (se 2 (by rfl) ⟨267054, by rfl⟩ : syracuseStep 712145 = 534109) B534109
theorem B1433105 : Blo 421773 1433105 := bstep (se 2 (by rfl) ⟨537414, by rfl⟩ : syracuseStep 1433105 = 1074829) B1074829
theorem B1203761 : Blo 421773 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B474691 : Blo 421773 474691 := bstep (se 1 (by rfl) ⟨356018, by rfl⟩ : syracuseStep 474691 = 712037) B712037
theorem B1605197 : Blo 421773 1605197 := bstep (se 3 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 1605197 = 601949) B601949
theorem B712273 : Blo 421773 712273 := bstep (se 2 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 712273 = 534205) B534205
theorem B949841 : Blo 421773 949841 := bstep (se 2 (by rfl) ⟨356190, by rfl⟩ : syracuseStep 949841 = 712381) B712381
theorem B949859 : Blo 421773 949859 := bstep (se 1 (by rfl) ⟨712394, by rfl⟩ : syracuseStep 949859 = 1424789) B1424789
theorem B515683 : Blo 421773 515683 := bstep (se 1 (by rfl) ⟨386762, by rfl⟩ : syracuseStep 515683 = 773525) B773525
theorem B2719331 : Blo 421773 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B1425005 : Blo 421773 1425005 := bstep (se 3 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 1425005 = 534377) B534377
theorem B712307 : Blo 421773 712307 := bstep (se 1 (by rfl) ⟨534230, by rfl⟩ : syracuseStep 712307 = 1068461) B1068461
theorem B2408069 : Blo 421773 2408069 := bstep (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) B451513
theorem B1425059 : Blo 421773 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B1072835 : Blo 421773 1072835 := bstep (se 1 (by rfl) ⟨804626, by rfl⟩ : syracuseStep 1072835 = 1609253) B1609253
theorem B474835 : Blo 421773 474835 := bstep (se 1 (by rfl) ⟨356126, by rfl⟩ : syracuseStep 474835 = 712253) B712253
theorem B712435 : Blo 421773 712435 := bstep (se 1 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 712435 = 1068653) B1068653
theorem B4874053 : Blo 421773 4874053 := bstep (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) B913885
theorem B474979 : Blo 421773 474979 := bstep (se 1 (by rfl) ⟨356234, by rfl⟩ : syracuseStep 474979 = 712469) B712469
theorem B761699 : Blo 421773 761699 := bstep (se 1 (by rfl) ⟨571274, by rfl⟩ : syracuseStep 761699 = 1142549) B1142549
theorem B950129 : Blo 421773 950129 := bstep (se 2 (by rfl) ⟨356298, by rfl⟩ : syracuseStep 950129 = 712597) B712597
theorem B1810289 : Blo 421773 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B712577 : Blo 421773 712577 := bstep (se 2 (by rfl) ⟨267216, by rfl⟩ : syracuseStep 712577 = 534433) B534433
theorem B950147 : Blo 421773 950147 := bstep (se 1 (by rfl) ⟨712610, by rfl⟩ : syracuseStep 950147 = 1425221) B1425221
theorem B1073027 : Blo 421773 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B3710861 : Blo 421773 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B802705 : Blo 421773 802705 := bstep (se 2 (by rfl) ⟨301014, by rfl⟩ : syracuseStep 802705 = 602029) B602029
theorem B1425329 : Blo 421773 1425329 := bstep (se 2 (by rfl) ⟨534498, by rfl⟩ : syracuseStep 1425329 = 1068997) B1068997
theorem B1802225 : Blo 421773 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B475123 : Blo 421773 475123 := bstep (se 1 (by rfl) ⟨356342, by rfl⟩ : syracuseStep 475123 = 712685) B712685
theorem B950273 : Blo 421773 950273 := bstep (se 2 (by rfl) ⟨356352, by rfl⟩ : syracuseStep 950273 = 712705) B712705
theorem B475159 : Blo 421773 475159 := bstep (se 1 (by rfl) ⟨356369, by rfl⟩ : syracuseStep 475159 = 712739) B712739
theorem B679961 : Blo 421773 679961 := bstep (se 2 (by rfl) ⟨254985, by rfl⟩ : syracuseStep 679961 = 509971) B509971
theorem B1605683 : Blo 421773 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B712793 : Blo 421773 712793 := bstep (se 2 (by rfl) ⟨267297, by rfl⟩ : syracuseStep 712793 = 534595) B534595
theorem B803009 : Blo 421773 803009 := bstep (se 2 (by rfl) ⟨301128, by rfl⟩ : syracuseStep 803009 = 602257) B602257
theorem B475339 : Blo 421773 475339 := bstep (se 1 (by rfl) ⟨356504, by rfl⟩ : syracuseStep 475339 = 713009) B713009
theorem B950489 : Blo 421773 950489 := bstep (se 2 (by rfl) ⟨356433, by rfl⟩ : syracuseStep 950489 = 712867) B712867
theorem B712921 : Blo 421773 712921 := bstep (se 2 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 712921 = 534691) B534691
theorem B1220825 : Blo 421773 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B1204445 : Blo 421773 1204445 := bstep (se 3 (by rfl) ⟨225833, by rfl⟩ : syracuseStep 1204445 = 451667) B451667
theorem B3621125 : Blo 421773 3621125 := bstep (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) B678961
theorem B13066541 : Blo 421773 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B950579 : Blo 421773 950579 := bstep (se 1 (by rfl) ⟨712934, by rfl⟩ : syracuseStep 950579 = 1425869) B1425869
theorem B475447 : Blo 421773 475447 := bstep (se 1 (by rfl) ⟨356585, by rfl⟩ : syracuseStep 475447 = 713171) B713171
theorem B1073483 : Blo 421773 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B950615 : Blo 421773 950615 := bstep (se 1 (by rfl) ⟨712961, by rfl⟩ : syracuseStep 950615 = 1425923) B1425923
theorem B1425815 : Blo 421773 1425815 := bstep (se 1 (by rfl) ⟨1069361, by rfl⟩ : syracuseStep 1425815 = 2138723) B2138723
theorem B6693299 : Blo 421773 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B1360307 : Blo 421773 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B508375 : Blo 421773 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B475627 : Blo 421773 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B950795 : Blo 421773 950795 := bstep (se 1 (by rfl) ⟨713096, by rfl⟩ : syracuseStep 950795 = 1426193) B1426193
theorem B803351 : Blo 421773 803351 := bstep (se 1 (by rfl) ⟨602513, by rfl⟩ : syracuseStep 803351 = 1205027) B1205027
theorem B1204787 : Blo 421773 1204787 := bstep (se 1 (by rfl) ⟨903590, by rfl⟩ : syracuseStep 1204787 = 1807181) B1807181
theorem B1360435 : Blo 421773 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B950849 : Blo 421773 950849 := bstep (se 2 (by rfl) ⟨356568, by rfl⟩ : syracuseStep 950849 = 713137) B713137
theorem B475735 : Blo 421773 475735 := bstep (se 1 (by rfl) ⟨356801, by rfl⟩ : syracuseStep 475735 = 713603) B713603
theorem B836185 : Blo 421773 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B1352285 : Blo 421773 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B1712771 : Blo 421773 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B1712785 : Blo 421773 1712785 := bstep (se 2 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 1712785 = 1284589) B1284589
theorem B1606337 : Blo 421773 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B1073857 : Blo 421773 1073857 := bstep (se 2 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 1073857 = 805393) B805393
theorem B1360577 : Blo 421773 1360577 := bstep (se 2 (by rfl) ⟨510216, by rfl⟩ : syracuseStep 1360577 = 1020433) B1020433
theorem B475915 : Blo 421773 475915 := bstep (se 1 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 475915 = 713873) B713873
theorem B713495 : Blo 421773 713495 := bstep (se 1 (by rfl) ⟨535121, by rfl⟩ : syracuseStep 713495 = 1070243) B1070243
theorem B951065 : Blo 421773 951065 := bstep (se 2 (by rfl) ⟨356649, by rfl⟩ : syracuseStep 951065 = 713299) B713299
theorem B1360691 : Blo 421773 1360691 := bstep (se 1 (by rfl) ⟨1020518, by rfl⟩ : syracuseStep 1360691 = 2041037) B2041037
theorem B2147147 : Blo 421773 2147147 := bstep (se 1 (by rfl) ⟨1610360, by rfl⟩ : syracuseStep 2147147 = 3220721) B3220721
theorem B951155 : Blo 421773 951155 := bstep (se 1 (by rfl) ⟨713366, by rfl⟩ : syracuseStep 951155 = 1426733) B1426733
theorem B6595445 : Blo 421773 6595445 := bstep (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) B618323
theorem B476023 : Blo 421773 476023 := bstep (se 1 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 476023 = 714035) B714035
theorem B951191 : Blo 421773 951191 := bstep (se 1 (by rfl) ⟨713393, by rfl⟩ : syracuseStep 951191 = 1426787) B1426787
theorem B713623 : Blo 421773 713623 := bstep (se 1 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 713623 = 1070435) B1070435
theorem B1426355 : Blo 421773 1426355 := bstep (se 1 (by rfl) ⟨1069766, by rfl⟩ : syracuseStep 1426355 = 2139533) B2139533
theorem B7234595 : Blo 421773 7234595 := bstep (se 1 (by rfl) ⟨5425946, by rfl⟩ : syracuseStep 7234595 = 10851893) B10851893
theorem B476203 : Blo 421773 476203 := bstep (se 1 (by rfl) ⟨357152, by rfl⟩ : syracuseStep 476203 = 714305) B714305
theorem B9159749 : Blo 421773 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B951371 : Blo 421773 951371 := bstep (se 1 (by rfl) ⟨713528, by rfl⟩ : syracuseStep 951371 = 1427057) B1427057
theorem B2032715 : Blo 421773 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B762967 : Blo 421773 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B943193 : Blo 421773 943193 := bstep (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) B707395
theorem B6186077 : Blo 421773 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B3204197 : Blo 421773 3204197 := bstep (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) B600787
theorem B951425 : Blo 421773 951425 := bstep (se 2 (by rfl) ⟨356784, by rfl⟩ : syracuseStep 951425 = 713569) B713569
theorem B2032771 : Blo 421773 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B2172055 : Blo 421773 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B476311 : Blo 421773 476311 := bstep (se 1 (by rfl) ⟨357233, by rfl⟩ : syracuseStep 476311 = 714467) B714467
theorem B804019 : Blo 421773 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B1426625 : Blo 421773 1426625 := bstep (se 2 (by rfl) ⟨534984, by rfl⟩ : syracuseStep 1426625 = 1069969) B1069969
theorem B1713431 : Blo 421773 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B1074455 : Blo 421773 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B3614017 : Blo 421773 3614017 := bstep (se 2 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 3614017 = 2710513) B2710513
theorem B476491 : Blo 421773 476491 := bstep (se 1 (by rfl) ⟨357368, by rfl⟩ : syracuseStep 476491 = 714737) B714737
theorem B951641 : Blo 421773 951641 := bstep (se 2 (by rfl) ⟨356865, by rfl⟩ : syracuseStep 951641 = 713731) B713731
theorem B951731 : Blo 421773 951731 := bstep (se 1 (by rfl) ⟨713798, by rfl⟩ : syracuseStep 951731 = 1427597) B1427597
theorem B476599 : Blo 421773 476599 := bstep (se 1 (by rfl) ⟨357449, by rfl⟩ : syracuseStep 476599 = 714899) B714899
theorem B1811915 : Blo 421773 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B951767 : Blo 421773 951767 := bstep (se 1 (by rfl) ⟨713825, by rfl⟩ : syracuseStep 951767 = 1427651) B1427651
theorem B714251 : Blo 421773 714251 := bstep (se 1 (by rfl) ⟨535688, by rfl⟩ : syracuseStep 714251 = 1071377) B1071377
theorem B3204683 : Blo 421773 3204683 := bstep (se 1 (by rfl) ⟨2403512, by rfl⟩ : syracuseStep 3204683 = 4807025) B4807025
theorem B1803865 : Blo 421773 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B476779 : Blo 421773 476779 := bstep (se 1 (by rfl) ⟨357584, by rfl⟩ : syracuseStep 476779 = 715169) B715169
theorem B804467 : Blo 421773 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B951947 : Blo 421773 951947 := bstep (se 1 (by rfl) ⟨713960, by rfl⟩ : syracuseStep 951947 = 1427921) B1427921
theorem B714379 : Blo 421773 714379 := bstep (se 1 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 714379 = 1071569) B1071569
theorem B804505 : Blo 421773 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B952001 : Blo 421773 952001 := bstep (se 2 (by rfl) ⟨357000, by rfl⟩ : syracuseStep 952001 = 714001) B714001
theorem B476887 : Blo 421773 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B1427165 : Blo 421773 1427165 := bstep (se 3 (by rfl) ⟨267593, by rfl⟩ : syracuseStep 1427165 = 535187) B535187
theorem B714521 : Blo 421773 714521 := bstep (se 2 (by rfl) ⟨267945, by rfl⟩ : syracuseStep 714521 = 535891) B535891
theorem B763673 : Blo 421773 763673 := bstep (se 2 (by rfl) ⟨286377, by rfl⟩ : syracuseStep 763673 = 572755) B572755
theorem B4130605 : Blo 421773 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B632663 : Blo 421773 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B477067 : Blo 421773 477067 := bstep (se 1 (by rfl) ⟨357800, by rfl⟩ : syracuseStep 477067 = 715601) B715601
theorem B2566039 : Blo 421773 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B632729 : Blo 421773 632729 := bstep (se 2 (by rfl) ⟨237273, by rfl⟩ : syracuseStep 632729 = 474547) B474547
theorem B952217 : Blo 421773 952217 := bstep (se 2 (by rfl) ⟨357081, by rfl⟩ : syracuseStep 952217 = 714163) B714163
theorem B714649 : Blo 421773 714649 := bstep (se 2 (by rfl) ⟨267993, by rfl⟩ : syracuseStep 714649 = 535987) B535987
theorem B1607597 : Blo 421773 1607597 := bstep (se 3 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 1607597 = 602849) B602849
theorem B1607627 : Blo 421773 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B952307 : Blo 421773 952307 := bstep (se 1 (by rfl) ⟨714230, by rfl⟩ : syracuseStep 952307 = 1428461) B1428461
theorem B477175 : Blo 421773 477175 := bstep (se 1 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 477175 = 715763) B715763
theorem B632843 : Blo 421773 632843 := bstep (se 1 (by rfl) ⟨474632, by rfl⟩ : syracuseStep 632843 = 949265) B949265
theorem B534539 : Blo 421773 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B632855 : Blo 421773 632855 := bstep (se 1 (by rfl) ⟨474641, by rfl⟩ : syracuseStep 632855 = 949283) B949283
theorem B952343 : Blo 421773 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B813143 : Blo 421773 813143 := bstep (se 1 (by rfl) ⟨609857, by rfl⟩ : syracuseStep 813143 = 1219715) B1219715
theorem B632921 : Blo 421773 632921 := bstep (se 2 (by rfl) ⟨237345, by rfl⟩ : syracuseStep 632921 = 474691) B474691
theorem B804953 : Blo 421773 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B477355 : Blo 421773 477355 := bstep (se 1 (by rfl) ⟨358016, by rfl⟩ : syracuseStep 477355 = 716033) B716033
theorem B1804481 : Blo 421773 1804481 := bstep (se 2 (by rfl) ⟨676680, by rfl⟩ : syracuseStep 1804481 = 1353361) B1353361
theorem B633035 : Blo 421773 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B952523 : Blo 421773 952523 := bstep (se 1 (by rfl) ⟨714392, by rfl⟩ : syracuseStep 952523 = 1428785) B1428785
theorem B633047 : Blo 421773 633047 := bstep (se 1 (by rfl) ⟨474785, by rfl⟩ : syracuseStep 633047 = 949571) B949571
theorem B6621425 : Blo 421773 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B952577 : Blo 421773 952577 := bstep (se 2 (by rfl) ⟨357216, by rfl⟩ : syracuseStep 952577 = 714433) B714433
theorem B12216581 : Blo 421773 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B469271 : Blo 421773 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B633113 : Blo 421773 633113 := bstep (se 2 (by rfl) ⟨237417, by rfl⟩ : syracuseStep 633113 = 474835) B474835
theorem B477463 : Blo 421773 477463 := bstep (se 1 (by rfl) ⟨358097, by rfl⟩ : syracuseStep 477463 = 716195) B716195
theorem B4827437 : Blo 421773 4827437 := bstep (se 3 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 4827437 = 1810289) B1810289
theorem B428375 : Blo 421773 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B633227 : Blo 421773 633227 := bstep (se 1 (by rfl) ⟨474920, by rfl⟩ : syracuseStep 633227 = 949841) B949841
theorem B633239 : Blo 421773 633239 := bstep (se 1 (by rfl) ⟨474929, by rfl⟩ : syracuseStep 633239 = 949859) B949859
theorem B1812887 : Blo 421773 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B6498737 : Blo 421773 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B477643 : Blo 421773 477643 := bstep (se 1 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 477643 = 716465) B716465
theorem B715223 : Blo 421773 715223 := bstep (se 1 (by rfl) ⟨536417, by rfl⟩ : syracuseStep 715223 = 1072835) B1072835
theorem B633305 : Blo 421773 633305 := bstep (se 2 (by rfl) ⟨237489, by rfl⟩ : syracuseStep 633305 = 474979) B474979
theorem B903641 : Blo 421773 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B952793 : Blo 421773 952793 := bstep (se 2 (by rfl) ⟨357297, by rfl⟩ : syracuseStep 952793 = 714595) B714595
theorem B952883 : Blo 421773 952883 := bstep (se 1 (by rfl) ⟨714662, by rfl⟩ : syracuseStep 952883 = 1429325) B1429325
theorem B477751 : Blo 421773 477751 := bstep (se 1 (by rfl) ⟨358313, by rfl⟩ : syracuseStep 477751 = 716627) B716627
theorem B2148929 : Blo 421773 2148929 := bstep (se 2 (by rfl) ⟨805848, by rfl⟩ : syracuseStep 2148929 = 1611697) B1611697
theorem B633419 : Blo 421773 633419 := bstep (se 1 (by rfl) ⟨475064, by rfl⟩ : syracuseStep 633419 = 950129) B950129
theorem B633431 : Blo 421773 633431 := bstep (se 1 (by rfl) ⟨475073, by rfl⟩ : syracuseStep 633431 = 950147) B950147
theorem B952919 : Blo 421773 952919 := bstep (se 1 (by rfl) ⟨714689, by rfl⟩ : syracuseStep 952919 = 1429379) B1429379
theorem B1608281 : Blo 421773 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B715351 : Blo 421773 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B3213917 : Blo 421773 3213917 := bstep (se 3 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 3213917 = 1205219) B1205219
theorem B633497 : Blo 421773 633497 := bstep (se 2 (by rfl) ⟨237561, by rfl⟩ : syracuseStep 633497 = 475123) B475123
theorem B535243 : Blo 421773 535243 := bstep (se 1 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 535243 = 802865) B802865
theorem B453367 : Blo 421773 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B633611 : Blo 421773 633611 := bstep (se 1 (by rfl) ⟨475208, by rfl⟩ : syracuseStep 633611 = 950417) B950417
theorem B953099 : Blo 421773 953099 := bstep (se 1 (by rfl) ⟨714824, by rfl⟩ : syracuseStep 953099 = 1429649) B1429649
theorem B633623 : Blo 421773 633623 := bstep (se 1 (by rfl) ⟨475217, by rfl⟩ : syracuseStep 633623 = 950435) B950435
theorem B7744301 : Blo 421773 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B5442349 : Blo 421773 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B813889 : Blo 421773 813889 := bstep (se 2 (by rfl) ⟨305208, by rfl⟩ : syracuseStep 813889 = 610417) B610417
theorem B953153 : Blo 421773 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B805697 : Blo 421773 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B1428299 : Blo 421773 1428299 := bstep (se 1 (by rfl) ⟨1071224, by rfl⟩ : syracuseStep 1428299 = 2142449) B2142449
theorem B723799 : Blo 421773 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B633689 : Blo 421773 633689 := bstep (se 2 (by rfl) ⟨237633, by rfl⟩ : syracuseStep 633689 = 475267) B475267
theorem B3910493 : Blo 421773 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B1207133 : Blo 421773 1207133 := bstep (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) B452675
theorem B904051 : Blo 421773 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B1608599 : Blo 421773 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B633803 : Blo 421773 633803 := bstep (se 1 (by rfl) ⟨475352, by rfl⟩ : syracuseStep 633803 = 950705) B950705
theorem B609239 : Blo 421773 609239 := bstep (se 1 (by rfl) ⟨456929, by rfl⟩ : syracuseStep 609239 = 913859) B913859
theorem B633815 : Blo 421773 633815 := bstep (se 1 (by rfl) ⟨475361, by rfl⟩ : syracuseStep 633815 = 950723) B950723
theorem B535511 : Blo 421773 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B1018903 : Blo 421773 1018903 := bstep (se 1 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 1018903 = 1528355) B1528355
theorem B633881 : Blo 421773 633881 := bstep (se 2 (by rfl) ⟨237705, by rfl⟩ : syracuseStep 633881 = 475411) B475411
theorem B953369 : Blo 421773 953369 := bstep (se 2 (by rfl) ⟨357513, by rfl⟩ : syracuseStep 953369 = 715027) B715027
theorem B1207361 : Blo 421773 1207361 := bstep (se 2 (by rfl) ⟨452760, by rfl⟩ : syracuseStep 1207361 = 905521) B905521
theorem B805963 : Blo 421773 805963 := bstep (se 1 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 805963 = 1208945) B1208945
theorem B1428569 : Blo 421773 1428569 := bstep (se 2 (by rfl) ⟨535713, by rfl⟩ : syracuseStep 1428569 = 1071427) B1071427
theorem B953459 : Blo 421773 953459 := bstep (se 1 (by rfl) ⟨715094, by rfl⟩ : syracuseStep 953459 = 1430189) B1430189
theorem B2141315 : Blo 421773 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B4574339 : Blo 421773 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B633995 : Blo 421773 633995 := bstep (se 1 (by rfl) ⟨475496, by rfl⟩ : syracuseStep 633995 = 950993) B950993
theorem B634007 : Blo 421773 634007 := bstep (se 1 (by rfl) ⟨475505, by rfl⟩ : syracuseStep 634007 = 951011) B951011
theorem B953495 : Blo 421773 953495 := bstep (se 1 (by rfl) ⟨715121, by rfl⟩ : syracuseStep 953495 = 1430243) B1430243
theorem B904385 : Blo 421773 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B715979 : Blo 421773 715979 := bstep (se 1 (by rfl) ⟨536984, by rfl⟩ : syracuseStep 715979 = 1073969) B1073969
theorem B634073 : Blo 421773 634073 := bstep (se 2 (by rfl) ⟨237777, by rfl⟩ : syracuseStep 634073 = 475555) B475555
theorem B634187 : Blo 421773 634187 := bstep (se 1 (by rfl) ⟨475640, by rfl⟩ : syracuseStep 634187 = 951281) B951281
theorem B953675 : Blo 421773 953675 := bstep (se 1 (by rfl) ⟨715256, by rfl⟩ : syracuseStep 953675 = 1430513) B1430513
theorem B716107 : Blo 421773 716107 := bstep (se 1 (by rfl) ⟨537080, by rfl⟩ : syracuseStep 716107 = 1074161) B1074161
theorem B634199 : Blo 421773 634199 := bstep (se 1 (by rfl) ⟨475649, by rfl⟩ : syracuseStep 634199 = 951299) B951299
theorem B1625437 : Blo 421773 1625437 := bstep (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) B609539
theorem B953729 : Blo 421773 953729 := bstep (se 2 (by rfl) ⟨357648, by rfl⟩ : syracuseStep 953729 = 715297) B715297
theorem B1207703 : Blo 421773 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B634265 : Blo 421773 634265 := bstep (se 2 (by rfl) ⟨237849, by rfl⟩ : syracuseStep 634265 = 475699) B475699
theorem B1068491 : Blo 421773 1068491 := bstep (se 1 (by rfl) ⟨801368, by rfl⟩ : syracuseStep 1068491 = 1602737) B1602737
theorem B1510859 : Blo 421773 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B716249 : Blo 421773 716249 := bstep (se 2 (by rfl) ⟨268593, by rfl⟩ : syracuseStep 716249 = 537187) B537187
theorem B1224157 : Blo 421773 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B634379 : Blo 421773 634379 := bstep (se 1 (by rfl) ⟨475784, by rfl⟩ : syracuseStep 634379 = 951569) B951569
theorem B6852113 : Blo 421773 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B634391 : Blo 421773 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B1609267 : Blo 421773 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B634457 : Blo 421773 634457 := bstep (se 2 (by rfl) ⟨237921, by rfl⟩ : syracuseStep 634457 = 475843) B475843
theorem B953945 : Blo 421773 953945 := bstep (se 2 (by rfl) ⟨357729, by rfl⟩ : syracuseStep 953945 = 715459) B715459
theorem B716377 : Blo 421773 716377 := bstep (se 2 (by rfl) ⟨268641, by rfl⟩ : syracuseStep 716377 = 537283) B537283
theorem B2412125 : Blo 421773 2412125 := bstep (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) B904547
theorem B536215 : Blo 421773 536215 := bstep (se 1 (by rfl) ⟨402161, by rfl⟩ : syracuseStep 536215 = 804323) B804323
theorem B954035 : Blo 421773 954035 := bstep (se 1 (by rfl) ⟨715526, by rfl⟩ : syracuseStep 954035 = 1431053) B1431053
theorem B7212725 : Blo 421773 7212725 := bstep (se 5 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 7212725 = 676193) B676193
theorem B634571 : Blo 421773 634571 := bstep (se 1 (by rfl) ⟨475928, by rfl⟩ : syracuseStep 634571 = 951857) B951857
theorem B634583 : Blo 421773 634583 := bstep (se 1 (by rfl) ⟨475937, by rfl⟩ : syracuseStep 634583 = 951875) B951875
theorem B954071 : Blo 421773 954071 := bstep (se 1 (by rfl) ⟨715553, by rfl⟩ : syracuseStep 954071 = 1431107) B1431107
theorem B1429271 : Blo 421773 1429271 := bstep (se 1 (by rfl) ⟨1071953, by rfl⟩ : syracuseStep 1429271 = 2143907) B2143907
theorem B634649 : Blo 421773 634649 := bstep (se 2 (by rfl) ⟨237993, by rfl⟩ : syracuseStep 634649 = 475987) B475987
theorem B1543981 : Blo 421773 1543981 := bstep (se 3 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 1543981 = 578993) B578993
theorem B3624749 : Blo 421773 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B1716061 : Blo 421773 1716061 := bstep (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) B643523
theorem B4566901 : Blo 421773 4566901 := bstep (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) B428147
theorem B634763 : Blo 421773 634763 := bstep (se 1 (by rfl) ⟨476072, by rfl⟩ : syracuseStep 634763 = 952145) B952145
theorem B954251 : Blo 421773 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B421783 : Blo 421773 421783 := bstep (se 1 (by rfl) ⟨316337, by rfl⟩ : syracuseStep 421783 = 632675) B632675
theorem B634775 : Blo 421773 634775 := bstep (se 1 (by rfl) ⟨476081, by rfl⟩ : syracuseStep 634775 = 952163) B952163
theorem B905111 : Blo 421773 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B421803 : Blo 421773 421803 := bstep (se 1 (by rfl) ⟨316352, by rfl⟩ : syracuseStep 421803 = 632705) B632705
theorem B10825649 : Blo 421773 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B421815 : Blo 421773 421815 := bstep (se 1 (by rfl) ⟨316361, by rfl⟩ : syracuseStep 421815 = 632723) B632723
theorem B954305 : Blo 421773 954305 := bstep (se 2 (by rfl) ⟨357864, by rfl⟩ : syracuseStep 954305 = 715729) B715729
theorem B421835 : Blo 421773 421835 := bstep (se 1 (by rfl) ⟨316376, by rfl⟩ : syracuseStep 421835 = 632753) B632753
theorem B421847 : Blo 421773 421847 := bstep (se 1 (by rfl) ⟨316385, by rfl⟩ : syracuseStep 421847 = 632771) B632771
theorem B634841 : Blo 421773 634841 := bstep (se 2 (by rfl) ⟨238065, by rfl⟩ : syracuseStep 634841 = 476131) B476131
theorem B421867 : Blo 421773 421867 := bstep (se 1 (by rfl) ⟨316400, by rfl⟩ : syracuseStep 421867 = 632801) B632801
theorem B421879 : Blo 421773 421879 := bstep (se 1 (by rfl) ⟨316409, by rfl⟩ : syracuseStep 421879 = 632819) B632819
theorem B421899 : Blo 421773 421899 := bstep (se 1 (by rfl) ⟨316424, by rfl⟩ : syracuseStep 421899 = 632849) B632849
theorem B421911 : Blo 421773 421911 := bstep (se 1 (by rfl) ⟨316433, by rfl⟩ : syracuseStep 421911 = 632867) B632867
theorem B421931 : Blo 421773 421931 := bstep (se 1 (by rfl) ⟨316448, by rfl⟩ : syracuseStep 421931 = 632897) B632897
theorem B421943 : Blo 421773 421943 := bstep (se 1 (by rfl) ⟨316457, by rfl⟩ : syracuseStep 421943 = 632915) B632915
theorem B421963 : Blo 421773 421963 := bstep (se 1 (by rfl) ⟨316472, by rfl⟩ : syracuseStep 421963 = 632945) B632945
theorem B634955 : Blo 421773 634955 := bstep (se 1 (by rfl) ⟨476216, by rfl⟩ : syracuseStep 634955 = 952433) B952433
theorem B421975 : Blo 421773 421975 := bstep (se 1 (by rfl) ⟨316481, by rfl⟩ : syracuseStep 421975 = 632963) B632963
theorem B634967 : Blo 421773 634967 := bstep (se 1 (by rfl) ⟨476225, by rfl⟩ : syracuseStep 634967 = 952451) B952451
theorem B421995 : Blo 421773 421995 := bstep (se 1 (by rfl) ⟨316496, by rfl⟩ : syracuseStep 421995 = 632993) B632993
theorem B422007 : Blo 421773 422007 := bstep (se 1 (by rfl) ⟨316505, by rfl⟩ : syracuseStep 422007 = 633011) B633011
theorem B422027 : Blo 421773 422027 := bstep (se 1 (by rfl) ⟨316520, by rfl⟩ : syracuseStep 422027 = 633041) B633041
theorem B422039 : Blo 421773 422039 := bstep (se 1 (by rfl) ⟨316529, by rfl⟩ : syracuseStep 422039 = 633059) B633059
theorem B5165207 : Blo 421773 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B635033 : Blo 421773 635033 := bstep (se 2 (by rfl) ⟨238137, by rfl⟩ : syracuseStep 635033 = 476275) B476275
theorem B954521 : Blo 421773 954521 := bstep (se 2 (by rfl) ⟨357945, by rfl⟩ : syracuseStep 954521 = 715891) B715891
theorem B422059 : Blo 421773 422059 := bstep (se 1 (by rfl) ⟨316544, by rfl⟩ : syracuseStep 422059 = 633089) B633089
theorem B2027699 : Blo 421773 2027699 := bstep (se 1 (by rfl) ⟨1520774, by rfl⟩ : syracuseStep 2027699 = 3041549) B3041549
theorem B422071 : Blo 421773 422071 := bstep (se 1 (by rfl) ⟨316553, by rfl⟩ : syracuseStep 422071 = 633107) B633107
theorem B422091 : Blo 421773 422091 := bstep (se 1 (by rfl) ⟨316568, by rfl⟩ : syracuseStep 422091 = 633137) B633137
theorem B422103 : Blo 421773 422103 := bstep (se 1 (by rfl) ⟨316577, by rfl⟩ : syracuseStep 422103 = 633155) B633155
theorem B3420377 : Blo 421773 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B856279 : Blo 421773 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B422123 : Blo 421773 422123 := bstep (se 1 (by rfl) ⟨316592, by rfl⟩ : syracuseStep 422123 = 633185) B633185
theorem B954611 : Blo 421773 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B422135 : Blo 421773 422135 := bstep (se 1 (by rfl) ⟨316601, by rfl⟩ : syracuseStep 422135 = 633203) B633203
theorem B1601795 : Blo 421773 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B422155 : Blo 421773 422155 := bstep (se 1 (by rfl) ⟨316616, by rfl⟩ : syracuseStep 422155 = 633233) B633233
theorem B635147 : Blo 421773 635147 := bstep (se 1 (by rfl) ⟨476360, by rfl⟩ : syracuseStep 635147 = 952721) B952721
theorem B422167 : Blo 421773 422167 := bstep (se 1 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 422167 = 633251) B633251
theorem B635159 : Blo 421773 635159 := bstep (se 1 (by rfl) ⟨476369, by rfl⟩ : syracuseStep 635159 = 952739) B952739
theorem B954647 : Blo 421773 954647 := bstep (se 1 (by rfl) ⟨715985, by rfl⟩ : syracuseStep 954647 = 1431971) B1431971
theorem B422187 : Blo 421773 422187 := bstep (se 1 (by rfl) ⟨316640, by rfl⟩ : syracuseStep 422187 = 633281) B633281
theorem B1429811 : Blo 421773 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B422199 : Blo 421773 422199 := bstep (se 1 (by rfl) ⟨316649, by rfl⟩ : syracuseStep 422199 = 633299) B633299
theorem B422219 : Blo 421773 422219 := bstep (se 1 (by rfl) ⟨316664, by rfl⟩ : syracuseStep 422219 = 633329) B633329
theorem B422231 : Blo 421773 422231 := bstep (se 1 (by rfl) ⟨316673, by rfl⟩ : syracuseStep 422231 = 633347) B633347
theorem B635225 : Blo 421773 635225 := bstep (se 2 (by rfl) ⟨238209, by rfl⟩ : syracuseStep 635225 = 476419) B476419
theorem B422251 : Blo 421773 422251 := bstep (se 1 (by rfl) ⟨316688, by rfl⟩ : syracuseStep 422251 = 633377) B633377
theorem B422263 : Blo 421773 422263 := bstep (se 1 (by rfl) ⟨316697, by rfl⟩ : syracuseStep 422263 = 633395) B633395
theorem B422283 : Blo 421773 422283 := bstep (se 1 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 422283 = 633425) B633425
theorem B422295 : Blo 421773 422295 := bstep (se 1 (by rfl) ⟨316721, by rfl⟩ : syracuseStep 422295 = 633443) B633443
theorem B1069463 : Blo 421773 1069463 := bstep (se 1 (by rfl) ⟨802097, by rfl⟩ : syracuseStep 1069463 = 1604195) B1604195
theorem B422315 : Blo 421773 422315 := bstep (se 1 (by rfl) ⟨316736, by rfl⟩ : syracuseStep 422315 = 633473) B633473
theorem B422327 : Blo 421773 422327 := bstep (se 1 (by rfl) ⟨316745, by rfl⟩ : syracuseStep 422327 = 633491) B633491
theorem B422347 : Blo 421773 422347 := bstep (se 1 (by rfl) ⟨316760, by rfl⟩ : syracuseStep 422347 = 633521) B633521
theorem B635339 : Blo 421773 635339 := bstep (se 1 (by rfl) ⟨476504, by rfl⟩ : syracuseStep 635339 = 953009) B953009
theorem B954827 : Blo 421773 954827 := bstep (se 1 (by rfl) ⟨716120, by rfl⟩ : syracuseStep 954827 = 1432241) B1432241
theorem B422359 : Blo 421773 422359 := bstep (se 1 (by rfl) ⟨316769, by rfl⟩ : syracuseStep 422359 = 633539) B633539
theorem B635351 : Blo 421773 635351 := bstep (se 1 (by rfl) ⟨476513, by rfl⟩ : syracuseStep 635351 = 953027) B953027
theorem B1446365 : Blo 421773 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B422379 : Blo 421773 422379 := bstep (se 1 (by rfl) ⟨316784, by rfl⟩ : syracuseStep 422379 = 633569) B633569
theorem B422391 : Blo 421773 422391 := bstep (se 1 (by rfl) ⟨316793, by rfl⟩ : syracuseStep 422391 = 633587) B633587
theorem B954881 : Blo 421773 954881 := bstep (se 2 (by rfl) ⟨358080, by rfl⟩ : syracuseStep 954881 = 716161) B716161
theorem B422411 : Blo 421773 422411 := bstep (se 1 (by rfl) ⟨316808, by rfl⟩ : syracuseStep 422411 = 633617) B633617
theorem B3248657 : Blo 421773 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B422423 : Blo 421773 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B635417 : Blo 421773 635417 := bstep (se 2 (by rfl) ⟨238281, by rfl⟩ : syracuseStep 635417 = 476563) B476563
theorem B422443 : Blo 421773 422443 := bstep (se 1 (by rfl) ⟨316832, by rfl⟩ : syracuseStep 422443 = 633665) B633665
theorem B422455 : Blo 421773 422455 := bstep (se 1 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 422455 = 633683) B633683
theorem B1430081 : Blo 421773 1430081 := bstep (se 2 (by rfl) ⟨536280, by rfl⟩ : syracuseStep 1430081 = 1072561) B1072561
theorem B422475 : Blo 421773 422475 := bstep (se 1 (by rfl) ⟨316856, by rfl⟩ : syracuseStep 422475 = 633713) B633713
theorem B856651 : Blo 421773 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B422487 : Blo 421773 422487 := bstep (se 1 (by rfl) ⟨316865, by rfl⟩ : syracuseStep 422487 = 633731) B633731
theorem B1806941 : Blo 421773 1806941 := bstep (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) B677603
theorem B422507 : Blo 421773 422507 := bstep (se 1 (by rfl) ⟨316880, by rfl⟩ : syracuseStep 422507 = 633761) B633761
theorem B422519 : Blo 421773 422519 := bstep (se 1 (by rfl) ⟨316889, by rfl⟩ : syracuseStep 422519 = 633779) B633779
theorem B422539 : Blo 421773 422539 := bstep (se 1 (by rfl) ⟨316904, by rfl⟩ : syracuseStep 422539 = 633809) B633809
theorem B635531 : Blo 421773 635531 := bstep (se 1 (by rfl) ⟨476648, by rfl⟩ : syracuseStep 635531 = 953297) B953297
theorem B422551 : Blo 421773 422551 := bstep (se 1 (by rfl) ⟨316913, by rfl⟩ : syracuseStep 422551 = 633827) B633827
theorem B635543 : Blo 421773 635543 := bstep (se 1 (by rfl) ⟨476657, by rfl⟩ : syracuseStep 635543 = 953315) B953315
theorem B422571 : Blo 421773 422571 := bstep (se 1 (by rfl) ⟨316928, by rfl⟩ : syracuseStep 422571 = 633857) B633857
theorem B1020595 : Blo 421773 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B422583 : Blo 421773 422583 := bstep (se 1 (by rfl) ⟨316937, by rfl⟩ : syracuseStep 422583 = 633875) B633875
theorem B1602251 : Blo 421773 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B422603 : Blo 421773 422603 := bstep (se 1 (by rfl) ⟨316952, by rfl⟩ : syracuseStep 422603 = 633905) B633905
theorem B422615 : Blo 421773 422615 := bstep (se 1 (by rfl) ⟨316961, by rfl⟩ : syracuseStep 422615 = 633923) B633923
theorem B635609 : Blo 421773 635609 := bstep (se 2 (by rfl) ⟨238353, by rfl⟩ : syracuseStep 635609 = 476707) B476707
theorem B955097 : Blo 421773 955097 := bstep (se 2 (by rfl) ⟨358161, by rfl⟩ : syracuseStep 955097 = 716323) B716323
theorem B422635 : Blo 421773 422635 := bstep (se 1 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 422635 = 633953) B633953
theorem B422647 : Blo 421773 422647 := bstep (se 1 (by rfl) ⟨316985, by rfl⟩ : syracuseStep 422647 = 633971) B633971
theorem B422667 : Blo 421773 422667 := bstep (se 1 (by rfl) ⟨317000, by rfl⟩ : syracuseStep 422667 = 634001) B634001
theorem B1610513 : Blo 421773 1610513 := bstep (se 2 (by rfl) ⟨603942, by rfl⟩ : syracuseStep 1610513 = 1207885) B1207885
theorem B422679 : Blo 421773 422679 := bstep (se 1 (by rfl) ⟨317009, by rfl⟩ : syracuseStep 422679 = 634019) B634019
theorem B422699 : Blo 421773 422699 := bstep (se 1 (by rfl) ⟨317024, by rfl⟩ : syracuseStep 422699 = 634049) B634049
theorem B1307443 : Blo 421773 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B955187 : Blo 421773 955187 := bstep (se 1 (by rfl) ⟨716390, by rfl⟩ : syracuseStep 955187 = 1432781) B1432781
theorem B422711 : Blo 421773 422711 := bstep (se 1 (by rfl) ⟨317033, by rfl⟩ : syracuseStep 422711 = 634067) B634067
theorem B422731 : Blo 421773 422731 := bstep (se 1 (by rfl) ⟨317048, by rfl⟩ : syracuseStep 422731 = 634097) B634097
theorem B635723 : Blo 421773 635723 := bstep (se 1 (by rfl) ⟨476792, by rfl⟩ : syracuseStep 635723 = 953585) B953585
theorem B422743 : Blo 421773 422743 := bstep (se 1 (by rfl) ⟨317057, by rfl⟩ : syracuseStep 422743 = 634115) B634115
theorem B635735 : Blo 421773 635735 := bstep (se 1 (by rfl) ⟨476801, by rfl⟩ : syracuseStep 635735 = 953603) B953603
theorem B955223 : Blo 421773 955223 := bstep (se 1 (by rfl) ⟨716417, by rfl⟩ : syracuseStep 955223 = 1432835) B1432835
theorem B422763 : Blo 421773 422763 := bstep (se 1 (by rfl) ⟨317072, by rfl⟩ : syracuseStep 422763 = 634145) B634145
theorem B422775 : Blo 421773 422775 := bstep (se 1 (by rfl) ⟨317081, by rfl⟩ : syracuseStep 422775 = 634163) B634163
theorem B422795 : Blo 421773 422795 := bstep (se 1 (by rfl) ⟨317096, by rfl⟩ : syracuseStep 422795 = 634193) B634193
theorem B1602449 : Blo 421773 1602449 := bstep (se 2 (by rfl) ⟨600918, by rfl⟩ : syracuseStep 1602449 = 1201837) B1201837
theorem B422807 : Blo 421773 422807 := bstep (se 1 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 422807 = 634211) B634211
theorem B635801 : Blo 421773 635801 := bstep (se 2 (by rfl) ⟨238425, by rfl⟩ : syracuseStep 635801 = 476851) B476851
theorem B422827 : Blo 421773 422827 := bstep (se 1 (by rfl) ⟨317120, by rfl⟩ : syracuseStep 422827 = 634241) B634241
theorem B422839 : Blo 421773 422839 := bstep (se 1 (by rfl) ⟨317129, by rfl⟩ : syracuseStep 422839 = 634259) B634259
theorem B422859 : Blo 421773 422859 := bstep (se 1 (by rfl) ⟨317144, by rfl⟩ : syracuseStep 422859 = 634289) B634289
theorem B652235 : Blo 421773 652235 := bstep (se 1 (by rfl) ⟨489176, by rfl⟩ : syracuseStep 652235 = 978353) B978353
theorem B422871 : Blo 421773 422871 := bstep (se 1 (by rfl) ⟨317153, by rfl⟩ : syracuseStep 422871 = 634307) B634307
theorem B422891 : Blo 421773 422891 := bstep (se 1 (by rfl) ⟨317168, by rfl⟩ : syracuseStep 422891 = 634337) B634337
theorem B422903 : Blo 421773 422903 := bstep (se 1 (by rfl) ⟨317177, by rfl⟩ : syracuseStep 422903 = 634355) B634355
theorem B422923 : Blo 421773 422923 := bstep (se 1 (by rfl) ⟨317192, by rfl⟩ : syracuseStep 422923 = 634385) B634385
theorem B635915 : Blo 421773 635915 := bstep (se 1 (by rfl) ⟨476936, by rfl⟩ : syracuseStep 635915 = 953873) B953873
theorem B955403 : Blo 421773 955403 := bstep (se 1 (by rfl) ⟨716552, by rfl⟩ : syracuseStep 955403 = 1433105) B1433105
theorem B422935 : Blo 421773 422935 := bstep (se 1 (by rfl) ⟨317201, by rfl⟩ : syracuseStep 422935 = 634403) B634403
theorem B635927 : Blo 421773 635927 := bstep (se 1 (by rfl) ⟨476945, by rfl⟩ : syracuseStep 635927 = 953891) B953891
theorem B422955 : Blo 421773 422955 := bstep (se 1 (by rfl) ⟨317216, by rfl⟩ : syracuseStep 422955 = 634433) B634433
theorem B1070131 : Blo 421773 1070131 := bstep (se 1 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 1070131 = 1605197) B1605197
theorem B422967 : Blo 421773 422967 := bstep (se 1 (by rfl) ⟨317225, by rfl⟩ : syracuseStep 422967 = 634451) B634451
theorem B955457 : Blo 421773 955457 := bstep (se 2 (by rfl) ⟨358296, by rfl⟩ : syracuseStep 955457 = 716593) B716593
theorem B422987 : Blo 421773 422987 := bstep (se 1 (by rfl) ⟨317240, by rfl⟩ : syracuseStep 422987 = 634481) B634481
theorem B422999 : Blo 421773 422999 := bstep (se 1 (by rfl) ⟨317249, by rfl⟩ : syracuseStep 422999 = 634499) B634499
theorem B635993 : Blo 421773 635993 := bstep (se 2 (by rfl) ⟨238497, by rfl⟩ : syracuseStep 635993 = 476995) B476995
theorem B1430621 : Blo 421773 1430621 := bstep (se 3 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 1430621 = 536483) B536483
theorem B423019 : Blo 421773 423019 := bstep (se 1 (by rfl) ⟨317264, by rfl⟩ : syracuseStep 423019 = 634529) B634529
theorem B423031 : Blo 421773 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B423051 : Blo 421773 423051 := bstep (se 1 (by rfl) ⟨317288, by rfl⟩ : syracuseStep 423051 = 634577) B634577
theorem B423063 : Blo 421773 423063 := bstep (se 1 (by rfl) ⟨317297, by rfl⟩ : syracuseStep 423063 = 634595) B634595
theorem B423083 : Blo 421773 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B423095 : Blo 421773 423095 := bstep (se 1 (by rfl) ⟨317321, by rfl⟩ : syracuseStep 423095 = 634643) B634643
theorem B1070273 : Blo 421773 1070273 := bstep (se 2 (by rfl) ⟨401352, by rfl⟩ : syracuseStep 1070273 = 802705) B802705
theorem B423115 : Blo 421773 423115 := bstep (se 1 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 423115 = 634673) B634673
theorem B636107 : Blo 421773 636107 := bstep (se 1 (by rfl) ⟨477080, by rfl⟩ : syracuseStep 636107 = 954161) B954161
theorem B423127 : Blo 421773 423127 := bstep (se 1 (by rfl) ⟨317345, by rfl⟩ : syracuseStep 423127 = 634691) B634691
theorem B636119 : Blo 421773 636119 := bstep (se 1 (by rfl) ⟨477089, by rfl⟩ : syracuseStep 636119 = 954179) B954179
theorem B423147 : Blo 421773 423147 := bstep (se 1 (by rfl) ⟨317360, by rfl⟩ : syracuseStep 423147 = 634721) B634721
theorem B423159 : Blo 421773 423159 := bstep (se 1 (by rfl) ⟨317369, by rfl⟩ : syracuseStep 423159 = 634739) B634739
theorem B423179 : Blo 421773 423179 := bstep (se 1 (by rfl) ⟨317384, by rfl⟩ : syracuseStep 423179 = 634769) B634769
theorem B423191 : Blo 421773 423191 := bstep (se 1 (by rfl) ⟨317393, by rfl⟩ : syracuseStep 423191 = 634787) B634787
theorem B636185 : Blo 421773 636185 := bstep (se 2 (by rfl) ⟨238569, by rfl⟩ : syracuseStep 636185 = 477139) B477139
theorem B955673 : Blo 421773 955673 := bstep (se 2 (by rfl) ⟨358377, by rfl⟩ : syracuseStep 955673 = 716755) B716755
theorem B423211 : Blo 421773 423211 := bstep (se 1 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 423211 = 634817) B634817
theorem B2716973 : Blo 421773 2716973 := bstep (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) B1018865
theorem B423223 : Blo 421773 423223 := bstep (se 1 (by rfl) ⟨317417, by rfl⟩ : syracuseStep 423223 = 634835) B634835
theorem B1201483 : Blo 421773 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B423243 : Blo 421773 423243 := bstep (se 1 (by rfl) ⟨317432, by rfl⟩ : syracuseStep 423243 = 634865) B634865
theorem B423255 : Blo 421773 423255 := bstep (se 1 (by rfl) ⟨317441, by rfl⟩ : syracuseStep 423255 = 634883) B634883
theorem B1070425 : Blo 421773 1070425 := bstep (se 2 (by rfl) ⟨401409, by rfl⟩ : syracuseStep 1070425 = 802819) B802819
theorem B4330853 : Blo 421773 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B423275 : Blo 421773 423275 := bstep (se 1 (by rfl) ⟨317456, by rfl⟩ : syracuseStep 423275 = 634913) B634913
theorem B423287 : Blo 421773 423287 := bstep (se 1 (by rfl) ⟨317465, by rfl⟩ : syracuseStep 423287 = 634931) B634931
theorem B423307 : Blo 421773 423307 := bstep (se 1 (by rfl) ⟨317480, by rfl⟩ : syracuseStep 423307 = 634961) B634961
theorem B636299 : Blo 421773 636299 := bstep (se 1 (by rfl) ⟨477224, by rfl⟩ : syracuseStep 636299 = 954449) B954449
theorem B423319 : Blo 421773 423319 := bstep (se 1 (by rfl) ⟨317489, by rfl⟩ : syracuseStep 423319 = 634979) B634979
theorem B636311 : Blo 421773 636311 := bstep (se 1 (by rfl) ⟨477233, by rfl⟩ : syracuseStep 636311 = 954467) B954467
theorem B423339 : Blo 421773 423339 := bstep (se 1 (by rfl) ⟨317504, by rfl⟩ : syracuseStep 423339 = 635009) B635009
theorem B5854643 : Blo 421773 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B423351 : Blo 421773 423351 := bstep (se 1 (by rfl) ⟨317513, by rfl⟩ : syracuseStep 423351 = 635027) B635027
theorem B423371 : Blo 421773 423371 := bstep (se 1 (by rfl) ⟨317528, by rfl⟩ : syracuseStep 423371 = 635057) B635057
theorem B1611211 : Blo 421773 1611211 := bstep (se 1 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 1611211 = 2416817) B2416817
theorem B423383 : Blo 421773 423383 := bstep (se 1 (by rfl) ⟨317537, by rfl⟩ : syracuseStep 423383 = 635075) B635075
theorem B603607 : Blo 421773 603607 := bstep (se 1 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 603607 = 905411) B905411
theorem B636377 : Blo 421773 636377 := bstep (se 2 (by rfl) ⟨238641, by rfl⟩ : syracuseStep 636377 = 477283) B477283
theorem B423403 : Blo 421773 423403 := bstep (se 1 (by rfl) ⟨317552, by rfl⟩ : syracuseStep 423403 = 635105) B635105
theorem B423415 : Blo 421773 423415 := bstep (se 1 (by rfl) ⟨317561, by rfl⟩ : syracuseStep 423415 = 635123) B635123
theorem B423435 : Blo 421773 423435 := bstep (se 1 (by rfl) ⟨317576, by rfl⟩ : syracuseStep 423435 = 635153) B635153
theorem B423447 : Blo 421773 423447 := bstep (se 1 (by rfl) ⟨317585, by rfl⟩ : syracuseStep 423447 = 635171) B635171
theorem B423467 : Blo 421773 423467 := bstep (se 1 (by rfl) ⟨317600, by rfl⟩ : syracuseStep 423467 = 635201) B635201
theorem B1963565 : Blo 421773 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B423479 : Blo 421773 423479 := bstep (se 1 (by rfl) ⟨317609, by rfl⟩ : syracuseStep 423479 = 635219) B635219
theorem B423499 : Blo 421773 423499 := bstep (se 1 (by rfl) ⟨317624, by rfl⟩ : syracuseStep 423499 = 635249) B635249
theorem B636491 : Blo 421773 636491 := bstep (se 1 (by rfl) ⟨477368, by rfl⟩ : syracuseStep 636491 = 954737) B954737
theorem B423511 : Blo 421773 423511 := bstep (se 1 (by rfl) ⟨317633, by rfl⟩ : syracuseStep 423511 = 635267) B635267
theorem B636503 : Blo 421773 636503 := bstep (se 1 (by rfl) ⟨477377, by rfl⟩ : syracuseStep 636503 = 954755) B954755
theorem B2135645 : Blo 421773 2135645 := bstep (se 3 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 2135645 = 800867) B800867
theorem B423531 : Blo 421773 423531 := bstep (se 1 (by rfl) ⟨317648, by rfl⟩ : syracuseStep 423531 = 635297) B635297
theorem B423543 : Blo 421773 423543 := bstep (se 1 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 423543 = 635315) B635315
theorem B423563 : Blo 421773 423563 := bstep (se 1 (by rfl) ⟨317672, by rfl⟩ : syracuseStep 423563 = 635345) B635345
theorem B1603223 : Blo 421773 1603223 := bstep (se 1 (by rfl) ⟨1202417, by rfl⟩ : syracuseStep 1603223 = 2404835) B2404835
theorem B423575 : Blo 421773 423575 := bstep (se 1 (by rfl) ⟨317681, by rfl⟩ : syracuseStep 423575 = 635363) B635363
theorem B636569 : Blo 421773 636569 := bstep (se 2 (by rfl) ⟨238713, by rfl⟩ : syracuseStep 636569 = 477427) B477427
theorem B423595 : Blo 421773 423595 := bstep (se 1 (by rfl) ⟨317696, by rfl⟩ : syracuseStep 423595 = 635393) B635393
theorem B1562285 : Blo 421773 1562285 := bstep (se 3 (by rfl) ⟨292928, by rfl⟩ : syracuseStep 1562285 = 585857) B585857
theorem B423607 : Blo 421773 423607 := bstep (se 1 (by rfl) ⟨317705, by rfl⟩ : syracuseStep 423607 = 635411) B635411
theorem B423627 : Blo 421773 423627 := bstep (se 1 (by rfl) ⟨317720, by rfl⟩ : syracuseStep 423627 = 635441) B635441
theorem B423639 : Blo 421773 423639 := bstep (se 1 (by rfl) ⟨317729, by rfl⟩ : syracuseStep 423639 = 635459) B635459
theorem B1013465 : Blo 421773 1013465 := bstep (se 2 (by rfl) ⟨380049, by rfl⟩ : syracuseStep 1013465 = 760099) B760099
theorem B1611485 : Blo 421773 1611485 := bstep (se 3 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 1611485 = 604307) B604307
theorem B423659 : Blo 421773 423659 := bstep (se 1 (by rfl) ⟨317744, by rfl⟩ : syracuseStep 423659 = 635489) B635489
theorem B423671 : Blo 421773 423671 := bstep (se 1 (by rfl) ⟨317753, by rfl⟩ : syracuseStep 423671 = 635507) B635507
theorem B4888325 : Blo 421773 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B423691 : Blo 421773 423691 := bstep (se 1 (by rfl) ⟨317768, by rfl⟩ : syracuseStep 423691 = 635537) B635537
theorem B636683 : Blo 421773 636683 := bstep (se 1 (by rfl) ⟨477512, by rfl⟩ : syracuseStep 636683 = 955025) B955025
theorem B423703 : Blo 421773 423703 := bstep (se 1 (by rfl) ⟨317777, by rfl⟩ : syracuseStep 423703 = 635555) B635555
theorem B636695 : Blo 421773 636695 := bstep (se 1 (by rfl) ⟨477521, by rfl⟩ : syracuseStep 636695 = 955043) B955043
theorem B423723 : Blo 421773 423723 := bstep (se 1 (by rfl) ⟨317792, by rfl⟩ : syracuseStep 423723 = 635585) B635585
theorem B423735 : Blo 421773 423735 := bstep (se 1 (by rfl) ⟨317801, by rfl⟩ : syracuseStep 423735 = 635603) B635603
theorem B1201985 : Blo 421773 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B423755 : Blo 421773 423755 := bstep (se 1 (by rfl) ⟨317816, by rfl⟩ : syracuseStep 423755 = 635633) B635633
theorem B423767 : Blo 421773 423767 := bstep (se 1 (by rfl) ⟨317825, by rfl⟩ : syracuseStep 423767 = 635651) B635651
theorem B636761 : Blo 421773 636761 := bstep (se 2 (by rfl) ⟨238785, by rfl⟩ : syracuseStep 636761 = 477571) B477571
theorem B1603421 : Blo 421773 1603421 := bstep (se 3 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 1603421 = 601283) B601283
theorem B2283365 : Blo 421773 2283365 := bstep (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) B428131
theorem B7247717 : Blo 421773 7247717 := bstep (se 4 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 7247717 = 1358947) B1358947
theorem B423787 : Blo 421773 423787 := bstep (se 1 (by rfl) ⟨317840, by rfl⟩ : syracuseStep 423787 = 635681) B635681
theorem B423799 : Blo 421773 423799 := bstep (se 1 (by rfl) ⟨317849, by rfl⟩ : syracuseStep 423799 = 635699) B635699
theorem B423819 : Blo 421773 423819 := bstep (se 1 (by rfl) ⟨317864, by rfl⟩ : syracuseStep 423819 = 635729) B635729
theorem B677783 : Blo 421773 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B423831 : Blo 421773 423831 := bstep (se 1 (by rfl) ⟨317873, by rfl⟩ : syracuseStep 423831 = 635747) B635747
theorem B423851 : Blo 421773 423851 := bstep (se 1 (by rfl) ⟨317888, by rfl⟩ : syracuseStep 423851 = 635777) B635777
theorem B423863 : Blo 421773 423863 := bstep (se 1 (by rfl) ⟨317897, by rfl⟩ : syracuseStep 423863 = 635795) B635795
theorem B1521611 : Blo 421773 1521611 := bstep (se 1 (by rfl) ⟨1141208, by rfl⟩ : syracuseStep 1521611 = 2282417) B2282417
theorem B423883 : Blo 421773 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B645067 : Blo 421773 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B636875 : Blo 421773 636875 := bstep (se 1 (by rfl) ⟨477656, by rfl⟩ : syracuseStep 636875 = 955313) B955313
theorem B423895 : Blo 421773 423895 := bstep (se 1 (by rfl) ⟨317921, by rfl⟩ : syracuseStep 423895 = 635843) B635843
theorem B636887 : Blo 421773 636887 := bstep (se 1 (by rfl) ⟨477665, by rfl⟩ : syracuseStep 636887 = 955331) B955331
theorem B423915 : Blo 421773 423915 := bstep (se 1 (by rfl) ⟨317936, by rfl⟩ : syracuseStep 423915 = 635873) B635873
theorem B423927 : Blo 421773 423927 := bstep (se 1 (by rfl) ⟨317945, by rfl⟩ : syracuseStep 423927 = 635891) B635891
theorem B423947 : Blo 421773 423947 := bstep (se 1 (by rfl) ⟨317960, by rfl⟩ : syracuseStep 423947 = 635921) B635921
theorem B2414609 : Blo 421773 2414609 := bstep (se 2 (by rfl) ⟨905478, by rfl⟩ : syracuseStep 2414609 = 1810957) B1810957
theorem B677911 : Blo 421773 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B1357847 : Blo 421773 1357847 := bstep (se 1 (by rfl) ⟨1018385, by rfl⟩ : syracuseStep 1357847 = 2036771) B2036771
theorem B423959 : Blo 421773 423959 := bstep (se 1 (by rfl) ⟨317969, by rfl⟩ : syracuseStep 423959 = 635939) B635939
theorem B636953 : Blo 421773 636953 := bstep (se 2 (by rfl) ⟨238857, by rfl⟩ : syracuseStep 636953 = 477715) B477715
theorem B423979 : Blo 421773 423979 := bstep (se 1 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 423979 = 635969) B635969
theorem B423991 : Blo 421773 423991 := bstep (se 1 (by rfl) ⟨317993, by rfl⟩ : syracuseStep 423991 = 635987) B635987
theorem B424011 : Blo 421773 424011 := bstep (se 1 (by rfl) ⟨318008, by rfl⟩ : syracuseStep 424011 = 636017) B636017
theorem B424023 : Blo 421773 424023 := bstep (se 1 (by rfl) ⟨318017, by rfl⟩ : syracuseStep 424023 = 636035) B636035
theorem B424043 : Blo 421773 424043 := bstep (se 1 (by rfl) ⟨318032, by rfl⟩ : syracuseStep 424043 = 636065) B636065
theorem B424055 : Blo 421773 424055 := bstep (se 1 (by rfl) ⟨318041, by rfl⟩ : syracuseStep 424055 = 636083) B636083
theorem B3627139 : Blo 421773 3627139 := bstep (se 1 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 3627139 = 5440709) B5440709
theorem B424075 : Blo 421773 424075 := bstep (se 1 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 424075 = 636113) B636113
theorem B637067 : Blo 421773 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B1202327 : Blo 421773 1202327 := bstep (se 1 (by rfl) ⟨901745, by rfl⟩ : syracuseStep 1202327 = 1803491) B1803491
theorem B424087 : Blo 421773 424087 := bstep (se 1 (by rfl) ⟨318065, by rfl⟩ : syracuseStep 424087 = 636131) B636131
theorem B800921 : Blo 421773 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B637079 : Blo 421773 637079 := bstep (se 1 (by rfl) ⟨477809, by rfl⟩ : syracuseStep 637079 = 955619) B955619
theorem B424107 : Blo 421773 424107 := bstep (se 1 (by rfl) ⟨318080, by rfl⟩ : syracuseStep 424107 = 636161) B636161
theorem B424119 : Blo 421773 424119 := bstep (se 1 (by rfl) ⟨318089, by rfl⟩ : syracuseStep 424119 = 636179) B636179
theorem B424139 : Blo 421773 424139 := bstep (se 1 (by rfl) ⟨318104, by rfl⟩ : syracuseStep 424139 = 636209) B636209
theorem B1431755 : Blo 421773 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B424151 : Blo 421773 424151 := bstep (se 1 (by rfl) ⟨318113, by rfl⟩ : syracuseStep 424151 = 636227) B636227
theorem B645335 : Blo 421773 645335 := bstep (se 1 (by rfl) ⟨484001, by rfl⟩ : syracuseStep 645335 = 968003) B968003
theorem B637145 : Blo 421773 637145 := bstep (se 2 (by rfl) ⟨238929, by rfl⟩ : syracuseStep 637145 = 477859) B477859
theorem B424171 : Blo 421773 424171 := bstep (se 1 (by rfl) ⟨318128, by rfl⟩ : syracuseStep 424171 = 636257) B636257
theorem B424183 : Blo 421773 424183 := bstep (se 1 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 424183 = 636275) B636275
theorem B3045637 : Blo 421773 3045637 := bstep (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) B571057
theorem B424203 : Blo 421773 424203 := bstep (se 1 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 424203 = 636305) B636305
theorem B424215 : Blo 421773 424215 := bstep (se 1 (by rfl) ⟨318161, by rfl⟩ : syracuseStep 424215 = 636323) B636323
theorem B424235 : Blo 421773 424235 := bstep (se 1 (by rfl) ⟨318176, by rfl⟩ : syracuseStep 424235 = 636353) B636353
theorem B424247 : Blo 421773 424247 := bstep (se 1 (by rfl) ⟨318185, by rfl⟩ : syracuseStep 424247 = 636371) B636371
theorem B424267 : Blo 421773 424267 := bstep (se 1 (by rfl) ⟨318200, by rfl⟩ : syracuseStep 424267 = 636401) B636401
theorem B424279 : Blo 421773 424279 := bstep (se 1 (by rfl) ⟨318209, by rfl⟩ : syracuseStep 424279 = 636419) B636419
theorem B1423709 : Blo 421773 1423709 := bstep (se 3 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 1423709 = 533891) B533891
theorem B2677093 : Blo 421773 2677093 := bstep (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) B501955
theorem B424299 : Blo 421773 424299 := bstep (se 1 (by rfl) ⟨318224, by rfl⟩ : syracuseStep 424299 = 636449) B636449
theorem B424311 : Blo 421773 424311 := bstep (se 1 (by rfl) ⟨318233, by rfl⟩ : syracuseStep 424311 = 636467) B636467
theorem B424331 : Blo 421773 424331 := bstep (se 1 (by rfl) ⟨318248, by rfl⟩ : syracuseStep 424331 = 636497) B636497
theorem B678295 : Blo 421773 678295 := bstep (se 1 (by rfl) ⟨508721, by rfl⟩ : syracuseStep 678295 = 1017443) B1017443
theorem B424343 : Blo 421773 424343 := bstep (se 1 (by rfl) ⟨318257, by rfl⟩ : syracuseStep 424343 = 636515) B636515
theorem B1612183 : Blo 421773 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B424363 : Blo 421773 424363 := bstep (se 1 (by rfl) ⟨318272, by rfl⟩ : syracuseStep 424363 = 636545) B636545
theorem B1071539 : Blo 421773 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B424375 : Blo 421773 424375 := bstep (se 1 (by rfl) ⟨318281, by rfl⟩ : syracuseStep 424375 = 636563) B636563
theorem B424395 : Blo 421773 424395 := bstep (se 1 (by rfl) ⟨318296, by rfl⟩ : syracuseStep 424395 = 636593) B636593
theorem B2980313 : Blo 421773 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B1432025 : Blo 421773 1432025 := bstep (se 2 (by rfl) ⟨537009, by rfl⟩ : syracuseStep 1432025 = 1074019) B1074019
theorem B424407 : Blo 421773 424407 := bstep (se 1 (by rfl) ⟨318305, by rfl⟩ : syracuseStep 424407 = 636611) B636611
theorem B424427 : Blo 421773 424427 := bstep (se 1 (by rfl) ⟨318320, by rfl⟩ : syracuseStep 424427 = 636641) B636641
theorem B424439 : Blo 421773 424439 := bstep (se 1 (by rfl) ⟨318329, by rfl⟩ : syracuseStep 424439 = 636659) B636659
theorem B424459 : Blo 421773 424459 := bstep (se 1 (by rfl) ⟨318344, by rfl⟩ : syracuseStep 424459 = 636689) B636689
theorem B10271245 : Blo 421773 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B424471 : Blo 421773 424471 := bstep (se 1 (by rfl) ⟨318353, by rfl⟩ : syracuseStep 424471 = 636707) B636707
theorem B424491 : Blo 421773 424491 := bstep (se 1 (by rfl) ⟨318368, by rfl⟩ : syracuseStep 424491 = 636737) B636737
theorem B424503 : Blo 421773 424503 := bstep (se 1 (by rfl) ⟨318377, by rfl⟩ : syracuseStep 424503 = 636755) B636755
theorem B424523 : Blo 421773 424523 := bstep (se 1 (by rfl) ⟨318392, by rfl⟩ : syracuseStep 424523 = 636785) B636785
theorem B424535 : Blo 421773 424535 := bstep (se 1 (by rfl) ⟨318401, by rfl⟩ : syracuseStep 424535 = 636803) B636803
theorem B424555 : Blo 421773 424555 := bstep (se 1 (by rfl) ⟨318416, by rfl⟩ : syracuseStep 424555 = 636833) B636833
theorem B424567 : Blo 421773 424567 := bstep (se 1 (by rfl) ⟨318425, by rfl⟩ : syracuseStep 424567 = 636851) B636851
theorem B424587 : Blo 421773 424587 := bstep (se 1 (by rfl) ⟨318440, by rfl⟩ : syracuseStep 424587 = 636881) B636881
theorem B678551 : Blo 421773 678551 := bstep (se 1 (by rfl) ⟨508913, by rfl⟩ : syracuseStep 678551 = 1017827) B1017827
theorem B2718359 : Blo 421773 2718359 := bstep (se 1 (by rfl) ⟨2038769, by rfl⟩ : syracuseStep 2718359 = 4077539) B4077539
theorem B424599 : Blo 421773 424599 := bstep (se 1 (by rfl) ⟨318449, by rfl⟩ : syracuseStep 424599 = 636899) B636899
theorem B424619 : Blo 421773 424619 := bstep (se 1 (by rfl) ⟨318464, by rfl⟩ : syracuseStep 424619 = 636929) B636929
theorem B424631 : Blo 421773 424631 := bstep (se 1 (by rfl) ⟨318473, by rfl⟩ : syracuseStep 424631 = 636947) B636947
theorem B424651 : Blo 421773 424651 := bstep (se 1 (by rfl) ⟨318488, by rfl⟩ : syracuseStep 424651 = 636977) B636977
theorem B424663 : Blo 421773 424663 := bstep (se 1 (by rfl) ⟨318497, by rfl⟩ : syracuseStep 424663 = 636995) B636995
theorem B424683 : Blo 421773 424683 := bstep (se 1 (by rfl) ⟨318512, by rfl⟩ : syracuseStep 424683 = 637025) B637025
theorem B424695 : Blo 421773 424695 := bstep (se 1 (by rfl) ⟨318521, by rfl⟩ : syracuseStep 424695 = 637043) B637043
theorem B482059 : Blo 421773 482059 := bstep (se 1 (by rfl) ⟨361544, by rfl⟩ : syracuseStep 482059 = 723089) B723089
theorem B424715 : Blo 421773 424715 := bstep (se 1 (by rfl) ⟨318536, by rfl⟩ : syracuseStep 424715 = 637073) B637073
theorem B2145041 : Blo 421773 2145041 := bstep (se 2 (by rfl) ⟨804390, by rfl⟩ : syracuseStep 2145041 = 1608781) B1608781
theorem B424727 : Blo 421773 424727 := bstep (se 1 (by rfl) ⟨318545, by rfl⟩ : syracuseStep 424727 = 637091) B637091
theorem B3210029 : Blo 421773 3210029 := bstep (se 3 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 3210029 = 1203761) B1203761
theorem B3873581 : Blo 421773 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B424747 : Blo 421773 424747 := bstep (se 1 (by rfl) ⟨318560, by rfl⟩ : syracuseStep 424747 = 637121) B637121
theorem B424759 : Blo 421773 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B949067 : Blo 421773 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B949121 : Blo 421773 949121 := bstep (se 2 (by rfl) ⟨355920, by rfl⟩ : syracuseStep 949121 = 711841) B711841
theorem B736139 : Blo 421773 736139 := bstep (se 1 (by rfl) ⟨552104, by rfl⟩ : syracuseStep 736139 = 1104209) B1104209
theorem B2407319 : Blo 421773 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B2145203 : Blo 421773 2145203 := bstep (se 1 (by rfl) ⟨1608902, by rfl⟩ : syracuseStep 2145203 = 3217805) B3217805
theorem B760769 : Blo 421773 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B1072075 : Blo 421773 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B1358795 : Blo 421773 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B572441 : Blo 421773 572441 := bstep (se 2 (by rfl) ⟨214665, by rfl⟩ : syracuseStep 572441 = 429331) B429331
theorem B3628097 : Blo 421773 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B1522763 : Blo 421773 1522763 := bstep (se 1 (by rfl) ⟨1142072, by rfl⟩ : syracuseStep 1522763 = 2284145) B2284145
theorem B711767 : Blo 421773 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B949337 : Blo 421773 949337 := bstep (se 2 (by rfl) ⟨356001, by rfl⟩ : syracuseStep 949337 = 712003) B712003
theorem B1072217 : Blo 421773 1072217 := bstep (se 2 (by rfl) ⟨402081, by rfl⟩ : syracuseStep 1072217 = 804163) B804163
theorem B1809539 : Blo 421773 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B1432727 : Blo 421773 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B949427 : Blo 421773 949427 := bstep (se 1 (by rfl) ⟨712070, by rfl⟩ : syracuseStep 949427 = 1424141) B1424141
theorem B1629377 : Blo 421773 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B679115 : Blo 421773 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B711895 : Blo 421773 711895 := bstep (se 1 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 711895 = 1067843) B1067843
theorem B949463 : Blo 421773 949463 := bstep (se 1 (by rfl) ⟨712097, by rfl⟩ : syracuseStep 949463 = 1424195) B1424195
theorem B949643 : Blo 421773 949643 := bstep (se 1 (by rfl) ⟨712232, by rfl⟩ : syracuseStep 949643 = 1424465) B1424465
theorem B949697 : Blo 421773 949697 := bstep (se 2 (by rfl) ⟨356136, by rfl⟩ : syracuseStep 949697 = 712273) B712273
theorem B1424843 : Blo 421773 1424843 := bstep (se 1 (by rfl) ⟨1068632, by rfl⟩ : syracuseStep 1424843 = 2137265) B2137265
theorem B474583 : Blo 421773 474583 := bstep (se 1 (by rfl) ⟨355937, by rfl⟩ : syracuseStep 474583 = 711875) B711875
theorem B687577 : Blo 421773 687577 := bstep (se 2 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 687577 = 515683) B515683
theorem B802379 : Blo 421773 802379 := bstep (se 1 (by rfl) ⟨601784, by rfl⟩ : syracuseStep 802379 = 1203569) B1203569
theorem B966233 : Blo 421773 966233 := bstep (se 2 (by rfl) ⟨362337, by rfl⟩ : syracuseStep 966233 = 724675) B724675
theorem B1359449 : Blo 421773 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B2637413 : Blo 421773 2637413 := bstep (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) B494515
theorem B2293379 : Blo 421773 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B474763 : Blo 421773 474763 := bstep (se 1 (by rfl) ⟨356072, by rfl⟩ : syracuseStep 474763 = 712145) B712145
theorem B761483 : Blo 421773 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B2137751 : Blo 421773 2137751 := bstep (se 1 (by rfl) ⟨1603313, by rfl⟩ : syracuseStep 2137751 = 3206627) B3206627
theorem B949913 : Blo 421773 949913 := bstep (se 2 (by rfl) ⟨356217, by rfl⟩ : syracuseStep 949913 = 712435) B712435
theorem B1433267 : Blo 421773 1433267 := bstep (se 1 (by rfl) ⟨1074950, by rfl⟩ : syracuseStep 1433267 = 2149901) B2149901
theorem B1351361 : Blo 421773 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B1425113 : Blo 421773 1425113 := bstep (se 2 (by rfl) ⟨534417, by rfl⟩ : syracuseStep 1425113 = 1068835) B1068835
theorem B3612377 : Blo 421773 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B950003 : Blo 421773 950003 := bstep (se 1 (by rfl) ⟨712502, by rfl⟩ : syracuseStep 950003 = 1425005) B1425005
theorem B474871 : Blo 421773 474871 := bstep (se 1 (by rfl) ⟨356153, by rfl⟩ : syracuseStep 474871 = 712307) B712307
theorem B802561 : Blo 421773 802561 := bstep (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) B601921
theorem B1605379 : Blo 421773 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B950039 : Blo 421773 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B859927 : Blo 421773 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B3677987 : Blo 421773 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B1089331 : Blo 421773 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B712523 : Blo 421773 712523 := bstep (se 1 (by rfl) ⟨534392, by rfl⟩ : syracuseStep 712523 = 1068785) B1068785
theorem B507799 : Blo 421773 507799 := bstep (se 1 (by rfl) ⟨380849, by rfl⟩ : syracuseStep 507799 = 761699) B761699
theorem B1073047 : Blo 421773 1073047 := bstep (se 1 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 1073047 = 1609571) B1609571
theorem B475051 : Blo 421773 475051 := bstep (se 1 (by rfl) ⟨356288, by rfl⟩ : syracuseStep 475051 = 712577) B712577
theorem B2473907 : Blo 421773 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1433537 : Blo 421773 1433537 := bstep (se 2 (by rfl) ⟨537576, by rfl⟩ : syracuseStep 1433537 = 1075153) B1075153
theorem B712651 : Blo 421773 712651 := bstep (se 1 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 712651 = 1068977) B1068977
theorem B950219 : Blo 421773 950219 := bstep (se 1 (by rfl) ⟨712664, by rfl⟩ : syracuseStep 950219 = 1425329) B1425329
theorem B1425437 : Blo 421773 1425437 := bstep (se 3 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 1425437 = 534539) B534539
theorem B475195 : Blo 421773 475195 := bstep (se 1 (by rfl) ⟨356396, by rfl⟩ : syracuseStep 475195 = 712793) B712793
theorem B1351799 : Blo 421773 1351799 := bstep (se 1 (by rfl) ⟨1013849, by rfl⟩ : syracuseStep 1351799 = 2027699) B2027699
theorem B802963 : Blo 421773 802963 := bstep (se 1 (by rfl) ⟨602222, by rfl⟩ : syracuseStep 802963 = 1204445) B1204445
theorem B2515181 : Blo 421773 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B950543 : Blo 421773 950543 := bstep (se 1 (by rfl) ⟨712907, by rfl⟩ : syracuseStep 950543 = 1425815) B1425815
theorem B712975 : Blo 421773 712975 := bstep (se 1 (by rfl) ⟨534731, by rfl⟩ : syracuseStep 712975 = 1069463) B1069463
theorem B950561 : Blo 421773 950561 := bstep (se 2 (by rfl) ⟨356460, by rfl⟩ : syracuseStep 950561 = 712921) B712921
theorem B803191 : Blo 421773 803191 := bstep (se 1 (by rfl) ⟨602393, by rfl⟩ : syracuseStep 803191 = 1204787) B1204787
theorem B901523 : Blo 421773 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B1204627 : Blo 421773 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B1073675 : Blo 421773 1073675 := bstep (se 1 (by rfl) ⟨805256, by rfl⟩ : syracuseStep 1073675 = 1610513) B1610513
theorem B475663 : Blo 421773 475663 := bstep (se 1 (by rfl) ⟨356747, by rfl⟩ : syracuseStep 475663 = 713495) B713495
theorem B1810973 : Blo 421773 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B950903 : Blo 421773 950903 := bstep (se 1 (by rfl) ⟨713177, by rfl⟩ : syracuseStep 950903 = 1426355) B1426355
theorem B1114913 : Blo 421773 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B951083 : Blo 421773 951083 := bstep (se 1 (by rfl) ⟨713312, by rfl⟩ : syracuseStep 951083 = 1426625) B1426625
theorem B713515 : Blo 421773 713515 := bstep (se 1 (by rfl) ⟨535136, by rfl⟩ : syracuseStep 713515 = 1070273) B1070273
theorem B1811315 : Blo 421773 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B1360793 : Blo 421773 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B713657 : Blo 421773 713657 := bstep (se 2 (by rfl) ⟨267621, by rfl⟩ : syracuseStep 713657 = 535243) B535243
theorem B476167 : Blo 421773 476167 := bstep (se 1 (by rfl) ⟨357125, by rfl⟩ : syracuseStep 476167 = 714251) B714251
theorem B1041523 : Blo 421773 1041523 := bstep (se 1 (by rfl) ⟨781142, by rfl⟩ : syracuseStep 1041523 = 1562285) B1562285
theorem B951443 : Blo 421773 951443 := bstep (se 1 (by rfl) ⟨713582, by rfl⟩ : syracuseStep 951443 = 1427165) B1427165
theorem B1074323 : Blo 421773 1074323 := bstep (se 1 (by rfl) ⟨805742, by rfl⟩ : syracuseStep 1074323 = 1611485) B1611485
theorem B476347 : Blo 421773 476347 := bstep (se 1 (by rfl) ⟨357260, by rfl⟩ : syracuseStep 476347 = 714521) B714521
theorem B951497 : Blo 421773 951497 := bstep (se 2 (by rfl) ⟨356811, by rfl⟩ : syracuseStep 951497 = 713623) B713623
theorem B2409709 : Blo 421773 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B451855 : Blo 421773 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B2417957 : Blo 421773 2417957 := bstep (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) B453367
theorem B542095 : Blo 421773 542095 := bstep (se 1 (by rfl) ⟨406571, by rfl⟩ : syracuseStep 542095 = 813143) B813143
theorem B1426841 : Blo 421773 1426841 := bstep (se 2 (by rfl) ⟨535065, by rfl⟩ : syracuseStep 1426841 = 1070131) B1070131
theorem B1074617 : Blo 421773 1074617 := bstep (se 2 (by rfl) ⟨402981, by rfl⟩ : syracuseStep 1074617 = 805963) B805963
theorem B533947 : Blo 421773 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B1017289 : Blo 421773 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B8144387 : Blo 421773 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B22029893 : Blo 421773 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B714359 : Blo 421773 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B476815 : Blo 421773 476815 := bstep (se 1 (by rfl) ⟨357611, by rfl⟩ : syracuseStep 476815 = 715223) B715223
theorem B4818689 : Blo 421773 4818689 := bstep (se 2 (by rfl) ⟨1807008, by rfl⟩ : syracuseStep 4818689 = 3614017) B3614017
theorem B1812239 : Blo 421773 1812239 := bstep (se 1 (by rfl) ⟨1359179, by rfl⟩ : syracuseStep 1812239 = 2718359) B2718359
theorem B1427233 : Blo 421773 1427233 := bstep (se 2 (by rfl) ⟨535212, by rfl⟩ : syracuseStep 1427233 = 1070425) B1070425
theorem B3860261 : Blo 421773 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B2140019 : Blo 421773 2140019 := bstep (se 1 (by rfl) ⟨1605014, by rfl⟩ : syracuseStep 2140019 = 3210029) B3210029
theorem B5162867 : Blo 421773 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B26388341 : Blo 421773 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B2582387 : Blo 421773 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B632711 : Blo 421773 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B952199 : Blo 421773 952199 := bstep (se 1 (by rfl) ⟨714149, by rfl⟩ : syracuseStep 952199 = 1428299) B1428299
theorem B2606995 : Blo 421773 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B804755 : Blo 421773 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B632747 : Blo 421773 632747 := bstep (se 1 (by rfl) ⟨474560, by rfl⟩ : syracuseStep 632747 = 949121) B949121
theorem B2148281 : Blo 421773 2148281 := bstep (se 2 (by rfl) ⟨805605, by rfl⟩ : syracuseStep 2148281 = 1611211) B1611211
theorem B632777 : Blo 421773 632777 := bstep (se 2 (by rfl) ⟨237291, by rfl⟩ : syracuseStep 632777 = 474583) B474583
theorem B804809 : Blo 421773 804809 := bstep (se 2 (by rfl) ⟨301803, by rfl⟩ : syracuseStep 804809 = 603607) B603607
theorem B1632209 : Blo 421773 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B804907 : Blo 421773 804907 := bstep (se 1 (by rfl) ⟨603680, by rfl⟩ : syracuseStep 804907 = 1207361) B1207361
theorem B2418731 : Blo 421773 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B632891 : Blo 421773 632891 := bstep (se 1 (by rfl) ⟨474668, by rfl⟩ : syracuseStep 632891 = 949337) B949337
theorem B952379 : Blo 421773 952379 := bstep (se 1 (by rfl) ⟨714284, by rfl⟩ : syracuseStep 952379 = 1428569) B1428569
theorem B714811 : Blo 421773 714811 := bstep (se 1 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 714811 = 1072217) B1072217
theorem B1427543 : Blo 421773 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B3049559 : Blo 421773 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B1206359 : Blo 421773 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B632951 : Blo 421773 632951 := bstep (se 1 (by rfl) ⟨474713, by rfl⟩ : syracuseStep 632951 = 949427) B949427
theorem B477319 : Blo 421773 477319 := bstep (se 1 (by rfl) ⟨357989, by rfl⟩ : syracuseStep 477319 = 715979) B715979
theorem B632975 : Blo 421773 632975 := bstep (se 1 (by rfl) ⟨474731, by rfl⟩ : syracuseStep 632975 = 949463) B949463
theorem B633017 : Blo 421773 633017 := bstep (se 2 (by rfl) ⟨237381, by rfl⟩ : syracuseStep 633017 = 474763) B474763
theorem B952505 : Blo 421773 952505 := bstep (se 2 (by rfl) ⟨357189, by rfl⟩ : syracuseStep 952505 = 714379) B714379
theorem B714953 : Blo 421773 714953 := bstep (se 2 (by rfl) ⟨268107, by rfl⟩ : syracuseStep 714953 = 536215) B536215
theorem B633095 : Blo 421773 633095 := bstep (se 1 (by rfl) ⟨474821, by rfl⟩ : syracuseStep 633095 = 949643) B949643
theorem B805135 : Blo 421773 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B633131 : Blo 421773 633131 := bstep (se 1 (by rfl) ⟨474848, by rfl⟩ : syracuseStep 633131 = 949697) B949697
theorem B477499 : Blo 421773 477499 := bstep (se 1 (by rfl) ⟨358124, by rfl⟩ : syracuseStep 477499 = 716249) B716249
theorem B633161 : Blo 421773 633161 := bstep (se 2 (by rfl) ⟨237435, by rfl⟩ : syracuseStep 633161 = 474871) B474871
theorem B2140505 : Blo 421773 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B534919 : Blo 421773 534919 := bstep (se 1 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 534919 = 802379) B802379
theorem B2058641 : Blo 421773 2058641 := bstep (se 2 (by rfl) ⟨771990, by rfl⟩ : syracuseStep 2058641 = 1543981) B1543981
theorem B1608083 : Blo 421773 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B633275 : Blo 421773 633275 := bstep (se 1 (by rfl) ⟨474956, by rfl⟩ : syracuseStep 633275 = 949913) B949913
theorem B2288081 : Blo 421773 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B6089201 : Blo 421773 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B633335 : Blo 421773 633335 := bstep (se 1 (by rfl) ⟨475001, by rfl⟩ : syracuseStep 633335 = 950003) B950003
theorem B633359 : Blo 421773 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B952847 : Blo 421773 952847 := bstep (se 1 (by rfl) ⟨714635, by rfl⟩ : syracuseStep 952847 = 1429271) B1429271
theorem B2451991 : Blo 421773 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B1739293 : Blo 421773 1739293 := bstep (se 3 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 1739293 = 652235) B652235
theorem B952865 : Blo 421773 952865 := bstep (se 2 (by rfl) ⟨357324, by rfl⟩ : syracuseStep 952865 = 714649) B714649
theorem B633401 : Blo 421773 633401 := bstep (se 2 (by rfl) ⟨237525, by rfl⟩ : syracuseStep 633401 = 475051) B475051
theorem B1624637 : Blo 421773 1624637 := bstep (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) B609239
theorem B1428029 : Blo 421773 1428029 := bstep (se 3 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 1428029 = 535511) B535511
theorem B633479 : Blo 421773 633479 := bstep (se 1 (by rfl) ⟨475109, by rfl⟩ : syracuseStep 633479 = 950219) B950219
theorem B633515 : Blo 421773 633515 := bstep (se 1 (by rfl) ⟨475136, by rfl⟩ : syracuseStep 633515 = 950273) B950273
theorem B633545 : Blo 421773 633545 := bstep (se 2 (by rfl) ⟨237579, by rfl⟩ : syracuseStep 633545 = 475159) B475159
theorem B903881 : Blo 421773 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B1526509 : Blo 421773 1526509 := bstep (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) B572441
theorem B1813229 : Blo 421773 1813229 := bstep (se 3 (by rfl) ⟨339980, by rfl⟩ : syracuseStep 1813229 = 679961) B679961
theorem B3443471 : Blo 421773 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B535339 : Blo 421773 535339 := bstep (se 1 (by rfl) ⟨401504, by rfl⟩ : syracuseStep 535339 = 803009) B803009
theorem B2280251 : Blo 421773 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B633659 : Blo 421773 633659 := bstep (se 1 (by rfl) ⟨475244, by rfl⟩ : syracuseStep 633659 = 950489) B950489
theorem B813883 : Blo 421773 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B1067863 : Blo 421773 1067863 := bstep (se 1 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 1067863 = 1601795) B1601795
theorem B4836185 : Blo 421773 4836185 := bstep (se 2 (by rfl) ⟨1813569, by rfl⟩ : syracuseStep 4836185 = 3627139) B3627139
theorem B8711027 : Blo 421773 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B633719 : Blo 421773 633719 := bstep (se 1 (by rfl) ⟨475289, by rfl⟩ : syracuseStep 633719 = 950579) B950579
theorem B953207 : Blo 421773 953207 := bstep (se 1 (by rfl) ⟨714905, by rfl⟩ : syracuseStep 953207 = 1429811) B1429811
theorem B715655 : Blo 421773 715655 := bstep (se 1 (by rfl) ⟨536741, by rfl⟩ : syracuseStep 715655 = 1073483) B1073483
theorem B633743 : Blo 421773 633743 := bstep (se 1 (by rfl) ⟨475307, by rfl⟩ : syracuseStep 633743 = 950615) B950615
theorem B8145845 : Blo 421773 8145845 := bstep (se 5 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 8145845 = 763673) B763673
theorem B633785 : Blo 421773 633785 := bstep (se 2 (by rfl) ⟨237669, by rfl⟩ : syracuseStep 633785 = 475339) B475339
theorem B1141705 : Blo 421773 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B633863 : Blo 421773 633863 := bstep (se 1 (by rfl) ⟨475397, by rfl⟩ : syracuseStep 633863 = 950795) B950795
theorem B2165771 : Blo 421773 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B535567 : Blo 421773 535567 := bstep (se 1 (by rfl) ⟨401675, by rfl⟩ : syracuseStep 535567 = 803351) B803351
theorem B633899 : Blo 421773 633899 := bstep (se 1 (by rfl) ⟨475424, by rfl⟩ : syracuseStep 633899 = 950849) B950849
theorem B953387 : Blo 421773 953387 := bstep (se 1 (by rfl) ⟨715040, by rfl⟩ : syracuseStep 953387 = 1430081) B1430081
theorem B633929 : Blo 421773 633929 := bstep (se 2 (by rfl) ⟨237723, by rfl⟩ : syracuseStep 633929 = 475447) B475447
theorem B1141847 : Blo 421773 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B1068167 : Blo 421773 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B2411693 : Blo 421773 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B634043 : Blo 421773 634043 := bstep (se 1 (by rfl) ⟨475532, by rfl⟩ : syracuseStep 634043 = 951065) B951065
theorem B904393 : Blo 421773 904393 := bstep (se 2 (by rfl) ⟨339147, by rfl⟩ : syracuseStep 904393 = 678295) B678295
theorem B2149577 : Blo 421773 2149577 := bstep (se 2 (by rfl) ⟨806091, by rfl⟩ : syracuseStep 2149577 = 1612183) B1612183
theorem B634103 : Blo 421773 634103 := bstep (se 1 (by rfl) ⟨475577, by rfl⟩ : syracuseStep 634103 = 951155) B951155
theorem B1068299 : Blo 421773 1068299 := bstep (se 1 (by rfl) ⟨801224, by rfl⟩ : syracuseStep 1068299 = 1602449) B1602449
theorem B634127 : Blo 421773 634127 := bstep (se 1 (by rfl) ⟨475595, by rfl⟩ : syracuseStep 634127 = 951191) B951191
theorem B634169 : Blo 421773 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B6106499 : Blo 421773 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B634247 : Blo 421773 634247 := bstep (se 1 (by rfl) ⟨475685, by rfl⟩ : syracuseStep 634247 = 951371) B951371
theorem B1355143 : Blo 421773 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B4124051 : Blo 421773 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B953747 : Blo 421773 953747 := bstep (se 1 (by rfl) ⟨715310, by rfl⟩ : syracuseStep 953747 = 1430621) B1430621
theorem B1813913 : Blo 421773 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B634283 : Blo 421773 634283 := bstep (se 1 (by rfl) ⟨475712, by rfl⟩ : syracuseStep 634283 = 951425) B951425
theorem B1142201 : Blo 421773 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B634313 : Blo 421773 634313 := bstep (se 2 (by rfl) ⟨237867, by rfl⟩ : syracuseStep 634313 = 475735) B475735
theorem B953801 : Blo 421773 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B716303 : Blo 421773 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B634427 : Blo 421773 634427 := bstep (se 1 (by rfl) ⟨475820, by rfl⟩ : syracuseStep 634427 = 951641) B951641
theorem B1142333 : Blo 421773 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B2887235 : Blo 421773 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B3903095 : Blo 421773 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B634487 : Blo 421773 634487 := bstep (se 1 (by rfl) ⟨475865, by rfl⟩ : syracuseStep 634487 = 951731) B951731
theorem B1207943 : Blo 421773 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B634511 : Blo 421773 634511 := bstep (se 1 (by rfl) ⟨475883, by rfl⟩ : syracuseStep 634511 = 951767) B951767
theorem B642745 : Blo 421773 642745 := bstep (se 2 (by rfl) ⟨241029, by rfl⟩ : syracuseStep 642745 = 482059) B482059
theorem B634553 : Blo 421773 634553 := bstep (se 2 (by rfl) ⟨237957, by rfl⟩ : syracuseStep 634553 = 475915) B475915
theorem B536311 : Blo 421773 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B1085185 : Blo 421773 1085185 := bstep (se 2 (by rfl) ⟨406944, by rfl⟩ : syracuseStep 1085185 = 813889) B813889
theorem B634631 : Blo 421773 634631 := bstep (se 1 (by rfl) ⟨475973, by rfl⟩ : syracuseStep 634631 = 951947) B951947
theorem B1068815 : Blo 421773 1068815 := bstep (se 1 (by rfl) ⟨801611, by rfl⟩ : syracuseStep 1068815 = 1603223) B1603223
theorem B634667 : Blo 421773 634667 := bstep (se 1 (by rfl) ⟨476000, by rfl⟩ : syracuseStep 634667 = 952001) B952001
theorem B675643 : Blo 421773 675643 := bstep (se 1 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 675643 = 1013465) B1013465
theorem B634697 : Blo 421773 634697 := bstep (se 2 (by rfl) ⟨238011, by rfl⟩ : syracuseStep 634697 = 476023) B476023
theorem B421775 : Blo 421773 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B1068947 : Blo 421773 1068947 := bstep (se 1 (by rfl) ⟨801710, by rfl⟩ : syracuseStep 1068947 = 1603421) B1603421
theorem B1429433 : Blo 421773 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B421819 : Blo 421773 421819 := bstep (se 1 (by rfl) ⟨316364, by rfl⟩ : syracuseStep 421819 = 632729) B632729
theorem B634811 : Blo 421773 634811 := bstep (se 1 (by rfl) ⟨476108, by rfl⟩ : syracuseStep 634811 = 952217) B952217
theorem B634871 : Blo 421773 634871 := bstep (se 1 (by rfl) ⟨476153, by rfl⟩ : syracuseStep 634871 = 952307) B952307
theorem B421895 : Blo 421773 421895 := bstep (se 1 (by rfl) ⟨316421, by rfl⟩ : syracuseStep 421895 = 632843) B632843
theorem B1609739 : Blo 421773 1609739 := bstep (se 1 (by rfl) ⟨1207304, by rfl⟩ : syracuseStep 1609739 = 2414609) B2414609
theorem B421903 : Blo 421773 421903 := bstep (se 1 (by rfl) ⟨316427, by rfl⟩ : syracuseStep 421903 = 632855) B632855
theorem B634895 : Blo 421773 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B905231 : Blo 421773 905231 := bstep (se 1 (by rfl) ⟨678923, by rfl⟩ : syracuseStep 905231 = 1357847) B1357847
theorem B634937 : Blo 421773 634937 := bstep (se 2 (by rfl) ⟨238101, by rfl⟩ : syracuseStep 634937 = 476203) B476203
theorem B421947 : Blo 421773 421947 := bstep (se 1 (by rfl) ⟨316460, by rfl⟩ : syracuseStep 421947 = 632921) B632921
theorem B536635 : Blo 421773 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B422023 : Blo 421773 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B635015 : Blo 421773 635015 := bstep (se 1 (by rfl) ⟨476261, by rfl⟩ : syracuseStep 635015 = 952523) B952523
theorem B954503 : Blo 421773 954503 := bstep (se 1 (by rfl) ⟨715877, by rfl⟩ : syracuseStep 954503 = 1431755) B1431755
theorem B422031 : Blo 421773 422031 := bstep (se 1 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 422031 = 633047) B633047
theorem B430223 : Blo 421773 430223 := bstep (se 1 (by rfl) ⟨322667, by rfl⟩ : syracuseStep 430223 = 645335) B645335
theorem B635051 : Blo 421773 635051 := bstep (se 1 (by rfl) ⟨476288, by rfl⟩ : syracuseStep 635051 = 952577) B952577
theorem B422075 : Blo 421773 422075 := bstep (se 1 (by rfl) ⟨316556, by rfl⟩ : syracuseStep 422075 = 633113) B633113
theorem B2896073 : Blo 421773 2896073 := bstep (se 2 (by rfl) ⟨1086027, by rfl⟩ : syracuseStep 2896073 = 2172055) B2172055
theorem B635081 : Blo 421773 635081 := bstep (se 2 (by rfl) ⟨238155, by rfl⟩ : syracuseStep 635081 = 476311) B476311
theorem B422151 : Blo 421773 422151 := bstep (se 1 (by rfl) ⟨316613, by rfl⟩ : syracuseStep 422151 = 633227) B633227
theorem B422159 : Blo 421773 422159 := bstep (se 1 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 422159 = 633239) B633239
theorem B1208591 : Blo 421773 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B422203 : Blo 421773 422203 := bstep (se 1 (by rfl) ⟨316652, by rfl⟩ : syracuseStep 422203 = 633305) B633305
theorem B635195 : Blo 421773 635195 := bstep (se 1 (by rfl) ⟨476396, by rfl⟩ : syracuseStep 635195 = 952793) B952793
theorem B1986875 : Blo 421773 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B954683 : Blo 421773 954683 := bstep (se 1 (by rfl) ⟨716012, by rfl⟩ : syracuseStep 954683 = 1432025) B1432025
theorem B635255 : Blo 421773 635255 := bstep (se 1 (by rfl) ⟨476441, by rfl⟩ : syracuseStep 635255 = 952883) B952883
theorem B422279 : Blo 421773 422279 := bstep (se 1 (by rfl) ⟨316709, by rfl⟩ : syracuseStep 422279 = 633419) B633419
theorem B422287 : Blo 421773 422287 := bstep (se 1 (by rfl) ⟨316715, by rfl⟩ : syracuseStep 422287 = 633431) B633431
theorem B635279 : Blo 421773 635279 := bstep (se 1 (by rfl) ⟨476459, by rfl⟩ : syracuseStep 635279 = 952919) B952919
theorem B2142611 : Blo 421773 2142611 := bstep (se 1 (by rfl) ⟨1606958, by rfl⟩ : syracuseStep 2142611 = 3213917) B3213917
theorem B1601977 : Blo 421773 1601977 := bstep (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) B1201483
theorem B635321 : Blo 421773 635321 := bstep (se 2 (by rfl) ⟨238245, by rfl⟩ : syracuseStep 635321 = 476491) B476491
theorem B422331 : Blo 421773 422331 := bstep (se 1 (by rfl) ⟨316748, by rfl⟩ : syracuseStep 422331 = 633497) B633497
theorem B954809 : Blo 421773 954809 := bstep (se 2 (by rfl) ⟨358053, by rfl⟩ : syracuseStep 954809 = 716107) B716107
theorem B2167249 : Blo 421773 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B422407 : Blo 421773 422407 := bstep (se 1 (by rfl) ⟨316805, by rfl⟩ : syracuseStep 422407 = 633611) B633611
theorem B635399 : Blo 421773 635399 := bstep (se 1 (by rfl) ⟨476549, by rfl⟩ : syracuseStep 635399 = 953099) B953099
theorem B1430027 : Blo 421773 1430027 := bstep (se 1 (by rfl) ⟨1072520, by rfl⟩ : syracuseStep 1430027 = 2145041) B2145041
theorem B422415 : Blo 421773 422415 := bstep (se 1 (by rfl) ⟨316811, by rfl⟩ : syracuseStep 422415 = 633623) B633623
theorem B635435 : Blo 421773 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B537131 : Blo 421773 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B422459 : Blo 421773 422459 := bstep (se 1 (by rfl) ⟨316844, by rfl⟩ : syracuseStep 422459 = 633689) B633689
theorem B635465 : Blo 421773 635465 := bstep (se 2 (by rfl) ⟨238299, by rfl⟩ : syracuseStep 635465 = 476599) B476599
theorem B4821605 : Blo 421773 4821605 := bstep (se 4 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 4821605 = 904051) B904051
theorem B1430135 : Blo 421773 1430135 := bstep (se 1 (by rfl) ⟨1072601, by rfl⟩ : syracuseStep 1430135 = 2145203) B2145203
theorem B422535 : Blo 421773 422535 := bstep (se 1 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 422535 = 633803) B633803
theorem B905863 : Blo 421773 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B422543 : Blo 421773 422543 := bstep (se 1 (by rfl) ⟨316907, by rfl⟩ : syracuseStep 422543 = 633815) B633815
theorem B422587 : Blo 421773 422587 := bstep (se 1 (by rfl) ⟨316940, by rfl⟩ : syracuseStep 422587 = 633881) B633881
theorem B635579 : Blo 421773 635579 := bstep (se 1 (by rfl) ⟨476684, by rfl⟩ : syracuseStep 635579 = 953369) B953369
theorem B635639 : Blo 421773 635639 := bstep (se 1 (by rfl) ⟨476729, by rfl⟩ : syracuseStep 635639 = 953459) B953459
theorem B422663 : Blo 421773 422663 := bstep (se 1 (by rfl) ⟨316997, by rfl⟩ : syracuseStep 422663 = 633995) B633995
theorem B422671 : Blo 421773 422671 := bstep (se 1 (by rfl) ⟨317003, by rfl⟩ : syracuseStep 422671 = 634007) B634007
theorem B635663 : Blo 421773 635663 := bstep (se 1 (by rfl) ⟨476747, by rfl⟩ : syracuseStep 635663 = 953495) B953495
theorem B955151 : Blo 421773 955151 := bstep (se 1 (by rfl) ⟨716363, by rfl⟩ : syracuseStep 955151 = 1432727) B1432727
theorem B2405153 : Blo 421773 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B955169 : Blo 421773 955169 := bstep (se 2 (by rfl) ⟨358188, by rfl⟩ : syracuseStep 955169 = 716377) B716377
theorem B1086251 : Blo 421773 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B635705 : Blo 421773 635705 := bstep (se 2 (by rfl) ⟨238389, by rfl⟩ : syracuseStep 635705 = 476779) B476779
theorem B422715 : Blo 421773 422715 := bstep (se 1 (by rfl) ⟨317036, by rfl⟩ : syracuseStep 422715 = 634073) B634073
theorem B422791 : Blo 421773 422791 := bstep (se 1 (by rfl) ⟨317093, by rfl⟩ : syracuseStep 422791 = 634187) B634187
theorem B635783 : Blo 421773 635783 := bstep (se 1 (by rfl) ⟨476837, by rfl⟩ : syracuseStep 635783 = 953675) B953675
theorem B422799 : Blo 421773 422799 := bstep (se 1 (by rfl) ⟨317099, by rfl⟩ : syracuseStep 422799 = 634199) B634199
theorem B635819 : Blo 421773 635819 := bstep (se 1 (by rfl) ⟨476864, by rfl⟩ : syracuseStep 635819 = 953729) B953729
theorem B422843 : Blo 421773 422843 := bstep (se 1 (by rfl) ⟨317132, by rfl⟩ : syracuseStep 422843 = 634265) B634265
theorem B635849 : Blo 421773 635849 := bstep (se 2 (by rfl) ⟨238443, by rfl⟩ : syracuseStep 635849 = 476887) B476887
theorem B1070081 : Blo 421773 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B422919 : Blo 421773 422919 := bstep (se 1 (by rfl) ⟨317189, by rfl⟩ : syracuseStep 422919 = 634379) B634379
theorem B4568075 : Blo 421773 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B422927 : Blo 421773 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B422971 : Blo 421773 422971 := bstep (se 1 (by rfl) ⟨317228, by rfl⟩ : syracuseStep 422971 = 634457) B634457
theorem B644155 : Blo 421773 644155 := bstep (se 1 (by rfl) ⟨483116, by rfl⟩ : syracuseStep 644155 = 966233) B966233
theorem B635963 : Blo 421773 635963 := bstep (se 1 (by rfl) ⟨476972, by rfl⟩ : syracuseStep 635963 = 953945) B953945
theorem B906299 : Blo 421773 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B1758275 : Blo 421773 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1528919 : Blo 421773 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B636023 : Blo 421773 636023 := bstep (se 1 (by rfl) ⟨477017, by rfl⟩ : syracuseStep 636023 = 954035) B954035
theorem B955511 : Blo 421773 955511 := bstep (se 1 (by rfl) ⟨716633, by rfl⟩ : syracuseStep 955511 = 1433267) B1433267
theorem B423047 : Blo 421773 423047 := bstep (se 1 (by rfl) ⟨317285, by rfl⟩ : syracuseStep 423047 = 634571) B634571
theorem B423055 : Blo 421773 423055 := bstep (se 1 (by rfl) ⟨317291, by rfl⟩ : syracuseStep 423055 = 634583) B634583
theorem B636047 : Blo 421773 636047 := bstep (se 1 (by rfl) ⟨477035, by rfl⟩ : syracuseStep 636047 = 954071) B954071
theorem B636089 : Blo 421773 636089 := bstep (se 2 (by rfl) ⟨238533, by rfl⟩ : syracuseStep 636089 = 477067) B477067
theorem B423099 : Blo 421773 423099 := bstep (se 1 (by rfl) ⟨317324, by rfl⟩ : syracuseStep 423099 = 634649) B634649
theorem B3421385 : Blo 421773 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B677065 : Blo 421773 677065 := bstep (se 2 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 677065 = 507799) B507799
theorem B1430729 : Blo 421773 1430729 := bstep (se 2 (by rfl) ⟨536523, by rfl⟩ : syracuseStep 1430729 = 1073047) B1073047
theorem B423175 : Blo 421773 423175 := bstep (se 1 (by rfl) ⟨317381, by rfl⟩ : syracuseStep 423175 = 634763) B634763
theorem B636167 : Blo 421773 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B423183 : Blo 421773 423183 := bstep (se 1 (by rfl) ⟨317387, by rfl⟩ : syracuseStep 423183 = 634775) B634775
theorem B603407 : Blo 421773 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B636203 : Blo 421773 636203 := bstep (se 1 (by rfl) ⟨477152, by rfl⟩ : syracuseStep 636203 = 954305) B954305
theorem B955691 : Blo 421773 955691 := bstep (se 1 (by rfl) ⟨716768, by rfl⟩ : syracuseStep 955691 = 1433537) B1433537
theorem B423227 : Blo 421773 423227 := bstep (se 1 (by rfl) ⟨317420, by rfl⟩ : syracuseStep 423227 = 634841) B634841
theorem B636233 : Blo 421773 636233 := bstep (se 2 (by rfl) ⟨238587, by rfl⟩ : syracuseStep 636233 = 477175) B477175
theorem B1070455 : Blo 421773 1070455 := bstep (se 1 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 1070455 = 1605683) B1605683
theorem B423303 : Blo 421773 423303 := bstep (se 1 (by rfl) ⟨317477, by rfl⟩ : syracuseStep 423303 = 634955) B634955
theorem B423311 : Blo 421773 423311 := bstep (se 1 (by rfl) ⟨317483, by rfl⟩ : syracuseStep 423311 = 634967) B634967
theorem B7256465 : Blo 421773 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B423355 : Blo 421773 423355 := bstep (se 1 (by rfl) ⟨317516, by rfl⟩ : syracuseStep 423355 = 635033) B635033
theorem B636347 : Blo 421773 636347 := bstep (se 1 (by rfl) ⟨477260, by rfl⟩ : syracuseStep 636347 = 954521) B954521
theorem B636407 : Blo 421773 636407 := bstep (se 1 (by rfl) ⟨477305, by rfl⟩ : syracuseStep 636407 = 954611) B954611
theorem B2414083 : Blo 421773 2414083 := bstep (se 1 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 2414083 = 3621125) B3621125
theorem B423431 : Blo 421773 423431 := bstep (se 1 (by rfl) ⟨317573, by rfl⟩ : syracuseStep 423431 = 635147) B635147
theorem B423439 : Blo 421773 423439 := bstep (se 1 (by rfl) ⟨317579, by rfl⟩ : syracuseStep 423439 = 635159) B635159
theorem B636431 : Blo 421773 636431 := bstep (se 1 (by rfl) ⟨477323, by rfl⟩ : syracuseStep 636431 = 954647) B954647
theorem B636473 : Blo 421773 636473 := bstep (se 2 (by rfl) ⟨238677, by rfl⟩ : syracuseStep 636473 = 477355) B477355
theorem B423483 : Blo 421773 423483 := bstep (se 1 (by rfl) ⟨317612, by rfl⟩ : syracuseStep 423483 = 635225) B635225
theorem B4462199 : Blo 421773 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B906871 : Blo 421773 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B423559 : Blo 421773 423559 := bstep (se 1 (by rfl) ⟨317669, by rfl⟩ : syracuseStep 423559 = 635339) B635339
theorem B636551 : Blo 421773 636551 := bstep (se 1 (by rfl) ⟨477413, by rfl⟩ : syracuseStep 636551 = 954827) B954827
theorem B423567 : Blo 421773 423567 := bstep (se 1 (by rfl) ⟨317675, by rfl⟩ : syracuseStep 423567 = 635351) B635351
theorem B964243 : Blo 421773 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B636587 : Blo 421773 636587 := bstep (se 1 (by rfl) ⟨477440, by rfl⟩ : syracuseStep 636587 = 954881) B954881
theorem B4060849 : Blo 421773 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B423611 : Blo 421773 423611 := bstep (se 1 (by rfl) ⟨317708, by rfl⟩ : syracuseStep 423611 = 635417) B635417
theorem B636617 : Blo 421773 636617 := bstep (se 2 (by rfl) ⟨238731, by rfl⟩ : syracuseStep 636617 = 477463) B477463
theorem B423687 : Blo 421773 423687 := bstep (se 1 (by rfl) ⟨317765, by rfl⟩ : syracuseStep 423687 = 635531) B635531
theorem B423695 : Blo 421773 423695 := bstep (se 1 (by rfl) ⟨317771, by rfl⟩ : syracuseStep 423695 = 635543) B635543
theorem B1070891 : Blo 421773 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B907051 : Blo 421773 907051 := bstep (se 1 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 907051 = 1360577) B1360577
theorem B423739 : Blo 421773 423739 := bstep (se 1 (by rfl) ⟨317804, by rfl⟩ : syracuseStep 423739 = 635609) B635609
theorem B636731 : Blo 421773 636731 := bstep (se 1 (by rfl) ⟨477548, by rfl⟩ : syracuseStep 636731 = 955097) B955097
theorem B636791 : Blo 421773 636791 := bstep (se 1 (by rfl) ⟨477593, by rfl⟩ : syracuseStep 636791 = 955187) B955187
theorem B907127 : Blo 421773 907127 := bstep (se 1 (by rfl) ⟨680345, by rfl⟩ : syracuseStep 907127 = 1360691) B1360691
theorem B423815 : Blo 421773 423815 := bstep (se 1 (by rfl) ⟨317861, by rfl⟩ : syracuseStep 423815 = 635723) B635723
theorem B1431431 : Blo 421773 1431431 := bstep (se 1 (by rfl) ⟨1073573, by rfl⟩ : syracuseStep 1431431 = 2147147) B2147147
theorem B423823 : Blo 421773 423823 := bstep (se 1 (by rfl) ⟨317867, by rfl⟩ : syracuseStep 423823 = 635735) B635735
theorem B636815 : Blo 421773 636815 := bstep (se 1 (by rfl) ⟨477611, by rfl⟩ : syracuseStep 636815 = 955223) B955223
theorem B4396963 : Blo 421773 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B636857 : Blo 421773 636857 := bstep (se 2 (by rfl) ⟨238821, by rfl⟩ : syracuseStep 636857 = 477643) B477643
theorem B423867 : Blo 421773 423867 := bstep (se 1 (by rfl) ⟨317900, by rfl⟩ : syracuseStep 423867 = 635801) B635801
theorem B423943 : Blo 421773 423943 := bstep (se 1 (by rfl) ⟨317957, by rfl⟩ : syracuseStep 423943 = 635915) B635915
theorem B636935 : Blo 421773 636935 := bstep (se 1 (by rfl) ⟨477701, by rfl⟩ : syracuseStep 636935 = 955403) B955403
theorem B423951 : Blo 421773 423951 := bstep (se 1 (by rfl) ⟨317963, by rfl⟩ : syracuseStep 423951 = 635927) B635927
theorem B13694993 : Blo 421773 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B4823063 : Blo 421773 4823063 := bstep (se 1 (by rfl) ⟨3617297, by rfl⟩ : syracuseStep 4823063 = 7234595) B7234595
theorem B636971 : Blo 421773 636971 := bstep (se 1 (by rfl) ⟨477728, by rfl⟩ : syracuseStep 636971 = 955457) B955457
theorem B423995 : Blo 421773 423995 := bstep (se 1 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 423995 = 635993) B635993
theorem B1251389 : Blo 421773 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B4569149 : Blo 421773 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B2136131 : Blo 421773 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B637001 : Blo 421773 637001 := bstep (se 2 (by rfl) ⟨238875, by rfl⟩ : syracuseStep 637001 = 477751) B477751
theorem B424071 : Blo 421773 424071 := bstep (se 1 (by rfl) ⟨318053, by rfl⟩ : syracuseStep 424071 = 636107) B636107
theorem B424079 : Blo 421773 424079 := bstep (se 1 (by rfl) ⟨318059, by rfl⟩ : syracuseStep 424079 = 636119) B636119
theorem B424123 : Blo 421773 424123 := bstep (se 1 (by rfl) ⟨318092, by rfl⟩ : syracuseStep 424123 = 636185) B636185
theorem B637115 : Blo 421773 637115 := bstep (se 1 (by rfl) ⟨477836, by rfl⟩ : syracuseStep 637115 = 955673) B955673
theorem B2283713 : Blo 421773 2283713 := bstep (se 2 (by rfl) ⟨856392, by rfl⟩ : syracuseStep 2283713 = 1712785) B1712785
theorem B1431809 : Blo 421773 1431809 := bstep (se 2 (by rfl) ⟨536928, by rfl⟩ : syracuseStep 1431809 = 1073857) B1073857
theorem B424199 : Blo 421773 424199 := bstep (se 1 (by rfl) ⟨318149, by rfl⟩ : syracuseStep 424199 = 636299) B636299
theorem B424207 : Blo 421773 424207 := bstep (se 1 (by rfl) ⟨318155, by rfl⟩ : syracuseStep 424207 = 636311) B636311
theorem B424251 : Blo 421773 424251 := bstep (se 1 (by rfl) ⟨318188, by rfl⟩ : syracuseStep 424251 = 636377) B636377
theorem B1309043 : Blo 421773 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B2136455 : Blo 421773 2136455 := bstep (se 1 (by rfl) ⟨1602341, by rfl⟩ : syracuseStep 2136455 = 3204683) B3204683
theorem B424327 : Blo 421773 424327 := bstep (se 1 (by rfl) ⟨318245, by rfl⟩ : syracuseStep 424327 = 636491) B636491
theorem B424335 : Blo 421773 424335 := bstep (se 1 (by rfl) ⟨318251, by rfl⟩ : syracuseStep 424335 = 636503) B636503
theorem B1423763 : Blo 421773 1423763 := bstep (se 1 (by rfl) ⟨1067822, by rfl⟩ : syracuseStep 1423763 = 2135645) B2135645
theorem B23239061 : Blo 421773 23239061 := bstep (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) B1089331
theorem B1743257 : Blo 421773 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B424379 : Blo 421773 424379 := bstep (se 1 (by rfl) ⟨318284, by rfl⟩ : syracuseStep 424379 = 636569) B636569
theorem B3258883 : Blo 421773 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B424455 : Blo 421773 424455 := bstep (se 1 (by rfl) ⟨318341, by rfl⟩ : syracuseStep 424455 = 636683) B636683
theorem B424463 : Blo 421773 424463 := bstep (se 1 (by rfl) ⟨318347, by rfl⟩ : syracuseStep 424463 = 636695) B636695
theorem B801323 : Blo 421773 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B424507 : Blo 421773 424507 := bstep (se 1 (by rfl) ⟨318380, by rfl⟩ : syracuseStep 424507 = 636761) B636761
theorem B1522243 : Blo 421773 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B4831811 : Blo 421773 4831811 := bstep (se 1 (by rfl) ⟨3623858, by rfl⟩ : syracuseStep 4831811 = 7247717) B7247717
theorem B1071731 : Blo 421773 1071731 := bstep (se 1 (by rfl) ⟨803798, by rfl⟩ : syracuseStep 1071731 = 1607597) B1607597
theorem B1014407 : Blo 421773 1014407 := bstep (se 1 (by rfl) ⟨760805, by rfl⟩ : syracuseStep 1014407 = 1521611) B1521611
theorem B1071751 : Blo 421773 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B424583 : Blo 421773 424583 := bstep (se 1 (by rfl) ⟨318437, by rfl⟩ : syracuseStep 424583 = 636875) B636875
theorem B424591 : Blo 421773 424591 := bstep (se 1 (by rfl) ⟨318443, by rfl⟩ : syracuseStep 424591 = 636887) B636887
theorem B424635 : Blo 421773 424635 := bstep (se 1 (by rfl) ⟨318476, by rfl⟩ : syracuseStep 424635 = 636953) B636953
theorem B1358537 : Blo 421773 1358537 := bstep (se 2 (by rfl) ⟨509451, by rfl⟩ : syracuseStep 1358537 = 1018903) B1018903
theorem B424711 : Blo 421773 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B801551 : Blo 421773 801551 := bstep (se 1 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 801551 = 1202327) B1202327
theorem B424719 : Blo 421773 424719 := bstep (se 1 (by rfl) ⟨318539, by rfl⟩ : syracuseStep 424719 = 637079) B637079
theorem B1202987 : Blo 421773 1202987 := bstep (se 1 (by rfl) ⟨902240, by rfl⟩ : syracuseStep 1202987 = 1804481) B1804481
theorem B424763 : Blo 421773 424763 := bstep (se 1 (by rfl) ⟨318572, by rfl⟩ : syracuseStep 424763 = 637145) B637145
theorem B4414283 : Blo 421773 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B2710361 : Blo 421773 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B3218291 : Blo 421773 3218291 := bstep (se 1 (by rfl) ⟨2413718, by rfl⟩ : syracuseStep 3218291 = 4827437) B4827437
theorem B949139 : Blo 421773 949139 := bstep (se 1 (by rfl) ⟨711854, by rfl⟩ : syracuseStep 949139 = 1423709) B1423709
theorem B1072025 : Blo 421773 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B949193 : Blo 421773 949193 := bstep (se 2 (by rfl) ⟨355947, by rfl⟩ : syracuseStep 949193 = 711895) B711895
theorem B4332491 : Blo 421773 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B1432619 : Blo 421773 1432619 := bstep (se 1 (by rfl) ⟨1074464, by rfl⟩ : syracuseStep 1432619 = 2148929) B2148929
theorem B1072187 : Blo 421773 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B1809469 : Blo 421773 1809469 := bstep (se 3 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 1809469 = 678551) B678551
theorem B3603629 : Blo 421773 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B14277829 : Blo 421773 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B490759 : Blo 421773 490759 := bstep (se 1 (by rfl) ⟨368069, by rfl⟩ : syracuseStep 490759 = 736139) B736139
theorem B1604879 : Blo 421773 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B1072399 : Blo 421773 1072399 := bstep (se 1 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 1072399 = 1608599) B1608599
theorem B916769 : Blo 421773 916769 := bstep (se 2 (by rfl) ⟨343788, by rfl⟩ : syracuseStep 916769 = 687577) B687577
theorem B507179 : Blo 421773 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B1015175 : Blo 421773 1015175 := bstep (se 1 (by rfl) ⟨761381, by rfl⟩ : syracuseStep 1015175 = 1522763) B1522763
theorem B474511 : Blo 421773 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B2145689 : Blo 421773 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B1072673 : Blo 421773 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B712327 : Blo 421773 712327 := bstep (se 1 (by rfl) ⟨534245, by rfl⟩ : syracuseStep 712327 = 1068491) B1068491
theorem B949895 : Blo 421773 949895 := bstep (se 1 (by rfl) ⟨712421, by rfl⟩ : syracuseStep 949895 = 1424843) B1424843
theorem B1007239 : Blo 421773 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B1146569 : Blo 421773 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B3440357 : Blo 421773 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B507655 : Blo 421773 507655 := bstep (se 1 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 507655 = 761483) B761483
theorem B1425167 : Blo 421773 1425167 := bstep (se 1 (by rfl) ⟨1068875, by rfl⟩ : syracuseStep 1425167 = 2137751) B2137751
theorem B4808483 : Blo 421773 4808483 := bstep (se 1 (by rfl) ⟨3606362, by rfl⟩ : syracuseStep 4808483 = 7212725) B7212725
theorem B2711333 : Blo 421773 2711333 := bstep (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) B508375
theorem B950075 : Blo 421773 950075 := bstep (se 1 (by rfl) ⟨712556, by rfl⟩ : syracuseStep 950075 = 1425113) B1425113
theorem B2408251 : Blo 421773 2408251 := bstep (se 1 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 2408251 = 3612377) B3612377
theorem B2416499 : Blo 421773 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B475015 : Blo 421773 475015 := bstep (se 1 (by rfl) ⟨356261, by rfl⟩ : syracuseStep 475015 = 712523) B712523
theorem B950201 : Blo 421773 950201 := bstep (se 2 (by rfl) ⟨356325, by rfl⟩ : syracuseStep 950201 = 712651) B712651
theorem B7217099 : Blo 421773 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B1073159 : Blo 421773 1073159 := bstep (se 1 (by rfl) ⟨804869, by rfl⟩ : syracuseStep 1073159 = 1609739) B1609739
theorem B950291 : Blo 421773 950291 := bstep (se 1 (by rfl) ⟨712718, by rfl⟩ : syracuseStep 950291 = 1425437) B1425437
theorem B1073209 : Blo 421773 1073209 := bstep (se 2 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 1073209 = 804907) B804907
theorem B901199 : Blo 421773 901199 := bstep (se 1 (by rfl) ⟨675899, by rfl⟩ : syracuseStep 901199 = 1351799) B1351799
theorem B950633 : Blo 421773 950633 := bstep (se 2 (by rfl) ⟨356487, by rfl⟩ : syracuseStep 950633 = 712975) B712975
theorem B1073513 : Blo 421773 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B713225 : Blo 421773 713225 := bstep (se 2 (by rfl) ⟨267459, by rfl⟩ : syracuseStep 713225 = 534919) B534919
theorem B1606169 : Blo 421773 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B475771 : Blo 421773 475771 := bstep (se 1 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 475771 = 713657) B713657
theorem B713387 : Blo 421773 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B3269321 : Blo 421773 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B1172183 : Blo 421773 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1352477 : Blo 421773 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B951227 : Blo 421773 951227 := bstep (se 1 (by rfl) ⟨713420, by rfl⟩ : syracuseStep 951227 = 1426841) B1426841
theorem B3490781 : Blo 421773 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B951353 : Blo 421773 951353 := bstep (se 2 (by rfl) ⟨356757, by rfl⟩ : syracuseStep 951353 = 713515) B713515
theorem B713785 : Blo 421773 713785 := bstep (se 2 (by rfl) ⟨267669, by rfl⟩ : syracuseStep 713785 = 535339) B535339
theorem B2974799 : Blo 421773 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B476239 : Blo 421773 476239 := bstep (se 1 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 476239 = 714359) B714359
theorem B3212459 : Blo 421773 3212459 := bstep (se 1 (by rfl) ⟨2409344, by rfl⟩ : syracuseStep 3212459 = 4818689) B4818689
theorem B2573507 : Blo 421773 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B713927 : Blo 421773 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B1426679 : Blo 421773 1426679 := bstep (se 1 (by rfl) ⟨1070009, by rfl⟩ : syracuseStep 1426679 = 2140019) B2140019
theorem B3441911 : Blo 421773 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B1721591 : Blo 421773 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B714089 : Blo 421773 714089 := bstep (se 2 (by rfl) ⟨267783, by rfl⟩ : syracuseStep 714089 = 535567) B535567
theorem B951695 : Blo 421773 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B2033039 : Blo 421773 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B804239 : Blo 421773 804239 := bstep (se 1 (by rfl) ⟨603179, by rfl⟩ : syracuseStep 804239 = 1206359) B1206359
theorem B476635 : Blo 421773 476635 := bstep (se 1 (by rfl) ⟨357476, by rfl⟩ : syracuseStep 476635 = 714953) B714953
theorem B4589045 : Blo 421773 4589045 := bstep (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) B430223
theorem B1427003 : Blo 421773 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B902753 : Blo 421773 902753 := bstep (se 2 (by rfl) ⟨338532, by rfl⟩ : syracuseStep 902753 = 677065) B677065
theorem B1205857 : Blo 421773 1205857 := bstep (se 2 (by rfl) ⟨452196, by rfl⟩ : syracuseStep 1205857 = 904393) B904393
theorem B15492707 : Blo 421773 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B1525387 : Blo 421773 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B3212945 : Blo 421773 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B534215 : Blo 421773 534215 := bstep (se 1 (by rfl) ⟨400661, by rfl⟩ : syracuseStep 534215 = 801323) B801323
theorem B952019 : Blo 421773 952019 := bstep (se 1 (by rfl) ⟨714014, by rfl⟩ : syracuseStep 952019 = 1428029) B1428029
theorem B3221207 : Blo 421773 3221207 := bstep (se 1 (by rfl) ⟨2415905, by rfl⟩ : syracuseStep 3221207 = 4831811) B4831811
theorem B714487 : Blo 421773 714487 := bstep (se 1 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 714487 = 1071731) B1071731
theorem B1427273 : Blo 421773 1427273 := bstep (se 2 (by rfl) ⟨535227, by rfl⟩ : syracuseStep 1427273 = 1070455) B1070455
theorem B534367 : Blo 421773 534367 := bstep (se 1 (by rfl) ⟨400775, by rfl⟩ : syracuseStep 534367 = 801551) B801551
theorem B2295647 : Blo 421773 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B632681 : Blo 421773 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B3622765 : Blo 421773 3622765 := bstep (se 3 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 3622765 = 1358537) B1358537
theorem B3057517 : Blo 421773 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B2942855 : Blo 421773 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B477103 : Blo 421773 477103 := bstep (se 1 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 477103 = 715655) B715655
theorem B632759 : Blo 421773 632759 := bstep (se 1 (by rfl) ⟨474569, by rfl⟩ : syracuseStep 632759 = 949139) B949139
theorem B714683 : Blo 421773 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B632795 : Blo 421773 632795 := bstep (se 1 (by rfl) ⟨474596, by rfl⟩ : syracuseStep 632795 = 949193) B949193
theorem B1443847 : Blo 421773 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B714791 : Blo 421773 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B2402419 : Blo 421773 2402419 := bstep (se 1 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 2402419 = 3603629) B3603629
theorem B1607795 : Blo 421773 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B17410229 : Blo 421773 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B715081 : Blo 421773 715081 := bstep (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) B536311
theorem B477535 : Blo 421773 477535 := bstep (se 1 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 477535 = 716303) B716303
theorem B715115 : Blo 421773 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B1902977 : Blo 421773 1902977 := bstep (se 2 (by rfl) ⟨713616, by rfl⟩ : syracuseStep 1902977 = 1427233) B1427233
theorem B22219157 : Blo 421773 22219157 := bstep (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) B1041523
theorem B633263 : Blo 421773 633263 := bstep (se 1 (by rfl) ⟨474947, by rfl⟩ : syracuseStep 633263 = 949895) B949895
theorem B805295 : Blo 421773 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B633353 : Blo 421773 633353 := bstep (se 2 (by rfl) ⟨237507, by rfl⟩ : syracuseStep 633353 = 475015) B475015
theorem B3205655 : Blo 421773 3205655 := bstep (se 1 (by rfl) ⟨2404241, by rfl⟩ : syracuseStep 3205655 = 4808483) B4808483
theorem B3475993 : Blo 421773 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B633383 : Blo 421773 633383 := bstep (se 1 (by rfl) ⟨475037, by rfl⟩ : syracuseStep 633383 = 950075) B950075
theorem B633467 : Blo 421773 633467 := bstep (se 1 (by rfl) ⟨475100, by rfl⟩ : syracuseStep 633467 = 950201) B950201
theorem B952955 : Blo 421773 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B4811399 : Blo 421773 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B633593 : Blo 421773 633593 := bstep (se 2 (by rfl) ⟨237597, by rfl⟩ : syracuseStep 633593 = 475195) B475195
theorem B953081 : Blo 421773 953081 := bstep (se 2 (by rfl) ⟨357405, by rfl⟩ : syracuseStep 953081 = 714811) B714811
theorem B715513 : Blo 421773 715513 := bstep (se 2 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 715513 = 536635) B536635
theorem B9276229 : Blo 421773 9276229 := bstep (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) B1739293
theorem B3337037 : Blo 421773 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B633695 : Blo 421773 633695 := bstep (se 1 (by rfl) ⟨475271, by rfl⟩ : syracuseStep 633695 = 950543) B950543
theorem B805727 : Blo 421773 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B633707 : Blo 421773 633707 := bstep (se 1 (by rfl) ⟨475280, by rfl⟩ : syracuseStep 633707 = 950561) B950561
theorem B601015 : Blo 421773 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B1428407 : Blo 421773 1428407 := bstep (se 1 (by rfl) ⟨1071305, by rfl⟩ : syracuseStep 1428407 = 2142611) B2142611
theorem B3435493 : Blo 421773 3435493 := bstep (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) B644155
theorem B953351 : Blo 421773 953351 := bstep (se 1 (by rfl) ⟨715013, by rfl⟩ : syracuseStep 953351 = 1430027) B1430027
theorem B715783 : Blo 421773 715783 := bstep (se 1 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 715783 = 1073675) B1073675
theorem B1207315 : Blo 421773 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B3214403 : Blo 421773 3214403 := bstep (se 1 (by rfl) ⟨2410802, by rfl⟩ : syracuseStep 3214403 = 4821605) B4821605
theorem B633935 : Blo 421773 633935 := bstep (se 1 (by rfl) ⟨475451, by rfl⟩ : syracuseStep 633935 = 950903) B950903
theorem B953423 : Blo 421773 953423 := bstep (se 1 (by rfl) ⟨715067, by rfl⟩ : syracuseStep 953423 = 1430135) B1430135
theorem B634055 : Blo 421773 634055 := bstep (se 1 (by rfl) ⟨475541, by rfl⟩ : syracuseStep 634055 = 951083) B951083
theorem B1207543 : Blo 421773 1207543 := bstep (se 1 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 1207543 = 1811315) B1811315
theorem B4345177 : Blo 421773 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B634217 : Blo 421773 634217 := bstep (se 2 (by rfl) ⟨237831, by rfl⟩ : syracuseStep 634217 = 475663) B475663
theorem B1609085 : Blo 421773 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B1019279 : Blo 421773 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B2444717 : Blo 421773 2444717 := bstep (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) B916769
theorem B634295 : Blo 421773 634295 := bstep (se 1 (by rfl) ⟨475721, by rfl⟩ : syracuseStep 634295 = 951443) B951443
theorem B716215 : Blo 421773 716215 := bstep (se 1 (by rfl) ⟨537161, by rfl⟩ : syracuseStep 716215 = 1074323) B1074323
theorem B2280923 : Blo 421773 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B634331 : Blo 421773 634331 := bstep (se 1 (by rfl) ⟨475748, by rfl⟩ : syracuseStep 634331 = 951497) B951497
theorem B953819 : Blo 421773 953819 := bstep (se 1 (by rfl) ⟨715364, by rfl⟩ : syracuseStep 953819 = 1430729) B1430729
theorem B1429001 : Blo 421773 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1207817 : Blo 421773 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B716411 : Blo 421773 716411 := bstep (se 1 (by rfl) ⟨537308, by rfl⟩ : syracuseStep 716411 = 1074617) B1074617
theorem B1085177 : Blo 421773 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B1208159 : Blo 421773 1208159 := bstep (se 1 (by rfl) ⟨906119, by rfl⟩ : syracuseStep 1208159 = 1812239) B1812239
theorem B17592227 : Blo 421773 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B421807 : Blo 421773 421807 := bstep (se 1 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 421807 = 632711) B632711
theorem B634799 : Blo 421773 634799 := bstep (se 1 (by rfl) ⟨476099, by rfl⟩ : syracuseStep 634799 = 952199) B952199
theorem B954287 : Blo 421773 954287 := bstep (se 1 (by rfl) ⟨715715, by rfl⟩ : syracuseStep 954287 = 1431431) B1431431
theorem B421831 : Blo 421773 421831 := bstep (se 1 (by rfl) ⟨316373, by rfl⟩ : syracuseStep 421831 = 632747) B632747
theorem B421851 : Blo 421773 421851 := bstep (se 1 (by rfl) ⟨316388, by rfl⟩ : syracuseStep 421851 = 632777) B632777
theorem B536539 : Blo 421773 536539 := bstep (se 1 (by rfl) ⟨402404, by rfl⟩ : syracuseStep 536539 = 804809) B804809
theorem B634889 : Blo 421773 634889 := bstep (se 2 (by rfl) ⟨238083, by rfl⟩ : syracuseStep 634889 = 476167) B476167
theorem B9129995 : Blo 421773 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B3215375 : Blo 421773 3215375 := bstep (se 1 (by rfl) ⟨2411531, by rfl⟩ : syracuseStep 3215375 = 4823063) B4823063
theorem B421927 : Blo 421773 421927 := bstep (se 1 (by rfl) ⟨316445, by rfl⟩ : syracuseStep 421927 = 632891) B632891
theorem B634919 : Blo 421773 634919 := bstep (se 1 (by rfl) ⟨476189, by rfl⟩ : syracuseStep 634919 = 952379) B952379
theorem B2617381 : Blo 421773 2617381 := bstep (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) B490759
theorem B421967 : Blo 421773 421967 := bstep (se 1 (by rfl) ⟨316475, by rfl⟩ : syracuseStep 421967 = 632951) B632951
theorem B2412625 : Blo 421773 2412625 := bstep (se 2 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 2412625 = 1809469) B1809469
theorem B421983 : Blo 421773 421983 := bstep (se 1 (by rfl) ⟨316487, by rfl⟩ : syracuseStep 421983 = 632975) B632975
theorem B422011 : Blo 421773 422011 := bstep (se 1 (by rfl) ⟨316508, by rfl⟩ : syracuseStep 422011 = 633017) B633017
theorem B635003 : Blo 421773 635003 := bstep (se 1 (by rfl) ⟨476252, by rfl⟩ : syracuseStep 635003 = 952505) B952505
theorem B954539 : Blo 421773 954539 := bstep (se 1 (by rfl) ⟨715904, by rfl⟩ : syracuseStep 954539 = 1431809) B1431809
theorem B422063 : Blo 421773 422063 := bstep (se 1 (by rfl) ⟨316547, by rfl⟩ : syracuseStep 422063 = 633095) B633095
theorem B422087 : Blo 421773 422087 := bstep (se 1 (by rfl) ⟨316565, by rfl⟩ : syracuseStep 422087 = 633131) B633131
theorem B422107 : Blo 421773 422107 := bstep (se 1 (by rfl) ⟨316580, by rfl⟩ : syracuseStep 422107 = 633161) B633161
theorem B635129 : Blo 421773 635129 := bstep (se 2 (by rfl) ⟨238173, by rfl⟩ : syracuseStep 635129 = 476347) B476347
theorem B1372427 : Blo 421773 1372427 := bstep (se 1 (by rfl) ⟨1029320, by rfl⟩ : syracuseStep 1372427 = 2058641) B2058641
theorem B4837643 : Blo 421773 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B422183 : Blo 421773 422183 := bstep (se 1 (by rfl) ⟨316637, by rfl⟩ : syracuseStep 422183 = 633275) B633275
theorem B4059467 : Blo 421773 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B422223 : Blo 421773 422223 := bstep (se 1 (by rfl) ⟨316667, by rfl⟩ : syracuseStep 422223 = 633335) B633335
theorem B422239 : Blo 421773 422239 := bstep (se 1 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 422239 = 633359) B633359
theorem B635231 : Blo 421773 635231 := bstep (se 1 (by rfl) ⟨476423, by rfl⟩ : syracuseStep 635231 = 952847) B952847
theorem B602473 : Blo 421773 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B1429865 : Blo 421773 1429865 := bstep (se 2 (by rfl) ⟨536199, by rfl⟩ : syracuseStep 1429865 = 1072399) B1072399
theorem B635243 : Blo 421773 635243 := bstep (se 1 (by rfl) ⟨476432, by rfl⟩ : syracuseStep 635243 = 952865) B952865
theorem B422267 : Blo 421773 422267 := bstep (se 1 (by rfl) ⟨316700, by rfl⟩ : syracuseStep 422267 = 633401) B633401
theorem B676271 : Blo 421773 676271 := bstep (se 1 (by rfl) ⟨507203, by rfl⟩ : syracuseStep 676271 = 1014407) B1014407
theorem B422319 : Blo 421773 422319 := bstep (se 1 (by rfl) ⟨316739, by rfl⟩ : syracuseStep 422319 = 633479) B633479
theorem B422343 : Blo 421773 422343 := bstep (se 1 (by rfl) ⟨316757, by rfl⟩ : syracuseStep 422343 = 633515) B633515
theorem B422363 : Blo 421773 422363 := bstep (se 1 (by rfl) ⟨316772, by rfl⟩ : syracuseStep 422363 = 633545) B633545
theorem B602587 : Blo 421773 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B1208819 : Blo 421773 1208819 := bstep (se 1 (by rfl) ⟨906614, by rfl⟩ : syracuseStep 1208819 = 1813229) B1813229
theorem B1806857 : Blo 421773 1806857 := bstep (se 2 (by rfl) ⟨677571, by rfl⟩ : syracuseStep 1806857 = 1355143) B1355143
theorem B1520167 : Blo 421773 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B422439 : Blo 421773 422439 := bstep (se 1 (by rfl) ⟨316829, by rfl⟩ : syracuseStep 422439 = 633659) B633659
theorem B1806907 : Blo 421773 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B3224123 : Blo 421773 3224123 := bstep (se 1 (by rfl) ⟨2418092, by rfl⟩ : syracuseStep 3224123 = 4836185) B4836185
theorem B422479 : Blo 421773 422479 := bstep (se 1 (by rfl) ⟨316859, by rfl⟩ : syracuseStep 422479 = 633719) B633719
theorem B635471 : Blo 421773 635471 := bstep (se 1 (by rfl) ⟨476603, by rfl⟩ : syracuseStep 635471 = 953207) B953207
theorem B422495 : Blo 421773 422495 := bstep (se 1 (by rfl) ⟨316871, by rfl⟩ : syracuseStep 422495 = 633743) B633743
theorem B1356385 : Blo 421773 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B422523 : Blo 421773 422523 := bstep (se 1 (by rfl) ⟨316892, by rfl⟩ : syracuseStep 422523 = 633785) B633785
theorem B2888327 : Blo 421773 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B422575 : Blo 421773 422575 := bstep (se 1 (by rfl) ⟨316931, by rfl⟩ : syracuseStep 422575 = 633863) B633863
theorem B422599 : Blo 421773 422599 := bstep (se 1 (by rfl) ⟨316949, by rfl⟩ : syracuseStep 422599 = 633899) B633899
theorem B635591 : Blo 421773 635591 := bstep (se 1 (by rfl) ⟨476693, by rfl⟩ : syracuseStep 635591 = 953387) B953387
theorem B955079 : Blo 421773 955079 := bstep (se 1 (by rfl) ⟨716309, by rfl⟩ : syracuseStep 955079 = 1432619) B1432619
theorem B422619 : Blo 421773 422619 := bstep (se 1 (by rfl) ⟨316964, by rfl⟩ : syracuseStep 422619 = 633929) B633929
theorem B7230221 : Blo 421773 7230221 := bstep (se 3 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 7230221 = 2711333) B2711333
theorem B2896669 : Blo 421773 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B422695 : Blo 421773 422695 := bstep (se 1 (by rfl) ⟨317021, by rfl⟩ : syracuseStep 422695 = 634043) B634043
theorem B1209161 : Blo 421773 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B422735 : Blo 421773 422735 := bstep (se 1 (by rfl) ⟨317051, by rfl⟩ : syracuseStep 422735 = 634103) B634103
theorem B1069919 : Blo 421773 1069919 := bstep (se 1 (by rfl) ⟨802439, by rfl⟩ : syracuseStep 1069919 = 1604879) B1604879
theorem B422751 : Blo 421773 422751 := bstep (se 1 (by rfl) ⟨317063, by rfl⟩ : syracuseStep 422751 = 634127) B634127
theorem B635753 : Blo 421773 635753 := bstep (se 2 (by rfl) ⟨238407, by rfl⟩ : syracuseStep 635753 = 476815) B476815
theorem B422779 : Blo 421773 422779 := bstep (se 1 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 422779 = 634169) B634169
theorem B856993 : Blo 421773 856993 := bstep (se 2 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 856993 = 642745) B642745
theorem B676783 : Blo 421773 676783 := bstep (se 1 (by rfl) ⟨507587, by rfl⟩ : syracuseStep 676783 = 1015175) B1015175
theorem B422831 : Blo 421773 422831 := bstep (se 1 (by rfl) ⟨317123, by rfl⟩ : syracuseStep 422831 = 634247) B634247
theorem B2749367 : Blo 421773 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B635831 : Blo 421773 635831 := bstep (se 1 (by rfl) ⟨476873, by rfl⟩ : syracuseStep 635831 = 953747) B953747
theorem B1430459 : Blo 421773 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B1209275 : Blo 421773 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B422855 : Blo 421773 422855 := bstep (se 1 (by rfl) ⟨317141, by rfl⟩ : syracuseStep 422855 = 634283) B634283
theorem B422875 : Blo 421773 422875 := bstep (se 1 (by rfl) ⟨317156, by rfl⟩ : syracuseStep 422875 = 634313) B634313
theorem B635867 : Blo 421773 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B1446913 : Blo 421773 1446913 := bstep (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) B1085185
theorem B676873 : Blo 421773 676873 := bstep (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) B507655
theorem B422951 : Blo 421773 422951 := bstep (se 1 (by rfl) ⟨317213, by rfl⟩ : syracuseStep 422951 = 634427) B634427
theorem B1209401 : Blo 421773 1209401 := bstep (se 2 (by rfl) ⟨453525, by rfl⟩ : syracuseStep 1209401 = 907051) B907051
theorem B2602063 : Blo 421773 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B422991 : Blo 421773 422991 := bstep (se 1 (by rfl) ⟨317243, by rfl⟩ : syracuseStep 422991 = 634487) B634487
theorem B423007 : Blo 421773 423007 := bstep (se 1 (by rfl) ⟨317255, by rfl⟩ : syracuseStep 423007 = 634511) B634511
theorem B423035 : Blo 421773 423035 := bstep (se 1 (by rfl) ⟨317276, by rfl⟩ : syracuseStep 423035 = 634553) B634553
theorem B423087 : Blo 421773 423087 := bstep (se 1 (by rfl) ⟨317315, by rfl⟩ : syracuseStep 423087 = 634631) B634631
theorem B423111 : Blo 421773 423111 := bstep (se 1 (by rfl) ⟨317333, by rfl⟩ : syracuseStep 423111 = 634667) B634667
theorem B5862617 : Blo 421773 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B423131 : Blo 421773 423131 := bstep (se 1 (by rfl) ⟨317348, by rfl⟩ : syracuseStep 423131 = 634697) B634697
theorem B1610999 : Blo 421773 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B423207 : Blo 421773 423207 := bstep (se 1 (by rfl) ⟨317405, by rfl⟩ : syracuseStep 423207 = 634811) B634811
theorem B423247 : Blo 421773 423247 := bstep (se 1 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 423247 = 634871) B634871
theorem B423263 : Blo 421773 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B603487 : Blo 421773 603487 := bstep (se 1 (by rfl) ⟨452615, by rfl⟩ : syracuseStep 603487 = 905231) B905231
theorem B423291 : Blo 421773 423291 := bstep (se 1 (by rfl) ⟨317468, by rfl⟩ : syracuseStep 423291 = 634937) B634937
theorem B423343 : Blo 421773 423343 := bstep (se 1 (by rfl) ⟨317507, by rfl⟩ : syracuseStep 423343 = 635015) B635015
theorem B636335 : Blo 421773 636335 := bstep (se 1 (by rfl) ⟨477251, by rfl⟩ : syracuseStep 636335 = 954503) B954503
theorem B423367 : Blo 421773 423367 := bstep (se 1 (by rfl) ⟨317525, by rfl⟩ : syracuseStep 423367 = 635051) B635051
theorem B1930715 : Blo 421773 1930715 := bstep (se 1 (by rfl) ⟨1448036, by rfl⟩ : syracuseStep 1930715 = 2896073) B2896073
theorem B423387 : Blo 421773 423387 := bstep (se 1 (by rfl) ⟨317540, by rfl⟩ : syracuseStep 423387 = 635081) B635081
theorem B636425 : Blo 421773 636425 := bstep (se 2 (by rfl) ⟨238659, by rfl⟩ : syracuseStep 636425 = 477319) B477319
theorem B1070617 : Blo 421773 1070617 := bstep (se 2 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 1070617 = 802963) B802963
theorem B423463 : Blo 421773 423463 := bstep (se 1 (by rfl) ⟨317597, by rfl⟩ : syracuseStep 423463 = 635195) B635195
theorem B1324583 : Blo 421773 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B636455 : Blo 421773 636455 := bstep (se 1 (by rfl) ⟨477341, by rfl⟩ : syracuseStep 636455 = 954683) B954683
theorem B423503 : Blo 421773 423503 := bstep (se 1 (by rfl) ⟨317627, by rfl⟩ : syracuseStep 423503 = 635255) B635255
theorem B423519 : Blo 421773 423519 := bstep (se 1 (by rfl) ⟨317639, by rfl⟩ : syracuseStep 423519 = 635279) B635279
theorem B423547 : Blo 421773 423547 := bstep (se 1 (by rfl) ⟨317660, by rfl⟩ : syracuseStep 423547 = 635321) B635321
theorem B636539 : Blo 421773 636539 := bstep (se 1 (by rfl) ⟨477404, by rfl⟩ : syracuseStep 636539 = 954809) B954809
theorem B423599 : Blo 421773 423599 := bstep (se 1 (by rfl) ⟨317699, by rfl⟩ : syracuseStep 423599 = 635399) B635399
theorem B423623 : Blo 421773 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B423643 : Blo 421773 423643 := bstep (se 1 (by rfl) ⟨317732, by rfl⟩ : syracuseStep 423643 = 635465) B635465
theorem B636665 : Blo 421773 636665 := bstep (se 2 (by rfl) ⟨238749, by rfl⟩ : syracuseStep 636665 = 477499) B477499
theorem B423719 : Blo 421773 423719 := bstep (se 1 (by rfl) ⟨317789, by rfl⟩ : syracuseStep 423719 = 635579) B635579
theorem B1070921 : Blo 421773 1070921 := bstep (se 2 (by rfl) ⟨401595, by rfl⟩ : syracuseStep 1070921 = 803191) B803191
theorem B423759 : Blo 421773 423759 := bstep (se 1 (by rfl) ⟨317819, by rfl⟩ : syracuseStep 423759 = 635639) B635639
theorem B423775 : Blo 421773 423775 := bstep (se 1 (by rfl) ⟨317831, by rfl⟩ : syracuseStep 423775 = 635663) B635663
theorem B636767 : Blo 421773 636767 := bstep (se 1 (by rfl) ⟨477575, by rfl⟩ : syracuseStep 636767 = 955151) B955151
theorem B1603435 : Blo 421773 1603435 := bstep (se 1 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 1603435 = 2405153) B2405153
theorem B743275 : Blo 421773 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B636779 : Blo 421773 636779 := bstep (se 1 (by rfl) ⟨477584, by rfl⟩ : syracuseStep 636779 = 955169) B955169
theorem B423803 : Blo 421773 423803 := bstep (se 1 (by rfl) ⟨317852, by rfl⟩ : syracuseStep 423803 = 635705) B635705
theorem B2135969 : Blo 421773 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B423855 : Blo 421773 423855 := bstep (se 1 (by rfl) ⟨317891, by rfl⟩ : syracuseStep 423855 = 635783) B635783
theorem B907195 : Blo 421773 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B2889665 : Blo 421773 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B423879 : Blo 421773 423879 := bstep (se 1 (by rfl) ⟨317909, by rfl⟩ : syracuseStep 423879 = 635819) B635819
theorem B423899 : Blo 421773 423899 := bstep (se 1 (by rfl) ⟨317924, by rfl⟩ : syracuseStep 423899 = 635849) B635849
theorem B3045383 : Blo 421773 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B423975 : Blo 421773 423975 := bstep (se 1 (by rfl) ⟨317981, by rfl⟩ : syracuseStep 423975 = 635963) B635963
theorem B604199 : Blo 421773 604199 := bstep (se 1 (by rfl) ⟨453149, by rfl⟩ : syracuseStep 604199 = 906299) B906299
theorem B424015 : Blo 421773 424015 := bstep (se 1 (by rfl) ⟨318011, by rfl⟩ : syracuseStep 424015 = 636023) B636023
theorem B637007 : Blo 421773 637007 := bstep (se 1 (by rfl) ⟨477755, by rfl⟩ : syracuseStep 637007 = 955511) B955511
theorem B2029657 : Blo 421773 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B424031 : Blo 421773 424031 := bstep (se 1 (by rfl) ⟨318023, by rfl⟩ : syracuseStep 424031 = 636047) B636047
theorem B5142629 : Blo 421773 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B424059 : Blo 421773 424059 := bstep (se 1 (by rfl) ⟨318044, by rfl⟩ : syracuseStep 424059 = 636089) B636089
theorem B424111 : Blo 421773 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B1611971 : Blo 421773 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B424135 : Blo 421773 424135 := bstep (se 1 (by rfl) ⟨318101, by rfl⟩ : syracuseStep 424135 = 636203) B636203
theorem B637127 : Blo 421773 637127 := bstep (se 1 (by rfl) ⟨477845, by rfl⟩ : syracuseStep 637127 = 955691) B955691
theorem B424155 : Blo 421773 424155 := bstep (se 1 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 424155 = 636233) B636233
theorem B424231 : Blo 421773 424231 := bstep (se 1 (by rfl) ⟨318173, by rfl⟩ : syracuseStep 424231 = 636347) B636347
theorem B424271 : Blo 421773 424271 := bstep (se 1 (by rfl) ⟨318203, by rfl⟩ : syracuseStep 424271 = 636407) B636407
theorem B5429591 : Blo 421773 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B424287 : Blo 421773 424287 := bstep (se 1 (by rfl) ⟨318215, by rfl⟩ : syracuseStep 424287 = 636431) B636431
theorem B424315 : Blo 421773 424315 := bstep (se 1 (by rfl) ⟨318236, by rfl⟩ : syracuseStep 424315 = 636473) B636473
theorem B14686595 : Blo 421773 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B424367 : Blo 421773 424367 := bstep (se 1 (by rfl) ⟨318275, by rfl⟩ : syracuseStep 424367 = 636551) B636551
theorem B424391 : Blo 421773 424391 := bstep (se 1 (by rfl) ⟨318293, by rfl⟩ : syracuseStep 424391 = 636587) B636587
theorem B1423817 : Blo 421773 1423817 := bstep (se 2 (by rfl) ⟨533931, by rfl⟩ : syracuseStep 1423817 = 1067863) B1067863
theorem B424411 : Blo 421773 424411 := bstep (se 1 (by rfl) ⟨318308, by rfl⟩ : syracuseStep 424411 = 636617) B636617
theorem B3045869 : Blo 421773 3045869 := bstep (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) B1142201
theorem B424487 : Blo 421773 424487 := bstep (se 1 (by rfl) ⟨318365, by rfl⟩ : syracuseStep 424487 = 636731) B636731
theorem B8141381 : Blo 421773 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B424527 : Blo 421773 424527 := bstep (se 1 (by rfl) ⟨318395, by rfl⟩ : syracuseStep 424527 = 636791) B636791
theorem B604751 : Blo 421773 604751 := bstep (se 1 (by rfl) ⟨453563, by rfl⟩ : syracuseStep 604751 = 907127) B907127
theorem B424543 : Blo 421773 424543 := bstep (se 1 (by rfl) ⟨318407, by rfl⟩ : syracuseStep 424543 = 636815) B636815
theorem B1522273 : Blo 421773 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B1432187 : Blo 421773 1432187 := bstep (se 1 (by rfl) ⟨1074140, by rfl⟩ : syracuseStep 1432187 = 2148281) B2148281
theorem B424571 : Blo 421773 424571 := bstep (se 1 (by rfl) ⟨318428, by rfl⟩ : syracuseStep 424571 = 636857) B636857
theorem B424623 : Blo 421773 424623 := bstep (se 1 (by rfl) ⟨318467, by rfl⟩ : syracuseStep 424623 = 636935) B636935
theorem B424647 : Blo 421773 424647 := bstep (se 1 (by rfl) ⟨318485, by rfl⟩ : syracuseStep 424647 = 636971) B636971
theorem B1612487 : Blo 421773 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B3046099 : Blo 421773 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B1424087 : Blo 421773 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B424667 : Blo 421773 424667 := bstep (se 1 (by rfl) ⟨318500, by rfl⟩ : syracuseStep 424667 = 637001) B637001
theorem B1432349 : Blo 421773 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B424743 : Blo 421773 424743 := bstep (se 1 (by rfl) ⟨318557, by rfl⟩ : syracuseStep 424743 = 637115) B637115
theorem B1522475 : Blo 421773 1522475 := bstep (se 1 (by rfl) ⟨1141856, by rfl⟩ : syracuseStep 1522475 = 2283713) B2283713
theorem B4332365 : Blo 421773 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B1424303 : Blo 421773 1424303 := bstep (se 1 (by rfl) ⟨1068227, by rfl⟩ : syracuseStep 1424303 = 2136455) B2136455
theorem B19037105 : Blo 421773 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B949175 : Blo 421773 949175 := bstep (se 1 (by rfl) ⟨711881, by rfl⟩ : syracuseStep 949175 = 1423763) B1423763
theorem B1072055 : Blo 421773 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B1162171 : Blo 421773 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B801991 : Blo 421773 801991 := bstep (se 1 (by rfl) ⟨601493, by rfl⟩ : syracuseStep 801991 = 1202987) B1202987
theorem B2145527 : Blo 421773 2145527 := bstep (se 1 (by rfl) ⟨1609145, by rfl⟩ : syracuseStep 2145527 = 3218291) B3218291
theorem B5807351 : Blo 421773 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B711929 : Blo 421773 711929 := bstep (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) B533947
theorem B5430563 : Blo 421773 5430563 := bstep (se 1 (by rfl) ⟨4072922, by rfl⟩ : syracuseStep 5430563 = 8145845) B8145845
theorem B3218777 : Blo 421773 3218777 := bstep (se 2 (by rfl) ⟨1207041, by rfl⟩ : syracuseStep 3218777 = 2414083) B2414083
theorem B761231 : Blo 421773 761231 := bstep (se 1 (by rfl) ⟨570923, by rfl⟩ : syracuseStep 761231 = 1141847) B1141847
theorem B2891173 : Blo 421773 2891173 := bstep (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) B542095
theorem B712111 : Blo 421773 712111 := bstep (se 1 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 712111 = 1068167) B1068167
theorem B1433051 : Blo 421773 1433051 := bstep (se 1 (by rfl) ⟨1074788, by rfl⟩ : syracuseStep 1433051 = 2149577) B2149577
theorem B712199 : Blo 421773 712199 := bstep (se 1 (by rfl) ⟨534149, by rfl⟩ : syracuseStep 712199 = 1068299) B1068299
theorem B949769 : Blo 421773 949769 := bstep (se 2 (by rfl) ⟨356163, by rfl⟩ : syracuseStep 949769 = 712327) B712327
theorem B1342985 : Blo 421773 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B5414465 : Blo 421773 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B4070999 : Blo 421773 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B761555 : Blo 421773 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B1924823 : Blo 421773 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B2146013 : Blo 421773 2146013 := bstep (se 3 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 2146013 = 804755) B804755
theorem B900857 : Blo 421773 900857 := bstep (se 2 (by rfl) ⟨337821, by rfl⟩ : syracuseStep 900857 = 675643) B675643
theorem B3211001 : Blo 421773 3211001 := bstep (se 2 (by rfl) ⟨1204125, by rfl⟩ : syracuseStep 3211001 = 2408251) B2408251
theorem B26828597 : Blo 421773 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B2293571 : Blo 421773 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B712543 : Blo 421773 712543 := bstep (se 1 (by rfl) ⟨534407, by rfl⟩ : syracuseStep 712543 = 1068815) B1068815
theorem B950111 : Blo 421773 950111 := bstep (se 1 (by rfl) ⟨712583, by rfl⟩ : syracuseStep 950111 = 1425167) B1425167
theorem B712631 : Blo 421773 712631 := bstep (se 1 (by rfl) ⟨534473, by rfl⟩ : syracuseStep 712631 = 1068947) B1068947
theorem B6086663 : Blo 421773 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B1925129 : Blo 421773 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B3489841 : Blo 421773 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B3203225 : Blo 421773 3203225 := bstep (se 2 (by rfl) ⟨1201209, by rfl⟩ : syracuseStep 3203225 = 2402419) B2402419
theorem B450847 : Blo 421773 450847 := bstep (se 1 (by rfl) ⟨338135, by rfl⟩ : syracuseStep 450847 = 676271) B676271
theorem B475483 : Blo 421773 475483 := bstep (se 1 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 475483 = 713225) B713225
theorem B1204571 : Blo 421773 1204571 := bstep (se 1 (by rfl) ⟨903428, by rfl⟩ : syracuseStep 1204571 = 1806857) B1806857
theorem B13877669 : Blo 421773 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B1925551 : Blo 421773 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B475591 : Blo 421773 475591 := bstep (se 1 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 475591 = 713387) B713387
theorem B2179547 : Blo 421773 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B803297 : Blo 421773 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B713279 : Blo 421773 713279 := bstep (se 1 (by rfl) ⟨534959, by rfl⟩ : syracuseStep 713279 = 1069919) B1069919
theorem B803449 : Blo 421773 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B1983199 : Blo 421773 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B2409209 : Blo 421773 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B475951 : Blo 421773 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B3908411 : Blo 421773 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B951119 : Blo 421773 951119 := bstep (se 1 (by rfl) ⟨713339, by rfl⟩ : syracuseStep 951119 = 1426679) B1426679
theorem B1073999 : Blo 421773 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B1147727 : Blo 421773 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B476059 : Blo 421773 476059 := bstep (se 1 (by rfl) ⟨357044, by rfl⟩ : syracuseStep 476059 = 714089) B714089
theorem B1287143 : Blo 421773 1287143 := bstep (se 1 (by rfl) ⟨965357, by rfl⟩ : syracuseStep 1287143 = 1930715) B1930715
theorem B951335 : Blo 421773 951335 := bstep (se 1 (by rfl) ⟨713501, by rfl⟩ : syracuseStep 951335 = 1427003) B1427003
theorem B2147471 : Blo 421773 2147471 := bstep (se 1 (by rfl) ⟨1610603, by rfl⟩ : syracuseStep 2147471 = 3221207) B3221207
theorem B951515 : Blo 421773 951515 := bstep (se 1 (by rfl) ⟨713636, by rfl⟩ : syracuseStep 951515 = 1427273) B1427273
theorem B713947 : Blo 421773 713947 := bstep (se 1 (by rfl) ⟨535460, by rfl⟩ : syracuseStep 713947 = 1070921) B1070921
theorem B902377 : Blo 421773 902377 := bstep (se 2 (by rfl) ⟨338391, by rfl⟩ : syracuseStep 902377 = 676783) B676783
theorem B1549561 : Blo 421773 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B476455 : Blo 421773 476455 := bstep (se 1 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 476455 = 714683) B714683
theorem B1926443 : Blo 421773 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B4580657 : Blo 421773 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B902497 : Blo 421773 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B3581293 : Blo 421773 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B476527 : Blo 421773 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B951713 : Blo 421773 951713 := bstep (se 2 (by rfl) ⟨356892, by rfl⟩ : syracuseStep 951713 = 713785) B713785
theorem B1074647 : Blo 421773 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B476743 : Blo 421773 476743 := bstep (se 1 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 476743 = 715115) B715115
theorem B9791063 : Blo 421773 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B5793569 : Blo 421773 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B804649 : Blo 421773 804649 := bstep (se 2 (by rfl) ⟨301743, by rfl⟩ : syracuseStep 804649 = 603487) B603487
theorem B1074991 : Blo 421773 1074991 := bstep (se 1 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 1074991 = 1612487) B1612487
theorem B12691403 : Blo 421773 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B632783 : Blo 421773 632783 := bstep (se 1 (by rfl) ⟨474587, by rfl⟩ : syracuseStep 632783 = 949175) B949175
theorem B952271 : Blo 421773 952271 := bstep (se 1 (by rfl) ⟨714203, by rfl⟩ : syracuseStep 952271 = 1428407) B1428407
theorem B714703 : Blo 421773 714703 := bstep (se 1 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 714703 = 1072055) B1072055
theorem B1427489 : Blo 421773 1427489 := bstep (se 2 (by rfl) ⟨535308, by rfl⟩ : syracuseStep 1427489 = 1070617) B1070617
theorem B3606605 : Blo 421773 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B1607809 : Blo 421773 1607809 := bstep (se 2 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 1607809 = 1205857) B1205857
theorem B2033849 : Blo 421773 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B12503285 : Blo 421773 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B2148605 : Blo 421773 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B37234997 : Blo 421773 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B952649 : Blo 421773 952649 := bstep (se 2 (by rfl) ⟨357243, by rfl⟩ : syracuseStep 952649 = 714487) B714487
theorem B633179 : Blo 421773 633179 := bstep (se 1 (by rfl) ⟨474884, by rfl⟩ : syracuseStep 633179 = 949769) B949769
theorem B952667 : Blo 421773 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B805211 : Blo 421773 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B2713999 : Blo 421773 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B477607 : Blo 421773 477607 := bstep (se 1 (by rfl) ⟨358205, by rfl⟩ : syracuseStep 477607 = 716411) B716411
theorem B600571 : Blo 421773 600571 := bstep (se 1 (by rfl) ⟨450428, by rfl⟩ : syracuseStep 600571 = 900857) B900857
theorem B2140667 : Blo 421773 2140667 := bstep (se 1 (by rfl) ⟨1605500, by rfl⟩ : syracuseStep 2140667 = 3211001) B3211001
theorem B723451 : Blo 421773 723451 := bstep (se 1 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 723451 = 1085177) B1085177
theorem B17885731 : Blo 421773 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B633407 : Blo 421773 633407 := bstep (se 1 (by rfl) ⟨475055, by rfl⟩ : syracuseStep 633407 = 950111) B950111
theorem B805439 : Blo 421773 805439 := bstep (se 1 (by rfl) ⟨604079, by rfl⟩ : syracuseStep 805439 = 1208159) B1208159
theorem B715385 : Blo 421773 715385 := bstep (se 2 (by rfl) ⟨268269, by rfl⟩ : syracuseStep 715385 = 536539) B536539
theorem B715439 : Blo 421773 715439 := bstep (se 1 (by rfl) ⟨536579, by rfl⟩ : syracuseStep 715439 = 1073159) B1073159
theorem B633527 : Blo 421773 633527 := bstep (se 1 (by rfl) ⟨475145, by rfl⟩ : syracuseStep 633527 = 950291) B950291
theorem B600799 : Blo 421773 600799 := bstep (se 1 (by rfl) ⟨450599, by rfl⟩ : syracuseStep 600799 = 901199) B901199
theorem B2706209 : Blo 421773 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B2706311 : Blo 421773 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B633755 : Blo 421773 633755 := bstep (se 1 (by rfl) ⟨475316, by rfl⟩ : syracuseStep 633755 = 950633) B950633
theorem B953243 : Blo 421773 953243 := bstep (se 1 (by rfl) ⟨714932, by rfl⟩ : syracuseStep 953243 = 1429865) B1429865
theorem B715675 : Blo 421773 715675 := bstep (se 1 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 715675 = 1073513) B1073513
theorem B805879 : Blo 421773 805879 := bstep (se 1 (by rfl) ⟨604409, by rfl⟩ : syracuseStep 805879 = 1208819) B1208819
theorem B2149415 : Blo 421773 2149415 := bstep (se 1 (by rfl) ⟨1612061, by rfl⟩ : syracuseStep 2149415 = 3224123) B3224123
theorem B953441 : Blo 421773 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B4820147 : Blo 421773 4820147 := bstep (se 1 (by rfl) ⟨3615110, by rfl⟩ : syracuseStep 4820147 = 7230221) B7230221
theorem B806107 : Blo 421773 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B634151 : Blo 421773 634151 := bstep (se 1 (by rfl) ⟨475613, by rfl⟩ : syracuseStep 634151 = 951227) B951227
theorem B953639 : Blo 421773 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B806183 : Blo 421773 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B9178429 : Blo 421773 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B634235 : Blo 421773 634235 := bstep (se 1 (by rfl) ⟨475676, by rfl⟩ : syracuseStep 634235 = 951353) B951353
theorem B806267 : Blo 421773 806267 := bstep (se 1 (by rfl) ⟨604700, by rfl⟩ : syracuseStep 806267 = 1209401) B1209401
theorem B2026889 : Blo 421773 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B2141639 : Blo 421773 2141639 := bstep (se 1 (by rfl) ⟨1606229, by rfl⟩ : syracuseStep 2141639 = 3212459) B3212459
theorem B1715671 : Blo 421773 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B634361 : Blo 421773 634361 := bstep (se 2 (by rfl) ⟨237885, by rfl⟩ : syracuseStep 634361 = 475771) B475771
theorem B634463 : Blo 421773 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B536159 : Blo 421773 536159 := bstep (se 1 (by rfl) ⟨402119, by rfl⟩ : syracuseStep 536159 = 804239) B804239
theorem B954017 : Blo 421773 954017 := bstep (se 2 (by rfl) ⟨357756, by rfl⟩ : syracuseStep 954017 = 715513) B715513
theorem B3059363 : Blo 421773 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B3862225 : Blo 421773 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B601835 : Blo 421773 601835 := bstep (se 1 (by rfl) ⟨451376, by rfl⟩ : syracuseStep 601835 = 902753) B902753
theorem B2141963 : Blo 421773 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B634679 : Blo 421773 634679 := bstep (se 1 (by rfl) ⟨476009, by rfl⟩ : syracuseStep 634679 = 952019) B952019
theorem B1142657 : Blo 421773 1142657 := bstep (se 2 (by rfl) ⟨428496, by rfl⟩ : syracuseStep 1142657 = 856993) B856993
theorem B421787 : Blo 421773 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B1961903 : Blo 421773 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B421839 : Blo 421773 421839 := bstep (se 1 (by rfl) ⟨316379, by rfl⟩ : syracuseStep 421839 = 632759) B632759
theorem B421863 : Blo 421773 421863 := bstep (se 1 (by rfl) ⟨316397, by rfl⟩ : syracuseStep 421863 = 632795) B632795
theorem B1929217 : Blo 421773 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B954377 : Blo 421773 954377 := bstep (se 2 (by rfl) ⟨357891, by rfl⟩ : syracuseStep 954377 = 715783) B715783
theorem B1609753 : Blo 421773 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B3428419 : Blo 421773 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B634985 : Blo 421773 634985 := bstep (se 2 (by rfl) ⟨238119, by rfl⟩ : syracuseStep 634985 = 476239) B476239
theorem B1069321 : Blo 421773 1069321 := bstep (se 2 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 1069321 = 801991) B801991
theorem B422175 : Blo 421773 422175 := bstep (se 1 (by rfl) ⟨316631, by rfl⟩ : syracuseStep 422175 = 633263) B633263
theorem B536863 : Blo 421773 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B1610057 : Blo 421773 1610057 := bstep (se 2 (by rfl) ⟨603771, by rfl⟩ : syracuseStep 1610057 = 1207543) B1207543
theorem B422235 : Blo 421773 422235 := bstep (se 1 (by rfl) ⟨316676, by rfl⟩ : syracuseStep 422235 = 633353) B633353
theorem B422255 : Blo 421773 422255 := bstep (se 1 (by rfl) ⟨316691, by rfl⟩ : syracuseStep 422255 = 633383) B633383
theorem B5427587 : Blo 421773 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B422311 : Blo 421773 422311 := bstep (se 1 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 422311 = 633467) B633467
theorem B635303 : Blo 421773 635303 := bstep (se 1 (by rfl) ⟨476477, by rfl⟩ : syracuseStep 635303 = 952955) B952955
theorem B954791 : Blo 421773 954791 := bstep (se 1 (by rfl) ⟨716093, by rfl⟩ : syracuseStep 954791 = 1432187) B1432187
theorem B3207599 : Blo 421773 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B422395 : Blo 421773 422395 := bstep (se 1 (by rfl) ⟨316796, by rfl⟩ : syracuseStep 422395 = 633593) B633593
theorem B635387 : Blo 421773 635387 := bstep (se 1 (by rfl) ⟨476540, by rfl⟩ : syracuseStep 635387 = 953081) B953081
theorem B954899 : Blo 421773 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B3854897 : Blo 421773 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B2224691 : Blo 421773 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B2888243 : Blo 421773 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B422463 : Blo 421773 422463 := bstep (se 1 (by rfl) ⟨316847, by rfl⟩ : syracuseStep 422463 = 633695) B633695
theorem B422471 : Blo 421773 422471 := bstep (se 1 (by rfl) ⟨316853, by rfl⟩ : syracuseStep 422471 = 633707) B633707
theorem B954953 : Blo 421773 954953 := bstep (se 2 (by rfl) ⟨358107, by rfl⟩ : syracuseStep 954953 = 716215) B716215
theorem B635513 : Blo 421773 635513 := bstep (se 2 (by rfl) ⟨238317, by rfl⟩ : syracuseStep 635513 = 476635) B476635
theorem B635567 : Blo 421773 635567 := bstep (se 1 (by rfl) ⟨476675, by rfl⟩ : syracuseStep 635567 = 953351) B953351
theorem B2142935 : Blo 421773 2142935 := bstep (se 1 (by rfl) ⟨1607201, by rfl⟩ : syracuseStep 2142935 = 3214403) B3214403
theorem B422623 : Blo 421773 422623 := bstep (se 1 (by rfl) ⟨316967, by rfl⟩ : syracuseStep 422623 = 633935) B633935
theorem B635615 : Blo 421773 635615 := bstep (se 1 (by rfl) ⟨476711, by rfl⟩ : syracuseStep 635615 = 953423) B953423
theorem B422703 : Blo 421773 422703 := bstep (se 1 (by rfl) ⟨317027, by rfl⟩ : syracuseStep 422703 = 634055) B634055
theorem B1430351 : Blo 421773 1430351 := bstep (se 1 (by rfl) ⟨1072763, by rfl⟩ : syracuseStep 1430351 = 2145527) B2145527
theorem B3871567 : Blo 421773 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B422811 : Blo 421773 422811 := bstep (se 1 (by rfl) ⟨317108, by rfl⟩ : syracuseStep 422811 = 634217) B634217
theorem B422863 : Blo 421773 422863 := bstep (se 1 (by rfl) ⟨317147, by rfl⟩ : syracuseStep 422863 = 634295) B634295
theorem B1520615 : Blo 421773 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B422887 : Blo 421773 422887 := bstep (se 1 (by rfl) ⟨317165, by rfl⟩ : syracuseStep 422887 = 634331) B634331
theorem B635879 : Blo 421773 635879 := bstep (se 1 (by rfl) ⟨476909, by rfl⟩ : syracuseStep 635879 = 953819) B953819
theorem B955367 : Blo 421773 955367 := bstep (se 1 (by rfl) ⟨716525, by rfl⟩ : syracuseStep 955367 = 1433051) B1433051
theorem B3609643 : Blo 421773 3609643 := bstep (se 1 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 3609643 = 5414465) B5414465
theorem B1283215 : Blo 421773 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B4830353 : Blo 421773 4830353 := bstep (se 2 (by rfl) ⟨1811382, by rfl⟩ : syracuseStep 4830353 = 3622765) B3622765
theorem B1430675 : Blo 421773 1430675 := bstep (se 1 (by rfl) ⟨1073006, by rfl⟩ : syracuseStep 1430675 = 2146013) B2146013
theorem B4076689 : Blo 421773 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B1529047 : Blo 421773 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B636137 : Blo 421773 636137 := bstep (se 2 (by rfl) ⟨238551, by rfl⟩ : syracuseStep 636137 = 477103) B477103
theorem B1209593 : Blo 421773 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B11728151 : Blo 421773 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B423199 : Blo 421773 423199 := bstep (se 1 (by rfl) ⟨317399, by rfl⟩ : syracuseStep 423199 = 634799) B634799
theorem B636191 : Blo 421773 636191 := bstep (se 1 (by rfl) ⟨477143, by rfl⟩ : syracuseStep 636191 = 954287) B954287
theorem B423259 : Blo 421773 423259 := bstep (se 1 (by rfl) ⟨317444, by rfl⟩ : syracuseStep 423259 = 634889) B634889
theorem B2143583 : Blo 421773 2143583 := bstep (se 1 (by rfl) ⟨1607687, by rfl⟩ : syracuseStep 2143583 = 3215375) B3215375
theorem B423279 : Blo 421773 423279 := bstep (se 1 (by rfl) ⟨317459, by rfl⟩ : syracuseStep 423279 = 634919) B634919
theorem B1430945 : Blo 421773 1430945 := bstep (se 2 (by rfl) ⟨536604, by rfl⟩ : syracuseStep 1430945 = 1073209) B1073209
theorem B423335 : Blo 421773 423335 := bstep (se 1 (by rfl) ⟨317501, by rfl⟩ : syracuseStep 423335 = 635003) B635003
theorem B1611197 : Blo 421773 1611197 := bstep (se 3 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 1611197 = 604199) B604199
theorem B3216833 : Blo 421773 3216833 := bstep (se 2 (by rfl) ⟨1206312, by rfl⟩ : syracuseStep 3216833 = 2412625) B2412625
theorem B636359 : Blo 421773 636359 := bstep (se 1 (by rfl) ⟨477269, by rfl⟩ : syracuseStep 636359 = 954539) B954539
theorem B423419 : Blo 421773 423419 := bstep (se 1 (by rfl) ⟨317564, by rfl⟩ : syracuseStep 423419 = 635129) B635129
theorem B914951 : Blo 421773 914951 := bstep (se 1 (by rfl) ⟨686213, by rfl⟩ : syracuseStep 914951 = 1372427) B1372427
theorem B3225095 : Blo 421773 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B423487 : Blo 421773 423487 := bstep (se 1 (by rfl) ⟨317615, by rfl⟩ : syracuseStep 423487 = 635231) B635231
theorem B423495 : Blo 421773 423495 := bstep (se 1 (by rfl) ⟨317621, by rfl⟩ : syracuseStep 423495 = 635243) B635243
theorem B1070779 : Blo 421773 1070779 := bstep (se 1 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 1070779 = 1606169) B1606169
theorem B423647 : Blo 421773 423647 := bstep (se 1 (by rfl) ⟨317735, by rfl⟩ : syracuseStep 423647 = 635471) B635471
theorem B636713 : Blo 421773 636713 := bstep (se 2 (by rfl) ⟨238767, by rfl⟩ : syracuseStep 636713 = 477535) B477535
theorem B423727 : Blo 421773 423727 := bstep (se 1 (by rfl) ⟨317795, by rfl⟩ : syracuseStep 423727 = 635591) B635591
theorem B636719 : Blo 421773 636719 := bstep (se 1 (by rfl) ⟨477539, by rfl⟩ : syracuseStep 636719 = 955079) B955079
theorem B423835 : Blo 421773 423835 := bstep (se 1 (by rfl) ⟨317876, by rfl⟩ : syracuseStep 423835 = 635753) B635753
theorem B1832911 : Blo 421773 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B423887 : Blo 421773 423887 := bstep (se 1 (by rfl) ⟨317915, by rfl⟩ : syracuseStep 423887 = 635831) B635831
theorem B423911 : Blo 421773 423911 := bstep (se 1 (by rfl) ⟨317933, by rfl⟩ : syracuseStep 423911 = 635867) B635867
theorem B4634657 : Blo 421773 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B2029697 : Blo 421773 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B1808513 : Blo 421773 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B4061465 : Blo 421773 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B424223 : Blo 421773 424223 := bstep (se 1 (by rfl) ⟨318167, by rfl⟩ : syracuseStep 424223 = 636335) B636335
theorem B424283 : Blo 421773 424283 := bstep (se 1 (by rfl) ⟨318212, by rfl⟩ : syracuseStep 424283 = 636425) B636425
theorem B883055 : Blo 421773 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B424303 : Blo 421773 424303 := bstep (se 1 (by rfl) ⟨318227, by rfl⟩ : syracuseStep 424303 = 636455) B636455
theorem B5421437 : Blo 421773 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B59251085 : Blo 421773 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B10328471 : Blo 421773 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B424359 : Blo 421773 424359 := bstep (se 1 (by rfl) ⟨318269, by rfl⟩ : syracuseStep 424359 = 636539) B636539
theorem B12368305 : Blo 421773 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B424443 : Blo 421773 424443 := bstep (se 1 (by rfl) ⟨318332, by rfl⟩ : syracuseStep 424443 = 636665) B636665
theorem B424511 : Blo 421773 424511 := bstep (se 1 (by rfl) ⟨318383, by rfl⟩ : syracuseStep 424511 = 636767) B636767
theorem B1530431 : Blo 421773 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B801353 : Blo 421773 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B424519 : Blo 421773 424519 := bstep (se 1 (by rfl) ⟨318389, by rfl⟩ : syracuseStep 424519 = 636779) B636779
theorem B1423979 : Blo 421773 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B2030255 : Blo 421773 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B424671 : Blo 421773 424671 := bstep (se 1 (by rfl) ⟨318503, by rfl⟩ : syracuseStep 424671 = 637007) B637007
theorem B1071863 : Blo 421773 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B11606819 : Blo 421773 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B424751 : Blo 421773 424751 := bstep (se 1 (by rfl) ⟨318563, by rfl⟩ : syracuseStep 424751 = 637127) B637127
theorem B1612669 : Blo 421773 1612669 := bstep (se 3 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 1612669 = 604751) B604751
theorem B3619727 : Blo 421773 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B1268651 : Blo 421773 1268651 := bstep (se 1 (by rfl) ⟨951488, by rfl⟩ : syracuseStep 1268651 = 1902977) B1902977
theorem B949211 : Blo 421773 949211 := bstep (se 1 (by rfl) ⟨711908, by rfl⟩ : syracuseStep 949211 = 1423817) B1423817
theorem B2030579 : Blo 421773 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B2137103 : Blo 421773 2137103 := bstep (se 1 (by rfl) ⟨1602827, by rfl⟩ : syracuseStep 2137103 = 3205655) B3205655
theorem B949391 : Blo 421773 949391 := bstep (se 1 (by rfl) ⟨712043, by rfl⟩ : syracuseStep 949391 = 1424087) B1424087
theorem B1424573 : Blo 421773 1424573 := bstep (se 3 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 1424573 = 534215) B534215
theorem B1014983 : Blo 421773 1014983 := bstep (se 1 (by rfl) ⟨761237, by rfl⟩ : syracuseStep 1014983 = 1522475) B1522475
theorem B949481 : Blo 421773 949481 := bstep (se 2 (by rfl) ⟨356055, by rfl⟩ : syracuseStep 949481 = 712111) B712111
theorem B949535 : Blo 421773 949535 := bstep (se 1 (by rfl) ⟨712151, by rfl⟩ : syracuseStep 949535 = 1424303) B1424303
theorem B474619 : Blo 421773 474619 := bstep (se 1 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 474619 = 711929) B711929
theorem B3620375 : Blo 421773 3620375 := bstep (se 1 (by rfl) ⟨2715281, by rfl⟩ : syracuseStep 3620375 = 5430563) B5430563
theorem B2145851 : Blo 421773 2145851 := bstep (se 1 (by rfl) ⟨1609388, by rfl⟩ : syracuseStep 2145851 = 3218777) B3218777
theorem B1072723 : Blo 421773 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B507487 : Blo 421773 507487 := bstep (se 1 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 507487 = 761231) B761231
theorem B679519 : Blo 421773 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B1629811 : Blo 421773 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B474799 : Blo 421773 474799 := bstep (se 1 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 474799 = 712199) B712199
theorem B712489 : Blo 421773 712489 := bstep (se 2 (by rfl) ⟨267183, by rfl⟩ : syracuseStep 712489 = 534367) B534367
theorem B950057 : Blo 421773 950057 := bstep (se 2 (by rfl) ⟨356271, by rfl⟩ : syracuseStep 950057 = 712543) B712543
theorem B507703 : Blo 421773 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B2137913 : Blo 421773 2137913 := bstep (se 2 (by rfl) ⟨801717, by rfl⟩ : syracuseStep 2137913 = 1603435) B1603435
theorem B991033 : Blo 421773 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B475087 : Blo 421773 475087 := bstep (se 1 (by rfl) ⟨356315, by rfl⟩ : syracuseStep 475087 = 712631) B712631
theorem B2572289 : Blo 421773 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B2146337 : Blo 421773 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B4653121 : Blo 421773 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B4571225 : Blo 421773 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B1073371 : Blo 421773 1073371 := bstep (se 1 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 1073371 = 1610057) B1610057
theorem B803047 : Blo 421773 803047 := bstep (se 1 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 803047 = 1204571) B1204571
theorem B2138399 : Blo 421773 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B1425761 : Blo 421773 1425761 := bstep (se 2 (by rfl) ⟨534660, by rfl⟩ : syracuseStep 1425761 = 1069321) B1069321
theorem B1483127 : Blo 421773 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B1925495 : Blo 421773 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B475519 : Blo 421773 475519 := bstep (se 1 (by rfl) ⟨356639, by rfl⟩ : syracuseStep 475519 = 713279) B713279
theorem B1606139 : Blo 421773 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B2605607 : Blo 421773 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B16491073 : Blo 421773 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B23847641 : Blo 421773 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B3220235 : Blo 421773 3220235 := bstep (se 1 (by rfl) ⟨2415176, by rfl⟩ : syracuseStep 3220235 = 4830353) B4830353
theorem B5137181 : Blo 421773 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B1074131 : Blo 421773 1074131 := bstep (se 1 (by rfl) ⟨805598, by rfl⟩ : syracuseStep 1074131 = 1611197) B1611197
theorem B1074505 : Blo 421773 1074505 := bstep (se 2 (by rfl) ⟨402939, by rfl⟩ : syracuseStep 1074505 = 805879) B805879
theorem B3089771 : Blo 421773 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B951659 : Blo 421773 951659 := bstep (se 1 (by rfl) ⟨713744, by rfl⟩ : syracuseStep 951659 = 1427489) B1427489
theorem B1353131 : Blo 421773 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B1205675 : Blo 421773 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B24823331 : Blo 421773 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B3614291 : Blo 421773 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B951929 : Blo 421773 951929 := bstep (se 2 (by rfl) ⟨356973, by rfl⟩ : syracuseStep 951929 = 713947) B713947
theorem B1074809 : Blo 421773 1074809 := bstep (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) B806107
theorem B2066081 : Blo 421773 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B1427111 : Blo 421773 1427111 := bstep (se 1 (by rfl) ⟨1070333, by rfl⟩ : syracuseStep 1427111 = 2140667) B2140667
theorem B476923 : Blo 421773 476923 := bstep (se 1 (by rfl) ⟨357692, by rfl⟩ : syracuseStep 476923 = 715385) B715385
theorem B1353503 : Blo 421773 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B476959 : Blo 421773 476959 := bstep (se 1 (by rfl) ⟨357719, by rfl⟩ : syracuseStep 476959 = 715439) B715439
theorem B714575 : Blo 421773 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B1804139 : Blo 421773 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B1804207 : Blo 421773 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B845767 : Blo 421773 845767 := bstep (se 1 (by rfl) ⟨634325, by rfl⟩ : syracuseStep 845767 = 1268651) B1268651
theorem B2287561 : Blo 421773 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B632807 : Blo 421773 632807 := bstep (se 1 (by rfl) ⟨474605, by rfl⟩ : syracuseStep 632807 = 949211) B949211
theorem B1353719 : Blo 421773 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B632825 : Blo 421773 632825 := bstep (se 2 (by rfl) ⟨237309, by rfl⟩ : syracuseStep 632825 = 474619) B474619
theorem B632927 : Blo 421773 632927 := bstep (se 1 (by rfl) ⟨474695, by rfl⟩ : syracuseStep 632927 = 949391) B949391
theorem B30951517 : Blo 421773 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B3213431 : Blo 421773 3213431 := bstep (se 1 (by rfl) ⟨2410073, by rfl⟩ : syracuseStep 3213431 = 4820147) B4820147
theorem B2173081 : Blo 421773 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B632987 : Blo 421773 632987 := bstep (se 1 (by rfl) ⟨474740, by rfl⟩ : syracuseStep 632987 = 949481) B949481
theorem B633023 : Blo 421773 633023 := bstep (se 1 (by rfl) ⟨474767, by rfl⟩ : syracuseStep 633023 = 949535) B949535
theorem B633065 : Blo 421773 633065 := bstep (se 2 (by rfl) ⟨237399, by rfl⟩ : syracuseStep 633065 = 474799) B474799
theorem B1427705 : Blo 421773 1427705 := bstep (se 2 (by rfl) ⟨535389, by rfl⟩ : syracuseStep 1427705 = 1070779) B1070779
theorem B1427759 : Blo 421773 1427759 := bstep (se 1 (by rfl) ⟨1070819, by rfl⟩ : syracuseStep 1427759 = 2141639) B2141639
theorem B9775525 : Blo 421773 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B1427975 : Blo 421773 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B633371 : Blo 421773 633371 := bstep (se 1 (by rfl) ⟨475028, by rfl⟩ : syracuseStep 633371 = 950057) B950057
theorem B633449 : Blo 421773 633449 := bstep (se 2 (by rfl) ⟨237543, by rfl⟩ : syracuseStep 633449 = 475087) B475087
theorem B952937 : Blo 421773 952937 := bstep (se 2 (by rfl) ⟨357351, by rfl⟩ : syracuseStep 952937 = 714703) B714703
theorem B4057775 : Blo 421773 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B1453031 : Blo 421773 1453031 := bstep (se 1 (by rfl) ⟨1089773, by rfl⟩ : syracuseStep 1453031 = 2179547) B2179547
theorem B601129 : Blo 421773 601129 := bstep (se 2 (by rfl) ⟨225423, by rfl⟩ : syracuseStep 601129 = 450847) B450847
theorem B715817 : Blo 421773 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B633977 : Blo 421773 633977 := bstep (se 2 (by rfl) ⟨237741, by rfl⟩ : syracuseStep 633977 = 475483) B475483
theorem B1428623 : Blo 421773 1428623 := bstep (se 1 (by rfl) ⟨1071467, by rfl⟩ : syracuseStep 1428623 = 2142935) B2142935
theorem B3624101 : Blo 421773 3624101 := bstep (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) B679519
theorem B634079 : Blo 421773 634079 := bstep (se 1 (by rfl) ⟨475559, by rfl⟩ : syracuseStep 634079 = 951119) B951119
theorem B953567 : Blo 421773 953567 := bstep (se 1 (by rfl) ⟨715175, by rfl⟩ : syracuseStep 953567 = 1430351) B1430351
theorem B715999 : Blo 421773 715999 := bstep (se 1 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 715999 = 1073999) B1073999
theorem B634121 : Blo 421773 634121 := bstep (se 2 (by rfl) ⟨237795, by rfl⟩ : syracuseStep 634121 = 475591) B475591
theorem B634223 : Blo 421773 634223 := bstep (se 1 (by rfl) ⟨475667, by rfl⟩ : syracuseStep 634223 = 951335) B951335
theorem B953783 : Blo 421773 953783 := bstep (se 1 (by rfl) ⟨715337, by rfl⟩ : syracuseStep 953783 = 1430675) B1430675
theorem B634343 : Blo 421773 634343 := bstep (se 1 (by rfl) ⟨475757, by rfl⟩ : syracuseStep 634343 = 951515) B951515
theorem B7818767 : Blo 421773 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B1429055 : Blo 421773 1429055 := bstep (se 1 (by rfl) ⟨1071791, by rfl⟩ : syracuseStep 1429055 = 2143583) B2143583
theorem B634475 : Blo 421773 634475 := bstep (se 1 (by rfl) ⟨475856, by rfl⟩ : syracuseStep 634475 = 951713) B951713
theorem B953963 : Blo 421773 953963 := bstep (se 1 (by rfl) ⟨715472, by rfl⟩ : syracuseStep 953963 = 1430945) B1430945
theorem B716431 : Blo 421773 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B609967 : Blo 421773 609967 := bstep (se 1 (by rfl) ⟨457475, by rfl⟩ : syracuseStep 609967 = 914951) B914951
theorem B2150063 : Blo 421773 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B634601 : Blo 421773 634601 := bstep (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) B475951
theorem B20598533 : Blo 421773 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B37007117 : Blo 421773 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B2150225 : Blo 421773 2150225 := bstep (se 2 (by rfl) ⟨806334, by rfl⟩ : syracuseStep 2150225 = 1612669) B1612669
theorem B3862379 : Blo 421773 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B634745 : Blo 421773 634745 := bstep (se 2 (by rfl) ⟨238029, by rfl⟩ : syracuseStep 634745 = 476059) B476059
theorem B954233 : Blo 421773 954233 := bstep (se 2 (by rfl) ⟨357837, by rfl⟩ : syracuseStep 954233 = 715675) B715675
theorem B2142125 : Blo 421773 2142125 := bstep (se 3 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 2142125 = 803297) B803297
theorem B421855 : Blo 421773 421855 := bstep (se 1 (by rfl) ⟨316391, by rfl⟩ : syracuseStep 421855 = 632783) B632783
theorem B634847 : Blo 421773 634847 := bstep (se 1 (by rfl) ⟨476135, by rfl⟩ : syracuseStep 634847 = 952271) B952271
theorem B2404403 : Blo 421773 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B4812857 : Blo 421773 4812857 := bstep (se 2 (by rfl) ⟨1804821, by rfl⟩ : syracuseStep 4812857 = 3609643) B3609643
theorem B1355899 : Blo 421773 1355899 := bstep (se 1 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 1355899 = 2033849) B2033849
theorem B8335523 : Blo 421773 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B2707643 : Blo 421773 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B5435585 : Blo 421773 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B635099 : Blo 421773 635099 := bstep (se 1 (by rfl) ⟨476324, by rfl⟩ : syracuseStep 635099 = 952649) B952649
theorem B422119 : Blo 421773 422119 := bstep (se 1 (by rfl) ⟨316589, by rfl⟩ : syracuseStep 422119 = 633179) B633179
theorem B635111 : Blo 421773 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B536807 : Blo 421773 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B1429757 : Blo 421773 1429757 := bstep (se 3 (by rfl) ⟨268079, by rfl⟩ : syracuseStep 1429757 = 536159) B536159
theorem B6885647 : Blo 421773 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B422271 : Blo 421773 422271 := bstep (se 1 (by rfl) ⟨316703, by rfl⟩ : syracuseStep 422271 = 633407) B633407
theorem B536959 : Blo 421773 536959 := bstep (se 1 (by rfl) ⟨402719, by rfl⟩ : syracuseStep 536959 = 805439) B805439
theorem B1020287 : Blo 421773 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B635273 : Blo 421773 635273 := bstep (se 2 (by rfl) ⟨238227, by rfl⟩ : syracuseStep 635273 = 476455) B476455
theorem B20648357 : Blo 421773 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B422351 : Blo 421773 422351 := bstep (se 1 (by rfl) ⟨316763, by rfl⟩ : syracuseStep 422351 = 633527) B633527
theorem B635369 : Blo 421773 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B2413151 : Blo 421773 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B422503 : Blo 421773 422503 := bstep (se 1 (by rfl) ⟨316877, by rfl⟩ : syracuseStep 422503 = 633755) B633755
theorem B635495 : Blo 421773 635495 := bstep (se 1 (by rfl) ⟨476621, by rfl⟩ : syracuseStep 635495 = 953243) B953243
theorem B635627 : Blo 421773 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B635657 : Blo 421773 635657 := bstep (se 2 (by rfl) ⟨238371, by rfl⟩ : syracuseStep 635657 = 476743) B476743
theorem B1430297 : Blo 421773 1430297 := bstep (se 2 (by rfl) ⟨536361, by rfl⟩ : syracuseStep 1430297 = 1072723) B1072723
theorem B676649 : Blo 421773 676649 := bstep (se 2 (by rfl) ⟨253743, by rfl⟩ : syracuseStep 676649 = 507487) B507487
theorem B676655 : Blo 421773 676655 := bstep (se 1 (by rfl) ⟨507491, by rfl⟩ : syracuseStep 676655 = 1014983) B1014983
theorem B422767 : Blo 421773 422767 := bstep (se 1 (by rfl) ⟨317075, by rfl⟩ : syracuseStep 422767 = 634151) B634151
theorem B635759 : Blo 421773 635759 := bstep (se 1 (by rfl) ⟨476819, by rfl⟩ : syracuseStep 635759 = 953639) B953639
theorem B537455 : Blo 421773 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B3060605 : Blo 421773 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B10269605 : Blo 421773 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B422823 : Blo 421773 422823 := bstep (se 1 (by rfl) ⟨317117, by rfl⟩ : syracuseStep 422823 = 634235) B634235
theorem B537511 : Blo 421773 537511 := bstep (se 1 (by rfl) ⟨403133, by rfl⟩ : syracuseStep 537511 = 806267) B806267
theorem B422907 : Blo 421773 422907 := bstep (se 1 (by rfl) ⟨317180, by rfl⟩ : syracuseStep 422907 = 634361) B634361
theorem B2413583 : Blo 421773 2413583 := bstep (se 1 (by rfl) ⟨1810187, by rfl⟩ : syracuseStep 2413583 = 3620375) B3620375
theorem B1430567 : Blo 421773 1430567 := bstep (se 1 (by rfl) ⟨1072925, by rfl⟩ : syracuseStep 1430567 = 2145851) B2145851
theorem B422975 : Blo 421773 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B676937 : Blo 421773 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B636011 : Blo 421773 636011 := bstep (se 1 (by rfl) ⟨477008, by rfl⟩ : syracuseStep 636011 = 954017) B954017
theorem B423119 : Blo 421773 423119 := bstep (se 1 (by rfl) ⟨317339, by rfl⟩ : syracuseStep 423119 = 634679) B634679
theorem B1307935 : Blo 421773 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B1283419 : Blo 421773 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B636251 : Blo 421773 636251 := bstep (se 1 (by rfl) ⟨477188, by rfl⟩ : syracuseStep 636251 = 954377) B954377
theorem B423323 : Blo 421773 423323 := bstep (se 1 (by rfl) ⟨317492, by rfl⟩ : syracuseStep 423323 = 634985) B634985
theorem B2135483 : Blo 421773 2135483 := bstep (se 1 (by rfl) ⟨1601612, by rfl⟩ : syracuseStep 2135483 = 3203225) B3203225
theorem B2143745 : Blo 421773 2143745 := bstep (se 2 (by rfl) ⟨803904, by rfl⟩ : syracuseStep 2143745 = 1607809) B1607809
theorem B3618391 : Blo 421773 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B423535 : Blo 421773 423535 := bstep (se 1 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 423535 = 635303) B635303
theorem B636527 : Blo 421773 636527 := bstep (se 1 (by rfl) ⟨477395, by rfl⟩ : syracuseStep 636527 = 954791) B954791
theorem B423591 : Blo 421773 423591 := bstep (se 1 (by rfl) ⟨317693, by rfl⟩ : syracuseStep 423591 = 635387) B635387
theorem B636599 : Blo 421773 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B2569931 : Blo 421773 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B636635 : Blo 421773 636635 := bstep (se 1 (by rfl) ⟨477476, by rfl⟩ : syracuseStep 636635 = 954953) B954953
theorem B423675 : Blo 421773 423675 := bstep (se 1 (by rfl) ⟨317756, by rfl⟩ : syracuseStep 423675 = 635513) B635513
theorem B423711 : Blo 421773 423711 := bstep (se 1 (by rfl) ⟨317783, by rfl⟩ : syracuseStep 423711 = 635567) B635567
theorem B423743 : Blo 421773 423743 := bstep (se 1 (by rfl) ⟨317807, by rfl⟩ : syracuseStep 423743 = 635615) B635615
theorem B3618665 : Blo 421773 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B636809 : Blo 421773 636809 := bstep (se 2 (by rfl) ⟨238803, by rfl⟩ : syracuseStep 636809 = 477607) B477607
theorem B1013743 : Blo 421773 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B858095 : Blo 421773 858095 := bstep (se 1 (by rfl) ⟨643571, by rfl⟩ : syracuseStep 858095 = 1287143) B1287143
theorem B423919 : Blo 421773 423919 := bstep (se 1 (by rfl) ⟨317939, by rfl⟩ : syracuseStep 423919 = 635879) B635879
theorem B636911 : Blo 421773 636911 := bstep (se 1 (by rfl) ⟨477683, by rfl⟩ : syracuseStep 636911 = 955367) B955367
theorem B3225581 : Blo 421773 3225581 := bstep (se 3 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 3225581 = 1209593) B1209593
theorem B800761 : Blo 421773 800761 := bstep (se 2 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 800761 = 600571) B600571
theorem B964601 : Blo 421773 964601 := bstep (se 2 (by rfl) ⟨361725, by rfl⟩ : syracuseStep 964601 = 723451) B723451
theorem B1431647 : Blo 421773 1431647 := bstep (se 1 (by rfl) ⟨1073735, by rfl⟩ : syracuseStep 1431647 = 2147471) B2147471
theorem B424091 : Blo 421773 424091 := bstep (se 1 (by rfl) ⟨318068, by rfl⟩ : syracuseStep 424091 = 636137) B636137
theorem B1071265 : Blo 421773 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B424127 : Blo 421773 424127 := bstep (se 1 (by rfl) ⟨318095, by rfl⟩ : syracuseStep 424127 = 636191) B636191
theorem B3053771 : Blo 421773 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B801065 : Blo 421773 801065 := bstep (se 2 (by rfl) ⟨300399, by rfl⟩ : syracuseStep 801065 = 600799) B600799
theorem B2644265 : Blo 421773 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B2144555 : Blo 421773 2144555 := bstep (se 1 (by rfl) ⟨1608416, by rfl⟩ : syracuseStep 2144555 = 3216833) B3216833
theorem B424239 : Blo 421773 424239 := bstep (se 1 (by rfl) ⟨318179, by rfl⟩ : syracuseStep 424239 = 636359) B636359
theorem B6527375 : Blo 421773 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B21142037 : Blo 421773 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B424475 : Blo 421773 424475 := bstep (se 1 (by rfl) ⟨318356, by rfl⟩ : syracuseStep 424475 = 636713) B636713
theorem B424479 : Blo 421773 424479 := bstep (se 1 (by rfl) ⟨318359, by rfl⟩ : syracuseStep 424479 = 636719) B636719
theorem B8460935 : Blo 421773 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B1432403 : Blo 421773 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B1710953 : Blo 421773 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B2136941 : Blo 421773 2136941 := bstep (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) B801353
theorem B588703 : Blo 421773 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B39500723 : Blo 421773 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B2038729 : Blo 421773 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B1203169 : Blo 421773 1203169 := bstep (se 2 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 1203169 = 902377) B902377
theorem B949319 : Blo 421773 949319 := bstep (se 1 (by rfl) ⟨711989, by rfl⟩ : syracuseStep 949319 = 1423979) B1423979
theorem B12237905 : Blo 421773 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B1203329 : Blo 421773 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B4775057 : Blo 421773 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B1604893 : Blo 421773 1604893 := bstep (se 3 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 1604893 = 601835) B601835
theorem B1424735 : Blo 421773 1424735 := bstep (se 1 (by rfl) ⟨1068551, by rfl⟩ : syracuseStep 1424735 = 2137103) B2137103
theorem B1432943 : Blo 421773 1432943 := bstep (se 1 (by rfl) ⟨1074707, by rfl⟩ : syracuseStep 1432943 = 2149415) B2149415
theorem B949715 : Blo 421773 949715 := bstep (se 1 (by rfl) ⟨712286, by rfl⟩ : syracuseStep 949715 = 1424573) B1424573
theorem B1351259 : Blo 421773 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B949985 : Blo 421773 949985 := bstep (se 2 (by rfl) ⟨356244, by rfl⟩ : syracuseStep 949985 = 712489) B712489
theorem B1072865 : Blo 421773 1072865 := bstep (se 2 (by rfl) ⟨402324, by rfl⟩ : syracuseStep 1072865 = 804649) B804649
theorem B1433321 : Blo 421773 1433321 := bstep (se 2 (by rfl) ⟨537495, by rfl⟩ : syracuseStep 1433321 = 1074991) B1074991
theorem B2039575 : Blo 421773 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B1425275 : Blo 421773 1425275 := bstep (se 1 (by rfl) ⟨1068956, by rfl⟩ : syracuseStep 1425275 = 2137913) B2137913
theorem B761771 : Blo 421773 761771 := bstep (se 1 (by rfl) ⟨571328, by rfl⟩ : syracuseStep 761771 = 1142657) B1142657
theorem B3047483 : Blo 421773 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B1425599 : Blo 421773 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B950507 : Blo 421773 950507 := bstep (se 1 (by rfl) ⟨712880, by rfl⟩ : syracuseStep 950507 = 1425761) B1425761
theorem B1737071 : Blo 421773 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B2146823 : Blo 421773 2146823 := bstep (se 1 (by rfl) ⟨1610117, by rfl⟩ : syracuseStep 2146823 = 3220235) B3220235
theorem B3424787 : Blo 421773 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B451099 : Blo 421773 451099 := bstep (se 1 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 451099 = 676649) B676649
theorem B451103 : Blo 421773 451103 := bstep (se 1 (by rfl) ⟨338327, by rfl⟩ : syracuseStep 451103 = 676655) B676655
theorem B13034033 : Blo 421773 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B2040403 : Blo 421773 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B21988097 : Blo 421773 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B902087 : Blo 421773 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B803783 : Blo 421773 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B2720765 : Blo 421773 2720765 := bstep (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) B1020287
theorem B16548887 : Blo 421773 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B2409527 : Blo 421773 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B951407 : Blo 421773 951407 := bstep (se 1 (by rfl) ⟨713555, by rfl⟩ : syracuseStep 951407 = 1427111) B1427111
theorem B1713287 : Blo 421773 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B902335 : Blo 421773 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B476383 : Blo 421773 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B951803 : Blo 421773 951803 := bstep (se 1 (by rfl) ⟨713852, by rfl⟩ : syracuseStep 951803 = 1427705) B1427705
theorem B534043 : Blo 421773 534043 := bstep (se 1 (by rfl) ⟨400532, by rfl⟩ : syracuseStep 534043 = 801065) B801065
theorem B1762843 : Blo 421773 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B951839 : Blo 421773 951839 := bstep (se 1 (by rfl) ⟨713879, by rfl⟩ : syracuseStep 951839 = 1427759) B1427759
theorem B4351583 : Blo 421773 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B951983 : Blo 421773 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B2139857 : Blo 421773 2139857 := bstep (se 2 (by rfl) ⟨802446, by rfl⟩ : syracuseStep 2139857 = 1604893) B1604893
theorem B2705183 : Blo 421773 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B1140635 : Blo 421773 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B968687 : Blo 421773 968687 := bstep (se 1 (by rfl) ⟨726515, by rfl⟩ : syracuseStep 968687 = 1453031) B1453031
theorem B477211 : Blo 421773 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B632879 : Blo 421773 632879 := bstep (se 1 (by rfl) ⟨474659, by rfl⟩ : syracuseStep 632879 = 949319) B949319
theorem B952415 : Blo 421773 952415 := bstep (se 1 (by rfl) ⟨714311, by rfl⟩ : syracuseStep 952415 = 1428623) B1428623
theorem B813289 : Blo 421773 813289 := bstep (se 2 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 813289 = 609967) B609967
theorem B633143 : Blo 421773 633143 := bstep (se 1 (by rfl) ⟨474857, by rfl⟩ : syracuseStep 633143 = 949715) B949715
theorem B5212511 : Blo 421773 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B952703 : Blo 421773 952703 := bstep (se 1 (by rfl) ⟨714527, by rfl⟩ : syracuseStep 952703 = 1429055) B1429055
theorem B105335261 : Blo 421773 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B633323 : Blo 421773 633323 := bstep (se 1 (by rfl) ⟨474992, by rfl⟩ : syracuseStep 633323 = 949985) B949985
theorem B715243 : Blo 421773 715243 := bstep (se 1 (by rfl) ⟨536432, by rfl⟩ : syracuseStep 715243 = 1072865) B1072865
theorem B13732355 : Blo 421773 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B2574919 : Blo 421773 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B3050081 : Blo 421773 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B1428083 : Blo 421773 1428083 := bstep (se 1 (by rfl) ⟨1071062, by rfl⟩ : syracuseStep 1428083 = 2142125) B2142125
theorem B1067681 : Blo 421773 1067681 := bstep (se 2 (by rfl) ⟨400380, by rfl⟩ : syracuseStep 1067681 = 800761) B800761
theorem B1714859 : Blo 421773 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B6204161 : Blo 421773 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B5557015 : Blo 421773 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B1805095 : Blo 421773 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B3623723 : Blo 421773 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B953171 : Blo 421773 953171 := bstep (se 1 (by rfl) ⟨714878, by rfl⟩ : syracuseStep 953171 = 1429757) B1429757
theorem B4590431 : Blo 421773 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B1805165 : Blo 421773 1805165 := bstep (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) B676937
theorem B1428353 : Blo 421773 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B13765571 : Blo 421773 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B1608767 : Blo 421773 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B634025 : Blo 421773 634025 := bstep (se 2 (by rfl) ⟨237759, by rfl⟩ : syracuseStep 634025 = 475519) B475519
theorem B715945 : Blo 421773 715945 := bstep (se 2 (by rfl) ⟨268479, by rfl⟩ : syracuseStep 715945 = 536959) B536959
theorem B953531 : Blo 421773 953531 := bstep (se 1 (by rfl) ⟨715148, by rfl⟩ : syracuseStep 953531 = 1430297) B1430297
theorem B716087 : Blo 421773 716087 := bstep (se 1 (by rfl) ⟨537065, by rfl⟩ : syracuseStep 716087 = 1074131) B1074131
theorem B1609055 : Blo 421773 1609055 := bstep (se 1 (by rfl) ⟨1206791, by rfl⟩ : syracuseStep 1609055 = 2413583) B2413583
theorem B953711 : Blo 421773 953711 := bstep (se 1 (by rfl) ⟨715283, by rfl⟩ : syracuseStep 953711 = 1430567) B1430567
theorem B2059847 : Blo 421773 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B634439 : Blo 421773 634439 := bstep (se 1 (by rfl) ⟨475829, by rfl⟩ : syracuseStep 634439 = 951659) B951659
theorem B1429163 : Blo 421773 1429163 := bstep (se 1 (by rfl) ⟨1071872, by rfl⟩ : syracuseStep 1429163 = 2143745) B2143745
theorem B634619 : Blo 421773 634619 := bstep (se 1 (by rfl) ⟨475964, by rfl⟩ : syracuseStep 634619 = 951929) B951929
theorem B716539 : Blo 421773 716539 := bstep (se 1 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 716539 = 1074809) B1074809
theorem B716681 : Blo 421773 716681 := bstep (se 2 (by rfl) ⟨268755, by rfl⟩ : syracuseStep 716681 = 537511) B537511
theorem B2412443 : Blo 421773 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B421871 : Blo 421773 421871 := bstep (se 1 (by rfl) ⟨316403, by rfl⟩ : syracuseStep 421871 = 632807) B632807
theorem B2150387 : Blo 421773 2150387 := bstep (se 1 (by rfl) ⟨1612790, by rfl⟩ : syracuseStep 2150387 = 3225581) B3225581
theorem B421883 : Blo 421773 421883 := bstep (se 1 (by rfl) ⟨316412, by rfl⟩ : syracuseStep 421883 = 632825) B632825
theorem B643067 : Blo 421773 643067 := bstep (se 1 (by rfl) ⟨482300, by rfl⟩ : syracuseStep 643067 = 964601) B964601
theorem B421951 : Blo 421773 421951 := bstep (se 1 (by rfl) ⟨316463, by rfl⟩ : syracuseStep 421951 = 632927) B632927
theorem B954431 : Blo 421773 954431 := bstep (se 1 (by rfl) ⟨715823, by rfl⟩ : syracuseStep 954431 = 1431647) B1431647
theorem B2142287 : Blo 421773 2142287 := bstep (se 1 (by rfl) ⟨1606715, by rfl⟩ : syracuseStep 2142287 = 3213431) B3213431
theorem B421991 : Blo 421773 421991 := bstep (se 1 (by rfl) ⟨316493, by rfl⟩ : syracuseStep 421991 = 632987) B632987
theorem B422015 : Blo 421773 422015 := bstep (se 1 (by rfl) ⟨316511, by rfl⟩ : syracuseStep 422015 = 633023) B633023
theorem B2035847 : Blo 421773 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B422043 : Blo 421773 422043 := bstep (se 1 (by rfl) ⟨316532, by rfl⟩ : syracuseStep 422043 = 633065) B633065
theorem B1429703 : Blo 421773 1429703 := bstep (se 1 (by rfl) ⟨1072277, by rfl⟩ : syracuseStep 1429703 = 2144555) B2144555
theorem B954665 : Blo 421773 954665 := bstep (se 2 (by rfl) ⟨357999, by rfl⟩ : syracuseStep 954665 = 715999) B715999
theorem B14094691 : Blo 421773 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B422247 : Blo 421773 422247 := bstep (se 1 (by rfl) ⟨316685, by rfl⟩ : syracuseStep 422247 = 633371) B633371
theorem B422299 : Blo 421773 422299 := bstep (se 1 (by rfl) ⟨316724, by rfl⟩ : syracuseStep 422299 = 633449) B633449
theorem B635291 : Blo 421773 635291 := bstep (se 1 (by rfl) ⟨476468, by rfl⟩ : syracuseStep 635291 = 952937) B952937
theorem B5640623 : Blo 421773 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B5509549 : Blo 421773 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B954935 : Blo 421773 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B422651 : Blo 421773 422651 := bstep (se 1 (by rfl) ⟨316988, by rfl⟩ : syracuseStep 422651 = 633977) B633977
theorem B3183371 : Blo 421773 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B422719 : Blo 421773 422719 := bstep (se 1 (by rfl) ⟨317039, by rfl⟩ : syracuseStep 422719 = 634079) B634079
theorem B635711 : Blo 421773 635711 := bstep (se 1 (by rfl) ⟨476783, by rfl⟩ : syracuseStep 635711 = 953567) B953567
theorem B422747 : Blo 421773 422747 := bstep (se 1 (by rfl) ⟨317060, by rfl⟩ : syracuseStep 422747 = 634121) B634121
theorem B955241 : Blo 421773 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B422815 : Blo 421773 422815 := bstep (se 1 (by rfl) ⟨317111, by rfl⟩ : syracuseStep 422815 = 634223) B634223
theorem B635855 : Blo 421773 635855 := bstep (se 1 (by rfl) ⟨476891, by rfl⟩ : syracuseStep 635855 = 953783) B953783
theorem B422895 : Blo 421773 422895 := bstep (se 1 (by rfl) ⟨317171, by rfl⟩ : syracuseStep 422895 = 634343) B634343
theorem B635897 : Blo 421773 635897 := bstep (se 2 (by rfl) ⟨238461, by rfl⟩ : syracuseStep 635897 = 476923) B476923
theorem B635945 : Blo 421773 635945 := bstep (se 2 (by rfl) ⟨238479, by rfl⟩ : syracuseStep 635945 = 476959) B476959
theorem B422983 : Blo 421773 422983 := bstep (se 1 (by rfl) ⟨317237, by rfl⟩ : syracuseStep 422983 = 634475) B634475
theorem B635975 : Blo 421773 635975 := bstep (se 1 (by rfl) ⟨476981, by rfl⟩ : syracuseStep 635975 = 953963) B953963
theorem B423067 : Blo 421773 423067 := bstep (se 1 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 423067 = 634601) B634601
theorem B955547 : Blo 421773 955547 := bstep (se 1 (by rfl) ⟨716660, by rfl⟩ : syracuseStep 955547 = 1433321) B1433321
theorem B24671411 : Blo 421773 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B2405609 : Blo 421773 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B423163 : Blo 421773 423163 := bstep (se 1 (by rfl) ⟨317372, by rfl⟩ : syracuseStep 423163 = 634745) B634745
theorem B636155 : Blo 421773 636155 := bstep (se 1 (by rfl) ⟨477116, by rfl⟩ : syracuseStep 636155 = 954233) B954233
theorem B1127689 : Blo 421773 1127689 := bstep (se 2 (by rfl) ⟨422883, by rfl⟩ : syracuseStep 1127689 = 845767) B845767
theorem B3609917 : Blo 421773 3609917 := bstep (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) B1353719
theorem B423231 : Blo 421773 423231 := bstep (se 1 (by rfl) ⟨317423, by rfl⟩ : syracuseStep 423231 = 634847) B634847
theorem B1430891 : Blo 421773 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B1602935 : Blo 421773 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B3208571 : Blo 421773 3208571 := bstep (se 1 (by rfl) ⟨2406428, by rfl⟩ : syracuseStep 3208571 = 4812857) B4812857
theorem B41268689 : Blo 421773 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B423399 : Blo 421773 423399 := bstep (se 1 (by rfl) ⟨317549, by rfl⟩ : syracuseStep 423399 = 635099) B635099
theorem B423407 : Blo 421773 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B1807865 : Blo 421773 1807865 := bstep (se 2 (by rfl) ⟨677949, by rfl⟩ : syracuseStep 1807865 = 1355899) B1355899
theorem B2897441 : Blo 421773 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B988751 : Blo 421773 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B1283663 : Blo 421773 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B423515 : Blo 421773 423515 := bstep (se 1 (by rfl) ⟨317636, by rfl⟩ : syracuseStep 423515 = 635273) B635273
theorem B1431161 : Blo 421773 1431161 := bstep (se 2 (by rfl) ⟨536685, by rfl⟩ : syracuseStep 1431161 = 1073371) B1073371
theorem B1070729 : Blo 421773 1070729 := bstep (se 2 (by rfl) ⟨401523, by rfl⟩ : syracuseStep 1070729 = 803047) B803047
theorem B423579 : Blo 421773 423579 := bstep (se 1 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 423579 = 635369) B635369
theorem B1070759 : Blo 421773 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B955295 : Blo 421773 955295 := bstep (se 1 (by rfl) ⟨716471, by rfl⟩ : syracuseStep 955295 = 1432943) B1432943
theorem B423663 : Blo 421773 423663 := bstep (se 1 (by rfl) ⟨317747, by rfl⟩ : syracuseStep 423663 = 635495) B635495
theorem B15898427 : Blo 421773 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B423751 : Blo 421773 423751 := bstep (se 1 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 423751 = 635627) B635627
theorem B423771 : Blo 421773 423771 := bstep (se 1 (by rfl) ⟨317828, by rfl⟩ : syracuseStep 423771 = 635657) B635657
theorem B423839 : Blo 421773 423839 := bstep (se 1 (by rfl) ⟨317879, by rfl⟩ : syracuseStep 423839 = 635759) B635759
theorem B1431485 : Blo 421773 1431485 := bstep (se 3 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 1431485 = 536807) B536807
theorem B6846403 : Blo 421773 6846403 := bstep (se 1 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 6846403 = 10269605) B10269605
theorem B424007 : Blo 421773 424007 := bstep (se 1 (by rfl) ⟨318005, by rfl⟩ : syracuseStep 424007 = 636011) B636011
theorem B424167 : Blo 421773 424167 := bstep (se 1 (by rfl) ⟨318125, by rfl⟩ : syracuseStep 424167 = 636251) B636251
theorem B1423655 : Blo 421773 1423655 := bstep (se 1 (by rfl) ⟨1067741, by rfl⟩ : syracuseStep 1423655 = 2135483) B2135483
theorem B424351 : Blo 421773 424351 := bstep (se 1 (by rfl) ⟨318263, by rfl⟩ : syracuseStep 424351 = 636527) B636527
theorem B424399 : Blo 421773 424399 := bstep (se 1 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 424399 = 636599) B636599
theorem B424423 : Blo 421773 424423 := bstep (se 1 (by rfl) ⟨318317, by rfl⟩ : syracuseStep 424423 = 636635) B636635
theorem B784937 : Blo 421773 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B1202759 : Blo 421773 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B424539 : Blo 421773 424539 := bstep (se 1 (by rfl) ⟨318404, by rfl⟩ : syracuseStep 424539 = 636809) B636809
theorem B2718305 : Blo 421773 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1604225 : Blo 421773 1604225 := bstep (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) B1203169
theorem B572063 : Blo 421773 572063 := bstep (se 1 (by rfl) ⟨429047, by rfl⟩ : syracuseStep 572063 = 858095) B858095
theorem B424607 : Blo 421773 424607 := bstep (se 1 (by rfl) ⟨318455, by rfl⟩ : syracuseStep 424607 = 636911) B636911
theorem B801505 : Blo 421773 801505 := bstep (se 2 (by rfl) ⟨300564, by rfl⟩ : syracuseStep 801505 = 601129) B601129
theorem B1743913 : Blo 421773 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B1432673 : Blo 421773 1432673 := bstep (se 2 (by rfl) ⟨537252, by rfl⟩ : syracuseStep 1432673 = 1074505) B1074505
theorem B1711225 : Blo 421773 1711225 := bstep (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) B1283419
theorem B1424627 : Blo 421773 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B8158603 : Blo 421773 8158603 := bstep (se 1 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 8158603 = 12237905) B12237905
theorem B802219 : Blo 421773 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B2416067 : Blo 421773 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B4824521 : Blo 421773 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B949823 : Blo 421773 949823 := bstep (se 1 (by rfl) ⟨712367, by rfl⟩ : syracuseStep 949823 = 1424735) B1424735
theorem B1433213 : Blo 421773 1433213 := bstep (se 3 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 1433213 = 537455) B537455
theorem B2719433 : Blo 421773 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B900839 : Blo 421773 900839 := bstep (se 1 (by rfl) ⟨675629, by rfl⟩ : syracuseStep 900839 = 1351259) B1351259
theorem B2031389 : Blo 421773 2031389 := bstep (se 3 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 2031389 = 761771) B761771
theorem B1433375 : Blo 421773 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B1433483 : Blo 421773 1433483 := bstep (se 1 (by rfl) ⟨1075112, by rfl⟩ : syracuseStep 1433483 = 2150225) B2150225
theorem B950183 : Blo 421773 950183 := bstep (se 1 (by rfl) ⟨712637, by rfl⟩ : syracuseStep 950183 = 1425275) B1425275
theorem B1351657 : Blo 421773 1351657 := bstep (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) B1013743
theorem B2031655 : Blo 421773 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B44130365 : Blo 421773 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B950399 : Blo 421773 950399 := bstep (se 1 (by rfl) ⟨712799, by rfl⟩ : syracuseStep 950399 = 1425599) B1425599
theorem B3760415 : Blo 421773 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B2122247 : Blo 421773 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B9126533 : Blo 421773 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B1606351 : Blo 421773 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B3433225 : Blo 421773 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B2720537 : Blo 421773 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B2139047 : Blo 421773 2139047 := bstep (se 1 (by rfl) ⟨1604285, by rfl⟩ : syracuseStep 2139047 = 3208571) B3208571
theorem B1205243 : Blo 421773 1205243 := bstep (se 1 (by rfl) ⟨903932, by rfl⟩ : syracuseStep 1205243 = 1807865) B1807865
theorem B2901055 : Blo 421773 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B713819 : Blo 421773 713819 := bstep (se 1 (by rfl) ⟨535364, by rfl⟩ : syracuseStep 713819 = 1070729) B1070729
theorem B713839 : Blo 421773 713839 := bstep (se 1 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 713839 = 1070759) B1070759
theorem B1426571 : Blo 421773 1426571 := bstep (se 1 (by rfl) ⟨1069928, by rfl⟩ : syracuseStep 1426571 = 2139857) B2139857
theorem B1803455 : Blo 421773 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B6014341 : Blo 421773 6014341 := bstep (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) B1127689
theorem B3475007 : Blo 421773 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B70223507 : Blo 421773 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B2033387 : Blo 421773 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B1812203 : Blo 421773 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B952055 : Blo 421773 952055 := bstep (se 1 (by rfl) ⟨714041, by rfl⟩ : syracuseStep 952055 = 1428083) B1428083
theorem B1525501 : Blo 421773 1525501 := bstep (se 3 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 1525501 = 572063) B572063
theorem B75171685 : Blo 421773 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B952235 : Blo 421773 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B2402237 : Blo 421773 2402237 := bstep (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) B900839
theorem B9177047 : Blo 421773 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B477391 : Blo 421773 477391 := bstep (se 1 (by rfl) ⟨358043, by rfl⟩ : syracuseStep 477391 = 716087) B716087
theorem B633215 : Blo 421773 633215 := bstep (se 1 (by rfl) ⟨474911, by rfl⟩ : syracuseStep 633215 = 949823) B949823
theorem B952775 : Blo 421773 952775 := bstep (se 1 (by rfl) ⟨714581, by rfl⟩ : syracuseStep 952775 = 1429163) B1429163
theorem B1812955 : Blo 421773 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B1354259 : Blo 421773 1354259 := bstep (se 1 (by rfl) ⟨1015694, by rfl⟩ : syracuseStep 1354259 = 2031389) B2031389
theorem B9128537 : Blo 421773 9128537 := bstep (se 2 (by rfl) ⟨3423201, by rfl⟩ : syracuseStep 9128537 = 6846403) B6846403
theorem B477787 : Blo 421773 477787 := bstep (se 1 (by rfl) ⟨358340, by rfl⟩ : syracuseStep 477787 = 716681) B716681
theorem B1608295 : Blo 421773 1608295 := bstep (se 1 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 1608295 = 2412443) B2412443
theorem B633455 : Blo 421773 633455 := bstep (se 1 (by rfl) ⟨475091, by rfl⟩ : syracuseStep 633455 = 950183) B950183
theorem B428711 : Blo 421773 428711 := bstep (se 1 (by rfl) ⟨321533, by rfl⟩ : syracuseStep 428711 = 643067) B643067
theorem B1428191 : Blo 421773 1428191 := bstep (se 1 (by rfl) ⟨1071143, by rfl⟩ : syracuseStep 1428191 = 2142287) B2142287
theorem B953135 : Blo 421773 953135 := bstep (se 1 (by rfl) ⟨714851, by rfl⟩ : syracuseStep 953135 = 1429703) B1429703
theorem B633671 : Blo 421773 633671 := bstep (se 1 (by rfl) ⟨475253, by rfl⟩ : syracuseStep 633671 = 950507) B950507
theorem B1158047 : Blo 421773 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1084385 : Blo 421773 1084385 := bstep (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) B813289
theorem B14658731 : Blo 421773 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B601391 : Blo 421773 601391 := bstep (se 1 (by rfl) ⟨451043, by rfl⟩ : syracuseStep 601391 = 902087) B902087
theorem B953657 : Blo 421773 953657 := bstep (se 2 (by rfl) ⟨357621, by rfl⟩ : syracuseStep 953657 = 715243) B715243
theorem B1813843 : Blo 421773 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B634271 : Blo 421773 634271 := bstep (se 1 (by rfl) ⟨475703, by rfl⟩ : syracuseStep 634271 = 951407) B951407
theorem B1142191 : Blo 421773 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B953927 : Blo 421773 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B1068623 : Blo 421773 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B1068673 : Blo 421773 1068673 := bstep (se 2 (by rfl) ⟨400752, by rfl⟩ : syracuseStep 1068673 = 801505) B801505
theorem B27512459 : Blo 421773 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B634535 : Blo 421773 634535 := bstep (se 1 (by rfl) ⟨475901, by rfl⟩ : syracuseStep 634535 = 951803) B951803
theorem B634559 : Blo 421773 634559 := bstep (se 1 (by rfl) ⟨475919, by rfl⟩ : syracuseStep 634559 = 951839) B951839
theorem B659167 : Blo 421773 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B855775 : Blo 421773 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B954107 : Blo 421773 954107 := bstep (se 1 (by rfl) ⟨715580, by rfl⟩ : syracuseStep 954107 = 1431161) B1431161
theorem B634655 : Blo 421773 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B954323 : Blo 421773 954323 := bstep (se 1 (by rfl) ⟨715742, by rfl⟩ : syracuseStep 954323 = 1431485) B1431485
theorem B421919 : Blo 421773 421919 := bstep (se 1 (by rfl) ⟨316439, by rfl⟩ : syracuseStep 421919 = 632879) B632879
theorem B634943 : Blo 421773 634943 := bstep (se 1 (by rfl) ⟨476207, by rfl⟩ : syracuseStep 634943 = 952415) B952415
theorem B2093165 : Blo 421773 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B422095 : Blo 421773 422095 := bstep (se 1 (by rfl) ⟨316571, by rfl⟩ : syracuseStep 422095 = 633143) B633143
theorem B954593 : Blo 421773 954593 := bstep (se 2 (by rfl) ⟨357972, by rfl⟩ : syracuseStep 954593 = 715945) B715945
theorem B635135 : Blo 421773 635135 := bstep (se 1 (by rfl) ⟨476351, by rfl⟩ : syracuseStep 635135 = 952703) B952703
theorem B635177 : Blo 421773 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B422215 : Blo 421773 422215 := bstep (se 1 (by rfl) ⟨316661, by rfl⟩ : syracuseStep 422215 = 633323) B633323
theorem B9154903 : Blo 421773 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B1069483 : Blo 421773 1069483 := bstep (se 1 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 1069483 = 1604225) B1604225
theorem B1143239 : Blo 421773 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B635447 : Blo 421773 635447 := bstep (se 1 (by rfl) ⟨476585, by rfl⟩ : syracuseStep 635447 = 953171) B953171
theorem B1069625 : Blo 421773 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B3060287 : Blo 421773 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B955115 : Blo 421773 955115 := bstep (se 1 (by rfl) ⟨716336, by rfl⟩ : syracuseStep 955115 = 1432673) B1432673
theorem B422683 : Blo 421773 422683 := bstep (se 1 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 422683 = 634025) B634025
theorem B635687 : Blo 421773 635687 := bstep (se 1 (by rfl) ⟨476765, by rfl⟩ : syracuseStep 635687 = 953531) B953531
theorem B635807 : Blo 421773 635807 := bstep (se 1 (by rfl) ⟨476855, by rfl⟩ : syracuseStep 635807 = 953711) B953711
theorem B1610711 : Blo 421773 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B3216347 : Blo 421773 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B955385 : Blo 421773 955385 := bstep (se 2 (by rfl) ⟨358269, by rfl⟩ : syracuseStep 955385 = 716539) B716539
theorem B1373231 : Blo 421773 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B422959 : Blo 421773 422959 := bstep (se 1 (by rfl) ⟨317219, by rfl⟩ : syracuseStep 422959 = 634439) B634439
theorem B955475 : Blo 421773 955475 := bstep (se 1 (by rfl) ⟨716606, by rfl⟩ : syracuseStep 955475 = 1433213) B1433213
theorem B423079 : Blo 421773 423079 := bstep (se 1 (by rfl) ⟨317309, by rfl⟩ : syracuseStep 423079 = 634619) B634619
theorem B2143421 : Blo 421773 2143421 := bstep (se 3 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 2143421 = 803783) B803783
theorem B955583 : Blo 421773 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B955655 : Blo 421773 955655 := bstep (se 1 (by rfl) ⟨716741, by rfl⟩ : syracuseStep 955655 = 1433483) B1433483
theorem B636281 : Blo 421773 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B636287 : Blo 421773 636287 := bstep (se 1 (by rfl) ⟨477215, by rfl⟩ : syracuseStep 636287 = 954431) B954431
theorem B1357231 : Blo 421773 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B2405861 : Blo 421773 2405861 := bstep (se 4 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 2405861 = 451099) B451099
theorem B636443 : Blo 421773 636443 := bstep (se 1 (by rfl) ⟨477332, by rfl⟩ : syracuseStep 636443 = 954665) B954665
theorem B423527 : Blo 421773 423527 := bstep (se 1 (by rfl) ⟨317645, by rfl⟩ : syracuseStep 423527 = 635291) B635291
theorem B1431215 : Blo 421773 1431215 := bstep (se 1 (by rfl) ⟨1073411, by rfl⟩ : syracuseStep 1431215 = 2146823) B2146823
theorem B2283191 : Blo 421773 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B8689355 : Blo 421773 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B636623 : Blo 421773 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B423807 : Blo 421773 423807 := bstep (se 1 (by rfl) ⟨317855, by rfl⟩ : syracuseStep 423807 = 635711) B635711
theorem B7346065 : Blo 421773 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B636827 : Blo 421773 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B636863 : Blo 421773 636863 := bstep (se 1 (by rfl) ⟨477647, by rfl⟩ : syracuseStep 636863 = 955295) B955295
theorem B423903 : Blo 421773 423903 := bstep (se 1 (by rfl) ⟨317927, by rfl⟩ : syracuseStep 423903 = 635855) B635855
theorem B423931 : Blo 421773 423931 := bstep (se 1 (by rfl) ⟨317948, by rfl⟩ : syracuseStep 423931 = 635897) B635897
theorem B423963 : Blo 421773 423963 := bstep (se 1 (by rfl) ⟨317972, by rfl⟩ : syracuseStep 423963 = 635945) B635945
theorem B423983 : Blo 421773 423983 := bstep (se 1 (by rfl) ⟨317987, by rfl⟩ : syracuseStep 423983 = 635975) B635975
theorem B637031 : Blo 421773 637031 := bstep (se 1 (by rfl) ⟨477773, by rfl⟩ : syracuseStep 637031 = 955547) B955547
theorem B16447607 : Blo 421773 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B1603739 : Blo 421773 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B424103 : Blo 421773 424103 := bstep (se 1 (by rfl) ⟨318077, by rfl⟩ : syracuseStep 424103 = 636155) B636155
theorem B2406611 : Blo 421773 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B1931627 : Blo 421773 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B2406793 : Blo 421773 2406793 := bstep (se 2 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 2406793 = 1805095) B1805095
theorem B10598951 : Blo 421773 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B760423 : Blo 421773 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B645791 : Blo 421773 645791 := bstep (se 1 (by rfl) ⟨484343, by rfl⟩ : syracuseStep 645791 = 968687) B968687
theorem B2325217 : Blo 421773 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B1202941 : Blo 421773 1202941 := bstep (se 3 (by rfl) ⟨225551, by rfl⟩ : syracuseStep 1202941 = 451103) B451103
theorem B29637413 : Blo 421773 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B949103 : Blo 421773 949103 := bstep (se 1 (by rfl) ⟨711827, by rfl⟩ : syracuseStep 949103 = 1423655) B1423655
theorem B1203113 : Blo 421773 1203113 := bstep (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) B902335
theorem B801839 : Blo 421773 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B711787 : Blo 421773 711787 := bstep (se 1 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 711787 = 1067681) B1067681
theorem B4136107 : Blo 421773 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B10878137 : Blo 421773 10878137 := bstep (se 2 (by rfl) ⟨4079301, by rfl⟩ : syracuseStep 10878137 = 8158603) B8158603
theorem B2415815 : Blo 421773 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B1203443 : Blo 421773 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B712057 : Blo 421773 712057 := bstep (se 2 (by rfl) ⟨267021, by rfl⟩ : syracuseStep 712057 = 534043) B534043
theorem B2350457 : Blo 421773 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B1072511 : Blo 421773 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B949751 : Blo 421773 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B1072703 : Blo 421773 1072703 := bstep (se 1 (by rfl) ⟨804527, by rfl⟩ : syracuseStep 1072703 = 1609055) B1609055
theorem B1802209 : Blo 421773 1802209 := bstep (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) B1351657
theorem B1433591 : Blo 421773 1433591 := bstep (se 1 (by rfl) ⟨1075193, by rfl⟩ : syracuseStep 1433591 = 2150387) B2150387
theorem B2138237 : Blo 421773 2138237 := bstep (se 3 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 2138237 = 801839) B801839
theorem B3661949 : Blo 421773 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B2506943 : Blo 421773 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B713083 : Blo 421773 713083 := bstep (se 1 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 713083 = 1069625) B1069625
theorem B2040191 : Blo 421773 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B12206537 : Blo 421773 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B1425977 : Blo 421773 1425977 := bstep (se 2 (by rfl) ⟨534741, by rfl⟩ : syracuseStep 1425977 = 1069483) B1069483
theorem B1426031 : Blo 421773 1426031 := bstep (se 1 (by rfl) ⟨1069523, by rfl⟩ : syracuseStep 1426031 = 2139047) B2139047
theorem B2417273 : Blo 421773 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B1073807 : Blo 421773 1073807 := bstep (se 1 (by rfl) ⟨805355, by rfl⟩ : syracuseStep 1073807 = 1610711) B1610711
theorem B803495 : Blo 421773 803495 := bstep (se 1 (by rfl) ⟨602621, by rfl⟩ : syracuseStep 803495 = 1205243) B1205243
theorem B475879 : Blo 421773 475879 := bstep (se 1 (by rfl) ⟨356909, by rfl⟩ : syracuseStep 475879 = 713819) B713819
theorem B951047 : Blo 421773 951047 := bstep (se 1 (by rfl) ⟨713285, by rfl⟩ : syracuseStep 951047 = 1426571) B1426571
theorem B5792903 : Blo 421773 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B3515557 : Blo 421773 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B4564133 : Blo 421773 4564133 := bstep (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) B855775
theorem B3048637 : Blo 421773 3048637 := bstep (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) B1143239
theorem B3868073 : Blo 421773 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B951785 : Blo 421773 951785 := bstep (se 2 (by rfl) ⟨356919, by rfl⟩ : syracuseStep 951785 = 713839) B713839
theorem B5514809 : Blo 421773 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B1287751 : Blo 421773 1287751 := bstep (se 1 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 1287751 = 1931627) B1931627
theorem B902839 : Blo 421773 902839 := bstep (se 1 (by rfl) ⟨677129, by rfl⟩ : syracuseStep 902839 = 1354259) B1354259
theorem B1722109 : Blo 421773 1722109 := bstep (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) B645791
theorem B2418457 : Blo 421773 2418457 := bstep (se 2 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 2418457 = 1813843) B1813843
theorem B952127 : Blo 421773 952127 := bstep (se 1 (by rfl) ⟨714095, by rfl⟩ : syracuseStep 952127 = 1428191) B1428191
theorem B632735 : Blo 421773 632735 := bstep (se 1 (by rfl) ⟨474551, by rfl⟩ : syracuseStep 632735 = 949103) B949103
theorem B7252091 : Blo 421773 7252091 := bstep (se 1 (by rfl) ⟨5439068, by rfl⟩ : syracuseStep 7252091 = 10878137) B10878137
theorem B1566971 : Blo 421773 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B715007 : Blo 421773 715007 := bstep (se 1 (by rfl) ⟨536255, by rfl⟩ : syracuseStep 715007 = 1072511) B1072511
theorem B633167 : Blo 421773 633167 := bstep (se 1 (by rfl) ⟨474875, by rfl⟩ : syracuseStep 633167 = 949751) B949751
theorem B2034001 : Blo 421773 2034001 := bstep (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) B1525501
theorem B715135 : Blo 421773 715135 := bstep (se 1 (by rfl) ⟨536351, by rfl⟩ : syracuseStep 715135 = 1072703) B1072703
theorem B2402945 : Blo 421773 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B29420243 : Blo 421773 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1395443 : Blo 421773 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B633599 : Blo 421773 633599 := bstep (se 1 (by rfl) ⟨475199, by rfl⟩ : syracuseStep 633599 = 950399) B950399
theorem B1813691 : Blo 421773 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B1428947 : Blo 421773 1428947 := bstep (se 1 (by rfl) ⟨1071710, by rfl⟩ : syracuseStep 1428947 = 2143421) B2143421
theorem B2141801 : Blo 421773 2141801 := bstep (se 2 (by rfl) ⟨803175, by rfl⟩ : syracuseStep 2141801 = 1606351) B1606351
theorem B3100289 : Blo 421773 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B954143 : Blo 421773 954143 := bstep (se 1 (by rfl) ⟨715607, by rfl⟩ : syracuseStep 954143 = 1431215) B1431215
theorem B1355591 : Blo 421773 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B1208135 : Blo 421773 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B634703 : Blo 421773 634703 := bstep (se 1 (by rfl) ⟨476027, by rfl⟩ : syracuseStep 634703 = 952055) B952055
theorem B634823 : Blo 421773 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B1601491 : Blo 421773 1601491 := bstep (se 1 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 1601491 = 2402237) B2402237
theorem B10965071 : Blo 421773 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B1069159 : Blo 421773 1069159 := bstep (se 1 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 1069159 = 1603739) B1603739
theorem B422143 : Blo 421773 422143 := bstep (se 1 (by rfl) ⟨316607, by rfl⟩ : syracuseStep 422143 = 633215) B633215
theorem B635183 : Blo 421773 635183 := bstep (se 1 (by rfl) ⟨476387, by rfl⟩ : syracuseStep 635183 = 952775) B952775
theorem B7065967 : Blo 421773 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B422303 : Blo 421773 422303 := bstep (se 1 (by rfl) ⟨316727, by rfl⟩ : syracuseStep 422303 = 633455) B633455
theorem B1143229 : Blo 421773 1143229 := bstep (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) B428711
theorem B635423 : Blo 421773 635423 := bstep (se 1 (by rfl) ⟨476567, by rfl⟩ : syracuseStep 635423 = 953135) B953135
theorem B422447 : Blo 421773 422447 := bstep (se 1 (by rfl) ⟨316835, by rfl⟩ : syracuseStep 422447 = 633671) B633671
theorem B1610543 : Blo 421773 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B635771 : Blo 421773 635771 := bstep (se 1 (by rfl) ⟨476828, by rfl⟩ : syracuseStep 635771 = 953657) B953657
theorem B6091685 : Blo 421773 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B422847 : Blo 421773 422847 := bstep (se 1 (by rfl) ⟨317135, by rfl⟩ : syracuseStep 422847 = 634271) B634271
theorem B635951 : Blo 421773 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B423023 : Blo 421773 423023 := bstep (se 1 (by rfl) ⟨317267, by rfl⟩ : syracuseStep 423023 = 634535) B634535
theorem B423039 : Blo 421773 423039 := bstep (se 1 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 423039 = 634559) B634559
theorem B636071 : Blo 421773 636071 := bstep (se 1 (by rfl) ⟨477053, by rfl⟩ : syracuseStep 636071 = 954107) B954107
theorem B423103 : Blo 421773 423103 := bstep (se 1 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 423103 = 634655) B634655
theorem B9794753 : Blo 421773 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B636215 : Blo 421773 636215 := bstep (se 1 (by rfl) ⟨477161, by rfl⟩ : syracuseStep 636215 = 954323) B954323
theorem B955727 : Blo 421773 955727 := bstep (se 1 (by rfl) ⟨716795, by rfl⟩ : syracuseStep 955727 = 1433591) B1433591
theorem B423295 : Blo 421773 423295 := bstep (se 1 (by rfl) ⟨317471, by rfl⟩ : syracuseStep 423295 = 634943) B634943
theorem B2708873 : Blo 421773 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B636395 : Blo 421773 636395 := bstep (se 1 (by rfl) ⟨477296, by rfl⟩ : syracuseStep 636395 = 954593) B954593
theorem B423423 : Blo 421773 423423 := bstep (se 1 (by rfl) ⟨317567, by rfl⟩ : syracuseStep 423423 = 635135) B635135
theorem B423451 : Blo 421773 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B636521 : Blo 421773 636521 := bstep (se 2 (by rfl) ⟨238695, by rfl⟩ : syracuseStep 636521 = 477391) B477391
theorem B1414831 : Blo 421773 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B423631 : Blo 421773 423631 := bstep (se 1 (by rfl) ⟨317723, by rfl⟩ : syracuseStep 423631 = 635447) B635447
theorem B6084355 : Blo 421773 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B636743 : Blo 421773 636743 := bstep (se 1 (by rfl) ⟨477557, by rfl⟩ : syracuseStep 636743 = 955115) B955115
theorem B3209057 : Blo 421773 3209057 := bstep (se 2 (by rfl) ⟨1203396, by rfl⟩ : syracuseStep 3209057 = 2406793) B2406793
theorem B423791 : Blo 421773 423791 := bstep (se 1 (by rfl) ⟨317843, by rfl⟩ : syracuseStep 423791 = 635687) B635687
theorem B423871 : Blo 421773 423871 := bstep (se 1 (by rfl) ⟨317903, by rfl⟩ : syracuseStep 423871 = 635807) B635807
theorem B2144231 : Blo 421773 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B636923 : Blo 421773 636923 := bstep (se 1 (by rfl) ⟨477692, by rfl⟩ : syracuseStep 636923 = 955385) B955385
theorem B636983 : Blo 421773 636983 := bstep (se 1 (by rfl) ⟨477737, by rfl⟩ : syracuseStep 636983 = 955475) B955475
theorem B637049 : Blo 421773 637049 := bstep (se 2 (by rfl) ⟨238893, by rfl⟩ : syracuseStep 637049 = 477787) B477787
theorem B1603709 : Blo 421773 1603709 := bstep (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) B601391
theorem B1202303 : Blo 421773 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B637055 : Blo 421773 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B1013897 : Blo 421773 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B2144393 : Blo 421773 2144393 := bstep (se 2 (by rfl) ⟨804147, by rfl⟩ : syracuseStep 2144393 = 1608295) B1608295
theorem B637103 : Blo 421773 637103 := bstep (se 1 (by rfl) ⟨477827, by rfl⟩ : syracuseStep 637103 = 955655) B955655
theorem B424187 : Blo 421773 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B424191 : Blo 421773 424191 := bstep (se 1 (by rfl) ⟨318143, by rfl⟩ : syracuseStep 424191 = 636287) B636287
theorem B1603907 : Blo 421773 1603907 := bstep (se 1 (by rfl) ⟨1202930, by rfl⟩ : syracuseStep 1603907 = 2405861) B2405861
theorem B1603921 : Blo 421773 1603921 := bstep (se 2 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 1603921 = 1202941) B1202941
theorem B4577633 : Blo 421773 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B424295 : Blo 421773 424295 := bstep (se 1 (by rfl) ⟨318221, by rfl⟩ : syracuseStep 424295 = 636443) B636443
theorem B2316671 : Blo 421773 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B46815671 : Blo 421773 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B1522127 : Blo 421773 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B424415 : Blo 421773 424415 := bstep (se 1 (by rfl) ⟨318311, by rfl⟩ : syracuseStep 424415 = 636623) B636623
theorem B424551 : Blo 421773 424551 := bstep (se 1 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 424551 = 636827) B636827
theorem B424575 : Blo 421773 424575 := bstep (se 1 (by rfl) ⟨318431, by rfl⟩ : syracuseStep 424575 = 636863) B636863
theorem B6118031 : Blo 421773 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B424687 : Blo 421773 424687 := bstep (se 1 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 424687 = 637031) B637031
theorem B1604407 : Blo 421773 1604407 := bstep (se 1 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 1604407 = 2406611) B2406611
theorem B949049 : Blo 421773 949049 := bstep (se 2 (by rfl) ⟨355893, by rfl⟩ : syracuseStep 949049 = 711787) B711787
theorem B12352501 : Blo 421773 12352501 := bstep (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) B1158047
theorem B6085691 : Blo 421773 6085691 := bstep (se 1 (by rfl) ⟨4564268, by rfl⟩ : syracuseStep 6085691 = 9128537) B9128537
theorem B949409 : Blo 421773 949409 := bstep (se 2 (by rfl) ⟨356028, by rfl⟩ : syracuseStep 949409 = 712057) B712057
theorem B8019121 : Blo 421773 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B19758275 : Blo 421773 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1809641 : Blo 421773 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B802075 : Blo 421773 802075 := bstep (se 1 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 802075 = 1203113) B1203113
theorem B9772487 : Blo 421773 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B802295 : Blo 421773 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B1424897 : Blo 421773 1424897 := bstep (se 2 (by rfl) ⟨534336, by rfl⟩ : syracuseStep 1424897 = 1068673) B1068673
theorem B712415 : Blo 421773 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B18341639 : Blo 421773 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B100228913 : Blo 421773 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B2891693 : Blo 421773 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B1425491 : Blo 421773 1425491 := bstep (se 1 (by rfl) ⟨1069118, by rfl⟩ : syracuseStep 1425491 = 2138237) B2138237
theorem B1425545 : Blo 421773 1425545 := bstep (se 2 (by rfl) ⟨534579, by rfl⟩ : syracuseStep 1425545 = 1069159) B1069159
theorem B1360127 : Blo 421773 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B9765197 : Blo 421773 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B2703725 : Blo 421773 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B950651 : Blo 421773 950651 := bstep (se 1 (by rfl) ⟨712988, by rfl⟩ : syracuseStep 950651 = 1425977) B1425977
theorem B950687 : Blo 421773 950687 := bstep (se 1 (by rfl) ⟨713015, by rfl⟩ : syracuseStep 950687 = 1426031) B1426031
theorem B2138561 : Blo 421773 2138561 := bstep (se 2 (by rfl) ⟨801960, by rfl⟩ : syracuseStep 2138561 = 1603921) B1603921
theorem B2712001 : Blo 421773 2712001 := bstep (se 2 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 2712001 = 2034001) B2034001
theorem B9421289 : Blo 421773 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B950777 : Blo 421773 950777 := bstep (se 2 (by rfl) ⟨356541, by rfl⟩ : syracuseStep 950777 = 713083) B713083
theorem B6685181 : Blo 421773 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B1073695 : Blo 421773 1073695 := bstep (se 1 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 1073695 = 1610543) B1610543
theorem B1524305 : Blo 421773 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B6529835 : Blo 421773 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B2139209 : Blo 421773 2139209 := bstep (se 2 (by rfl) ⟨802203, by rfl⟩ : syracuseStep 2139209 = 1604407) B1604407
theorem B2139371 : Blo 421773 2139371 := bstep (se 1 (by rfl) ⟨1604528, by rfl⟩ : syracuseStep 2139371 = 3209057) B3209057
theorem B4834727 : Blo 421773 4834727 := bstep (se 1 (by rfl) ⟨3626045, by rfl⟩ : syracuseStep 4834727 = 7252091) B7252091
theorem B476671 : Blo 421773 476671 := bstep (se 1 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 476671 = 715007) B715007
theorem B4687409 : Blo 421773 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B10692161 : Blo 421773 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B4064849 : Blo 421773 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B8267437 : Blo 421773 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B19613495 : Blo 421773 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B632699 : Blo 421773 632699 := bstep (se 1 (by rfl) ⟨474524, by rfl⟩ : syracuseStep 632699 = 949049) B949049
theorem B4057127 : Blo 421773 4057127 := bstep (se 1 (by rfl) ⟨3042845, by rfl⟩ : syracuseStep 4057127 = 6085691) B6085691
theorem B632939 : Blo 421773 632939 := bstep (se 1 (by rfl) ⟨474704, by rfl⟩ : syracuseStep 632939 = 949409) B949409
theorem B1206427 : Blo 421773 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B3221693 : Blo 421773 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B1886441 : Blo 421773 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B6514991 : Blo 421773 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B952631 : Blo 421773 952631 := bstep (se 1 (by rfl) ⟨714473, by rfl⟩ : syracuseStep 952631 = 1428947) B1428947
theorem B534863 : Blo 421773 534863 := bstep (se 1 (by rfl) ⟨401147, by rfl⟩ : syracuseStep 534863 = 802295) B802295
theorem B2296145 : Blo 421773 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B8112473 : Blo 421773 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B1427867 : Blo 421773 1427867 := bstep (se 1 (by rfl) ⟨1070900, by rfl⟩ : syracuseStep 1427867 = 2141801) B2141801
theorem B903727 : Blo 421773 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B1927795 : Blo 421773 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B7310047 : Blo 421773 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B8137691 : Blo 421773 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B3206141 : Blo 421773 3206141 := bstep (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) B1202303
theorem B715871 : Blo 421773 715871 := bstep (se 1 (by rfl) ⟨536903, by rfl⟩ : syracuseStep 715871 = 1073807) B1073807
theorem B535663 : Blo 421773 535663 := bstep (se 1 (by rfl) ⟨401747, by rfl⟩ : syracuseStep 535663 = 803495) B803495
theorem B953513 : Blo 421773 953513 := bstep (se 2 (by rfl) ⟨357567, by rfl⟩ : syracuseStep 953513 = 715135) B715135
theorem B634031 : Blo 421773 634031 := bstep (se 1 (by rfl) ⟨475523, by rfl⟩ : syracuseStep 634031 = 951047) B951047
theorem B3861935 : Blo 421773 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B3042755 : Blo 421773 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B1805915 : Blo 421773 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B634505 : Blo 421773 634505 := bstep (se 2 (by rfl) ⟨237939, by rfl⟩ : syracuseStep 634505 = 475879) B475879
theorem B634523 : Blo 421773 634523 := bstep (se 1 (by rfl) ⟨475892, by rfl⟩ : syracuseStep 634523 = 951785) B951785
theorem B634751 : Blo 421773 634751 := bstep (se 1 (by rfl) ⟨476063, by rfl⟩ : syracuseStep 634751 = 952127) B952127
theorem B421823 : Blo 421773 421823 := bstep (se 1 (by rfl) ⟨316367, by rfl⟩ : syracuseStep 421823 = 632735) B632735
theorem B16470001 : Blo 421773 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B1429487 : Blo 421773 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B1069139 : Blo 421773 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B1429595 : Blo 421773 1429595 := bstep (se 1 (by rfl) ⟨1072196, by rfl⟩ : syracuseStep 1429595 = 2144393) B2144393
theorem B1044647 : Blo 421773 1044647 := bstep (se 1 (by rfl) ⟨783485, by rfl⟩ : syracuseStep 1044647 = 1566971) B1566971
theorem B1069271 : Blo 421773 1069271 := bstep (se 1 (by rfl) ⟨801953, by rfl⟩ : syracuseStep 1069271 = 1603907) B1603907
theorem B422111 : Blo 421773 422111 := bstep (se 1 (by rfl) ⟨316583, by rfl⟩ : syracuseStep 422111 = 633167) B633167
theorem B3051755 : Blo 421773 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B1544447 : Blo 421773 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1069433 : Blo 421773 1069433 := bstep (se 2 (by rfl) ⟨401037, by rfl⟩ : syracuseStep 1069433 = 802075) B802075
theorem B1601963 : Blo 421773 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B930295 : Blo 421773 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B422399 : Blo 421773 422399 := bstep (se 1 (by rfl) ⟨316799, by rfl⟩ : syracuseStep 422399 = 633599) B633599
theorem B1717001 : Blo 421773 1717001 := bstep (se 2 (by rfl) ⟨643875, by rfl⟩ : syracuseStep 1717001 = 1287751) B1287751
theorem B1209127 : Blo 421773 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B3224609 : Blo 421773 3224609 := bstep (se 2 (by rfl) ⟨1209228, by rfl⟩ : syracuseStep 3224609 = 2418457) B2418457
theorem B12227759 : Blo 421773 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B636095 : Blo 421773 636095 := bstep (se 1 (by rfl) ⟨477071, by rfl⟩ : syracuseStep 636095 = 954143) B954143
theorem B66819275 : Blo 421773 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B423135 : Blo 421773 423135 := bstep (se 1 (by rfl) ⟨317351, by rfl⟩ : syracuseStep 423135 = 634703) B634703
theorem B2135321 : Blo 421773 2135321 := bstep (se 2 (by rfl) ⟨800745, by rfl⟩ : syracuseStep 2135321 = 1601491) B1601491
theorem B423215 : Blo 421773 423215 := bstep (se 1 (by rfl) ⟨317411, by rfl⟩ : syracuseStep 423215 = 634823) B634823
theorem B423455 : Blo 421773 423455 := bstep (se 1 (by rfl) ⟨317591, by rfl⟩ : syracuseStep 423455 = 635183) B635183
theorem B423615 : Blo 421773 423615 := bstep (se 1 (by rfl) ⟨317711, by rfl⟩ : syracuseStep 423615 = 635423) B635423
theorem B1611515 : Blo 421773 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B423847 : Blo 421773 423847 := bstep (se 1 (by rfl) ⟨317885, by rfl⟩ : syracuseStep 423847 = 635771) B635771
theorem B58824629 : Blo 421773 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B4061123 : Blo 421773 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B423967 : Blo 421773 423967 := bstep (se 1 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 423967 = 635951) B635951
theorem B424047 : Blo 421773 424047 := bstep (se 1 (by rfl) ⟨318035, by rfl⟩ : syracuseStep 424047 = 636071) B636071
theorem B424143 : Blo 421773 424143 := bstep (se 1 (by rfl) ⟨318107, by rfl⟩ : syracuseStep 424143 = 636215) B636215
theorem B637151 : Blo 421773 637151 := bstep (se 1 (by rfl) ⟨477863, by rfl⟩ : syracuseStep 637151 = 955727) B955727
theorem B2578715 : Blo 421773 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B424263 : Blo 421773 424263 := bstep (se 1 (by rfl) ⟨318197, by rfl⟩ : syracuseStep 424263 = 636395) B636395
theorem B424347 : Blo 421773 424347 := bstep (se 1 (by rfl) ⟨318260, by rfl⟩ : syracuseStep 424347 = 636521) B636521
theorem B424495 : Blo 421773 424495 := bstep (se 1 (by rfl) ⟨318371, by rfl⟩ : syracuseStep 424495 = 636743) B636743
theorem B424615 : Blo 421773 424615 := bstep (se 1 (by rfl) ⟨318461, by rfl⟩ : syracuseStep 424615 = 636923) B636923
theorem B424655 : Blo 421773 424655 := bstep (se 1 (by rfl) ⟨318491, by rfl⟩ : syracuseStep 424655 = 636983) B636983
theorem B424699 : Blo 421773 424699 := bstep (se 1 (by rfl) ⟨318524, by rfl⟩ : syracuseStep 424699 = 637049) B637049
theorem B424703 : Blo 421773 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B424735 : Blo 421773 424735 := bstep (se 1 (by rfl) ⟨318551, by rfl⟩ : syracuseStep 424735 = 637103) B637103
theorem B31210447 : Blo 421773 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B1014751 : Blo 421773 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B4078687 : Blo 421773 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B13172183 : Blo 421773 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1203785 : Blo 421773 1203785 := bstep (se 2 (by rfl) ⟨451419, by rfl⟩ : syracuseStep 1203785 = 902839) B902839
theorem B949931 : Blo 421773 949931 := bstep (se 1 (by rfl) ⟨712448, by rfl⟩ : syracuseStep 949931 = 1424897) B1424897
theorem B474943 : Blo 421773 474943 := bstep (se 1 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 474943 = 712415) B712415
theorem B950327 : Blo 421773 950327 := bstep (se 1 (by rfl) ⟨712745, by rfl⟩ : syracuseStep 950327 = 1425491) B1425491
theorem B712759 : Blo 421773 712759 := bstep (se 1 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 712759 = 1069139) B1069139
theorem B950363 : Blo 421773 950363 := bstep (se 1 (by rfl) ⟨712772, by rfl⟩ : syracuseStep 950363 = 1425545) B1425545
theorem B696431 : Blo 421773 696431 := bstep (se 1 (by rfl) ⟨522323, by rfl⟩ : syracuseStep 696431 = 1044647) B1044647
theorem B712847 : Blo 421773 712847 := bstep (se 1 (by rfl) ⟨534635, by rfl⟩ : syracuseStep 712847 = 1069271) B1069271
theorem B1802483 : Blo 421773 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B712955 : Blo 421773 712955 := bstep (se 1 (by rfl) ⟨534716, by rfl⟩ : syracuseStep 712955 = 1069433) B1069433
theorem B1425707 : Blo 421773 1425707 := bstep (se 1 (by rfl) ⟨1069280, by rfl⟩ : syracuseStep 1425707 = 2138561) B2138561
theorem B4456787 : Blo 421773 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B1426139 : Blo 421773 1426139 := bstep (se 1 (by rfl) ⟨1069604, by rfl⟩ : syracuseStep 1426139 = 2139209) B2139209
theorem B1204969 : Blo 421773 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B8151839 : Blo 421773 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B1426247 : Blo 421773 1426247 := bstep (se 1 (by rfl) ⟨1069685, by rfl⟩ : syracuseStep 1426247 = 2139371) B2139371
theorem B1426301 : Blo 421773 1426301 := bstep (se 3 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 1426301 = 534863) B534863
theorem B7128107 : Blo 421773 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B1074343 : Blo 421773 1074343 := bstep (se 1 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 1074343 = 1611515) B1611515
theorem B13075663 : Blo 421773 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B39216419 : Blo 421773 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B2704751 : Blo 421773 2704751 := bstep (se 1 (by rfl) ⟨2028563, by rfl⟩ : syracuseStep 2704751 = 4057127) B4057127
theorem B2147795 : Blo 421773 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B714217 : Blo 421773 714217 := bstep (se 2 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 714217 = 535663) B535663
theorem B4343327 : Blo 421773 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B4064813 : Blo 421773 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B5408315 : Blo 421773 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B951911 : Blo 421773 951911 := bstep (se 1 (by rfl) ⟨713933, by rfl⟩ : syracuseStep 951911 = 1427867) B1427867
theorem B5425127 : Blo 421773 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B477247 : Blo 421773 477247 := bstep (se 1 (by rfl) ⟨357935, by rfl⟩ : syracuseStep 477247 = 715871) B715871
theorem B2574623 : Blo 421773 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B633257 : Blo 421773 633257 := bstep (se 2 (by rfl) ⟨237471, by rfl⟩ : syracuseStep 633257 = 474943) B474943
theorem B20122037 : Blo 421773 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B633287 : Blo 421773 633287 := bstep (se 1 (by rfl) ⟨474965, by rfl⟩ : syracuseStep 633287 = 949931) B949931
theorem B952991 : Blo 421773 952991 := bstep (se 1 (by rfl) ⟨714743, by rfl⟩ : syracuseStep 952991 = 1429487) B1429487
theorem B953063 : Blo 421773 953063 := bstep (se 1 (by rfl) ⟨714797, by rfl⟩ : syracuseStep 953063 = 1429595) B1429595
theorem B2034503 : Blo 421773 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B1608569 : Blo 421773 1608569 := bstep (se 2 (by rfl) ⟨603213, by rfl⟩ : syracuseStep 1608569 = 1206427) B1206427
theorem B633767 : Blo 421773 633767 := bstep (se 1 (by rfl) ⟨475325, by rfl⟩ : syracuseStep 633767 = 950651) B950651
theorem B633791 : Blo 421773 633791 := bstep (se 1 (by rfl) ⟨475343, by rfl⟩ : syracuseStep 633791 = 950687) B950687
theorem B1067975 : Blo 421773 1067975 := bstep (se 1 (by rfl) ⟨800981, by rfl⟩ : syracuseStep 1067975 = 1601963) B1601963
theorem B633851 : Blo 421773 633851 := bstep (se 1 (by rfl) ⟨475388, by rfl⟩ : syracuseStep 633851 = 950777) B950777
theorem B3616001 : Blo 421773 3616001 := bstep (se 2 (by rfl) ⟨1356000, by rfl⟩ : syracuseStep 3616001 = 2712001) B2712001
theorem B2149739 : Blo 421773 2149739 := bstep (se 1 (by rfl) ⟨1612304, by rfl⟩ : syracuseStep 2149739 = 3224609) B3224609
theorem B6123053 : Blo 421773 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B44092997 : Blo 421773 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B3223151 : Blo 421773 3223151 := bstep (se 1 (by rfl) ⟨2417363, by rfl⟩ : syracuseStep 3223151 = 4834727) B4834727
theorem B3124939 : Blo 421773 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B421799 : Blo 421773 421799 := bstep (se 1 (by rfl) ⟨316349, by rfl⟩ : syracuseStep 421799 = 632699) B632699
theorem B2707415 : Blo 421773 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B421959 : Blo 421773 421959 := bstep (se 1 (by rfl) ⟨316469, by rfl⟩ : syracuseStep 421959 = 632939) B632939
theorem B635087 : Blo 421773 635087 := bstep (se 1 (by rfl) ⟨476315, by rfl⟩ : syracuseStep 635087 = 952631) B952631
theorem B635561 : Blo 421773 635561 := bstep (se 2 (by rfl) ⟨238335, by rfl⟩ : syracuseStep 635561 = 476671) B476671
theorem B635675 : Blo 421773 635675 := bstep (se 1 (by rfl) ⟨476756, by rfl⟩ : syracuseStep 635675 = 953513) B953513
theorem B422687 : Blo 421773 422687 := bstep (se 1 (by rfl) ⟨317015, by rfl⟩ : syracuseStep 422687 = 634031) B634031
theorem B17412893 : Blo 421773 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B2028503 : Blo 421773 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B423003 : Blo 421773 423003 := bstep (se 1 (by rfl) ⟨317252, by rfl⟩ : syracuseStep 423003 = 634505) B634505
theorem B423015 : Blo 421773 423015 := bstep (se 1 (by rfl) ⟨317261, by rfl⟩ : syracuseStep 423015 = 634523) B634523
theorem B5412005 : Blo 421773 5412005 := bstep (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) B1014751
theorem B423167 : Blo 421773 423167 := bstep (se 1 (by rfl) ⟨317375, by rfl⟩ : syracuseStep 423167 = 634751) B634751
theorem B4961573 : Blo 421773 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B21960001 : Blo 421773 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B1029631 : Blo 421773 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B906751 : Blo 421773 906751 := bstep (se 1 (by rfl) ⟨680063, by rfl⟩ : syracuseStep 906751 = 1360127) B1360127
theorem B6510131 : Blo 421773 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B6280859 : Blo 421773 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B1144667 : Blo 421773 1144667 := bstep (se 1 (by rfl) ⟨858500, by rfl⟩ : syracuseStep 1144667 = 1717001) B1717001
theorem B1431593 : Blo 421773 1431593 := bstep (se 2 (by rfl) ⟨536847, by rfl⟩ : syracuseStep 1431593 = 1073695) B1073695
theorem B424063 : Blo 421773 424063 := bstep (se 1 (by rfl) ⟨318047, by rfl⟩ : syracuseStep 424063 = 636095) B636095
theorem B44546183 : Blo 421773 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2570393 : Blo 421773 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B1423547 : Blo 421773 1423547 := bstep (se 1 (by rfl) ⟨1067660, by rfl⟩ : syracuseStep 1423547 = 2135321) B2135321
theorem B9746729 : Blo 421773 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B1612169 : Blo 421773 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B2709899 : Blo 421773 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B41613929 : Blo 421773 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B5438249 : Blo 421773 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B424767 : Blo 421773 424767 := bstep (se 1 (by rfl) ⟨318575, by rfl⟩ : syracuseStep 424767 = 637151) B637151
theorem B1719143 : Blo 421773 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B4815773 : Blo 421773 4815773 := bstep (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) B1805915
theorem B2137427 : Blo 421773 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B8781455 : Blo 421773 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B802523 : Blo 421773 802523 := bstep (se 1 (by rfl) ⟨601892, by rfl⟩ : syracuseStep 802523 = 1203785) B1203785
theorem B950345 : Blo 421773 950345 := bstep (se 2 (by rfl) ⟨356379, by rfl⟩ : syracuseStep 950345 = 712759) B712759
theorem B475231 : Blo 421773 475231 := bstep (se 1 (by rfl) ⟨356423, by rfl⟩ : syracuseStep 475231 = 712847) B712847
theorem B475303 : Blo 421773 475303 := bstep (se 1 (by rfl) ⟨356477, by rfl⟩ : syracuseStep 475303 = 712955) B712955
theorem B950471 : Blo 421773 950471 := bstep (se 1 (by rfl) ⟨712853, by rfl⟩ : syracuseStep 950471 = 1425707) B1425707
theorem B950759 : Blo 421773 950759 := bstep (se 1 (by rfl) ⟨713069, by rfl⟩ : syracuseStep 950759 = 1426139) B1426139
theorem B11608595 : Blo 421773 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B950831 : Blo 421773 950831 := bstep (se 1 (by rfl) ⟨713123, by rfl⟩ : syracuseStep 950831 = 1426247) B1426247
theorem B950867 : Blo 421773 950867 := bstep (se 1 (by rfl) ⟨713150, by rfl⟩ : syracuseStep 950867 = 1426301) B1426301
theorem B4752071 : Blo 421773 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B6865661 : Blo 421773 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B47539061 : Blo 421773 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B1803167 : Blo 421773 1803167 := bstep (se 1 (by rfl) ⟨1352375, by rfl⟩ : syracuseStep 1803167 = 2704751) B2704751
theorem B1606625 : Blo 421773 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B3605543 : Blo 421773 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B763111 : Blo 421773 763111 := bstep (se 1 (by rfl) ⟨572333, by rfl⟩ : syracuseStep 763111 = 1144667) B1144667
theorem B29697455 : Blo 421773 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B1713595 : Blo 421773 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B6497819 : Blo 421773 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B1074779 : Blo 421773 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B17434217 : Blo 421773 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B29280001 : Blo 421773 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B952289 : Blo 421773 952289 := bstep (se 2 (by rfl) ⟨357108, by rfl⟩ : syracuseStep 952289 = 714217) B714217
theorem B2410667 : Blo 421773 2410667 := bstep (se 1 (by rfl) ⟨1808000, by rfl⟩ : syracuseStep 2410667 = 3616001) B3616001
theorem B4082035 : Blo 421773 4082035 := bstep (se 1 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 4082035 = 6123053) B6123053
theorem B29395331 : Blo 421773 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B2148767 : Blo 421773 2148767 := bstep (se 1 (by rfl) ⟨1611575, by rfl⟩ : syracuseStep 2148767 = 3223151) B3223151
theorem B535015 : Blo 421773 535015 := bstep (se 1 (by rfl) ⟨401261, by rfl⟩ : syracuseStep 535015 = 802523) B802523
theorem B5409341 : Blo 421773 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B1804943 : Blo 421773 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B633551 : Blo 421773 633551 := bstep (se 1 (by rfl) ⟨475163, by rfl⟩ : syracuseStep 633551 = 950327) B950327
theorem B633575 : Blo 421773 633575 := bstep (se 1 (by rfl) ⟨475181, by rfl⟩ : syracuseStep 633575 = 950363) B950363
theorem B5434559 : Blo 421773 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B3608003 : Blo 421773 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B26144279 : Blo 421773 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B2895551 : Blo 421773 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B634607 : Blo 421773 634607 := bstep (se 1 (by rfl) ⟨475955, by rfl⟩ : syracuseStep 634607 = 951911) B951911
theorem B3616751 : Blo 421773 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B954395 : Blo 421773 954395 := bstep (se 1 (by rfl) ⟨715796, by rfl⟩ : syracuseStep 954395 = 1431593) B1431593
theorem B1806599 : Blo 421773 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B422171 : Blo 421773 422171 := bstep (se 1 (by rfl) ⟨316628, by rfl⟩ : syracuseStep 422171 = 633257) B633257
theorem B13414691 : Blo 421773 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B422191 : Blo 421773 422191 := bstep (se 1 (by rfl) ⟨316643, by rfl⟩ : syracuseStep 422191 = 633287) B633287
theorem B27742619 : Blo 421773 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B16748957 : Blo 421773 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B635327 : Blo 421773 635327 := bstep (se 1 (by rfl) ⟨476495, by rfl⟩ : syracuseStep 635327 = 952991) B952991
theorem B635375 : Blo 421773 635375 := bstep (se 1 (by rfl) ⟨476531, by rfl⟩ : syracuseStep 635375 = 953063) B953063
theorem B3625499 : Blo 421773 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B1356335 : Blo 421773 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B422511 : Blo 421773 422511 := bstep (se 1 (by rfl) ⟨316883, by rfl⟩ : syracuseStep 422511 = 633767) B633767
theorem B422527 : Blo 421773 422527 := bstep (se 1 (by rfl) ⟨316895, by rfl⟩ : syracuseStep 422527 = 633791) B633791
theorem B422567 : Blo 421773 422567 := bstep (se 1 (by rfl) ⟨316925, by rfl⟩ : syracuseStep 422567 = 633851) B633851
theorem B1372841 : Blo 421773 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B1209001 : Blo 421773 1209001 := bstep (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) B906751
theorem B4166585 : Blo 421773 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B5854303 : Blo 421773 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B464287 : Blo 421773 464287 := bstep (se 1 (by rfl) ⟨348215, by rfl⟩ : syracuseStep 464287 = 696431) B696431
theorem B636329 : Blo 421773 636329 := bstep (se 2 (by rfl) ⟨238623, by rfl⟩ : syracuseStep 636329 = 477247) B477247
theorem B423391 : Blo 421773 423391 := bstep (se 1 (by rfl) ⟨317543, by rfl⟩ : syracuseStep 423391 = 635087) B635087
theorem B1201655 : Blo 421773 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B423707 : Blo 421773 423707 := bstep (se 1 (by rfl) ⟨317780, by rfl⟩ : syracuseStep 423707 = 635561) B635561
theorem B423783 : Blo 421773 423783 := bstep (se 1 (by rfl) ⟨317837, by rfl⟩ : syracuseStep 423783 = 635675) B635675
theorem B3307715 : Blo 421773 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B1431863 : Blo 421773 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B2709875 : Blo 421773 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B4340087 : Blo 421773 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B949031 : Blo 421773 949031 := bstep (se 1 (by rfl) ⟨711773, by rfl⟩ : syracuseStep 949031 = 1423547) B1423547
theorem B1432457 : Blo 421773 1432457 := bstep (se 2 (by rfl) ⟨537171, by rfl⟩ : syracuseStep 1432457 = 1074343) B1074343
theorem B1146095 : Blo 421773 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B1072379 : Blo 421773 1072379 := bstep (se 1 (by rfl) ⟨804284, by rfl⟩ : syracuseStep 1072379 = 1608569) B1608569
theorem B3210515 : Blo 421773 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B711983 : Blo 421773 711983 := bstep (se 1 (by rfl) ⟨533987, by rfl⟩ : syracuseStep 711983 = 1067975) B1067975
theorem B1424951 : Blo 421773 1424951 := bstep (se 1 (by rfl) ⟨1068713, by rfl⟩ : syracuseStep 1424951 = 2137427) B2137427
theorem B1433159 : Blo 421773 1433159 := bstep (se 1 (by rfl) ⟨1074869, by rfl⟩ : syracuseStep 1433159 = 2149739) B2149739
theorem B1204399 : Blo 421773 1204399 := bstep (se 1 (by rfl) ⟨903299, by rfl⟩ : syracuseStep 1204399 = 1806599) B1806599
theorem B2416999 : Blo 421773 2416999 := bstep (se 1 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 2416999 = 3625499) B3625499
theorem B2777723 : Blo 421773 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B713353 : Blo 421773 713353 := bstep (se 2 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 713353 = 535015) B535015
theorem B44663885 : Blo 421773 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B79193213 : Blo 421773 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B1607111 : Blo 421773 1607111 := bstep (se 1 (by rfl) ⟨1205333, by rfl⟩ : syracuseStep 1607111 = 2410667) B2410667
theorem B2205143 : Blo 421773 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B2893391 : Blo 421773 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B19596887 : Blo 421773 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B46491245 : Blo 421773 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B3606227 : Blo 421773 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B632687 : Blo 421773 632687 := bstep (se 1 (by rfl) ⟨474515, by rfl⟩ : syracuseStep 632687 = 949031) B949031
theorem B3623039 : Blo 421773 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B764063 : Blo 421773 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B714919 : Blo 421773 714919 := bstep (se 1 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 714919 = 1072379) B1072379
theorem B2140343 : Blo 421773 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B2411167 : Blo 421773 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B633563 : Blo 421773 633563 := bstep (se 1 (by rfl) ⟨475172, by rfl⟩ : syracuseStep 633563 = 950345) B950345
theorem B633641 : Blo 421773 633641 := bstep (se 2 (by rfl) ⟨237615, by rfl⟩ : syracuseStep 633641 = 475231) B475231
theorem B633647 : Blo 421773 633647 := bstep (se 1 (by rfl) ⟨475235, by rfl⟩ : syracuseStep 633647 = 950471) B950471
theorem B633737 : Blo 421773 633737 := bstep (se 2 (by rfl) ⟨237651, by rfl⟩ : syracuseStep 633737 = 475303) B475303
theorem B633839 : Blo 421773 633839 := bstep (se 1 (by rfl) ⟨475379, by rfl⟩ : syracuseStep 633839 = 950759) B950759
theorem B633887 : Blo 421773 633887 := bstep (se 1 (by rfl) ⟨475415, by rfl⟩ : syracuseStep 633887 = 950831) B950831
theorem B904223 : Blo 421773 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B633911 : Blo 421773 633911 := bstep (se 1 (by rfl) ⟨475433, by rfl⟩ : syracuseStep 633911 = 950867) B950867
theorem B5442713 : Blo 421773 5442713 := bstep (se 2 (by rfl) ⟨2041017, by rfl⟩ : syracuseStep 5442713 = 4082035) B4082035
theorem B2403695 : Blo 421773 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B716519 : Blo 421773 716519 := bstep (se 1 (by rfl) ⟨537389, by rfl⟩ : syracuseStep 716519 = 1074779) B1074779
theorem B634859 : Blo 421773 634859 := bstep (se 1 (by rfl) ⟨476144, by rfl⟩ : syracuseStep 634859 = 952289) B952289
theorem B954575 : Blo 421773 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B1806583 : Blo 421773 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B422367 : Blo 421773 422367 := bstep (se 1 (by rfl) ⟨316775, by rfl⟩ : syracuseStep 422367 = 633551) B633551
theorem B422383 : Blo 421773 422383 := bstep (se 1 (by rfl) ⟨316787, by rfl⟩ : syracuseStep 422383 = 633575) B633575
theorem B619049 : Blo 421773 619049 := bstep (se 2 (by rfl) ⟨232143, by rfl⟩ : syracuseStep 619049 = 464287) B464287
theorem B954971 : Blo 421773 954971 := bstep (se 1 (by rfl) ⟨716228, by rfl⟩ : syracuseStep 954971 = 1432457) B1432457
theorem B2405335 : Blo 421773 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B39040001 : Blo 421773 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B17429519 : Blo 421773 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B955439 : Blo 421773 955439 := bstep (se 1 (by rfl) ⟨716579, by rfl⟩ : syracuseStep 955439 = 1433159) B1433159
theorem B1930367 : Blo 421773 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B423071 : Blo 421773 423071 := bstep (se 1 (by rfl) ⟨317303, by rfl⟩ : syracuseStep 423071 = 634607) B634607
theorem B636263 : Blo 421773 636263 := bstep (se 1 (by rfl) ⟨477197, by rfl⟩ : syracuseStep 636263 = 954395) B954395
theorem B423551 : Blo 421773 423551 := bstep (se 1 (by rfl) ⟨317663, by rfl⟩ : syracuseStep 423551 = 635327) B635327
theorem B423583 : Blo 421773 423583 := bstep (se 1 (by rfl) ⟨317687, by rfl⟩ : syracuseStep 423583 = 635375) B635375
theorem B7739063 : Blo 421773 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B915227 : Blo 421773 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B3168047 : Blo 421773 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B4577107 : Blo 421773 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B31692707 : Blo 421773 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B1202111 : Blo 421773 1202111 := bstep (se 1 (by rfl) ⟨901583, by rfl⟩ : syracuseStep 1202111 = 1803167) B1803167
theorem B1071083 : Blo 421773 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B35772509 : Blo 421773 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B1612001 : Blo 421773 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B424219 : Blo 421773 424219 := bstep (se 1 (by rfl) ⟨318164, by rfl⟩ : syracuseStep 424219 = 636329) B636329
theorem B801103 : Blo 421773 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B4331879 : Blo 421773 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B73980317 : Blo 421773 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B4069925 : Blo 421773 4069925 := bstep (se 4 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 4069925 = 763111) B763111
theorem B7805737 : Blo 421773 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B1432511 : Blo 421773 1432511 := bstep (se 1 (by rfl) ⟨1074383, by rfl⟩ : syracuseStep 1432511 = 2148767) B2148767
theorem B1203295 : Blo 421773 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B2284793 : Blo 421773 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B474655 : Blo 421773 474655 := bstep (se 1 (by rfl) ⟨355991, by rfl⟩ : syracuseStep 474655 = 711983) B711983
theorem B949967 : Blo 421773 949967 := bstep (se 1 (by rfl) ⟨712475, by rfl⟩ : syracuseStep 949967 = 1424951) B1424951
theorem B1605865 : Blo 421773 1605865 := bstep (se 2 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 1605865 = 1204399) B1204399
theorem B2408777 : Blo 421773 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B1851815 : Blo 421773 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B26026667 : Blo 421773 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B1286911 : Blo 421773 1286911 := bstep (se 1 (by rfl) ⟨965183, by rfl⟩ : syracuseStep 1286911 = 1930367) B1930367
theorem B951137 : Blo 421773 951137 := bstep (se 2 (by rfl) ⟨356676, by rfl⟩ : syracuseStep 951137 = 713353) B713353
theorem B21128471 : Blo 421773 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B714055 : Blo 421773 714055 := bstep (se 1 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 714055 = 1071083) B1071083
theorem B23848339 : Blo 421773 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B509375 : Blo 421773 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B1426895 : Blo 421773 1426895 := bstep (se 1 (by rfl) ⟨1070171, by rfl⟩ : syracuseStep 1426895 = 2140343) B2140343
theorem B1074667 : Blo 421773 1074667 := bstep (se 1 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 1074667 = 1612001) B1612001
theorem B2713283 : Blo 421773 2713283 := bstep (se 1 (by rfl) ⟨2034962, by rfl⟩ : syracuseStep 2713283 = 4069925) B4069925
theorem B632873 : Blo 421773 632873 := bstep (se 2 (by rfl) ⟨237327, by rfl⟩ : syracuseStep 632873 = 474655) B474655
theorem B633311 : Blo 421773 633311 := bstep (se 1 (by rfl) ⟨474983, by rfl⟩ : syracuseStep 633311 = 949967) B949967
theorem B477679 : Blo 421773 477679 := bstep (se 1 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 477679 = 716519) B716519
theorem B953225 : Blo 421773 953225 := bstep (se 2 (by rfl) ⟨357459, by rfl⟩ : syracuseStep 953225 = 714919) B714919
theorem B1068137 : Blo 421773 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B3222665 : Blo 421773 3222665 := bstep (se 2 (by rfl) ⟨1208499, by rfl⟩ : syracuseStep 3222665 = 2416999) B2416999
theorem B3214889 : Blo 421773 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B1470095 : Blo 421773 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B10407649 : Blo 421773 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B1928927 : Blo 421773 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B30994163 : Blo 421773 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B2404151 : Blo 421773 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B610151 : Blo 421773 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B421791 : Blo 421773 421791 := bstep (se 1 (by rfl) ⟨316343, by rfl⟩ : syracuseStep 421791 = 632687) B632687
theorem B3207113 : Blo 421773 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B1650797 : Blo 421773 1650797 := bstep (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) B619049
theorem B2887919 : Blo 421773 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B49320211 : Blo 421773 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B422375 : Blo 421773 422375 := bstep (se 1 (by rfl) ⟨316781, by rfl⟩ : syracuseStep 422375 = 633563) B633563
theorem B422427 : Blo 421773 422427 := bstep (se 1 (by rfl) ⟨316820, by rfl⟩ : syracuseStep 422427 = 633641) B633641
theorem B422431 : Blo 421773 422431 := bstep (se 1 (by rfl) ⟨316823, by rfl⟩ : syracuseStep 422431 = 633647) B633647
theorem B422491 : Blo 421773 422491 := bstep (se 1 (by rfl) ⟨316868, by rfl⟩ : syracuseStep 422491 = 633737) B633737
theorem B955007 : Blo 421773 955007 := bstep (se 1 (by rfl) ⟨716255, by rfl⟩ : syracuseStep 955007 = 1432511) B1432511
theorem B422559 : Blo 421773 422559 := bstep (se 1 (by rfl) ⟨316919, by rfl⟩ : syracuseStep 422559 = 633839) B633839
theorem B422591 : Blo 421773 422591 := bstep (se 1 (by rfl) ⟨316943, by rfl⟩ : syracuseStep 422591 = 633887) B633887
theorem B602815 : Blo 421773 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B422607 : Blo 421773 422607 := bstep (se 1 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 422607 = 633911) B633911
theorem B1602463 : Blo 421773 1602463 := bstep (se 1 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 1602463 = 2403695) B2403695
theorem B423239 : Blo 421773 423239 := bstep (se 1 (by rfl) ⟨317429, by rfl⟩ : syracuseStep 423239 = 634859) B634859
theorem B46478717 : Blo 421773 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B636383 : Blo 421773 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B636647 : Blo 421773 636647 := bstep (se 1 (by rfl) ⟨477485, by rfl⟩ : syracuseStep 636647 = 954971) B954971
theorem B636959 : Blo 421773 636959 := bstep (se 1 (by rfl) ⟨477719, by rfl⟩ : syracuseStep 636959 = 955439) B955439
theorem B29775923 : Blo 421773 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B52795475 : Blo 421773 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B424175 : Blo 421773 424175 := bstep (se 1 (by rfl) ⟨318131, by rfl⟩ : syracuseStep 424175 = 636263) B636263
theorem B1071407 : Blo 421773 1071407 := bstep (se 1 (by rfl) ⟨803555, by rfl⟩ : syracuseStep 1071407 = 1607111) B1607111
theorem B13064591 : Blo 421773 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B5159375 : Blo 421773 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B2112031 : Blo 421773 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B801407 : Blo 421773 801407 := bstep (se 1 (by rfl) ⟨601055, by rfl⟩ : syracuseStep 801407 = 1202111) B1202111
theorem B2415359 : Blo 421773 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B1604393 : Blo 421773 1604393 := bstep (se 2 (by rfl) ⟨601647, by rfl⟩ : syracuseStep 1604393 = 1203295) B1203295
theorem B3628475 : Blo 421773 3628475 := bstep (se 1 (by rfl) ⟨2721356, by rfl⟩ : syracuseStep 3628475 = 5442713) B5442713
theorem B1523195 : Blo 421773 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B6102809 : Blo 421773 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B1925279 : Blo 421773 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B1605851 : Blo 421773 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B17351111 : Blo 421773 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B803753 : Blo 421773 803753 := bstep (se 2 (by rfl) ⟨301407, by rfl⟩ : syracuseStep 803753 = 602815) B602815
theorem B951263 : Blo 421773 951263 := bstep (se 1 (by rfl) ⟨713447, by rfl⟩ : syracuseStep 951263 = 1426895) B1426895
theorem B19850615 : Blo 421773 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B714271 : Blo 421773 714271 := bstep (se 1 (by rfl) ⟨535703, by rfl⟩ : syracuseStep 714271 = 1071407) B1071407
theorem B8709727 : Blo 421773 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B534271 : Blo 421773 534271 := bstep (se 1 (by rfl) ⟨400703, by rfl⟩ : syracuseStep 534271 = 801407) B801407
theorem B952073 : Blo 421773 952073 := bstep (se 2 (by rfl) ⟨357027, by rfl⟩ : syracuseStep 952073 = 714055) B714055
theorem B2148443 : Blo 421773 2148443 := bstep (se 1 (by rfl) ⟨1611332, by rfl⟩ : syracuseStep 2148443 = 3222665) B3222665
theorem B2418983 : Blo 421773 2418983 := bstep (se 1 (by rfl) ⟨1814237, by rfl⟩ : syracuseStep 2418983 = 3628475) B3628475
theorem B20662775 : Blo 421773 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B1100531 : Blo 421773 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B2141153 : Blo 421773 2141153 := bstep (se 2 (by rfl) ⟨802932, by rfl⟩ : syracuseStep 2141153 = 1605865) B1605865
theorem B65760281 : Blo 421773 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B634091 : Blo 421773 634091 := bstep (se 1 (by rfl) ⟨475568, by rfl⟩ : syracuseStep 634091 = 951137) B951137
theorem B14085647 : Blo 421773 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B30985811 : Blo 421773 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B421915 : Blo 421773 421915 := bstep (se 1 (by rfl) ⟨316436, by rfl⟩ : syracuseStep 421915 = 632873) B632873
theorem B35196983 : Blo 421773 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B422207 : Blo 421773 422207 := bstep (se 1 (by rfl) ⟨316655, by rfl⟩ : syracuseStep 422207 = 633311) B633311
theorem B1610239 : Blo 421773 1610239 := bstep (se 1 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 1610239 = 2415359) B2415359
theorem B31797785 : Blo 421773 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B1069595 : Blo 421773 1069595 := bstep (se 1 (by rfl) ⟨802196, by rfl⟩ : syracuseStep 1069595 = 1604393) B1604393
theorem B635483 : Blo 421773 635483 := bstep (se 1 (by rfl) ⟨476612, by rfl⟩ : syracuseStep 635483 = 953225) B953225
theorem B1627069 : Blo 421773 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B2143259 : Blo 421773 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B980063 : Blo 421773 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B4068539 : Blo 421773 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B1602767 : Blo 421773 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B1234543 : Blo 421773 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B636671 : Blo 421773 636671 := bstep (se 1 (by rfl) ⟨477503, by rfl⟩ : syracuseStep 636671 = 955007) B955007
theorem B636905 : Blo 421773 636905 := bstep (se 2 (by rfl) ⟨238839, by rfl⟩ : syracuseStep 636905 = 477679) B477679
theorem B2816041 : Blo 421773 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B424255 : Blo 421773 424255 := bstep (se 1 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 424255 = 636383) B636383
theorem B1808855 : Blo 421773 1808855 := bstep (se 1 (by rfl) ⟨1356641, by rfl⟩ : syracuseStep 1808855 = 2713283) B2713283
theorem B424431 : Blo 421773 424431 := bstep (se 1 (by rfl) ⟨318323, by rfl⟩ : syracuseStep 424431 = 636647) B636647
theorem B1358333 : Blo 421773 1358333 := bstep (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) B509375
theorem B2136617 : Blo 421773 2136617 := bstep (se 2 (by rfl) ⟨801231, by rfl⟩ : syracuseStep 2136617 = 1602463) B1602463
theorem B6863525 : Blo 421773 6863525 := bstep (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) B1286911
theorem B424639 : Blo 421773 424639 := bstep (se 1 (by rfl) ⟨318479, by rfl⟩ : syracuseStep 424639 = 636959) B636959
theorem B3439583 : Blo 421773 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B1432889 : Blo 421773 1432889 := bstep (se 2 (by rfl) ⟨537333, by rfl⟩ : syracuseStep 1432889 = 1074667) B1074667
theorem B712091 : Blo 421773 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B13876865 : Blo 421773 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B1015463 : Blo 421773 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B1285951 : Blo 421773 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B2138075 : Blo 421773 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B713063 : Blo 421773 713063 := bstep (se 1 (by rfl) ⟨534797, by rfl⟩ : syracuseStep 713063 = 1069595) B1069595
theorem B2146985 : Blo 421773 2146985 := bstep (se 2 (by rfl) ⟨805119, by rfl⟩ : syracuseStep 2146985 = 1610239) B1610239
theorem B2712359 : Blo 421773 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B46269629 : Blo 421773 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B1205903 : Blo 421773 1205903 := bstep (se 1 (by rfl) ⟨904427, by rfl⟩ : syracuseStep 1205903 = 1808855) B1808855
theorem B2934749 : Blo 421773 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B1427435 : Blo 421773 1427435 := bstep (se 1 (by rfl) ⟨1070576, by rfl⟩ : syracuseStep 1427435 = 2141153) B2141153
theorem B952361 : Blo 421773 952361 := bstep (se 2 (by rfl) ⟨357135, by rfl⟩ : syracuseStep 952361 = 714271) B714271
theorem B9390431 : Blo 421773 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B1714601 : Blo 421773 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B9251243 : Blo 421773 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B23464655 : Blo 421773 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B3754721 : Blo 421773 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B535835 : Blo 421773 535835 := bstep (se 1 (by rfl) ⟨401876, by rfl⟩ : syracuseStep 535835 = 803753) B803753
theorem B634175 : Blo 421773 634175 := bstep (se 1 (by rfl) ⟨475631, by rfl⟩ : syracuseStep 634175 = 951263) B951263
theorem B1428839 : Blo 421773 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B1068511 : Blo 421773 1068511 := bstep (se 1 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 1068511 = 1602767) B1602767
theorem B13233743 : Blo 421773 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B634715 : Blo 421773 634715 := bstep (se 1 (by rfl) ⟨476036, by rfl⟩ : syracuseStep 634715 = 952073) B952073
theorem B13775183 : Blo 421773 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B905555 : Blo 421773 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B2707901 : Blo 421773 2707901 := bstep (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) B1015463
theorem B4575683 : Blo 421773 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B43840187 : Blo 421773 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B11612969 : Blo 421773 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B422727 : Blo 421773 422727 := bstep (se 1 (by rfl) ⟨317045, by rfl⟩ : syracuseStep 422727 = 634091) B634091
theorem B955259 : Blo 421773 955259 := bstep (se 1 (by rfl) ⟨716444, by rfl⟩ : syracuseStep 955259 = 1432889) B1432889
theorem B20657207 : Blo 421773 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B1283519 : Blo 421773 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B1070567 : Blo 421773 1070567 := bstep (se 1 (by rfl) ⟨802925, by rfl⟩ : syracuseStep 1070567 = 1605851) B1605851
theorem B21198523 : Blo 421773 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B423655 : Blo 421773 423655 := bstep (se 1 (by rfl) ⟨317741, by rfl⟩ : syracuseStep 423655 = 635483) B635483
theorem B653375 : Blo 421773 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B424447 : Blo 421773 424447 := bstep (se 1 (by rfl) ⟨318335, by rfl⟩ : syracuseStep 424447 = 636671) B636671
theorem B2169425 : Blo 421773 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B424603 : Blo 421773 424603 := bstep (se 1 (by rfl) ⟨318452, by rfl⟩ : syracuseStep 424603 = 636905) B636905
theorem B1432295 : Blo 421773 1432295 := bstep (se 1 (by rfl) ⟨1074221, by rfl⟩ : syracuseStep 1432295 = 2148443) B2148443
theorem B1612655 : Blo 421773 1612655 := bstep (se 1 (by rfl) ⟨1209491, by rfl⟩ : syracuseStep 1612655 = 2418983) B2418983
theorem B1424411 : Blo 421773 1424411 := bstep (se 1 (by rfl) ⟨1068308, by rfl⟩ : syracuseStep 1424411 = 2136617) B2136617
theorem B2293055 : Blo 421773 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B1646057 : Blo 421773 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B474727 : Blo 421773 474727 := bstep (se 1 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 474727 = 712091) B712091
theorem B712361 : Blo 421773 712361 := bstep (se 2 (by rfl) ⟨267135, by rfl⟩ : syracuseStep 712361 = 534271) B534271
theorem B1425383 : Blo 421773 1425383 := bstep (se 1 (by rfl) ⟨1069037, by rfl⟩ : syracuseStep 1425383 = 2138075) B2138075
theorem B9183455 : Blo 421773 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B475375 : Blo 421773 475375 := bstep (se 1 (by rfl) ⟨356531, by rfl⟩ : syracuseStep 475375 = 713063) B713063
theorem B7741979 : Blo 421773 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B13771471 : Blo 421773 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B713711 : Blo 421773 713711 := bstep (se 1 (by rfl) ⟨535283, by rfl⟩ : syracuseStep 713711 = 1070567) B1070567
theorem B803935 : Blo 421773 803935 := bstep (se 1 (by rfl) ⟨602951, by rfl⟩ : syracuseStep 803935 = 1205903) B1205903
theorem B951623 : Blo 421773 951623 := bstep (se 1 (by rfl) ⟨713717, by rfl⟩ : syracuseStep 951623 = 1427435) B1427435
theorem B435583 : Blo 421773 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B6260287 : Blo 421773 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B1075103 : Blo 421773 1075103 := bstep (se 1 (by rfl) ⟨806327, by rfl⟩ : syracuseStep 1075103 = 1612655) B1612655
theorem B632969 : Blo 421773 632969 := bstep (se 2 (by rfl) ⟨237363, by rfl⟩ : syracuseStep 632969 = 474727) B474727
theorem B952559 : Blo 421773 952559 := bstep (se 1 (by rfl) ⟨714419, by rfl⟩ : syracuseStep 952559 = 1428839) B1428839
theorem B28264697 : Blo 421773 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B7825997 : Blo 421773 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B1805267 : Blo 421773 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B3050455 : Blo 421773 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B1428893 : Blo 421773 1428893 := bstep (se 3 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 1428893 = 535835) B535835
theorem B30846419 : Blo 421773 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B954863 : Blo 421773 954863 := bstep (se 1 (by rfl) ⟨716147, by rfl⟩ : syracuseStep 954863 = 1432295) B1432295
theorem B855679 : Blo 421773 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B634907 : Blo 421773 634907 := bstep (se 1 (by rfl) ⟨476180, by rfl⟩ : syracuseStep 634907 = 952361) B952361
theorem B1143067 : Blo 421773 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B1446283 : Blo 421773 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B15643103 : Blo 421773 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B2503147 : Blo 421773 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B422783 : Blo 421773 422783 := bstep (se 1 (by rfl) ⟨317087, by rfl⟩ : syracuseStep 422783 = 634175) B634175
theorem B1528703 : Blo 421773 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B423143 : Blo 421773 423143 := bstep (se 1 (by rfl) ⟨317357, by rfl⟩ : syracuseStep 423143 = 634715) B634715
theorem B603703 : Blo 421773 603703 := bstep (se 1 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 603703 = 905555) B905555
theorem B1431323 : Blo 421773 1431323 := bstep (se 1 (by rfl) ⟨1073492, by rfl⟩ : syracuseStep 1431323 = 2146985) B2146985
theorem B29226791 : Blo 421773 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B1808239 : Blo 421773 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B636839 : Blo 421773 636839 := bstep (se 1 (by rfl) ⟨477629, by rfl⟩ : syracuseStep 636839 = 955259) B955259
theorem B6167495 : Blo 421773 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1424681 : Blo 421773 1424681 := bstep (se 2 (by rfl) ⟨534255, by rfl⟩ : syracuseStep 1424681 = 1068511) B1068511
theorem B949607 : Blo 421773 949607 := bstep (se 1 (by rfl) ⟨712205, by rfl⟩ : syracuseStep 949607 = 1424411) B1424411
theorem B1097371 : Blo 421773 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B8822495 : Blo 421773 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B474907 : Blo 421773 474907 := bstep (se 1 (by rfl) ⟨356180, by rfl⟩ : syracuseStep 474907 = 712361) B712361
theorem B950255 : Blo 421773 950255 := bstep (se 1 (by rfl) ⟨712691, by rfl⟩ : syracuseStep 950255 = 1425383) B1425383
theorem B3219749 : Blo 421773 3219749 := bstep (se 4 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 3219749 = 603703) B603703
theorem B5161319 : Blo 421773 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B1524089 : Blo 421773 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B475807 : Blo 421773 475807 := bstep (se 1 (by rfl) ⟨356855, by rfl⟩ : syracuseStep 475807 = 713711) B713711
theorem B41714941 : Blo 421773 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B18843131 : Blo 421773 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B1140905 : Blo 421773 1140905 := bstep (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) B855679
theorem B633071 : Blo 421773 633071 := bstep (se 1 (by rfl) ⟨474803, by rfl⟩ : syracuseStep 633071 = 949607) B949607
theorem B952595 : Blo 421773 952595 := bstep (se 1 (by rfl) ⟨714446, by rfl⟩ : syracuseStep 952595 = 1428893) B1428893
theorem B20564279 : Blo 421773 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B633209 : Blo 421773 633209 := bstep (se 2 (by rfl) ⟨237453, by rfl⟩ : syracuseStep 633209 = 474907) B474907
theorem B2410985 : Blo 421773 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B633503 : Blo 421773 633503 := bstep (se 1 (by rfl) ⟨475127, by rfl⟩ : syracuseStep 633503 = 950255) B950255
theorem B6122303 : Blo 421773 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B633833 : Blo 421773 633833 := bstep (se 2 (by rfl) ⟨237687, by rfl⟩ : syracuseStep 633833 = 475375) B475375
theorem B1928377 : Blo 421773 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B1019135 : Blo 421773 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B3337529 : Blo 421773 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B5852645 : Blo 421773 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B634415 : Blo 421773 634415 := bstep (se 1 (by rfl) ⟨475811, by rfl⟩ : syracuseStep 634415 = 951623) B951623
theorem B18361961 : Blo 421773 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B954215 : Blo 421773 954215 := bstep (se 1 (by rfl) ⟨715661, by rfl⟩ : syracuseStep 954215 = 1431323) B1431323
theorem B716735 : Blo 421773 716735 := bstep (se 1 (by rfl) ⟨537551, by rfl⟩ : syracuseStep 716735 = 1075103) B1075103
theorem B4067273 : Blo 421773 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B421979 : Blo 421773 421979 := bstep (se 1 (by rfl) ⟨316484, by rfl⟩ : syracuseStep 421979 = 632969) B632969
theorem B635039 : Blo 421773 635039 := bstep (se 1 (by rfl) ⟨476279, by rfl⟩ : syracuseStep 635039 = 952559) B952559
theorem B2323109 : Blo 421773 2323109 := bstep (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) B435583
theorem B423271 : Blo 421773 423271 := bstep (se 1 (by rfl) ⟨317453, by rfl⟩ : syracuseStep 423271 = 634907) B634907
theorem B636575 : Blo 421773 636575 := bstep (se 1 (by rfl) ⟨477431, by rfl⟩ : syracuseStep 636575 = 954863) B954863
theorem B424559 : Blo 421773 424559 := bstep (se 1 (by rfl) ⟨318419, by rfl⟩ : syracuseStep 424559 = 636839) B636839
theorem B1071913 : Blo 421773 1071913 := bstep (se 2 (by rfl) ⟨401967, by rfl⟩ : syracuseStep 1071913 = 803935) B803935
theorem B5217331 : Blo 421773 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B4111663 : Blo 421773 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B1203511 : Blo 421773 1203511 := bstep (se 1 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 1203511 = 1805267) B1805267
theorem B8347049 : Blo 421773 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B77938109 : Blo 421773 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B949787 : Blo 421773 949787 := bstep (se 1 (by rfl) ⟨712340, by rfl⟩ : syracuseStep 949787 = 1424681) B1424681
theorem B5881663 : Blo 421773 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B2146499 : Blo 421773 2146499 := bstep (se 1 (by rfl) ⟨1609874, by rfl⟩ : syracuseStep 2146499 = 3219749) B3219749
theorem B3440879 : Blo 421773 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B1016059 : Blo 421773 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B1548739 : Blo 421773 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B6956441 : Blo 421773 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B1607323 : Blo 421773 1607323 := bstep (se 1 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 1607323 = 2410985) B2410985
theorem B5482217 : Blo 421773 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B4081535 : Blo 421773 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B5564699 : Blo 421773 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B3901763 : Blo 421773 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B633191 : Blo 421773 633191 := bstep (se 1 (by rfl) ⟨474893, by rfl⟩ : syracuseStep 633191 = 949787) B949787
theorem B12241307 : Blo 421773 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B7842217 : Blo 421773 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B477823 : Blo 421773 477823 := bstep (se 1 (by rfl) ⟨358367, by rfl⟩ : syracuseStep 477823 = 716735) B716735
theorem B8900077 : Blo 421773 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B634409 : Blo 421773 634409 := bstep (se 2 (by rfl) ⟨237903, by rfl⟩ : syracuseStep 634409 = 475807) B475807
theorem B10284677 : Blo 421773 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B12562087 : Blo 421773 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B1429217 : Blo 421773 1429217 := bstep (se 2 (by rfl) ⟨535956, by rfl⟩ : syracuseStep 1429217 = 1071913) B1071913
theorem B422047 : Blo 421773 422047 := bstep (se 1 (by rfl) ⟨316535, by rfl⟩ : syracuseStep 422047 = 633071) B633071
theorem B635063 : Blo 421773 635063 := bstep (se 1 (by rfl) ⟨476297, by rfl⟩ : syracuseStep 635063 = 952595) B952595
theorem B13709519 : Blo 421773 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B422139 : Blo 421773 422139 := bstep (se 1 (by rfl) ⟨316604, by rfl⟩ : syracuseStep 422139 = 633209) B633209
theorem B55619921 : Blo 421773 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B422335 : Blo 421773 422335 := bstep (se 1 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 422335 = 633503) B633503
theorem B422555 : Blo 421773 422555 := bstep (se 1 (by rfl) ⟨316916, by rfl⟩ : syracuseStep 422555 = 633833) B633833
theorem B51958739 : Blo 421773 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B422943 : Blo 421773 422943 := bstep (se 1 (by rfl) ⟨317207, by rfl⟩ : syracuseStep 422943 = 634415) B634415
theorem B636143 : Blo 421773 636143 := bstep (se 1 (by rfl) ⟨477107, by rfl⟩ : syracuseStep 636143 = 954215) B954215
theorem B423359 : Blo 421773 423359 := bstep (se 1 (by rfl) ⟨317519, by rfl⟩ : syracuseStep 423359 = 635039) B635039
theorem B424383 : Blo 421773 424383 := bstep (se 1 (by rfl) ⟨318287, by rfl⟩ : syracuseStep 424383 = 636575) B636575
theorem B760603 : Blo 421773 760603 := bstep (se 1 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 760603 = 1140905) B1140905
theorem B1604681 : Blo 421773 1604681 := bstep (se 2 (by rfl) ⟨601755, by rfl⟩ : syracuseStep 1604681 = 1203511) B1203511
theorem B679423 : Blo 421773 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B2711515 : Blo 421773 2711515 := bstep (se 1 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 2711515 = 4067273) B4067273
theorem B2293919 : Blo 421773 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B4637627 : Blo 421773 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B3654811 : Blo 421773 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B2721023 : Blo 421773 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B8160871 : Blo 421773 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B8259941 : Blo 421773 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B952811 : Blo 421773 952811 := bstep (se 1 (by rfl) ⟨714608, by rfl⟩ : syracuseStep 952811 = 1429217) B1429217
theorem B3615353 : Blo 421773 3615353 := bstep (se 2 (by rfl) ⟨1355757, by rfl⟩ : syracuseStep 3615353 = 2711515) B2711515
theorem B37079947 : Blo 421773 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B1354745 : Blo 421773 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B10456289 : Blo 421773 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B34639159 : Blo 421773 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B2601175 : Blo 421773 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B422127 : Blo 421773 422127 := bstep (se 1 (by rfl) ⟨316595, by rfl⟩ : syracuseStep 422127 = 633191) B633191
theorem B11866769 : Blo 421773 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B905897 : Blo 421773 905897 := bstep (se 2 (by rfl) ⟨339711, by rfl⟩ : syracuseStep 905897 = 679423) B679423
theorem B1069787 : Blo 421773 1069787 := bstep (se 1 (by rfl) ⟨802340, by rfl⟩ : syracuseStep 1069787 = 1604681) B1604681
theorem B2143097 : Blo 421773 2143097 := bstep (se 2 (by rfl) ⟨803661, by rfl⟩ : syracuseStep 2143097 = 1607323) B1607323
theorem B16749449 : Blo 421773 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B422939 : Blo 421773 422939 := bstep (se 1 (by rfl) ⟨317204, by rfl⟩ : syracuseStep 422939 = 634409) B634409
theorem B423375 : Blo 421773 423375 := bstep (se 1 (by rfl) ⟨317531, by rfl⟩ : syracuseStep 423375 = 635063) B635063
theorem B1430999 : Blo 421773 1430999 := bstep (se 1 (by rfl) ⟨1073249, by rfl⟩ : syracuseStep 1430999 = 2146499) B2146499
theorem B9139679 : Blo 421773 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B424095 : Blo 421773 424095 := bstep (se 1 (by rfl) ⟨318071, by rfl⟩ : syracuseStep 424095 = 636143) B636143
theorem B637097 : Blo 421773 637097 := bstep (se 2 (by rfl) ⟨238911, by rfl⟩ : syracuseStep 637097 = 477823) B477823
theorem B1014137 : Blo 421773 1014137 := bstep (se 2 (by rfl) ⟨380301, by rfl⟩ : syracuseStep 1014137 = 760603) B760603
theorem B3709799 : Blo 421773 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B6856451 : Blo 421773 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B713191 : Blo 421773 713191 := bstep (se 1 (by rfl) ⟨534893, by rfl⟩ : syracuseStep 713191 = 1069787) B1069787
theorem B11166299 : Blo 421773 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B5506627 : Blo 421773 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B2410235 : Blo 421773 2410235 := bstep (se 1 (by rfl) ⟨1807676, by rfl⟩ : syracuseStep 2410235 = 3615353) B3615353
theorem B903163 : Blo 421773 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B10881161 : Blo 421773 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B3468233 : Blo 421773 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B1428731 : Blo 421773 1428731 := bstep (se 1 (by rfl) ⟨1071548, by rfl⟩ : syracuseStep 1428731 = 2143097) B2143097
theorem B3091751 : Blo 421773 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B1814015 : Blo 421773 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B953999 : Blo 421773 953999 := bstep (se 1 (by rfl) ⟨715499, by rfl⟩ : syracuseStep 953999 = 1430999) B1430999
theorem B676091 : Blo 421773 676091 := bstep (se 1 (by rfl) ⟨507068, by rfl⟩ : syracuseStep 676091 = 1014137) B1014137
theorem B635207 : Blo 421773 635207 := bstep (se 1 (by rfl) ⟨476405, by rfl⟩ : syracuseStep 635207 = 952811) B952811
theorem B197759717 : Blo 421773 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B1529279 : Blo 421773 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B7911179 : Blo 421773 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B603931 : Blo 421773 603931 := bstep (se 1 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 603931 = 905897) B905897
theorem B6093119 : Blo 421773 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B424731 : Blo 421773 424731 := bstep (se 1 (by rfl) ⟨318548, by rfl⟩ : syracuseStep 424731 = 637097) B637097
theorem B4873081 : Blo 421773 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B46185545 : Blo 421773 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B2473199 : Blo 421773 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B6970859 : Blo 421773 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B4570967 : Blo 421773 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B450727 : Blo 421773 450727 := bstep (se 1 (by rfl) ⟨338045, by rfl⟩ : syracuseStep 450727 = 676091) B676091
theorem B950921 : Blo 421773 950921 := bstep (se 2 (by rfl) ⟨356595, by rfl⟩ : syracuseStep 950921 = 713191) B713191
theorem B6497441 : Blo 421773 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B1606823 : Blo 421773 1606823 := bstep (se 1 (by rfl) ⟨1205117, by rfl⟩ : syracuseStep 1606823 = 2410235) B2410235
theorem B2312155 : Blo 421773 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B7342169 : Blo 421773 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B1648799 : Blo 421773 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B952487 : Blo 421773 952487 := bstep (se 1 (by rfl) ⟨714365, by rfl⟩ : syracuseStep 952487 = 1428731) B1428731
theorem B4647239 : Blo 421773 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B805241 : Blo 421773 805241 := bstep (se 2 (by rfl) ⟨301965, by rfl⟩ : syracuseStep 805241 = 603931) B603931
theorem B1019519 : Blo 421773 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B7254107 : Blo 421773 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B30790363 : Blo 421773 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B2061167 : Blo 421773 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1209343 : Blo 421773 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B635999 : Blo 421773 635999 := bstep (se 1 (by rfl) ⟨476999, by rfl⟩ : syracuseStep 635999 = 953999) B953999
theorem B423471 : Blo 421773 423471 := bstep (se 1 (by rfl) ⟨317603, by rfl⟩ : syracuseStep 423471 = 635207) B635207
theorem B7444199 : Blo 421773 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B131839811 : Blo 421773 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B5274119 : Blo 421773 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B4062079 : Blo 421773 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B3047311 : Blo 421773 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B1204217 : Blo 421773 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B19579117 : Blo 421773 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B2147309 : Blo 421773 2147309 := bstep (se 3 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 2147309 = 805241) B805241
theorem B5416105 : Blo 421773 5416105 := bstep (se 2 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 5416105 = 4062079) B4062079
theorem B87893207 : Blo 421773 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1099199 : Blo 421773 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B3098159 : Blo 421773 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B3082873 : Blo 421773 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B4836071 : Blo 421773 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B633947 : Blo 421773 633947 := bstep (se 1 (by rfl) ⟨475460, by rfl⟩ : syracuseStep 633947 = 950921) B950921
theorem B2403877 : Blo 421773 2403877 := bstep (se 4 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 2403877 = 450727) B450727
theorem B41053817 : Blo 421773 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B634991 : Blo 421773 634991 := bstep (se 1 (by rfl) ⟨476243, by rfl⟩ : syracuseStep 634991 = 952487) B952487
theorem B423999 : Blo 421773 423999 := bstep (se 1 (by rfl) ⟨317999, by rfl⟩ : syracuseStep 423999 = 635999) B635999
theorem B4331627 : Blo 421773 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B1071215 : Blo 421773 1071215 := bstep (se 1 (by rfl) ⟨803411, by rfl⟩ : syracuseStep 1071215 = 1606823) B1606823
theorem B4962799 : Blo 421773 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B1612457 : Blo 421773 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B14064317 : Blo 421773 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B5496445 : Blo 421773 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B679679 : Blo 421773 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B4063081 : Blo 421773 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B802811 : Blo 421773 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B2065439 : Blo 421773 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B714143 : Blo 421773 714143 := bstep (se 1 (by rfl) ⟨535607, by rfl⟩ : syracuseStep 714143 = 1071215) B1071215
theorem B1074971 : Blo 421773 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B12896189 : Blo 421773 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B3205169 : Blo 421773 3205169 := bstep (se 2 (by rfl) ⟨1201938, by rfl⟩ : syracuseStep 3205169 = 2403877) B2403877
theorem B5417441 : Blo 421773 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B453119 : Blo 421773 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B2140829 : Blo 421773 2140829 := bstep (se 3 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 2140829 = 802811) B802811
theorem B2887751 : Blo 421773 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B7221473 : Blo 421773 7221473 := bstep (se 2 (by rfl) ⟨2708052, by rfl⟩ : syracuseStep 7221473 = 5416105) B5416105
theorem B9376211 : Blo 421773 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B422631 : Blo 421773 422631 := bstep (se 1 (by rfl) ⟨316973, by rfl⟩ : syracuseStep 422631 = 633947) B633947
theorem B7328593 : Blo 421773 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B423327 : Blo 421773 423327 := bstep (se 1 (by rfl) ⟨317495, by rfl⟩ : syracuseStep 423327 = 634991) B634991
theorem B26105489 : Blo 421773 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B6617065 : Blo 421773 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B1431539 : Blo 421773 1431539 := bstep (se 1 (by rfl) ⟨1073654, by rfl⟩ : syracuseStep 1431539 = 2147309) B2147309
theorem B58595471 : Blo 421773 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B4110497 : Blo 421773 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2931197 : Blo 421773 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B27369211 : Blo 421773 27369211 := bstep (se 1 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 27369211 = 41053817) B41053817
theorem B7700669 : Blo 421773 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B6250807 : Blo 421773 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B476095 : Blo 421773 476095 := bstep (se 1 (by rfl) ⟨357071, by rfl⟩ : syracuseStep 476095 = 714143) B714143
theorem B1427219 : Blo 421773 1427219 := bstep (se 1 (by rfl) ⟨1070414, by rfl⟩ : syracuseStep 1427219 = 2140829) B2140829
theorem B5507837 : Blo 421773 5507837 := bstep (se 3 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 5507837 = 2065439) B2065439
theorem B17403659 : Blo 421773 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B716647 : Blo 421773 716647 := bstep (se 1 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 716647 = 1074971) B1074971
theorem B8597459 : Blo 421773 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B954359 : Blo 421773 954359 := bstep (se 1 (by rfl) ⟨715769, by rfl⟩ : syracuseStep 954359 = 1431539) B1431539
theorem B39063647 : Blo 421773 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B2740331 : Blo 421773 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B36492281 : Blo 421773 36492281 := bstep (se 2 (by rfl) ⟨13684605, by rfl⟩ : syracuseStep 36492281 = 27369211) B27369211
theorem B31266101 : Blo 421773 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B4814315 : Blo 421773 4814315 := bstep (se 1 (by rfl) ⟨3610736, by rfl⟩ : syracuseStep 4814315 = 7221473) B7221473
theorem B9771457 : Blo 421773 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B2136779 : Blo 421773 2136779 := bstep (se 1 (by rfl) ⟨1602584, by rfl⟩ : syracuseStep 2136779 = 3205169) B3205169
theorem B3611627 : Blo 421773 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B8822753 : Blo 421773 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B4833269 : Blo 421773 4833269 := bstep (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) B453119
theorem B26042431 : Blo 421773 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B1826887 : Blo 421773 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B951479 : Blo 421773 951479 := bstep (se 1 (by rfl) ⟨713609, by rfl⟩ : syracuseStep 951479 = 1427219) B1427219
theorem B3671891 : Blo 421773 3671891 := bstep (se 1 (by rfl) ⟨2753918, by rfl⟩ : syracuseStep 3671891 = 5507837) B5507837
theorem B11602439 : Blo 421773 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B3222179 : Blo 421773 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B8334409 : Blo 421773 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B13028609 : Blo 421773 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B20844067 : Blo 421773 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B634793 : Blo 421773 634793 := bstep (se 2 (by rfl) ⟨238047, by rfl⟩ : syracuseStep 634793 = 476095) B476095
theorem B955529 : Blo 421773 955529 := bstep (se 2 (by rfl) ⟨358323, by rfl⟩ : syracuseStep 955529 = 716647) B716647
theorem B22926557 : Blo 421773 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B636239 : Blo 421773 636239 := bstep (se 1 (by rfl) ⟨477179, by rfl⟩ : syracuseStep 636239 = 954359) B954359
theorem B5133779 : Blo 421773 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B24328187 : Blo 421773 24328187 := bstep (se 1 (by rfl) ⟨18246140, by rfl⟩ : syracuseStep 24328187 = 36492281) B36492281
theorem B3209543 : Blo 421773 3209543 := bstep (se 1 (by rfl) ⟨2407157, by rfl⟩ : syracuseStep 3209543 = 4814315) B4814315
theorem B1424519 : Blo 421773 1424519 := bstep (se 1 (by rfl) ⟨1068389, by rfl⟩ : syracuseStep 1424519 = 2136779) B2136779
theorem B2407751 : Blo 421773 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B5881835 : Blo 421773 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B2139695 : Blo 421773 2139695 := bstep (se 1 (by rfl) ⟨1604771, by rfl⟩ : syracuseStep 2139695 = 3209543) B3209543
theorem B7734959 : Blo 421773 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B2148119 : Blo 421773 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B8685739 : Blo 421773 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B2435849 : Blo 421773 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B634319 : Blo 421773 634319 := bstep (se 1 (by rfl) ⟨475739, by rfl⟩ : syracuseStep 634319 = 951479) B951479
theorem B11112545 : Blo 421773 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B27792089 : Blo 421773 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B423195 : Blo 421773 423195 := bstep (se 1 (by rfl) ⟨317396, by rfl⟩ : syracuseStep 423195 = 634793) B634793
theorem B3921223 : Blo 421773 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B34723241 : Blo 421773 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B637019 : Blo 421773 637019 := bstep (se 1 (by rfl) ⟨477764, by rfl⟩ : syracuseStep 637019 = 955529) B955529
theorem B15284371 : Blo 421773 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B424159 : Blo 421773 424159 := bstep (se 1 (by rfl) ⟨318119, by rfl⟩ : syracuseStep 424159 = 636239) B636239
theorem B3422519 : Blo 421773 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B2447927 : Blo 421773 2447927 := bstep (se 1 (by rfl) ⟨1835945, by rfl⟩ : syracuseStep 2447927 = 3671891) B3671891
theorem B16218791 : Blo 421773 16218791 := bstep (se 1 (by rfl) ⟨12164093, by rfl⟩ : syracuseStep 16218791 = 24328187) B24328187
theorem B949679 : Blo 421773 949679 := bstep (se 1 (by rfl) ⟨712259, by rfl⟩ : syracuseStep 949679 = 1424519) B1424519
theorem B1605167 : Blo 421773 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B1426463 : Blo 421773 1426463 := bstep (se 1 (by rfl) ⟨1069847, by rfl⟩ : syracuseStep 1426463 = 2139695) B2139695
theorem B1631951 : Blo 421773 1631951 := bstep (se 1 (by rfl) ⟨1223963, by rfl⟩ : syracuseStep 1631951 = 2447927) B2447927
theorem B5228297 : Blo 421773 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B1623899 : Blo 421773 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B633119 : Blo 421773 633119 := bstep (se 1 (by rfl) ⟨474839, by rfl⟩ : syracuseStep 633119 = 949679) B949679
theorem B7408363 : Blo 421773 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B5156639 : Blo 421773 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B2281679 : Blo 421773 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B422879 : Blo 421773 422879 := bstep (se 1 (by rfl) ⟨317159, by rfl⟩ : syracuseStep 422879 = 634319) B634319
theorem B1070111 : Blo 421773 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B20379161 : Blo 421773 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B11580985 : Blo 421773 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B18528059 : Blo 421773 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B23148827 : Blo 421773 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B1432079 : Blo 421773 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B424679 : Blo 421773 424679 := bstep (se 1 (by rfl) ⟨318509, by rfl⟩ : syracuseStep 424679 = 637019) B637019
theorem B10812527 : Blo 421773 10812527 := bstep (se 1 (by rfl) ⟨8109395, by rfl⟩ : syracuseStep 10812527 = 16218791) B16218791
theorem B950975 : Blo 421773 950975 := bstep (se 1 (by rfl) ⟨713231, by rfl⟩ : syracuseStep 950975 = 1426463) B1426463
theorem B713407 : Blo 421773 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B49408157 : Blo 421773 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B3485531 : Blo 421773 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B422079 : Blo 421773 422079 := bstep (se 1 (by rfl) ⟨316559, by rfl⟩ : syracuseStep 422079 = 633119) B633119
theorem B954719 : Blo 421773 954719 := bstep (se 1 (by rfl) ⟨716039, by rfl⟩ : syracuseStep 954719 = 1432079) B1432079
theorem B4330397 : Blo 421773 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B3437759 : Blo 421773 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B1521119 : Blo 421773 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B61765253 : Blo 421773 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B9877817 : Blo 421773 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B1087967 : Blo 421773 1087967 := bstep (se 1 (by rfl) ⟨815975, by rfl⟩ : syracuseStep 1087967 = 1631951) B1631951
theorem B54344429 : Blo 421773 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B15432551 : Blo 421773 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B7208351 : Blo 421773 7208351 := bstep (se 1 (by rfl) ⟨5406263, by rfl⟩ : syracuseStep 7208351 = 10812527) B10812527
theorem B9167357 : Blo 421773 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B951209 : Blo 421773 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B4056317 : Blo 421773 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B131755085 : Blo 421773 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B633983 : Blo 421773 633983 := bstep (se 1 (by rfl) ⟨475487, by rfl⟩ : syracuseStep 633983 = 950975) B950975
theorem B2886931 : Blo 421773 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B41176835 : Blo 421773 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B725311 : Blo 421773 725311 := bstep (se 1 (by rfl) ⟨543983, by rfl⟩ : syracuseStep 725311 = 1087967) B1087967
theorem B36229619 : Blo 421773 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B9294749 : Blo 421773 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B4805567 : Blo 421773 4805567 := bstep (se 1 (by rfl) ⟨3604175, by rfl⟩ : syracuseStep 4805567 = 7208351) B7208351
theorem B636479 : Blo 421773 636479 := bstep (se 1 (by rfl) ⟨477359, by rfl⟩ : syracuseStep 636479 = 954719) B954719
theorem B6585211 : Blo 421773 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B10288367 : Blo 421773 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B3203711 : Blo 421773 3203711 := bstep (se 1 (by rfl) ⟨2402783, by rfl⟩ : syracuseStep 3203711 = 4805567) B4805567
theorem B2704211 : Blo 421773 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B24446285 : Blo 421773 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B3868325 : Blo 421773 3868325 := bstep (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) B725311
theorem B87836723 : Blo 421773 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B6858911 : Blo 421773 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B24153079 : Blo 421773 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B6196499 : Blo 421773 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B634139 : Blo 421773 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B422655 : Blo 421773 422655 := bstep (se 1 (by rfl) ⟨316991, by rfl⟩ : syracuseStep 422655 = 633983) B633983
theorem B424319 : Blo 421773 424319 := bstep (se 1 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 424319 = 636479) B636479
theorem B8780281 : Blo 421773 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B3849241 : Blo 421773 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B27451223 : Blo 421773 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B1802807 : Blo 421773 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B32204105 : Blo 421773 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B58557815 : Blo 421773 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B4572607 : Blo 421773 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B4130999 : Blo 421773 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B46828165 : Blo 421773 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B16297523 : Blo 421773 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B5132321 : Blo 421773 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B422759 : Blo 421773 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B2135807 : Blo 421773 2135807 := bstep (se 1 (by rfl) ⟨1601855, by rfl⟩ : syracuseStep 2135807 = 3203711) B3203711
theorem B2578883 : Blo 421773 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B18300815 : Blo 421773 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B2753999 : Blo 421773 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B6096809 : Blo 421773 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B10865015 : Blo 421773 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B12200543 : Blo 421773 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B39038543 : Blo 421773 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B6877021 : Blo 421773 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B3421547 : Blo 421773 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1201871 : Blo 421773 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B62437553 : Blo 421773 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B21469403 : Blo 421773 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B1423871 : Blo 421773 1423871 := bstep (se 1 (by rfl) ⟨1067903, by rfl⟩ : syracuseStep 1423871 = 2135807) B2135807
theorem B1835999 : Blo 421773 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B41625035 : Blo 421773 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B14312935 : Blo 421773 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B7243343 : Blo 421773 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B9169361 : Blo 421773 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B2281031 : Blo 421773 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B16258157 : Blo 421773 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B801247 : Blo 421773 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B949247 : Blo 421773 949247 := bstep (se 1 (by rfl) ⟨711935, by rfl⟩ : syracuseStep 949247 = 1423871) B1423871
theorem B8133695 : Blo 421773 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B26025695 : Blo 421773 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B10838771 : Blo 421773 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B6112907 : Blo 421773 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B632831 : Blo 421773 632831 := bstep (se 1 (by rfl) ⟨474623, by rfl⟩ : syracuseStep 632831 = 949247) B949247
theorem B76335653 : Blo 421773 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B1068329 : Blo 421773 1068329 := bstep (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) B801247
theorem B1223999 : Blo 421773 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B27750023 : Blo 421773 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B4828895 : Blo 421773 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B1520687 : Blo 421773 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B5422463 : Blo 421773 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B17350463 : Blo 421773 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B7225847 : Blo 421773 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B3614975 : Blo 421773 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B18500015 : Blo 421773 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B4075271 : Blo 421773 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B421887 : Blo 421773 421887 := bstep (se 1 (by rfl) ⟨316415, by rfl⟩ : syracuseStep 421887 = 632831) B632831
theorem B815999 : Blo 421773 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B1013791 : Blo 421773 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B203561741 : Blo 421773 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B712219 : Blo 421773 712219 := bstep (se 1 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 712219 = 1068329) B1068329
theorem B3219263 : Blo 421773 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B11566975 : Blo 421773 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B1351721 : Blo 421773 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B4817231 : Blo 421773 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B2409983 : Blo 421773 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B12333343 : Blo 421773 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B2175997 : Blo 421773 2175997 := bstep (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) B815999
theorem B15422633 : Blo 421773 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B2716847 : Blo 421773 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B135707827 : Blo 421773 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B949625 : Blo 421773 949625 := bstep (se 2 (by rfl) ⟨356109, by rfl⟩ : syracuseStep 949625 = 712219) B712219
theorem B2146175 : Blo 421773 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B901147 : Blo 421773 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B3211487 : Blo 421773 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B10281755 : Blo 421773 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B1811231 : Blo 421773 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B1606655 : Blo 421773 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B2901329 : Blo 421773 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B633083 : Blo 421773 633083 := bstep (se 1 (by rfl) ⟨474812, by rfl⟩ : syracuseStep 633083 = 949625) B949625
theorem B16444457 : Blo 421773 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B1430783 : Blo 421773 1430783 := bstep (se 1 (by rfl) ⟨1073087, by rfl⟩ : syracuseStep 1430783 = 2146175) B2146175
theorem B180943769 : Blo 421773 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B1934219 : Blo 421773 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B120629179 : Blo 421773 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B10962971 : Blo 421773 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B2140991 : Blo 421773 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B1207487 : Blo 421773 1207487 := bstep (se 1 (by rfl) ⟨905615, by rfl⟩ : syracuseStep 1207487 = 1811231) B1811231
theorem B953855 : Blo 421773 953855 := bstep (se 1 (by rfl) ⟨715391, by rfl⟩ : syracuseStep 953855 = 1430783) B1430783
theorem B422055 : Blo 421773 422055 := bstep (se 1 (by rfl) ⟨316541, by rfl⟩ : syracuseStep 422055 = 633083) B633083
theorem B1201529 : Blo 421773 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B6854503 : Blo 421773 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B1071103 : Blo 421773 1071103 := bstep (se 1 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 1071103 = 1606655) B1606655
theorem B7308647 : Blo 421773 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B1427327 : Blo 421773 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B804991 : Blo 421773 804991 := bstep (se 1 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 804991 = 1207487) B1207487
theorem B1428137 : Blo 421773 1428137 := bstep (se 2 (by rfl) ⟨535551, by rfl⟩ : syracuseStep 1428137 = 1071103) B1071103
theorem B1289479 : Blo 421773 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B643355621 : Blo 421773 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B635903 : Blo 421773 635903 := bstep (se 1 (by rfl) ⟨476927, by rfl⟩ : syracuseStep 635903 = 953855) B953855
theorem B9139337 : Blo 421773 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B801019 : Blo 421773 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B1073321 : Blo 421773 1073321 := bstep (se 2 (by rfl) ⟨402495, by rfl⟩ : syracuseStep 1073321 = 804991) B804991
theorem B951551 : Blo 421773 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B952091 : Blo 421773 952091 := bstep (se 1 (by rfl) ⟨714068, by rfl⟩ : syracuseStep 952091 = 1428137) B1428137
theorem B1068025 : Blo 421773 1068025 := bstep (se 2 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 1068025 = 801019) B801019
theorem B428903747 : Blo 421773 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B423935 : Blo 421773 423935 := bstep (se 1 (by rfl) ⟨317951, by rfl⟩ : syracuseStep 423935 = 635903) B635903
theorem B6092891 : Blo 421773 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B4872431 : Blo 421773 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B1719305 : Blo 421773 1719305 := bstep (se 2 (by rfl) ⟨644739, by rfl⟩ : syracuseStep 1719305 = 1289479) B1289479
theorem B12993149 : Blo 421773 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B285935831 : Blo 421773 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B715547 : Blo 421773 715547 := bstep (se 1 (by rfl) ⟨536660, by rfl⟩ : syracuseStep 715547 = 1073321) B1073321
theorem B634367 : Blo 421773 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B634727 : Blo 421773 634727 := bstep (se 1 (by rfl) ⟨476045, by rfl⟩ : syracuseStep 634727 = 952091) B952091
theorem B1424033 : Blo 421773 1424033 := bstep (se 2 (by rfl) ⟨534012, by rfl⟩ : syracuseStep 1424033 = 1068025) B1068025
theorem B4061927 : Blo 421773 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B1146203 : Blo 421773 1146203 := bstep (se 1 (by rfl) ⟨859652, by rfl⟩ : syracuseStep 1146203 = 1719305) B1719305
theorem B477031 : Blo 421773 477031 := bstep (se 1 (by rfl) ⟨357773, by rfl⟩ : syracuseStep 477031 = 715547) B715547
theorem B764135 : Blo 421773 764135 := bstep (se 1 (by rfl) ⟨573101, by rfl⟩ : syracuseStep 764135 = 1146203) B1146203
theorem B8662099 : Blo 421773 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B190623887 : Blo 421773 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B2707951 : Blo 421773 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B422911 : Blo 421773 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B423151 : Blo 421773 423151 := bstep (se 1 (by rfl) ⟨317363, by rfl⟩ : syracuseStep 423151 = 634727) B634727
theorem B949355 : Blo 421773 949355 := bstep (se 1 (by rfl) ⟨712016, by rfl⟩ : syracuseStep 949355 = 1424033) B1424033
theorem B127082591 : Blo 421773 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B509423 : Blo 421773 509423 := bstep (se 1 (by rfl) ⟨382067, by rfl⟩ : syracuseStep 509423 = 764135) B764135
theorem B632903 : Blo 421773 632903 := bstep (se 1 (by rfl) ⟨474677, by rfl⟩ : syracuseStep 632903 = 949355) B949355
theorem B636041 : Blo 421773 636041 := bstep (se 2 (by rfl) ⟨238515, by rfl⟩ : syracuseStep 636041 = 477031) B477031
theorem B3610601 : Blo 421773 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B11549465 : Blo 421773 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B84721727 : Blo 421773 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B421935 : Blo 421773 421935 := bstep (se 1 (by rfl) ⟨316451, by rfl⟩ : syracuseStep 421935 = 632903) B632903
theorem B424027 : Blo 421773 424027 := bstep (se 1 (by rfl) ⟨318020, by rfl⟩ : syracuseStep 424027 = 636041) B636041
theorem B1358461 : Blo 421773 1358461 := bstep (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) B509423
theorem B2407067 : Blo 421773 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B7699643 : Blo 421773 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B1811281 : Blo 421773 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B5133095 : Blo 421773 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B56481151 : Blo 421773 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B1604711 : Blo 421773 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B1069807 : Blo 421773 1069807 := bstep (se 1 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 1069807 = 1604711) B1604711
theorem B3422063 : Blo 421773 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B2415041 : Blo 421773 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B75308201 : Blo 421773 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B1426409 : Blo 421773 1426409 := bstep (se 2 (by rfl) ⟨534903, by rfl⟩ : syracuseStep 1426409 = 1069807) B1069807
theorem B2281375 : Blo 421773 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B1610027 : Blo 421773 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B50205467 : Blo 421773 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B1073351 : Blo 421773 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B950939 : Blo 421773 950939 := bstep (se 1 (by rfl) ⟨713204, by rfl⟩ : syracuseStep 950939 = 1426409) B1426409
theorem B3041833 : Blo 421773 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B133881245 : Blo 421773 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B4055777 : Blo 421773 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B89254163 : Blo 421773 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B715567 : Blo 421773 715567 := bstep (se 1 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 715567 = 1073351) B1073351
theorem B633959 : Blo 421773 633959 := bstep (se 1 (by rfl) ⟨475469, by rfl⟩ : syracuseStep 633959 = 950939) B950939
theorem B2703851 : Blo 421773 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B954089 : Blo 421773 954089 := bstep (se 2 (by rfl) ⟨357783, by rfl⟩ : syracuseStep 954089 = 715567) B715567
theorem B59502775 : Blo 421773 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B422639 : Blo 421773 422639 := bstep (se 1 (by rfl) ⟨316979, by rfl⟩ : syracuseStep 422639 = 633959) B633959
theorem B1802567 : Blo 421773 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B636059 : Blo 421773 636059 := bstep (se 1 (by rfl) ⟨477044, by rfl⟩ : syracuseStep 636059 = 954089) B954089
theorem B79337033 : Blo 421773 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B52891355 : Blo 421773 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B1201711 : Blo 421773 1201711 := bstep (se 1 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 1201711 = 1802567) B1802567
theorem B424039 : Blo 421773 424039 := bstep (se 1 (by rfl) ⟨318029, by rfl⟩ : syracuseStep 424039 = 636059) B636059
theorem B35260903 : Blo 421773 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B1602281 : Blo 421773 1602281 := bstep (se 2 (by rfl) ⟨600855, by rfl⟩ : syracuseStep 1602281 = 1201711) B1201711
theorem B188058149 : Blo 421773 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B1068187 : Blo 421773 1068187 := bstep (se 1 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 1068187 = 1602281) B1602281
theorem B125372099 : Blo 421773 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B1424249 : Blo 421773 1424249 := bstep (se 2 (by rfl) ⟨534093, by rfl⟩ : syracuseStep 1424249 = 1068187) B1068187
theorem B83581399 : Blo 421773 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B949499 : Blo 421773 949499 := bstep (se 1 (by rfl) ⟨712124, by rfl⟩ : syracuseStep 949499 = 1424249) B1424249
theorem B632999 : Blo 421773 632999 := bstep (se 1 (by rfl) ⟨474749, by rfl⟩ : syracuseStep 632999 = 949499) B949499
theorem B111441865 : Blo 421773 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B148589153 : Blo 421773 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B421999 : Blo 421773 421999 := bstep (se 1 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 421999 = 632999) B632999
theorem B99059435 : Blo 421773 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B66039623 : Blo 421773 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B44026415 : Blo 421773 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B29350943 : Blo 421773 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 421773 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 421773 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B8696575 : Blo 421773 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B11595433 : Blo 421773 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 421773 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 421773 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B6871367 : Blo 421773 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B4580911 : Blo 421773 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B6107881 : Blo 421773 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 421773 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B5429227 : Blo 421773 5429227 := bstep (se 1 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 5429227 = 8143841) B8143841
theorem B7238969 : Blo 421773 7238969 := bstep (se 2 (by rfl) ⟨2714613, by rfl⟩ : syracuseStep 7238969 = 5429227) B5429227
theorem B4825979 : Blo 421773 4825979 := bstep (se 1 (by rfl) ⟨3619484, by rfl⟩ : syracuseStep 4825979 = 7238969) B7238969
theorem B3217319 : Blo 421773 3217319 := bstep (se 1 (by rfl) ⟨2412989, by rfl⟩ : syracuseStep 3217319 = 4825979) B4825979
theorem B2144879 : Blo 421773 2144879 := bstep (se 1 (by rfl) ⟨1608659, by rfl⟩ : syracuseStep 2144879 = 3217319) B3217319
theorem B1429919 : Blo 421773 1429919 := bstep (se 1 (by rfl) ⟨1072439, by rfl⟩ : syracuseStep 1429919 = 2144879) B2144879
theorem B953279 : Blo 421773 953279 := bstep (se 1 (by rfl) ⟨714959, by rfl⟩ : syracuseStep 953279 = 1429919) B1429919
theorem B635519 : Blo 421773 635519 := bstep (se 1 (by rfl) ⟨476639, by rfl⟩ : syracuseStep 635519 = 953279) B953279
theorem B423679 : Blo 421773 423679 := bstep (se 1 (by rfl) ⟨317759, by rfl⟩ : syracuseStep 423679 = 635519) B635519

theorem C0 (j : ℕ) (h1 : 105443 ≤ j) (h2 : j ≤ 106142) : Blo 421773 (4 * j + 3) := by
  interval_cases j
  · exact B421775
  · exact B421779
  · exact B421783
  · exact B421787
  · exact B421791
  · exact B421795
  · exact B421799
  · exact B421803
  · exact B421807
  · exact B421811
  · exact B421815
  · exact B421819
  · exact B421823
  · exact B421827
  · exact B421831
  · exact B421835
  · exact B421839
  · exact B421843
  · exact B421847
  · exact B421851
  · exact B421855
  · exact B421859
  · exact B421863
  · exact B421867
  · exact B421871
  · exact B421875
  · exact B421879
  · exact B421883
  · exact B421887
  · exact B421891
  · exact B421895
  · exact B421899
  · exact B421903
  · exact B421907
  · exact B421911
  · exact B421915
  · exact B421919
  · exact B421923
  · exact B421927
  · exact B421931
  · exact B421935
  · exact B421939
  · exact B421943
  · exact B421947
  · exact B421951
  · exact B421955
  · exact B421959
  · exact B421963
  · exact B421967
  · exact B421971
  · exact B421975
  · exact B421979
  · exact B421983
  · exact B421987
  · exact B421991
  · exact B421995
  · exact B421999
  · exact B422003
  · exact B422007
  · exact B422011
  · exact B422015
  · exact B422019
  · exact B422023
  · exact B422027
  · exact B422031
  · exact B422035
  · exact B422039
  · exact B422043
  · exact B422047
  · exact B422051
  · exact B422055
  · exact B422059
  · exact B422063
  · exact B422067
  · exact B422071
  · exact B422075
  · exact B422079
  · exact B422083
  · exact B422087
  · exact B422091
  · exact B422095
  · exact B422099
  · exact B422103
  · exact B422107
  · exact B422111
  · exact B422115
  · exact B422119
  · exact B422123
  · exact B422127
  · exact B422131
  · exact B422135
  · exact B422139
  · exact B422143
  · exact B422147
  · exact B422151
  · exact B422155
  · exact B422159
  · exact B422163
  · exact B422167
  · exact B422171
  · exact B422175
  · exact B422179
  · exact B422183
  · exact B422187
  · exact B422191
  · exact B422195
  · exact B422199
  · exact B422203
  · exact B422207
  · exact B422211
  · exact B422215
  · exact B422219
  · exact B422223
  · exact B422227
  · exact B422231
  · exact B422235
  · exact B422239
  · exact B422243
  · exact B422247
  · exact B422251
  · exact B422255
  · exact B422259
  · exact B422263
  · exact B422267
  · exact B422271
  · exact B422275
  · exact B422279
  · exact B422283
  · exact B422287
  · exact B422291
  · exact B422295
  · exact B422299
  · exact B422303
  · exact B422307
  · exact B422311
  · exact B422315
  · exact B422319
  · exact B422323
  · exact B422327
  · exact B422331
  · exact B422335
  · exact B422339
  · exact B422343
  · exact B422347
  · exact B422351
  · exact B422355
  · exact B422359
  · exact B422363
  · exact B422367
  · exact B422371
  · exact B422375
  · exact B422379
  · exact B422383
  · exact B422387
  · exact B422391
  · exact B422395
  · exact B422399
  · exact B422403
  · exact B422407
  · exact B422411
  · exact B422415
  · exact B422419
  · exact B422423
  · exact B422427
  · exact B422431
  · exact B422435
  · exact B422439
  · exact B422443
  · exact B422447
  · exact B422451
  · exact B422455
  · exact B422459
  · exact B422463
  · exact B422467
  · exact B422471
  · exact B422475
  · exact B422479
  · exact B422483
  · exact B422487
  · exact B422491
  · exact B422495
  · exact B422499
  · exact B422503
  · exact B422507
  · exact B422511
  · exact B422515
  · exact B422519
  · exact B422523
  · exact B422527
  · exact B422531
  · exact B422535
  · exact B422539
  · exact B422543
  · exact B422547
  · exact B422551
  · exact B422555
  · exact B422559
  · exact B422563
  · exact B422567
  · exact B422571
  · exact B422575
  · exact B422579
  · exact B422583
  · exact B422587
  · exact B422591
  · exact B422595
  · exact B422599
  · exact B422603
  · exact B422607
  · exact B422611
  · exact B422615
  · exact B422619
  · exact B422623
  · exact B422627
  · exact B422631
  · exact B422635
  · exact B422639
  · exact B422643
  · exact B422647
  · exact B422651
  · exact B422655
  · exact B422659
  · exact B422663
  · exact B422667
  · exact B422671
  · exact B422675
  · exact B422679
  · exact B422683
  · exact B422687
  · exact B422691
  · exact B422695
  · exact B422699
  · exact B422703
  · exact B422707
  · exact B422711
  · exact B422715
  · exact B422719
  · exact B422723
  · exact B422727
  · exact B422731
  · exact B422735
  · exact B422739
  · exact B422743
  · exact B422747
  · exact B422751
  · exact B422755
  · exact B422759
  · exact B422763
  · exact B422767
  · exact B422771
  · exact B422775
  · exact B422779
  · exact B422783
  · exact B422787
  · exact B422791
  · exact B422795
  · exact B422799
  · exact B422803
  · exact B422807
  · exact B422811
  · exact B422815
  · exact B422819
  · exact B422823
  · exact B422827
  · exact B422831
  · exact B422835
  · exact B422839
  · exact B422843
  · exact B422847
  · exact B422851
  · exact B422855
  · exact B422859
  · exact B422863
  · exact B422867
  · exact B422871
  · exact B422875
  · exact B422879
  · exact B422883
  · exact B422887
  · exact B422891
  · exact B422895
  · exact B422899
  · exact B422903
  · exact B422907
  · exact B422911
  · exact B422915
  · exact B422919
  · exact B422923
  · exact B422927
  · exact B422931
  · exact B422935
  · exact B422939
  · exact B422943
  · exact B422947
  · exact B422951
  · exact B422955
  · exact B422959
  · exact B422963
  · exact B422967
  · exact B422971
  · exact B422975
  · exact B422979
  · exact B422983
  · exact B422987
  · exact B422991
  · exact B422995
  · exact B422999
  · exact B423003
  · exact B423007
  · exact B423011
  · exact B423015
  · exact B423019
  · exact B423023
  · exact B423027
  · exact B423031
  · exact B423035
  · exact B423039
  · exact B423043
  · exact B423047
  · exact B423051
  · exact B423055
  · exact B423059
  · exact B423063
  · exact B423067
  · exact B423071
  · exact B423075
  · exact B423079
  · exact B423083
  · exact B423087
  · exact B423091
  · exact B423095
  · exact B423099
  · exact B423103
  · exact B423107
  · exact B423111
  · exact B423115
  · exact B423119
  · exact B423123
  · exact B423127
  · exact B423131
  · exact B423135
  · exact B423139
  · exact B423143
  · exact B423147
  · exact B423151
  · exact B423155
  · exact B423159
  · exact B423163
  · exact B423167
  · exact B423171
  · exact B423175
  · exact B423179
  · exact B423183
  · exact B423187
  · exact B423191
  · exact B423195
  · exact B423199
  · exact B423203
  · exact B423207
  · exact B423211
  · exact B423215
  · exact B423219
  · exact B423223
  · exact B423227
  · exact B423231
  · exact B423235
  · exact B423239
  · exact B423243
  · exact B423247
  · exact B423251
  · exact B423255
  · exact B423259
  · exact B423263
  · exact B423267
  · exact B423271
  · exact B423275
  · exact B423279
  · exact B423283
  · exact B423287
  · exact B423291
  · exact B423295
  · exact B423299
  · exact B423303
  · exact B423307
  · exact B423311
  · exact B423315
  · exact B423319
  · exact B423323
  · exact B423327
  · exact B423331
  · exact B423335
  · exact B423339
  · exact B423343
  · exact B423347
  · exact B423351
  · exact B423355
  · exact B423359
  · exact B423363
  · exact B423367
  · exact B423371
  · exact B423375
  · exact B423379
  · exact B423383
  · exact B423387
  · exact B423391
  · exact B423395
  · exact B423399
  · exact B423403
  · exact B423407
  · exact B423411
  · exact B423415
  · exact B423419
  · exact B423423
  · exact B423427
  · exact B423431
  · exact B423435
  · exact B423439
  · exact B423443
  · exact B423447
  · exact B423451
  · exact B423455
  · exact B423459
  · exact B423463
  · exact B423467
  · exact B423471
  · exact B423475
  · exact B423479
  · exact B423483
  · exact B423487
  · exact B423491
  · exact B423495
  · exact B423499
  · exact B423503
  · exact B423507
  · exact B423511
  · exact B423515
  · exact B423519
  · exact B423523
  · exact B423527
  · exact B423531
  · exact B423535
  · exact B423539
  · exact B423543
  · exact B423547
  · exact B423551
  · exact B423555
  · exact B423559
  · exact B423563
  · exact B423567
  · exact B423571
  · exact B423575
  · exact B423579
  · exact B423583
  · exact B423587
  · exact B423591
  · exact B423595
  · exact B423599
  · exact B423603
  · exact B423607
  · exact B423611
  · exact B423615
  · exact B423619
  · exact B423623
  · exact B423627
  · exact B423631
  · exact B423635
  · exact B423639
  · exact B423643
  · exact B423647
  · exact B423651
  · exact B423655
  · exact B423659
  · exact B423663
  · exact B423667
  · exact B423671
  · exact B423675
  · exact B423679
  · exact B423683
  · exact B423687
  · exact B423691
  · exact B423695
  · exact B423699
  · exact B423703
  · exact B423707
  · exact B423711
  · exact B423715
  · exact B423719
  · exact B423723
  · exact B423727
  · exact B423731
  · exact B423735
  · exact B423739
  · exact B423743
  · exact B423747
  · exact B423751
  · exact B423755
  · exact B423759
  · exact B423763
  · exact B423767
  · exact B423771
  · exact B423775
  · exact B423779
  · exact B423783
  · exact B423787
  · exact B423791
  · exact B423795
  · exact B423799
  · exact B423803
  · exact B423807
  · exact B423811
  · exact B423815
  · exact B423819
  · exact B423823
  · exact B423827
  · exact B423831
  · exact B423835
  · exact B423839
  · exact B423843
  · exact B423847
  · exact B423851
  · exact B423855
  · exact B423859
  · exact B423863
  · exact B423867
  · exact B423871
  · exact B423875
  · exact B423879
  · exact B423883
  · exact B423887
  · exact B423891
  · exact B423895
  · exact B423899
  · exact B423903
  · exact B423907
  · exact B423911
  · exact B423915
  · exact B423919
  · exact B423923
  · exact B423927
  · exact B423931
  · exact B423935
  · exact B423939
  · exact B423943
  · exact B423947
  · exact B423951
  · exact B423955
  · exact B423959
  · exact B423963
  · exact B423967
  · exact B423971
  · exact B423975
  · exact B423979
  · exact B423983
  · exact B423987
  · exact B423991
  · exact B423995
  · exact B423999
  · exact B424003
  · exact B424007
  · exact B424011
  · exact B424015
  · exact B424019
  · exact B424023
  · exact B424027
  · exact B424031
  · exact B424035
  · exact B424039
  · exact B424043
  · exact B424047
  · exact B424051
  · exact B424055
  · exact B424059
  · exact B424063
  · exact B424067
  · exact B424071
  · exact B424075
  · exact B424079
  · exact B424083
  · exact B424087
  · exact B424091
  · exact B424095
  · exact B424099
  · exact B424103
  · exact B424107
  · exact B424111
  · exact B424115
  · exact B424119
  · exact B424123
  · exact B424127
  · exact B424131
  · exact B424135
  · exact B424139
  · exact B424143
  · exact B424147
  · exact B424151
  · exact B424155
  · exact B424159
  · exact B424163
  · exact B424167
  · exact B424171
  · exact B424175
  · exact B424179
  · exact B424183
  · exact B424187
  · exact B424191
  · exact B424195
  · exact B424199
  · exact B424203
  · exact B424207
  · exact B424211
  · exact B424215
  · exact B424219
  · exact B424223
  · exact B424227
  · exact B424231
  · exact B424235
  · exact B424239
  · exact B424243
  · exact B424247
  · exact B424251
  · exact B424255
  · exact B424259
  · exact B424263
  · exact B424267
  · exact B424271
  · exact B424275
  · exact B424279
  · exact B424283
  · exact B424287
  · exact B424291
  · exact B424295
  · exact B424299
  · exact B424303
  · exact B424307
  · exact B424311
  · exact B424315
  · exact B424319
  · exact B424323
  · exact B424327
  · exact B424331
  · exact B424335
  · exact B424339
  · exact B424343
  · exact B424347
  · exact B424351
  · exact B424355
  · exact B424359
  · exact B424363
  · exact B424367
  · exact B424371
  · exact B424375
  · exact B424379
  · exact B424383
  · exact B424387
  · exact B424391
  · exact B424395
  · exact B424399
  · exact B424403
  · exact B424407
  · exact B424411
  · exact B424415
  · exact B424419
  · exact B424423
  · exact B424427
  · exact B424431
  · exact B424435
  · exact B424439
  · exact B424443
  · exact B424447
  · exact B424451
  · exact B424455
  · exact B424459
  · exact B424463
  · exact B424467
  · exact B424471
  · exact B424475
  · exact B424479
  · exact B424483
  · exact B424487
  · exact B424491
  · exact B424495
  · exact B424499
  · exact B424503
  · exact B424507
  · exact B424511
  · exact B424515
  · exact B424519
  · exact B424523
  · exact B424527
  · exact B424531
  · exact B424535
  · exact B424539
  · exact B424543
  · exact B424547
  · exact B424551
  · exact B424555
  · exact B424559
  · exact B424563
  · exact B424567
  · exact B424571

theorem C1 (j : ℕ) (h1 : 106143 ≤ j) (h2 : j ≤ 106192) : Blo 421773 (4 * j + 3) := by
  interval_cases j
  · exact B424575
  · exact B424579
  · exact B424583
  · exact B424587
  · exact B424591
  · exact B424595
  · exact B424599
  · exact B424603
  · exact B424607
  · exact B424611
  · exact B424615
  · exact B424619
  · exact B424623
  · exact B424627
  · exact B424631
  · exact B424635
  · exact B424639
  · exact B424643
  · exact B424647
  · exact B424651
  · exact B424655
  · exact B424659
  · exact B424663
  · exact B424667
  · exact B424671
  · exact B424675
  · exact B424679
  · exact B424683
  · exact B424687
  · exact B424691
  · exact B424695
  · exact B424699
  · exact B424703
  · exact B424707
  · exact B424711
  · exact B424715
  · exact B424719
  · exact B424723
  · exact B424727
  · exact B424731
  · exact B424735
  · exact B424739
  · exact B424743
  · exact B424747
  · exact B424751
  · exact B424755
  · exact B424759
  · exact B424763
  · exact B424767
  · exact B424771

theorem solution (m : ℕ) (hlo : 421773 ≤ m) (hhi : m ≤ 424773) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 105443 ≤ j := by omega
    have hj2 : j ≤ 106192 := by omega
    have hb : Blo 421773 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 106143 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
