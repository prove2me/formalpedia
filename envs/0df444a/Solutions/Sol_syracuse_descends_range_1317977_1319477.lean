-- Prove2me | solution 1 for syracuse_descends_range_1317977_1319477
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:33.912274+00:00
-- url     : https://prove2.me/submissions/14c6895c-6be5-4e82-a61c-5d5f0c6140ca

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


theorem B2965517 : Blo 1317977 2965517 := bbase (se 3 (by rfl) ⟨556034, by rfl⟩ : syracuseStep 2965517 = 1112069) (by norm_num)
theorem B1482781 : Blo 1317977 1482781 := bbase (se 3 (by rfl) ⟨278021, by rfl⟩ : syracuseStep 1482781 = 556043) (by norm_num)
theorem B1482817 : Blo 1317977 1482817 := bbase (se 2 (by rfl) ⟨556056, by rfl⟩ : syracuseStep 1482817 = 1112113) (by norm_num)
theorem B2965589 : Blo 1317977 2965589 := bbase (se 8 (by rfl) ⟨17376, by rfl⟩ : syracuseStep 2965589 = 34753) (by norm_num)
theorem B4448357 : Blo 1317977 4448357 := bbase (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) (by norm_num)
theorem B1482853 : Blo 1317977 1482853 := bbase (se 4 (by rfl) ⟨139017, by rfl⟩ : syracuseStep 1482853 = 278035) (by norm_num)
theorem B1482889 : Blo 1317977 1482889 := bbase (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) (by norm_num)
theorem B2965661 : Blo 1317977 2965661 := bbase (se 3 (by rfl) ⟨556061, by rfl⟩ : syracuseStep 2965661 = 1112123) (by norm_num)
theorem B3383461 : Blo 1317977 3383461 := bbase (se 4 (by rfl) ⟨317199, by rfl⟩ : syracuseStep 3383461 = 634399) (by norm_num)
theorem B1482925 : Blo 1317977 1482925 := bbase (se 3 (by rfl) ⟨278048, by rfl⟩ : syracuseStep 1482925 = 556097) (by norm_num)
theorem B1482961 : Blo 1317977 1482961 := bbase (se 2 (by rfl) ⟨556110, by rfl⟩ : syracuseStep 1482961 = 1112221) (by norm_num)
theorem B2965733 : Blo 1317977 2965733 := bbase (se 4 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 2965733 = 556075) (by norm_num)
theorem B1482997 : Blo 1317977 1482997 := bbase (se 5 (by rfl) ⟨69515, by rfl⟩ : syracuseStep 1482997 = 139031) (by norm_num)
theorem B1483033 : Blo 1317977 1483033 := bbase (se 2 (by rfl) ⟨556137, by rfl⟩ : syracuseStep 1483033 = 1112275) (by norm_num)
theorem B2965805 : Blo 1317977 2965805 := bbase (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) (by norm_num)
theorem B1483069 : Blo 1317977 1483069 := bbase (se 3 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 1483069 = 556151) (by norm_num)
theorem B1483105 : Blo 1317977 1483105 := bbase (se 2 (by rfl) ⟨556164, by rfl⟩ : syracuseStep 1483105 = 1112329) (by norm_num)
theorem B2965877 : Blo 1317977 2965877 := bbase (se 5 (by rfl) ⟨139025, by rfl⟩ : syracuseStep 2965877 = 278051) (by norm_num)
theorem B1483141 : Blo 1317977 1483141 := bbase (se 4 (by rfl) ⟨139044, by rfl⟩ : syracuseStep 1483141 = 278089) (by norm_num)
theorem B1483177 : Blo 1317977 1483177 := bbase (se 2 (by rfl) ⟨556191, by rfl⟩ : syracuseStep 1483177 = 1112383) (by norm_num)
theorem B3047861 : Blo 1317977 3047861 := bbase (se 5 (by rfl) ⟨142868, by rfl⟩ : syracuseStep 3047861 = 285737) (by norm_num)
theorem B2965949 : Blo 1317977 2965949 := bbase (se 3 (by rfl) ⟨556115, by rfl⟩ : syracuseStep 2965949 = 1112231) (by norm_num)
theorem B1483213 : Blo 1317977 1483213 := bbase (se 3 (by rfl) ⟨278102, by rfl⟩ : syracuseStep 1483213 = 556205) (by norm_num)
theorem B32063957 : Blo 1317977 32063957 := bbase (se 7 (by rfl) ⟨375749, by rfl⟩ : syracuseStep 32063957 = 751499) (by norm_num)
theorem B1483249 : Blo 1317977 1483249 := bbase (se 2 (by rfl) ⟨556218, by rfl⟩ : syracuseStep 1483249 = 1112437) (by norm_num)
theorem B2966021 : Blo 1317977 2966021 := bbase (se 4 (by rfl) ⟨278064, by rfl⟩ : syracuseStep 2966021 = 556129) (by norm_num)
theorem B4448789 : Blo 1317977 4448789 := bbase (se 6 (by rfl) ⟨104268, by rfl⟩ : syracuseStep 4448789 = 208537) (by norm_num)
theorem B1483285 : Blo 1317977 1483285 := bbase (se 6 (by rfl) ⟨34764, by rfl⟩ : syracuseStep 1483285 = 69529) (by norm_num)
theorem B1483321 : Blo 1317977 1483321 := bbase (se 2 (by rfl) ⟨556245, by rfl⟩ : syracuseStep 1483321 = 1112491) (by norm_num)
theorem B2966093 : Blo 1317977 2966093 := bbase (se 3 (by rfl) ⟨556142, by rfl⟩ : syracuseStep 2966093 = 1112285) (by norm_num)
theorem B1483357 : Blo 1317977 1483357 := bbase (se 3 (by rfl) ⟨278129, by rfl⟩ : syracuseStep 1483357 = 556259) (by norm_num)
theorem B1483393 : Blo 1317977 1483393 := bbase (se 2 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 1483393 = 1112545) (by norm_num)
theorem B2171525 : Blo 1317977 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B2966165 : Blo 1317977 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B1483429 : Blo 1317977 1483429 := bbase (se 4 (by rfl) ⟨139071, by rfl⟩ : syracuseStep 1483429 = 278143) (by norm_num)
theorem B1483465 : Blo 1317977 1483465 := bbase (se 2 (by rfl) ⟨556299, by rfl⟩ : syracuseStep 1483465 = 1112599) (by norm_num)
theorem B2966237 : Blo 1317977 2966237 := bbase (se 3 (by rfl) ⟨556169, by rfl⟩ : syracuseStep 2966237 = 1112339) (by norm_num)
theorem B1483501 : Blo 1317977 1483501 := bbase (se 3 (by rfl) ⟨278156, by rfl⟩ : syracuseStep 1483501 = 556313) (by norm_num)
theorem B2286341 : Blo 1317977 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B3212045 : Blo 1317977 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B1483537 : Blo 1317977 1483537 := bbase (se 2 (by rfl) ⟨556326, by rfl⟩ : syracuseStep 1483537 = 1112653) (by norm_num)
theorem B1876765 : Blo 1317977 1876765 := bbase (se 3 (by rfl) ⟨351893, by rfl⟩ : syracuseStep 1876765 = 703787) (by norm_num)
theorem B2966309 : Blo 1317977 2966309 := bbase (se 4 (by rfl) ⟨278091, by rfl⟩ : syracuseStep 2966309 = 556183) (by norm_num)
theorem B1483573 : Blo 1317977 1483573 := bbase (se 5 (by rfl) ⟨69542, by rfl⟩ : syracuseStep 1483573 = 139085) (by norm_num)
theorem B1483609 : Blo 1317977 1483609 := bbase (se 2 (by rfl) ⟨556353, by rfl⟩ : syracuseStep 1483609 = 1112707) (by norm_num)
theorem B2966381 : Blo 1317977 2966381 := bbase (se 3 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 2966381 = 1112393) (by norm_num)
theorem B1483645 : Blo 1317977 1483645 := bbase (se 3 (by rfl) ⟨278183, by rfl⟩ : syracuseStep 1483645 = 556367) (by norm_num)
theorem B1483681 : Blo 1317977 1483681 := bbase (se 2 (by rfl) ⟨556380, by rfl⟩ : syracuseStep 1483681 = 1112761) (by norm_num)
theorem B2966453 : Blo 1317977 2966453 := bbase (se 5 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 2966453 = 278105) (by norm_num)
theorem B4449221 : Blo 1317977 4449221 := bbase (se 4 (by rfl) ⟨417114, by rfl⟩ : syracuseStep 4449221 = 834229) (by norm_num)
theorem B1483717 : Blo 1317977 1483717 := bbase (se 4 (by rfl) ⟨139098, by rfl⟩ : syracuseStep 1483717 = 278197) (by norm_num)
theorem B6677477 : Blo 1317977 6677477 := bbase (se 4 (by rfl) ⟨626013, by rfl⟩ : syracuseStep 6677477 = 1252027) (by norm_num)
theorem B1483753 : Blo 1317977 1483753 := bbase (se 2 (by rfl) ⟨556407, by rfl⟩ : syracuseStep 1483753 = 1112815) (by norm_num)
theorem B2966525 : Blo 1317977 2966525 := bbase (se 3 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 2966525 = 1112447) (by norm_num)
theorem B1483789 : Blo 1317977 1483789 := bbase (se 3 (by rfl) ⟨278210, by rfl⟩ : syracuseStep 1483789 = 556421) (by norm_num)
theorem B1483825 : Blo 1317977 1483825 := bbase (se 2 (by rfl) ⟨556434, by rfl⟩ : syracuseStep 1483825 = 1112869) (by norm_num)
theorem B2966597 : Blo 1317977 2966597 := bbase (se 4 (by rfl) ⟨278118, by rfl⟩ : syracuseStep 2966597 = 556237) (by norm_num)
theorem B1483861 : Blo 1317977 1483861 := bbase (se 8 (by rfl) ⟨8694, by rfl⟩ : syracuseStep 1483861 = 17389) (by norm_num)
theorem B1483897 : Blo 1317977 1483897 := bbase (se 2 (by rfl) ⟨556461, by rfl⟩ : syracuseStep 1483897 = 1112923) (by norm_num)
theorem B2966669 : Blo 1317977 2966669 := bbase (se 3 (by rfl) ⟨556250, by rfl⟩ : syracuseStep 2966669 = 1112501) (by norm_num)
theorem B1877141 : Blo 1317977 1877141 := bbase (se 6 (by rfl) ⟨43995, by rfl⟩ : syracuseStep 1877141 = 87991) (by norm_num)
theorem B1483933 : Blo 1317977 1483933 := bbase (se 3 (by rfl) ⟨278237, by rfl⟩ : syracuseStep 1483933 = 556475) (by norm_num)
theorem B1483969 : Blo 1317977 1483969 := bbase (se 2 (by rfl) ⟨556488, by rfl⟩ : syracuseStep 1483969 = 1112977) (by norm_num)
theorem B2966741 : Blo 1317977 2966741 := bbase (se 7 (by rfl) ⟨34766, by rfl⟩ : syracuseStep 2966741 = 69533) (by norm_num)
theorem B1484005 : Blo 1317977 1484005 := bbase (se 4 (by rfl) ⟨139125, by rfl⟩ : syracuseStep 1484005 = 278251) (by norm_num)
theorem B1484041 : Blo 1317977 1484041 := bbase (se 2 (by rfl) ⟨556515, by rfl⟩ : syracuseStep 1484041 = 1113031) (by norm_num)
theorem B2966813 : Blo 1317977 2966813 := bbase (se 3 (by rfl) ⟨556277, by rfl⟩ : syracuseStep 2966813 = 1112555) (by norm_num)
theorem B1484077 : Blo 1317977 1484077 := bbase (se 3 (by rfl) ⟨278264, by rfl⟩ : syracuseStep 1484077 = 556529) (by norm_num)
theorem B2671949 : Blo 1317977 2671949 := bbase (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) (by norm_num)
theorem B1484113 : Blo 1317977 1484113 := bbase (se 2 (by rfl) ⟨556542, by rfl⟩ : syracuseStep 1484113 = 1113085) (by norm_num)
theorem B2966885 : Blo 1317977 2966885 := bbase (se 4 (by rfl) ⟨278145, by rfl⟩ : syracuseStep 2966885 = 556291) (by norm_num)
theorem B4449653 : Blo 1317977 4449653 := bbase (se 5 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 4449653 = 417155) (by norm_num)
theorem B1484149 : Blo 1317977 1484149 := bbase (se 5 (by rfl) ⟨69569, by rfl⟩ : syracuseStep 1484149 = 139139) (by norm_num)
theorem B1484185 : Blo 1317977 1484185 := bbase (se 2 (by rfl) ⟨556569, by rfl⟩ : syracuseStep 1484185 = 1113139) (by norm_num)
theorem B2966957 : Blo 1317977 2966957 := bbase (se 3 (by rfl) ⟨556304, by rfl⟩ : syracuseStep 2966957 = 1112609) (by norm_num)
theorem B10012085 : Blo 1317977 10012085 := bbase (se 5 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 10012085 = 938633) (by norm_num)
theorem B1484221 : Blo 1317977 1484221 := bbase (se 3 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 1484221 = 556583) (by norm_num)
theorem B1484257 : Blo 1317977 1484257 := bbase (se 2 (by rfl) ⟨556596, by rfl⟩ : syracuseStep 1484257 = 1113193) (by norm_num)
theorem B2967029 : Blo 1317977 2967029 := bbase (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) (by norm_num)
theorem B1484293 : Blo 1317977 1484293 := bbase (se 4 (by rfl) ⟨139152, by rfl⟩ : syracuseStep 1484293 = 278305) (by norm_num)
theorem B1484329 : Blo 1317977 1484329 := bbase (se 2 (by rfl) ⟨556623, by rfl⟩ : syracuseStep 1484329 = 1113247) (by norm_num)
theorem B2967101 : Blo 1317977 2967101 := bbase (se 3 (by rfl) ⟨556331, by rfl⟩ : syracuseStep 2967101 = 1112663) (by norm_num)
theorem B1484365 : Blo 1317977 1484365 := bbase (se 3 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 1484365 = 556637) (by norm_num)
theorem B1484401 : Blo 1317977 1484401 := bbase (se 2 (by rfl) ⟨556650, by rfl⟩ : syracuseStep 1484401 = 1113301) (by norm_num)
theorem B2967173 : Blo 1317977 2967173 := bbase (se 4 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 2967173 = 556345) (by norm_num)
theorem B2967245 : Blo 1317977 2967245 := bbase (se 3 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 2967245 = 1112717) (by norm_num)
theorem B2967317 : Blo 1317977 2967317 := bbase (se 6 (by rfl) ⟨69546, by rfl⟩ : syracuseStep 2967317 = 139093) (by norm_num)
theorem B5629733 : Blo 1317977 5629733 := bbase (se 4 (by rfl) ⟨527787, by rfl⟩ : syracuseStep 5629733 = 1055575) (by norm_num)
theorem B4450085 : Blo 1317977 4450085 := bbase (se 4 (by rfl) ⟨417195, by rfl⟩ : syracuseStep 4450085 = 834391) (by norm_num)
theorem B1713997 : Blo 1317977 1713997 := bbase (se 3 (by rfl) ⟨321374, by rfl⟩ : syracuseStep 1713997 = 642749) (by norm_num)
theorem B3008333 : Blo 1317977 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B144385877 : Blo 1317977 144385877 := bbase (se 9 (by rfl) ⟨423005, by rfl⟩ : syracuseStep 144385877 = 846011) (by norm_num)
theorem B117253973 : Blo 1317977 117253973 := bbase (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) (by norm_num)
theorem B2967389 : Blo 1317977 2967389 := bbase (se 3 (by rfl) ⟨556385, by rfl⟩ : syracuseStep 2967389 = 1112771) (by norm_num)
theorem B3008405 : Blo 1317977 3008405 := bbase (se 6 (by rfl) ⟨70509, by rfl⟩ : syracuseStep 3008405 = 141019) (by norm_num)
theorem B2967461 : Blo 1317977 2967461 := bbase (se 4 (by rfl) ⟨278199, by rfl⟩ : syracuseStep 2967461 = 556399) (by norm_num)
theorem B2672581 : Blo 1317977 2672581 := bbase (se 4 (by rfl) ⟨250554, by rfl⟩ : syracuseStep 2672581 = 501109) (by norm_num)
theorem B2967533 : Blo 1317977 2967533 := bbase (se 3 (by rfl) ⟨556412, by rfl⟩ : syracuseStep 2967533 = 1112825) (by norm_num)
theorem B6768629 : Blo 1317977 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B6334469 : Blo 1317977 6334469 := bbase (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) (by norm_num)
theorem B2672645 : Blo 1317977 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B5007365 : Blo 1317977 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B2967605 : Blo 1317977 2967605 := bbase (se 5 (by rfl) ⟨139106, by rfl⟩ : syracuseStep 2967605 = 278213) (by norm_num)
theorem B2967677 : Blo 1317977 2967677 := bbase (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) (by norm_num)
theorem B3336349 : Blo 1317977 3336349 := bbase (se 3 (by rfl) ⟨625565, by rfl⟩ : syracuseStep 3336349 = 1251131) (by norm_num)
theorem B2967749 : Blo 1317977 2967749 := bbase (se 4 (by rfl) ⟨278226, by rfl⟩ : syracuseStep 2967749 = 556453) (by norm_num)
theorem B4450517 : Blo 1317977 4450517 := bbase (se 7 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 4450517 = 104309) (by norm_num)
theorem B4696309 : Blo 1317977 4696309 := bbase (se 5 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 4696309 = 440279) (by norm_num)
theorem B6678773 : Blo 1317977 6678773 := bbase (se 5 (by rfl) ⟨313067, by rfl⟩ : syracuseStep 6678773 = 626135) (by norm_num)
theorem B3336461 : Blo 1317977 3336461 := bbase (se 3 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 3336461 = 1251173) (by norm_num)
theorem B2967821 : Blo 1317977 2967821 := bbase (se 3 (by rfl) ⟨556466, by rfl⟩ : syracuseStep 2967821 = 1112933) (by norm_num)
theorem B5007653 : Blo 1317977 5007653 := bbase (se 4 (by rfl) ⟨469467, by rfl⟩ : syracuseStep 5007653 = 938935) (by norm_num)
theorem B1321285 : Blo 1317977 1321285 := bbase (se 4 (by rfl) ⟨123870, by rfl⟩ : syracuseStep 1321285 = 247741) (by norm_num)
theorem B2967893 : Blo 1317977 2967893 := bbase (se 10 (by rfl) ⟨4347, by rfl⟩ : syracuseStep 2967893 = 8695) (by norm_num)
theorem B2967965 : Blo 1317977 2967965 := bbase (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) (by norm_num)
theorem B3336653 : Blo 1317977 3336653 := bbase (se 3 (by rfl) ⟨625622, by rfl⟩ : syracuseStep 3336653 = 1251245) (by norm_num)
theorem B2968037 : Blo 1317977 2968037 := bbase (se 4 (by rfl) ⟨278253, by rfl⟩ : syracuseStep 2968037 = 556507) (by norm_num)
theorem B1583593 : Blo 1317977 1583593 := bbase (se 2 (by rfl) ⟨593847, by rfl⟩ : syracuseStep 1583593 = 1187695) (by norm_num)
theorem B1878565 : Blo 1317977 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B2968109 : Blo 1317977 2968109 := bbase (se 3 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 2968109 = 1113041) (by norm_num)
theorem B1583713 : Blo 1317977 1583713 := bbase (se 2 (by rfl) ⟨593892, by rfl⟩ : syracuseStep 1583713 = 1187785) (by norm_num)
theorem B3754613 : Blo 1317977 3754613 := bbase (se 5 (by rfl) ⟨175997, by rfl⟩ : syracuseStep 3754613 = 351995) (by norm_num)
theorem B2968181 : Blo 1317977 2968181 := bbase (se 5 (by rfl) ⟨139133, by rfl⟩ : syracuseStep 2968181 = 278267) (by norm_num)
theorem B4450949 : Blo 1317977 4450949 := bbase (se 4 (by rfl) ⟨417276, by rfl⟩ : syracuseStep 4450949 = 834553) (by norm_num)
theorem B1976981 : Blo 1317977 1976981 := bbase (se 6 (by rfl) ⟨46335, by rfl⟩ : syracuseStep 1976981 = 92671) (by norm_num)
theorem B1977005 : Blo 1317977 1977005 := bbase (se 3 (by rfl) ⟨370688, by rfl⟩ : syracuseStep 1977005 = 741377) (by norm_num)
theorem B2968253 : Blo 1317977 2968253 := bbase (se 3 (by rfl) ⟨556547, by rfl⟩ : syracuseStep 2968253 = 1113095) (by norm_num)
theorem B1977029 : Blo 1317977 1977029 := bbase (se 4 (by rfl) ⟨185346, by rfl⟩ : syracuseStep 1977029 = 370693) (by norm_num)
theorem B1977053 : Blo 1317977 1977053 := bbase (se 3 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 1977053 = 741395) (by norm_num)
theorem B1977077 : Blo 1317977 1977077 := bbase (se 5 (by rfl) ⟨92675, by rfl⟩ : syracuseStep 1977077 = 185351) (by norm_num)
theorem B2968325 : Blo 1317977 2968325 := bbase (se 4 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 2968325 = 556561) (by norm_num)
theorem B1977101 : Blo 1317977 1977101 := bbase (se 3 (by rfl) ⟨370706, by rfl⟩ : syracuseStep 1977101 = 741413) (by norm_num)
theorem B5630741 : Blo 1317977 5630741 := bbase (se 6 (by rfl) ⟨131970, by rfl⟩ : syracuseStep 5630741 = 263941) (by norm_num)
theorem B1977125 : Blo 1317977 1977125 := bbase (se 4 (by rfl) ⟨185355, by rfl⟩ : syracuseStep 1977125 = 370711) (by norm_num)
theorem B3336997 : Blo 1317977 3336997 := bbase (se 4 (by rfl) ⟨312843, by rfl⟩ : syracuseStep 3336997 = 625687) (by norm_num)
theorem B1977149 : Blo 1317977 1977149 := bbase (se 3 (by rfl) ⟨370715, by rfl⟩ : syracuseStep 1977149 = 741431) (by norm_num)
theorem B3566405 : Blo 1317977 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B2968397 : Blo 1317977 2968397 := bbase (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) (by norm_num)
theorem B1977173 : Blo 1317977 1977173 := bbase (se 9 (by rfl) ⟨5792, by rfl⟩ : syracuseStep 1977173 = 11585) (by norm_num)
theorem B1977197 : Blo 1317977 1977197 := bbase (se 3 (by rfl) ⟨370724, by rfl⟩ : syracuseStep 1977197 = 741449) (by norm_num)
theorem B1977221 : Blo 1317977 1977221 := bbase (se 4 (by rfl) ⟨185364, by rfl⟩ : syracuseStep 1977221 = 370729) (by norm_num)
theorem B3337109 : Blo 1317977 3337109 := bbase (se 6 (by rfl) ⟨78213, by rfl⟩ : syracuseStep 3337109 = 156427) (by norm_num)
theorem B2968469 : Blo 1317977 2968469 := bbase (se 6 (by rfl) ⟨69573, by rfl⟩ : syracuseStep 2968469 = 139147) (by norm_num)
theorem B1977245 : Blo 1317977 1977245 := bbase (se 3 (by rfl) ⟨370733, by rfl⟩ : syracuseStep 1977245 = 741467) (by norm_num)
theorem B1977269 : Blo 1317977 1977269 := bbase (se 5 (by rfl) ⟨92684, by rfl⟩ : syracuseStep 1977269 = 185369) (by norm_num)
theorem B1977293 : Blo 1317977 1977293 := bbase (se 3 (by rfl) ⟨370742, by rfl⟩ : syracuseStep 1977293 = 741485) (by norm_num)
theorem B22539221 : Blo 1317977 22539221 := bbase (se 7 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 22539221 = 528263) (by norm_num)
theorem B2968541 : Blo 1317977 2968541 := bbase (se 3 (by rfl) ⟨556601, by rfl⟩ : syracuseStep 2968541 = 1113203) (by norm_num)
theorem B1977317 : Blo 1317977 1977317 := bbase (se 4 (by rfl) ⟨185373, by rfl⟩ : syracuseStep 1977317 = 370747) (by norm_num)
theorem B1977341 : Blo 1317977 1977341 := bbase (se 3 (by rfl) ⟨370751, by rfl⟩ : syracuseStep 1977341 = 741503) (by norm_num)
theorem B1977365 : Blo 1317977 1977365 := bbase (se 6 (by rfl) ⟨46344, by rfl⟩ : syracuseStep 1977365 = 92689) (by norm_num)
theorem B12028949 : Blo 1317977 12028949 := bbase (se 6 (by rfl) ⟨281928, by rfl⟩ : syracuseStep 12028949 = 563857) (by norm_num)
theorem B2968613 : Blo 1317977 2968613 := bbase (se 4 (by rfl) ⟨278307, by rfl⟩ : syracuseStep 2968613 = 556615) (by norm_num)
theorem B1977389 : Blo 1317977 1977389 := bbase (se 3 (by rfl) ⟨370760, by rfl⟩ : syracuseStep 1977389 = 741521) (by norm_num)
theorem B4451381 : Blo 1317977 4451381 := bbase (se 5 (by rfl) ⟨208658, by rfl⟩ : syracuseStep 4451381 = 417317) (by norm_num)
theorem B1977413 : Blo 1317977 1977413 := bbase (se 4 (by rfl) ⟨185382, by rfl⟩ : syracuseStep 1977413 = 370765) (by norm_num)
theorem B3337301 : Blo 1317977 3337301 := bbase (se 8 (by rfl) ⟨19554, by rfl⟩ : syracuseStep 3337301 = 39109) (by norm_num)
theorem B1977437 : Blo 1317977 1977437 := bbase (se 3 (by rfl) ⟨370769, by rfl⟩ : syracuseStep 1977437 = 741539) (by norm_num)
theorem B2968685 : Blo 1317977 2968685 := bbase (se 3 (by rfl) ⟨556628, by rfl⟩ : syracuseStep 2968685 = 1113257) (by norm_num)
theorem B1977461 : Blo 1317977 1977461 := bbase (se 5 (by rfl) ⟨92693, by rfl⟩ : syracuseStep 1977461 = 185387) (by norm_num)
theorem B6335621 : Blo 1317977 6335621 := bbase (se 4 (by rfl) ⟨593964, by rfl⟩ : syracuseStep 6335621 = 1187929) (by norm_num)
theorem B2256005 : Blo 1317977 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B1977485 : Blo 1317977 1977485 := bbase (se 3 (by rfl) ⟨370778, by rfl⟩ : syracuseStep 1977485 = 741557) (by norm_num)
theorem B1977509 : Blo 1317977 1977509 := bbase (se 4 (by rfl) ⟨185391, by rfl⟩ : syracuseStep 1977509 = 370783) (by norm_num)
theorem B2968757 : Blo 1317977 2968757 := bbase (se 5 (by rfl) ⟨139160, by rfl⟩ : syracuseStep 2968757 = 278321) (by norm_num)
theorem B1977533 : Blo 1317977 1977533 := bbase (se 3 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 1977533 = 741575) (by norm_num)
theorem B4754629 : Blo 1317977 4754629 := bbase (se 4 (by rfl) ⟨445746, by rfl⟩ : syracuseStep 4754629 = 891493) (by norm_num)
theorem B1977557 : Blo 1317977 1977557 := bbase (se 7 (by rfl) ⟨23174, by rfl⟩ : syracuseStep 1977557 = 46349) (by norm_num)
theorem B1690853 : Blo 1317977 1690853 := bbase (se 4 (by rfl) ⟨158517, by rfl⟩ : syracuseStep 1690853 = 317035) (by norm_num)
theorem B1977581 : Blo 1317977 1977581 := bbase (se 3 (by rfl) ⟨370796, by rfl⟩ : syracuseStep 1977581 = 741593) (by norm_num)
theorem B1977605 : Blo 1317977 1977605 := bbase (se 4 (by rfl) ⟨185400, by rfl⟩ : syracuseStep 1977605 = 370801) (by norm_num)
theorem B3755285 : Blo 1317977 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B1977629 : Blo 1317977 1977629 := bbase (se 3 (by rfl) ⟨370805, by rfl⟩ : syracuseStep 1977629 = 741611) (by norm_num)
theorem B1977653 : Blo 1317977 1977653 := bbase (se 5 (by rfl) ⟨92702, by rfl⟩ : syracuseStep 1977653 = 185405) (by norm_num)
theorem B1977677 : Blo 1317977 1977677 := bbase (se 3 (by rfl) ⟨370814, by rfl⟩ : syracuseStep 1977677 = 741629) (by norm_num)
theorem B1977701 : Blo 1317977 1977701 := bbase (se 4 (by rfl) ⟨185409, by rfl⟩ : syracuseStep 1977701 = 370819) (by norm_num)
theorem B1977725 : Blo 1317977 1977725 := bbase (se 3 (by rfl) ⟨370823, by rfl⟩ : syracuseStep 1977725 = 741647) (by norm_num)
theorem B1977749 : Blo 1317977 1977749 := bbase (se 6 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 1977749 = 92707) (by norm_num)
theorem B15027605 : Blo 1317977 15027605 := bbase (se 6 (by rfl) ⟨352209, by rfl⟩ : syracuseStep 15027605 = 704419) (by norm_num)
theorem B1355177 : Blo 1317977 1355177 := bbase (se 2 (by rfl) ⟨508191, by rfl⟩ : syracuseStep 1355177 = 1016383) (by norm_num)
theorem B1977773 : Blo 1317977 1977773 := bbase (se 3 (by rfl) ⟨370832, by rfl⟩ : syracuseStep 1977773 = 741665) (by norm_num)
theorem B3337645 : Blo 1317977 3337645 := bbase (se 3 (by rfl) ⟨625808, by rfl⟩ : syracuseStep 3337645 = 1251617) (by norm_num)
theorem B1584569 : Blo 1317977 1584569 := bbase (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) (by norm_num)
theorem B1977797 : Blo 1317977 1977797 := bbase (se 4 (by rfl) ⟨185418, by rfl⟩ : syracuseStep 1977797 = 370837) (by norm_num)
theorem B5008837 : Blo 1317977 5008837 := bbase (se 4 (by rfl) ⟨469578, by rfl⟩ : syracuseStep 5008837 = 939157) (by norm_num)
theorem B1977821 : Blo 1317977 1977821 := bbase (se 3 (by rfl) ⟨370841, by rfl⟩ : syracuseStep 1977821 = 741683) (by norm_num)
theorem B4451813 : Blo 1317977 4451813 := bbase (se 4 (by rfl) ⟨417357, by rfl⟩ : syracuseStep 4451813 = 834715) (by norm_num)
theorem B1977845 : Blo 1317977 1977845 := bbase (se 5 (by rfl) ⟨92711, by rfl⟩ : syracuseStep 1977845 = 185423) (by norm_num)
theorem B4754933 : Blo 1317977 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B1977869 : Blo 1317977 1977869 := bbase (se 3 (by rfl) ⟨370850, by rfl⟩ : syracuseStep 1977869 = 741701) (by norm_num)
theorem B3337757 : Blo 1317977 3337757 := bbase (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) (by norm_num)
theorem B1977893 : Blo 1317977 1977893 := bbase (se 4 (by rfl) ⟨185427, by rfl⟩ : syracuseStep 1977893 = 370855) (by norm_num)
theorem B1977917 : Blo 1317977 1977917 := bbase (se 3 (by rfl) ⟨370859, by rfl⟩ : syracuseStep 1977917 = 741719) (by norm_num)
theorem B4951621 : Blo 1317977 4951621 := bbase (se 4 (by rfl) ⟨464214, by rfl⟩ : syracuseStep 4951621 = 928429) (by norm_num)
theorem B1977941 : Blo 1317977 1977941 := bbase (se 8 (by rfl) ⟨11589, by rfl⟩ : syracuseStep 1977941 = 23179) (by norm_num)
theorem B1977965 : Blo 1317977 1977965 := bbase (se 3 (by rfl) ⟨370868, by rfl⟩ : syracuseStep 1977965 = 741737) (by norm_num)
theorem B1977989 : Blo 1317977 1977989 := bbase (se 4 (by rfl) ⟨185436, by rfl⟩ : syracuseStep 1977989 = 370873) (by norm_num)
theorem B1978013 : Blo 1317977 1978013 := bbase (se 3 (by rfl) ⟨370877, by rfl⟩ : syracuseStep 1978013 = 741755) (by norm_num)
theorem B1978037 : Blo 1317977 1978037 := bbase (se 5 (by rfl) ⟨92720, by rfl⟩ : syracuseStep 1978037 = 185441) (by norm_num)
theorem B3755717 : Blo 1317977 3755717 := bbase (se 4 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 3755717 = 704197) (by norm_num)
theorem B1978061 : Blo 1317977 1978061 := bbase (se 3 (by rfl) ⟨370886, by rfl⟩ : syracuseStep 1978061 = 741773) (by norm_num)
theorem B3337949 : Blo 1317977 3337949 := bbase (se 3 (by rfl) ⟨625865, by rfl⟩ : syracuseStep 3337949 = 1251731) (by norm_num)
theorem B1978085 : Blo 1317977 1978085 := bbase (se 4 (by rfl) ⟨185445, by rfl⟩ : syracuseStep 1978085 = 370891) (by norm_num)
theorem B5009141 : Blo 1317977 5009141 := bbase (se 5 (by rfl) ⟨234803, by rfl⟩ : syracuseStep 5009141 = 469607) (by norm_num)
theorem B1978109 : Blo 1317977 1978109 := bbase (se 3 (by rfl) ⟨370895, by rfl⟩ : syracuseStep 1978109 = 741791) (by norm_num)
theorem B1978133 : Blo 1317977 1978133 := bbase (se 6 (by rfl) ⟨46362, by rfl⟩ : syracuseStep 1978133 = 92725) (by norm_num)
theorem B1978157 : Blo 1317977 1978157 := bbase (se 3 (by rfl) ⟨370904, by rfl⟩ : syracuseStep 1978157 = 741809) (by norm_num)
theorem B2748205 : Blo 1317977 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B1978181 : Blo 1317977 1978181 := bbase (se 4 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 1978181 = 370909) (by norm_num)
theorem B1929053 : Blo 1317977 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B1978205 : Blo 1317977 1978205 := bbase (se 3 (by rfl) ⟨370913, by rfl⟩ : syracuseStep 1978205 = 741827) (by norm_num)
theorem B1978229 : Blo 1317977 1978229 := bbase (se 5 (by rfl) ⟨92729, by rfl⟩ : syracuseStep 1978229 = 185459) (by norm_num)
theorem B6336389 : Blo 1317977 6336389 := bbase (se 4 (by rfl) ⟨594036, by rfl⟩ : syracuseStep 6336389 = 1188073) (by norm_num)
theorem B1978253 : Blo 1317977 1978253 := bbase (se 3 (by rfl) ⟨370922, by rfl⟩ : syracuseStep 1978253 = 741845) (by norm_num)
theorem B1806229 : Blo 1317977 1806229 := bbase (se 6 (by rfl) ⟨42333, by rfl⟩ : syracuseStep 1806229 = 84667) (by norm_num)
theorem B4452245 : Blo 1317977 4452245 := bbase (se 6 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 4452245 = 208699) (by norm_num)
theorem B6672293 : Blo 1317977 6672293 := bbase (se 4 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 6672293 = 1251055) (by norm_num)
theorem B1978277 : Blo 1317977 1978277 := bbase (se 4 (by rfl) ⟨185463, by rfl⟩ : syracuseStep 1978277 = 370927) (by norm_num)
theorem B2502589 : Blo 1317977 2502589 := bbase (se 3 (by rfl) ⟨469235, by rfl⟩ : syracuseStep 2502589 = 938471) (by norm_num)
theorem B1978301 : Blo 1317977 1978301 := bbase (se 3 (by rfl) ⟨370931, by rfl⟩ : syracuseStep 1978301 = 741863) (by norm_num)
theorem B1978325 : Blo 1317977 1978325 := bbase (se 7 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 1978325 = 46367) (by norm_num)
theorem B1978349 : Blo 1317977 1978349 := bbase (se 3 (by rfl) ⟨370940, by rfl⟩ : syracuseStep 1978349 = 741881) (by norm_num)
theorem B1978373 : Blo 1317977 1978373 := bbase (se 4 (by rfl) ⟨185472, by rfl⟩ : syracuseStep 1978373 = 370945) (by norm_num)
theorem B16904213 : Blo 1317977 16904213 := bbase (se 6 (by rfl) ⟨396192, by rfl⟩ : syracuseStep 16904213 = 792385) (by norm_num)
theorem B1978397 : Blo 1317977 1978397 := bbase (se 3 (by rfl) ⟨370949, by rfl⟩ : syracuseStep 1978397 = 741899) (by norm_num)
theorem B2224165 : Blo 1317977 2224165 := bbase (se 4 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 2224165 = 417031) (by norm_num)
theorem B4223029 : Blo 1317977 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B3338293 : Blo 1317977 3338293 := bbase (se 5 (by rfl) ⟨156482, by rfl⟩ : syracuseStep 3338293 = 312965) (by norm_num)
theorem B1978421 : Blo 1317977 1978421 := bbase (se 5 (by rfl) ⟨92738, by rfl⟩ : syracuseStep 1978421 = 185477) (by norm_num)
theorem B2502733 : Blo 1317977 2502733 := bbase (se 3 (by rfl) ⟨469262, by rfl⟩ : syracuseStep 2502733 = 938525) (by norm_num)
theorem B1978445 : Blo 1317977 1978445 := bbase (se 3 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 1978445 = 741917) (by norm_num)
theorem B1978469 : Blo 1317977 1978469 := bbase (se 4 (by rfl) ⟨185481, by rfl⟩ : syracuseStep 1978469 = 370963) (by norm_num)
theorem B2224253 : Blo 1317977 2224253 := bbase (se 3 (by rfl) ⟨417047, by rfl⟩ : syracuseStep 2224253 = 834095) (by norm_num)
theorem B1978493 : Blo 1317977 1978493 := bbase (se 3 (by rfl) ⟨370967, by rfl⟩ : syracuseStep 1978493 = 741935) (by norm_num)
theorem B8564885 : Blo 1317977 8564885 := bbase (se 6 (by rfl) ⟨200739, by rfl⟩ : syracuseStep 8564885 = 401479) (by norm_num)
theorem B1978517 : Blo 1317977 1978517 := bbase (se 6 (by rfl) ⟨46371, by rfl⟩ : syracuseStep 1978517 = 92743) (by norm_num)
theorem B3338405 : Blo 1317977 3338405 := bbase (se 4 (by rfl) ⟨312975, by rfl⟩ : syracuseStep 3338405 = 625951) (by norm_num)
theorem B1978541 : Blo 1317977 1978541 := bbase (se 3 (by rfl) ⟨370976, by rfl⟩ : syracuseStep 1978541 = 741953) (by norm_num)
theorem B1978565 : Blo 1317977 1978565 := bbase (se 4 (by rfl) ⟨185490, by rfl⟩ : syracuseStep 1978565 = 370981) (by norm_num)
theorem B1978589 : Blo 1317977 1978589 := bbase (se 3 (by rfl) ⟨370985, by rfl⟩ : syracuseStep 1978589 = 741971) (by norm_num)
theorem B2502893 : Blo 1317977 2502893 := bbase (se 3 (by rfl) ⟨469292, by rfl⟩ : syracuseStep 2502893 = 938585) (by norm_num)
theorem B1503469 : Blo 1317977 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1978613 : Blo 1317977 1978613 := bbase (se 5 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 1978613 = 185495) (by norm_num)
theorem B2224381 : Blo 1317977 2224381 := bbase (se 3 (by rfl) ⟨417071, by rfl⟩ : syracuseStep 2224381 = 834143) (by norm_num)
theorem B2674949 : Blo 1317977 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B1978637 : Blo 1317977 1978637 := bbase (se 3 (by rfl) ⟨370994, by rfl⟩ : syracuseStep 1978637 = 741989) (by norm_num)
theorem B1978661 : Blo 1317977 1978661 := bbase (se 4 (by rfl) ⟨185499, by rfl⟩ : syracuseStep 1978661 = 370999) (by norm_num)
theorem B1978685 : Blo 1317977 1978685 := bbase (se 3 (by rfl) ⟨371003, by rfl⟩ : syracuseStep 1978685 = 742007) (by norm_num)
theorem B4452677 : Blo 1317977 4452677 := bbase (se 4 (by rfl) ⟨417438, by rfl⟩ : syracuseStep 4452677 = 834877) (by norm_num)
theorem B2224469 : Blo 1317977 2224469 := bbase (se 10 (by rfl) ⟨3258, by rfl⟩ : syracuseStep 2224469 = 6517) (by norm_num)
theorem B1978709 : Blo 1317977 1978709 := bbase (se 10 (by rfl) ⟨2898, by rfl⟩ : syracuseStep 1978709 = 5797) (by norm_num)
theorem B3338597 : Blo 1317977 3338597 := bbase (se 4 (by rfl) ⟨312993, by rfl⟩ : syracuseStep 3338597 = 625987) (by norm_num)
theorem B1978733 : Blo 1317977 1978733 := bbase (se 3 (by rfl) ⟨371012, by rfl⟩ : syracuseStep 1978733 = 742025) (by norm_num)
theorem B2503037 : Blo 1317977 2503037 := bbase (se 3 (by rfl) ⟨469319, by rfl⟩ : syracuseStep 2503037 = 938639) (by norm_num)
theorem B1978757 : Blo 1317977 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B1978781 : Blo 1317977 1978781 := bbase (se 3 (by rfl) ⟨371021, by rfl⟩ : syracuseStep 1978781 = 742043) (by norm_num)
theorem B3756469 : Blo 1317977 3756469 := bbase (se 5 (by rfl) ⟨176084, by rfl⟩ : syracuseStep 3756469 = 352169) (by norm_num)
theorem B1978805 : Blo 1317977 1978805 := bbase (se 5 (by rfl) ⟨92756, by rfl⟩ : syracuseStep 1978805 = 185513) (by norm_num)
theorem B1978829 : Blo 1317977 1978829 := bbase (se 3 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 1978829 = 742061) (by norm_num)
theorem B2224597 : Blo 1317977 2224597 := bbase (se 7 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 2224597 = 52139) (by norm_num)
theorem B1978853 : Blo 1317977 1978853 := bbase (se 4 (by rfl) ⟨185517, by rfl⟩ : syracuseStep 1978853 = 371035) (by norm_num)
theorem B1978877 : Blo 1317977 1978877 := bbase (se 3 (by rfl) ⟨371039, by rfl⟩ : syracuseStep 1978877 = 742079) (by norm_num)
theorem B5632517 : Blo 1317977 5632517 := bbase (se 4 (by rfl) ⟨528048, by rfl⟩ : syracuseStep 5632517 = 1056097) (by norm_num)
theorem B1978901 : Blo 1317977 1978901 := bbase (se 6 (by rfl) ⟨46380, by rfl⟩ : syracuseStep 1978901 = 92761) (by norm_num)
theorem B2224685 : Blo 1317977 2224685 := bbase (se 3 (by rfl) ⟨417128, by rfl⟩ : syracuseStep 2224685 = 834257) (by norm_num)
theorem B1978925 : Blo 1317977 1978925 := bbase (se 3 (by rfl) ⟨371048, by rfl⟩ : syracuseStep 1978925 = 742097) (by norm_num)
theorem B1978949 : Blo 1317977 1978949 := bbase (se 4 (by rfl) ⟨185526, by rfl⟩ : syracuseStep 1978949 = 371053) (by norm_num)
theorem B1978973 : Blo 1317977 1978973 := bbase (se 3 (by rfl) ⟨371057, by rfl⟩ : syracuseStep 1978973 = 742115) (by norm_num)
theorem B7713397 : Blo 1317977 7713397 := bbase (se 5 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 7713397 = 723131) (by norm_num)
theorem B1978997 : Blo 1317977 1978997 := bbase (se 5 (by rfl) ⟨92765, by rfl⟩ : syracuseStep 1978997 = 185531) (by norm_num)
theorem B1979021 : Blo 1317977 1979021 := bbase (se 3 (by rfl) ⟨371066, by rfl⟩ : syracuseStep 1979021 = 742133) (by norm_num)
theorem B2503325 : Blo 1317977 2503325 := bbase (se 3 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 2503325 = 938747) (by norm_num)
theorem B1979045 : Blo 1317977 1979045 := bbase (se 4 (by rfl) ⟨185535, by rfl⟩ : syracuseStep 1979045 = 371071) (by norm_num)
theorem B2224813 : Blo 1317977 2224813 := bbase (se 3 (by rfl) ⟨417152, by rfl⟩ : syracuseStep 2224813 = 834305) (by norm_num)
theorem B13718197 : Blo 1317977 13718197 := bbase (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) (by norm_num)
theorem B3338941 : Blo 1317977 3338941 := bbase (se 3 (by rfl) ⟨626051, by rfl⟩ : syracuseStep 3338941 = 1252103) (by norm_num)
theorem B1979069 : Blo 1317977 1979069 := bbase (se 3 (by rfl) ⟨371075, by rfl⟩ : syracuseStep 1979069 = 742151) (by norm_num)
theorem B1979093 : Blo 1317977 1979093 := bbase (se 7 (by rfl) ⟨23192, by rfl⟩ : syracuseStep 1979093 = 46385) (by norm_num)
theorem B1954541 : Blo 1317977 1954541 := bbase (se 3 (by rfl) ⟨366476, by rfl⟩ : syracuseStep 1954541 = 732953) (by norm_num)
theorem B1979117 : Blo 1317977 1979117 := bbase (se 3 (by rfl) ⟨371084, by rfl⟩ : syracuseStep 1979117 = 742169) (by norm_num)
theorem B1807093 : Blo 1317977 1807093 := bbase (se 5 (by rfl) ⟨84707, by rfl⟩ : syracuseStep 1807093 = 169415) (by norm_num)
theorem B4453109 : Blo 1317977 4453109 := bbase (se 5 (by rfl) ⟨208739, by rfl⟩ : syracuseStep 4453109 = 417479) (by norm_num)
theorem B2224901 : Blo 1317977 2224901 := bbase (se 4 (by rfl) ⟨208584, by rfl⟩ : syracuseStep 2224901 = 417169) (by norm_num)
theorem B1979141 : Blo 1317977 1979141 := bbase (se 4 (by rfl) ⟨185544, by rfl⟩ : syracuseStep 1979141 = 371089) (by norm_num)
theorem B1979165 : Blo 1317977 1979165 := bbase (se 3 (by rfl) ⟨371093, by rfl⟩ : syracuseStep 1979165 = 742187) (by norm_num)
theorem B3339053 : Blo 1317977 3339053 := bbase (se 3 (by rfl) ⟨626072, by rfl⟩ : syracuseStep 3339053 = 1252145) (by norm_num)
theorem B2503477 : Blo 1317977 2503477 := bbase (se 5 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 2503477 = 234701) (by norm_num)
theorem B1979189 : Blo 1317977 1979189 := bbase (se 5 (by rfl) ⟨92774, by rfl⟩ : syracuseStep 1979189 = 185549) (by norm_num)
theorem B1504057 : Blo 1317977 1504057 := bbase (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) (by norm_num)
theorem B1979213 : Blo 1317977 1979213 := bbase (se 3 (by rfl) ⟨371102, by rfl⟩ : syracuseStep 1979213 = 742205) (by norm_num)
theorem B2225029 : Blo 1317977 2225029 := bbase (se 4 (by rfl) ⟨208596, by rfl⟩ : syracuseStep 2225029 = 417193) (by norm_num)
theorem B4010917 : Blo 1317977 4010917 := bbase (se 4 (by rfl) ⟨376023, by rfl⟩ : syracuseStep 4010917 = 752047) (by norm_num)
theorem B4281269 : Blo 1317977 4281269 := bbase (se 5 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 4281269 = 401369) (by norm_num)
theorem B2225117 : Blo 1317977 2225117 := bbase (se 3 (by rfl) ⟨417209, by rfl⟩ : syracuseStep 2225117 = 834419) (by norm_num)
theorem B3339245 : Blo 1317977 3339245 := bbase (se 3 (by rfl) ⟨626108, by rfl⟩ : syracuseStep 3339245 = 1252217) (by norm_num)
theorem B1668109 : Blo 1317977 1668109 := bbase (se 3 (by rfl) ⟨312770, by rfl⟩ : syracuseStep 1668109 = 625541) (by norm_num)
theorem B4011061 : Blo 1317977 4011061 := bbase (se 5 (by rfl) ⟨188018, by rfl⟩ : syracuseStep 4011061 = 376037) (by norm_num)
theorem B5706821 : Blo 1317977 5706821 := bbase (se 4 (by rfl) ⟨535014, by rfl⟩ : syracuseStep 5706821 = 1070029) (by norm_num)
theorem B1504345 : Blo 1317977 1504345 := bbase (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) (by norm_num)
theorem B2225245 : Blo 1317977 2225245 := bbase (se 3 (by rfl) ⟨417233, by rfl⟩ : syracuseStep 2225245 = 834467) (by norm_num)
theorem B2503781 : Blo 1317977 2503781 := bbase (se 4 (by rfl) ⟨234729, by rfl⟩ : syracuseStep 2503781 = 469459) (by norm_num)
theorem B1668205 : Blo 1317977 1668205 := bbase (se 3 (by rfl) ⟨312788, by rfl⟩ : syracuseStep 1668205 = 625577) (by norm_num)
theorem B6673589 : Blo 1317977 6673589 := bbase (se 5 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 6673589 = 625649) (by norm_num)
theorem B2225333 : Blo 1317977 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B2815165 : Blo 1317977 2815165 := bbase (se 3 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 2815165 = 1055687) (by norm_num)
theorem B1668377 : Blo 1317977 1668377 := bbase (se 2 (by rfl) ⟨625641, by rfl⟩ : syracuseStep 1668377 = 1251283) (by norm_num)
theorem B2225461 : Blo 1317977 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B3339589 : Blo 1317977 3339589 := bbase (se 4 (by rfl) ⟨313086, by rfl⟩ : syracuseStep 3339589 = 626173) (by norm_num)
theorem B1668433 : Blo 1317977 1668433 := bbase (se 2 (by rfl) ⟨625662, by rfl⟩ : syracuseStep 1668433 = 1251325) (by norm_num)
theorem B2225549 : Blo 1317977 2225549 := bbase (se 3 (by rfl) ⟨417290, by rfl⟩ : syracuseStep 2225549 = 834581) (by norm_num)
theorem B1668529 : Blo 1317977 1668529 := bbase (se 2 (by rfl) ⟨625698, by rfl⟩ : syracuseStep 1668529 = 1251397) (by norm_num)
theorem B3339701 : Blo 1317977 3339701 := bbase (se 5 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 3339701 = 313097) (by norm_num)
theorem B2225677 : Blo 1317977 2225677 := bbase (se 3 (by rfl) ⟨417314, by rfl⟩ : syracuseStep 2225677 = 834629) (by norm_num)
theorem B1668701 : Blo 1317977 1668701 := bbase (se 3 (by rfl) ⟨312881, by rfl⟩ : syracuseStep 1668701 = 625763) (by norm_num)
theorem B2225765 : Blo 1317977 2225765 := bbase (se 4 (by rfl) ⟨208665, by rfl⟩ : syracuseStep 2225765 = 417331) (by norm_num)
theorem B3339893 : Blo 1317977 3339893 := bbase (se 5 (by rfl) ⟨156557, by rfl⟩ : syracuseStep 3339893 = 313115) (by norm_num)
theorem B1668757 : Blo 1317977 1668757 := bbase (se 6 (by rfl) ⟨39111, by rfl⟩ : syracuseStep 1668757 = 78223) (by norm_num)
theorem B5346965 : Blo 1317977 5346965 := bbase (se 6 (by rfl) ⟨125319, by rfl⟩ : syracuseStep 5346965 = 250639) (by norm_num)
theorem B2815661 : Blo 1317977 2815661 := bbase (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) (by norm_num)
theorem B2225893 : Blo 1317977 2225893 := bbase (se 4 (by rfl) ⟨208677, by rfl⟩ : syracuseStep 2225893 = 417355) (by norm_num)
theorem B1668853 : Blo 1317977 1668853 := bbase (se 5 (by rfl) ⟨78227, by rfl⟩ : syracuseStep 1668853 = 156455) (by norm_num)
theorem B5420789 : Blo 1317977 5420789 := bbase (se 5 (by rfl) ⟨254099, by rfl⟩ : syracuseStep 5420789 = 508199) (by norm_num)
theorem B2225981 : Blo 1317977 2225981 := bbase (se 3 (by rfl) ⟨417371, by rfl⟩ : syracuseStep 2225981 = 834743) (by norm_num)
theorem B2504533 : Blo 1317977 2504533 := bbase (se 9 (by rfl) ⟨7337, by rfl⟩ : syracuseStep 2504533 = 14675) (by norm_num)
theorem B3168109 : Blo 1317977 3168109 := bbase (se 3 (by rfl) ⟨594020, by rfl⟩ : syracuseStep 3168109 = 1188041) (by norm_num)
theorem B1669025 : Blo 1317977 1669025 := bbase (se 2 (by rfl) ⟨625884, by rfl⟩ : syracuseStep 1669025 = 1251769) (by norm_num)
theorem B2226109 : Blo 1317977 2226109 := bbase (se 3 (by rfl) ⟨417395, by rfl⟩ : syracuseStep 2226109 = 834791) (by norm_num)
theorem B1669081 : Blo 1317977 1669081 := bbase (se 2 (by rfl) ⟨625905, by rfl⟩ : syracuseStep 1669081 = 1251811) (by norm_num)
theorem B2504677 : Blo 1317977 2504677 := bbase (se 4 (by rfl) ⟨234813, by rfl⟩ : syracuseStep 2504677 = 469627) (by norm_num)
theorem B2226197 : Blo 1317977 2226197 := bbase (se 6 (by rfl) ⟨52176, by rfl⟩ : syracuseStep 2226197 = 104353) (by norm_num)
theorem B1669177 : Blo 1317977 1669177 := bbase (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) (by norm_num)
theorem B2005069 : Blo 1317977 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B3168341 : Blo 1317977 3168341 := bbase (se 8 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 3168341 = 37129) (by norm_num)
theorem B2504837 : Blo 1317977 2504837 := bbase (se 4 (by rfl) ⟨234828, by rfl⟩ : syracuseStep 2504837 = 469657) (by norm_num)
theorem B2226325 : Blo 1317977 2226325 := bbase (se 6 (by rfl) ⟨52179, by rfl⟩ : syracuseStep 2226325 = 104359) (by norm_num)
theorem B4012229 : Blo 1317977 4012229 := bbase (se 4 (by rfl) ⟨376146, by rfl⟩ : syracuseStep 4012229 = 752293) (by norm_num)
theorem B17832149 : Blo 1317977 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B1669349 : Blo 1317977 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B2226413 : Blo 1317977 2226413 := bbase (se 3 (by rfl) ⟨417452, by rfl⟩ : syracuseStep 2226413 = 834905) (by norm_num)
theorem B1669405 : Blo 1317977 1669405 := bbase (se 3 (by rfl) ⟨313013, by rfl⟩ : syracuseStep 1669405 = 626027) (by norm_num)
theorem B2226541 : Blo 1317977 2226541 := bbase (se 3 (by rfl) ⟨417476, by rfl⟩ : syracuseStep 2226541 = 834953) (by norm_num)
theorem B1669501 : Blo 1317977 1669501 := bbase (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) (by norm_num)
theorem B6674885 : Blo 1317977 6674885 := bbase (se 4 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 6674885 = 1251541) (by norm_num)
theorem B3807701 : Blo 1317977 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B3168733 : Blo 1317977 3168733 := bbase (se 3 (by rfl) ⟨594137, by rfl⟩ : syracuseStep 3168733 = 1188275) (by norm_num)
theorem B2111989 : Blo 1317977 2111989 := bbase (se 5 (by rfl) ⟨98999, by rfl⟩ : syracuseStep 2111989 = 197999) (by norm_num)
theorem B2005501 : Blo 1317977 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B2816549 : Blo 1317977 2816549 := bbase (se 4 (by rfl) ⟨264051, by rfl⟩ : syracuseStep 2816549 = 528103) (by norm_num)
theorem B1669673 : Blo 1317977 1669673 := bbase (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) (by norm_num)
theorem B1407557 : Blo 1317977 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1669729 : Blo 1317977 1669729 := bbase (se 2 (by rfl) ⟨626148, by rfl⟩ : syracuseStep 1669729 = 1252297) (by norm_num)
theorem B2816669 : Blo 1317977 2816669 := bbase (se 3 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 2816669 = 1056251) (by norm_num)
theorem B1669825 : Blo 1317977 1669825 := bbase (se 2 (by rfl) ⟨626184, by rfl⟩ : syracuseStep 1669825 = 1252369) (by norm_num)
theorem B2112437 : Blo 1317977 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B1408001 : Blo 1317977 1408001 := bbase (se 2 (by rfl) ⟨528000, by rfl⟩ : syracuseStep 1408001 = 1056001) (by norm_num)
theorem B4815877 : Blo 1317977 4815877 := bbase (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) (by norm_num)
theorem B1408061 : Blo 1317977 1408061 := bbase (se 3 (by rfl) ⟨264011, by rfl⟩ : syracuseStep 1408061 = 528023) (by norm_num)
theorem B2112637 : Blo 1317977 2112637 := bbase (se 3 (by rfl) ⟨396119, by rfl⟩ : syracuseStep 2112637 = 792239) (by norm_num)
theorem B1408189 : Blo 1317977 1408189 := bbase (se 3 (by rfl) ⟨264035, by rfl⟩ : syracuseStep 1408189 = 528071) (by norm_num)
theorem B2817301 : Blo 1317977 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B2112893 : Blo 1317977 2112893 := bbase (se 3 (by rfl) ⟨396167, by rfl⟩ : syracuseStep 2112893 = 792335) (by norm_num)
theorem B4513157 : Blo 1317977 4513157 := bbase (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) (by norm_num)
theorem B3612053 : Blo 1317977 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B3169829 : Blo 1317977 3169829 := bbase (se 4 (by rfl) ⟨297171, by rfl⟩ : syracuseStep 3169829 = 594343) (by norm_num)
theorem B1408633 : Blo 1317977 1408633 := bbase (se 2 (by rfl) ⟨528237, by rfl⟩ : syracuseStep 1408633 = 1056475) (by norm_num)
theorem B3210877 : Blo 1317977 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B5004949 : Blo 1317977 5004949 := bbase (se 6 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 5004949 = 234607) (by norm_num)
theorem B2375333 : Blo 1317977 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B6676181 : Blo 1317977 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B1408753 : Blo 1317977 1408753 := bbase (se 2 (by rfl) ⟨528282, by rfl⟩ : syracuseStep 1408753 = 1056565) (by norm_num)
theorem B3170117 : Blo 1317977 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B5005253 : Blo 1317977 5005253 := bbase (se 4 (by rfl) ⟨469242, by rfl⟩ : syracuseStep 5005253 = 938485) (by norm_num)
theorem B1409005 : Blo 1317977 1409005 := bbase (se 3 (by rfl) ⟨264188, by rfl⟩ : syracuseStep 1409005 = 528377) (by norm_num)
theorem B1409009 : Blo 1317977 1409009 := bbase (se 2 (by rfl) ⟨528378, by rfl⟩ : syracuseStep 1409009 = 1056757) (by norm_num)
theorem B1482745 : Blo 1317977 1482745 := bbase (se 2 (by rfl) ⟨556029, by rfl⟩ : syracuseStep 1482745 = 1112059) (by norm_num)
theorem B1318915 : Blo 1317977 1318915 := bstep (se 1 (by rfl) ⟨989186, by rfl⟩ : syracuseStep 1318915 = 1978373) B1978373
theorem B1318931 : Blo 1317977 1318931 := bstep (se 1 (by rfl) ⟨989198, by rfl⟩ : syracuseStep 1318931 = 1978397) B1978397
theorem B1318947 : Blo 1317977 1318947 := bstep (se 1 (by rfl) ⟨989210, by rfl⟩ : syracuseStep 1318947 = 1978421) B1978421
theorem B2965553 : Blo 1317977 2965553 := bstep (se 2 (by rfl) ⟨1112082, by rfl⟩ : syracuseStep 2965553 = 2224165) B2224165
theorem B1318963 : Blo 1317977 1318963 := bstep (se 1 (by rfl) ⟨989222, by rfl⟩ : syracuseStep 1318963 = 1978445) B1978445
theorem B28508213 : Blo 1317977 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B2965571 : Blo 1317977 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B1318979 : Blo 1317977 1318979 := bstep (se 1 (by rfl) ⟨989234, by rfl⟩ : syracuseStep 1318979 = 1978469) B1978469
theorem B1482835 : Blo 1317977 1482835 := bstep (se 1 (by rfl) ⟨1112126, by rfl⟩ : syracuseStep 1482835 = 2224253) B2224253
theorem B1318995 : Blo 1317977 1318995 := bstep (se 1 (by rfl) ⟨989246, by rfl⟩ : syracuseStep 1318995 = 1978493) B1978493
theorem B5709923 : Blo 1317977 5709923 := bstep (se 1 (by rfl) ⟨4282442, by rfl⟩ : syracuseStep 5709923 = 8564885) B8564885
theorem B1319011 : Blo 1317977 1319011 := bstep (se 1 (by rfl) ⟨989258, by rfl⟩ : syracuseStep 1319011 = 1978517) B1978517
theorem B1319027 : Blo 1317977 1319027 := bstep (se 1 (by rfl) ⟨989270, by rfl⟩ : syracuseStep 1319027 = 1978541) B1978541
theorem B1319043 : Blo 1317977 1319043 := bstep (se 1 (by rfl) ⟨989282, by rfl⟩ : syracuseStep 1319043 = 1978565) B1978565
theorem B1319059 : Blo 1317977 1319059 := bstep (se 1 (by rfl) ⟨989294, by rfl⟩ : syracuseStep 1319059 = 1978589) B1978589
theorem B1319075 : Blo 1317977 1319075 := bstep (se 1 (by rfl) ⟨989306, by rfl⟩ : syracuseStep 1319075 = 1978613) B1978613
theorem B1319091 : Blo 1317977 1319091 := bstep (se 1 (by rfl) ⟨989318, by rfl⟩ : syracuseStep 1319091 = 1978637) B1978637
theorem B1319107 : Blo 1317977 1319107 := bstep (se 1 (by rfl) ⟨989330, by rfl⟩ : syracuseStep 1319107 = 1978661) B1978661
theorem B4448465 : Blo 1317977 4448465 := bstep (se 2 (by rfl) ⟨1668174, by rfl⟩ : syracuseStep 4448465 = 3336349) B3336349
theorem B1319123 : Blo 1317977 1319123 := bstep (se 1 (by rfl) ⟨989342, by rfl⟩ : syracuseStep 1319123 = 1978685) B1978685
theorem B1482979 : Blo 1317977 1482979 := bstep (se 1 (by rfl) ⟨1112234, by rfl⟩ : syracuseStep 1482979 = 2224469) B2224469
theorem B1319139 : Blo 1317977 1319139 := bstep (se 1 (by rfl) ⟨989354, by rfl⟩ : syracuseStep 1319139 = 1978709) B1978709
theorem B1319155 : Blo 1317977 1319155 := bstep (se 1 (by rfl) ⟨989366, by rfl⟩ : syracuseStep 1319155 = 1978733) B1978733
theorem B1319171 : Blo 1317977 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B1319187 : Blo 1317977 1319187 := bstep (se 1 (by rfl) ⟨989390, by rfl⟩ : syracuseStep 1319187 = 1978781) B1978781
theorem B1319203 : Blo 1317977 1319203 := bstep (se 1 (by rfl) ⟨989402, by rfl⟩ : syracuseStep 1319203 = 1978805) B1978805
theorem B1319219 : Blo 1317977 1319219 := bstep (se 1 (by rfl) ⟨989414, by rfl⟩ : syracuseStep 1319219 = 1978829) B1978829
theorem B1319235 : Blo 1317977 1319235 := bstep (se 1 (by rfl) ⟨989426, by rfl⟩ : syracuseStep 1319235 = 1978853) B1978853
theorem B2965841 : Blo 1317977 2965841 := bstep (se 2 (by rfl) ⟨1112190, by rfl⟩ : syracuseStep 2965841 = 2224381) B2224381
theorem B1319251 : Blo 1317977 1319251 := bstep (se 1 (by rfl) ⟨989438, by rfl⟩ : syracuseStep 1319251 = 1978877) B1978877
theorem B2965859 : Blo 1317977 2965859 := bstep (se 1 (by rfl) ⟨2224394, by rfl⟩ : syracuseStep 2965859 = 4448789) B4448789
theorem B1319267 : Blo 1317977 1319267 := bstep (se 1 (by rfl) ⟨989450, by rfl⟩ : syracuseStep 1319267 = 1978901) B1978901
theorem B1483123 : Blo 1317977 1483123 := bstep (se 1 (by rfl) ⟨1112342, by rfl⟩ : syracuseStep 1483123 = 2224685) B2224685
theorem B1319283 : Blo 1317977 1319283 := bstep (se 1 (by rfl) ⟨989462, by rfl⟩ : syracuseStep 1319283 = 1978925) B1978925
theorem B1319299 : Blo 1317977 1319299 := bstep (se 1 (by rfl) ⟨989474, by rfl⟩ : syracuseStep 1319299 = 1978949) B1978949
theorem B5005709 : Blo 1317977 5005709 := bstep (se 3 (by rfl) ⟨938570, by rfl⟩ : syracuseStep 5005709 = 1877141) B1877141
theorem B1319315 : Blo 1317977 1319315 := bstep (se 1 (by rfl) ⟨989486, by rfl⟩ : syracuseStep 1319315 = 1978973) B1978973
theorem B1319331 : Blo 1317977 1319331 := bstep (se 1 (by rfl) ⟨989498, by rfl⟩ : syracuseStep 1319331 = 1978997) B1978997
theorem B1761713 : Blo 1317977 1761713 := bstep (se 2 (by rfl) ⟨660642, by rfl⟩ : syracuseStep 1761713 = 1321285) B1321285
theorem B1319347 : Blo 1317977 1319347 := bstep (se 1 (by rfl) ⟨989510, by rfl⟩ : syracuseStep 1319347 = 1979021) B1979021
theorem B1319363 : Blo 1317977 1319363 := bstep (se 1 (by rfl) ⟨989522, by rfl⟩ : syracuseStep 1319363 = 1979045) B1979045
theorem B1319379 : Blo 1317977 1319379 := bstep (se 1 (by rfl) ⟨989534, by rfl⟩ : syracuseStep 1319379 = 1979069) B1979069
theorem B1319395 : Blo 1317977 1319395 := bstep (se 1 (by rfl) ⟨989546, by rfl⟩ : syracuseStep 1319395 = 1979093) B1979093
theorem B1319411 : Blo 1317977 1319411 := bstep (se 1 (by rfl) ⟨989558, by rfl⟩ : syracuseStep 1319411 = 1979117) B1979117
theorem B1483267 : Blo 1317977 1483267 := bstep (se 1 (by rfl) ⟨1112450, by rfl⟩ : syracuseStep 1483267 = 2224901) B2224901
theorem B1524227 : Blo 1317977 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B1319427 : Blo 1317977 1319427 := bstep (se 1 (by rfl) ⟨989570, by rfl⟩ : syracuseStep 1319427 = 1979141) B1979141
theorem B1319443 : Blo 1317977 1319443 := bstep (se 1 (by rfl) ⟨989582, by rfl⟩ : syracuseStep 1319443 = 1979165) B1979165
theorem B1319459 : Blo 1317977 1319459 := bstep (se 1 (by rfl) ⟨989594, by rfl⟩ : syracuseStep 1319459 = 1979189) B1979189
theorem B1319475 : Blo 1317977 1319475 := bstep (se 1 (by rfl) ⟨989606, by rfl⟩ : syracuseStep 1319475 = 1979213) B1979213
theorem B2966129 : Blo 1317977 2966129 := bstep (se 2 (by rfl) ⟨1112298, by rfl⟩ : syracuseStep 2966129 = 2224597) B2224597
theorem B2966147 : Blo 1317977 2966147 := bstep (se 1 (by rfl) ⟨2224610, by rfl⟩ : syracuseStep 2966147 = 4449221) B4449221
theorem B7512709 : Blo 1317977 7512709 := bstep (se 4 (by rfl) ⟨704316, by rfl⟩ : syracuseStep 7512709 = 1408633) B1408633
theorem B1483411 : Blo 1317977 1483411 := bstep (se 1 (by rfl) ⟨1112558, by rfl⟩ : syracuseStep 1483411 = 2225117) B2225117
theorem B4449005 : Blo 1317977 4449005 := bstep (se 3 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 4449005 = 1668377) B1668377
theorem B4449059 : Blo 1317977 4449059 := bstep (se 1 (by rfl) ⟨3336794, by rfl⟩ : syracuseStep 4449059 = 6673589) B6673589
theorem B1483555 : Blo 1317977 1483555 := bstep (se 1 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 1483555 = 2225333) B2225333
theorem B2966417 : Blo 1317977 2966417 := bstep (se 2 (by rfl) ⟨1112406, by rfl⟩ : syracuseStep 2966417 = 2224813) B2224813
theorem B2966435 : Blo 1317977 2966435 := bstep (se 1 (by rfl) ⟨2224826, by rfl⟩ : syracuseStep 2966435 = 4449653) B4449653
theorem B1483699 : Blo 1317977 1483699 := bstep (se 1 (by rfl) ⟨1112774, by rfl⟩ : syracuseStep 1483699 = 2225549) B2225549
theorem B4449329 : Blo 1317977 4449329 := bstep (se 2 (by rfl) ⟨1668498, by rfl⟩ : syracuseStep 4449329 = 3336997) B3336997
theorem B1483843 : Blo 1317977 1483843 := bstep (se 1 (by rfl) ⟨1112882, by rfl⟩ : syracuseStep 1483843 = 2225765) B2225765
theorem B3564643 : Blo 1317977 3564643 := bstep (se 1 (by rfl) ⟨2673482, by rfl⟩ : syracuseStep 3564643 = 5346965) B5346965
theorem B3613805 : Blo 1317977 3613805 := bstep (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) B1355177
theorem B1877107 : Blo 1317977 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B8127629 : Blo 1317977 8127629 := bstep (se 3 (by rfl) ⟨1523930, by rfl⟩ : syracuseStep 8127629 = 3047861) B3047861
theorem B3613859 : Blo 1317977 3613859 := bstep (se 1 (by rfl) ⟨2710394, by rfl⟩ : syracuseStep 3613859 = 5420789) B5420789
theorem B2966705 : Blo 1317977 2966705 := bstep (se 2 (by rfl) ⟨1112514, by rfl⟩ : syracuseStep 2966705 = 2225029) B2225029
theorem B3753155 : Blo 1317977 3753155 := bstep (se 1 (by rfl) ⟨2814866, by rfl⟩ : syracuseStep 3753155 = 5629733) B5629733
theorem B2966723 : Blo 1317977 2966723 := bstep (se 1 (by rfl) ⟨2225042, by rfl⟩ : syracuseStep 2966723 = 4450085) B4450085
theorem B1483987 : Blo 1317977 1483987 := bstep (se 1 (by rfl) ⟨1112990, by rfl⟩ : syracuseStep 1483987 = 2225981) B2225981
theorem B96257251 : Blo 1317977 96257251 := bstep (se 1 (by rfl) ⟨72192938, by rfl⟩ : syracuseStep 96257251 = 144385877) B144385877
theorem B78169315 : Blo 1317977 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B1484131 : Blo 1317977 1484131 := bstep (se 1 (by rfl) ⟨1113098, by rfl⟩ : syracuseStep 1484131 = 2226197) B2226197
theorem B2966993 : Blo 1317977 2966993 := bstep (se 2 (by rfl) ⟨1112622, by rfl⟩ : syracuseStep 2966993 = 2225245) B2225245
theorem B11888099 : Blo 1317977 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B2967011 : Blo 1317977 2967011 := bstep (se 1 (by rfl) ⟨2225258, by rfl⟩ : syracuseStep 2967011 = 4450517) B4450517
theorem B1484275 : Blo 1317977 1484275 := bstep (se 1 (by rfl) ⟨1113206, by rfl⟩ : syracuseStep 1484275 = 2226413) B2226413
theorem B3753485 : Blo 1317977 3753485 := bstep (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) B1407557
theorem B4449869 : Blo 1317977 4449869 := bstep (se 3 (by rfl) ⟨834350, by rfl⟩ : syracuseStep 4449869 = 1668701) B1668701
theorem B3753553 : Blo 1317977 3753553 := bstep (se 2 (by rfl) ⟨1407582, by rfl⟩ : syracuseStep 3753553 = 2815165) B2815165
theorem B1877585 : Blo 1317977 1877585 := bstep (se 2 (by rfl) ⟨704094, by rfl⟩ : syracuseStep 1877585 = 1408189) B1408189
theorem B4449923 : Blo 1317977 4449923 := bstep (se 1 (by rfl) ⟨3337442, by rfl⟩ : syracuseStep 4449923 = 6674885) B6674885
theorem B1877699 : Blo 1317977 1877699 := bstep (se 1 (by rfl) ⟨1408274, by rfl⟩ : syracuseStep 1877699 = 2816549) B2816549
theorem B2967281 : Blo 1317977 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B2967299 : Blo 1317977 2967299 := bstep (se 1 (by rfl) ⟨2225474, by rfl⟩ : syracuseStep 2967299 = 4450949) B4450949
theorem B1877779 : Blo 1317977 1877779 := bstep (se 1 (by rfl) ⟨1408334, by rfl⟩ : syracuseStep 1877779 = 2816669) B2816669
theorem B3753827 : Blo 1317977 3753827 := bstep (se 1 (by rfl) ⟨2815370, by rfl⟩ : syracuseStep 3753827 = 5630741) B5630741
theorem B2377603 : Blo 1317977 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B4450193 : Blo 1317977 4450193 := bstep (se 2 (by rfl) ⟨1668822, by rfl⟩ : syracuseStep 4450193 = 3337645) B3337645
theorem B6678449 : Blo 1317977 6678449 := bstep (se 2 (by rfl) ⟨2504418, by rfl⟩ : syracuseStep 6678449 = 5008837) B5008837
theorem B5212109 : Blo 1317977 5212109 := bstep (se 3 (by rfl) ⟨977270, by rfl⟩ : syracuseStep 5212109 = 1954541) B1954541
theorem B15026147 : Blo 1317977 15026147 := bstep (se 1 (by rfl) ⟨11269610, by rfl⟩ : syracuseStep 15026147 = 22539221) B22539221
theorem B2967569 : Blo 1317977 2967569 := bstep (se 2 (by rfl) ⟨1112838, by rfl⟩ : syracuseStep 2967569 = 2225677) B2225677
theorem B2967587 : Blo 1317977 2967587 := bstep (se 1 (by rfl) ⟨2225690, by rfl⟩ : syracuseStep 2967587 = 4451381) B4451381
theorem B3008771 : Blo 1317977 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B2967857 : Blo 1317977 2967857 := bstep (se 2 (by rfl) ⟨1112946, by rfl⟩ : syracuseStep 2967857 = 2225893) B2225893
theorem B1878337 : Blo 1317977 1878337 := bstep (se 2 (by rfl) ⟨704376, by rfl⟩ : syracuseStep 1878337 = 1408753) B1408753
theorem B2967875 : Blo 1317977 2967875 := bstep (se 1 (by rfl) ⟨2225906, by rfl⟩ : syracuseStep 2967875 = 4451813) B4451813
theorem B3664273 : Blo 1317977 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B4450733 : Blo 1317977 4450733 := bstep (se 3 (by rfl) ⟨834512, by rfl⟩ : syracuseStep 4450733 = 1669025) B1669025
theorem B1583555 : Blo 1317977 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B4450787 : Blo 1317977 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B7514693 : Blo 1317977 7514693 := bstep (se 4 (by rfl) ⟨704502, by rfl⟩ : syracuseStep 7514693 = 1409005) B1409005
theorem B3336785 : Blo 1317977 3336785 := bstep (se 2 (by rfl) ⟨1251294, by rfl⟩ : syracuseStep 3336785 = 2502589) B2502589
theorem B2968145 : Blo 1317977 2968145 := bstep (se 2 (by rfl) ⟨1113054, by rfl⟩ : syracuseStep 2968145 = 2226109) B2226109
theorem B2968163 : Blo 1317977 2968163 := bstep (se 1 (by rfl) ⟨2226122, by rfl⟩ : syracuseStep 2968163 = 4452245) B4452245
theorem B3336835 : Blo 1317977 3336835 := bstep (se 1 (by rfl) ⟨2502626, by rfl⟩ : syracuseStep 3336835 = 5005253) B5005253
theorem B1976993 : Blo 1317977 1976993 := bstep (se 2 (by rfl) ⟨741372, by rfl⟩ : syracuseStep 1976993 = 1482745) B1482745
theorem B3754669 : Blo 1317977 3754669 := bstep (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) B1408001
theorem B1977011 : Blo 1317977 1977011 := bstep (se 1 (by rfl) ⟨1482758, by rfl⟩ : syracuseStep 1977011 = 2965517) B2965517
theorem B1977041 : Blo 1317977 1977041 := bstep (se 2 (by rfl) ⟨741390, by rfl⟩ : syracuseStep 1977041 = 1482781) B1482781
theorem B1977059 : Blo 1317977 1977059 := bstep (se 1 (by rfl) ⟨1482794, by rfl⟩ : syracuseStep 1977059 = 2965589) B2965589
theorem B5630705 : Blo 1317977 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B4451057 : Blo 1317977 4451057 := bstep (se 2 (by rfl) ⟨1669146, by rfl⟩ : syracuseStep 4451057 = 3338293) B3338293
theorem B1977089 : Blo 1317977 1977089 := bstep (se 2 (by rfl) ⟨741408, by rfl⟩ : syracuseStep 1977089 = 1482817) B1482817
theorem B3336977 : Blo 1317977 3336977 := bstep (se 2 (by rfl) ⟨1251366, by rfl⟩ : syracuseStep 3336977 = 2502733) B2502733
theorem B2673425 : Blo 1317977 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B1977107 : Blo 1317977 1977107 := bstep (se 1 (by rfl) ⟨1482830, by rfl⟩ : syracuseStep 1977107 = 2965661) B2965661
theorem B1977137 : Blo 1317977 1977137 := bstep (se 2 (by rfl) ⟨741426, by rfl⟩ : syracuseStep 1977137 = 1482853) B1482853
theorem B1977155 : Blo 1317977 1977155 := bstep (se 1 (by rfl) ⟨1482866, by rfl⟩ : syracuseStep 1977155 = 2965733) B2965733
theorem B3754829 : Blo 1317977 3754829 := bstep (se 3 (by rfl) ⟨704030, by rfl⟩ : syracuseStep 3754829 = 1408061) B1408061
theorem B1977185 : Blo 1317977 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B2968433 : Blo 1317977 2968433 := bstep (se 2 (by rfl) ⟨1113162, by rfl⟩ : syracuseStep 2968433 = 2226325) B2226325
theorem B1977203 : Blo 1317977 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B2968451 : Blo 1317977 2968451 := bstep (se 1 (by rfl) ⟨2226338, by rfl⟩ : syracuseStep 2968451 = 4452677) B4452677
theorem B1977233 : Blo 1317977 1977233 := bstep (se 2 (by rfl) ⟨741462, by rfl⟩ : syracuseStep 1977233 = 1482925) B1482925
theorem B1977251 : Blo 1317977 1977251 := bstep (se 1 (by rfl) ⟨1482938, by rfl⟩ : syracuseStep 1977251 = 2965877) B2965877
theorem B1977281 : Blo 1317977 1977281 := bstep (se 2 (by rfl) ⟨741480, by rfl⟩ : syracuseStep 1977281 = 1482961) B1482961
theorem B1977299 : Blo 1317977 1977299 := bstep (se 1 (by rfl) ⟨1482974, by rfl⟩ : syracuseStep 1977299 = 2965949) B2965949
theorem B21375971 : Blo 1317977 21375971 := bstep (se 1 (by rfl) ⟨16031978, by rfl⟩ : syracuseStep 21375971 = 32063957) B32063957
theorem B6261745 : Blo 1317977 6261745 := bstep (se 2 (by rfl) ⟨2348154, by rfl⟩ : syracuseStep 6261745 = 4696309) B4696309
theorem B1977329 : Blo 1317977 1977329 := bstep (se 2 (by rfl) ⟨741498, by rfl⟩ : syracuseStep 1977329 = 1482997) B1482997
theorem B1977347 : Blo 1317977 1977347 := bstep (se 1 (by rfl) ⟨1483010, by rfl⟩ : syracuseStep 1977347 = 2966021) B2966021
theorem B3755011 : Blo 1317977 3755011 := bstep (se 1 (by rfl) ⟨2816258, by rfl⟩ : syracuseStep 3755011 = 5632517) B5632517
theorem B1977377 : Blo 1317977 1977377 := bstep (se 2 (by rfl) ⟨741516, by rfl⟩ : syracuseStep 1977377 = 1483033) B1483033
theorem B1977395 : Blo 1317977 1977395 := bstep (se 1 (by rfl) ⟨1483046, by rfl⟩ : syracuseStep 1977395 = 2966093) B2966093
theorem B1977425 : Blo 1317977 1977425 := bstep (se 2 (by rfl) ⟨741534, by rfl⟩ : syracuseStep 1977425 = 1483069) B1483069
theorem B1977443 : Blo 1317977 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B1977473 : Blo 1317977 1977473 := bstep (se 2 (by rfl) ⟨741552, by rfl⟩ : syracuseStep 1977473 = 1483105) B1483105
theorem B2968721 : Blo 1317977 2968721 := bstep (se 2 (by rfl) ⟨1113270, by rfl⟩ : syracuseStep 2968721 = 2226541) B2226541
theorem B1977491 : Blo 1317977 1977491 := bstep (se 1 (by rfl) ⟨1483118, by rfl⟩ : syracuseStep 1977491 = 2966237) B2966237
theorem B2968739 : Blo 1317977 2968739 := bstep (se 1 (by rfl) ⟨2226554, by rfl⟩ : syracuseStep 2968739 = 4453109) B4453109
theorem B1977521 : Blo 1317977 1977521 := bstep (se 2 (by rfl) ⟨741570, by rfl⟩ : syracuseStep 1977521 = 1483141) B1483141
theorem B2141363 : Blo 1317977 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B1977539 : Blo 1317977 1977539 := bstep (se 1 (by rfl) ⟨1483154, by rfl⟩ : syracuseStep 1977539 = 2966309) B2966309
theorem B1977569 : Blo 1317977 1977569 := bstep (se 2 (by rfl) ⟨741588, by rfl⟩ : syracuseStep 1977569 = 1483177) B1483177
theorem B5008625 : Blo 1317977 5008625 := bstep (se 2 (by rfl) ⟨1878234, by rfl⟩ : syracuseStep 5008625 = 3756469) B3756469
theorem B1977587 : Blo 1317977 1977587 := bstep (se 1 (by rfl) ⟨1483190, by rfl⟩ : syracuseStep 1977587 = 2966381) B2966381
theorem B4508941 : Blo 1317977 4508941 := bstep (se 3 (by rfl) ⟨845426, by rfl⟩ : syracuseStep 4508941 = 1690853) B1690853
theorem B4451597 : Blo 1317977 4451597 := bstep (se 3 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 4451597 = 1669349) B1669349
theorem B1977617 : Blo 1317977 1977617 := bstep (se 2 (by rfl) ⟨741606, by rfl⟩ : syracuseStep 1977617 = 1483213) B1483213
theorem B1977635 : Blo 1317977 1977635 := bstep (se 1 (by rfl) ⟨1483226, by rfl⟩ : syracuseStep 1977635 = 2966453) B2966453
theorem B1977665 : Blo 1317977 1977665 := bstep (se 2 (by rfl) ⟨741624, by rfl⟩ : syracuseStep 1977665 = 1483249) B1483249
theorem B4451651 : Blo 1317977 4451651 := bstep (se 1 (by rfl) ⟨3338738, by rfl⟩ : syracuseStep 4451651 = 6677477) B6677477
theorem B2674001 : Blo 1317977 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B1977683 : Blo 1317977 1977683 := bstep (se 1 (by rfl) ⟨1483262, by rfl⟩ : syracuseStep 1977683 = 2966525) B2966525
theorem B1977713 : Blo 1317977 1977713 := bstep (se 2 (by rfl) ⟨741642, by rfl⟩ : syracuseStep 1977713 = 1483285) B1483285
theorem B1977731 : Blo 1317977 1977731 := bstep (se 1 (by rfl) ⟨1483298, by rfl⟩ : syracuseStep 1977731 = 2966597) B2966597
theorem B1977761 : Blo 1317977 1977761 := bstep (se 2 (by rfl) ⟨741660, by rfl⟩ : syracuseStep 1977761 = 1483321) B1483321
theorem B1977779 : Blo 1317977 1977779 := bstep (se 1 (by rfl) ⟨1483334, by rfl⟩ : syracuseStep 1977779 = 2966669) B2966669
theorem B1977809 : Blo 1317977 1977809 := bstep (se 2 (by rfl) ⟨741678, by rfl⟩ : syracuseStep 1977809 = 1483357) B1483357
theorem B1977827 : Blo 1317977 1977827 := bstep (se 1 (by rfl) ⟨1483370, by rfl⟩ : syracuseStep 1977827 = 2966741) B2966741
theorem B10284529 : Blo 1317977 10284529 := bstep (se 2 (by rfl) ⟨3856698, by rfl⟩ : syracuseStep 10284529 = 7713397) B7713397
theorem B1977857 : Blo 1317977 1977857 := bstep (se 2 (by rfl) ⟨741696, by rfl⟩ : syracuseStep 1977857 = 1483393) B1483393
theorem B1977875 : Blo 1317977 1977875 := bstep (se 1 (by rfl) ⟨1483406, by rfl⟩ : syracuseStep 1977875 = 2966813) B2966813
theorem B1977905 : Blo 1317977 1977905 := bstep (se 2 (by rfl) ⟨741714, by rfl⟩ : syracuseStep 1977905 = 1483429) B1483429
theorem B1781299 : Blo 1317977 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B1977923 : Blo 1317977 1977923 := bstep (se 1 (by rfl) ⟨1483442, by rfl⟩ : syracuseStep 1977923 = 2966885) B2966885
theorem B4451921 : Blo 1317977 4451921 := bstep (se 2 (by rfl) ⟨1669470, by rfl⟩ : syracuseStep 4451921 = 3338941) B3338941
theorem B1977953 : Blo 1317977 1977953 := bstep (se 2 (by rfl) ⟨741732, by rfl⟩ : syracuseStep 1977953 = 1483465) B1483465
theorem B1977971 : Blo 1317977 1977971 := bstep (se 1 (by rfl) ⟨1483478, by rfl⟩ : syracuseStep 1977971 = 2966957) B2966957
theorem B1978001 : Blo 1317977 1978001 := bstep (se 2 (by rfl) ⟨741750, by rfl⟩ : syracuseStep 1978001 = 1483501) B1483501
theorem B1978019 : Blo 1317977 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B1978049 : Blo 1317977 1978049 := bstep (se 2 (by rfl) ⟨741768, by rfl⟩ : syracuseStep 1978049 = 1483537) B1483537
theorem B2502353 : Blo 1317977 2502353 := bstep (se 2 (by rfl) ⟨938382, by rfl⟩ : syracuseStep 2502353 = 1876765) B1876765
theorem B1978067 : Blo 1317977 1978067 := bstep (se 1 (by rfl) ⟨1483550, by rfl⟩ : syracuseStep 1978067 = 2967101) B2967101
theorem B3337969 : Blo 1317977 3337969 := bstep (se 2 (by rfl) ⟨1251738, by rfl⟩ : syracuseStep 3337969 = 2503477) B2503477
theorem B1978097 : Blo 1317977 1978097 := bstep (se 2 (by rfl) ⟨741786, by rfl⟩ : syracuseStep 1978097 = 1483573) B1483573
theorem B1978115 : Blo 1317977 1978115 := bstep (se 1 (by rfl) ⟨1483586, by rfl⟩ : syracuseStep 1978115 = 2967173) B2967173
theorem B1978145 : Blo 1317977 1978145 := bstep (se 2 (by rfl) ⟨741804, by rfl⟩ : syracuseStep 1978145 = 1483609) B1483609
theorem B1978163 : Blo 1317977 1978163 := bstep (se 1 (by rfl) ⟨1483622, by rfl⟩ : syracuseStep 1978163 = 2967245) B2967245
theorem B1978193 : Blo 1317977 1978193 := bstep (se 2 (by rfl) ⟨741822, by rfl⟩ : syracuseStep 1978193 = 1483645) B1483645
theorem B1978211 : Blo 1317977 1978211 := bstep (se 1 (by rfl) ⟨1483658, by rfl⟩ : syracuseStep 1978211 = 2967317) B2967317
theorem B1978241 : Blo 1317977 1978241 := bstep (se 2 (by rfl) ⟨741840, by rfl⟩ : syracuseStep 1978241 = 1483681) B1483681
theorem B1978259 : Blo 1317977 1978259 := bstep (se 1 (by rfl) ⟨1483694, by rfl⟩ : syracuseStep 1978259 = 2967389) B2967389
theorem B1978289 : Blo 1317977 1978289 := bstep (se 2 (by rfl) ⟨741858, by rfl⟩ : syracuseStep 1978289 = 1483717) B1483717
theorem B1978307 : Blo 1317977 1978307 := bstep (se 1 (by rfl) ⟨1483730, by rfl⟩ : syracuseStep 1978307 = 2967461) B2967461
theorem B9637829 : Blo 1317977 9637829 := bstep (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) B1807093
theorem B1978337 : Blo 1317977 1978337 := bstep (se 2 (by rfl) ⟨741876, by rfl⟩ : syracuseStep 1978337 = 1483753) B1483753
theorem B1978355 : Blo 1317977 1978355 := bstep (se 1 (by rfl) ⟨1483766, by rfl⟩ : syracuseStep 1978355 = 2967533) B2967533
theorem B4222979 : Blo 1317977 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B3338243 : Blo 1317977 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B2224145 : Blo 1317977 2224145 := bstep (se 2 (by rfl) ⟨834054, by rfl⟩ : syracuseStep 2224145 = 1668109) B1668109
theorem B1978385 : Blo 1317977 1978385 := bstep (se 2 (by rfl) ⟨741894, by rfl⟩ : syracuseStep 1978385 = 1483789) B1483789
theorem B1978403 : Blo 1317977 1978403 := bstep (se 1 (by rfl) ⟨1483802, by rfl⟩ : syracuseStep 1978403 = 2967605) B2967605
theorem B1978433 : Blo 1317977 1978433 := bstep (se 2 (by rfl) ⟨741912, by rfl⟩ : syracuseStep 1978433 = 1483825) B1483825
theorem B1978451 : Blo 1317977 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B4452461 : Blo 1317977 4452461 := bstep (se 3 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 4452461 = 1669673) B1669673
theorem B1978481 : Blo 1317977 1978481 := bstep (se 2 (by rfl) ⟨741930, by rfl⟩ : syracuseStep 1978481 = 1483861) B1483861
theorem B1978499 : Blo 1317977 1978499 := bstep (se 1 (by rfl) ⟨1483874, by rfl⟩ : syracuseStep 1978499 = 2967749) B2967749
theorem B2674819 : Blo 1317977 2674819 := bstep (se 1 (by rfl) ⟨2006114, by rfl⟩ : syracuseStep 2674819 = 4012229) B4012229
theorem B2224273 : Blo 1317977 2224273 := bstep (se 2 (by rfl) ⟨834102, by rfl⟩ : syracuseStep 2224273 = 1668205) B1668205
theorem B1978529 : Blo 1317977 1978529 := bstep (se 2 (by rfl) ⟨741948, by rfl⟩ : syracuseStep 1978529 = 1483897) B1483897
theorem B4452515 : Blo 1317977 4452515 := bstep (se 1 (by rfl) ⟨3339386, by rfl⟩ : syracuseStep 4452515 = 6678773) B6678773
theorem B2224307 : Blo 1317977 2224307 := bstep (se 1 (by rfl) ⟨1668230, by rfl⟩ : syracuseStep 2224307 = 3336461) B3336461
theorem B1978547 : Blo 1317977 1978547 := bstep (se 1 (by rfl) ⟨1483910, by rfl⟩ : syracuseStep 1978547 = 2967821) B2967821
theorem B3338435 : Blo 1317977 3338435 := bstep (se 1 (by rfl) ⟨2503826, by rfl⟩ : syracuseStep 3338435 = 5007653) B5007653
theorem B1978577 : Blo 1317977 1978577 := bstep (se 2 (by rfl) ⟨741966, by rfl⟩ : syracuseStep 1978577 = 1483933) B1483933
theorem B1978595 : Blo 1317977 1978595 := bstep (se 1 (by rfl) ⟨1483946, by rfl⟩ : syracuseStep 1978595 = 2967893) B2967893
theorem B1978625 : Blo 1317977 1978625 := bstep (se 2 (by rfl) ⟨741984, by rfl⟩ : syracuseStep 1978625 = 1483969) B1483969
theorem B1978643 : Blo 1317977 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B1978673 : Blo 1317977 1978673 := bstep (se 2 (by rfl) ⟨742002, by rfl⟩ : syracuseStep 1978673 = 1484005) B1484005
theorem B2224435 : Blo 1317977 2224435 := bstep (se 1 (by rfl) ⟨1668326, by rfl⟩ : syracuseStep 2224435 = 3336653) B3336653
theorem B1978691 : Blo 1317977 1978691 := bstep (se 1 (by rfl) ⟨1484018, by rfl⟩ : syracuseStep 1978691 = 2968037) B2968037
theorem B1978721 : Blo 1317977 1978721 := bstep (se 2 (by rfl) ⟨742020, by rfl⟩ : syracuseStep 1978721 = 1484041) B1484041
theorem B3756401 : Blo 1317977 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B1978739 : Blo 1317977 1978739 := bstep (se 1 (by rfl) ⟨1484054, by rfl⟩ : syracuseStep 1978739 = 2968109) B2968109
theorem B1978769 : Blo 1317977 1978769 := bstep (se 2 (by rfl) ⟨742038, by rfl⟩ : syracuseStep 1978769 = 1484077) B1484077
theorem B2503075 : Blo 1317977 2503075 := bstep (se 1 (by rfl) ⟨1877306, by rfl⟩ : syracuseStep 2503075 = 3754613) B3754613
theorem B1978787 : Blo 1317977 1978787 := bstep (se 1 (by rfl) ⟨1484090, by rfl⟩ : syracuseStep 1978787 = 2968181) B2968181
theorem B4452785 : Blo 1317977 4452785 := bstep (se 2 (by rfl) ⟨1669794, by rfl⟩ : syracuseStep 4452785 = 3339589) B3339589
theorem B2224577 : Blo 1317977 2224577 := bstep (se 2 (by rfl) ⟨834216, by rfl⟩ : syracuseStep 2224577 = 1668433) B1668433
theorem B1978817 : Blo 1317977 1978817 := bstep (se 2 (by rfl) ⟨742056, by rfl⟩ : syracuseStep 1978817 = 1484113) B1484113
theorem B1978835 : Blo 1317977 1978835 := bstep (se 1 (by rfl) ⟨1484126, by rfl⟩ : syracuseStep 1978835 = 2968253) B2968253
theorem B1978865 : Blo 1317977 1978865 := bstep (se 2 (by rfl) ⟨742074, by rfl⟩ : syracuseStep 1978865 = 1484149) B1484149
theorem B1978883 : Blo 1317977 1978883 := bstep (se 1 (by rfl) ⟨1484162, by rfl⟩ : syracuseStep 1978883 = 2968325) B2968325
theorem B1978913 : Blo 1317977 1978913 := bstep (se 2 (by rfl) ⟨742092, by rfl⟩ : syracuseStep 1978913 = 1484185) B1484185
theorem B1978931 : Blo 1317977 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B2224705 : Blo 1317977 2224705 := bstep (se 2 (by rfl) ⟨834264, by rfl⟩ : syracuseStep 2224705 = 1668529) B1668529
theorem B1978961 : Blo 1317977 1978961 := bstep (se 2 (by rfl) ⟨742110, by rfl⟩ : syracuseStep 1978961 = 1484221) B1484221
theorem B2224739 : Blo 1317977 2224739 := bstep (se 1 (by rfl) ⟨1668554, by rfl⟩ : syracuseStep 2224739 = 3337109) B3337109
theorem B1978979 : Blo 1317977 1978979 := bstep (se 1 (by rfl) ⟨1484234, by rfl⟩ : syracuseStep 1978979 = 2968469) B2968469
theorem B1979009 : Blo 1317977 1979009 := bstep (se 2 (by rfl) ⟨742128, by rfl⟩ : syracuseStep 1979009 = 1484257) B1484257
theorem B1979027 : Blo 1317977 1979027 := bstep (se 1 (by rfl) ⟨1484270, by rfl⟩ : syracuseStep 1979027 = 2968541) B2968541
theorem B1979057 : Blo 1317977 1979057 := bstep (se 2 (by rfl) ⟨742146, by rfl⟩ : syracuseStep 1979057 = 1484293) B1484293
theorem B1979075 : Blo 1317977 1979075 := bstep (se 1 (by rfl) ⟨1484306, by rfl⟩ : syracuseStep 1979075 = 2968613) B2968613
theorem B1979105 : Blo 1317977 1979105 := bstep (se 2 (by rfl) ⟨742164, by rfl⟩ : syracuseStep 1979105 = 1484329) B1484329
theorem B2224867 : Blo 1317977 2224867 := bstep (se 1 (by rfl) ⟨1668650, by rfl⟩ : syracuseStep 2224867 = 3337301) B3337301
theorem B1979123 : Blo 1317977 1979123 := bstep (se 1 (by rfl) ⟨1484342, by rfl⟩ : syracuseStep 1979123 = 2968685) B2968685
theorem B4223747 : Blo 1317977 4223747 := bstep (se 1 (by rfl) ⟨3167810, by rfl⟩ : syracuseStep 4223747 = 6335621) B6335621
theorem B1504003 : Blo 1317977 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B1979153 : Blo 1317977 1979153 := bstep (se 2 (by rfl) ⟨742182, by rfl⟩ : syracuseStep 1979153 = 1484365) B1484365
theorem B1979171 : Blo 1317977 1979171 := bstep (se 1 (by rfl) ⟨1484378, by rfl⟩ : syracuseStep 1979171 = 2968757) B2968757
theorem B1979201 : Blo 1317977 1979201 := bstep (se 2 (by rfl) ⟨742200, by rfl⟩ : syracuseStep 1979201 = 1484401) B1484401
theorem B4281169 : Blo 1317977 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B2503523 : Blo 1317977 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B6673265 : Blo 1317977 6673265 := bstep (se 2 (by rfl) ⟨2502474, by rfl⟩ : syracuseStep 6673265 = 5004949) B5004949
theorem B2225009 : Blo 1317977 2225009 := bstep (se 2 (by rfl) ⟨834378, by rfl⟩ : syracuseStep 2225009 = 1668757) B1668757
theorem B2225137 : Blo 1317977 2225137 := bstep (se 2 (by rfl) ⟨834426, by rfl⟩ : syracuseStep 2225137 = 1668853) B1668853
theorem B2225171 : Blo 1317977 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B3339377 : Blo 1317977 3339377 := bstep (se 2 (by rfl) ⟨1252266, by rfl⟩ : syracuseStep 3339377 = 2504533) B2504533
theorem B2503811 : Blo 1317977 2503811 := bstep (se 1 (by rfl) ⟨1877858, by rfl⟩ : syracuseStep 2503811 = 3755717) B3755717
theorem B11416717 : Blo 1317977 11416717 := bstep (se 3 (by rfl) ⟨2140634, by rfl⟩ : syracuseStep 11416717 = 4281269) B4281269
theorem B5633165 : Blo 1317977 5633165 := bstep (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) B2112437
theorem B4224145 : Blo 1317977 4224145 := bstep (se 2 (by rfl) ⟨1584054, by rfl⟩ : syracuseStep 4224145 = 3168109) B3168109
theorem B2225299 : Blo 1317977 2225299 := bstep (se 1 (by rfl) ⟨1668974, by rfl⟩ : syracuseStep 2225299 = 3337949) B3337949
theorem B3339427 : Blo 1317977 3339427 := bstep (se 1 (by rfl) ⟨2504570, by rfl⟩ : syracuseStep 3339427 = 5009141) B5009141
theorem B4224259 : Blo 1317977 4224259 := bstep (se 1 (by rfl) ⟨3168194, by rfl⟩ : syracuseStep 4224259 = 6336389) B6336389
theorem B2225441 : Blo 1317977 2225441 := bstep (se 2 (by rfl) ⟨834540, by rfl⟩ : syracuseStep 2225441 = 1669081) B1669081
theorem B3757357 : Blo 1317977 3757357 := bstep (se 3 (by rfl) ⟨704504, by rfl⟩ : syracuseStep 3757357 = 1409009) B1409009
theorem B3339569 : Blo 1317977 3339569 := bstep (se 2 (by rfl) ⟨1252338, by rfl⟩ : syracuseStep 3339569 = 2504677) B2504677
theorem B11269475 : Blo 1317977 11269475 := bstep (se 1 (by rfl) ⟨8452106, by rfl⟩ : syracuseStep 11269475 = 16904213) B16904213
theorem B2225569 : Blo 1317977 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B2225603 : Blo 1317977 2225603 := bstep (se 1 (by rfl) ⟨1669202, by rfl⟩ : syracuseStep 2225603 = 3338405) B3338405
theorem B1668595 : Blo 1317977 1668595 := bstep (se 1 (by rfl) ⟨1251446, by rfl⟩ : syracuseStep 1668595 = 2502893) B2502893
theorem B15218189 : Blo 1317977 15218189 := bstep (se 3 (by rfl) ⟨2853410, by rfl⟩ : syracuseStep 15218189 = 5706821) B5706821
theorem B4511281 : Blo 1317977 4511281 := bstep (se 2 (by rfl) ⟨1691730, by rfl⟩ : syracuseStep 4511281 = 3383461) B3383461
theorem B2225731 : Blo 1317977 2225731 := bstep (se 1 (by rfl) ⟨1669298, by rfl⟩ : syracuseStep 2225731 = 3338597) B3338597
theorem B1668691 : Blo 1317977 1668691 := bstep (se 1 (by rfl) ⟨1251518, by rfl⟩ : syracuseStep 1668691 = 2503037) B2503037
theorem B2004625 : Blo 1317977 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B2225873 : Blo 1317977 2225873 := bstep (se 2 (by rfl) ⟨834702, by rfl⟩ : syracuseStep 2225873 = 1669405) B1669405
theorem B2226001 : Blo 1317977 2226001 := bstep (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) B1669501
theorem B2226035 : Blo 1317977 2226035 := bstep (se 1 (by rfl) ⟨1669526, by rfl⟩ : syracuseStep 2226035 = 3339053) B3339053
theorem B4224977 : Blo 1317977 4224977 := bstep (se 2 (by rfl) ⟨1584366, by rfl⟩ : syracuseStep 4224977 = 3168733) B3168733
theorem B2815985 : Blo 1317977 2815985 := bstep (se 2 (by rfl) ⟨1055994, by rfl⟩ : syracuseStep 2815985 = 2111989) B2111989
theorem B2226163 : Blo 1317977 2226163 := bstep (se 1 (by rfl) ⟨1669622, by rfl⟩ : syracuseStep 2226163 = 3339245) B3339245
theorem B7133197 : Blo 1317977 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B2504753 : Blo 1317977 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1669187 : Blo 1317977 1669187 := bstep (se 1 (by rfl) ⟨1251890, by rfl⟩ : syracuseStep 1669187 = 2503781) B2503781
theorem B2111617 : Blo 1317977 2111617 := bstep (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) B1583713
theorem B2226305 : Blo 1317977 2226305 := bstep (se 2 (by rfl) ⟨834864, by rfl⟩ : syracuseStep 2226305 = 1669729) B1669729
theorem B18290929 : Blo 1317977 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B2226433 : Blo 1317977 2226433 := bstep (se 2 (by rfl) ⟨834912, by rfl⟩ : syracuseStep 2226433 = 1669825) B1669825
theorem B6674723 : Blo 1317977 6674723 := bstep (se 1 (by rfl) ⟨5006042, by rfl⟩ : syracuseStep 6674723 = 10012085) B10012085
theorem B2226467 : Blo 1317977 2226467 := bstep (se 1 (by rfl) ⟨1669850, by rfl⟩ : syracuseStep 2226467 = 3339701) B3339701
theorem B9632141 : Blo 1317977 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B2005409 : Blo 1317977 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B2226595 : Blo 1317977 2226595 := bstep (se 1 (by rfl) ⟨1669946, by rfl⟩ : syracuseStep 2226595 = 3339893) B3339893
theorem B4225517 : Blo 1317977 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B5347889 : Blo 1317977 5347889 := bstep (se 2 (by rfl) ⟨2005458, by rfl⟩ : syracuseStep 5347889 = 4010917) B4010917
theorem B2005555 : Blo 1317977 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B2005603 : Blo 1317977 2005603 := bstep (se 1 (by rfl) ⟨1504202, by rfl⟩ : syracuseStep 2005603 = 3008405) B3008405
theorem B4512419 : Blo 1317977 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B6421169 : Blo 1317977 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B2112227 : Blo 1317977 2112227 := bstep (se 1 (by rfl) ⟨1584170, by rfl⟩ : syracuseStep 2112227 = 3168341) B3168341
theorem B5348081 : Blo 1317977 5348081 := bstep (se 2 (by rfl) ⟨2005530, by rfl⟩ : syracuseStep 5348081 = 4011061) B4011061
theorem B1669891 : Blo 1317977 1669891 := bstep (se 1 (by rfl) ⟨1252418, by rfl⟩ : syracuseStep 1669891 = 2504837) B2504837
theorem B2005793 : Blo 1317977 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B2816849 : Blo 1317977 2816849 := bstep (se 2 (by rfl) ⟨1056318, by rfl⟩ : syracuseStep 2816849 = 2112637) B2112637
theorem B6339505 : Blo 1317977 6339505 := bstep (se 2 (by rfl) ⟨2377314, by rfl⟩ : syracuseStep 6339505 = 4754629) B4754629
theorem B2538467 : Blo 1317977 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B5790733 : Blo 1317977 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B6675533 : Blo 1317977 6675533 := bstep (se 3 (by rfl) ⟨1251662, by rfl⟩ : syracuseStep 6675533 = 2503325) B2503325
theorem B1317987 : Blo 1317977 1317987 := bstep (se 1 (by rfl) ⟨988490, by rfl⟩ : syracuseStep 1317987 = 1976981) B1976981
theorem B1318003 : Blo 1317977 1318003 := bstep (se 1 (by rfl) ⟨988502, by rfl⟩ : syracuseStep 1318003 = 1977005) B1977005
theorem B1318019 : Blo 1317977 1318019 := bstep (se 1 (by rfl) ⟨988514, by rfl⟩ : syracuseStep 1318019 = 1977029) B1977029
theorem B1318035 : Blo 1317977 1318035 := bstep (se 1 (by rfl) ⟨988526, by rfl⟩ : syracuseStep 1318035 = 1977053) B1977053
theorem B1318051 : Blo 1317977 1318051 := bstep (se 1 (by rfl) ⟨988538, by rfl⟩ : syracuseStep 1318051 = 1977077) B1977077
theorem B1318067 : Blo 1317977 1318067 := bstep (se 1 (by rfl) ⟨988550, by rfl⟩ : syracuseStep 1318067 = 1977101) B1977101
theorem B1318083 : Blo 1317977 1318083 := bstep (se 1 (by rfl) ⟨988562, by rfl⟩ : syracuseStep 1318083 = 1977125) B1977125
theorem B1318099 : Blo 1317977 1318099 := bstep (se 1 (by rfl) ⟨988574, by rfl⟩ : syracuseStep 1318099 = 1977149) B1977149
theorem B1318115 : Blo 1317977 1318115 := bstep (se 1 (by rfl) ⟨988586, by rfl⟩ : syracuseStep 1318115 = 1977173) B1977173
theorem B1318131 : Blo 1317977 1318131 := bstep (se 1 (by rfl) ⟨988598, by rfl⟩ : syracuseStep 1318131 = 1977197) B1977197
theorem B1318147 : Blo 1317977 1318147 := bstep (se 1 (by rfl) ⟨988610, by rfl⟩ : syracuseStep 1318147 = 1977221) B1977221
theorem B1318163 : Blo 1317977 1318163 := bstep (se 1 (by rfl) ⟨988622, by rfl⟩ : syracuseStep 1318163 = 1977245) B1977245
theorem B1318179 : Blo 1317977 1318179 := bstep (se 1 (by rfl) ⟨988634, by rfl⟩ : syracuseStep 1318179 = 1977269) B1977269
theorem B1318195 : Blo 1317977 1318195 := bstep (se 1 (by rfl) ⟨988646, by rfl⟩ : syracuseStep 1318195 = 1977293) B1977293
theorem B1318211 : Blo 1317977 1318211 := bstep (se 1 (by rfl) ⟨988658, by rfl⟩ : syracuseStep 1318211 = 1977317) B1977317
theorem B1318227 : Blo 1317977 1318227 := bstep (se 1 (by rfl) ⟨988670, by rfl⟩ : syracuseStep 1318227 = 1977341) B1977341
theorem B1318243 : Blo 1317977 1318243 := bstep (se 1 (by rfl) ⟨988682, by rfl⟩ : syracuseStep 1318243 = 1977365) B1977365
theorem B8019299 : Blo 1317977 8019299 := bstep (se 1 (by rfl) ⟨6014474, by rfl⟩ : syracuseStep 8019299 = 12028949) B12028949
theorem B1318259 : Blo 1317977 1318259 := bstep (se 1 (by rfl) ⟨988694, by rfl⟩ : syracuseStep 1318259 = 1977389) B1977389
theorem B1318275 : Blo 1317977 1318275 := bstep (se 1 (by rfl) ⟨988706, by rfl⟩ : syracuseStep 1318275 = 1977413) B1977413
theorem B1318291 : Blo 1317977 1318291 := bstep (se 1 (by rfl) ⟨988718, by rfl⟩ : syracuseStep 1318291 = 1977437) B1977437
theorem B1318307 : Blo 1317977 1318307 := bstep (se 1 (by rfl) ⟨988730, by rfl⟩ : syracuseStep 1318307 = 1977461) B1977461
theorem B6602161 : Blo 1317977 6602161 := bstep (se 2 (by rfl) ⟨2475810, by rfl⟩ : syracuseStep 6602161 = 4951621) B4951621
theorem B1318323 : Blo 1317977 1318323 := bstep (se 1 (by rfl) ⟨988742, by rfl⟩ : syracuseStep 1318323 = 1977485) B1977485
theorem B1318339 : Blo 1317977 1318339 := bstep (se 1 (by rfl) ⟨988754, by rfl⟩ : syracuseStep 1318339 = 1977509) B1977509
theorem B1318355 : Blo 1317977 1318355 := bstep (se 1 (by rfl) ⟨988766, by rfl⟩ : syracuseStep 1318355 = 1977533) B1977533
theorem B1318371 : Blo 1317977 1318371 := bstep (se 1 (by rfl) ⟨988778, by rfl⟩ : syracuseStep 1318371 = 1977557) B1977557
theorem B1318387 : Blo 1317977 1318387 := bstep (se 1 (by rfl) ⟨988790, by rfl⟩ : syracuseStep 1318387 = 1977581) B1977581
theorem B1318403 : Blo 1317977 1318403 := bstep (se 1 (by rfl) ⟨988802, by rfl⟩ : syracuseStep 1318403 = 1977605) B1977605
theorem B8453645 : Blo 1317977 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B1318419 : Blo 1317977 1318419 := bstep (se 1 (by rfl) ⟨988814, by rfl⟩ : syracuseStep 1318419 = 1977629) B1977629
theorem B1318435 : Blo 1317977 1318435 := bstep (se 1 (by rfl) ⟨988826, by rfl⟩ : syracuseStep 1318435 = 1977653) B1977653
theorem B1318451 : Blo 1317977 1318451 := bstep (se 1 (by rfl) ⟨988838, by rfl⟩ : syracuseStep 1318451 = 1977677) B1977677
theorem B1318467 : Blo 1317977 1318467 := bstep (se 1 (by rfl) ⟨988850, by rfl⟩ : syracuseStep 1318467 = 1977701) B1977701
theorem B5144141 : Blo 1317977 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B1318483 : Blo 1317977 1318483 := bstep (se 1 (by rfl) ⟨988862, by rfl⟩ : syracuseStep 1318483 = 1977725) B1977725
theorem B1408595 : Blo 1317977 1408595 := bstep (se 1 (by rfl) ⟨1056446, by rfl⟩ : syracuseStep 1408595 = 2112893) B2112893
theorem B1318499 : Blo 1317977 1318499 := bstep (se 1 (by rfl) ⟨988874, by rfl⟩ : syracuseStep 1318499 = 1977749) B1977749
theorem B10018403 : Blo 1317977 10018403 := bstep (se 1 (by rfl) ⟨7513802, by rfl⟩ : syracuseStep 10018403 = 15027605) B15027605
theorem B1318515 : Blo 1317977 1318515 := bstep (se 1 (by rfl) ⟨988886, by rfl⟩ : syracuseStep 1318515 = 1977773) B1977773
theorem B1318531 : Blo 1317977 1318531 := bstep (se 1 (by rfl) ⟨988898, by rfl⟩ : syracuseStep 1318531 = 1977797) B1977797
theorem B1318547 : Blo 1317977 1318547 := bstep (se 1 (by rfl) ⟨988910, by rfl⟩ : syracuseStep 1318547 = 1977821) B1977821
theorem B1318563 : Blo 1317977 1318563 := bstep (se 1 (by rfl) ⟨988922, by rfl⟩ : syracuseStep 1318563 = 1977845) B1977845
theorem B3169955 : Blo 1317977 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B1318579 : Blo 1317977 1318579 := bstep (se 1 (by rfl) ⟨988934, by rfl⟩ : syracuseStep 1318579 = 1977869) B1977869
theorem B1318595 : Blo 1317977 1318595 := bstep (se 1 (by rfl) ⟨988946, by rfl⟩ : syracuseStep 1318595 = 1977893) B1977893
theorem B2113219 : Blo 1317977 2113219 := bstep (se 1 (by rfl) ⟨1584914, by rfl⟩ : syracuseStep 2113219 = 3169829) B3169829
theorem B1318611 : Blo 1317977 1318611 := bstep (se 1 (by rfl) ⟨988958, by rfl⟩ : syracuseStep 1318611 = 1977917) B1977917
theorem B1318627 : Blo 1317977 1318627 := bstep (se 1 (by rfl) ⟨988970, by rfl⟩ : syracuseStep 1318627 = 1977941) B1977941
theorem B1318643 : Blo 1317977 1318643 := bstep (se 1 (by rfl) ⟨988982, by rfl⟩ : syracuseStep 1318643 = 1977965) B1977965
theorem B1318659 : Blo 1317977 1318659 := bstep (se 1 (by rfl) ⟨988994, by rfl⟩ : syracuseStep 1318659 = 1977989) B1977989
theorem B2285329 : Blo 1317977 2285329 := bstep (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) B1713997
theorem B1318675 : Blo 1317977 1318675 := bstep (se 1 (by rfl) ⟨989006, by rfl⟩ : syracuseStep 1318675 = 1978013) B1978013
theorem B1318691 : Blo 1317977 1318691 := bstep (se 1 (by rfl) ⟨989018, by rfl⟩ : syracuseStep 1318691 = 1978037) B1978037
theorem B1318707 : Blo 1317977 1318707 := bstep (se 1 (by rfl) ⟨989030, by rfl⟩ : syracuseStep 1318707 = 1978061) B1978061
theorem B1318723 : Blo 1317977 1318723 := bstep (se 1 (by rfl) ⟨989042, by rfl⟩ : syracuseStep 1318723 = 1978085) B1978085
theorem B1318739 : Blo 1317977 1318739 := bstep (se 1 (by rfl) ⟨989054, by rfl⟩ : syracuseStep 1318739 = 1978109) B1978109
theorem B1318755 : Blo 1317977 1318755 := bstep (se 1 (by rfl) ⟨989066, by rfl⟩ : syracuseStep 1318755 = 1978133) B1978133
theorem B2408305 : Blo 1317977 2408305 := bstep (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) B1806229
theorem B1318771 : Blo 1317977 1318771 := bstep (se 1 (by rfl) ⟨989078, by rfl⟩ : syracuseStep 1318771 = 1978157) B1978157
theorem B1318787 : Blo 1317977 1318787 := bstep (se 1 (by rfl) ⟨989090, by rfl⟩ : syracuseStep 1318787 = 1978181) B1978181
theorem B8445829 : Blo 1317977 8445829 := bstep (se 4 (by rfl) ⟨791796, by rfl⟩ : syracuseStep 8445829 = 1583593) B1583593
theorem B1318803 : Blo 1317977 1318803 := bstep (se 1 (by rfl) ⟨989102, by rfl⟩ : syracuseStep 1318803 = 1978205) B1978205
theorem B1318819 : Blo 1317977 1318819 := bstep (se 1 (by rfl) ⟨989114, by rfl⟩ : syracuseStep 1318819 = 1978229) B1978229
theorem B3563441 : Blo 1317977 3563441 := bstep (se 2 (by rfl) ⟨1336290, by rfl⟩ : syracuseStep 3563441 = 2672581) B2672581
theorem B1318835 : Blo 1317977 1318835 := bstep (se 1 (by rfl) ⟨989126, by rfl⟩ : syracuseStep 1318835 = 1978253) B1978253
theorem B4448195 : Blo 1317977 4448195 := bstep (se 1 (by rfl) ⟨3336146, by rfl⟩ : syracuseStep 4448195 = 6672293) B6672293
theorem B1318851 : Blo 1317977 1318851 := bstep (se 1 (by rfl) ⟨989138, by rfl⟩ : syracuseStep 1318851 = 1978277) B1978277
theorem B1318867 : Blo 1317977 1318867 := bstep (se 1 (by rfl) ⟨989150, by rfl⟩ : syracuseStep 1318867 = 1978301) B1978301
theorem B1318883 : Blo 1317977 1318883 := bstep (se 1 (by rfl) ⟨989162, by rfl⟩ : syracuseStep 1318883 = 1978325) B1978325
theorem B1318899 : Blo 1317977 1318899 := bstep (se 1 (by rfl) ⟨989174, by rfl⟩ : syracuseStep 1318899 = 1978349) B1978349
theorem B1482763 : Blo 1317977 1482763 := bstep (se 1 (by rfl) ⟨1112072, by rfl⟩ : syracuseStep 1482763 = 2224145) B2224145
theorem B1318923 : Blo 1317977 1318923 := bstep (se 1 (by rfl) ⟨989192, by rfl⟩ : syracuseStep 1318923 = 1978385) B1978385
theorem B9510929 : Blo 1317977 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B1318935 : Blo 1317977 1318935 := bstep (se 1 (by rfl) ⟨989201, by rfl⟩ : syracuseStep 1318935 = 1978403) B1978403
theorem B19005475 : Blo 1317977 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B1318955 : Blo 1317977 1318955 := bstep (se 1 (by rfl) ⟨989216, by rfl⟩ : syracuseStep 1318955 = 1978433) B1978433
theorem B1318967 : Blo 1317977 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B30883909 : Blo 1317977 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B1318987 : Blo 1317977 1318987 := bstep (se 1 (by rfl) ⟨989240, by rfl⟩ : syracuseStep 1318987 = 1978481) B1978481
theorem B1318999 : Blo 1317977 1318999 := bstep (se 1 (by rfl) ⟨989249, by rfl⟩ : syracuseStep 1318999 = 1978499) B1978499
theorem B1319019 : Blo 1317977 1319019 := bstep (se 1 (by rfl) ⟨989264, by rfl⟩ : syracuseStep 1319019 = 1978529) B1978529
theorem B1482871 : Blo 1317977 1482871 := bstep (se 1 (by rfl) ⟨1112153, by rfl⟩ : syracuseStep 1482871 = 2224307) B2224307
theorem B1319031 : Blo 1317977 1319031 := bstep (se 1 (by rfl) ⟨989273, by rfl⟩ : syracuseStep 1319031 = 1978547) B1978547
theorem B2965643 : Blo 1317977 2965643 := bstep (se 1 (by rfl) ⟨2224232, by rfl⟩ : syracuseStep 2965643 = 4448465) B4448465
theorem B1319051 : Blo 1317977 1319051 := bstep (se 1 (by rfl) ⟨989288, by rfl⟩ : syracuseStep 1319051 = 1978577) B1978577
theorem B1319063 : Blo 1317977 1319063 := bstep (se 1 (by rfl) ⟨989297, by rfl⟩ : syracuseStep 1319063 = 1978595) B1978595
theorem B1319083 : Blo 1317977 1319083 := bstep (se 1 (by rfl) ⟨989312, by rfl⟩ : syracuseStep 1319083 = 1978625) B1978625
theorem B1319095 : Blo 1317977 1319095 := bstep (se 1 (by rfl) ⟨989321, by rfl⟩ : syracuseStep 1319095 = 1978643) B1978643
theorem B2965697 : Blo 1317977 2965697 := bstep (se 2 (by rfl) ⟨1112136, by rfl⟩ : syracuseStep 2965697 = 2224273) B2224273
theorem B1319115 : Blo 1317977 1319115 := bstep (se 1 (by rfl) ⟨989336, by rfl⟩ : syracuseStep 1319115 = 1978673) B1978673
theorem B1319127 : Blo 1317977 1319127 := bstep (se 1 (by rfl) ⟨989345, by rfl⟩ : syracuseStep 1319127 = 1978691) B1978691
theorem B1319147 : Blo 1317977 1319147 := bstep (se 1 (by rfl) ⟨989360, by rfl⟩ : syracuseStep 1319147 = 1978721) B1978721
theorem B1319159 : Blo 1317977 1319159 := bstep (se 1 (by rfl) ⟨989369, by rfl⟩ : syracuseStep 1319159 = 1978739) B1978739
theorem B1319179 : Blo 1317977 1319179 := bstep (se 1 (by rfl) ⟨989384, by rfl⟩ : syracuseStep 1319179 = 1978769) B1978769
theorem B1319191 : Blo 1317977 1319191 := bstep (se 1 (by rfl) ⟨989393, by rfl⟩ : syracuseStep 1319191 = 1978787) B1978787
theorem B1483051 : Blo 1317977 1483051 := bstep (se 1 (by rfl) ⟨1112288, by rfl⟩ : syracuseStep 1483051 = 2224577) B2224577
theorem B1319211 : Blo 1317977 1319211 := bstep (se 1 (by rfl) ⟨989408, by rfl⟩ : syracuseStep 1319211 = 1978817) B1978817
theorem B1319223 : Blo 1317977 1319223 := bstep (se 1 (by rfl) ⟨989417, by rfl⟩ : syracuseStep 1319223 = 1978835) B1978835
theorem B24387905 : Blo 1317977 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B1319243 : Blo 1317977 1319243 := bstep (se 1 (by rfl) ⟨989432, by rfl⟩ : syracuseStep 1319243 = 1978865) B1978865
theorem B1319255 : Blo 1317977 1319255 := bstep (se 1 (by rfl) ⟨989441, by rfl⟩ : syracuseStep 1319255 = 1978883) B1978883
theorem B6676829 : Blo 1317977 6676829 := bstep (se 3 (by rfl) ⟨1251905, by rfl⟩ : syracuseStep 6676829 = 2503811) B2503811
theorem B1319275 : Blo 1317977 1319275 := bstep (se 1 (by rfl) ⟨989456, by rfl⟩ : syracuseStep 1319275 = 1978913) B1978913
theorem B1319287 : Blo 1317977 1319287 := bstep (se 1 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 1319287 = 1978931) B1978931
theorem B1319307 : Blo 1317977 1319307 := bstep (se 1 (by rfl) ⟨989480, by rfl⟩ : syracuseStep 1319307 = 1978961) B1978961
theorem B1483159 : Blo 1317977 1483159 := bstep (se 1 (by rfl) ⟨1112369, by rfl⟩ : syracuseStep 1483159 = 2224739) B2224739
theorem B1319319 : Blo 1317977 1319319 := bstep (se 1 (by rfl) ⟨989489, by rfl⟩ : syracuseStep 1319319 = 1978979) B1978979
theorem B2965913 : Blo 1317977 2965913 := bstep (se 2 (by rfl) ⟨1112217, by rfl⟩ : syracuseStep 2965913 = 2224435) B2224435
theorem B1319339 : Blo 1317977 1319339 := bstep (se 1 (by rfl) ⟨989504, by rfl⟩ : syracuseStep 1319339 = 1979009) B1979009
theorem B1319351 : Blo 1317977 1319351 := bstep (se 1 (by rfl) ⟨989513, by rfl⟩ : syracuseStep 1319351 = 1979027) B1979027
theorem B1319371 : Blo 1317977 1319371 := bstep (se 1 (by rfl) ⟨989528, by rfl⟩ : syracuseStep 1319371 = 1979057) B1979057
theorem B1319383 : Blo 1317977 1319383 := bstep (se 1 (by rfl) ⟨989537, by rfl⟩ : syracuseStep 1319383 = 1979075) B1979075
theorem B5710301 : Blo 1317977 5710301 := bstep (se 3 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 5710301 = 2141363) B2141363
theorem B1319403 : Blo 1317977 1319403 := bstep (se 1 (by rfl) ⟨989552, by rfl⟩ : syracuseStep 1319403 = 1979105) B1979105
theorem B2966003 : Blo 1317977 2966003 := bstep (se 1 (by rfl) ⟨2224502, by rfl⟩ : syracuseStep 2966003 = 4449005) B4449005
theorem B1319415 : Blo 1317977 1319415 := bstep (se 1 (by rfl) ⟨989561, by rfl⟩ : syracuseStep 1319415 = 1979123) B1979123
theorem B1319435 : Blo 1317977 1319435 := bstep (se 1 (by rfl) ⟨989576, by rfl⟩ : syracuseStep 1319435 = 1979153) B1979153
theorem B2966039 : Blo 1317977 2966039 := bstep (se 1 (by rfl) ⟨2224529, by rfl⟩ : syracuseStep 2966039 = 4449059) B4449059
theorem B1319447 : Blo 1317977 1319447 := bstep (se 1 (by rfl) ⟨989585, by rfl⟩ : syracuseStep 1319447 = 1979171) B1979171
theorem B1319467 : Blo 1317977 1319467 := bstep (se 1 (by rfl) ⟨989600, by rfl⟩ : syracuseStep 1319467 = 1979201) B1979201
theorem B4448843 : Blo 1317977 4448843 := bstep (se 1 (by rfl) ⟨3336632, by rfl⟩ : syracuseStep 4448843 = 6673265) B6673265
theorem B1483339 : Blo 1317977 1483339 := bstep (se 1 (by rfl) ⟨1112504, by rfl⟩ : syracuseStep 1483339 = 2225009) B2225009
theorem B1483447 : Blo 1317977 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B2966219 : Blo 1317977 2966219 := bstep (se 1 (by rfl) ⟨2224664, by rfl⟩ : syracuseStep 2966219 = 4449329) B4449329
theorem B2409203 : Blo 1317977 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B2966273 : Blo 1317977 2966273 := bstep (se 2 (by rfl) ⟨1112352, by rfl⟩ : syracuseStep 2966273 = 2224705) B2224705
theorem B2409239 : Blo 1317977 2409239 := bstep (se 1 (by rfl) ⟨1806929, by rfl⟩ : syracuseStep 2409239 = 3613859) B3613859
theorem B4449113 : Blo 1317977 4449113 := bstep (se 2 (by rfl) ⟨1668417, by rfl⟩ : syracuseStep 4449113 = 3336835) B3336835
theorem B1483627 : Blo 1317977 1483627 := bstep (se 1 (by rfl) ⟨1112720, by rfl⟩ : syracuseStep 1483627 = 2225441) B2225441
theorem B5006225 : Blo 1317977 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B7512983 : Blo 1317977 7512983 := bstep (se 1 (by rfl) ⟨5634737, by rfl⟩ : syracuseStep 7512983 = 11269475) B11269475
theorem B1483735 : Blo 1317977 1483735 := bstep (se 1 (by rfl) ⟨1112801, by rfl⟩ : syracuseStep 1483735 = 2225603) B2225603
theorem B2966489 : Blo 1317977 2966489 := bstep (se 2 (by rfl) ⟨1112433, by rfl⟩ : syracuseStep 2966489 = 2224867) B2224867
theorem B2966579 : Blo 1317977 2966579 := bstep (se 1 (by rfl) ⟨2224934, by rfl⟩ : syracuseStep 2966579 = 4449869) B4449869
theorem B2966615 : Blo 1317977 2966615 := bstep (se 1 (by rfl) ⟨2224961, by rfl⟩ : syracuseStep 2966615 = 4449923) B4449923
theorem B1483915 : Blo 1317977 1483915 := bstep (se 1 (by rfl) ⟨1112936, by rfl⟩ : syracuseStep 1483915 = 2225873) B2225873
theorem B1484023 : Blo 1317977 1484023 := bstep (se 1 (by rfl) ⟨1113017, by rfl⟩ : syracuseStep 1484023 = 2226035) B2226035
theorem B2966795 : Blo 1317977 2966795 := bstep (se 1 (by rfl) ⟨2225096, by rfl⟩ : syracuseStep 2966795 = 4450193) B4450193
theorem B3474739 : Blo 1317977 3474739 := bstep (se 1 (by rfl) ⟨2606054, by rfl⟩ : syracuseStep 3474739 = 5212109) B5212109
theorem B8348993 : Blo 1317977 8348993 := bstep (se 2 (by rfl) ⟨3130872, by rfl⟩ : syracuseStep 8348993 = 6261745) B6261745
theorem B2966849 : Blo 1317977 2966849 := bstep (se 2 (by rfl) ⟨1112568, by rfl⟩ : syracuseStep 2966849 = 2225137) B2225137
theorem B5006681 : Blo 1317977 5006681 := bstep (se 2 (by rfl) ⟨1877505, by rfl⟩ : syracuseStep 5006681 = 3755011) B3755011
theorem B1484203 : Blo 1317977 1484203 := bstep (se 1 (by rfl) ⟨1113152, by rfl⟩ : syracuseStep 1484203 = 2226305) B2226305
theorem B4752857 : Blo 1317977 4752857 := bstep (se 2 (by rfl) ⟨1782321, by rfl⟩ : syracuseStep 4752857 = 3564643) B3564643
theorem B4449815 : Blo 1317977 4449815 := bstep (se 1 (by rfl) ⟨3337361, by rfl⟩ : syracuseStep 4449815 = 6674723) B6674723
theorem B1484311 : Blo 1317977 1484311 := bstep (se 1 (by rfl) ⟨1113233, by rfl⟩ : syracuseStep 1484311 = 2226467) B2226467
theorem B2967065 : Blo 1317977 2967065 := bstep (se 2 (by rfl) ⟨1112649, by rfl⟩ : syracuseStep 2967065 = 2225299) B2225299
theorem B5006893 : Blo 1317977 5006893 := bstep (se 3 (by rfl) ⟨938792, by rfl⟩ : syracuseStep 5006893 = 1877585) B1877585
theorem B2967155 : Blo 1317977 2967155 := bstep (se 1 (by rfl) ⟨2225366, by rfl⟩ : syracuseStep 2967155 = 4450733) B4450733
theorem B2967191 : Blo 1317977 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B3565259 : Blo 1317977 3565259 := bstep (se 1 (by rfl) ⟨2673944, by rfl⟩ : syracuseStep 3565259 = 5347889) B5347889
theorem B3008279 : Blo 1317977 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B3753803 : Blo 1317977 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B2967371 : Blo 1317977 2967371 := bstep (se 1 (by rfl) ⟨2225528, by rfl⟩ : syracuseStep 2967371 = 4451057) B4451057
theorem B3565387 : Blo 1317977 3565387 := bstep (se 1 (by rfl) ⟨2674040, by rfl⟩ : syracuseStep 3565387 = 5348081) B5348081
theorem B5007197 : Blo 1317977 5007197 := bstep (se 3 (by rfl) ⟨938849, by rfl⟩ : syracuseStep 5007197 = 1877699) B1877699
theorem B1337195 : Blo 1317977 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B2967425 : Blo 1317977 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B1877899 : Blo 1317977 1877899 := bstep (se 1 (by rfl) ⟨1408424, by rfl⟩ : syracuseStep 1877899 = 2816849) B2816849
theorem B7129133 : Blo 1317977 7129133 := bstep (se 3 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 7129133 = 2673425) B2673425
theorem B4450355 : Blo 1317977 4450355 := bstep (se 1 (by rfl) ⟨3337766, by rfl⟩ : syracuseStep 4450355 = 6675533) B6675533
theorem B6015041 : Blo 1317977 6015041 := bstep (se 2 (by rfl) ⟨2255640, by rfl⟩ : syracuseStep 6015041 = 4511281) B4511281
theorem B2967641 : Blo 1317977 2967641 := bstep (se 2 (by rfl) ⟨1112865, by rfl⟩ : syracuseStep 2967641 = 2225731) B2225731
theorem B2967731 : Blo 1317977 2967731 := bstep (se 1 (by rfl) ⟨2225798, by rfl⟩ : syracuseStep 2967731 = 4451597) B4451597
theorem B2672833 : Blo 1317977 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B2967767 : Blo 1317977 2967767 := bstep (se 1 (by rfl) ⟨2225825, by rfl⟩ : syracuseStep 2967767 = 4451651) B4451651
theorem B4450625 : Blo 1317977 4450625 := bstep (se 2 (by rfl) ⟨1668984, by rfl⟩ : syracuseStep 4450625 = 3337969) B3337969
theorem B2967947 : Blo 1317977 2967947 := bstep (se 1 (by rfl) ⟨2225960, by rfl⟩ : syracuseStep 2967947 = 4451921) B4451921
theorem B6678935 : Blo 1317977 6678935 := bstep (se 1 (by rfl) ⟨5009201, by rfl⟩ : syracuseStep 6678935 = 10018403) B10018403
theorem B2968001 : Blo 1317977 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B6425219 : Blo 1317977 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B2968217 : Blo 1317977 2968217 := bstep (se 2 (by rfl) ⟨1113081, by rfl⟩ : syracuseStep 2968217 = 2226163) B2226163
theorem B1977035 : Blo 1317977 1977035 := bstep (se 1 (by rfl) ⟨1482776, by rfl⟩ : syracuseStep 1977035 = 2965553) B2965553
theorem B1977047 : Blo 1317977 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B2968307 : Blo 1317977 2968307 := bstep (se 1 (by rfl) ⟨2226230, by rfl⟩ : syracuseStep 2968307 = 4452461) B4452461
theorem B2968343 : Blo 1317977 2968343 := bstep (se 1 (by rfl) ⟨2226257, by rfl⟩ : syracuseStep 2968343 = 4452515) B4452515
theorem B1977113 : Blo 1317977 1977113 := bstep (se 2 (by rfl) ⟨741417, by rfl⟩ : syracuseStep 1977113 = 1482835) B1482835
theorem B3566425 : Blo 1317977 3566425 := bstep (se 2 (by rfl) ⟨1337409, by rfl⟩ : syracuseStep 3566425 = 2674819) B2674819
theorem B4451165 : Blo 1317977 4451165 := bstep (se 3 (by rfl) ⟨834593, by rfl⟩ : syracuseStep 4451165 = 1669187) B1669187
theorem B1977227 : Blo 1317977 1977227 := bstep (se 1 (by rfl) ⟨1482920, by rfl⟩ : syracuseStep 1977227 = 2965841) B2965841
theorem B1977239 : Blo 1317977 1977239 := bstep (se 1 (by rfl) ⟨1482929, by rfl⟩ : syracuseStep 1977239 = 2965859) B2965859
theorem B3337139 : Blo 1317977 3337139 := bstep (se 1 (by rfl) ⟨2502854, by rfl⟩ : syracuseStep 3337139 = 5005709) B5005709
theorem B2968523 : Blo 1317977 2968523 := bstep (se 1 (by rfl) ⟨2226392, by rfl⟩ : syracuseStep 2968523 = 4452785) B4452785
theorem B1977305 : Blo 1317977 1977305 := bstep (se 2 (by rfl) ⟨741489, by rfl⟩ : syracuseStep 1977305 = 1482979) B1482979
theorem B2968577 : Blo 1317977 2968577 := bstep (se 2 (by rfl) ⟨1113216, by rfl⟩ : syracuseStep 2968577 = 2226433) B2226433
theorem B1977419 : Blo 1317977 1977419 := bstep (se 1 (by rfl) ⟨1483064, by rfl⟩ : syracuseStep 1977419 = 2966129) B2966129
theorem B1977431 : Blo 1317977 1977431 := bstep (se 1 (by rfl) ⟨1483073, by rfl⟩ : syracuseStep 1977431 = 2966147) B2966147
theorem B1977497 : Blo 1317977 1977497 := bstep (se 2 (by rfl) ⟨741561, by rfl⟩ : syracuseStep 1977497 = 1483123) B1483123
theorem B4885697 : Blo 1317977 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B3337433 : Blo 1317977 3337433 := bstep (se 2 (by rfl) ⟨1251537, by rfl⟩ : syracuseStep 3337433 = 2503075) B2503075
theorem B2968793 : Blo 1317977 2968793 := bstep (se 2 (by rfl) ⟨1113297, by rfl⟩ : syracuseStep 2968793 = 2226595) B2226595
theorem B1977611 : Blo 1317977 1977611 := bstep (se 1 (by rfl) ⟨1483208, by rfl⟩ : syracuseStep 1977611 = 2966417) B2966417
theorem B1977623 : Blo 1317977 1977623 := bstep (se 1 (by rfl) ⟨1483217, by rfl⟩ : syracuseStep 1977623 = 2966435) B2966435
theorem B1977689 : Blo 1317977 1977689 := bstep (se 2 (by rfl) ⟨741633, by rfl⟩ : syracuseStep 1977689 = 1483267) B1483267
theorem B2674073 : Blo 1317977 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B5418419 : Blo 1317977 5418419 := bstep (se 1 (by rfl) ⟨4063814, by rfl⟩ : syracuseStep 5418419 = 8127629) B8127629
theorem B1977803 : Blo 1317977 1977803 := bstep (se 1 (by rfl) ⟨1483352, by rfl⟩ : syracuseStep 1977803 = 2966705) B2966705
theorem B2502103 : Blo 1317977 2502103 := bstep (se 1 (by rfl) ⟨1876577, by rfl⟩ : syracuseStep 2502103 = 3753155) B3753155
theorem B1977815 : Blo 1317977 1977815 := bstep (se 1 (by rfl) ⟨1483361, by rfl⟩ : syracuseStep 1977815 = 2966723) B2966723
theorem B1977881 : Blo 1317977 1977881 := bstep (se 2 (by rfl) ⟨741705, by rfl⟩ : syracuseStep 1977881 = 1483411) B1483411
theorem B1977995 : Blo 1317977 1977995 := bstep (se 1 (by rfl) ⟨1483496, by rfl⟩ : syracuseStep 1977995 = 2966993) B2966993
theorem B7925399 : Blo 1317977 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B1978007 : Blo 1317977 1978007 := bstep (se 1 (by rfl) ⟨1483505, by rfl⟩ : syracuseStep 1978007 = 2967011) B2967011
theorem B10145459 : Blo 1317977 10145459 := bstep (se 1 (by rfl) ⟨7609094, by rfl⟩ : syracuseStep 10145459 = 15218189) B15218189
theorem B2502323 : Blo 1317977 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B1978073 : Blo 1317977 1978073 := bstep (se 2 (by rfl) ⟨741777, by rfl⟩ : syracuseStep 1978073 = 1483555) B1483555
theorem B1978187 : Blo 1317977 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B1978199 : Blo 1317977 1978199 := bstep (se 1 (by rfl) ⟨1483649, by rfl⟩ : syracuseStep 1978199 = 2967299) B2967299
theorem B4222813 : Blo 1317977 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B2502551 : Blo 1317977 2502551 := bstep (se 1 (by rfl) ⟨1876913, by rfl⟩ : syracuseStep 2502551 = 3753827) B3753827
theorem B1978265 : Blo 1317977 1978265 := bstep (se 2 (by rfl) ⟨741849, by rfl⟩ : syracuseStep 1978265 = 1483699) B1483699
theorem B4452299 : Blo 1317977 4452299 := bstep (se 1 (by rfl) ⟨3339224, by rfl⟩ : syracuseStep 4452299 = 6678449) B6678449
theorem B1978379 : Blo 1317977 1978379 := bstep (se 1 (by rfl) ⟨1483784, by rfl⟩ : syracuseStep 1978379 = 2967569) B2967569
theorem B1978391 : Blo 1317977 1978391 := bstep (se 1 (by rfl) ⟨1483793, by rfl⟩ : syracuseStep 1978391 = 2967587) B2967587
theorem B1978457 : Blo 1317977 1978457 := bstep (se 2 (by rfl) ⟨741921, by rfl⟩ : syracuseStep 1978457 = 1483843) B1483843
theorem B2502809 : Blo 1317977 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B5632193 : Blo 1317977 5632193 := bstep (se 2 (by rfl) ⟨2112072, by rfl⟩ : syracuseStep 5632193 = 4224145) B4224145
theorem B1978571 : Blo 1317977 1978571 := bstep (se 1 (by rfl) ⟨1483928, by rfl⟩ : syracuseStep 1978571 = 2967857) B2967857
theorem B1978583 : Blo 1317977 1978583 := bstep (se 1 (by rfl) ⟨1483937, by rfl⟩ : syracuseStep 1978583 = 2967875) B2967875
theorem B4452569 : Blo 1317977 4452569 := bstep (se 2 (by rfl) ⟨1669713, by rfl⟩ : syracuseStep 4452569 = 3339427) B3339427
theorem B3756253 : Blo 1317977 3756253 := bstep (se 3 (by rfl) ⟨704297, by rfl⟩ : syracuseStep 3756253 = 1408595) B1408595
theorem B1978649 : Blo 1317977 1978649 := bstep (se 2 (by rfl) ⟨741993, by rfl⟩ : syracuseStep 1978649 = 1483987) B1483987
theorem B5632345 : Blo 1317977 5632345 := bstep (se 2 (by rfl) ⟨2112129, by rfl⟩ : syracuseStep 5632345 = 4224259) B4224259
theorem B5009795 : Blo 1317977 5009795 := bstep (se 1 (by rfl) ⟨3757346, by rfl⟩ : syracuseStep 5009795 = 7514693) B7514693
theorem B2224523 : Blo 1317977 2224523 := bstep (se 1 (by rfl) ⟨1668392, by rfl⟩ : syracuseStep 2224523 = 3336785) B3336785
theorem B1978763 : Blo 1317977 1978763 := bstep (se 1 (by rfl) ⟨1484072, by rfl⟩ : syracuseStep 1978763 = 2968145) B2968145
theorem B5009809 : Blo 1317977 5009809 := bstep (se 2 (by rfl) ⟨1878678, by rfl⟩ : syracuseStep 5009809 = 3757357) B3757357
theorem B1978775 : Blo 1317977 1978775 := bstep (se 1 (by rfl) ⟨1484081, by rfl⟩ : syracuseStep 1978775 = 2968163) B2968163
theorem B4280779 : Blo 1317977 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B1978841 : Blo 1317977 1978841 := bstep (se 2 (by rfl) ⟨742065, by rfl⟩ : syracuseStep 1978841 = 1484131) B1484131
theorem B2224651 : Blo 1317977 2224651 := bstep (se 1 (by rfl) ⟨1668488, by rfl⟩ : syracuseStep 2224651 = 3336977) B3336977
theorem B6672941 : Blo 1317977 6672941 := bstep (se 3 (by rfl) ⟨1251176, by rfl⟩ : syracuseStep 6672941 = 2502353) B2502353
theorem B2503219 : Blo 1317977 2503219 := bstep (se 1 (by rfl) ⟨1877414, by rfl⟩ : syracuseStep 2503219 = 3754829) B3754829
theorem B8802881 : Blo 1317977 8802881 := bstep (se 2 (by rfl) ⟨3301080, by rfl⟩ : syracuseStep 8802881 = 6602161) B6602161
theorem B1978955 : Blo 1317977 1978955 := bstep (se 1 (by rfl) ⟨1484216, by rfl⟩ : syracuseStep 1978955 = 2968433) B2968433
theorem B1978967 : Blo 1317977 1978967 := bstep (se 1 (by rfl) ⟨1484225, by rfl⟩ : syracuseStep 1978967 = 2968451) B2968451
theorem B14250647 : Blo 1317977 14250647 := bstep (se 1 (by rfl) ⟨10687985, by rfl⟩ : syracuseStep 14250647 = 21375971) B21375971
theorem B1692311 : Blo 1317977 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B2224793 : Blo 1317977 2224793 := bstep (se 2 (by rfl) ⟨834297, by rfl⟩ : syracuseStep 2224793 = 1668595) B1668595
theorem B1979033 : Blo 1317977 1979033 := bstep (se 2 (by rfl) ⟨742137, by rfl⟩ : syracuseStep 1979033 = 1484275) B1484275
theorem B1979147 : Blo 1317977 1979147 := bstep (se 1 (by rfl) ⟨1484360, by rfl⟩ : syracuseStep 1979147 = 2968721) B2968721
theorem B1979159 : Blo 1317977 1979159 := bstep (se 1 (by rfl) ⟨1484369, by rfl⟩ : syracuseStep 1979159 = 2968739) B2968739
theorem B2224921 : Blo 1317977 2224921 := bstep (se 2 (by rfl) ⟨834345, by rfl⟩ : syracuseStep 2224921 = 1668691) B1668691
theorem B3339083 : Blo 1317977 3339083 := bstep (se 1 (by rfl) ⟨2504312, by rfl⟩ : syracuseStep 3339083 = 5008625) B5008625
theorem B1782667 : Blo 1317977 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B5346199 : Blo 1317977 5346199 := bstep (se 1 (by rfl) ⟨4009649, by rfl⟩ : syracuseStep 5346199 = 8019299) B8019299
theorem B2503705 : Blo 1317977 2503705 := bstep (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) B1877779
theorem B3429427 : Blo 1317977 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B11261105 : Blo 1317977 11261105 := bstep (se 2 (by rfl) ⟨4222914, by rfl⟩ : syracuseStep 11261105 = 8445829) B8445829
theorem B7509293 : Blo 1317977 7509293 := bstep (se 3 (by rfl) ⟨1407992, by rfl⟩ : syracuseStep 7509293 = 2815985) B2815985
theorem B2815319 : Blo 1317977 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B2225495 : Blo 1317977 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B16258421 : Blo 1317977 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B3806615 : Blo 1317977 3806615 := bstep (se 1 (by rfl) ⟨2854961, by rfl⟩ : syracuseStep 3806615 = 5709923) B5709923
theorem B2225623 : Blo 1317977 2225623 := bstep (se 1 (by rfl) ⟨1669217, by rfl⟩ : syracuseStep 2225623 = 3338435) B3338435
theorem B2815489 : Blo 1317977 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B2504267 : Blo 1317977 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B15021773 : Blo 1317977 15021773 := bstep (se 3 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 15021773 = 5633165) B5633165
theorem B2504449 : Blo 1317977 2504449 := bstep (se 2 (by rfl) ⟨939168, by rfl⟩ : syracuseStep 2504449 = 1878337) B1878337
theorem B2815831 : Blo 1317977 2815831 := bstep (se 1 (by rfl) ⟨2111873, by rfl⟩ : syracuseStep 2815831 = 4223747) B4223747
theorem B10696549 : Blo 1317977 10696549 := bstep (se 4 (by rfl) ⟨1002801, by rfl⟩ : syracuseStep 10696549 = 2005603) B2005603
theorem B1669015 : Blo 1317977 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B60889157 : Blo 1317977 60889157 := bstep (se 4 (by rfl) ⟨5708358, by rfl⟩ : syracuseStep 60889157 = 11416717) B11416717
theorem B2226251 : Blo 1317977 2226251 := bstep (se 1 (by rfl) ⟨1669688, by rfl⟩ : syracuseStep 2226251 = 3339377) B3339377
theorem B10016945 : Blo 1317977 10016945 := bstep (se 2 (by rfl) ⟨3756354, by rfl⟩ : syracuseStep 10016945 = 7512709) B7512709
theorem B2226379 : Blo 1317977 2226379 := bstep (se 1 (by rfl) ⟨1669784, by rfl⟩ : syracuseStep 2226379 = 3339569) B3339569
theorem B2005337 : Blo 1317977 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B2226521 : Blo 1317977 2226521 := bstep (se 2 (by rfl) ⟨834945, by rfl⟩ : syracuseStep 2226521 = 1669891) B1669891
theorem B11270501 : Blo 1317977 11270501 := bstep (se 4 (by rfl) ⟨1056609, by rfl⟩ : syracuseStep 11270501 = 2113219) B2113219
theorem B5347757 : Blo 1317977 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B5708225 : Blo 1317977 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B8452673 : Blo 1317977 8452673 := bstep (se 2 (by rfl) ⟨3169752, by rfl⟩ : syracuseStep 8452673 = 6339505) B6339505
theorem B2816651 : Blo 1317977 2816651 := bstep (se 1 (by rfl) ⟨2112488, by rfl⟩ : syracuseStep 2816651 = 4224977) B4224977
theorem B10017431 : Blo 1317977 10017431 := bstep (se 1 (by rfl) ⟨7513073, by rfl⟩ : syracuseStep 10017431 = 15026147) B15026147
theorem B1669835 : Blo 1317977 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B2005847 : Blo 1317977 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B6421427 : Blo 1317977 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B128343001 : Blo 1317977 128343001 := bstep (se 2 (by rfl) ⟨48128625, by rfl⟩ : syracuseStep 128343001 = 96257251) B96257251
theorem B104225753 : Blo 1317977 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B2817011 : Blo 1317977 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B6011921 : Blo 1317977 6011921 := bstep (se 2 (by rfl) ⟨2254470, by rfl⟩ : syracuseStep 6011921 = 4508941) B4508941
theorem B1317995 : Blo 1317977 1317995 := bstep (se 1 (by rfl) ⟨988496, by rfl⟩ : syracuseStep 1317995 = 1976993) B1976993
theorem B1318007 : Blo 1317977 1318007 := bstep (se 1 (by rfl) ⟨988505, by rfl⟩ : syracuseStep 1318007 = 1977011) B1977011
theorem B1318027 : Blo 1317977 1318027 := bstep (se 1 (by rfl) ⟨988520, by rfl⟩ : syracuseStep 1318027 = 1977041) B1977041
theorem B1318039 : Blo 1317977 1318039 := bstep (se 1 (by rfl) ⟨988529, by rfl⟩ : syracuseStep 1318039 = 1977059) B1977059
theorem B1408151 : Blo 1317977 1408151 := bstep (se 1 (by rfl) ⟨1056113, by rfl⟩ : syracuseStep 1408151 = 2112227) B2112227
theorem B1318059 : Blo 1317977 1318059 := bstep (se 1 (by rfl) ⟨988544, by rfl⟩ : syracuseStep 1318059 = 1977089) B1977089
theorem B18791605 : Blo 1317977 18791605 := bstep (se 5 (by rfl) ⟨880856, by rfl⟩ : syracuseStep 18791605 = 1761713) B1761713
theorem B1318071 : Blo 1317977 1318071 := bstep (se 1 (by rfl) ⟨988553, by rfl⟩ : syracuseStep 1318071 = 1977107) B1977107
theorem B1318091 : Blo 1317977 1318091 := bstep (se 1 (by rfl) ⟨988568, by rfl⟩ : syracuseStep 1318091 = 1977137) B1977137
theorem B1318103 : Blo 1317977 1318103 := bstep (se 1 (by rfl) ⟨988577, by rfl⟩ : syracuseStep 1318103 = 1977155) B1977155
theorem B1318123 : Blo 1317977 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B1318135 : Blo 1317977 1318135 := bstep (se 1 (by rfl) ⟨988601, by rfl⟩ : syracuseStep 1318135 = 1977203) B1977203
theorem B1318155 : Blo 1317977 1318155 := bstep (se 1 (by rfl) ⟨988616, by rfl⟩ : syracuseStep 1318155 = 1977233) B1977233
theorem B1318167 : Blo 1317977 1318167 := bstep (se 1 (by rfl) ⟨988625, by rfl⟩ : syracuseStep 1318167 = 1977251) B1977251
theorem B1318187 : Blo 1317977 1318187 := bstep (se 1 (by rfl) ⟨988640, by rfl⟩ : syracuseStep 1318187 = 1977281) B1977281
theorem B1318199 : Blo 1317977 1318199 := bstep (se 1 (by rfl) ⟨988649, by rfl⟩ : syracuseStep 1318199 = 1977299) B1977299
theorem B13712705 : Blo 1317977 13712705 := bstep (se 2 (by rfl) ⟨5142264, by rfl⟩ : syracuseStep 13712705 = 10284529) B10284529
theorem B1318219 : Blo 1317977 1318219 := bstep (se 1 (by rfl) ⟨988664, by rfl⟩ : syracuseStep 1318219 = 1977329) B1977329
theorem B1318231 : Blo 1317977 1318231 := bstep (se 1 (by rfl) ⟨988673, by rfl⟩ : syracuseStep 1318231 = 1977347) B1977347
theorem B1318251 : Blo 1317977 1318251 := bstep (se 1 (by rfl) ⟨988688, by rfl⟩ : syracuseStep 1318251 = 1977377) B1977377
theorem B1318263 : Blo 1317977 1318263 := bstep (se 1 (by rfl) ⟨988697, by rfl⟩ : syracuseStep 1318263 = 1977395) B1977395
theorem B1318283 : Blo 1317977 1318283 := bstep (se 1 (by rfl) ⟨988712, by rfl⟩ : syracuseStep 1318283 = 1977425) B1977425
theorem B1318295 : Blo 1317977 1318295 := bstep (se 1 (by rfl) ⟨988721, by rfl⟩ : syracuseStep 1318295 = 1977443) B1977443
theorem B2375065 : Blo 1317977 2375065 := bstep (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) B1781299
theorem B1318315 : Blo 1317977 1318315 := bstep (se 1 (by rfl) ⟨988736, by rfl⟩ : syracuseStep 1318315 = 1977473) B1977473
theorem B1318327 : Blo 1317977 1318327 := bstep (se 1 (by rfl) ⟨988745, by rfl⟩ : syracuseStep 1318327 = 1977491) B1977491
theorem B5004737 : Blo 1317977 5004737 := bstep (se 2 (by rfl) ⟨1876776, by rfl⟩ : syracuseStep 5004737 = 3753553) B3753553
theorem B1318347 : Blo 1317977 1318347 := bstep (se 1 (by rfl) ⟨988760, by rfl⟩ : syracuseStep 1318347 = 1977521) B1977521
theorem B1318359 : Blo 1317977 1318359 := bstep (se 1 (by rfl) ⟨988769, by rfl⟩ : syracuseStep 1318359 = 1977539) B1977539
theorem B1318379 : Blo 1317977 1318379 := bstep (se 1 (by rfl) ⟨988784, by rfl⟩ : syracuseStep 1318379 = 1977569) B1977569
theorem B1318391 : Blo 1317977 1318391 := bstep (se 1 (by rfl) ⟨988793, by rfl⟩ : syracuseStep 1318391 = 1977587) B1977587
theorem B1318411 : Blo 1317977 1318411 := bstep (se 1 (by rfl) ⟨988808, by rfl⟩ : syracuseStep 1318411 = 1977617) B1977617
theorem B1318423 : Blo 1317977 1318423 := bstep (se 1 (by rfl) ⟨988817, by rfl⟩ : syracuseStep 1318423 = 1977635) B1977635
theorem B1318443 : Blo 1317977 1318443 := bstep (se 1 (by rfl) ⟨988832, by rfl⟩ : syracuseStep 1318443 = 1977665) B1977665
theorem B1318455 : Blo 1317977 1318455 := bstep (se 1 (by rfl) ⟨988841, by rfl⟩ : syracuseStep 1318455 = 1977683) B1977683
theorem B1318475 : Blo 1317977 1318475 := bstep (se 1 (by rfl) ⟨988856, by rfl⟩ : syracuseStep 1318475 = 1977713) B1977713
theorem B1318487 : Blo 1317977 1318487 := bstep (se 1 (by rfl) ⟨988865, by rfl⟩ : syracuseStep 1318487 = 1977731) B1977731
theorem B1318507 : Blo 1317977 1318507 := bstep (se 1 (by rfl) ⟨988880, by rfl⟩ : syracuseStep 1318507 = 1977761) B1977761
theorem B1318519 : Blo 1317977 1318519 := bstep (se 1 (by rfl) ⟨988889, by rfl⟩ : syracuseStep 1318519 = 1977779) B1977779
theorem B1318539 : Blo 1317977 1318539 := bstep (se 1 (by rfl) ⟨988904, by rfl⟩ : syracuseStep 1318539 = 1977809) B1977809
theorem B1318551 : Blo 1317977 1318551 := bstep (se 1 (by rfl) ⟨988913, by rfl⟩ : syracuseStep 1318551 = 1977827) B1977827
theorem B1318571 : Blo 1317977 1318571 := bstep (se 1 (by rfl) ⟨988928, by rfl⟩ : syracuseStep 1318571 = 1977857) B1977857
theorem B5635763 : Blo 1317977 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B1318583 : Blo 1317977 1318583 := bstep (se 1 (by rfl) ⟨988937, by rfl⟩ : syracuseStep 1318583 = 1977875) B1977875
theorem B3047105 : Blo 1317977 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B1318603 : Blo 1317977 1318603 := bstep (se 1 (by rfl) ⟨988952, by rfl⟩ : syracuseStep 1318603 = 1977905) B1977905
theorem B1318615 : Blo 1317977 1318615 := bstep (se 1 (by rfl) ⟨988961, by rfl⟩ : syracuseStep 1318615 = 1977923) B1977923
theorem B1318635 : Blo 1317977 1318635 := bstep (se 1 (by rfl) ⟨988976, by rfl⟩ : syracuseStep 1318635 = 1977953) B1977953
theorem B1318647 : Blo 1317977 1318647 := bstep (se 1 (by rfl) ⟨988985, by rfl⟩ : syracuseStep 1318647 = 1977971) B1977971
theorem B1318667 : Blo 1317977 1318667 := bstep (se 1 (by rfl) ⟨989000, by rfl⟩ : syracuseStep 1318667 = 1978001) B1978001
theorem B1318679 : Blo 1317977 1318679 := bstep (se 1 (by rfl) ⟨989009, by rfl⟩ : syracuseStep 1318679 = 1978019) B1978019
theorem B2113303 : Blo 1317977 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B1318699 : Blo 1317977 1318699 := bstep (se 1 (by rfl) ⟨989024, by rfl⟩ : syracuseStep 1318699 = 1978049) B1978049
theorem B1318711 : Blo 1317977 1318711 := bstep (se 1 (by rfl) ⟨989033, by rfl⟩ : syracuseStep 1318711 = 1978067) B1978067
theorem B3211073 : Blo 1317977 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B1318731 : Blo 1317977 1318731 := bstep (se 1 (by rfl) ⟨989048, by rfl⟩ : syracuseStep 1318731 = 1978097) B1978097
theorem B1318743 : Blo 1317977 1318743 := bstep (se 1 (by rfl) ⟨989057, by rfl⟩ : syracuseStep 1318743 = 1978115) B1978115
theorem B3170137 : Blo 1317977 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B1318763 : Blo 1317977 1318763 := bstep (se 1 (by rfl) ⟨989072, by rfl⟩ : syracuseStep 1318763 = 1978145) B1978145
theorem B1318775 : Blo 1317977 1318775 := bstep (se 1 (by rfl) ⟨989081, by rfl⟩ : syracuseStep 1318775 = 1978163) B1978163
theorem B1318795 : Blo 1317977 1318795 := bstep (se 1 (by rfl) ⟨989096, by rfl⟩ : syracuseStep 1318795 = 1978193) B1978193
theorem B1318807 : Blo 1317977 1318807 := bstep (se 1 (by rfl) ⟨989105, by rfl⟩ : syracuseStep 1318807 = 1978211) B1978211
theorem B1318827 : Blo 1317977 1318827 := bstep (se 1 (by rfl) ⟨989120, by rfl⟩ : syracuseStep 1318827 = 1978241) B1978241
theorem B1318839 : Blo 1317977 1318839 := bstep (se 1 (by rfl) ⟨989129, by rfl⟩ : syracuseStep 1318839 = 1978259) B1978259
theorem B2375627 : Blo 1317977 2375627 := bstep (se 1 (by rfl) ⟨1781720, by rfl⟩ : syracuseStep 2375627 = 3563441) B3563441
theorem B1318859 : Blo 1317977 1318859 := bstep (se 1 (by rfl) ⟨989144, by rfl⟩ : syracuseStep 1318859 = 1978289) B1978289
theorem B2965463 : Blo 1317977 2965463 := bstep (se 1 (by rfl) ⟨2224097, by rfl⟩ : syracuseStep 2965463 = 4448195) B4448195
theorem B1318871 : Blo 1317977 1318871 := bstep (se 1 (by rfl) ⟨989153, by rfl⟩ : syracuseStep 1318871 = 1978307) B1978307
theorem B1318891 : Blo 1317977 1318891 := bstep (se 1 (by rfl) ⟨989168, by rfl⟩ : syracuseStep 1318891 = 1978337) B1978337
theorem B1318903 : Blo 1317977 1318903 := bstep (se 1 (by rfl) ⟨989177, by rfl⟩ : syracuseStep 1318903 = 1978355) B1978355
theorem B15015941 : Blo 1317977 15015941 := bstep (se 4 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 15015941 = 2815489) B2815489
theorem B1318919 : Blo 1317977 1318919 := bstep (se 1 (by rfl) ⟨989189, by rfl⟩ : syracuseStep 1318919 = 1978379) B1978379
theorem B6340619 : Blo 1317977 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B1318927 : Blo 1317977 1318927 := bstep (se 1 (by rfl) ⟨989195, by rfl⟩ : syracuseStep 1318927 = 1978391) B1978391
theorem B16031789 : Blo 1317977 16031789 := bstep (se 3 (by rfl) ⟨3005960, by rfl⟩ : syracuseStep 16031789 = 6011921) B6011921
theorem B1318971 : Blo 1317977 1318971 := bstep (se 1 (by rfl) ⟨989228, by rfl⟩ : syracuseStep 1318971 = 1978457) B1978457
theorem B1319047 : Blo 1317977 1319047 := bstep (se 1 (by rfl) ⟨989285, by rfl⟩ : syracuseStep 1319047 = 1978571) B1978571
theorem B1319055 : Blo 1317977 1319055 := bstep (se 1 (by rfl) ⟨989291, by rfl⟩ : syracuseStep 1319055 = 1978583) B1978583
theorem B1319099 : Blo 1317977 1319099 := bstep (se 1 (by rfl) ⟨989324, by rfl⟩ : syracuseStep 1319099 = 1978649) B1978649
theorem B3563777 : Blo 1317977 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B1483015 : Blo 1317977 1483015 := bstep (se 1 (by rfl) ⟨1112261, by rfl⟩ : syracuseStep 1483015 = 2224523) B2224523
theorem B1319175 : Blo 1317977 1319175 := bstep (se 1 (by rfl) ⟨989381, by rfl⟩ : syracuseStep 1319175 = 1978763) B1978763
theorem B1319183 : Blo 1317977 1319183 := bstep (se 1 (by rfl) ⟨989387, by rfl⟩ : syracuseStep 1319183 = 1978775) B1978775
theorem B1319227 : Blo 1317977 1319227 := bstep (se 1 (by rfl) ⟨989420, by rfl⟩ : syracuseStep 1319227 = 1978841) B1978841
theorem B4448627 : Blo 1317977 4448627 := bstep (se 1 (by rfl) ⟨3336470, by rfl⟩ : syracuseStep 4448627 = 6672941) B6672941
theorem B2965895 : Blo 1317977 2965895 := bstep (se 1 (by rfl) ⟨2224421, by rfl⟩ : syracuseStep 2965895 = 4448843) B4448843
theorem B1319303 : Blo 1317977 1319303 := bstep (se 1 (by rfl) ⟨989477, by rfl⟩ : syracuseStep 1319303 = 1978955) B1978955
theorem B1319311 : Blo 1317977 1319311 := bstep (se 1 (by rfl) ⟨989483, by rfl⟩ : syracuseStep 1319311 = 1978967) B1978967
theorem B1483195 : Blo 1317977 1483195 := bstep (se 1 (by rfl) ⟨1112396, by rfl⟩ : syracuseStep 1483195 = 2224793) B2224793
theorem B1319355 : Blo 1317977 1319355 := bstep (se 1 (by rfl) ⟨989516, by rfl⟩ : syracuseStep 1319355 = 1979033) B1979033
theorem B1319431 : Blo 1317977 1319431 := bstep (se 1 (by rfl) ⟨989573, by rfl⟩ : syracuseStep 1319431 = 1979147) B1979147
theorem B1606159 : Blo 1317977 1606159 := bstep (se 1 (by rfl) ⟨1204619, by rfl⟩ : syracuseStep 1606159 = 2409239) B2409239
theorem B1319439 : Blo 1317977 1319439 := bstep (se 1 (by rfl) ⟨989579, by rfl⟩ : syracuseStep 1319439 = 1979159) B1979159
theorem B2966075 : Blo 1317977 2966075 := bstep (se 1 (by rfl) ⟨2224556, by rfl⟩ : syracuseStep 2966075 = 4449113) B4449113
theorem B2966201 : Blo 1317977 2966201 := bstep (se 2 (by rfl) ⟨1112325, by rfl⟩ : syracuseStep 2966201 = 2224651) B2224651
theorem B5006195 : Blo 1317977 5006195 := bstep (se 1 (by rfl) ⟨3754646, by rfl⟩ : syracuseStep 5006195 = 7509293) B7509293
theorem B1876879 : Blo 1317977 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B1483663 : Blo 1317977 1483663 := bstep (se 1 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 1483663 = 2225495) B2225495
theorem B10838947 : Blo 1317977 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B2966543 : Blo 1317977 2966543 := bstep (se 1 (by rfl) ⟨2224907, by rfl⟩ : syracuseStep 2966543 = 4449815) B4449815
theorem B2966561 : Blo 1317977 2966561 := bstep (se 2 (by rfl) ⟨1112460, by rfl⟩ : syracuseStep 2966561 = 2224921) B2224921
theorem B2376839 : Blo 1317977 2376839 := bstep (se 1 (by rfl) ⟨1782629, by rfl⟩ : syracuseStep 2376839 = 3565259) B3565259
theorem B7128265 : Blo 1317977 7128265 := bstep (se 2 (by rfl) ⟨2673099, by rfl⟩ : syracuseStep 7128265 = 5346199) B5346199
theorem B171124001 : Blo 1317977 171124001 := bstep (se 2 (by rfl) ⟨64171500, by rfl⟩ : syracuseStep 171124001 = 128343001) B128343001
theorem B4752755 : Blo 1317977 4752755 := bstep (se 1 (by rfl) ⟨3564566, by rfl⟩ : syracuseStep 4752755 = 7129133) B7129133
theorem B2966903 : Blo 1317977 2966903 := bstep (se 1 (by rfl) ⟨2225177, by rfl⟩ : syracuseStep 2966903 = 4450355) B4450355
theorem B40592771 : Blo 1317977 40592771 := bstep (se 1 (by rfl) ⟨30444578, by rfl⟩ : syracuseStep 40592771 = 60889157) B60889157
theorem B1484167 : Blo 1317977 1484167 := bstep (se 1 (by rfl) ⟨1113125, by rfl⟩ : syracuseStep 1484167 = 2226251) B2226251
theorem B4572569 : Blo 1317977 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B6677963 : Blo 1317977 6677963 := bstep (se 1 (by rfl) ⟨5008472, by rfl⟩ : syracuseStep 6677963 = 10016945) B10016945
theorem B2967083 : Blo 1317977 2967083 := bstep (se 1 (by rfl) ⟨2225312, by rfl⟩ : syracuseStep 2967083 = 4450625) B4450625
theorem B1484347 : Blo 1317977 1484347 := bstep (se 1 (by rfl) ⟨1113260, by rfl⟩ : syracuseStep 1484347 = 2226521) B2226521
theorem B7513667 : Blo 1317977 7513667 := bstep (se 1 (by rfl) ⟨5635250, by rfl⟩ : syracuseStep 7513667 = 11270501) B11270501
theorem B3565171 : Blo 1317977 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B19015397 : Blo 1317977 19015397 := bstep (se 4 (by rfl) ⟨1782693, by rfl⟩ : syracuseStep 19015397 = 3565387) B3565387
theorem B6678287 : Blo 1317977 6678287 := bstep (se 1 (by rfl) ⟨5008715, by rfl⟩ : syracuseStep 6678287 = 10017431) B10017431
theorem B1337231 : Blo 1317977 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B2967443 : Blo 1317977 2967443 := bstep (se 1 (by rfl) ⟨2225582, by rfl⟩ : syracuseStep 2967443 = 4451165) B4451165
theorem B3336137 : Blo 1317977 3336137 := bstep (se 2 (by rfl) ⟨1251051, by rfl⟩ : syracuseStep 3336137 = 2502103) B2502103
theorem B2967497 : Blo 1317977 2967497 := bstep (se 2 (by rfl) ⟨1112811, by rfl⟩ : syracuseStep 2967497 = 2225623) B2225623
theorem B6424541 : Blo 1317977 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B1878007 : Blo 1317977 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B8022077 : Blo 1317977 8022077 := bstep (se 3 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 8022077 = 3008279) B3008279
theorem B12667013 : Blo 1317977 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B3565853 : Blo 1317977 3565853 := bstep (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) B1337195
theorem B3336491 : Blo 1317977 3336491 := bstep (se 1 (by rfl) ⟨2502368, by rfl⟩ : syracuseStep 3336491 = 5004737) B5004737
theorem B3754441 : Blo 1317977 3754441 := bstep (se 2 (by rfl) ⟨1407915, by rfl⟩ : syracuseStep 3754441 = 2815831) B2815831
theorem B5630417 : Blo 1317977 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B6335005 : Blo 1317977 6335005 := bstep (se 3 (by rfl) ⟨1187813, by rfl⟩ : syracuseStep 6335005 = 2375627) B2375627
theorem B2140715 : Blo 1317977 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B2968199 : Blo 1317977 2968199 := bstep (se 1 (by rfl) ⟨2226149, by rfl⟩ : syracuseStep 2968199 = 4452299) B4452299
theorem B1976975 : Blo 1317977 1976975 := bstep (se 1 (by rfl) ⟨1482731, by rfl⟩ : syracuseStep 1976975 = 2965463) B2965463
theorem B1977017 : Blo 1317977 1977017 := bstep (se 2 (by rfl) ⟨741381, by rfl⟩ : syracuseStep 1977017 = 1482763) B1482763
theorem B25340633 : Blo 1317977 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B1977095 : Blo 1317977 1977095 := bstep (se 1 (by rfl) ⟨1482821, by rfl⟩ : syracuseStep 1977095 = 2965643) B2965643
theorem B1977131 : Blo 1317977 1977131 := bstep (se 1 (by rfl) ⟨1482848, by rfl⟩ : syracuseStep 1977131 = 2965697) B2965697
theorem B3754795 : Blo 1317977 3754795 := bstep (se 1 (by rfl) ⟨2816096, by rfl⟩ : syracuseStep 3754795 = 5632193) B5632193
theorem B2968379 : Blo 1317977 2968379 := bstep (se 1 (by rfl) ⟨2226284, by rfl⟩ : syracuseStep 2968379 = 4452569) B4452569
theorem B1977161 : Blo 1317977 1977161 := bstep (se 2 (by rfl) ⟨741435, by rfl⟩ : syracuseStep 1977161 = 1482871) B1482871
theorem B4451219 : Blo 1317977 4451219 := bstep (se 1 (by rfl) ⟨3338414, by rfl⟩ : syracuseStep 4451219 = 6676829) B6676829
theorem B2968505 : Blo 1317977 2968505 := bstep (se 2 (by rfl) ⟨1113189, by rfl⟩ : syracuseStep 2968505 = 2226379) B2226379
theorem B1977275 : Blo 1317977 1977275 := bstep (se 1 (by rfl) ⟨1482956, by rfl⟩ : syracuseStep 1977275 = 2965913) B2965913
theorem B5008337 : Blo 1317977 5008337 := bstep (se 2 (by rfl) ⟨1878126, by rfl⟩ : syracuseStep 5008337 = 3756253) B3756253
theorem B1977335 : Blo 1317977 1977335 := bstep (se 1 (by rfl) ⟨1483001, by rfl⟩ : syracuseStep 1977335 = 2966003) B2966003
theorem B1977359 : Blo 1317977 1977359 := bstep (se 1 (by rfl) ⟨1483019, by rfl⟩ : syracuseStep 1977359 = 2966039) B2966039
theorem B5868587 : Blo 1317977 5868587 := bstep (se 1 (by rfl) ⟨4401440, by rfl⟩ : syracuseStep 5868587 = 8802881) B8802881
theorem B1977401 : Blo 1317977 1977401 := bstep (se 2 (by rfl) ⟨741525, by rfl⟩ : syracuseStep 1977401 = 1483051) B1483051
theorem B3755069 : Blo 1317977 3755069 := bstep (se 3 (by rfl) ⟨704075, by rfl⟩ : syracuseStep 3755069 = 1408151) B1408151
theorem B1977479 : Blo 1317977 1977479 := bstep (se 1 (by rfl) ⟨1483109, by rfl⟩ : syracuseStep 1977479 = 2966219) B2966219
theorem B1977515 : Blo 1317977 1977515 := bstep (se 1 (by rfl) ⟨1483136, by rfl⟩ : syracuseStep 1977515 = 2966273) B2966273
theorem B13028525 : Blo 1317977 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B6679745 : Blo 1317977 6679745 := bstep (se 2 (by rfl) ⟨2504904, by rfl⟩ : syracuseStep 6679745 = 5009809) B5009809
theorem B1977545 : Blo 1317977 1977545 := bstep (se 2 (by rfl) ⟨741579, by rfl⟩ : syracuseStep 1977545 = 1483159) B1483159
theorem B3337483 : Blo 1317977 3337483 := bstep (se 1 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 3337483 = 5006225) B5006225
theorem B5008655 : Blo 1317977 5008655 := bstep (se 1 (by rfl) ⟨3756491, by rfl⟩ : syracuseStep 5008655 = 7512983) B7512983
theorem B1977659 : Blo 1317977 1977659 := bstep (se 1 (by rfl) ⟨1483244, by rfl⟩ : syracuseStep 1977659 = 2966489) B2966489
theorem B1977719 : Blo 1317977 1977719 := bstep (se 1 (by rfl) ⟨1483289, by rfl⟩ : syracuseStep 1977719 = 2966579) B2966579
theorem B1977743 : Blo 1317977 1977743 := bstep (se 1 (by rfl) ⟨1483307, by rfl⟩ : syracuseStep 1977743 = 2966615) B2966615
theorem B3337625 : Blo 1317977 3337625 := bstep (se 2 (by rfl) ⟨1251609, by rfl⟩ : syracuseStep 3337625 = 2503219) B2503219
theorem B1977785 : Blo 1317977 1977785 := bstep (se 2 (by rfl) ⟨741669, by rfl⟩ : syracuseStep 1977785 = 1483339) B1483339
theorem B7507403 : Blo 1317977 7507403 := bstep (se 1 (by rfl) ⟨5630552, by rfl⟩ : syracuseStep 7507403 = 11261105) B11261105
theorem B1977863 : Blo 1317977 1977863 := bstep (se 1 (by rfl) ⟨1483397, by rfl⟩ : syracuseStep 1977863 = 2966795) B2966795
theorem B5565995 : Blo 1317977 5565995 := bstep (se 1 (by rfl) ⟨4174496, by rfl⟩ : syracuseStep 5565995 = 8348993) B8348993
theorem B1977899 : Blo 1317977 1977899 := bstep (se 1 (by rfl) ⟨1483424, by rfl⟩ : syracuseStep 1977899 = 2966849) B2966849
theorem B3337787 : Blo 1317977 3337787 := bstep (se 1 (by rfl) ⟨2503340, by rfl⟩ : syracuseStep 3337787 = 5006681) B5006681
theorem B1977929 : Blo 1317977 1977929 := bstep (se 2 (by rfl) ⟨741723, by rfl⟩ : syracuseStep 1977929 = 1483447) B1483447
theorem B1978043 : Blo 1317977 1978043 := bstep (se 1 (by rfl) ⟨1483532, by rfl⟩ : syracuseStep 1978043 = 2967065) B2967065
theorem B7130861 : Blo 1317977 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B1978103 : Blo 1317977 1978103 := bstep (se 1 (by rfl) ⟨1483577, by rfl⟩ : syracuseStep 1978103 = 2967155) B2967155
theorem B1978127 : Blo 1317977 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B4755233 : Blo 1317977 4755233 := bstep (se 2 (by rfl) ⟨1783212, by rfl⟩ : syracuseStep 4755233 = 3566425) B3566425
theorem B10014515 : Blo 1317977 10014515 := bstep (se 1 (by rfl) ⟨7510886, by rfl⟩ : syracuseStep 10014515 = 15021773) B15021773
theorem B1978169 : Blo 1317977 1978169 := bstep (se 2 (by rfl) ⟨741813, by rfl⟩ : syracuseStep 1978169 = 1483627) B1483627
theorem B1978247 : Blo 1317977 1978247 := bstep (se 1 (by rfl) ⟨1483685, by rfl⟩ : syracuseStep 1978247 = 2967371) B2967371
theorem B3338131 : Blo 1317977 3338131 := bstep (se 1 (by rfl) ⟨2503598, by rfl⟩ : syracuseStep 3338131 = 5007197) B5007197
theorem B1978283 : Blo 1317977 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B1978313 : Blo 1317977 1978313 := bstep (se 2 (by rfl) ⟨741867, by rfl⟩ : syracuseStep 1978313 = 1483735) B1483735
theorem B3338273 : Blo 1317977 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B4010027 : Blo 1317977 4010027 := bstep (se 1 (by rfl) ⟨3007520, by rfl⟩ : syracuseStep 4010027 = 6015041) B6015041
theorem B1978427 : Blo 1317977 1978427 := bstep (se 1 (by rfl) ⟨1483820, by rfl⟩ : syracuseStep 1978427 = 2967641) B2967641
theorem B1978487 : Blo 1317977 1978487 := bstep (se 1 (by rfl) ⟨1483865, by rfl⟩ : syracuseStep 1978487 = 2967731) B2967731
theorem B1978511 : Blo 1317977 1978511 := bstep (se 1 (by rfl) ⟨1483883, by rfl⟩ : syracuseStep 1978511 = 2967767) B2967767
theorem B1978553 : Blo 1317977 1978553 := bstep (se 2 (by rfl) ⟨741957, by rfl⟩ : syracuseStep 1978553 = 1483915) B1483915
theorem B25055473 : Blo 1317977 25055473 := bstep (se 2 (by rfl) ⟨9395802, by rfl⟩ : syracuseStep 25055473 = 18791605) B18791605
theorem B84537589 : Blo 1317977 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B1978631 : Blo 1317977 1978631 := bstep (se 1 (by rfl) ⟨1483973, by rfl⟩ : syracuseStep 1978631 = 2967947) B2967947
theorem B4452623 : Blo 1317977 4452623 := bstep (se 1 (by rfl) ⟨3339467, by rfl⟩ : syracuseStep 4452623 = 6678935) B6678935
theorem B3805483 : Blo 1317977 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B1978667 : Blo 1317977 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B1978697 : Blo 1317977 1978697 := bstep (se 2 (by rfl) ⟨742011, by rfl⟩ : syracuseStep 1978697 = 1484023) B1484023
theorem B4632985 : Blo 1317977 4632985 := bstep (se 2 (by rfl) ⟨1737369, by rfl⟩ : syracuseStep 4632985 = 3474739) B3474739
theorem B1978811 : Blo 1317977 1978811 := bstep (se 1 (by rfl) ⟨1484108, by rfl⟩ : syracuseStep 1978811 = 2968217) B2968217
theorem B27054557 : Blo 1317977 27054557 := bstep (se 3 (by rfl) ⟨5072729, by rfl⟩ : syracuseStep 27054557 = 10145459) B10145459
theorem B1978871 : Blo 1317977 1978871 := bstep (se 1 (by rfl) ⟨1484153, by rfl⟩ : syracuseStep 1978871 = 2968307) B2968307
theorem B1978895 : Blo 1317977 1978895 := bstep (se 1 (by rfl) ⟨1484171, by rfl⟩ : syracuseStep 1978895 = 2968343) B2968343
theorem B4452893 : Blo 1317977 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B1978937 : Blo 1317977 1978937 := bstep (se 2 (by rfl) ⟨742101, by rfl⟩ : syracuseStep 1978937 = 1484203) B1484203
theorem B4280951 : Blo 1317977 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B2224759 : Blo 1317977 2224759 := bstep (se 1 (by rfl) ⟨1668569, by rfl⟩ : syracuseStep 2224759 = 3337139) B3337139
theorem B1979015 : Blo 1317977 1979015 := bstep (se 1 (by rfl) ⟨1484261, by rfl⟩ : syracuseStep 1979015 = 2968523) B2968523
theorem B1979051 : Blo 1317977 1979051 := bstep (se 1 (by rfl) ⟨1484288, by rfl⟩ : syracuseStep 1979051 = 2968577) B2968577
theorem B1979081 : Blo 1317977 1979081 := bstep (se 2 (by rfl) ⟨742155, by rfl⟩ : syracuseStep 1979081 = 1484311) B1484311
theorem B9507557 : Blo 1317977 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B2224955 : Blo 1317977 2224955 := bstep (se 1 (by rfl) ⟨1668716, by rfl⟩ : syracuseStep 2224955 = 3337433) B3337433
theorem B1979195 : Blo 1317977 1979195 := bstep (se 1 (by rfl) ⟨1484396, by rfl⟩ : syracuseStep 1979195 = 2968793) B2968793
theorem B3339265 : Blo 1317977 3339265 := bstep (se 2 (by rfl) ⟨1252224, by rfl⟩ : syracuseStep 3339265 = 2504449) B2504449
theorem B1668215 : Blo 1317977 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B3757175 : Blo 1317977 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B2503865 : Blo 1317977 2503865 := bstep (se 2 (by rfl) ⟨938949, by rfl⟩ : syracuseStep 2503865 = 1877899) B1877899
theorem B2225353 : Blo 1317977 2225353 := bstep (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) B1669015
theorem B1668367 : Blo 1317977 1668367 := bstep (se 1 (by rfl) ⟨1251275, by rfl⟩ : syracuseStep 1668367 = 2502551) B2502551
theorem B41178545 : Blo 1317977 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B1668539 : Blo 1317977 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B16258603 : Blo 1317977 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B3339863 : Blo 1317977 3339863 := bstep (se 1 (by rfl) ⟨2504897, by rfl⟩ : syracuseStep 3339863 = 5009795) B5009795
theorem B3806867 : Blo 1317977 3806867 := bstep (se 1 (by rfl) ⟨2855150, by rfl⟩ : syracuseStep 3806867 = 5710301) B5710301
theorem B9500431 : Blo 1317977 9500431 := bstep (se 1 (by rfl) ⟨7125323, by rfl⟩ : syracuseStep 9500431 = 14250647) B14250647
theorem B7509793 : Blo 1317977 7509793 := bstep (se 2 (by rfl) ⟨2816172, by rfl⟩ : syracuseStep 7509793 = 5632345) B5632345
theorem B2226055 : Blo 1317977 2226055 := bstep (se 1 (by rfl) ⟨1669541, by rfl⟩ : syracuseStep 2226055 = 3339083) B3339083
theorem B5707705 : Blo 1317977 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B5347565 : Blo 1317977 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B2537743 : Blo 1317977 2537743 := bstep (se 1 (by rfl) ⟨1903307, by rfl⟩ : syracuseStep 2537743 = 3806615) B3806615
theorem B3168571 : Blo 1317977 3168571 := bstep (se 1 (by rfl) ⟨2376428, by rfl⟩ : syracuseStep 3168571 = 4752857) B4752857
theorem B1669511 : Blo 1317977 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B14449117 : Blo 1317977 14449117 := bstep (se 3 (by rfl) ⟨2709209, by rfl⟩ : syracuseStep 14449117 = 5418419) B5418419
theorem B7511069 : Blo 1317977 7511069 := bstep (se 3 (by rfl) ⟨1408325, by rfl⟩ : syracuseStep 7511069 = 2816651) B2816651
theorem B5635115 : Blo 1317977 5635115 := bstep (se 1 (by rfl) ⟨4226336, by rfl⟩ : syracuseStep 5635115 = 8452673) B8452673
theorem B4512829 : Blo 1317977 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B4283479 : Blo 1317977 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B1318023 : Blo 1317977 1318023 := bstep (se 1 (by rfl) ⟨988517, by rfl⟩ : syracuseStep 1318023 = 1977035) B1977035
theorem B1318031 : Blo 1317977 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B1318075 : Blo 1317977 1318075 := bstep (se 1 (by rfl) ⟨988556, by rfl⟩ : syracuseStep 1318075 = 1977113) B1977113
theorem B1318151 : Blo 1317977 1318151 := bstep (se 1 (by rfl) ⟨988613, by rfl⟩ : syracuseStep 1318151 = 1977227) B1977227
theorem B1318159 : Blo 1317977 1318159 := bstep (se 1 (by rfl) ⟨988619, by rfl⟩ : syracuseStep 1318159 = 1977239) B1977239
theorem B1318203 : Blo 1317977 1318203 := bstep (se 1 (by rfl) ⟨988652, by rfl⟩ : syracuseStep 1318203 = 1977305) B1977305
theorem B69483835 : Blo 1317977 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B1318279 : Blo 1317977 1318279 := bstep (se 1 (by rfl) ⟨988709, by rfl⟩ : syracuseStep 1318279 = 1977419) B1977419
theorem B1318287 : Blo 1317977 1318287 := bstep (se 1 (by rfl) ⟨988715, by rfl⟩ : syracuseStep 1318287 = 1977431) B1977431
theorem B6675857 : Blo 1317977 6675857 := bstep (se 2 (by rfl) ⟨2503446, by rfl⟩ : syracuseStep 6675857 = 5006893) B5006893
theorem B1318331 : Blo 1317977 1318331 := bstep (se 1 (by rfl) ⟨988748, by rfl⟩ : syracuseStep 1318331 = 1977497) B1977497
theorem B1318407 : Blo 1317977 1318407 := bstep (se 1 (by rfl) ⟨988805, by rfl⟩ : syracuseStep 1318407 = 1977611) B1977611
theorem B1318415 : Blo 1317977 1318415 := bstep (se 1 (by rfl) ⟨988811, by rfl⟩ : syracuseStep 1318415 = 1977623) B1977623
theorem B10010141 : Blo 1317977 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B9141803 : Blo 1317977 9141803 := bstep (se 1 (by rfl) ⟨6856352, by rfl⟩ : syracuseStep 9141803 = 13712705) B13712705
theorem B1318459 : Blo 1317977 1318459 := bstep (se 1 (by rfl) ⟨988844, by rfl⟩ : syracuseStep 1318459 = 1977689) B1977689
theorem B1318535 : Blo 1317977 1318535 := bstep (se 1 (by rfl) ⟨988901, by rfl⟩ : syracuseStep 1318535 = 1977803) B1977803
theorem B1318543 : Blo 1317977 1318543 := bstep (se 1 (by rfl) ⟨988907, by rfl⟩ : syracuseStep 1318543 = 1977815) B1977815
theorem B1318587 : Blo 1317977 1318587 := bstep (se 1 (by rfl) ⟨988940, by rfl⟩ : syracuseStep 1318587 = 1977881) B1977881
theorem B2817737 : Blo 1317977 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B1318663 : Blo 1317977 1318663 := bstep (se 1 (by rfl) ⟨988997, by rfl⟩ : syracuseStep 1318663 = 1977995) B1977995
theorem B1318671 : Blo 1317977 1318671 := bstep (se 1 (by rfl) ⟨989003, by rfl⟩ : syracuseStep 1318671 = 1978007) B1978007
theorem B4226849 : Blo 1317977 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B2031403 : Blo 1317977 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B14262065 : Blo 1317977 14262065 := bstep (se 2 (by rfl) ⟨5348274, by rfl⟩ : syracuseStep 14262065 = 10696549) B10696549
theorem B1318715 : Blo 1317977 1318715 := bstep (se 1 (by rfl) ⟨989036, by rfl⟩ : syracuseStep 1318715 = 1978073) B1978073
theorem B1318791 : Blo 1317977 1318791 := bstep (se 1 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 1318791 = 1978187) B1978187
theorem B1318799 : Blo 1317977 1318799 := bstep (se 1 (by rfl) ⟨989099, by rfl⟩ : syracuseStep 1318799 = 1978199) B1978199
theorem B1318843 : Blo 1317977 1318843 := bstep (se 1 (by rfl) ⟨989132, by rfl⟩ : syracuseStep 1318843 = 1978265) B1978265
theorem B10010627 : Blo 1317977 10010627 := bstep (se 1 (by rfl) ⟨7507970, by rfl⟩ : syracuseStep 10010627 = 15015941) B15015941
theorem B4227079 : Blo 1317977 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B1318951 : Blo 1317977 1318951 := bstep (se 1 (by rfl) ⟨989213, by rfl⟩ : syracuseStep 1318951 = 1978427) B1978427
theorem B1318991 : Blo 1317977 1318991 := bstep (se 1 (by rfl) ⟨989243, by rfl⟩ : syracuseStep 1318991 = 1978487) B1978487
theorem B1319007 : Blo 1317977 1319007 := bstep (se 1 (by rfl) ⟨989255, by rfl⟩ : syracuseStep 1319007 = 1978511) B1978511
theorem B1319035 : Blo 1317977 1319035 := bstep (se 1 (by rfl) ⟨989276, by rfl⟩ : syracuseStep 1319035 = 1978553) B1978553
theorem B1319087 : Blo 1317977 1319087 := bstep (se 1 (by rfl) ⟨989315, by rfl⟩ : syracuseStep 1319087 = 1978631) B1978631
theorem B1319111 : Blo 1317977 1319111 := bstep (se 1 (by rfl) ⟨989333, by rfl⟩ : syracuseStep 1319111 = 1978667) B1978667
theorem B1319131 : Blo 1317977 1319131 := bstep (se 1 (by rfl) ⟨989348, by rfl⟩ : syracuseStep 1319131 = 1978697) B1978697
theorem B2965751 : Blo 1317977 2965751 := bstep (se 1 (by rfl) ⟨2224313, by rfl⟩ : syracuseStep 2965751 = 4448627) B4448627
theorem B1319207 : Blo 1317977 1319207 := bstep (se 1 (by rfl) ⟨989405, by rfl⟩ : syracuseStep 1319207 = 1978811) B1978811
theorem B4448573 : Blo 1317977 4448573 := bstep (se 3 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 4448573 = 1668215) B1668215
theorem B33407297 : Blo 1317977 33407297 := bstep (se 2 (by rfl) ⟨12527736, by rfl⟩ : syracuseStep 33407297 = 25055473) B25055473
theorem B1319247 : Blo 1317977 1319247 := bstep (se 1 (by rfl) ⟨989435, by rfl⟩ : syracuseStep 1319247 = 1978871) B1978871
theorem B1319263 : Blo 1317977 1319263 := bstep (se 1 (by rfl) ⟨989447, by rfl⟩ : syracuseStep 1319263 = 1978895) B1978895
theorem B3383657 : Blo 1317977 3383657 := bstep (se 2 (by rfl) ⟨1268871, by rfl⟩ : syracuseStep 3383657 = 2537743) B2537743
theorem B1319291 : Blo 1317977 1319291 := bstep (se 1 (by rfl) ⟨989468, by rfl⟩ : syracuseStep 1319291 = 1978937) B1978937
theorem B1319343 : Blo 1317977 1319343 := bstep (se 1 (by rfl) ⟨989507, by rfl⟩ : syracuseStep 1319343 = 1979015) B1979015
theorem B1319367 : Blo 1317977 1319367 := bstep (se 1 (by rfl) ⟨989525, by rfl⟩ : syracuseStep 1319367 = 1979051) B1979051
theorem B1319387 : Blo 1317977 1319387 := bstep (se 1 (by rfl) ⟨989540, by rfl⟩ : syracuseStep 1319387 = 1979081) B1979081
theorem B6177313 : Blo 1317977 6177313 := bstep (se 2 (by rfl) ⟨2316492, by rfl⟩ : syracuseStep 6177313 = 4632985) B4632985
theorem B1483303 : Blo 1317977 1483303 := bstep (se 1 (by rfl) ⟨1112477, by rfl⟩ : syracuseStep 1483303 = 2224955) B2224955
theorem B1319463 : Blo 1317977 1319463 := bstep (se 1 (by rfl) ⟨989597, by rfl⟩ : syracuseStep 1319463 = 1979195) B1979195
theorem B5005921 : Blo 1317977 5005921 := bstep (se 2 (by rfl) ⟨1877220, by rfl⟩ : syracuseStep 5005921 = 3754441) B3754441
theorem B9503405 : Blo 1317977 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B8446673 : Blo 1317977 8446673 := bstep (se 2 (by rfl) ⟨3167502, by rfl⟩ : syracuseStep 8446673 = 6335005) B6335005
theorem B2966345 : Blo 1317977 2966345 := bstep (se 2 (by rfl) ⟨1112379, by rfl⟩ : syracuseStep 2966345 = 2224759) B2224759
theorem B114082667 : Blo 1317977 114082667 := bstep (se 1 (by rfl) ⟨85562000, by rfl⟩ : syracuseStep 114082667 = 171124001) B171124001
theorem B27452363 : Blo 1317977 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B5006393 : Blo 1317977 5006393 := bstep (se 2 (by rfl) ⟨1877397, by rfl⟩ : syracuseStep 5006393 = 3754795) B3754795
theorem B4449437 : Blo 1317977 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B14451929 : Blo 1317977 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B5711305 : Blo 1317977 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B3565043 : Blo 1317977 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B2377235 : Blo 1317977 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B9504353 : Blo 1317977 9504353 := bstep (se 2 (by rfl) ⟨3564132, by rfl⟩ : syracuseStep 9504353 = 7128265) B7128265
theorem B2967137 : Blo 1317977 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B3753611 : Blo 1317977 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B4449977 : Blo 1317977 4449977 := bstep (se 2 (by rfl) ⟨1668741, by rfl⟩ : syracuseStep 4449977 = 3337483) B3337483
theorem B1427143 : Blo 1317977 1427143 := bstep (se 1 (by rfl) ⟨1070357, by rfl⟩ : syracuseStep 1427143 = 2140715) B2140715
theorem B16893755 : Blo 1317977 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B2967479 : Blo 1317977 2967479 := bstep (se 1 (by rfl) ⟨2225609, by rfl⟩ : syracuseStep 2967479 = 4451219) B4451219
theorem B5007379 : Blo 1317977 5007379 := bstep (se 1 (by rfl) ⟨3755534, by rfl⟩ : syracuseStep 5007379 = 7511069) B7511069
theorem B21678137 : Blo 1317977 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B8685683 : Blo 1317977 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B4753561 : Blo 1317977 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B4450571 : Blo 1317977 4450571 := bstep (se 1 (by rfl) ⟨3337928, by rfl⟩ : syracuseStep 4450571 = 6675857) B6675857
theorem B12667241 : Blo 1317977 12667241 := bstep (se 2 (by rfl) ⟨4750215, by rfl⟩ : syracuseStep 12667241 = 9500431) B9500431
theorem B3565949 : Blo 1317977 3565949 := bstep (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) B1337231
theorem B10013057 : Blo 1317977 10013057 := bstep (se 2 (by rfl) ⟨3754896, by rfl⟩ : syracuseStep 10013057 = 7509793) B7509793
theorem B1878491 : Blo 1317977 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B4753907 : Blo 1317977 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B2968073 : Blo 1317977 2968073 := bstep (se 2 (by rfl) ⟨1113027, by rfl⟩ : syracuseStep 2968073 = 2226055) B2226055
theorem B4450841 : Blo 1317977 4450841 := bstep (se 2 (by rfl) ⟨1669065, by rfl⟩ : syracuseStep 4450841 = 3338131) B3338131
theorem B10693405 : Blo 1317977 10693405 := bstep (se 3 (by rfl) ⟨2005013, by rfl⟩ : syracuseStep 10693405 = 4010027) B4010027
theorem B2968415 : Blo 1317977 2968415 := bstep (se 1 (by rfl) ⟨2226311, by rfl⟩ : syracuseStep 2968415 = 4452623) B4452623
theorem B1977263 : Blo 1317977 1977263 := bstep (se 1 (by rfl) ⟨1482947, by rfl⟩ : syracuseStep 1977263 = 2965895) B2965895
theorem B112716785 : Blo 1317977 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B1977353 : Blo 1317977 1977353 := bstep (se 2 (by rfl) ⟨741507, by rfl⟩ : syracuseStep 1977353 = 1483015) B1483015
theorem B2968595 : Blo 1317977 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1977383 : Blo 1317977 1977383 := bstep (se 1 (by rfl) ⟨1483037, by rfl⟩ : syracuseStep 1977383 = 2966075) B2966075
theorem B5073977 : Blo 1317977 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B2853967 : Blo 1317977 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B1977467 : Blo 1317977 1977467 := bstep (se 1 (by rfl) ⟨1483100, by rfl⟩ : syracuseStep 1977467 = 2966201) B2966201
theorem B3337463 : Blo 1317977 3337463 := bstep (se 1 (by rfl) ⟨2503097, by rfl⟩ : syracuseStep 3337463 = 5006195) B5006195
theorem B1977593 : Blo 1317977 1977593 := bstep (se 2 (by rfl) ⟨741597, by rfl⟩ : syracuseStep 1977593 = 1483195) B1483195
theorem B1977695 : Blo 1317977 1977695 := bstep (se 1 (by rfl) ⟨1483271, by rfl⟩ : syracuseStep 1977695 = 2966543) B2966543
theorem B1977707 : Blo 1317977 1977707 := bstep (se 1 (by rfl) ⟨1483280, by rfl⟩ : syracuseStep 1977707 = 2966561) B2966561
theorem B1584559 : Blo 1317977 1584559 := bstep (se 1 (by rfl) ⟨1188419, by rfl⟩ : syracuseStep 1584559 = 2376839) B2376839
theorem B1977935 : Blo 1317977 1977935 := bstep (se 1 (by rfl) ⟨1483451, by rfl⟩ : syracuseStep 1977935 = 2966903) B2966903
theorem B27061847 : Blo 1317977 27061847 := bstep (se 1 (by rfl) ⟨20296385, by rfl⟩ : syracuseStep 27061847 = 40592771) B40592771
theorem B4451975 : Blo 1317977 4451975 := bstep (se 1 (by rfl) ⟨3338981, by rfl⟩ : syracuseStep 4451975 = 6677963) B6677963
theorem B4452029 : Blo 1317977 4452029 := bstep (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) B1669511
theorem B1978055 : Blo 1317977 1978055 := bstep (se 1 (by rfl) ⟨1483541, by rfl⟩ : syracuseStep 1978055 = 2967083) B2967083
theorem B5009111 : Blo 1317977 5009111 := bstep (se 1 (by rfl) ⟨3756833, by rfl⟩ : syracuseStep 5009111 = 7513667) B7513667
theorem B12193517 : Blo 1317977 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B12676931 : Blo 1317977 12676931 := bstep (se 1 (by rfl) ⟨9507698, by rfl⟩ : syracuseStep 12676931 = 19015397) B19015397
theorem B4452191 : Blo 1317977 4452191 := bstep (se 1 (by rfl) ⟨3339143, by rfl⟩ : syracuseStep 4452191 = 6678287) B6678287
theorem B2502505 : Blo 1317977 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B1978217 : Blo 1317977 1978217 := bstep (se 2 (by rfl) ⟨741831, by rfl⟩ : syracuseStep 1978217 = 1483663) B1483663
theorem B1978295 : Blo 1317977 1978295 := bstep (se 1 (by rfl) ⟨1483721, by rfl⟩ : syracuseStep 1978295 = 2967443) B2967443
theorem B2224091 : Blo 1317977 2224091 := bstep (se 1 (by rfl) ⟨1668068, by rfl⟩ : syracuseStep 2224091 = 3336137) B3336137
theorem B1978331 : Blo 1317977 1978331 := bstep (se 1 (by rfl) ⟨1483748, by rfl⟩ : syracuseStep 1978331 = 2967497) B2967497
theorem B4452353 : Blo 1317977 4452353 := bstep (se 2 (by rfl) ⟨1669632, by rfl⟩ : syracuseStep 4452353 = 3339265) B3339265
theorem B6017105 : Blo 1317977 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B2224327 : Blo 1317977 2224327 := bstep (se 1 (by rfl) ⟨1668245, by rfl⟩ : syracuseStep 2224327 = 3336491) B3336491
theorem B2224489 : Blo 1317977 2224489 := bstep (se 2 (by rfl) ⟨834183, by rfl⟩ : syracuseStep 2224489 = 1668367) B1668367
theorem B1978799 : Blo 1317977 1978799 := bstep (se 1 (by rfl) ⟨1484099, by rfl⟩ : syracuseStep 1978799 = 2968199) B2968199
theorem B1978889 : Blo 1317977 1978889 := bstep (se 2 (by rfl) ⟨742083, by rfl⟩ : syracuseStep 1978889 = 1484167) B1484167
theorem B1978919 : Blo 1317977 1978919 := bstep (se 1 (by rfl) ⟨1484189, by rfl⟩ : syracuseStep 1978919 = 2968379) B2968379
theorem B1979003 : Blo 1317977 1979003 := bstep (se 1 (by rfl) ⟨1484252, by rfl⟩ : syracuseStep 1979003 = 2968505) B2968505
theorem B3338891 : Blo 1317977 3338891 := bstep (se 1 (by rfl) ⟨2504168, by rfl⟩ : syracuseStep 3338891 = 5008337) B5008337
theorem B3912391 : Blo 1317977 3912391 := bstep (se 1 (by rfl) ⟨2934293, by rfl⟩ : syracuseStep 3912391 = 5868587) B5868587
theorem B3756743 : Blo 1317977 3756743 := bstep (se 1 (by rfl) ⟨2817557, by rfl⟩ : syracuseStep 3756743 = 5635115) B5635115
theorem B2503379 : Blo 1317977 2503379 := bstep (se 1 (by rfl) ⟨1877534, by rfl⟩ : syracuseStep 2503379 = 3755069) B3755069
theorem B1979129 : Blo 1317977 1979129 := bstep (se 2 (by rfl) ⟨742173, by rfl⟩ : syracuseStep 1979129 = 1484347) B1484347
theorem B4453163 : Blo 1317977 4453163 := bstep (se 1 (by rfl) ⟨3339872, by rfl⟩ : syracuseStep 4453163 = 6679745) B6679745
theorem B3339103 : Blo 1317977 3339103 := bstep (se 1 (by rfl) ⟨2504327, by rfl⟩ : syracuseStep 3339103 = 5008655) B5008655
theorem B2225083 : Blo 1317977 2225083 := bstep (se 1 (by rfl) ⟨1668812, by rfl⟩ : syracuseStep 2225083 = 3337625) B3337625
theorem B6673427 : Blo 1317977 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B2225191 : Blo 1317977 2225191 := bstep (se 1 (by rfl) ⟨1668893, by rfl⟩ : syracuseStep 2225191 = 3337787) B3337787
theorem B2708537 : Blo 1317977 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B9508043 : Blo 1317977 9508043 := bstep (se 1 (by rfl) ⟨7131032, by rfl⟩ : syracuseStep 9508043 = 14262065) B14262065
theorem B2504009 : Blo 1317977 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B2225515 : Blo 1317977 2225515 := bstep (se 1 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 2225515 = 3338273) B3338273
theorem B10687859 : Blo 1317977 10687859 := bstep (se 1 (by rfl) ⟨8015894, by rfl⟩ : syracuseStep 10687859 = 16031789) B16031789
theorem B8566181 : Blo 1317977 8566181 := bstep (se 4 (by rfl) ⟨803079, by rfl⟩ : syracuseStep 8566181 = 1606159) B1606159
theorem B18036371 : Blo 1317977 18036371 := bstep (se 1 (by rfl) ⟨13527278, by rfl⟩ : syracuseStep 18036371 = 27054557) B27054557
theorem B4224761 : Blo 1317977 4224761 := bstep (se 2 (by rfl) ⟨1584285, by rfl⟩ : syracuseStep 4224761 = 3168571) B3168571
theorem B6338371 : Blo 1317977 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B19265489 : Blo 1317977 19265489 := bstep (se 2 (by rfl) ⟨7224558, by rfl⟩ : syracuseStep 19265489 = 14449117) B14449117
theorem B2504783 : Blo 1317977 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B1669243 : Blo 1317977 1669243 := bstep (se 1 (by rfl) ⟨1251932, by rfl⟩ : syracuseStep 1669243 = 2503865) B2503865
theorem B3168503 : Blo 1317977 3168503 := bstep (se 1 (by rfl) ⟨2376377, by rfl⟩ : syracuseStep 3168503 = 4752755) B4752755
theorem B2226575 : Blo 1317977 2226575 := bstep (se 1 (by rfl) ⟨1669931, by rfl⟩ : syracuseStep 2226575 = 3339863) B3339863
theorem B2537911 : Blo 1317977 2537911 := bstep (se 1 (by rfl) ⟨1903433, by rfl⟩ : syracuseStep 2537911 = 3806867) B3806867
theorem B4283027 : Blo 1317977 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B5348051 : Blo 1317977 5348051 := bstep (se 1 (by rfl) ⟨4011038, by rfl⟩ : syracuseStep 5348051 = 8022077) B8022077
theorem B8444675 : Blo 1317977 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B370580453 : Blo 1317977 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B1317983 : Blo 1317977 1317983 := bstep (se 1 (by rfl) ⟨988487, by rfl⟩ : syracuseStep 1317983 = 1976975) B1976975
theorem B1318011 : Blo 1317977 1318011 := bstep (se 1 (by rfl) ⟨988508, by rfl⟩ : syracuseStep 1318011 = 1977017) B1977017
theorem B1318063 : Blo 1317977 1318063 := bstep (se 1 (by rfl) ⟨988547, by rfl⟩ : syracuseStep 1318063 = 1977095) B1977095
theorem B1318087 : Blo 1317977 1318087 := bstep (se 1 (by rfl) ⟨988565, by rfl⟩ : syracuseStep 1318087 = 1977131) B1977131
theorem B1318107 : Blo 1317977 1318107 := bstep (se 1 (by rfl) ⟨988580, by rfl⟩ : syracuseStep 1318107 = 1977161) B1977161
theorem B1318183 : Blo 1317977 1318183 := bstep (se 1 (by rfl) ⟨988637, by rfl⟩ : syracuseStep 1318183 = 1977275) B1977275
theorem B1318223 : Blo 1317977 1318223 := bstep (se 1 (by rfl) ⟨988667, by rfl⟩ : syracuseStep 1318223 = 1977335) B1977335
theorem B1318239 : Blo 1317977 1318239 := bstep (se 1 (by rfl) ⟨988679, by rfl⟩ : syracuseStep 1318239 = 1977359) B1977359
theorem B1318267 : Blo 1317977 1318267 := bstep (se 1 (by rfl) ⟨988700, by rfl⟩ : syracuseStep 1318267 = 1977401) B1977401
theorem B12680621 : Blo 1317977 12680621 := bstep (se 3 (by rfl) ⟨2377616, by rfl⟩ : syracuseStep 12680621 = 4755233) B4755233
theorem B1318319 : Blo 1317977 1318319 := bstep (se 1 (by rfl) ⟨988739, by rfl⟩ : syracuseStep 1318319 = 1977479) B1977479
theorem B1318343 : Blo 1317977 1318343 := bstep (se 1 (by rfl) ⟨988757, by rfl⟩ : syracuseStep 1318343 = 1977515) B1977515
theorem B1318363 : Blo 1317977 1318363 := bstep (se 1 (by rfl) ⟨988772, by rfl⟩ : syracuseStep 1318363 = 1977545) B1977545
theorem B1318439 : Blo 1317977 1318439 := bstep (se 1 (by rfl) ⟨988829, by rfl⟩ : syracuseStep 1318439 = 1977659) B1977659
theorem B1318479 : Blo 1317977 1318479 := bstep (se 1 (by rfl) ⟨988859, by rfl⟩ : syracuseStep 1318479 = 1977719) B1977719
theorem B1318495 : Blo 1317977 1318495 := bstep (se 1 (by rfl) ⟨988871, by rfl⟩ : syracuseStep 1318495 = 1977743) B1977743
theorem B1318523 : Blo 1317977 1318523 := bstep (se 1 (by rfl) ⟨988892, by rfl⟩ : syracuseStep 1318523 = 1977785) B1977785
theorem B5004935 : Blo 1317977 5004935 := bstep (se 1 (by rfl) ⟨3753701, by rfl⟩ : syracuseStep 5004935 = 7507403) B7507403
theorem B1318575 : Blo 1317977 1318575 := bstep (se 1 (by rfl) ⟨988931, by rfl⟩ : syracuseStep 1318575 = 1977863) B1977863
theorem B3710663 : Blo 1317977 3710663 := bstep (se 1 (by rfl) ⟨2782997, by rfl⟩ : syracuseStep 3710663 = 5565995) B5565995
theorem B6094535 : Blo 1317977 6094535 := bstep (se 1 (by rfl) ⟨4570901, by rfl⟩ : syracuseStep 6094535 = 9141803) B9141803
theorem B1318599 : Blo 1317977 1318599 := bstep (se 1 (by rfl) ⟨988949, by rfl⟩ : syracuseStep 1318599 = 1977899) B1977899
theorem B1318619 : Blo 1317977 1318619 := bstep (se 1 (by rfl) ⟨988964, by rfl⟩ : syracuseStep 1318619 = 1977929) B1977929
theorem B1318695 : Blo 1317977 1318695 := bstep (se 1 (by rfl) ⟨989021, by rfl⟩ : syracuseStep 1318695 = 1978043) B1978043
theorem B1318735 : Blo 1317977 1318735 := bstep (se 1 (by rfl) ⟨989051, by rfl⟩ : syracuseStep 1318735 = 1978103) B1978103
theorem B1318751 : Blo 1317977 1318751 := bstep (se 1 (by rfl) ⟨989063, by rfl⟩ : syracuseStep 1318751 = 1978127) B1978127
theorem B2817899 : Blo 1317977 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B6676343 : Blo 1317977 6676343 := bstep (se 1 (by rfl) ⟨5007257, by rfl⟩ : syracuseStep 6676343 = 10014515) B10014515
theorem B1318779 : Blo 1317977 1318779 := bstep (se 1 (by rfl) ⟨989084, by rfl⟩ : syracuseStep 1318779 = 1978169) B1978169
theorem B7610273 : Blo 1317977 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B1318831 : Blo 1317977 1318831 := bstep (se 1 (by rfl) ⟨989123, by rfl⟩ : syracuseStep 1318831 = 1978247) B1978247
theorem B1318855 : Blo 1317977 1318855 := bstep (se 1 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 1318855 = 1978283) B1978283
theorem B1318875 : Blo 1317977 1318875 := bstep (se 1 (by rfl) ⟨989156, by rfl⟩ : syracuseStep 1318875 = 1978313) B1978313
theorem B5636105 : Blo 1317977 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B6676505 : Blo 1317977 6676505 := bstep (se 2 (by rfl) ⟨2503689, by rfl⟩ : syracuseStep 6676505 = 5007379) B5007379
theorem B2965715 : Blo 1317977 2965715 := bstep (se 1 (by rfl) ⟨2224286, by rfl⟩ : syracuseStep 2965715 = 4448573) B4448573
theorem B2965769 : Blo 1317977 2965769 := bstep (se 2 (by rfl) ⟨1112163, by rfl⟩ : syracuseStep 2965769 = 2224327) B2224327
theorem B1319199 : Blo 1317977 1319199 := bstep (se 1 (by rfl) ⟨989399, by rfl⟩ : syracuseStep 1319199 = 1978799) B1978799
theorem B1319259 : Blo 1317977 1319259 := bstep (se 1 (by rfl) ⟨989444, by rfl⟩ : syracuseStep 1319259 = 1978889) B1978889
theorem B1319279 : Blo 1317977 1319279 := bstep (se 1 (by rfl) ⟨989459, by rfl⟩ : syracuseStep 1319279 = 1978919) B1978919
theorem B1319335 : Blo 1317977 1319335 := bstep (se 1 (by rfl) ⟨989501, by rfl⟩ : syracuseStep 1319335 = 1979003) B1979003
theorem B2965985 : Blo 1317977 2965985 := bstep (se 2 (by rfl) ⟨1112244, by rfl⟩ : syracuseStep 2965985 = 2224489) B2224489
theorem B1319419 : Blo 1317977 1319419 := bstep (se 1 (by rfl) ⟨989564, by rfl⟩ : syracuseStep 1319419 = 1979129) B1979129
theorem B25354781 : Blo 1317977 25354781 := bstep (se 3 (by rfl) ⟨4754021, by rfl⟩ : syracuseStep 25354781 = 9508043) B9508043
theorem B76055111 : Blo 1317977 76055111 := bstep (se 1 (by rfl) ⟨57041333, by rfl⟩ : syracuseStep 76055111 = 114082667) B114082667
theorem B4448951 : Blo 1317977 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B2966291 : Blo 1317977 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B9634619 : Blo 1317977 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B5710787 : Blo 1317977 5710787 := bstep (se 1 (by rfl) ⟨4283090, by rfl⟩ : syracuseStep 5710787 = 8566181) B8566181
theorem B2376695 : Blo 1317977 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B20866085 : Blo 1317977 20866085 := bstep (se 4 (by rfl) ⟨1956195, by rfl⟩ : syracuseStep 20866085 = 3912391) B3912391
theorem B2966651 : Blo 1317977 2966651 := bstep (se 1 (by rfl) ⟨2224988, by rfl⟩ : syracuseStep 2966651 = 4449977) B4449977
theorem B2966777 : Blo 1317977 2966777 := bstep (se 2 (by rfl) ⟨1112541, by rfl⟩ : syracuseStep 2966777 = 2225083) B2225083
theorem B14452091 : Blo 1317977 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B2966921 : Blo 1317977 2966921 := bstep (se 2 (by rfl) ⟨1112595, by rfl⟩ : syracuseStep 2966921 = 2225191) B2225191
theorem B2967047 : Blo 1317977 2967047 := bstep (se 1 (by rfl) ⟨2225285, by rfl⟩ : syracuseStep 2967047 = 4450571) B4450571
theorem B1484383 : Blo 1317977 1484383 := bstep (se 1 (by rfl) ⟨1113287, by rfl⟩ : syracuseStep 1484383 = 2226575) B2226575
theorem B2967227 : Blo 1317977 2967227 := bstep (se 1 (by rfl) ⟨2225420, by rfl⟩ : syracuseStep 2967227 = 4450841) B4450841
theorem B3565367 : Blo 1317977 3565367 := bstep (se 1 (by rfl) ⟨2674025, by rfl⟩ : syracuseStep 3565367 = 5348051) B5348051
theorem B2967353 : Blo 1317977 2967353 := bstep (se 2 (by rfl) ⟨1112757, by rfl⟩ : syracuseStep 2967353 = 2225515) B2225515
theorem B5629783 : Blo 1317977 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B1902857 : Blo 1317977 1902857 := bstep (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) B1427143
theorem B13535525 : Blo 1317977 13535525 := bstep (se 4 (by rfl) ⟨1268955, by rfl⟩ : syracuseStep 13535525 = 2537911) B2537911
theorem B18041231 : Blo 1317977 18041231 := bstep (se 1 (by rfl) ⟨13530923, by rfl⟩ : syracuseStep 18041231 = 27061847) B27061847
theorem B3336623 : Blo 1317977 3336623 := bstep (se 1 (by rfl) ⟨2502467, by rfl⟩ : syracuseStep 3336623 = 5004935) B5004935
theorem B2967983 : Blo 1317977 2967983 := bstep (se 1 (by rfl) ⟨2225987, by rfl⟩ : syracuseStep 2967983 = 4451975) B4451975
theorem B2968019 : Blo 1317977 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B3336673 : Blo 1317977 3336673 := bstep (se 2 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 3336673 = 2502505) B2502505
theorem B8129011 : Blo 1317977 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B73206301 : Blo 1317977 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B2968127 : Blo 1317977 2968127 := bstep (se 1 (by rfl) ⟨2226095, by rfl⟩ : syracuseStep 2968127 = 4452191) B4452191
theorem B1878599 : Blo 1317977 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B4450895 : Blo 1317977 4450895 := bstep (se 1 (by rfl) ⟨3338171, by rfl⟩ : syracuseStep 4450895 = 6676343) B6676343
theorem B5073515 : Blo 1317977 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B2968235 : Blo 1317977 2968235 := bstep (se 1 (by rfl) ⟨2226176, by rfl⟩ : syracuseStep 2968235 = 4452353) B4452353
theorem B1977167 : Blo 1317977 1977167 := bstep (se 1 (by rfl) ⟨1482875, by rfl⟩ : syracuseStep 1977167 = 2965751) B2965751
theorem B6679421 : Blo 1317977 6679421 := bstep (se 3 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 6679421 = 2504783) B2504783
theorem B2255771 : Blo 1317977 2255771 := bstep (se 1 (by rfl) ⟨1691828, by rfl⟩ : syracuseStep 2255771 = 3383657) B3383657
theorem B6335603 : Blo 1317977 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B5631115 : Blo 1317977 5631115 := bstep (se 1 (by rfl) ⟨4223336, by rfl⟩ : syracuseStep 5631115 = 8446673) B8446673
theorem B2968775 : Blo 1317977 2968775 := bstep (se 1 (by rfl) ⟨2226581, by rfl⟩ : syracuseStep 2968775 = 4453163) B4453163
theorem B1977563 : Blo 1317977 1977563 := bstep (se 1 (by rfl) ⟨1483172, by rfl⟩ : syracuseStep 1977563 = 2966345) B2966345
theorem B3337595 : Blo 1317977 3337595 := bstep (se 1 (by rfl) ⟨2503196, by rfl⟩ : syracuseStep 3337595 = 5006393) B5006393
theorem B8236417 : Blo 1317977 8236417 := bstep (se 2 (by rfl) ⟨3088656, by rfl⟩ : syracuseStep 8236417 = 6177313) B6177313
theorem B1977737 : Blo 1317977 1977737 := bstep (se 2 (by rfl) ⟨741651, by rfl⟩ : syracuseStep 1977737 = 1483303) B1483303
theorem B14257873 : Blo 1317977 14257873 := bstep (se 2 (by rfl) ⟨5346702, by rfl⟩ : syracuseStep 14257873 = 10693405) B10693405
theorem B6336235 : Blo 1317977 6336235 := bstep (se 1 (by rfl) ⟨4752176, by rfl⟩ : syracuseStep 6336235 = 9504353) B9504353
theorem B1978091 : Blo 1317977 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B2502407 : Blo 1317977 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B4452137 : Blo 1317977 4452137 := bstep (se 2 (by rfl) ⟨1669551, by rfl⟩ : syracuseStep 4452137 = 3339103) B3339103
theorem B5009309 : Blo 1317977 5009309 := bstep (se 3 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 5009309 = 1878491) B1878491
theorem B1978319 : Blo 1317977 1978319 := bstep (se 1 (by rfl) ⟨1483739, by rfl⟩ : syracuseStep 1978319 = 2967479) B2967479
theorem B3805289 : Blo 1317977 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B1978715 : Blo 1317977 1978715 := bstep (se 1 (by rfl) ⟨1484036, by rfl⟩ : syracuseStep 1978715 = 2968073) B2968073
theorem B2855351 : Blo 1317977 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B1978943 : Blo 1317977 1978943 := bstep (se 1 (by rfl) ⟨1484207, by rfl⟩ : syracuseStep 1978943 = 2968415) B2968415
theorem B7615073 : Blo 1317977 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B1979063 : Blo 1317977 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B2224975 : Blo 1317977 2224975 := bstep (se 1 (by rfl) ⟨1668731, by rfl⟩ : syracuseStep 2224975 = 3337463) B3337463
theorem B8451161 : Blo 1317977 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B3339407 : Blo 1317977 3339407 := bstep (se 1 (by rfl) ⟨2504555, by rfl⟩ : syracuseStep 3339407 = 5009111) B5009111
theorem B8451287 : Blo 1317977 8451287 := bstep (se 1 (by rfl) ⟨6338465, by rfl⟩ : syracuseStep 8451287 = 12676931) B12676931
theorem B6673751 : Blo 1317977 6673751 := bstep (se 1 (by rfl) ⟨5005313, by rfl⟩ : syracuseStep 6673751 = 10010627) B10010627
theorem B4011403 : Blo 1317977 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B7222765 : Blo 1317977 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B2225657 : Blo 1317977 2225657 := bstep (se 2 (by rfl) ⟨834621, by rfl⟩ : syracuseStep 2225657 = 1669243) B1669243
theorem B6338081 : Blo 1317977 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B22271531 : Blo 1317977 22271531 := bstep (se 1 (by rfl) ⟨16703648, by rfl⟩ : syracuseStep 22271531 = 33407297) B33407297
theorem B2225927 : Blo 1317977 2225927 := bstep (se 1 (by rfl) ⟨1669445, by rfl⟩ : syracuseStep 2225927 = 3338891) B3338891
theorem B2504495 : Blo 1317977 2504495 := bstep (se 1 (by rfl) ⟨1878371, by rfl⟩ : syracuseStep 2504495 = 3756743) B3756743
theorem B1668919 : Blo 1317977 1668919 := bstep (se 1 (by rfl) ⟨1251689, by rfl⟩ : syracuseStep 1668919 = 2503379) B2503379
theorem B6674561 : Blo 1317977 6674561 := bstep (se 2 (by rfl) ⟨2502960, by rfl⟩ : syracuseStep 6674561 = 5005921) B5005921
theorem B1669339 : Blo 1317977 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B7125239 : Blo 1317977 7125239 := bstep (se 1 (by rfl) ⟨5343929, by rfl⟩ : syracuseStep 7125239 = 10687859) B10687859
theorem B9509197 : Blo 1317977 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B12024247 : Blo 1317977 12024247 := bstep (se 1 (by rfl) ⟨9018185, by rfl⟩ : syracuseStep 12024247 = 18036371) B18036371
theorem B2816507 : Blo 1317977 2816507 := bstep (se 1 (by rfl) ⟨2112380, by rfl⟩ : syracuseStep 2816507 = 4224761) B4224761
theorem B11262503 : Blo 1317977 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B12843659 : Blo 1317977 12843659 := bstep (se 1 (by rfl) ⟨9632744, by rfl⟩ : syracuseStep 12843659 = 19265489) B19265489
theorem B6339293 : Blo 1317977 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B5790455 : Blo 1317977 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B2112335 : Blo 1317977 2112335 := bstep (se 1 (by rfl) ⟨1584251, by rfl⟩ : syracuseStep 2112335 = 3168503) B3168503
theorem B8444827 : Blo 1317977 8444827 := bstep (se 1 (by rfl) ⟨6333620, by rfl⟩ : syracuseStep 8444827 = 12667241) B12667241
theorem B6675371 : Blo 1317977 6675371 := bstep (se 1 (by rfl) ⟨5006528, by rfl⟩ : syracuseStep 6675371 = 10013057) B10013057
theorem B3169271 : Blo 1317977 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B16252093 : Blo 1317977 16252093 := bstep (se 3 (by rfl) ⟨3047267, by rfl⟩ : syracuseStep 16252093 = 6094535) B6094535
theorem B2112745 : Blo 1317977 2112745 := bstep (se 2 (by rfl) ⟨792279, by rfl⟩ : syracuseStep 2112745 = 1584559) B1584559
theorem B1318175 : Blo 1317977 1318175 := bstep (se 1 (by rfl) ⟨988631, by rfl⟩ : syracuseStep 1318175 = 1977263) B1977263
theorem B247053635 : Blo 1317977 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B75144523 : Blo 1317977 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B1318235 : Blo 1317977 1318235 := bstep (se 1 (by rfl) ⟨988676, by rfl⟩ : syracuseStep 1318235 = 1977353) B1977353
theorem B1318255 : Blo 1317977 1318255 := bstep (se 1 (by rfl) ⟨988691, by rfl⟩ : syracuseStep 1318255 = 1977383) B1977383
theorem B3382651 : Blo 1317977 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B1318311 : Blo 1317977 1318311 := bstep (se 1 (by rfl) ⟨988733, by rfl⟩ : syracuseStep 1318311 = 1977467) B1977467
theorem B1318395 : Blo 1317977 1318395 := bstep (se 1 (by rfl) ⟨988796, by rfl⟩ : syracuseStep 1318395 = 1977593) B1977593
theorem B1318463 : Blo 1317977 1318463 := bstep (se 1 (by rfl) ⟨988847, by rfl⟩ : syracuseStep 1318463 = 1977695) B1977695
theorem B1318471 : Blo 1317977 1318471 := bstep (se 1 (by rfl) ⟨988853, by rfl⟩ : syracuseStep 1318471 = 1977707) B1977707
theorem B8453747 : Blo 1317977 8453747 := bstep (se 1 (by rfl) ⟨6340310, by rfl⟩ : syracuseStep 8453747 = 12680621) B12680621
theorem B1318623 : Blo 1317977 1318623 := bstep (se 1 (by rfl) ⟨988967, by rfl⟩ : syracuseStep 1318623 = 1977935) B1977935
theorem B2473775 : Blo 1317977 2473775 := bstep (se 1 (by rfl) ⟨1855331, by rfl⟩ : syracuseStep 2473775 = 3710663) B3710663
theorem B1318703 : Blo 1317977 1318703 := bstep (se 1 (by rfl) ⟨989027, by rfl⟩ : syracuseStep 1318703 = 1978055) B1978055
theorem B1318811 : Blo 1317977 1318811 := bstep (se 1 (by rfl) ⟨989108, by rfl⟩ : syracuseStep 1318811 = 1978217) B1978217
theorem B1318863 : Blo 1317977 1318863 := bstep (se 1 (by rfl) ⟨989147, by rfl⟩ : syracuseStep 1318863 = 1978295) B1978295
theorem B1482727 : Blo 1317977 1482727 := bstep (se 1 (by rfl) ⟨1112045, by rfl⟩ : syracuseStep 1482727 = 2224091) B2224091
theorem B1318887 : Blo 1317977 1318887 := bstep (se 1 (by rfl) ⟨989165, by rfl⟩ : syracuseStep 1318887 = 1978331) B1978331
theorem B1319143 : Blo 1317977 1319143 := bstep (se 1 (by rfl) ⟨989357, by rfl⟩ : syracuseStep 1319143 = 1978715) B1978715
theorem B1319295 : Blo 1317977 1319295 := bstep (se 1 (by rfl) ⟨989471, by rfl⟩ : syracuseStep 1319295 = 1978943) B1978943
theorem B2965967 : Blo 1317977 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B1319375 : Blo 1317977 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B6423079 : Blo 1317977 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B16032329 : Blo 1317977 16032329 := bstep (se 2 (by rfl) ⟨6012123, by rfl⟩ : syracuseStep 16032329 = 12024247) B12024247
theorem B4448897 : Blo 1317977 4448897 := bstep (se 2 (by rfl) ⟨1668336, by rfl⟩ : syracuseStep 4448897 = 3336673) B3336673
theorem B10838681 : Blo 1317977 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B13910723 : Blo 1317977 13910723 := bstep (se 1 (by rfl) ⟨10433042, by rfl⟩ : syracuseStep 13910723 = 20866085) B20866085
theorem B97608401 : Blo 1317977 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B4449167 : Blo 1317977 4449167 := bstep (se 1 (by rfl) ⟨3336875, by rfl⟩ : syracuseStep 4449167 = 6673751) B6673751
theorem B9634727 : Blo 1317977 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B1483771 : Blo 1317977 1483771 := bstep (se 1 (by rfl) ⟨1112828, by rfl⟩ : syracuseStep 1483771 = 2225657) B2225657
theorem B2966633 : Blo 1317977 2966633 := bstep (se 2 (by rfl) ⟨1112487, by rfl⟩ : syracuseStep 2966633 = 2224975) B2224975
theorem B1483951 : Blo 1317977 1483951 := bstep (se 1 (by rfl) ⟨1112963, by rfl⟩ : syracuseStep 1483951 = 2225927) B2225927
theorem B2376911 : Blo 1317977 2376911 := bstep (se 1 (by rfl) ⟨1782683, by rfl⟩ : syracuseStep 2376911 = 3565367) B3565367
theorem B4449707 : Blo 1317977 4449707 := bstep (se 1 (by rfl) ⟨3337280, by rfl⟩ : syracuseStep 4449707 = 6674561) B6674561
theorem B21669457 : Blo 1317977 21669457 := bstep (se 2 (by rfl) ⟨8126046, by rfl⟩ : syracuseStep 21669457 = 16252093) B16252093
theorem B12027487 : Blo 1317977 12027487 := bstep (se 1 (by rfl) ⟨9020615, by rfl⟩ : syracuseStep 12027487 = 18041231) B18041231
theorem B1877671 : Blo 1317977 1877671 := bstep (se 1 (by rfl) ⟨1408253, by rfl⟩ : syracuseStep 1877671 = 2816507) B2816507
theorem B2967263 : Blo 1317977 2967263 := bstep (se 1 (by rfl) ⟨2225447, by rfl⟩ : syracuseStep 2967263 = 4450895) B4450895
theorem B8562439 : Blo 1317977 8562439 := bstep (se 1 (by rfl) ⟨6421829, by rfl⟩ : syracuseStep 8562439 = 12843659) B12843659
theorem B3860303 : Blo 1317977 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B4450247 : Blo 1317977 4450247 := bstep (se 1 (by rfl) ⟨3337685, by rfl⟩ : syracuseStep 4450247 = 6675371) B6675371
theorem B18040805 : Blo 1317977 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B164702423 : Blo 1317977 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B8448313 : Blo 1317977 8448313 := bstep (se 2 (by rfl) ⟨3168117, by rfl⟩ : syracuseStep 8448313 = 6336235) B6336235
theorem B7506377 : Blo 1317977 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B2968091 : Blo 1317977 2968091 := bstep (se 1 (by rfl) ⟨2226068, by rfl⟩ : syracuseStep 2968091 = 4452137) B4452137
theorem B1649183 : Blo 1317977 1649183 := bstep (se 1 (by rfl) ⟨1236887, by rfl⟩ : syracuseStep 1649183 = 2473775) B2473775
theorem B1976969 : Blo 1317977 1976969 := bstep (se 2 (by rfl) ⟨741363, by rfl⟩ : syracuseStep 1976969 = 1482727) B1482727
theorem B4451003 : Blo 1317977 4451003 := bstep (se 1 (by rfl) ⟨3338252, by rfl⟩ : syracuseStep 4451003 = 6676505) B6676505
theorem B1977143 : Blo 1317977 1977143 := bstep (se 1 (by rfl) ⟨1482857, by rfl⟩ : syracuseStep 1977143 = 2965715) B2965715
theorem B1977179 : Blo 1317977 1977179 := bstep (se 1 (by rfl) ⟨1482884, by rfl⟩ : syracuseStep 1977179 = 2965769) B2965769
theorem B1977323 : Blo 1317977 1977323 := bstep (se 1 (by rfl) ⟨1482992, by rfl⟩ : syracuseStep 1977323 = 2965985) B2965985
theorem B16903187 : Blo 1317977 16903187 := bstep (se 1 (by rfl) ⟨12677390, by rfl⟩ : syracuseStep 16903187 = 25354781) B25354781
theorem B50703407 : Blo 1317977 50703407 := bstep (se 1 (by rfl) ⟨38027555, by rfl⟩ : syracuseStep 50703407 = 76055111) B76055111
theorem B1977527 : Blo 1317977 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B1584463 : Blo 1317977 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B5074285 : Blo 1317977 5074285 := bstep (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) B1902857
theorem B1977767 : Blo 1317977 1977767 := bstep (se 1 (by rfl) ⟨1483325, by rfl⟩ : syracuseStep 1977767 = 2966651) B2966651
theorem B1977851 : Blo 1317977 1977851 := bstep (se 1 (by rfl) ⟨1483388, by rfl⟩ : syracuseStep 1977851 = 2966777) B2966777
theorem B1977947 : Blo 1317977 1977947 := bstep (se 1 (by rfl) ⟨1483460, by rfl⟩ : syracuseStep 1977947 = 2966921) B2966921
theorem B1978031 : Blo 1317977 1978031 := bstep (se 1 (by rfl) ⟨1483523, by rfl⟩ : syracuseStep 1978031 = 2967047) B2967047
theorem B1978151 : Blo 1317977 1978151 := bstep (se 1 (by rfl) ⟨1483613, by rfl⟩ : syracuseStep 1978151 = 2967227) B2967227
theorem B7614269 : Blo 1317977 7614269 := bstep (se 3 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 7614269 = 2855351) B2855351
theorem B11259769 : Blo 1317977 11259769 := bstep (se 2 (by rfl) ⟨4222413, by rfl⟩ : syracuseStep 11259769 = 8444827) B8444827
theorem B1978235 : Blo 1317977 1978235 := bstep (se 1 (by rfl) ⟨1483676, by rfl⟩ : syracuseStep 1978235 = 2967353) B2967353
theorem B7508153 : Blo 1317977 7508153 := bstep (se 2 (by rfl) ⟨2815557, by rfl⟩ : syracuseStep 7508153 = 5631115) B5631115
theorem B5009597 : Blo 1317977 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B9023683 : Blo 1317977 9023683 := bstep (se 1 (by rfl) ⟨6767762, by rfl⟩ : syracuseStep 9023683 = 13535525) B13535525
theorem B2224415 : Blo 1317977 2224415 := bstep (se 1 (by rfl) ⟨1668311, by rfl⟩ : syracuseStep 2224415 = 3336623) B3336623
theorem B1978655 : Blo 1317977 1978655 := bstep (se 1 (by rfl) ⟨1483991, by rfl⟩ : syracuseStep 1978655 = 2967983) B2967983
theorem B1978679 : Blo 1317977 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B7508335 : Blo 1317977 7508335 := bstep (se 1 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 7508335 = 11262503) B11262503
theorem B1978751 : Blo 1317977 1978751 := bstep (se 1 (by rfl) ⟨1484063, by rfl⟩ : syracuseStep 1978751 = 2968127) B2968127
theorem B100192697 : Blo 1317977 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B1978823 : Blo 1317977 1978823 := bstep (se 1 (by rfl) ⟨1484117, by rfl⟩ : syracuseStep 1978823 = 2968235) B2968235
theorem B10981889 : Blo 1317977 10981889 := bstep (se 2 (by rfl) ⟨4118208, by rfl⟩ : syracuseStep 10981889 = 8236417) B8236417
theorem B4452947 : Blo 1317977 4452947 := bstep (se 1 (by rfl) ⟨3339710, by rfl⟩ : syracuseStep 4452947 = 6679421) B6679421
theorem B1503847 : Blo 1317977 1503847 := bstep (se 1 (by rfl) ⟨1127885, by rfl⟩ : syracuseStep 1503847 = 2255771) B2255771
theorem B9630353 : Blo 1317977 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B4223735 : Blo 1317977 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B1979177 : Blo 1317977 1979177 := bstep (se 2 (by rfl) ⟨742191, by rfl⟩ : syracuseStep 1979177 = 1484383) B1484383
theorem B1979183 : Blo 1317977 1979183 := bstep (se 1 (by rfl) ⟨1484387, by rfl⟩ : syracuseStep 1979183 = 2968775) B2968775
theorem B2225063 : Blo 1317977 2225063 := bstep (se 1 (by rfl) ⟨1668797, by rfl⟩ : syracuseStep 2225063 = 3337595) B3337595
theorem B19010497 : Blo 1317977 19010497 := bstep (se 2 (by rfl) ⟨7128936, by rfl⟩ : syracuseStep 19010497 = 14257873) B14257873
theorem B2225225 : Blo 1317977 2225225 := bstep (se 2 (by rfl) ⟨834459, by rfl⟩ : syracuseStep 2225225 = 1668919) B1668919
theorem B1668271 : Blo 1317977 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B3339539 : Blo 1317977 3339539 := bstep (se 1 (by rfl) ⟨2504654, by rfl⟩ : syracuseStep 3339539 = 5009309) B5009309
theorem B3757403 : Blo 1317977 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B2536859 : Blo 1317977 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B2225785 : Blo 1317977 2225785 := bstep (se 2 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 2225785 = 1669339) B1669339
theorem B12678929 : Blo 1317977 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B3807191 : Blo 1317977 3807191 := bstep (se 1 (by rfl) ⟨2855393, by rfl⟩ : syracuseStep 3807191 = 5710787) B5710787
theorem B5634107 : Blo 1317977 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B2226271 : Blo 1317977 2226271 := bstep (se 1 (by rfl) ⟨1669703, by rfl⟩ : syracuseStep 2226271 = 3339407) B3339407
theorem B5634191 : Blo 1317977 5634191 := bstep (se 1 (by rfl) ⟨4225643, by rfl⟩ : syracuseStep 5634191 = 8451287) B8451287
theorem B4225387 : Blo 1317977 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B1669663 : Blo 1317977 1669663 := bstep (se 1 (by rfl) ⟨1252247, by rfl⟩ : syracuseStep 1669663 = 2504495) B2504495
theorem B59390749 : Blo 1317977 59390749 := bstep (se 3 (by rfl) ⟨11135765, by rfl⟩ : syracuseStep 59390749 = 22271531) B22271531
theorem B4750159 : Blo 1317977 4750159 := bstep (se 1 (by rfl) ⟨3562619, by rfl⟩ : syracuseStep 4750159 = 7125239) B7125239
theorem B20306861 : Blo 1317977 20306861 := bstep (se 3 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 20306861 = 7615073) B7615073
theorem B2816993 : Blo 1317977 2816993 := bstep (se 2 (by rfl) ⟨1056372, by rfl⟩ : syracuseStep 2816993 = 2112745) B2112745
theorem B3382343 : Blo 1317977 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B4226195 : Blo 1317977 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B5348537 : Blo 1317977 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B1318111 : Blo 1317977 1318111 := bstep (se 1 (by rfl) ⟨988583, by rfl⟩ : syracuseStep 1318111 = 1977167) B1977167
theorem B1408223 : Blo 1317977 1408223 := bstep (se 1 (by rfl) ⟨1056167, by rfl⟩ : syracuseStep 1408223 = 2112335) B2112335
theorem B2112847 : Blo 1317977 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B1318375 : Blo 1317977 1318375 := bstep (se 1 (by rfl) ⟨988781, by rfl⟩ : syracuseStep 1318375 = 1977563) B1977563
theorem B1318491 : Blo 1317977 1318491 := bstep (se 1 (by rfl) ⟨988868, by rfl⟩ : syracuseStep 1318491 = 1977737) B1977737
theorem B5635831 : Blo 1317977 5635831 := bstep (se 1 (by rfl) ⟨4226873, by rfl⟩ : syracuseStep 5635831 = 8453747) B8453747
theorem B1318727 : Blo 1317977 1318727 := bstep (se 1 (by rfl) ⟨989045, by rfl⟩ : syracuseStep 1318727 = 1978091) B1978091
theorem B1318879 : Blo 1317977 1318879 := bstep (se 1 (by rfl) ⟨989159, by rfl⟩ : syracuseStep 1318879 = 1978319) B1978319
theorem B5005435 : Blo 1317977 5005435 := bstep (se 1 (by rfl) ⟨3754076, by rfl⟩ : syracuseStep 5005435 = 7508153) B7508153
theorem B1482943 : Blo 1317977 1482943 := bstep (se 1 (by rfl) ⟨1112207, by rfl⟩ : syracuseStep 1482943 = 2224415) B2224415
theorem B1319103 : Blo 1317977 1319103 := bstep (se 1 (by rfl) ⟨989327, by rfl⟩ : syracuseStep 1319103 = 1978655) B1978655
theorem B1319119 : Blo 1317977 1319119 := bstep (se 1 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 1319119 = 1978679) B1978679
theorem B1319167 : Blo 1317977 1319167 := bstep (se 1 (by rfl) ⟨989375, by rfl⟩ : syracuseStep 1319167 = 1978751) B1978751
theorem B1319215 : Blo 1317977 1319215 := bstep (se 1 (by rfl) ⟨989411, by rfl⟩ : syracuseStep 1319215 = 1978823) B1978823
theorem B11264417 : Blo 1317977 11264417 := bstep (se 2 (by rfl) ⟨4224156, by rfl⟩ : syracuseStep 11264417 = 8448313) B8448313
theorem B2965931 : Blo 1317977 2965931 := bstep (se 1 (by rfl) ⟨2224448, by rfl⟩ : syracuseStep 2965931 = 4448897) B4448897
theorem B7225787 : Blo 1317977 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B9273815 : Blo 1317977 9273815 := bstep (se 1 (by rfl) ⟨6955361, by rfl⟩ : syracuseStep 9273815 = 13910723) B13910723
theorem B10011113 : Blo 1317977 10011113 := bstep (se 2 (by rfl) ⟨3754167, by rfl⟩ : syracuseStep 10011113 = 7508335) B7508335
theorem B1319451 : Blo 1317977 1319451 := bstep (se 1 (by rfl) ⟨989588, by rfl⟩ : syracuseStep 1319451 = 1979177) B1979177
theorem B1319455 : Blo 1317977 1319455 := bstep (se 1 (by rfl) ⟨989591, by rfl⟩ : syracuseStep 1319455 = 1979183) B1979183
theorem B2966111 : Blo 1317977 2966111 := bstep (se 1 (by rfl) ⟨2224583, by rfl⟩ : syracuseStep 2966111 = 4449167) B4449167
theorem B1483375 : Blo 1317977 1483375 := bstep (se 1 (by rfl) ⟨1112531, by rfl⟩ : syracuseStep 1483375 = 2225063) B2225063
theorem B6423151 : Blo 1317977 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B1483483 : Blo 1317977 1483483 := bstep (se 1 (by rfl) ⟨1112612, by rfl⟩ : syracuseStep 1483483 = 2225225) B2225225
theorem B2966471 : Blo 1317977 2966471 := bstep (se 1 (by rfl) ⟨2224853, by rfl⟩ : syracuseStep 2966471 = 4449707) B4449707
theorem B6333545 : Blo 1317977 6333545 := bstep (se 2 (by rfl) ⟨2375079, by rfl⟩ : syracuseStep 6333545 = 4750159) B4750159
theorem B25347329 : Blo 1317977 25347329 := bstep (se 2 (by rfl) ⟨9505248, by rfl⟩ : syracuseStep 25347329 = 19010497) B19010497
theorem B2966831 : Blo 1317977 2966831 := bstep (se 1 (by rfl) ⟨2225123, by rfl⟩ : syracuseStep 2966831 = 4450247) B4450247
theorem B12027203 : Blo 1317977 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B2967335 : Blo 1317977 2967335 := bstep (se 1 (by rfl) ⟨2225501, by rfl⟩ : syracuseStep 2967335 = 4451003) B4451003
theorem B1877995 : Blo 1317977 1877995 := bstep (se 1 (by rfl) ⟨1408496, by rfl⟩ : syracuseStep 1877995 = 2816993) B2816993
theorem B33802271 : Blo 1317977 33802271 := bstep (se 1 (by rfl) ⟨25351703, by rfl⟩ : syracuseStep 33802271 = 50703407) B50703407
theorem B2254895 : Blo 1317977 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B3565691 : Blo 1317977 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B2967713 : Blo 1317977 2967713 := bstep (se 2 (by rfl) ⟨1112892, by rfl⟩ : syracuseStep 2967713 = 2225785) B2225785
theorem B7514441 : Blo 1317977 7514441 := bstep (se 2 (by rfl) ⟨2817915, by rfl⟩ : syracuseStep 7514441 = 5635831) B5635831
theorem B2968361 : Blo 1317977 2968361 := bstep (se 2 (by rfl) ⟨1113135, by rfl⟩ : syracuseStep 2968361 = 2226271) B2226271
theorem B1977311 : Blo 1317977 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B17591285 : Blo 1317977 17591285 := bstep (se 5 (by rfl) ⟨824591, by rfl⟩ : syracuseStep 17591285 = 1649183) B1649183
theorem B2968631 : Blo 1317977 2968631 := bstep (se 1 (by rfl) ⟨2226473, by rfl⟩ : syracuseStep 2968631 = 4452947) B4452947
theorem B65072267 : Blo 1317977 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B3755261 : Blo 1317977 3755261 := bstep (se 3 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 3755261 = 1408223) B1408223
theorem B8564105 : Blo 1317977 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B1977755 : Blo 1317977 1977755 := bstep (se 1 (by rfl) ⟨1483316, by rfl⟩ : syracuseStep 1977755 = 2966633) B2966633
theorem B1584607 : Blo 1317977 1584607 := bstep (se 1 (by rfl) ⟨1188455, by rfl⟩ : syracuseStep 1584607 = 2376911) B2376911
theorem B1978175 : Blo 1317977 1978175 := bstep (se 1 (by rfl) ⟨1483631, by rfl⟩ : syracuseStep 1978175 = 2967263) B2967263
theorem B1978361 : Blo 1317977 1978361 := bstep (se 2 (by rfl) ⟨741885, by rfl⟩ : syracuseStep 1978361 = 1483771) B1483771
theorem B3756071 : Blo 1317977 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B3756127 : Blo 1317977 3756127 := bstep (se 1 (by rfl) ⟨2817095, by rfl⟩ : syracuseStep 3756127 = 5634191) B5634191
theorem B109801615 : Blo 1317977 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B2224361 : Blo 1317977 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B1978601 : Blo 1317977 1978601 := bstep (se 2 (by rfl) ⟨741975, by rfl⟩ : syracuseStep 1978601 = 1483951) B1483951
theorem B1978727 : Blo 1317977 1978727 := bstep (se 1 (by rfl) ⟨1484045, by rfl⟩ : syracuseStep 1978727 = 2968091) B2968091
theorem B11268517 : Blo 1317977 11268517 := bstep (se 4 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 11268517 = 2112847) B2112847
theorem B13537907 : Blo 1317977 13537907 := bstep (se 1 (by rfl) ⟨10153430, by rfl⟩ : syracuseStep 13537907 = 20306861) B20306861
theorem B11268791 : Blo 1317977 11268791 := bstep (se 1 (by rfl) ⟨8451593, by rfl⟩ : syracuseStep 11268791 = 16903187) B16903187
theorem B16036649 : Blo 1317977 16036649 := bstep (se 2 (by rfl) ⟨6013743, by rfl⟩ : syracuseStep 16036649 = 12027487) B12027487
theorem B10294141 : Blo 1317977 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B2503561 : Blo 1317977 2503561 := bstep (se 2 (by rfl) ⟨938835, by rfl⟩ : syracuseStep 2503561 = 1877671) B1877671
theorem B11416585 : Blo 1317977 11416585 := bstep (se 2 (by rfl) ⟨4281219, by rfl⟩ : syracuseStep 11416585 = 8562439) B8562439
theorem B15013025 : Blo 1317977 15013025 := bstep (se 2 (by rfl) ⟨5629884, by rfl⟩ : syracuseStep 15013025 = 11259769) B11259769
theorem B5076179 : Blo 1317977 5076179 := bstep (se 1 (by rfl) ⟨3807134, by rfl⟩ : syracuseStep 5076179 = 7614269) B7614269
theorem B3339731 : Blo 1317977 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B12031577 : Blo 1317977 12031577 := bstep (se 2 (by rfl) ⟨4511841, by rfl⟩ : syracuseStep 12031577 = 9023683) B9023683
theorem B66795131 : Blo 1317977 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B7321259 : Blo 1317977 7321259 := bstep (se 1 (by rfl) ⟨5490944, by rfl⟩ : syracuseStep 7321259 = 10981889) B10981889
theorem B10688219 : Blo 1317977 10688219 := bstep (se 1 (by rfl) ⟨8016164, by rfl⟩ : syracuseStep 10688219 = 16032329) B16032329
theorem B11269853 : Blo 1317977 11269853 := bstep (se 3 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 11269853 = 4226195) B4226195
theorem B6420235 : Blo 1317977 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B5633849 : Blo 1317977 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B2815823 : Blo 1317977 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B2226217 : Blo 1317977 2226217 := bstep (se 2 (by rfl) ⟨834831, by rfl⟩ : syracuseStep 2226217 = 1669663) B1669663
theorem B2005129 : Blo 1317977 2005129 := bstep (se 2 (by rfl) ⟨751923, by rfl⟩ : syracuseStep 2005129 = 1503847) B1503847
theorem B2226359 : Blo 1317977 2226359 := bstep (se 1 (by rfl) ⟨1669769, by rfl⟩ : syracuseStep 2226359 = 3339539) B3339539
theorem B2504935 : Blo 1317977 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B6764957 : Blo 1317977 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B8452619 : Blo 1317977 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B2538127 : Blo 1317977 2538127 := bstep (se 1 (by rfl) ⟨1903595, by rfl⟩ : syracuseStep 2538127 = 3807191) B3807191
theorem B316750661 : Blo 1317977 316750661 := bstep (se 4 (by rfl) ⟨29695374, by rfl⟩ : syracuseStep 316750661 = 59390749) B59390749
theorem B5004251 : Blo 1317977 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B1317979 : Blo 1317977 1317979 := bstep (se 1 (by rfl) ⟨988484, by rfl⟩ : syracuseStep 1317979 = 1976969) B1976969
theorem B2112617 : Blo 1317977 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B6765713 : Blo 1317977 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B1318095 : Blo 1317977 1318095 := bstep (se 1 (by rfl) ⟨988571, by rfl⟩ : syracuseStep 1318095 = 1977143) B1977143
theorem B1318119 : Blo 1317977 1318119 := bstep (se 1 (by rfl) ⟨988589, by rfl⟩ : syracuseStep 1318119 = 1977179) B1977179
theorem B1318215 : Blo 1317977 1318215 := bstep (se 1 (by rfl) ⟨988661, by rfl⟩ : syracuseStep 1318215 = 1977323) B1977323
theorem B28892609 : Blo 1317977 28892609 := bstep (se 2 (by rfl) ⟨10834728, by rfl⟩ : syracuseStep 28892609 = 21669457) B21669457
theorem B1318351 : Blo 1317977 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B1318511 : Blo 1317977 1318511 := bstep (se 1 (by rfl) ⟨988883, by rfl⟩ : syracuseStep 1318511 = 1977767) B1977767
theorem B1318567 : Blo 1317977 1318567 := bstep (se 1 (by rfl) ⟨988925, by rfl⟩ : syracuseStep 1318567 = 1977851) B1977851
theorem B1318631 : Blo 1317977 1318631 := bstep (se 1 (by rfl) ⟨988973, by rfl⟩ : syracuseStep 1318631 = 1977947) B1977947
theorem B1318687 : Blo 1317977 1318687 := bstep (se 1 (by rfl) ⟨989015, by rfl⟩ : syracuseStep 1318687 = 1978031) B1978031
theorem B1318767 : Blo 1317977 1318767 := bstep (se 1 (by rfl) ⟨989075, by rfl⟩ : syracuseStep 1318767 = 1978151) B1978151
theorem B1318823 : Blo 1317977 1318823 := bstep (se 1 (by rfl) ⟨989117, by rfl⟩ : syracuseStep 1318823 = 1978235) B1978235
theorem B1482907 : Blo 1317977 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B1319067 : Blo 1317977 1319067 := bstep (se 1 (by rfl) ⟨989300, by rfl⟩ : syracuseStep 1319067 = 1978601) B1978601
theorem B1318907 : Blo 1317977 1318907 := bstep (se 1 (by rfl) ⟨989180, by rfl⟩ : syracuseStep 1318907 = 1978361) B1978361
theorem B1319151 : Blo 1317977 1319151 := bstep (se 1 (by rfl) ⟨989363, by rfl⟩ : syracuseStep 1319151 = 1978727) B1978727
theorem B4817191 : Blo 1317977 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B7512527 : Blo 1317977 7512527 := bstep (se 1 (by rfl) ⟨5634395, by rfl⟩ : syracuseStep 7512527 = 11268791) B11268791
theorem B10691099 : Blo 1317977 10691099 := bstep (se 1 (by rfl) ⟨8018324, by rfl⟩ : syracuseStep 10691099 = 16036649) B16036649
theorem B15024689 : Blo 1317977 15024689 := bstep (se 2 (by rfl) ⟨5634258, by rfl⟩ : syracuseStep 15024689 = 11268517) B11268517
theorem B3384119 : Blo 1317977 3384119 := bstep (se 1 (by rfl) ⟨2538089, by rfl⟩ : syracuseStep 3384119 = 5076179) B5076179
theorem B3384169 : Blo 1317977 3384169 := bstep (se 2 (by rfl) ⟨1269063, by rfl⟩ : syracuseStep 3384169 = 2538127) B2538127
theorem B8021051 : Blo 1317977 8021051 := bstep (se 1 (by rfl) ⟨6015788, by rfl⟩ : syracuseStep 8021051 = 12031577) B12031577
theorem B7513235 : Blo 1317977 7513235 := bstep (se 1 (by rfl) ⟨5634926, by rfl⟩ : syracuseStep 7513235 = 11269853) B11269853
theorem B15222113 : Blo 1317977 15222113 := bstep (se 2 (by rfl) ⟨5708292, by rfl⟩ : syracuseStep 15222113 = 11416585) B11416585
theorem B2377127 : Blo 1317977 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B1484239 : Blo 1317977 1484239 := bstep (se 1 (by rfl) ⟨1113179, by rfl⟩ : syracuseStep 1484239 = 2226359) B2226359
theorem B178120349 : Blo 1317977 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B211167107 : Blo 1317977 211167107 := bstep (se 1 (by rfl) ⟨158375330, by rfl⟩ : syracuseStep 211167107 = 316750661) B316750661
theorem B3336167 : Blo 1317977 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B19261739 : Blo 1317977 19261739 := bstep (se 1 (by rfl) ⟨14446304, by rfl⟩ : syracuseStep 19261739 = 28892609) B28892609
theorem B2968289 : Blo 1317977 2968289 := bstep (se 2 (by rfl) ⟨1113108, by rfl⟩ : syracuseStep 2968289 = 2226217) B2226217
theorem B5008169 : Blo 1317977 5008169 := bstep (se 2 (by rfl) ⟨1878063, by rfl⟩ : syracuseStep 5008169 = 3756127) B3756127
theorem B2673505 : Blo 1317977 2673505 := bstep (se 2 (by rfl) ⟨1002564, by rfl⟩ : syracuseStep 2673505 = 2005129) B2005129
theorem B146402153 : Blo 1317977 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B1977257 : Blo 1317977 1977257 := bstep (se 2 (by rfl) ⟨741471, by rfl⟩ : syracuseStep 1977257 = 1482943) B1482943
theorem B1977287 : Blo 1317977 1977287 := bstep (se 1 (by rfl) ⟨1482965, by rfl⟩ : syracuseStep 1977287 = 2965931) B2965931
theorem B1977407 : Blo 1317977 1977407 := bstep (se 1 (by rfl) ⟨1483055, by rfl⟩ : syracuseStep 1977407 = 2966111) B2966111
theorem B1977647 : Blo 1317977 1977647 := bstep (se 1 (by rfl) ⟨1483235, by rfl⟩ : syracuseStep 1977647 = 2966471) B2966471
theorem B10014029 : Blo 1317977 10014029 := bstep (se 3 (by rfl) ⟨1877630, by rfl⟩ : syracuseStep 10014029 = 3755261) B3755261
theorem B4222363 : Blo 1317977 4222363 := bstep (se 1 (by rfl) ⟨3166772, by rfl⟩ : syracuseStep 4222363 = 6333545) B6333545
theorem B1977833 : Blo 1317977 1977833 := bstep (se 2 (by rfl) ⟨741687, by rfl⟩ : syracuseStep 1977833 = 1483375) B1483375
theorem B8564201 : Blo 1317977 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B1977887 : Blo 1317977 1977887 := bstep (se 1 (by rfl) ⟨1483415, by rfl⟩ : syracuseStep 1977887 = 2966831) B2966831
theorem B1977977 : Blo 1317977 1977977 := bstep (se 2 (by rfl) ⟨741741, by rfl⟩ : syracuseStep 1977977 = 1483483) B1483483
theorem B13725521 : Blo 1317977 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B3338081 : Blo 1317977 3338081 := bstep (se 2 (by rfl) ⟨1251780, by rfl⟩ : syracuseStep 3338081 = 2503561) B2503561
theorem B1978223 : Blo 1317977 1978223 := bstep (se 1 (by rfl) ⟨1483667, by rfl⟩ : syracuseStep 1978223 = 2967335) B2967335
theorem B3755899 : Blo 1317977 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B1503263 : Blo 1317977 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B1978475 : Blo 1317977 1978475 := bstep (se 1 (by rfl) ⟨1483856, by rfl⟩ : syracuseStep 1978475 = 2967713) B2967713
theorem B5009627 : Blo 1317977 5009627 := bstep (se 1 (by rfl) ⟨3757220, by rfl⟩ : syracuseStep 5009627 = 7514441) B7514441
theorem B4509971 : Blo 1317977 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B1978907 : Blo 1317977 1978907 := bstep (se 1 (by rfl) ⟨1484180, by rfl⟩ : syracuseStep 1978907 = 2968361) B2968361
theorem B11727523 : Blo 1317977 11727523 := bstep (se 1 (by rfl) ⟨8795642, by rfl⟩ : syracuseStep 11727523 = 17591285) B17591285
theorem B1979087 : Blo 1317977 1979087 := bstep (se 1 (by rfl) ⟨1484315, by rfl⟩ : syracuseStep 1979087 = 2968631) B2968631
theorem B43381511 : Blo 1317977 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B4510475 : Blo 1317977 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B7508861 : Blo 1317977 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B10015973 : Blo 1317977 10015973 := bstep (se 4 (by rfl) ⟨938997, by rfl⟩ : syracuseStep 10015973 = 1877995) B1877995
theorem B2504047 : Blo 1317977 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B6673913 : Blo 1317977 6673913 := bstep (se 2 (by rfl) ⟨2502717, by rfl⟩ : syracuseStep 6673913 = 5005435) B5005435
theorem B7509611 : Blo 1317977 7509611 := bstep (se 1 (by rfl) ⟨5632208, by rfl⟩ : syracuseStep 7509611 = 11264417) B11264417
theorem B3339913 : Blo 1317977 3339913 := bstep (se 2 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 3339913 = 2504935) B2504935
theorem B6182543 : Blo 1317977 6182543 := bstep (se 1 (by rfl) ⟨4636907, by rfl⟩ : syracuseStep 6182543 = 9273815) B9273815
theorem B6674075 : Blo 1317977 6674075 := bstep (se 1 (by rfl) ⟨5005556, by rfl⟩ : syracuseStep 6674075 = 10011113) B10011113
theorem B9025271 : Blo 1317977 9025271 := bstep (se 1 (by rfl) ⟨6768953, by rfl⟩ : syracuseStep 9025271 = 13537907) B13537907
theorem B10008683 : Blo 1317977 10008683 := bstep (se 1 (by rfl) ⟨7506512, by rfl⟩ : syracuseStep 10008683 = 15013025) B15013025
theorem B16898219 : Blo 1317977 16898219 := bstep (se 1 (by rfl) ⟨12673664, by rfl⟩ : syracuseStep 16898219 = 25347329) B25347329
theorem B8018135 : Blo 1317977 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B2226487 : Blo 1317977 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B4880839 : Blo 1317977 4880839 := bstep (se 1 (by rfl) ⟨3660629, by rfl⟩ : syracuseStep 4880839 = 7321259) B7321259
theorem B7125479 : Blo 1317977 7125479 := bstep (se 1 (by rfl) ⟨5344109, by rfl⟩ : syracuseStep 7125479 = 10688219) B10688219
theorem B22534847 : Blo 1317977 22534847 := bstep (se 1 (by rfl) ⟨16901135, by rfl⟩ : syracuseStep 22534847 = 33802271) B33802271
theorem B5635079 : Blo 1317977 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B2112809 : Blo 1317977 2112809 := bstep (se 2 (by rfl) ⟨792303, by rfl⟩ : syracuseStep 2112809 = 1584607) B1584607
theorem B1318207 : Blo 1317977 1318207 := bstep (se 1 (by rfl) ⟨988655, by rfl⟩ : syracuseStep 1318207 = 1977311) B1977311
theorem B1408411 : Blo 1317977 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B5709403 : Blo 1317977 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B1318503 : Blo 1317977 1318503 := bstep (se 1 (by rfl) ⟨988877, by rfl⟩ : syracuseStep 1318503 = 1977755) B1977755
theorem B8560313 : Blo 1317977 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B1318783 : Blo 1317977 1318783 := bstep (se 1 (by rfl) ⟨989087, by rfl⟩ : syracuseStep 1318783 = 1978175) B1978175
theorem B1318983 : Blo 1317977 1318983 := bstep (se 1 (by rfl) ⟨989237, by rfl⟩ : syracuseStep 1318983 = 1978475) B1978475
theorem B3006647 : Blo 1317977 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B7127399 : Blo 1317977 7127399 := bstep (se 1 (by rfl) ⟨5345549, by rfl⟩ : syracuseStep 7127399 = 10691099) B10691099
theorem B1319271 : Blo 1317977 1319271 := bstep (se 1 (by rfl) ⟨989453, by rfl⟩ : syracuseStep 1319271 = 1978907) B1978907
theorem B6422921 : Blo 1317977 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B1319391 : Blo 1317977 1319391 := bstep (se 1 (by rfl) ⟨989543, by rfl⟩ : syracuseStep 1319391 = 1979087) B1979087
theorem B3006983 : Blo 1317977 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B5005907 : Blo 1317977 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B6677315 : Blo 1317977 6677315 := bstep (se 1 (by rfl) ⟨5007986, by rfl⟩ : syracuseStep 6677315 = 10015973) B10015973
theorem B62546789 : Blo 1317977 62546789 := bstep (se 4 (by rfl) ⟨5863761, by rfl⟩ : syracuseStep 62546789 = 11727523) B11727523
theorem B4449275 : Blo 1317977 4449275 := bstep (se 1 (by rfl) ⟨3336956, by rfl⟩ : syracuseStep 4449275 = 6673913) B6673913
theorem B5006407 : Blo 1317977 5006407 := bstep (se 1 (by rfl) ⟨3754805, by rfl⟩ : syracuseStep 5006407 = 7509611) B7509611
theorem B4121695 : Blo 1317977 4121695 := bstep (se 1 (by rfl) ⟨3091271, by rfl⟩ : syracuseStep 4121695 = 6182543) B6182543
theorem B4449383 : Blo 1317977 4449383 := bstep (se 1 (by rfl) ⟨3337037, by rfl⟩ : syracuseStep 4449383 = 6674075) B6674075
theorem B11265479 : Blo 1317977 11265479 := bstep (se 1 (by rfl) ⟨8449109, by rfl⟩ : syracuseStep 11265479 = 16898219) B16898219
theorem B5629817 : Blo 1317977 5629817 := bstep (se 2 (by rfl) ⟨2111181, by rfl⟩ : syracuseStep 5629817 = 4222363) B4222363
theorem B18048901 : Blo 1317977 18048901 := bstep (se 4 (by rfl) ⟨1692084, by rfl⟩ : syracuseStep 18048901 = 3384169) B3384169
theorem B97601435 : Blo 1317977 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B7612537 : Blo 1317977 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B5007865 : Blo 1317977 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B4008701 : Blo 1317977 4008701 := bstep (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) B1503263
theorem B1977209 : Blo 1317977 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B5008351 : Blo 1317977 5008351 := bstep (se 1 (by rfl) ⟨3756263, by rfl⟩ : syracuseStep 5008351 = 7512527) B7512527
theorem B2968649 : Blo 1317977 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B28921007 : Blo 1317977 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B2256079 : Blo 1317977 2256079 := bstep (se 1 (by rfl) ⟨1692059, by rfl⟩ : syracuseStep 2256079 = 3384119) B3384119
theorem B6507785 : Blo 1317977 6507785 := bstep (se 2 (by rfl) ⟨2440419, by rfl⟩ : syracuseStep 6507785 = 4880839) B4880839
theorem B5008823 : Blo 1317977 5008823 := bstep (se 1 (by rfl) ⟨3756617, by rfl⟩ : syracuseStep 5008823 = 7513235) B7513235
theorem B118746899 : Blo 1317977 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B6016847 : Blo 1317977 6016847 := bstep (se 1 (by rfl) ⟨4512635, by rfl⟩ : syracuseStep 6016847 = 9025271) B9025271
theorem B2224111 : Blo 1317977 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B6672455 : Blo 1317977 6672455 := bstep (se 1 (by rfl) ⟨5004341, by rfl⟩ : syracuseStep 6672455 = 10008683) B10008683
theorem B5345423 : Blo 1317977 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B12841159 : Blo 1317977 12841159 := bstep (se 1 (by rfl) ⟨9630869, by rfl⟩ : syracuseStep 12841159 = 19261739) B19261739
theorem B3338729 : Blo 1317977 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B1978859 : Blo 1317977 1978859 := bstep (se 1 (by rfl) ⟨1484144, by rfl⟩ : syracuseStep 1978859 = 2968289) B2968289
theorem B14258693 : Blo 1317977 14258693 := bstep (se 4 (by rfl) ⟨1336752, by rfl⟩ : syracuseStep 14258693 = 2673505) B2673505
theorem B3338779 : Blo 1317977 3338779 := bstep (se 1 (by rfl) ⟨2504084, by rfl⟩ : syracuseStep 3338779 = 5008169) B5008169
theorem B1978985 : Blo 1317977 1978985 := bstep (se 2 (by rfl) ⟨742119, by rfl⟩ : syracuseStep 1978985 = 1484239) B1484239
theorem B3756719 : Blo 1317977 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B4453217 : Blo 1317977 4453217 := bstep (se 2 (by rfl) ⟨1669956, by rfl⟩ : syracuseStep 4453217 = 3339913) B3339913
theorem B5706875 : Blo 1317977 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B2225387 : Blo 1317977 2225387 := bstep (se 1 (by rfl) ⟨1669040, by rfl⟩ : syracuseStep 2225387 = 3338081) B3338081
theorem B3339751 : Blo 1317977 3339751 := bstep (se 1 (by rfl) ⟨2504813, by rfl⟩ : syracuseStep 3339751 = 5009627) B5009627
theorem B10016459 : Blo 1317977 10016459 := bstep (se 1 (by rfl) ⟨7512344, by rfl⟩ : syracuseStep 10016459 = 15024689) B15024689
theorem B5347367 : Blo 1317977 5347367 := bstep (se 1 (by rfl) ⟨4010525, by rfl⟩ : syracuseStep 5347367 = 8021051) B8021051
theorem B5634157 : Blo 1317977 5634157 := bstep (se 3 (by rfl) ⟨1056404, by rfl⟩ : syracuseStep 5634157 = 2112809) B2112809
theorem B10148075 : Blo 1317977 10148075 := bstep (se 1 (by rfl) ⟨7611056, by rfl⟩ : syracuseStep 10148075 = 15222113) B15222113
theorem B6339005 : Blo 1317977 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B140778071 : Blo 1317977 140778071 := bstep (se 1 (by rfl) ⟨105583553, by rfl⟩ : syracuseStep 140778071 = 211167107) B211167107
theorem B4750319 : Blo 1317977 4750319 := bstep (se 1 (by rfl) ⟨3562739, by rfl⟩ : syracuseStep 4750319 = 7125479) B7125479
theorem B15023231 : Blo 1317977 15023231 := bstep (se 1 (by rfl) ⟨11267423, by rfl⟩ : syracuseStep 15023231 = 22534847) B22534847
theorem B1318171 : Blo 1317977 1318171 := bstep (se 1 (by rfl) ⟨988628, by rfl⟩ : syracuseStep 1318171 = 1977257) B1977257
theorem B1318191 : Blo 1317977 1318191 := bstep (se 1 (by rfl) ⟨988643, by rfl⟩ : syracuseStep 1318191 = 1977287) B1977287
theorem B1318271 : Blo 1317977 1318271 := bstep (se 1 (by rfl) ⟨988703, by rfl⟩ : syracuseStep 1318271 = 1977407) B1977407
theorem B7511525 : Blo 1317977 7511525 := bstep (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) B1408411
theorem B1318431 : Blo 1317977 1318431 := bstep (se 1 (by rfl) ⟨988823, by rfl⟩ : syracuseStep 1318431 = 1977647) B1977647
theorem B6676019 : Blo 1317977 6676019 := bstep (se 1 (by rfl) ⟨5007014, by rfl⟩ : syracuseStep 6676019 = 10014029) B10014029
theorem B1318555 : Blo 1317977 1318555 := bstep (se 1 (by rfl) ⟨988916, by rfl⟩ : syracuseStep 1318555 = 1977833) B1977833
theorem B5709467 : Blo 1317977 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B1318591 : Blo 1317977 1318591 := bstep (se 1 (by rfl) ⟨988943, by rfl⟩ : syracuseStep 1318591 = 1977887) B1977887
theorem B1318651 : Blo 1317977 1318651 := bstep (se 1 (by rfl) ⟨988988, by rfl⟩ : syracuseStep 1318651 = 1977977) B1977977
theorem B9150347 : Blo 1317977 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B1318815 : Blo 1317977 1318815 := bstep (se 1 (by rfl) ⟨989111, by rfl⟩ : syracuseStep 1318815 = 1978223) B1978223
theorem B4448303 : Blo 1317977 4448303 := bstep (se 1 (by rfl) ⟨3336227, by rfl⟩ : syracuseStep 4448303 = 6672455) B6672455
theorem B3563615 : Blo 1317977 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B7512209 : Blo 1317977 7512209 := bstep (se 2 (by rfl) ⟨2817078, by rfl⟩ : syracuseStep 7512209 = 5634157) B5634157
theorem B10150049 : Blo 1317977 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B17121545 : Blo 1317977 17121545 := bstep (se 2 (by rfl) ⟨6420579, by rfl⟩ : syracuseStep 17121545 = 12841159) B12841159
theorem B1319239 : Blo 1317977 1319239 := bstep (se 1 (by rfl) ⟨989429, by rfl⟩ : syracuseStep 1319239 = 1978859) B1978859
theorem B1319323 : Blo 1317977 1319323 := bstep (se 1 (by rfl) ⟨989492, by rfl⟩ : syracuseStep 1319323 = 1978985) B1978985
theorem B6677153 : Blo 1317977 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B2966183 : Blo 1317977 2966183 := bstep (se 1 (by rfl) ⟨2224637, by rfl⟩ : syracuseStep 2966183 = 4449275) B4449275
theorem B2966255 : Blo 1317977 2966255 := bstep (se 1 (by rfl) ⟨2224691, by rfl⟩ : syracuseStep 2966255 = 4449383) B4449383
theorem B1483591 : Blo 1317977 1483591 := bstep (se 1 (by rfl) ⟨1112693, by rfl⟩ : syracuseStep 1483591 = 2225387) B2225387
theorem B19006397 : Blo 1317977 19006397 := bstep (se 3 (by rfl) ⟨3563699, by rfl⟩ : syracuseStep 19006397 = 7127399) B7127399
theorem B6677639 : Blo 1317977 6677639 := bstep (se 1 (by rfl) ⟨5008229, by rfl⟩ : syracuseStep 6677639 = 10016459) B10016459
theorem B3753211 : Blo 1317977 3753211 := bstep (se 1 (by rfl) ⟨2814908, by rfl⟩ : syracuseStep 3753211 = 5629817) B5629817
theorem B6677801 : Blo 1317977 6677801 := bstep (se 2 (by rfl) ⟨2504175, by rfl⟩ : syracuseStep 6677801 = 5008351) B5008351
theorem B3564911 : Blo 1317977 3564911 := bstep (se 1 (by rfl) ⟨2673683, by rfl⟩ : syracuseStep 3564911 = 5347367) B5347367
theorem B3008105 : Blo 1317977 3008105 := bstep (se 2 (by rfl) ⟨1128039, by rfl⟩ : syracuseStep 3008105 = 2256079) B2256079
theorem B166791437 : Blo 1317977 166791437 := bstep (se 3 (by rfl) ⟨31273394, by rfl⟩ : syracuseStep 166791437 = 62546789) B62546789
theorem B5007683 : Blo 1317977 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B4450679 : Blo 1317977 4450679 := bstep (se 1 (by rfl) ⟨3338009, by rfl⟩ : syracuseStep 4450679 = 6676019) B6676019
theorem B3337271 : Blo 1317977 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B77122685 : Blo 1317977 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B21982373 : Blo 1317977 21982373 := bstep (se 4 (by rfl) ⟨2060847, by rfl⟩ : syracuseStep 21982373 = 4121695) B4121695
theorem B4451543 : Blo 1317977 4451543 := bstep (se 1 (by rfl) ⟨3338657, by rfl⟩ : syracuseStep 4451543 = 6677315) B6677315
theorem B2968811 : Blo 1317977 2968811 := bstep (se 1 (by rfl) ⟨2226608, by rfl⟩ : syracuseStep 2968811 = 4453217) B4453217
theorem B4451705 : Blo 1317977 4451705 := bstep (se 2 (by rfl) ⟨1669389, by rfl⟩ : syracuseStep 4451705 = 3338779) B3338779
theorem B3804583 : Blo 1317977 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B64179701 : Blo 1317977 64179701 := bstep (se 5 (by rfl) ⟨3008423, by rfl⟩ : syracuseStep 64179701 = 6016847) B6016847
theorem B38023181 : Blo 1317977 38023181 := bstep (se 3 (by rfl) ⟨7129346, by rfl⟩ : syracuseStep 38023181 = 14258693) B14258693
theorem B93852047 : Blo 1317977 93852047 := bstep (se 1 (by rfl) ⟨70389035, by rfl⟩ : syracuseStep 93852047 = 140778071) B140778071
theorem B15225245 : Blo 1317977 15225245 := bstep (se 3 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 15225245 = 5709467) B5709467
theorem B4453001 : Blo 1317977 4453001 := bstep (se 2 (by rfl) ⟨1669875, by rfl⟩ : syracuseStep 4453001 = 3339751) B3339751
theorem B3166879 : Blo 1317977 3166879 := bstep (se 1 (by rfl) ⟨2375159, by rfl⟩ : syracuseStep 3166879 = 4750319) B4750319
theorem B1979099 : Blo 1317977 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B10015487 : Blo 1317977 10015487 := bstep (se 1 (by rfl) ⟨7511615, by rfl⟩ : syracuseStep 10015487 = 15023231) B15023231
theorem B4338523 : Blo 1317977 4338523 := bstep (se 1 (by rfl) ⟨3253892, by rfl⟩ : syracuseStep 4338523 = 6507785) B6507785
theorem B3339215 : Blo 1317977 3339215 := bstep (se 1 (by rfl) ⟨2504411, by rfl⟩ : syracuseStep 3339215 = 5008823) B5008823
theorem B24400925 : Blo 1317977 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B24065201 : Blo 1317977 24065201 := bstep (se 2 (by rfl) ⟨9024450, by rfl⟩ : syracuseStep 24065201 = 18048901) B18048901
theorem B79164599 : Blo 1317977 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B2004431 : Blo 1317977 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B4281947 : Blo 1317977 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B2225819 : Blo 1317977 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B7510319 : Blo 1317977 7510319 := bstep (se 1 (by rfl) ⟨5632739, by rfl⟩ : syracuseStep 7510319 = 11265479) B11265479
theorem B65067623 : Blo 1317977 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B8018621 : Blo 1317977 8018621 := bstep (se 3 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 8018621 = 3006983) B3006983
theorem B6675209 : Blo 1317977 6675209 := bstep (se 2 (by rfl) ⟨2503203, by rfl⟩ : syracuseStep 6675209 = 5006407) B5006407
theorem B6765383 : Blo 1317977 6765383 := bstep (se 1 (by rfl) ⟨5074037, by rfl⟩ : syracuseStep 6765383 = 10148075) B10148075
theorem B4226003 : Blo 1317977 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B10017917 : Blo 1317977 10017917 := bstep (se 3 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 10017917 = 3756719) B3756719
theorem B1318139 : Blo 1317977 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B10689869 : Blo 1317977 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B2965481 : Blo 1317977 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B2965535 : Blo 1317977 2965535 := bstep (se 1 (by rfl) ⟨2224151, by rfl⟩ : syracuseStep 2965535 = 4448303) B4448303
theorem B2375743 : Blo 1317977 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B6766699 : Blo 1317977 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B10150163 : Blo 1317977 10150163 := bstep (se 1 (by rfl) ⟨7612622, by rfl⟩ : syracuseStep 10150163 = 15225245) B15225245
theorem B1319399 : Blo 1317977 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B6676991 : Blo 1317977 6676991 := bstep (se 1 (by rfl) ⟨5007743, by rfl⟩ : syracuseStep 6676991 = 10015487) B10015487
theorem B1483879 : Blo 1317977 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B5006879 : Blo 1317977 5006879 := bstep (se 1 (by rfl) ⟨3755159, by rfl⟩ : syracuseStep 5006879 = 7510319) B7510319
theorem B2967119 : Blo 1317977 2967119 := bstep (se 1 (by rfl) ⟨2225339, by rfl⟩ : syracuseStep 2967119 = 4450679) B4450679
theorem B43378415 : Blo 1317977 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B4450139 : Blo 1317977 4450139 := bstep (se 1 (by rfl) ⟨3337604, by rfl⟩ : syracuseStep 4450139 = 6675209) B6675209
theorem B5072777 : Blo 1317977 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B6678611 : Blo 1317977 6678611 := bstep (se 1 (by rfl) ⟨5008958, by rfl⟩ : syracuseStep 6678611 = 10017917) B10017917
theorem B51415123 : Blo 1317977 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B2967695 : Blo 1317977 2967695 := bstep (se 1 (by rfl) ⟨2225771, by rfl⟩ : syracuseStep 2967695 = 4451543) B4451543
theorem B2967803 : Blo 1317977 2967803 := bstep (se 1 (by rfl) ⟨2225852, by rfl⟩ : syracuseStep 2967803 = 4451705) B4451705
theorem B1976987 : Blo 1317977 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B25348787 : Blo 1317977 25348787 := bstep (se 1 (by rfl) ⟨19011590, by rfl⟩ : syracuseStep 25348787 = 38023181) B38023181
theorem B5008139 : Blo 1317977 5008139 := bstep (se 1 (by rfl) ⟨3756104, by rfl⟩ : syracuseStep 5008139 = 7512209) B7512209
theorem B11414363 : Blo 1317977 11414363 := bstep (se 1 (by rfl) ⟨8560772, by rfl⟩ : syracuseStep 11414363 = 17121545) B17121545
theorem B2968667 : Blo 1317977 2968667 := bstep (se 1 (by rfl) ⟨2226500, by rfl⟩ : syracuseStep 2968667 = 4453001) B4453001
theorem B4451435 : Blo 1317977 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B1977455 : Blo 1317977 1977455 := bstep (se 1 (by rfl) ⟨1483091, by rfl⟩ : syracuseStep 1977455 = 2966183) B2966183
theorem B1977503 : Blo 1317977 1977503 := bstep (se 1 (by rfl) ⟨1483127, by rfl⟩ : syracuseStep 1977503 = 2966255) B2966255
theorem B4451759 : Blo 1317977 4451759 := bstep (se 1 (by rfl) ⟨3338819, by rfl⟩ : syracuseStep 4451759 = 6677639) B6677639
theorem B16043467 : Blo 1317977 16043467 := bstep (se 1 (by rfl) ⟨12032600, by rfl⟩ : syracuseStep 16043467 = 24065201) B24065201
theorem B4451867 : Blo 1317977 4451867 := bstep (se 1 (by rfl) ⟨3338900, by rfl⟩ : syracuseStep 4451867 = 6677801) B6677801
theorem B4222505 : Blo 1317977 4222505 := bstep (se 2 (by rfl) ⟨1583439, by rfl⟩ : syracuseStep 4222505 = 3166879) B3166879
theorem B9506429 : Blo 1317977 9506429 := bstep (se 3 (by rfl) ⟨1782455, by rfl⟩ : syracuseStep 9506429 = 3564911) B3564911
theorem B2854631 : Blo 1317977 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B1978121 : Blo 1317977 1978121 := bstep (se 2 (by rfl) ⟨741795, by rfl⟩ : syracuseStep 1978121 = 1483591) B1483591
theorem B5345149 : Blo 1317977 5345149 := bstep (se 3 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 5345149 = 2004431) B2004431
theorem B111194291 : Blo 1317977 111194291 := bstep (se 1 (by rfl) ⟨83395718, by rfl⟩ : syracuseStep 111194291 = 166791437) B166791437
theorem B3338455 : Blo 1317977 3338455 := bstep (se 1 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 3338455 = 5007683) B5007683
theorem B5345747 : Blo 1317977 5345747 := bstep (se 1 (by rfl) ⟨4009310, by rfl⟩ : syracuseStep 5345747 = 8018621) B8018621
theorem B23138789 : Blo 1317977 23138789 := bstep (se 4 (by rfl) ⟨2169261, by rfl⟩ : syracuseStep 23138789 = 4338523) B4338523
theorem B4510255 : Blo 1317977 4510255 := bstep (se 1 (by rfl) ⟨3382691, by rfl⟩ : syracuseStep 4510255 = 6765383) B6765383
theorem B2224847 : Blo 1317977 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B1979207 : Blo 1317977 1979207 := bstep (se 1 (by rfl) ⟨1484405, by rfl⟩ : syracuseStep 1979207 = 2968811) B2968811
theorem B211105597 : Blo 1317977 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B12670931 : Blo 1317977 12670931 := bstep (se 1 (by rfl) ⟨9503198, by rfl⟩ : syracuseStep 12670931 = 19006397) B19006397
theorem B2226143 : Blo 1317977 2226143 := bstep (se 1 (by rfl) ⟨1669607, by rfl⟩ : syracuseStep 2226143 = 3339215) B3339215
theorem B16267283 : Blo 1317977 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B250272125 : Blo 1317977 250272125 := bstep (se 3 (by rfl) ⟨46926023, by rfl⟩ : syracuseStep 250272125 = 93852047) B93852047
theorem B2005403 : Blo 1317977 2005403 := bstep (se 1 (by rfl) ⟨1504052, by rfl⟩ : syracuseStep 2005403 = 3008105) B3008105
theorem B5004281 : Blo 1317977 5004281 := bstep (se 2 (by rfl) ⟨1876605, by rfl⟩ : syracuseStep 5004281 = 3753211) B3753211
theorem B2817335 : Blo 1317977 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B14654915 : Blo 1317977 14654915 := bstep (se 1 (by rfl) ⟨10991186, by rfl⟩ : syracuseStep 14654915 = 21982373) B21982373
theorem B7126579 : Blo 1317977 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B42786467 : Blo 1317977 42786467 := bstep (se 1 (by rfl) ⟨32089850, by rfl⟩ : syracuseStep 42786467 = 64179701) B64179701
theorem B74129527 : Blo 1317977 74129527 := bstep (se 1 (by rfl) ⟨55597145, by rfl⟩ : syracuseStep 74129527 = 111194291) B111194291
theorem B6766775 : Blo 1317977 6766775 := bstep (se 1 (by rfl) ⟨5075081, by rfl⟩ : syracuseStep 6766775 = 10150163) B10150163
theorem B3563831 : Blo 1317977 3563831 := bstep (se 1 (by rfl) ⟨2672873, by rfl⟩ : syracuseStep 3563831 = 5345747) B5345747
theorem B1483231 : Blo 1317977 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B1319471 : Blo 1317977 1319471 := bstep (se 1 (by rfl) ⟨989603, by rfl⟩ : syracuseStep 1319471 = 1979207) B1979207
theorem B6013673 : Blo 1317977 6013673 := bstep (se 2 (by rfl) ⟨2255127, by rfl⟩ : syracuseStep 6013673 = 4510255) B4510255
theorem B28918943 : Blo 1317977 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B2966759 : Blo 1317977 2966759 := bstep (se 1 (by rfl) ⟨2225069, by rfl⟩ : syracuseStep 2966759 = 4450139) B4450139
theorem B1484095 : Blo 1317977 1484095 := bstep (se 1 (by rfl) ⟨1113071, by rfl⟩ : syracuseStep 1484095 = 2226143) B2226143
theorem B166848083 : Blo 1317977 166848083 := bstep (se 1 (by rfl) ⟨125136062, by rfl⟩ : syracuseStep 166848083 = 250272125) B250272125
theorem B21390965 : Blo 1317977 21390965 := bstep (se 5 (by rfl) ⟨1002701, by rfl⟩ : syracuseStep 21390965 = 2005403) B2005403
theorem B21391289 : Blo 1317977 21391289 := bstep (se 2 (by rfl) ⟨8021733, by rfl⟩ : syracuseStep 21391289 = 16043467) B16043467
theorem B3336187 : Blo 1317977 3336187 := bstep (se 1 (by rfl) ⟨2502140, by rfl⟩ : syracuseStep 3336187 = 5004281) B5004281
theorem B2967623 : Blo 1317977 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B1878223 : Blo 1317977 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B2967839 : Blo 1317977 2967839 := bstep (se 1 (by rfl) ⟨2225879, by rfl⟩ : syracuseStep 2967839 = 4451759) B4451759
theorem B2967911 : Blo 1317977 2967911 := bstep (se 1 (by rfl) ⟨2225933, by rfl⟩ : syracuseStep 2967911 = 4451867) B4451867
theorem B1903087 : Blo 1317977 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B1977023 : Blo 1317977 1977023 := bstep (se 1 (by rfl) ⟨1482767, by rfl⟩ : syracuseStep 1977023 = 2965535) B2965535
theorem B68553497 : Blo 1317977 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B9022265 : Blo 1317977 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B4451273 : Blo 1317977 4451273 := bstep (se 2 (by rfl) ⟨1669227, by rfl⟩ : syracuseStep 4451273 = 3338455) B3338455
theorem B4451327 : Blo 1317977 4451327 := bstep (se 1 (by rfl) ⟨3338495, by rfl⟩ : syracuseStep 4451327 = 6676991) B6676991
theorem B3337919 : Blo 1317977 3337919 := bstep (se 1 (by rfl) ⟨2503439, by rfl⟩ : syracuseStep 3337919 = 5006879) B5006879
theorem B1978079 : Blo 1317977 1978079 := bstep (se 1 (by rfl) ⟨1483559, by rfl⟩ : syracuseStep 1978079 = 2967119) B2967119
theorem B4452407 : Blo 1317977 4452407 := bstep (se 1 (by rfl) ⟨3339305, by rfl⟩ : syracuseStep 4452407 = 6678611) B6678611
theorem B1978463 : Blo 1317977 1978463 := bstep (se 1 (by rfl) ⟨1483847, by rfl⟩ : syracuseStep 1978463 = 2967695) B2967695
theorem B1978505 : Blo 1317977 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B1978535 : Blo 1317977 1978535 := bstep (se 1 (by rfl) ⟨1483901, by rfl⟩ : syracuseStep 1978535 = 2967803) B2967803
theorem B3338759 : Blo 1317977 3338759 := bstep (se 1 (by rfl) ⟨2504069, by rfl⟩ : syracuseStep 3338759 = 5008139) B5008139
theorem B1979111 : Blo 1317977 1979111 := bstep (se 1 (by rfl) ⟨1484333, by rfl⟩ : syracuseStep 1979111 = 2968667) B2968667
theorem B30438301 : Blo 1317977 30438301 := bstep (se 3 (by rfl) ⟨5707181, by rfl⟩ : syracuseStep 30438301 = 11414363) B11414363
theorem B9769943 : Blo 1317977 9769943 := bstep (se 1 (by rfl) ⟨7327457, by rfl⟩ : syracuseStep 9769943 = 14654915) B14654915
theorem B2815003 : Blo 1317977 2815003 := bstep (se 1 (by rfl) ⟨2111252, by rfl⟩ : syracuseStep 2815003 = 4222505) B4222505
theorem B246813749 : Blo 1317977 246813749 := bstep (se 5 (by rfl) ⟨11569394, by rfl⟩ : syracuseStep 246813749 = 23138789) B23138789
theorem B281474129 : Blo 1317977 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B6337619 : Blo 1317977 6337619 := bstep (se 1 (by rfl) ⟨4753214, by rfl⟩ : syracuseStep 6337619 = 9506429) B9506429
theorem B33789149 : Blo 1317977 33789149 := bstep (se 3 (by rfl) ⟨6335465, by rfl⟩ : syracuseStep 33789149 = 12670931) B12670931
theorem B3167657 : Blo 1317977 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B3381851 : Blo 1317977 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B10844855 : Blo 1317977 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B1317991 : Blo 1317977 1317991 := bstep (se 1 (by rfl) ⟨988493, by rfl⟩ : syracuseStep 1317991 = 1976987) B1976987
theorem B16899191 : Blo 1317977 16899191 := bstep (se 1 (by rfl) ⟨12674393, by rfl⟩ : syracuseStep 16899191 = 25348787) B25348787
theorem B9502105 : Blo 1317977 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B1318303 : Blo 1317977 1318303 := bstep (se 1 (by rfl) ⟨988727, by rfl⟩ : syracuseStep 1318303 = 1977455) B1977455
theorem B1318335 : Blo 1317977 1318335 := bstep (se 1 (by rfl) ⟨988751, by rfl⟩ : syracuseStep 1318335 = 1977503) B1977503
theorem B28524311 : Blo 1317977 28524311 := bstep (se 1 (by rfl) ⟨21393233, by rfl⟩ : syracuseStep 28524311 = 42786467) B42786467
theorem B7126865 : Blo 1317977 7126865 := bstep (se 2 (by rfl) ⟨2672574, by rfl⟩ : syracuseStep 7126865 = 5345149) B5345149
theorem B1318747 : Blo 1317977 1318747 := bstep (se 1 (by rfl) ⟨989060, by rfl⟩ : syracuseStep 1318747 = 1978121) B1978121
theorem B1318975 : Blo 1317977 1318975 := bstep (se 1 (by rfl) ⟨989231, by rfl⟩ : syracuseStep 1318975 = 1978463) B1978463
theorem B1319003 : Blo 1317977 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B1319023 : Blo 1317977 1319023 := bstep (se 1 (by rfl) ⟨989267, by rfl⟩ : syracuseStep 1319023 = 1978535) B1978535
theorem B2375887 : Blo 1317977 2375887 := bstep (se 1 (by rfl) ⟨1781915, by rfl⟩ : syracuseStep 2375887 = 3563831) B3563831
theorem B1319407 : Blo 1317977 1319407 := bstep (se 1 (by rfl) ⟨989555, by rfl⟩ : syracuseStep 1319407 = 1979111) B1979111
theorem B6513295 : Blo 1317977 6513295 := bstep (se 1 (by rfl) ⟨4884971, by rfl⟩ : syracuseStep 6513295 = 9769943) B9769943
theorem B111232055 : Blo 1317977 111232055 := bstep (se 1 (by rfl) ⟨83424041, by rfl⟩ : syracuseStep 111232055 = 166848083) B166848083
theorem B40584401 : Blo 1317977 40584401 := bstep (se 2 (by rfl) ⟨15219150, by rfl⟩ : syracuseStep 40584401 = 30438301) B30438301
theorem B3753337 : Blo 1317977 3753337 := bstep (se 2 (by rfl) ⟨1407501, by rfl⟩ : syracuseStep 3753337 = 2815003) B2815003
theorem B2254567 : Blo 1317977 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B6014843 : Blo 1317977 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B2967515 : Blo 1317977 2967515 := bstep (se 1 (by rfl) ⟨2225636, by rfl⟩ : syracuseStep 2967515 = 4451273) B4451273
theorem B2967551 : Blo 1317977 2967551 := bstep (se 1 (by rfl) ⟨2225663, by rfl⟩ : syracuseStep 2967551 = 4451327) B4451327
theorem B11266127 : Blo 1317977 11266127 := bstep (se 1 (by rfl) ⟨8449595, by rfl⟩ : syracuseStep 11266127 = 16899191) B16899191
theorem B19016207 : Blo 1317977 19016207 := bstep (se 1 (by rfl) ⟨14262155, by rfl⟩ : syracuseStep 19016207 = 28524311) B28524311
theorem B2968271 : Blo 1317977 2968271 := bstep (se 1 (by rfl) ⟨2226203, by rfl⟩ : syracuseStep 2968271 = 4452407) B4452407
theorem B98839369 : Blo 1317977 98839369 := bstep (se 2 (by rfl) ⟨37064763, by rfl⟩ : syracuseStep 98839369 = 74129527) B74129527
theorem B4009115 : Blo 1317977 4009115 := bstep (se 1 (by rfl) ⟨3006836, by rfl⟩ : syracuseStep 4009115 = 6013673) B6013673
theorem B1977641 : Blo 1317977 1977641 := bstep (se 2 (by rfl) ⟨741615, by rfl⟩ : syracuseStep 1977641 = 1483231) B1483231
theorem B187649419 : Blo 1317977 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B19279295 : Blo 1317977 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B1977839 : Blo 1317977 1977839 := bstep (se 1 (by rfl) ⟨1483379, by rfl⟩ : syracuseStep 1977839 = 2966759) B2966759
theorem B1978415 : Blo 1317977 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B1978559 : Blo 1317977 1978559 := bstep (se 1 (by rfl) ⟨1483919, by rfl⟩ : syracuseStep 1978559 = 2967839) B2967839
theorem B1978607 : Blo 1317977 1978607 := bstep (se 1 (by rfl) ⟨1483955, by rfl⟩ : syracuseStep 1978607 = 2967911) B2967911
theorem B1978793 : Blo 1317977 1978793 := bstep (se 2 (by rfl) ⟨742047, by rfl⟩ : syracuseStep 1978793 = 1484095) B1484095
theorem B7229903 : Blo 1317977 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B12669473 : Blo 1317977 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B182809325 : Blo 1317977 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B2225279 : Blo 1317977 2225279 := bstep (se 1 (by rfl) ⟨1668959, by rfl⟩ : syracuseStep 2225279 = 3337919) B3337919
theorem B4511183 : Blo 1317977 4511183 := bstep (se 1 (by rfl) ⟨3383387, by rfl⟩ : syracuseStep 4511183 = 6766775) B6766775
theorem B2504297 : Blo 1317977 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B2225839 : Blo 1317977 2225839 := bstep (se 1 (by rfl) ⟨1669379, by rfl⟩ : syracuseStep 2225839 = 3338759) B3338759
theorem B164542499 : Blo 1317977 164542499 := bstep (se 1 (by rfl) ⟨123406874, by rfl⟩ : syracuseStep 164542499 = 246813749) B246813749
theorem B4225079 : Blo 1317977 4225079 := bstep (se 1 (by rfl) ⟨3168809, by rfl⟩ : syracuseStep 4225079 = 6337619) B6337619
theorem B22526099 : Blo 1317977 22526099 := bstep (se 1 (by rfl) ⟨16894574, by rfl⟩ : syracuseStep 22526099 = 33789149) B33789149
theorem B2111771 : Blo 1317977 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B14260643 : Blo 1317977 14260643 := bstep (se 1 (by rfl) ⟨10695482, by rfl⟩ : syracuseStep 14260643 = 21390965) B21390965
theorem B14260859 : Blo 1317977 14260859 := bstep (se 1 (by rfl) ⟨10695644, by rfl⟩ : syracuseStep 14260859 = 21391289) B21391289
theorem B1318015 : Blo 1317977 1318015 := bstep (se 1 (by rfl) ⟨988511, by rfl⟩ : syracuseStep 1318015 = 1977023) B1977023
theorem B4448249 : Blo 1317977 4448249 := bstep (se 2 (by rfl) ⟨1668093, by rfl⟩ : syracuseStep 4448249 = 3336187) B3336187
theorem B1318719 : Blo 1317977 1318719 := bstep (se 1 (by rfl) ⟨989039, by rfl⟩ : syracuseStep 1318719 = 1978079) B1978079
theorem B4751243 : Blo 1317977 4751243 := bstep (se 1 (by rfl) ⟨3563432, by rfl⟩ : syracuseStep 4751243 = 7126865) B7126865
theorem B10149797 : Blo 1317977 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B1318943 : Blo 1317977 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B1319039 : Blo 1317977 1319039 := bstep (se 1 (by rfl) ⟨989279, by rfl⟩ : syracuseStep 1319039 = 1978559) B1978559
theorem B1319071 : Blo 1317977 1319071 := bstep (se 1 (by rfl) ⟨989303, by rfl⟩ : syracuseStep 1319071 = 1978607) B1978607
theorem B1319195 : Blo 1317977 1319195 := bstep (se 1 (by rfl) ⟨989396, by rfl⟩ : syracuseStep 1319195 = 1978793) B1978793
theorem B8446315 : Blo 1317977 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B10690973 : Blo 1317977 10690973 := bstep (se 3 (by rfl) ⟨2004557, by rfl⟩ : syracuseStep 10690973 = 4009115) B4009115
theorem B121872883 : Blo 1317977 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B1483519 : Blo 1317977 1483519 := bstep (se 1 (by rfl) ⟨1112639, by rfl⟩ : syracuseStep 1483519 = 2225279) B2225279
theorem B131785825 : Blo 1317977 131785825 := bstep (se 2 (by rfl) ⟨49419684, by rfl⟩ : syracuseStep 131785825 = 98839369) B98839369
theorem B15017399 : Blo 1317977 15017399 := bstep (se 1 (by rfl) ⟨11263049, by rfl⟩ : syracuseStep 15017399 = 22526099) B22526099
theorem B6678125 : Blo 1317977 6678125 := bstep (se 3 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 6678125 = 2504297) B2504297
theorem B2967785 : Blo 1317977 2967785 := bstep (se 2 (by rfl) ⟨1112919, by rfl⟩ : syracuseStep 2967785 = 2225839) B2225839
theorem B296618813 : Blo 1317977 296618813 := bstep (se 3 (by rfl) ⟨55616027, by rfl⟩ : syracuseStep 296618813 = 111232055) B111232055
theorem B11266877 : Blo 1317977 11266877 := bstep (se 3 (by rfl) ⟨2112539, by rfl⟩ : syracuseStep 11266877 = 4225079) B4225079
theorem B5631389 : Blo 1317977 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B19279741 : Blo 1317977 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B4009895 : Blo 1317977 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B1978343 : Blo 1317977 1978343 := bstep (se 1 (by rfl) ⟨1483757, by rfl⟩ : syracuseStep 1978343 = 2967515) B2967515
theorem B1978367 : Blo 1317977 1978367 := bstep (se 1 (by rfl) ⟨1483775, by rfl⟩ : syracuseStep 1978367 = 2967551) B2967551
theorem B109694999 : Blo 1317977 109694999 := bstep (se 1 (by rfl) ⟨82271249, by rfl⟩ : syracuseStep 109694999 = 164542499) B164542499
theorem B9507095 : Blo 1317977 9507095 := bstep (se 1 (by rfl) ⟨7130321, by rfl⟩ : syracuseStep 9507095 = 14260643) B14260643
theorem B12677471 : Blo 1317977 12677471 := bstep (se 1 (by rfl) ⟨9508103, by rfl⟩ : syracuseStep 12677471 = 19016207) B19016207
theorem B9507239 : Blo 1317977 9507239 := bstep (se 1 (by rfl) ⟨7130429, by rfl⟩ : syracuseStep 9507239 = 14260859) B14260859
theorem B1978847 : Blo 1317977 1978847 := bstep (se 1 (by rfl) ⟨1484135, by rfl⟩ : syracuseStep 1978847 = 2968271) B2968271
theorem B3167495 : Blo 1317977 3167495 := bstep (se 1 (by rfl) ⟨2375621, by rfl⟩ : syracuseStep 3167495 = 4751243) B4751243
theorem B3167849 : Blo 1317977 3167849 := bstep (se 2 (by rfl) ⟨1187943, by rfl⟩ : syracuseStep 3167849 = 2375887) B2375887
theorem B27056267 : Blo 1317977 27056267 := bstep (se 1 (by rfl) ⟨20292200, by rfl⟩ : syracuseStep 27056267 = 40584401) B40584401
theorem B555801173 : Blo 1317977 555801173 := bstep (se 8 (by rfl) ⟨3256647, by rfl⟩ : syracuseStep 555801173 = 6513295) B6513295
theorem B7510751 : Blo 1317977 7510751 := bstep (se 1 (by rfl) ⟨5633063, by rfl⟩ : syracuseStep 7510751 = 11266127) B11266127
theorem B5004449 : Blo 1317977 5004449 := bstep (se 2 (by rfl) ⟨1876668, by rfl⟩ : syracuseStep 5004449 = 3753337) B3753337
theorem B250199225 : Blo 1317977 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B48119285 : Blo 1317977 48119285 := bstep (se 5 (by rfl) ⟨2255591, by rfl⟩ : syracuseStep 48119285 = 4511183) B4511183
theorem B1318427 : Blo 1317977 1318427 := bstep (se 1 (by rfl) ⟨988820, by rfl⟩ : syracuseStep 1318427 = 1977641) B1977641
theorem B12852863 : Blo 1317977 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B3006089 : Blo 1317977 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B1318559 : Blo 1317977 1318559 := bstep (se 1 (by rfl) ⟨988919, by rfl⟩ : syracuseStep 1318559 = 1977839) B1977839
theorem B27066125 : Blo 1317977 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B2965499 : Blo 1317977 2965499 := bstep (se 1 (by rfl) ⟨2224124, by rfl⟩ : syracuseStep 2965499 = 4448249) B4448249
theorem B73129999 : Blo 1317977 73129999 := bstep (se 1 (by rfl) ⟨54847499, by rfl⟩ : syracuseStep 73129999 = 109694999) B109694999
theorem B1318911 : Blo 1317977 1318911 := bstep (se 1 (by rfl) ⟨989183, by rfl⟩ : syracuseStep 1318911 = 1978367) B1978367
theorem B7127315 : Blo 1317977 7127315 := bstep (se 1 (by rfl) ⟨5345486, by rfl⟩ : syracuseStep 7127315 = 10690973) B10690973
theorem B1319231 : Blo 1317977 1319231 := bstep (se 1 (by rfl) ⟨989423, by rfl⟩ : syracuseStep 1319231 = 1978847) B1978847
theorem B162497177 : Blo 1317977 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B10011599 : Blo 1317977 10011599 := bstep (se 1 (by rfl) ⟨7508699, by rfl⟩ : syracuseStep 10011599 = 15017399) B15017399
theorem B8447597 : Blo 1317977 8447597 := bstep (se 3 (by rfl) ⟨1583924, by rfl⟩ : syracuseStep 8447597 = 3167849) B3167849
theorem B370534115 : Blo 1317977 370534115 := bstep (se 1 (by rfl) ⟨277900586, by rfl⟩ : syracuseStep 370534115 = 555801173) B555801173
theorem B5007167 : Blo 1317977 5007167 := bstep (se 1 (by rfl) ⟨3755375, by rfl⟩ : syracuseStep 5007167 = 7510751) B7510751
theorem B3336299 : Blo 1317977 3336299 := bstep (se 1 (by rfl) ⟨2502224, by rfl⟩ : syracuseStep 3336299 = 5004449) B5004449
theorem B166799483 : Blo 1317977 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B3754259 : Blo 1317977 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B2673263 : Blo 1317977 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B1976999 : Blo 1317977 1976999 := bstep (se 1 (by rfl) ⟨1482749, by rfl⟩ : syracuseStep 1976999 = 2965499) B2965499
theorem B1978025 : Blo 1317977 1978025 := bstep (se 2 (by rfl) ⟨741759, by rfl⟩ : syracuseStep 1978025 = 1483519) B1483519
theorem B4452083 : Blo 1317977 4452083 := bstep (se 1 (by rfl) ⟨3339062, by rfl⟩ : syracuseStep 4452083 = 6678125) B6678125
theorem B175714433 : Blo 1317977 175714433 := bstep (se 2 (by rfl) ⟨65892912, by rfl⟩ : syracuseStep 175714433 = 131785825) B131785825
theorem B1978523 : Blo 1317977 1978523 := bstep (se 1 (by rfl) ⟨1483892, by rfl⟩ : syracuseStep 1978523 = 2967785) B2967785
theorem B2004059 : Blo 1317977 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B18044083 : Blo 1317977 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B6338063 : Blo 1317977 6338063 := bstep (se 1 (by rfl) ⟨4753547, by rfl⟩ : syracuseStep 6338063 = 9507095) B9507095
theorem B8451647 : Blo 1317977 8451647 := bstep (se 1 (by rfl) ⟨6338735, by rfl⟩ : syracuseStep 8451647 = 12677471) B12677471
theorem B6338159 : Blo 1317977 6338159 := bstep (se 1 (by rfl) ⟨4753619, by rfl⟩ : syracuseStep 6338159 = 9507239) B9507239
theorem B11261753 : Blo 1317977 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B2111663 : Blo 1317977 2111663 := bstep (se 1 (by rfl) ⟨1583747, by rfl⟩ : syracuseStep 2111663 = 3167495) B3167495
theorem B128318093 : Blo 1317977 128318093 := bstep (se 3 (by rfl) ⟨24059642, by rfl⟩ : syracuseStep 128318093 = 48119285) B48119285
theorem B18037511 : Blo 1317977 18037511 := bstep (se 1 (by rfl) ⟨13528133, by rfl⟩ : syracuseStep 18037511 = 27056267) B27056267
theorem B197745875 : Blo 1317977 197745875 := bstep (se 1 (by rfl) ⟨148309406, by rfl⟩ : syracuseStep 197745875 = 296618813) B296618813
theorem B7511251 : Blo 1317977 7511251 := bstep (se 1 (by rfl) ⟨5633438, by rfl⟩ : syracuseStep 7511251 = 11266877) B11266877
theorem B8568575 : Blo 1317977 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B25706321 : Blo 1317977 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B1318895 : Blo 1317977 1318895 := bstep (se 1 (by rfl) ⟨989171, by rfl⟩ : syracuseStep 1318895 = 1978343) B1978343
theorem B1319015 : Blo 1317977 1319015 := bstep (se 1 (by rfl) ⟨989261, by rfl⟩ : syracuseStep 1319015 = 1978523) B1978523
theorem B4751543 : Blo 1317977 4751543 := bstep (se 1 (by rfl) ⟨3563657, by rfl⟩ : syracuseStep 4751543 = 7127315) B7127315
theorem B108331451 : Blo 1317977 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B247022743 : Blo 1317977 247022743 := bstep (se 1 (by rfl) ⟨185267057, by rfl⟩ : syracuseStep 247022743 = 370534115) B370534115
theorem B111199655 : Blo 1317977 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B2968055 : Blo 1317977 2968055 := bstep (se 1 (by rfl) ⟨2226041, by rfl⟩ : syracuseStep 2968055 = 4452083) B4452083
theorem B5712383 : Blo 1317977 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B5344157 : Blo 1317977 5344157 := bstep (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) B2004059
theorem B5631731 : Blo 1317977 5631731 := bstep (se 1 (by rfl) ⟨4223798, by rfl⟩ : syracuseStep 5631731 = 8447597) B8447597
theorem B7507835 : Blo 1317977 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B3338111 : Blo 1317977 3338111 := bstep (se 1 (by rfl) ⟨2503583, by rfl⟩ : syracuseStep 3338111 = 5007167) B5007167
theorem B2224199 : Blo 1317977 2224199 := bstep (se 1 (by rfl) ⟨1668149, by rfl⟩ : syracuseStep 2224199 = 3336299) B3336299
theorem B2502839 : Blo 1317977 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B10015001 : Blo 1317977 10015001 := bstep (se 2 (by rfl) ⟨3755625, by rfl⟩ : syracuseStep 10015001 = 7511251) B7511251
theorem B1782175 : Blo 1317977 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B85545395 : Blo 1317977 85545395 := bstep (se 1 (by rfl) ⟨64159046, by rfl⟩ : syracuseStep 85545395 = 128318093) B128318093
theorem B131830583 : Blo 1317977 131830583 := bstep (se 1 (by rfl) ⟨98872937, by rfl⟩ : syracuseStep 131830583 = 197745875) B197745875
theorem B97506665 : Blo 1317977 97506665 := bstep (se 2 (by rfl) ⟨36564999, by rfl⟩ : syracuseStep 97506665 = 73129999) B73129999
theorem B117142955 : Blo 1317977 117142955 := bstep (se 1 (by rfl) ⟨87857216, by rfl⟩ : syracuseStep 117142955 = 175714433) B175714433
theorem B6674399 : Blo 1317977 6674399 := bstep (se 1 (by rfl) ⟨5005799, by rfl⟩ : syracuseStep 6674399 = 10011599) B10011599
theorem B4225375 : Blo 1317977 4225375 := bstep (se 1 (by rfl) ⟨3169031, by rfl⟩ : syracuseStep 4225375 = 6338063) B6338063
theorem B5634431 : Blo 1317977 5634431 := bstep (se 1 (by rfl) ⟨4225823, by rfl⟩ : syracuseStep 5634431 = 8451647) B8451647
theorem B4225439 : Blo 1317977 4225439 := bstep (se 1 (by rfl) ⟨3169079, by rfl⟩ : syracuseStep 4225439 = 6338159) B6338159
theorem B1407775 : Blo 1317977 1407775 := bstep (se 1 (by rfl) ⟨1055831, by rfl⟩ : syracuseStep 1407775 = 2111663) B2111663
theorem B24058777 : Blo 1317977 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B1317999 : Blo 1317977 1317999 := bstep (se 1 (by rfl) ⟨988499, by rfl⟩ : syracuseStep 1317999 = 1976999) B1976999
theorem B12025007 : Blo 1317977 12025007 := bstep (se 1 (by rfl) ⟨9018755, by rfl⟩ : syracuseStep 12025007 = 18037511) B18037511
theorem B1318683 : Blo 1317977 1318683 := bstep (se 1 (by rfl) ⟨989012, by rfl⟩ : syracuseStep 1318683 = 1978025) B1978025
theorem B17137547 : Blo 1317977 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B1482799 : Blo 1317977 1482799 := bstep (se 1 (by rfl) ⟨1112099, by rfl⟩ : syracuseStep 1482799 = 2224199) B2224199
theorem B6676667 : Blo 1317977 6676667 := bstep (se 1 (by rfl) ⟨5007500, by rfl⟩ : syracuseStep 6676667 = 10015001) B10015001
theorem B72220967 : Blo 1317977 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B2376233 : Blo 1317977 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B65004443 : Blo 1317977 65004443 := bstep (se 1 (by rfl) ⟨48753332, by rfl⟩ : syracuseStep 65004443 = 97506665) B97506665
theorem B78095303 : Blo 1317977 78095303 := bstep (se 1 (by rfl) ⟨58571477, by rfl⟩ : syracuseStep 78095303 = 117142955) B117142955
theorem B1877033 : Blo 1317977 1877033 := bstep (se 2 (by rfl) ⟨703887, by rfl⟩ : syracuseStep 1877033 = 1407775) B1407775
theorem B4449599 : Blo 1317977 4449599 := bstep (se 1 (by rfl) ⟨3337199, by rfl⟩ : syracuseStep 4449599 = 6674399) B6674399
theorem B3754487 : Blo 1317977 3754487 := bstep (se 1 (by rfl) ⟨2815865, by rfl⟩ : syracuseStep 3754487 = 5631731) B5631731
theorem B1406192885 : Blo 1317977 1406192885 := bstep (se 5 (by rfl) ⟨65915291, by rfl⟩ : syracuseStep 1406192885 = 131830583) B131830583
theorem B329363657 : Blo 1317977 329363657 := bstep (se 2 (by rfl) ⟨123511371, by rfl⟩ : syracuseStep 329363657 = 247022743) B247022743
theorem B3756287 : Blo 1317977 3756287 := bstep (se 1 (by rfl) ⟨2817215, by rfl⟩ : syracuseStep 3756287 = 5634431) B5634431
theorem B1978703 : Blo 1317977 1978703 := bstep (se 1 (by rfl) ⟨1484027, by rfl⟩ : syracuseStep 1978703 = 2968055) B2968055
theorem B8016671 : Blo 1317977 8016671 := bstep (se 1 (by rfl) ⟨6012503, by rfl⟩ : syracuseStep 8016671 = 12025007) B12025007
theorem B14251085 : Blo 1317977 14251085 := bstep (se 3 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 14251085 = 5344157) B5344157
theorem B2225407 : Blo 1317977 2225407 := bstep (se 1 (by rfl) ⟨1669055, by rfl⟩ : syracuseStep 2225407 = 3338111) B3338111
theorem B11425031 : Blo 1317977 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B3167695 : Blo 1317977 3167695 := bstep (se 1 (by rfl) ⟨2375771, by rfl⟩ : syracuseStep 3167695 = 4751543) B4751543
theorem B57030263 : Blo 1317977 57030263 := bstep (se 1 (by rfl) ⟨42772697, by rfl⟩ : syracuseStep 57030263 = 85545395) B85545395
theorem B5633833 : Blo 1317977 5633833 := bstep (se 2 (by rfl) ⟨2112687, by rfl⟩ : syracuseStep 5633833 = 4225375) B4225375
theorem B6674237 : Blo 1317977 6674237 := bstep (se 3 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 6674237 = 2502839) B2502839
theorem B296532413 : Blo 1317977 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B32078369 : Blo 1317977 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B2816959 : Blo 1317977 2816959 := bstep (se 1 (by rfl) ⟨2112719, by rfl⟩ : syracuseStep 2816959 = 4225439) B4225439
theorem B3808255 : Blo 1317977 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B5005223 : Blo 1317977 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B5005421 : Blo 1317977 5005421 := bstep (se 3 (by rfl) ⟨938516, by rfl⟩ : syracuseStep 5005421 = 1877033) B1877033
theorem B1319135 : Blo 1317977 1319135 := bstep (se 1 (by rfl) ⟨989351, by rfl⟩ : syracuseStep 1319135 = 1978703) B1978703
theorem B43336295 : Blo 1317977 43336295 := bstep (se 1 (by rfl) ⟨32502221, by rfl⟩ : syracuseStep 43336295 = 65004443) B65004443
theorem B2966399 : Blo 1317977 2966399 := bstep (se 1 (by rfl) ⟨2224799, by rfl⟩ : syracuseStep 2966399 = 4449599) B4449599
theorem B38020175 : Blo 1317977 38020175 := bstep (se 1 (by rfl) ⟨28515131, by rfl⟩ : syracuseStep 38020175 = 57030263) B57030263
theorem B4449491 : Blo 1317977 4449491 := bstep (se 1 (by rfl) ⟨3337118, by rfl⟩ : syracuseStep 4449491 = 6674237) B6674237
theorem B2967209 : Blo 1317977 2967209 := bstep (se 2 (by rfl) ⟨1112703, by rfl⟩ : syracuseStep 2967209 = 2225407) B2225407
theorem B937461923 : Blo 1317977 937461923 := bstep (se 1 (by rfl) ⟨703096442, by rfl⟩ : syracuseStep 937461923 = 1406192885) B1406192885
theorem B3336815 : Blo 1317977 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B1977065 : Blo 1317977 1977065 := bstep (se 2 (by rfl) ⟨741399, by rfl⟩ : syracuseStep 1977065 = 1482799) B1482799
theorem B4451111 : Blo 1317977 4451111 := bstep (se 1 (by rfl) ⟨3338333, by rfl⟩ : syracuseStep 4451111 = 6676667) B6676667
theorem B48147311 : Blo 1317977 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B1584155 : Blo 1317977 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B52063535 : Blo 1317977 52063535 := bstep (se 1 (by rfl) ⟨39047651, by rfl⟩ : syracuseStep 52063535 = 78095303) B78095303
theorem B3755945 : Blo 1317977 3755945 := bstep (se 2 (by rfl) ⟨1408479, by rfl⟩ : syracuseStep 3755945 = 2816959) B2816959
theorem B2502991 : Blo 1317977 2502991 := bstep (se 1 (by rfl) ⟨1877243, by rfl⟩ : syracuseStep 2502991 = 3754487) B3754487
theorem B21385579 : Blo 1317977 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B4223593 : Blo 1317977 4223593 := bstep (se 2 (by rfl) ⟨1583847, by rfl⟩ : syracuseStep 4223593 = 3167695) B3167695
theorem B21377789 : Blo 1317977 21377789 := bstep (se 3 (by rfl) ⟨4008335, by rfl⟩ : syracuseStep 21377789 = 8016671) B8016671
theorem B219575771 : Blo 1317977 219575771 := bstep (se 1 (by rfl) ⟨164681828, by rfl⟩ : syracuseStep 219575771 = 329363657) B329363657
theorem B2504191 : Blo 1317977 2504191 := bstep (se 1 (by rfl) ⟨1878143, by rfl⟩ : syracuseStep 2504191 = 3756287) B3756287
theorem B9500723 : Blo 1317977 9500723 := bstep (se 1 (by rfl) ⟨7125542, by rfl⟩ : syracuseStep 9500723 = 14251085) B14251085
theorem B7616687 : Blo 1317977 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B5077673 : Blo 1317977 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B197688275 : Blo 1317977 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B7511777 : Blo 1317977 7511777 := bstep (se 2 (by rfl) ⟨2816916, by rfl⟩ : syracuseStep 7511777 = 5633833) B5633833
theorem B25346783 : Blo 1317977 25346783 := bstep (se 1 (by rfl) ⟨19010087, by rfl⟩ : syracuseStep 25346783 = 38020175) B38020175
theorem B2966327 : Blo 1317977 2966327 := bstep (se 1 (by rfl) ⟨2224745, by rfl⟩ : syracuseStep 2966327 = 4449491) B4449491
theorem B146383847 : Blo 1317977 146383847 := bstep (se 1 (by rfl) ⟨109787885, by rfl⟩ : syracuseStep 146383847 = 219575771) B219575771
theorem B6333815 : Blo 1317977 6333815 := bstep (se 1 (by rfl) ⟨4750361, by rfl⟩ : syracuseStep 6333815 = 9500723) B9500723
theorem B3385115 : Blo 1317977 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B2967407 : Blo 1317977 2967407 := bstep (se 1 (by rfl) ⟨2225555, by rfl⟩ : syracuseStep 2967407 = 4451111) B4451111
theorem B32098207 : Blo 1317977 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B5007851 : Blo 1317977 5007851 := bstep (se 1 (by rfl) ⟨3755888, by rfl⟩ : syracuseStep 5007851 = 7511777) B7511777
theorem B3336947 : Blo 1317977 3336947 := bstep (se 1 (by rfl) ⟨2502710, by rfl⟩ : syracuseStep 3336947 = 5005421) B5005421
theorem B3337321 : Blo 1317977 3337321 := bstep (se 2 (by rfl) ⟨1251495, by rfl⟩ : syracuseStep 3337321 = 2502991) B2502991
theorem B20311165 : Blo 1317977 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B1977599 : Blo 1317977 1977599 := bstep (se 1 (by rfl) ⟨1483199, by rfl⟩ : syracuseStep 1977599 = 2966399) B2966399
theorem B5631457 : Blo 1317977 5631457 := bstep (se 2 (by rfl) ⟨2111796, by rfl⟩ : syracuseStep 5631457 = 4223593) B4223593
theorem B1978139 : Blo 1317977 1978139 := bstep (se 1 (by rfl) ⟨1483604, by rfl⟩ : syracuseStep 1978139 = 2967209) B2967209
theorem B2224543 : Blo 1317977 2224543 := bstep (se 1 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 2224543 = 3336815) B3336815
theorem B3338921 : Blo 1317977 3338921 := bstep (se 2 (by rfl) ⟨1252095, by rfl⟩ : syracuseStep 3338921 = 2504191) B2504191
theorem B2503963 : Blo 1317977 2503963 := bstep (se 1 (by rfl) ⟨1877972, by rfl⟩ : syracuseStep 2503963 = 3755945) B3755945
theorem B4224413 : Blo 1317977 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B28890863 : Blo 1317977 28890863 := bstep (se 1 (by rfl) ⟨21668147, by rfl⟩ : syracuseStep 28890863 = 43336295) B43336295
theorem B28514105 : Blo 1317977 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B14251859 : Blo 1317977 14251859 := bstep (se 1 (by rfl) ⟨10688894, by rfl⟩ : syracuseStep 14251859 = 21377789) B21377789
theorem B624974615 : Blo 1317977 624974615 := bstep (se 1 (by rfl) ⟨468730961, by rfl⟩ : syracuseStep 624974615 = 937461923) B937461923
theorem B1318043 : Blo 1317977 1318043 := bstep (se 1 (by rfl) ⟨988532, by rfl⟩ : syracuseStep 1318043 = 1977065) B1977065
theorem B131792183 : Blo 1317977 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B34709023 : Blo 1317977 34709023 := bstep (se 1 (by rfl) ⟨26031767, by rfl⟩ : syracuseStep 34709023 = 52063535) B52063535
theorem B2966057 : Blo 1317977 2966057 := bstep (se 2 (by rfl) ⟨1112271, by rfl⟩ : syracuseStep 2966057 = 2224543) B2224543
theorem B11265101 : Blo 1317977 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B19260575 : Blo 1317977 19260575 := bstep (se 1 (by rfl) ⟨14445431, by rfl⟩ : syracuseStep 19260575 = 28890863) B28890863
theorem B4449761 : Blo 1317977 4449761 := bstep (se 2 (by rfl) ⟨1668660, by rfl⟩ : syracuseStep 4449761 = 3337321) B3337321
theorem B46278697 : Blo 1317977 46278697 := bstep (se 2 (by rfl) ⟨17354511, by rfl⟩ : syracuseStep 46278697 = 34709023) B34709023
theorem B87861455 : Blo 1317977 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B42797609 : Blo 1317977 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B1977551 : Blo 1317977 1977551 := bstep (se 1 (by rfl) ⟨1483163, by rfl⟩ : syracuseStep 1977551 = 2966327) B2966327
theorem B4222543 : Blo 1317977 4222543 := bstep (se 1 (by rfl) ⟨3166907, by rfl⟩ : syracuseStep 4222543 = 6333815) B6333815
theorem B2256743 : Blo 1317977 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B19009403 : Blo 1317977 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B1978271 : Blo 1317977 1978271 := bstep (se 1 (by rfl) ⟨1483703, by rfl⟩ : syracuseStep 1978271 = 2967407) B2967407
theorem B3338567 : Blo 1317977 3338567 := bstep (se 1 (by rfl) ⟨2503925, by rfl⟩ : syracuseStep 3338567 = 5007851) B5007851
theorem B3338617 : Blo 1317977 3338617 := bstep (se 2 (by rfl) ⟨1251981, by rfl⟩ : syracuseStep 3338617 = 2503963) B2503963
theorem B2224631 : Blo 1317977 2224631 := bstep (se 1 (by rfl) ⟨1668473, by rfl⟩ : syracuseStep 2224631 = 3336947) B3336947
theorem B416649743 : Blo 1317977 416649743 := bstep (se 1 (by rfl) ⟨312487307, by rfl⟩ : syracuseStep 416649743 = 624974615) B624974615
theorem B7508609 : Blo 1317977 7508609 := bstep (se 2 (by rfl) ⟨2815728, by rfl⟩ : syracuseStep 7508609 = 5631457) B5631457
theorem B2225947 : Blo 1317977 2225947 := bstep (se 1 (by rfl) ⟨1669460, by rfl⟩ : syracuseStep 2225947 = 3338921) B3338921
theorem B16897855 : Blo 1317977 16897855 := bstep (se 1 (by rfl) ⟨12673391, by rfl⟩ : syracuseStep 16897855 = 25346783) B25346783
theorem B97589231 : Blo 1317977 97589231 := bstep (se 1 (by rfl) ⟨73191923, by rfl⟩ : syracuseStep 97589231 = 146383847) B146383847
theorem B9501239 : Blo 1317977 9501239 := bstep (se 1 (by rfl) ⟨7125929, by rfl⟩ : syracuseStep 9501239 = 14251859) B14251859
theorem B27081553 : Blo 1317977 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B1318399 : Blo 1317977 1318399 := bstep (se 1 (by rfl) ⟨988799, by rfl⟩ : syracuseStep 1318399 = 1977599) B1977599
theorem B1318759 : Blo 1317977 1318759 := bstep (se 1 (by rfl) ⟨989069, by rfl⟩ : syracuseStep 1318759 = 1978139) B1978139
theorem B1483087 : Blo 1317977 1483087 := bstep (se 1 (by rfl) ⟨1112315, by rfl⟩ : syracuseStep 1483087 = 2224631) B2224631
theorem B277766495 : Blo 1317977 277766495 := bstep (se 1 (by rfl) ⟨208324871, by rfl⟩ : syracuseStep 277766495 = 416649743) B416649743
theorem B5005739 : Blo 1317977 5005739 := bstep (se 1 (by rfl) ⟨3754304, by rfl⟩ : syracuseStep 5005739 = 7508609) B7508609
theorem B2966507 : Blo 1317977 2966507 := bstep (se 1 (by rfl) ⟨2224880, by rfl⟩ : syracuseStep 2966507 = 4449761) B4449761
theorem B58574303 : Blo 1317977 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B5630057 : Blo 1317977 5630057 := bstep (se 2 (by rfl) ⟨2111271, by rfl⟩ : syracuseStep 5630057 = 4222543) B4222543
theorem B2967929 : Blo 1317977 2967929 := bstep (se 2 (by rfl) ⟨1112973, by rfl⟩ : syracuseStep 2967929 = 2225947) B2225947
theorem B22530473 : Blo 1317977 22530473 := bstep (se 2 (by rfl) ⟨8448927, by rfl⟩ : syracuseStep 22530473 = 16897855) B16897855
theorem B61704929 : Blo 1317977 61704929 := bstep (se 2 (by rfl) ⟨23139348, by rfl⟩ : syracuseStep 61704929 = 46278697) B46278697
theorem B1977371 : Blo 1317977 1977371 := bstep (se 1 (by rfl) ⟨1483028, by rfl⟩ : syracuseStep 1977371 = 2966057) B2966057
theorem B4451489 : Blo 1317977 4451489 := bstep (se 2 (by rfl) ⟨1669308, by rfl⟩ : syracuseStep 4451489 = 3338617) B3338617
theorem B12840383 : Blo 1317977 12840383 := bstep (se 1 (by rfl) ⟨9630287, by rfl⟩ : syracuseStep 12840383 = 19260575) B19260575
theorem B1504495 : Blo 1317977 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B2225711 : Blo 1317977 2225711 := bstep (se 1 (by rfl) ⟨1669283, by rfl⟩ : syracuseStep 2225711 = 3338567) B3338567
theorem B7510067 : Blo 1317977 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B36108737 : Blo 1317977 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B65059487 : Blo 1317977 65059487 := bstep (se 1 (by rfl) ⟨48794615, by rfl⟩ : syracuseStep 65059487 = 97589231) B97589231
theorem B25336637 : Blo 1317977 25336637 := bstep (se 3 (by rfl) ⟨4750619, by rfl⟩ : syracuseStep 25336637 = 9501239) B9501239
theorem B28531739 : Blo 1317977 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B1318367 : Blo 1317977 1318367 := bstep (se 1 (by rfl) ⟨988775, by rfl⟩ : syracuseStep 1318367 = 1977551) B1977551
theorem B12672935 : Blo 1317977 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B1318847 : Blo 1317977 1318847 := bstep (se 1 (by rfl) ⟨989135, by rfl⟩ : syracuseStep 1318847 = 1978271) B1978271
theorem B1483807 : Blo 1317977 1483807 := bstep (se 1 (by rfl) ⟨1112855, by rfl⟩ : syracuseStep 1483807 = 2225711) B2225711
theorem B5006711 : Blo 1317977 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B3753371 : Blo 1317977 3753371 := bstep (se 1 (by rfl) ⟨2815028, by rfl⟩ : syracuseStep 3753371 = 5630057) B5630057
theorem B164546477 : Blo 1317977 164546477 := bstep (se 3 (by rfl) ⟨30852464, by rfl⟩ : syracuseStep 164546477 = 61704929) B61704929
theorem B2967659 : Blo 1317977 2967659 := bstep (se 1 (by rfl) ⟨2225744, by rfl⟩ : syracuseStep 2967659 = 4451489) B4451489
theorem B8448623 : Blo 1317977 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B3337159 : Blo 1317977 3337159 := bstep (se 1 (by rfl) ⟨2502869, by rfl⟩ : syracuseStep 3337159 = 5005739) B5005739
theorem B1977449 : Blo 1317977 1977449 := bstep (se 2 (by rfl) ⟨741543, by rfl⟩ : syracuseStep 1977449 = 1483087) B1483087
theorem B1977671 : Blo 1317977 1977671 := bstep (se 1 (by rfl) ⟨1483253, by rfl⟩ : syracuseStep 1977671 = 2966507) B2966507
theorem B1978619 : Blo 1317977 1978619 := bstep (se 1 (by rfl) ⟨1483964, by rfl⟩ : syracuseStep 1978619 = 2967929) B2967929
theorem B15020315 : Blo 1317977 15020315 := bstep (se 1 (by rfl) ⟨11265236, by rfl⟩ : syracuseStep 15020315 = 22530473) B22530473
theorem B24072491 : Blo 1317977 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B43372991 : Blo 1317977 43372991 := bstep (se 1 (by rfl) ⟨32529743, by rfl⟩ : syracuseStep 43372991 = 65059487) B65059487
theorem B185177663 : Blo 1317977 185177663 := bstep (se 1 (by rfl) ⟨138883247, by rfl⟩ : syracuseStep 185177663 = 277766495) B277766495
theorem B39049535 : Blo 1317977 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B2005993 : Blo 1317977 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B16891091 : Blo 1317977 16891091 := bstep (se 1 (by rfl) ⟨12668318, by rfl⟩ : syracuseStep 16891091 = 25336637) B25336637
theorem B1318247 : Blo 1317977 1318247 := bstep (se 1 (by rfl) ⟨988685, by rfl⟩ : syracuseStep 1318247 = 1977371) B1977371
theorem B19021159 : Blo 1317977 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B8560255 : Blo 1317977 8560255 := bstep (se 1 (by rfl) ⟨6420191, by rfl⟩ : syracuseStep 8560255 = 12840383) B12840383
theorem B1319079 : Blo 1317977 1319079 := bstep (se 1 (by rfl) ⟨989309, by rfl⟩ : syracuseStep 1319079 = 1978619) B1978619
theorem B16048327 : Blo 1317977 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B4449545 : Blo 1317977 4449545 := bstep (se 2 (by rfl) ⟨1668579, by rfl⟩ : syracuseStep 4449545 = 3337159) B3337159
theorem B11413673 : Blo 1317977 11413673 := bstep (se 2 (by rfl) ⟨4280127, by rfl⟩ : syracuseStep 11413673 = 8560255) B8560255
theorem B10013543 : Blo 1317977 10013543 := bstep (se 1 (by rfl) ⟨7510157, by rfl⟩ : syracuseStep 10013543 = 15020315) B15020315
theorem B3337807 : Blo 1317977 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B2502247 : Blo 1317977 2502247 := bstep (se 1 (by rfl) ⟨1876685, by rfl⟩ : syracuseStep 2502247 = 3753371) B3753371
theorem B2674657 : Blo 1317977 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B1978409 : Blo 1317977 1978409 := bstep (se 2 (by rfl) ⟨741903, by rfl⟩ : syracuseStep 1978409 = 1483807) B1483807
theorem B1978439 : Blo 1317977 1978439 := bstep (se 1 (by rfl) ⟨1483829, by rfl⟩ : syracuseStep 1978439 = 2967659) B2967659
theorem B5632415 : Blo 1317977 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B11260727 : Blo 1317977 11260727 := bstep (se 1 (by rfl) ⟨8445545, by rfl⟩ : syracuseStep 11260727 = 16891091) B16891091
theorem B28915327 : Blo 1317977 28915327 := bstep (se 1 (by rfl) ⟨21686495, by rfl⟩ : syracuseStep 28915327 = 43372991) B43372991
theorem B123451775 : Blo 1317977 123451775 := bstep (se 1 (by rfl) ⟨92588831, by rfl⟩ : syracuseStep 123451775 = 185177663) B185177663
theorem B109697651 : Blo 1317977 109697651 := bstep (se 1 (by rfl) ⟨82273238, by rfl⟩ : syracuseStep 109697651 = 164546477) B164546477
theorem B26033023 : Blo 1317977 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B25361545 : Blo 1317977 25361545 := bstep (se 2 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 25361545 = 19021159) B19021159
theorem B1318299 : Blo 1317977 1318299 := bstep (se 1 (by rfl) ⟨988724, by rfl⟩ : syracuseStep 1318299 = 1977449) B1977449
theorem B1318447 : Blo 1317977 1318447 := bstep (se 1 (by rfl) ⟨988835, by rfl⟩ : syracuseStep 1318447 = 1977671) B1977671
theorem B1318939 : Blo 1317977 1318939 := bstep (se 1 (by rfl) ⟨989204, by rfl⟩ : syracuseStep 1318939 = 1978409) B1978409
theorem B1318959 : Blo 1317977 1318959 := bstep (se 1 (by rfl) ⟨989219, by rfl⟩ : syracuseStep 1318959 = 1978439) B1978439
theorem B21397769 : Blo 1317977 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B2966363 : Blo 1317977 2966363 := bstep (se 1 (by rfl) ⟨2224772, by rfl⟩ : syracuseStep 2966363 = 4449545) B4449545
theorem B34710697 : Blo 1317977 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B73131767 : Blo 1317977 73131767 := bstep (se 1 (by rfl) ⟨54848825, by rfl⟩ : syracuseStep 73131767 = 109697651) B109697651
theorem B4450409 : Blo 1317977 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B3336329 : Blo 1317977 3336329 := bstep (se 2 (by rfl) ⟨1251123, by rfl⟩ : syracuseStep 3336329 = 2502247) B2502247
theorem B38553769 : Blo 1317977 38553769 := bstep (se 2 (by rfl) ⟨14457663, by rfl⟩ : syracuseStep 38553769 = 28915327) B28915327
theorem B3566209 : Blo 1317977 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B3754943 : Blo 1317977 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B7507151 : Blo 1317977 7507151 := bstep (se 1 (by rfl) ⟨5630363, by rfl⟩ : syracuseStep 7507151 = 11260727) B11260727
theorem B82301183 : Blo 1317977 82301183 := bstep (se 1 (by rfl) ⟨61725887, by rfl⟩ : syracuseStep 82301183 = 123451775) B123451775
theorem B7609115 : Blo 1317977 7609115 := bstep (se 1 (by rfl) ⟨5706836, by rfl⟩ : syracuseStep 7609115 = 11413673) B11413673
theorem B33815393 : Blo 1317977 33815393 := bstep (se 2 (by rfl) ⟨12680772, by rfl⟩ : syracuseStep 33815393 = 25361545) B25361545
theorem B6675695 : Blo 1317977 6675695 := bstep (se 1 (by rfl) ⟨5006771, by rfl⟩ : syracuseStep 6675695 = 10013543) B10013543
theorem B51405025 : Blo 1317977 51405025 := bstep (se 2 (by rfl) ⟨19276884, by rfl⟩ : syracuseStep 51405025 = 38553769) B38553769
theorem B2966939 : Blo 1317977 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B5072743 : Blo 1317977 5072743 := bstep (se 1 (by rfl) ⟨3804557, by rfl⟩ : syracuseStep 5072743 = 7609115) B7609115
theorem B4450463 : Blo 1317977 4450463 := bstep (se 1 (by rfl) ⟨3337847, by rfl⟩ : syracuseStep 4450463 = 6675695) B6675695
theorem B14265179 : Blo 1317977 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B1977575 : Blo 1317977 1977575 := bstep (se 1 (by rfl) ⟨1483181, by rfl⟩ : syracuseStep 1977575 = 2966363) B2966363
theorem B4754945 : Blo 1317977 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B48754511 : Blo 1317977 48754511 := bstep (se 1 (by rfl) ⟨36565883, by rfl⟩ : syracuseStep 48754511 = 73131767) B73131767
theorem B2224219 : Blo 1317977 2224219 := bstep (se 1 (by rfl) ⟨1668164, by rfl⟩ : syracuseStep 2224219 = 3336329) B3336329
theorem B46280929 : Blo 1317977 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B2503295 : Blo 1317977 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B54867455 : Blo 1317977 54867455 := bstep (se 1 (by rfl) ⟨41150591, by rfl⟩ : syracuseStep 54867455 = 82301183) B82301183
theorem B22543595 : Blo 1317977 22543595 := bstep (se 1 (by rfl) ⟨16907696, by rfl⟩ : syracuseStep 22543595 = 33815393) B33815393
theorem B5004767 : Blo 1317977 5004767 := bstep (se 1 (by rfl) ⟨3753575, by rfl⟩ : syracuseStep 5004767 = 7507151) B7507151
theorem B2965625 : Blo 1317977 2965625 := bstep (se 2 (by rfl) ⟨1112109, by rfl⟩ : syracuseStep 2965625 = 2224219) B2224219
theorem B36578303 : Blo 1317977 36578303 := bstep (se 1 (by rfl) ⟨27433727, by rfl⟩ : syracuseStep 36578303 = 54867455) B54867455
theorem B2966975 : Blo 1317977 2966975 := bstep (se 1 (by rfl) ⟨2225231, by rfl⟩ : syracuseStep 2966975 = 4450463) B4450463
theorem B3336511 : Blo 1317977 3336511 := bstep (se 1 (by rfl) ⟨2502383, by rfl⟩ : syracuseStep 3336511 = 5004767) B5004767
theorem B1977959 : Blo 1317977 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B15029063 : Blo 1317977 15029063 := bstep (se 1 (by rfl) ⟨11271797, by rfl⟩ : syracuseStep 15029063 = 22543595) B22543595
theorem B6763657 : Blo 1317977 6763657 := bstep (se 2 (by rfl) ⟨2536371, by rfl⟩ : syracuseStep 6763657 = 5072743) B5072743
theorem B32503007 : Blo 1317977 32503007 := bstep (se 1 (by rfl) ⟨24377255, by rfl⟩ : syracuseStep 32503007 = 48754511) B48754511
theorem B61707905 : Blo 1317977 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B68540033 : Blo 1317977 68540033 := bstep (se 2 (by rfl) ⟨25702512, by rfl⟩ : syracuseStep 68540033 = 51405025) B51405025
theorem B1668863 : Blo 1317977 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B9510119 : Blo 1317977 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B1318383 : Blo 1317977 1318383 := bstep (se 1 (by rfl) ⟨988787, by rfl⟩ : syracuseStep 1318383 = 1977575) B1977575
theorem B3169963 : Blo 1317977 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B4448681 : Blo 1317977 4448681 := bstep (se 2 (by rfl) ⟨1668255, by rfl⟩ : syracuseStep 4448681 = 3336511) B3336511
theorem B10019375 : Blo 1317977 10019375 := bstep (se 1 (by rfl) ⟨7514531, by rfl⟩ : syracuseStep 10019375 = 15029063) B15029063
theorem B21668671 : Blo 1317977 21668671 := bstep (se 1 (by rfl) ⟨16251503, by rfl⟩ : syracuseStep 21668671 = 32503007) B32503007
theorem B182773421 : Blo 1317977 182773421 := bstep (se 3 (by rfl) ⟨34270016, by rfl⟩ : syracuseStep 182773421 = 68540033) B68540033
theorem B4450301 : Blo 1317977 4450301 := bstep (se 3 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 4450301 = 1668863) B1668863
theorem B1977083 : Blo 1317977 1977083 := bstep (se 1 (by rfl) ⟨1482812, by rfl⟩ : syracuseStep 1977083 = 2965625) B2965625
theorem B1977983 : Blo 1317977 1977983 := bstep (se 1 (by rfl) ⟨1483487, by rfl⟩ : syracuseStep 1977983 = 2966975) B2966975
theorem B24385535 : Blo 1317977 24385535 := bstep (se 1 (by rfl) ⟨18289151, by rfl⟩ : syracuseStep 24385535 = 36578303) B36578303
theorem B41138603 : Blo 1317977 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B9018209 : Blo 1317977 9018209 := bstep (se 2 (by rfl) ⟨3381828, by rfl⟩ : syracuseStep 9018209 = 6763657) B6763657
theorem B6340079 : Blo 1317977 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B4226617 : Blo 1317977 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B1318639 : Blo 1317977 1318639 := bstep (se 1 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 1318639 = 1977959) B1977959
theorem B2965787 : Blo 1317977 2965787 := bstep (se 1 (by rfl) ⟨2224340, by rfl⟩ : syracuseStep 2965787 = 4448681) B4448681
theorem B121848947 : Blo 1317977 121848947 := bstep (se 1 (by rfl) ⟨91386710, by rfl⟩ : syracuseStep 121848947 = 182773421) B182773421
theorem B2966867 : Blo 1317977 2966867 := bstep (se 1 (by rfl) ⟨2225150, by rfl⟩ : syracuseStep 2966867 = 4450301) B4450301
theorem B6679583 : Blo 1317977 6679583 := bstep (se 1 (by rfl) ⟨5009687, by rfl⟩ : syracuseStep 6679583 = 10019375) B10019375
theorem B16257023 : Blo 1317977 16257023 := bstep (se 1 (by rfl) ⟨12192767, by rfl⟩ : syracuseStep 16257023 = 24385535) B24385535
theorem B28891561 : Blo 1317977 28891561 := bstep (se 2 (by rfl) ⟨10834335, by rfl⟩ : syracuseStep 28891561 = 21668671) B21668671
theorem B16906877 : Blo 1317977 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B27425735 : Blo 1317977 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B1318055 : Blo 1317977 1318055 := bstep (se 1 (by rfl) ⟨988541, by rfl⟩ : syracuseStep 1318055 = 1977083) B1977083
theorem B6012139 : Blo 1317977 6012139 := bstep (se 1 (by rfl) ⟨4509104, by rfl⟩ : syracuseStep 6012139 = 9018209) B9018209
theorem B5635489 : Blo 1317977 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B1318655 : Blo 1317977 1318655 := bstep (se 1 (by rfl) ⟨988991, by rfl⟩ : syracuseStep 1318655 = 1977983) B1977983
theorem B81232631 : Blo 1317977 81232631 := bstep (se 1 (by rfl) ⟨60924473, by rfl⟩ : syracuseStep 81232631 = 121848947) B121848947
theorem B7513985 : Blo 1317977 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B1977191 : Blo 1317977 1977191 := bstep (se 1 (by rfl) ⟨1482893, by rfl⟩ : syracuseStep 1977191 = 2965787) B2965787
theorem B38522081 : Blo 1317977 38522081 := bstep (se 2 (by rfl) ⟨14445780, by rfl⟩ : syracuseStep 38522081 = 28891561) B28891561
theorem B1977911 : Blo 1317977 1977911 := bstep (se 1 (by rfl) ⟨1483433, by rfl⟩ : syracuseStep 1977911 = 2966867) B2966867
theorem B8016185 : Blo 1317977 8016185 := bstep (se 2 (by rfl) ⟨3006069, by rfl⟩ : syracuseStep 8016185 = 6012139) B6012139
theorem B4453055 : Blo 1317977 4453055 := bstep (se 1 (by rfl) ⟨3339791, by rfl⟩ : syracuseStep 4453055 = 6679583) B6679583
theorem B11271251 : Blo 1317977 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B18283823 : Blo 1317977 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B10838015 : Blo 1317977 10838015 := bstep (se 1 (by rfl) ⟨8128511, by rfl⟩ : syracuseStep 10838015 = 16257023) B16257023
theorem B7514167 : Blo 1317977 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B5344123 : Blo 1317977 5344123 := bstep (se 1 (by rfl) ⟨4008092, by rfl⟩ : syracuseStep 5344123 = 8016185) B8016185
theorem B2968703 : Blo 1317977 2968703 := bstep (se 1 (by rfl) ⟨2226527, by rfl⟩ : syracuseStep 2968703 = 4453055) B4453055
theorem B5009323 : Blo 1317977 5009323 := bstep (se 1 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 5009323 = 7513985) B7513985
theorem B7225343 : Blo 1317977 7225343 := bstep (se 1 (by rfl) ⟨5419007, by rfl⟩ : syracuseStep 7225343 = 10838015) B10838015
theorem B54155087 : Blo 1317977 54155087 := bstep (se 1 (by rfl) ⟨40616315, by rfl⟩ : syracuseStep 54155087 = 81232631) B81232631
theorem B1318127 : Blo 1317977 1318127 := bstep (se 1 (by rfl) ⟨988595, by rfl⟩ : syracuseStep 1318127 = 1977191) B1977191
theorem B25681387 : Blo 1317977 25681387 := bstep (se 1 (by rfl) ⟨19261040, by rfl⟩ : syracuseStep 25681387 = 38522081) B38522081
theorem B12189215 : Blo 1317977 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B1318607 : Blo 1317977 1318607 := bstep (se 1 (by rfl) ⟨988955, by rfl⟩ : syracuseStep 1318607 = 1977911) B1977911
theorem B10018889 : Blo 1317977 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B36103391 : Blo 1317977 36103391 := bstep (se 1 (by rfl) ⟨27077543, by rfl⟩ : syracuseStep 36103391 = 54155087) B54155087
theorem B6679097 : Blo 1317977 6679097 := bstep (se 2 (by rfl) ⟨2504661, by rfl⟩ : syracuseStep 6679097 = 5009323) B5009323
theorem B1979135 : Blo 1317977 1979135 := bstep (se 1 (by rfl) ⟨1484351, by rfl⟩ : syracuseStep 1979135 = 2968703) B2968703
theorem B7125497 : Blo 1317977 7125497 := bstep (se 2 (by rfl) ⟨2672061, by rfl⟩ : syracuseStep 7125497 = 5344123) B5344123
theorem B34241849 : Blo 1317977 34241849 := bstep (se 2 (by rfl) ⟨12840693, by rfl⟩ : syracuseStep 34241849 = 25681387) B25681387
theorem B8126143 : Blo 1317977 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B77070325 : Blo 1317977 77070325 := bstep (se 5 (by rfl) ⟨3612671, by rfl⟩ : syracuseStep 77070325 = 7225343) B7225343
theorem B1319423 : Blo 1317977 1319423 := bstep (se 1 (by rfl) ⟨989567, by rfl⟩ : syracuseStep 1319423 = 1979135) B1979135
theorem B24068927 : Blo 1317977 24068927 := bstep (se 1 (by rfl) ⟨18051695, by rfl⟩ : syracuseStep 24068927 = 36103391) B36103391
theorem B6679259 : Blo 1317977 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B43339429 : Blo 1317977 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B4452731 : Blo 1317977 4452731 := bstep (se 1 (by rfl) ⟨3339548, by rfl⟩ : syracuseStep 4452731 = 6679097) B6679097
theorem B22827899 : Blo 1317977 22827899 := bstep (se 1 (by rfl) ⟨17120924, by rfl⟩ : syracuseStep 22827899 = 34241849) B34241849
theorem B4750331 : Blo 1317977 4750331 := bstep (se 1 (by rfl) ⟨3562748, by rfl⟩ : syracuseStep 4750331 = 7125497) B7125497
theorem B102760433 : Blo 1317977 102760433 := bstep (se 2 (by rfl) ⟨38535162, by rfl⟩ : syracuseStep 102760433 = 77070325) B77070325
theorem B12667549 : Blo 1317977 12667549 := bstep (se 3 (by rfl) ⟨2375165, by rfl⟩ : syracuseStep 12667549 = 4750331) B4750331
theorem B2968487 : Blo 1317977 2968487 := bstep (se 1 (by rfl) ⟨2226365, by rfl⟩ : syracuseStep 2968487 = 4452731) B4452731
theorem B4452839 : Blo 1317977 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B68506955 : Blo 1317977 68506955 := bstep (se 1 (by rfl) ⟨51380216, by rfl⟩ : syracuseStep 68506955 = 102760433) B102760433
theorem B16045951 : Blo 1317977 16045951 := bstep (se 1 (by rfl) ⟨12034463, by rfl⟩ : syracuseStep 16045951 = 24068927) B24068927
theorem B15218599 : Blo 1317977 15218599 := bstep (se 1 (by rfl) ⟨11413949, by rfl⟩ : syracuseStep 15218599 = 22827899) B22827899
theorem B57785905 : Blo 1317977 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B308191493 : Blo 1317977 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B45671303 : Blo 1317977 45671303 := bstep (se 1 (by rfl) ⟨34253477, by rfl⟩ : syracuseStep 45671303 = 68506955) B68506955
theorem B2968559 : Blo 1317977 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B1978991 : Blo 1317977 1978991 := bstep (se 1 (by rfl) ⟨1484243, by rfl⟩ : syracuseStep 1978991 = 2968487) B2968487
theorem B21394601 : Blo 1317977 21394601 := bstep (se 2 (by rfl) ⟨8022975, by rfl⟩ : syracuseStep 21394601 = 16045951) B16045951
theorem B16890065 : Blo 1317977 16890065 := bstep (se 2 (by rfl) ⟨6333774, by rfl⟩ : syracuseStep 16890065 = 12667549) B12667549
theorem B20291465 : Blo 1317977 20291465 := bstep (se 2 (by rfl) ⟨7609299, by rfl⟩ : syracuseStep 20291465 = 15218599) B15218599
theorem B1319327 : Blo 1317977 1319327 := bstep (se 1 (by rfl) ⟨989495, by rfl⟩ : syracuseStep 1319327 = 1978991) B1978991
theorem B14263067 : Blo 1317977 14263067 := bstep (se 1 (by rfl) ⟨10697300, by rfl⟩ : syracuseStep 14263067 = 21394601) B21394601
theorem B13527643 : Blo 1317977 13527643 := bstep (se 1 (by rfl) ⟨10145732, by rfl⟩ : syracuseStep 13527643 = 20291465) B20291465
theorem B11260043 : Blo 1317977 11260043 := bstep (se 1 (by rfl) ⟨8445032, by rfl⟩ : syracuseStep 11260043 = 16890065) B16890065
theorem B1979039 : Blo 1317977 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B205460995 : Blo 1317977 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B30447535 : Blo 1317977 30447535 := bstep (se 1 (by rfl) ⟨22835651, by rfl⟩ : syracuseStep 30447535 = 45671303) B45671303
theorem B1319359 : Blo 1317977 1319359 := bstep (se 1 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 1319359 = 1979039) B1979039
theorem B7506695 : Blo 1317977 7506695 := bstep (se 1 (by rfl) ⟨5630021, by rfl⟩ : syracuseStep 7506695 = 11260043) B11260043
theorem B40596713 : Blo 1317977 40596713 := bstep (se 2 (by rfl) ⟨15223767, by rfl⟩ : syracuseStep 40596713 = 30447535) B30447535
theorem B9508711 : Blo 1317977 9508711 := bstep (se 1 (by rfl) ⟨7131533, by rfl⟩ : syracuseStep 9508711 = 14263067) B14263067
theorem B18036857 : Blo 1317977 18036857 := bstep (se 2 (by rfl) ⟨6763821, by rfl⟩ : syracuseStep 18036857 = 13527643) B13527643
theorem B273947993 : Blo 1317977 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B12678281 : Blo 1317977 12678281 := bstep (se 2 (by rfl) ⟨4754355, by rfl⟩ : syracuseStep 12678281 = 9508711) B9508711
theorem B27064475 : Blo 1317977 27064475 := bstep (se 1 (by rfl) ⟨20298356, by rfl⟩ : syracuseStep 27064475 = 40596713) B40596713
theorem B12024571 : Blo 1317977 12024571 := bstep (se 1 (by rfl) ⟨9018428, by rfl⟩ : syracuseStep 12024571 = 18036857) B18036857
theorem B5004463 : Blo 1317977 5004463 := bstep (se 1 (by rfl) ⟨3753347, by rfl⟩ : syracuseStep 5004463 = 7506695) B7506695
theorem B182631995 : Blo 1317977 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B16032761 : Blo 1317977 16032761 := bstep (se 2 (by rfl) ⟨6012285, by rfl⟩ : syracuseStep 16032761 = 12024571) B12024571
theorem B18042983 : Blo 1317977 18042983 := bstep (se 1 (by rfl) ⟨13532237, by rfl⟩ : syracuseStep 18042983 = 27064475) B27064475
theorem B6672617 : Blo 1317977 6672617 := bstep (se 2 (by rfl) ⟨2502231, by rfl⟩ : syracuseStep 6672617 = 5004463) B5004463
theorem B121754663 : Blo 1317977 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B8452187 : Blo 1317977 8452187 := bstep (se 1 (by rfl) ⟨6339140, by rfl⟩ : syracuseStep 8452187 = 12678281) B12678281
theorem B4448411 : Blo 1317977 4448411 := bstep (se 1 (by rfl) ⟨3336308, by rfl⟩ : syracuseStep 4448411 = 6672617) B6672617
theorem B12028655 : Blo 1317977 12028655 := bstep (se 1 (by rfl) ⟨9021491, by rfl⟩ : syracuseStep 12028655 = 18042983) B18042983
theorem B81169775 : Blo 1317977 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B10688507 : Blo 1317977 10688507 := bstep (se 1 (by rfl) ⟨8016380, by rfl⟩ : syracuseStep 10688507 = 16032761) B16032761
theorem B5634791 : Blo 1317977 5634791 := bstep (se 1 (by rfl) ⟨4226093, by rfl⟩ : syracuseStep 5634791 = 8452187) B8452187
theorem B2965607 : Blo 1317977 2965607 := bstep (se 1 (by rfl) ⟨2224205, by rfl⟩ : syracuseStep 2965607 = 4448411) B4448411
theorem B3756527 : Blo 1317977 3756527 := bstep (se 1 (by rfl) ⟨2817395, by rfl⟩ : syracuseStep 3756527 = 5634791) B5634791
theorem B54113183 : Blo 1317977 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B7125671 : Blo 1317977 7125671 := bstep (se 1 (by rfl) ⟨5344253, by rfl⟩ : syracuseStep 7125671 = 10688507) B10688507
theorem B8019103 : Blo 1317977 8019103 := bstep (se 1 (by rfl) ⟨6014327, by rfl⟩ : syracuseStep 8019103 = 12028655) B12028655
theorem B10692137 : Blo 1317977 10692137 := bstep (se 2 (by rfl) ⟨4009551, by rfl⟩ : syracuseStep 10692137 = 8019103) B8019103
theorem B1977071 : Blo 1317977 1977071 := bstep (se 1 (by rfl) ⟨1482803, by rfl⟩ : syracuseStep 1977071 = 2965607) B2965607
theorem B2504351 : Blo 1317977 2504351 := bstep (se 1 (by rfl) ⟨1878263, by rfl⟩ : syracuseStep 2504351 = 3756527) B3756527
theorem B36075455 : Blo 1317977 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B4750447 : Blo 1317977 4750447 := bstep (se 1 (by rfl) ⟨3562835, by rfl⟩ : syracuseStep 4750447 = 7125671) B7125671
theorem B7128091 : Blo 1317977 7128091 := bstep (se 1 (by rfl) ⟨5346068, by rfl⟩ : syracuseStep 7128091 = 10692137) B10692137
theorem B6333929 : Blo 1317977 6333929 := bstep (se 2 (by rfl) ⟨2375223, by rfl⟩ : syracuseStep 6333929 = 4750447) B4750447
theorem B1669567 : Blo 1317977 1669567 := bstep (se 1 (by rfl) ⟨1252175, by rfl⟩ : syracuseStep 1669567 = 2504351) B2504351
theorem B24050303 : Blo 1317977 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B1318047 : Blo 1317977 1318047 := bstep (se 1 (by rfl) ⟨988535, by rfl⟩ : syracuseStep 1318047 = 1977071) B1977071
theorem B16033535 : Blo 1317977 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B4222619 : Blo 1317977 4222619 := bstep (se 1 (by rfl) ⟨3166964, by rfl⟩ : syracuseStep 4222619 = 6333929) B6333929
theorem B38016485 : Blo 1317977 38016485 := bstep (se 4 (by rfl) ⟨3564045, by rfl⟩ : syracuseStep 38016485 = 7128091) B7128091
theorem B2226089 : Blo 1317977 2226089 := bstep (se 2 (by rfl) ⟨834783, by rfl⟩ : syracuseStep 2226089 = 1669567) B1669567
theorem B1484059 : Blo 1317977 1484059 := bstep (se 1 (by rfl) ⟨1113044, by rfl⟩ : syracuseStep 1484059 = 2226089) B2226089
theorem B2815079 : Blo 1317977 2815079 := bstep (se 1 (by rfl) ⟨2111309, by rfl⟩ : syracuseStep 2815079 = 4222619) B4222619
theorem B25344323 : Blo 1317977 25344323 := bstep (se 1 (by rfl) ⟨19008242, by rfl⟩ : syracuseStep 25344323 = 38016485) B38016485
theorem B10689023 : Blo 1317977 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B7506877 : Blo 1317977 7506877 := bstep (se 3 (by rfl) ⟨1407539, by rfl⟩ : syracuseStep 7506877 = 2815079) B2815079
theorem B28504061 : Blo 1317977 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B16896215 : Blo 1317977 16896215 := bstep (se 1 (by rfl) ⟨12672161, by rfl⟩ : syracuseStep 16896215 = 25344323) B25344323
theorem B1978745 : Blo 1317977 1978745 := bstep (se 2 (by rfl) ⟨742029, by rfl⟩ : syracuseStep 1978745 = 1484059) B1484059
theorem B11264143 : Blo 1317977 11264143 := bstep (se 1 (by rfl) ⟨8448107, by rfl⟩ : syracuseStep 11264143 = 16896215) B16896215
theorem B1319163 : Blo 1317977 1319163 := bstep (se 1 (by rfl) ⟨989372, by rfl⟩ : syracuseStep 1319163 = 1978745) B1978745
theorem B19002707 : Blo 1317977 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B10009169 : Blo 1317977 10009169 := bstep (se 2 (by rfl) ⟨3753438, by rfl⟩ : syracuseStep 10009169 = 7506877) B7506877
theorem B15018857 : Blo 1317977 15018857 := bstep (se 2 (by rfl) ⟨5632071, by rfl⟩ : syracuseStep 15018857 = 11264143) B11264143
theorem B12668471 : Blo 1317977 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B6672779 : Blo 1317977 6672779 := bstep (se 1 (by rfl) ⟨5004584, by rfl⟩ : syracuseStep 6672779 = 10009169) B10009169
theorem B4448519 : Blo 1317977 4448519 := bstep (se 1 (by rfl) ⟨3336389, by rfl⟩ : syracuseStep 4448519 = 6672779) B6672779
theorem B10012571 : Blo 1317977 10012571 := bstep (se 1 (by rfl) ⟨7509428, by rfl⟩ : syracuseStep 10012571 = 15018857) B15018857
theorem B8445647 : Blo 1317977 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B2965679 : Blo 1317977 2965679 := bstep (se 1 (by rfl) ⟨2224259, by rfl⟩ : syracuseStep 2965679 = 4448519) B4448519
theorem B22521725 : Blo 1317977 22521725 := bstep (se 3 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 22521725 = 8445647) B8445647
theorem B6675047 : Blo 1317977 6675047 := bstep (se 1 (by rfl) ⟨5006285, by rfl⟩ : syracuseStep 6675047 = 10012571) B10012571
theorem B4450031 : Blo 1317977 4450031 := bstep (se 1 (by rfl) ⟨3337523, by rfl⟩ : syracuseStep 4450031 = 6675047) B6675047
theorem B1977119 : Blo 1317977 1977119 := bstep (se 1 (by rfl) ⟨1482839, by rfl⟩ : syracuseStep 1977119 = 2965679) B2965679
theorem B15014483 : Blo 1317977 15014483 := bstep (se 1 (by rfl) ⟨11260862, by rfl⟩ : syracuseStep 15014483 = 22521725) B22521725
theorem B2966687 : Blo 1317977 2966687 := bstep (se 1 (by rfl) ⟨2225015, by rfl⟩ : syracuseStep 2966687 = 4450031) B4450031
theorem B10009655 : Blo 1317977 10009655 := bstep (se 1 (by rfl) ⟨7507241, by rfl⟩ : syracuseStep 10009655 = 15014483) B15014483
theorem B1318079 : Blo 1317977 1318079 := bstep (se 1 (by rfl) ⟨988559, by rfl⟩ : syracuseStep 1318079 = 1977119) B1977119
theorem B1977791 : Blo 1317977 1977791 := bstep (se 1 (by rfl) ⟨1483343, by rfl⟩ : syracuseStep 1977791 = 2966687) B2966687
theorem B6673103 : Blo 1317977 6673103 := bstep (se 1 (by rfl) ⟨5004827, by rfl⟩ : syracuseStep 6673103 = 10009655) B10009655
theorem B4448735 : Blo 1317977 4448735 := bstep (se 1 (by rfl) ⟨3336551, by rfl⟩ : syracuseStep 4448735 = 6673103) B6673103
theorem B1318527 : Blo 1317977 1318527 := bstep (se 1 (by rfl) ⟨988895, by rfl⟩ : syracuseStep 1318527 = 1977791) B1977791
theorem B2965823 : Blo 1317977 2965823 := bstep (se 1 (by rfl) ⟨2224367, by rfl⟩ : syracuseStep 2965823 = 4448735) B4448735
theorem B1977215 : Blo 1317977 1977215 := bstep (se 1 (by rfl) ⟨1482911, by rfl⟩ : syracuseStep 1977215 = 2965823) B2965823
theorem B1318143 : Blo 1317977 1318143 := bstep (se 1 (by rfl) ⟨988607, by rfl⟩ : syracuseStep 1318143 = 1977215) B1977215

theorem C0 (j : ℕ) (h1 : 329494 ≤ j) (h2 : j ≤ 329868) : Blo 1317977 (4 * j + 3) := by
  interval_cases j
  · exact B1317979
  · exact B1317983
  · exact B1317987
  · exact B1317991
  · exact B1317995
  · exact B1317999
  · exact B1318003
  · exact B1318007
  · exact B1318011
  · exact B1318015
  · exact B1318019
  · exact B1318023
  · exact B1318027
  · exact B1318031
  · exact B1318035
  · exact B1318039
  · exact B1318043
  · exact B1318047
  · exact B1318051
  · exact B1318055
  · exact B1318059
  · exact B1318063
  · exact B1318067
  · exact B1318071
  · exact B1318075
  · exact B1318079
  · exact B1318083
  · exact B1318087
  · exact B1318091
  · exact B1318095
  · exact B1318099
  · exact B1318103
  · exact B1318107
  · exact B1318111
  · exact B1318115
  · exact B1318119
  · exact B1318123
  · exact B1318127
  · exact B1318131
  · exact B1318135
  · exact B1318139
  · exact B1318143
  · exact B1318147
  · exact B1318151
  · exact B1318155
  · exact B1318159
  · exact B1318163
  · exact B1318167
  · exact B1318171
  · exact B1318175
  · exact B1318179
  · exact B1318183
  · exact B1318187
  · exact B1318191
  · exact B1318195
  · exact B1318199
  · exact B1318203
  · exact B1318207
  · exact B1318211
  · exact B1318215
  · exact B1318219
  · exact B1318223
  · exact B1318227
  · exact B1318231
  · exact B1318235
  · exact B1318239
  · exact B1318243
  · exact B1318247
  · exact B1318251
  · exact B1318255
  · exact B1318259
  · exact B1318263
  · exact B1318267
  · exact B1318271
  · exact B1318275
  · exact B1318279
  · exact B1318283
  · exact B1318287
  · exact B1318291
  · exact B1318295
  · exact B1318299
  · exact B1318303
  · exact B1318307
  · exact B1318311
  · exact B1318315
  · exact B1318319
  · exact B1318323
  · exact B1318327
  · exact B1318331
  · exact B1318335
  · exact B1318339
  · exact B1318343
  · exact B1318347
  · exact B1318351
  · exact B1318355
  · exact B1318359
  · exact B1318363
  · exact B1318367
  · exact B1318371
  · exact B1318375
  · exact B1318379
  · exact B1318383
  · exact B1318387
  · exact B1318391
  · exact B1318395
  · exact B1318399
  · exact B1318403
  · exact B1318407
  · exact B1318411
  · exact B1318415
  · exact B1318419
  · exact B1318423
  · exact B1318427
  · exact B1318431
  · exact B1318435
  · exact B1318439
  · exact B1318443
  · exact B1318447
  · exact B1318451
  · exact B1318455
  · exact B1318459
  · exact B1318463
  · exact B1318467
  · exact B1318471
  · exact B1318475
  · exact B1318479
  · exact B1318483
  · exact B1318487
  · exact B1318491
  · exact B1318495
  · exact B1318499
  · exact B1318503
  · exact B1318507
  · exact B1318511
  · exact B1318515
  · exact B1318519
  · exact B1318523
  · exact B1318527
  · exact B1318531
  · exact B1318535
  · exact B1318539
  · exact B1318543
  · exact B1318547
  · exact B1318551
  · exact B1318555
  · exact B1318559
  · exact B1318563
  · exact B1318567
  · exact B1318571
  · exact B1318575
  · exact B1318579
  · exact B1318583
  · exact B1318587
  · exact B1318591
  · exact B1318595
  · exact B1318599
  · exact B1318603
  · exact B1318607
  · exact B1318611
  · exact B1318615
  · exact B1318619
  · exact B1318623
  · exact B1318627
  · exact B1318631
  · exact B1318635
  · exact B1318639
  · exact B1318643
  · exact B1318647
  · exact B1318651
  · exact B1318655
  · exact B1318659
  · exact B1318663
  · exact B1318667
  · exact B1318671
  · exact B1318675
  · exact B1318679
  · exact B1318683
  · exact B1318687
  · exact B1318691
  · exact B1318695
  · exact B1318699
  · exact B1318703
  · exact B1318707
  · exact B1318711
  · exact B1318715
  · exact B1318719
  · exact B1318723
  · exact B1318727
  · exact B1318731
  · exact B1318735
  · exact B1318739
  · exact B1318743
  · exact B1318747
  · exact B1318751
  · exact B1318755
  · exact B1318759
  · exact B1318763
  · exact B1318767
  · exact B1318771
  · exact B1318775
  · exact B1318779
  · exact B1318783
  · exact B1318787
  · exact B1318791
  · exact B1318795
  · exact B1318799
  · exact B1318803
  · exact B1318807
  · exact B1318811
  · exact B1318815
  · exact B1318819
  · exact B1318823
  · exact B1318827
  · exact B1318831
  · exact B1318835
  · exact B1318839
  · exact B1318843
  · exact B1318847
  · exact B1318851
  · exact B1318855
  · exact B1318859
  · exact B1318863
  · exact B1318867
  · exact B1318871
  · exact B1318875
  · exact B1318879
  · exact B1318883
  · exact B1318887
  · exact B1318891
  · exact B1318895
  · exact B1318899
  · exact B1318903
  · exact B1318907
  · exact B1318911
  · exact B1318915
  · exact B1318919
  · exact B1318923
  · exact B1318927
  · exact B1318931
  · exact B1318935
  · exact B1318939
  · exact B1318943
  · exact B1318947
  · exact B1318951
  · exact B1318955
  · exact B1318959
  · exact B1318963
  · exact B1318967
  · exact B1318971
  · exact B1318975
  · exact B1318979
  · exact B1318983
  · exact B1318987
  · exact B1318991
  · exact B1318995
  · exact B1318999
  · exact B1319003
  · exact B1319007
  · exact B1319011
  · exact B1319015
  · exact B1319019
  · exact B1319023
  · exact B1319027
  · exact B1319031
  · exact B1319035
  · exact B1319039
  · exact B1319043
  · exact B1319047
  · exact B1319051
  · exact B1319055
  · exact B1319059
  · exact B1319063
  · exact B1319067
  · exact B1319071
  · exact B1319075
  · exact B1319079
  · exact B1319083
  · exact B1319087
  · exact B1319091
  · exact B1319095
  · exact B1319099
  · exact B1319103
  · exact B1319107
  · exact B1319111
  · exact B1319115
  · exact B1319119
  · exact B1319123
  · exact B1319127
  · exact B1319131
  · exact B1319135
  · exact B1319139
  · exact B1319143
  · exact B1319147
  · exact B1319151
  · exact B1319155
  · exact B1319159
  · exact B1319163
  · exact B1319167
  · exact B1319171
  · exact B1319175
  · exact B1319179
  · exact B1319183
  · exact B1319187
  · exact B1319191
  · exact B1319195
  · exact B1319199
  · exact B1319203
  · exact B1319207
  · exact B1319211
  · exact B1319215
  · exact B1319219
  · exact B1319223
  · exact B1319227
  · exact B1319231
  · exact B1319235
  · exact B1319239
  · exact B1319243
  · exact B1319247
  · exact B1319251
  · exact B1319255
  · exact B1319259
  · exact B1319263
  · exact B1319267
  · exact B1319271
  · exact B1319275
  · exact B1319279
  · exact B1319283
  · exact B1319287
  · exact B1319291
  · exact B1319295
  · exact B1319299
  · exact B1319303
  · exact B1319307
  · exact B1319311
  · exact B1319315
  · exact B1319319
  · exact B1319323
  · exact B1319327
  · exact B1319331
  · exact B1319335
  · exact B1319339
  · exact B1319343
  · exact B1319347
  · exact B1319351
  · exact B1319355
  · exact B1319359
  · exact B1319363
  · exact B1319367
  · exact B1319371
  · exact B1319375
  · exact B1319379
  · exact B1319383
  · exact B1319387
  · exact B1319391
  · exact B1319395
  · exact B1319399
  · exact B1319403
  · exact B1319407
  · exact B1319411
  · exact B1319415
  · exact B1319419
  · exact B1319423
  · exact B1319427
  · exact B1319431
  · exact B1319435
  · exact B1319439
  · exact B1319443
  · exact B1319447
  · exact B1319451
  · exact B1319455
  · exact B1319459
  · exact B1319463
  · exact B1319467
  · exact B1319471
  · exact B1319475

theorem solution (m : ℕ) (hlo : 1317977 ≤ m) (hhi : m ≤ 1319477) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 329494 ≤ j := by omega
    have hj2 : j ≤ 329868 := by omega
    have hb : Blo 1317977 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
