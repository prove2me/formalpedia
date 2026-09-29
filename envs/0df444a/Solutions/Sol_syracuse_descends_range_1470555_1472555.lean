-- Prove2me | solution 1 for syracuse_descends_range_1470555_1472555
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:14:11.772655+00:00
-- url     : https://prove2.me/submissions/d14e1951-5681-4b64-b08a-7b48ac3a619d

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


theorem B1654789 : Blo 1470555 1654789 := bbase (se 4 (by rfl) ⟨155136, by rfl⟩ : syracuseStep 1654789 = 310273) (by norm_num)
theorem B5586965 : Blo 1470555 5586965 := bbase (se 6 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 5586965 = 261889) (by norm_num)
theorem B3309605 : Blo 1470555 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B3727397 : Blo 1470555 3727397 := bbase (se 4 (by rfl) ⟨349443, by rfl⟩ : syracuseStep 3727397 = 698887) (by norm_num)
theorem B1654825 : Blo 1470555 1654825 := bbase (se 2 (by rfl) ⟨620559, by rfl⟩ : syracuseStep 1654825 = 1241119) (by norm_num)
theorem B1491013 : Blo 1470555 1491013 := bbase (se 4 (by rfl) ⟨139782, by rfl⟩ : syracuseStep 1491013 = 279565) (by norm_num)
theorem B1654861 : Blo 1470555 1654861 := bbase (se 3 (by rfl) ⟨310286, by rfl⟩ : syracuseStep 1654861 = 620573) (by norm_num)
theorem B1491029 : Blo 1470555 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B3309677 : Blo 1470555 3309677 := bbase (se 3 (by rfl) ⟨620564, by rfl⟩ : syracuseStep 3309677 = 1241129) (by norm_num)
theorem B2482285 : Blo 1470555 2482285 := bbase (se 3 (by rfl) ⟨465428, by rfl⟩ : syracuseStep 2482285 = 930857) (by norm_num)
theorem B1654897 : Blo 1470555 1654897 := bbase (se 2 (by rfl) ⟨620586, by rfl⟩ : syracuseStep 1654897 = 1241173) (by norm_num)
theorem B1654933 : Blo 1470555 1654933 := bbase (se 6 (by rfl) ⟨38787, by rfl⟩ : syracuseStep 1654933 = 77575) (by norm_num)
theorem B3309749 : Blo 1470555 3309749 := bbase (se 5 (by rfl) ⟨155144, by rfl⟩ : syracuseStep 3309749 = 310289) (by norm_num)
theorem B1654969 : Blo 1470555 1654969 := bbase (se 2 (by rfl) ⟨620613, by rfl⟩ : syracuseStep 1654969 = 1241227) (by norm_num)
theorem B2482373 : Blo 1470555 2482373 := bbase (se 4 (by rfl) ⟨232722, by rfl⟩ : syracuseStep 2482373 = 465445) (by norm_num)
theorem B1655005 : Blo 1470555 1655005 := bbase (se 3 (by rfl) ⟨310313, by rfl⟩ : syracuseStep 1655005 = 620627) (by norm_num)
theorem B4964597 : Blo 1470555 4964597 := bbase (se 5 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 4964597 = 465431) (by norm_num)
theorem B3309821 : Blo 1470555 3309821 := bbase (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) (by norm_num)
theorem B1655041 : Blo 1470555 1655041 := bbase (se 2 (by rfl) ⟨620640, by rfl⟩ : syracuseStep 1655041 = 1241281) (by norm_num)
theorem B1655077 : Blo 1470555 1655077 := bbase (se 4 (by rfl) ⟨155163, by rfl⟩ : syracuseStep 1655077 = 310327) (by norm_num)
theorem B1491257 : Blo 1470555 1491257 := bbase (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) (by norm_num)
theorem B3309893 : Blo 1470555 3309893 := bbase (se 4 (by rfl) ⟨310302, by rfl⟩ : syracuseStep 3309893 = 620605) (by norm_num)
theorem B2482501 : Blo 1470555 2482501 := bbase (se 4 (by rfl) ⟨232734, by rfl⟩ : syracuseStep 2482501 = 465469) (by norm_num)
theorem B1655113 : Blo 1470555 1655113 := bbase (se 2 (by rfl) ⟨620667, by rfl⟩ : syracuseStep 1655113 = 1241335) (by norm_num)
theorem B1655149 : Blo 1470555 1655149 := bbase (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) (by norm_num)
theorem B3309965 : Blo 1470555 3309965 := bbase (se 3 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 3309965 = 1241237) (by norm_num)
theorem B1655185 : Blo 1470555 1655185 := bbase (se 2 (by rfl) ⟨620694, by rfl⟩ : syracuseStep 1655185 = 1241389) (by norm_num)
theorem B7553429 : Blo 1470555 7553429 := bbase (se 6 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 7553429 = 354067) (by norm_num)
theorem B2482589 : Blo 1470555 2482589 := bbase (se 3 (by rfl) ⟨465485, by rfl⟩ : syracuseStep 2482589 = 930971) (by norm_num)
theorem B1655221 : Blo 1470555 1655221 := bbase (se 5 (by rfl) ⟨77588, by rfl⟩ : syracuseStep 1655221 = 155177) (by norm_num)
theorem B3310037 : Blo 1470555 3310037 := bbase (se 7 (by rfl) ⟨38789, by rfl⟩ : syracuseStep 3310037 = 77579) (by norm_num)
theorem B1655257 : Blo 1470555 1655257 := bbase (se 2 (by rfl) ⟨620721, by rfl⟩ : syracuseStep 1655257 = 1241443) (by norm_num)
theorem B1655293 : Blo 1470555 1655293 := bbase (se 3 (by rfl) ⟨310367, by rfl⟩ : syracuseStep 1655293 = 620735) (by norm_num)
theorem B3310109 : Blo 1470555 3310109 := bbase (se 3 (by rfl) ⟨620645, by rfl⟩ : syracuseStep 3310109 = 1241291) (by norm_num)
theorem B2482717 : Blo 1470555 2482717 := bbase (se 3 (by rfl) ⟨465509, by rfl⟩ : syracuseStep 2482717 = 931019) (by norm_num)
theorem B1655329 : Blo 1470555 1655329 := bbase (se 2 (by rfl) ⟨620748, by rfl⟩ : syracuseStep 1655329 = 1241497) (by norm_num)
theorem B1655365 : Blo 1470555 1655365 := bbase (se 4 (by rfl) ⟨155190, by rfl⟩ : syracuseStep 1655365 = 310381) (by norm_num)
theorem B3310181 : Blo 1470555 3310181 := bbase (se 4 (by rfl) ⟨310329, by rfl⟩ : syracuseStep 3310181 = 620659) (by norm_num)
theorem B1655401 : Blo 1470555 1655401 := bbase (se 2 (by rfl) ⟨620775, by rfl⟩ : syracuseStep 1655401 = 1241551) (by norm_num)
theorem B2482805 : Blo 1470555 2482805 := bbase (se 5 (by rfl) ⟨116381, by rfl⟩ : syracuseStep 2482805 = 232763) (by norm_num)
theorem B1491593 : Blo 1470555 1491593 := bbase (se 2 (by rfl) ⟨559347, by rfl⟩ : syracuseStep 1491593 = 1118695) (by norm_num)
theorem B1655437 : Blo 1470555 1655437 := bbase (se 3 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 1655437 = 620789) (by norm_num)
theorem B4965029 : Blo 1470555 4965029 := bbase (se 4 (by rfl) ⟨465471, by rfl⟩ : syracuseStep 4965029 = 930943) (by norm_num)
theorem B3310253 : Blo 1470555 3310253 := bbase (se 3 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 3310253 = 1241345) (by norm_num)
theorem B1655473 : Blo 1470555 1655473 := bbase (se 2 (by rfl) ⟨620802, by rfl⟩ : syracuseStep 1655473 = 1241605) (by norm_num)
theorem B2794189 : Blo 1470555 2794189 := bbase (se 3 (by rfl) ⟨523910, by rfl⟩ : syracuseStep 2794189 = 1047821) (by norm_num)
theorem B1655509 : Blo 1470555 1655509 := bbase (se 7 (by rfl) ⟨19400, by rfl⟩ : syracuseStep 1655509 = 38801) (by norm_num)
theorem B3310325 : Blo 1470555 3310325 := bbase (se 5 (by rfl) ⟨155171, by rfl⟩ : syracuseStep 3310325 = 310343) (by norm_num)
theorem B2482933 : Blo 1470555 2482933 := bbase (se 5 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 2482933 = 232775) (by norm_num)
theorem B1655545 : Blo 1470555 1655545 := bbase (se 2 (by rfl) ⟨620829, by rfl⟩ : syracuseStep 1655545 = 1241659) (by norm_num)
theorem B7447301 : Blo 1470555 7447301 := bbase (se 4 (by rfl) ⟨698184, by rfl⟩ : syracuseStep 7447301 = 1396369) (by norm_num)
theorem B1655581 : Blo 1470555 1655581 := bbase (se 3 (by rfl) ⟨310421, by rfl⟩ : syracuseStep 1655581 = 620843) (by norm_num)
theorem B3310397 : Blo 1470555 3310397 := bbase (se 3 (by rfl) ⟨620699, by rfl⟩ : syracuseStep 3310397 = 1241399) (by norm_num)
theorem B1655617 : Blo 1470555 1655617 := bbase (se 2 (by rfl) ⟨620856, by rfl⟩ : syracuseStep 1655617 = 1241713) (by norm_num)
theorem B2483021 : Blo 1470555 2483021 := bbase (se 3 (by rfl) ⟨465566, by rfl⟩ : syracuseStep 2483021 = 931133) (by norm_num)
theorem B2794333 : Blo 1470555 2794333 := bbase (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) (by norm_num)
theorem B2982757 : Blo 1470555 2982757 := bbase (se 4 (by rfl) ⟨279633, by rfl⟩ : syracuseStep 2982757 = 559267) (by norm_num)
theorem B1655653 : Blo 1470555 1655653 := bbase (se 4 (by rfl) ⟨155217, by rfl⟩ : syracuseStep 1655653 = 310435) (by norm_num)
theorem B3310469 : Blo 1470555 3310469 := bbase (se 4 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 3310469 = 620713) (by norm_num)
theorem B1655689 : Blo 1470555 1655689 := bbase (se 2 (by rfl) ⟨620883, by rfl⟩ : syracuseStep 1655689 = 1241767) (by norm_num)
theorem B1655725 : Blo 1470555 1655725 := bbase (se 3 (by rfl) ⟨310448, by rfl⟩ : syracuseStep 1655725 = 620897) (by norm_num)
theorem B3310541 : Blo 1470555 3310541 := bbase (se 3 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 3310541 = 1241453) (by norm_num)
theorem B2483149 : Blo 1470555 2483149 := bbase (se 3 (by rfl) ⟨465590, by rfl⟩ : syracuseStep 2483149 = 931181) (by norm_num)
theorem B1655761 : Blo 1470555 1655761 := bbase (se 2 (by rfl) ⟨620910, by rfl⟩ : syracuseStep 1655761 = 1241821) (by norm_num)
theorem B1655797 : Blo 1470555 1655797 := bbase (se 5 (by rfl) ⟨77615, by rfl⟩ : syracuseStep 1655797 = 155231) (by norm_num)
theorem B2794493 : Blo 1470555 2794493 := bbase (se 3 (by rfl) ⟨523967, by rfl⟩ : syracuseStep 2794493 = 1047935) (by norm_num)
theorem B3310613 : Blo 1470555 3310613 := bbase (se 6 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 3310613 = 155185) (by norm_num)
theorem B1655833 : Blo 1470555 1655833 := bbase (se 2 (by rfl) ⟨620937, by rfl⟩ : syracuseStep 1655833 = 1241875) (by norm_num)
theorem B2483237 : Blo 1470555 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B7955509 : Blo 1470555 7955509 := bbase (se 5 (by rfl) ⟨372914, by rfl⟩ : syracuseStep 7955509 = 745829) (by norm_num)
theorem B1655869 : Blo 1470555 1655869 := bbase (se 3 (by rfl) ⟨310475, by rfl⟩ : syracuseStep 1655869 = 620951) (by norm_num)
theorem B40264789 : Blo 1470555 40264789 := bbase (se 8 (by rfl) ⟨235926, by rfl⟩ : syracuseStep 40264789 = 471853) (by norm_num)
theorem B4965461 : Blo 1470555 4965461 := bbase (se 8 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 4965461 = 58189) (by norm_num)
theorem B3310685 : Blo 1470555 3310685 := bbase (se 3 (by rfl) ⟨620753, by rfl⟩ : syracuseStep 3310685 = 1241507) (by norm_num)
theorem B1655905 : Blo 1470555 1655905 := bbase (se 2 (by rfl) ⟨620964, by rfl⟩ : syracuseStep 1655905 = 1241929) (by norm_num)
theorem B1655941 : Blo 1470555 1655941 := bbase (se 4 (by rfl) ⟨155244, by rfl⟩ : syracuseStep 1655941 = 310489) (by norm_num)
theorem B2794637 : Blo 1470555 2794637 := bbase (se 3 (by rfl) ⟨523994, by rfl⟩ : syracuseStep 2794637 = 1047989) (by norm_num)
theorem B3310757 : Blo 1470555 3310757 := bbase (se 4 (by rfl) ⟨310383, by rfl⟩ : syracuseStep 3310757 = 620767) (by norm_num)
theorem B2483365 : Blo 1470555 2483365 := bbase (se 4 (by rfl) ⟨232815, by rfl⟩ : syracuseStep 2483365 = 465631) (by norm_num)
theorem B1655977 : Blo 1470555 1655977 := bbase (se 2 (by rfl) ⟨620991, by rfl⟩ : syracuseStep 1655977 = 1241983) (by norm_num)
theorem B5588149 : Blo 1470555 5588149 := bbase (se 5 (by rfl) ⟨261944, by rfl⟩ : syracuseStep 5588149 = 523889) (by norm_num)
theorem B1656013 : Blo 1470555 1656013 := bbase (se 3 (by rfl) ⟨310502, by rfl⟩ : syracuseStep 1656013 = 621005) (by norm_num)
theorem B16753877 : Blo 1470555 16753877 := bbase (se 7 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 16753877 = 392669) (by norm_num)
theorem B2516189 : Blo 1470555 2516189 := bbase (se 3 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 2516189 = 943571) (by norm_num)
theorem B3310829 : Blo 1470555 3310829 := bbase (se 3 (by rfl) ⟨620780, by rfl⟩ : syracuseStep 3310829 = 1241561) (by norm_num)
theorem B1656049 : Blo 1470555 1656049 := bbase (se 2 (by rfl) ⟨621018, by rfl⟩ : syracuseStep 1656049 = 1242037) (by norm_num)
theorem B5301493 : Blo 1470555 5301493 := bbase (se 5 (by rfl) ⟨248507, by rfl⟩ : syracuseStep 5301493 = 497015) (by norm_num)
theorem B1492213 : Blo 1470555 1492213 := bbase (se 5 (by rfl) ⟨69947, by rfl⟩ : syracuseStep 1492213 = 139895) (by norm_num)
theorem B2483453 : Blo 1470555 2483453 := bbase (se 3 (by rfl) ⟨465647, by rfl⟩ : syracuseStep 2483453 = 931295) (by norm_num)
theorem B1656085 : Blo 1470555 1656085 := bbase (se 6 (by rfl) ⟨38814, by rfl⟩ : syracuseStep 1656085 = 77629) (by norm_num)
theorem B3310901 : Blo 1470555 3310901 := bbase (se 5 (by rfl) ⟨155198, by rfl⟩ : syracuseStep 3310901 = 310397) (by norm_num)
theorem B1656121 : Blo 1470555 1656121 := bbase (se 2 (by rfl) ⟨621045, by rfl⟩ : syracuseStep 1656121 = 1242091) (by norm_num)
theorem B1656157 : Blo 1470555 1656157 := bbase (se 3 (by rfl) ⟨310529, by rfl⟩ : syracuseStep 1656157 = 621059) (by norm_num)
theorem B3310973 : Blo 1470555 3310973 := bbase (se 3 (by rfl) ⟨620807, by rfl⟩ : syracuseStep 3310973 = 1241615) (by norm_num)
theorem B2483581 : Blo 1470555 2483581 := bbase (se 3 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 2483581 = 931343) (by norm_num)
theorem B1656193 : Blo 1470555 1656193 := bbase (se 2 (by rfl) ⟨621072, by rfl⟩ : syracuseStep 1656193 = 1242145) (by norm_num)
theorem B1656229 : Blo 1470555 1656229 := bbase (se 4 (by rfl) ⟨155271, by rfl⟩ : syracuseStep 1656229 = 310543) (by norm_num)
theorem B2794925 : Blo 1470555 2794925 := bbase (se 3 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 2794925 = 1048097) (by norm_num)
theorem B3311045 : Blo 1470555 3311045 := bbase (se 4 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 3311045 = 620821) (by norm_num)
theorem B1656265 : Blo 1470555 1656265 := bbase (se 2 (by rfl) ⟨621099, by rfl⟩ : syracuseStep 1656265 = 1242199) (by norm_num)
theorem B2516429 : Blo 1470555 2516429 := bbase (se 3 (by rfl) ⟨471830, by rfl⟩ : syracuseStep 2516429 = 943661) (by norm_num)
theorem B2483669 : Blo 1470555 2483669 := bbase (se 7 (by rfl) ⟨29105, by rfl⟩ : syracuseStep 2483669 = 58211) (by norm_num)
theorem B5588453 : Blo 1470555 5588453 := bbase (se 4 (by rfl) ⟨523917, by rfl⟩ : syracuseStep 5588453 = 1047835) (by norm_num)
theorem B1656301 : Blo 1470555 1656301 := bbase (se 3 (by rfl) ⟨310556, by rfl⟩ : syracuseStep 1656301 = 621113) (by norm_num)
theorem B4965893 : Blo 1470555 4965893 := bbase (se 4 (by rfl) ⟨465552, by rfl⟩ : syracuseStep 4965893 = 931105) (by norm_num)
theorem B3311117 : Blo 1470555 3311117 := bbase (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) (by norm_num)
theorem B1656337 : Blo 1470555 1656337 := bbase (se 2 (by rfl) ⟨621126, by rfl⟩ : syracuseStep 1656337 = 1242253) (by norm_num)
theorem B1656373 : Blo 1470555 1656373 := bbase (se 5 (by rfl) ⟨77642, by rfl⟩ : syracuseStep 1656373 = 155285) (by norm_num)
theorem B2795077 : Blo 1470555 2795077 := bbase (se 4 (by rfl) ⟨262038, by rfl⟩ : syracuseStep 2795077 = 524077) (by norm_num)
theorem B3311189 : Blo 1470555 3311189 := bbase (se 8 (by rfl) ⟨19401, by rfl⟩ : syracuseStep 3311189 = 38803) (by norm_num)
theorem B2483797 : Blo 1470555 2483797 := bbase (se 8 (by rfl) ⟨14553, by rfl⟩ : syracuseStep 2483797 = 29107) (by norm_num)
theorem B1656409 : Blo 1470555 1656409 := bbase (se 2 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 1656409 = 1242307) (by norm_num)
theorem B1861213 : Blo 1470555 1861213 := bbase (se 3 (by rfl) ⟨348977, by rfl⟩ : syracuseStep 1861213 = 697955) (by norm_num)
theorem B2238077 : Blo 1470555 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B1656445 : Blo 1470555 1656445 := bbase (se 3 (by rfl) ⟨310583, by rfl⟩ : syracuseStep 1656445 = 621167) (by norm_num)
theorem B3311261 : Blo 1470555 3311261 := bbase (se 3 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 3311261 = 1241723) (by norm_num)
theorem B1656481 : Blo 1470555 1656481 := bbase (se 2 (by rfl) ⟨621180, by rfl⟩ : syracuseStep 1656481 = 1242361) (by norm_num)
theorem B2483885 : Blo 1470555 2483885 := bbase (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) (by norm_num)
theorem B1861309 : Blo 1470555 1861309 := bbase (se 3 (by rfl) ⟨348995, by rfl⟩ : syracuseStep 1861309 = 697991) (by norm_num)
theorem B1656517 : Blo 1470555 1656517 := bbase (se 4 (by rfl) ⟨155298, by rfl⟩ : syracuseStep 1656517 = 310597) (by norm_num)
theorem B4474597 : Blo 1470555 4474597 := bbase (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) (by norm_num)
theorem B3311333 : Blo 1470555 3311333 := bbase (se 4 (by rfl) ⟨310437, by rfl⟩ : syracuseStep 3311333 = 620875) (by norm_num)
theorem B1656553 : Blo 1470555 1656553 := bbase (se 2 (by rfl) ⟨621207, by rfl⟩ : syracuseStep 1656553 = 1242415) (by norm_num)
theorem B1656589 : Blo 1470555 1656589 := bbase (se 3 (by rfl) ⟨310610, by rfl⟩ : syracuseStep 1656589 = 621221) (by norm_num)
theorem B3311405 : Blo 1470555 3311405 := bbase (se 3 (by rfl) ⟨620888, by rfl⟩ : syracuseStep 3311405 = 1241777) (by norm_num)
theorem B2484013 : Blo 1470555 2484013 := bbase (se 3 (by rfl) ⟨465752, by rfl⟩ : syracuseStep 2484013 = 931505) (by norm_num)
theorem B1656625 : Blo 1470555 1656625 := bbase (se 2 (by rfl) ⟨621234, by rfl⟩ : syracuseStep 1656625 = 1242469) (by norm_num)
theorem B1861481 : Blo 1470555 1861481 := bbase (se 2 (by rfl) ⟨698055, by rfl⟩ : syracuseStep 1861481 = 1396111) (by norm_num)
theorem B3311477 : Blo 1470555 3311477 := bbase (se 5 (by rfl) ⟨155225, by rfl⟩ : syracuseStep 3311477 = 310451) (by norm_num)
theorem B2795381 : Blo 1470555 2795381 := bbase (se 5 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 2795381 = 262067) (by norm_num)
theorem B4188037 : Blo 1470555 4188037 := bbase (se 4 (by rfl) ⟨392628, by rfl⟩ : syracuseStep 4188037 = 785257) (by norm_num)
theorem B2484101 : Blo 1470555 2484101 := bbase (se 4 (by rfl) ⟨232884, by rfl⟩ : syracuseStep 2484101 = 465769) (by norm_num)
theorem B1861537 : Blo 1470555 1861537 := bbase (se 2 (by rfl) ⟨698076, by rfl⟩ : syracuseStep 1861537 = 1396153) (by norm_num)
theorem B4966325 : Blo 1470555 4966325 := bbase (se 5 (by rfl) ⟨232796, by rfl⟩ : syracuseStep 4966325 = 465593) (by norm_num)
theorem B3311549 : Blo 1470555 3311549 := bbase (se 3 (by rfl) ⟨620915, by rfl⟩ : syracuseStep 3311549 = 1241831) (by norm_num)
theorem B7071733 : Blo 1470555 7071733 := bbase (se 5 (by rfl) ⟨331487, by rfl⟩ : syracuseStep 7071733 = 662975) (by norm_num)
theorem B1861633 : Blo 1470555 1861633 := bbase (se 2 (by rfl) ⟨698112, by rfl⟩ : syracuseStep 1861633 = 1396225) (by norm_num)
theorem B3311621 : Blo 1470555 3311621 := bbase (se 4 (by rfl) ⟨310464, by rfl⟩ : syracuseStep 3311621 = 620929) (by norm_num)
theorem B2484229 : Blo 1470555 2484229 := bbase (se 4 (by rfl) ⟨232896, by rfl⟩ : syracuseStep 2484229 = 465793) (by norm_num)
theorem B7448597 : Blo 1470555 7448597 := bbase (se 6 (by rfl) ⟨174576, by rfl⟩ : syracuseStep 7448597 = 349153) (by norm_num)
theorem B3311693 : Blo 1470555 3311693 := bbase (se 3 (by rfl) ⟨620942, by rfl⟩ : syracuseStep 3311693 = 1241885) (by norm_num)
theorem B2484317 : Blo 1470555 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B2238557 : Blo 1470555 2238557 := bbase (se 3 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 2238557 = 839459) (by norm_num)
theorem B2205845 : Blo 1470555 2205845 := bbase (se 6 (by rfl) ⟨51699, by rfl⟩ : syracuseStep 2205845 = 103399) (by norm_num)
theorem B3311765 : Blo 1470555 3311765 := bbase (se 6 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 3311765 = 155239) (by norm_num)
theorem B2205869 : Blo 1470555 2205869 := bbase (se 3 (by rfl) ⟨413600, by rfl⟩ : syracuseStep 2205869 = 827201) (by norm_num)
theorem B1861805 : Blo 1470555 1861805 := bbase (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) (by norm_num)
theorem B14141621 : Blo 1470555 14141621 := bbase (se 5 (by rfl) ⟨662888, by rfl⟩ : syracuseStep 14141621 = 1325777) (by norm_num)
theorem B2205893 : Blo 1470555 2205893 := bbase (se 4 (by rfl) ⟨206802, by rfl⟩ : syracuseStep 2205893 = 413605) (by norm_num)
theorem B2205917 : Blo 1470555 2205917 := bbase (se 3 (by rfl) ⟨413609, by rfl⟩ : syracuseStep 2205917 = 827219) (by norm_num)
theorem B3311837 : Blo 1470555 3311837 := bbase (se 3 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 3311837 = 1241939) (by norm_num)
theorem B2484445 : Blo 1470555 2484445 := bbase (se 3 (by rfl) ⟨465833, by rfl⟩ : syracuseStep 2484445 = 931667) (by norm_num)
theorem B1861861 : Blo 1470555 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B2205941 : Blo 1470555 2205941 := bbase (se 5 (by rfl) ⟨103403, by rfl⟩ : syracuseStep 2205941 = 206807) (by norm_num)
theorem B2205965 : Blo 1470555 2205965 := bbase (se 3 (by rfl) ⟨413618, by rfl⟩ : syracuseStep 2205965 = 827237) (by norm_num)
theorem B2205989 : Blo 1470555 2205989 := bbase (se 4 (by rfl) ⟨206811, by rfl⟩ : syracuseStep 2205989 = 413623) (by norm_num)
theorem B3311909 : Blo 1470555 3311909 := bbase (se 4 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 3311909 = 620983) (by norm_num)
theorem B2484533 : Blo 1470555 2484533 := bbase (se 5 (by rfl) ⟨116462, by rfl⟩ : syracuseStep 2484533 = 232925) (by norm_num)
theorem B2206013 : Blo 1470555 2206013 := bbase (se 3 (by rfl) ⟨413627, by rfl⟩ : syracuseStep 2206013 = 827255) (by norm_num)
theorem B1861957 : Blo 1470555 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B2206037 : Blo 1470555 2206037 := bbase (se 10 (by rfl) ⟨3231, by rfl⟩ : syracuseStep 2206037 = 6463) (by norm_num)
theorem B4966757 : Blo 1470555 4966757 := bbase (se 4 (by rfl) ⟨465633, by rfl⟩ : syracuseStep 4966757 = 931267) (by norm_num)
theorem B2206061 : Blo 1470555 2206061 := bbase (se 3 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 2206061 = 827273) (by norm_num)
theorem B3311981 : Blo 1470555 3311981 := bbase (se 3 (by rfl) ⟨620996, by rfl⟩ : syracuseStep 3311981 = 1241993) (by norm_num)
theorem B2206085 : Blo 1470555 2206085 := bbase (se 4 (by rfl) ⟨206820, by rfl⟩ : syracuseStep 2206085 = 413641) (by norm_num)
theorem B2206109 : Blo 1470555 2206109 := bbase (se 3 (by rfl) ⟨413645, by rfl⟩ : syracuseStep 2206109 = 827291) (by norm_num)
theorem B2206133 : Blo 1470555 2206133 := bbase (se 5 (by rfl) ⟨103412, by rfl⟩ : syracuseStep 2206133 = 206825) (by norm_num)
theorem B3312053 : Blo 1470555 3312053 := bbase (se 5 (by rfl) ⟨155252, by rfl⟩ : syracuseStep 3312053 = 310505) (by norm_num)
theorem B2484661 : Blo 1470555 2484661 := bbase (se 5 (by rfl) ⟨116468, by rfl⟩ : syracuseStep 2484661 = 232937) (by norm_num)
theorem B1886653 : Blo 1470555 1886653 := bbase (se 3 (by rfl) ⟨353747, by rfl⟩ : syracuseStep 1886653 = 707495) (by norm_num)
theorem B2206157 : Blo 1470555 2206157 := bbase (se 3 (by rfl) ⟨413654, by rfl⟩ : syracuseStep 2206157 = 827309) (by norm_num)
theorem B2206181 : Blo 1470555 2206181 := bbase (se 4 (by rfl) ⟨206829, by rfl⟩ : syracuseStep 2206181 = 413659) (by norm_num)
theorem B1862129 : Blo 1470555 1862129 := bbase (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) (by norm_num)
theorem B2206205 : Blo 1470555 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B3312125 : Blo 1470555 3312125 := bbase (se 3 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 3312125 = 1242047) (by norm_num)
theorem B2484749 : Blo 1470555 2484749 := bbase (se 3 (by rfl) ⟨465890, by rfl⟩ : syracuseStep 2484749 = 931781) (by norm_num)
theorem B2206229 : Blo 1470555 2206229 := bbase (se 6 (by rfl) ⟨51708, by rfl⟩ : syracuseStep 2206229 = 103417) (by norm_num)
theorem B12577301 : Blo 1470555 12577301 := bbase (se 6 (by rfl) ⟨294780, by rfl⟩ : syracuseStep 12577301 = 589561) (by norm_num)
theorem B1862185 : Blo 1470555 1862185 := bbase (se 2 (by rfl) ⟨698319, by rfl⟩ : syracuseStep 1862185 = 1396639) (by norm_num)
theorem B2206253 : Blo 1470555 2206253 := bbase (se 3 (by rfl) ⟨413672, by rfl⟩ : syracuseStep 2206253 = 827345) (by norm_num)
theorem B2206277 : Blo 1470555 2206277 := bbase (se 4 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 2206277 = 413677) (by norm_num)
theorem B3312197 : Blo 1470555 3312197 := bbase (se 4 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 3312197 = 621037) (by norm_num)
theorem B2206301 : Blo 1470555 2206301 := bbase (se 3 (by rfl) ⟨413681, by rfl⟩ : syracuseStep 2206301 = 827363) (by norm_num)
theorem B2206325 : Blo 1470555 2206325 := bbase (se 5 (by rfl) ⟨103421, by rfl⟩ : syracuseStep 2206325 = 206843) (by norm_num)
theorem B1862281 : Blo 1470555 1862281 := bbase (se 2 (by rfl) ⟨698355, by rfl⟩ : syracuseStep 1862281 = 1396711) (by norm_num)
theorem B2206349 : Blo 1470555 2206349 := bbase (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) (by norm_num)
theorem B3312269 : Blo 1470555 3312269 := bbase (se 3 (by rfl) ⟨621050, by rfl⟩ : syracuseStep 3312269 = 1242101) (by norm_num)
theorem B2484877 : Blo 1470555 2484877 := bbase (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) (by norm_num)
theorem B2206373 : Blo 1470555 2206373 := bbase (se 4 (by rfl) ⟨206847, by rfl⟩ : syracuseStep 2206373 = 413695) (by norm_num)
theorem B4475557 : Blo 1470555 4475557 := bbase (se 4 (by rfl) ⟨419583, by rfl⟩ : syracuseStep 4475557 = 839167) (by norm_num)
theorem B2206397 : Blo 1470555 2206397 := bbase (se 3 (by rfl) ⟨413699, by rfl⟩ : syracuseStep 2206397 = 827399) (by norm_num)
theorem B2206421 : Blo 1470555 2206421 := bbase (se 7 (by rfl) ⟨25856, by rfl⟩ : syracuseStep 2206421 = 51713) (by norm_num)
theorem B3312341 : Blo 1470555 3312341 := bbase (se 7 (by rfl) ⟨38816, by rfl⟩ : syracuseStep 3312341 = 77633) (by norm_num)
theorem B2206445 : Blo 1470555 2206445 := bbase (se 3 (by rfl) ⟨413708, by rfl⟩ : syracuseStep 2206445 = 827417) (by norm_num)
theorem B11938549 : Blo 1470555 11938549 := bbase (se 5 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 11938549 = 1119239) (by norm_num)
theorem B2206469 : Blo 1470555 2206469 := bbase (se 4 (by rfl) ⟨206856, by rfl⟩ : syracuseStep 2206469 = 413713) (by norm_num)
theorem B4967189 : Blo 1470555 4967189 := bbase (se 6 (by rfl) ⟨116418, by rfl⟩ : syracuseStep 4967189 = 232837) (by norm_num)
theorem B2206493 : Blo 1470555 2206493 := bbase (se 3 (by rfl) ⟨413717, by rfl⟩ : syracuseStep 2206493 = 827435) (by norm_num)
theorem B3312413 : Blo 1470555 3312413 := bbase (se 3 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 3312413 = 1242155) (by norm_num)
theorem B2206517 : Blo 1470555 2206517 := bbase (se 5 (by rfl) ⟨103430, by rfl⟩ : syracuseStep 2206517 = 206861) (by norm_num)
theorem B1862453 : Blo 1470555 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B7269173 : Blo 1470555 7269173 := bbase (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) (by norm_num)
theorem B2206541 : Blo 1470555 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B9423701 : Blo 1470555 9423701 := bbase (se 9 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 9423701 = 55217) (by norm_num)
theorem B4246357 : Blo 1470555 4246357 := bbase (se 9 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 4246357 = 24881) (by norm_num)
theorem B135940949 : Blo 1470555 135940949 := bbase (se 9 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 135940949 = 796529) (by norm_num)
theorem B2206565 : Blo 1470555 2206565 := bbase (se 4 (by rfl) ⟨206865, by rfl⟩ : syracuseStep 2206565 = 413731) (by norm_num)
theorem B3312485 : Blo 1470555 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B1862509 : Blo 1470555 1862509 := bbase (se 3 (by rfl) ⟨349220, by rfl⟩ : syracuseStep 1862509 = 698441) (by norm_num)
theorem B2206589 : Blo 1470555 2206589 := bbase (se 3 (by rfl) ⟨413735, by rfl⟩ : syracuseStep 2206589 = 827471) (by norm_num)
theorem B2206613 : Blo 1470555 2206613 := bbase (se 6 (by rfl) ⟨51717, by rfl⟩ : syracuseStep 2206613 = 103435) (by norm_num)
theorem B2206637 : Blo 1470555 2206637 := bbase (se 3 (by rfl) ⟨413744, by rfl⟩ : syracuseStep 2206637 = 827489) (by norm_num)
theorem B3312557 : Blo 1470555 3312557 := bbase (se 3 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 3312557 = 1242209) (by norm_num)
theorem B2206661 : Blo 1470555 2206661 := bbase (se 4 (by rfl) ⟨206874, by rfl⟩ : syracuseStep 2206661 = 413749) (by norm_num)
theorem B1862605 : Blo 1470555 1862605 := bbase (se 3 (by rfl) ⟨349238, by rfl⟩ : syracuseStep 1862605 = 698477) (by norm_num)
theorem B2206685 : Blo 1470555 2206685 := bbase (se 3 (by rfl) ⟨413753, by rfl⟩ : syracuseStep 2206685 = 827507) (by norm_num)
theorem B2206709 : Blo 1470555 2206709 := bbase (se 5 (by rfl) ⟨103439, by rfl⟩ : syracuseStep 2206709 = 206879) (by norm_num)
theorem B3312629 : Blo 1470555 3312629 := bbase (se 5 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 3312629 = 310559) (by norm_num)
theorem B2206733 : Blo 1470555 2206733 := bbase (se 3 (by rfl) ⟨413762, by rfl⟩ : syracuseStep 2206733 = 827525) (by norm_num)
theorem B1592345 : Blo 1470555 1592345 := bbase (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) (by norm_num)
theorem B2206757 : Blo 1470555 2206757 := bbase (se 4 (by rfl) ⟨206883, by rfl⟩ : syracuseStep 2206757 = 413767) (by norm_num)
theorem B2206781 : Blo 1470555 2206781 := bbase (se 3 (by rfl) ⟨413771, by rfl⟩ : syracuseStep 2206781 = 827543) (by norm_num)
theorem B3312701 : Blo 1470555 3312701 := bbase (se 3 (by rfl) ⟨621131, by rfl⟩ : syracuseStep 3312701 = 1242263) (by norm_num)
theorem B1887305 : Blo 1470555 1887305 := bbase (se 2 (by rfl) ⟨707739, by rfl⟩ : syracuseStep 1887305 = 1415479) (by norm_num)
theorem B2206805 : Blo 1470555 2206805 := bbase (se 8 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 2206805 = 25861) (by norm_num)
theorem B2206829 : Blo 1470555 2206829 := bbase (se 3 (by rfl) ⟨413780, by rfl⟩ : syracuseStep 2206829 = 827561) (by norm_num)
theorem B1862777 : Blo 1470555 1862777 := bbase (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) (by norm_num)
theorem B2206853 : Blo 1470555 2206853 := bbase (se 4 (by rfl) ⟨206892, by rfl⟩ : syracuseStep 2206853 = 413785) (by norm_num)
theorem B3312773 : Blo 1470555 3312773 := bbase (se 4 (by rfl) ⟨310572, by rfl⟩ : syracuseStep 3312773 = 621145) (by norm_num)
theorem B2206877 : Blo 1470555 2206877 := bbase (se 3 (by rfl) ⟨413789, by rfl⟩ : syracuseStep 2206877 = 827579) (by norm_num)
theorem B1592497 : Blo 1470555 1592497 := bbase (se 2 (by rfl) ⟨597186, by rfl⟩ : syracuseStep 1592497 = 1194373) (by norm_num)
theorem B1862833 : Blo 1470555 1862833 := bbase (se 2 (by rfl) ⟨698562, by rfl⟩ : syracuseStep 1862833 = 1397125) (by norm_num)
theorem B2206901 : Blo 1470555 2206901 := bbase (se 5 (by rfl) ⟨103448, by rfl⟩ : syracuseStep 2206901 = 206897) (by norm_num)
theorem B6286517 : Blo 1470555 6286517 := bbase (se 5 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 6286517 = 589361) (by norm_num)
theorem B4967621 : Blo 1470555 4967621 := bbase (se 4 (by rfl) ⟨465714, by rfl⟩ : syracuseStep 4967621 = 931429) (by norm_num)
theorem B2206925 : Blo 1470555 2206925 := bbase (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) (by norm_num)
theorem B3312845 : Blo 1470555 3312845 := bbase (se 3 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 3312845 = 1242317) (by norm_num)
theorem B2206949 : Blo 1470555 2206949 := bbase (se 4 (by rfl) ⟨206901, by rfl⟩ : syracuseStep 2206949 = 413803) (by norm_num)
theorem B2206973 : Blo 1470555 2206973 := bbase (se 3 (by rfl) ⟨413807, by rfl⟩ : syracuseStep 2206973 = 827615) (by norm_num)
theorem B1862929 : Blo 1470555 1862929 := bbase (se 2 (by rfl) ⟨698598, by rfl⟩ : syracuseStep 1862929 = 1397197) (by norm_num)
theorem B2206997 : Blo 1470555 2206997 := bbase (se 6 (by rfl) ⟨51726, by rfl⟩ : syracuseStep 2206997 = 103453) (by norm_num)
theorem B3312917 : Blo 1470555 3312917 := bbase (se 6 (by rfl) ⟨77646, by rfl⟩ : syracuseStep 3312917 = 155293) (by norm_num)
theorem B7449893 : Blo 1470555 7449893 := bbase (se 4 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 7449893 = 1396855) (by norm_num)
theorem B2207021 : Blo 1470555 2207021 := bbase (se 3 (by rfl) ⟨413816, by rfl⟩ : syracuseStep 2207021 = 827633) (by norm_num)
theorem B3722557 : Blo 1470555 3722557 := bbase (se 3 (by rfl) ⟨697979, by rfl⟩ : syracuseStep 3722557 = 1395959) (by norm_num)
theorem B2207045 : Blo 1470555 2207045 := bbase (se 4 (by rfl) ⟨206910, by rfl⟩ : syracuseStep 2207045 = 413821) (by norm_num)
theorem B2207069 : Blo 1470555 2207069 := bbase (se 3 (by rfl) ⟨413825, by rfl⟩ : syracuseStep 2207069 = 827651) (by norm_num)
theorem B3312989 : Blo 1470555 3312989 := bbase (se 3 (by rfl) ⟨621185, by rfl⟩ : syracuseStep 3312989 = 1242371) (by norm_num)
theorem B2207093 : Blo 1470555 2207093 := bbase (se 5 (by rfl) ⟨103457, by rfl⟩ : syracuseStep 2207093 = 206915) (by norm_num)
theorem B2207117 : Blo 1470555 2207117 := bbase (se 3 (by rfl) ⟨413834, by rfl⟩ : syracuseStep 2207117 = 827669) (by norm_num)
theorem B2207141 : Blo 1470555 2207141 := bbase (se 4 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 2207141 = 413839) (by norm_num)
theorem B3313061 : Blo 1470555 3313061 := bbase (se 4 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 3313061 = 621199) (by norm_num)
theorem B3722669 : Blo 1470555 3722669 := bbase (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) (by norm_num)
theorem B2207165 : Blo 1470555 2207165 := bbase (se 3 (by rfl) ⟨413843, by rfl⟩ : syracuseStep 2207165 = 827687) (by norm_num)
theorem B1863101 : Blo 1470555 1863101 := bbase (se 3 (by rfl) ⟨349331, by rfl⟩ : syracuseStep 1863101 = 698663) (by norm_num)
theorem B2207189 : Blo 1470555 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B6286805 : Blo 1470555 6286805 := bbase (se 7 (by rfl) ⟨73673, by rfl⟩ : syracuseStep 6286805 = 147347) (by norm_num)
theorem B2207213 : Blo 1470555 2207213 := bbase (se 3 (by rfl) ⟨413852, by rfl⟩ : syracuseStep 2207213 = 827705) (by norm_num)
theorem B3313133 : Blo 1470555 3313133 := bbase (se 3 (by rfl) ⟨621212, by rfl⟩ : syracuseStep 3313133 = 1242425) (by norm_num)
theorem B1863157 : Blo 1470555 1863157 := bbase (se 5 (by rfl) ⟨87335, by rfl⟩ : syracuseStep 1863157 = 174671) (by norm_num)
theorem B2043389 : Blo 1470555 2043389 := bbase (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) (by norm_num)
theorem B2207237 : Blo 1470555 2207237 := bbase (se 4 (by rfl) ⟨206928, by rfl⟩ : syracuseStep 2207237 = 413857) (by norm_num)
theorem B18853397 : Blo 1470555 18853397 := bbase (se 6 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 18853397 = 883753) (by norm_num)
theorem B2207261 : Blo 1470555 2207261 := bbase (se 3 (by rfl) ⟨413861, by rfl⟩ : syracuseStep 2207261 = 827723) (by norm_num)
theorem B5590565 : Blo 1470555 5590565 := bbase (se 4 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 5590565 = 1048231) (by norm_num)
theorem B2207285 : Blo 1470555 2207285 := bbase (se 5 (by rfl) ⟨103466, by rfl⟩ : syracuseStep 2207285 = 206933) (by norm_num)
theorem B3313205 : Blo 1470555 3313205 := bbase (se 5 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 3313205 = 310613) (by norm_num)
theorem B2207309 : Blo 1470555 2207309 := bbase (se 3 (by rfl) ⟨413870, by rfl⟩ : syracuseStep 2207309 = 827741) (by norm_num)
theorem B1863253 : Blo 1470555 1863253 := bbase (se 8 (by rfl) ⟨10917, by rfl⟩ : syracuseStep 1863253 = 21835) (by norm_num)
theorem B2207333 : Blo 1470555 2207333 := bbase (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) (by norm_num)
theorem B3722861 : Blo 1470555 3722861 := bbase (se 3 (by rfl) ⟨698036, by rfl⟩ : syracuseStep 3722861 = 1396073) (by norm_num)
theorem B3534445 : Blo 1470555 3534445 := bbase (se 3 (by rfl) ⟨662708, by rfl⟩ : syracuseStep 3534445 = 1325417) (by norm_num)
theorem B4968053 : Blo 1470555 4968053 := bbase (se 5 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 4968053 = 465755) (by norm_num)
theorem B2207357 : Blo 1470555 2207357 := bbase (se 3 (by rfl) ⟨413879, by rfl⟩ : syracuseStep 2207357 = 827759) (by norm_num)
theorem B2207381 : Blo 1470555 2207381 := bbase (se 6 (by rfl) ⟨51735, by rfl⟩ : syracuseStep 2207381 = 103471) (by norm_num)
theorem B2207405 : Blo 1470555 2207405 := bbase (se 3 (by rfl) ⟨413888, by rfl⟩ : syracuseStep 2207405 = 827777) (by norm_num)
theorem B3976901 : Blo 1470555 3976901 := bbase (se 4 (by rfl) ⟨372834, by rfl⟩ : syracuseStep 3976901 = 745669) (by norm_num)
theorem B2207429 : Blo 1470555 2207429 := bbase (se 4 (by rfl) ⟨206946, by rfl⟩ : syracuseStep 2207429 = 413893) (by norm_num)
theorem B2207453 : Blo 1470555 2207453 := bbase (se 3 (by rfl) ⟨413897, by rfl⟩ : syracuseStep 2207453 = 827795) (by norm_num)
theorem B5967589 : Blo 1470555 5967589 := bbase (se 4 (by rfl) ⟨559461, by rfl⟩ : syracuseStep 5967589 = 1118923) (by norm_num)
theorem B2207477 : Blo 1470555 2207477 := bbase (se 5 (by rfl) ⟨103475, by rfl⟩ : syracuseStep 2207477 = 206951) (by norm_num)
theorem B1863425 : Blo 1470555 1863425 := bbase (se 2 (by rfl) ⟨698784, by rfl⟩ : syracuseStep 1863425 = 1397569) (by norm_num)
theorem B2207501 : Blo 1470555 2207501 := bbase (se 3 (by rfl) ⟨413906, by rfl⟩ : syracuseStep 2207501 = 827813) (by norm_num)
theorem B3141413 : Blo 1470555 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B2207525 : Blo 1470555 2207525 := bbase (se 4 (by rfl) ⟨206955, by rfl⟩ : syracuseStep 2207525 = 413911) (by norm_num)
theorem B1863481 : Blo 1470555 1863481 := bbase (se 2 (by rfl) ⟨698805, by rfl⟩ : syracuseStep 1863481 = 1397611) (by norm_num)
theorem B2207549 : Blo 1470555 2207549 := bbase (se 3 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 2207549 = 827831) (by norm_num)
theorem B5590853 : Blo 1470555 5590853 := bbase (se 4 (by rfl) ⟨524142, by rfl⟩ : syracuseStep 5590853 = 1048285) (by norm_num)
theorem B5304149 : Blo 1470555 5304149 := bbase (se 9 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 5304149 = 31079) (by norm_num)
theorem B2207573 : Blo 1470555 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B2207597 : Blo 1470555 2207597 := bbase (se 3 (by rfl) ⟨413924, by rfl⟩ : syracuseStep 2207597 = 827849) (by norm_num)
theorem B2207621 : Blo 1470555 2207621 := bbase (se 4 (by rfl) ⟨206964, by rfl⟩ : syracuseStep 2207621 = 413929) (by norm_num)
theorem B1863577 : Blo 1470555 1863577 := bbase (se 2 (by rfl) ⟨698841, by rfl⟩ : syracuseStep 1863577 = 1397683) (by norm_num)
theorem B2207645 : Blo 1470555 2207645 := bbase (se 3 (by rfl) ⟨413933, by rfl⟩ : syracuseStep 2207645 = 827867) (by norm_num)
theorem B2207669 : Blo 1470555 2207669 := bbase (se 5 (by rfl) ⟨103484, by rfl⟩ : syracuseStep 2207669 = 206969) (by norm_num)
theorem B3723205 : Blo 1470555 3723205 := bbase (se 4 (by rfl) ⟨349050, by rfl⟩ : syracuseStep 3723205 = 698101) (by norm_num)
theorem B2207693 : Blo 1470555 2207693 := bbase (se 3 (by rfl) ⟨413942, by rfl⟩ : syracuseStep 2207693 = 827885) (by norm_num)
theorem B2207717 : Blo 1470555 2207717 := bbase (se 4 (by rfl) ⟨206973, by rfl⟩ : syracuseStep 2207717 = 413947) (by norm_num)
theorem B2207741 : Blo 1470555 2207741 := bbase (se 3 (by rfl) ⟨413951, by rfl⟩ : syracuseStep 2207741 = 827903) (by norm_num)
theorem B2207765 : Blo 1470555 2207765 := bbase (se 6 (by rfl) ⟨51744, by rfl⟩ : syracuseStep 2207765 = 103489) (by norm_num)
theorem B4968485 : Blo 1470555 4968485 := bbase (se 4 (by rfl) ⟨465795, by rfl⟩ : syracuseStep 4968485 = 931591) (by norm_num)
theorem B2207789 : Blo 1470555 2207789 := bbase (se 3 (by rfl) ⟨413960, by rfl⟩ : syracuseStep 2207789 = 827921) (by norm_num)
theorem B3723317 : Blo 1470555 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B2207813 : Blo 1470555 2207813 := bbase (se 4 (by rfl) ⟨206982, by rfl⟩ : syracuseStep 2207813 = 413965) (by norm_num)
theorem B2207837 : Blo 1470555 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B5820517 : Blo 1470555 5820517 := bbase (se 4 (by rfl) ⟨545673, by rfl⟩ : syracuseStep 5820517 = 1091347) (by norm_num)
theorem B2650229 : Blo 1470555 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B5304437 : Blo 1470555 5304437 := bbase (se 5 (by rfl) ⟨248645, by rfl⟩ : syracuseStep 5304437 = 497291) (by norm_num)
theorem B2207861 : Blo 1470555 2207861 := bbase (se 5 (by rfl) ⟨103493, by rfl⟩ : syracuseStep 2207861 = 206987) (by norm_num)
theorem B2207885 : Blo 1470555 2207885 := bbase (se 3 (by rfl) ⟨413978, by rfl⟩ : syracuseStep 2207885 = 827957) (by norm_num)
theorem B2207909 : Blo 1470555 2207909 := bbase (se 4 (by rfl) ⟨206991, by rfl⟩ : syracuseStep 2207909 = 413983) (by norm_num)
theorem B2207933 : Blo 1470555 2207933 := bbase (se 3 (by rfl) ⟨413987, by rfl⟩ : syracuseStep 2207933 = 827975) (by norm_num)
theorem B6287557 : Blo 1470555 6287557 := bbase (se 4 (by rfl) ⟨589458, by rfl⟩ : syracuseStep 6287557 = 1178917) (by norm_num)
theorem B35778773 : Blo 1470555 35778773 := bbase (se 7 (by rfl) ⟨419282, by rfl⟩ : syracuseStep 35778773 = 838565) (by norm_num)
theorem B2207957 : Blo 1470555 2207957 := bbase (se 7 (by rfl) ⟨25874, by rfl⟩ : syracuseStep 2207957 = 51749) (by norm_num)
theorem B2207981 : Blo 1470555 2207981 := bbase (se 3 (by rfl) ⟨413996, by rfl⟩ : syracuseStep 2207981 = 827993) (by norm_num)
theorem B3723509 : Blo 1470555 3723509 := bbase (se 5 (by rfl) ⟨174539, by rfl⟩ : syracuseStep 3723509 = 349079) (by norm_num)
theorem B2208005 : Blo 1470555 2208005 := bbase (se 4 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 2208005 = 414001) (by norm_num)
theorem B1913101 : Blo 1470555 1913101 := bbase (se 3 (by rfl) ⟨358706, by rfl⟩ : syracuseStep 1913101 = 717413) (by norm_num)
theorem B2208029 : Blo 1470555 2208029 := bbase (se 3 (by rfl) ⟨414005, by rfl⟩ : syracuseStep 2208029 = 828011) (by norm_num)
theorem B2208053 : Blo 1470555 2208053 := bbase (se 5 (by rfl) ⟨103502, by rfl⟩ : syracuseStep 2208053 = 207005) (by norm_num)
theorem B2208077 : Blo 1470555 2208077 := bbase (se 3 (by rfl) ⟨414014, by rfl⟩ : syracuseStep 2208077 = 828029) (by norm_num)
theorem B2208101 : Blo 1470555 2208101 := bbase (se 4 (by rfl) ⟨207009, by rfl⟩ : syracuseStep 2208101 = 414019) (by norm_num)
theorem B2208125 : Blo 1470555 2208125 := bbase (se 3 (by rfl) ⟨414023, by rfl⟩ : syracuseStep 2208125 = 828047) (by norm_num)
theorem B2208149 : Blo 1470555 2208149 := bbase (se 6 (by rfl) ⟨51753, by rfl⟩ : syracuseStep 2208149 = 103507) (by norm_num)
theorem B12751253 : Blo 1470555 12751253 := bbase (se 6 (by rfl) ⟨298857, by rfl⟩ : syracuseStep 12751253 = 597715) (by norm_num)
theorem B2208173 : Blo 1470555 2208173 := bbase (se 3 (by rfl) ⟨414032, by rfl⟩ : syracuseStep 2208173 = 828065) (by norm_num)
theorem B2208197 : Blo 1470555 2208197 := bbase (se 4 (by rfl) ⟨207018, by rfl⟩ : syracuseStep 2208197 = 414037) (by norm_num)
theorem B4968917 : Blo 1470555 4968917 := bbase (se 7 (by rfl) ⟨58229, by rfl⟩ : syracuseStep 4968917 = 116459) (by norm_num)
theorem B2208221 : Blo 1470555 2208221 := bbase (se 3 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 2208221 = 828083) (by norm_num)
theorem B3355109 : Blo 1470555 3355109 := bbase (se 4 (by rfl) ⟨314541, by rfl⟩ : syracuseStep 3355109 = 629083) (by norm_num)
theorem B11178485 : Blo 1470555 11178485 := bbase (se 5 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 11178485 = 1047983) (by norm_num)
theorem B2208245 : Blo 1470555 2208245 := bbase (se 5 (by rfl) ⟨103511, by rfl⟩ : syracuseStep 2208245 = 207023) (by norm_num)
theorem B2208269 : Blo 1470555 2208269 := bbase (se 3 (by rfl) ⟨414050, by rfl⟩ : syracuseStep 2208269 = 828101) (by norm_num)
theorem B2355733 : Blo 1470555 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B3142165 : Blo 1470555 3142165 := bbase (se 6 (by rfl) ⟨73644, by rfl⟩ : syracuseStep 3142165 = 147289) (by norm_num)
theorem B2208293 : Blo 1470555 2208293 := bbase (se 4 (by rfl) ⟨207027, by rfl⟩ : syracuseStep 2208293 = 414055) (by norm_num)
theorem B7451189 : Blo 1470555 7451189 := bbase (se 5 (by rfl) ⟨349274, by rfl⟩ : syracuseStep 7451189 = 698549) (by norm_num)
theorem B2208317 : Blo 1470555 2208317 := bbase (se 3 (by rfl) ⟨414059, by rfl⟩ : syracuseStep 2208317 = 828119) (by norm_num)
theorem B3723853 : Blo 1470555 3723853 := bbase (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) (by norm_num)
theorem B2208341 : Blo 1470555 2208341 := bbase (se 8 (by rfl) ⟨12939, by rfl⟩ : syracuseStep 2208341 = 25879) (by norm_num)
theorem B2208365 : Blo 1470555 2208365 := bbase (se 3 (by rfl) ⟨414068, by rfl⟩ : syracuseStep 2208365 = 828137) (by norm_num)
theorem B2208389 : Blo 1470555 2208389 := bbase (se 4 (by rfl) ⟨207036, by rfl⟩ : syracuseStep 2208389 = 414073) (by norm_num)
theorem B2208413 : Blo 1470555 2208413 := bbase (se 3 (by rfl) ⟨414077, by rfl⟩ : syracuseStep 2208413 = 828155) (by norm_num)
theorem B3142309 : Blo 1470555 3142309 := bbase (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) (by norm_num)
theorem B4190885 : Blo 1470555 4190885 := bbase (se 4 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 4190885 = 785791) (by norm_num)
theorem B6460085 : Blo 1470555 6460085 := bbase (se 5 (by rfl) ⟨302816, by rfl⟩ : syracuseStep 6460085 = 605633) (by norm_num)
theorem B2208437 : Blo 1470555 2208437 := bbase (se 5 (by rfl) ⟨103520, by rfl⟩ : syracuseStep 2208437 = 207041) (by norm_num)
theorem B10613429 : Blo 1470555 10613429 := bbase (se 5 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 10613429 = 995009) (by norm_num)
theorem B3723965 : Blo 1470555 3723965 := bbase (se 3 (by rfl) ⟨698243, by rfl⟩ : syracuseStep 3723965 = 1396487) (by norm_num)
theorem B2208461 : Blo 1470555 2208461 := bbase (se 3 (by rfl) ⟨414086, by rfl⟩ : syracuseStep 2208461 = 828173) (by norm_num)
theorem B2208485 : Blo 1470555 2208485 := bbase (se 4 (by rfl) ⟨207045, by rfl⟩ : syracuseStep 2208485 = 414091) (by norm_num)
theorem B2208509 : Blo 1470555 2208509 := bbase (se 3 (by rfl) ⟨414095, by rfl⟩ : syracuseStep 2208509 = 828191) (by norm_num)
theorem B12563221 : Blo 1470555 12563221 := bbase (se 6 (by rfl) ⟨294450, by rfl⟩ : syracuseStep 12563221 = 588901) (by norm_num)
theorem B2208533 : Blo 1470555 2208533 := bbase (se 6 (by rfl) ⟨51762, by rfl⟩ : syracuseStep 2208533 = 103525) (by norm_num)
theorem B6370085 : Blo 1470555 6370085 := bbase (se 4 (by rfl) ⟨597195, by rfl⟩ : syracuseStep 6370085 = 1194391) (by norm_num)
theorem B2208557 : Blo 1470555 2208557 := bbase (se 3 (by rfl) ⟨414104, by rfl⟩ : syracuseStep 2208557 = 828209) (by norm_num)
theorem B4723525 : Blo 1470555 4723525 := bbase (se 4 (by rfl) ⟨442830, by rfl⟩ : syracuseStep 4723525 = 885661) (by norm_num)
theorem B2208581 : Blo 1470555 2208581 := bbase (se 4 (by rfl) ⟨207054, by rfl⟩ : syracuseStep 2208581 = 414109) (by norm_num)
theorem B2208605 : Blo 1470555 2208605 := bbase (se 3 (by rfl) ⟨414113, by rfl⟩ : syracuseStep 2208605 = 828227) (by norm_num)
theorem B2208629 : Blo 1470555 2208629 := bbase (se 5 (by rfl) ⟨103529, by rfl⟩ : syracuseStep 2208629 = 207059) (by norm_num)
theorem B3724157 : Blo 1470555 3724157 := bbase (se 3 (by rfl) ⟨698279, by rfl⟩ : syracuseStep 3724157 = 1396559) (by norm_num)
theorem B4969349 : Blo 1470555 4969349 := bbase (se 4 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 4969349 = 931753) (by norm_num)
theorem B2208653 : Blo 1470555 2208653 := bbase (se 3 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 2208653 = 828245) (by norm_num)
theorem B11170709 : Blo 1470555 11170709 := bbase (se 6 (by rfl) ⟨261813, by rfl⟩ : syracuseStep 11170709 = 523627) (by norm_num)
theorem B6288293 : Blo 1470555 6288293 := bbase (se 4 (by rfl) ⟨589527, by rfl⟩ : syracuseStep 6288293 = 1179055) (by norm_num)
theorem B2208677 : Blo 1470555 2208677 := bbase (se 4 (by rfl) ⟨207063, by rfl⟩ : syracuseStep 2208677 = 414127) (by norm_num)
theorem B2208701 : Blo 1470555 2208701 := bbase (se 3 (by rfl) ⟨414131, by rfl⟩ : syracuseStep 2208701 = 828263) (by norm_num)
theorem B3535829 : Blo 1470555 3535829 := bbase (se 7 (by rfl) ⟨41435, by rfl⟩ : syracuseStep 3535829 = 82871) (by norm_num)
theorem B3978197 : Blo 1470555 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B5305301 : Blo 1470555 5305301 := bbase (se 7 (by rfl) ⟨62171, by rfl⟩ : syracuseStep 5305301 = 124343) (by norm_num)
theorem B2208725 : Blo 1470555 2208725 := bbase (se 7 (by rfl) ⟨25883, by rfl⟩ : syracuseStep 2208725 = 51767) (by norm_num)
theorem B2208749 : Blo 1470555 2208749 := bbase (se 3 (by rfl) ⟨414140, by rfl⟩ : syracuseStep 2208749 = 828281) (by norm_num)
theorem B2208773 : Blo 1470555 2208773 := bbase (se 4 (by rfl) ⟨207072, by rfl⟩ : syracuseStep 2208773 = 414145) (by norm_num)
theorem B3142685 : Blo 1470555 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B2208797 : Blo 1470555 2208797 := bbase (se 3 (by rfl) ⟨414149, by rfl⟩ : syracuseStep 2208797 = 828299) (by norm_num)
theorem B2208821 : Blo 1470555 2208821 := bbase (se 5 (by rfl) ⟨103538, by rfl⟩ : syracuseStep 2208821 = 207077) (by norm_num)
theorem B1791041 : Blo 1470555 1791041 := bbase (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) (by norm_num)
theorem B5968981 : Blo 1470555 5968981 := bbase (se 8 (by rfl) ⟨34974, by rfl⟩ : syracuseStep 5968981 = 69949) (by norm_num)
theorem B3536021 : Blo 1470555 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B3724501 : Blo 1470555 3724501 := bbase (se 7 (by rfl) ⟨43646, by rfl⟩ : syracuseStep 3724501 = 87293) (by norm_num)
theorem B2094349 : Blo 1470555 2094349 := bbase (se 3 (by rfl) ⟨392690, by rfl⟩ : syracuseStep 2094349 = 785381) (by norm_num)
theorem B4969781 : Blo 1470555 4969781 := bbase (se 5 (by rfl) ⟨232958, by rfl⟩ : syracuseStep 4969781 = 465917) (by norm_num)
theorem B3724613 : Blo 1470555 3724613 := bbase (se 4 (by rfl) ⟨349182, by rfl⟩ : syracuseStep 3724613 = 698365) (by norm_num)
theorem B5584261 : Blo 1470555 5584261 := bbase (se 4 (by rfl) ⟨523524, by rfl⟩ : syracuseStep 5584261 = 1047049) (by norm_num)
theorem B3143053 : Blo 1470555 3143053 := bbase (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) (by norm_num)
theorem B3356093 : Blo 1470555 3356093 := bbase (se 3 (by rfl) ⟨629267, by rfl⟩ : syracuseStep 3356093 = 1258535) (by norm_num)
theorem B1766857 : Blo 1470555 1766857 := bbase (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) (by norm_num)
theorem B3724805 : Blo 1470555 3724805 := bbase (se 4 (by rfl) ⟨349200, by rfl⟩ : syracuseStep 3724805 = 698401) (by norm_num)
theorem B4716053 : Blo 1470555 4716053 := bbase (se 6 (by rfl) ⟨110532, by rfl⟩ : syracuseStep 4716053 = 221065) (by norm_num)
theorem B5305877 : Blo 1470555 5305877 := bbase (se 6 (by rfl) ⟨124356, by rfl⟩ : syracuseStep 5305877 = 248713) (by norm_num)
theorem B7075349 : Blo 1470555 7075349 := bbase (se 6 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 7075349 = 331657) (by norm_num)
theorem B1570433 : Blo 1470555 1570433 := bbase (se 2 (by rfl) ⟨588912, by rfl⟩ : syracuseStep 1570433 = 1177825) (by norm_num)
theorem B5584565 : Blo 1470555 5584565 := bbase (se 5 (by rfl) ⟨261776, by rfl⟩ : syracuseStep 5584565 = 523553) (by norm_num)
theorem B10065653 : Blo 1470555 10065653 := bbase (se 5 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 10065653 = 943655) (by norm_num)
theorem B8386325 : Blo 1470555 8386325 := bbase (se 6 (by rfl) ⟨196554, by rfl⟩ : syracuseStep 8386325 = 393109) (by norm_num)
theorem B7452485 : Blo 1470555 7452485 := bbase (se 4 (by rfl) ⟨698670, by rfl⟩ : syracuseStep 7452485 = 1397341) (by norm_num)
theorem B4192069 : Blo 1470555 4192069 := bbase (se 4 (by rfl) ⟨393006, by rfl⟩ : syracuseStep 4192069 = 786013) (by norm_num)
theorem B3774293 : Blo 1470555 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B2094941 : Blo 1470555 2094941 := bbase (se 3 (by rfl) ⟨392801, by rfl⟩ : syracuseStep 2094941 = 785603) (by norm_num)
theorem B3725149 : Blo 1470555 3725149 := bbase (se 3 (by rfl) ⟨698465, by rfl⟩ : syracuseStep 3725149 = 1396931) (by norm_num)
theorem B2357117 : Blo 1470555 2357117 := bbase (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) (by norm_num)
theorem B8378261 : Blo 1470555 8378261 := bbase (se 6 (by rfl) ⟨196365, by rfl⟩ : syracuseStep 8378261 = 392731) (by norm_num)
theorem B3536789 : Blo 1470555 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B2095021 : Blo 1470555 2095021 := bbase (se 3 (by rfl) ⟨392816, by rfl⟩ : syracuseStep 2095021 = 785633) (by norm_num)
theorem B3725261 : Blo 1470555 3725261 := bbase (se 3 (by rfl) ⟨698486, by rfl⟩ : syracuseStep 3725261 = 1396973) (by norm_num)
theorem B4192229 : Blo 1470555 4192229 := bbase (se 4 (by rfl) ⟨393021, by rfl⟩ : syracuseStep 4192229 = 786043) (by norm_num)
theorem B2095141 : Blo 1470555 2095141 := bbase (se 4 (by rfl) ⟨196419, by rfl⟩ : syracuseStep 2095141 = 392839) (by norm_num)
theorem B1677353 : Blo 1470555 1677353 := bbase (se 2 (by rfl) ⟨629007, by rfl⟩ : syracuseStep 1677353 = 1258015) (by norm_num)
theorem B2357309 : Blo 1470555 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B2095237 : Blo 1470555 2095237 := bbase (se 4 (by rfl) ⟨196428, by rfl⟩ : syracuseStep 2095237 = 392857) (by norm_num)
theorem B3725453 : Blo 1470555 3725453 := bbase (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) (by norm_num)
theorem B4192469 : Blo 1470555 4192469 := bbase (se 7 (by rfl) ⟨49130, by rfl⟩ : syracuseStep 4192469 = 98261) (by norm_num)
theorem B7444709 : Blo 1470555 7444709 := bbase (se 4 (by rfl) ⟨697941, by rfl⟩ : syracuseStep 7444709 = 1395883) (by norm_num)
theorem B1988893 : Blo 1470555 1988893 := bbase (se 3 (by rfl) ⟨372917, by rfl⟩ : syracuseStep 1988893 = 745835) (by norm_num)
theorem B6281509 : Blo 1470555 6281509 := bbase (se 4 (by rfl) ⟨588891, by rfl⟩ : syracuseStep 6281509 = 1177783) (by norm_num)
theorem B188627285 : Blo 1470555 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B1571185 : Blo 1470555 1571185 := bbase (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) (by norm_num)
theorem B4192661 : Blo 1470555 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B4716949 : Blo 1470555 4716949 := bbase (se 6 (by rfl) ⟨110553, by rfl⟩ : syracuseStep 4716949 = 221107) (by norm_num)
theorem B1571257 : Blo 1470555 1571257 := bbase (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) (by norm_num)
theorem B3725797 : Blo 1470555 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B7068197 : Blo 1470555 7068197 := bbase (se 4 (by rfl) ⟨662643, by rfl⟩ : syracuseStep 7068197 = 1325287) (by norm_num)
theorem B3725909 : Blo 1470555 3725909 := bbase (se 8 (by rfl) ⟨21831, by rfl⟩ : syracuseStep 3725909 = 43663) (by norm_num)
theorem B1571437 : Blo 1470555 1571437 := bbase (se 3 (by rfl) ⟨294644, by rfl⟩ : syracuseStep 1571437 = 589289) (by norm_num)
theorem B2095733 : Blo 1470555 2095733 := bbase (se 5 (by rfl) ⟨98237, by rfl⟩ : syracuseStep 2095733 = 196475) (by norm_num)
theorem B3775133 : Blo 1470555 3775133 := bbase (se 3 (by rfl) ⟨707837, by rfl⟩ : syracuseStep 3775133 = 1415675) (by norm_num)
theorem B12565205 : Blo 1470555 12565205 := bbase (se 7 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 12565205 = 294497) (by norm_num)
theorem B3726101 : Blo 1470555 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B4717349 : Blo 1470555 4717349 := bbase (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) (by norm_num)
theorem B1768241 : Blo 1470555 1768241 := bbase (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) (by norm_num)
theorem B2792245 : Blo 1470555 2792245 := bbase (se 5 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 2792245 = 261773) (by norm_num)
theorem B3144557 : Blo 1470555 3144557 := bbase (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) (by norm_num)
theorem B7650229 : Blo 1470555 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B2792389 : Blo 1470555 2792389 := bbase (se 4 (by rfl) ⟨261786, by rfl⟩ : syracuseStep 2792389 = 523573) (by norm_num)
theorem B4963301 : Blo 1470555 4963301 := bbase (se 4 (by rfl) ⟨465309, by rfl⟩ : syracuseStep 4963301 = 930619) (by norm_num)
theorem B1768429 : Blo 1470555 1768429 := bbase (se 3 (by rfl) ⟨331580, by rfl⟩ : syracuseStep 1768429 = 663161) (by norm_num)
theorem B3144701 : Blo 1470555 3144701 := bbase (se 3 (by rfl) ⟨589631, by rfl⟩ : syracuseStep 3144701 = 1179263) (by norm_num)
theorem B1571881 : Blo 1470555 1571881 := bbase (se 2 (by rfl) ⟨589455, by rfl⟩ : syracuseStep 1571881 = 1178911) (by norm_num)
theorem B4471861 : Blo 1470555 4471861 := bbase (se 5 (by rfl) ⟨209618, by rfl⟩ : syracuseStep 4471861 = 419237) (by norm_num)
theorem B1678421 : Blo 1470555 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B7453781 : Blo 1470555 7453781 := bbase (se 8 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 7453781 = 87349) (by norm_num)
theorem B2792549 : Blo 1470555 2792549 := bbase (se 4 (by rfl) ⟨261801, by rfl⟩ : syracuseStep 2792549 = 523603) (by norm_num)
theorem B3726445 : Blo 1470555 3726445 := bbase (se 3 (by rfl) ⟨698708, by rfl⟩ : syracuseStep 3726445 = 1397417) (by norm_num)
theorem B2096285 : Blo 1470555 2096285 := bbase (se 3 (by rfl) ⟨393053, by rfl⟩ : syracuseStep 2096285 = 786107) (by norm_num)
theorem B1572005 : Blo 1470555 1572005 := bbase (se 4 (by rfl) ⟨147375, by rfl⟩ : syracuseStep 1572005 = 294751) (by norm_num)
theorem B1768645 : Blo 1470555 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B3726557 : Blo 1470555 3726557 := bbase (se 3 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 3726557 = 1397459) (by norm_num)
theorem B2792693 : Blo 1470555 2792693 := bbase (se 5 (by rfl) ⟨130907, by rfl⟩ : syracuseStep 2792693 = 261815) (by norm_num)
theorem B3308813 : Blo 1470555 3308813 := bbase (se 3 (by rfl) ⟨620402, by rfl⟩ : syracuseStep 3308813 = 1240805) (by norm_num)
theorem B1678649 : Blo 1470555 1678649 := bbase (se 2 (by rfl) ⟨629493, by rfl⟩ : syracuseStep 1678649 = 1258987) (by norm_num)
theorem B2686285 : Blo 1470555 2686285 := bbase (se 3 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 2686285 = 1007357) (by norm_num)
theorem B3308885 : Blo 1470555 3308885 := bbase (se 11 (by rfl) ⟨2423, by rfl⟩ : syracuseStep 3308885 = 4847) (by norm_num)
theorem B4472165 : Blo 1470555 4472165 := bbase (se 4 (by rfl) ⟨419265, by rfl⟩ : syracuseStep 4472165 = 838531) (by norm_num)
theorem B2358629 : Blo 1470555 2358629 := bbase (se 4 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 2358629 = 442243) (by norm_num)
theorem B2653573 : Blo 1470555 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B4963733 : Blo 1470555 4963733 := bbase (se 6 (by rfl) ⟨116337, by rfl⟩ : syracuseStep 4963733 = 232675) (by norm_num)
theorem B3308957 : Blo 1470555 3308957 := bbase (se 3 (by rfl) ⟨620429, by rfl⟩ : syracuseStep 3308957 = 1240859) (by norm_num)
theorem B3726749 : Blo 1470555 3726749 := bbase (se 3 (by rfl) ⟨698765, by rfl⟩ : syracuseStep 3726749 = 1397531) (by norm_num)
theorem B1572257 : Blo 1470555 1572257 := bbase (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) (by norm_num)
theorem B3186101 : Blo 1470555 3186101 := bbase (se 5 (by rfl) ⟨149348, by rfl⟩ : syracuseStep 3186101 = 298697) (by norm_num)
theorem B3775933 : Blo 1470555 3775933 := bbase (se 3 (by rfl) ⟨707987, by rfl⟩ : syracuseStep 3775933 = 1415975) (by norm_num)
theorem B2358725 : Blo 1470555 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B2481637 : Blo 1470555 2481637 := bbase (se 4 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 2481637 = 465307) (by norm_num)
theorem B3309029 : Blo 1470555 3309029 := bbase (se 4 (by rfl) ⟨310221, by rfl⟩ : syracuseStep 3309029 = 620443) (by norm_num)
theorem B1768933 : Blo 1470555 1768933 := bbase (se 4 (by rfl) ⟨165837, by rfl⟩ : syracuseStep 1768933 = 331675) (by norm_num)
theorem B4472309 : Blo 1470555 4472309 := bbase (se 5 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 4472309 = 419279) (by norm_num)
theorem B7446005 : Blo 1470555 7446005 := bbase (se 5 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 7446005 = 698063) (by norm_num)
theorem B2792981 : Blo 1470555 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B3309101 : Blo 1470555 3309101 := bbase (se 3 (by rfl) ⟨620456, by rfl⟩ : syracuseStep 3309101 = 1240913) (by norm_num)
theorem B2481725 : Blo 1470555 2481725 := bbase (se 3 (by rfl) ⟨465323, by rfl⟩ : syracuseStep 2481725 = 930647) (by norm_num)
theorem B3309173 : Blo 1470555 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B1654393 : Blo 1470555 1654393 := bbase (se 2 (by rfl) ⟨620397, by rfl⟩ : syracuseStep 1654393 = 1240795) (by norm_num)
theorem B1654429 : Blo 1470555 1654429 := bbase (se 3 (by rfl) ⟨310205, by rfl⟩ : syracuseStep 1654429 = 620411) (by norm_num)
theorem B1679005 : Blo 1470555 1679005 := bbase (se 3 (by rfl) ⟨314813, by rfl⟩ : syracuseStep 1679005 = 629627) (by norm_num)
theorem B2793133 : Blo 1470555 2793133 := bbase (se 3 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 2793133 = 1047425) (by norm_num)
theorem B2481853 : Blo 1470555 2481853 := bbase (se 3 (by rfl) ⟨465347, by rfl⟩ : syracuseStep 2481853 = 930695) (by norm_num)
theorem B3309245 : Blo 1470555 3309245 := bbase (se 3 (by rfl) ⟨620483, by rfl⟩ : syracuseStep 3309245 = 1240967) (by norm_num)
theorem B1654465 : Blo 1470555 1654465 := bbase (se 2 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 1654465 = 1240849) (by norm_num)
theorem B1654501 : Blo 1470555 1654501 := bbase (se 4 (by rfl) ⟨155109, by rfl⟩ : syracuseStep 1654501 = 310219) (by norm_num)
theorem B5586677 : Blo 1470555 5586677 := bbase (se 5 (by rfl) ⟨261875, by rfl⟩ : syracuseStep 5586677 = 523751) (by norm_num)
theorem B3727093 : Blo 1470555 3727093 := bbase (se 5 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 3727093 = 349415) (by norm_num)
theorem B3309317 : Blo 1470555 3309317 := bbase (se 4 (by rfl) ⟨310248, by rfl⟩ : syracuseStep 3309317 = 620497) (by norm_num)
theorem B1654537 : Blo 1470555 1654537 := bbase (se 2 (by rfl) ⟨620451, by rfl⟩ : syracuseStep 1654537 = 1240903) (by norm_num)
theorem B2481941 : Blo 1470555 2481941 := bbase (se 6 (by rfl) ⟨58170, by rfl⟩ : syracuseStep 2481941 = 116341) (by norm_num)
theorem B6045461 : Blo 1470555 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B1654573 : Blo 1470555 1654573 := bbase (se 3 (by rfl) ⟨310232, by rfl⟩ : syracuseStep 1654573 = 620465) (by norm_num)
theorem B4964165 : Blo 1470555 4964165 := bbase (se 4 (by rfl) ⟨465390, by rfl⟩ : syracuseStep 4964165 = 930781) (by norm_num)
theorem B3309389 : Blo 1470555 3309389 := bbase (se 3 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 3309389 = 1241021) (by norm_num)
theorem B1654609 : Blo 1470555 1654609 := bbase (se 2 (by rfl) ⟨620478, by rfl⟩ : syracuseStep 1654609 = 1240957) (by norm_num)
theorem B2236253 : Blo 1470555 2236253 := bbase (se 3 (by rfl) ⟨419297, by rfl⟩ : syracuseStep 2236253 = 838595) (by norm_num)
theorem B3727205 : Blo 1470555 3727205 := bbase (se 4 (by rfl) ⟨349425, by rfl⟩ : syracuseStep 3727205 = 698851) (by norm_num)
theorem B1654645 : Blo 1470555 1654645 := bbase (se 5 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 1654645 = 155123) (by norm_num)
theorem B2482069 : Blo 1470555 2482069 := bbase (se 6 (by rfl) ⟨58173, by rfl⟩ : syracuseStep 2482069 = 116347) (by norm_num)
theorem B3309461 : Blo 1470555 3309461 := bbase (se 6 (by rfl) ⟨77565, by rfl⟩ : syracuseStep 3309461 = 155131) (by norm_num)
theorem B1654681 : Blo 1470555 1654681 := bbase (se 2 (by rfl) ⟨620505, by rfl⟩ : syracuseStep 1654681 = 1241011) (by norm_num)
theorem B1654717 : Blo 1470555 1654717 := bbase (se 3 (by rfl) ⟨310259, by rfl⟩ : syracuseStep 1654717 = 620519) (by norm_num)
theorem B3309533 : Blo 1470555 3309533 := bbase (se 3 (by rfl) ⟨620537, by rfl⟩ : syracuseStep 3309533 = 1241075) (by norm_num)
theorem B2793437 : Blo 1470555 2793437 := bbase (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) (by norm_num)
theorem B1654753 : Blo 1470555 1654753 := bbase (se 2 (by rfl) ⟨620532, by rfl⟩ : syracuseStep 1654753 = 1241065) (by norm_num)
theorem B2482157 : Blo 1470555 2482157 := bbase (se 3 (by rfl) ⟨465404, by rfl⟩ : syracuseStep 2482157 = 930809) (by norm_num)
theorem B2482177 : Blo 1470555 2482177 := bstep (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) B1861633
theorem B2482211 : Blo 1470555 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B2793521 : Blo 1470555 2793521 := bstep (se 2 (by rfl) ⟨1047570, by rfl⟩ : syracuseStep 2793521 = 2095141) B2095141
theorem B8380493 : Blo 1470555 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B1654915 : Blo 1470555 1654915 := bstep (se 1 (by rfl) ⟨1241186, by rfl⟩ : syracuseStep 1654915 = 2482373) B2482373
theorem B3309713 : Blo 1470555 3309713 := bstep (se 2 (by rfl) ⟨1241142, by rfl⟩ : syracuseStep 3309713 = 2482285) B2482285
theorem B3309731 : Blo 1470555 3309731 := bstep (se 1 (by rfl) ⟨2482298, by rfl⟩ : syracuseStep 3309731 = 4964597) B4964597
theorem B2482339 : Blo 1470555 2482339 := bstep (se 1 (by rfl) ⟨1861754, by rfl⟩ : syracuseStep 2482339 = 3723509) B3723509
theorem B1655059 : Blo 1470555 1655059 := bstep (se 1 (by rfl) ⟨1241294, by rfl⟩ : syracuseStep 1655059 = 2482589) B2482589
theorem B2482481 : Blo 1470555 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B2236739 : Blo 1470555 2236739 := bstep (se 1 (by rfl) ⟨1677554, by rfl⟩ : syracuseStep 2236739 = 3355109) B3355109
theorem B1655203 : Blo 1470555 1655203 := bstep (se 1 (by rfl) ⟨1241402, by rfl⟩ : syracuseStep 1655203 = 2482805) B2482805
theorem B3310001 : Blo 1470555 3310001 := bstep (se 2 (by rfl) ⟨1241250, by rfl⟩ : syracuseStep 3310001 = 2482501) B2482501
theorem B2482609 : Blo 1470555 2482609 := bstep (se 2 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 2482609 = 1861957) B1861957
theorem B17891765 : Blo 1470555 17891765 := bstep (se 5 (by rfl) ⟨838676, by rfl⟩ : syracuseStep 17891765 = 1677353) B1677353
theorem B3310019 : Blo 1470555 3310019 := bstep (se 1 (by rfl) ⟨2482514, by rfl⟩ : syracuseStep 3310019 = 4965029) B4965029
theorem B2793923 : Blo 1470555 2793923 := bstep (se 1 (by rfl) ⟨2095442, by rfl⟩ : syracuseStep 2793923 = 4190885) B4190885
theorem B31834565 : Blo 1470555 31834565 := bstep (se 4 (by rfl) ⟨2984490, by rfl⟩ : syracuseStep 31834565 = 5968981) B5968981
theorem B4964813 : Blo 1470555 4964813 := bstep (se 3 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 4964813 = 1861805) B1861805
theorem B2482643 : Blo 1470555 2482643 := bstep (se 1 (by rfl) ⟨1861982, by rfl⟩ : syracuseStep 2482643 = 3723965) B3723965
theorem B4964867 : Blo 1470555 4964867 := bstep (se 1 (by rfl) ⟨3723650, by rfl⟩ : syracuseStep 4964867 = 7447301) B7447301
theorem B1655347 : Blo 1470555 1655347 := bstep (se 1 (by rfl) ⟨1241510, by rfl⟩ : syracuseStep 1655347 = 2483021) B2483021
theorem B77537845 : Blo 1470555 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B6709837 : Blo 1470555 6709837 := bstep (se 3 (by rfl) ⟨1258094, by rfl⟩ : syracuseStep 6709837 = 2516189) B2516189
theorem B2515537 : Blo 1470555 2515537 := bstep (se 2 (by rfl) ⟨943326, by rfl⟩ : syracuseStep 2515537 = 1886653) B1886653
theorem B2482771 : Blo 1470555 2482771 := bstep (se 1 (by rfl) ⟨1862078, by rfl⟩ : syracuseStep 2482771 = 3724157) B3724157
theorem B7447139 : Blo 1470555 7447139 := bstep (se 1 (by rfl) ⟨5585354, by rfl⟩ : syracuseStep 7447139 = 11170709) B11170709
theorem B19104437 : Blo 1470555 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B1655491 : Blo 1470555 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B11174597 : Blo 1470555 11174597 := bstep (se 4 (by rfl) ⟨1047618, by rfl⟩ : syracuseStep 11174597 = 2095237) B2095237
theorem B3310289 : Blo 1470555 3310289 := bstep (se 2 (by rfl) ⟨1241358, by rfl⟩ : syracuseStep 3310289 = 2482717) B2482717
theorem B2482913 : Blo 1470555 2482913 := bstep (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) B1862185
theorem B3310307 : Blo 1470555 3310307 := bstep (se 1 (by rfl) ⟨2482730, by rfl⟩ : syracuseStep 3310307 = 4965461) B4965461
theorem B4965137 : Blo 1470555 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B1655635 : Blo 1470555 1655635 := bstep (se 1 (by rfl) ⟨1241726, by rfl⟩ : syracuseStep 1655635 = 2483453) B2483453
theorem B2483041 : Blo 1470555 2483041 := bstep (se 2 (by rfl) ⟨931140, by rfl⟩ : syracuseStep 2483041 = 1862281) B1862281
theorem B2483075 : Blo 1470555 2483075 := bstep (se 1 (by rfl) ⟨1862306, by rfl⟩ : syracuseStep 2483075 = 3724613) B3724613
theorem B1655779 : Blo 1470555 1655779 := bstep (se 1 (by rfl) ⟨1241834, by rfl⟩ : syracuseStep 1655779 = 2483669) B2483669
theorem B3310577 : Blo 1470555 3310577 := bstep (se 2 (by rfl) ⟨1241466, by rfl⟩ : syracuseStep 3310577 = 2482933) B2482933
theorem B15918065 : Blo 1470555 15918065 := bstep (se 2 (by rfl) ⟨5969274, by rfl⟩ : syracuseStep 15918065 = 11938549) B11938549
theorem B3310595 : Blo 1470555 3310595 := bstep (se 1 (by rfl) ⟨2482946, by rfl⟩ : syracuseStep 3310595 = 4965893) B4965893
theorem B2483203 : Blo 1470555 2483203 := bstep (se 1 (by rfl) ⟨1862402, by rfl⟩ : syracuseStep 2483203 = 3724805) B3724805
theorem B5661809 : Blo 1470555 5661809 := bstep (se 2 (by rfl) ⟨2123178, by rfl⟩ : syracuseStep 5661809 = 4246357) B4246357
theorem B1655923 : Blo 1470555 1655923 := bstep (se 1 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 1655923 = 2483885) B2483885
theorem B2483345 : Blo 1470555 2483345 := bstep (se 2 (by rfl) ⟨931254, by rfl⟩ : syracuseStep 2483345 = 1862509) B1862509
theorem B6710435 : Blo 1470555 6710435 := bstep (se 1 (by rfl) ⟨5032826, by rfl⟩ : syracuseStep 6710435 = 10065653) B10065653
theorem B2516195 : Blo 1470555 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B10200305 : Blo 1470555 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1656067 : Blo 1470555 1656067 := bstep (se 1 (by rfl) ⟨1242050, by rfl⟩ : syracuseStep 1656067 = 2484101) B2484101
theorem B3310865 : Blo 1470555 3310865 := bstep (se 2 (by rfl) ⟨1241574, by rfl⟩ : syracuseStep 3310865 = 2483149) B2483149
theorem B2483473 : Blo 1470555 2483473 := bstep (se 2 (by rfl) ⟨931302, by rfl⟩ : syracuseStep 2483473 = 1862605) B1862605
theorem B3310883 : Blo 1470555 3310883 := bstep (se 1 (by rfl) ⟨2483162, by rfl⟩ : syracuseStep 3310883 = 4966325) B4966325
theorem B4965677 : Blo 1470555 4965677 := bstep (se 3 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 4965677 = 1862129) B1862129
theorem B2483507 : Blo 1470555 2483507 := bstep (se 1 (by rfl) ⟨1862630, by rfl⟩ : syracuseStep 2483507 = 3725261) B3725261
theorem B2794819 : Blo 1470555 2794819 := bstep (se 1 (by rfl) ⟨2096114, by rfl⟩ : syracuseStep 2794819 = 4192229) B4192229
theorem B5449037 : Blo 1470555 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B4965731 : Blo 1470555 4965731 := bstep (se 1 (by rfl) ⟨3724298, by rfl⟩ : syracuseStep 4965731 = 7448597) B7448597
theorem B7447949 : Blo 1470555 7447949 := bstep (se 3 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 7447949 = 2792981) B2792981
theorem B1656211 : Blo 1470555 1656211 := bstep (se 1 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 1656211 = 2484317) B2484317
theorem B2483635 : Blo 1470555 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B2794979 : Blo 1470555 2794979 := bstep (se 1 (by rfl) ⟨2096234, by rfl⟩ : syracuseStep 2794979 = 4192469) B4192469
theorem B1656355 : Blo 1470555 1656355 := bstep (se 1 (by rfl) ⟨1242266, by rfl⟩ : syracuseStep 1656355 = 2484533) B2484533
theorem B3311153 : Blo 1470555 3311153 := bstep (se 2 (by rfl) ⟨1241682, by rfl⟩ : syracuseStep 3311153 = 2483365) B2483365
theorem B37725749 : Blo 1470555 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B2123329 : Blo 1470555 2123329 := bstep (se 2 (by rfl) ⟨796248, by rfl⟩ : syracuseStep 2123329 = 1592497) B1592497
theorem B3311171 : Blo 1470555 3311171 := bstep (se 1 (by rfl) ⟨2483378, by rfl⟩ : syracuseStep 3311171 = 4966757) B4966757
theorem B2483777 : Blo 1470555 2483777 := bstep (se 2 (by rfl) ⟨931416, by rfl⟩ : syracuseStep 2483777 = 1862833) B1862833
theorem B4966001 : Blo 1470555 4966001 := bstep (se 2 (by rfl) ⟨1862250, by rfl⟩ : syracuseStep 4966001 = 3724501) B3724501
theorem B5588621 : Blo 1470555 5588621 := bstep (se 3 (by rfl) ⟨1047866, by rfl⟩ : syracuseStep 5588621 = 2095733) B2095733
theorem B4187821 : Blo 1470555 4187821 := bstep (se 3 (by rfl) ⟨785216, by rfl⟩ : syracuseStep 4187821 = 1570433) B1570433
theorem B1656499 : Blo 1470555 1656499 := bstep (se 1 (by rfl) ⟨1242374, by rfl⟩ : syracuseStep 1656499 = 2484749) B2484749
theorem B2483905 : Blo 1470555 2483905 := bstep (se 2 (by rfl) ⟨931464, by rfl⟩ : syracuseStep 2483905 = 1862929) B1862929
theorem B4712131 : Blo 1470555 4712131 := bstep (se 1 (by rfl) ⟨3534098, by rfl⟩ : syracuseStep 4712131 = 7068197) B7068197
theorem B25192133 : Blo 1470555 25192133 := bstep (se 4 (by rfl) ⟨2361762, by rfl⟩ : syracuseStep 25192133 = 4723525) B4723525
theorem B2483939 : Blo 1470555 2483939 := bstep (se 1 (by rfl) ⟨1862954, by rfl⟩ : syracuseStep 2483939 = 3725909) B3725909
theorem B3581713 : Blo 1470555 3581713 := bstep (se 2 (by rfl) ⟨1343142, by rfl⟩ : syracuseStep 3581713 = 2686285) B2686285
theorem B2516755 : Blo 1470555 2516755 := bstep (se 1 (by rfl) ⟨1887566, by rfl⟩ : syracuseStep 2516755 = 3775133) B3775133
theorem B3311441 : Blo 1470555 3311441 := bstep (se 2 (by rfl) ⟨1241790, by rfl⟩ : syracuseStep 3311441 = 2483581) B2483581
theorem B3311459 : Blo 1470555 3311459 := bstep (se 1 (by rfl) ⟨2483594, by rfl⟩ : syracuseStep 3311459 = 4967189) B4967189
theorem B2484067 : Blo 1470555 2484067 := bstep (se 1 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 2484067 = 3726101) B3726101
theorem B2484209 : Blo 1470555 2484209 := bstep (se 2 (by rfl) ⟨931578, by rfl⟩ : syracuseStep 2484209 = 1863157) B1863157
theorem B1861699 : Blo 1470555 1861699 := bstep (se 1 (by rfl) ⟨1396274, by rfl⟩ : syracuseStep 1861699 = 2792549) B2792549
theorem B3311729 : Blo 1470555 3311729 := bstep (se 2 (by rfl) ⟨1241898, by rfl⟩ : syracuseStep 3311729 = 2483797) B2483797
theorem B2484337 : Blo 1470555 2484337 := bstep (se 2 (by rfl) ⟨931626, by rfl⟩ : syracuseStep 2484337 = 1863253) B1863253
theorem B3311747 : Blo 1470555 3311747 := bstep (se 1 (by rfl) ⟨2483810, by rfl⟩ : syracuseStep 3311747 = 4967621) B4967621
theorem B4966541 : Blo 1470555 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B4712593 : Blo 1470555 4712593 := bstep (se 2 (by rfl) ⟨1767222, by rfl⟩ : syracuseStep 4712593 = 3534445) B3534445
theorem B2484371 : Blo 1470555 2484371 := bstep (se 1 (by rfl) ⟨1863278, by rfl⟩ : syracuseStep 2484371 = 3726557) B3726557
theorem B2205857 : Blo 1470555 2205857 := bstep (se 2 (by rfl) ⟨827196, by rfl⟩ : syracuseStep 2205857 = 1654393) B1654393
theorem B1861795 : Blo 1470555 1861795 := bstep (se 1 (by rfl) ⟨1396346, by rfl⟩ : syracuseStep 1861795 = 2792693) B2792693
theorem B2205875 : Blo 1470555 2205875 := bstep (se 1 (by rfl) ⟨1654406, by rfl⟩ : syracuseStep 2205875 = 3308813) B3308813
theorem B4966595 : Blo 1470555 4966595 := bstep (se 1 (by rfl) ⟨3724946, by rfl⟩ : syracuseStep 4966595 = 7449893) B7449893
theorem B2205905 : Blo 1470555 2205905 := bstep (se 2 (by rfl) ⟨827214, by rfl⟩ : syracuseStep 2205905 = 1654429) B1654429
theorem B2238673 : Blo 1470555 2238673 := bstep (se 2 (by rfl) ⟨839502, by rfl⟩ : syracuseStep 2238673 = 1679005) B1679005
theorem B2205923 : Blo 1470555 2205923 := bstep (se 1 (by rfl) ⟨1654442, by rfl⟩ : syracuseStep 2205923 = 3308885) B3308885
theorem B2205953 : Blo 1470555 2205953 := bstep (se 2 (by rfl) ⟨827232, by rfl⟩ : syracuseStep 2205953 = 1654465) B1654465
theorem B2205971 : Blo 1470555 2205971 := bstep (se 1 (by rfl) ⟨1654478, by rfl⟩ : syracuseStep 2205971 = 3308957) B3308957
theorem B2484499 : Blo 1470555 2484499 := bstep (se 1 (by rfl) ⟨1863374, by rfl⟩ : syracuseStep 2484499 = 3726749) B3726749
theorem B2124067 : Blo 1470555 2124067 := bstep (se 1 (by rfl) ⟨1593050, by rfl⟩ : syracuseStep 2124067 = 3186101) B3186101
theorem B2206001 : Blo 1470555 2206001 := bstep (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) B1654501
theorem B5966129 : Blo 1470555 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B7956785 : Blo 1470555 7956785 := bstep (se 2 (by rfl) ⟨2983794, by rfl⟩ : syracuseStep 7956785 = 5967589) B5967589
theorem B2206019 : Blo 1470555 2206019 := bstep (se 1 (by rfl) ⟨1654514, by rfl⟩ : syracuseStep 2206019 = 3309029) B3309029
theorem B2206049 : Blo 1470555 2206049 := bstep (se 2 (by rfl) ⟨827268, by rfl⟩ : syracuseStep 2206049 = 1654537) B1654537
theorem B12568931 : Blo 1470555 12568931 := bstep (se 1 (by rfl) ⟨9426698, by rfl⟩ : syracuseStep 12568931 = 18853397) B18853397
theorem B2206067 : Blo 1470555 2206067 := bstep (se 1 (by rfl) ⟨1654550, by rfl⟩ : syracuseStep 2206067 = 3309101) B3309101
theorem B2206097 : Blo 1470555 2206097 := bstep (se 2 (by rfl) ⟨827286, by rfl⟩ : syracuseStep 2206097 = 1654573) B1654573
theorem B3312017 : Blo 1470555 3312017 := bstep (se 2 (by rfl) ⟨1242006, by rfl⟩ : syracuseStep 3312017 = 2484013) B2484013
theorem B2484641 : Blo 1470555 2484641 := bstep (se 2 (by rfl) ⟨931740, by rfl⟩ : syracuseStep 2484641 = 1863481) B1863481
theorem B2206115 : Blo 1470555 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B3312035 : Blo 1470555 3312035 := bstep (se 1 (by rfl) ⟨2484026, by rfl⟩ : syracuseStep 3312035 = 4968053) B4968053
theorem B5589425 : Blo 1470555 5589425 := bstep (se 2 (by rfl) ⟨2096034, by rfl⟩ : syracuseStep 5589425 = 4192069) B4192069
theorem B2206145 : Blo 1470555 2206145 := bstep (se 2 (by rfl) ⟨827304, by rfl⟩ : syracuseStep 2206145 = 1654609) B1654609
theorem B4966865 : Blo 1470555 4966865 := bstep (se 2 (by rfl) ⟨1862574, by rfl⟩ : syracuseStep 4966865 = 3725149) B3725149
theorem B2206163 : Blo 1470555 2206163 := bstep (se 1 (by rfl) ⟨1654622, by rfl⟩ : syracuseStep 2206163 = 3309245) B3309245
theorem B2206193 : Blo 1470555 2206193 := bstep (se 2 (by rfl) ⟨827322, by rfl⟩ : syracuseStep 2206193 = 1654645) B1654645
theorem B2206211 : Blo 1470555 2206211 := bstep (se 1 (by rfl) ⟨1654658, by rfl⟩ : syracuseStep 2206211 = 3309317) B3309317
theorem B2206241 : Blo 1470555 2206241 := bstep (se 2 (by rfl) ⟨827340, by rfl⟩ : syracuseStep 2206241 = 1654681) B1654681
theorem B2484769 : Blo 1470555 2484769 := bstep (se 2 (by rfl) ⟨931788, by rfl⟩ : syracuseStep 2484769 = 1863577) B1863577
theorem B2206259 : Blo 1470555 2206259 := bstep (se 1 (by rfl) ⟨1654694, by rfl⟩ : syracuseStep 2206259 = 3309389) B3309389
theorem B2484803 : Blo 1470555 2484803 := bstep (se 1 (by rfl) ⟨1863602, by rfl⟩ : syracuseStep 2484803 = 3727205) B3727205
theorem B2206289 : Blo 1470555 2206289 := bstep (se 2 (by rfl) ⟨827358, by rfl⟩ : syracuseStep 2206289 = 1654717) B1654717
theorem B2206307 : Blo 1470555 2206307 := bstep (se 1 (by rfl) ⟨1654730, by rfl⟩ : syracuseStep 2206307 = 3309461) B3309461
theorem B2206337 : Blo 1470555 2206337 := bstep (se 2 (by rfl) ⟨827376, by rfl⟩ : syracuseStep 2206337 = 1654753) B1654753
theorem B2206355 : Blo 1470555 2206355 := bstep (se 1 (by rfl) ⟨1654766, by rfl⟩ : syracuseStep 2206355 = 3309533) B3309533
theorem B1862291 : Blo 1470555 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B2206385 : Blo 1470555 2206385 := bstep (se 2 (by rfl) ⟨827394, by rfl⟩ : syracuseStep 2206385 = 1654789) B1654789
theorem B3312305 : Blo 1470555 3312305 := bstep (se 2 (by rfl) ⟨1242114, by rfl⟩ : syracuseStep 3312305 = 2484229) B2484229
theorem B2206403 : Blo 1470555 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B3312323 : Blo 1470555 3312323 := bstep (se 1 (by rfl) ⟨2484242, by rfl⟩ : syracuseStep 3312323 = 4968485) B4968485
theorem B2484931 : Blo 1470555 2484931 := bstep (se 1 (by rfl) ⟨1863698, by rfl⟩ : syracuseStep 2484931 = 3727397) B3727397
theorem B2206433 : Blo 1470555 2206433 := bstep (se 2 (by rfl) ⟨827412, by rfl⟩ : syracuseStep 2206433 = 1654825) B1654825
theorem B4246253 : Blo 1470555 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B2206451 : Blo 1470555 2206451 := bstep (se 1 (by rfl) ⟨1654838, by rfl⟩ : syracuseStep 2206451 = 3309677) B3309677
theorem B2206481 : Blo 1470555 2206481 := bstep (se 2 (by rfl) ⟨827430, by rfl⟩ : syracuseStep 2206481 = 1654861) B1654861
theorem B2206499 : Blo 1470555 2206499 := bstep (se 1 (by rfl) ⟨1654874, by rfl⟩ : syracuseStep 2206499 = 3309749) B3309749
theorem B2206529 : Blo 1470555 2206529 := bstep (se 2 (by rfl) ⟨827448, by rfl⟩ : syracuseStep 2206529 = 1654897) B1654897
theorem B6286157 : Blo 1470555 6286157 := bstep (se 3 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 6286157 = 2357309) B2357309
theorem B2206547 : Blo 1470555 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B2206577 : Blo 1470555 2206577 := bstep (se 2 (by rfl) ⟨827466, by rfl⟩ : syracuseStep 2206577 = 1654933) B1654933
theorem B2206595 : Blo 1470555 2206595 := bstep (se 1 (by rfl) ⟨1654946, by rfl⟩ : syracuseStep 2206595 = 3309893) B3309893
theorem B4475789 : Blo 1470555 4475789 := bstep (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) B1678421
theorem B2206625 : Blo 1470555 2206625 := bstep (se 2 (by rfl) ⟨827484, by rfl⟩ : syracuseStep 2206625 = 1654969) B1654969
theorem B8383409 : Blo 1470555 8383409 := bstep (se 2 (by rfl) ⟨3143778, by rfl⟩ : syracuseStep 8383409 = 6287557) B6287557
theorem B2206643 : Blo 1470555 2206643 := bstep (se 1 (by rfl) ⟨1654982, by rfl⟩ : syracuseStep 2206643 = 3309965) B3309965
theorem B2206673 : Blo 1470555 2206673 := bstep (se 2 (by rfl) ⟨827502, by rfl⟩ : syracuseStep 2206673 = 1655005) B1655005
theorem B3312593 : Blo 1470555 3312593 := bstep (se 2 (by rfl) ⟨1242222, by rfl⟩ : syracuseStep 3312593 = 2484445) B2484445
theorem B2206691 : Blo 1470555 2206691 := bstep (se 1 (by rfl) ⟨1655018, by rfl⟩ : syracuseStep 2206691 = 3310037) B3310037
theorem B3312611 : Blo 1470555 3312611 := bstep (se 1 (by rfl) ⟨2484458, by rfl⟩ : syracuseStep 3312611 = 4968917) B4968917
theorem B4967405 : Blo 1470555 4967405 := bstep (se 3 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 4967405 = 1862777) B1862777
theorem B2206721 : Blo 1470555 2206721 := bstep (se 2 (by rfl) ⟨827520, by rfl⟩ : syracuseStep 2206721 = 1655041) B1655041
theorem B2206739 : Blo 1470555 2206739 := bstep (se 1 (by rfl) ⟨1655054, by rfl⟩ : syracuseStep 2206739 = 3310109) B3310109
theorem B4967459 : Blo 1470555 4967459 := bstep (se 1 (by rfl) ⟨3725594, by rfl⟩ : syracuseStep 4967459 = 7451189) B7451189
theorem B8375345 : Blo 1470555 8375345 := bstep (se 2 (by rfl) ⟨3140754, by rfl⟩ : syracuseStep 8375345 = 6281509) B6281509
theorem B2206769 : Blo 1470555 2206769 := bstep (se 2 (by rfl) ⟨827538, by rfl⟩ : syracuseStep 2206769 = 1655077) B1655077
theorem B2206787 : Blo 1470555 2206787 := bstep (se 1 (by rfl) ⟨1655090, by rfl⟩ : syracuseStep 2206787 = 3310181) B3310181
theorem B5590093 : Blo 1470555 5590093 := bstep (se 3 (by rfl) ⟨1048142, by rfl⟩ : syracuseStep 5590093 = 2096285) B2096285
theorem B2206817 : Blo 1470555 2206817 := bstep (se 2 (by rfl) ⟨827556, by rfl⟩ : syracuseStep 2206817 = 1655113) B1655113
theorem B2206835 : Blo 1470555 2206835 := bstep (se 1 (by rfl) ⟨1655126, by rfl⟩ : syracuseStep 2206835 = 3310253) B3310253
theorem B2206865 : Blo 1470555 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B2206883 : Blo 1470555 2206883 := bstep (se 1 (by rfl) ⟨1655162, by rfl⟩ : syracuseStep 2206883 = 3310325) B3310325
theorem B2206913 : Blo 1470555 2206913 := bstep (se 2 (by rfl) ⟨827592, by rfl⟩ : syracuseStep 2206913 = 1655185) B1655185
theorem B4246723 : Blo 1470555 4246723 := bstep (se 1 (by rfl) ⟨3185042, by rfl⟩ : syracuseStep 4246723 = 6370085) B6370085
theorem B31042757 : Blo 1470555 31042757 := bstep (se 4 (by rfl) ⟨2910258, by rfl⟩ : syracuseStep 31042757 = 5820517) B5820517
theorem B2206931 : Blo 1470555 2206931 := bstep (se 1 (by rfl) ⟨1655198, by rfl⟩ : syracuseStep 2206931 = 3310397) B3310397
theorem B2206961 : Blo 1470555 2206961 := bstep (se 2 (by rfl) ⟨827610, by rfl⟩ : syracuseStep 2206961 = 1655221) B1655221
theorem B3312881 : Blo 1470555 3312881 := bstep (se 2 (by rfl) ⟨1242330, by rfl⟩ : syracuseStep 3312881 = 2484661) B2484661
theorem B2206979 : Blo 1470555 2206979 := bstep (se 1 (by rfl) ⟨1655234, by rfl⟩ : syracuseStep 2206979 = 3310469) B3310469
theorem B3312899 : Blo 1470555 3312899 := bstep (se 1 (by rfl) ⟨2484674, by rfl⟩ : syracuseStep 3312899 = 4969349) B4969349
theorem B2207009 : Blo 1470555 2207009 := bstep (se 2 (by rfl) ⟨827628, by rfl⟩ : syracuseStep 2207009 = 1655257) B1655257
theorem B4967729 : Blo 1470555 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B2207027 : Blo 1470555 2207027 := bstep (se 1 (by rfl) ⟨1655270, by rfl⟩ : syracuseStep 2207027 = 3310541) B3310541
theorem B2207057 : Blo 1470555 2207057 := bstep (se 2 (by rfl) ⟨827646, by rfl⟩ : syracuseStep 2207057 = 1655293) B1655293
theorem B1862995 : Blo 1470555 1862995 := bstep (se 1 (by rfl) ⟨1397246, by rfl⟩ : syracuseStep 1862995 = 2794493) B2794493
theorem B2207075 : Blo 1470555 2207075 := bstep (se 1 (by rfl) ⟨1655306, by rfl⟩ : syracuseStep 2207075 = 3310613) B3310613
theorem B3140977 : Blo 1470555 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B4189553 : Blo 1470555 4189553 := bstep (se 2 (by rfl) ⟨1571082, by rfl⟩ : syracuseStep 4189553 = 3142165) B3142165
theorem B2207105 : Blo 1470555 2207105 := bstep (se 2 (by rfl) ⟨827664, by rfl⟩ : syracuseStep 2207105 = 1655329) B1655329
theorem B2207123 : Blo 1470555 2207123 := bstep (se 1 (by rfl) ⟨1655342, by rfl⟩ : syracuseStep 2207123 = 3310685) B3310685
theorem B2207153 : Blo 1470555 2207153 := bstep (se 2 (by rfl) ⟨827682, by rfl⟩ : syracuseStep 2207153 = 1655365) B1655365
theorem B1863091 : Blo 1470555 1863091 := bstep (se 1 (by rfl) ⟨1397318, by rfl⟩ : syracuseStep 1863091 = 2794637) B2794637
theorem B20131253 : Blo 1470555 20131253 := bstep (se 5 (by rfl) ⟨943652, by rfl⟩ : syracuseStep 20131253 = 1887305) B1887305
theorem B2207171 : Blo 1470555 2207171 := bstep (se 1 (by rfl) ⟨1655378, by rfl⟩ : syracuseStep 2207171 = 3310757) B3310757
theorem B2207201 : Blo 1470555 2207201 := bstep (se 2 (by rfl) ⟨827700, by rfl⟩ : syracuseStep 2207201 = 1655401) B1655401
theorem B11169251 : Blo 1470555 11169251 := bstep (se 1 (by rfl) ⟨8376938, by rfl⟩ : syracuseStep 11169251 = 16753877) B16753877
theorem B3976685 : Blo 1470555 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B4476397 : Blo 1470555 4476397 := bstep (se 3 (by rfl) ⟨839324, by rfl⟩ : syracuseStep 4476397 = 1678649) B1678649
theorem B2207219 : Blo 1470555 2207219 := bstep (se 1 (by rfl) ⟨1655414, by rfl⟩ : syracuseStep 2207219 = 3310829) B3310829
theorem B2207249 : Blo 1470555 2207249 := bstep (se 2 (by rfl) ⟨827718, by rfl⟩ : syracuseStep 2207249 = 1655437) B1655437
theorem B3313169 : Blo 1470555 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B2207267 : Blo 1470555 2207267 := bstep (se 1 (by rfl) ⟨1655450, by rfl⟩ : syracuseStep 2207267 = 3310901) B3310901
theorem B3313187 : Blo 1470555 3313187 := bstep (se 1 (by rfl) ⟨2484890, by rfl⟩ : syracuseStep 3313187 = 4969781) B4969781
theorem B4189745 : Blo 1470555 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B15904309 : Blo 1470555 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B2207297 : Blo 1470555 2207297 := bstep (se 2 (by rfl) ⟨827736, by rfl⟩ : syracuseStep 2207297 = 1655473) B1655473
theorem B2207315 : Blo 1470555 2207315 := bstep (se 1 (by rfl) ⟨1655486, by rfl⟩ : syracuseStep 2207315 = 3310973) B3310973
theorem B2207345 : Blo 1470555 2207345 := bstep (se 2 (by rfl) ⟨827754, by rfl⟩ : syracuseStep 2207345 = 1655509) B1655509
theorem B2207363 : Blo 1470555 2207363 := bstep (se 1 (by rfl) ⟨1655522, by rfl⟩ : syracuseStep 2207363 = 3311045) B3311045
theorem B2207393 : Blo 1470555 2207393 := bstep (se 2 (by rfl) ⟨827772, by rfl⟩ : syracuseStep 2207393 = 1655545) B1655545
theorem B2207411 : Blo 1470555 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B9432773 : Blo 1470555 9432773 := bstep (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) B1768645
theorem B2207441 : Blo 1470555 2207441 := bstep (se 2 (by rfl) ⟨827790, by rfl⟩ : syracuseStep 2207441 = 1655581) B1655581
theorem B2207459 : Blo 1470555 2207459 := bstep (se 1 (by rfl) ⟨1655594, by rfl⟩ : syracuseStep 2207459 = 3311189) B3311189
theorem B3722993 : Blo 1470555 3722993 := bstep (se 2 (by rfl) ⟨1396122, by rfl⟩ : syracuseStep 3722993 = 2792245) B2792245
theorem B2207489 : Blo 1470555 2207489 := bstep (se 2 (by rfl) ⟨827808, by rfl⟩ : syracuseStep 2207489 = 1655617) B1655617
theorem B2207507 : Blo 1470555 2207507 := bstep (se 1 (by rfl) ⟨1655630, by rfl⟩ : syracuseStep 2207507 = 3311261) B3311261
theorem B3723043 : Blo 1470555 3723043 := bstep (se 1 (by rfl) ⟨2792282, by rfl⟩ : syracuseStep 3723043 = 5584565) B5584565
theorem B3977009 : Blo 1470555 3977009 := bstep (se 2 (by rfl) ⟨1491378, by rfl⟩ : syracuseStep 3977009 = 2982757) B2982757
theorem B2207537 : Blo 1470555 2207537 := bstep (se 2 (by rfl) ⟨827826, by rfl⟩ : syracuseStep 2207537 = 1655653) B1655653
theorem B2207555 : Blo 1470555 2207555 := bstep (se 1 (by rfl) ⟨1655666, by rfl⟩ : syracuseStep 2207555 = 3311333) B3311333
theorem B8949581 : Blo 1470555 8949581 := bstep (se 3 (by rfl) ⟨1678046, by rfl⟩ : syracuseStep 8949581 = 3356093) B3356093
theorem B4968269 : Blo 1470555 4968269 := bstep (se 3 (by rfl) ⟨931550, by rfl⟩ : syracuseStep 4968269 = 1863101) B1863101
theorem B2207585 : Blo 1470555 2207585 := bstep (se 2 (by rfl) ⟨827844, by rfl⟩ : syracuseStep 2207585 = 1655689) B1655689
theorem B5590883 : Blo 1470555 5590883 := bstep (se 1 (by rfl) ⟨4193162, by rfl⟩ : syracuseStep 5590883 = 8386325) B8386325
theorem B2207603 : Blo 1470555 2207603 := bstep (se 1 (by rfl) ⟨1655702, by rfl⟩ : syracuseStep 2207603 = 3311405) B3311405
theorem B4968323 : Blo 1470555 4968323 := bstep (se 1 (by rfl) ⟨3726242, by rfl⟩ : syracuseStep 4968323 = 7452485) B7452485
theorem B2207633 : Blo 1470555 2207633 := bstep (se 2 (by rfl) ⟨827862, by rfl⟩ : syracuseStep 2207633 = 1655725) B1655725
theorem B2207651 : Blo 1470555 2207651 := bstep (se 1 (by rfl) ⟨1655738, by rfl⟩ : syracuseStep 2207651 = 3311477) B3311477
theorem B1863587 : Blo 1470555 1863587 := bstep (se 1 (by rfl) ⟨1397690, by rfl⟩ : syracuseStep 1863587 = 2795381) B2795381
theorem B3723185 : Blo 1470555 3723185 := bstep (se 2 (by rfl) ⟨1396194, by rfl⟩ : syracuseStep 3723185 = 2792389) B2792389
theorem B2207681 : Blo 1470555 2207681 := bstep (se 2 (by rfl) ⟨827880, by rfl⟩ : syracuseStep 2207681 = 1655761) B1655761
theorem B28274629 : Blo 1470555 28274629 := bstep (se 4 (by rfl) ⟨2650746, by rfl⟩ : syracuseStep 28274629 = 5301493) B5301493
theorem B2207699 : Blo 1470555 2207699 := bstep (se 1 (by rfl) ⟨1655774, by rfl⟩ : syracuseStep 2207699 = 3311549) B3311549
theorem B2207729 : Blo 1470555 2207729 := bstep (se 2 (by rfl) ⟨827898, by rfl⟩ : syracuseStep 2207729 = 1655797) B1655797
theorem B2207747 : Blo 1470555 2207747 := bstep (se 1 (by rfl) ⟨1655810, by rfl⟩ : syracuseStep 2207747 = 3311621) B3311621
theorem B2207777 : Blo 1470555 2207777 := bstep (se 2 (by rfl) ⟨827916, by rfl⟩ : syracuseStep 2207777 = 1655833) B1655833
theorem B2207795 : Blo 1470555 2207795 := bstep (se 1 (by rfl) ⟨1655846, by rfl⟩ : syracuseStep 2207795 = 3311693) B3311693
theorem B10203205 : Blo 1470555 10203205 := bstep (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) B1913101
theorem B2207825 : Blo 1470555 2207825 := bstep (se 2 (by rfl) ⟨827934, by rfl⟩ : syracuseStep 2207825 = 1655869) B1655869
theorem B1470563 : Blo 1470555 1470563 := bstep (se 1 (by rfl) ⟨1102922, by rfl⟩ : syracuseStep 1470563 = 2205845) B2205845
theorem B2207843 : Blo 1470555 2207843 := bstep (se 1 (by rfl) ⟨1655882, by rfl⟩ : syracuseStep 2207843 = 3311765) B3311765
theorem B53686385 : Blo 1470555 53686385 := bstep (se 2 (by rfl) ⟨20132394, by rfl⟩ : syracuseStep 53686385 = 40264789) B40264789
theorem B1470579 : Blo 1470555 1470579 := bstep (se 1 (by rfl) ⟨1102934, by rfl⟩ : syracuseStep 1470579 = 2205869) B2205869
theorem B2207873 : Blo 1470555 2207873 := bstep (se 2 (by rfl) ⟨827952, by rfl⟩ : syracuseStep 2207873 = 1655905) B1655905
theorem B1470595 : Blo 1470555 1470595 := bstep (se 1 (by rfl) ⟨1102946, by rfl⟩ : syracuseStep 1470595 = 2205893) B2205893
theorem B4968593 : Blo 1470555 4968593 := bstep (se 2 (by rfl) ⟨1863222, by rfl⟩ : syracuseStep 4968593 = 3726445) B3726445
theorem B1470611 : Blo 1470555 1470611 := bstep (se 1 (by rfl) ⟨1102958, by rfl⟩ : syracuseStep 1470611 = 2205917) B2205917
theorem B2207891 : Blo 1470555 2207891 := bstep (se 1 (by rfl) ⟨1655918, by rfl⟩ : syracuseStep 2207891 = 3311837) B3311837
theorem B1470627 : Blo 1470555 1470627 := bstep (se 1 (by rfl) ⟨1102970, by rfl⟩ : syracuseStep 1470627 = 2205941) B2205941
theorem B1470643 : Blo 1470555 1470643 := bstep (se 1 (by rfl) ⟨1102982, by rfl⟩ : syracuseStep 1470643 = 2205965) B2205965
theorem B2207921 : Blo 1470555 2207921 := bstep (se 2 (by rfl) ⟨827970, by rfl⟩ : syracuseStep 2207921 = 1655941) B1655941
theorem B1470659 : Blo 1470555 1470659 := bstep (se 1 (by rfl) ⟨1102994, by rfl⟩ : syracuseStep 1470659 = 2205989) B2205989
theorem B2207939 : Blo 1470555 2207939 := bstep (se 1 (by rfl) ⟨1655954, by rfl⟩ : syracuseStep 2207939 = 3311909) B3311909
theorem B1470675 : Blo 1470555 1470675 := bstep (se 1 (by rfl) ⟨1103006, by rfl⟩ : syracuseStep 1470675 = 2206013) B2206013
theorem B125751523 : Blo 1470555 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B1470691 : Blo 1470555 1470691 := bstep (se 1 (by rfl) ⟨1103018, by rfl⟩ : syracuseStep 1470691 = 2206037) B2206037
theorem B2207969 : Blo 1470555 2207969 := bstep (se 2 (by rfl) ⟨827988, by rfl⟩ : syracuseStep 2207969 = 1655977) B1655977
theorem B7450865 : Blo 1470555 7450865 := bstep (se 2 (by rfl) ⟨2794074, by rfl⟩ : syracuseStep 7450865 = 5588149) B5588149
theorem B1470707 : Blo 1470555 1470707 := bstep (se 1 (by rfl) ⟨1103030, by rfl⟩ : syracuseStep 1470707 = 2206061) B2206061
theorem B2207987 : Blo 1470555 2207987 := bstep (se 1 (by rfl) ⟨1655990, by rfl⟩ : syracuseStep 2207987 = 3311981) B3311981
theorem B1470723 : Blo 1470555 1470723 := bstep (se 1 (by rfl) ⟨1103042, by rfl⟩ : syracuseStep 1470723 = 2206085) B2206085
theorem B2208017 : Blo 1470555 2208017 := bstep (se 2 (by rfl) ⟨828006, by rfl⟩ : syracuseStep 2208017 = 1656013) B1656013
theorem B1470739 : Blo 1470555 1470739 := bstep (se 1 (by rfl) ⟨1103054, by rfl⟩ : syracuseStep 1470739 = 2206109) B2206109
theorem B1470755 : Blo 1470555 1470755 := bstep (se 1 (by rfl) ⟨1103066, by rfl⟩ : syracuseStep 1470755 = 2206133) B2206133
theorem B2208035 : Blo 1470555 2208035 := bstep (se 1 (by rfl) ⟨1656026, by rfl⟩ : syracuseStep 2208035 = 3312053) B3312053
theorem B1470771 : Blo 1470555 1470771 := bstep (se 1 (by rfl) ⟨1103078, by rfl⟩ : syracuseStep 1470771 = 2206157) B2206157
theorem B2208065 : Blo 1470555 2208065 := bstep (se 2 (by rfl) ⟨828024, by rfl⟩ : syracuseStep 2208065 = 1656049) B1656049
theorem B1470787 : Blo 1470555 1470787 := bstep (se 1 (by rfl) ⟨1103090, by rfl⟩ : syracuseStep 1470787 = 2206181) B2206181
theorem B5968205 : Blo 1470555 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B1470803 : Blo 1470555 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B2208083 : Blo 1470555 2208083 := bstep (se 1 (by rfl) ⟨1656062, by rfl⟩ : syracuseStep 2208083 = 3312125) B3312125
theorem B1470819 : Blo 1470555 1470819 := bstep (se 1 (by rfl) ⟨1103114, by rfl⟩ : syracuseStep 1470819 = 2206229) B2206229
theorem B8384867 : Blo 1470555 8384867 := bstep (se 1 (by rfl) ⟨6288650, by rfl⟩ : syracuseStep 8384867 = 12577301) B12577301
theorem B3977581 : Blo 1470555 3977581 := bstep (se 3 (by rfl) ⟨745796, by rfl⟩ : syracuseStep 3977581 = 1491593) B1491593
theorem B2208113 : Blo 1470555 2208113 := bstep (se 2 (by rfl) ⟨828042, by rfl⟩ : syracuseStep 2208113 = 1656085) B1656085
theorem B1470835 : Blo 1470555 1470835 := bstep (se 1 (by rfl) ⟨1103126, by rfl⟩ : syracuseStep 1470835 = 2206253) B2206253
theorem B1470851 : Blo 1470555 1470851 := bstep (se 1 (by rfl) ⟨1103138, by rfl⟩ : syracuseStep 1470851 = 2206277) B2206277
theorem B2208131 : Blo 1470555 2208131 := bstep (se 1 (by rfl) ⟨1656098, by rfl⟩ : syracuseStep 2208131 = 3312197) B3312197
theorem B1470867 : Blo 1470555 1470867 := bstep (se 1 (by rfl) ⟨1103150, by rfl⟩ : syracuseStep 1470867 = 2206301) B2206301
theorem B2208161 : Blo 1470555 2208161 := bstep (se 2 (by rfl) ⟨828060, by rfl⟩ : syracuseStep 2208161 = 1656121) B1656121
theorem B1470883 : Blo 1470555 1470883 := bstep (se 1 (by rfl) ⟨1103162, by rfl⟩ : syracuseStep 1470883 = 2206325) B2206325
theorem B1470899 : Blo 1470555 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B2208179 : Blo 1470555 2208179 := bstep (se 1 (by rfl) ⟨1656134, by rfl⟩ : syracuseStep 2208179 = 3312269) B3312269
theorem B1470915 : Blo 1470555 1470915 := bstep (se 1 (by rfl) ⟨1103186, by rfl⟩ : syracuseStep 1470915 = 2206373) B2206373
theorem B2208209 : Blo 1470555 2208209 := bstep (se 2 (by rfl) ⟨828078, by rfl⟩ : syracuseStep 2208209 = 1656157) B1656157
theorem B1470931 : Blo 1470555 1470931 := bstep (se 1 (by rfl) ⟨1103198, by rfl⟩ : syracuseStep 1470931 = 2206397) B2206397
theorem B8376803 : Blo 1470555 8376803 := bstep (se 1 (by rfl) ⟨6282602, by rfl⟩ : syracuseStep 8376803 = 12565205) B12565205
theorem B1470947 : Blo 1470555 1470947 := bstep (se 1 (by rfl) ⟨1103210, by rfl⟩ : syracuseStep 1470947 = 2206421) B2206421
theorem B2208227 : Blo 1470555 2208227 := bstep (se 1 (by rfl) ⟨1656170, by rfl⟩ : syracuseStep 2208227 = 3312341) B3312341
theorem B1470963 : Blo 1470555 1470963 := bstep (se 1 (by rfl) ⟨1103222, by rfl⟩ : syracuseStep 1470963 = 2206445) B2206445
theorem B2208257 : Blo 1470555 2208257 := bstep (se 2 (by rfl) ⟨828096, by rfl⟩ : syracuseStep 2208257 = 1656193) B1656193
theorem B1470979 : Blo 1470555 1470979 := bstep (se 1 (by rfl) ⟨1103234, by rfl⟩ : syracuseStep 1470979 = 2206469) B2206469
theorem B4190737 : Blo 1470555 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B1470995 : Blo 1470555 1470995 := bstep (se 1 (by rfl) ⟨1103246, by rfl⟩ : syracuseStep 1470995 = 2206493) B2206493
theorem B2208275 : Blo 1470555 2208275 := bstep (se 1 (by rfl) ⟨1656206, by rfl⟩ : syracuseStep 2208275 = 3312413) B3312413
theorem B1471011 : Blo 1470555 1471011 := bstep (se 1 (by rfl) ⟨1103258, by rfl⟩ : syracuseStep 1471011 = 2206517) B2206517
theorem B2208305 : Blo 1470555 2208305 := bstep (se 2 (by rfl) ⟨828114, by rfl⟩ : syracuseStep 2208305 = 1656229) B1656229
theorem B1471027 : Blo 1470555 1471027 := bstep (se 1 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 1471027 = 2206541) B2206541
theorem B1471043 : Blo 1470555 1471043 := bstep (se 1 (by rfl) ⟨1103282, by rfl⟩ : syracuseStep 1471043 = 2206565) B2206565
theorem B2208323 : Blo 1470555 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B5034577 : Blo 1470555 5034577 := bstep (se 2 (by rfl) ⟨1887966, by rfl⟩ : syracuseStep 5034577 = 3775933) B3775933
theorem B1471059 : Blo 1470555 1471059 := bstep (se 1 (by rfl) ⟨1103294, by rfl⟩ : syracuseStep 1471059 = 2206589) B2206589
theorem B2355809 : Blo 1470555 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B1471075 : Blo 1470555 1471075 := bstep (se 1 (by rfl) ⟨1103306, by rfl⟩ : syracuseStep 1471075 = 2206613) B2206613
theorem B2208353 : Blo 1470555 2208353 := bstep (se 2 (by rfl) ⟨828132, by rfl⟩ : syracuseStep 2208353 = 1656265) B1656265
theorem B1471091 : Blo 1470555 1471091 := bstep (se 1 (by rfl) ⟨1103318, by rfl⟩ : syracuseStep 1471091 = 2206637) B2206637
theorem B2208371 : Blo 1470555 2208371 := bstep (se 1 (by rfl) ⟨1656278, by rfl⟩ : syracuseStep 2208371 = 3312557) B3312557
theorem B1471107 : Blo 1470555 1471107 := bstep (se 1 (by rfl) ⟨1103330, by rfl⟩ : syracuseStep 1471107 = 2206661) B2206661
theorem B2208401 : Blo 1470555 2208401 := bstep (se 2 (by rfl) ⟨828150, by rfl⟩ : syracuseStep 2208401 = 1656301) B1656301
theorem B1471123 : Blo 1470555 1471123 := bstep (se 1 (by rfl) ⟨1103342, by rfl⟩ : syracuseStep 1471123 = 2206685) B2206685
theorem B1471139 : Blo 1470555 1471139 := bstep (se 1 (by rfl) ⟨1103354, by rfl⟩ : syracuseStep 1471139 = 2206709) B2206709
theorem B2208419 : Blo 1470555 2208419 := bstep (se 1 (by rfl) ⟨1656314, by rfl⟩ : syracuseStep 2208419 = 3312629) B3312629
theorem B4969133 : Blo 1470555 4969133 := bstep (se 3 (by rfl) ⟨931712, by rfl⟩ : syracuseStep 4969133 = 1863425) B1863425
theorem B1471155 : Blo 1470555 1471155 := bstep (se 1 (by rfl) ⟨1103366, by rfl⟩ : syracuseStep 1471155 = 2206733) B2206733
theorem B2208449 : Blo 1470555 2208449 := bstep (se 2 (by rfl) ⟨828168, by rfl⟩ : syracuseStep 2208449 = 1656337) B1656337
theorem B1471171 : Blo 1470555 1471171 := bstep (se 1 (by rfl) ⟨1103378, by rfl⟩ : syracuseStep 1471171 = 2206757) B2206757
theorem B1471187 : Blo 1470555 1471187 := bstep (se 1 (by rfl) ⟨1103390, by rfl⟩ : syracuseStep 1471187 = 2206781) B2206781
theorem B2208467 : Blo 1470555 2208467 := bstep (se 1 (by rfl) ⟨1656350, by rfl⟩ : syracuseStep 2208467 = 3312701) B3312701
theorem B1471203 : Blo 1470555 1471203 := bstep (se 1 (by rfl) ⟨1103402, by rfl⟩ : syracuseStep 1471203 = 2206805) B2206805
theorem B4969187 : Blo 1470555 4969187 := bstep (se 1 (by rfl) ⟨3726890, by rfl⟩ : syracuseStep 4969187 = 7453781) B7453781
theorem B2208497 : Blo 1470555 2208497 := bstep (se 2 (by rfl) ⟨828186, by rfl⟩ : syracuseStep 2208497 = 1656373) B1656373
theorem B1471219 : Blo 1470555 1471219 := bstep (se 1 (by rfl) ⟨1103414, by rfl⟩ : syracuseStep 1471219 = 2206829) B2206829
theorem B1471235 : Blo 1470555 1471235 := bstep (se 1 (by rfl) ⟨1103426, by rfl⟩ : syracuseStep 1471235 = 2206853) B2206853
theorem B2208515 : Blo 1470555 2208515 := bstep (se 1 (by rfl) ⟨1656386, by rfl⟩ : syracuseStep 2208515 = 3312773) B3312773
theorem B1471251 : Blo 1470555 1471251 := bstep (se 1 (by rfl) ⟨1103438, by rfl⟩ : syracuseStep 1471251 = 2206877) B2206877
theorem B1471267 : Blo 1470555 1471267 := bstep (se 1 (by rfl) ⟨1103450, by rfl⟩ : syracuseStep 1471267 = 2206901) B2206901
theorem B4191011 : Blo 1470555 4191011 := bstep (se 1 (by rfl) ⟨3143258, by rfl⟩ : syracuseStep 4191011 = 6286517) B6286517
theorem B2208545 : Blo 1470555 2208545 := bstep (se 2 (by rfl) ⟨828204, by rfl⟩ : syracuseStep 2208545 = 1656409) B1656409
theorem B4715309 : Blo 1470555 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B1471283 : Blo 1470555 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B2208563 : Blo 1470555 2208563 := bstep (se 1 (by rfl) ⟨1656422, by rfl⟩ : syracuseStep 2208563 = 3312845) B3312845
theorem B1471299 : Blo 1470555 1471299 := bstep (se 1 (by rfl) ⟨1103474, by rfl⟩ : syracuseStep 1471299 = 2206949) B2206949
theorem B2208593 : Blo 1470555 2208593 := bstep (se 2 (by rfl) ⟨828222, by rfl⟩ : syracuseStep 2208593 = 1656445) B1656445
theorem B1471315 : Blo 1470555 1471315 := bstep (se 1 (by rfl) ⟨1103486, by rfl⟩ : syracuseStep 1471315 = 2206973) B2206973
theorem B1471331 : Blo 1470555 1471331 := bstep (se 1 (by rfl) ⟨1103498, by rfl⟩ : syracuseStep 1471331 = 2206997) B2206997
theorem B2208611 : Blo 1470555 2208611 := bstep (se 1 (by rfl) ⟨1656458, by rfl⟩ : syracuseStep 2208611 = 3312917) B3312917
theorem B1471347 : Blo 1470555 1471347 := bstep (se 1 (by rfl) ⟨1103510, by rfl⟩ : syracuseStep 1471347 = 2207021) B2207021
theorem B2208641 : Blo 1470555 2208641 := bstep (se 2 (by rfl) ⟨828240, by rfl⟩ : syracuseStep 2208641 = 1656481) B1656481
theorem B1471363 : Blo 1470555 1471363 := bstep (se 1 (by rfl) ⟨1103522, by rfl⟩ : syracuseStep 1471363 = 2207045) B2207045
theorem B3724177 : Blo 1470555 3724177 := bstep (se 2 (by rfl) ⟨1396566, by rfl⟩ : syracuseStep 3724177 = 2793133) B2793133
theorem B1471379 : Blo 1470555 1471379 := bstep (se 1 (by rfl) ⟨1103534, by rfl⟩ : syracuseStep 1471379 = 2207069) B2207069
theorem B2208659 : Blo 1470555 2208659 := bstep (se 1 (by rfl) ⟨1656494, by rfl⟩ : syracuseStep 2208659 = 3312989) B3312989
theorem B1471395 : Blo 1470555 1471395 := bstep (se 1 (by rfl) ⟨1103546, by rfl⟩ : syracuseStep 1471395 = 2207093) B2207093
theorem B2208689 : Blo 1470555 2208689 := bstep (se 2 (by rfl) ⟨828258, by rfl⟩ : syracuseStep 2208689 = 1656517) B1656517
theorem B1471411 : Blo 1470555 1471411 := bstep (se 1 (by rfl) ⟨1103558, by rfl⟩ : syracuseStep 1471411 = 2207117) B2207117
theorem B1471427 : Blo 1470555 1471427 := bstep (se 1 (by rfl) ⟨1103570, by rfl⟩ : syracuseStep 1471427 = 2207141) B2207141
theorem B2208707 : Blo 1470555 2208707 := bstep (se 1 (by rfl) ⟨1656530, by rfl⟩ : syracuseStep 2208707 = 3313061) B3313061
theorem B1471443 : Blo 1470555 1471443 := bstep (se 1 (by rfl) ⟨1103582, by rfl⟩ : syracuseStep 1471443 = 2207165) B2207165
theorem B2208737 : Blo 1470555 2208737 := bstep (se 2 (by rfl) ⟨828276, by rfl⟩ : syracuseStep 2208737 = 1656553) B1656553
theorem B1471459 : Blo 1470555 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B4191203 : Blo 1470555 4191203 := bstep (se 1 (by rfl) ⟨3143402, by rfl⟩ : syracuseStep 4191203 = 6286805) B6286805
theorem B4969457 : Blo 1470555 4969457 := bstep (se 2 (by rfl) ⟨1863546, by rfl⟩ : syracuseStep 4969457 = 3727093) B3727093
theorem B1471475 : Blo 1470555 1471475 := bstep (se 1 (by rfl) ⟨1103606, by rfl⟩ : syracuseStep 1471475 = 2207213) B2207213
theorem B2208755 : Blo 1470555 2208755 := bstep (se 1 (by rfl) ⟨1656566, by rfl⟩ : syracuseStep 2208755 = 3313133) B3313133
theorem B1471491 : Blo 1470555 1471491 := bstep (se 1 (by rfl) ⟨1103618, by rfl⟩ : syracuseStep 1471491 = 2207237) B2207237
theorem B1471507 : Blo 1470555 1471507 := bstep (se 1 (by rfl) ⟨1103630, by rfl⟩ : syracuseStep 1471507 = 2207261) B2207261
theorem B2208785 : Blo 1470555 2208785 := bstep (se 2 (by rfl) ⟨828294, by rfl⟩ : syracuseStep 2208785 = 1656589) B1656589
theorem B1471523 : Blo 1470555 1471523 := bstep (se 1 (by rfl) ⟨1103642, by rfl⟩ : syracuseStep 1471523 = 2207285) B2207285
theorem B2208803 : Blo 1470555 2208803 := bstep (se 1 (by rfl) ⟨1656602, by rfl⟩ : syracuseStep 2208803 = 3313205) B3313205
theorem B1471539 : Blo 1470555 1471539 := bstep (se 1 (by rfl) ⟨1103654, by rfl⟩ : syracuseStep 1471539 = 2207309) B2207309
theorem B2208833 : Blo 1470555 2208833 := bstep (se 2 (by rfl) ⟨828312, by rfl⟩ : syracuseStep 2208833 = 1656625) B1656625
theorem B1471555 : Blo 1470555 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B1471571 : Blo 1470555 1471571 := bstep (se 1 (by rfl) ⟨1103678, by rfl⟩ : syracuseStep 1471571 = 2207357) B2207357
theorem B1471587 : Blo 1470555 1471587 := bstep (se 1 (by rfl) ⟨1103690, by rfl⟩ : syracuseStep 1471587 = 2207381) B2207381
theorem B1471603 : Blo 1470555 1471603 := bstep (se 1 (by rfl) ⟨1103702, by rfl⟩ : syracuseStep 1471603 = 2207405) B2207405
theorem B2651267 : Blo 1470555 2651267 := bstep (se 1 (by rfl) ⟨1988450, by rfl⟩ : syracuseStep 2651267 = 3976901) B3976901
theorem B1471619 : Blo 1470555 1471619 := bstep (se 1 (by rfl) ⟨1103714, by rfl⟩ : syracuseStep 1471619 = 2207429) B2207429
theorem B1471635 : Blo 1470555 1471635 := bstep (se 1 (by rfl) ⟨1103726, by rfl⟩ : syracuseStep 1471635 = 2207453) B2207453
theorem B3724451 : Blo 1470555 3724451 := bstep (se 1 (by rfl) ⟨2793338, by rfl⟩ : syracuseStep 3724451 = 5586677) B5586677
theorem B1471651 : Blo 1470555 1471651 := bstep (se 1 (by rfl) ⟨1103738, by rfl⟩ : syracuseStep 1471651 = 2207477) B2207477
theorem B5584049 : Blo 1470555 5584049 := bstep (se 2 (by rfl) ⟨2094018, by rfl⟩ : syracuseStep 5584049 = 4188037) B4188037
theorem B1471667 : Blo 1470555 1471667 := bstep (se 1 (by rfl) ⟨1103750, by rfl⟩ : syracuseStep 1471667 = 2207501) B2207501
theorem B2094275 : Blo 1470555 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B1471683 : Blo 1470555 1471683 := bstep (se 1 (by rfl) ⟨1103762, by rfl⟩ : syracuseStep 1471683 = 2207525) B2207525
theorem B1471699 : Blo 1470555 1471699 := bstep (se 1 (by rfl) ⟨1103774, by rfl⟩ : syracuseStep 1471699 = 2207549) B2207549
theorem B3536099 : Blo 1470555 3536099 := bstep (se 1 (by rfl) ⟨2652074, by rfl⟩ : syracuseStep 3536099 = 5304149) B5304149
theorem B1471715 : Blo 1470555 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B1471731 : Blo 1470555 1471731 := bstep (se 1 (by rfl) ⟨1103798, by rfl⟩ : syracuseStep 1471731 = 2207597) B2207597
theorem B1471747 : Blo 1470555 1471747 := bstep (se 1 (by rfl) ⟨1103810, by rfl⟩ : syracuseStep 1471747 = 2207621) B2207621
theorem B1471763 : Blo 1470555 1471763 := bstep (se 1 (by rfl) ⟨1103822, by rfl⟩ : syracuseStep 1471763 = 2207645) B2207645
theorem B1471779 : Blo 1470555 1471779 := bstep (se 1 (by rfl) ⟨1103834, by rfl⟩ : syracuseStep 1471779 = 2207669) B2207669
theorem B1471795 : Blo 1470555 1471795 := bstep (se 1 (by rfl) ⟨1103846, by rfl⟩ : syracuseStep 1471795 = 2207693) B2207693
theorem B1471811 : Blo 1470555 1471811 := bstep (se 1 (by rfl) ⟨1103858, by rfl⟩ : syracuseStep 1471811 = 2207717) B2207717
theorem B8385869 : Blo 1470555 8385869 := bstep (se 3 (by rfl) ⟨1572350, by rfl⟩ : syracuseStep 8385869 = 3144701) B3144701
theorem B1471827 : Blo 1470555 1471827 := bstep (se 1 (by rfl) ⟨1103870, by rfl⟩ : syracuseStep 1471827 = 2207741) B2207741
theorem B3724643 : Blo 1470555 3724643 := bstep (se 1 (by rfl) ⟨2793482, by rfl⟩ : syracuseStep 3724643 = 5586965) B5586965
theorem B1471843 : Blo 1470555 1471843 := bstep (se 1 (by rfl) ⟨1103882, by rfl⟩ : syracuseStep 1471843 = 2207765) B2207765
theorem B1471859 : Blo 1470555 1471859 := bstep (se 1 (by rfl) ⟨1103894, by rfl⟩ : syracuseStep 1471859 = 2207789) B2207789
theorem B1471875 : Blo 1470555 1471875 := bstep (se 1 (by rfl) ⟨1103906, by rfl⟩ : syracuseStep 1471875 = 2207813) B2207813
theorem B1471891 : Blo 1470555 1471891 := bstep (se 1 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 1471891 = 2207837) B2207837
theorem B1766819 : Blo 1470555 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B3536291 : Blo 1470555 3536291 := bstep (se 1 (by rfl) ⟨2652218, by rfl⟩ : syracuseStep 3536291 = 5304437) B5304437
theorem B1471907 : Blo 1470555 1471907 := bstep (se 1 (by rfl) ⟨1103930, by rfl⟩ : syracuseStep 1471907 = 2207861) B2207861
theorem B1471923 : Blo 1470555 1471923 := bstep (se 1 (by rfl) ⟨1103942, by rfl⟩ : syracuseStep 1471923 = 2207885) B2207885
theorem B1471939 : Blo 1470555 1471939 := bstep (se 1 (by rfl) ⟨1103954, by rfl⟩ : syracuseStep 1471939 = 2207909) B2207909
theorem B1471955 : Blo 1470555 1471955 := bstep (se 1 (by rfl) ⟨1103966, by rfl⟩ : syracuseStep 1471955 = 2207933) B2207933
theorem B23852515 : Blo 1470555 23852515 := bstep (se 1 (by rfl) ⟨17889386, by rfl⟩ : syracuseStep 23852515 = 35778773) B35778773
theorem B1471971 : Blo 1470555 1471971 := bstep (se 1 (by rfl) ⟨1103978, by rfl⟩ : syracuseStep 1471971 = 2207957) B2207957
theorem B1471987 : Blo 1470555 1471987 := bstep (se 1 (by rfl) ⟨1103990, by rfl⟩ : syracuseStep 1471987 = 2207981) B2207981
theorem B1472003 : Blo 1470555 1472003 := bstep (se 1 (by rfl) ⟨1104002, by rfl⟩ : syracuseStep 1472003 = 2208005) B2208005
theorem B1472019 : Blo 1470555 1472019 := bstep (se 1 (by rfl) ⟨1104014, by rfl⟩ : syracuseStep 1472019 = 2208029) B2208029
theorem B1472035 : Blo 1470555 1472035 := bstep (se 1 (by rfl) ⟨1104026, by rfl⟩ : syracuseStep 1472035 = 2208053) B2208053
theorem B1472051 : Blo 1470555 1472051 := bstep (se 1 (by rfl) ⟨1104038, by rfl⟩ : syracuseStep 1472051 = 2208077) B2208077
theorem B1472067 : Blo 1470555 1472067 := bstep (se 1 (by rfl) ⟨1104050, by rfl⟩ : syracuseStep 1472067 = 2208101) B2208101
theorem B5969485 : Blo 1470555 5969485 := bstep (se 3 (by rfl) ⟨1119278, by rfl⟩ : syracuseStep 5969485 = 2238557) B2238557
theorem B1472083 : Blo 1470555 1472083 := bstep (se 1 (by rfl) ⟨1104062, by rfl⟩ : syracuseStep 1472083 = 2208125) B2208125
theorem B5035619 : Blo 1470555 5035619 := bstep (se 1 (by rfl) ⟨3776714, by rfl⟩ : syracuseStep 5035619 = 7553429) B7553429
theorem B1472099 : Blo 1470555 1472099 := bstep (se 1 (by rfl) ⟨1104074, by rfl⟩ : syracuseStep 1472099 = 2208149) B2208149
theorem B8500835 : Blo 1470555 8500835 := bstep (se 1 (by rfl) ⟨6375626, by rfl⟩ : syracuseStep 8500835 = 12751253) B12751253
theorem B1472115 : Blo 1470555 1472115 := bstep (se 1 (by rfl) ⟨1104086, by rfl⟩ : syracuseStep 1472115 = 2208173) B2208173
theorem B1472131 : Blo 1470555 1472131 := bstep (se 1 (by rfl) ⟨1104098, by rfl⟩ : syracuseStep 1472131 = 2208197) B2208197
theorem B1472147 : Blo 1470555 1472147 := bstep (se 1 (by rfl) ⟨1104110, by rfl⟩ : syracuseStep 1472147 = 2208221) B2208221
theorem B7452323 : Blo 1470555 7452323 := bstep (se 1 (by rfl) ⟨5589242, by rfl⟩ : syracuseStep 7452323 = 11178485) B11178485
theorem B1472163 : Blo 1470555 1472163 := bstep (se 1 (by rfl) ⟨1104122, by rfl⟩ : syracuseStep 1472163 = 2208245) B2208245
theorem B1472179 : Blo 1470555 1472179 := bstep (se 1 (by rfl) ⟨1104134, by rfl⟩ : syracuseStep 1472179 = 2208269) B2208269
theorem B1472195 : Blo 1470555 1472195 := bstep (se 1 (by rfl) ⟨1104146, by rfl⟩ : syracuseStep 1472195 = 2208293) B2208293
theorem B7952069 : Blo 1470555 7952069 := bstep (se 4 (by rfl) ⟨745506, by rfl⟩ : syracuseStep 7952069 = 1491013) B1491013
theorem B1472211 : Blo 1470555 1472211 := bstep (se 1 (by rfl) ⟨1104158, by rfl⟩ : syracuseStep 1472211 = 2208317) B2208317
theorem B1472227 : Blo 1470555 1472227 := bstep (se 1 (by rfl) ⟨1104170, by rfl⟩ : syracuseStep 1472227 = 2208341) B2208341
theorem B1472243 : Blo 1470555 1472243 := bstep (se 1 (by rfl) ⟨1104182, by rfl⟩ : syracuseStep 1472243 = 2208365) B2208365
theorem B1472259 : Blo 1470555 1472259 := bstep (se 1 (by rfl) ⟨1104194, by rfl⟩ : syracuseStep 1472259 = 2208389) B2208389
theorem B4192013 : Blo 1470555 4192013 := bstep (se 3 (by rfl) ⟨786002, by rfl⟩ : syracuseStep 4192013 = 1572005) B1572005
theorem B1472275 : Blo 1470555 1472275 := bstep (se 1 (by rfl) ⟨1104206, by rfl⟩ : syracuseStep 1472275 = 2208413) B2208413
theorem B1472291 : Blo 1470555 1472291 := bstep (se 1 (by rfl) ⟨1104218, by rfl⟩ : syracuseStep 1472291 = 2208437) B2208437
theorem B7075619 : Blo 1470555 7075619 := bstep (se 1 (by rfl) ⟨5306714, by rfl⟩ : syracuseStep 7075619 = 10613429) B10613429
theorem B1472307 : Blo 1470555 1472307 := bstep (se 1 (by rfl) ⟨1104230, by rfl⟩ : syracuseStep 1472307 = 2208461) B2208461
theorem B2094913 : Blo 1470555 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1472323 : Blo 1470555 1472323 := bstep (se 1 (by rfl) ⟨1104242, by rfl⟩ : syracuseStep 1472323 = 2208485) B2208485
theorem B1472339 : Blo 1470555 1472339 := bstep (se 1 (by rfl) ⟨1104254, by rfl⟩ : syracuseStep 1472339 = 2208509) B2208509
theorem B1472355 : Blo 1470555 1472355 := bstep (se 1 (by rfl) ⟨1104266, by rfl⟩ : syracuseStep 1472355 = 2208533) B2208533
theorem B6289265 : Blo 1470555 6289265 := bstep (se 2 (by rfl) ⟨2358474, by rfl⟩ : syracuseStep 6289265 = 4716949) B4716949
theorem B1472371 : Blo 1470555 1472371 := bstep (se 1 (by rfl) ⟨1104278, by rfl⟩ : syracuseStep 1472371 = 2208557) B2208557
theorem B1472387 : Blo 1470555 1472387 := bstep (se 1 (by rfl) ⟨1104290, by rfl⟩ : syracuseStep 1472387 = 2208581) B2208581
theorem B1472403 : Blo 1470555 1472403 := bstep (se 1 (by rfl) ⟨1104302, by rfl⟩ : syracuseStep 1472403 = 2208605) B2208605
theorem B1472419 : Blo 1470555 1472419 := bstep (se 1 (by rfl) ⟨1104314, by rfl⟩ : syracuseStep 1472419 = 2208629) B2208629
theorem B1472435 : Blo 1470555 1472435 := bstep (se 1 (by rfl) ⟨1104326, by rfl⟩ : syracuseStep 1472435 = 2208653) B2208653
theorem B4192195 : Blo 1470555 4192195 := bstep (se 1 (by rfl) ⟨3144146, by rfl⟩ : syracuseStep 4192195 = 6288293) B6288293
theorem B1472451 : Blo 1470555 1472451 := bstep (se 1 (by rfl) ⟨1104338, by rfl⟩ : syracuseStep 1472451 = 2208677) B2208677
theorem B1472467 : Blo 1470555 1472467 := bstep (se 1 (by rfl) ⟨1104350, by rfl⟩ : syracuseStep 1472467 = 2208701) B2208701
theorem B2357219 : Blo 1470555 2357219 := bstep (se 1 (by rfl) ⟨1767914, by rfl⟩ : syracuseStep 2357219 = 3535829) B3535829
theorem B2652131 : Blo 1470555 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B3536867 : Blo 1470555 3536867 := bstep (se 1 (by rfl) ⟨2652650, by rfl⟩ : syracuseStep 3536867 = 5305301) B5305301
theorem B1472483 : Blo 1470555 1472483 := bstep (se 1 (by rfl) ⟨1104362, by rfl⟩ : syracuseStep 1472483 = 2208725) B2208725
theorem B1472499 : Blo 1470555 1472499 := bstep (se 1 (by rfl) ⟨1104374, by rfl⟩ : syracuseStep 1472499 = 2208749) B2208749
theorem B1472515 : Blo 1470555 1472515 := bstep (se 1 (by rfl) ⟨1104386, by rfl⟩ : syracuseStep 1472515 = 2208773) B2208773
theorem B1472531 : Blo 1470555 1472531 := bstep (se 1 (by rfl) ⟨1104398, by rfl⟩ : syracuseStep 1472531 = 2208797) B2208797
theorem B1472547 : Blo 1470555 1472547 := bstep (se 1 (by rfl) ⟨1104410, by rfl⟩ : syracuseStep 1472547 = 2208821) B2208821
theorem B2357347 : Blo 1470555 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B2095249 : Blo 1470555 2095249 := bstep (se 2 (by rfl) ⟨785718, by rfl⟩ : syracuseStep 2095249 = 1571437) B1571437
theorem B23869637 : Blo 1470555 23869637 := bstep (se 4 (by rfl) ⟨2237778, by rfl⟩ : syracuseStep 23869637 = 4475557) B4475557
theorem B3725585 : Blo 1470555 3725585 := bstep (se 2 (by rfl) ⟨1397094, by rfl⟩ : syracuseStep 3725585 = 2794189) B2794189
theorem B1677619 : Blo 1470555 1677619 := bstep (se 1 (by rfl) ⟨1258214, by rfl⟩ : syracuseStep 1677619 = 2516429) B2516429
theorem B3725635 : Blo 1470555 3725635 := bstep (se 1 (by rfl) ⟨2794226, by rfl⟩ : syracuseStep 3725635 = 5588453) B5588453
theorem B3144035 : Blo 1470555 3144035 := bstep (se 1 (by rfl) ⟨2358026, by rfl⟩ : syracuseStep 3144035 = 4716053) B4716053
theorem B3537251 : Blo 1470555 3537251 := bstep (se 1 (by rfl) ⟨2652938, by rfl⟩ : syracuseStep 3537251 = 5305877) B5305877
theorem B4716899 : Blo 1470555 4716899 := bstep (se 1 (by rfl) ⟨3537674, by rfl⟩ : syracuseStep 4716899 = 7075349) B7075349
theorem B16750961 : Blo 1470555 16750961 := bstep (se 2 (by rfl) ⟨6281610, by rfl⟩ : syracuseStep 16750961 = 12563221) B12563221
theorem B11180429 : Blo 1470555 11180429 := bstep (se 3 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 11180429 = 4192661) B4192661
theorem B4192685 : Blo 1470555 4192685 := bstep (se 3 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 4192685 = 1572257) B1572257
theorem B7453133 : Blo 1470555 7453133 := bstep (se 3 (by rfl) ⟨1397462, by rfl⟩ : syracuseStep 7453133 = 2794925) B2794925
theorem B3725777 : Blo 1470555 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B6289933 : Blo 1470555 6289933 := bstep (se 3 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 6289933 = 2358725) B2358725
theorem B1571411 : Blo 1470555 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B5585507 : Blo 1470555 5585507 := bstep (se 1 (by rfl) ⟨4189130, by rfl⟩ : syracuseStep 5585507 = 8378261) B8378261
theorem B2357905 : Blo 1470555 2357905 := bstep (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) B1768429
theorem B2095841 : Blo 1470555 2095841 := bstep (se 2 (by rfl) ⟨785940, by rfl⟩ : syracuseStep 2095841 = 1571881) B1571881
theorem B5962481 : Blo 1470555 5962481 := bstep (se 2 (by rfl) ⟨2235930, by rfl⟩ : syracuseStep 5962481 = 4471861) B4471861
theorem B10607345 : Blo 1470555 10607345 := bstep (se 2 (by rfl) ⟨3977754, by rfl⟩ : syracuseStep 10607345 = 7955509) B7955509
theorem B9427747 : Blo 1470555 9427747 := bstep (se 1 (by rfl) ⟨7070810, by rfl⟩ : syracuseStep 9427747 = 14141621) B14141621
theorem B4963139 : Blo 1470555 4963139 := bstep (se 1 (by rfl) ⟨3722354, by rfl⟩ : syracuseStep 4963139 = 7444709) B7444709
theorem B10607429 : Blo 1470555 10607429 := bstep (se 4 (by rfl) ⟨994446, by rfl⟩ : syracuseStep 10607429 = 1988893) B1988893
theorem B1989617 : Blo 1470555 1989617 := bstep (se 2 (by rfl) ⟨746106, by rfl⟩ : syracuseStep 1989617 = 1492213) B1492213
theorem B2792465 : Blo 1470555 2792465 := bstep (se 2 (by rfl) ⟨1047174, by rfl⟩ : syracuseStep 2792465 = 2094349) B2094349
theorem B4963409 : Blo 1470555 4963409 := bstep (se 2 (by rfl) ⟨1861278, by rfl⟩ : syracuseStep 4963409 = 3722557) B3722557
theorem B17226893 : Blo 1470555 17226893 := bstep (se 3 (by rfl) ⟨3230042, by rfl⟩ : syracuseStep 17226893 = 6460085) B6460085
theorem B7445681 : Blo 1470555 7445681 := bstep (se 2 (by rfl) ⟨2792130, by rfl⟩ : syracuseStep 7445681 = 5584261) B5584261
theorem B3538097 : Blo 1470555 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B3144899 : Blo 1470555 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B6282467 : Blo 1470555 6282467 := bstep (se 1 (by rfl) ⟨4711850, by rfl⟩ : syracuseStep 6282467 = 9423701) B9423701
theorem B90627299 : Blo 1470555 90627299 := bstep (se 1 (by rfl) ⟨67970474, by rfl⟩ : syracuseStep 90627299 = 135940949) B135940949
theorem B2096371 : Blo 1470555 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B3308849 : Blo 1470555 3308849 := bstep (se 2 (by rfl) ⟨1240818, by rfl⟩ : syracuseStep 3308849 = 2481637) B2481637
theorem B2358577 : Blo 1470555 2358577 := bstep (se 2 (by rfl) ⟨884466, by rfl⟩ : syracuseStep 2358577 = 1768933) B1768933
theorem B3308867 : Blo 1470555 3308867 := bstep (se 1 (by rfl) ⟨2481650, by rfl⟩ : syracuseStep 3308867 = 4963301) B4963301
theorem B3726769 : Blo 1470555 3726769 := bstep (se 2 (by rfl) ⟨1397538, by rfl⟩ : syracuseStep 3726769 = 2795077) B2795077
theorem B2481617 : Blo 1470555 2481617 := bstep (se 2 (by rfl) ⟨930606, by rfl⟩ : syracuseStep 2481617 = 1861213) B1861213
theorem B2981443 : Blo 1470555 2981443 := bstep (se 1 (by rfl) ⟨2236082, by rfl⟩ : syracuseStep 2981443 = 4472165) B4472165
theorem B1572419 : Blo 1470555 1572419 := bstep (se 1 (by rfl) ⟨1179314, by rfl⟩ : syracuseStep 1572419 = 2358629) B2358629
theorem B5963341 : Blo 1470555 5963341 := bstep (se 3 (by rfl) ⟨1118126, by rfl⟩ : syracuseStep 5963341 = 2236253) B2236253
theorem B5586509 : Blo 1470555 5586509 := bstep (se 3 (by rfl) ⟨1047470, by rfl⟩ : syracuseStep 5586509 = 2094941) B2094941
theorem B2481745 : Blo 1470555 2481745 := bstep (se 2 (by rfl) ⟨930654, by rfl⟩ : syracuseStep 2481745 = 1861309) B1861309
theorem B3309137 : Blo 1470555 3309137 := bstep (se 2 (by rfl) ⟨1240926, by rfl⟩ : syracuseStep 3309137 = 2481853) B2481853
theorem B3309155 : Blo 1470555 3309155 := bstep (se 1 (by rfl) ⟨2481866, by rfl⟩ : syracuseStep 3309155 = 4963733) B4963733
theorem B4963949 : Blo 1470555 4963949 := bstep (se 3 (by rfl) ⟨930740, by rfl⟩ : syracuseStep 4963949 = 1861481) B1861481
theorem B2481779 : Blo 1470555 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B8380037 : Blo 1470555 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B2981539 : Blo 1470555 2981539 := bstep (se 1 (by rfl) ⟨2236154, by rfl⟩ : syracuseStep 2981539 = 4472309) B4472309
theorem B4964003 : Blo 1470555 4964003 := bstep (se 1 (by rfl) ⟨3723002, by rfl⟩ : syracuseStep 4964003 = 7446005) B7446005
theorem B3727043 : Blo 1470555 3727043 := bstep (se 1 (by rfl) ⟨2795282, by rfl⟩ : syracuseStep 3727043 = 5590565) B5590565
theorem B1654483 : Blo 1470555 1654483 := bstep (se 1 (by rfl) ⟨1240862, by rfl⟩ : syracuseStep 1654483 = 2481725) B2481725
theorem B2481907 : Blo 1470555 2481907 := bstep (se 1 (by rfl) ⟨1861430, by rfl⟩ : syracuseStep 2481907 = 3722861) B3722861
theorem B1654627 : Blo 1470555 1654627 := bstep (se 1 (by rfl) ⟨1240970, by rfl⟩ : syracuseStep 1654627 = 2481941) B2481941
theorem B4030307 : Blo 1470555 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B3309425 : Blo 1470555 3309425 := bstep (se 2 (by rfl) ⟨1241034, by rfl⟩ : syracuseStep 3309425 = 2482069) B2482069
theorem B2482049 : Blo 1470555 2482049 := bstep (se 2 (by rfl) ⟨930768, by rfl⟩ : syracuseStep 2482049 = 1861537) B1861537
theorem B3309443 : Blo 1470555 3309443 := bstep (se 1 (by rfl) ⟨2482082, by rfl⟩ : syracuseStep 3309443 = 4964165) B4964165
theorem B3727235 : Blo 1470555 3727235 := bstep (se 1 (by rfl) ⟨2795426, by rfl⟩ : syracuseStep 3727235 = 5590853) B5590853
theorem B2793361 : Blo 1470555 2793361 := bstep (se 2 (by rfl) ⟨1047510, by rfl⟩ : syracuseStep 2793361 = 2095021) B2095021
theorem B4964273 : Blo 1470555 4964273 := bstep (se 2 (by rfl) ⟨1861602, by rfl⟩ : syracuseStep 4964273 = 3723205) B3723205
theorem B9428977 : Blo 1470555 9428977 := bstep (se 2 (by rfl) ⟨3535866, by rfl⟩ : syracuseStep 9428977 = 7071733) B7071733
theorem B1654771 : Blo 1470555 1654771 := bstep (se 1 (by rfl) ⟨1241078, by rfl⟩ : syracuseStep 1654771 = 2482157) B2482157
theorem B3309569 : Blo 1470555 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B1654807 : Blo 1470555 1654807 := bstep (se 1 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 1654807 = 2482211) B2482211
theorem B5586995 : Blo 1470555 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B35790923 : Blo 1470555 35790923 := bstep (se 1 (by rfl) ⟨26843192, by rfl⟩ : syracuseStep 35790923 = 53686385) B53686385
theorem B2482265 : Blo 1470555 2482265 := bstep (se 2 (by rfl) ⟨930849, by rfl⟩ : syracuseStep 2482265 = 1861699) B1861699
theorem B6283457 : Blo 1470555 6283457 := bstep (se 2 (by rfl) ⟨2356296, by rfl⟩ : syracuseStep 6283457 = 4712593) B4712593
theorem B2793665 : Blo 1470555 2793665 := bstep (se 2 (by rfl) ⟨1047624, by rfl⟩ : syracuseStep 2793665 = 2095249) B2095249
theorem B1654987 : Blo 1470555 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B3309785 : Blo 1470555 3309785 := bstep (se 2 (by rfl) ⟨1241169, by rfl⟩ : syracuseStep 3309785 = 2482339) B2482339
theorem B2482393 : Blo 1470555 2482393 := bstep (se 2 (by rfl) ⟨930897, by rfl⟩ : syracuseStep 2482393 = 1861795) B1861795
theorem B11927843 : Blo 1470555 11927843 := bstep (se 1 (by rfl) ⟨8945882, by rfl⟩ : syracuseStep 11927843 = 17891765) B17891765
theorem B3309875 : Blo 1470555 3309875 := bstep (se 1 (by rfl) ⟨2482406, by rfl⟩ : syracuseStep 3309875 = 4964813) B4964813
theorem B1655095 : Blo 1470555 1655095 := bstep (se 1 (by rfl) ⟨1241321, by rfl⟩ : syracuseStep 1655095 = 2482643) B2482643
theorem B3309911 : Blo 1470555 3309911 := bstep (se 1 (by rfl) ⟨2482433, by rfl⟩ : syracuseStep 3309911 = 4964867) B4964867
theorem B4964759 : Blo 1470555 4964759 := bstep (se 1 (by rfl) ⟨3723569, by rfl⟩ : syracuseStep 4964759 = 7447139) B7447139
theorem B2236825 : Blo 1470555 2236825 := bstep (se 2 (by rfl) ⟨838809, by rfl⟩ : syracuseStep 2236825 = 1677619) B1677619
theorem B1655275 : Blo 1470555 1655275 := bstep (se 1 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 1655275 = 2482913) B2482913
theorem B3310091 : Blo 1470555 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B2794007 : Blo 1470555 2794007 := bstep (se 1 (by rfl) ⟨2095505, by rfl⟩ : syracuseStep 2794007 = 4191011) B4191011
theorem B3310145 : Blo 1470555 3310145 := bstep (se 2 (by rfl) ⟨1241304, by rfl⟩ : syracuseStep 3310145 = 2482609) B2482609
theorem B1655383 : Blo 1470555 1655383 := bstep (se 1 (by rfl) ⟨1241537, by rfl⟩ : syracuseStep 1655383 = 2483075) B2483075
theorem B6709853 : Blo 1470555 6709853 := bstep (se 3 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 6709853 = 2516195) B2516195
theorem B5587649 : Blo 1470555 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B103383793 : Blo 1470555 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B1655563 : Blo 1470555 1655563 := bstep (se 1 (by rfl) ⟨1241672, by rfl⟩ : syracuseStep 1655563 = 2483345) B2483345
theorem B8946449 : Blo 1470555 8946449 := bstep (se 2 (by rfl) ⟨3354918, by rfl⟩ : syracuseStep 8946449 = 6709837) B6709837
theorem B4473623 : Blo 1470555 4473623 := bstep (se 1 (by rfl) ⟨3355217, by rfl⟩ : syracuseStep 4473623 = 6710435) B6710435
theorem B2482967 : Blo 1470555 2482967 := bstep (se 1 (by rfl) ⟨1862225, by rfl⟩ : syracuseStep 2482967 = 3724451) B3724451
theorem B3310361 : Blo 1470555 3310361 := bstep (se 2 (by rfl) ⟨1241385, by rfl⟩ : syracuseStep 3310361 = 2482771) B2482771
theorem B6800203 : Blo 1470555 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B5964637 : Blo 1470555 5964637 := bstep (se 3 (by rfl) ⟨1118369, by rfl⟩ : syracuseStep 5964637 = 2236739) B2236739
theorem B15901541 : Blo 1470555 15901541 := bstep (se 4 (by rfl) ⟨1490769, by rfl⟩ : syracuseStep 15901541 = 2981539) B2981539
theorem B3310451 : Blo 1470555 3310451 := bstep (se 1 (by rfl) ⟨2482838, by rfl⟩ : syracuseStep 3310451 = 4965677) B4965677
theorem B1655671 : Blo 1470555 1655671 := bstep (se 1 (by rfl) ⟨1241753, by rfl⟩ : syracuseStep 1655671 = 2483507) B2483507
theorem B3310487 : Blo 1470555 3310487 := bstep (se 1 (by rfl) ⟨2482865, by rfl⟩ : syracuseStep 3310487 = 4965731) B4965731
theorem B2483095 : Blo 1470555 2483095 := bstep (se 1 (by rfl) ⟨1862321, by rfl⟩ : syracuseStep 2483095 = 3724643) B3724643
theorem B4965299 : Blo 1470555 4965299 := bstep (se 1 (by rfl) ⟨3723974, by rfl⟩ : syracuseStep 4965299 = 7447949) B7447949
theorem B25150499 : Blo 1470555 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B1655851 : Blo 1470555 1655851 := bstep (se 1 (by rfl) ⟨1241888, by rfl⟩ : syracuseStep 1655851 = 2483777) B2483777
theorem B3310667 : Blo 1470555 3310667 := bstep (se 1 (by rfl) ⟨2483000, by rfl⟩ : syracuseStep 3310667 = 4966001) B4966001
theorem B4711517 : Blo 1470555 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B3310721 : Blo 1470555 3310721 := bstep (se 2 (by rfl) ⟨1241520, by rfl⟩ : syracuseStep 3310721 = 2483041) B2483041
theorem B5301379 : Blo 1470555 5301379 := bstep (se 1 (by rfl) ⟨3976034, by rfl⟩ : syracuseStep 5301379 = 7952069) B7952069
theorem B16794755 : Blo 1470555 16794755 := bstep (se 1 (by rfl) ⟨12596066, by rfl⟩ : syracuseStep 16794755 = 25192133) B25192133
theorem B1655959 : Blo 1470555 1655959 := bstep (se 1 (by rfl) ⟨1241969, by rfl⟩ : syracuseStep 1655959 = 2483939) B2483939
theorem B2794675 : Blo 1470555 2794675 := bstep (se 1 (by rfl) ⟨2096006, by rfl⟩ : syracuseStep 2794675 = 4192013) B4192013
theorem B4965569 : Blo 1470555 4965569 := bstep (se 2 (by rfl) ⟨1862088, by rfl⟩ : syracuseStep 4965569 = 3724177) B3724177
theorem B1656139 : Blo 1470555 1656139 := bstep (se 1 (by rfl) ⟨1242104, by rfl⟩ : syracuseStep 1656139 = 2484209) B2484209
theorem B3310937 : Blo 1470555 3310937 := bstep (se 2 (by rfl) ⟨1241601, by rfl⟩ : syracuseStep 3310937 = 2483203) B2483203
theorem B3311027 : Blo 1470555 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B1656247 : Blo 1470555 1656247 := bstep (se 1 (by rfl) ⟨1242185, by rfl⟩ : syracuseStep 1656247 = 2484371) B2484371
theorem B3311063 : Blo 1470555 3311063 := bstep (se 1 (by rfl) ⟨2483297, by rfl⟩ : syracuseStep 3311063 = 4966595) B4966595
theorem B2483723 : Blo 1470555 2483723 := bstep (se 1 (by rfl) ⟨1862792, by rfl⟩ : syracuseStep 2483723 = 3725585) B3725585
theorem B11167307 : Blo 1470555 11167307 := bstep (se 1 (by rfl) ⟨8375480, by rfl⟩ : syracuseStep 11167307 = 16750961) B16750961
theorem B5662297 : Blo 1470555 5662297 := bstep (se 2 (by rfl) ⟨2123361, by rfl⟩ : syracuseStep 5662297 = 4246723) B4246723
theorem B13428317 : Blo 1470555 13428317 := bstep (se 3 (by rfl) ⟨2517809, by rfl⟩ : syracuseStep 13428317 = 5035619) B5035619
theorem B22668893 : Blo 1470555 22668893 := bstep (se 3 (by rfl) ⟨4250417, by rfl⟩ : syracuseStep 22668893 = 8500835) B8500835
theorem B1656427 : Blo 1470555 1656427 := bstep (se 1 (by rfl) ⟨1242320, by rfl⟩ : syracuseStep 1656427 = 2484641) B2484641
theorem B2795123 : Blo 1470555 2795123 := bstep (se 1 (by rfl) ⟨2096342, by rfl⟩ : syracuseStep 2795123 = 4192685) B4192685
theorem B3311243 : Blo 1470555 3311243 := bstep (se 1 (by rfl) ⟨2483432, by rfl⟩ : syracuseStep 3311243 = 4966865) B4966865
theorem B2483851 : Blo 1470555 2483851 := bstep (se 1 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 2483851 = 3725777) B3725777
theorem B2795161 : Blo 1470555 2795161 := bstep (se 2 (by rfl) ⟨1048185, by rfl⟩ : syracuseStep 2795161 = 2096371) B2096371
theorem B3311297 : Blo 1470555 3311297 := bstep (se 2 (by rfl) ⟨1241736, by rfl⟩ : syracuseStep 3311297 = 2483473) B2483473
theorem B1656535 : Blo 1470555 1656535 := bstep (se 1 (by rfl) ⟨1242401, by rfl⟩ : syracuseStep 1656535 = 2484803) B2484803
theorem B4966109 : Blo 1470555 4966109 := bstep (se 3 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 4966109 = 1862291) B1862291
theorem B2483993 : Blo 1470555 2483993 := bstep (se 2 (by rfl) ⟨931497, by rfl⟩ : syracuseStep 2483993 = 1862995) B1862995
theorem B4187969 : Blo 1470555 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B3974987 : Blo 1470555 3974987 := bstep (se 1 (by rfl) ⟨2981240, by rfl⟩ : syracuseStep 3974987 = 5962481) B5962481
theorem B7071563 : Blo 1470555 7071563 := bstep (se 1 (by rfl) ⟨5303672, by rfl⟩ : syracuseStep 7071563 = 10607345) B10607345
theorem B7071619 : Blo 1470555 7071619 := bstep (se 1 (by rfl) ⟨5303714, by rfl⟩ : syracuseStep 7071619 = 10607429) B10607429
theorem B3311513 : Blo 1470555 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B2484121 : Blo 1470555 2484121 := bstep (se 2 (by rfl) ⟨931545, by rfl⟩ : syracuseStep 2484121 = 1863091) B1863091
theorem B5588909 : Blo 1470555 5588909 := bstep (se 3 (by rfl) ⟨1047920, by rfl⟩ : syracuseStep 5588909 = 2095841) B2095841
theorem B2983859 : Blo 1470555 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B5588939 : Blo 1470555 5588939 := bstep (se 1 (by rfl) ⟨4191704, by rfl⟩ : syracuseStep 5588939 = 8383409) B8383409
theorem B31803353 : Blo 1470555 31803353 := bstep (se 2 (by rfl) ⟨11926257, by rfl⟩ : syracuseStep 31803353 = 23852515) B23852515
theorem B3311603 : Blo 1470555 3311603 := bstep (se 1 (by rfl) ⟨2483702, by rfl⟩ : syracuseStep 3311603 = 4967405) B4967405
theorem B1861643 : Blo 1470555 1861643 := bstep (se 1 (by rfl) ⟨1396232, by rfl⟩ : syracuseStep 1861643 = 2792465) B2792465
theorem B3311639 : Blo 1470555 3311639 := bstep (se 1 (by rfl) ⟨2483729, by rfl⟩ : syracuseStep 3311639 = 4967459) B4967459
theorem B3975257 : Blo 1470555 3975257 := bstep (se 2 (by rfl) ⟨1490721, by rfl⟩ : syracuseStep 3975257 = 2981443) B2981443
theorem B20695171 : Blo 1470555 20695171 := bstep (se 1 (by rfl) ⟨15521378, by rfl⟩ : syracuseStep 20695171 = 31042757) B31042757
theorem B4188311 : Blo 1470555 4188311 := bstep (se 1 (by rfl) ⟨3141233, by rfl⟩ : syracuseStep 4188311 = 6282467) B6282467
theorem B60418199 : Blo 1470555 60418199 := bstep (se 1 (by rfl) ⟨45313649, by rfl⟩ : syracuseStep 60418199 = 90627299) B90627299
theorem B2205899 : Blo 1470555 2205899 := bstep (se 1 (by rfl) ⟨1654424, by rfl⟩ : syracuseStep 2205899 = 3308849) B3308849
theorem B3311819 : Blo 1470555 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B2205911 : Blo 1470555 2205911 := bstep (se 1 (by rfl) ⟨1654433, by rfl⟩ : syracuseStep 2205911 = 3308867) B3308867
theorem B3311873 : Blo 1470555 3311873 := bstep (se 2 (by rfl) ⟨1241952, by rfl⟩ : syracuseStep 3311873 = 2483905) B2483905
theorem B2205977 : Blo 1470555 2205977 := bstep (se 2 (by rfl) ⟨827241, by rfl⟩ : syracuseStep 2205977 = 1654483) B1654483
theorem B13420835 : Blo 1470555 13420835 := bstep (se 1 (by rfl) ⟨10065626, by rfl⟩ : syracuseStep 13420835 = 20131253) B20131253
theorem B16771373 : Blo 1470555 16771373 := bstep (se 3 (by rfl) ⟨3144632, by rfl⟩ : syracuseStep 16771373 = 6289265) B6289265
theorem B2206091 : Blo 1470555 2206091 := bstep (se 1 (by rfl) ⟨1654568, by rfl⟩ : syracuseStep 2206091 = 3309137) B3309137
theorem B2206103 : Blo 1470555 2206103 := bstep (se 1 (by rfl) ⟨1654577, by rfl⟩ : syracuseStep 2206103 = 3309155) B3309155
theorem B2484695 : Blo 1470555 2484695 := bstep (se 1 (by rfl) ⟨1863521, by rfl⟩ : syracuseStep 2484695 = 3727043) B3727043
theorem B2206169 : Blo 1470555 2206169 := bstep (se 2 (by rfl) ⟨827313, by rfl⟩ : syracuseStep 2206169 = 1654627) B1654627
theorem B3312089 : Blo 1470555 3312089 := bstep (se 2 (by rfl) ⟨1242033, by rfl⟩ : syracuseStep 3312089 = 2484067) B2484067
theorem B5966387 : Blo 1470555 5966387 := bstep (se 1 (by rfl) ⟨4474790, by rfl⟩ : syracuseStep 5966387 = 8949581) B8949581
theorem B3312179 : Blo 1470555 3312179 := bstep (se 1 (by rfl) ⟨2484134, by rfl⟩ : syracuseStep 3312179 = 4968269) B4968269
theorem B2206283 : Blo 1470555 2206283 := bstep (se 1 (by rfl) ⟨1654712, by rfl⟩ : syracuseStep 2206283 = 3309425) B3309425
theorem B2206295 : Blo 1470555 2206295 := bstep (se 1 (by rfl) ⟨1654721, by rfl⟩ : syracuseStep 2206295 = 3309443) B3309443
theorem B3312215 : Blo 1470555 3312215 := bstep (se 1 (by rfl) ⟨2484161, by rfl⟩ : syracuseStep 3312215 = 4968323) B4968323
theorem B5589593 : Blo 1470555 5589593 := bstep (se 2 (by rfl) ⟨2096097, by rfl⟩ : syracuseStep 5589593 = 4192195) B4192195
theorem B2484823 : Blo 1470555 2484823 := bstep (se 1 (by rfl) ⟨1863617, by rfl⟩ : syracuseStep 2484823 = 3727235) B3727235
theorem B6285917 : Blo 1470555 6285917 := bstep (se 3 (by rfl) ⟨1178609, by rfl⟩ : syracuseStep 6285917 = 2357219) B2357219
theorem B11176541 : Blo 1470555 11176541 := bstep (se 3 (by rfl) ⟨2095601, by rfl⟩ : syracuseStep 11176541 = 4191203) B4191203
theorem B2206361 : Blo 1470555 2206361 := bstep (se 2 (by rfl) ⟨827385, by rfl⟩ : syracuseStep 2206361 = 1654771) B1654771
theorem B1862347 : Blo 1470555 1862347 := bstep (se 1 (by rfl) ⟨1396760, by rfl⟩ : syracuseStep 1862347 = 2793521) B2793521
theorem B2206475 : Blo 1470555 2206475 := bstep (se 1 (by rfl) ⟨1654856, by rfl⟩ : syracuseStep 2206475 = 3309713) B3309713
theorem B3312395 : Blo 1470555 3312395 := bstep (se 1 (by rfl) ⟨2484296, by rfl⟩ : syracuseStep 3312395 = 4968593) B4968593
theorem B2206487 : Blo 1470555 2206487 := bstep (se 1 (by rfl) ⟨1654865, by rfl⟩ : syracuseStep 2206487 = 3309731) B3309731
theorem B3312449 : Blo 1470555 3312449 := bstep (se 2 (by rfl) ⟨1242168, by rfl⟩ : syracuseStep 3312449 = 2484337) B2484337
theorem B4967243 : Blo 1470555 4967243 := bstep (se 1 (by rfl) ⟨3725432, by rfl⟩ : syracuseStep 4967243 = 7450865) B7450865
theorem B2206553 : Blo 1470555 2206553 := bstep (se 2 (by rfl) ⟨827457, by rfl⟩ : syracuseStep 2206553 = 1654915) B1654915
theorem B5589911 : Blo 1470555 5589911 := bstep (se 1 (by rfl) ⟨4192433, by rfl⟩ : syracuseStep 5589911 = 8384867) B8384867
theorem B2984897 : Blo 1470555 2984897 := bstep (se 2 (by rfl) ⟨1119336, by rfl⟩ : syracuseStep 2984897 = 2238673) B2238673
theorem B2206667 : Blo 1470555 2206667 := bstep (se 1 (by rfl) ⟨1655000, by rfl⟩ : syracuseStep 2206667 = 3310001) B3310001
theorem B2206679 : Blo 1470555 2206679 := bstep (se 1 (by rfl) ⟨1655009, by rfl⟩ : syracuseStep 2206679 = 3310019) B3310019
theorem B1862615 : Blo 1470555 1862615 := bstep (se 1 (by rfl) ⟨1396961, by rfl⟩ : syracuseStep 1862615 = 2793923) B2793923
theorem B167668697 : Blo 1470555 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B2206745 : Blo 1470555 2206745 := bstep (se 2 (by rfl) ⟨827529, by rfl⟩ : syracuseStep 2206745 = 1655059) B1655059
theorem B3312665 : Blo 1470555 3312665 := bstep (se 2 (by rfl) ⟨1242249, by rfl⟩ : syracuseStep 3312665 = 2484499) B2484499
theorem B4967513 : Blo 1470555 4967513 := bstep (se 2 (by rfl) ⟨1862817, by rfl⟩ : syracuseStep 4967513 = 3725635) B3725635
theorem B3312755 : Blo 1470555 3312755 := bstep (se 1 (by rfl) ⟨2484566, by rfl⟩ : syracuseStep 3312755 = 4969133) B4969133
theorem B7449731 : Blo 1470555 7449731 := bstep (se 1 (by rfl) ⟨5587298, by rfl⟩ : syracuseStep 7449731 = 11174597) B11174597
theorem B2206859 : Blo 1470555 2206859 := bstep (se 1 (by rfl) ⟨1655144, by rfl⟩ : syracuseStep 2206859 = 3310289) B3310289
theorem B5303441 : Blo 1470555 5303441 := bstep (se 2 (by rfl) ⟨1988790, by rfl⟩ : syracuseStep 5303441 = 3977581) B3977581
theorem B2206871 : Blo 1470555 2206871 := bstep (se 1 (by rfl) ⟨1655153, by rfl⟩ : syracuseStep 2206871 = 3310307) B3310307
theorem B3312791 : Blo 1470555 3312791 := bstep (se 1 (by rfl) ⟨2484593, by rfl⟩ : syracuseStep 3312791 = 4969187) B4969187
theorem B2206937 : Blo 1470555 2206937 := bstep (se 2 (by rfl) ⟨827601, by rfl⟩ : syracuseStep 2206937 = 1655203) B1655203
theorem B2207051 : Blo 1470555 2207051 := bstep (se 1 (by rfl) ⟨1655288, by rfl⟩ : syracuseStep 2207051 = 3310577) B3310577
theorem B10612043 : Blo 1470555 10612043 := bstep (se 1 (by rfl) ⟨7959032, by rfl⟩ : syracuseStep 10612043 = 15918065) B15918065
theorem B3312971 : Blo 1470555 3312971 := bstep (se 1 (by rfl) ⟨2484728, by rfl⟩ : syracuseStep 3312971 = 4969457) B4969457
theorem B2207063 : Blo 1470555 2207063 := bstep (se 1 (by rfl) ⟨1655297, by rfl⟩ : syracuseStep 2207063 = 3310595) B3310595
theorem B3313025 : Blo 1470555 3313025 := bstep (se 2 (by rfl) ⟨1242384, by rfl⟩ : syracuseStep 3313025 = 2484769) B2484769
theorem B2207129 : Blo 1470555 2207129 := bstep (se 2 (by rfl) ⟨827673, by rfl⟩ : syracuseStep 2207129 = 1655347) B1655347
theorem B3354049 : Blo 1470555 3354049 := bstep (se 2 (by rfl) ⟨1257768, by rfl⟩ : syracuseStep 3354049 = 2515537) B2515537
theorem B6712769 : Blo 1470555 6712769 := bstep (se 2 (by rfl) ⟨2517288, by rfl⟩ : syracuseStep 6712769 = 5034577) B5034577
theorem B3722699 : Blo 1470555 3722699 := bstep (se 1 (by rfl) ⟨2792024, by rfl⟩ : syracuseStep 3722699 = 5584049) B5584049
theorem B2207243 : Blo 1470555 2207243 := bstep (se 1 (by rfl) ⟨1655432, by rfl⟩ : syracuseStep 2207243 = 3310865) B3310865
theorem B2207255 : Blo 1470555 2207255 := bstep (se 1 (by rfl) ⟨1655441, by rfl⟩ : syracuseStep 2207255 = 3310883) B3310883
theorem B5590579 : Blo 1470555 5590579 := bstep (se 1 (by rfl) ⟨4192934, by rfl⟩ : syracuseStep 5590579 = 8385869) B8385869
theorem B2207321 : Blo 1470555 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B3313241 : Blo 1470555 3313241 := bstep (se 2 (by rfl) ⟨1242465, by rfl⟩ : syracuseStep 3313241 = 2484931) B2484931
theorem B8384093 : Blo 1470555 8384093 := bstep (se 3 (by rfl) ⟨1572017, by rfl⟩ : syracuseStep 8384093 = 3144035) B3144035
theorem B1863319 : Blo 1470555 1863319 := bstep (se 1 (by rfl) ⟨1397489, by rfl⟩ : syracuseStep 1863319 = 2794979) B2794979
theorem B25128629 : Blo 1470555 25128629 := bstep (se 5 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 25128629 = 2355809) B2355809
theorem B2207435 : Blo 1470555 2207435 := bstep (se 1 (by rfl) ⟨1655576, by rfl⟩ : syracuseStep 2207435 = 3311153) B3311153
theorem B2207447 : Blo 1470555 2207447 := bstep (se 1 (by rfl) ⟨1655585, by rfl⟩ : syracuseStep 2207447 = 3311171) B3311171
theorem B12570329 : Blo 1470555 12570329 := bstep (se 2 (by rfl) ⟨4713873, by rfl⟩ : syracuseStep 12570329 = 9427747) B9427747
theorem B4968215 : Blo 1470555 4968215 := bstep (se 1 (by rfl) ⟨3726161, by rfl⟩ : syracuseStep 4968215 = 7452323) B7452323
theorem B2207513 : Blo 1470555 2207513 := bstep (se 2 (by rfl) ⟨827817, by rfl⟩ : syracuseStep 2207513 = 1655635) B1655635
theorem B2207627 : Blo 1470555 2207627 := bstep (se 1 (by rfl) ⟨1655720, by rfl⟩ : syracuseStep 2207627 = 3311441) B3311441
theorem B2207639 : Blo 1470555 2207639 := bstep (se 1 (by rfl) ⟨1655729, by rfl⟩ : syracuseStep 2207639 = 3311459) B3311459
theorem B2207705 : Blo 1470555 2207705 := bstep (se 2 (by rfl) ⟨827889, by rfl⟩ : syracuseStep 2207705 = 1655779) B1655779
theorem B2207819 : Blo 1470555 2207819 := bstep (se 1 (by rfl) ⟨1655864, by rfl⟩ : syracuseStep 2207819 = 3311729) B3311729
theorem B2207831 : Blo 1470555 2207831 := bstep (se 1 (by rfl) ⟨1655873, by rfl⟩ : syracuseStep 2207831 = 3311747) B3311747
theorem B1470571 : Blo 1470555 1470571 := bstep (se 1 (by rfl) ⟨1102928, by rfl⟩ : syracuseStep 1470571 = 2205857) B2205857
theorem B1470583 : Blo 1470555 1470583 := bstep (se 1 (by rfl) ⟨1102937, by rfl⟩ : syracuseStep 1470583 = 2205875) B2205875
theorem B15913091 : Blo 1470555 15913091 := bstep (se 1 (by rfl) ⟨11934818, by rfl⟩ : syracuseStep 15913091 = 23869637) B23869637
theorem B1470603 : Blo 1470555 1470603 := bstep (se 1 (by rfl) ⟨1102952, by rfl⟩ : syracuseStep 1470603 = 2205905) B2205905
theorem B1470615 : Blo 1470555 1470615 := bstep (se 1 (by rfl) ⟨1102961, by rfl⟩ : syracuseStep 1470615 = 2205923) B2205923
theorem B2207897 : Blo 1470555 2207897 := bstep (se 2 (by rfl) ⟨827961, by rfl⟩ : syracuseStep 2207897 = 1655923) B1655923
theorem B1470635 : Blo 1470555 1470635 := bstep (se 1 (by rfl) ⟨1102976, by rfl⟩ : syracuseStep 1470635 = 2205953) B2205953
theorem B1470647 : Blo 1470555 1470647 := bstep (se 1 (by rfl) ⟨1102985, by rfl⟩ : syracuseStep 1470647 = 2205971) B2205971
theorem B1470667 : Blo 1470555 1470667 := bstep (se 1 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 1470667 = 2206001) B2206001
theorem B3977419 : Blo 1470555 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B5304523 : Blo 1470555 5304523 := bstep (se 1 (by rfl) ⟨3978392, by rfl⟩ : syracuseStep 5304523 = 7956785) B7956785
theorem B1470679 : Blo 1470555 1470679 := bstep (se 1 (by rfl) ⟨1103009, by rfl⟩ : syracuseStep 1470679 = 2206019) B2206019
theorem B4190429 : Blo 1470555 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B1470699 : Blo 1470555 1470699 := bstep (se 1 (by rfl) ⟨1103024, by rfl⟩ : syracuseStep 1470699 = 2206049) B2206049
theorem B1470711 : Blo 1470555 1470711 := bstep (se 1 (by rfl) ⟨1103033, by rfl⟩ : syracuseStep 1470711 = 2206067) B2206067
theorem B12579077 : Blo 1470555 12579077 := bstep (se 4 (by rfl) ⟨1179288, by rfl⟩ : syracuseStep 12579077 = 2358577) B2358577
theorem B1470731 : Blo 1470555 1470731 := bstep (se 1 (by rfl) ⟨1103048, by rfl⟩ : syracuseStep 1470731 = 2206097) B2206097
theorem B2208011 : Blo 1470555 2208011 := bstep (se 1 (by rfl) ⟨1656008, by rfl⟩ : syracuseStep 2208011 = 3312017) B3312017
theorem B1470743 : Blo 1470555 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B2208023 : Blo 1470555 2208023 := bstep (se 1 (by rfl) ⟨1656017, by rfl⟩ : syracuseStep 2208023 = 3312035) B3312035
theorem B1470763 : Blo 1470555 1470763 := bstep (se 1 (by rfl) ⟨1103072, by rfl⟩ : syracuseStep 1470763 = 2206145) B2206145
theorem B4968755 : Blo 1470555 4968755 := bstep (se 1 (by rfl) ⟨3726566, by rfl⟩ : syracuseStep 4968755 = 7453133) B7453133
theorem B1470775 : Blo 1470555 1470775 := bstep (se 1 (by rfl) ⟨1103081, by rfl⟩ : syracuseStep 1470775 = 2206163) B2206163
theorem B1470795 : Blo 1470555 1470795 := bstep (se 1 (by rfl) ⟨1103096, by rfl⟩ : syracuseStep 1470795 = 2206193) B2206193
theorem B1470807 : Blo 1470555 1470807 := bstep (se 1 (by rfl) ⟨1103105, by rfl⟩ : syracuseStep 1470807 = 2206211) B2206211
theorem B2208089 : Blo 1470555 2208089 := bstep (se 2 (by rfl) ⟨828033, by rfl⟩ : syracuseStep 2208089 = 1656067) B1656067
theorem B1470827 : Blo 1470555 1470827 := bstep (se 1 (by rfl) ⟨1103120, by rfl⟩ : syracuseStep 1470827 = 2206241) B2206241
theorem B1470839 : Blo 1470555 1470839 := bstep (se 1 (by rfl) ⟨1103129, by rfl⟩ : syracuseStep 1470839 = 2206259) B2206259
theorem B1470859 : Blo 1470555 1470859 := bstep (se 1 (by rfl) ⟨1103144, by rfl⟩ : syracuseStep 1470859 = 2206289) B2206289
theorem B1470871 : Blo 1470555 1470871 := bstep (se 1 (by rfl) ⟨1103153, by rfl⟩ : syracuseStep 1470871 = 2206307) B2206307
theorem B3723671 : Blo 1470555 3723671 := bstep (se 1 (by rfl) ⟨2792753, by rfl⟩ : syracuseStep 3723671 = 5585507) B5585507
theorem B1470891 : Blo 1470555 1470891 := bstep (se 1 (by rfl) ⟨1103168, by rfl⟩ : syracuseStep 1470891 = 2206337) B2206337
theorem B1470903 : Blo 1470555 1470903 := bstep (se 1 (by rfl) ⟨1103177, by rfl⟩ : syracuseStep 1470903 = 2206355) B2206355
theorem B1470923 : Blo 1470555 1470923 := bstep (se 1 (by rfl) ⟨1103192, by rfl⟩ : syracuseStep 1470923 = 2206385) B2206385
theorem B2208203 : Blo 1470555 2208203 := bstep (se 1 (by rfl) ⟨1656152, by rfl⟩ : syracuseStep 2208203 = 3312305) B3312305
theorem B1470935 : Blo 1470555 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B2208215 : Blo 1470555 2208215 := bstep (se 1 (by rfl) ⟨1656161, by rfl⟩ : syracuseStep 2208215 = 3312323) B3312323
theorem B1470955 : Blo 1470555 1470955 := bstep (se 1 (by rfl) ⟨1103216, by rfl⟩ : syracuseStep 1470955 = 2206433) B2206433
theorem B2830835 : Blo 1470555 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B1470967 : Blo 1470555 1470967 := bstep (se 1 (by rfl) ⟨1103225, by rfl⟩ : syracuseStep 1470967 = 2206451) B2206451
theorem B1470987 : Blo 1470555 1470987 := bstep (se 1 (by rfl) ⟨1103240, by rfl⟩ : syracuseStep 1470987 = 2206481) B2206481
theorem B1470999 : Blo 1470555 1470999 := bstep (se 1 (by rfl) ⟨1103249, by rfl⟩ : syracuseStep 1470999 = 2206499) B2206499
theorem B2208281 : Blo 1470555 2208281 := bstep (se 2 (by rfl) ⟨828105, by rfl⟩ : syracuseStep 2208281 = 1656211) B1656211
theorem B1471019 : Blo 1470555 1471019 := bstep (se 1 (by rfl) ⟨1103264, by rfl⟩ : syracuseStep 1471019 = 2206529) B2206529
theorem B4190771 : Blo 1470555 4190771 := bstep (se 1 (by rfl) ⟨3143078, by rfl⟩ : syracuseStep 4190771 = 6286157) B6286157
theorem B1471031 : Blo 1470555 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B4969025 : Blo 1470555 4969025 := bstep (se 2 (by rfl) ⟨1863384, by rfl⟩ : syracuseStep 4969025 = 3726769) B3726769
theorem B1471051 : Blo 1470555 1471051 := bstep (se 1 (by rfl) ⟨1103288, by rfl⟩ : syracuseStep 1471051 = 2206577) B2206577
theorem B1471063 : Blo 1470555 1471063 := bstep (se 1 (by rfl) ⟨1103297, by rfl⟩ : syracuseStep 1471063 = 2206595) B2206595
theorem B1471083 : Blo 1470555 1471083 := bstep (se 1 (by rfl) ⟨1103312, by rfl⟩ : syracuseStep 1471083 = 2206625) B2206625
theorem B1471095 : Blo 1470555 1471095 := bstep (se 1 (by rfl) ⟨1103321, by rfl⟩ : syracuseStep 1471095 = 2206643) B2206643
theorem B1471115 : Blo 1470555 1471115 := bstep (se 1 (by rfl) ⟨1103336, by rfl⟩ : syracuseStep 1471115 = 2206673) B2206673
theorem B2208395 : Blo 1470555 2208395 := bstep (se 1 (by rfl) ⟨1656296, by rfl⟩ : syracuseStep 2208395 = 3312593) B3312593
theorem B5968529 : Blo 1470555 5968529 := bstep (se 2 (by rfl) ⟨2238198, by rfl⟩ : syracuseStep 5968529 = 4476397) B4476397
theorem B1471127 : Blo 1470555 1471127 := bstep (se 1 (by rfl) ⟨1103345, by rfl⟩ : syracuseStep 1471127 = 2206691) B2206691
theorem B2208407 : Blo 1470555 2208407 := bstep (se 1 (by rfl) ⟨1656305, by rfl⟩ : syracuseStep 2208407 = 3312611) B3312611
theorem B1471147 : Blo 1470555 1471147 := bstep (se 1 (by rfl) ⟨1103360, by rfl⟩ : syracuseStep 1471147 = 2206721) B2206721
theorem B1471159 : Blo 1470555 1471159 := bstep (se 1 (by rfl) ⟨1103369, by rfl⟩ : syracuseStep 1471159 = 2206739) B2206739
theorem B5583563 : Blo 1470555 5583563 := bstep (se 1 (by rfl) ⟨4187672, by rfl⟩ : syracuseStep 5583563 = 8375345) B8375345
theorem B1471179 : Blo 1470555 1471179 := bstep (se 1 (by rfl) ⟨1103384, by rfl⟩ : syracuseStep 1471179 = 2206769) B2206769
theorem B1471191 : Blo 1470555 1471191 := bstep (se 1 (by rfl) ⟨1103393, by rfl⟩ : syracuseStep 1471191 = 2206787) B2206787
theorem B2208473 : Blo 1470555 2208473 := bstep (se 2 (by rfl) ⟨828177, by rfl⟩ : syracuseStep 2208473 = 1656355) B1656355
theorem B1471211 : Blo 1470555 1471211 := bstep (se 1 (by rfl) ⟨1103408, by rfl⟩ : syracuseStep 1471211 = 2206817) B2206817
theorem B21205745 : Blo 1470555 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B1471223 : Blo 1470555 1471223 := bstep (se 1 (by rfl) ⟨1103417, by rfl⟩ : syracuseStep 1471223 = 2206835) B2206835
theorem B2831105 : Blo 1470555 2831105 := bstep (se 2 (by rfl) ⟨1061664, by rfl⟩ : syracuseStep 2831105 = 2123329) B2123329
theorem B1471243 : Blo 1470555 1471243 := bstep (se 1 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 1471243 = 2206865) B2206865
theorem B7951121 : Blo 1470555 7951121 := bstep (se 2 (by rfl) ⟨2981670, by rfl⟩ : syracuseStep 7951121 = 5963341) B5963341
theorem B7959313 : Blo 1470555 7959313 := bstep (se 2 (by rfl) ⟨2984742, by rfl⟩ : syracuseStep 7959313 = 5969485) B5969485
theorem B1471255 : Blo 1470555 1471255 := bstep (se 1 (by rfl) ⟨1103441, by rfl⟩ : syracuseStep 1471255 = 2206883) B2206883
theorem B1471275 : Blo 1470555 1471275 := bstep (se 1 (by rfl) ⟨1103456, by rfl⟩ : syracuseStep 1471275 = 2206913) B2206913
theorem B1471287 : Blo 1470555 1471287 := bstep (se 1 (by rfl) ⟨1103465, by rfl⟩ : syracuseStep 1471287 = 2206931) B2206931
theorem B1471307 : Blo 1470555 1471307 := bstep (se 1 (by rfl) ⟨1103480, by rfl⟩ : syracuseStep 1471307 = 2206961) B2206961
theorem B2208587 : Blo 1470555 2208587 := bstep (se 1 (by rfl) ⟨1656440, by rfl⟩ : syracuseStep 2208587 = 3312881) B3312881
theorem B1471319 : Blo 1470555 1471319 := bstep (se 1 (by rfl) ⟨1103489, by rfl⟩ : syracuseStep 1471319 = 2206979) B2206979
theorem B2208599 : Blo 1470555 2208599 := bstep (se 1 (by rfl) ⟨1656449, by rfl⟩ : syracuseStep 2208599 = 3312899) B3312899
theorem B1471339 : Blo 1470555 1471339 := bstep (se 1 (by rfl) ⟨1103504, by rfl⟩ : syracuseStep 1471339 = 2207009) B2207009
theorem B1471351 : Blo 1470555 1471351 := bstep (se 1 (by rfl) ⟨1103513, by rfl⟩ : syracuseStep 1471351 = 2207027) B2207027
theorem B1471371 : Blo 1470555 1471371 := bstep (se 1 (by rfl) ⟨1103528, by rfl⟩ : syracuseStep 1471371 = 2207057) B2207057
theorem B5583761 : Blo 1470555 5583761 := bstep (se 2 (by rfl) ⟨2093910, by rfl⟩ : syracuseStep 5583761 = 4187821) B4187821
theorem B1471383 : Blo 1470555 1471383 := bstep (se 1 (by rfl) ⟨1103537, by rfl⟩ : syracuseStep 1471383 = 2207075) B2207075
theorem B2208665 : Blo 1470555 2208665 := bstep (se 2 (by rfl) ⟨828249, by rfl⟩ : syracuseStep 2208665 = 1656499) B1656499
theorem B1471403 : Blo 1470555 1471403 := bstep (se 1 (by rfl) ⟨1103552, by rfl⟩ : syracuseStep 1471403 = 2207105) B2207105
theorem B1471415 : Blo 1470555 1471415 := bstep (se 1 (by rfl) ⟨1103561, by rfl⟩ : syracuseStep 1471415 = 2207123) B2207123
theorem B1471435 : Blo 1470555 1471435 := bstep (se 1 (by rfl) ⟨1103576, by rfl⟩ : syracuseStep 1471435 = 2207153) B2207153
theorem B1471447 : Blo 1470555 1471447 := bstep (se 1 (by rfl) ⟨1103585, by rfl⟩ : syracuseStep 1471447 = 2207171) B2207171
theorem B1471467 : Blo 1470555 1471467 := bstep (se 1 (by rfl) ⟨1103600, by rfl⟩ : syracuseStep 1471467 = 2207201) B2207201
theorem B2651123 : Blo 1470555 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B1471479 : Blo 1470555 1471479 := bstep (se 1 (by rfl) ⟨1103609, by rfl⟩ : syracuseStep 1471479 = 2207219) B2207219
theorem B1471499 : Blo 1470555 1471499 := bstep (se 1 (by rfl) ⟨1103624, by rfl⟩ : syracuseStep 1471499 = 2207249) B2207249
theorem B2208779 : Blo 1470555 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B1471511 : Blo 1470555 1471511 := bstep (se 1 (by rfl) ⟨1103633, by rfl⟩ : syracuseStep 1471511 = 2207267) B2207267
theorem B2208791 : Blo 1470555 2208791 := bstep (se 1 (by rfl) ⟨1656593, by rfl⟩ : syracuseStep 2208791 = 3313187) B3313187
theorem B3355673 : Blo 1470555 3355673 := bstep (se 2 (by rfl) ⟨1258377, by rfl⟩ : syracuseStep 3355673 = 2516755) B2516755
theorem B1471531 : Blo 1470555 1471531 := bstep (se 1 (by rfl) ⟨1103648, by rfl⟩ : syracuseStep 1471531 = 2207297) B2207297
theorem B3724339 : Blo 1470555 3724339 := bstep (se 1 (by rfl) ⟨2793254, by rfl⟩ : syracuseStep 3724339 = 5586509) B5586509
theorem B1471543 : Blo 1470555 1471543 := bstep (se 1 (by rfl) ⟨1103657, by rfl⟩ : syracuseStep 1471543 = 2207315) B2207315
theorem B1471563 : Blo 1470555 1471563 := bstep (se 1 (by rfl) ⟨1103672, by rfl⟩ : syracuseStep 1471563 = 2207345) B2207345
theorem B1471575 : Blo 1470555 1471575 := bstep (se 1 (by rfl) ⟨1103681, by rfl⟩ : syracuseStep 1471575 = 2207363) B2207363
theorem B4969565 : Blo 1470555 4969565 := bstep (se 3 (by rfl) ⟨931793, by rfl⟩ : syracuseStep 4969565 = 1863587) B1863587
theorem B1471595 : Blo 1470555 1471595 := bstep (se 1 (by rfl) ⟨1103696, by rfl⟩ : syracuseStep 1471595 = 2207393) B2207393
theorem B1471607 : Blo 1470555 1471607 := bstep (se 1 (by rfl) ⟨1103705, by rfl⟩ : syracuseStep 1471607 = 2207411) B2207411
theorem B6288515 : Blo 1470555 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B1471627 : Blo 1470555 1471627 := bstep (se 1 (by rfl) ⟨1103720, by rfl⟩ : syracuseStep 1471627 = 2207441) B2207441
theorem B1471639 : Blo 1470555 1471639 := bstep (se 1 (by rfl) ⟨1103729, by rfl⟩ : syracuseStep 1471639 = 2207459) B2207459
theorem B1471659 : Blo 1470555 1471659 := bstep (se 1 (by rfl) ⟨1103744, by rfl⟩ : syracuseStep 1471659 = 2207489) B2207489
theorem B1471671 : Blo 1470555 1471671 := bstep (se 1 (by rfl) ⟨1103753, by rfl⟩ : syracuseStep 1471671 = 2207507) B2207507
theorem B3724481 : Blo 1470555 3724481 := bstep (se 2 (by rfl) ⟨1396680, by rfl⟩ : syracuseStep 3724481 = 2793361) B2793361
theorem B2651339 : Blo 1470555 2651339 := bstep (se 1 (by rfl) ⟨1988504, by rfl⟩ : syracuseStep 2651339 = 3977009) B3977009
theorem B1471691 : Blo 1470555 1471691 := bstep (se 1 (by rfl) ⟨1103768, by rfl⟩ : syracuseStep 1471691 = 2207537) B2207537
theorem B1471703 : Blo 1470555 1471703 := bstep (se 1 (by rfl) ⟨1103777, by rfl⟩ : syracuseStep 1471703 = 2207555) B2207555
theorem B1471723 : Blo 1470555 1471723 := bstep (se 1 (by rfl) ⟨1103792, by rfl⟩ : syracuseStep 1471723 = 2207585) B2207585
theorem B1471735 : Blo 1470555 1471735 := bstep (se 1 (by rfl) ⟨1103801, by rfl⟩ : syracuseStep 1471735 = 2207603) B2207603
theorem B1471755 : Blo 1470555 1471755 := bstep (se 1 (by rfl) ⟨1103816, by rfl⟩ : syracuseStep 1471755 = 2207633) B2207633
theorem B1471767 : Blo 1470555 1471767 := bstep (se 1 (by rfl) ⟨1103825, by rfl⟩ : syracuseStep 1471767 = 2207651) B2207651
theorem B1471787 : Blo 1470555 1471787 := bstep (se 1 (by rfl) ⟨1103840, by rfl⟩ : syracuseStep 1471787 = 2207681) B2207681
theorem B5305645 : Blo 1470555 5305645 := bstep (se 3 (by rfl) ⟨994808, by rfl⟩ : syracuseStep 5305645 = 1989617) B1989617
theorem B1471799 : Blo 1470555 1471799 := bstep (se 1 (by rfl) ⟨1103849, by rfl⟩ : syracuseStep 1471799 = 2207699) B2207699
theorem B12571969 : Blo 1470555 12571969 := bstep (se 2 (by rfl) ⟨4714488, by rfl⟩ : syracuseStep 12571969 = 9428977) B9428977
theorem B1471819 : Blo 1470555 1471819 := bstep (se 1 (by rfl) ⟨1103864, by rfl⟩ : syracuseStep 1471819 = 2207729) B2207729
theorem B1471831 : Blo 1470555 1471831 := bstep (se 1 (by rfl) ⟨1103873, by rfl⟩ : syracuseStep 1471831 = 2207747) B2207747
theorem B1471851 : Blo 1470555 1471851 := bstep (se 1 (by rfl) ⟨1103888, by rfl⟩ : syracuseStep 1471851 = 2207777) B2207777
theorem B1471863 : Blo 1470555 1471863 := bstep (se 1 (by rfl) ⟨1103897, by rfl⟩ : syracuseStep 1471863 = 2207795) B2207795
theorem B1471883 : Blo 1470555 1471883 := bstep (se 1 (by rfl) ⟨1103912, by rfl⟩ : syracuseStep 1471883 = 2207825) B2207825
theorem B1471895 : Blo 1470555 1471895 := bstep (se 1 (by rfl) ⟨1103921, by rfl⟩ : syracuseStep 1471895 = 2207843) B2207843
theorem B1471915 : Blo 1470555 1471915 := bstep (se 1 (by rfl) ⟨1103936, by rfl⟩ : syracuseStep 1471915 = 2207873) B2207873
theorem B13604273 : Blo 1470555 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B1471927 : Blo 1470555 1471927 := bstep (se 1 (by rfl) ⟨1103945, by rfl⟩ : syracuseStep 1471927 = 2207891) B2207891
theorem B1471947 : Blo 1470555 1471947 := bstep (se 1 (by rfl) ⟨1103960, by rfl⟩ : syracuseStep 1471947 = 2207921) B2207921
theorem B1471959 : Blo 1470555 1471959 := bstep (se 1 (by rfl) ⟨1103969, by rfl⟩ : syracuseStep 1471959 = 2207939) B2207939
theorem B3143129 : Blo 1470555 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B1471979 : Blo 1470555 1471979 := bstep (se 1 (by rfl) ⟨1103984, by rfl⟩ : syracuseStep 1471979 = 2207969) B2207969
theorem B1471991 : Blo 1470555 1471991 := bstep (se 1 (by rfl) ⟨1103993, by rfl⟩ : syracuseStep 1471991 = 2207987) B2207987
theorem B1472011 : Blo 1470555 1472011 := bstep (se 1 (by rfl) ⟨1104008, by rfl⟩ : syracuseStep 1472011 = 2208017) B2208017
theorem B1472023 : Blo 1470555 1472023 := bstep (se 1 (by rfl) ⟨1104017, by rfl⟩ : syracuseStep 1472023 = 2208035) B2208035
theorem B1472043 : Blo 1470555 1472043 := bstep (se 1 (by rfl) ⟨1104032, by rfl⟩ : syracuseStep 1472043 = 2208065) B2208065
theorem B3978803 : Blo 1470555 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B1472055 : Blo 1470555 1472055 := bstep (se 1 (by rfl) ⟨1104041, by rfl⟩ : syracuseStep 1472055 = 2208083) B2208083
theorem B1472075 : Blo 1470555 1472075 := bstep (se 1 (by rfl) ⟨1104056, by rfl⟩ : syracuseStep 1472075 = 2208113) B2208113
theorem B1472087 : Blo 1470555 1472087 := bstep (se 1 (by rfl) ⟨1104065, by rfl⟩ : syracuseStep 1472087 = 2208131) B2208131
theorem B1472107 : Blo 1470555 1472107 := bstep (se 1 (by rfl) ⟨1104080, by rfl⟩ : syracuseStep 1472107 = 2208161) B2208161
theorem B1472119 : Blo 1470555 1472119 := bstep (se 1 (by rfl) ⟨1104089, by rfl⟩ : syracuseStep 1472119 = 2208179) B2208179
theorem B21223043 : Blo 1470555 21223043 := bstep (se 1 (by rfl) ⟨15917282, by rfl⟩ : syracuseStep 21223043 = 31834565) B31834565
theorem B1472139 : Blo 1470555 1472139 := bstep (se 1 (by rfl) ⟨1104104, by rfl⟩ : syracuseStep 1472139 = 2208209) B2208209
theorem B5584535 : Blo 1470555 5584535 := bstep (se 1 (by rfl) ⟨4188401, by rfl⟩ : syracuseStep 5584535 = 8376803) B8376803
theorem B1472151 : Blo 1470555 1472151 := bstep (se 1 (by rfl) ⟨1104113, by rfl⟩ : syracuseStep 1472151 = 2208227) B2208227
theorem B1472171 : Blo 1470555 1472171 := bstep (se 1 (by rfl) ⟨1104128, by rfl⟩ : syracuseStep 1472171 = 2208257) B2208257
theorem B1472183 : Blo 1470555 1472183 := bstep (se 1 (by rfl) ⟨1104137, by rfl⟩ : syracuseStep 1472183 = 2208275) B2208275
theorem B1472203 : Blo 1470555 1472203 := bstep (se 1 (by rfl) ⟨1104152, by rfl⟩ : syracuseStep 1472203 = 2208305) B2208305
theorem B1472215 : Blo 1470555 1472215 := bstep (se 1 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 1472215 = 2208323) B2208323
theorem B2832089 : Blo 1470555 2832089 := bstep (se 2 (by rfl) ⟨1062033, by rfl⟩ : syracuseStep 2832089 = 2124067) B2124067
theorem B1472235 : Blo 1470555 1472235 := bstep (se 1 (by rfl) ⟨1104176, by rfl⟩ : syracuseStep 1472235 = 2208353) B2208353
theorem B1472247 : Blo 1470555 1472247 := bstep (se 1 (by rfl) ⟨1104185, by rfl⟩ : syracuseStep 1472247 = 2208371) B2208371
theorem B1472267 : Blo 1470555 1472267 := bstep (se 1 (by rfl) ⟨1104200, by rfl⟩ : syracuseStep 1472267 = 2208401) B2208401
theorem B1472279 : Blo 1470555 1472279 := bstep (se 1 (by rfl) ⟨1104209, by rfl⟩ : syracuseStep 1472279 = 2208419) B2208419
theorem B12736291 : Blo 1470555 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B1472299 : Blo 1470555 1472299 := bstep (se 1 (by rfl) ⟨1104224, by rfl⟩ : syracuseStep 1472299 = 2208449) B2208449
theorem B1472311 : Blo 1470555 1472311 := bstep (se 1 (by rfl) ⟨1104233, by rfl⟩ : syracuseStep 1472311 = 2208467) B2208467
theorem B1472331 : Blo 1470555 1472331 := bstep (se 1 (by rfl) ⟨1104248, by rfl⟩ : syracuseStep 1472331 = 2208497) B2208497
theorem B1472343 : Blo 1470555 1472343 := bstep (se 1 (by rfl) ⟨1104257, by rfl⟩ : syracuseStep 1472343 = 2208515) B2208515
theorem B5584733 : Blo 1470555 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B1472363 : Blo 1470555 1472363 := bstep (se 1 (by rfl) ⟨1104272, by rfl⟩ : syracuseStep 1472363 = 2208545) B2208545
theorem B3143539 : Blo 1470555 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B1472375 : Blo 1470555 1472375 := bstep (se 1 (by rfl) ⟨1104281, by rfl⟩ : syracuseStep 1472375 = 2208563) B2208563
theorem B1472395 : Blo 1470555 1472395 := bstep (se 1 (by rfl) ⟨1104296, by rfl⟩ : syracuseStep 1472395 = 2208593) B2208593
theorem B1472407 : Blo 1470555 1472407 := bstep (se 1 (by rfl) ⟨1104305, by rfl⟩ : syracuseStep 1472407 = 2208611) B2208611
theorem B1472427 : Blo 1470555 1472427 := bstep (se 1 (by rfl) ⟨1104320, by rfl⟩ : syracuseStep 1472427 = 2208641) B2208641
theorem B1472439 : Blo 1470555 1472439 := bstep (se 1 (by rfl) ⟨1104329, by rfl⟩ : syracuseStep 1472439 = 2208659) B2208659
theorem B1472459 : Blo 1470555 1472459 := bstep (se 1 (by rfl) ⟨1104344, by rfl⟩ : syracuseStep 1472459 = 2208689) B2208689
theorem B1472471 : Blo 1470555 1472471 := bstep (se 1 (by rfl) ⟨1104353, by rfl⟩ : syracuseStep 1472471 = 2208707) B2208707
theorem B1472491 : Blo 1470555 1472491 := bstep (se 1 (by rfl) ⟨1104368, by rfl⟩ : syracuseStep 1472491 = 2208737) B2208737
theorem B1472503 : Blo 1470555 1472503 := bstep (se 1 (by rfl) ⟨1104377, by rfl⟩ : syracuseStep 1472503 = 2208755) B2208755
theorem B1472523 : Blo 1470555 1472523 := bstep (se 1 (by rfl) ⟨1104392, by rfl⟩ : syracuseStep 1472523 = 2208785) B2208785
theorem B8386577 : Blo 1470555 8386577 := bstep (se 2 (by rfl) ⟨3144966, by rfl⟩ : syracuseStep 8386577 = 6289933) B6289933
theorem B1472535 : Blo 1470555 1472535 := bstep (se 1 (by rfl) ⟨1104401, by rfl⟩ : syracuseStep 1472535 = 2208803) B2208803
theorem B1472555 : Blo 1470555 1472555 := bstep (se 1 (by rfl) ⟨1104416, by rfl⟩ : syracuseStep 1472555 = 2208833) B2208833
theorem B3774539 : Blo 1470555 3774539 := bstep (se 1 (by rfl) ⟨2830904, by rfl⟩ : syracuseStep 3774539 = 5661809) B5661809
theorem B1767511 : Blo 1470555 1767511 := bstep (se 1 (by rfl) ⟨1325633, by rfl⟩ : syracuseStep 1767511 = 2651267) B2651267
theorem B2357399 : Blo 1470555 2357399 := bstep (se 1 (by rfl) ⟨1768049, by rfl⟩ : syracuseStep 2357399 = 3536099) B3536099
theorem B3143873 : Blo 1470555 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B14530765 : Blo 1470555 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B2357527 : Blo 1470555 2357527 := bstep (se 1 (by rfl) ⟨1768145, by rfl⟩ : syracuseStep 2357527 = 3536291) B3536291
theorem B3725747 : Blo 1470555 3725747 := bstep (se 1 (by rfl) ⟨2794310, by rfl⟩ : syracuseStep 3725747 = 5588621) B5588621
theorem B4717079 : Blo 1470555 4717079 := bstep (se 1 (by rfl) ⟨3537809, by rfl⟩ : syracuseStep 4717079 = 7075619) B7075619
theorem B1768087 : Blo 1470555 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B2357911 : Blo 1470555 2357911 := bstep (se 1 (by rfl) ⟨1768433, by rfl⟩ : syracuseStep 2357911 = 3536867) B3536867
theorem B7453457 : Blo 1470555 7453457 := bstep (se 2 (by rfl) ⟨2795046, by rfl⟩ : syracuseStep 7453457 = 5590093) B5590093
theorem B11172653 : Blo 1470555 11172653 := bstep (se 3 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 11172653 = 4189745) B4189745
theorem B4193117 : Blo 1470555 4193117 := bstep (se 3 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 4193117 = 1572419) B1572419
theorem B8379287 : Blo 1470555 8379287 := bstep (se 1 (by rfl) ⟨6284465, by rfl⟩ : syracuseStep 8379287 = 12568931) B12568931
theorem B2358167 : Blo 1470555 2358167 := bstep (se 1 (by rfl) ⟨1768625, by rfl⟩ : syracuseStep 2358167 = 3537251) B3537251
theorem B3144599 : Blo 1470555 3144599 := bstep (se 1 (by rfl) ⟨2358449, by rfl⟩ : syracuseStep 3144599 = 4716899) B4716899
theorem B7453619 : Blo 1470555 7453619 := bstep (se 1 (by rfl) ⟨5590214, by rfl⟩ : syracuseStep 7453619 = 11180429) B11180429
theorem B3726283 : Blo 1470555 3726283 := bstep (se 1 (by rfl) ⟨2794712, by rfl⟩ : syracuseStep 3726283 = 5589425) B5589425
theorem B3726425 : Blo 1470555 3726425 := bstep (se 2 (by rfl) ⟨1397409, by rfl⟩ : syracuseStep 3726425 = 2794819) B2794819
theorem B3308759 : Blo 1470555 3308759 := bstep (se 1 (by rfl) ⟨2481569, by rfl⟩ : syracuseStep 3308759 = 4963139) B4963139
theorem B3308939 : Blo 1470555 3308939 := bstep (se 1 (by rfl) ⟨2481704, by rfl⟩ : syracuseStep 3308939 = 4963409) B4963409
theorem B11484595 : Blo 1470555 11484595 := bstep (se 1 (by rfl) ⟨8613446, by rfl⟩ : syracuseStep 11484595 = 17226893) B17226893
theorem B3308993 : Blo 1470555 3308993 := bstep (se 2 (by rfl) ⟨1240872, by rfl⟩ : syracuseStep 3308993 = 2481745) B2481745
theorem B4963787 : Blo 1470555 4963787 := bstep (se 1 (by rfl) ⟨3722840, by rfl⟩ : syracuseStep 4963787 = 7445681) B7445681
theorem B2358731 : Blo 1470555 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B2096599 : Blo 1470555 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B2793035 : Blo 1470555 2793035 := bstep (se 1 (by rfl) ⟨2094776, by rfl⟩ : syracuseStep 2793035 = 4189553) B4189553
theorem B6282841 : Blo 1470555 6282841 := bstep (se 2 (by rfl) ⟨2356065, by rfl⟩ : syracuseStep 6282841 = 4712131) B4712131
theorem B1654411 : Blo 1470555 1654411 := bstep (se 1 (by rfl) ⟨1240808, by rfl⟩ : syracuseStep 1654411 = 2481617) B2481617
theorem B7446167 : Blo 1470555 7446167 := bstep (se 1 (by rfl) ⟨5584625, by rfl⟩ : syracuseStep 7446167 = 11169251) B11169251
theorem B3309209 : Blo 1470555 3309209 := bstep (se 2 (by rfl) ⟨1240953, by rfl⟩ : syracuseStep 3309209 = 2481907) B2481907
theorem B4775617 : Blo 1470555 4775617 := bstep (se 2 (by rfl) ⟨1790856, by rfl⟩ : syracuseStep 4775617 = 3581713) B3581713
theorem B4964057 : Blo 1470555 4964057 := bstep (se 2 (by rfl) ⟨1861521, by rfl⟩ : syracuseStep 4964057 = 3723043) B3723043
theorem B3309299 : Blo 1470555 3309299 := bstep (se 1 (by rfl) ⟨2481974, by rfl⟩ : syracuseStep 3309299 = 4963949) B4963949
theorem B1654519 : Blo 1470555 1654519 := bstep (se 1 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 1654519 = 2481779) B2481779
theorem B2793217 : Blo 1470555 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B5586691 : Blo 1470555 5586691 := bstep (se 1 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 5586691 = 8380037) B8380037
theorem B3309335 : Blo 1470555 3309335 := bstep (se 1 (by rfl) ⟨2482001, by rfl⟩ : syracuseStep 3309335 = 4964003) B4964003
theorem B2481995 : Blo 1470555 2481995 := bstep (se 1 (by rfl) ⟨1861496, by rfl⟩ : syracuseStep 2481995 = 3722993) B3722993
theorem B2686871 : Blo 1470555 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B3727255 : Blo 1470555 3727255 := bstep (se 1 (by rfl) ⟨2795441, by rfl⟩ : syracuseStep 3727255 = 5590883) B5590883
theorem B1654699 : Blo 1470555 1654699 := bstep (se 1 (by rfl) ⟨1241024, by rfl⟩ : syracuseStep 1654699 = 2482049) B2482049
theorem B37699505 : Blo 1470555 37699505 := bstep (se 2 (by rfl) ⟨14137314, by rfl⟩ : syracuseStep 37699505 = 28274629) B28274629
theorem B2482123 : Blo 1470555 2482123 := bstep (se 1 (by rfl) ⟨1861592, by rfl⟩ : syracuseStep 2482123 = 3723185) B3723185
theorem B3309515 : Blo 1470555 3309515 := bstep (se 1 (by rfl) ⟨2482136, by rfl⟩ : syracuseStep 3309515 = 4964273) B4964273
theorem B4964381 : Blo 1470555 4964381 := bstep (se 3 (by rfl) ⟨930821, by rfl⟩ : syracuseStep 4964381 = 1861643) B1861643
theorem B1654843 : Blo 1470555 1654843 := bstep (se 1 (by rfl) ⟨1241132, by rfl⟩ : syracuseStep 1654843 = 2482265) B2482265
theorem B10608727 : Blo 1470555 10608727 := bstep (se 1 (by rfl) ⟨7956545, by rfl⟩ : syracuseStep 10608727 = 15913091) B15913091
theorem B2793619 : Blo 1470555 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B3309839 : Blo 1470555 3309839 := bstep (se 1 (by rfl) ⟨2482379, by rfl⟩ : syracuseStep 3309839 = 4964759) B4964759
theorem B2482447 : Blo 1470555 2482447 := bstep (se 1 (by rfl) ⟨1861835, by rfl⟩ : syracuseStep 2482447 = 3723671) B3723671
theorem B19374353 : Blo 1470555 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B3309857 : Blo 1470555 3309857 := bstep (se 2 (by rfl) ⟨1241196, by rfl⟩ : syracuseStep 3309857 = 2482393) B2482393
theorem B2793847 : Blo 1470555 2793847 := bstep (se 1 (by rfl) ⟨2095385, by rfl⟩ : syracuseStep 2793847 = 4190771) B4190771
theorem B4473235 : Blo 1470555 4473235 := bstep (se 1 (by rfl) ⟨3354926, by rfl⟩ : syracuseStep 4473235 = 6709853) B6709853
theorem B5300747 : Blo 1470555 5300747 := bstep (se 1 (by rfl) ⟨3975560, by rfl⟩ : syracuseStep 5300747 = 7951121) B7951121
theorem B5964299 : Blo 1470555 5964299 := bstep (se 1 (by rfl) ⟨4473224, by rfl⟩ : syracuseStep 5964299 = 8946449) B8946449
theorem B2982415 : Blo 1470555 2982415 := bstep (se 1 (by rfl) ⟨2236811, by rfl⟩ : syracuseStep 2982415 = 4473623) B4473623
theorem B1655311 : Blo 1470555 1655311 := bstep (se 1 (by rfl) ⟨1241483, by rfl⟩ : syracuseStep 1655311 = 2482967) B2482967
theorem B7070237 : Blo 1470555 7070237 := bstep (se 3 (by rfl) ⟨1325669, by rfl⟩ : syracuseStep 7070237 = 2651339) B2651339
theorem B2982433 : Blo 1470555 2982433 := bstep (se 2 (by rfl) ⟨1118412, by rfl⟩ : syracuseStep 2982433 = 2236825) B2236825
theorem B10601027 : Blo 1470555 10601027 := bstep (se 1 (by rfl) ⟨7950770, by rfl⟩ : syracuseStep 10601027 = 15901541) B15901541
theorem B3310199 : Blo 1470555 3310199 := bstep (se 1 (by rfl) ⟨2482649, by rfl⟩ : syracuseStep 3310199 = 4965299) B4965299
theorem B9429797 : Blo 1470555 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B3310379 : Blo 1470555 3310379 := bstep (se 1 (by rfl) ⟨2482784, by rfl⟩ : syracuseStep 3310379 = 4965569) B4965569
theorem B2482987 : Blo 1470555 2482987 := bstep (se 1 (by rfl) ⟨1862240, by rfl⟩ : syracuseStep 2482987 = 3724481) B3724481
theorem B2483129 : Blo 1470555 2483129 := bstep (se 2 (by rfl) ⟨931173, by rfl⟩ : syracuseStep 2483129 = 1862347) B1862347
theorem B9069515 : Blo 1470555 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B25469957 : Blo 1470555 25469957 := bstep (se 4 (by rfl) ⟨2387808, by rfl⟩ : syracuseStep 25469957 = 4775617) B4775617
theorem B1655815 : Blo 1470555 1655815 := bstep (se 1 (by rfl) ⟨1241861, by rfl⟩ : syracuseStep 1655815 = 2483723) B2483723
theorem B14148695 : Blo 1470555 14148695 := bstep (se 1 (by rfl) ⟨10611521, by rfl⟩ : syracuseStep 14148695 = 21223043) B21223043
theorem B3310739 : Blo 1470555 3310739 := bstep (se 1 (by rfl) ⟨2483054, by rfl⟩ : syracuseStep 3310739 = 4966109) B4966109
theorem B1655995 : Blo 1470555 1655995 := bstep (se 1 (by rfl) ⟨1241996, by rfl⟩ : syracuseStep 1655995 = 2483993) B2483993
theorem B3310793 : Blo 1470555 3310793 := bstep (se 2 (by rfl) ⟨1241547, by rfl⟩ : syracuseStep 3310793 = 2483095) B2483095
theorem B8381677 : Blo 1470555 8381677 := bstep (se 3 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 8381677 = 3143129) B3143129
theorem B551380229 : Blo 1470555 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B21202235 : Blo 1470555 21202235 := bstep (se 1 (by rfl) ⟨15901676, by rfl⟩ : syracuseStep 21202235 = 31803353) B31803353
theorem B2516359 : Blo 1470555 2516359 := bstep (se 1 (by rfl) ⟨1887269, by rfl⟩ : syracuseStep 2516359 = 3774539) B3774539
theorem B4965785 : Blo 1470555 4965785 := bstep (se 2 (by rfl) ⟨1862169, by rfl⟩ : syracuseStep 4965785 = 3724339) B3724339
theorem B8947223 : Blo 1470555 8947223 := bstep (se 1 (by rfl) ⟨6710417, by rfl⟩ : syracuseStep 8947223 = 13420835) B13420835
theorem B28296773 : Blo 1470555 28296773 := bstep (se 4 (by rfl) ⟨2652822, by rfl⟩ : syracuseStep 28296773 = 5305645) B5305645
theorem B2483831 : Blo 1470555 2483831 := bstep (se 1 (by rfl) ⟨1862873, by rfl⟩ : syracuseStep 2483831 = 3725747) B3725747
theorem B1656463 : Blo 1470555 1656463 := bstep (se 1 (by rfl) ⟨1242347, by rfl⟩ : syracuseStep 1656463 = 2484695) B2484695
theorem B16762625 : Blo 1470555 16762625 := bstep (se 2 (by rfl) ⟨6285984, by rfl⟩ : syracuseStep 16762625 = 12571969) B12571969
theorem B7448435 : Blo 1470555 7448435 := bstep (se 1 (by rfl) ⟨5586326, by rfl⟩ : syracuseStep 7448435 = 11172653) B11172653
theorem B3311495 : Blo 1470555 3311495 := bstep (se 1 (by rfl) ⟨2483621, by rfl⟩ : syracuseStep 3311495 = 4967243) B4967243
theorem B2795411 : Blo 1470555 2795411 := bstep (se 1 (by rfl) ⟨2096558, by rfl⟩ : syracuseStep 2795411 = 4193117) B4193117
theorem B2795465 : Blo 1470555 2795465 := bstep (se 2 (by rfl) ⟨1048299, by rfl⟩ : syracuseStep 2795465 = 2096599) B2096599
theorem B3311675 : Blo 1470555 3311675 := bstep (se 1 (by rfl) ⟨2483756, by rfl⟩ : syracuseStep 3311675 = 4967513) B4967513
theorem B2484283 : Blo 1470555 2484283 := bstep (se 1 (by rfl) ⟨1863212, by rfl⟩ : syracuseStep 2484283 = 3726425) B3726425
theorem B4966487 : Blo 1470555 4966487 := bstep (se 1 (by rfl) ⟨3724865, by rfl⟩ : syracuseStep 4966487 = 7449731) B7449731
theorem B2205839 : Blo 1470555 2205839 := bstep (se 1 (by rfl) ⟨1654379, by rfl⟩ : syracuseStep 2205839 = 3308759) B3308759
theorem B2205881 : Blo 1470555 2205881 := bstep (se 2 (by rfl) ⟨827205, by rfl⟩ : syracuseStep 2205881 = 1654411) B1654411
theorem B3311801 : Blo 1470555 3311801 := bstep (se 2 (by rfl) ⟨1241925, by rfl⟩ : syracuseStep 3311801 = 2483851) B2483851
theorem B2484425 : Blo 1470555 2484425 := bstep (se 2 (by rfl) ⟨931659, by rfl⟩ : syracuseStep 2484425 = 1863319) B1863319
theorem B2205959 : Blo 1470555 2205959 := bstep (se 1 (by rfl) ⟨1654469, by rfl⟩ : syracuseStep 2205959 = 3308939) B3308939
theorem B2205995 : Blo 1470555 2205995 := bstep (se 1 (by rfl) ⟨1654496, by rfl⟩ : syracuseStep 2205995 = 3308993) B3308993
theorem B4475179 : Blo 1470555 4475179 := bstep (se 1 (by rfl) ⟨3356384, by rfl⟩ : syracuseStep 4475179 = 6712769) B6712769
theorem B2206025 : Blo 1470555 2206025 := bstep (se 2 (by rfl) ⟨827259, by rfl⟩ : syracuseStep 2206025 = 1654519) B1654519
theorem B7448921 : Blo 1470555 7448921 := bstep (se 2 (by rfl) ⟨2793345, by rfl⟩ : syracuseStep 7448921 = 5586691) B5586691
theorem B1862023 : Blo 1470555 1862023 := bstep (se 1 (by rfl) ⟨1396517, by rfl⟩ : syracuseStep 1862023 = 2793035) B2793035
theorem B5589395 : Blo 1470555 5589395 := bstep (se 1 (by rfl) ⟨4192046, by rfl⟩ : syracuseStep 5589395 = 8384093) B8384093
theorem B2206139 : Blo 1470555 2206139 := bstep (se 1 (by rfl) ⟨1654604, by rfl⟩ : syracuseStep 2206139 = 3309209) B3309209
theorem B2206199 : Blo 1470555 2206199 := bstep (se 1 (by rfl) ⟨1654649, by rfl⟩ : syracuseStep 2206199 = 3309299) B3309299
theorem B2206223 : Blo 1470555 2206223 := bstep (se 1 (by rfl) ⟨1654667, by rfl⟩ : syracuseStep 2206223 = 3309335) B3309335
theorem B3312143 : Blo 1470555 3312143 := bstep (se 1 (by rfl) ⟨2484107, by rfl⟩ : syracuseStep 3312143 = 4968215) B4968215
theorem B3312161 : Blo 1470555 3312161 := bstep (se 2 (by rfl) ⟨1242060, by rfl⟩ : syracuseStep 3312161 = 2484121) B2484121
theorem B2206265 : Blo 1470555 2206265 := bstep (se 2 (by rfl) ⟨827349, by rfl⟩ : syracuseStep 2206265 = 1654699) B1654699
theorem B4966973 : Blo 1470555 4966973 := bstep (se 3 (by rfl) ⟨931307, by rfl⟩ : syracuseStep 4966973 = 1862615) B1862615
theorem B2206343 : Blo 1470555 2206343 := bstep (se 1 (by rfl) ⟨1654757, by rfl⟩ : syracuseStep 2206343 = 3309515) B3309515
theorem B2206379 : Blo 1470555 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B2206409 : Blo 1470555 2206409 := bstep (se 2 (by rfl) ⟨827403, by rfl⟩ : syracuseStep 2206409 = 1654807) B1654807
theorem B4188971 : Blo 1470555 4188971 := bstep (se 1 (by rfl) ⟨3141728, by rfl⟩ : syracuseStep 4188971 = 6283457) B6283457
theorem B1862443 : Blo 1470555 1862443 := bstep (se 1 (by rfl) ⟨1396832, by rfl⟩ : syracuseStep 1862443 = 2793665) B2793665
theorem B2206523 : Blo 1470555 2206523 := bstep (se 1 (by rfl) ⟨1654892, by rfl⟩ : syracuseStep 2206523 = 3309785) B3309785
theorem B27593561 : Blo 1470555 27593561 := bstep (se 2 (by rfl) ⟨10347585, by rfl⟩ : syracuseStep 27593561 = 20695171) B20695171
theorem B2206583 : Blo 1470555 2206583 := bstep (se 1 (by rfl) ⟨1654937, by rfl⟩ : syracuseStep 2206583 = 3309875) B3309875
theorem B3312503 : Blo 1470555 3312503 := bstep (se 1 (by rfl) ⟨2484377, by rfl⟩ : syracuseStep 3312503 = 4968755) B4968755
theorem B2206607 : Blo 1470555 2206607 := bstep (se 1 (by rfl) ⟨1654955, by rfl⟩ : syracuseStep 2206607 = 3309911) B3309911
theorem B35793845 : Blo 1470555 35793845 := bstep (se 5 (by rfl) ⟨1677836, by rfl⟩ : syracuseStep 35793845 = 3355673) B3355673
theorem B2206649 : Blo 1470555 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B5303225 : Blo 1470555 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B7072697 : Blo 1470555 7072697 := bstep (se 2 (by rfl) ⟨2652261, by rfl⟩ : syracuseStep 7072697 = 5304523) B5304523
theorem B2206727 : Blo 1470555 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B1862671 : Blo 1470555 1862671 := bstep (se 1 (by rfl) ⟨1397003, by rfl⟩ : syracuseStep 1862671 = 2794007) B2794007
theorem B2206763 : Blo 1470555 2206763 := bstep (se 1 (by rfl) ⟨1655072, by rfl⟩ : syracuseStep 2206763 = 3310145) B3310145
theorem B3312683 : Blo 1470555 3312683 := bstep (se 1 (by rfl) ⟨2484512, by rfl⟩ : syracuseStep 3312683 = 4969025) B4969025
theorem B14142509 : Blo 1470555 14142509 := bstep (se 3 (by rfl) ⟨2651720, by rfl⟩ : syracuseStep 14142509 = 5303441) B5303441
theorem B2206793 : Blo 1470555 2206793 := bstep (se 2 (by rfl) ⟨827547, by rfl⟩ : syracuseStep 2206793 = 1655095) B1655095
theorem B3722375 : Blo 1470555 3722375 := bstep (se 1 (by rfl) ⟨2791781, by rfl⟩ : syracuseStep 3722375 = 5583563) B5583563
theorem B1887403 : Blo 1470555 1887403 := bstep (se 1 (by rfl) ⟨1415552, by rfl⟩ : syracuseStep 1887403 = 2831105) B2831105
theorem B8383661 : Blo 1470555 8383661 := bstep (se 3 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 8383661 = 3143873) B3143873
theorem B2206907 : Blo 1470555 2206907 := bstep (se 1 (by rfl) ⟨1655180, by rfl⟩ : syracuseStep 2206907 = 3310361) B3310361
theorem B2206967 : Blo 1470555 2206967 := bstep (se 1 (by rfl) ⟨1655225, by rfl⟩ : syracuseStep 2206967 = 3310451) B3310451
theorem B3722507 : Blo 1470555 3722507 := bstep (se 1 (by rfl) ⟨2791880, by rfl⟩ : syracuseStep 3722507 = 5583761) B5583761
theorem B2206991 : Blo 1470555 2206991 := bstep (se 1 (by rfl) ⟨1655243, by rfl⟩ : syracuseStep 2206991 = 3310487) B3310487
theorem B2207033 : Blo 1470555 2207033 := bstep (se 2 (by rfl) ⟨827637, by rfl⟩ : syracuseStep 2207033 = 1655275) B1655275
theorem B2207111 : Blo 1470555 2207111 := bstep (se 1 (by rfl) ⟨1655333, by rfl⟩ : syracuseStep 2207111 = 3310667) B3310667
theorem B3141011 : Blo 1470555 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B3313043 : Blo 1470555 3313043 := bstep (se 1 (by rfl) ⟨2484782, by rfl⟩ : syracuseStep 3313043 = 4969565) B4969565
theorem B2207147 : Blo 1470555 2207147 := bstep (se 1 (by rfl) ⟨1655360, by rfl⟩ : syracuseStep 2207147 = 3310721) B3310721
theorem B2207177 : Blo 1470555 2207177 := bstep (se 2 (by rfl) ⟨827691, by rfl⟩ : syracuseStep 2207177 = 1655383) B1655383
theorem B3313097 : Blo 1470555 3313097 := bstep (se 2 (by rfl) ⟨1242411, by rfl⟩ : syracuseStep 3313097 = 2484823) B2484823
theorem B2207291 : Blo 1470555 2207291 := bstep (se 1 (by rfl) ⟨1655468, by rfl⟩ : syracuseStep 2207291 = 3310937) B3310937
theorem B2207351 : Blo 1470555 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B2207375 : Blo 1470555 2207375 := bstep (se 1 (by rfl) ⟨1655531, by rfl⟩ : syracuseStep 2207375 = 3311063) B3311063
theorem B2207417 : Blo 1470555 2207417 := bstep (se 2 (by rfl) ⟨827781, by rfl⟩ : syracuseStep 2207417 = 1655563) B1655563
theorem B1863415 : Blo 1470555 1863415 := bstep (se 1 (by rfl) ⟨1397561, by rfl⟩ : syracuseStep 1863415 = 2795123) B2795123
theorem B2207495 : Blo 1470555 2207495 := bstep (se 1 (by rfl) ⟨1655621, by rfl⟩ : syracuseStep 2207495 = 3311243) B3311243
theorem B3723023 : Blo 1470555 3723023 := bstep (se 1 (by rfl) ⟨2792267, by rfl⟩ : syracuseStep 3723023 = 5584535) B5584535
theorem B2207531 : Blo 1470555 2207531 := bstep (se 1 (by rfl) ⟨1655648, by rfl⟩ : syracuseStep 2207531 = 3311297) B3311297
theorem B2207561 : Blo 1470555 2207561 := bstep (se 2 (by rfl) ⟨827835, by rfl⟩ : syracuseStep 2207561 = 1655671) B1655671
theorem B2649991 : Blo 1470555 2649991 := bstep (se 1 (by rfl) ⟨1987493, by rfl⟩ : syracuseStep 2649991 = 3974987) B3974987
theorem B4714375 : Blo 1470555 4714375 := bstep (se 1 (by rfl) ⟨3535781, by rfl⟩ : syracuseStep 4714375 = 7071563) B7071563
theorem B3723155 : Blo 1470555 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B4968377 : Blo 1470555 4968377 := bstep (se 2 (by rfl) ⟨1863141, by rfl⟩ : syracuseStep 4968377 = 3726283) B3726283
theorem B2207675 : Blo 1470555 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B7548893 : Blo 1470555 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B2207735 : Blo 1470555 2207735 := bstep (se 1 (by rfl) ⟨1655801, by rfl⟩ : syracuseStep 2207735 = 3311603) B3311603
theorem B5591051 : Blo 1470555 5591051 := bstep (se 1 (by rfl) ⟨4193288, by rfl⟩ : syracuseStep 5591051 = 8386577) B8386577
theorem B2207759 : Blo 1470555 2207759 := bstep (se 1 (by rfl) ⟨1655819, by rfl⟩ : syracuseStep 2207759 = 3311639) B3311639
theorem B2207801 : Blo 1470555 2207801 := bstep (se 2 (by rfl) ⟨827925, by rfl⟩ : syracuseStep 2207801 = 1655851) B1655851
theorem B2650171 : Blo 1470555 2650171 := bstep (se 1 (by rfl) ⟨1987628, by rfl⟩ : syracuseStep 2650171 = 3975257) B3975257
theorem B1470599 : Blo 1470555 1470599 := bstep (se 1 (by rfl) ⟨1102949, by rfl⟩ : syracuseStep 1470599 = 2205899) B2205899
theorem B2207879 : Blo 1470555 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B1470607 : Blo 1470555 1470607 := bstep (se 1 (by rfl) ⟨1102955, by rfl⟩ : syracuseStep 1470607 = 2205911) B2205911
theorem B2207915 : Blo 1470555 2207915 := bstep (se 1 (by rfl) ⟨1655936, by rfl⟩ : syracuseStep 2207915 = 3311873) B3311873
theorem B1470651 : Blo 1470555 1470651 := bstep (se 1 (by rfl) ⟨1102988, by rfl⟩ : syracuseStep 1470651 = 2205977) B2205977
theorem B2207945 : Blo 1470555 2207945 := bstep (se 2 (by rfl) ⟨827979, by rfl⟩ : syracuseStep 2207945 = 1655959) B1655959
theorem B1470727 : Blo 1470555 1470727 := bstep (se 1 (by rfl) ⟨1103045, by rfl⟩ : syracuseStep 1470727 = 2206091) B2206091
theorem B1470735 : Blo 1470555 1470735 := bstep (se 1 (by rfl) ⟨1103051, by rfl⟩ : syracuseStep 1470735 = 2206103) B2206103
theorem B1470779 : Blo 1470555 1470779 := bstep (se 1 (by rfl) ⟨1103084, by rfl⟩ : syracuseStep 1470779 = 2206169) B2206169
theorem B2208059 : Blo 1470555 2208059 := bstep (se 1 (by rfl) ⟨1656044, by rfl⟩ : syracuseStep 2208059 = 3312089) B3312089
theorem B3977591 : Blo 1470555 3977591 := bstep (se 1 (by rfl) ⟨2983193, by rfl⟩ : syracuseStep 3977591 = 5966387) B5966387
theorem B2208119 : Blo 1470555 2208119 := bstep (se 1 (by rfl) ⟨1656089, by rfl⟩ : syracuseStep 2208119 = 3312179) B3312179
theorem B1470855 : Blo 1470555 1470855 := bstep (se 1 (by rfl) ⟨1103141, by rfl⟩ : syracuseStep 1470855 = 2206283) B2206283
theorem B1470863 : Blo 1470555 1470863 := bstep (se 1 (by rfl) ⟨1103147, by rfl⟩ : syracuseStep 1470863 = 2206295) B2206295
theorem B2208143 : Blo 1470555 2208143 := bstep (se 1 (by rfl) ⟨1656107, by rfl⟩ : syracuseStep 2208143 = 3312215) B3312215
theorem B4190611 : Blo 1470555 4190611 := bstep (se 1 (by rfl) ⟨3142958, by rfl⟩ : syracuseStep 4190611 = 6285917) B6285917
theorem B7451027 : Blo 1470555 7451027 := bstep (se 1 (by rfl) ⟨5588270, by rfl⟩ : syracuseStep 7451027 = 11176541) B11176541
theorem B2208185 : Blo 1470555 2208185 := bstep (se 2 (by rfl) ⟨828069, by rfl⟩ : syracuseStep 2208185 = 1656139) B1656139
theorem B1470907 : Blo 1470555 1470907 := bstep (se 1 (by rfl) ⟨1103180, by rfl⟩ : syracuseStep 1470907 = 2206361) B2206361
theorem B1470983 : Blo 1470555 1470983 := bstep (se 1 (by rfl) ⟨1103237, by rfl⟩ : syracuseStep 1470983 = 2206475) B2206475
theorem B2208263 : Blo 1470555 2208263 := bstep (se 1 (by rfl) ⟨1656197, by rfl⟩ : syracuseStep 2208263 = 3312395) B3312395
theorem B4968971 : Blo 1470555 4968971 := bstep (se 1 (by rfl) ⟨3726728, by rfl⟩ : syracuseStep 4968971 = 7453457) B7453457
theorem B1470991 : Blo 1470555 1470991 := bstep (se 1 (by rfl) ⟨1103243, by rfl⟩ : syracuseStep 1470991 = 2206487) B2206487
theorem B2208299 : Blo 1470555 2208299 := bstep (se 1 (by rfl) ⟨1656224, by rfl⟩ : syracuseStep 2208299 = 3312449) B3312449
theorem B1471035 : Blo 1470555 1471035 := bstep (se 1 (by rfl) ⟨1103276, by rfl⟩ : syracuseStep 1471035 = 2206553) B2206553
theorem B2208329 : Blo 1470555 2208329 := bstep (se 2 (by rfl) ⟨828123, by rfl⟩ : syracuseStep 2208329 = 1656247) B1656247
theorem B16765541 : Blo 1470555 16765541 := bstep (se 4 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 16765541 = 3143539) B3143539
theorem B4969079 : Blo 1470555 4969079 := bstep (se 1 (by rfl) ⟨3726809, by rfl⟩ : syracuseStep 4969079 = 7453619) B7453619
theorem B1471111 : Blo 1470555 1471111 := bstep (se 1 (by rfl) ⟨1103333, by rfl⟩ : syracuseStep 1471111 = 2206667) B2206667
theorem B1471119 : Blo 1470555 1471119 := bstep (se 1 (by rfl) ⟨1103339, by rfl⟩ : syracuseStep 1471119 = 2206679) B2206679
theorem B1471163 : Blo 1470555 1471163 := bstep (se 1 (by rfl) ⟨1103372, by rfl⟩ : syracuseStep 1471163 = 2206745) B2206745
theorem B2208443 : Blo 1470555 2208443 := bstep (se 1 (by rfl) ⟨1656332, by rfl⟩ : syracuseStep 2208443 = 3312665) B3312665
theorem B2208503 : Blo 1470555 2208503 := bstep (se 1 (by rfl) ⟨1656377, by rfl⟩ : syracuseStep 2208503 = 3312755) B3312755
theorem B1471239 : Blo 1470555 1471239 := bstep (se 1 (by rfl) ⟨1103429, by rfl⟩ : syracuseStep 1471239 = 2206859) B2206859
theorem B1471247 : Blo 1470555 1471247 := bstep (se 1 (by rfl) ⟨1103435, by rfl⟩ : syracuseStep 1471247 = 2206871) B2206871
theorem B2208527 : Blo 1470555 2208527 := bstep (se 1 (by rfl) ⟨1656395, by rfl⟩ : syracuseStep 2208527 = 3312791) B3312791
theorem B8377121 : Blo 1470555 8377121 := bstep (se 2 (by rfl) ⟨3141420, by rfl⟩ : syracuseStep 8377121 = 6282841) B6282841
theorem B7549729 : Blo 1470555 7549729 := bstep (se 2 (by rfl) ⟨2831148, by rfl⟩ : syracuseStep 7549729 = 5662297) B5662297
theorem B2208569 : Blo 1470555 2208569 := bstep (se 2 (by rfl) ⟨828213, by rfl⟩ : syracuseStep 2208569 = 1656427) B1656427
theorem B1471291 : Blo 1470555 1471291 := bstep (se 1 (by rfl) ⟨1103468, by rfl⟩ : syracuseStep 1471291 = 2206937) B2206937
theorem B1471367 : Blo 1470555 1471367 := bstep (se 1 (by rfl) ⟨1103525, by rfl⟩ : syracuseStep 1471367 = 2207051) B2207051
theorem B7074695 : Blo 1470555 7074695 := bstep (se 1 (by rfl) ⟨5306021, by rfl⟩ : syracuseStep 7074695 = 10612043) B10612043
theorem B2208647 : Blo 1470555 2208647 := bstep (se 1 (by rfl) ⟨1656485, by rfl⟩ : syracuseStep 2208647 = 3312971) B3312971
theorem B1471375 : Blo 1470555 1471375 := bstep (se 1 (by rfl) ⟨1103531, by rfl⟩ : syracuseStep 1471375 = 2207063) B2207063
theorem B2208683 : Blo 1470555 2208683 := bstep (se 1 (by rfl) ⟨1656512, by rfl⟩ : syracuseStep 2208683 = 3313025) B3313025
theorem B30208949 : Blo 1470555 30208949 := bstep (se 5 (by rfl) ⟨1416044, by rfl⟩ : syracuseStep 30208949 = 2832089) B2832089
theorem B1471419 : Blo 1470555 1471419 := bstep (se 1 (by rfl) ⟨1103564, by rfl⟩ : syracuseStep 1471419 = 2207129) B2207129
theorem B2208713 : Blo 1470555 2208713 := bstep (se 2 (by rfl) ⟨828267, by rfl⟩ : syracuseStep 2208713 = 1656535) B1656535
theorem B3724289 : Blo 1470555 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B1471495 : Blo 1470555 1471495 := bstep (se 1 (by rfl) ⟨1103621, by rfl⟩ : syracuseStep 1471495 = 2207243) B2207243
theorem B1471503 : Blo 1470555 1471503 := bstep (se 1 (by rfl) ⟨1103627, by rfl⟩ : syracuseStep 1471503 = 2207255) B2207255
theorem B1471547 : Blo 1470555 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B2208827 : Blo 1470555 2208827 := bstep (se 1 (by rfl) ⟨1656620, by rfl⟩ : syracuseStep 2208827 = 3313241) B3313241
theorem B7164989 : Blo 1470555 7164989 := bstep (se 3 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 7164989 = 2686871) B2686871
theorem B6288445 : Blo 1470555 6288445 := bstep (se 3 (by rfl) ⟨1179083, by rfl⟩ : syracuseStep 6288445 = 2358167) B2358167
theorem B1471623 : Blo 1470555 1471623 := bstep (se 1 (by rfl) ⟨1103717, by rfl⟩ : syracuseStep 1471623 = 2207435) B2207435
theorem B1471631 : Blo 1470555 1471631 := bstep (se 1 (by rfl) ⟨1103723, by rfl⟩ : syracuseStep 1471631 = 2207447) B2207447
theorem B1471675 : Blo 1470555 1471675 := bstep (se 1 (by rfl) ⟨1103756, by rfl⟩ : syracuseStep 1471675 = 2207513) B2207513
theorem B4969673 : Blo 1470555 4969673 := bstep (se 2 (by rfl) ⟨1863627, by rfl⟩ : syracuseStep 4969673 = 3727255) B3727255
theorem B1471751 : Blo 1470555 1471751 := bstep (se 1 (by rfl) ⟨1103813, by rfl⟩ : syracuseStep 1471751 = 2207627) B2207627
theorem B1471759 : Blo 1470555 1471759 := bstep (se 1 (by rfl) ⟨1103819, by rfl⟩ : syracuseStep 1471759 = 2207639) B2207639
theorem B1471803 : Blo 1470555 1471803 := bstep (se 1 (by rfl) ⟨1103852, by rfl⟩ : syracuseStep 1471803 = 2207705) B2207705
theorem B3724663 : Blo 1470555 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B23860615 : Blo 1470555 23860615 := bstep (se 1 (by rfl) ⟨17895461, by rfl⟩ : syracuseStep 23860615 = 35790923) B35790923
theorem B1471879 : Blo 1470555 1471879 := bstep (se 1 (by rfl) ⟨1103909, by rfl⟩ : syracuseStep 1471879 = 2207819) B2207819
theorem B1471887 : Blo 1470555 1471887 := bstep (se 1 (by rfl) ⟨1103915, by rfl⟩ : syracuseStep 1471887 = 2207831) B2207831
theorem B1471931 : Blo 1470555 1471931 := bstep (se 1 (by rfl) ⟨1103948, by rfl⟩ : syracuseStep 1471931 = 2207897) B2207897
theorem B2356681 : Blo 1470555 2356681 := bstep (se 2 (by rfl) ⟨883755, by rfl⟩ : syracuseStep 2356681 = 1767511) B1767511
theorem B8386051 : Blo 1470555 8386051 := bstep (se 1 (by rfl) ⟨6289538, by rfl⟩ : syracuseStep 8386051 = 12579077) B12579077
theorem B1472007 : Blo 1470555 1472007 := bstep (se 1 (by rfl) ⟨1104005, by rfl⟩ : syracuseStep 1472007 = 2208011) B2208011
theorem B1472015 : Blo 1470555 1472015 := bstep (se 1 (by rfl) ⟨1104011, by rfl⟩ : syracuseStep 1472015 = 2208023) B2208023
theorem B7951895 : Blo 1470555 7951895 := bstep (se 1 (by rfl) ⟨5963921, by rfl⟩ : syracuseStep 7951895 = 11927843) B11927843
theorem B1472059 : Blo 1470555 1472059 := bstep (se 1 (by rfl) ⟨1104044, by rfl⟩ : syracuseStep 1472059 = 2208089) B2208089
theorem B1472135 : Blo 1470555 1472135 := bstep (se 1 (by rfl) ⟨1104101, by rfl⟩ : syracuseStep 1472135 = 2208203) B2208203
theorem B1472143 : Blo 1470555 1472143 := bstep (se 1 (by rfl) ⟨1104107, by rfl⟩ : syracuseStep 1472143 = 2208215) B2208215
theorem B1472187 : Blo 1470555 1472187 := bstep (se 1 (by rfl) ⟨1104140, by rfl⟩ : syracuseStep 1472187 = 2208281) B2208281
theorem B3143369 : Blo 1470555 3143369 := bstep (se 2 (by rfl) ⟨1178763, by rfl⟩ : syracuseStep 3143369 = 2357527) B2357527
theorem B1472263 : Blo 1470555 1472263 := bstep (se 1 (by rfl) ⟨1104197, by rfl⟩ : syracuseStep 1472263 = 2208395) B2208395
theorem B3979019 : Blo 1470555 3979019 := bstep (se 1 (by rfl) ⟨2984264, by rfl⟩ : syracuseStep 3979019 = 5968529) B5968529
theorem B1472271 : Blo 1470555 1472271 := bstep (se 1 (by rfl) ⟨1104203, by rfl⟩ : syracuseStep 1472271 = 2208407) B2208407
theorem B3725099 : Blo 1470555 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B1472315 : Blo 1470555 1472315 := bstep (se 1 (by rfl) ⟨1104236, by rfl⟩ : syracuseStep 1472315 = 2208473) B2208473
theorem B14137163 : Blo 1470555 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B1472391 : Blo 1470555 1472391 := bstep (se 1 (by rfl) ⟨1104293, by rfl⟩ : syracuseStep 1472391 = 2208587) B2208587
theorem B1472399 : Blo 1470555 1472399 := bstep (se 1 (by rfl) ⟨1104299, by rfl⟩ : syracuseStep 1472399 = 2208599) B2208599
theorem B1472443 : Blo 1470555 1472443 := bstep (se 1 (by rfl) ⟨1104332, by rfl⟩ : syracuseStep 1472443 = 2208665) B2208665
theorem B1767415 : Blo 1470555 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B1472519 : Blo 1470555 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B1472527 : Blo 1470555 1472527 := bstep (se 1 (by rfl) ⟨1104395, by rfl⟩ : syracuseStep 1472527 = 2208791) B2208791
theorem B16766999 : Blo 1470555 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B11196503 : Blo 1470555 11196503 := bstep (se 1 (by rfl) ⟨8397377, by rfl⟩ : syracuseStep 11196503 = 16794755) B16794755
theorem B4192343 : Blo 1470555 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B3143881 : Blo 1470555 3143881 := bstep (se 2 (by rfl) ⟨1178955, by rfl⟩ : syracuseStep 3143881 = 2357911) B2357911
theorem B2652535 : Blo 1470555 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B7444871 : Blo 1470555 7444871 := bstep (se 1 (by rfl) ⟨5583653, by rfl⟩ : syracuseStep 7444871 = 11167307) B11167307
theorem B8952211 : Blo 1470555 8952211 := bstep (se 1 (by rfl) ⟨6714158, by rfl⟩ : syracuseStep 8952211 = 13428317) B13428317
theorem B15112595 : Blo 1470555 15112595 := bstep (se 1 (by rfl) ⟨11334446, by rfl⟩ : syracuseStep 15112595 = 22668893) B22668893
theorem B9066937 : Blo 1470555 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B7952849 : Blo 1470555 7952849 := bstep (se 2 (by rfl) ⟨2982318, by rfl⟩ : syracuseStep 7952849 = 5964637) B5964637
theorem B6289949 : Blo 1470555 6289949 := bstep (se 3 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 6289949 = 2358731) B2358731
theorem B2791979 : Blo 1470555 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B3725939 : Blo 1470555 3725939 := bstep (se 1 (by rfl) ⟨2794454, by rfl⟩ : syracuseStep 3725939 = 5588909) B5588909
theorem B1989239 : Blo 1470555 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B3725959 : Blo 1470555 3725959 := bstep (se 1 (by rfl) ⟨2794469, by rfl⟩ : syracuseStep 3725959 = 5588939) B5588939
theorem B42449669 : Blo 1470555 42449669 := bstep (se 4 (by rfl) ⟨3979656, by rfl⟩ : syracuseStep 42449669 = 7959313) B7959313
theorem B2792207 : Blo 1470555 2792207 := bstep (se 1 (by rfl) ⟨2094155, by rfl⟩ : syracuseStep 2792207 = 4188311) B4188311
theorem B1571599 : Blo 1470555 1571599 := bstep (se 1 (by rfl) ⟨1178699, by rfl⟩ : syracuseStep 1571599 = 2357399) B2357399
theorem B40278799 : Blo 1470555 40278799 := bstep (se 1 (by rfl) ⟨30209099, by rfl⟩ : syracuseStep 40278799 = 60418199) B60418199
theorem B7068505 : Blo 1470555 7068505 := bstep (se 2 (by rfl) ⟨2650689, by rfl⟩ : syracuseStep 7068505 = 5301379) B5301379
theorem B11180915 : Blo 1470555 11180915 := bstep (se 1 (by rfl) ⟨8385686, by rfl⟩ : syracuseStep 11180915 = 16771373) B16771373
theorem B3726233 : Blo 1470555 3726233 := bstep (se 2 (by rfl) ⟨1397337, by rfl⟩ : syracuseStep 3726233 = 2794675) B2794675
theorem B3144719 : Blo 1470555 3144719 := bstep (se 1 (by rfl) ⟨2358539, by rfl⟩ : syracuseStep 3144719 = 4717079) B4717079
theorem B3726395 : Blo 1470555 3726395 := bstep (se 1 (by rfl) ⟨2794796, by rfl⟩ : syracuseStep 3726395 = 5589593) B5589593
theorem B4472065 : Blo 1470555 4472065 := bstep (se 2 (by rfl) ⟨1677024, by rfl⟩ : syracuseStep 4472065 = 3354049) B3354049
theorem B5586191 : Blo 1470555 5586191 := bstep (se 1 (by rfl) ⟨4189643, by rfl⟩ : syracuseStep 5586191 = 8379287) B8379287
theorem B3726607 : Blo 1470555 3726607 := bstep (se 1 (by rfl) ⟨2794955, by rfl⟩ : syracuseStep 3726607 = 5589911) B5589911
theorem B2096399 : Blo 1470555 2096399 := bstep (se 1 (by rfl) ⟨1572299, by rfl⟩ : syracuseStep 2096399 = 3144599) B3144599
theorem B1989931 : Blo 1470555 1989931 := bstep (se 1 (by rfl) ⟨1492448, by rfl⟩ : syracuseStep 1989931 = 2984897) B2984897
theorem B111779131 : Blo 1470555 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B7454105 : Blo 1470555 7454105 := bstep (se 2 (by rfl) ⟨2795289, by rfl⟩ : syracuseStep 7454105 = 5590579) B5590579
theorem B3726881 : Blo 1470555 3726881 := bstep (se 2 (by rfl) ⟨1397580, by rfl⟩ : syracuseStep 3726881 = 2795161) B2795161
theorem B61251173 : Blo 1470555 61251173 := bstep (se 4 (by rfl) ⟨5742297, by rfl⟩ : syracuseStep 61251173 = 11484595) B11484595
theorem B2481799 : Blo 1470555 2481799 := bstep (se 1 (by rfl) ⟨1861349, by rfl⟩ : syracuseStep 2481799 = 3722699) B3722699
theorem B3309191 : Blo 1470555 3309191 := bstep (se 1 (by rfl) ⟨2481893, by rfl⟩ : syracuseStep 3309191 = 4963787) B4963787
theorem B16981721 : Blo 1470555 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B4964111 : Blo 1470555 4964111 := bstep (se 1 (by rfl) ⟨3723083, by rfl⟩ : syracuseStep 4964111 = 7446167) B7446167
theorem B16752419 : Blo 1470555 16752419 := bstep (se 1 (by rfl) ⟨12564314, by rfl⟩ : syracuseStep 16752419 = 25128629) B25128629
theorem B3309371 : Blo 1470555 3309371 := bstep (se 1 (by rfl) ⟨2482028, by rfl⟩ : syracuseStep 3309371 = 4964057) B4964057
theorem B8380219 : Blo 1470555 8380219 := bstep (se 1 (by rfl) ⟨6285164, by rfl⟩ : syracuseStep 8380219 = 12570329) B12570329
theorem B9428825 : Blo 1470555 9428825 := bstep (se 2 (by rfl) ⟨3535809, by rfl⟩ : syracuseStep 9428825 = 7071619) B7071619
theorem B1654663 : Blo 1470555 1654663 := bstep (se 1 (by rfl) ⟨1240997, by rfl⟩ : syracuseStep 1654663 = 2481995) B2481995
theorem B3309497 : Blo 1470555 3309497 := bstep (se 2 (by rfl) ⟨1241061, by rfl⟩ : syracuseStep 3309497 = 2482123) B2482123
theorem B25133003 : Blo 1470555 25133003 := bstep (se 1 (by rfl) ⟨18849752, by rfl⟩ : syracuseStep 25133003 = 37699505) B37699505
theorem B3727367 : Blo 1470555 3727367 := bstep (se 1 (by rfl) ⟨2795525, by rfl⟩ : syracuseStep 3727367 = 5591051) B5591051
theorem B3309587 : Blo 1470555 3309587 := bstep (se 1 (by rfl) ⟨2482190, by rfl⟩ : syracuseStep 3309587 = 4964381) B4964381
theorem B3309929 : Blo 1470555 3309929 := bstep (se 2 (by rfl) ⟨1241223, by rfl⟩ : syracuseStep 3309929 = 2482447) B2482447
theorem B2482697 : Blo 1470555 2482697 := bstep (se 2 (by rfl) ⟨931011, by rfl⟩ : syracuseStep 2482697 = 1862023) B1862023
theorem B5964313 : Blo 1470555 5964313 := bstep (se 2 (by rfl) ⟨2236617, by rfl⟩ : syracuseStep 5964313 = 4473235) B4473235
theorem B5587481 : Blo 1470555 5587481 := bstep (se 2 (by rfl) ⟨2095305, by rfl⟩ : syracuseStep 5587481 = 4190611) B4190611
theorem B11936281 : Blo 1470555 11936281 := bstep (se 2 (by rfl) ⟨4476105, by rfl⟩ : syracuseStep 11936281 = 8952211) B8952211
theorem B1655419 : Blo 1470555 1655419 := bstep (se 1 (by rfl) ⟨1241564, by rfl⟩ : syracuseStep 1655419 = 2483129) B2483129
theorem B6046343 : Blo 1470555 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B2482859 : Blo 1470555 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B4776659 : Blo 1470555 4776659 := bstep (se 1 (by rfl) ⟨3582494, by rfl⟩ : syracuseStep 4776659 = 7164989) B7164989
theorem B3310523 : Blo 1470555 3310523 := bstep (se 1 (by rfl) ⟨2482892, by rfl⟩ : syracuseStep 3310523 = 4965785) B4965785
theorem B5301263 : Blo 1470555 5301263 := bstep (se 1 (by rfl) ⟨3975947, by rfl⟩ : syracuseStep 5301263 = 7951895) B7951895
theorem B5964815 : Blo 1470555 5964815 := bstep (se 1 (by rfl) ⟨4473611, by rfl⟩ : syracuseStep 5964815 = 8947223) B8947223
theorem B3310649 : Blo 1470555 3310649 := bstep (se 2 (by rfl) ⟨1241493, by rfl⟩ : syracuseStep 3310649 = 2482987) B2482987
theorem B2483257 : Blo 1470555 2483257 := bstep (se 2 (by rfl) ⟨931221, by rfl⟩ : syracuseStep 2483257 = 1862443) B1862443
theorem B1655887 : Blo 1470555 1655887 := bstep (se 1 (by rfl) ⟨1241915, by rfl⟩ : syracuseStep 1655887 = 2483831) B2483831
theorem B11175083 : Blo 1470555 11175083 := bstep (se 1 (by rfl) ⟨8381312, by rfl⟩ : syracuseStep 11175083 = 16762625) B16762625
theorem B2483399 : Blo 1470555 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B4965623 : Blo 1470555 4965623 := bstep (se 1 (by rfl) ⟨3724217, by rfl⟩ : syracuseStep 4965623 = 7448435) B7448435
theorem B2483561 : Blo 1470555 2483561 := bstep (se 2 (by rfl) ⟨931335, by rfl⟩ : syracuseStep 2483561 = 1862671) B1862671
theorem B7464335 : Blo 1470555 7464335 := bstep (se 1 (by rfl) ⟨5598251, by rfl⟩ : syracuseStep 7464335 = 11196503) B11196503
theorem B3310991 : Blo 1470555 3310991 := bstep (se 1 (by rfl) ⟨2483243, by rfl⟩ : syracuseStep 3310991 = 4966487) B4966487
theorem B2794895 : Blo 1470555 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B214820261 : Blo 1470555 214820261 := bstep (se 4 (by rfl) ⟨20139399, by rfl⟩ : syracuseStep 214820261 = 40278799) B40278799
theorem B1656283 : Blo 1470555 1656283 := bstep (se 1 (by rfl) ⟨1242212, by rfl⟩ : syracuseStep 1656283 = 2484425) B2484425
theorem B2516537 : Blo 1470555 2516537 := bstep (se 2 (by rfl) ⟨943701, by rfl⟩ : syracuseStep 2516537 = 1887403) B1887403
theorem B4965947 : Blo 1470555 4965947 := bstep (se 1 (by rfl) ⟨3724460, by rfl⟩ : syracuseStep 4965947 = 7448921) B7448921
theorem B5301899 : Blo 1470555 5301899 := bstep (se 1 (by rfl) ⟨3976424, by rfl⟩ : syracuseStep 5301899 = 7952849) B7952849
theorem B11175569 : Blo 1470555 11175569 := bstep (se 2 (by rfl) ⟨4190838, by rfl⟩ : syracuseStep 11175569 = 8381677) B8381677
theorem B1861319 : Blo 1470555 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B3311315 : Blo 1470555 3311315 := bstep (se 1 (by rfl) ⟨2483486, by rfl⟩ : syracuseStep 3311315 = 4966973) B4966973
theorem B2483959 : Blo 1470555 2483959 := bstep (se 1 (by rfl) ⟨1862969, by rfl⟩ : syracuseStep 2483959 = 3725939) B3725939
theorem B149038841 : Blo 1470555 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B4966217 : Blo 1470555 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B1861471 : Blo 1470555 1861471 := bstep (se 1 (by rfl) ⟨1396103, by rfl⟩ : syracuseStep 1861471 = 2792207) B2792207
theorem B2484155 : Blo 1470555 2484155 := bstep (se 1 (by rfl) ⟨1863116, by rfl⟩ : syracuseStep 2484155 = 3726233) B3726233
theorem B2484263 : Blo 1470555 2484263 := bstep (se 1 (by rfl) ⟨1863197, by rfl⟩ : syracuseStep 2484263 = 3726395) B3726395
theorem B5589107 : Blo 1470555 5589107 := bstep (se 1 (by rfl) ⟨4191830, by rfl⟩ : syracuseStep 5589107 = 8383661) B8383661
theorem B2484553 : Blo 1470555 2484553 := bstep (se 2 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 2484553 = 1863415) B1863415
theorem B2484587 : Blo 1470555 2484587 := bstep (se 1 (by rfl) ⟨1863440, by rfl⟩ : syracuseStep 2484587 = 3726881) B3726881
theorem B2206127 : Blo 1470555 2206127 := bstep (se 1 (by rfl) ⟨1654595, by rfl⟩ : syracuseStep 2206127 = 3309191) B3309191
theorem B3533321 : Blo 1470555 3533321 := bstep (se 2 (by rfl) ⟨1324995, by rfl⟩ : syracuseStep 3533321 = 2649991) B2649991
theorem B2206217 : Blo 1470555 2206217 := bstep (se 2 (by rfl) ⟨827331, by rfl⟩ : syracuseStep 2206217 = 1654663) B1654663
theorem B6285833 : Blo 1470555 6285833 := bstep (se 2 (by rfl) ⟨2357187, by rfl⟩ : syracuseStep 6285833 = 4714375) B4714375
theorem B11168279 : Blo 1470555 11168279 := bstep (se 1 (by rfl) ⟨8376209, by rfl⟩ : syracuseStep 11168279 = 16752419) B16752419
theorem B2206247 : Blo 1470555 2206247 := bstep (se 1 (by rfl) ⟨1654685, by rfl⟩ : syracuseStep 2206247 = 3309371) B3309371
theorem B6285883 : Blo 1470555 6285883 := bstep (se 1 (by rfl) ⟨4714412, by rfl⟩ : syracuseStep 6285883 = 9428825) B9428825
theorem B2206331 : Blo 1470555 2206331 := bstep (se 1 (by rfl) ⟨1654748, by rfl⟩ : syracuseStep 2206331 = 3309497) B3309497
theorem B3312251 : Blo 1470555 3312251 := bstep (se 1 (by rfl) ⟨2484188, by rfl⟩ : syracuseStep 3312251 = 4968377) B4968377
theorem B16755335 : Blo 1470555 16755335 := bstep (se 1 (by rfl) ⟨12566501, by rfl⟩ : syracuseStep 16755335 = 25133003) B25133003
theorem B5032595 : Blo 1470555 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B3533561 : Blo 1470555 3533561 := bstep (se 2 (by rfl) ⟨1325085, by rfl⟩ : syracuseStep 3533561 = 2650171) B2650171
theorem B2206457 : Blo 1470555 2206457 := bstep (se 2 (by rfl) ⟨827421, by rfl⟩ : syracuseStep 2206457 = 1654843) B1654843
theorem B3312377 : Blo 1470555 3312377 := bstep (se 2 (by rfl) ⟨1242141, by rfl⟩ : syracuseStep 3312377 = 2484283) B2484283
theorem B2206559 : Blo 1470555 2206559 := bstep (se 1 (by rfl) ⟨1654919, by rfl⟩ : syracuseStep 2206559 = 3309839) B3309839
theorem B2206571 : Blo 1470555 2206571 := bstep (se 1 (by rfl) ⟨1654928, by rfl⟩ : syracuseStep 2206571 = 3309857) B3309857
theorem B4967351 : Blo 1470555 4967351 := bstep (se 1 (by rfl) ⟨3725513, by rfl⟩ : syracuseStep 4967351 = 7451027) B7451027
theorem B3533831 : Blo 1470555 3533831 := bstep (se 1 (by rfl) ⟨2650373, by rfl⟩ : syracuseStep 3533831 = 5300747) B5300747
theorem B3976199 : Blo 1470555 3976199 := bstep (se 1 (by rfl) ⟨2982149, by rfl⟩ : syracuseStep 3976199 = 5964299) B5964299
theorem B3312647 : Blo 1470555 3312647 := bstep (se 1 (by rfl) ⟨2484485, by rfl⟩ : syracuseStep 3312647 = 4968971) B4968971
theorem B4713491 : Blo 1470555 4713491 := bstep (se 1 (by rfl) ⟨3535118, by rfl⟩ : syracuseStep 4713491 = 7070237) B7070237
theorem B11177027 : Blo 1470555 11177027 := bstep (se 1 (by rfl) ⟨8382770, by rfl⟩ : syracuseStep 11177027 = 16765541) B16765541
theorem B2206799 : Blo 1470555 2206799 := bstep (se 1 (by rfl) ⟨1655099, by rfl⟩ : syracuseStep 2206799 = 3310199) B3310199
theorem B3312719 : Blo 1470555 3312719 := bstep (se 1 (by rfl) ⟨2484539, by rfl⟩ : syracuseStep 3312719 = 4969079) B4969079
theorem B2206919 : Blo 1470555 2206919 := bstep (se 1 (by rfl) ⟨1655189, by rfl⟩ : syracuseStep 2206919 = 3310379) B3310379
theorem B20139299 : Blo 1470555 20139299 := bstep (se 1 (by rfl) ⟨15104474, by rfl⟩ : syracuseStep 20139299 = 30208949) B30208949
theorem B3976553 : Blo 1470555 3976553 := bstep (se 2 (by rfl) ⟨1491207, by rfl⟩ : syracuseStep 3976553 = 2982415) B2982415
theorem B2207081 : Blo 1470555 2207081 := bstep (se 2 (by rfl) ⟨827655, by rfl⟩ : syracuseStep 2207081 = 1655311) B1655311
theorem B5590397 : Blo 1470555 5590397 := bstep (se 3 (by rfl) ⟨1048199, by rfl⟩ : syracuseStep 5590397 = 2096399) B2096399
theorem B3976577 : Blo 1470555 3976577 := bstep (se 2 (by rfl) ⟨1491216, by rfl⟩ : syracuseStep 3976577 = 2982433) B2982433
theorem B9432463 : Blo 1470555 9432463 := bstep (se 1 (by rfl) ⟨7074347, by rfl⟩ : syracuseStep 9432463 = 14148695) B14148695
theorem B2207159 : Blo 1470555 2207159 := bstep (se 1 (by rfl) ⟨1655369, by rfl⟩ : syracuseStep 2207159 = 3310739) B3310739
theorem B2207195 : Blo 1470555 2207195 := bstep (se 1 (by rfl) ⟨1655396, by rfl⟩ : syracuseStep 2207195 = 3310793) B3310793
theorem B3313115 : Blo 1470555 3313115 := bstep (se 1 (by rfl) ⟨2484836, by rfl⟩ : syracuseStep 3313115 = 4969673) B4969673
theorem B367586819 : Blo 1470555 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B4967945 : Blo 1470555 4967945 := bstep (se 2 (by rfl) ⟨1862979, by rfl⟩ : syracuseStep 4967945 = 3725959) B3725959
theorem B14134823 : Blo 1470555 14134823 := bstep (se 1 (by rfl) ⟨10601117, by rfl⟩ : syracuseStep 14134823 = 21202235) B21202235
theorem B40300253 : Blo 1470555 40300253 := bstep (se 3 (by rfl) ⟨7556297, by rfl⟩ : syracuseStep 40300253 = 15112595) B15112595
theorem B9424673 : Blo 1470555 9424673 := bstep (se 2 (by rfl) ⟨3534252, by rfl⟩ : syracuseStep 9424673 = 7068505) B7068505
theorem B9424775 : Blo 1470555 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B2207663 : Blo 1470555 2207663 := bstep (se 1 (by rfl) ⟨1655747, by rfl⟩ : syracuseStep 2207663 = 3311495) B3311495
theorem B1863643 : Blo 1470555 1863643 := bstep (se 1 (by rfl) ⟨1397732, by rfl⟩ : syracuseStep 1863643 = 2795465) B2795465
theorem B2207753 : Blo 1470555 2207753 := bstep (se 2 (by rfl) ⟨827907, by rfl⟩ : syracuseStep 2207753 = 1655815) B1655815
theorem B11177999 : Blo 1470555 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B2207783 : Blo 1470555 2207783 := bstep (se 1 (by rfl) ⟨1655837, by rfl⟩ : syracuseStep 2207783 = 3311675) B3311675
theorem B8384593 : Blo 1470555 8384593 := bstep (se 2 (by rfl) ⟨3144222, by rfl⟩ : syracuseStep 8384593 = 6288445) B6288445
theorem B1470559 : Blo 1470555 1470559 := bstep (se 1 (by rfl) ⟨1102919, by rfl⟩ : syracuseStep 1470559 = 2205839) B2205839
theorem B1470587 : Blo 1470555 1470587 := bstep (se 1 (by rfl) ⟨1102940, by rfl⟩ : syracuseStep 1470587 = 2205881) B2205881
theorem B2207867 : Blo 1470555 2207867 := bstep (se 1 (by rfl) ⟨1655900, by rfl⟩ : syracuseStep 2207867 = 3311801) B3311801
theorem B1470639 : Blo 1470555 1470639 := bstep (se 1 (by rfl) ⟨1102979, by rfl⟩ : syracuseStep 1470639 = 2205959) B2205959
theorem B1470663 : Blo 1470555 1470663 := bstep (se 1 (by rfl) ⟨1102997, by rfl⟩ : syracuseStep 1470663 = 2205995) B2205995
theorem B1470683 : Blo 1470555 1470683 := bstep (se 1 (by rfl) ⟨1103012, by rfl⟩ : syracuseStep 1470683 = 2206025) B2206025
theorem B23867621 : Blo 1470555 23867621 := bstep (se 4 (by rfl) ⟨2237589, by rfl⟩ : syracuseStep 23867621 = 4475179) B4475179
theorem B2207993 : Blo 1470555 2207993 := bstep (se 2 (by rfl) ⟨827997, by rfl⟩ : syracuseStep 2207993 = 1655995) B1655995
theorem B1470759 : Blo 1470555 1470759 := bstep (se 1 (by rfl) ⟨1103069, by rfl⟩ : syracuseStep 1470759 = 2206139) B2206139
theorem B5304637 : Blo 1470555 5304637 := bstep (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) B1989239
theorem B1470799 : Blo 1470555 1470799 := bstep (se 1 (by rfl) ⟨1103099, by rfl⟩ : syracuseStep 1470799 = 2206199) B2206199
theorem B1470815 : Blo 1470555 1470815 := bstep (se 1 (by rfl) ⟨1103111, by rfl⟩ : syracuseStep 1470815 = 2206223) B2206223
theorem B2208095 : Blo 1470555 2208095 := bstep (se 1 (by rfl) ⟨1656071, by rfl⟩ : syracuseStep 2208095 = 3312143) B3312143
theorem B4968809 : Blo 1470555 4968809 := bstep (se 2 (by rfl) ⟨1863303, by rfl⟩ : syracuseStep 4968809 = 3726607) B3726607
theorem B2208107 : Blo 1470555 2208107 := bstep (se 1 (by rfl) ⟨1656080, by rfl⟩ : syracuseStep 2208107 = 3312161) B3312161
theorem B1470843 : Blo 1470555 1470843 := bstep (se 1 (by rfl) ⟨1103132, by rfl⟩ : syracuseStep 1470843 = 2206265) B2206265
theorem B1470895 : Blo 1470555 1470895 := bstep (se 1 (by rfl) ⟨1103171, by rfl⟩ : syracuseStep 1470895 = 2206343) B2206343
theorem B1470919 : Blo 1470555 1470919 := bstep (se 1 (by rfl) ⟨1103189, by rfl⟩ : syracuseStep 1470919 = 2206379) B2206379
theorem B1470939 : Blo 1470555 1470939 := bstep (se 1 (by rfl) ⟨1103204, by rfl⟩ : syracuseStep 1470939 = 2206409) B2206409
theorem B28299779 : Blo 1470555 28299779 := bstep (se 1 (by rfl) ⟨21224834, by rfl⟩ : syracuseStep 28299779 = 42449669) B42449669
theorem B3355145 : Blo 1470555 3355145 := bstep (se 2 (by rfl) ⟨1258179, by rfl⟩ : syracuseStep 3355145 = 2516359) B2516359
theorem B31814153 : Blo 1470555 31814153 := bstep (se 2 (by rfl) ⟨11930307, by rfl⟩ : syracuseStep 31814153 = 23860615) B23860615
theorem B1471015 : Blo 1470555 1471015 := bstep (se 1 (by rfl) ⟨1103261, by rfl⟩ : syracuseStep 1471015 = 2206523) B2206523
theorem B18395707 : Blo 1470555 18395707 := bstep (se 1 (by rfl) ⟨13796780, by rfl⟩ : syracuseStep 18395707 = 27593561) B27593561
theorem B1471055 : Blo 1470555 1471055 := bstep (se 1 (by rfl) ⟨1103291, by rfl⟩ : syracuseStep 1471055 = 2206583) B2206583
theorem B2208335 : Blo 1470555 2208335 := bstep (se 1 (by rfl) ⟨1656251, by rfl⟩ : syracuseStep 2208335 = 3312503) B3312503
theorem B1471071 : Blo 1470555 1471071 := bstep (se 1 (by rfl) ⟨1103303, by rfl⟩ : syracuseStep 1471071 = 2206607) B2206607
theorem B3142241 : Blo 1470555 3142241 := bstep (se 2 (by rfl) ⟨1178340, by rfl⟩ : syracuseStep 3142241 = 2356681) B2356681
theorem B1471099 : Blo 1470555 1471099 := bstep (se 1 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 1471099 = 2206649) B2206649
theorem B3535483 : Blo 1470555 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B4715131 : Blo 1470555 4715131 := bstep (se 1 (by rfl) ⟨3536348, by rfl⟩ : syracuseStep 4715131 = 7072697) B7072697
theorem B1471151 : Blo 1470555 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B1471175 : Blo 1470555 1471175 := bstep (se 1 (by rfl) ⟨1103381, by rfl⟩ : syracuseStep 1471175 = 2206763) B2206763
theorem B2208455 : Blo 1470555 2208455 := bstep (se 1 (by rfl) ⟨1656341, by rfl⟩ : syracuseStep 2208455 = 3312683) B3312683
theorem B1471195 : Blo 1470555 1471195 := bstep (se 1 (by rfl) ⟨1103396, by rfl⟩ : syracuseStep 1471195 = 2206793) B2206793
theorem B25146125 : Blo 1470555 25146125 := bstep (se 3 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 25146125 = 9429797) B9429797
theorem B1471271 : Blo 1470555 1471271 := bstep (se 1 (by rfl) ⟨1103453, by rfl⟩ : syracuseStep 1471271 = 2206907) B2206907
theorem B1471311 : Blo 1470555 1471311 := bstep (se 1 (by rfl) ⟨1103483, by rfl⟩ : syracuseStep 1471311 = 2206967) B2206967
theorem B3724127 : Blo 1470555 3724127 := bstep (se 1 (by rfl) ⟨2793095, by rfl⟩ : syracuseStep 3724127 = 5586191) B5586191
theorem B1471327 : Blo 1470555 1471327 := bstep (se 1 (by rfl) ⟨1103495, by rfl⟩ : syracuseStep 1471327 = 2206991) B2206991
theorem B2208617 : Blo 1470555 2208617 := bstep (se 2 (by rfl) ⟨828231, by rfl⟩ : syracuseStep 2208617 = 1656463) B1656463
theorem B1471355 : Blo 1470555 1471355 := bstep (se 1 (by rfl) ⟨1103516, by rfl⟩ : syracuseStep 1471355 = 2207033) B2207033
theorem B1471407 : Blo 1470555 1471407 := bstep (se 1 (by rfl) ⟨1103555, by rfl⟩ : syracuseStep 1471407 = 2207111) B2207111
theorem B2094007 : Blo 1470555 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B2208695 : Blo 1470555 2208695 := bstep (se 1 (by rfl) ⟨1656521, by rfl⟩ : syracuseStep 2208695 = 3313043) B3313043
theorem B4969403 : Blo 1470555 4969403 := bstep (se 1 (by rfl) ⟨3727052, by rfl⟩ : syracuseStep 4969403 = 7454105) B7454105
theorem B1471431 : Blo 1470555 1471431 := bstep (se 1 (by rfl) ⟨1103573, by rfl⟩ : syracuseStep 1471431 = 2207147) B2207147
theorem B1471451 : Blo 1470555 1471451 := bstep (se 1 (by rfl) ⟨1103588, by rfl⟩ : syracuseStep 1471451 = 2207177) B2207177
theorem B2208731 : Blo 1470555 2208731 := bstep (se 1 (by rfl) ⟨1656548, by rfl⟩ : syracuseStep 2208731 = 3313097) B3313097
theorem B1471527 : Blo 1470555 1471527 := bstep (se 1 (by rfl) ⟨1103645, by rfl⟩ : syracuseStep 1471527 = 2207291) B2207291
theorem B40834115 : Blo 1470555 40834115 := bstep (se 1 (by rfl) ⟨30625586, by rfl⟩ : syracuseStep 40834115 = 61251173) B61251173
theorem B1471567 : Blo 1470555 1471567 := bstep (se 1 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 1471567 = 2207351) B2207351
theorem B1471583 : Blo 1470555 1471583 := bstep (se 1 (by rfl) ⟨1103687, by rfl⟩ : syracuseStep 1471583 = 2207375) B2207375
theorem B1471611 : Blo 1470555 1471611 := bstep (se 1 (by rfl) ⟨1103708, by rfl⟩ : syracuseStep 1471611 = 2207417) B2207417
theorem B1471663 : Blo 1470555 1471663 := bstep (se 1 (by rfl) ⟨1103747, by rfl⟩ : syracuseStep 1471663 = 2207495) B2207495
theorem B1471687 : Blo 1470555 1471687 := bstep (se 1 (by rfl) ⟨1103765, by rfl⟩ : syracuseStep 1471687 = 2207531) B2207531
theorem B1471707 : Blo 1470555 1471707 := bstep (se 1 (by rfl) ⟨1103780, by rfl⟩ : syracuseStep 1471707 = 2207561) B2207561
theorem B1471783 : Blo 1470555 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B2356553 : Blo 1470555 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B1471823 : Blo 1470555 1471823 := bstep (se 1 (by rfl) ⟨1103867, by rfl⟩ : syracuseStep 1471823 = 2207735) B2207735
theorem B1471839 : Blo 1470555 1471839 := bstep (se 1 (by rfl) ⟨1103879, by rfl⟩ : syracuseStep 1471839 = 2207759) B2207759
theorem B1471867 : Blo 1470555 1471867 := bstep (se 1 (by rfl) ⟨1103900, by rfl⟩ : syracuseStep 1471867 = 2207801) B2207801
theorem B1471919 : Blo 1470555 1471919 := bstep (se 1 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 1471919 = 2207879) B2207879
theorem B1471943 : Blo 1470555 1471943 := bstep (se 1 (by rfl) ⟨1103957, by rfl⟩ : syracuseStep 1471943 = 2207915) B2207915
theorem B14144969 : Blo 1470555 14144969 := bstep (se 2 (by rfl) ⟨5304363, by rfl⟩ : syracuseStep 14144969 = 10608727) B10608727
theorem B1471963 : Blo 1470555 1471963 := bstep (se 1 (by rfl) ⟨1103972, by rfl⟩ : syracuseStep 1471963 = 2207945) B2207945
theorem B12916235 : Blo 1470555 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B3724825 : Blo 1470555 3724825 := bstep (se 2 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 3724825 = 2793619) B2793619
theorem B1472039 : Blo 1470555 1472039 := bstep (se 1 (by rfl) ⟨1104029, by rfl⟩ : syracuseStep 1472039 = 2208059) B2208059
theorem B1472079 : Blo 1470555 1472079 := bstep (se 1 (by rfl) ⟨1104059, by rfl⟩ : syracuseStep 1472079 = 2208119) B2208119
theorem B1472095 : Blo 1470555 1472095 := bstep (se 1 (by rfl) ⟨1104071, by rfl⟩ : syracuseStep 1472095 = 2208143) B2208143
theorem B4191841 : Blo 1470555 4191841 := bstep (se 2 (by rfl) ⟨1571940, by rfl⟩ : syracuseStep 4191841 = 3143881) B3143881
theorem B1472123 : Blo 1470555 1472123 := bstep (se 1 (by rfl) ⟨1104092, by rfl⟩ : syracuseStep 1472123 = 2208185) B2208185
theorem B1472175 : Blo 1470555 1472175 := bstep (se 1 (by rfl) ⟨1104131, by rfl⟩ : syracuseStep 1472175 = 2208263) B2208263
theorem B1472199 : Blo 1470555 1472199 := bstep (se 1 (by rfl) ⟨1104149, by rfl⟩ : syracuseStep 1472199 = 2208299) B2208299
theorem B7067351 : Blo 1470555 7067351 := bstep (se 1 (by rfl) ⟨5300513, by rfl⟩ : syracuseStep 7067351 = 10601027) B10601027
theorem B1472219 : Blo 1470555 1472219 := bstep (se 1 (by rfl) ⟨1104164, by rfl⟩ : syracuseStep 1472219 = 2208329) B2208329
theorem B1472295 : Blo 1470555 1472295 := bstep (se 1 (by rfl) ⟨1104221, by rfl⟩ : syracuseStep 1472295 = 2208443) B2208443
theorem B3725129 : Blo 1470555 3725129 := bstep (se 2 (by rfl) ⟨1396923, by rfl⟩ : syracuseStep 3725129 = 2793847) B2793847
theorem B3536713 : Blo 1470555 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B1472335 : Blo 1470555 1472335 := bstep (se 1 (by rfl) ⟨1104251, by rfl⟩ : syracuseStep 1472335 = 2208503) B2208503
theorem B1472351 : Blo 1470555 1472351 := bstep (se 1 (by rfl) ⟨1104263, by rfl⟩ : syracuseStep 1472351 = 2208527) B2208527
theorem B5584747 : Blo 1470555 5584747 := bstep (se 1 (by rfl) ⟨4188560, by rfl⟩ : syracuseStep 5584747 = 8377121) B8377121
theorem B1472379 : Blo 1470555 1472379 := bstep (se 1 (by rfl) ⟨1104284, by rfl⟩ : syracuseStep 1472379 = 2208569) B2208569
theorem B12089249 : Blo 1470555 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B4716463 : Blo 1470555 4716463 := bstep (se 1 (by rfl) ⟨3537347, by rfl⟩ : syracuseStep 4716463 = 7074695) B7074695
theorem B1472431 : Blo 1470555 1472431 := bstep (se 1 (by rfl) ⟨1104323, by rfl⟩ : syracuseStep 1472431 = 2208647) B2208647
theorem B1472455 : Blo 1470555 1472455 := bstep (se 1 (by rfl) ⟨1104341, by rfl⟩ : syracuseStep 1472455 = 2208683) B2208683
theorem B1472475 : Blo 1470555 1472475 := bstep (se 1 (by rfl) ⟨1104356, by rfl⟩ : syracuseStep 1472475 = 2208713) B2208713
theorem B16979971 : Blo 1470555 16979971 := bstep (se 1 (by rfl) ⟨12734978, by rfl⟩ : syracuseStep 16979971 = 25469957) B25469957
theorem B161060885 : Blo 1470555 161060885 := bstep (se 6 (by rfl) ⟨3774864, by rfl⟩ : syracuseStep 161060885 = 7549729) B7549729
theorem B1472551 : Blo 1470555 1472551 := bstep (se 1 (by rfl) ⟨1104413, by rfl⟩ : syracuseStep 1472551 = 2208827) B2208827
theorem B10606909 : Blo 1470555 10606909 := bstep (se 3 (by rfl) ⟨1988795, by rfl⟩ : syracuseStep 10606909 = 3977591) B3977591
theorem B2095465 : Blo 1470555 2095465 := bstep (se 2 (by rfl) ⟨785799, by rfl⟩ : syracuseStep 2095465 = 1571599) B1571599
theorem B18864515 : Blo 1470555 18864515 := bstep (se 1 (by rfl) ⟨14148386, by rfl⟩ : syracuseStep 18864515 = 28296773) B28296773
theorem B2095579 : Blo 1470555 2095579 := bstep (se 1 (by rfl) ⟨1571684, by rfl⟩ : syracuseStep 2095579 = 3143369) B3143369
theorem B2652679 : Blo 1470555 2652679 := bstep (se 1 (by rfl) ⟨1989509, by rfl⟩ : syracuseStep 2652679 = 3979019) B3979019
theorem B4963247 : Blo 1470555 4963247 := bstep (se 1 (by rfl) ⟨3722435, by rfl⟩ : syracuseStep 4963247 = 7444871) B7444871
theorem B3726263 : Blo 1470555 3726263 := bstep (se 1 (by rfl) ⟨2794697, by rfl⟩ : syracuseStep 3726263 = 5589395) B5589395
theorem B5962753 : Blo 1470555 5962753 := bstep (se 2 (by rfl) ⟨2236032, by rfl⟩ : syracuseStep 5962753 = 4472065) B4472065
theorem B4193299 : Blo 1470555 4193299 := bstep (se 1 (by rfl) ⟨3144974, by rfl⟩ : syracuseStep 4193299 = 6289949) B6289949
theorem B2653241 : Blo 1470555 2653241 := bstep (se 2 (by rfl) ⟨994965, by rfl⟩ : syracuseStep 2653241 = 1989931) B1989931
theorem B2792647 : Blo 1470555 2792647 := bstep (se 1 (by rfl) ⟨2094485, by rfl⟩ : syracuseStep 2792647 = 4188971) B4188971
theorem B7453943 : Blo 1470555 7453943 := bstep (se 1 (by rfl) ⟨5590457, by rfl⟩ : syracuseStep 7453943 = 11180915) B11180915
theorem B23862563 : Blo 1470555 23862563 := bstep (se 1 (by rfl) ⟨17896922, by rfl⟩ : syracuseStep 23862563 = 35793845) B35793845
theorem B11181401 : Blo 1470555 11181401 := bstep (se 2 (by rfl) ⟨4193025, by rfl⟩ : syracuseStep 11181401 = 8386051) B8386051
theorem B2096479 : Blo 1470555 2096479 := bstep (se 1 (by rfl) ⟨1572359, by rfl⟩ : syracuseStep 2096479 = 3144719) B3144719
theorem B9428339 : Blo 1470555 9428339 := bstep (se 1 (by rfl) ⟨7071254, by rfl⟩ : syracuseStep 9428339 = 14142509) B14142509
theorem B2481583 : Blo 1470555 2481583 := bstep (se 1 (by rfl) ⟨1861187, by rfl⟩ : syracuseStep 2481583 = 3722375) B3722375
theorem B2481671 : Blo 1470555 2481671 := bstep (se 1 (by rfl) ⟨1861253, by rfl⟩ : syracuseStep 2481671 = 3722507) B3722507
theorem B3309065 : Blo 1470555 3309065 := bstep (se 2 (by rfl) ⟨1240899, by rfl⟩ : syracuseStep 3309065 = 2481799) B2481799
theorem B7454429 : Blo 1470555 7454429 := bstep (se 3 (by rfl) ⟨1397705, by rfl⟩ : syracuseStep 7454429 = 2795411) B2795411
theorem B11173625 : Blo 1470555 11173625 := bstep (se 2 (by rfl) ⟨4190109, by rfl⟩ : syracuseStep 11173625 = 8380219) B8380219
theorem B11321147 : Blo 1470555 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B2482015 : Blo 1470555 2482015 := bstep (se 1 (by rfl) ⟨1861511, by rfl⟩ : syracuseStep 2482015 = 3723023) B3723023
theorem B3309407 : Blo 1470555 3309407 := bstep (se 1 (by rfl) ⟨2482055, by rfl⟩ : syracuseStep 3309407 = 4964111) B4964111
theorem B2482103 : Blo 1470555 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B31801349 : Blo 1470555 31801349 := bstep (se 4 (by rfl) ⟨2981376, by rfl⟩ : syracuseStep 31801349 = 5962753) B5962753
theorem B14147621 : Blo 1470555 14147621 := bstep (se 4 (by rfl) ⟨1326339, by rfl⟩ : syracuseStep 14147621 = 2652679) B2652679
theorem B18866519 : Blo 1470555 18866519 := bstep (se 1 (by rfl) ⟨14149889, by rfl⟩ : syracuseStep 18866519 = 28299779) B28299779
theorem B2236763 : Blo 1470555 2236763 := bstep (se 1 (by rfl) ⟨1677572, by rfl⟩ : syracuseStep 2236763 = 3355145) B3355145
theorem B21209435 : Blo 1470555 21209435 := bstep (se 1 (by rfl) ⟨15907076, by rfl⟩ : syracuseStep 21209435 = 31814153) B31814153
theorem B1655131 : Blo 1470555 1655131 := bstep (se 1 (by rfl) ⟨1241348, by rfl⟩ : syracuseStep 1655131 = 2482697) B2482697
theorem B4030895 : Blo 1470555 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B1655239 : Blo 1470555 1655239 := bstep (se 1 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 1655239 = 2482859) B2482859
theorem B2793953 : Blo 1470555 2793953 := bstep (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) B2095465
theorem B2482751 : Blo 1470555 2482751 := bstep (se 1 (by rfl) ⟨1862063, by rfl⟩ : syracuseStep 2482751 = 3724127) B3724127
theorem B2794105 : Blo 1470555 2794105 := bstep (se 2 (by rfl) ⟨1047789, by rfl⟩ : syracuseStep 2794105 = 2095579) B2095579
theorem B27222743 : Blo 1470555 27222743 := bstep (se 1 (by rfl) ⟨20417057, by rfl⟩ : syracuseStep 27222743 = 40834115) B40834115
theorem B8381177 : Blo 1470555 8381177 := bstep (se 2 (by rfl) ⟨3142941, by rfl⟩ : syracuseStep 8381177 = 6285883) B6285883
theorem B24527609 : Blo 1470555 24527609 := bstep (se 2 (by rfl) ⟨9197853, by rfl⟩ : syracuseStep 24527609 = 18395707) B18395707
theorem B1655599 : Blo 1470555 1655599 := bstep (se 1 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 1655599 = 2483399) B2483399
theorem B3310415 : Blo 1470555 3310415 := bstep (se 1 (by rfl) ⟨2482811, by rfl⟩ : syracuseStep 3310415 = 4965623) B4965623
theorem B6284141 : Blo 1470555 6284141 := bstep (se 3 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 6284141 = 2356553) B2356553
theorem B1655707 : Blo 1470555 1655707 := bstep (se 1 (by rfl) ⟨1241780, by rfl⟩ : syracuseStep 1655707 = 2483561) B2483561
theorem B143213507 : Blo 1470555 143213507 := bstep (se 1 (by rfl) ⟨107410130, by rfl⟩ : syracuseStep 143213507 = 214820261) B214820261
theorem B9429979 : Blo 1470555 9429979 := bstep (se 1 (by rfl) ⟨7072484, by rfl⟩ : syracuseStep 9429979 = 14144969) B14144969
theorem B8610823 : Blo 1470555 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B3310631 : Blo 1470555 3310631 := bstep (se 1 (by rfl) ⟨2482973, by rfl⟩ : syracuseStep 3310631 = 4965947) B4965947
theorem B3310811 : Blo 1470555 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B2483419 : Blo 1470555 2483419 := bstep (se 1 (by rfl) ⟨1862564, by rfl⟩ : syracuseStep 2483419 = 3725129) B3725129
theorem B1656103 : Blo 1470555 1656103 := bstep (se 1 (by rfl) ⟨1242077, by rfl⟩ : syracuseStep 1656103 = 2484155) B2484155
theorem B107373923 : Blo 1470555 107373923 := bstep (se 1 (by rfl) ⟨80530442, by rfl⟩ : syracuseStep 107373923 = 161060885) B161060885
theorem B9422189 : Blo 1470555 9422189 := bstep (se 3 (by rfl) ⟨1766660, by rfl⟩ : syracuseStep 9422189 = 3533321) B3533321
theorem B1656175 : Blo 1470555 1656175 := bstep (se 1 (by rfl) ⟨1242131, by rfl⟩ : syracuseStep 1656175 = 2484263) B2484263
theorem B3311009 : Blo 1470555 3311009 := bstep (se 2 (by rfl) ⟨1241628, by rfl⟩ : syracuseStep 3311009 = 2483257) B2483257
theorem B79619573 : Blo 1470555 79619573 := bstep (se 5 (by rfl) ⟨3732167, by rfl⟩ : syracuseStep 79619573 = 7464335) B7464335
theorem B1656391 : Blo 1470555 1656391 := bstep (se 1 (by rfl) ⟨1242293, by rfl⟩ : syracuseStep 1656391 = 2484587) B2484587
theorem B12576343 : Blo 1470555 12576343 := bstep (se 1 (by rfl) ⟨9432257, by rfl⟩ : syracuseStep 12576343 = 18864515) B18864515
theorem B2795305 : Blo 1470555 2795305 := bstep (se 2 (by rfl) ⟨1048239, by rfl⟩ : syracuseStep 2795305 = 2096479) B2096479
theorem B12576617 : Blo 1470555 12576617 := bstep (se 2 (by rfl) ⟨4716231, by rfl⟩ : syracuseStep 12576617 = 9432463) B9432463
theorem B3311567 : Blo 1470555 3311567 := bstep (se 1 (by rfl) ⟨2483675, by rfl⟩ : syracuseStep 3311567 = 4967351) B4967351
theorem B2484175 : Blo 1470555 2484175 := bstep (se 1 (by rfl) ⟨1863131, by rfl⟩ : syracuseStep 2484175 = 3726263) B3726263
theorem B4966433 : Blo 1470555 4966433 := bstep (se 2 (by rfl) ⟨1862412, by rfl⟩ : syracuseStep 4966433 = 3724825) B3724825
theorem B5589121 : Blo 1470555 5589121 := bstep (se 2 (by rfl) ⟨2095920, by rfl⟩ : syracuseStep 5589121 = 4191841) B4191841
theorem B30189725 : Blo 1470555 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B6285559 : Blo 1470555 6285559 := bstep (se 1 (by rfl) ⟨4714169, by rfl⟩ : syracuseStep 6285559 = 9428339) B9428339
theorem B3311945 : Blo 1470555 3311945 := bstep (se 2 (by rfl) ⟨1241979, by rfl⟩ : syracuseStep 3311945 = 2483959) B2483959
theorem B245057879 : Blo 1470555 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B2206043 : Blo 1470555 2206043 := bstep (se 1 (by rfl) ⟨1654532, by rfl⟩ : syracuseStep 2206043 = 3309065) B3309065
theorem B3311963 : Blo 1470555 3311963 := bstep (se 1 (by rfl) ⟨2483972, by rfl⟩ : syracuseStep 3311963 = 4967945) B4967945
theorem B9423215 : Blo 1470555 9423215 := bstep (se 1 (by rfl) ⟨7067411, by rfl⟩ : syracuseStep 9423215 = 14134823) B14134823
theorem B7449083 : Blo 1470555 7449083 := bstep (se 1 (by rfl) ⟨5586812, by rfl⟩ : syracuseStep 7449083 = 11173625) B11173625
theorem B2206271 : Blo 1470555 2206271 := bstep (se 1 (by rfl) ⟨1654703, by rfl⟩ : syracuseStep 2206271 = 3309407) B3309407
theorem B2484857 : Blo 1470555 2484857 := bstep (se 2 (by rfl) ⟨931821, by rfl⟩ : syracuseStep 2484857 = 1863643) B1863643
theorem B2484911 : Blo 1470555 2484911 := bstep (se 1 (by rfl) ⟨1863683, by rfl⟩ : syracuseStep 2484911 = 3727367) B3727367
theorem B2206391 : Blo 1470555 2206391 := bstep (se 1 (by rfl) ⟨1654793, by rfl⟩ : syracuseStep 2206391 = 3309587) B3309587
theorem B15911747 : Blo 1470555 15911747 := bstep (se 1 (by rfl) ⟨11933810, by rfl⟩ : syracuseStep 15911747 = 23867621) B23867621
theorem B2206619 : Blo 1470555 2206619 := bstep (se 1 (by rfl) ⟨1654964, by rfl⟩ : syracuseStep 2206619 = 3309929) B3309929
theorem B3312539 : Blo 1470555 3312539 := bstep (se 1 (by rfl) ⟨2484404, by rfl⟩ : syracuseStep 3312539 = 4968809) B4968809
theorem B14142545 : Blo 1470555 14142545 := bstep (se 2 (by rfl) ⟨5303454, by rfl⟩ : syracuseStep 14142545 = 10606909) B10606909
theorem B7072849 : Blo 1470555 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B3312737 : Blo 1470555 3312737 := bstep (se 2 (by rfl) ⟨1242276, by rfl⟩ : syracuseStep 3312737 = 2484553) B2484553
theorem B16764083 : Blo 1470555 16764083 := bstep (se 1 (by rfl) ⟨12573062, by rfl⟩ : syracuseStep 16764083 = 25146125) B25146125
theorem B2207015 : Blo 1470555 2207015 := bstep (se 1 (by rfl) ⟨1655261, by rfl⟩ : syracuseStep 2207015 = 3310523) B3310523
theorem B3312935 : Blo 1470555 3312935 := bstep (se 1 (by rfl) ⟨2484701, by rfl⟩ : syracuseStep 3312935 = 4969403) B4969403
theorem B3534175 : Blo 1470555 3534175 := bstep (se 1 (by rfl) ⟨2650631, by rfl⟩ : syracuseStep 3534175 = 5301263) B5301263
theorem B3976543 : Blo 1470555 3976543 := bstep (se 1 (by rfl) ⟨2982407, by rfl⟩ : syracuseStep 3976543 = 5964815) B5964815
theorem B2207099 : Blo 1470555 2207099 := bstep (se 1 (by rfl) ⟨1655324, by rfl⟩ : syracuseStep 2207099 = 3310649) B3310649
theorem B7450055 : Blo 1470555 7450055 := bstep (se 1 (by rfl) ⟨5587541, by rfl⟩ : syracuseStep 7450055 = 11175083) B11175083
theorem B4713977 : Blo 1470555 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B2207225 : Blo 1470555 2207225 := bstep (se 2 (by rfl) ⟨827709, by rfl⟩ : syracuseStep 2207225 = 1655419) B1655419
theorem B6286841 : Blo 1470555 6286841 := bstep (se 2 (by rfl) ⟨2357565, by rfl⟩ : syracuseStep 6286841 = 4715131) B4715131
theorem B2207327 : Blo 1470555 2207327 := bstep (se 1 (by rfl) ⟨1655495, by rfl⟩ : syracuseStep 2207327 = 3310991) B3310991
theorem B1863263 : Blo 1470555 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B10604141 : Blo 1470555 10604141 := bstep (se 3 (by rfl) ⟨1988276, by rfl⟩ : syracuseStep 10604141 = 3976553) B3976553
theorem B3534599 : Blo 1470555 3534599 := bstep (se 1 (by rfl) ⟨2650949, by rfl⟩ : syracuseStep 3534599 = 5301899) B5301899
theorem B7450379 : Blo 1470555 7450379 := bstep (se 1 (by rfl) ⟨5587784, by rfl⟩ : syracuseStep 7450379 = 11175569) B11175569
theorem B2207543 : Blo 1470555 2207543 := bstep (se 1 (by rfl) ⟨1655657, by rfl⟩ : syracuseStep 2207543 = 3311315) B3311315
theorem B5591065 : Blo 1470555 5591065 := bstep (se 2 (by rfl) ⟨2096649, by rfl⟩ : syracuseStep 5591065 = 4193299) B4193299
theorem B2207849 : Blo 1470555 2207849 := bstep (se 2 (by rfl) ⟨827943, by rfl⟩ : syracuseStep 2207849 = 1655887) B1655887
theorem B3723529 : Blo 1470555 3723529 := bstep (se 2 (by rfl) ⟨1396323, by rfl⟩ : syracuseStep 3723529 = 2792647) B2792647
theorem B1470751 : Blo 1470555 1470751 := bstep (se 1 (by rfl) ⟨1103063, by rfl⟩ : syracuseStep 1470751 = 2206127) B2206127
theorem B1470811 : Blo 1470555 1470811 := bstep (se 1 (by rfl) ⟨1103108, by rfl⟩ : syracuseStep 1470811 = 2206217) B2206217
theorem B4190555 : Blo 1470555 4190555 := bstep (se 1 (by rfl) ⟨3142916, by rfl⟩ : syracuseStep 4190555 = 6285833) B6285833
theorem B1470831 : Blo 1470555 1470831 := bstep (se 1 (by rfl) ⟨1103123, by rfl⟩ : syracuseStep 1470831 = 2206247) B2206247
theorem B1470887 : Blo 1470555 1470887 := bstep (se 1 (by rfl) ⟨1103165, by rfl⟩ : syracuseStep 1470887 = 2206331) B2206331
theorem B2208167 : Blo 1470555 2208167 := bstep (se 1 (by rfl) ⟨1656125, by rfl⟩ : syracuseStep 2208167 = 3312251) B3312251
theorem B11170223 : Blo 1470555 11170223 := bstep (se 1 (by rfl) ⟨8377667, by rfl⟩ : syracuseStep 11170223 = 16755335) B16755335
theorem B3355063 : Blo 1470555 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B2355707 : Blo 1470555 2355707 := bstep (se 1 (by rfl) ⟨1766780, by rfl⟩ : syracuseStep 2355707 = 3533561) B3533561
theorem B1470971 : Blo 1470555 1470971 := bstep (se 1 (by rfl) ⟨1103228, by rfl⟩ : syracuseStep 1470971 = 2206457) B2206457
theorem B2208251 : Blo 1470555 2208251 := bstep (se 1 (by rfl) ⟨1656188, by rfl⟩ : syracuseStep 2208251 = 3312377) B3312377
theorem B18846269 : Blo 1470555 18846269 := bstep (se 3 (by rfl) ⟨3533675, by rfl⟩ : syracuseStep 18846269 = 7067351) B7067351
theorem B1471039 : Blo 1470555 1471039 := bstep (se 1 (by rfl) ⟨1103279, by rfl⟩ : syracuseStep 1471039 = 2206559) B2206559
theorem B1471047 : Blo 1470555 1471047 := bstep (se 1 (by rfl) ⟨1103285, by rfl⟩ : syracuseStep 1471047 = 2206571) B2206571
theorem B2208377 : Blo 1470555 2208377 := bstep (se 2 (by rfl) ⟨828141, by rfl⟩ : syracuseStep 2208377 = 1656283) B1656283
theorem B2355887 : Blo 1470555 2355887 := bstep (se 1 (by rfl) ⟨1766915, by rfl⟩ : syracuseStep 2355887 = 3533831) B3533831
theorem B2650799 : Blo 1470555 2650799 := bstep (se 1 (by rfl) ⟨1988099, by rfl⟩ : syracuseStep 2650799 = 3976199) B3976199
theorem B2208431 : Blo 1470555 2208431 := bstep (se 1 (by rfl) ⟨1656323, by rfl⟩ : syracuseStep 2208431 = 3312647) B3312647
theorem B3142327 : Blo 1470555 3142327 := bstep (se 1 (by rfl) ⟨2356745, by rfl⟩ : syracuseStep 3142327 = 4713491) B4713491
theorem B7451351 : Blo 1470555 7451351 := bstep (se 1 (by rfl) ⟨5588513, by rfl⟩ : syracuseStep 7451351 = 11177027) B11177027
theorem B1471199 : Blo 1470555 1471199 := bstep (se 1 (by rfl) ⟨1103399, by rfl⟩ : syracuseStep 1471199 = 2206799) B2206799
theorem B2208479 : Blo 1470555 2208479 := bstep (se 1 (by rfl) ⟨1656359, by rfl⟩ : syracuseStep 2208479 = 3312719) B3312719
theorem B1471279 : Blo 1470555 1471279 := bstep (se 1 (by rfl) ⟨1103459, by rfl⟩ : syracuseStep 1471279 = 2206919) B2206919
theorem B4969295 : Blo 1470555 4969295 := bstep (se 1 (by rfl) ⟨3726971, by rfl⟩ : syracuseStep 4969295 = 7453943) B7453943
theorem B1471387 : Blo 1470555 1471387 := bstep (se 1 (by rfl) ⟨1103540, by rfl⟩ : syracuseStep 1471387 = 2207081) B2207081
theorem B2651051 : Blo 1470555 2651051 := bstep (se 1 (by rfl) ⟨1988288, by rfl⟩ : syracuseStep 2651051 = 3976577) B3976577
theorem B1471439 : Blo 1470555 1471439 := bstep (se 1 (by rfl) ⟨1103579, by rfl⟩ : syracuseStep 1471439 = 2207159) B2207159
theorem B1471463 : Blo 1470555 1471463 := bstep (se 1 (by rfl) ⟨1103597, by rfl⟩ : syracuseStep 1471463 = 2207195) B2207195
theorem B2208743 : Blo 1470555 2208743 := bstep (se 1 (by rfl) ⟨1656557, by rfl⟩ : syracuseStep 2208743 = 3313115) B3313115
theorem B4715617 : Blo 1470555 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B4969619 : Blo 1470555 4969619 := bstep (se 1 (by rfl) ⟨3727214, by rfl⟩ : syracuseStep 4969619 = 7454429) B7454429
theorem B26866835 : Blo 1470555 26866835 := bstep (se 1 (by rfl) ⟨20150126, by rfl⟩ : syracuseStep 26866835 = 40300253) B40300253
theorem B6288617 : Blo 1470555 6288617 := bstep (se 2 (by rfl) ⟨2358231, by rfl⟩ : syracuseStep 6288617 = 4716463) B4716463
theorem B1471775 : Blo 1470555 1471775 := bstep (se 1 (by rfl) ⟨1103831, by rfl⟩ : syracuseStep 1471775 = 2207663) B2207663
theorem B22639961 : Blo 1470555 22639961 := bstep (se 2 (by rfl) ⟨8489985, by rfl⟩ : syracuseStep 22639961 = 16979971) B16979971
theorem B1471835 : Blo 1470555 1471835 := bstep (se 1 (by rfl) ⟨1103876, by rfl⟩ : syracuseStep 1471835 = 2207753) B2207753
theorem B7451999 : Blo 1470555 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B1471855 : Blo 1470555 1471855 := bstep (se 1 (by rfl) ⟨1103891, by rfl⟩ : syracuseStep 1471855 = 2207783) B2207783
theorem B1471911 : Blo 1470555 1471911 := bstep (se 1 (by rfl) ⟨1103933, by rfl⟩ : syracuseStep 1471911 = 2207867) B2207867
theorem B11179457 : Blo 1470555 11179457 := bstep (se 2 (by rfl) ⟨4192296, by rfl⟩ : syracuseStep 11179457 = 8384593) B8384593
theorem B1471995 : Blo 1470555 1471995 := bstep (se 1 (by rfl) ⟨1103996, by rfl⟩ : syracuseStep 1471995 = 2207993) B2207993
theorem B1472063 : Blo 1470555 1472063 := bstep (se 1 (by rfl) ⟨1104047, by rfl⟩ : syracuseStep 1472063 = 2208095) B2208095
theorem B1472071 : Blo 1470555 1472071 := bstep (se 1 (by rfl) ⟨1104053, by rfl⟩ : syracuseStep 1472071 = 2208107) B2208107
theorem B3724987 : Blo 1470555 3724987 := bstep (se 1 (by rfl) ⟨2793740, by rfl⟩ : syracuseStep 3724987 = 5587481) B5587481
theorem B1472223 : Blo 1470555 1472223 := bstep (se 1 (by rfl) ⟨1104167, by rfl⟩ : syracuseStep 1472223 = 2208335) B2208335
theorem B2094827 : Blo 1470555 2094827 := bstep (se 1 (by rfl) ⟨1571120, by rfl⟩ : syracuseStep 2094827 = 3142241) B3142241
theorem B1472303 : Blo 1470555 1472303 := bstep (se 1 (by rfl) ⟨1104227, by rfl⟩ : syracuseStep 1472303 = 2208455) B2208455
theorem B3184439 : Blo 1470555 3184439 := bstep (se 1 (by rfl) ⟨2388329, by rfl⟩ : syracuseStep 3184439 = 4776659) B4776659
theorem B1472411 : Blo 1470555 1472411 := bstep (se 1 (by rfl) ⟨1104308, by rfl⟩ : syracuseStep 1472411 = 2208617) B2208617
theorem B28301237 : Blo 1470555 28301237 := bstep (se 5 (by rfl) ⟨1326620, by rfl⟩ : syracuseStep 28301237 = 2653241) B2653241
theorem B1472463 : Blo 1470555 1472463 := bstep (se 1 (by rfl) ⟨1104347, by rfl⟩ : syracuseStep 1472463 = 2208695) B2208695
theorem B1472487 : Blo 1470555 1472487 := bstep (se 1 (by rfl) ⟨1104365, by rfl⟩ : syracuseStep 1472487 = 2208731) B2208731
theorem B7952417 : Blo 1470555 7952417 := bstep (se 2 (by rfl) ⟨2982156, by rfl⟩ : syracuseStep 7952417 = 5964313) B5964313
theorem B15915041 : Blo 1470555 15915041 := bstep (se 2 (by rfl) ⟨5968140, by rfl⟩ : syracuseStep 15915041 = 11936281) B11936281
theorem B1677691 : Blo 1470555 1677691 := bstep (se 1 (by rfl) ⟨1258268, by rfl⟩ : syracuseStep 1677691 = 2516537) B2516537
theorem B99359227 : Blo 1470555 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B2792009 : Blo 1470555 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B8059499 : Blo 1470555 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B3726071 : Blo 1470555 3726071 := bstep (se 1 (by rfl) ⟨2794553, by rfl⟩ : syracuseStep 3726071 = 5589107) B5589107
theorem B7445519 : Blo 1470555 7445519 := bstep (se 1 (by rfl) ⟨5584139, by rfl⟩ : syracuseStep 7445519 = 11168279) B11168279
theorem B4963517 : Blo 1470555 4963517 := bstep (se 3 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 4963517 = 1861319) B1861319
theorem B3308777 : Blo 1470555 3308777 := bstep (se 2 (by rfl) ⟨1240791, by rfl⟩ : syracuseStep 3308777 = 2481583) B2481583
theorem B3308831 : Blo 1470555 3308831 := bstep (se 1 (by rfl) ⟨2481623, by rfl⟩ : syracuseStep 3308831 = 4963247) B4963247
theorem B15908375 : Blo 1470555 15908375 := bstep (se 1 (by rfl) ⟨11931281, by rfl⟩ : syracuseStep 15908375 = 23862563) B23862563
theorem B13426199 : Blo 1470555 13426199 := bstep (se 1 (by rfl) ⟨10069649, by rfl⟩ : syracuseStep 13426199 = 20139299) B20139299
theorem B7454267 : Blo 1470555 7454267 := bstep (se 1 (by rfl) ⟨5590700, by rfl⟩ : syracuseStep 7454267 = 11181401) B11181401
theorem B3726931 : Blo 1470555 3726931 := bstep (se 1 (by rfl) ⟨2795198, by rfl⟩ : syracuseStep 3726931 = 5590397) B5590397
theorem B1654447 : Blo 1470555 1654447 := bstep (se 1 (by rfl) ⟨1240835, by rfl⟩ : syracuseStep 1654447 = 2481671) B2481671
theorem B2481961 : Blo 1470555 2481961 := bstep (se 2 (by rfl) ⟨930735, by rfl⟩ : syracuseStep 2481961 = 1861471) B1861471
theorem B3309353 : Blo 1470555 3309353 := bstep (se 2 (by rfl) ⟨1241007, by rfl⟩ : syracuseStep 3309353 = 2482015) B2482015
theorem B7446329 : Blo 1470555 7446329 := bstep (se 2 (by rfl) ⟨2792373, by rfl⟩ : syracuseStep 7446329 = 5584747) B5584747
theorem B6283115 : Blo 1470555 6283115 := bstep (se 1 (by rfl) ⟨4712336, by rfl⟩ : syracuseStep 6283115 = 9424673) B9424673
theorem B6283183 : Blo 1470555 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B1654735 : Blo 1470555 1654735 := bstep (se 1 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 1654735 = 2482103) B2482103
theorem B21200899 : Blo 1470555 21200899 := bstep (se 1 (by rfl) ⟨15900674, by rfl⟩ : syracuseStep 21200899 = 31801349) B31801349
theorem B7454753 : Blo 1470555 7454753 := bstep (se 2 (by rfl) ⟨2795532, by rfl⟩ : syracuseStep 7454753 = 5591065) B5591065
theorem B1491175 : Blo 1470555 1491175 := bstep (se 1 (by rfl) ⟨1118381, by rfl⟩ : syracuseStep 1491175 = 2236763) B2236763
theorem B14139623 : Blo 1470555 14139623 := bstep (se 1 (by rfl) ⟨10604717, by rfl⟩ : syracuseStep 14139623 = 21209435) B21209435
theorem B2793703 : Blo 1470555 2793703 := bstep (se 1 (by rfl) ⟨2095277, by rfl⟩ : syracuseStep 2793703 = 4190555) B4190555
theorem B7446815 : Blo 1470555 7446815 := bstep (se 1 (by rfl) ⟨5585111, by rfl⟩ : syracuseStep 7446815 = 11170223) B11170223
theorem B2687263 : Blo 1470555 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B8380745 : Blo 1470555 8380745 := bstep (se 2 (by rfl) ⟨3142779, by rfl⟩ : syracuseStep 8380745 = 6285559) B6285559
theorem B4964705 : Blo 1470555 4964705 := bstep (se 2 (by rfl) ⟨1861764, by rfl⟩ : syracuseStep 4964705 = 3723529) B3723529
theorem B1655167 : Blo 1470555 1655167 := bstep (se 1 (by rfl) ⟨1241375, by rfl⟩ : syracuseStep 1655167 = 2482751) B2482751
theorem B5587451 : Blo 1470555 5587451 := bstep (se 1 (by rfl) ⟨4190588, by rfl⟩ : syracuseStep 5587451 = 8381177) B8381177
theorem B16351739 : Blo 1470555 16351739 := bstep (se 1 (by rfl) ⟨12263804, by rfl⟩ : syracuseStep 16351739 = 24527609) B24527609
theorem B71582615 : Blo 1470555 71582615 := bstep (se 1 (by rfl) ⟨53686961, by rfl⟩ : syracuseStep 71582615 = 107373923) B107373923
theorem B18867491 : Blo 1470555 18867491 := bstep (se 1 (by rfl) ⟨14150618, by rfl⟩ : syracuseStep 18867491 = 28301237) B28301237
theorem B5301611 : Blo 1470555 5301611 := bstep (se 1 (by rfl) ⟨3976208, by rfl⟩ : syracuseStep 5301611 = 7952417) B7952417
theorem B3310955 : Blo 1470555 3310955 := bstep (se 1 (by rfl) ⟨2483216, by rfl⟩ : syracuseStep 3310955 = 4966433) B4966433
theorem B10610027 : Blo 1470555 10610027 := bstep (se 1 (by rfl) ⟨7957520, by rfl⟩ : syracuseStep 10610027 = 15915041) B15915041
theorem B9430465 : Blo 1470555 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B3311225 : Blo 1470555 3311225 := bstep (se 2 (by rfl) ⟨1241709, by rfl⟩ : syracuseStep 3311225 = 2483419) B2483419
theorem B4966055 : Blo 1470555 4966055 := bstep (se 1 (by rfl) ⟨3724541, by rfl⟩ : syracuseStep 4966055 = 7449083) B7449083
theorem B1656571 : Blo 1470555 1656571 := bstep (se 1 (by rfl) ⟨1242428, by rfl⟩ : syracuseStep 1656571 = 2484857) B2484857
theorem B1656607 : Blo 1470555 1656607 := bstep (se 1 (by rfl) ⟨1242455, by rfl⟩ : syracuseStep 1656607 = 2484911) B2484911
theorem B2484047 : Blo 1470555 2484047 := bstep (se 1 (by rfl) ⟨1863035, by rfl⟩ : syracuseStep 2484047 = 3726071) B3726071
theorem B8947685 : Blo 1470555 8947685 := bstep (se 4 (by rfl) ⟨838845, by rfl⟩ : syracuseStep 8947685 = 1677691) B1677691
theorem B11176055 : Blo 1470555 11176055 := bstep (se 1 (by rfl) ⟨8382041, by rfl⟩ : syracuseStep 11176055 = 16764083) B16764083
theorem B2205851 : Blo 1470555 2205851 := bstep (se 1 (by rfl) ⟨1654388, by rfl⟩ : syracuseStep 2205851 = 3308777) B3308777
theorem B2205887 : Blo 1470555 2205887 := bstep (se 1 (by rfl) ⟨1654415, by rfl⟩ : syracuseStep 2205887 = 3308831) B3308831
theorem B2205929 : Blo 1470555 2205929 := bstep (se 2 (by rfl) ⟨827223, by rfl⟩ : syracuseStep 2205929 = 1654447) B1654447
theorem B4966649 : Blo 1470555 4966649 := bstep (se 2 (by rfl) ⟨1862493, by rfl⟩ : syracuseStep 4966649 = 3724987) B3724987
theorem B17893669 : Blo 1470555 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B4966703 : Blo 1470555 4966703 := bstep (se 1 (by rfl) ⟨3725027, by rfl⟩ : syracuseStep 4966703 = 7450055) B7450055
theorem B4966919 : Blo 1470555 4966919 := bstep (se 1 (by rfl) ⟨3725189, by rfl⟩ : syracuseStep 4966919 = 7450379) B7450379
theorem B2206235 : Blo 1470555 2206235 := bstep (se 1 (by rfl) ⟨1654676, by rfl⟩ : syracuseStep 2206235 = 3309353) B3309353
theorem B4188743 : Blo 1470555 4188743 := bstep (se 1 (by rfl) ⟨3141557, by rfl⟩ : syracuseStep 4188743 = 6283115) B6283115
theorem B2206313 : Blo 1470555 2206313 := bstep (se 2 (by rfl) ⟨827367, by rfl⟩ : syracuseStep 2206313 = 1654735) B1654735
theorem B3312233 : Blo 1470555 3312233 := bstep (se 2 (by rfl) ⟨1242087, by rfl⟩ : syracuseStep 3312233 = 2484175) B2484175
theorem B9431747 : Blo 1470555 9431747 := bstep (se 1 (by rfl) ⟨7073810, by rfl⟩ : syracuseStep 9431747 = 14147621) B14147621
theorem B12577679 : Blo 1470555 12577679 := bstep (se 1 (by rfl) ⟨9433259, by rfl⟩ : syracuseStep 12577679 = 18866519) B18866519
theorem B2206841 : Blo 1470555 2206841 := bstep (se 2 (by rfl) ⟨827565, by rfl⟩ : syracuseStep 2206841 = 1655131) B1655131
theorem B4967567 : Blo 1470555 4967567 := bstep (se 1 (by rfl) ⟨3725675, by rfl⟩ : syracuseStep 4967567 = 7451351) B7451351
theorem B2206943 : Blo 1470555 2206943 := bstep (se 1 (by rfl) ⟨1655207, by rfl⟩ : syracuseStep 2206943 = 3310415) B3310415
theorem B3312863 : Blo 1470555 3312863 := bstep (se 1 (by rfl) ⟨2484647, by rfl⟩ : syracuseStep 3312863 = 4969295) B4969295
theorem B4189427 : Blo 1470555 4189427 := bstep (se 1 (by rfl) ⟨3142070, by rfl⟩ : syracuseStep 4189427 = 6284141) B6284141
theorem B2206985 : Blo 1470555 2206985 := bstep (se 2 (by rfl) ⟨827619, by rfl⟩ : syracuseStep 2206985 = 1655239) B1655239
theorem B2207087 : Blo 1470555 2207087 := bstep (se 1 (by rfl) ⟨1655315, by rfl⟩ : syracuseStep 2207087 = 3310631) B3310631
theorem B3313079 : Blo 1470555 3313079 := bstep (se 1 (by rfl) ⟨2484809, by rfl⟩ : syracuseStep 3313079 = 4969619) B4969619
theorem B17911223 : Blo 1470555 17911223 := bstep (se 1 (by rfl) ⟨13433417, by rfl⟩ : syracuseStep 17911223 = 26866835) B26866835
theorem B2207207 : Blo 1470555 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B15093307 : Blo 1470555 15093307 := bstep (se 1 (by rfl) ⟨11319980, by rfl⟩ : syracuseStep 15093307 = 22639961) B22639961
theorem B4967999 : Blo 1470555 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B4189769 : Blo 1470555 4189769 := bstep (se 2 (by rfl) ⟨1571163, by rfl⟩ : syracuseStep 4189769 = 3142327) B3142327
theorem B2207339 : Blo 1470555 2207339 := bstep (se 1 (by rfl) ⟨1655504, by rfl⟩ : syracuseStep 2207339 = 3311009) B3311009
theorem B53079715 : Blo 1470555 53079715 := bstep (se 1 (by rfl) ⟨39809786, by rfl⟩ : syracuseStep 53079715 = 79619573) B79619573
theorem B2207465 : Blo 1470555 2207465 := bstep (se 2 (by rfl) ⟨827799, by rfl⟩ : syracuseStep 2207465 = 1655599) B1655599
theorem B2207609 : Blo 1470555 2207609 := bstep (se 2 (by rfl) ⟨827853, by rfl⟩ : syracuseStep 2207609 = 1655707) B1655707
theorem B8384411 : Blo 1470555 8384411 := bstep (se 1 (by rfl) ⟨6288308, by rfl⟩ : syracuseStep 8384411 = 12576617) B12576617
theorem B7450541 : Blo 1470555 7450541 := bstep (se 3 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 7450541 = 2793953) B2793953
theorem B2207711 : Blo 1470555 2207711 := bstep (se 1 (by rfl) ⟨1655783, by rfl⟩ : syracuseStep 2207711 = 3311567) B3311567
theorem B11481097 : Blo 1470555 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B6287489 : Blo 1470555 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B2207963 : Blo 1470555 2207963 := bstep (se 1 (by rfl) ⟨1655972, by rfl⟩ : syracuseStep 2207963 = 3311945) B3311945
theorem B1470695 : Blo 1470555 1470695 := bstep (se 1 (by rfl) ⟨1103021, by rfl⟩ : syracuseStep 1470695 = 2206043) B2206043
theorem B2207975 : Blo 1470555 2207975 := bstep (se 1 (by rfl) ⟨1655981, by rfl⟩ : syracuseStep 2207975 = 3311963) B3311963
theorem B4968701 : Blo 1470555 4968701 := bstep (se 3 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 4968701 = 1863263) B1863263
theorem B1470847 : Blo 1470555 1470847 := bstep (se 1 (by rfl) ⟨1103135, by rfl⟩ : syracuseStep 1470847 = 2206271) B2206271
theorem B2208137 : Blo 1470555 2208137 := bstep (se 2 (by rfl) ⟨828051, by rfl⟩ : syracuseStep 2208137 = 1656103) B1656103
theorem B1470927 : Blo 1470555 1470927 := bstep (se 1 (by rfl) ⟨1103195, by rfl⟩ : syracuseStep 1470927 = 2206391) B2206391
theorem B2208233 : Blo 1470555 2208233 := bstep (se 2 (by rfl) ⟨828087, by rfl⟩ : syracuseStep 2208233 = 1656175) B1656175
theorem B72593981 : Blo 1470555 72593981 := bstep (se 3 (by rfl) ⟨13611371, by rfl⟩ : syracuseStep 72593981 = 27222743) B27222743
theorem B1471079 : Blo 1470555 1471079 := bstep (se 1 (by rfl) ⟨1103309, by rfl⟩ : syracuseStep 1471079 = 2206619) B2206619
theorem B2208359 : Blo 1470555 2208359 := bstep (se 1 (by rfl) ⟨1656269, by rfl⟩ : syracuseStep 2208359 = 3312539) B3312539
theorem B2208491 : Blo 1470555 2208491 := bstep (se 1 (by rfl) ⟨1656368, by rfl⟩ : syracuseStep 2208491 = 3312737) B3312737
theorem B2208521 : Blo 1470555 2208521 := bstep (se 2 (by rfl) ⟨828195, by rfl⟩ : syracuseStep 2208521 = 1656391) B1656391
theorem B4969241 : Blo 1470555 4969241 := bstep (se 2 (by rfl) ⟨1863465, by rfl⟩ : syracuseStep 4969241 = 3726931) B3726931
theorem B8491837 : Blo 1470555 8491837 := bstep (se 3 (by rfl) ⟨1592219, by rfl⟩ : syracuseStep 8491837 = 3184439) B3184439
theorem B1471343 : Blo 1470555 1471343 := bstep (se 1 (by rfl) ⟨1103507, by rfl⟩ : syracuseStep 1471343 = 2207015) B2207015
theorem B2208623 : Blo 1470555 2208623 := bstep (se 1 (by rfl) ⟨1656467, by rfl⟩ : syracuseStep 2208623 = 3312935) B3312935
theorem B1471399 : Blo 1470555 1471399 := bstep (se 1 (by rfl) ⟨1103549, by rfl⟩ : syracuseStep 1471399 = 2207099) B2207099
theorem B3142651 : Blo 1470555 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B1471483 : Blo 1470555 1471483 := bstep (se 1 (by rfl) ⟨1103612, by rfl⟩ : syracuseStep 1471483 = 2207225) B2207225
theorem B4191227 : Blo 1470555 4191227 := bstep (se 1 (by rfl) ⟨3143420, by rfl⟩ : syracuseStep 4191227 = 6286841) B6286841
theorem B10605583 : Blo 1470555 10605583 := bstep (se 1 (by rfl) ⟨7954187, by rfl⟩ : syracuseStep 10605583 = 15908375) B15908375
theorem B8950799 : Blo 1470555 8950799 := bstep (se 1 (by rfl) ⟨6713099, by rfl⟩ : syracuseStep 8950799 = 13426199) B13426199
theorem B4969511 : Blo 1470555 4969511 := bstep (se 1 (by rfl) ⟨3727133, by rfl⟩ : syracuseStep 4969511 = 7454267) B7454267
theorem B1471551 : Blo 1470555 1471551 := bstep (se 1 (by rfl) ⟨1103663, by rfl⟩ : syracuseStep 1471551 = 2207327) B2207327
theorem B2356399 : Blo 1470555 2356399 := bstep (se 1 (by rfl) ⟨1767299, by rfl⟩ : syracuseStep 2356399 = 3534599) B3534599
theorem B1471695 : Blo 1470555 1471695 := bstep (se 1 (by rfl) ⟨1103771, by rfl⟩ : syracuseStep 1471695 = 2207543) B2207543
theorem B8377577 : Blo 1470555 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B1471899 : Blo 1470555 1471899 := bstep (se 1 (by rfl) ⟨1103924, by rfl⟩ : syracuseStep 1471899 = 2207849) B2207849
theorem B7452161 : Blo 1470555 7452161 := bstep (se 2 (by rfl) ⟨2794560, by rfl⟩ : syracuseStep 7452161 = 5589121) B5589121
theorem B1472111 : Blo 1470555 1472111 := bstep (se 1 (by rfl) ⟨1104083, by rfl⟩ : syracuseStep 1472111 = 2208167) B2208167
theorem B1570471 : Blo 1470555 1570471 := bstep (se 1 (by rfl) ⟨1177853, by rfl⟩ : syracuseStep 1570471 = 2355707) B2355707
theorem B1472167 : Blo 1470555 1472167 := bstep (se 1 (by rfl) ⟨1104125, by rfl⟩ : syracuseStep 1472167 = 2208251) B2208251
theorem B12564179 : Blo 1470555 12564179 := bstep (se 1 (by rfl) ⟨9423134, by rfl⟩ : syracuseStep 12564179 = 18846269) B18846269
theorem B1472251 : Blo 1470555 1472251 := bstep (se 1 (by rfl) ⟨1104188, by rfl⟩ : syracuseStep 1472251 = 2208377) B2208377
theorem B1570591 : Blo 1470555 1570591 := bstep (se 1 (by rfl) ⟨1177943, by rfl⟩ : syracuseStep 1570591 = 2355887) B2355887
theorem B1767199 : Blo 1470555 1767199 := bstep (se 1 (by rfl) ⟨1325399, by rfl⟩ : syracuseStep 1767199 = 2650799) B2650799
theorem B1472287 : Blo 1470555 1472287 := bstep (se 1 (by rfl) ⟨1104215, by rfl⟩ : syracuseStep 1472287 = 2208431) B2208431
theorem B1472319 : Blo 1470555 1472319 := bstep (se 1 (by rfl) ⟨1104239, by rfl⟩ : syracuseStep 1472319 = 2208479) B2208479
theorem B1767367 : Blo 1470555 1767367 := bstep (se 1 (by rfl) ⟨1325525, by rfl⟩ : syracuseStep 1767367 = 2651051) B2651051
theorem B95475671 : Blo 1470555 95475671 := bstep (se 1 (by rfl) ⟨71606753, by rfl⟩ : syracuseStep 95475671 = 143213507) B143213507
theorem B1472495 : Blo 1470555 1472495 := bstep (se 1 (by rfl) ⟨1104371, by rfl⟩ : syracuseStep 1472495 = 2208743) B2208743
theorem B4192411 : Blo 1470555 4192411 := bstep (se 1 (by rfl) ⟨3144308, by rfl⟩ : syracuseStep 4192411 = 6288617) B6288617
theorem B3725473 : Blo 1470555 3725473 := bstep (se 2 (by rfl) ⟨1397052, by rfl⟩ : syracuseStep 3725473 = 2794105) B2794105
theorem B6281459 : Blo 1470555 6281459 := bstep (se 1 (by rfl) ⟨4711094, by rfl⟩ : syracuseStep 6281459 = 9422189) B9422189
theorem B7452971 : Blo 1470555 7452971 := bstep (se 1 (by rfl) ⟨5589728, by rfl⟩ : syracuseStep 7452971 = 11179457) B11179457
theorem B12573305 : Blo 1470555 12573305 := bstep (se 2 (by rfl) ⟨4714989, by rfl⟩ : syracuseStep 12573305 = 9429979) B9429979
theorem B20126483 : Blo 1470555 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B7445357 : Blo 1470555 7445357 := bstep (se 3 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 7445357 = 2792009) B2792009
theorem B163371919 : Blo 1470555 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B6282143 : Blo 1470555 6282143 := bstep (se 1 (by rfl) ⟨4711607, by rfl⟩ : syracuseStep 6282143 = 9423215) B9423215
theorem B5372999 : Blo 1470555 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B18848933 : Blo 1470555 18848933 := bstep (se 4 (by rfl) ⟨1767087, by rfl⟩ : syracuseStep 18848933 = 3534175) B3534175
theorem B21208229 : Blo 1470555 21208229 := bstep (se 4 (by rfl) ⟨1988271, by rfl⟩ : syracuseStep 21208229 = 3976543) B3976543
theorem B10607831 : Blo 1470555 10607831 := bstep (se 1 (by rfl) ⟨7955873, by rfl⟩ : syracuseStep 10607831 = 15911747) B15911747
theorem B5586205 : Blo 1470555 5586205 := bstep (se 3 (by rfl) ⟨1047413, by rfl⟩ : syracuseStep 5586205 = 2094827) B2094827
theorem B4963679 : Blo 1470555 4963679 := bstep (se 1 (by rfl) ⟨3722759, by rfl⟩ : syracuseStep 4963679 = 7445519) B7445519
theorem B9428363 : Blo 1470555 9428363 := bstep (se 1 (by rfl) ⟨7071272, by rfl⟩ : syracuseStep 9428363 = 14142545) B14142545
theorem B16768457 : Blo 1470555 16768457 := bstep (se 2 (by rfl) ⟨6288171, by rfl⟩ : syracuseStep 16768457 = 12576343) B12576343
theorem B3309011 : Blo 1470555 3309011 := bstep (se 1 (by rfl) ⟨2481758, by rfl⟩ : syracuseStep 3309011 = 4963517) B4963517
theorem B3309281 : Blo 1470555 3309281 := bstep (se 2 (by rfl) ⟨1240980, by rfl⟩ : syracuseStep 3309281 = 2481961) B2481961
theorem B3727073 : Blo 1470555 3727073 := bstep (se 2 (by rfl) ⟨1397652, by rfl⟩ : syracuseStep 3727073 = 2795305) B2795305
theorem B7069427 : Blo 1470555 7069427 := bstep (se 1 (by rfl) ⟨5302070, by rfl⟩ : syracuseStep 7069427 = 10604141) B10604141
theorem B4964219 : Blo 1470555 4964219 := bstep (se 1 (by rfl) ⟨3723164, by rfl⟩ : syracuseStep 4964219 = 7446329) B7446329
theorem B529915877 : Blo 1470555 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B4964543 : Blo 1470555 4964543 := bstep (se 1 (by rfl) ⟨3723407, by rfl⟩ : syracuseStep 4964543 = 7446815) B7446815
theorem B5587163 : Blo 1470555 5587163 := bstep (se 1 (by rfl) ⟨4190372, by rfl⟩ : syracuseStep 5587163 = 8380745) B8380745
theorem B3309803 : Blo 1470555 3309803 := bstep (se 1 (by rfl) ⟨2482352, by rfl⟩ : syracuseStep 3309803 = 4964705) B4964705
theorem B2794151 : Blo 1470555 2794151 := bstep (se 1 (by rfl) ⟨2095613, by rfl⟩ : syracuseStep 2794151 = 4191227) B4191227
theorem B11322449 : Blo 1470555 11322449 := bstep (se 2 (by rfl) ⟨4245918, by rfl⟩ : syracuseStep 11322449 = 8491837) B8491837
theorem B3310703 : Blo 1470555 3310703 := bstep (se 1 (by rfl) ⟨2483027, by rfl⟩ : syracuseStep 3310703 = 4966055) B4966055
theorem B1656031 : Blo 1470555 1656031 := bstep (se 1 (by rfl) ⟨1242023, by rfl⟩ : syracuseStep 1656031 = 2484047) B2484047
theorem B5965123 : Blo 1470555 5965123 := bstep (se 1 (by rfl) ⟨4473842, by rfl⟩ : syracuseStep 5965123 = 8947685) B8947685
theorem B14140777 : Blo 1470555 14140777 := bstep (se 2 (by rfl) ⟨5302791, by rfl⟩ : syracuseStep 14140777 = 10605583) B10605583
theorem B4187639 : Blo 1470555 4187639 := bstep (se 1 (by rfl) ⟨3140729, by rfl⟩ : syracuseStep 4187639 = 6281459) B6281459
theorem B3311099 : Blo 1470555 3311099 := bstep (se 1 (by rfl) ⟨2483324, by rfl⟩ : syracuseStep 3311099 = 4966649) B4966649
theorem B3311135 : Blo 1470555 3311135 := bstep (se 1 (by rfl) ⟨2483351, by rfl⟩ : syracuseStep 3311135 = 4966703) B4966703
theorem B3311279 : Blo 1470555 3311279 := bstep (se 1 (by rfl) ⟨2483459, by rfl⟩ : syracuseStep 3311279 = 4966919) B4966919
theorem B7448273 : Blo 1470555 7448273 := bstep (se 2 (by rfl) ⟨2793102, by rfl⟩ : syracuseStep 7448273 = 5586205) B5586205
theorem B8382203 : Blo 1470555 8382203 := bstep (se 1 (by rfl) ⟨6286652, by rfl⟩ : syracuseStep 8382203 = 12573305) B12573305
theorem B4188095 : Blo 1470555 4188095 := bstep (se 1 (by rfl) ⟨3141071, by rfl⟩ : syracuseStep 4188095 = 6282143) B6282143
theorem B3581999 : Blo 1470555 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B3311711 : Blo 1470555 3311711 := bstep (se 1 (by rfl) ⟨2483783, by rfl⟩ : syracuseStep 3311711 = 4967567) B4967567
theorem B7071887 : Blo 1470555 7071887 := bstep (se 1 (by rfl) ⟨5303915, by rfl⟩ : syracuseStep 7071887 = 10607831) B10607831
theorem B70772953 : Blo 1470555 70772953 := bstep (se 2 (by rfl) ⟨26539857, by rfl⟩ : syracuseStep 70772953 = 53079715) B53079715
theorem B6285575 : Blo 1470555 6285575 := bstep (se 1 (by rfl) ⟨4714181, by rfl⟩ : syracuseStep 6285575 = 9428363) B9428363
theorem B2206007 : Blo 1470555 2206007 := bstep (se 1 (by rfl) ⟨1654505, by rfl⟩ : syracuseStep 2206007 = 3309011) B3309011
theorem B3311999 : Blo 1470555 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B2206187 : Blo 1470555 2206187 := bstep (se 1 (by rfl) ⟨1654640, by rfl⟩ : syracuseStep 2206187 = 3309281) B3309281
theorem B2484715 : Blo 1470555 2484715 := bstep (se 1 (by rfl) ⟨1863536, by rfl⟩ : syracuseStep 2484715 = 3727073) B3727073
theorem B4712951 : Blo 1470555 4712951 := bstep (se 1 (by rfl) ⟨3534713, by rfl⟩ : syracuseStep 4712951 = 7069427) B7069427
theorem B5589607 : Blo 1470555 5589607 := bstep (se 1 (by rfl) ⟨4192205, by rfl⟩ : syracuseStep 5589607 = 8384411) B8384411
theorem B4967027 : Blo 1470555 4967027 := bstep (se 1 (by rfl) ⟨3725270, by rfl⟩ : syracuseStep 4967027 = 7450541) B7450541
theorem B3312467 : Blo 1470555 3312467 := bstep (se 1 (by rfl) ⟨2484350, by rfl⟩ : syracuseStep 3312467 = 4968701) B4968701
theorem B5589881 : Blo 1470555 5589881 := bstep (se 2 (by rfl) ⟨2096205, by rfl⟩ : syracuseStep 5589881 = 4192411) B4192411
theorem B4967297 : Blo 1470555 4967297 := bstep (se 2 (by rfl) ⟨1862736, by rfl⟩ : syracuseStep 4967297 = 3725473) B3725473
theorem B23858225 : Blo 1470555 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B2206889 : Blo 1470555 2206889 := bstep (se 2 (by rfl) ⟨827583, by rfl⟩ : syracuseStep 2206889 = 1655167) B1655167
theorem B3312827 : Blo 1470555 3312827 := bstep (se 1 (by rfl) ⟨2484620, by rfl⟩ : syracuseStep 3312827 = 4969241) B4969241
theorem B47721743 : Blo 1470555 47721743 := bstep (se 1 (by rfl) ⟨35791307, by rfl⟩ : syracuseStep 47721743 = 71582615) B71582615
theorem B5967199 : Blo 1470555 5967199 := bstep (se 1 (by rfl) ⟨4475399, by rfl⟩ : syracuseStep 5967199 = 8950799) B8950799
theorem B3313007 : Blo 1470555 3313007 := bstep (se 1 (by rfl) ⟨2484755, by rfl⟩ : syracuseStep 3313007 = 4969511) B4969511
theorem B12578327 : Blo 1470555 12578327 := bstep (se 1 (by rfl) ⟨9433745, by rfl⟩ : syracuseStep 12578327 = 18867491) B18867491
theorem B8375845 : Blo 1470555 8375845 := bstep (se 4 (by rfl) ⟨785235, by rfl⟩ : syracuseStep 8375845 = 1570471) B1570471
theorem B3534407 : Blo 1470555 3534407 := bstep (se 1 (by rfl) ⟨2650805, by rfl⟩ : syracuseStep 3534407 = 5301611) B5301611
theorem B2207303 : Blo 1470555 2207303 := bstep (se 1 (by rfl) ⟨1655477, by rfl⟩ : syracuseStep 2207303 = 3310955) B3310955
theorem B7073351 : Blo 1470555 7073351 := bstep (se 1 (by rfl) ⟨5305013, by rfl⟩ : syracuseStep 7073351 = 10610027) B10610027
theorem B4968107 : Blo 1470555 4968107 := bstep (se 1 (by rfl) ⟨3726080, by rfl⟩ : syracuseStep 4968107 = 7452161) B7452161
theorem B2207483 : Blo 1470555 2207483 := bstep (se 1 (by rfl) ⟨1655612, by rfl⟩ : syracuseStep 2207483 = 3311225) B3311225
theorem B8376119 : Blo 1470555 8376119 := bstep (se 1 (by rfl) ⟨6282089, by rfl⟩ : syracuseStep 8376119 = 12564179) B12564179
theorem B217829225 : Blo 1470555 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B4190201 : Blo 1470555 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B7450703 : Blo 1470555 7450703 := bstep (se 1 (by rfl) ⟨5588027, by rfl⟩ : syracuseStep 7450703 = 11176055) B11176055
theorem B1470567 : Blo 1470555 1470567 := bstep (se 1 (by rfl) ⟨1102925, by rfl⟩ : syracuseStep 1470567 = 2205851) B2205851
theorem B1470591 : Blo 1470555 1470591 := bstep (se 1 (by rfl) ⟨1102943, by rfl⟩ : syracuseStep 1470591 = 2205887) B2205887
theorem B1470619 : Blo 1470555 1470619 := bstep (se 1 (by rfl) ⟨1102964, by rfl⟩ : syracuseStep 1470619 = 2205929) B2205929
theorem B14332069 : Blo 1470555 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B4968647 : Blo 1470555 4968647 := bstep (se 1 (by rfl) ⟨3726485, by rfl⟩ : syracuseStep 4968647 = 7452971) B7452971
theorem B3141865 : Blo 1470555 3141865 := bstep (se 2 (by rfl) ⟨1178199, by rfl⟩ : syracuseStep 3141865 = 2356399) B2356399
theorem B1470823 : Blo 1470555 1470823 := bstep (se 1 (by rfl) ⟨1103117, by rfl⟩ : syracuseStep 1470823 = 2206235) B2206235
theorem B1470875 : Blo 1470555 1470875 := bstep (se 1 (by rfl) ⟨1103156, by rfl⟩ : syracuseStep 1470875 = 2206313) B2206313
theorem B2208155 : Blo 1470555 2208155 := bstep (se 1 (by rfl) ⟨1656116, by rfl⟩ : syracuseStep 2208155 = 3312233) B3312233
theorem B6287831 : Blo 1470555 6287831 := bstep (se 1 (by rfl) ⟨4715873, by rfl⟩ : syracuseStep 6287831 = 9431747) B9431747
theorem B8385119 : Blo 1470555 8385119 := bstep (se 1 (by rfl) ⟨6288839, by rfl⟩ : syracuseStep 8385119 = 12577679) B12577679
theorem B20124409 : Blo 1470555 20124409 := bstep (se 2 (by rfl) ⟨7546653, by rfl⟩ : syracuseStep 20124409 = 15093307) B15093307
theorem B1471227 : Blo 1470555 1471227 := bstep (se 1 (by rfl) ⟨1103420, by rfl⟩ : syracuseStep 1471227 = 2206841) B2206841
theorem B1471295 : Blo 1470555 1471295 := bstep (se 1 (by rfl) ⟨1103471, by rfl⟩ : syracuseStep 1471295 = 2206943) B2206943
theorem B2208575 : Blo 1470555 2208575 := bstep (se 1 (by rfl) ⟨1656431, by rfl⟩ : syracuseStep 2208575 = 3312863) B3312863
theorem B1471323 : Blo 1470555 1471323 := bstep (se 1 (by rfl) ⟨1103492, by rfl⟩ : syracuseStep 1471323 = 2206985) B2206985
theorem B1471391 : Blo 1470555 1471391 := bstep (se 1 (by rfl) ⟨1103543, by rfl⟩ : syracuseStep 1471391 = 2207087) B2207087
theorem B2208719 : Blo 1470555 2208719 := bstep (se 1 (by rfl) ⟨1656539, by rfl⟩ : syracuseStep 2208719 = 3313079) B3313079
theorem B11940815 : Blo 1470555 11940815 := bstep (se 1 (by rfl) ⟨8955611, by rfl⟩ : syracuseStep 11940815 = 17911223) B17911223
theorem B11178971 : Blo 1470555 11178971 := bstep (se 1 (by rfl) ⟨8384228, by rfl⟩ : syracuseStep 11178971 = 16768457) B16768457
theorem B1471471 : Blo 1470555 1471471 := bstep (se 1 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 1471471 = 2207207) B2207207
theorem B2208761 : Blo 1470555 2208761 := bstep (se 2 (by rfl) ⟨828285, by rfl⟩ : syracuseStep 2208761 = 1656571) B1656571
theorem B2094121 : Blo 1470555 2094121 := bstep (se 2 (by rfl) ⟨785295, by rfl⟩ : syracuseStep 2094121 = 1570591) B1570591
theorem B2356265 : Blo 1470555 2356265 := bstep (se 2 (by rfl) ⟨883599, by rfl⟩ : syracuseStep 2356265 = 1767199) B1767199
theorem B2208809 : Blo 1470555 2208809 := bstep (se 2 (by rfl) ⟨828303, by rfl⟩ : syracuseStep 2208809 = 1656607) B1656607
theorem B1471559 : Blo 1470555 1471559 := bstep (se 1 (by rfl) ⟨1103669, by rfl⟩ : syracuseStep 1471559 = 2207339) B2207339
theorem B1471643 : Blo 1470555 1471643 := bstep (se 1 (by rfl) ⟨1103732, by rfl⟩ : syracuseStep 1471643 = 2207465) B2207465
theorem B1471739 : Blo 1470555 1471739 := bstep (se 1 (by rfl) ⟨1103804, by rfl⟩ : syracuseStep 1471739 = 2207609) B2207609
theorem B2356489 : Blo 1470555 2356489 := bstep (se 2 (by rfl) ⟨883683, by rfl⟩ : syracuseStep 2356489 = 1767367) B1767367
theorem B1471807 : Blo 1470555 1471807 := bstep (se 1 (by rfl) ⟨1103855, by rfl⟩ : syracuseStep 1471807 = 2207711) B2207711
theorem B353277251 : Blo 1470555 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B28267865 : Blo 1470555 28267865 := bstep (se 2 (by rfl) ⟨10600449, by rfl⟩ : syracuseStep 28267865 = 21200899) B21200899
theorem B15308129 : Blo 1470555 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B4969835 : Blo 1470555 4969835 := bstep (se 1 (by rfl) ⟨3727376, by rfl⟩ : syracuseStep 4969835 = 7454753) B7454753
theorem B4191659 : Blo 1470555 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B1471975 : Blo 1470555 1471975 := bstep (se 1 (by rfl) ⟨1103981, by rfl⟩ : syracuseStep 1471975 = 2207963) B2207963
theorem B9426415 : Blo 1470555 9426415 := bstep (se 1 (by rfl) ⟨7069811, by rfl⟩ : syracuseStep 9426415 = 14139623) B14139623
theorem B1471983 : Blo 1470555 1471983 := bstep (se 1 (by rfl) ⟨1103987, by rfl⟩ : syracuseStep 1471983 = 2207975) B2207975
theorem B1472091 : Blo 1470555 1472091 := bstep (se 1 (by rfl) ⟨1104068, by rfl⟩ : syracuseStep 1472091 = 2208137) B2208137
theorem B1988233 : Blo 1470555 1988233 := bstep (se 2 (by rfl) ⟨745587, by rfl⟩ : syracuseStep 1988233 = 1491175) B1491175
theorem B3724937 : Blo 1470555 3724937 := bstep (se 2 (by rfl) ⟨1396851, by rfl⟩ : syracuseStep 3724937 = 2793703) B2793703
theorem B1472155 : Blo 1470555 1472155 := bstep (se 1 (by rfl) ⟨1104116, by rfl⟩ : syracuseStep 1472155 = 2208233) B2208233
theorem B3724967 : Blo 1470555 3724967 := bstep (se 1 (by rfl) ⟨2793725, by rfl⟩ : syracuseStep 3724967 = 5587451) B5587451
theorem B10901159 : Blo 1470555 10901159 := bstep (se 1 (by rfl) ⟨8175869, by rfl⟩ : syracuseStep 10901159 = 16351739) B16351739
theorem B48395987 : Blo 1470555 48395987 := bstep (se 1 (by rfl) ⟨36296990, by rfl⟩ : syracuseStep 48395987 = 72593981) B72593981
theorem B1472239 : Blo 1470555 1472239 := bstep (se 1 (by rfl) ⟨1104179, by rfl⟩ : syracuseStep 1472239 = 2208359) B2208359
theorem B1472327 : Blo 1470555 1472327 := bstep (se 1 (by rfl) ⟨1104245, by rfl⟩ : syracuseStep 1472327 = 2208491) B2208491
theorem B1472347 : Blo 1470555 1472347 := bstep (se 1 (by rfl) ⟨1104260, by rfl⟩ : syracuseStep 1472347 = 2208521) B2208521
theorem B1472415 : Blo 1470555 1472415 := bstep (se 1 (by rfl) ⟨1104311, by rfl⟩ : syracuseStep 1472415 = 2208623) B2208623
theorem B5585051 : Blo 1470555 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B63650447 : Blo 1470555 63650447 := bstep (se 1 (by rfl) ⟨47737835, by rfl⟩ : syracuseStep 63650447 = 95475671) B95475671
theorem B2792495 : Blo 1470555 2792495 := bstep (se 1 (by rfl) ⟨2094371, by rfl⟩ : syracuseStep 2792495 = 4188743) B4188743
theorem B13417655 : Blo 1470555 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B4963571 : Blo 1470555 4963571 := bstep (se 1 (by rfl) ⟨3722678, by rfl⟩ : syracuseStep 4963571 = 7445357) B7445357
theorem B12573953 : Blo 1470555 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B12565955 : Blo 1470555 12565955 := bstep (se 1 (by rfl) ⟨9424466, by rfl⟩ : syracuseStep 12565955 = 18848933) B18848933
theorem B14138819 : Blo 1470555 14138819 := bstep (se 1 (by rfl) ⟨10604114, by rfl⟩ : syracuseStep 14138819 = 21208229) B21208229
theorem B2792951 : Blo 1470555 2792951 := bstep (se 1 (by rfl) ⟨2094713, by rfl⟩ : syracuseStep 2792951 = 4189427) B4189427
theorem B3309119 : Blo 1470555 3309119 := bstep (se 1 (by rfl) ⟨2481839, by rfl⟩ : syracuseStep 3309119 = 4963679) B4963679
theorem B2793179 : Blo 1470555 2793179 := bstep (se 1 (by rfl) ⟨2094884, by rfl⟩ : syracuseStep 2793179 = 4189769) B4189769
theorem B3309479 : Blo 1470555 3309479 := bstep (se 1 (by rfl) ⟨2482109, by rfl⟩ : syracuseStep 3309479 = 4964219) B4964219
theorem B7446653 : Blo 1470555 7446653 := bstep (se 3 (by rfl) ⟨1396247, by rfl⟩ : syracuseStep 7446653 = 2792495) B2792495
theorem B3309695 : Blo 1470555 3309695 := bstep (se 1 (by rfl) ⟨2482271, by rfl⟩ : syracuseStep 3309695 = 4964543) B4964543
theorem B94363937 : Blo 1470555 94363937 := bstep (se 2 (by rfl) ⟨35386476, by rfl⟩ : syracuseStep 94363937 = 70772953) B70772953
theorem B18858365 : Blo 1470555 18858365 := bstep (se 3 (by rfl) ⟨3535943, by rfl⟩ : syracuseStep 18858365 = 7071887) B7071887
theorem B40821677 : Blo 1470555 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B2794439 : Blo 1470555 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B2483291 : Blo 1470555 2483291 := bstep (se 1 (by rfl) ⟨1862468, by rfl⟩ : syracuseStep 2483291 = 3724937) B3724937
theorem B2483311 : Blo 1470555 2483311 := bstep (se 1 (by rfl) ⟨1862483, by rfl⟩ : syracuseStep 2483311 = 3724967) B3724967
theorem B7267439 : Blo 1470555 7267439 := bstep (se 1 (by rfl) ⟨5450579, by rfl⟩ : syracuseStep 7267439 = 10901159) B10901159
theorem B4965515 : Blo 1470555 4965515 := bstep (se 1 (by rfl) ⟨3724136, by rfl⟩ : syracuseStep 4965515 = 7448273) B7448273
theorem B5588135 : Blo 1470555 5588135 := bstep (se 1 (by rfl) ⟨4191101, by rfl⟩ : syracuseStep 5588135 = 8382203) B8382203
theorem B12567869 : Blo 1470555 12567869 := bstep (se 3 (by rfl) ⟨2356475, by rfl⟩ : syracuseStep 12567869 = 4712951) B4712951
theorem B3311351 : Blo 1470555 3311351 := bstep (se 1 (by rfl) ⟨2483513, by rfl⟩ : syracuseStep 3311351 = 4967027) B4967027
theorem B7956265 : Blo 1470555 7956265 := bstep (se 2 (by rfl) ⟨2983599, by rfl⟩ : syracuseStep 7956265 = 5967199) B5967199
theorem B3311531 : Blo 1470555 3311531 := bstep (se 1 (by rfl) ⟨2483648, by rfl⟩ : syracuseStep 3311531 = 4967297) B4967297
theorem B12568553 : Blo 1470555 12568553 := bstep (se 2 (by rfl) ⟨4713207, by rfl⟩ : syracuseStep 12568553 = 9426415) B9426415
theorem B11167793 : Blo 1470555 11167793 := bstep (se 2 (by rfl) ⟨4187922, by rfl⟩ : syracuseStep 11167793 = 8375845) B8375845
theorem B8382635 : Blo 1470555 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B1861967 : Blo 1470555 1861967 := bstep (se 1 (by rfl) ⟨1396475, by rfl⟩ : syracuseStep 1861967 = 2792951) B2792951
theorem B2206079 : Blo 1470555 2206079 := bstep (se 1 (by rfl) ⟨1654559, by rfl⟩ : syracuseStep 2206079 = 3309119) B3309119
theorem B3312071 : Blo 1470555 3312071 := bstep (se 1 (by rfl) ⟨2484053, by rfl⟩ : syracuseStep 3312071 = 4968107) B4968107
theorem B1862119 : Blo 1470555 1862119 := bstep (se 1 (by rfl) ⟨1396589, by rfl⟩ : syracuseStep 1862119 = 2793179) B2793179
theorem B2206319 : Blo 1470555 2206319 := bstep (se 1 (by rfl) ⟨1654739, by rfl⟩ : syracuseStep 2206319 = 3309479) B3309479
theorem B4967135 : Blo 1470555 4967135 := bstep (se 1 (by rfl) ⟨3725351, by rfl⟩ : syracuseStep 4967135 = 7450703) B7450703
theorem B3312431 : Blo 1470555 3312431 := bstep (se 1 (by rfl) ⟨2484323, by rfl⟩ : syracuseStep 3312431 = 4968647) B4968647
theorem B2206535 : Blo 1470555 2206535 := bstep (se 1 (by rfl) ⟨1654901, by rfl⟩ : syracuseStep 2206535 = 3309803) B3309803
theorem B4189153 : Blo 1470555 4189153 := bstep (se 2 (by rfl) ⟨1570932, by rfl⟩ : syracuseStep 4189153 = 3141865) B3141865
theorem B5590079 : Blo 1470555 5590079 := bstep (se 1 (by rfl) ⟨4192559, by rfl⟩ : syracuseStep 5590079 = 8385119) B8385119
theorem B1862767 : Blo 1470555 1862767 := bstep (se 1 (by rfl) ⟨1397075, by rfl⟩ : syracuseStep 1862767 = 2794151) B2794151
theorem B3312953 : Blo 1470555 3312953 := bstep (se 2 (by rfl) ⟨1242357, by rfl⟩ : syracuseStep 3312953 = 2484715) B2484715
theorem B10603909 : Blo 1470555 10603909 := bstep (se 4 (by rfl) ⟨994116, by rfl⟩ : syracuseStep 10603909 = 1988233) B1988233
theorem B7548299 : Blo 1470555 7548299 := bstep (se 1 (by rfl) ⟨5661224, by rfl⟩ : syracuseStep 7548299 = 11322449) B11322449
theorem B2207135 : Blo 1470555 2207135 := bstep (se 1 (by rfl) ⟨1655351, by rfl⟩ : syracuseStep 2207135 = 3310703) B3310703
theorem B18845243 : Blo 1470555 18845243 := bstep (se 1 (by rfl) ⟨14133932, by rfl⟩ : syracuseStep 18845243 = 28267865) B28267865
theorem B3313223 : Blo 1470555 3313223 := bstep (se 1 (by rfl) ⟨2484917, by rfl⟩ : syracuseStep 3313223 = 4969835) B4969835
theorem B26832545 : Blo 1470555 26832545 := bstep (se 2 (by rfl) ⟨10062204, by rfl⟩ : syracuseStep 26832545 = 20124409) B20124409
theorem B2207399 : Blo 1470555 2207399 := bstep (se 1 (by rfl) ⟨1655549, by rfl⟩ : syracuseStep 2207399 = 3311099) B3311099
theorem B2207423 : Blo 1470555 2207423 := bstep (se 1 (by rfl) ⟨1655567, by rfl⟩ : syracuseStep 2207423 = 3311135) B3311135
theorem B2207519 : Blo 1470555 2207519 := bstep (se 1 (by rfl) ⟨1655639, by rfl⟩ : syracuseStep 2207519 = 3311279) B3311279
theorem B32263991 : Blo 1470555 32263991 := bstep (se 1 (by rfl) ⟨24197993, by rfl⟩ : syracuseStep 32263991 = 48395987) B48395987
theorem B2387999 : Blo 1470555 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B2207807 : Blo 1470555 2207807 := bstep (se 1 (by rfl) ⟨1655855, by rfl⟩ : syracuseStep 2207807 = 3311711) B3311711
theorem B3723367 : Blo 1470555 3723367 := bstep (se 1 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 3723367 = 5585051) B5585051
theorem B4190383 : Blo 1470555 4190383 := bstep (se 1 (by rfl) ⟨3142787, by rfl⟩ : syracuseStep 4190383 = 6285575) B6285575
theorem B1470671 : Blo 1470555 1470671 := bstep (se 1 (by rfl) ⟨1103003, by rfl⟩ : syracuseStep 1470671 = 2206007) B2206007
theorem B2207999 : Blo 1470555 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B2208041 : Blo 1470555 2208041 := bstep (se 2 (by rfl) ⟨828015, by rfl⟩ : syracuseStep 2208041 = 1656031) B1656031
theorem B1470791 : Blo 1470555 1470791 := bstep (se 1 (by rfl) ⟨1103093, by rfl⟩ : syracuseStep 1470791 = 2206187) B2206187
theorem B3141985 : Blo 1470555 3141985 := bstep (se 2 (by rfl) ⟨1178244, by rfl⟩ : syracuseStep 3141985 = 2356489) B2356489
theorem B18854369 : Blo 1470555 18854369 := bstep (se 2 (by rfl) ⟨7070388, by rfl⟩ : syracuseStep 18854369 = 14140777) B14140777
theorem B2208311 : Blo 1470555 2208311 := bstep (se 1 (by rfl) ⟨1656233, by rfl⟩ : syracuseStep 2208311 = 3312467) B3312467
theorem B15905483 : Blo 1470555 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B1471259 : Blo 1470555 1471259 := bstep (se 1 (by rfl) ⟨1103444, by rfl⟩ : syracuseStep 1471259 = 2206889) B2206889
theorem B2208551 : Blo 1470555 2208551 := bstep (se 1 (by rfl) ⟨1656413, by rfl⟩ : syracuseStep 2208551 = 3312827) B3312827
theorem B31814495 : Blo 1470555 31814495 := bstep (se 1 (by rfl) ⟨23860871, by rfl⟩ : syracuseStep 31814495 = 47721743) B47721743
theorem B2208671 : Blo 1470555 2208671 := bstep (se 1 (by rfl) ⟨1656503, by rfl⟩ : syracuseStep 2208671 = 3313007) B3313007
theorem B8377303 : Blo 1470555 8377303 := bstep (se 1 (by rfl) ⟨6282977, by rfl⟩ : syracuseStep 8377303 = 12565955) B12565955
theorem B9425879 : Blo 1470555 9425879 := bstep (se 1 (by rfl) ⟨7069409, by rfl⟩ : syracuseStep 9425879 = 14138819) B14138819
theorem B8385551 : Blo 1470555 8385551 := bstep (se 1 (by rfl) ⟨6289163, by rfl⟩ : syracuseStep 8385551 = 12578327) B12578327
theorem B2356271 : Blo 1470555 2356271 := bstep (se 1 (by rfl) ⟨1767203, by rfl⟩ : syracuseStep 2356271 = 3534407) B3534407
theorem B1471535 : Blo 1470555 1471535 := bstep (se 1 (by rfl) ⟨1103651, by rfl⟩ : syracuseStep 1471535 = 2207303) B2207303
theorem B4715567 : Blo 1470555 4715567 := bstep (se 1 (by rfl) ⟨3536675, by rfl⟩ : syracuseStep 4715567 = 7073351) B7073351
theorem B1471655 : Blo 1470555 1471655 := bstep (se 1 (by rfl) ⟨1103741, by rfl⟩ : syracuseStep 1471655 = 2207483) B2207483
theorem B5584079 : Blo 1470555 5584079 := bstep (se 1 (by rfl) ⟨4188059, by rfl⟩ : syracuseStep 5584079 = 8376119) B8376119
theorem B3724775 : Blo 1470555 3724775 := bstep (se 1 (by rfl) ⟨2793581, by rfl⟩ : syracuseStep 3724775 = 5587163) B5587163
theorem B1472103 : Blo 1470555 1472103 := bstep (se 1 (by rfl) ⟨1104077, by rfl⟩ : syracuseStep 1472103 = 2208155) B2208155
theorem B4191887 : Blo 1470555 4191887 := bstep (se 1 (by rfl) ⟨3143915, by rfl⟩ : syracuseStep 4191887 = 6287831) B6287831
theorem B35780413 : Blo 1470555 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B1472383 : Blo 1470555 1472383 := bstep (se 1 (by rfl) ⟨1104287, by rfl⟩ : syracuseStep 1472383 = 2208575) B2208575
theorem B1472479 : Blo 1470555 1472479 := bstep (se 1 (by rfl) ⟨1104359, by rfl⟩ : syracuseStep 1472479 = 2208719) B2208719
theorem B7452647 : Blo 1470555 7452647 := bstep (se 1 (by rfl) ⟨5589485, by rfl⟩ : syracuseStep 7452647 = 11178971) B11178971
theorem B1472507 : Blo 1470555 1472507 := bstep (se 1 (by rfl) ⟨1104380, by rfl⟩ : syracuseStep 1472507 = 2208761) B2208761
theorem B1570843 : Blo 1470555 1570843 := bstep (se 1 (by rfl) ⟨1178132, by rfl⟩ : syracuseStep 1570843 = 2356265) B2356265
theorem B1472539 : Blo 1470555 1472539 := bstep (se 1 (by rfl) ⟨1104404, by rfl⟩ : syracuseStep 1472539 = 2208809) B2208809
theorem B7452809 : Blo 1470555 7452809 := bstep (se 2 (by rfl) ⟨2794803, by rfl⟩ : syracuseStep 7452809 = 5589607) B5589607
theorem B76437701 : Blo 1470555 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B235518167 : Blo 1470555 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B2791759 : Blo 1470555 2791759 := bstep (se 1 (by rfl) ⟨2093819, by rfl⟩ : syracuseStep 2791759 = 4187639) B4187639
theorem B2792063 : Blo 1470555 2792063 := bstep (se 1 (by rfl) ⟨2094047, by rfl⟩ : syracuseStep 2792063 = 4188095) B4188095
theorem B2792161 : Blo 1470555 2792161 := bstep (se 2 (by rfl) ⟨1047060, by rfl⟩ : syracuseStep 2792161 = 2094121) B2094121
theorem B7953497 : Blo 1470555 7953497 := bstep (se 2 (by rfl) ⟨2982561, by rfl⟩ : syracuseStep 7953497 = 5965123) B5965123
theorem B42433631 : Blo 1470555 42433631 := bstep (se 1 (by rfl) ⟨31825223, by rfl⟩ : syracuseStep 42433631 = 63650447) B63650447
theorem B3726587 : Blo 1470555 3726587 := bstep (se 1 (by rfl) ⟨2794940, by rfl⟩ : syracuseStep 3726587 = 5589881) B5589881
theorem B3309047 : Blo 1470555 3309047 := bstep (se 1 (by rfl) ⟨2481785, by rfl⟩ : syracuseStep 3309047 = 4963571) B4963571
theorem B31842173 : Blo 1470555 31842173 := bstep (se 3 (by rfl) ⟨5970407, by rfl⟩ : syracuseStep 31842173 = 11940815) B11940815
theorem B145219483 : Blo 1470555 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B2793467 : Blo 1470555 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B4964435 : Blo 1470555 4964435 := bstep (se 1 (by rfl) ⟨3723326, by rfl⟩ : syracuseStep 4964435 = 7446653) B7446653
theorem B4964489 : Blo 1470555 4964489 := bstep (se 2 (by rfl) ⟨1861683, by rfl⟩ : syracuseStep 4964489 = 3723367) B3723367
theorem B5587177 : Blo 1470555 5587177 := bstep (se 2 (by rfl) ⟨2095191, by rfl⟩ : syracuseStep 5587177 = 4190383) B4190383
theorem B21209663 : Blo 1470555 21209663 := bstep (se 1 (by rfl) ⟨15907247, by rfl⟩ : syracuseStep 21209663 = 31814495) B31814495
theorem B27214451 : Blo 1470555 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B2482825 : Blo 1470555 2482825 := bstep (se 2 (by rfl) ⟨931059, by rfl⟩ : syracuseStep 2482825 = 1862119) B1862119
theorem B6283919 : Blo 1470555 6283919 := bstep (se 1 (by rfl) ⟨4712939, by rfl⟩ : syracuseStep 6283919 = 9425879) B9425879
theorem B1655527 : Blo 1470555 1655527 := bstep (se 1 (by rfl) ⟨1241645, by rfl⟩ : syracuseStep 1655527 = 2483291) B2483291
theorem B3310343 : Blo 1470555 3310343 := bstep (se 1 (by rfl) ⟨2482757, by rfl⟩ : syracuseStep 3310343 = 4965515) B4965515
theorem B4965245 : Blo 1470555 4965245 := bstep (se 3 (by rfl) ⟨930983, by rfl⟩ : syracuseStep 4965245 = 1861967) B1861967
theorem B2483183 : Blo 1470555 2483183 := bstep (se 1 (by rfl) ⟨1862387, by rfl⟩ : syracuseStep 2483183 = 3724775) B3724775
theorem B2794591 : Blo 1470555 2794591 := bstep (se 1 (by rfl) ⟨2095943, by rfl⟩ : syracuseStep 2794591 = 4191887) B4191887
theorem B5588423 : Blo 1470555 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B3311081 : Blo 1470555 3311081 := bstep (se 2 (by rfl) ⟨1241655, by rfl⟩ : syracuseStep 3311081 = 2483311) B2483311
theorem B2483689 : Blo 1470555 2483689 := bstep (se 2 (by rfl) ⟨931383, by rfl⟩ : syracuseStep 2483689 = 1862767) B1862767
theorem B1861375 : Blo 1470555 1861375 := bstep (se 1 (by rfl) ⟨1396031, by rfl⟩ : syracuseStep 1861375 = 2792063) B2792063
theorem B3311423 : Blo 1470555 3311423 := bstep (se 1 (by rfl) ⟨2483567, by rfl⟩ : syracuseStep 3311423 = 4967135) B4967135
theorem B5302331 : Blo 1470555 5302331 := bstep (se 1 (by rfl) ⟨3976748, by rfl⟩ : syracuseStep 5302331 = 7953497) B7953497
theorem B28289087 : Blo 1470555 28289087 := bstep (se 1 (by rfl) ⟨21216815, by rfl⟩ : syracuseStep 28289087 = 42433631) B42433631
theorem B2484391 : Blo 1470555 2484391 := bstep (se 1 (by rfl) ⟨1863293, by rfl⟩ : syracuseStep 2484391 = 3726587) B3726587
theorem B5032199 : Blo 1470555 5032199 := bstep (se 1 (by rfl) ⟨3774149, by rfl⟩ : syracuseStep 5032199 = 7548299) B7548299
theorem B84912461 : Blo 1470555 84912461 := bstep (se 3 (by rfl) ⟨15921086, by rfl⟩ : syracuseStep 84912461 = 31842173) B31842173
theorem B2206031 : Blo 1470555 2206031 := bstep (se 1 (by rfl) ⟨1654523, by rfl⟩ : syracuseStep 2206031 = 3309047) B3309047
theorem B7449245 : Blo 1470555 7449245 := bstep (se 3 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 7449245 = 2793467) B2793467
theorem B6367997 : Blo 1470555 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B2206463 : Blo 1470555 2206463 := bstep (se 1 (by rfl) ⟨1654847, by rfl⟩ : syracuseStep 2206463 = 3309695) B3309695
theorem B62909291 : Blo 1470555 62909291 := bstep (se 1 (by rfl) ⟨47181968, by rfl⟩ : syracuseStep 62909291 = 94363937) B94363937
theorem B12569579 : Blo 1470555 12569579 := bstep (se 1 (by rfl) ⟨9427184, by rfl⟩ : syracuseStep 12569579 = 18854369) B18854369
theorem B3722345 : Blo 1470555 3722345 := bstep (se 2 (by rfl) ⟨1395879, by rfl⟩ : syracuseStep 3722345 = 2791759) B2791759
theorem B4189313 : Blo 1470555 4189313 := bstep (se 2 (by rfl) ⟨1570992, by rfl⟩ : syracuseStep 4189313 = 3141985) B3141985
theorem B10603655 : Blo 1470555 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B5590367 : Blo 1470555 5590367 := bstep (se 1 (by rfl) ⟨4192775, by rfl⟩ : syracuseStep 5590367 = 8385551) B8385551
theorem B3722719 : Blo 1470555 3722719 := bstep (se 1 (by rfl) ⟨2792039, by rfl⟩ : syracuseStep 3722719 = 5584079) B5584079
theorem B3722881 : Blo 1470555 3722881 := bstep (se 2 (by rfl) ⟨1396080, by rfl⟩ : syracuseStep 3722881 = 2792161) B2792161
theorem B2207567 : Blo 1470555 2207567 := bstep (se 1 (by rfl) ⟨1655675, by rfl⟩ : syracuseStep 2207567 = 3311351) B3311351
theorem B2207687 : Blo 1470555 2207687 := bstep (se 1 (by rfl) ⟨1655765, by rfl⟩ : syracuseStep 2207687 = 3311531) B3311531
theorem B11169737 : Blo 1470555 11169737 := bstep (se 2 (by rfl) ⟨4188651, by rfl⟩ : syracuseStep 11169737 = 8377303) B8377303
theorem B4968431 : Blo 1470555 4968431 := bstep (se 1 (by rfl) ⟨3726323, by rfl⟩ : syracuseStep 4968431 = 7452647) B7452647
theorem B4968539 : Blo 1470555 4968539 := bstep (se 1 (by rfl) ⟨3726404, by rfl⟩ : syracuseStep 4968539 = 7452809) B7452809
theorem B50958467 : Blo 1470555 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B157012111 : Blo 1470555 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B1470719 : Blo 1470555 1470719 := bstep (se 1 (by rfl) ⟨1103039, by rfl⟩ : syracuseStep 1470719 = 2206079) B2206079
theorem B2208047 : Blo 1470555 2208047 := bstep (se 1 (by rfl) ⟨1656035, by rfl⟩ : syracuseStep 2208047 = 3312071) B3312071
theorem B1470879 : Blo 1470555 1470879 := bstep (se 1 (by rfl) ⟨1103159, by rfl⟩ : syracuseStep 1470879 = 2206319) B2206319
theorem B2208287 : Blo 1470555 2208287 := bstep (se 1 (by rfl) ⟨1656215, by rfl⟩ : syracuseStep 2208287 = 3312431) B3312431
theorem B1471023 : Blo 1470555 1471023 := bstep (se 1 (by rfl) ⟨1103267, by rfl⟩ : syracuseStep 1471023 = 2206535) B2206535
theorem B2208635 : Blo 1470555 2208635 := bstep (se 1 (by rfl) ⟨1656476, by rfl⟩ : syracuseStep 2208635 = 3312953) B3312953
theorem B1471423 : Blo 1470555 1471423 := bstep (se 1 (by rfl) ⟨1103567, by rfl⟩ : syracuseStep 1471423 = 2207135) B2207135
theorem B12563495 : Blo 1470555 12563495 := bstep (se 1 (by rfl) ⟨9422621, by rfl⟩ : syracuseStep 12563495 = 18845243) B18845243
theorem B2208815 : Blo 1470555 2208815 := bstep (se 1 (by rfl) ⟨1656611, by rfl⟩ : syracuseStep 2208815 = 3313223) B3313223
theorem B47707217 : Blo 1470555 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B17888363 : Blo 1470555 17888363 := bstep (se 1 (by rfl) ⟨13416272, by rfl⟩ : syracuseStep 17888363 = 26832545) B26832545
theorem B1471599 : Blo 1470555 1471599 := bstep (se 1 (by rfl) ⟨1103699, by rfl⟩ : syracuseStep 1471599 = 2207399) B2207399
theorem B1471615 : Blo 1470555 1471615 := bstep (se 1 (by rfl) ⟨1103711, by rfl⟩ : syracuseStep 1471615 = 2207423) B2207423
theorem B7451837 : Blo 1470555 7451837 := bstep (se 3 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 7451837 = 2794439) B2794439
theorem B1471679 : Blo 1470555 1471679 := bstep (se 1 (by rfl) ⟨1103759, by rfl⟩ : syracuseStep 1471679 = 2207519) B2207519
theorem B21509327 : Blo 1470555 21509327 := bstep (se 1 (by rfl) ⟨16131995, by rfl⟩ : syracuseStep 21509327 = 32263991) B32263991
theorem B1471871 : Blo 1470555 1471871 := bstep (se 1 (by rfl) ⟨1103903, by rfl⟩ : syracuseStep 1471871 = 2207807) B2207807
theorem B8377829 : Blo 1470555 8377829 := bstep (se 4 (by rfl) ⟨785421, by rfl⟩ : syracuseStep 8377829 = 1570843) B1570843
theorem B1471999 : Blo 1470555 1471999 := bstep (se 1 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 1471999 = 2207999) B2207999
theorem B1472027 : Blo 1470555 1472027 := bstep (se 1 (by rfl) ⟨1104020, by rfl⟩ : syracuseStep 1472027 = 2208041) B2208041
theorem B12572243 : Blo 1470555 12572243 := bstep (se 1 (by rfl) ⟨9429182, by rfl⟩ : syracuseStep 12572243 = 18858365) B18858365
theorem B19379837 : Blo 1470555 19379837 := bstep (se 3 (by rfl) ⟨3633719, by rfl⟩ : syracuseStep 19379837 = 7267439) B7267439
theorem B1472207 : Blo 1470555 1472207 := bstep (se 1 (by rfl) ⟨1104155, by rfl⟩ : syracuseStep 1472207 = 2208311) B2208311
theorem B1472367 : Blo 1470555 1472367 := bstep (se 1 (by rfl) ⟨1104275, by rfl⟩ : syracuseStep 1472367 = 2208551) B2208551
theorem B1472447 : Blo 1470555 1472447 := bstep (se 1 (by rfl) ⟨1104335, by rfl⟩ : syracuseStep 1472447 = 2208671) B2208671
theorem B1570847 : Blo 1470555 1570847 := bstep (se 1 (by rfl) ⟨1178135, by rfl⟩ : syracuseStep 1570847 = 2356271) B2356271
theorem B3143711 : Blo 1470555 3143711 := bstep (se 1 (by rfl) ⟨2357783, by rfl⟩ : syracuseStep 3143711 = 4715567) B4715567
theorem B3725423 : Blo 1470555 3725423 := bstep (se 1 (by rfl) ⟨2794067, by rfl⟩ : syracuseStep 3725423 = 5588135) B5588135
theorem B8378579 : Blo 1470555 8378579 := bstep (se 1 (by rfl) ⟨6283934, by rfl⟩ : syracuseStep 8378579 = 12567869) B12567869
theorem B5585537 : Blo 1470555 5585537 := bstep (se 2 (by rfl) ⟨2094576, by rfl⟩ : syracuseStep 5585537 = 4189153) B4189153
theorem B8379035 : Blo 1470555 8379035 := bstep (se 1 (by rfl) ⟨6284276, by rfl⟩ : syracuseStep 8379035 = 12568553) B12568553
theorem B7445195 : Blo 1470555 7445195 := bstep (se 1 (by rfl) ⟨5583896, by rfl⟩ : syracuseStep 7445195 = 11167793) B11167793
theorem B14138545 : Blo 1470555 14138545 := bstep (se 2 (by rfl) ⟨5301954, by rfl⟩ : syracuseStep 14138545 = 10603909) B10603909
theorem B3726719 : Blo 1470555 3726719 := bstep (se 1 (by rfl) ⟨2795039, by rfl⟩ : syracuseStep 3726719 = 5590079) B5590079
theorem B10608353 : Blo 1470555 10608353 := bstep (se 2 (by rfl) ⟨3978132, by rfl⟩ : syracuseStep 10608353 = 7956265) B7956265
theorem B193625977 : Blo 1470555 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B3309623 : Blo 1470555 3309623 := bstep (se 1 (by rfl) ⟨2482217, by rfl⟩ : syracuseStep 3309623 = 4964435) B4964435
theorem B33972311 : Blo 1470555 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B3309659 : Blo 1470555 3309659 := bstep (se 1 (by rfl) ⟨2482244, by rfl⟩ : syracuseStep 3309659 = 4964489) B4964489
theorem B14139775 : Blo 1470555 14139775 := bstep (se 1 (by rfl) ⟨10604831, by rfl⟩ : syracuseStep 14139775 = 21209663) B21209663
theorem B3310163 : Blo 1470555 3310163 := bstep (se 1 (by rfl) ⟨2482622, by rfl⟩ : syracuseStep 3310163 = 4965245) B4965245
theorem B1655455 : Blo 1470555 1655455 := bstep (se 1 (by rfl) ⟨1241591, by rfl⟩ : syracuseStep 1655455 = 2483183) B2483183
theorem B3310433 : Blo 1470555 3310433 := bstep (se 2 (by rfl) ⟨1241412, by rfl⟩ : syracuseStep 3310433 = 2482825) B2482825
theorem B8381495 : Blo 1470555 8381495 := bstep (se 1 (by rfl) ⟨6286121, by rfl⟩ : syracuseStep 8381495 = 12572243) B12572243
theorem B12919891 : Blo 1470555 12919891 := bstep (se 1 (by rfl) ⟨9689918, by rfl⟩ : syracuseStep 12919891 = 19379837) B19379837
theorem B18859391 : Blo 1470555 18859391 := bstep (se 1 (by rfl) ⟨14144543, by rfl⟩ : syracuseStep 18859391 = 28289087) B28289087
theorem B2483615 : Blo 1470555 2483615 := bstep (se 1 (by rfl) ⟨1862711, by rfl⟩ : syracuseStep 2483615 = 3725423) B3725423
theorem B56608307 : Blo 1470555 56608307 := bstep (se 1 (by rfl) ⟨42456230, by rfl⟩ : syracuseStep 56608307 = 84912461) B84912461
theorem B18851393 : Blo 1470555 18851393 := bstep (se 2 (by rfl) ⟨7069272, by rfl⟩ : syracuseStep 18851393 = 14138545) B14138545
theorem B4966163 : Blo 1470555 4966163 := bstep (se 1 (by rfl) ⟨3724622, by rfl⟩ : syracuseStep 4966163 = 7449245) B7449245
theorem B3311585 : Blo 1470555 3311585 := bstep (se 2 (by rfl) ⟨1241844, by rfl⟩ : syracuseStep 3311585 = 2483689) B2483689
theorem B2484479 : Blo 1470555 2484479 := bstep (se 1 (by rfl) ⟨1863359, by rfl⟩ : syracuseStep 2484479 = 3726719) B3726719
theorem B7072235 : Blo 1470555 7072235 := bstep (se 1 (by rfl) ⟨5304176, by rfl⟩ : syracuseStep 7072235 = 10608353) B10608353
theorem B3312287 : Blo 1470555 3312287 := bstep (se 1 (by rfl) ⟨2484215, by rfl⟩ : syracuseStep 3312287 = 4968431) B4968431
theorem B3312359 : Blo 1470555 3312359 := bstep (se 1 (by rfl) ⟨2484269, by rfl⟩ : syracuseStep 3312359 = 4968539) B4968539
theorem B4188925 : Blo 1470555 4188925 := bstep (se 3 (by rfl) ⟨785423, by rfl⟩ : syracuseStep 4188925 = 1570847) B1570847
theorem B3312521 : Blo 1470555 3312521 := bstep (se 2 (by rfl) ⟨1242195, by rfl⟩ : syracuseStep 3312521 = 2484391) B2484391
theorem B7449569 : Blo 1470555 7449569 := bstep (se 2 (by rfl) ⟨2793588, by rfl⟩ : syracuseStep 7449569 = 5587177) B5587177
theorem B4189279 : Blo 1470555 4189279 := bstep (se 1 (by rfl) ⟨3141959, by rfl⟩ : syracuseStep 4189279 = 6283919) B6283919
theorem B2206895 : Blo 1470555 2206895 := bstep (se 1 (by rfl) ⟨1655171, by rfl⟩ : syracuseStep 2206895 = 3310343) B3310343
theorem B8375663 : Blo 1470555 8375663 := bstep (se 1 (by rfl) ⟨6281747, by rfl⟩ : syracuseStep 8375663 = 12563495) B12563495
theorem B31804811 : Blo 1470555 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B837397925 : Blo 1470555 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B4967891 : Blo 1470555 4967891 := bstep (se 1 (by rfl) ⟨3725918, by rfl⟩ : syracuseStep 4967891 = 7451837) B7451837
theorem B14339551 : Blo 1470555 14339551 := bstep (se 1 (by rfl) ⟨10754663, by rfl⟩ : syracuseStep 14339551 = 21509327) B21509327
theorem B2207369 : Blo 1470555 2207369 := bstep (se 2 (by rfl) ⟨827763, by rfl⟩ : syracuseStep 2207369 = 1655527) B1655527
theorem B2207387 : Blo 1470555 2207387 := bstep (se 1 (by rfl) ⟨1655540, by rfl⟩ : syracuseStep 2207387 = 3311081) B3311081
theorem B2207615 : Blo 1470555 2207615 := bstep (se 1 (by rfl) ⟨1655711, by rfl⟩ : syracuseStep 2207615 = 3311423) B3311423
theorem B3534887 : Blo 1470555 3534887 := bstep (se 1 (by rfl) ⟨2651165, by rfl⟩ : syracuseStep 3534887 = 5302331) B5302331
theorem B3354799 : Blo 1470555 3354799 := bstep (se 1 (by rfl) ⟨2516099, by rfl⟩ : syracuseStep 3354799 = 5032199) B5032199
theorem B1470687 : Blo 1470555 1470687 := bstep (se 1 (by rfl) ⟨1103015, by rfl⟩ : syracuseStep 1470687 = 2206031) B2206031
theorem B3723691 : Blo 1470555 3723691 := bstep (se 1 (by rfl) ⟨2792768, by rfl⟩ : syracuseStep 3723691 = 5585537) B5585537
theorem B1470975 : Blo 1470555 1470975 := bstep (se 1 (by rfl) ⟨1103231, by rfl⟩ : syracuseStep 1470975 = 2206463) B2206463
theorem B41939527 : Blo 1470555 41939527 := bstep (se 1 (by rfl) ⟨31454645, by rfl⟩ : syracuseStep 41939527 = 62909291) B62909291
theorem B258167969 : Blo 1470555 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B1471711 : Blo 1470555 1471711 := bstep (se 1 (by rfl) ⟨1103783, by rfl⟩ : syracuseStep 1471711 = 2207567) B2207567
theorem B1471791 : Blo 1470555 1471791 := bstep (se 1 (by rfl) ⟨1103843, by rfl⟩ : syracuseStep 1471791 = 2207687) B2207687
theorem B1472031 : Blo 1470555 1472031 := bstep (se 1 (by rfl) ⟨1104023, by rfl⟩ : syracuseStep 1472031 = 2208047) B2208047
theorem B1472191 : Blo 1470555 1472191 := bstep (se 1 (by rfl) ⟨1104143, by rfl⟩ : syracuseStep 1472191 = 2208287) B2208287
theorem B18142967 : Blo 1470555 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1472423 : Blo 1470555 1472423 := bstep (se 1 (by rfl) ⟨1104317, by rfl⟩ : syracuseStep 1472423 = 2208635) B2208635
theorem B1472543 : Blo 1470555 1472543 := bstep (se 1 (by rfl) ⟨1104407, by rfl⟩ : syracuseStep 1472543 = 2208815) B2208815
theorem B11925575 : Blo 1470555 11925575 := bstep (se 1 (by rfl) ⟨8944181, by rfl⟩ : syracuseStep 11925575 = 17888363) B17888363
theorem B3725615 : Blo 1470555 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B5585219 : Blo 1470555 5585219 := bstep (se 1 (by rfl) ⟨4188914, by rfl⟩ : syracuseStep 5585219 = 8377829) B8377829
theorem B2095807 : Blo 1470555 2095807 := bstep (se 1 (by rfl) ⟨1571855, by rfl⟩ : syracuseStep 2095807 = 3143711) B3143711
theorem B3726121 : Blo 1470555 3726121 := bstep (se 2 (by rfl) ⟨1397295, by rfl⟩ : syracuseStep 3726121 = 2794591) B2794591
theorem B5585719 : Blo 1470555 5585719 := bstep (se 1 (by rfl) ⟨4189289, by rfl⟩ : syracuseStep 5585719 = 8378579) B8378579
theorem B5586023 : Blo 1470555 5586023 := bstep (se 1 (by rfl) ⟨4189517, by rfl⟩ : syracuseStep 5586023 = 8379035) B8379035
theorem B4963463 : Blo 1470555 4963463 := bstep (se 1 (by rfl) ⟨3722597, by rfl⟩ : syracuseStep 4963463 = 7445195) B7445195
theorem B4963625 : Blo 1470555 4963625 := bstep (se 2 (by rfl) ⟨1861359, by rfl⟩ : syracuseStep 4963625 = 3722719) B3722719
theorem B8379719 : Blo 1470555 8379719 := bstep (se 1 (by rfl) ⟨6284789, by rfl⟩ : syracuseStep 8379719 = 12569579) B12569579
theorem B16981325 : Blo 1470555 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B2481563 : Blo 1470555 2481563 := bstep (se 1 (by rfl) ⟨1861172, by rfl⟩ : syracuseStep 2481563 = 3722345) B3722345
theorem B2792875 : Blo 1470555 2792875 := bstep (se 1 (by rfl) ⟨2094656, by rfl⟩ : syracuseStep 2792875 = 4189313) B4189313
theorem B7069103 : Blo 1470555 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B4963841 : Blo 1470555 4963841 := bstep (se 2 (by rfl) ⟨1861440, by rfl⟩ : syracuseStep 4963841 = 3722881) B3722881
theorem B3726911 : Blo 1470555 3726911 := bstep (se 1 (by rfl) ⟨2795183, by rfl⟩ : syracuseStep 3726911 = 5590367) B5590367
theorem B2481833 : Blo 1470555 2481833 := bstep (se 2 (by rfl) ⟨930687, by rfl⟩ : syracuseStep 2481833 = 1861375) B1861375
theorem B7446491 : Blo 1470555 7446491 := bstep (se 1 (by rfl) ⟨5584868, by rfl⟩ : syracuseStep 7446491 = 11169737) B11169737
theorem B4473065 : Blo 1470555 4473065 := bstep (se 2 (by rfl) ⟨1677399, by rfl⟩ : syracuseStep 4473065 = 3354799) B3354799
theorem B4964921 : Blo 1470555 4964921 := bstep (se 2 (by rfl) ⟨1861845, by rfl⟩ : syracuseStep 4964921 = 3723691) B3723691
theorem B5587663 : Blo 1470555 5587663 := bstep (se 1 (by rfl) ⟨4190747, by rfl⟩ : syracuseStep 5587663 = 8381495) B8381495
theorem B55919369 : Blo 1470555 55919369 := bstep (se 2 (by rfl) ⟨20969763, by rfl⟩ : syracuseStep 55919369 = 41939527) B41939527
theorem B2794409 : Blo 1470555 2794409 := bstep (se 2 (by rfl) ⟨1047903, by rfl⟩ : syracuseStep 2794409 = 2095807) B2095807
theorem B1655743 : Blo 1470555 1655743 := bstep (se 1 (by rfl) ⟨1241807, by rfl⟩ : syracuseStep 1655743 = 2483615) B2483615
theorem B12567595 : Blo 1470555 12567595 := bstep (se 1 (by rfl) ⟨9425696, by rfl⟩ : syracuseStep 12567595 = 18851393) B18851393
theorem B7447625 : Blo 1470555 7447625 := bstep (se 2 (by rfl) ⟨2792859, by rfl⟩ : syracuseStep 7447625 = 5585719) B5585719
theorem B3310775 : Blo 1470555 3310775 := bstep (se 1 (by rfl) ⟨2483081, by rfl⟩ : syracuseStep 3310775 = 4966163) B4966163
theorem B1656319 : Blo 1470555 1656319 := bstep (se 1 (by rfl) ⟨1242239, by rfl⟩ : syracuseStep 1656319 = 2484479) B2484479
theorem B2483743 : Blo 1470555 2483743 := bstep (se 1 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 2483743 = 3725615) B3725615
theorem B4966379 : Blo 1470555 4966379 := bstep (se 1 (by rfl) ⟨3724784, by rfl⟩ : syracuseStep 4966379 = 7449569) B7449569
theorem B21203207 : Blo 1470555 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B4712735 : Blo 1470555 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B3311927 : Blo 1470555 3311927 := bstep (se 1 (by rfl) ⟨2483945, by rfl⟩ : syracuseStep 3311927 = 4967891) B4967891
theorem B2484607 : Blo 1470555 2484607 := bstep (se 1 (by rfl) ⟨1863455, by rfl⟩ : syracuseStep 2484607 = 3726911) B3726911
theorem B2206415 : Blo 1470555 2206415 := bstep (se 1 (by rfl) ⟨1654811, by rfl⟩ : syracuseStep 2206415 = 3309623) B3309623
theorem B2206439 : Blo 1470555 2206439 := bstep (se 1 (by rfl) ⟨1654829, by rfl⟩ : syracuseStep 2206439 = 3309659) B3309659
theorem B2206775 : Blo 1470555 2206775 := bstep (se 1 (by rfl) ⟨1655081, by rfl⟩ : syracuseStep 2206775 = 3310163) B3310163
theorem B18853033 : Blo 1470555 18853033 := bstep (se 2 (by rfl) ⟨7069887, by rfl⟩ : syracuseStep 18853033 = 14139775) B14139775
theorem B2206955 : Blo 1470555 2206955 := bstep (se 1 (by rfl) ⟨1655216, by rfl⟩ : syracuseStep 2206955 = 3310433) B3310433
theorem B2207273 : Blo 1470555 2207273 := bstep (se 2 (by rfl) ⟨827727, by rfl⟩ : syracuseStep 2207273 = 1655455) B1655455
theorem B4968161 : Blo 1470555 4968161 := bstep (se 2 (by rfl) ⟨1863060, by rfl⟩ : syracuseStep 4968161 = 3726121) B3726121
theorem B2207723 : Blo 1470555 2207723 := bstep (se 1 (by rfl) ⟨1655792, by rfl⟩ : syracuseStep 2207723 = 3311585) B3311585
theorem B7950383 : Blo 1470555 7950383 := bstep (se 1 (by rfl) ⟨5962787, by rfl⟩ : syracuseStep 7950383 = 11925575) B11925575
theorem B3723479 : Blo 1470555 3723479 := bstep (se 1 (by rfl) ⟨2792609, by rfl⟩ : syracuseStep 3723479 = 5585219) B5585219
theorem B4714823 : Blo 1470555 4714823 := bstep (se 1 (by rfl) ⟨3536117, by rfl⟩ : syracuseStep 4714823 = 7072235) B7072235
theorem B2208191 : Blo 1470555 2208191 := bstep (se 1 (by rfl) ⟨1656143, by rfl⟩ : syracuseStep 2208191 = 3312287) B3312287
theorem B2208239 : Blo 1470555 2208239 := bstep (se 1 (by rfl) ⟨1656179, by rfl⟩ : syracuseStep 2208239 = 3312359) B3312359
theorem B3723833 : Blo 1470555 3723833 := bstep (se 2 (by rfl) ⟨1396437, by rfl⟩ : syracuseStep 3723833 = 2792875) B2792875
theorem B2208347 : Blo 1470555 2208347 := bstep (se 1 (by rfl) ⟨1656260, by rfl⟩ : syracuseStep 2208347 = 3312521) B3312521
theorem B3724015 : Blo 1470555 3724015 := bstep (se 1 (by rfl) ⟨2793011, by rfl⟩ : syracuseStep 3724015 = 5586023) B5586023
theorem B1471263 : Blo 1470555 1471263 := bstep (se 1 (by rfl) ⟨1103447, by rfl⟩ : syracuseStep 1471263 = 2206895) B2206895
theorem B5583775 : Blo 1470555 5583775 := bstep (se 1 (by rfl) ⟨4187831, by rfl⟩ : syracuseStep 5583775 = 8375663) B8375663
theorem B558265283 : Blo 1470555 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B1471579 : Blo 1470555 1471579 := bstep (se 1 (by rfl) ⟨1103684, by rfl⟩ : syracuseStep 1471579 = 2207369) B2207369
theorem B1471591 : Blo 1470555 1471591 := bstep (se 1 (by rfl) ⟨1103693, by rfl⟩ : syracuseStep 1471591 = 2207387) B2207387
theorem B1471743 : Blo 1470555 1471743 := bstep (se 1 (by rfl) ⟨1103807, by rfl⟩ : syracuseStep 1471743 = 2207615) B2207615
theorem B22648207 : Blo 1470555 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B9426365 : Blo 1470555 9426365 := bstep (se 3 (by rfl) ⟨1767443, by rfl⟩ : syracuseStep 9426365 = 3534887) B3534887
theorem B172111979 : Blo 1470555 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B12572927 : Blo 1470555 12572927 := bstep (se 1 (by rfl) ⟨9429695, by rfl⟩ : syracuseStep 12572927 = 18859391) B18859391
theorem B5585233 : Blo 1470555 5585233 := bstep (se 2 (by rfl) ⟨2094462, by rfl⟩ : syracuseStep 5585233 = 4188925) B4188925
theorem B37738871 : Blo 1470555 37738871 := bstep (se 1 (by rfl) ⟨28304153, by rfl⟩ : syracuseStep 37738871 = 56608307) B56608307
theorem B17226521 : Blo 1470555 17226521 := bstep (se 2 (by rfl) ⟨6459945, by rfl⟩ : syracuseStep 17226521 = 12919891) B12919891
theorem B5585705 : Blo 1470555 5585705 := bstep (se 2 (by rfl) ⟨2094639, by rfl⟩ : syracuseStep 5585705 = 4189279) B4189279
theorem B19119401 : Blo 1470555 19119401 := bstep (se 2 (by rfl) ⟨7169775, by rfl⟩ : syracuseStep 19119401 = 14339551) B14339551
theorem B48381245 : Blo 1470555 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B3308975 : Blo 1470555 3308975 := bstep (se 1 (by rfl) ⟨2481731, by rfl⟩ : syracuseStep 3308975 = 4963463) B4963463
theorem B3309083 : Blo 1470555 3309083 := bstep (se 1 (by rfl) ⟨2481812, by rfl⟩ : syracuseStep 3309083 = 4963625) B4963625
theorem B5586479 : Blo 1470555 5586479 := bstep (se 1 (by rfl) ⟨4189859, by rfl⟩ : syracuseStep 5586479 = 8379719) B8379719
theorem B11320883 : Blo 1470555 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B1654375 : Blo 1470555 1654375 := bstep (se 1 (by rfl) ⟨1240781, by rfl⟩ : syracuseStep 1654375 = 2481563) B2481563
theorem B3309227 : Blo 1470555 3309227 := bstep (se 1 (by rfl) ⟨2481920, by rfl⟩ : syracuseStep 3309227 = 4963841) B4963841
theorem B1654555 : Blo 1470555 1654555 := bstep (se 1 (by rfl) ⟨1240916, by rfl⟩ : syracuseStep 1654555 = 2481833) B2481833
theorem B4964327 : Blo 1470555 4964327 := bstep (se 1 (by rfl) ⟨3723245, by rfl⟩ : syracuseStep 4964327 = 7446491) B7446491
theorem B5300255 : Blo 1470555 5300255 := bstep (se 1 (by rfl) ⟨3975191, by rfl⟩ : syracuseStep 5300255 = 7950383) B7950383
theorem B2482319 : Blo 1470555 2482319 := bstep (se 1 (by rfl) ⟨1861739, by rfl⟩ : syracuseStep 2482319 = 3723479) B3723479
theorem B2982043 : Blo 1470555 2982043 := bstep (se 1 (by rfl) ⟨2236532, by rfl⟩ : syracuseStep 2982043 = 4473065) B4473065
theorem B458965277 : Blo 1470555 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B3309947 : Blo 1470555 3309947 := bstep (se 1 (by rfl) ⟨2482460, by rfl⟩ : syracuseStep 3309947 = 4964921) B4964921
theorem B2482555 : Blo 1470555 2482555 := bstep (se 1 (by rfl) ⟨1861916, by rfl⟩ : syracuseStep 2482555 = 3723833) B3723833
theorem B7446977 : Blo 1470555 7446977 := bstep (se 2 (by rfl) ⟨2792616, by rfl⟩ : syracuseStep 7446977 = 5585233) B5585233
theorem B4965083 : Blo 1470555 4965083 := bstep (se 1 (by rfl) ⟨3723812, by rfl⟩ : syracuseStep 4965083 = 7447625) B7447625
theorem B6284243 : Blo 1470555 6284243 := bstep (se 1 (by rfl) ⟨4713182, by rfl⟩ : syracuseStep 6284243 = 9426365) B9426365
theorem B4965353 : Blo 1470555 4965353 := bstep (se 2 (by rfl) ⟨1862007, by rfl⟩ : syracuseStep 4965353 = 3724015) B3724015
theorem B3310919 : Blo 1470555 3310919 := bstep (se 1 (by rfl) ⟨2483189, by rfl⟩ : syracuseStep 3310919 = 4966379) B4966379
theorem B8381951 : Blo 1470555 8381951 := bstep (se 1 (by rfl) ⟨6286463, by rfl⟩ : syracuseStep 8381951 = 12572927) B12572927
theorem B25159247 : Blo 1470555 25159247 := bstep (se 1 (by rfl) ⟨18869435, by rfl⟩ : syracuseStep 25159247 = 37738871) B37738871
theorem B30197609 : Blo 1470555 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B3311657 : Blo 1470555 3311657 := bstep (se 2 (by rfl) ⟨1241871, by rfl⟩ : syracuseStep 3311657 = 2483743) B2483743
theorem B2205833 : Blo 1470555 2205833 := bstep (se 2 (by rfl) ⟨827187, by rfl⟩ : syracuseStep 2205833 = 1654375) B1654375
theorem B32254163 : Blo 1470555 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B2205983 : Blo 1470555 2205983 := bstep (se 1 (by rfl) ⟨1654487, by rfl⟩ : syracuseStep 2205983 = 3308975) B3308975
theorem B2206055 : Blo 1470555 2206055 := bstep (se 1 (by rfl) ⟨1654541, by rfl⟩ : syracuseStep 2206055 = 3309083) B3309083
theorem B7547255 : Blo 1470555 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B2206073 : Blo 1470555 2206073 := bstep (se 2 (by rfl) ⟨827277, by rfl⟩ : syracuseStep 2206073 = 1654555) B1654555
theorem B2206151 : Blo 1470555 2206151 := bstep (se 1 (by rfl) ⟨1654613, by rfl⟩ : syracuseStep 2206151 = 3309227) B3309227
theorem B3312107 : Blo 1470555 3312107 := bstep (se 1 (by rfl) ⟨2484080, by rfl⟩ : syracuseStep 3312107 = 4968161) B4968161
theorem B3312809 : Blo 1470555 3312809 := bstep (se 2 (by rfl) ⟨1242303, by rfl⟩ : syracuseStep 3312809 = 2484607) B2484607
theorem B1862939 : Blo 1470555 1862939 := bstep (se 1 (by rfl) ⟨1397204, by rfl⟩ : syracuseStep 1862939 = 2794409) B2794409
theorem B2207183 : Blo 1470555 2207183 := bstep (se 1 (by rfl) ⟨1655387, by rfl⟩ : syracuseStep 2207183 = 3310775) B3310775
theorem B7450217 : Blo 1470555 7450217 := bstep (se 2 (by rfl) ⟨2793831, by rfl⟩ : syracuseStep 7450217 = 5587663) B5587663
theorem B2207657 : Blo 1470555 2207657 := bstep (se 2 (by rfl) ⟨827871, by rfl⟩ : syracuseStep 2207657 = 1655743) B1655743
theorem B16756793 : Blo 1470555 16756793 := bstep (se 2 (by rfl) ⟨6283797, by rfl⟩ : syracuseStep 16756793 = 12567595) B12567595
theorem B14135471 : Blo 1470555 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B3141823 : Blo 1470555 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B2207951 : Blo 1470555 2207951 := bstep (se 1 (by rfl) ⟨1655963, by rfl⟩ : syracuseStep 2207951 = 3311927) B3311927
theorem B25137377 : Blo 1470555 25137377 := bstep (se 2 (by rfl) ⟨9426516, by rfl⟩ : syracuseStep 25137377 = 18853033) B18853033
theorem B1470943 : Blo 1470555 1470943 := bstep (se 1 (by rfl) ⟨1103207, by rfl⟩ : syracuseStep 1470943 = 2206415) B2206415
theorem B1470959 : Blo 1470555 1470959 := bstep (se 1 (by rfl) ⟨1103219, by rfl⟩ : syracuseStep 1470959 = 2206439) B2206439
theorem B3723803 : Blo 1470555 3723803 := bstep (se 1 (by rfl) ⟨2792852, by rfl⟩ : syracuseStep 3723803 = 5585705) B5585705
theorem B2208425 : Blo 1470555 2208425 := bstep (se 2 (by rfl) ⟨828159, by rfl⟩ : syracuseStep 2208425 = 1656319) B1656319
theorem B1471183 : Blo 1470555 1471183 := bstep (se 1 (by rfl) ⟨1103387, by rfl⟩ : syracuseStep 1471183 = 2206775) B2206775
theorem B1471303 : Blo 1470555 1471303 := bstep (se 1 (by rfl) ⟨1103477, by rfl⟩ : syracuseStep 1471303 = 2206955) B2206955
theorem B1471515 : Blo 1470555 1471515 := bstep (se 1 (by rfl) ⟨1103636, by rfl⟩ : syracuseStep 1471515 = 2207273) B2207273
theorem B3724319 : Blo 1470555 3724319 := bstep (se 1 (by rfl) ⟨2793239, by rfl⟩ : syracuseStep 3724319 = 5586479) B5586479
theorem B1471815 : Blo 1470555 1471815 := bstep (se 1 (by rfl) ⟨1103861, by rfl⟩ : syracuseStep 1471815 = 2207723) B2207723
theorem B3143215 : Blo 1470555 3143215 := bstep (se 1 (by rfl) ⟨2357411, by rfl⟩ : syracuseStep 3143215 = 4714823) B4714823
theorem B1472127 : Blo 1470555 1472127 := bstep (se 1 (by rfl) ⟨1104095, by rfl⟩ : syracuseStep 1472127 = 2208191) B2208191
theorem B1472159 : Blo 1470555 1472159 := bstep (se 1 (by rfl) ⟨1104119, by rfl⟩ : syracuseStep 1472159 = 2208239) B2208239
theorem B1472231 : Blo 1470555 1472231 := bstep (se 1 (by rfl) ⟨1104173, by rfl⟩ : syracuseStep 1472231 = 2208347) B2208347
theorem B372176855 : Blo 1470555 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B7445033 : Blo 1470555 7445033 := bstep (se 2 (by rfl) ⟨2791887, by rfl⟩ : syracuseStep 7445033 = 5583775) B5583775
theorem B11484347 : Blo 1470555 11484347 := bstep (se 1 (by rfl) ⟨8613260, by rfl⟩ : syracuseStep 11484347 = 17226521) B17226521
theorem B149118317 : Blo 1470555 149118317 := bstep (se 3 (by rfl) ⟨27959684, by rfl⟩ : syracuseStep 149118317 = 55919369) B55919369
theorem B12746267 : Blo 1470555 12746267 := bstep (se 1 (by rfl) ⟨9559700, by rfl⟩ : syracuseStep 12746267 = 19119401) B19119401
theorem B3309551 : Blo 1470555 3309551 := bstep (se 1 (by rfl) ⟨2482163, by rfl⟩ : syracuseStep 3309551 = 4964327) B4964327
theorem B1654879 : Blo 1470555 1654879 := bstep (se 1 (by rfl) ⟨1241159, by rfl⟩ : syracuseStep 1654879 = 2482319) B2482319
theorem B4964651 : Blo 1470555 4964651 := bstep (se 1 (by rfl) ⟨3723488, by rfl⟩ : syracuseStep 4964651 = 7446977) B7446977
theorem B2482535 : Blo 1470555 2482535 := bstep (se 1 (by rfl) ⟨1861901, by rfl⟩ : syracuseStep 2482535 = 3723803) B3723803
theorem B3310055 : Blo 1470555 3310055 := bstep (se 1 (by rfl) ⟨2482541, by rfl⟩ : syracuseStep 3310055 = 4965083) B4965083
theorem B3310073 : Blo 1470555 3310073 := bstep (se 2 (by rfl) ⟨1241277, by rfl⟩ : syracuseStep 3310073 = 2482555) B2482555
theorem B3310235 : Blo 1470555 3310235 := bstep (se 1 (by rfl) ⟨2482676, by rfl⟩ : syracuseStep 3310235 = 4965353) B4965353
theorem B2482879 : Blo 1470555 2482879 := bstep (se 1 (by rfl) ⟨1862159, by rfl⟩ : syracuseStep 2482879 = 3724319) B3724319
theorem B5587967 : Blo 1470555 5587967 := bstep (se 1 (by rfl) ⟨4190975, by rfl⟩ : syracuseStep 5587967 = 8381951) B8381951
theorem B5031503 : Blo 1470555 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B99412211 : Blo 1470555 99412211 := bstep (se 1 (by rfl) ⟨74559158, by rfl⟩ : syracuseStep 99412211 = 149118317) B149118317
theorem B8497511 : Blo 1470555 8497511 := bstep (se 1 (by rfl) ⟨6373133, by rfl⟩ : syracuseStep 8497511 = 12746267) B12746267
theorem B4966811 : Blo 1470555 4966811 := bstep (se 1 (by rfl) ⟨3725108, by rfl⟩ : syracuseStep 4966811 = 7450217) B7450217
theorem B2206367 : Blo 1470555 2206367 := bstep (se 1 (by rfl) ⟨1654775, by rfl⟩ : syracuseStep 2206367 = 3309551) B3309551
theorem B14134013 : Blo 1470555 14134013 := bstep (se 3 (by rfl) ⟨2650127, by rfl⟩ : syracuseStep 14134013 = 5300255) B5300255
theorem B9423647 : Blo 1470555 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B3976057 : Blo 1470555 3976057 := bstep (se 2 (by rfl) ⟨1491021, by rfl⟩ : syracuseStep 3976057 = 2982043) B2982043
theorem B2206631 : Blo 1470555 2206631 := bstep (se 1 (by rfl) ⟨1654973, by rfl⟩ : syracuseStep 2206631 = 3309947) B3309947
theorem B4189097 : Blo 1470555 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B30624925 : Blo 1470555 30624925 := bstep (se 3 (by rfl) ⟨5742173, by rfl⟩ : syracuseStep 30624925 = 11484347) B11484347
theorem B4189495 : Blo 1470555 4189495 := bstep (se 1 (by rfl) ⟨3142121, by rfl⟩ : syracuseStep 4189495 = 6284243) B6284243
theorem B4967837 : Blo 1470555 4967837 := bstep (se 3 (by rfl) ⟨931469, by rfl⟩ : syracuseStep 4967837 = 1862939) B1862939
theorem B2207279 : Blo 1470555 2207279 := bstep (se 1 (by rfl) ⟨1655459, by rfl⟩ : syracuseStep 2207279 = 3310919) B3310919
theorem B16772831 : Blo 1470555 16772831 := bstep (se 1 (by rfl) ⟨12579623, by rfl⟩ : syracuseStep 16772831 = 25159247) B25159247
theorem B20131739 : Blo 1470555 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B2207771 : Blo 1470555 2207771 := bstep (se 1 (by rfl) ⟨1655828, by rfl⟩ : syracuseStep 2207771 = 3311657) B3311657
theorem B1470555 : Blo 1470555 1470555 := bstep (se 1 (by rfl) ⟨1102916, by rfl⟩ : syracuseStep 1470555 = 2205833) B2205833
theorem B1470655 : Blo 1470555 1470655 := bstep (se 1 (by rfl) ⟨1102991, by rfl⟩ : syracuseStep 1470655 = 2205983) B2205983
theorem B1470703 : Blo 1470555 1470703 := bstep (se 1 (by rfl) ⟨1103027, by rfl⟩ : syracuseStep 1470703 = 2206055) B2206055
theorem B1470715 : Blo 1470555 1470715 := bstep (se 1 (by rfl) ⟨1103036, by rfl⟩ : syracuseStep 1470715 = 2206073) B2206073
theorem B1470767 : Blo 1470555 1470767 := bstep (se 1 (by rfl) ⟨1103075, by rfl⟩ : syracuseStep 1470767 = 2206151) B2206151
theorem B2208071 : Blo 1470555 2208071 := bstep (se 1 (by rfl) ⟨1656053, by rfl⟩ : syracuseStep 2208071 = 3312107) B3312107
theorem B4190953 : Blo 1470555 4190953 := bstep (se 2 (by rfl) ⟨1571607, by rfl⟩ : syracuseStep 4190953 = 3143215) B3143215
theorem B2208539 : Blo 1470555 2208539 := bstep (se 1 (by rfl) ⟨1656404, by rfl⟩ : syracuseStep 2208539 = 3312809) B3312809
theorem B1471455 : Blo 1470555 1471455 := bstep (se 1 (by rfl) ⟨1103591, by rfl⟩ : syracuseStep 1471455 = 2207183) B2207183
theorem B1471771 : Blo 1470555 1471771 := bstep (se 1 (by rfl) ⟨1103828, by rfl⟩ : syracuseStep 1471771 = 2207657) B2207657
theorem B11171195 : Blo 1470555 11171195 := bstep (se 1 (by rfl) ⟨8378396, by rfl⟩ : syracuseStep 11171195 = 16756793) B16756793
theorem B1471967 : Blo 1470555 1471967 := bstep (se 1 (by rfl) ⟨1103975, by rfl⟩ : syracuseStep 1471967 = 2207951) B2207951
theorem B16758251 : Blo 1470555 16758251 := bstep (se 1 (by rfl) ⟨12568688, by rfl⟩ : syracuseStep 16758251 = 25137377) B25137377
theorem B305976851 : Blo 1470555 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B1472283 : Blo 1470555 1472283 := bstep (se 1 (by rfl) ⟨1104212, by rfl⟩ : syracuseStep 1472283 = 2208425) B2208425
theorem B248117903 : Blo 1470555 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B21502775 : Blo 1470555 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B4963355 : Blo 1470555 4963355 := bstep (se 1 (by rfl) ⟨3722516, by rfl⟩ : syracuseStep 4963355 = 7445033) B7445033
theorem B3309767 : Blo 1470555 3309767 := bstep (se 1 (by rfl) ⟨2482325, by rfl⟩ : syracuseStep 3309767 = 4964651) B4964651
theorem B1655023 : Blo 1470555 1655023 := bstep (se 1 (by rfl) ⟨1241267, by rfl⟩ : syracuseStep 1655023 = 2482535) B2482535
theorem B7447463 : Blo 1470555 7447463 := bstep (se 1 (by rfl) ⟨5585597, by rfl⟩ : syracuseStep 7447463 = 11171195) B11171195
theorem B3310505 : Blo 1470555 3310505 := bstep (se 2 (by rfl) ⟨1241439, by rfl⟩ : syracuseStep 3310505 = 2482879) B2482879
theorem B5587937 : Blo 1470555 5587937 := bstep (se 2 (by rfl) ⟨2095476, by rfl⟩ : syracuseStep 5587937 = 4190953) B4190953
theorem B5301409 : Blo 1470555 5301409 := bstep (se 2 (by rfl) ⟨1988028, by rfl⟩ : syracuseStep 5301409 = 3976057) B3976057
theorem B66274807 : Blo 1470555 66274807 := bstep (se 1 (by rfl) ⟨49706105, by rfl⟩ : syracuseStep 66274807 = 99412211) B99412211
theorem B3311207 : Blo 1470555 3311207 := bstep (se 1 (by rfl) ⟨2483405, by rfl⟩ : syracuseStep 3311207 = 4966811) B4966811
theorem B9422675 : Blo 1470555 9422675 := bstep (se 1 (by rfl) ⟨7067006, by rfl⟩ : syracuseStep 9422675 = 14134013) B14134013
theorem B3311891 : Blo 1470555 3311891 := bstep (se 1 (by rfl) ⟨2483918, by rfl⟩ : syracuseStep 3311891 = 4967837) B4967837
theorem B13421159 : Blo 1470555 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B2206505 : Blo 1470555 2206505 := bstep (se 2 (by rfl) ⟨827439, by rfl⟩ : syracuseStep 2206505 = 1654879) B1654879
theorem B2206703 : Blo 1470555 2206703 := bstep (se 1 (by rfl) ⟨1655027, by rfl⟩ : syracuseStep 2206703 = 3310055) B3310055
theorem B2206715 : Blo 1470555 2206715 := bstep (se 1 (by rfl) ⟨1655036, by rfl⟩ : syracuseStep 2206715 = 3310073) B3310073
theorem B2206823 : Blo 1470555 2206823 := bstep (se 1 (by rfl) ⟨1655117, by rfl⟩ : syracuseStep 2206823 = 3310235) B3310235
theorem B203984567 : Blo 1470555 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B3354335 : Blo 1470555 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B40833233 : Blo 1470555 40833233 := bstep (se 2 (by rfl) ⟨15312462, by rfl⟩ : syracuseStep 40833233 = 30624925) B30624925
theorem B5665007 : Blo 1470555 5665007 := bstep (se 1 (by rfl) ⟨4248755, by rfl⟩ : syracuseStep 5665007 = 8497511) B8497511
theorem B1470911 : Blo 1470555 1470911 := bstep (se 1 (by rfl) ⟨1103183, by rfl⟩ : syracuseStep 1470911 = 2206367) B2206367
theorem B1471087 : Blo 1470555 1471087 := bstep (se 1 (by rfl) ⟨1103315, by rfl⟩ : syracuseStep 1471087 = 2206631) B2206631
theorem B1471519 : Blo 1470555 1471519 := bstep (se 1 (by rfl) ⟨1103639, by rfl⟩ : syracuseStep 1471519 = 2207279) B2207279
theorem B1471847 : Blo 1470555 1471847 := bstep (se 1 (by rfl) ⟨1103885, by rfl⟩ : syracuseStep 1471847 = 2207771) B2207771
theorem B1472047 : Blo 1470555 1472047 := bstep (se 1 (by rfl) ⟨1104035, by rfl⟩ : syracuseStep 1472047 = 2208071) B2208071
theorem B1472359 : Blo 1470555 1472359 := bstep (se 1 (by rfl) ⟨1104269, by rfl⟩ : syracuseStep 1472359 = 2208539) B2208539
theorem B3725311 : Blo 1470555 3725311 := bstep (se 1 (by rfl) ⟨2793983, by rfl⟩ : syracuseStep 3725311 = 5587967) B5587967
theorem B11172167 : Blo 1470555 11172167 := bstep (se 1 (by rfl) ⟨8379125, by rfl⟩ : syracuseStep 11172167 = 16758251) B16758251
theorem B5585993 : Blo 1470555 5585993 := bstep (se 2 (by rfl) ⟨2094747, by rfl⟩ : syracuseStep 5585993 = 4189495) B4189495
theorem B165411935 : Blo 1470555 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B6282431 : Blo 1470555 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B14335183 : Blo 1470555 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B2792731 : Blo 1470555 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B3308903 : Blo 1470555 3308903 := bstep (se 1 (by rfl) ⟨2481677, by rfl⟩ : syracuseStep 3308903 = 4963355) B4963355
theorem B11181887 : Blo 1470555 11181887 := bstep (se 1 (by rfl) ⟨8386415, by rfl⟩ : syracuseStep 11181887 = 16772831) B16772831
theorem B27222155 : Blo 1470555 27222155 := bstep (se 1 (by rfl) ⟨20416616, by rfl⟩ : syracuseStep 27222155 = 40833233) B40833233
theorem B3776671 : Blo 1470555 3776671 := bstep (se 1 (by rfl) ⟨2832503, by rfl⟩ : syracuseStep 3776671 = 5665007) B5665007
theorem B4964975 : Blo 1470555 4964975 := bstep (se 1 (by rfl) ⟨3723731, by rfl⟩ : syracuseStep 4964975 = 7447463) B7447463
theorem B7448111 : Blo 1470555 7448111 := bstep (se 1 (by rfl) ⟨5586083, by rfl⟩ : syracuseStep 7448111 = 11172167) B11172167
theorem B19113577 : Blo 1470555 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B8947439 : Blo 1470555 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B110274623 : Blo 1470555 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B4188287 : Blo 1470555 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B2205935 : Blo 1470555 2205935 := bstep (se 1 (by rfl) ⟨1654451, by rfl⟩ : syracuseStep 2205935 = 3308903) B3308903
theorem B135989711 : Blo 1470555 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B4967081 : Blo 1470555 4967081 := bstep (se 2 (by rfl) ⟨1862655, by rfl⟩ : syracuseStep 4967081 = 3725311) B3725311
theorem B2206511 : Blo 1470555 2206511 := bstep (se 1 (by rfl) ⟨1654883, by rfl⟩ : syracuseStep 2206511 = 3309767) B3309767
theorem B2206697 : Blo 1470555 2206697 := bstep (se 2 (by rfl) ⟨827511, by rfl⟩ : syracuseStep 2206697 = 1655023) B1655023
theorem B2207003 : Blo 1470555 2207003 := bstep (se 1 (by rfl) ⟨1655252, by rfl⟩ : syracuseStep 2207003 = 3310505) B3310505
theorem B2207471 : Blo 1470555 2207471 := bstep (se 1 (by rfl) ⟨1655603, by rfl⟩ : syracuseStep 2207471 = 3311207) B3311207
theorem B2207927 : Blo 1470555 2207927 := bstep (se 1 (by rfl) ⟨1655945, by rfl⟩ : syracuseStep 2207927 = 3311891) B3311891
theorem B3723641 : Blo 1470555 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B1471003 : Blo 1470555 1471003 := bstep (se 1 (by rfl) ⟨1103252, by rfl⟩ : syracuseStep 1471003 = 2206505) B2206505
theorem B1471135 : Blo 1470555 1471135 := bstep (se 1 (by rfl) ⟨1103351, by rfl⟩ : syracuseStep 1471135 = 2206703) B2206703
theorem B1471143 : Blo 1470555 1471143 := bstep (se 1 (by rfl) ⟨1103357, by rfl⟩ : syracuseStep 1471143 = 2206715) B2206715
theorem B3723995 : Blo 1470555 3723995 := bstep (se 1 (by rfl) ⟨2792996, by rfl⟩ : syracuseStep 3723995 = 5585993) B5585993
theorem B1471215 : Blo 1470555 1471215 := bstep (se 1 (by rfl) ⟨1103411, by rfl⟩ : syracuseStep 1471215 = 2206823) B2206823
theorem B3725291 : Blo 1470555 3725291 := bstep (se 1 (by rfl) ⟨2793968, by rfl⟩ : syracuseStep 3725291 = 5587937) B5587937
theorem B6281783 : Blo 1470555 6281783 := bstep (se 1 (by rfl) ⟨4711337, by rfl⟩ : syracuseStep 6281783 = 9422675) B9422675
theorem B7068545 : Blo 1470555 7068545 := bstep (se 2 (by rfl) ⟨2650704, by rfl⟩ : syracuseStep 7068545 = 5301409) B5301409
theorem B88366409 : Blo 1470555 88366409 := bstep (se 2 (by rfl) ⟨33137403, by rfl⟩ : syracuseStep 88366409 = 66274807) B66274807
theorem B2236223 : Blo 1470555 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B7454591 : Blo 1470555 7454591 := bstep (se 1 (by rfl) ⟨5590943, by rfl⟩ : syracuseStep 7454591 = 11181887) B11181887
theorem B2482427 : Blo 1470555 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B3309983 : Blo 1470555 3309983 := bstep (se 1 (by rfl) ⟨2482487, by rfl⟩ : syracuseStep 3309983 = 4964975) B4964975
theorem B2482663 : Blo 1470555 2482663 := bstep (se 1 (by rfl) ⟨1861997, by rfl⟩ : syracuseStep 2482663 = 3723995) B3723995
theorem B4965407 : Blo 1470555 4965407 := bstep (se 1 (by rfl) ⟨3724055, by rfl⟩ : syracuseStep 4965407 = 7448111) B7448111
theorem B5964959 : Blo 1470555 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B2483527 : Blo 1470555 2483527 := bstep (se 1 (by rfl) ⟨1862645, by rfl⟩ : syracuseStep 2483527 = 3725291) B3725291
theorem B73516415 : Blo 1470555 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B4187855 : Blo 1470555 4187855 := bstep (se 1 (by rfl) ⟨3140891, by rfl⟩ : syracuseStep 4187855 = 6281783) B6281783
theorem B3311387 : Blo 1470555 3311387 := bstep (se 1 (by rfl) ⟨2483540, by rfl⟩ : syracuseStep 3311387 = 4967081) B4967081
theorem B4712363 : Blo 1470555 4712363 := bstep (se 1 (by rfl) ⟨3534272, by rfl⟩ : syracuseStep 4712363 = 7068545) B7068545
theorem B58910939 : Blo 1470555 58910939 := bstep (se 1 (by rfl) ⟨44183204, by rfl⟩ : syracuseStep 58910939 = 88366409) B88366409
theorem B18148103 : Blo 1470555 18148103 := bstep (se 1 (by rfl) ⟨13611077, by rfl⟩ : syracuseStep 18148103 = 27222155) B27222155
theorem B11168765 : Blo 1470555 11168765 := bstep (se 3 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 11168765 = 4188287) B4188287
theorem B1470623 : Blo 1470555 1470623 := bstep (se 1 (by rfl) ⟨1102967, by rfl⟩ : syracuseStep 1470623 = 2205935) B2205935
theorem B1471007 : Blo 1470555 1471007 := bstep (se 1 (by rfl) ⟨1103255, by rfl⟩ : syracuseStep 1471007 = 2206511) B2206511
theorem B1471131 : Blo 1470555 1471131 := bstep (se 1 (by rfl) ⟨1103348, by rfl⟩ : syracuseStep 1471131 = 2206697) B2206697
theorem B1471335 : Blo 1470555 1471335 := bstep (se 1 (by rfl) ⟨1103501, by rfl⟩ : syracuseStep 1471335 = 2207003) B2207003
theorem B1471647 : Blo 1470555 1471647 := bstep (se 1 (by rfl) ⟨1103735, by rfl⟩ : syracuseStep 1471647 = 2207471) B2207471
theorem B4969727 : Blo 1470555 4969727 := bstep (se 1 (by rfl) ⟨3727295, by rfl⟩ : syracuseStep 4969727 = 7454591) B7454591
theorem B1471951 : Blo 1470555 1471951 := bstep (se 1 (by rfl) ⟨1103963, by rfl⟩ : syracuseStep 1471951 = 2207927) B2207927
theorem B101939077 : Blo 1470555 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B20142245 : Blo 1470555 20142245 := bstep (se 4 (by rfl) ⟨1888335, by rfl⟩ : syracuseStep 20142245 = 3776671) B3776671
theorem B90659807 : Blo 1470555 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B1490815 : Blo 1470555 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B1654951 : Blo 1470555 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B3310217 : Blo 1470555 3310217 := bstep (se 2 (by rfl) ⟨1241331, by rfl⟩ : syracuseStep 3310217 = 2482663) B2482663
theorem B3310271 : Blo 1470555 3310271 := bstep (se 1 (by rfl) ⟨2482703, by rfl⟩ : syracuseStep 3310271 = 4965407) B4965407
theorem B196043773 : Blo 1470555 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B13428163 : Blo 1470555 13428163 := bstep (se 1 (by rfl) ⟨10071122, by rfl⟩ : syracuseStep 13428163 = 20142245) B20142245
theorem B39273959 : Blo 1470555 39273959 := bstep (se 1 (by rfl) ⟨29455469, by rfl⟩ : syracuseStep 39273959 = 58910939) B58910939
theorem B3311369 : Blo 1470555 3311369 := bstep (se 2 (by rfl) ⟨1241763, by rfl⟩ : syracuseStep 3311369 = 2483527) B2483527
theorem B2206655 : Blo 1470555 2206655 := bstep (se 1 (by rfl) ⟨1654991, by rfl⟩ : syracuseStep 2206655 = 3309983) B3309983
theorem B3313151 : Blo 1470555 3313151 := bstep (se 1 (by rfl) ⟨2484863, by rfl⟩ : syracuseStep 3313151 = 4969727) B4969727
theorem B2207591 : Blo 1470555 2207591 := bstep (se 1 (by rfl) ⟨1655693, by rfl⟩ : syracuseStep 2207591 = 3311387) B3311387
theorem B3141575 : Blo 1470555 3141575 := bstep (se 1 (by rfl) ⟨2356181, by rfl⟩ : syracuseStep 3141575 = 4712363) B4712363
theorem B1987753 : Blo 1470555 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B135918769 : Blo 1470555 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B15906557 : Blo 1470555 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B2791903 : Blo 1470555 2791903 := bstep (se 1 (by rfl) ⟨2093927, by rfl⟩ : syracuseStep 2791903 = 4187855) B4187855
theorem B12098735 : Blo 1470555 12098735 := bstep (se 1 (by rfl) ⟨9074051, by rfl⟩ : syracuseStep 12098735 = 18148103) B18148103
theorem B60439871 : Blo 1470555 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B7445843 : Blo 1470555 7445843 := bstep (se 1 (by rfl) ⟨5584382, by rfl⟩ : syracuseStep 7445843 = 11168765) B11168765
theorem B26182639 : Blo 1470555 26182639 := bstep (se 1 (by rfl) ⟨19636979, by rfl⟩ : syracuseStep 26182639 = 39273959) B39273959
theorem B261391697 : Blo 1470555 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B181225025 : Blo 1470555 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B71616869 : Blo 1470555 71616869 := bstep (se 4 (by rfl) ⟨6714081, by rfl⟩ : syracuseStep 71616869 = 13428163) B13428163
theorem B2206601 : Blo 1470555 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B2206811 : Blo 1470555 2206811 := bstep (se 1 (by rfl) ⟨1655108, by rfl⟩ : syracuseStep 2206811 = 3310217) B3310217
theorem B2206847 : Blo 1470555 2206847 := bstep (se 1 (by rfl) ⟨1655135, by rfl⟩ : syracuseStep 2206847 = 3310271) B3310271
theorem B3722537 : Blo 1470555 3722537 := bstep (se 2 (by rfl) ⟨1395951, by rfl⟩ : syracuseStep 3722537 = 2791903) B2791903
theorem B10604371 : Blo 1470555 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B2207579 : Blo 1470555 2207579 := bstep (se 1 (by rfl) ⟨1655684, by rfl⟩ : syracuseStep 2207579 = 3311369) B3311369
theorem B2650337 : Blo 1470555 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B1471103 : Blo 1470555 1471103 := bstep (se 1 (by rfl) ⟨1103327, by rfl⟩ : syracuseStep 1471103 = 2206655) B2206655
theorem B8065823 : Blo 1470555 8065823 := bstep (se 1 (by rfl) ⟨6049367, by rfl⟩ : syracuseStep 8065823 = 12098735) B12098735
theorem B40293247 : Blo 1470555 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B2208767 : Blo 1470555 2208767 := bstep (se 1 (by rfl) ⟨1656575, by rfl⟩ : syracuseStep 2208767 = 3313151) B3313151
theorem B1471727 : Blo 1470555 1471727 := bstep (se 1 (by rfl) ⟨1103795, by rfl⟩ : syracuseStep 1471727 = 2207591) B2207591
theorem B2094383 : Blo 1470555 2094383 := bstep (se 1 (by rfl) ⟨1570787, by rfl⟩ : syracuseStep 2094383 = 3141575) B3141575
theorem B4963895 : Blo 1470555 4963895 := bstep (se 1 (by rfl) ⟨3722921, by rfl⟩ : syracuseStep 4963895 = 7445843) B7445843
theorem B174261131 : Blo 1470555 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B120816683 : Blo 1470555 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B53724329 : Blo 1470555 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B47744579 : Blo 1470555 47744579 := bstep (se 1 (by rfl) ⟨35808434, by rfl⟩ : syracuseStep 47744579 = 71616869) B71616869
theorem B34910185 : Blo 1470555 34910185 := bstep (se 2 (by rfl) ⟨13091319, by rfl⟩ : syracuseStep 34910185 = 26182639) B26182639
theorem B1471067 : Blo 1470555 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B1471207 : Blo 1470555 1471207 := bstep (se 1 (by rfl) ⟨1103405, by rfl⟩ : syracuseStep 1471207 = 2206811) B2206811
theorem B21508861 : Blo 1470555 21508861 := bstep (se 3 (by rfl) ⟨4032911, by rfl⟩ : syracuseStep 21508861 = 8065823) B8065823
theorem B1471231 : Blo 1470555 1471231 := bstep (se 1 (by rfl) ⟨1103423, by rfl⟩ : syracuseStep 1471231 = 2206847) B2206847
theorem B1471719 : Blo 1470555 1471719 := bstep (se 1 (by rfl) ⟨1103789, by rfl⟩ : syracuseStep 1471719 = 2207579) B2207579
theorem B1766891 : Blo 1470555 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B1472511 : Blo 1470555 1472511 := bstep (se 1 (by rfl) ⟨1104383, by rfl⟩ : syracuseStep 1472511 = 2208767) B2208767
theorem B5585021 : Blo 1470555 5585021 := bstep (se 3 (by rfl) ⟨1047191, by rfl⟩ : syracuseStep 5585021 = 2094383) B2094383
theorem B2481691 : Blo 1470555 2481691 := bstep (se 1 (by rfl) ⟨1861268, by rfl⟩ : syracuseStep 2481691 = 3722537) B3722537
theorem B3309263 : Blo 1470555 3309263 := bstep (se 1 (by rfl) ⟨2481947, by rfl⟩ : syracuseStep 3309263 = 4963895) B4963895
theorem B14139161 : Blo 1470555 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B80544455 : Blo 1470555 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B35816219 : Blo 1470555 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B4711709 : Blo 1470555 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B2206175 : Blo 1470555 2206175 := bstep (se 1 (by rfl) ⟨1654631, by rfl⟩ : syracuseStep 2206175 = 3309263) B3309263
theorem B116174087 : Blo 1470555 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B31829719 : Blo 1470555 31829719 := bstep (se 1 (by rfl) ⟨23872289, by rfl⟩ : syracuseStep 31829719 = 47744579) B47744579
theorem B3723347 : Blo 1470555 3723347 := bstep (se 1 (by rfl) ⟨2792510, by rfl⟩ : syracuseStep 3723347 = 5585021) B5585021
theorem B9426107 : Blo 1470555 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B28678481 : Blo 1470555 28678481 := bstep (se 2 (by rfl) ⟨10754430, by rfl⟩ : syracuseStep 28678481 = 21508861) B21508861
theorem B3308921 : Blo 1470555 3308921 := bstep (se 2 (by rfl) ⟨1240845, by rfl⟩ : syracuseStep 3308921 = 2481691) B2481691
theorem B46546913 : Blo 1470555 46546913 := bstep (se 2 (by rfl) ⟨17455092, by rfl⟩ : syracuseStep 46546913 = 34910185) B34910185
theorem B2482231 : Blo 1470555 2482231 := bstep (se 1 (by rfl) ⟨1861673, by rfl⟩ : syracuseStep 2482231 = 3723347) B3723347
theorem B6284071 : Blo 1470555 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B77449391 : Blo 1470555 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B2205947 : Blo 1470555 2205947 := bstep (se 1 (by rfl) ⟨1654460, by rfl⟩ : syracuseStep 2205947 = 3308921) B3308921
theorem B1470783 : Blo 1470555 1470783 := bstep (se 1 (by rfl) ⟨1103087, by rfl⟩ : syracuseStep 1470783 = 2206175) B2206175
theorem B42439625 : Blo 1470555 42439625 := bstep (se 2 (by rfl) ⟨15914859, by rfl⟩ : syracuseStep 42439625 = 31829719) B31829719
theorem B53696303 : Blo 1470555 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B23877479 : Blo 1470555 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B12564557 : Blo 1470555 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B19118987 : Blo 1470555 19118987 := bstep (se 1 (by rfl) ⟨14339240, by rfl⟩ : syracuseStep 19118987 = 28678481) B28678481
theorem B31031275 : Blo 1470555 31031275 := bstep (se 1 (by rfl) ⟨23273456, by rfl⟩ : syracuseStep 31031275 = 46546913) B46546913
theorem B3309641 : Blo 1470555 3309641 := bstep (se 2 (by rfl) ⟨1241115, by rfl⟩ : syracuseStep 3309641 = 2482231) B2482231
theorem B15918319 : Blo 1470555 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B8376371 : Blo 1470555 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B1470631 : Blo 1470555 1470631 := bstep (se 1 (by rfl) ⟨1102973, by rfl⟩ : syracuseStep 1470631 = 2205947) B2205947
theorem B41375033 : Blo 1470555 41375033 := bstep (se 2 (by rfl) ⟨15515637, by rfl⟩ : syracuseStep 41375033 = 31031275) B31031275
theorem B28293083 : Blo 1470555 28293083 := bstep (se 1 (by rfl) ⟨21219812, by rfl⟩ : syracuseStep 28293083 = 42439625) B42439625
theorem B8378761 : Blo 1470555 8378761 := bstep (se 2 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 8378761 = 6284071) B6284071
theorem B35797535 : Blo 1470555 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B51632927 : Blo 1470555 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B12745991 : Blo 1470555 12745991 := bstep (se 1 (by rfl) ⟨9559493, by rfl⟩ : syracuseStep 12745991 = 19118987) B19118987
theorem B27583355 : Blo 1470555 27583355 := bstep (se 1 (by rfl) ⟨20687516, by rfl⟩ : syracuseStep 27583355 = 41375033) B41375033
theorem B23865023 : Blo 1470555 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B8497327 : Blo 1470555 8497327 := bstep (se 1 (by rfl) ⟨6372995, by rfl⟩ : syracuseStep 8497327 = 12745991) B12745991
theorem B2206427 : Blo 1470555 2206427 := bstep (se 1 (by rfl) ⟨1654820, by rfl⟩ : syracuseStep 2206427 = 3309641) B3309641
theorem B18862055 : Blo 1470555 18862055 := bstep (se 1 (by rfl) ⟨14146541, by rfl⟩ : syracuseStep 18862055 = 28293083) B28293083
theorem B5584247 : Blo 1470555 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B11171681 : Blo 1470555 11171681 := bstep (se 2 (by rfl) ⟨4189380, by rfl⟩ : syracuseStep 11171681 = 8378761) B8378761
theorem B21224425 : Blo 1470555 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B34421951 : Blo 1470555 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B11329769 : Blo 1470555 11329769 := bstep (se 2 (by rfl) ⟨4248663, by rfl⟩ : syracuseStep 11329769 = 8497327) B8497327
theorem B15910015 : Blo 1470555 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B7447787 : Blo 1470555 7447787 := bstep (se 1 (by rfl) ⟨5585840, by rfl⟩ : syracuseStep 7447787 = 11171681) B11171681
theorem B22947967 : Blo 1470555 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B3722831 : Blo 1470555 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B28299233 : Blo 1470555 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B1470951 : Blo 1470555 1470951 := bstep (se 1 (by rfl) ⟨1103213, by rfl⟩ : syracuseStep 1470951 = 2206427) B2206427
theorem B73555613 : Blo 1470555 73555613 := bstep (se 3 (by rfl) ⟨13791677, by rfl⟩ : syracuseStep 73555613 = 27583355) B27583355
theorem B12574703 : Blo 1470555 12574703 := bstep (se 1 (by rfl) ⟨9431027, by rfl⟩ : syracuseStep 12574703 = 18862055) B18862055
theorem B7553179 : Blo 1470555 7553179 := bstep (se 1 (by rfl) ⟨5664884, by rfl⟩ : syracuseStep 7553179 = 11329769) B11329769
theorem B122389157 : Blo 1470555 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B4965191 : Blo 1470555 4965191 := bstep (se 1 (by rfl) ⟨3723893, by rfl⟩ : syracuseStep 4965191 = 7447787) B7447787
theorem B8383135 : Blo 1470555 8383135 := bstep (se 1 (by rfl) ⟨6287351, by rfl⟩ : syracuseStep 8383135 = 12574703) B12574703
theorem B21213353 : Blo 1470555 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B2481887 : Blo 1470555 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B49037075 : Blo 1470555 49037075 := bstep (se 1 (by rfl) ⟨36777806, by rfl⟩ : syracuseStep 49037075 = 73555613) B73555613
theorem B18866155 : Blo 1470555 18866155 := bstep (se 1 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 18866155 = 28299233) B28299233
theorem B81592771 : Blo 1470555 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B3310127 : Blo 1470555 3310127 := bstep (se 1 (by rfl) ⟨2482595, by rfl⟩ : syracuseStep 3310127 = 4965191) B4965191
theorem B10070905 : Blo 1470555 10070905 := bstep (se 2 (by rfl) ⟨3776589, by rfl⟩ : syracuseStep 10070905 = 7553179) B7553179
theorem B56568941 : Blo 1470555 56568941 := bstep (se 3 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 56568941 = 21213353) B21213353
theorem B11177513 : Blo 1470555 11177513 := bstep (se 2 (by rfl) ⟨4191567, by rfl⟩ : syracuseStep 11177513 = 8383135) B8383135
theorem B32691383 : Blo 1470555 32691383 := bstep (se 1 (by rfl) ⟨24518537, by rfl⟩ : syracuseStep 32691383 = 49037075) B49037075
theorem B25154873 : Blo 1470555 25154873 := bstep (se 2 (by rfl) ⟨9433077, by rfl⟩ : syracuseStep 25154873 = 18866155) B18866155
theorem B1654591 : Blo 1470555 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B108790361 : Blo 1470555 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B16769915 : Blo 1470555 16769915 := bstep (se 1 (by rfl) ⟨12577436, by rfl⟩ : syracuseStep 16769915 = 25154873) B25154873
theorem B13427873 : Blo 1470555 13427873 := bstep (se 2 (by rfl) ⟨5035452, by rfl⟩ : syracuseStep 13427873 = 10070905) B10070905
theorem B2206121 : Blo 1470555 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B2206751 : Blo 1470555 2206751 := bstep (se 1 (by rfl) ⟨1655063, by rfl⟩ : syracuseStep 2206751 = 3310127) B3310127
theorem B21794255 : Blo 1470555 21794255 := bstep (se 1 (by rfl) ⟨16345691, by rfl⟩ : syracuseStep 21794255 = 32691383) B32691383
theorem B37712627 : Blo 1470555 37712627 := bstep (se 1 (by rfl) ⟨28284470, by rfl⟩ : syracuseStep 37712627 = 56568941) B56568941
theorem B7451675 : Blo 1470555 7451675 := bstep (se 1 (by rfl) ⟨5588756, by rfl⟩ : syracuseStep 7451675 = 11177513) B11177513
theorem B25141751 : Blo 1470555 25141751 := bstep (se 1 (by rfl) ⟨18856313, by rfl⟩ : syracuseStep 25141751 = 37712627) B37712627
theorem B72526907 : Blo 1470555 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B4967783 : Blo 1470555 4967783 := bstep (se 1 (by rfl) ⟨3725837, by rfl⟩ : syracuseStep 4967783 = 7451675) B7451675
theorem B1470747 : Blo 1470555 1470747 := bstep (se 1 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 1470747 = 2206121) B2206121
theorem B1471167 : Blo 1470555 1471167 := bstep (se 1 (by rfl) ⟨1103375, by rfl⟩ : syracuseStep 1471167 = 2206751) B2206751
theorem B14529503 : Blo 1470555 14529503 := bstep (se 1 (by rfl) ⟨10897127, by rfl⟩ : syracuseStep 14529503 = 21794255) B21794255
theorem B11179943 : Blo 1470555 11179943 := bstep (se 1 (by rfl) ⟨8384957, by rfl⟩ : syracuseStep 11179943 = 16769915) B16769915
theorem B8951915 : Blo 1470555 8951915 := bstep (se 1 (by rfl) ⟨6713936, by rfl⟩ : syracuseStep 8951915 = 13427873) B13427873
theorem B23871773 : Blo 1470555 23871773 := bstep (se 3 (by rfl) ⟨4475957, by rfl⟩ : syracuseStep 23871773 = 8951915) B8951915
theorem B16761167 : Blo 1470555 16761167 := bstep (se 1 (by rfl) ⟨12570875, by rfl⟩ : syracuseStep 16761167 = 25141751) B25141751
theorem B48351271 : Blo 1470555 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B3311855 : Blo 1470555 3311855 := bstep (se 1 (by rfl) ⟨2483891, by rfl⟩ : syracuseStep 3311855 = 4967783) B4967783
theorem B38745341 : Blo 1470555 38745341 := bstep (se 3 (by rfl) ⟨7264751, by rfl⟩ : syracuseStep 38745341 = 14529503) B14529503
theorem B7453295 : Blo 1470555 7453295 := bstep (se 1 (by rfl) ⟨5589971, by rfl⟩ : syracuseStep 7453295 = 11179943) B11179943
theorem B11174111 : Blo 1470555 11174111 := bstep (se 1 (by rfl) ⟨8380583, by rfl⟩ : syracuseStep 11174111 = 16761167) B16761167
theorem B25830227 : Blo 1470555 25830227 := bstep (se 1 (by rfl) ⟨19372670, by rfl⟩ : syracuseStep 25830227 = 38745341) B38745341
theorem B2207903 : Blo 1470555 2207903 := bstep (se 1 (by rfl) ⟨1655927, by rfl⟩ : syracuseStep 2207903 = 3311855) B3311855
theorem B4968863 : Blo 1470555 4968863 := bstep (se 1 (by rfl) ⟨3726647, by rfl⟩ : syracuseStep 4968863 = 7453295) B7453295
theorem B64468361 : Blo 1470555 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B15914515 : Blo 1470555 15914515 := bstep (se 1 (by rfl) ⟨11935886, by rfl⟩ : syracuseStep 15914515 = 23871773) B23871773
theorem B17220151 : Blo 1470555 17220151 := bstep (se 1 (by rfl) ⟨12915113, by rfl⟩ : syracuseStep 17220151 = 25830227) B25830227
theorem B21219353 : Blo 1470555 21219353 := bstep (se 2 (by rfl) ⟨7957257, by rfl⟩ : syracuseStep 21219353 = 15914515) B15914515
theorem B7449407 : Blo 1470555 7449407 := bstep (se 1 (by rfl) ⟨5587055, by rfl⟩ : syracuseStep 7449407 = 11174111) B11174111
theorem B3312575 : Blo 1470555 3312575 := bstep (se 1 (by rfl) ⟨2484431, by rfl⟩ : syracuseStep 3312575 = 4968863) B4968863
theorem B42978907 : Blo 1470555 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B1471935 : Blo 1470555 1471935 := bstep (se 1 (by rfl) ⟨1103951, by rfl⟩ : syracuseStep 1471935 = 2207903) B2207903
theorem B229220837 : Blo 1470555 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B4966271 : Blo 1470555 4966271 := bstep (se 1 (by rfl) ⟨3724703, by rfl⟩ : syracuseStep 4966271 = 7449407) B7449407
theorem B2208383 : Blo 1470555 2208383 := bstep (se 1 (by rfl) ⟨1656287, by rfl⟩ : syracuseStep 2208383 = 3312575) B3312575
theorem B22960201 : Blo 1470555 22960201 := bstep (se 2 (by rfl) ⟨8610075, by rfl⟩ : syracuseStep 22960201 = 17220151) B17220151
theorem B14146235 : Blo 1470555 14146235 := bstep (se 1 (by rfl) ⟨10609676, by rfl⟩ : syracuseStep 14146235 = 21219353) B21219353
theorem B30613601 : Blo 1470555 30613601 := bstep (se 2 (by rfl) ⟨11480100, by rfl⟩ : syracuseStep 30613601 = 22960201) B22960201
theorem B152813891 : Blo 1470555 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B3310847 : Blo 1470555 3310847 := bstep (se 1 (by rfl) ⟨2483135, by rfl⟩ : syracuseStep 3310847 = 4966271) B4966271
theorem B9430823 : Blo 1470555 9430823 := bstep (se 1 (by rfl) ⟨7073117, by rfl⟩ : syracuseStep 9430823 = 14146235) B14146235
theorem B1472255 : Blo 1470555 1472255 := bstep (se 1 (by rfl) ⟨1104191, by rfl⟩ : syracuseStep 1472255 = 2208383) B2208383
theorem B101875927 : Blo 1470555 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B20409067 : Blo 1470555 20409067 := bstep (se 1 (by rfl) ⟨15306800, by rfl⟩ : syracuseStep 20409067 = 30613601) B30613601
theorem B2207231 : Blo 1470555 2207231 := bstep (se 1 (by rfl) ⟨1655423, by rfl⟩ : syracuseStep 2207231 = 3310847) B3310847
theorem B6287215 : Blo 1470555 6287215 := bstep (se 1 (by rfl) ⟨4715411, by rfl⟩ : syracuseStep 6287215 = 9430823) B9430823
theorem B108848357 : Blo 1470555 108848357 := bstep (se 4 (by rfl) ⟨10204533, by rfl⟩ : syracuseStep 108848357 = 20409067) B20409067
theorem B8382953 : Blo 1470555 8382953 := bstep (se 2 (by rfl) ⟨3143607, by rfl⟩ : syracuseStep 8382953 = 6287215) B6287215
theorem B135834569 : Blo 1470555 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B1471487 : Blo 1470555 1471487 := bstep (se 1 (by rfl) ⟨1103615, by rfl⟩ : syracuseStep 1471487 = 2207231) B2207231
theorem B72565571 : Blo 1470555 72565571 := bstep (se 1 (by rfl) ⟨54424178, by rfl⟩ : syracuseStep 72565571 = 108848357) B108848357
theorem B5588635 : Blo 1470555 5588635 := bstep (se 1 (by rfl) ⟨4191476, by rfl⟩ : syracuseStep 5588635 = 8382953) B8382953
theorem B90556379 : Blo 1470555 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B60370919 : Blo 1470555 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B193508189 : Blo 1470555 193508189 := bstep (se 3 (by rfl) ⟨36282785, by rfl⟩ : syracuseStep 193508189 = 72565571) B72565571
theorem B7451513 : Blo 1470555 7451513 := bstep (se 2 (by rfl) ⟨2794317, by rfl⟩ : syracuseStep 7451513 = 5588635) B5588635
theorem B4967675 : Blo 1470555 4967675 := bstep (se 1 (by rfl) ⟨3725756, by rfl⟩ : syracuseStep 4967675 = 7451513) B7451513
theorem B129005459 : Blo 1470555 129005459 := bstep (se 1 (by rfl) ⟨96754094, by rfl⟩ : syracuseStep 129005459 = 193508189) B193508189
theorem B40247279 : Blo 1470555 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B3311783 : Blo 1470555 3311783 := bstep (se 1 (by rfl) ⟨2483837, by rfl⟩ : syracuseStep 3311783 = 4967675) B4967675
theorem B26831519 : Blo 1470555 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B86003639 : Blo 1470555 86003639 := bstep (se 1 (by rfl) ⟨64502729, by rfl⟩ : syracuseStep 86003639 = 129005459) B129005459
theorem B2207855 : Blo 1470555 2207855 := bstep (se 1 (by rfl) ⟨1655891, by rfl⟩ : syracuseStep 2207855 = 3311783) B3311783
theorem B17887679 : Blo 1470555 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B57335759 : Blo 1470555 57335759 := bstep (se 1 (by rfl) ⟨43001819, by rfl⟩ : syracuseStep 57335759 = 86003639) B86003639
theorem B1471903 : Blo 1470555 1471903 := bstep (se 1 (by rfl) ⟨1103927, by rfl⟩ : syracuseStep 1471903 = 2207855) B2207855
theorem B11925119 : Blo 1470555 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B38223839 : Blo 1470555 38223839 := bstep (se 1 (by rfl) ⟨28667879, by rfl⟩ : syracuseStep 38223839 = 57335759) B57335759
theorem B7950079 : Blo 1470555 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B25482559 : Blo 1470555 25482559 := bstep (se 1 (by rfl) ⟨19111919, by rfl⟩ : syracuseStep 25482559 = 38223839) B38223839
theorem B33976745 : Blo 1470555 33976745 := bstep (se 2 (by rfl) ⟨12741279, by rfl⟩ : syracuseStep 33976745 = 25482559) B25482559
theorem B10600105 : Blo 1470555 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B22651163 : Blo 1470555 22651163 := bstep (se 1 (by rfl) ⟨16988372, by rfl⟩ : syracuseStep 22651163 = 33976745) B33976745
theorem B14133473 : Blo 1470555 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B9422315 : Blo 1470555 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B15100775 : Blo 1470555 15100775 := bstep (se 1 (by rfl) ⟨11325581, by rfl⟩ : syracuseStep 15100775 = 22651163) B22651163
theorem B6281543 : Blo 1470555 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B10067183 : Blo 1470555 10067183 := bstep (se 1 (by rfl) ⟨7550387, by rfl⟩ : syracuseStep 10067183 = 15100775) B15100775
theorem B4187695 : Blo 1470555 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B6711455 : Blo 1470555 6711455 := bstep (se 1 (by rfl) ⟨5033591, by rfl⟩ : syracuseStep 6711455 = 10067183) B10067183
theorem B5583593 : Blo 1470555 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B17897213 : Blo 1470555 17897213 := bstep (se 3 (by rfl) ⟨3355727, by rfl⟩ : syracuseStep 17897213 = 6711455) B6711455
theorem B3722395 : Blo 1470555 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B11931475 : Blo 1470555 11931475 := bstep (se 1 (by rfl) ⟨8948606, by rfl⟩ : syracuseStep 11931475 = 17897213) B17897213
theorem B4963193 : Blo 1470555 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B15908633 : Blo 1470555 15908633 := bstep (se 2 (by rfl) ⟨5965737, by rfl⟩ : syracuseStep 15908633 = 11931475) B11931475
theorem B10605755 : Blo 1470555 10605755 := bstep (se 1 (by rfl) ⟨7954316, by rfl⟩ : syracuseStep 10605755 = 15908633) B15908633
theorem B3308795 : Blo 1470555 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B7070503 : Blo 1470555 7070503 := bstep (se 1 (by rfl) ⟨5302877, by rfl⟩ : syracuseStep 7070503 = 10605755) B10605755
theorem B2205863 : Blo 1470555 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B1470575 : Blo 1470555 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B9427337 : Blo 1470555 9427337 := bstep (se 2 (by rfl) ⟨3535251, by rfl⟩ : syracuseStep 9427337 = 7070503) B7070503
theorem B6284891 : Blo 1470555 6284891 := bstep (se 1 (by rfl) ⟨4713668, by rfl⟩ : syracuseStep 6284891 = 9427337) B9427337
theorem B16759709 : Blo 1470555 16759709 := bstep (se 3 (by rfl) ⟨3142445, by rfl⟩ : syracuseStep 16759709 = 6284891) B6284891
theorem B11173139 : Blo 1470555 11173139 := bstep (se 1 (by rfl) ⟨8379854, by rfl⟩ : syracuseStep 11173139 = 16759709) B16759709
theorem B7448759 : Blo 1470555 7448759 := bstep (se 1 (by rfl) ⟨5586569, by rfl⟩ : syracuseStep 7448759 = 11173139) B11173139
theorem B4965839 : Blo 1470555 4965839 := bstep (se 1 (by rfl) ⟨3724379, by rfl⟩ : syracuseStep 4965839 = 7448759) B7448759
theorem B3310559 : Blo 1470555 3310559 := bstep (se 1 (by rfl) ⟨2482919, by rfl⟩ : syracuseStep 3310559 = 4965839) B4965839
theorem B2207039 : Blo 1470555 2207039 := bstep (se 1 (by rfl) ⟨1655279, by rfl⟩ : syracuseStep 2207039 = 3310559) B3310559
theorem B1471359 : Blo 1470555 1471359 := bstep (se 1 (by rfl) ⟨1103519, by rfl⟩ : syracuseStep 1471359 = 2207039) B2207039

theorem C0 (j : ℕ) (h1 : 367638 ≤ j) (h2 : j ≤ 368138) : Blo 1470555 (4 * j + 3) := by
  interval_cases j
  · exact B1470555
  · exact B1470559
  · exact B1470563
  · exact B1470567
  · exact B1470571
  · exact B1470575
  · exact B1470579
  · exact B1470583
  · exact B1470587
  · exact B1470591
  · exact B1470595
  · exact B1470599
  · exact B1470603
  · exact B1470607
  · exact B1470611
  · exact B1470615
  · exact B1470619
  · exact B1470623
  · exact B1470627
  · exact B1470631
  · exact B1470635
  · exact B1470639
  · exact B1470643
  · exact B1470647
  · exact B1470651
  · exact B1470655
  · exact B1470659
  · exact B1470663
  · exact B1470667
  · exact B1470671
  · exact B1470675
  · exact B1470679
  · exact B1470683
  · exact B1470687
  · exact B1470691
  · exact B1470695
  · exact B1470699
  · exact B1470703
  · exact B1470707
  · exact B1470711
  · exact B1470715
  · exact B1470719
  · exact B1470723
  · exact B1470727
  · exact B1470731
  · exact B1470735
  · exact B1470739
  · exact B1470743
  · exact B1470747
  · exact B1470751
  · exact B1470755
  · exact B1470759
  · exact B1470763
  · exact B1470767
  · exact B1470771
  · exact B1470775
  · exact B1470779
  · exact B1470783
  · exact B1470787
  · exact B1470791
  · exact B1470795
  · exact B1470799
  · exact B1470803
  · exact B1470807
  · exact B1470811
  · exact B1470815
  · exact B1470819
  · exact B1470823
  · exact B1470827
  · exact B1470831
  · exact B1470835
  · exact B1470839
  · exact B1470843
  · exact B1470847
  · exact B1470851
  · exact B1470855
  · exact B1470859
  · exact B1470863
  · exact B1470867
  · exact B1470871
  · exact B1470875
  · exact B1470879
  · exact B1470883
  · exact B1470887
  · exact B1470891
  · exact B1470895
  · exact B1470899
  · exact B1470903
  · exact B1470907
  · exact B1470911
  · exact B1470915
  · exact B1470919
  · exact B1470923
  · exact B1470927
  · exact B1470931
  · exact B1470935
  · exact B1470939
  · exact B1470943
  · exact B1470947
  · exact B1470951
  · exact B1470955
  · exact B1470959
  · exact B1470963
  · exact B1470967
  · exact B1470971
  · exact B1470975
  · exact B1470979
  · exact B1470983
  · exact B1470987
  · exact B1470991
  · exact B1470995
  · exact B1470999
  · exact B1471003
  · exact B1471007
  · exact B1471011
  · exact B1471015
  · exact B1471019
  · exact B1471023
  · exact B1471027
  · exact B1471031
  · exact B1471035
  · exact B1471039
  · exact B1471043
  · exact B1471047
  · exact B1471051
  · exact B1471055
  · exact B1471059
  · exact B1471063
  · exact B1471067
  · exact B1471071
  · exact B1471075
  · exact B1471079
  · exact B1471083
  · exact B1471087
  · exact B1471091
  · exact B1471095
  · exact B1471099
  · exact B1471103
  · exact B1471107
  · exact B1471111
  · exact B1471115
  · exact B1471119
  · exact B1471123
  · exact B1471127
  · exact B1471131
  · exact B1471135
  · exact B1471139
  · exact B1471143
  · exact B1471147
  · exact B1471151
  · exact B1471155
  · exact B1471159
  · exact B1471163
  · exact B1471167
  · exact B1471171
  · exact B1471175
  · exact B1471179
  · exact B1471183
  · exact B1471187
  · exact B1471191
  · exact B1471195
  · exact B1471199
  · exact B1471203
  · exact B1471207
  · exact B1471211
  · exact B1471215
  · exact B1471219
  · exact B1471223
  · exact B1471227
  · exact B1471231
  · exact B1471235
  · exact B1471239
  · exact B1471243
  · exact B1471247
  · exact B1471251
  · exact B1471255
  · exact B1471259
  · exact B1471263
  · exact B1471267
  · exact B1471271
  · exact B1471275
  · exact B1471279
  · exact B1471283
  · exact B1471287
  · exact B1471291
  · exact B1471295
  · exact B1471299
  · exact B1471303
  · exact B1471307
  · exact B1471311
  · exact B1471315
  · exact B1471319
  · exact B1471323
  · exact B1471327
  · exact B1471331
  · exact B1471335
  · exact B1471339
  · exact B1471343
  · exact B1471347
  · exact B1471351
  · exact B1471355
  · exact B1471359
  · exact B1471363
  · exact B1471367
  · exact B1471371
  · exact B1471375
  · exact B1471379
  · exact B1471383
  · exact B1471387
  · exact B1471391
  · exact B1471395
  · exact B1471399
  · exact B1471403
  · exact B1471407
  · exact B1471411
  · exact B1471415
  · exact B1471419
  · exact B1471423
  · exact B1471427
  · exact B1471431
  · exact B1471435
  · exact B1471439
  · exact B1471443
  · exact B1471447
  · exact B1471451
  · exact B1471455
  · exact B1471459
  · exact B1471463
  · exact B1471467
  · exact B1471471
  · exact B1471475
  · exact B1471479
  · exact B1471483
  · exact B1471487
  · exact B1471491
  · exact B1471495
  · exact B1471499
  · exact B1471503
  · exact B1471507
  · exact B1471511
  · exact B1471515
  · exact B1471519
  · exact B1471523
  · exact B1471527
  · exact B1471531
  · exact B1471535
  · exact B1471539
  · exact B1471543
  · exact B1471547
  · exact B1471551
  · exact B1471555
  · exact B1471559
  · exact B1471563
  · exact B1471567
  · exact B1471571
  · exact B1471575
  · exact B1471579
  · exact B1471583
  · exact B1471587
  · exact B1471591
  · exact B1471595
  · exact B1471599
  · exact B1471603
  · exact B1471607
  · exact B1471611
  · exact B1471615
  · exact B1471619
  · exact B1471623
  · exact B1471627
  · exact B1471631
  · exact B1471635
  · exact B1471639
  · exact B1471643
  · exact B1471647
  · exact B1471651
  · exact B1471655
  · exact B1471659
  · exact B1471663
  · exact B1471667
  · exact B1471671
  · exact B1471675
  · exact B1471679
  · exact B1471683
  · exact B1471687
  · exact B1471691
  · exact B1471695
  · exact B1471699
  · exact B1471703
  · exact B1471707
  · exact B1471711
  · exact B1471715
  · exact B1471719
  · exact B1471723
  · exact B1471727
  · exact B1471731
  · exact B1471735
  · exact B1471739
  · exact B1471743
  · exact B1471747
  · exact B1471751
  · exact B1471755
  · exact B1471759
  · exact B1471763
  · exact B1471767
  · exact B1471771
  · exact B1471775
  · exact B1471779
  · exact B1471783
  · exact B1471787
  · exact B1471791
  · exact B1471795
  · exact B1471799
  · exact B1471803
  · exact B1471807
  · exact B1471811
  · exact B1471815
  · exact B1471819
  · exact B1471823
  · exact B1471827
  · exact B1471831
  · exact B1471835
  · exact B1471839
  · exact B1471843
  · exact B1471847
  · exact B1471851
  · exact B1471855
  · exact B1471859
  · exact B1471863
  · exact B1471867
  · exact B1471871
  · exact B1471875
  · exact B1471879
  · exact B1471883
  · exact B1471887
  · exact B1471891
  · exact B1471895
  · exact B1471899
  · exact B1471903
  · exact B1471907
  · exact B1471911
  · exact B1471915
  · exact B1471919
  · exact B1471923
  · exact B1471927
  · exact B1471931
  · exact B1471935
  · exact B1471939
  · exact B1471943
  · exact B1471947
  · exact B1471951
  · exact B1471955
  · exact B1471959
  · exact B1471963
  · exact B1471967
  · exact B1471971
  · exact B1471975
  · exact B1471979
  · exact B1471983
  · exact B1471987
  · exact B1471991
  · exact B1471995
  · exact B1471999
  · exact B1472003
  · exact B1472007
  · exact B1472011
  · exact B1472015
  · exact B1472019
  · exact B1472023
  · exact B1472027
  · exact B1472031
  · exact B1472035
  · exact B1472039
  · exact B1472043
  · exact B1472047
  · exact B1472051
  · exact B1472055
  · exact B1472059
  · exact B1472063
  · exact B1472067
  · exact B1472071
  · exact B1472075
  · exact B1472079
  · exact B1472083
  · exact B1472087
  · exact B1472091
  · exact B1472095
  · exact B1472099
  · exact B1472103
  · exact B1472107
  · exact B1472111
  · exact B1472115
  · exact B1472119
  · exact B1472123
  · exact B1472127
  · exact B1472131
  · exact B1472135
  · exact B1472139
  · exact B1472143
  · exact B1472147
  · exact B1472151
  · exact B1472155
  · exact B1472159
  · exact B1472163
  · exact B1472167
  · exact B1472171
  · exact B1472175
  · exact B1472179
  · exact B1472183
  · exact B1472187
  · exact B1472191
  · exact B1472195
  · exact B1472199
  · exact B1472203
  · exact B1472207
  · exact B1472211
  · exact B1472215
  · exact B1472219
  · exact B1472223
  · exact B1472227
  · exact B1472231
  · exact B1472235
  · exact B1472239
  · exact B1472243
  · exact B1472247
  · exact B1472251
  · exact B1472255
  · exact B1472259
  · exact B1472263
  · exact B1472267
  · exact B1472271
  · exact B1472275
  · exact B1472279
  · exact B1472283
  · exact B1472287
  · exact B1472291
  · exact B1472295
  · exact B1472299
  · exact B1472303
  · exact B1472307
  · exact B1472311
  · exact B1472315
  · exact B1472319
  · exact B1472323
  · exact B1472327
  · exact B1472331
  · exact B1472335
  · exact B1472339
  · exact B1472343
  · exact B1472347
  · exact B1472351
  · exact B1472355
  · exact B1472359
  · exact B1472363
  · exact B1472367
  · exact B1472371
  · exact B1472375
  · exact B1472379
  · exact B1472383
  · exact B1472387
  · exact B1472391
  · exact B1472395
  · exact B1472399
  · exact B1472403
  · exact B1472407
  · exact B1472411
  · exact B1472415
  · exact B1472419
  · exact B1472423
  · exact B1472427
  · exact B1472431
  · exact B1472435
  · exact B1472439
  · exact B1472443
  · exact B1472447
  · exact B1472451
  · exact B1472455
  · exact B1472459
  · exact B1472463
  · exact B1472467
  · exact B1472471
  · exact B1472475
  · exact B1472479
  · exact B1472483
  · exact B1472487
  · exact B1472491
  · exact B1472495
  · exact B1472499
  · exact B1472503
  · exact B1472507
  · exact B1472511
  · exact B1472515
  · exact B1472519
  · exact B1472523
  · exact B1472527
  · exact B1472531
  · exact B1472535
  · exact B1472539
  · exact B1472543
  · exact B1472547
  · exact B1472551
  · exact B1472555

theorem solution (m : ℕ) (hlo : 1470555 ≤ m) (hhi : m ≤ 1472555) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 367638 ≤ j := by omega
    have hj2 : j ≤ 368138 := by omega
    have hb : Blo 1470555 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
