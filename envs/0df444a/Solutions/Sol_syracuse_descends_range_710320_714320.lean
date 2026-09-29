-- Prove2me | solution 1 for syracuse_descends_range_710320_714320
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:01.538614+00:00
-- url     : https://prove2.me/submissions/37ceb3fe-811f-4075-a895-f1c2ced98b87

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


theorem B1605653 : Blo 710320 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B720985 : Blo 710320 720985 := bbase (se 2 (by rfl) ⟨270369, by rfl⟩ : syracuseStep 720985 = 540739) (by norm_num)
theorem B1605725 : Blo 710320 1605725 := bbase (se 3 (by rfl) ⟨301073, by rfl⟩ : syracuseStep 1605725 = 602147) (by norm_num)
theorem B721001 : Blo 710320 721001 := bbase (se 2 (by rfl) ⟨270375, by rfl⟩ : syracuseStep 721001 = 540751) (by norm_num)
theorem B1605797 : Blo 710320 1605797 := bbase (se 4 (by rfl) ⟨150543, by rfl⟩ : syracuseStep 1605797 = 301087) (by norm_num)
theorem B3604661 : Blo 710320 3604661 := bbase (se 5 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 3604661 = 337937) (by norm_num)
theorem B1016021 : Blo 710320 1016021 := bbase (se 7 (by rfl) ⟨11906, by rfl⟩ : syracuseStep 1016021 = 23813) (by norm_num)
theorem B1605869 : Blo 710320 1605869 := bbase (se 3 (by rfl) ⟨301100, by rfl⟩ : syracuseStep 1605869 = 602201) (by norm_num)
theorem B2162933 : Blo 710320 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1736957 : Blo 710320 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1802533 : Blo 710320 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B1016101 : Blo 710320 1016101 := bbase (se 4 (by rfl) ⟨95259, by rfl⟩ : syracuseStep 1016101 = 190519) (by norm_num)
theorem B1605941 : Blo 710320 1605941 := bbase (se 5 (by rfl) ⟨75278, by rfl⟩ : syracuseStep 1605941 = 150557) (by norm_num)
theorem B1606013 : Blo 710320 1606013 := bbase (se 3 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 1606013 = 602255) (by norm_num)
theorem B1802645 : Blo 710320 1802645 := bbase (se 6 (by rfl) ⟨42249, by rfl⟩ : syracuseStep 1802645 = 84499) (by norm_num)
theorem B1016221 : Blo 710320 1016221 := bbase (se 3 (by rfl) ⟨190541, by rfl⟩ : syracuseStep 1016221 = 381083) (by norm_num)
theorem B1442213 : Blo 710320 1442213 := bbase (se 4 (by rfl) ⟨135207, by rfl⟩ : syracuseStep 1442213 = 270415) (by norm_num)
theorem B1606085 : Blo 710320 1606085 := bbase (se 4 (by rfl) ⟨150570, by rfl⟩ : syracuseStep 1606085 = 301141) (by norm_num)
theorem B1442261 : Blo 710320 1442261 := bbase (se 7 (by rfl) ⟨16901, by rfl⟩ : syracuseStep 1442261 = 33803) (by norm_num)
theorem B1016317 : Blo 710320 1016317 := bbase (se 3 (by rfl) ⟨190559, by rfl⟩ : syracuseStep 1016317 = 381119) (by norm_num)
theorem B1606157 : Blo 710320 1606157 := bbase (se 3 (by rfl) ⟨301154, by rfl⟩ : syracuseStep 1606157 = 602309) (by norm_num)
theorem B1802837 : Blo 710320 1802837 := bbase (se 8 (by rfl) ⟨10563, by rfl⟩ : syracuseStep 1802837 = 21127) (by norm_num)
theorem B1606229 : Blo 710320 1606229 := bbase (se 8 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 1606229 = 18823) (by norm_num)
theorem B721549 : Blo 710320 721549 := bbase (se 3 (by rfl) ⟨135290, by rfl⟩ : syracuseStep 721549 = 270581) (by norm_num)
theorem B1606301 : Blo 710320 1606301 := bbase (se 3 (by rfl) ⟨301181, by rfl⟩ : syracuseStep 1606301 = 602363) (by norm_num)
theorem B721585 : Blo 710320 721585 := bbase (se 2 (by rfl) ⟨270594, by rfl⟩ : syracuseStep 721585 = 541189) (by norm_num)
theorem B1606373 : Blo 710320 1606373 := bbase (se 4 (by rfl) ⟨150597, by rfl⟩ : syracuseStep 1606373 = 301195) (by norm_num)
theorem B1606445 : Blo 710320 1606445 := bbase (se 3 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 1606445 = 602417) (by norm_num)
theorem B1606517 : Blo 710320 1606517 := bbase (se 5 (by rfl) ⟨75305, by rfl⟩ : syracuseStep 1606517 = 150611) (by norm_num)
theorem B1803181 : Blo 710320 1803181 := bbase (se 3 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 1803181 = 676193) (by norm_num)
theorem B1606589 : Blo 710320 1606589 := bbase (se 3 (by rfl) ⟨301235, by rfl⟩ : syracuseStep 1606589 = 602471) (by norm_num)
theorem B721877 : Blo 710320 721877 := bbase (se 7 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 721877 = 16919) (by norm_num)
theorem B1082341 : Blo 710320 1082341 := bbase (se 4 (by rfl) ⟨101469, by rfl⟩ : syracuseStep 1082341 = 202939) (by norm_num)
theorem B1016813 : Blo 710320 1016813 := bbase (se 3 (by rfl) ⟨190652, by rfl⟩ : syracuseStep 1016813 = 381305) (by norm_num)
theorem B1606661 : Blo 710320 1606661 := bbase (se 4 (by rfl) ⟨150624, by rfl⟩ : syracuseStep 1606661 = 301249) (by norm_num)
theorem B1803293 : Blo 710320 1803293 := bbase (se 3 (by rfl) ⟨338117, by rfl⟩ : syracuseStep 1803293 = 676235) (by norm_num)
theorem B1606733 : Blo 710320 1606733 := bbase (se 3 (by rfl) ⟨301262, by rfl⟩ : syracuseStep 1606733 = 602525) (by norm_num)
theorem B1606805 : Blo 710320 1606805 := bbase (se 6 (by rfl) ⟨37659, by rfl⟩ : syracuseStep 1606805 = 75319) (by norm_num)
theorem B1803485 : Blo 710320 1803485 := bbase (se 3 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 1803485 = 676307) (by norm_num)
theorem B1606877 : Blo 710320 1606877 := bbase (se 3 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 1606877 = 602579) (by norm_num)
theorem B722197 : Blo 710320 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B1606949 : Blo 710320 1606949 := bbase (se 4 (by rfl) ⟨150651, by rfl⟩ : syracuseStep 1606949 = 301303) (by norm_num)
theorem B1607021 : Blo 710320 1607021 := bbase (se 3 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 1607021 = 602633) (by norm_num)
theorem B2033045 : Blo 710320 2033045 := bbase (se 6 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 2033045 = 95299) (by norm_num)
theorem B1607093 : Blo 710320 1607093 := bbase (se 5 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 1607093 = 150665) (by norm_num)
theorem B3605957 : Blo 710320 3605957 := bbase (se 4 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 3605957 = 676117) (by norm_num)
theorem B1541605 : Blo 710320 1541605 := bbase (se 4 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 1541605 = 289051) (by norm_num)
theorem B1607165 : Blo 710320 1607165 := bbase (se 3 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 1607165 = 602687) (by norm_num)
theorem B722477 : Blo 710320 722477 := bbase (se 3 (by rfl) ⟨135464, by rfl⟩ : syracuseStep 722477 = 270929) (by norm_num)
theorem B1803829 : Blo 710320 1803829 := bbase (se 5 (by rfl) ⟨84554, by rfl⟩ : syracuseStep 1803829 = 169109) (by norm_num)
theorem B1803941 : Blo 710320 1803941 := bbase (se 4 (by rfl) ⟨169119, by rfl⟩ : syracuseStep 1803941 = 338239) (by norm_num)
theorem B3049157 : Blo 710320 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B24610517 : Blo 710320 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B853789 : Blo 710320 853789 := bbase (se 3 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 853789 = 320171) (by norm_num)
theorem B1804133 : Blo 710320 1804133 := bbase (se 4 (by rfl) ⟨169137, by rfl⟩ : syracuseStep 1804133 = 338275) (by norm_num)
theorem B853885 : Blo 710320 853885 := bbase (se 3 (by rfl) ⟨160103, by rfl⟩ : syracuseStep 853885 = 320207) (by norm_num)
theorem B5408693 : Blo 710320 5408693 := bbase (se 5 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 5408693 = 507065) (by norm_num)
theorem B3049397 : Blo 710320 3049397 := bbase (se 5 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 3049397 = 285881) (by norm_num)
theorem B1804477 : Blo 710320 1804477 := bbase (se 3 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 1804477 = 676679) (by norm_num)
theorem B1804589 : Blo 710320 1804589 := bbase (se 3 (by rfl) ⟨338360, by rfl⟩ : syracuseStep 1804589 = 676721) (by norm_num)
theorem B1804781 : Blo 710320 1804781 := bbase (se 3 (by rfl) ⟨338396, by rfl⟩ : syracuseStep 1804781 = 676793) (by norm_num)
theorem B1739293 : Blo 710320 1739293 := bbase (se 3 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 1739293 = 652235) (by norm_num)
theorem B854669 : Blo 710320 854669 := bbase (se 3 (by rfl) ⟨160250, by rfl⟩ : syracuseStep 854669 = 320501) (by norm_num)
theorem B1280677 : Blo 710320 1280677 := bbase (se 4 (by rfl) ⟨120063, by rfl⟩ : syracuseStep 1280677 = 240127) (by norm_num)
theorem B3607253 : Blo 710320 3607253 := bbase (se 7 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 3607253 = 84545) (by norm_num)
theorem B1805125 : Blo 710320 1805125 := bbase (se 4 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 1805125 = 338461) (by norm_num)
theorem B2886533 : Blo 710320 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B1805237 : Blo 710320 1805237 := bbase (se 5 (by rfl) ⟨84620, by rfl⟩ : syracuseStep 1805237 = 169241) (by norm_num)
theorem B3476405 : Blo 710320 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B854977 : Blo 710320 854977 := bbase (se 2 (by rfl) ⟨320616, by rfl⟩ : syracuseStep 854977 = 641233) (by norm_num)
theorem B4557845 : Blo 710320 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B1805429 : Blo 710320 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B855365 : Blo 710320 855365 := bbase (se 4 (by rfl) ⟨80190, by rfl⟩ : syracuseStep 855365 = 160381) (by norm_num)
theorem B1084853 : Blo 710320 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B1805773 : Blo 710320 1805773 := bbase (se 3 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 1805773 = 677165) (by norm_num)
theorem B1707493 : Blo 710320 1707493 := bbase (se 4 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 1707493 = 320155) (by norm_num)
theorem B1805885 : Blo 710320 1805885 := bbase (se 3 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 1805885 = 677207) (by norm_num)
theorem B1085005 : Blo 710320 1085005 := bbase (se 3 (by rfl) ⟨203438, by rfl⟩ : syracuseStep 1085005 = 406877) (by norm_num)
theorem B855721 : Blo 710320 855721 := bbase (se 2 (by rfl) ⟨320895, by rfl⟩ : syracuseStep 855721 = 641791) (by norm_num)
theorem B2920133 : Blo 710320 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B1806077 : Blo 710320 1806077 := bbase (se 3 (by rfl) ⟨338639, by rfl⟩ : syracuseStep 1806077 = 677279) (by norm_num)
theorem B3608549 : Blo 710320 3608549 := bbase (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) (by norm_num)
theorem B856057 : Blo 710320 856057 := bbase (se 2 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 856057 = 642043) (by norm_num)
theorem B1806421 : Blo 710320 1806421 := bbase (se 8 (by rfl) ⟨10584, by rfl⟩ : syracuseStep 1806421 = 21169) (by norm_num)
theorem B1806533 : Blo 710320 1806533 := bbase (se 4 (by rfl) ⟨169362, by rfl⟩ : syracuseStep 1806533 = 338725) (by norm_num)
theorem B19501397 : Blo 710320 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B1806725 : Blo 710320 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B1216957 : Blo 710320 1216957 := bbase (se 3 (by rfl) ⟨228179, by rfl⟩ : syracuseStep 1216957 = 456359) (by norm_num)
theorem B1446365 : Blo 710320 1446365 := bbase (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) (by norm_num)
theorem B1807069 : Blo 710320 1807069 := bbase (se 3 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 1807069 = 677651) (by norm_num)
theorem B1807181 : Blo 710320 1807181 := bbase (se 3 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 1807181 = 677693) (by norm_num)
theorem B856937 : Blo 710320 856937 := bbase (se 2 (by rfl) ⟨321351, by rfl⟩ : syracuseStep 856937 = 642703) (by norm_num)
theorem B758693 : Blo 710320 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B1348589 : Blo 710320 1348589 := bbase (se 3 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 1348589 = 505721) (by norm_num)
theorem B1807373 : Blo 710320 1807373 := bbase (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) (by norm_num)
theorem B1446989 : Blo 710320 1446989 := bbase (se 3 (by rfl) ⟨271310, by rfl⟩ : syracuseStep 1446989 = 542621) (by norm_num)
theorem B1348741 : Blo 710320 1348741 := bbase (se 4 (by rfl) ⟨126444, by rfl⟩ : syracuseStep 1348741 = 252889) (by norm_num)
theorem B857245 : Blo 710320 857245 := bbase (se 3 (by rfl) ⟨160733, by rfl⟩ : syracuseStep 857245 = 321467) (by norm_num)
theorem B3609845 : Blo 710320 3609845 := bbase (se 5 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 3609845 = 338423) (by norm_num)
theorem B1283365 : Blo 710320 1283365 := bbase (se 4 (by rfl) ⟨120315, by rfl⟩ : syracuseStep 1283365 = 240631) (by norm_num)
theorem B2168149 : Blo 710320 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B759137 : Blo 710320 759137 := bbase (se 2 (by rfl) ⟨284676, by rfl⟩ : syracuseStep 759137 = 569353) (by norm_num)
theorem B1807717 : Blo 710320 1807717 := bbase (se 4 (by rfl) ⟨169473, by rfl⟩ : syracuseStep 1807717 = 338947) (by norm_num)
theorem B1349045 : Blo 710320 1349045 := bbase (se 5 (by rfl) ⟨63236, by rfl⟩ : syracuseStep 1349045 = 126473) (by norm_num)
theorem B2397653 : Blo 710320 2397653 := bbase (se 7 (by rfl) ⟨28097, by rfl⟩ : syracuseStep 2397653 = 56195) (by norm_num)
theorem B1807829 : Blo 710320 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B1218053 : Blo 710320 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1447445 : Blo 710320 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B857629 : Blo 710320 857629 := bbase (se 3 (by rfl) ⟨160805, by rfl⟩ : syracuseStep 857629 = 321611) (by norm_num)
theorem B857633 : Blo 710320 857633 := bbase (se 2 (by rfl) ⟨321612, by rfl⟩ : syracuseStep 857633 = 643225) (by norm_num)
theorem B759385 : Blo 710320 759385 := bbase (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) (by norm_num)
theorem B1808021 : Blo 710320 1808021 := bbase (se 6 (by rfl) ⟨42375, by rfl⟩ : syracuseStep 1808021 = 84751) (by norm_num)
theorem B1218221 : Blo 710320 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B1218277 : Blo 710320 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B6854453 : Blo 710320 6854453 := bbase (se 5 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 6854453 = 642605) (by norm_num)
theorem B1709885 : Blo 710320 1709885 := bbase (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) (by norm_num)
theorem B2398085 : Blo 710320 2398085 := bbase (se 4 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 2398085 = 449641) (by norm_num)
theorem B858037 : Blo 710320 858037 := bbase (se 5 (by rfl) ⟨40220, by rfl⟩ : syracuseStep 858037 = 80441) (by norm_num)
theorem B1710029 : Blo 710320 1710029 := bbase (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) (by norm_num)
theorem B2889701 : Blo 710320 2889701 := bbase (se 4 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 2889701 = 541819) (by norm_num)
theorem B759829 : Blo 710320 759829 := bbase (se 6 (by rfl) ⟨17808, by rfl⟩ : syracuseStep 759829 = 35617) (by norm_num)
theorem B759889 : Blo 710320 759889 := bbase (se 2 (by rfl) ⟨284958, by rfl⟩ : syracuseStep 759889 = 569917) (by norm_num)
theorem B923773 : Blo 710320 923773 := bbase (se 3 (by rfl) ⟨173207, by rfl⟩ : syracuseStep 923773 = 346415) (by norm_num)
theorem B1349797 : Blo 710320 1349797 := bbase (se 4 (by rfl) ⟨126543, by rfl⟩ : syracuseStep 1349797 = 253087) (by norm_num)
theorem B5773589 : Blo 710320 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B2398517 : Blo 710320 2398517 := bbase (se 5 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 2398517 = 224861) (by norm_num)
theorem B1349941 : Blo 710320 1349941 := bbase (se 5 (by rfl) ⟨63278, by rfl⟩ : syracuseStep 1349941 = 126557) (by norm_num)
theorem B760205 : Blo 710320 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B1218989 : Blo 710320 1218989 := bbase (se 3 (by rfl) ⟨228560, by rfl⟩ : syracuseStep 1218989 = 457121) (by norm_num)
theorem B1350101 : Blo 710320 1350101 := bbase (se 7 (by rfl) ⟨15821, by rfl⟩ : syracuseStep 1350101 = 31643) (by norm_num)
theorem B2169317 : Blo 710320 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B3611141 : Blo 710320 3611141 := bbase (se 4 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 3611141 = 677089) (by norm_num)
theorem B6068789 : Blo 710320 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B3414581 : Blo 710320 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B1350245 : Blo 710320 1350245 := bbase (se 4 (by rfl) ⟨126585, by rfl⟩ : syracuseStep 1350245 = 253171) (by norm_num)
theorem B1284749 : Blo 710320 1284749 := bbase (se 3 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 1284749 = 481781) (by norm_num)
theorem B2398949 : Blo 710320 2398949 := bbase (se 4 (by rfl) ⟨224901, by rfl⟩ : syracuseStep 2398949 = 449803) (by norm_num)
theorem B4561717 : Blo 710320 4561717 := bbase (se 5 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 4561717 = 427661) (by norm_num)
theorem B760649 : Blo 710320 760649 := bbase (se 2 (by rfl) ⟨285243, by rfl⟩ : syracuseStep 760649 = 570487) (by norm_num)
theorem B1350533 : Blo 710320 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B760709 : Blo 710320 760709 := bbase (se 4 (by rfl) ⟨71316, by rfl⟩ : syracuseStep 760709 = 142633) (by norm_num)
theorem B760837 : Blo 710320 760837 := bbase (se 4 (by rfl) ⟨71328, by rfl⟩ : syracuseStep 760837 = 142657) (by norm_num)
theorem B1350685 : Blo 710320 1350685 := bbase (se 3 (by rfl) ⟨253253, by rfl⟩ : syracuseStep 1350685 = 506507) (by norm_num)
theorem B1219645 : Blo 710320 1219645 := bbase (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) (by norm_num)
theorem B2399381 : Blo 710320 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B1350989 : Blo 710320 1350989 := bbase (se 3 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 1350989 = 506621) (by norm_num)
theorem B2891173 : Blo 710320 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B761281 : Blo 710320 761281 := bbase (se 2 (by rfl) ⟨285480, by rfl⟩ : syracuseStep 761281 = 570961) (by norm_num)
theorem B4562453 : Blo 710320 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B761401 : Blo 710320 761401 := bbase (se 2 (by rfl) ⟨285525, by rfl⟩ : syracuseStep 761401 = 571051) (by norm_num)
theorem B2399813 : Blo 710320 2399813 := bbase (se 4 (by rfl) ⟨224982, by rfl⟩ : syracuseStep 2399813 = 449965) (by norm_num)
theorem B3612437 : Blo 710320 3612437 := bbase (se 6 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 3612437 = 169333) (by norm_num)
theorem B761653 : Blo 710320 761653 := bbase (se 5 (by rfl) ⟨35702, by rfl⟩ : syracuseStep 761653 = 71405) (by norm_num)
theorem B761657 : Blo 710320 761657 := bbase (se 2 (by rfl) ⟨285621, by rfl⟩ : syracuseStep 761657 = 571243) (by norm_num)
theorem B1712029 : Blo 710320 1712029 := bbase (se 3 (by rfl) ⟨321005, by rfl⟩ : syracuseStep 1712029 = 642011) (by norm_num)
theorem B2400245 : Blo 710320 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B1351741 : Blo 710320 1351741 := bbase (se 3 (by rfl) ⟨253451, by rfl⟩ : syracuseStep 1351741 = 506903) (by norm_num)
theorem B9117845 : Blo 710320 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B1286293 : Blo 710320 1286293 := bbase (se 6 (by rfl) ⟨30147, by rfl⟩ : syracuseStep 1286293 = 60295) (by norm_num)
theorem B1351885 : Blo 710320 1351885 := bbase (se 3 (by rfl) ⟨253478, by rfl⟩ : syracuseStep 1351885 = 506957) (by norm_num)
theorem B2466133 : Blo 710320 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B1352045 : Blo 710320 1352045 := bbase (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) (by norm_num)
theorem B762221 : Blo 710320 762221 := bbase (se 3 (by rfl) ⟨142916, by rfl⟩ : syracuseStep 762221 = 285833) (by norm_num)
theorem B2400677 : Blo 710320 2400677 := bbase (se 4 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 2400677 = 450127) (by norm_num)
theorem B1352189 : Blo 710320 1352189 := bbase (se 3 (by rfl) ⟨253535, by rfl⟩ : syracuseStep 1352189 = 507071) (by norm_num)
theorem B762409 : Blo 710320 762409 := bbase (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) (by norm_num)
theorem B2433653 : Blo 710320 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B2564885 : Blo 710320 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B1352477 : Blo 710320 1352477 := bbase (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) (by norm_num)
theorem B2401109 : Blo 710320 2401109 := bbase (se 9 (by rfl) ⟨7034, by rfl⟩ : syracuseStep 2401109 = 14069) (by norm_num)
theorem B1352629 : Blo 710320 1352629 := bbase (se 5 (by rfl) ⟨63404, by rfl⟩ : syracuseStep 1352629 = 126809) (by norm_num)
theorem B3613733 : Blo 710320 3613733 := bbase (se 4 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 3613733 = 677575) (by norm_num)
theorem B4334741 : Blo 710320 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B2565317 : Blo 710320 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B2172101 : Blo 710320 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B1352933 : Blo 710320 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B2401541 : Blo 710320 2401541 := bbase (se 4 (by rfl) ⟨225144, by rfl⟩ : syracuseStep 2401541 = 450289) (by norm_num)
theorem B1713413 : Blo 710320 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B1713421 : Blo 710320 1713421 := bbase (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) (by norm_num)
theorem B5416469 : Blo 710320 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B2401973 : Blo 710320 2401973 := bbase (se 5 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 2401973 = 225185) (by norm_num)
theorem B2434805 : Blo 710320 2434805 := bbase (se 5 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 2434805 = 228263) (by norm_num)
theorem B1517429 : Blo 710320 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B1353685 : Blo 710320 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B3123173 : Blo 710320 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B1517573 : Blo 710320 1517573 := bbase (se 4 (by rfl) ⟨142272, by rfl⟩ : syracuseStep 1517573 = 284545) (by norm_num)
theorem B3254357 : Blo 710320 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B3418213 : Blo 710320 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B2402405 : Blo 710320 2402405 := bbase (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) (by norm_num)
theorem B1353829 : Blo 710320 1353829 := bbase (se 4 (by rfl) ⟨126921, by rfl⟩ : syracuseStep 1353829 = 253843) (by norm_num)
theorem B1714421 : Blo 710320 1714421 := bbase (se 5 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 1714421 = 160727) (by norm_num)
theorem B1353989 : Blo 710320 1353989 := bbase (se 4 (by rfl) ⟨126936, by rfl⟩ : syracuseStep 1353989 = 253873) (by norm_num)
theorem B3615029 : Blo 710320 3615029 := bbase (se 5 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 3615029 = 338909) (by norm_num)
theorem B1517933 : Blo 710320 1517933 := bbase (se 3 (by rfl) ⟨284612, by rfl⟩ : syracuseStep 1517933 = 569225) (by norm_num)
theorem B1354133 : Blo 710320 1354133 := bbase (se 6 (by rfl) ⟨31737, by rfl⟩ : syracuseStep 1354133 = 63475) (by norm_num)
theorem B2402837 : Blo 710320 2402837 := bbase (se 6 (by rfl) ⟨56316, by rfl⟩ : syracuseStep 2402837 = 112633) (by norm_num)
theorem B731693 : Blo 710320 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B2697893 : Blo 710320 2697893 := bbase (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) (by norm_num)
theorem B1354421 : Blo 710320 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B1354573 : Blo 710320 1354573 := bbase (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) (by norm_num)
theorem B2698181 : Blo 710320 2698181 := bbase (se 4 (by rfl) ⟨252954, by rfl⟩ : syracuseStep 2698181 = 505909) (by norm_num)
theorem B2403269 : Blo 710320 2403269 := bbase (se 4 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 2403269 = 450613) (by norm_num)
theorem B5483477 : Blo 710320 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B1715189 : Blo 710320 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B1354877 : Blo 710320 1354877 := bbase (se 3 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 1354877 = 508079) (by norm_num)
theorem B1518821 : Blo 710320 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B2403701 : Blo 710320 2403701 := bbase (se 5 (by rfl) ⟨112673, by rfl⟩ : syracuseStep 2403701 = 225347) (by norm_num)
theorem B962005 : Blo 710320 962005 := bbase (se 7 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 962005 = 22547) (by norm_num)
theorem B1519069 : Blo 710320 1519069 := bbase (se 3 (by rfl) ⟨284825, by rfl⟩ : syracuseStep 1519069 = 569651) (by norm_num)
theorem B3092213 : Blo 710320 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B2404133 : Blo 710320 2404133 := bbase (se 4 (by rfl) ⟨225387, by rfl⟩ : syracuseStep 2404133 = 450775) (by norm_num)
theorem B1355629 : Blo 710320 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B2895749 : Blo 710320 2895749 := bbase (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) (by norm_num)
theorem B3092357 : Blo 710320 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B1519573 : Blo 710320 1519573 := bbase (se 7 (by rfl) ⟨17807, by rfl⟩ : syracuseStep 1519573 = 35615) (by norm_num)
theorem B1355773 : Blo 710320 1355773 := bbase (se 3 (by rfl) ⟨254207, by rfl⟩ : syracuseStep 1355773 = 508415) (by norm_num)
theorem B1028101 : Blo 710320 1028101 := bbase (se 4 (by rfl) ⟨96384, by rfl⟩ : syracuseStep 1028101 = 192769) (by norm_num)
theorem B2699365 : Blo 710320 2699365 := bbase (se 4 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 2699365 = 506131) (by norm_num)
theorem B1355933 : Blo 710320 1355933 := bbase (se 3 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 1355933 = 508475) (by norm_num)
theorem B2404565 : Blo 710320 2404565 := bbase (se 7 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 2404565 = 56357) (by norm_num)
theorem B1356077 : Blo 710320 1356077 := bbase (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) (by norm_num)
theorem B2699669 : Blo 710320 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B799141 : Blo 710320 799141 := bbase (se 4 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 799141 = 149839) (by norm_num)
theorem B799177 : Blo 710320 799177 := bbase (se 2 (by rfl) ⟨299691, by rfl⟩ : syracuseStep 799177 = 599383) (by norm_num)
theorem B799213 : Blo 710320 799213 := bbase (se 3 (by rfl) ⟨149852, by rfl⟩ : syracuseStep 799213 = 299705) (by norm_num)
theorem B799249 : Blo 710320 799249 := bbase (se 2 (by rfl) ⟨299718, by rfl⟩ : syracuseStep 799249 = 599437) (by norm_num)
theorem B799285 : Blo 710320 799285 := bbase (se 5 (by rfl) ⟨37466, by rfl⟩ : syracuseStep 799285 = 74933) (by norm_num)
theorem B799321 : Blo 710320 799321 := bbase (se 2 (by rfl) ⟨299745, by rfl⟩ : syracuseStep 799321 = 599491) (by norm_num)
theorem B799357 : Blo 710320 799357 := bbase (se 3 (by rfl) ⟨149879, by rfl⟩ : syracuseStep 799357 = 299759) (by norm_num)
theorem B2404997 : Blo 710320 2404997 := bbase (se 4 (by rfl) ⟨225468, by rfl⟩ : syracuseStep 2404997 = 450937) (by norm_num)
theorem B799393 : Blo 710320 799393 := bbase (se 2 (by rfl) ⟨299772, by rfl⟩ : syracuseStep 799393 = 599545) (by norm_num)
theorem B799429 : Blo 710320 799429 := bbase (se 4 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 799429 = 149893) (by norm_num)
theorem B799465 : Blo 710320 799465 := bbase (se 2 (by rfl) ⟨299799, by rfl⟩ : syracuseStep 799465 = 599599) (by norm_num)
theorem B799501 : Blo 710320 799501 := bbase (se 3 (by rfl) ⟨149906, by rfl⟩ : syracuseStep 799501 = 299813) (by norm_num)
theorem B799537 : Blo 710320 799537 := bbase (se 2 (by rfl) ⟨299826, by rfl⟩ : syracuseStep 799537 = 599653) (by norm_num)
theorem B1520461 : Blo 710320 1520461 := bbase (se 3 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 1520461 = 570173) (by norm_num)
theorem B799573 : Blo 710320 799573 := bbase (se 9 (by rfl) ⟨2342, by rfl⟩ : syracuseStep 799573 = 4685) (by norm_num)
theorem B799609 : Blo 710320 799609 := bbase (se 2 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 799609 = 599707) (by norm_num)
theorem B799645 : Blo 710320 799645 := bbase (se 3 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 799645 = 299867) (by norm_num)
theorem B799681 : Blo 710320 799681 := bbase (se 2 (by rfl) ⟨299880, by rfl⟩ : syracuseStep 799681 = 599761) (by norm_num)
theorem B799717 : Blo 710320 799717 := bbase (se 4 (by rfl) ⟨74973, by rfl⟩ : syracuseStep 799717 = 149947) (by norm_num)
theorem B799753 : Blo 710320 799753 := bbase (se 2 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 799753 = 599815) (by norm_num)
theorem B799789 : Blo 710320 799789 := bbase (se 3 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 799789 = 299921) (by norm_num)
theorem B2405429 : Blo 710320 2405429 := bbase (se 5 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 2405429 = 225509) (by norm_num)
theorem B799825 : Blo 710320 799825 := bbase (se 2 (by rfl) ⟨299934, by rfl⟩ : syracuseStep 799825 = 599869) (by norm_num)
theorem B799861 : Blo 710320 799861 := bbase (se 5 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 799861 = 74987) (by norm_num)
theorem B799897 : Blo 710320 799897 := bbase (se 2 (by rfl) ⟨299961, by rfl⟩ : syracuseStep 799897 = 599923) (by norm_num)
theorem B2929829 : Blo 710320 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B799933 : Blo 710320 799933 := bbase (se 3 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 799933 = 299975) (by norm_num)
theorem B799969 : Blo 710320 799969 := bbase (se 2 (by rfl) ⟨299988, by rfl⟩ : syracuseStep 799969 = 599977) (by norm_num)
theorem B800005 : Blo 710320 800005 := bbase (se 4 (by rfl) ⟨75000, by rfl⟩ : syracuseStep 800005 = 150001) (by norm_num)
theorem B800041 : Blo 710320 800041 := bbase (se 2 (by rfl) ⟨300015, by rfl⟩ : syracuseStep 800041 = 600031) (by norm_num)
theorem B1520957 : Blo 710320 1520957 := bbase (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) (by norm_num)
theorem B800077 : Blo 710320 800077 := bbase (se 3 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 800077 = 300029) (by norm_num)
theorem B1848685 : Blo 710320 1848685 := bbase (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) (by norm_num)
theorem B800113 : Blo 710320 800113 := bbase (se 2 (by rfl) ⟨300042, by rfl⟩ : syracuseStep 800113 = 600085) (by norm_num)
theorem B800149 : Blo 710320 800149 := bbase (se 6 (by rfl) ⟨18753, by rfl⟩ : syracuseStep 800149 = 37507) (by norm_num)
theorem B800185 : Blo 710320 800185 := bbase (se 2 (by rfl) ⟨300069, by rfl⟩ : syracuseStep 800185 = 600139) (by norm_num)
theorem B832961 : Blo 710320 832961 := bbase (se 2 (by rfl) ⟨312360, by rfl⟩ : syracuseStep 832961 = 624721) (by norm_num)
theorem B800221 : Blo 710320 800221 := bbase (se 3 (by rfl) ⟨150041, by rfl⟩ : syracuseStep 800221 = 300083) (by norm_num)
theorem B2405861 : Blo 710320 2405861 := bbase (se 4 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 2405861 = 451099) (by norm_num)
theorem B800257 : Blo 710320 800257 := bbase (se 2 (by rfl) ⟨300096, by rfl⟩ : syracuseStep 800257 = 600193) (by norm_num)
theorem B800293 : Blo 710320 800293 := bbase (se 4 (by rfl) ⟨75027, by rfl⟩ : syracuseStep 800293 = 150055) (by norm_num)
theorem B800329 : Blo 710320 800329 := bbase (se 2 (by rfl) ⟨300123, by rfl⟩ : syracuseStep 800329 = 600247) (by norm_num)
theorem B800365 : Blo 710320 800365 := bbase (se 3 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 800365 = 300137) (by norm_num)
theorem B800401 : Blo 710320 800401 := bbase (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) (by norm_num)
theorem B800437 : Blo 710320 800437 := bbase (se 5 (by rfl) ⟨37520, by rfl⟩ : syracuseStep 800437 = 75041) (by norm_num)
theorem B800473 : Blo 710320 800473 := bbase (se 2 (by rfl) ⟨300177, by rfl⟩ : syracuseStep 800473 = 600355) (by norm_num)
theorem B800509 : Blo 710320 800509 := bbase (se 3 (by rfl) ⟨150095, by rfl⟩ : syracuseStep 800509 = 300191) (by norm_num)
theorem B8664853 : Blo 710320 8664853 := bbase (se 6 (by rfl) ⟨203082, by rfl⟩ : syracuseStep 8664853 = 406165) (by norm_num)
theorem B800545 : Blo 710320 800545 := bbase (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) (by norm_num)
theorem B800581 : Blo 710320 800581 := bbase (se 4 (by rfl) ⟨75054, by rfl⟩ : syracuseStep 800581 = 150109) (by norm_num)
theorem B800617 : Blo 710320 800617 := bbase (se 2 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 800617 = 600463) (by norm_num)
theorem B800653 : Blo 710320 800653 := bbase (se 3 (by rfl) ⟨150122, by rfl⟩ : syracuseStep 800653 = 300245) (by norm_num)
theorem B2406293 : Blo 710320 2406293 := bbase (se 6 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 2406293 = 112795) (by norm_num)
theorem B800689 : Blo 710320 800689 := bbase (se 2 (by rfl) ⟨300258, by rfl⟩ : syracuseStep 800689 = 600517) (by norm_num)
theorem B899029 : Blo 710320 899029 := bbase (se 7 (by rfl) ⟨10535, by rfl⟩ : syracuseStep 899029 = 21071) (by norm_num)
theorem B800725 : Blo 710320 800725 := bbase (se 7 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 800725 = 18767) (by norm_num)
theorem B800761 : Blo 710320 800761 := bbase (se 2 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 800761 = 600571) (by norm_num)
theorem B964621 : Blo 710320 964621 := bbase (se 3 (by rfl) ⟨180866, by rfl⟩ : syracuseStep 964621 = 361733) (by norm_num)
theorem B800797 : Blo 710320 800797 := bbase (se 3 (by rfl) ⟨150149, by rfl⟩ : syracuseStep 800797 = 300299) (by norm_num)
theorem B800833 : Blo 710320 800833 := bbase (se 2 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 800833 = 600625) (by norm_num)
theorem B800869 : Blo 710320 800869 := bbase (se 4 (by rfl) ⟨75081, by rfl⟩ : syracuseStep 800869 = 150163) (by norm_num)
theorem B899201 : Blo 710320 899201 := bbase (se 2 (by rfl) ⟨337200, by rfl⟩ : syracuseStep 899201 = 674401) (by norm_num)
theorem B1620101 : Blo 710320 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B800905 : Blo 710320 800905 := bbase (se 2 (by rfl) ⟨300339, by rfl⟩ : syracuseStep 800905 = 600679) (by norm_num)
theorem B800941 : Blo 710320 800941 := bbase (se 3 (by rfl) ⟨150176, by rfl⟩ : syracuseStep 800941 = 300353) (by norm_num)
theorem B1521845 : Blo 710320 1521845 := bbase (se 5 (by rfl) ⟨71336, by rfl⟩ : syracuseStep 1521845 = 142673) (by norm_num)
theorem B899257 : Blo 710320 899257 := bbase (se 2 (by rfl) ⟨337221, by rfl⟩ : syracuseStep 899257 = 674443) (by norm_num)
theorem B800977 : Blo 710320 800977 := bbase (se 2 (by rfl) ⟨300366, by rfl⟩ : syracuseStep 800977 = 600733) (by norm_num)
theorem B801013 : Blo 710320 801013 := bbase (se 5 (by rfl) ⟨37547, by rfl⟩ : syracuseStep 801013 = 75095) (by norm_num)
theorem B899353 : Blo 710320 899353 := bbase (se 2 (by rfl) ⟨337257, by rfl⟩ : syracuseStep 899353 = 674515) (by norm_num)
theorem B801049 : Blo 710320 801049 := bbase (se 2 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 801049 = 600787) (by norm_num)
theorem B1521965 : Blo 710320 1521965 := bbase (se 3 (by rfl) ⟨285368, by rfl⟩ : syracuseStep 1521965 = 570737) (by norm_num)
theorem B801085 : Blo 710320 801085 := bbase (se 3 (by rfl) ⟨150203, by rfl⟩ : syracuseStep 801085 = 300407) (by norm_num)
theorem B2406725 : Blo 710320 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B801121 : Blo 710320 801121 := bbase (se 2 (by rfl) ⟨300420, by rfl⟩ : syracuseStep 801121 = 600841) (by norm_num)
theorem B801157 : Blo 710320 801157 := bbase (se 4 (by rfl) ⟨75108, by rfl⟩ : syracuseStep 801157 = 150217) (by norm_num)
theorem B801193 : Blo 710320 801193 := bbase (se 2 (by rfl) ⟨300447, by rfl⟩ : syracuseStep 801193 = 600895) (by norm_num)
theorem B6076853 : Blo 710320 6076853 := bbase (se 5 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 6076853 = 569705) (by norm_num)
theorem B899525 : Blo 710320 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B801229 : Blo 710320 801229 := bbase (se 3 (by rfl) ⟨150230, by rfl⟩ : syracuseStep 801229 = 300461) (by norm_num)
theorem B2701781 : Blo 710320 2701781 := bbase (se 7 (by rfl) ⟨31661, by rfl⟩ : syracuseStep 2701781 = 63323) (by norm_num)
theorem B801265 : Blo 710320 801265 := bbase (se 2 (by rfl) ⟨300474, by rfl⟩ : syracuseStep 801265 = 600949) (by norm_num)
theorem B899581 : Blo 710320 899581 := bbase (se 3 (by rfl) ⟨168671, by rfl⟩ : syracuseStep 899581 = 337343) (by norm_num)
theorem B3389957 : Blo 710320 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B801301 : Blo 710320 801301 := bbase (se 6 (by rfl) ⟨18780, by rfl⟩ : syracuseStep 801301 = 37561) (by norm_num)
theorem B801337 : Blo 710320 801337 := bbase (se 2 (by rfl) ⟨300501, by rfl⟩ : syracuseStep 801337 = 601003) (by norm_num)
theorem B899677 : Blo 710320 899677 := bbase (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) (by norm_num)
theorem B801373 : Blo 710320 801373 := bbase (se 3 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 801373 = 300515) (by norm_num)
theorem B801409 : Blo 710320 801409 := bbase (se 2 (by rfl) ⟨300528, by rfl⟩ : syracuseStep 801409 = 601057) (by norm_num)
theorem B801445 : Blo 710320 801445 := bbase (se 4 (by rfl) ⟨75135, by rfl⟩ : syracuseStep 801445 = 150271) (by norm_num)
theorem B801481 : Blo 710320 801481 := bbase (se 2 (by rfl) ⟨300555, by rfl⟩ : syracuseStep 801481 = 601111) (by norm_num)
theorem B801517 : Blo 710320 801517 := bbase (se 3 (by rfl) ⟨150284, by rfl⟩ : syracuseStep 801517 = 300569) (by norm_num)
theorem B2702069 : Blo 710320 2702069 := bbase (se 5 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 2702069 = 253319) (by norm_num)
theorem B2407157 : Blo 710320 2407157 := bbase (se 5 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 2407157 = 225671) (by norm_num)
theorem B899849 : Blo 710320 899849 := bbase (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) (by norm_num)
theorem B801553 : Blo 710320 801553 := bbase (se 2 (by rfl) ⟨300582, by rfl⟩ : syracuseStep 801553 = 601165) (by norm_num)
theorem B801589 : Blo 710320 801589 := bbase (se 5 (by rfl) ⟨37574, by rfl⟩ : syracuseStep 801589 = 75149) (by norm_num)
theorem B899905 : Blo 710320 899905 := bbase (se 2 (by rfl) ⟨337464, by rfl⟩ : syracuseStep 899905 = 674929) (by norm_num)
theorem B801625 : Blo 710320 801625 := bbase (se 2 (by rfl) ⟨300609, by rfl⟩ : syracuseStep 801625 = 601219) (by norm_num)
theorem B801661 : Blo 710320 801661 := bbase (se 3 (by rfl) ⟨150311, by rfl⟩ : syracuseStep 801661 = 300623) (by norm_num)
theorem B900001 : Blo 710320 900001 := bbase (se 2 (by rfl) ⟨337500, by rfl⟩ : syracuseStep 900001 = 675001) (by norm_num)
theorem B801697 : Blo 710320 801697 := bbase (se 2 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 801697 = 601273) (by norm_num)
theorem B1522597 : Blo 710320 1522597 := bbase (se 4 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 1522597 = 285487) (by norm_num)
theorem B801733 : Blo 710320 801733 := bbase (se 4 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 801733 = 150325) (by norm_num)
theorem B801769 : Blo 710320 801769 := bbase (se 2 (by rfl) ⟨300663, by rfl⟩ : syracuseStep 801769 = 601327) (by norm_num)
theorem B801805 : Blo 710320 801805 := bbase (se 3 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 801805 = 300677) (by norm_num)
theorem B801841 : Blo 710320 801841 := bbase (se 2 (by rfl) ⟨300690, by rfl⟩ : syracuseStep 801841 = 601381) (by norm_num)
theorem B900173 : Blo 710320 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B801877 : Blo 710320 801877 := bbase (se 8 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 801877 = 9397) (by norm_num)
theorem B801913 : Blo 710320 801913 := bbase (se 2 (by rfl) ⟨300717, by rfl⟩ : syracuseStep 801913 = 601435) (by norm_num)
theorem B900229 : Blo 710320 900229 := bbase (se 4 (by rfl) ⟨84396, by rfl⟩ : syracuseStep 900229 = 168793) (by norm_num)
theorem B801949 : Blo 710320 801949 := bbase (se 3 (by rfl) ⟨150365, by rfl⟩ : syracuseStep 801949 = 300731) (by norm_num)
theorem B2407589 : Blo 710320 2407589 := bbase (se 4 (by rfl) ⟨225711, by rfl⟩ : syracuseStep 2407589 = 451423) (by norm_num)
theorem B801985 : Blo 710320 801985 := bbase (se 2 (by rfl) ⟨300744, by rfl⟩ : syracuseStep 801985 = 601489) (by norm_num)
theorem B900325 : Blo 710320 900325 := bbase (se 4 (by rfl) ⟨84405, by rfl⟩ : syracuseStep 900325 = 168811) (by norm_num)
theorem B802021 : Blo 710320 802021 := bbase (se 4 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 802021 = 150379) (by norm_num)
theorem B802057 : Blo 710320 802057 := bbase (se 2 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 802057 = 601543) (by norm_num)
theorem B802093 : Blo 710320 802093 := bbase (se 3 (by rfl) ⟨150392, by rfl⟩ : syracuseStep 802093 = 300785) (by norm_num)
theorem B802129 : Blo 710320 802129 := bbase (se 2 (by rfl) ⟨300798, by rfl⟩ : syracuseStep 802129 = 601597) (by norm_num)
theorem B11124053 : Blo 710320 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B802165 : Blo 710320 802165 := bbase (se 5 (by rfl) ⟨37601, by rfl⟩ : syracuseStep 802165 = 75203) (by norm_num)
theorem B900497 : Blo 710320 900497 := bbase (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) (by norm_num)
theorem B802201 : Blo 710320 802201 := bbase (se 2 (by rfl) ⟨300825, by rfl⟩ : syracuseStep 802201 = 601651) (by norm_num)
theorem B802237 : Blo 710320 802237 := bbase (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) (by norm_num)
theorem B900553 : Blo 710320 900553 := bbase (se 2 (by rfl) ⟨337707, by rfl⟩ : syracuseStep 900553 = 675415) (by norm_num)
theorem B802273 : Blo 710320 802273 := bbase (se 2 (by rfl) ⟨300852, by rfl⟩ : syracuseStep 802273 = 601705) (by norm_num)
theorem B802309 : Blo 710320 802309 := bbase (se 4 (by rfl) ⟨75216, by rfl⟩ : syracuseStep 802309 = 150433) (by norm_num)
theorem B1621541 : Blo 710320 1621541 := bbase (se 4 (by rfl) ⟨152019, by rfl⟩ : syracuseStep 1621541 = 304039) (by norm_num)
theorem B900649 : Blo 710320 900649 := bbase (se 2 (by rfl) ⟨337743, by rfl⟩ : syracuseStep 900649 = 675487) (by norm_num)
theorem B802345 : Blo 710320 802345 := bbase (se 2 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 802345 = 601759) (by norm_num)
theorem B802381 : Blo 710320 802381 := bbase (se 3 (by rfl) ⟨150446, by rfl⟩ : syracuseStep 802381 = 300893) (by norm_num)
theorem B2408021 : Blo 710320 2408021 := bbase (se 8 (by rfl) ⟨14109, by rfl⟩ : syracuseStep 2408021 = 28219) (by norm_num)
theorem B2637413 : Blo 710320 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B802417 : Blo 710320 802417 := bbase (se 2 (by rfl) ⟨300906, by rfl⟩ : syracuseStep 802417 = 601813) (by norm_num)
theorem B802453 : Blo 710320 802453 := bbase (se 6 (by rfl) ⟨18807, by rfl⟩ : syracuseStep 802453 = 37615) (by norm_num)
theorem B802489 : Blo 710320 802489 := bbase (se 2 (by rfl) ⟨300933, by rfl⟩ : syracuseStep 802489 = 601867) (by norm_num)
theorem B2277077 : Blo 710320 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B900821 : Blo 710320 900821 := bbase (se 7 (by rfl) ⟨10556, by rfl⟩ : syracuseStep 900821 = 21113) (by norm_num)
theorem B802525 : Blo 710320 802525 := bbase (se 3 (by rfl) ⟨150473, by rfl⟩ : syracuseStep 802525 = 300947) (by norm_num)
theorem B802561 : Blo 710320 802561 := bbase (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) (by norm_num)
theorem B900877 : Blo 710320 900877 := bbase (se 3 (by rfl) ⟨168914, by rfl⟩ : syracuseStep 900877 = 337829) (by norm_num)
theorem B6176533 : Blo 710320 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B1523485 : Blo 710320 1523485 := bbase (se 3 (by rfl) ⟨285653, by rfl⟩ : syracuseStep 1523485 = 571307) (by norm_num)
theorem B802597 : Blo 710320 802597 := bbase (se 4 (by rfl) ⟨75243, by rfl⟩ : syracuseStep 802597 = 150487) (by norm_num)
theorem B802633 : Blo 710320 802633 := bbase (se 2 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 802633 = 601975) (by norm_num)
theorem B900973 : Blo 710320 900973 := bbase (se 3 (by rfl) ⟨168932, by rfl⟩ : syracuseStep 900973 = 337865) (by norm_num)
theorem B802669 : Blo 710320 802669 := bbase (se 3 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 802669 = 301001) (by norm_num)
theorem B802705 : Blo 710320 802705 := bbase (se 2 (by rfl) ⟨301014, by rfl⟩ : syracuseStep 802705 = 602029) (by norm_num)
theorem B2703253 : Blo 710320 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B1523605 : Blo 710320 1523605 := bbase (se 6 (by rfl) ⟨35709, by rfl⟩ : syracuseStep 1523605 = 71419) (by norm_num)
theorem B802741 : Blo 710320 802741 := bbase (se 5 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 802741 = 75257) (by norm_num)
theorem B802777 : Blo 710320 802777 := bbase (se 2 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 802777 = 602083) (by norm_num)
theorem B802813 : Blo 710320 802813 := bbase (se 3 (by rfl) ⟨150527, by rfl⟩ : syracuseStep 802813 = 301055) (by norm_num)
theorem B2408453 : Blo 710320 2408453 := bbase (se 4 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 2408453 = 451585) (by norm_num)
theorem B5783573 : Blo 710320 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B901145 : Blo 710320 901145 := bbase (se 2 (by rfl) ⟨337929, by rfl⟩ : syracuseStep 901145 = 675859) (by norm_num)
theorem B802849 : Blo 710320 802849 := bbase (se 2 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 802849 = 602137) (by norm_num)
theorem B802885 : Blo 710320 802885 := bbase (se 4 (by rfl) ⟨75270, by rfl⟩ : syracuseStep 802885 = 150541) (by norm_num)
theorem B901201 : Blo 710320 901201 := bbase (se 2 (by rfl) ⟨337950, by rfl⟩ : syracuseStep 901201 = 675901) (by norm_num)
theorem B802921 : Blo 710320 802921 := bbase (se 2 (by rfl) ⟨301095, by rfl⟩ : syracuseStep 802921 = 602191) (by norm_num)
theorem B802957 : Blo 710320 802957 := bbase (se 3 (by rfl) ⟨150554, by rfl⟩ : syracuseStep 802957 = 301109) (by norm_num)
theorem B1523861 : Blo 710320 1523861 := bbase (se 6 (by rfl) ⟨35715, by rfl⟩ : syracuseStep 1523861 = 71431) (by norm_num)
theorem B901297 : Blo 710320 901297 := bbase (se 2 (by rfl) ⟨337986, by rfl⟩ : syracuseStep 901297 = 675973) (by norm_num)
theorem B802993 : Blo 710320 802993 := bbase (se 2 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 802993 = 602245) (by norm_num)
theorem B6832309 : Blo 710320 6832309 := bbase (se 5 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 6832309 = 640529) (by norm_num)
theorem B2703557 : Blo 710320 2703557 := bbase (se 4 (by rfl) ⟨253458, by rfl⟩ : syracuseStep 2703557 = 506917) (by norm_num)
theorem B803029 : Blo 710320 803029 := bbase (se 7 (by rfl) ⟨9410, by rfl⟩ : syracuseStep 803029 = 18821) (by norm_num)
theorem B803065 : Blo 710320 803065 := bbase (se 2 (by rfl) ⟨301149, by rfl⟩ : syracuseStep 803065 = 602299) (by norm_num)
theorem B803101 : Blo 710320 803101 := bbase (se 3 (by rfl) ⟨150581, by rfl⟩ : syracuseStep 803101 = 301163) (by norm_num)
theorem B803137 : Blo 710320 803137 := bbase (se 2 (by rfl) ⟨301176, by rfl⟩ : syracuseStep 803137 = 602353) (by norm_num)
theorem B901469 : Blo 710320 901469 := bbase (se 3 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 901469 = 338051) (by norm_num)
theorem B803173 : Blo 710320 803173 := bbase (se 4 (by rfl) ⟨75297, by rfl⟩ : syracuseStep 803173 = 150595) (by norm_num)
theorem B803209 : Blo 710320 803209 := bbase (se 2 (by rfl) ⟨301203, by rfl⟩ : syracuseStep 803209 = 602407) (by norm_num)
theorem B901525 : Blo 710320 901525 := bbase (se 6 (by rfl) ⟨21129, by rfl⟩ : syracuseStep 901525 = 42259) (by norm_num)
theorem B803245 : Blo 710320 803245 := bbase (se 3 (by rfl) ⟨150608, by rfl⟩ : syracuseStep 803245 = 301217) (by norm_num)
theorem B2408885 : Blo 710320 2408885 := bbase (se 5 (by rfl) ⟨112916, by rfl⟩ : syracuseStep 2408885 = 225833) (by norm_num)
theorem B803281 : Blo 710320 803281 := bbase (se 2 (by rfl) ⟨301230, by rfl⟩ : syracuseStep 803281 = 602461) (by norm_num)
theorem B4047317 : Blo 710320 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B1851869 : Blo 710320 1851869 := bbase (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) (by norm_num)
theorem B901621 : Blo 710320 901621 := bbase (se 5 (by rfl) ⟨42263, by rfl⟩ : syracuseStep 901621 = 84527) (by norm_num)
theorem B803317 : Blo 710320 803317 := bbase (se 5 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 803317 = 75311) (by norm_num)
theorem B1065485 : Blo 710320 1065485 := bbase (se 3 (by rfl) ⟨199778, by rfl⟩ : syracuseStep 1065485 = 399557) (by norm_num)
theorem B6242837 : Blo 710320 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B803353 : Blo 710320 803353 := bbase (se 2 (by rfl) ⟨301257, by rfl⟩ : syracuseStep 803353 = 602515) (by norm_num)
theorem B1065509 : Blo 710320 1065509 := bbase (se 4 (by rfl) ⟨99891, by rfl⟩ : syracuseStep 1065509 = 199783) (by norm_num)
theorem B1065533 : Blo 710320 1065533 := bbase (se 3 (by rfl) ⟨199787, by rfl⟩ : syracuseStep 1065533 = 399575) (by norm_num)
theorem B803389 : Blo 710320 803389 := bbase (se 3 (by rfl) ⟨150635, by rfl⟩ : syracuseStep 803389 = 301271) (by norm_num)
theorem B1065557 : Blo 710320 1065557 := bbase (se 8 (by rfl) ⟨6243, by rfl⟩ : syracuseStep 1065557 = 12487) (by norm_num)
theorem B836185 : Blo 710320 836185 := bbase (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) (by norm_num)
theorem B803425 : Blo 710320 803425 := bbase (se 2 (by rfl) ⟨301284, by rfl⟩ : syracuseStep 803425 = 602569) (by norm_num)
theorem B2277989 : Blo 710320 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B1065581 : Blo 710320 1065581 := bbase (se 3 (by rfl) ⟨199796, by rfl⟩ : syracuseStep 1065581 = 399593) (by norm_num)
theorem B1065605 : Blo 710320 1065605 := bbase (se 4 (by rfl) ⟨99900, by rfl⟩ : syracuseStep 1065605 = 199801) (by norm_num)
theorem B803461 : Blo 710320 803461 := bbase (se 4 (by rfl) ⟨75324, by rfl⟩ : syracuseStep 803461 = 150649) (by norm_num)
theorem B1065629 : Blo 710320 1065629 := bbase (se 3 (by rfl) ⟨199805, by rfl⟩ : syracuseStep 1065629 = 399611) (by norm_num)
theorem B901793 : Blo 710320 901793 := bbase (se 2 (by rfl) ⟨338172, by rfl⟩ : syracuseStep 901793 = 676345) (by norm_num)
theorem B2507429 : Blo 710320 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B803497 : Blo 710320 803497 := bbase (se 2 (by rfl) ⟨301311, by rfl⟩ : syracuseStep 803497 = 602623) (by norm_num)
theorem B1065653 : Blo 710320 1065653 := bbase (se 5 (by rfl) ⟨49952, by rfl⟩ : syracuseStep 1065653 = 99905) (by norm_num)
theorem B1065677 : Blo 710320 1065677 := bbase (se 3 (by rfl) ⟨199814, by rfl⟩ : syracuseStep 1065677 = 399629) (by norm_num)
theorem B803533 : Blo 710320 803533 := bbase (se 3 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 803533 = 301325) (by norm_num)
theorem B901849 : Blo 710320 901849 := bbase (se 2 (by rfl) ⟨338193, by rfl⟩ : syracuseStep 901849 = 676387) (by norm_num)
theorem B1065701 : Blo 710320 1065701 := bbase (se 4 (by rfl) ⟨99909, by rfl⟩ : syracuseStep 1065701 = 199819) (by norm_num)
theorem B3424997 : Blo 710320 3424997 := bbase (se 4 (by rfl) ⟨321093, by rfl⟩ : syracuseStep 3424997 = 642187) (by norm_num)
theorem B803569 : Blo 710320 803569 := bbase (se 2 (by rfl) ⟨301338, by rfl⟩ : syracuseStep 803569 = 602677) (by norm_num)
theorem B1065725 : Blo 710320 1065725 := bbase (se 3 (by rfl) ⟨199823, by rfl⟩ : syracuseStep 1065725 = 399647) (by norm_num)
theorem B1065749 : Blo 710320 1065749 := bbase (se 6 (by rfl) ⟨24978, by rfl⟩ : syracuseStep 1065749 = 49957) (by norm_num)
theorem B803605 : Blo 710320 803605 := bbase (se 6 (by rfl) ⟨18834, by rfl⟩ : syracuseStep 803605 = 37669) (by norm_num)
theorem B1065773 : Blo 710320 1065773 := bbase (se 3 (by rfl) ⟨199832, by rfl⟩ : syracuseStep 1065773 = 399665) (by norm_num)
theorem B901945 : Blo 710320 901945 := bbase (se 2 (by rfl) ⟨338229, by rfl⟩ : syracuseStep 901945 = 676459) (by norm_num)
theorem B1065797 : Blo 710320 1065797 := bbase (se 4 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 1065797 = 199837) (by norm_num)
theorem B1065821 : Blo 710320 1065821 := bbase (se 3 (by rfl) ⟨199841, by rfl⟩ : syracuseStep 1065821 = 399683) (by norm_num)
theorem B2409317 : Blo 710320 2409317 := bbase (se 4 (by rfl) ⟨225873, by rfl⟩ : syracuseStep 2409317 = 451747) (by norm_num)
theorem B1065845 : Blo 710320 1065845 := bbase (se 5 (by rfl) ⟨49961, by rfl⟩ : syracuseStep 1065845 = 99923) (by norm_num)
theorem B1065869 : Blo 710320 1065869 := bbase (se 3 (by rfl) ⟨199850, by rfl⟩ : syracuseStep 1065869 = 399701) (by norm_num)
theorem B1065893 : Blo 710320 1065893 := bbase (se 4 (by rfl) ⟨99927, by rfl⟩ : syracuseStep 1065893 = 199855) (by norm_num)
theorem B1065917 : Blo 710320 1065917 := bbase (se 3 (by rfl) ⟨199859, by rfl⟩ : syracuseStep 1065917 = 399719) (by norm_num)
theorem B1065941 : Blo 710320 1065941 := bbase (se 7 (by rfl) ⟨12491, by rfl⟩ : syracuseStep 1065941 = 24983) (by norm_num)
theorem B902117 : Blo 710320 902117 := bbase (se 4 (by rfl) ⟨84573, by rfl⟩ : syracuseStep 902117 = 169147) (by norm_num)
theorem B1065965 : Blo 710320 1065965 := bbase (se 3 (by rfl) ⟨199868, by rfl⟩ : syracuseStep 1065965 = 399737) (by norm_num)
theorem B1065989 : Blo 710320 1065989 := bbase (se 4 (by rfl) ⟨99936, by rfl⟩ : syracuseStep 1065989 = 199873) (by norm_num)
theorem B1524749 : Blo 710320 1524749 := bbase (se 3 (by rfl) ⟨285890, by rfl⟩ : syracuseStep 1524749 = 571781) (by norm_num)
theorem B1066013 : Blo 710320 1066013 := bbase (se 3 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 1066013 = 399755) (by norm_num)
theorem B902173 : Blo 710320 902173 := bbase (se 3 (by rfl) ⟨169157, by rfl⟩ : syracuseStep 902173 = 338315) (by norm_num)
theorem B1066037 : Blo 710320 1066037 := bbase (se 5 (by rfl) ⟨49970, by rfl⟩ : syracuseStep 1066037 = 99941) (by norm_num)
theorem B1066061 : Blo 710320 1066061 := bbase (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) (by norm_num)
theorem B1066085 : Blo 710320 1066085 := bbase (se 4 (by rfl) ⟨99945, by rfl⟩ : syracuseStep 1066085 = 199891) (by norm_num)
theorem B5424245 : Blo 710320 5424245 := bbase (se 5 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 5424245 = 508523) (by norm_num)
theorem B1066109 : Blo 710320 1066109 := bbase (se 3 (by rfl) ⟨199895, by rfl⟩ : syracuseStep 1066109 = 399791) (by norm_num)
theorem B902269 : Blo 710320 902269 := bbase (se 3 (by rfl) ⟨169175, by rfl⟩ : syracuseStep 902269 = 338351) (by norm_num)
theorem B1066133 : Blo 710320 1066133 := bbase (se 6 (by rfl) ⟨24987, by rfl⟩ : syracuseStep 1066133 = 49975) (by norm_num)
theorem B2573477 : Blo 710320 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B1066157 : Blo 710320 1066157 := bbase (se 3 (by rfl) ⟨199904, by rfl⟩ : syracuseStep 1066157 = 399809) (by norm_num)
theorem B1066181 : Blo 710320 1066181 := bbase (se 4 (by rfl) ⟨99954, by rfl⟩ : syracuseStep 1066181 = 199909) (by norm_num)
theorem B1066205 : Blo 710320 1066205 := bbase (se 3 (by rfl) ⟨199913, by rfl⟩ : syracuseStep 1066205 = 399827) (by norm_num)
theorem B1066229 : Blo 710320 1066229 := bbase (se 5 (by rfl) ⟨49979, by rfl⟩ : syracuseStep 1066229 = 99959) (by norm_num)
theorem B1524989 : Blo 710320 1524989 := bbase (se 3 (by rfl) ⟨285935, by rfl⟩ : syracuseStep 1524989 = 571871) (by norm_num)
theorem B1066253 : Blo 710320 1066253 := bbase (se 3 (by rfl) ⟨199922, by rfl⟩ : syracuseStep 1066253 = 399845) (by norm_num)
theorem B2409749 : Blo 710320 2409749 := bbase (se 6 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 2409749 = 112957) (by norm_num)
theorem B1066277 : Blo 710320 1066277 := bbase (se 4 (by rfl) ⟨99963, by rfl⟩ : syracuseStep 1066277 = 199927) (by norm_num)
theorem B902441 : Blo 710320 902441 := bbase (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) (by norm_num)
theorem B2573621 : Blo 710320 2573621 := bbase (se 5 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 2573621 = 241277) (by norm_num)
theorem B1066301 : Blo 710320 1066301 := bbase (se 3 (by rfl) ⟨199931, by rfl⟩ : syracuseStep 1066301 = 399863) (by norm_num)
theorem B1066325 : Blo 710320 1066325 := bbase (se 12 (by rfl) ⟨390, by rfl⟩ : syracuseStep 1066325 = 781) (by norm_num)
theorem B902497 : Blo 710320 902497 := bbase (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) (by norm_num)
theorem B1066349 : Blo 710320 1066349 := bbase (se 3 (by rfl) ⟨199940, by rfl⟩ : syracuseStep 1066349 = 399881) (by norm_num)
theorem B1066373 : Blo 710320 1066373 := bbase (se 4 (by rfl) ⟨99972, by rfl⟩ : syracuseStep 1066373 = 199945) (by norm_num)
theorem B1066397 : Blo 710320 1066397 := bbase (se 3 (by rfl) ⟨199949, by rfl⟩ : syracuseStep 1066397 = 399899) (by norm_num)
theorem B1066421 : Blo 710320 1066421 := bbase (se 5 (by rfl) ⟨49988, by rfl⟩ : syracuseStep 1066421 = 99977) (by norm_num)
theorem B902593 : Blo 710320 902593 := bbase (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) (by norm_num)
theorem B1623493 : Blo 710320 1623493 := bbase (se 4 (by rfl) ⟨152202, by rfl⟩ : syracuseStep 1623493 = 304405) (by norm_num)
theorem B1066445 : Blo 710320 1066445 := bbase (se 3 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 1066445 = 399917) (by norm_num)
theorem B1066469 : Blo 710320 1066469 := bbase (se 4 (by rfl) ⟨99981, by rfl⟩ : syracuseStep 1066469 = 199963) (by norm_num)
theorem B1066493 : Blo 710320 1066493 := bbase (se 3 (by rfl) ⟨199967, by rfl⟩ : syracuseStep 1066493 = 399935) (by norm_num)
theorem B1066517 : Blo 710320 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B1066541 : Blo 710320 1066541 := bbase (se 3 (by rfl) ⟨199976, by rfl⟩ : syracuseStep 1066541 = 399953) (by norm_num)
theorem B1066565 : Blo 710320 1066565 := bbase (se 4 (by rfl) ⟨99990, by rfl⟩ : syracuseStep 1066565 = 199981) (by norm_num)
theorem B1066589 : Blo 710320 1066589 := bbase (se 3 (by rfl) ⟨199985, by rfl⟩ : syracuseStep 1066589 = 399971) (by norm_num)
theorem B902765 : Blo 710320 902765 := bbase (se 3 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 902765 = 338537) (by norm_num)
theorem B4048501 : Blo 710320 4048501 := bbase (se 5 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 4048501 = 379547) (by norm_num)
theorem B1066613 : Blo 710320 1066613 := bbase (se 5 (by rfl) ⟨49997, by rfl⟩ : syracuseStep 1066613 = 99995) (by norm_num)
theorem B1066637 : Blo 710320 1066637 := bbase (se 3 (by rfl) ⟨199994, by rfl⟩ : syracuseStep 1066637 = 399989) (by norm_num)
theorem B1066661 : Blo 710320 1066661 := bbase (se 4 (by rfl) ⟨99999, by rfl⟩ : syracuseStep 1066661 = 199999) (by norm_num)
theorem B902821 : Blo 710320 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B1066685 : Blo 710320 1066685 := bbase (se 3 (by rfl) ⟨200003, by rfl⟩ : syracuseStep 1066685 = 400007) (by norm_num)
theorem B2410181 : Blo 710320 2410181 := bbase (se 4 (by rfl) ⟨225954, by rfl⟩ : syracuseStep 2410181 = 451909) (by norm_num)
theorem B1066709 : Blo 710320 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B1066733 : Blo 710320 1066733 := bbase (se 3 (by rfl) ⟨200012, by rfl⟩ : syracuseStep 1066733 = 400025) (by norm_num)
theorem B1525493 : Blo 710320 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B1525501 : Blo 710320 1525501 := bbase (se 3 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 1525501 = 572063) (by norm_num)
theorem B1066757 : Blo 710320 1066757 := bbase (se 4 (by rfl) ⟨100008, by rfl⟩ : syracuseStep 1066757 = 200017) (by norm_num)
theorem B902917 : Blo 710320 902917 := bbase (se 4 (by rfl) ⟨84648, by rfl⟩ : syracuseStep 902917 = 169297) (by norm_num)
theorem B2443013 : Blo 710320 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B1066781 : Blo 710320 1066781 := bbase (se 3 (by rfl) ⟨200021, by rfl⟩ : syracuseStep 1066781 = 400043) (by norm_num)
theorem B1066805 : Blo 710320 1066805 := bbase (se 5 (by rfl) ⟨50006, by rfl⟩ : syracuseStep 1066805 = 100013) (by norm_num)
theorem B1066829 : Blo 710320 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B1066853 : Blo 710320 1066853 := bbase (se 4 (by rfl) ⟨100017, by rfl⟩ : syracuseStep 1066853 = 200035) (by norm_num)
theorem B1066877 : Blo 710320 1066877 := bbase (se 3 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 1066877 = 400079) (by norm_num)
theorem B1066901 : Blo 710320 1066901 := bbase (se 6 (by rfl) ⟨25005, by rfl⟩ : syracuseStep 1066901 = 50011) (by norm_num)
theorem B2279333 : Blo 710320 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B1066925 : Blo 710320 1066925 := bbase (se 3 (by rfl) ⟨200048, by rfl⟩ : syracuseStep 1066925 = 400097) (by norm_num)
theorem B903089 : Blo 710320 903089 := bbase (se 2 (by rfl) ⟨338658, by rfl⟩ : syracuseStep 903089 = 677317) (by norm_num)
theorem B1066949 : Blo 710320 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B1066973 : Blo 710320 1066973 := bbase (se 3 (by rfl) ⟨200057, by rfl⟩ : syracuseStep 1066973 = 400115) (by norm_num)
theorem B903145 : Blo 710320 903145 := bbase (se 2 (by rfl) ⟨338679, by rfl⟩ : syracuseStep 903145 = 677359) (by norm_num)
theorem B1066997 : Blo 710320 1066997 := bbase (se 5 (by rfl) ⟨50015, by rfl⟩ : syracuseStep 1066997 = 100031) (by norm_num)
theorem B1067021 : Blo 710320 1067021 := bbase (se 3 (by rfl) ⟨200066, by rfl⟩ : syracuseStep 1067021 = 400133) (by norm_num)
theorem B1067045 : Blo 710320 1067045 := bbase (se 4 (by rfl) ⟨100035, by rfl⟩ : syracuseStep 1067045 = 200071) (by norm_num)
theorem B3655733 : Blo 710320 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B1067069 : Blo 710320 1067069 := bbase (se 3 (by rfl) ⟨200075, by rfl⟩ : syracuseStep 1067069 = 400151) (by norm_num)
theorem B903241 : Blo 710320 903241 := bbase (se 2 (by rfl) ⟨338715, by rfl⟩ : syracuseStep 903241 = 677431) (by norm_num)
theorem B1067093 : Blo 710320 1067093 := bbase (se 8 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 1067093 = 12505) (by norm_num)
theorem B1067117 : Blo 710320 1067117 := bbase (se 3 (by rfl) ⟨200084, by rfl⟩ : syracuseStep 1067117 = 400169) (by norm_num)
theorem B3426421 : Blo 710320 3426421 := bbase (se 5 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 3426421 = 321227) (by norm_num)
theorem B2410613 : Blo 710320 2410613 := bbase (se 5 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 2410613 = 225995) (by norm_num)
theorem B1067141 : Blo 710320 1067141 := bbase (se 4 (by rfl) ⟨100044, by rfl⟩ : syracuseStep 1067141 = 200089) (by norm_num)
theorem B1067165 : Blo 710320 1067165 := bbase (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) (by norm_num)
theorem B1067189 : Blo 710320 1067189 := bbase (se 5 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 1067189 = 100049) (by norm_num)
theorem B1067213 : Blo 710320 1067213 := bbase (se 3 (by rfl) ⟨200102, by rfl⟩ : syracuseStep 1067213 = 400205) (by norm_num)
theorem B1067237 : Blo 710320 1067237 := bbase (se 4 (by rfl) ⟨100053, by rfl⟩ : syracuseStep 1067237 = 200107) (by norm_num)
theorem B903413 : Blo 710320 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B1067261 : Blo 710320 1067261 := bbase (se 3 (by rfl) ⟨200111, by rfl⟩ : syracuseStep 1067261 = 400223) (by norm_num)
theorem B2705669 : Blo 710320 2705669 := bbase (se 4 (by rfl) ⟨253656, by rfl⟩ : syracuseStep 2705669 = 507313) (by norm_num)
theorem B1067285 : Blo 710320 1067285 := bbase (se 6 (by rfl) ⟨25014, by rfl⟩ : syracuseStep 1067285 = 50029) (by norm_num)
theorem B1067309 : Blo 710320 1067309 := bbase (se 3 (by rfl) ⟨200120, by rfl⟩ : syracuseStep 1067309 = 400241) (by norm_num)
theorem B903469 : Blo 710320 903469 := bbase (se 3 (by rfl) ⟨169400, by rfl⟩ : syracuseStep 903469 = 338801) (by norm_num)
theorem B1067333 : Blo 710320 1067333 := bbase (se 4 (by rfl) ⟨100062, by rfl⟩ : syracuseStep 1067333 = 200125) (by norm_num)
theorem B7686485 : Blo 710320 7686485 := bbase (se 10 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 7686485 = 22519) (by norm_num)
theorem B1067357 : Blo 710320 1067357 := bbase (se 3 (by rfl) ⟨200129, by rfl⟩ : syracuseStep 1067357 = 400259) (by norm_num)
theorem B1067381 : Blo 710320 1067381 := bbase (se 5 (by rfl) ⟨50033, by rfl⟩ : syracuseStep 1067381 = 100067) (by norm_num)
theorem B1067405 : Blo 710320 1067405 := bbase (se 3 (by rfl) ⟨200138, by rfl⟩ : syracuseStep 1067405 = 400277) (by norm_num)
theorem B903565 : Blo 710320 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B1067429 : Blo 710320 1067429 := bbase (se 4 (by rfl) ⟨100071, by rfl⟩ : syracuseStep 1067429 = 200143) (by norm_num)
theorem B1067453 : Blo 710320 1067453 := bbase (se 3 (by rfl) ⟨200147, by rfl⟩ : syracuseStep 1067453 = 400295) (by norm_num)
theorem B1067477 : Blo 710320 1067477 := bbase (se 7 (by rfl) ⟨12509, by rfl⟩ : syracuseStep 1067477 = 25019) (by norm_num)
theorem B1067501 : Blo 710320 1067501 := bbase (se 3 (by rfl) ⟨200156, by rfl⟩ : syracuseStep 1067501 = 400313) (by norm_num)
theorem B4573685 : Blo 710320 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B1067525 : Blo 710320 1067525 := bbase (se 4 (by rfl) ⟨100080, by rfl⟩ : syracuseStep 1067525 = 200161) (by norm_num)
theorem B1067549 : Blo 710320 1067549 := bbase (se 3 (by rfl) ⟨200165, by rfl⟩ : syracuseStep 1067549 = 400331) (by norm_num)
theorem B2705957 : Blo 710320 2705957 := bbase (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) (by norm_num)
theorem B1067573 : Blo 710320 1067573 := bbase (se 5 (by rfl) ⟨50042, by rfl⟩ : syracuseStep 1067573 = 100085) (by norm_num)
theorem B5130805 : Blo 710320 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B903737 : Blo 710320 903737 := bbase (se 2 (by rfl) ⟨338901, by rfl⟩ : syracuseStep 903737 = 677803) (by norm_num)
theorem B1067597 : Blo 710320 1067597 := bbase (se 3 (by rfl) ⟨200174, by rfl⟩ : syracuseStep 1067597 = 400349) (by norm_num)
theorem B1198685 : Blo 710320 1198685 := bbase (se 3 (by rfl) ⟨224753, by rfl⟩ : syracuseStep 1198685 = 449507) (by norm_num)
theorem B1067621 : Blo 710320 1067621 := bbase (se 4 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 1067621 = 200179) (by norm_num)
theorem B903793 : Blo 710320 903793 := bbase (se 2 (by rfl) ⟨338922, by rfl⟩ : syracuseStep 903793 = 677845) (by norm_num)
theorem B1067645 : Blo 710320 1067645 := bbase (se 3 (by rfl) ⟨200183, by rfl⟩ : syracuseStep 1067645 = 400367) (by norm_num)
theorem B1067669 : Blo 710320 1067669 := bbase (se 6 (by rfl) ⟨25023, by rfl⟩ : syracuseStep 1067669 = 50047) (by norm_num)
theorem B1067693 : Blo 710320 1067693 := bbase (se 3 (by rfl) ⟨200192, by rfl⟩ : syracuseStep 1067693 = 400385) (by norm_num)
theorem B1067717 : Blo 710320 1067717 := bbase (se 4 (by rfl) ⟨100098, by rfl⟩ : syracuseStep 1067717 = 200197) (by norm_num)
theorem B903889 : Blo 710320 903889 := bbase (se 2 (by rfl) ⟨338958, by rfl⟩ : syracuseStep 903889 = 677917) (by norm_num)
theorem B1198813 : Blo 710320 1198813 := bbase (se 3 (by rfl) ⟨224777, by rfl⟩ : syracuseStep 1198813 = 449555) (by norm_num)
theorem B1067741 : Blo 710320 1067741 := bbase (se 3 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 1067741 = 400403) (by norm_num)
theorem B1854181 : Blo 710320 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B1067765 : Blo 710320 1067765 := bbase (se 5 (by rfl) ⟨50051, by rfl⟩ : syracuseStep 1067765 = 100103) (by norm_num)
theorem B1067789 : Blo 710320 1067789 := bbase (se 3 (by rfl) ⟨200210, by rfl⟩ : syracuseStep 1067789 = 400421) (by norm_num)
theorem B1067813 : Blo 710320 1067813 := bbase (se 4 (by rfl) ⟨100107, by rfl⟩ : syracuseStep 1067813 = 200215) (by norm_num)
theorem B1198901 : Blo 710320 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B1067837 : Blo 710320 1067837 := bbase (se 3 (by rfl) ⟨200219, by rfl⟩ : syracuseStep 1067837 = 400439) (by norm_num)
theorem B1067861 : Blo 710320 1067861 := bbase (se 9 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 1067861 = 6257) (by norm_num)
theorem B1067885 : Blo 710320 1067885 := bbase (se 3 (by rfl) ⟨200228, by rfl⟩ : syracuseStep 1067885 = 400457) (by norm_num)
theorem B904061 : Blo 710320 904061 := bbase (se 3 (by rfl) ⟨169511, by rfl⟩ : syracuseStep 904061 = 339023) (by norm_num)
theorem B1067909 : Blo 710320 1067909 := bbase (se 4 (by rfl) ⟨100116, by rfl⟩ : syracuseStep 1067909 = 200233) (by norm_num)
theorem B1067933 : Blo 710320 1067933 := bbase (se 3 (by rfl) ⟨200237, by rfl⟩ : syracuseStep 1067933 = 400475) (by norm_num)
theorem B1199029 : Blo 710320 1199029 := bbase (se 5 (by rfl) ⟨56204, by rfl⟩ : syracuseStep 1199029 = 112409) (by norm_num)
theorem B1067957 : Blo 710320 1067957 := bbase (se 5 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 1067957 = 100121) (by norm_num)
theorem B1067981 : Blo 710320 1067981 := bbase (se 3 (by rfl) ⟨200246, by rfl⟩ : syracuseStep 1067981 = 400493) (by norm_num)
theorem B1068005 : Blo 710320 1068005 := bbase (se 4 (by rfl) ⟨100125, by rfl⟩ : syracuseStep 1068005 = 200251) (by norm_num)
theorem B1068029 : Blo 710320 1068029 := bbase (se 3 (by rfl) ⟨200255, by rfl⟩ : syracuseStep 1068029 = 400511) (by norm_num)
theorem B1199117 : Blo 710320 1199117 := bbase (se 3 (by rfl) ⟨224834, by rfl⟩ : syracuseStep 1199117 = 449669) (by norm_num)
theorem B12471317 : Blo 710320 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B1068053 : Blo 710320 1068053 := bbase (se 6 (by rfl) ⟨25032, by rfl⟩ : syracuseStep 1068053 = 50065) (by norm_num)
theorem B1068077 : Blo 710320 1068077 := bbase (se 3 (by rfl) ⟨200264, by rfl⟩ : syracuseStep 1068077 = 400529) (by norm_num)
theorem B1068101 : Blo 710320 1068101 := bbase (se 4 (by rfl) ⟨100134, by rfl⟩ : syracuseStep 1068101 = 200269) (by norm_num)
theorem B1068125 : Blo 710320 1068125 := bbase (se 3 (by rfl) ⟨200273, by rfl⟩ : syracuseStep 1068125 = 400547) (by norm_num)
theorem B1068149 : Blo 710320 1068149 := bbase (se 5 (by rfl) ⟨50069, by rfl⟩ : syracuseStep 1068149 = 100139) (by norm_num)
theorem B1199245 : Blo 710320 1199245 := bbase (se 3 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 1199245 = 449717) (by norm_num)
theorem B1068173 : Blo 710320 1068173 := bbase (se 3 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 1068173 = 400565) (by norm_num)
theorem B1068197 : Blo 710320 1068197 := bbase (se 4 (by rfl) ⟨100143, by rfl⟩ : syracuseStep 1068197 = 200287) (by norm_num)
theorem B1068221 : Blo 710320 1068221 := bbase (se 3 (by rfl) ⟨200291, by rfl⟩ : syracuseStep 1068221 = 400583) (by norm_num)
theorem B1068245 : Blo 710320 1068245 := bbase (se 7 (by rfl) ⟨12518, by rfl⟩ : syracuseStep 1068245 = 25037) (by norm_num)
theorem B1199333 : Blo 710320 1199333 := bbase (se 4 (by rfl) ⟨112437, by rfl⟩ : syracuseStep 1199333 = 224875) (by norm_num)
theorem B2608357 : Blo 710320 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B1068269 : Blo 710320 1068269 := bbase (se 3 (by rfl) ⟨200300, by rfl⟩ : syracuseStep 1068269 = 400601) (by norm_num)
theorem B1068293 : Blo 710320 1068293 := bbase (se 4 (by rfl) ⟨100152, by rfl⟩ : syracuseStep 1068293 = 200305) (by norm_num)
theorem B1068317 : Blo 710320 1068317 := bbase (se 3 (by rfl) ⟨200309, by rfl⟩ : syracuseStep 1068317 = 400619) (by norm_num)
theorem B2280757 : Blo 710320 2280757 := bbase (se 5 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 2280757 = 213821) (by norm_num)
theorem B1068341 : Blo 710320 1068341 := bbase (se 5 (by rfl) ⟨50078, by rfl⟩ : syracuseStep 1068341 = 100157) (by norm_num)
theorem B1068365 : Blo 710320 1068365 := bbase (se 3 (by rfl) ⟨200318, by rfl⟩ : syracuseStep 1068365 = 400637) (by norm_num)
theorem B1199461 : Blo 710320 1199461 := bbase (se 4 (by rfl) ⟨112449, by rfl⟩ : syracuseStep 1199461 = 224899) (by norm_num)
theorem B1068389 : Blo 710320 1068389 := bbase (se 4 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 1068389 = 200323) (by norm_num)
theorem B1068413 : Blo 710320 1068413 := bbase (se 3 (by rfl) ⟨200327, by rfl⟩ : syracuseStep 1068413 = 400655) (by norm_num)
theorem B1068437 : Blo 710320 1068437 := bbase (se 6 (by rfl) ⟨25041, by rfl⟩ : syracuseStep 1068437 = 50083) (by norm_num)
theorem B1068461 : Blo 710320 1068461 := bbase (se 3 (by rfl) ⟨200336, by rfl⟩ : syracuseStep 1068461 = 400673) (by norm_num)
theorem B1199549 : Blo 710320 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B1068485 : Blo 710320 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B1068509 : Blo 710320 1068509 := bbase (se 3 (by rfl) ⟨200345, by rfl⟩ : syracuseStep 1068509 = 400691) (by norm_num)
theorem B1068533 : Blo 710320 1068533 := bbase (se 5 (by rfl) ⟨50087, by rfl⟩ : syracuseStep 1068533 = 100175) (by norm_num)
theorem B3853813 : Blo 710320 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B1068557 : Blo 710320 1068557 := bbase (se 3 (by rfl) ⟨200354, by rfl⟩ : syracuseStep 1068557 = 400709) (by norm_num)
theorem B1068581 : Blo 710320 1068581 := bbase (se 4 (by rfl) ⟨100179, by rfl⟩ : syracuseStep 1068581 = 200359) (by norm_num)
theorem B4050485 : Blo 710320 4050485 := bbase (se 5 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 4050485 = 379733) (by norm_num)
theorem B1199677 : Blo 710320 1199677 := bbase (se 3 (by rfl) ⟨224939, by rfl⟩ : syracuseStep 1199677 = 449879) (by norm_num)
theorem B1068605 : Blo 710320 1068605 := bbase (se 3 (by rfl) ⟨200363, by rfl⟩ : syracuseStep 1068605 = 400727) (by norm_num)
theorem B1068629 : Blo 710320 1068629 := bbase (se 8 (by rfl) ⟨6261, by rfl⟩ : syracuseStep 1068629 = 12523) (by norm_num)
theorem B1068653 : Blo 710320 1068653 := bbase (se 3 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 1068653 = 400745) (by norm_num)
theorem B1068677 : Blo 710320 1068677 := bbase (se 4 (by rfl) ⟨100188, by rfl⟩ : syracuseStep 1068677 = 200377) (by norm_num)
theorem B1199765 : Blo 710320 1199765 := bbase (se 6 (by rfl) ⟨28119, by rfl⟩ : syracuseStep 1199765 = 56239) (by norm_num)
theorem B1068701 : Blo 710320 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B1068725 : Blo 710320 1068725 := bbase (se 5 (by rfl) ⟨50096, by rfl⟩ : syracuseStep 1068725 = 100193) (by norm_num)
theorem B2707141 : Blo 710320 2707141 := bbase (se 4 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 2707141 = 507589) (by norm_num)
theorem B1068749 : Blo 710320 1068749 := bbase (se 3 (by rfl) ⟨200390, by rfl⟩ : syracuseStep 1068749 = 400781) (by norm_num)
theorem B1068773 : Blo 710320 1068773 := bbase (se 4 (by rfl) ⟨100197, by rfl⟩ : syracuseStep 1068773 = 200395) (by norm_num)
theorem B1068797 : Blo 710320 1068797 := bbase (se 3 (by rfl) ⟨200399, by rfl⟩ : syracuseStep 1068797 = 400799) (by norm_num)
theorem B1199893 : Blo 710320 1199893 := bbase (se 6 (by rfl) ⟨28122, by rfl⟩ : syracuseStep 1199893 = 56245) (by norm_num)
theorem B1068821 : Blo 710320 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B1068845 : Blo 710320 1068845 := bbase (se 3 (by rfl) ⟨200408, by rfl⟩ : syracuseStep 1068845 = 400817) (by norm_num)
theorem B1068869 : Blo 710320 1068869 := bbase (se 4 (by rfl) ⟨100206, by rfl⟩ : syracuseStep 1068869 = 200413) (by norm_num)
theorem B1068893 : Blo 710320 1068893 := bbase (se 3 (by rfl) ⟨200417, by rfl⟩ : syracuseStep 1068893 = 400835) (by norm_num)
theorem B1199981 : Blo 710320 1199981 := bbase (se 3 (by rfl) ⟨224996, by rfl⟩ : syracuseStep 1199981 = 449993) (by norm_num)
theorem B1068917 : Blo 710320 1068917 := bbase (se 5 (by rfl) ⟨50105, by rfl⟩ : syracuseStep 1068917 = 100211) (by norm_num)
theorem B1068941 : Blo 710320 1068941 := bbase (se 3 (by rfl) ⟨200426, by rfl⟩ : syracuseStep 1068941 = 400853) (by norm_num)
theorem B1068965 : Blo 710320 1068965 := bbase (se 4 (by rfl) ⟨100215, by rfl⟩ : syracuseStep 1068965 = 200431) (by norm_num)
theorem B1068989 : Blo 710320 1068989 := bbase (se 3 (by rfl) ⟨200435, by rfl⟩ : syracuseStep 1068989 = 400871) (by norm_num)
theorem B1069013 : Blo 710320 1069013 := bbase (se 7 (by rfl) ⟨12527, by rfl⟩ : syracuseStep 1069013 = 25055) (by norm_num)
theorem B1200109 : Blo 710320 1200109 := bbase (se 3 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 1200109 = 450041) (by norm_num)
theorem B1069037 : Blo 710320 1069037 := bbase (se 3 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 1069037 = 400889) (by norm_num)
theorem B2707445 : Blo 710320 2707445 := bbase (se 5 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 2707445 = 253823) (by norm_num)
theorem B1069061 : Blo 710320 1069061 := bbase (se 4 (by rfl) ⟨100224, by rfl⟩ : syracuseStep 1069061 = 200449) (by norm_num)
theorem B1069085 : Blo 710320 1069085 := bbase (se 3 (by rfl) ⟨200453, by rfl⟩ : syracuseStep 1069085 = 400907) (by norm_num)
theorem B1069109 : Blo 710320 1069109 := bbase (se 5 (by rfl) ⟨50114, by rfl⟩ : syracuseStep 1069109 = 100229) (by norm_num)
theorem B1200197 : Blo 710320 1200197 := bbase (se 4 (by rfl) ⟨112518, by rfl⟩ : syracuseStep 1200197 = 225037) (by norm_num)
theorem B1069133 : Blo 710320 1069133 := bbase (se 3 (by rfl) ⟨200462, by rfl⟩ : syracuseStep 1069133 = 400925) (by norm_num)
theorem B1069157 : Blo 710320 1069157 := bbase (se 4 (by rfl) ⟨100233, by rfl⟩ : syracuseStep 1069157 = 200467) (by norm_num)
theorem B1069181 : Blo 710320 1069181 := bbase (se 3 (by rfl) ⟨200471, by rfl⟩ : syracuseStep 1069181 = 400943) (by norm_num)
theorem B1069205 : Blo 710320 1069205 := bbase (se 6 (by rfl) ⟨25059, by rfl⟩ : syracuseStep 1069205 = 50119) (by norm_num)
theorem B1069229 : Blo 710320 1069229 := bbase (se 3 (by rfl) ⟨200480, by rfl⟩ : syracuseStep 1069229 = 400961) (by norm_num)
theorem B1200325 : Blo 710320 1200325 := bbase (se 4 (by rfl) ⟨112530, by rfl⟩ : syracuseStep 1200325 = 225061) (by norm_num)
theorem B1069253 : Blo 710320 1069253 := bbase (se 4 (by rfl) ⟨100242, by rfl⟩ : syracuseStep 1069253 = 200485) (by norm_num)
theorem B1069277 : Blo 710320 1069277 := bbase (se 3 (by rfl) ⟨200489, by rfl⟩ : syracuseStep 1069277 = 400979) (by norm_num)
theorem B1069301 : Blo 710320 1069301 := bbase (se 5 (by rfl) ⟨50123, by rfl⟩ : syracuseStep 1069301 = 100247) (by norm_num)
theorem B1069325 : Blo 710320 1069325 := bbase (se 3 (by rfl) ⟨200498, by rfl⟩ : syracuseStep 1069325 = 400997) (by norm_num)
theorem B1200413 : Blo 710320 1200413 := bbase (se 3 (by rfl) ⟨225077, by rfl⟩ : syracuseStep 1200413 = 450155) (by norm_num)
theorem B1069349 : Blo 710320 1069349 := bbase (se 4 (by rfl) ⟨100251, by rfl⟩ : syracuseStep 1069349 = 200503) (by norm_num)
theorem B1069373 : Blo 710320 1069373 := bbase (se 3 (by rfl) ⟨200507, by rfl⟩ : syracuseStep 1069373 = 401015) (by norm_num)
theorem B1069397 : Blo 710320 1069397 := bbase (se 10 (by rfl) ⟨1566, by rfl⟩ : syracuseStep 1069397 = 3133) (by norm_num)
theorem B1069421 : Blo 710320 1069421 := bbase (se 3 (by rfl) ⟨200516, by rfl⟩ : syracuseStep 1069421 = 401033) (by norm_num)
theorem B1069445 : Blo 710320 1069445 := bbase (se 4 (by rfl) ⟨100260, by rfl⟩ : syracuseStep 1069445 = 200521) (by norm_num)
theorem B1200541 : Blo 710320 1200541 := bbase (se 3 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 1200541 = 450203) (by norm_num)
theorem B1069469 : Blo 710320 1069469 := bbase (se 3 (by rfl) ⟨200525, by rfl⟩ : syracuseStep 1069469 = 401051) (by norm_num)
theorem B1069493 : Blo 710320 1069493 := bbase (se 5 (by rfl) ⟨50132, by rfl⟩ : syracuseStep 1069493 = 100265) (by norm_num)
theorem B1069517 : Blo 710320 1069517 := bbase (se 3 (by rfl) ⟨200534, by rfl⟩ : syracuseStep 1069517 = 401069) (by norm_num)
theorem B1069541 : Blo 710320 1069541 := bbase (se 4 (by rfl) ⟨100269, by rfl⟩ : syracuseStep 1069541 = 200539) (by norm_num)
theorem B1200629 : Blo 710320 1200629 := bbase (se 5 (by rfl) ⟨56279, by rfl⟩ : syracuseStep 1200629 = 112559) (by norm_num)
theorem B1069565 : Blo 710320 1069565 := bbase (se 3 (by rfl) ⟨200543, by rfl⟩ : syracuseStep 1069565 = 401087) (by norm_num)
theorem B1069589 : Blo 710320 1069589 := bbase (se 6 (by rfl) ⟨25068, by rfl⟩ : syracuseStep 1069589 = 50137) (by norm_num)
theorem B1069613 : Blo 710320 1069613 := bbase (se 3 (by rfl) ⟨200552, by rfl⟩ : syracuseStep 1069613 = 401105) (by norm_num)
theorem B1299005 : Blo 710320 1299005 := bbase (se 3 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 1299005 = 487127) (by norm_num)
theorem B1069637 : Blo 710320 1069637 := bbase (se 4 (by rfl) ⟨100278, by rfl⟩ : syracuseStep 1069637 = 200557) (by norm_num)
theorem B1233485 : Blo 710320 1233485 := bbase (se 3 (by rfl) ⟨231278, by rfl⟩ : syracuseStep 1233485 = 462557) (by norm_num)
theorem B1069661 : Blo 710320 1069661 := bbase (se 3 (by rfl) ⟨200561, by rfl⟩ : syracuseStep 1069661 = 401123) (by norm_num)
theorem B1200757 : Blo 710320 1200757 := bbase (se 5 (by rfl) ⟨56285, by rfl⟩ : syracuseStep 1200757 = 112571) (by norm_num)
theorem B1069685 : Blo 710320 1069685 := bbase (se 5 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 1069685 = 100283) (by norm_num)
theorem B742009 : Blo 710320 742009 := bbase (se 2 (by rfl) ⟨278253, by rfl⟩ : syracuseStep 742009 = 556507) (by norm_num)
theorem B1069709 : Blo 710320 1069709 := bbase (se 3 (by rfl) ⟨200570, by rfl⟩ : syracuseStep 1069709 = 401141) (by norm_num)
theorem B1069733 : Blo 710320 1069733 := bbase (se 4 (by rfl) ⟨100287, by rfl⟩ : syracuseStep 1069733 = 200575) (by norm_num)
theorem B1069757 : Blo 710320 1069757 := bbase (se 3 (by rfl) ⟨200579, by rfl⟩ : syracuseStep 1069757 = 401159) (by norm_num)
theorem B1200845 : Blo 710320 1200845 := bbase (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) (by norm_num)
theorem B1069781 : Blo 710320 1069781 := bbase (se 7 (by rfl) ⟨12536, by rfl⟩ : syracuseStep 1069781 = 25073) (by norm_num)
theorem B1069805 : Blo 710320 1069805 := bbase (se 3 (by rfl) ⟨200588, by rfl⟩ : syracuseStep 1069805 = 401177) (by norm_num)
theorem B1069829 : Blo 710320 1069829 := bbase (se 4 (by rfl) ⟨100296, by rfl⟩ : syracuseStep 1069829 = 200593) (by norm_num)
theorem B1069853 : Blo 710320 1069853 := bbase (se 3 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 1069853 = 401195) (by norm_num)
theorem B1069877 : Blo 710320 1069877 := bbase (se 5 (by rfl) ⟨50150, by rfl⟩ : syracuseStep 1069877 = 100301) (by norm_num)
theorem B1200973 : Blo 710320 1200973 := bbase (se 3 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 1200973 = 450365) (by norm_num)
theorem B1069901 : Blo 710320 1069901 := bbase (se 3 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 1069901 = 401213) (by norm_num)
theorem B1069925 : Blo 710320 1069925 := bbase (se 4 (by rfl) ⟨100305, by rfl⟩ : syracuseStep 1069925 = 200611) (by norm_num)
theorem B2282357 : Blo 710320 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B1069949 : Blo 710320 1069949 := bbase (se 3 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 1069949 = 401231) (by norm_num)
theorem B1823629 : Blo 710320 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B1299341 : Blo 710320 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B1069973 : Blo 710320 1069973 := bbase (se 6 (by rfl) ⟨25077, by rfl⟩ : syracuseStep 1069973 = 50155) (by norm_num)
theorem B1201061 : Blo 710320 1201061 := bbase (se 4 (by rfl) ⟨112599, by rfl⟩ : syracuseStep 1201061 = 225199) (by norm_num)
theorem B1069997 : Blo 710320 1069997 := bbase (se 3 (by rfl) ⟨200624, by rfl⟩ : syracuseStep 1069997 = 401249) (by norm_num)
theorem B1627069 : Blo 710320 1627069 := bbase (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) (by norm_num)
theorem B1070021 : Blo 710320 1070021 := bbase (se 4 (by rfl) ⟨100314, by rfl⟩ : syracuseStep 1070021 = 200629) (by norm_num)
theorem B1070045 : Blo 710320 1070045 := bbase (se 3 (by rfl) ⟨200633, by rfl⟩ : syracuseStep 1070045 = 401267) (by norm_num)
theorem B1070069 : Blo 710320 1070069 := bbase (se 5 (by rfl) ⟨50159, by rfl⟩ : syracuseStep 1070069 = 100319) (by norm_num)
theorem B1070093 : Blo 710320 1070093 := bbase (se 3 (by rfl) ⟨200642, by rfl⟩ : syracuseStep 1070093 = 401285) (by norm_num)
theorem B1201189 : Blo 710320 1201189 := bbase (se 4 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 1201189 = 225223) (by norm_num)
theorem B1070117 : Blo 710320 1070117 := bbase (se 4 (by rfl) ⟨100323, by rfl⟩ : syracuseStep 1070117 = 200647) (by norm_num)
theorem B1070141 : Blo 710320 1070141 := bbase (se 3 (by rfl) ⟨200651, by rfl⟩ : syracuseStep 1070141 = 401303) (by norm_num)
theorem B1070165 : Blo 710320 1070165 := bbase (se 8 (by rfl) ⟨6270, by rfl⟩ : syracuseStep 1070165 = 12541) (by norm_num)
theorem B1922149 : Blo 710320 1922149 := bbase (se 4 (by rfl) ⟨180201, by rfl⟩ : syracuseStep 1922149 = 360403) (by norm_num)
theorem B1070189 : Blo 710320 1070189 := bbase (se 3 (by rfl) ⟨200660, by rfl⟩ : syracuseStep 1070189 = 401321) (by norm_num)
theorem B1201277 : Blo 710320 1201277 := bbase (se 3 (by rfl) ⟨225239, by rfl⟩ : syracuseStep 1201277 = 450479) (by norm_num)
theorem B1070213 : Blo 710320 1070213 := bbase (se 4 (by rfl) ⟨100332, by rfl⟩ : syracuseStep 1070213 = 200665) (by norm_num)
theorem B1070237 : Blo 710320 1070237 := bbase (se 3 (by rfl) ⟨200669, by rfl⟩ : syracuseStep 1070237 = 401339) (by norm_num)
theorem B1070261 : Blo 710320 1070261 := bbase (se 5 (by rfl) ⟨50168, by rfl⟩ : syracuseStep 1070261 = 100337) (by norm_num)
theorem B1070285 : Blo 710320 1070285 := bbase (se 3 (by rfl) ⟨200678, by rfl⟩ : syracuseStep 1070285 = 401357) (by norm_num)
theorem B1070309 : Blo 710320 1070309 := bbase (se 4 (by rfl) ⟨100341, by rfl⟩ : syracuseStep 1070309 = 200683) (by norm_num)
theorem B1627381 : Blo 710320 1627381 := bbase (se 5 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 1627381 = 152567) (by norm_num)
theorem B1201405 : Blo 710320 1201405 := bbase (se 3 (by rfl) ⟨225263, by rfl⟩ : syracuseStep 1201405 = 450527) (by norm_num)
theorem B1070333 : Blo 710320 1070333 := bbase (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) (by norm_num)
theorem B1070357 : Blo 710320 1070357 := bbase (se 6 (by rfl) ⟨25086, by rfl⟩ : syracuseStep 1070357 = 50173) (by norm_num)
theorem B1070381 : Blo 710320 1070381 := bbase (se 3 (by rfl) ⟨200696, by rfl⟩ : syracuseStep 1070381 = 401393) (by norm_num)
theorem B1070405 : Blo 710320 1070405 := bbase (se 4 (by rfl) ⟨100350, by rfl⟩ : syracuseStep 1070405 = 200701) (by norm_num)
theorem B1201493 : Blo 710320 1201493 := bbase (se 16 (by rfl) ⟨27, by rfl⟩ : syracuseStep 1201493 = 55) (by norm_num)
theorem B1070429 : Blo 710320 1070429 := bbase (se 3 (by rfl) ⟨200705, by rfl⟩ : syracuseStep 1070429 = 401411) (by norm_num)
theorem B1070453 : Blo 710320 1070453 := bbase (se 5 (by rfl) ⟨50177, by rfl⟩ : syracuseStep 1070453 = 100355) (by norm_num)
theorem B1070477 : Blo 710320 1070477 := bbase (se 3 (by rfl) ⟨200714, by rfl⟩ : syracuseStep 1070477 = 401429) (by norm_num)
theorem B1070501 : Blo 710320 1070501 := bbase (se 4 (by rfl) ⟨100359, by rfl⟩ : syracuseStep 1070501 = 200719) (by norm_num)
theorem B1070525 : Blo 710320 1070525 := bbase (se 3 (by rfl) ⟨200723, by rfl⟩ : syracuseStep 1070525 = 401447) (by norm_num)
theorem B1201621 : Blo 710320 1201621 := bbase (se 7 (by rfl) ⟨14081, by rfl⟩ : syracuseStep 1201621 = 28163) (by norm_num)
theorem B1070549 : Blo 710320 1070549 := bbase (se 7 (by rfl) ⟨12545, by rfl⟩ : syracuseStep 1070549 = 25091) (by norm_num)
theorem B1070573 : Blo 710320 1070573 := bbase (se 3 (by rfl) ⟨200732, by rfl⟩ : syracuseStep 1070573 = 401465) (by norm_num)
theorem B1070597 : Blo 710320 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B1070621 : Blo 710320 1070621 := bbase (se 3 (by rfl) ⟨200741, by rfl⟩ : syracuseStep 1070621 = 401483) (by norm_num)
theorem B1201709 : Blo 710320 1201709 := bbase (se 3 (by rfl) ⟨225320, by rfl⟩ : syracuseStep 1201709 = 450641) (by norm_num)
theorem B1070645 : Blo 710320 1070645 := bbase (se 5 (by rfl) ⟨50186, by rfl⟩ : syracuseStep 1070645 = 100373) (by norm_num)
theorem B1070669 : Blo 710320 1070669 := bbase (se 3 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 1070669 = 401501) (by norm_num)
theorem B1070693 : Blo 710320 1070693 := bbase (se 4 (by rfl) ⟨100377, by rfl⟩ : syracuseStep 1070693 = 200755) (by norm_num)
theorem B1070717 : Blo 710320 1070717 := bbase (se 3 (by rfl) ⟨200759, by rfl⟩ : syracuseStep 1070717 = 401519) (by norm_num)
theorem B1070741 : Blo 710320 1070741 := bbase (se 6 (by rfl) ⟨25095, by rfl⟩ : syracuseStep 1070741 = 50191) (by norm_num)
theorem B1201837 : Blo 710320 1201837 := bbase (se 3 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 1201837 = 450689) (by norm_num)
theorem B1070765 : Blo 710320 1070765 := bbase (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) (by norm_num)
theorem B1070789 : Blo 710320 1070789 := bbase (se 4 (by rfl) ⟨100386, by rfl⟩ : syracuseStep 1070789 = 200773) (by norm_num)
theorem B4052693 : Blo 710320 4052693 := bbase (se 7 (by rfl) ⟨47492, by rfl⟩ : syracuseStep 4052693 = 94985) (by norm_num)
theorem B1070813 : Blo 710320 1070813 := bbase (se 3 (by rfl) ⟨200777, by rfl⟩ : syracuseStep 1070813 = 401555) (by norm_num)
theorem B1070837 : Blo 710320 1070837 := bbase (se 5 (by rfl) ⟨50195, by rfl⟩ : syracuseStep 1070837 = 100391) (by norm_num)
theorem B1201925 : Blo 710320 1201925 := bbase (se 4 (by rfl) ⟨112680, by rfl⟩ : syracuseStep 1201925 = 225361) (by norm_num)
theorem B1070861 : Blo 710320 1070861 := bbase (se 3 (by rfl) ⟨200786, by rfl⟩ : syracuseStep 1070861 = 401573) (by norm_num)
theorem B1070885 : Blo 710320 1070885 := bbase (se 4 (by rfl) ⟨100395, by rfl⟩ : syracuseStep 1070885 = 200791) (by norm_num)
theorem B1070909 : Blo 710320 1070909 := bbase (se 3 (by rfl) ⟨200795, by rfl⟩ : syracuseStep 1070909 = 401591) (by norm_num)
theorem B13850453 : Blo 710320 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B1070933 : Blo 710320 1070933 := bbase (se 9 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 1070933 = 6275) (by norm_num)
theorem B1070957 : Blo 710320 1070957 := bbase (se 3 (by rfl) ⟨200804, by rfl⟩ : syracuseStep 1070957 = 401609) (by norm_num)
theorem B1202053 : Blo 710320 1202053 := bbase (se 4 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 1202053 = 225385) (by norm_num)
theorem B1070981 : Blo 710320 1070981 := bbase (se 4 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 1070981 = 200809) (by norm_num)
theorem B1071005 : Blo 710320 1071005 := bbase (se 3 (by rfl) ⟨200813, by rfl⟩ : syracuseStep 1071005 = 401627) (by norm_num)
theorem B1071029 : Blo 710320 1071029 := bbase (se 5 (by rfl) ⟨50204, by rfl⟩ : syracuseStep 1071029 = 100409) (by norm_num)
theorem B2283461 : Blo 710320 2283461 := bbase (se 4 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 2283461 = 428149) (by norm_num)
theorem B1071053 : Blo 710320 1071053 := bbase (se 3 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 1071053 = 401645) (by norm_num)
theorem B1202141 : Blo 710320 1202141 := bbase (se 3 (by rfl) ⟨225401, by rfl⟩ : syracuseStep 1202141 = 450803) (by norm_num)
theorem B1071077 : Blo 710320 1071077 := bbase (se 4 (by rfl) ⟨100413, by rfl⟩ : syracuseStep 1071077 = 200827) (by norm_num)
theorem B1071101 : Blo 710320 1071101 := bbase (se 3 (by rfl) ⟨200831, by rfl⟩ : syracuseStep 1071101 = 401663) (by norm_num)
theorem B1071125 : Blo 710320 1071125 := bbase (se 6 (by rfl) ⟨25104, by rfl⟩ : syracuseStep 1071125 = 50209) (by norm_num)
theorem B1071149 : Blo 710320 1071149 := bbase (se 3 (by rfl) ⟨200840, by rfl⟩ : syracuseStep 1071149 = 401681) (by norm_num)
theorem B2709557 : Blo 710320 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B1071173 : Blo 710320 1071173 := bbase (se 4 (by rfl) ⟨100422, by rfl⟩ : syracuseStep 1071173 = 200845) (by norm_num)
theorem B1202269 : Blo 710320 1202269 := bbase (se 3 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 1202269 = 450851) (by norm_num)
theorem B1071197 : Blo 710320 1071197 := bbase (se 3 (by rfl) ⟨200849, by rfl⟩ : syracuseStep 1071197 = 401699) (by norm_num)
theorem B1071221 : Blo 710320 1071221 := bbase (se 5 (by rfl) ⟨50213, by rfl⟩ : syracuseStep 1071221 = 100427) (by norm_num)
theorem B1071245 : Blo 710320 1071245 := bbase (se 3 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 1071245 = 401717) (by norm_num)
theorem B3037333 : Blo 710320 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B1071269 : Blo 710320 1071269 := bbase (se 4 (by rfl) ⟨100431, by rfl⟩ : syracuseStep 1071269 = 200863) (by norm_num)
theorem B1202357 : Blo 710320 1202357 := bbase (se 5 (by rfl) ⟨56360, by rfl⟩ : syracuseStep 1202357 = 112721) (by norm_num)
theorem B1071293 : Blo 710320 1071293 := bbase (se 3 (by rfl) ⟨200867, by rfl⟩ : syracuseStep 1071293 = 401735) (by norm_num)
theorem B1071317 : Blo 710320 1071317 := bbase (se 7 (by rfl) ⟨12554, by rfl⟩ : syracuseStep 1071317 = 25109) (by norm_num)
theorem B1071341 : Blo 710320 1071341 := bbase (se 3 (by rfl) ⟨200876, by rfl⟩ : syracuseStep 1071341 = 401753) (by norm_num)
theorem B1071365 : Blo 710320 1071365 := bbase (se 4 (by rfl) ⟨100440, by rfl⟩ : syracuseStep 1071365 = 200881) (by norm_num)
theorem B1071389 : Blo 710320 1071389 := bbase (se 3 (by rfl) ⟨200885, by rfl⟩ : syracuseStep 1071389 = 401771) (by norm_num)
theorem B1202485 : Blo 710320 1202485 := bbase (se 5 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 1202485 = 112733) (by norm_num)
theorem B1071413 : Blo 710320 1071413 := bbase (se 5 (by rfl) ⟨50222, by rfl⟩ : syracuseStep 1071413 = 100445) (by norm_num)
theorem B1071437 : Blo 710320 1071437 := bbase (se 3 (by rfl) ⟨200894, by rfl⟩ : syracuseStep 1071437 = 401789) (by norm_num)
theorem B6838613 : Blo 710320 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B2709845 : Blo 710320 2709845 := bbase (se 10 (by rfl) ⟨3969, by rfl⟩ : syracuseStep 2709845 = 7939) (by norm_num)
theorem B1071461 : Blo 710320 1071461 := bbase (se 4 (by rfl) ⟨100449, by rfl⟩ : syracuseStep 1071461 = 200899) (by norm_num)
theorem B1628549 : Blo 710320 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B1202573 : Blo 710320 1202573 := bbase (se 3 (by rfl) ⟨225482, by rfl⟩ : syracuseStep 1202573 = 450965) (by norm_num)
theorem B1202701 : Blo 710320 1202701 := bbase (se 3 (by rfl) ⟨225506, by rfl⟩ : syracuseStep 1202701 = 451013) (by norm_num)
theorem B1202789 : Blo 710320 1202789 := bbase (se 4 (by rfl) ⟨112761, by rfl⟩ : syracuseStep 1202789 = 225523) (by norm_num)
theorem B1825445 : Blo 710320 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B1202917 : Blo 710320 1202917 := bbase (se 4 (by rfl) ⟨112773, by rfl⟩ : syracuseStep 1202917 = 225547) (by norm_num)
theorem B1203005 : Blo 710320 1203005 := bbase (se 3 (by rfl) ⟨225563, by rfl⟩ : syracuseStep 1203005 = 451127) (by norm_num)
theorem B1203133 : Blo 710320 1203133 := bbase (se 3 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 1203133 = 451175) (by norm_num)
theorem B1203221 : Blo 710320 1203221 := bbase (se 6 (by rfl) ⟨28200, by rfl⟩ : syracuseStep 1203221 = 56401) (by norm_num)
theorem B1203349 : Blo 710320 1203349 := bbase (se 6 (by rfl) ⟨28203, by rfl⟩ : syracuseStep 1203349 = 56407) (by norm_num)
theorem B1137821 : Blo 710320 1137821 := bbase (se 3 (by rfl) ⟨213341, by rfl⟩ : syracuseStep 1137821 = 426683) (by norm_num)
theorem B1203437 : Blo 710320 1203437 := bbase (se 3 (by rfl) ⟨225644, by rfl⟩ : syracuseStep 1203437 = 451289) (by norm_num)
theorem B1203565 : Blo 710320 1203565 := bbase (se 3 (by rfl) ⟨225668, by rfl⟩ : syracuseStep 1203565 = 451337) (by norm_num)
theorem B810361 : Blo 710320 810361 := bbase (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) (by norm_num)
theorem B1203653 : Blo 710320 1203653 := bbase (se 4 (by rfl) ⟨112842, by rfl⟩ : syracuseStep 1203653 = 225685) (by norm_num)
theorem B2711029 : Blo 710320 2711029 := bbase (se 5 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 2711029 = 254159) (by norm_num)
theorem B2022965 : Blo 710320 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B1203781 : Blo 710320 1203781 := bbase (se 4 (by rfl) ⟨112854, by rfl⟩ : syracuseStep 1203781 = 225709) (by norm_num)
theorem B20012629 : Blo 710320 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B810589 : Blo 710320 810589 := bbase (se 3 (by rfl) ⟨151985, by rfl⟩ : syracuseStep 810589 = 303971) (by norm_num)
theorem B1203869 : Blo 710320 1203869 := bbase (se 3 (by rfl) ⟨225725, by rfl⟩ : syracuseStep 1203869 = 451451) (by norm_num)
theorem B2023157 : Blo 710320 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B810761 : Blo 710320 810761 := bbase (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) (by norm_num)
theorem B1203997 : Blo 710320 1203997 := bbase (se 3 (by rfl) ⟨225749, by rfl⟩ : syracuseStep 1203997 = 451499) (by norm_num)
theorem B2711333 : Blo 710320 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B2285381 : Blo 710320 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B1204085 : Blo 710320 1204085 := bbase (se 5 (by rfl) ⟨56441, by rfl⟩ : syracuseStep 1204085 = 112883) (by norm_num)
theorem B1204213 : Blo 710320 1204213 := bbase (se 5 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 1204213 = 112895) (by norm_num)
theorem B1138693 : Blo 710320 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B1204301 : Blo 710320 1204301 := bbase (se 3 (by rfl) ⟨225806, by rfl⟩ : syracuseStep 1204301 = 451613) (by norm_num)
theorem B12181589 : Blo 710320 12181589 := bbase (se 8 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 12181589 = 142753) (by norm_num)
theorem B1138789 : Blo 710320 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B1925221 : Blo 710320 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B1204429 : Blo 710320 1204429 := bbase (se 3 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 1204429 = 451661) (by norm_num)
theorem B1138949 : Blo 710320 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B1204517 : Blo 710320 1204517 := bbase (se 4 (by rfl) ⟨112923, by rfl⟩ : syracuseStep 1204517 = 225847) (by norm_num)
theorem B1204645 : Blo 710320 1204645 := bbase (se 4 (by rfl) ⟨112935, by rfl⟩ : syracuseStep 1204645 = 225871) (by norm_num)
theorem B1204733 : Blo 710320 1204733 := bbase (se 3 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 1204733 = 451775) (by norm_num)
theorem B3596885 : Blo 710320 3596885 := bbase (se 8 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 3596885 = 42151) (by norm_num)
theorem B1204861 : Blo 710320 1204861 := bbase (se 3 (by rfl) ⟨225911, by rfl⟩ : syracuseStep 1204861 = 451823) (by norm_num)
theorem B2024149 : Blo 710320 2024149 := bbase (se 7 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 2024149 = 47441) (by norm_num)
theorem B1204949 : Blo 710320 1204949 := bbase (se 7 (by rfl) ⟨14120, by rfl⟩ : syracuseStep 1204949 = 28241) (by norm_num)
theorem B1598237 : Blo 710320 1598237 := bbase (se 3 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 1598237 = 599339) (by norm_num)
theorem B1925957 : Blo 710320 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B1205077 : Blo 710320 1205077 := bbase (se 9 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 1205077 = 7061) (by norm_num)
theorem B1598309 : Blo 710320 1598309 := bbase (se 4 (by rfl) ⟨149841, by rfl⟩ : syracuseStep 1598309 = 299683) (by norm_num)
theorem B1598381 : Blo 710320 1598381 := bbase (se 3 (by rfl) ⟨299696, by rfl⟩ : syracuseStep 1598381 = 599393) (by norm_num)
theorem B1205165 : Blo 710320 1205165 := bbase (se 3 (by rfl) ⟨225968, by rfl⟩ : syracuseStep 1205165 = 451937) (by norm_num)
theorem B1598453 : Blo 710320 1598453 := bbase (se 5 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 1598453 = 149855) (by norm_num)
theorem B1205293 : Blo 710320 1205293 := bbase (se 3 (by rfl) ⟨225992, by rfl⟩ : syracuseStep 1205293 = 451985) (by norm_num)
theorem B1598525 : Blo 710320 1598525 := bbase (se 3 (by rfl) ⟨299723, by rfl⟩ : syracuseStep 1598525 = 599447) (by norm_num)
theorem B3040325 : Blo 710320 3040325 := bbase (se 4 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 3040325 = 570061) (by norm_num)
theorem B1598597 : Blo 710320 1598597 := bbase (se 4 (by rfl) ⟨149868, by rfl⟩ : syracuseStep 1598597 = 299737) (by norm_num)
theorem B1205381 : Blo 710320 1205381 := bbase (se 4 (by rfl) ⟨113004, by rfl⟩ : syracuseStep 1205381 = 226009) (by norm_num)
theorem B1598669 : Blo 710320 1598669 := bbase (se 3 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 1598669 = 599501) (by norm_num)
theorem B2286805 : Blo 710320 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B1598741 : Blo 710320 1598741 := bbase (se 6 (by rfl) ⟨37470, by rfl⟩ : syracuseStep 1598741 = 74941) (by norm_num)
theorem B1598813 : Blo 710320 1598813 := bbase (se 3 (by rfl) ⟨299777, by rfl⟩ : syracuseStep 1598813 = 599555) (by norm_num)
theorem B1140077 : Blo 710320 1140077 := bbase (se 3 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 1140077 = 427529) (by norm_num)
theorem B1598885 : Blo 710320 1598885 := bbase (se 4 (by rfl) ⟨149895, by rfl⟩ : syracuseStep 1598885 = 299791) (by norm_num)
theorem B1598957 : Blo 710320 1598957 := bbase (se 3 (by rfl) ⟨299804, by rfl⟩ : syracuseStep 1598957 = 599609) (by norm_num)
theorem B1599029 : Blo 710320 1599029 := bbase (se 5 (by rfl) ⟨74954, by rfl⟩ : syracuseStep 1599029 = 149909) (by norm_num)
theorem B3860021 : Blo 710320 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B1599101 : Blo 710320 1599101 := bbase (se 3 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 1599101 = 599663) (by norm_num)
theorem B2287253 : Blo 710320 2287253 := bbase (se 6 (by rfl) ⟨53607, by rfl⟩ : syracuseStep 2287253 = 107215) (by norm_num)
theorem B1926821 : Blo 710320 1926821 := bbase (se 4 (by rfl) ⟨180639, by rfl⟩ : syracuseStep 1926821 = 361279) (by norm_num)
theorem B1599173 : Blo 710320 1599173 := bbase (se 4 (by rfl) ⟨149922, by rfl⟩ : syracuseStep 1599173 = 299845) (by norm_num)
theorem B1599245 : Blo 710320 1599245 := bbase (se 3 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 1599245 = 599717) (by norm_num)
theorem B2025253 : Blo 710320 2025253 := bbase (se 4 (by rfl) ⟨189867, by rfl⟩ : syracuseStep 2025253 = 379735) (by norm_num)
theorem B1828645 : Blo 710320 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B812837 : Blo 710320 812837 := bbase (se 4 (by rfl) ⟨76203, by rfl⟩ : syracuseStep 812837 = 152407) (by norm_num)
theorem B1599317 : Blo 710320 1599317 := bbase (se 9 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 1599317 = 9371) (by norm_num)
theorem B3598181 : Blo 710320 3598181 := bbase (se 4 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 3598181 = 674659) (by norm_num)
theorem B1140589 : Blo 710320 1140589 := bbase (se 3 (by rfl) ⟨213860, by rfl⟩ : syracuseStep 1140589 = 427721) (by norm_num)
theorem B1599389 : Blo 710320 1599389 := bbase (se 3 (by rfl) ⟨299885, by rfl⟩ : syracuseStep 1599389 = 599771) (by norm_num)
theorem B1599461 : Blo 710320 1599461 := bbase (se 4 (by rfl) ⟨149949, by rfl⟩ : syracuseStep 1599461 = 299899) (by norm_num)
theorem B1927157 : Blo 710320 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B1599533 : Blo 710320 1599533 := bbase (se 3 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 1599533 = 599825) (by norm_num)
theorem B3041333 : Blo 710320 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B1599605 : Blo 710320 1599605 := bbase (se 5 (by rfl) ⟨74981, by rfl⟩ : syracuseStep 1599605 = 149963) (by norm_num)
theorem B1599677 : Blo 710320 1599677 := bbase (se 3 (by rfl) ⟨299939, by rfl⟩ : syracuseStep 1599677 = 599879) (by norm_num)
theorem B813289 : Blo 710320 813289 := bbase (se 2 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 813289 = 609967) (by norm_num)
theorem B1599749 : Blo 710320 1599749 := bbase (se 4 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 1599749 = 299953) (by norm_num)
theorem B1599821 : Blo 710320 1599821 := bbase (se 3 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 1599821 = 599933) (by norm_num)
theorem B5400917 : Blo 710320 5400917 := bbase (se 10 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 5400917 = 15823) (by norm_num)
theorem B1599893 : Blo 710320 1599893 := bbase (se 6 (by rfl) ⟨37497, by rfl⟩ : syracuseStep 1599893 = 74995) (by norm_num)
theorem B1599965 : Blo 710320 1599965 := bbase (se 3 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 1599965 = 599987) (by norm_num)
theorem B1731053 : Blo 710320 1731053 := bbase (se 3 (by rfl) ⟨324572, by rfl⟩ : syracuseStep 1731053 = 649145) (by norm_num)
theorem B1927685 : Blo 710320 1927685 := bbase (se 4 (by rfl) ⟨180720, by rfl⟩ : syracuseStep 1927685 = 361441) (by norm_num)
theorem B1600037 : Blo 710320 1600037 := bbase (se 4 (by rfl) ⟨150003, by rfl⟩ : syracuseStep 1600037 = 300007) (by norm_num)
theorem B1600109 : Blo 710320 1600109 := bbase (se 3 (by rfl) ⟨300020, by rfl⟩ : syracuseStep 1600109 = 600041) (by norm_num)
theorem B1600181 : Blo 710320 1600181 := bbase (se 5 (by rfl) ⟨75008, by rfl⟩ : syracuseStep 1600181 = 150017) (by norm_num)
theorem B1600253 : Blo 710320 1600253 := bbase (se 3 (by rfl) ⟨300047, by rfl⟩ : syracuseStep 1600253 = 600095) (by norm_num)
theorem B1600325 : Blo 710320 1600325 := bbase (se 4 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 1600325 = 300061) (by norm_num)
theorem B1141589 : Blo 710320 1141589 := bbase (se 9 (by rfl) ⟨3344, by rfl⟩ : syracuseStep 1141589 = 6689) (by norm_num)
theorem B1600397 : Blo 710320 1600397 := bbase (se 3 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 1600397 = 600149) (by norm_num)
theorem B1600469 : Blo 710320 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B1141717 : Blo 710320 1141717 := bbase (se 7 (by rfl) ⟨13379, by rfl⟩ : syracuseStep 1141717 = 26759) (by norm_num)
theorem B3894293 : Blo 710320 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B1141781 : Blo 710320 1141781 := bbase (se 6 (by rfl) ⟨26760, by rfl⟩ : syracuseStep 1141781 = 53521) (by norm_num)
theorem B1600541 : Blo 710320 1600541 := bbase (se 3 (by rfl) ⟨300101, by rfl⟩ : syracuseStep 1600541 = 600203) (by norm_num)
theorem B1731677 : Blo 710320 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B1600613 : Blo 710320 1600613 := bbase (se 4 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 1600613 = 300115) (by norm_num)
theorem B3599477 : Blo 710320 3599477 := bbase (se 5 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 3599477 = 337451) (by norm_num)
theorem B1600685 : Blo 710320 1600685 := bbase (se 3 (by rfl) ⟨300128, by rfl⟩ : syracuseStep 1600685 = 600257) (by norm_num)
theorem B2059445 : Blo 710320 2059445 := bbase (se 5 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 2059445 = 193073) (by norm_num)
theorem B1600757 : Blo 710320 1600757 := bbase (se 5 (by rfl) ⟨75035, by rfl⟩ : syracuseStep 1600757 = 150071) (by norm_num)
theorem B2026757 : Blo 710320 2026757 := bbase (se 4 (by rfl) ⟨190008, by rfl⟩ : syracuseStep 2026757 = 380017) (by norm_num)
theorem B3665173 : Blo 710320 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B1600829 : Blo 710320 1600829 := bbase (se 3 (by rfl) ⟨300155, by rfl⟩ : syracuseStep 1600829 = 600311) (by norm_num)
theorem B1600901 : Blo 710320 1600901 := bbase (se 4 (by rfl) ⟨150084, by rfl⟩ : syracuseStep 1600901 = 300169) (by norm_num)
theorem B1600973 : Blo 710320 1600973 := bbase (se 3 (by rfl) ⟨300182, by rfl⟩ : syracuseStep 1600973 = 600365) (by norm_num)
theorem B1601045 : Blo 710320 1601045 := bbase (se 6 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 1601045 = 75049) (by norm_num)
theorem B1371701 : Blo 710320 1371701 := bbase (se 5 (by rfl) ⟨64298, by rfl⟩ : syracuseStep 1371701 = 128597) (by norm_num)
theorem B58453589 : Blo 710320 58453589 := bbase (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) (by norm_num)
theorem B1601117 : Blo 710320 1601117 := bbase (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) (by norm_num)
theorem B1601189 : Blo 710320 1601189 := bbase (se 4 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 1601189 = 300223) (by norm_num)
theorem B1601261 : Blo 710320 1601261 := bbase (se 3 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 1601261 = 600473) (by norm_num)
theorem B3043109 : Blo 710320 3043109 := bbase (se 4 (by rfl) ⟨285291, by rfl⟩ : syracuseStep 3043109 = 570583) (by norm_num)
theorem B1601333 : Blo 710320 1601333 := bbase (se 5 (by rfl) ⟨75062, by rfl⟩ : syracuseStep 1601333 = 150125) (by norm_num)
theorem B1011533 : Blo 710320 1011533 := bbase (se 3 (by rfl) ⟨189662, by rfl⟩ : syracuseStep 1011533 = 379325) (by norm_num)
theorem B1601405 : Blo 710320 1601405 := bbase (se 3 (by rfl) ⟨300263, by rfl⟩ : syracuseStep 1601405 = 600527) (by norm_num)
theorem B1601477 : Blo 710320 1601477 := bbase (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) (by norm_num)
theorem B1798109 : Blo 710320 1798109 := bbase (se 3 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 1798109 = 674291) (by norm_num)
theorem B1601549 : Blo 710320 1601549 := bbase (se 3 (by rfl) ⟨300290, by rfl⟩ : syracuseStep 1601549 = 600581) (by norm_num)
theorem B1601621 : Blo 710320 1601621 := bbase (se 8 (by rfl) ⟨9384, by rfl⟩ : syracuseStep 1601621 = 18769) (by norm_num)
theorem B8122517 : Blo 710320 8122517 := bbase (se 6 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 8122517 = 380743) (by norm_num)
theorem B1798301 : Blo 710320 1798301 := bbase (se 3 (by rfl) ⟨337181, by rfl⟩ : syracuseStep 1798301 = 674363) (by norm_num)
theorem B1601693 : Blo 710320 1601693 := bbase (se 3 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 1601693 = 600635) (by norm_num)
theorem B3338437 : Blo 710320 3338437 := bbase (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) (by norm_num)
theorem B1601765 : Blo 710320 1601765 := bbase (se 4 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 1601765 = 300331) (by norm_num)
theorem B1601837 : Blo 710320 1601837 := bbase (se 3 (by rfl) ⟨300344, by rfl⟩ : syracuseStep 1601837 = 600689) (by norm_num)
theorem B1143101 : Blo 710320 1143101 := bbase (se 3 (by rfl) ⟨214331, by rfl⟩ : syracuseStep 1143101 = 428663) (by norm_num)
theorem B1601909 : Blo 710320 1601909 := bbase (se 5 (by rfl) ⟨75089, by rfl⟩ : syracuseStep 1601909 = 150179) (by norm_num)
theorem B3600773 : Blo 710320 3600773 := bbase (se 4 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 3600773 = 675145) (by norm_num)
theorem B1601981 : Blo 710320 1601981 := bbase (se 3 (by rfl) ⟨300371, by rfl⟩ : syracuseStep 1601981 = 600743) (by norm_num)
theorem B1143229 : Blo 710320 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B1798645 : Blo 710320 1798645 := bbase (se 5 (by rfl) ⟨84311, by rfl⟩ : syracuseStep 1798645 = 168623) (by norm_num)
theorem B1602053 : Blo 710320 1602053 := bbase (se 4 (by rfl) ⟨150192, by rfl⟩ : syracuseStep 1602053 = 300385) (by norm_num)
theorem B1012285 : Blo 710320 1012285 := bbase (se 3 (by rfl) ⟨189803, by rfl⟩ : syracuseStep 1012285 = 379607) (by norm_num)
theorem B1602125 : Blo 710320 1602125 := bbase (se 3 (by rfl) ⟨300398, by rfl⟩ : syracuseStep 1602125 = 600797) (by norm_num)
theorem B1798757 : Blo 710320 1798757 := bbase (se 4 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 1798757 = 337267) (by norm_num)
theorem B1602197 : Blo 710320 1602197 := bbase (se 6 (by rfl) ⟨37551, by rfl⟩ : syracuseStep 1602197 = 75103) (by norm_num)
theorem B1602269 : Blo 710320 1602269 := bbase (se 3 (by rfl) ⟨300425, by rfl⟩ : syracuseStep 1602269 = 600851) (by norm_num)
theorem B1798949 : Blo 710320 1798949 := bbase (se 4 (by rfl) ⟨168651, by rfl⟩ : syracuseStep 1798949 = 337303) (by norm_num)
theorem B1602341 : Blo 710320 1602341 := bbase (se 4 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 1602341 = 300439) (by norm_num)
theorem B783145 : Blo 710320 783145 := bbase (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) (by norm_num)
theorem B2028341 : Blo 710320 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B1602413 : Blo 710320 1602413 := bbase (se 3 (by rfl) ⟨300452, by rfl⟩ : syracuseStep 1602413 = 600905) (by norm_num)
theorem B1602485 : Blo 710320 1602485 := bbase (se 5 (by rfl) ⟨75116, by rfl⟩ : syracuseStep 1602485 = 150233) (by norm_num)
theorem B1602557 : Blo 710320 1602557 := bbase (se 3 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 1602557 = 600959) (by norm_num)
theorem B1602629 : Blo 710320 1602629 := bbase (se 4 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 1602629 = 300493) (by norm_num)
theorem B1799293 : Blo 710320 1799293 := bbase (se 3 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 1799293 = 674735) (by norm_num)
theorem B1602701 : Blo 710320 1602701 := bbase (se 3 (by rfl) ⟨300506, by rfl⟩ : syracuseStep 1602701 = 601013) (by norm_num)
theorem B1602773 : Blo 710320 1602773 := bbase (se 7 (by rfl) ⟨18782, by rfl⟩ : syracuseStep 1602773 = 37565) (by norm_num)
theorem B1144037 : Blo 710320 1144037 := bbase (se 4 (by rfl) ⟨107253, by rfl⟩ : syracuseStep 1144037 = 214507) (by norm_num)
theorem B1799405 : Blo 710320 1799405 := bbase (se 3 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 1799405 = 674777) (by norm_num)
theorem B1602845 : Blo 710320 1602845 := bbase (se 3 (by rfl) ⟨300533, by rfl⟩ : syracuseStep 1602845 = 601067) (by norm_num)
theorem B1013077 : Blo 710320 1013077 := bbase (se 13 (by rfl) ⟨185, by rfl⟩ : syracuseStep 1013077 = 371) (by norm_num)
theorem B1602917 : Blo 710320 1602917 := bbase (se 4 (by rfl) ⟨150273, by rfl⟩ : syracuseStep 1602917 = 300547) (by norm_num)
theorem B1799597 : Blo 710320 1799597 := bbase (se 3 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 1799597 = 674849) (by norm_num)
theorem B1602989 : Blo 710320 1602989 := bbase (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) (by norm_num)
theorem B2029013 : Blo 710320 2029013 := bbase (se 7 (by rfl) ⟨23777, by rfl⟩ : syracuseStep 2029013 = 47555) (by norm_num)
theorem B1603061 : Blo 710320 1603061 := bbase (se 5 (by rfl) ⟨75143, by rfl⟩ : syracuseStep 1603061 = 150287) (by norm_num)
theorem B1603133 : Blo 710320 1603133 := bbase (se 3 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 1603133 = 601175) (by norm_num)
theorem B1603205 : Blo 710320 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B3602069 : Blo 710320 3602069 := bbase (se 6 (by rfl) ⟨84423, by rfl⟩ : syracuseStep 3602069 = 168847) (by norm_num)
theorem B1013413 : Blo 710320 1013413 := bbase (se 4 (by rfl) ⟨95007, by rfl⟩ : syracuseStep 1013413 = 190015) (by norm_num)
theorem B1603277 : Blo 710320 1603277 := bbase (se 3 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 1603277 = 601229) (by norm_num)
theorem B1373917 : Blo 710320 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B1799941 : Blo 710320 1799941 := bbase (se 4 (by rfl) ⟨168744, by rfl⟩ : syracuseStep 1799941 = 337489) (by norm_num)
theorem B1603349 : Blo 710320 1603349 := bbase (se 6 (by rfl) ⟨37578, by rfl⟩ : syracuseStep 1603349 = 75157) (by norm_num)
theorem B1603421 : Blo 710320 1603421 := bbase (se 3 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 1603421 = 601283) (by norm_num)
theorem B915305 : Blo 710320 915305 := bbase (se 2 (by rfl) ⟨343239, by rfl⟩ : syracuseStep 915305 = 686479) (by norm_num)
theorem B1800053 : Blo 710320 1800053 := bbase (se 5 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 1800053 = 168755) (by norm_num)
theorem B1013629 : Blo 710320 1013629 := bbase (se 3 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 1013629 = 380111) (by norm_num)
theorem B2029445 : Blo 710320 2029445 := bbase (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) (by norm_num)
theorem B1603493 : Blo 710320 1603493 := bbase (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) (by norm_num)
theorem B1603565 : Blo 710320 1603565 := bbase (se 3 (by rfl) ⟨300668, by rfl⟩ : syracuseStep 1603565 = 601337) (by norm_num)
theorem B1800245 : Blo 710320 1800245 := bbase (se 5 (by rfl) ⟨84386, by rfl⟩ : syracuseStep 1800245 = 168773) (by norm_num)
theorem B1603637 : Blo 710320 1603637 := bbase (se 5 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 1603637 = 150341) (by norm_num)
theorem B1603709 : Blo 710320 1603709 := bbase (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) (by norm_num)
theorem B2881669 : Blo 710320 2881669 := bbase (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) (by norm_num)
theorem B1603781 : Blo 710320 1603781 := bbase (se 4 (by rfl) ⟨150354, by rfl⟩ : syracuseStep 1603781 = 300709) (by norm_num)
theorem B1014005 : Blo 710320 1014005 := bbase (se 5 (by rfl) ⟨47531, by rfl⟩ : syracuseStep 1014005 = 95063) (by norm_num)
theorem B1603853 : Blo 710320 1603853 := bbase (se 3 (by rfl) ⟨300722, by rfl⟩ : syracuseStep 1603853 = 601445) (by norm_num)
theorem B1603925 : Blo 710320 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1800589 : Blo 710320 1800589 := bbase (se 3 (by rfl) ⟨337610, by rfl⟩ : syracuseStep 1800589 = 675221) (by norm_num)
theorem B1603997 : Blo 710320 1603997 := bbase (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) (by norm_num)
theorem B1604069 : Blo 710320 1604069 := bbase (se 4 (by rfl) ⟨150381, by rfl⟩ : syracuseStep 1604069 = 300763) (by norm_num)
theorem B1735157 : Blo 710320 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B1800701 : Blo 710320 1800701 := bbase (se 3 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 1800701 = 675263) (by norm_num)
theorem B1604141 : Blo 710320 1604141 := bbase (se 3 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 1604141 = 601553) (by norm_num)
theorem B2161205 : Blo 710320 2161205 := bbase (se 5 (by rfl) ⟨101306, by rfl⟩ : syracuseStep 2161205 = 202613) (by norm_num)
theorem B2030197 : Blo 710320 2030197 := bbase (se 5 (by rfl) ⟨95165, by rfl⟩ : syracuseStep 2030197 = 190331) (by norm_num)
theorem B1604213 : Blo 710320 1604213 := bbase (se 5 (by rfl) ⟨75197, by rfl⟩ : syracuseStep 1604213 = 150395) (by norm_num)
theorem B1440445 : Blo 710320 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B1800893 : Blo 710320 1800893 := bbase (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) (by norm_num)
theorem B1604285 : Blo 710320 1604285 := bbase (se 3 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 1604285 = 601607) (by norm_num)
theorem B1604357 : Blo 710320 1604357 := bbase (se 4 (by rfl) ⟨150408, by rfl⟩ : syracuseStep 1604357 = 300817) (by norm_num)
theorem B1669901 : Blo 710320 1669901 := bbase (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) (by norm_num)
theorem B1604429 : Blo 710320 1604429 := bbase (se 3 (by rfl) ⟨300830, by rfl⟩ : syracuseStep 1604429 = 601661) (by norm_num)
theorem B1604501 : Blo 710320 1604501 := bbase (se 6 (by rfl) ⟨37605, by rfl⟩ : syracuseStep 1604501 = 75211) (by norm_num)
theorem B3603365 : Blo 710320 3603365 := bbase (se 4 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 3603365 = 675631) (by norm_num)
theorem B1604573 : Blo 710320 1604573 := bbase (se 3 (by rfl) ⟨300857, by rfl⟩ : syracuseStep 1604573 = 601715) (by norm_num)
theorem B1801237 : Blo 710320 1801237 := bbase (se 6 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 1801237 = 84433) (by norm_num)
theorem B1604645 : Blo 710320 1604645 := bbase (se 4 (by rfl) ⟨150435, by rfl⟩ : syracuseStep 1604645 = 300871) (by norm_num)
theorem B1604717 : Blo 710320 1604717 := bbase (se 3 (by rfl) ⟨300884, by rfl⟩ : syracuseStep 1604717 = 601769) (by norm_num)
theorem B1801349 : Blo 710320 1801349 := bbase (se 4 (by rfl) ⟨168876, by rfl⟩ : syracuseStep 1801349 = 337753) (by norm_num)
theorem B1604789 : Blo 710320 1604789 := bbase (se 5 (by rfl) ⟨75224, by rfl⟩ : syracuseStep 1604789 = 150449) (by norm_num)
theorem B720121 : Blo 710320 720121 := bbase (se 2 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 720121 = 540091) (by norm_num)
theorem B1604861 : Blo 710320 1604861 := bbase (se 3 (by rfl) ⟨300911, by rfl⟩ : syracuseStep 1604861 = 601823) (by norm_num)
theorem B1801541 : Blo 710320 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B1604933 : Blo 710320 1604933 := bbase (se 4 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 1604933 = 300925) (by norm_num)
theorem B4062581 : Blo 710320 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B1605005 : Blo 710320 1605005 := bbase (se 3 (by rfl) ⟨300938, by rfl⟩ : syracuseStep 1605005 = 601877) (by norm_num)
theorem B1605077 : Blo 710320 1605077 := bbase (se 7 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 1605077 = 37619) (by norm_num)
theorem B1605149 : Blo 710320 1605149 := bbase (se 3 (by rfl) ⟨300965, by rfl⟩ : syracuseStep 1605149 = 601931) (by norm_num)
theorem B5766709 : Blo 710320 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B1605221 : Blo 710320 1605221 := bbase (se 4 (by rfl) ⟨150489, by rfl⟩ : syracuseStep 1605221 = 300979) (by norm_num)
theorem B1015429 : Blo 710320 1015429 := bbase (se 4 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 1015429 = 190393) (by norm_num)
theorem B1801885 : Blo 710320 1801885 := bbase (se 3 (by rfl) ⟨337853, by rfl⟩ : syracuseStep 1801885 = 675707) (by norm_num)
theorem B1605293 : Blo 710320 1605293 := bbase (se 3 (by rfl) ⟨300992, by rfl⟩ : syracuseStep 1605293 = 601985) (by norm_num)
theorem B1605365 : Blo 710320 1605365 := bbase (se 5 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 1605365 = 150503) (by norm_num)
theorem B1801997 : Blo 710320 1801997 := bbase (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) (by norm_num)
theorem B1605437 : Blo 710320 1605437 := bbase (se 3 (by rfl) ⟨301019, by rfl⟩ : syracuseStep 1605437 = 602039) (by norm_num)
theorem B1605509 : Blo 710320 1605509 := bbase (se 4 (by rfl) ⟨150516, by rfl⟩ : syracuseStep 1605509 = 301033) (by norm_num)
theorem B1802189 : Blo 710320 1802189 := bbase (se 3 (by rfl) ⟨337910, by rfl⟩ : syracuseStep 1802189 = 675821) (by norm_num)
theorem B1605581 : Blo 710320 1605581 := bbase (se 3 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 1605581 = 602093) (by norm_num)
theorem B3047381 : Blo 710320 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B1605635 : Blo 710320 1605635 := bstep (se 1 (by rfl) ⟨1204226, by rfl⟩ : syracuseStep 1605635 = 2408453) B2408453
theorem B1802321 : Blo 710320 1802321 := bstep (se 2 (by rfl) ⟨675870, by rfl⟩ : syracuseStep 1802321 = 1351741) B1351741
theorem B1015907 : Blo 710320 1015907 := bstep (se 1 (by rfl) ⟨761930, by rfl⟩ : syracuseStep 1015907 = 1523861) B1523861
theorem B1802371 : Blo 710320 1802371 := bstep (se 1 (by rfl) ⟨1351778, by rfl⟩ : syracuseStep 1802371 = 2703557) B2703557
theorem B1441955 : Blo 710320 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B9109745 : Blo 710320 9109745 := bstep (se 2 (by rfl) ⟨3416154, by rfl⟩ : syracuseStep 9109745 = 6832309) B6832309
theorem B1802513 : Blo 710320 1802513 := bstep (se 2 (by rfl) ⟨675942, by rfl⟩ : syracuseStep 1802513 = 1351885) B1351885
theorem B1605905 : Blo 710320 1605905 := bstep (se 2 (by rfl) ⟨602214, by rfl⟩ : syracuseStep 1605905 = 1204429) B1204429
theorem B1605923 : Blo 710320 1605923 := bstep (se 1 (by rfl) ⟨1204442, by rfl⟩ : syracuseStep 1605923 = 2408885) B2408885
theorem B1606193 : Blo 710320 1606193 := bstep (se 2 (by rfl) ⟨602322, by rfl⟩ : syracuseStep 1606193 = 1204645) B1204645
theorem B1606211 : Blo 710320 1606211 := bstep (se 1 (by rfl) ⟨1204658, by rfl⟩ : syracuseStep 1606211 = 2409317) B2409317
theorem B1016545 : Blo 710320 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B1114913 : Blo 710320 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B15434549 : Blo 710320 15434549 := bstep (se 5 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 15434549 = 1446989) B1446989
theorem B1606481 : Blo 710320 1606481 := bstep (se 2 (by rfl) ⟨602430, by rfl⟩ : syracuseStep 1606481 = 1204861) B1204861
theorem B1016659 : Blo 710320 1016659 := bstep (se 1 (by rfl) ⟨762494, by rfl⟩ : syracuseStep 1016659 = 1524989) B1524989
theorem B1606499 : Blo 710320 1606499 := bstep (se 1 (by rfl) ⟨1204874, by rfl⟩ : syracuseStep 1606499 = 2409749) B2409749
theorem B2032589 : Blo 710320 2032589 := bstep (se 3 (by rfl) ⟨381110, by rfl⟩ : syracuseStep 2032589 = 762221) B762221
theorem B1606769 : Blo 710320 1606769 := bstep (se 2 (by rfl) ⟨602538, by rfl⟩ : syracuseStep 1606769 = 1205077) B1205077
theorem B2032771 : Blo 710320 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B1606787 : Blo 710320 1606787 := bstep (se 1 (by rfl) ⟨1205090, by rfl⟩ : syracuseStep 1606787 = 2410181) B2410181
theorem B1803505 : Blo 710320 1803505 := bstep (se 2 (by rfl) ⟨676314, by rfl⟩ : syracuseStep 1803505 = 1352629) B1352629
theorem B3605795 : Blo 710320 3605795 := bstep (se 1 (by rfl) ⟨2704346, by rfl⟩ : syracuseStep 3605795 = 5408693) B5408693
theorem B2032931 : Blo 710320 2032931 := bstep (se 1 (by rfl) ⟨1524698, by rfl⟩ : syracuseStep 2032931 = 3049397) B3049397
theorem B16647565 : Blo 710320 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B1607057 : Blo 710320 1607057 := bstep (se 2 (by rfl) ⟨602646, by rfl⟩ : syracuseStep 1607057 = 1205293) B1205293
theorem B1607075 : Blo 710320 1607075 := bstep (se 1 (by rfl) ⟨1205306, by rfl⟩ : syracuseStep 1607075 = 2410613) B2410613
theorem B1803779 : Blo 710320 1803779 := bstep (se 1 (by rfl) ⟨1352834, by rfl⟩ : syracuseStep 1803779 = 2705669) B2705669
theorem B3049073 : Blo 710320 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B3049123 : Blo 710320 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B1803971 : Blo 710320 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B6686477 : Blo 710320 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B2164657 : Blo 710320 2164657 := bstep (se 2 (by rfl) ⟨811746, by rfl⟩ : syracuseStep 2164657 = 1623493) B1623493
theorem B23169077 : Blo 710320 23169077 := bstep (se 5 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 23169077 = 2172101) B2172101
theorem B3606605 : Blo 710320 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B2034001 : Blo 710320 2034001 := bstep (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) B1525501
theorem B1804913 : Blo 710320 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B1804963 : Blo 710320 1804963 := bstep (se 1 (by rfl) ⟨1353722, by rfl⟩ : syracuseStep 1804963 = 2707445) B2707445
theorem B4065997 : Blo 710320 4065997 := bstep (se 3 (by rfl) ⟨762374, by rfl⟩ : syracuseStep 4065997 = 1524749) B1524749
theorem B4557617 : Blo 710320 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B1805105 : Blo 710320 1805105 := bstep (se 2 (by rfl) ⟨676914, by rfl⟩ : syracuseStep 1805105 = 1353829) B1353829
theorem B9276229 : Blo 710320 9276229 := bstep (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) B1739293
theorem B1084385 : Blo 710320 1084385 := bstep (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) B813289
theorem B822323 : Blo 710320 822323 := bstep (se 1 (by rfl) ⟨616742, by rfl⟩ : syracuseStep 822323 = 1233485) B1233485
theorem B1707569 : Blo 710320 1707569 := bstep (se 2 (by rfl) ⟨640338, by rfl⟩ : syracuseStep 1707569 = 1280677) B1280677
theorem B1806097 : Blo 710320 1806097 := bstep (se 2 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 1806097 = 1354573) B1354573
theorem B1806371 : Blo 710320 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B10293389 : Blo 710320 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B4559075 : Blo 710320 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B1806563 : Blo 710320 1806563 := bstep (se 1 (by rfl) ⟨1354922, by rfl⟩ : syracuseStep 1806563 = 2709845) B2709845
theorem B1085699 : Blo 710320 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B3477809 : Blo 710320 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1446211 : Blo 710320 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B4886897 : Blo 710320 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B856499 : Blo 710320 856499 := bstep (se 1 (by rfl) ⟨642374, by rfl⟩ : syracuseStep 856499 = 1284749) B1284749
theorem B1216963 : Blo 710320 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B1282673 : Blo 710320 1282673 := bstep (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) B962005
theorem B4067981 : Blo 710320 4067981 := bstep (se 3 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 4067981 = 1525493) B1525493
theorem B2167565 : Blo 710320 2167565 := bstep (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) B812837
theorem B1446673 : Blo 710320 1446673 := bstep (se 2 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 1446673 = 1085005) B1085005
theorem B3609521 : Blo 710320 3609521 := bstep (se 2 (by rfl) ⟨1353570, by rfl⟩ : syracuseStep 3609521 = 2707141) B2707141
theorem B1348643 : Blo 710320 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B1807505 : Blo 710320 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B1807555 : Blo 710320 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B5772485 : Blo 710320 5772485 := bstep (se 4 (by rfl) ⟨541170, by rfl⟩ : syracuseStep 5772485 = 1082341) B1082341
theorem B4560077 : Blo 710320 4560077 := bstep (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) B1710029
theorem B1807697 : Blo 710320 1807697 := bstep (se 2 (by rfl) ⟨677886, by rfl⟩ : syracuseStep 1807697 = 1355773) B1355773
theorem B759299 : Blo 710320 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B2397869 : Blo 710320 2397869 := bstep (se 3 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 2397869 = 899201) B899201
theorem B9148085 : Blo 710320 9148085 := bstep (se 5 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 9148085 = 857633) B857633
theorem B2397923 : Blo 710320 2397923 := bstep (se 1 (by rfl) ⟨1798442, by rfl⟩ : syracuseStep 2397923 = 3596885) B3596885
theorem B1709923 : Blo 710320 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B1283971 : Blo 710320 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B2398193 : Blo 710320 2398193 := bstep (se 2 (by rfl) ⟨899322, by rfl⟩ : syracuseStep 2398193 = 1798645) B1798645
theorem B1349713 : Blo 710320 1349713 := bstep (se 2 (by rfl) ⟨506142, by rfl⟩ : syracuseStep 1349713 = 1012285) B1012285
theorem B2889827 : Blo 710320 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B989345 : Blo 710320 989345 := bstep (se 2 (by rfl) ⟨371004, by rfl⟩ : syracuseStep 989345 = 742009) B742009
theorem B760051 : Blo 710320 760051 := bstep (se 1 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 760051 = 1140077) B1140077
theorem B3610979 : Blo 710320 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B1284547 : Blo 710320 1284547 := bstep (se 1 (by rfl) ⟨963410, by rfl⟩ : syracuseStep 1284547 = 1926821) B1926821
theorem B2398733 : Blo 710320 2398733 := bstep (se 3 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 2398733 = 899525) B899525
theorem B2431505 : Blo 710320 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B2398787 : Blo 710320 2398787 := bstep (se 1 (by rfl) ⟨1799090, by rfl⟩ : syracuseStep 2398787 = 3598181) B3598181
theorem B2169425 : Blo 710320 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B2169571 : Blo 710320 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B2399057 : Blo 710320 2399057 := bstep (se 2 (by rfl) ⟨899646, by rfl⟩ : syracuseStep 2399057 = 1799293) B1799293
theorem B2169841 : Blo 710320 2169841 := bstep (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) B1627381
theorem B1154035 : Blo 710320 1154035 := bstep (se 1 (by rfl) ⟨865526, by rfl⟩ : syracuseStep 1154035 = 1731053) B1731053
theorem B1711153 : Blo 710320 1711153 := bstep (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) B1283365
theorem B1350769 : Blo 710320 1350769 := bstep (se 2 (by rfl) ⟨506538, by rfl⟩ : syracuseStep 1350769 = 1013077) B1013077
theorem B2890865 : Blo 710320 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B3611789 : Blo 710320 3611789 := bstep (se 3 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 3611789 = 1354421) B1354421
theorem B2464913 : Blo 710320 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B761059 : Blo 710320 761059 := bstep (se 1 (by rfl) ⟨570794, by rfl⟩ : syracuseStep 761059 = 1141589) B1141589
theorem B2596195 : Blo 710320 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B2399597 : Blo 710320 2399597 := bstep (se 3 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 2399597 = 899849) B899849
theorem B2399651 : Blo 710320 2399651 := bstep (se 1 (by rfl) ⟨1799738, by rfl⟩ : syracuseStep 2399651 = 3599477) B3599477
theorem B1351171 : Blo 710320 1351171 := bstep (se 1 (by rfl) ⟨1013378, by rfl⟩ : syracuseStep 1351171 = 2026757) B2026757
theorem B1351217 : Blo 710320 1351217 := bstep (se 2 (by rfl) ⟨506706, by rfl⟩ : syracuseStep 1351217 = 1013413) B1013413
theorem B2399921 : Blo 710320 2399921 := bstep (se 2 (by rfl) ⟨899970, by rfl⟩ : syracuseStep 2399921 = 1799941) B1799941
theorem B38969059 : Blo 710320 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B1351505 : Blo 710320 1351505 := bstep (se 2 (by rfl) ⟨506814, by rfl⟩ : syracuseStep 1351505 = 1013629) B1013629
theorem B1286161 : Blo 710320 1286161 := bstep (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) B964621
theorem B5415011 : Blo 710320 5415011 := bstep (se 1 (by rfl) ⟨4061258, by rfl⟩ : syracuseStep 5415011 = 8122517) B8122517
theorem B3842225 : Blo 710320 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B2400461 : Blo 710320 2400461 := bstep (se 3 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 2400461 = 900173) B900173
theorem B762067 : Blo 710320 762067 := bstep (se 1 (by rfl) ⟨571550, by rfl⟩ : syracuseStep 762067 = 1143101) B1143101
theorem B2400515 : Blo 710320 2400515 := bstep (se 1 (by rfl) ⟨1800386, by rfl⟩ : syracuseStep 2400515 = 3600773) B3600773
theorem B2400785 : Blo 710320 2400785 := bstep (se 2 (by rfl) ⟨900294, by rfl⟩ : syracuseStep 2400785 = 1800589) B1800589
theorem B1352227 : Blo 710320 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B762691 : Blo 710320 762691 := bstep (se 1 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 762691 = 1144037) B1144037
theorem B1352675 : Blo 710320 1352675 := bstep (se 1 (by rfl) ⟨1014506, by rfl⟩ : syracuseStep 1352675 = 2029013) B2029013
theorem B2401325 : Blo 710320 2401325 := bstep (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) B900497
theorem B2401379 : Blo 710320 2401379 := bstep (se 1 (by rfl) ⟨1801034, by rfl⟩ : syracuseStep 2401379 = 3602069) B3602069
theorem B2892941 : Blo 710320 2892941 := bstep (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) B1084853
theorem B1352963 : Blo 710320 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B2401649 : Blo 710320 2401649 := bstep (se 2 (by rfl) ⟨900618, by rfl⟩ : syracuseStep 2401649 = 1801237) B1801237
theorem B12166541 : Blo 710320 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B1156771 : Blo 710320 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B6072205 : Blo 710320 6072205 := bstep (se 3 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 6072205 = 2277077) B2277077
theorem B2402189 : Blo 710320 2402189 := bstep (se 3 (by rfl) ⟨450410, by rfl⟩ : syracuseStep 2402189 = 900821) B900821
theorem B2402243 : Blo 710320 2402243 := bstep (se 1 (by rfl) ⟨1801682, by rfl⟩ : syracuseStep 2402243 = 3603365) B3603365
theorem B3614705 : Blo 710320 3614705 := bstep (se 2 (by rfl) ⟨1355514, by rfl⟩ : syracuseStep 3614705 = 2711029) B2711029
theorem B26683505 : Blo 710320 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B1353905 : Blo 710320 1353905 := bstep (se 2 (by rfl) ⟨507714, by rfl⟩ : syracuseStep 1353905 = 1015429) B1015429
theorem B2697421 : Blo 710320 2697421 := bstep (se 3 (by rfl) ⟨505766, by rfl⟩ : syracuseStep 2697421 = 1011533) B1011533
theorem B2402513 : Blo 710320 2402513 := bstep (se 2 (by rfl) ⟨900942, by rfl⟩ : syracuseStep 2402513 = 1801885) B1801885
theorem B7416035 : Blo 710320 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B8235377 : Blo 710320 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B1518257 : Blo 710320 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B2403053 : Blo 710320 2403053 := bstep (se 3 (by rfl) ⟨450572, by rfl⟩ : syracuseStep 2403053 = 901145) B901145
theorem B961313 : Blo 710320 961313 := bstep (se 2 (by rfl) ⟨360492, by rfl⟩ : syracuseStep 961313 = 720985) B720985
theorem B2403107 : Blo 710320 2403107 := bstep (se 1 (by rfl) ⟨1802330, by rfl⟩ : syracuseStep 2403107 = 3604661) B3604661
theorem B2566961 : Blo 710320 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B1157971 : Blo 710320 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B1715057 : Blo 710320 1715057 := bstep (se 2 (by rfl) ⟨643146, by rfl⟩ : syracuseStep 1715057 = 1286293) B1286293
theorem B961475 : Blo 710320 961475 := bstep (se 1 (by rfl) ⟨721106, by rfl⟩ : syracuseStep 961475 = 1442213) B1442213
theorem B2698211 : Blo 710320 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B961507 : Blo 710320 961507 := bstep (se 1 (by rfl) ⟨721130, by rfl⟩ : syracuseStep 961507 = 1442261) B1442261
theorem B2403377 : Blo 710320 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B1354801 : Blo 710320 1354801 := bstep (se 2 (by rfl) ⟨508050, by rfl⟩ : syracuseStep 1354801 = 1016101) B1016101
theorem B1518659 : Blo 710320 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B6073541 : Blo 710320 6073541 := bstep (se 4 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 6073541 = 1138789) B1138789
theorem B1354961 : Blo 710320 1354961 := bstep (se 2 (by rfl) ⟨508110, by rfl⟩ : syracuseStep 1354961 = 1016221) B1016221
theorem B3616163 : Blo 710320 3616163 := bstep (se 1 (by rfl) ⟨2712122, by rfl⟩ : syracuseStep 3616163 = 5424245) B5424245
theorem B1715651 : Blo 710320 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B962065 : Blo 710320 962065 := bstep (se 2 (by rfl) ⟨360774, by rfl⟩ : syracuseStep 962065 = 721549) B721549
theorem B1715747 : Blo 710320 1715747 := bstep (se 1 (by rfl) ⟨1286810, by rfl⟩ : syracuseStep 1715747 = 2573621) B2573621
theorem B962113 : Blo 710320 962113 := bstep (se 2 (by rfl) ⟨360792, by rfl⟩ : syracuseStep 962113 = 721585) B721585
theorem B2403917 : Blo 710320 2403917 := bstep (se 3 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 2403917 = 901469) B901469
theorem B1355363 : Blo 710320 1355363 := bstep (se 1 (by rfl) ⟨1016522, by rfl⟩ : syracuseStep 1355363 = 2033045) B2033045
theorem B2698865 : Blo 710320 2698865 := bstep (se 2 (by rfl) ⟨1012074, by rfl⟩ : syracuseStep 2698865 = 2024149) B2024149
theorem B2403971 : Blo 710320 2403971 := bstep (se 1 (by rfl) ⟨1802978, by rfl⟩ : syracuseStep 2403971 = 3605957) B3605957
theorem B2404241 : Blo 710320 2404241 := bstep (se 2 (by rfl) ⟨901590, by rfl⟩ : syracuseStep 2404241 = 1803181) B1803181
theorem B1519555 : Blo 710320 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B5124323 : Blo 710320 5124323 := bstep (se 1 (by rfl) ⟨3843242, by rfl⟩ : syracuseStep 5124323 = 7686485) B7686485
theorem B799123 : Blo 710320 799123 := bstep (se 1 (by rfl) ⟨599342, by rfl⟩ : syracuseStep 799123 = 1198685) B1198685
theorem B2404781 : Blo 710320 2404781 := bstep (se 3 (by rfl) ⟨450896, by rfl⟩ : syracuseStep 2404781 = 901793) B901793
theorem B13152709 : Blo 710320 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B2404835 : Blo 710320 2404835 := bstep (se 1 (by rfl) ⟨1803626, by rfl⟩ : syracuseStep 2404835 = 3607253) B3607253
theorem B799267 : Blo 710320 799267 := bstep (se 1 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 799267 = 1198901) B1198901
theorem B799411 : Blo 710320 799411 := bstep (se 1 (by rfl) ⟨599558, by rfl⟩ : syracuseStep 799411 = 1199117) B1199117
theorem B2405105 : Blo 710320 2405105 := bstep (se 2 (by rfl) ⟨901914, by rfl⟩ : syracuseStep 2405105 = 1803829) B1803829
theorem B799555 : Blo 710320 799555 := bstep (se 1 (by rfl) ⟨599666, by rfl⟩ : syracuseStep 799555 = 1199333) B1199333
theorem B799699 : Blo 710320 799699 := bstep (se 1 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 799699 = 1199549) B1199549
theorem B2700323 : Blo 710320 2700323 := bstep (se 1 (by rfl) ⟨2025242, by rfl⟩ : syracuseStep 2700323 = 4050485) B4050485
theorem B2700337 : Blo 710320 2700337 := bstep (se 2 (by rfl) ⟨1012626, by rfl⟩ : syracuseStep 2700337 = 2025253) B2025253
theorem B799843 : Blo 710320 799843 := bstep (se 1 (by rfl) ⟨599882, by rfl⟩ : syracuseStep 799843 = 1199765) B1199765
theorem B1946755 : Blo 710320 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B1520785 : Blo 710320 1520785 := bstep (se 2 (by rfl) ⟨570294, by rfl⟩ : syracuseStep 1520785 = 1140589) B1140589
theorem B799987 : Blo 710320 799987 := bstep (se 1 (by rfl) ⟨599990, by rfl⟩ : syracuseStep 799987 = 1199981) B1199981
theorem B2405645 : Blo 710320 2405645 := bstep (se 3 (by rfl) ⟨451058, by rfl⟩ : syracuseStep 2405645 = 902117) B902117
theorem B2405699 : Blo 710320 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B5420357 : Blo 710320 5420357 := bstep (se 4 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 5420357 = 1016317) B1016317
theorem B800131 : Blo 710320 800131 := bstep (se 1 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 800131 = 1200197) B1200197
theorem B4568561 : Blo 710320 4568561 := bstep (se 2 (by rfl) ⟨1713210, by rfl⟩ : syracuseStep 4568561 = 3426421) B3426421
theorem B800275 : Blo 710320 800275 := bstep (se 1 (by rfl) ⟨600206, by rfl⟩ : syracuseStep 800275 = 1200413) B1200413
theorem B2405969 : Blo 710320 2405969 := bstep (se 2 (by rfl) ⟨902238, by rfl⟩ : syracuseStep 2405969 = 1804477) B1804477
theorem B964243 : Blo 710320 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B800419 : Blo 710320 800419 := bstep (se 1 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 800419 = 1200629) B1200629
theorem B866003 : Blo 710320 866003 := bstep (se 1 (by rfl) ⟨649502, by rfl⟩ : syracuseStep 866003 = 1299005) B1299005
theorem B7812877 : Blo 710320 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B800563 : Blo 710320 800563 := bstep (se 1 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 800563 = 1200845) B1200845
theorem B800707 : Blo 710320 800707 := bstep (se 1 (by rfl) ⟨600530, by rfl⟩ : syracuseStep 800707 = 1201061) B1201061
theorem B800851 : Blo 710320 800851 := bstep (se 1 (by rfl) ⟨600638, by rfl⟩ : syracuseStep 800851 = 1201277) B1201277
theorem B2406509 : Blo 710320 2406509 := bstep (se 3 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 2406509 = 902441) B902441
theorem B2406563 : Blo 710320 2406563 := bstep (se 1 (by rfl) ⟨1804922, by rfl⟩ : syracuseStep 2406563 = 3609845) B3609845
theorem B800995 : Blo 710320 800995 := bstep (se 1 (by rfl) ⟨600746, by rfl⟩ : syracuseStep 800995 = 1201493) B1201493
theorem B899363 : Blo 710320 899363 := bstep (se 1 (by rfl) ⟨674522, by rfl⟩ : syracuseStep 899363 = 1349045) B1349045
theorem B2472241 : Blo 710320 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B964963 : Blo 710320 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B801139 : Blo 710320 801139 := bstep (se 1 (by rfl) ⟨600854, by rfl⟩ : syracuseStep 801139 = 1201709) B1201709
theorem B2406833 : Blo 710320 2406833 := bstep (se 2 (by rfl) ⟨902562, by rfl⟩ : syracuseStep 2406833 = 1805125) B1805125
theorem B2701795 : Blo 710320 2701795 := bstep (se 1 (by rfl) ⟨2026346, by rfl⟩ : syracuseStep 2701795 = 4052693) B4052693
theorem B801283 : Blo 710320 801283 := bstep (se 1 (by rfl) ⟨600962, by rfl⟩ : syracuseStep 801283 = 1201925) B1201925
theorem B4569635 : Blo 710320 4569635 := bstep (se 1 (by rfl) ⟨3427226, by rfl⟩ : syracuseStep 4569635 = 6854453) B6854453
theorem B1522289 : Blo 710320 1522289 := bstep (se 2 (by rfl) ⟨570858, by rfl⟩ : syracuseStep 1522289 = 1141717) B1141717
theorem B1522307 : Blo 710320 1522307 := bstep (se 1 (by rfl) ⟨1141730, by rfl⟩ : syracuseStep 1522307 = 2283461) B2283461
theorem B801427 : Blo 710320 801427 := bstep (se 1 (by rfl) ⟨601070, by rfl⟩ : syracuseStep 801427 = 1202141) B1202141
theorem B71219989 : Blo 710320 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B801571 : Blo 710320 801571 := bstep (se 1 (by rfl) ⟨601178, by rfl⟩ : syracuseStep 801571 = 1202357) B1202357
theorem B3849059 : Blo 710320 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B801715 : Blo 710320 801715 := bstep (se 1 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 801715 = 1202573) B1202573
theorem B2407373 : Blo 710320 2407373 := bstep (se 3 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 2407373 = 902765) B902765
theorem B900067 : Blo 710320 900067 := bstep (se 1 (by rfl) ⟨675050, by rfl⟩ : syracuseStep 900067 = 1350101) B1350101
theorem B2407427 : Blo 710320 2407427 := bstep (se 1 (by rfl) ⟨1805570, by rfl⟩ : syracuseStep 2407427 = 3611141) B3611141
theorem B4045859 : Blo 710320 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B2276387 : Blo 710320 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B900163 : Blo 710320 900163 := bstep (se 1 (by rfl) ⟨675122, by rfl⟩ : syracuseStep 900163 = 1350245) B1350245
theorem B801859 : Blo 710320 801859 := bstep (se 1 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 801859 = 1202789) B1202789
theorem B802003 : Blo 710320 802003 := bstep (se 1 (by rfl) ⟨601502, by rfl⟩ : syracuseStep 802003 = 1203005) B1203005
theorem B2407697 : Blo 710320 2407697 := bstep (se 2 (by rfl) ⟨902886, by rfl⟩ : syracuseStep 2407697 = 1805773) B1805773
theorem B2276657 : Blo 710320 2276657 := bstep (se 2 (by rfl) ⟨853746, by rfl⟩ : syracuseStep 2276657 = 1707493) B1707493
theorem B802147 : Blo 710320 802147 := bstep (se 1 (by rfl) ⟨601610, by rfl⟩ : syracuseStep 802147 = 1203221) B1203221
theorem B802291 : Blo 710320 802291 := bstep (se 1 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 802291 = 1203437) B1203437
theorem B900659 : Blo 710320 900659 := bstep (se 1 (by rfl) ⟨675494, by rfl⟩ : syracuseStep 900659 = 1350989) B1350989
theorem B2440813 : Blo 710320 2440813 := bstep (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) B915305
theorem B802435 : Blo 710320 802435 := bstep (se 1 (by rfl) ⟨601826, by rfl⟩ : syracuseStep 802435 = 1203653) B1203653
theorem B802579 : Blo 710320 802579 := bstep (se 1 (by rfl) ⟨601934, by rfl⟩ : syracuseStep 802579 = 1203869) B1203869
theorem B2408237 : Blo 710320 2408237 := bstep (se 3 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 2408237 = 903089) B903089
theorem B2408291 : Blo 710320 2408291 := bstep (se 1 (by rfl) ⟨1806218, by rfl⟩ : syracuseStep 2408291 = 3612437) B3612437
theorem B802723 : Blo 710320 802723 := bstep (se 1 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 802723 = 1204085) B1204085
theorem B4046861 : Blo 710320 4046861 := bstep (se 3 (by rfl) ⟨758786, by rfl⟩ : syracuseStep 4046861 = 1517573) B1517573
theorem B802867 : Blo 710320 802867 := bstep (se 1 (by rfl) ⟨602150, by rfl⟩ : syracuseStep 802867 = 1204301) B1204301
theorem B6078563 : Blo 710320 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B2408561 : Blo 710320 2408561 := bstep (se 2 (by rfl) ⟨903210, by rfl⟩ : syracuseStep 2408561 = 1806421) B1806421
theorem B9748621 : Blo 710320 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B803011 : Blo 710320 803011 := bstep (se 1 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 803011 = 1204517) B1204517
theorem B901363 : Blo 710320 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B901459 : Blo 710320 901459 := bstep (se 1 (by rfl) ⟨676094, by rfl⟩ : syracuseStep 901459 = 1352189) B1352189
theorem B803155 : Blo 710320 803155 := bstep (se 1 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 803155 = 1204733) B1204733
theorem B1622435 : Blo 710320 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B803299 : Blo 710320 803299 := bstep (se 1 (by rfl) ⟨602474, by rfl⟩ : syracuseStep 803299 = 1204949) B1204949
theorem B1065491 : Blo 710320 1065491 := bstep (se 1 (by rfl) ⟨799118, by rfl⟩ : syracuseStep 1065491 = 1598237) B1598237
theorem B1065521 : Blo 710320 1065521 := bstep (se 2 (by rfl) ⟨399570, by rfl⟩ : syracuseStep 1065521 = 799141) B799141
theorem B1065539 : Blo 710320 1065539 := bstep (se 1 (by rfl) ⟨799154, by rfl⟩ : syracuseStep 1065539 = 1598309) B1598309
theorem B1622609 : Blo 710320 1622609 := bstep (se 2 (by rfl) ⟨608478, by rfl⟩ : syracuseStep 1622609 = 1216957) B1216957
theorem B1524305 : Blo 710320 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B1065569 : Blo 710320 1065569 := bstep (se 2 (by rfl) ⟨399588, by rfl⟩ : syracuseStep 1065569 = 799177) B799177
theorem B1065587 : Blo 710320 1065587 := bstep (se 1 (by rfl) ⟨799190, by rfl⟩ : syracuseStep 1065587 = 1598381) B1598381
theorem B803443 : Blo 710320 803443 := bstep (se 1 (by rfl) ⟨602582, by rfl⟩ : syracuseStep 803443 = 1205165) B1205165
theorem B2704013 : Blo 710320 2704013 := bstep (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) B1014005
theorem B2409101 : Blo 710320 2409101 := bstep (se 3 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 2409101 = 903413) B903413
theorem B1065617 : Blo 710320 1065617 := bstep (se 2 (by rfl) ⟨399606, by rfl⟩ : syracuseStep 1065617 = 799213) B799213
theorem B1065635 : Blo 710320 1065635 := bstep (se 1 (by rfl) ⟨799226, by rfl⟩ : syracuseStep 1065635 = 1598453) B1598453
theorem B1065665 : Blo 710320 1065665 := bstep (se 2 (by rfl) ⟨399624, by rfl⟩ : syracuseStep 1065665 = 799249) B799249
theorem B2409155 : Blo 710320 2409155 := bstep (se 1 (by rfl) ⟨1806866, by rfl⟩ : syracuseStep 2409155 = 3613733) B3613733
theorem B1065683 : Blo 710320 1065683 := bstep (se 1 (by rfl) ⟨799262, by rfl⟩ : syracuseStep 1065683 = 1598525) B1598525
theorem B1065713 : Blo 710320 1065713 := bstep (se 2 (by rfl) ⟨399642, by rfl⟩ : syracuseStep 1065713 = 799285) B799285
theorem B1065731 : Blo 710320 1065731 := bstep (se 1 (by rfl) ⟨799298, by rfl⟩ : syracuseStep 1065731 = 1598597) B1598597
theorem B803587 : Blo 710320 803587 := bstep (se 1 (by rfl) ⟨602690, by rfl⟩ : syracuseStep 803587 = 1205381) B1205381
theorem B1065761 : Blo 710320 1065761 := bstep (se 2 (by rfl) ⟨399660, by rfl⟩ : syracuseStep 1065761 = 799321) B799321
theorem B1065779 : Blo 710320 1065779 := bstep (se 1 (by rfl) ⟨799334, by rfl⟩ : syracuseStep 1065779 = 1598669) B1598669
theorem B901955 : Blo 710320 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B1065809 : Blo 710320 1065809 := bstep (se 2 (by rfl) ⟨399678, by rfl⟩ : syracuseStep 1065809 = 799357) B799357
theorem B1065827 : Blo 710320 1065827 := bstep (se 1 (by rfl) ⟨799370, by rfl⟩ : syracuseStep 1065827 = 1598741) B1598741
theorem B1065857 : Blo 710320 1065857 := bstep (se 2 (by rfl) ⟨399696, by rfl⟩ : syracuseStep 1065857 = 799393) B799393
theorem B1065875 : Blo 710320 1065875 := bstep (se 1 (by rfl) ⟨799406, by rfl⟩ : syracuseStep 1065875 = 1598813) B1598813
theorem B1065905 : Blo 710320 1065905 := bstep (se 2 (by rfl) ⟨399714, by rfl⟩ : syracuseStep 1065905 = 799429) B799429
theorem B1065923 : Blo 710320 1065923 := bstep (se 1 (by rfl) ⟨799442, by rfl⟩ : syracuseStep 1065923 = 1598885) B1598885
theorem B2409425 : Blo 710320 2409425 := bstep (se 2 (by rfl) ⟨903534, by rfl⟩ : syracuseStep 2409425 = 1807069) B1807069
theorem B1065953 : Blo 710320 1065953 := bstep (se 2 (by rfl) ⟨399732, by rfl⟩ : syracuseStep 1065953 = 799465) B799465
theorem B1065971 : Blo 710320 1065971 := bstep (se 1 (by rfl) ⟨799478, by rfl⟩ : syracuseStep 1065971 = 1598957) B1598957
theorem B1066001 : Blo 710320 1066001 := bstep (se 2 (by rfl) ⟨399750, by rfl⟩ : syracuseStep 1066001 = 799501) B799501
theorem B1066019 : Blo 710320 1066019 := bstep (se 1 (by rfl) ⟨799514, by rfl⟩ : syracuseStep 1066019 = 1599029) B1599029
theorem B1066049 : Blo 710320 1066049 := bstep (se 2 (by rfl) ⟨399768, by rfl⟩ : syracuseStep 1066049 = 799537) B799537
theorem B1066067 : Blo 710320 1066067 := bstep (se 1 (by rfl) ⟨799550, by rfl⟩ : syracuseStep 1066067 = 1599101) B1599101
theorem B1524835 : Blo 710320 1524835 := bstep (se 1 (by rfl) ⟨1143626, by rfl⟩ : syracuseStep 1524835 = 2287253) B2287253
theorem B1066097 : Blo 710320 1066097 := bstep (se 2 (by rfl) ⟨399786, by rfl⟩ : syracuseStep 1066097 = 799573) B799573
theorem B1066115 : Blo 710320 1066115 := bstep (se 1 (by rfl) ⟨799586, by rfl⟩ : syracuseStep 1066115 = 1599173) B1599173
theorem B1066145 : Blo 710320 1066145 := bstep (se 2 (by rfl) ⟨399804, by rfl⟩ : syracuseStep 1066145 = 799609) B799609
theorem B1623203 : Blo 710320 1623203 := bstep (se 1 (by rfl) ⟨1217402, by rfl⟩ : syracuseStep 1623203 = 2434805) B2434805
theorem B1066163 : Blo 710320 1066163 := bstep (se 1 (by rfl) ⟨799622, by rfl⟩ : syracuseStep 1066163 = 1599245) B1599245
theorem B1066193 : Blo 710320 1066193 := bstep (se 2 (by rfl) ⟨399822, by rfl⟩ : syracuseStep 1066193 = 799645) B799645
theorem B1066211 : Blo 710320 1066211 := bstep (se 1 (by rfl) ⟨799658, by rfl⟩ : syracuseStep 1066211 = 1599317) B1599317
theorem B1066241 : Blo 710320 1066241 := bstep (se 2 (by rfl) ⟨399840, by rfl⟩ : syracuseStep 1066241 = 799681) B799681
theorem B1066259 : Blo 710320 1066259 := bstep (se 1 (by rfl) ⟨799694, by rfl⟩ : syracuseStep 1066259 = 1599389) B1599389
theorem B1066289 : Blo 710320 1066289 := bstep (se 2 (by rfl) ⟨399858, by rfl⟩ : syracuseStep 1066289 = 799717) B799717
theorem B1066307 : Blo 710320 1066307 := bstep (se 1 (by rfl) ⟨799730, by rfl⟩ : syracuseStep 1066307 = 1599461) B1599461
theorem B2082115 : Blo 710320 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B1066337 : Blo 710320 1066337 := bstep (se 2 (by rfl) ⟨399876, by rfl⟩ : syracuseStep 1066337 = 799753) B799753
theorem B1066355 : Blo 710320 1066355 := bstep (se 1 (by rfl) ⟨799766, by rfl⟩ : syracuseStep 1066355 = 1599533) B1599533
theorem B1066385 : Blo 710320 1066385 := bstep (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) B799789
theorem B1066403 : Blo 710320 1066403 := bstep (se 1 (by rfl) ⟨799802, by rfl⟩ : syracuseStep 1066403 = 1599605) B1599605
theorem B1066433 : Blo 710320 1066433 := bstep (se 2 (by rfl) ⟨399912, by rfl⟩ : syracuseStep 1066433 = 799825) B799825
theorem B3851717 : Blo 710320 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B1951181 : Blo 710320 1951181 := bstep (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) B731693
theorem B1066451 : Blo 710320 1066451 := bstep (se 1 (by rfl) ⟨799838, by rfl⟩ : syracuseStep 1066451 = 1599677) B1599677
theorem B2409965 : Blo 710320 2409965 := bstep (se 3 (by rfl) ⟨451868, by rfl⟩ : syracuseStep 2409965 = 903737) B903737
theorem B1066481 : Blo 710320 1066481 := bstep (se 2 (by rfl) ⟨399930, by rfl⟩ : syracuseStep 1066481 = 799861) B799861
theorem B1066499 : Blo 710320 1066499 := bstep (se 1 (by rfl) ⟨799874, by rfl⟩ : syracuseStep 1066499 = 1599749) B1599749
theorem B902659 : Blo 710320 902659 := bstep (se 1 (by rfl) ⟨676994, by rfl⟩ : syracuseStep 902659 = 1353989) B1353989
theorem B1066529 : Blo 710320 1066529 := bstep (se 2 (by rfl) ⟨399948, by rfl⟩ : syracuseStep 1066529 = 799897) B799897
theorem B2410019 : Blo 710320 2410019 := bstep (se 1 (by rfl) ⟨1807514, by rfl⟩ : syracuseStep 2410019 = 3615029) B3615029
theorem B1066547 : Blo 710320 1066547 := bstep (se 1 (by rfl) ⟨799910, by rfl⟩ : syracuseStep 1066547 = 1599821) B1599821
theorem B1066577 : Blo 710320 1066577 := bstep (se 2 (by rfl) ⟨399966, by rfl⟩ : syracuseStep 1066577 = 799933) B799933
theorem B1066595 : Blo 710320 1066595 := bstep (se 1 (by rfl) ⟨799946, by rfl⟩ : syracuseStep 1066595 = 1599893) B1599893
theorem B902755 : Blo 710320 902755 := bstep (se 1 (by rfl) ⟨677066, by rfl⟩ : syracuseStep 902755 = 1354133) B1354133
theorem B1066625 : Blo 710320 1066625 := bstep (se 2 (by rfl) ⟨399984, by rfl⟩ : syracuseStep 1066625 = 799969) B799969
theorem B1066643 : Blo 710320 1066643 := bstep (se 1 (by rfl) ⟨799982, by rfl⟩ : syracuseStep 1066643 = 1599965) B1599965
theorem B1066673 : Blo 710320 1066673 := bstep (se 2 (by rfl) ⟨400002, by rfl⟩ : syracuseStep 1066673 = 800005) B800005
theorem B1066691 : Blo 710320 1066691 := bstep (se 1 (by rfl) ⟨800018, by rfl⟩ : syracuseStep 1066691 = 1600037) B1600037
theorem B2279117 : Blo 710320 2279117 := bstep (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) B854669
theorem B1066721 : Blo 710320 1066721 := bstep (se 2 (by rfl) ⟨400020, by rfl⟩ : syracuseStep 1066721 = 800041) B800041
theorem B1066739 : Blo 710320 1066739 := bstep (se 1 (by rfl) ⟨800054, by rfl⟩ : syracuseStep 1066739 = 1600109) B1600109
theorem B1066769 : Blo 710320 1066769 := bstep (se 2 (by rfl) ⟨400038, by rfl⟩ : syracuseStep 1066769 = 800077) B800077
theorem B1066787 : Blo 710320 1066787 := bstep (se 1 (by rfl) ⟨800090, by rfl⟩ : syracuseStep 1066787 = 1600181) B1600181
theorem B2410289 : Blo 710320 2410289 := bstep (se 2 (by rfl) ⟨903858, by rfl⟩ : syracuseStep 2410289 = 1807717) B1807717
theorem B12994357 : Blo 710320 12994357 := bstep (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) B1218221
theorem B1066817 : Blo 710320 1066817 := bstep (se 2 (by rfl) ⟨400056, by rfl⟩ : syracuseStep 1066817 = 800113) B800113
theorem B1066835 : Blo 710320 1066835 := bstep (se 1 (by rfl) ⟨800126, by rfl⟩ : syracuseStep 1066835 = 1600253) B1600253
theorem B1066865 : Blo 710320 1066865 := bstep (se 2 (by rfl) ⟨400074, by rfl⟩ : syracuseStep 1066865 = 800149) B800149
theorem B1066883 : Blo 710320 1066883 := bstep (se 1 (by rfl) ⟨800162, by rfl⟩ : syracuseStep 1066883 = 1600325) B1600325
theorem B1066913 : Blo 710320 1066913 := bstep (se 2 (by rfl) ⟨400092, by rfl⟩ : syracuseStep 1066913 = 800185) B800185
theorem B1066931 : Blo 710320 1066931 := bstep (se 1 (by rfl) ⟨800198, by rfl⟩ : syracuseStep 1066931 = 1600397) B1600397
theorem B1066961 : Blo 710320 1066961 := bstep (se 2 (by rfl) ⟨400110, by rfl⟩ : syracuseStep 1066961 = 800221) B800221
theorem B1066979 : Blo 710320 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B3655651 : Blo 710320 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B1067009 : Blo 710320 1067009 := bstep (se 2 (by rfl) ⟨400128, by rfl⟩ : syracuseStep 1067009 = 800257) B800257
theorem B1067027 : Blo 710320 1067027 := bstep (se 1 (by rfl) ⟨800270, by rfl⟩ : syracuseStep 1067027 = 1600541) B1600541
theorem B1067057 : Blo 710320 1067057 := bstep (se 2 (by rfl) ⟨400146, by rfl⟩ : syracuseStep 1067057 = 800293) B800293
theorem B1067075 : Blo 710320 1067075 := bstep (se 1 (by rfl) ⟨800306, by rfl⟩ : syracuseStep 1067075 = 1600613) B1600613
theorem B903251 : Blo 710320 903251 := bstep (se 1 (by rfl) ⟨677438, by rfl⟩ : syracuseStep 903251 = 1354877) B1354877
theorem B1067105 : Blo 710320 1067105 := bstep (se 2 (by rfl) ⟨400164, by rfl⟩ : syracuseStep 1067105 = 800329) B800329
theorem B1067123 : Blo 710320 1067123 := bstep (se 1 (by rfl) ⟨800342, by rfl⟩ : syracuseStep 1067123 = 1600685) B1600685
theorem B1067153 : Blo 710320 1067153 := bstep (se 2 (by rfl) ⟨400182, by rfl⟩ : syracuseStep 1067153 = 800365) B800365
theorem B1067171 : Blo 710320 1067171 := bstep (se 1 (by rfl) ⟨800378, by rfl⟩ : syracuseStep 1067171 = 1600757) B1600757
theorem B1067201 : Blo 710320 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B1067219 : Blo 710320 1067219 := bstep (se 1 (by rfl) ⟨800414, by rfl⟩ : syracuseStep 1067219 = 1600829) B1600829
theorem B1067249 : Blo 710320 1067249 := bstep (se 2 (by rfl) ⟨400218, by rfl⟩ : syracuseStep 1067249 = 800437) B800437
theorem B1067267 : Blo 710320 1067267 := bstep (se 1 (by rfl) ⟨800450, by rfl⟩ : syracuseStep 1067267 = 1600901) B1600901
theorem B1067297 : Blo 710320 1067297 := bstep (se 2 (by rfl) ⟨400236, by rfl⟩ : syracuseStep 1067297 = 800473) B800473
theorem B1624369 : Blo 710320 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B1067315 : Blo 710320 1067315 := bstep (se 1 (by rfl) ⟨800486, by rfl⟩ : syracuseStep 1067315 = 1600973) B1600973
theorem B2410829 : Blo 710320 2410829 := bstep (se 3 (by rfl) ⟨452030, by rfl⟩ : syracuseStep 2410829 = 904061) B904061
theorem B1067345 : Blo 710320 1067345 := bstep (se 2 (by rfl) ⟨400254, by rfl⟩ : syracuseStep 1067345 = 800509) B800509
theorem B1067363 : Blo 710320 1067363 := bstep (se 1 (by rfl) ⟨800522, by rfl⟩ : syracuseStep 1067363 = 1601045) B1601045
theorem B11553137 : Blo 710320 11553137 := bstep (se 2 (by rfl) ⟨4332426, by rfl⟩ : syracuseStep 11553137 = 8664853) B8664853
theorem B1067393 : Blo 710320 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B1067411 : Blo 710320 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B1067441 : Blo 710320 1067441 := bstep (se 2 (by rfl) ⟨400290, by rfl⟩ : syracuseStep 1067441 = 800581) B800581
theorem B1067459 : Blo 710320 1067459 := bstep (se 1 (by rfl) ⟨800594, by rfl⟩ : syracuseStep 1067459 = 1601189) B1601189
theorem B1067489 : Blo 710320 1067489 := bstep (se 2 (by rfl) ⟨400308, by rfl⟩ : syracuseStep 1067489 = 800617) B800617
theorem B1067507 : Blo 710320 1067507 := bstep (se 1 (by rfl) ⟨800630, by rfl⟩ : syracuseStep 1067507 = 1601261) B1601261
theorem B1067537 : Blo 710320 1067537 := bstep (se 2 (by rfl) ⟨400326, by rfl⟩ : syracuseStep 1067537 = 800653) B800653
theorem B1067555 : Blo 710320 1067555 := bstep (se 1 (by rfl) ⟨800666, by rfl⟩ : syracuseStep 1067555 = 1601333) B1601333
theorem B1067585 : Blo 710320 1067585 := bstep (se 2 (by rfl) ⟨400344, by rfl⟩ : syracuseStep 1067585 = 800689) B800689
theorem B1067603 : Blo 710320 1067603 := bstep (se 1 (by rfl) ⟨800702, by rfl⟩ : syracuseStep 1067603 = 1601405) B1601405
theorem B1198705 : Blo 710320 1198705 := bstep (se 2 (by rfl) ⟨449514, by rfl⟩ : syracuseStep 1198705 = 899029) B899029
theorem B1067633 : Blo 710320 1067633 := bstep (se 2 (by rfl) ⟨400362, by rfl⟩ : syracuseStep 1067633 = 800725) B800725
theorem B1067651 : Blo 710320 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B4573837 : Blo 710320 4573837 := bstep (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) B1715189
theorem B1198739 : Blo 710320 1198739 := bstep (se 1 (by rfl) ⟨899054, by rfl⟩ : syracuseStep 1198739 = 1798109) B1798109
theorem B1067681 : Blo 710320 1067681 := bstep (se 2 (by rfl) ⟨400380, by rfl⟩ : syracuseStep 1067681 = 800761) B800761
theorem B1067699 : Blo 710320 1067699 := bstep (se 1 (by rfl) ⟨800774, by rfl⟩ : syracuseStep 1067699 = 1601549) B1601549
theorem B1067729 : Blo 710320 1067729 := bstep (se 2 (by rfl) ⟨400398, by rfl⟩ : syracuseStep 1067729 = 800797) B800797
theorem B1067747 : Blo 710320 1067747 := bstep (se 1 (by rfl) ⟨800810, by rfl⟩ : syracuseStep 1067747 = 1601621) B1601621
theorem B1067777 : Blo 710320 1067777 := bstep (se 2 (by rfl) ⟨400416, by rfl⟩ : syracuseStep 1067777 = 800833) B800833
theorem B1198867 : Blo 710320 1198867 := bstep (se 1 (by rfl) ⟨899150, by rfl⟩ : syracuseStep 1198867 = 1798301) B1798301
theorem B1067795 : Blo 710320 1067795 := bstep (se 1 (by rfl) ⟨800846, by rfl⟩ : syracuseStep 1067795 = 1601693) B1601693
theorem B903955 : Blo 710320 903955 := bstep (se 1 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 903955 = 1355933) B1355933
theorem B1067825 : Blo 710320 1067825 := bstep (se 2 (by rfl) ⟨400434, by rfl⟩ : syracuseStep 1067825 = 800869) B800869
theorem B1067843 : Blo 710320 1067843 := bstep (se 1 (by rfl) ⟨800882, by rfl⟩ : syracuseStep 1067843 = 1601765) B1601765
theorem B1231697 : Blo 710320 1231697 := bstep (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) B923773
theorem B1067873 : Blo 710320 1067873 := bstep (se 2 (by rfl) ⟨400452, by rfl⟩ : syracuseStep 1067873 = 800905) B800905
theorem B4049777 : Blo 710320 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B1067891 : Blo 710320 1067891 := bstep (se 1 (by rfl) ⟨800918, by rfl⟩ : syracuseStep 1067891 = 1601837) B1601837
theorem B904051 : Blo 710320 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B1067921 : Blo 710320 1067921 := bstep (se 2 (by rfl) ⟨400470, by rfl⟩ : syracuseStep 1067921 = 800941) B800941
theorem B1199009 : Blo 710320 1199009 := bstep (se 2 (by rfl) ⟨449628, by rfl⟩ : syracuseStep 1199009 = 899257) B899257
theorem B1067939 : Blo 710320 1067939 := bstep (se 1 (by rfl) ⟨800954, by rfl⟩ : syracuseStep 1067939 = 1601909) B1601909
theorem B1067969 : Blo 710320 1067969 := bstep (se 2 (by rfl) ⟨400488, by rfl⟩ : syracuseStep 1067969 = 800977) B800977
theorem B1067987 : Blo 710320 1067987 := bstep (se 1 (by rfl) ⟨800990, by rfl⟩ : syracuseStep 1067987 = 1601981) B1601981
theorem B1068017 : Blo 710320 1068017 := bstep (se 2 (by rfl) ⟨400506, by rfl⟩ : syracuseStep 1068017 = 801013) B801013
theorem B1068035 : Blo 710320 1068035 := bstep (se 1 (by rfl) ⟨801026, by rfl⟩ : syracuseStep 1068035 = 1602053) B1602053
theorem B1199137 : Blo 710320 1199137 := bstep (se 2 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 1199137 = 899353) B899353
theorem B1068065 : Blo 710320 1068065 := bstep (se 2 (by rfl) ⟨400524, by rfl⟩ : syracuseStep 1068065 = 801049) B801049
theorem B1068083 : Blo 710320 1068083 := bstep (se 1 (by rfl) ⟨801062, by rfl⟩ : syracuseStep 1068083 = 1602125) B1602125
theorem B1199171 : Blo 710320 1199171 := bstep (se 1 (by rfl) ⟨899378, by rfl⟩ : syracuseStep 1199171 = 1798757) B1798757
theorem B3034189 : Blo 710320 3034189 := bstep (se 3 (by rfl) ⟨568910, by rfl⟩ : syracuseStep 3034189 = 1137821) B1137821
theorem B1068113 : Blo 710320 1068113 := bstep (se 2 (by rfl) ⟨400542, by rfl⟩ : syracuseStep 1068113 = 801085) B801085
theorem B1068131 : Blo 710320 1068131 := bstep (se 1 (by rfl) ⟨801098, by rfl⟩ : syracuseStep 1068131 = 1602197) B1602197
theorem B1068161 : Blo 710320 1068161 := bstep (se 2 (by rfl) ⟨400560, by rfl⟩ : syracuseStep 1068161 = 801121) B801121
theorem B1068179 : Blo 710320 1068179 := bstep (se 1 (by rfl) ⟨801134, by rfl⟩ : syracuseStep 1068179 = 1602269) B1602269
theorem B1068209 : Blo 710320 1068209 := bstep (se 2 (by rfl) ⟨400578, by rfl⟩ : syracuseStep 1068209 = 801157) B801157
theorem B1199299 : Blo 710320 1199299 := bstep (se 1 (by rfl) ⟨899474, by rfl⟩ : syracuseStep 1199299 = 1798949) B1798949
theorem B1068227 : Blo 710320 1068227 := bstep (se 1 (by rfl) ⟨801170, by rfl⟩ : syracuseStep 1068227 = 1602341) B1602341
theorem B1068257 : Blo 710320 1068257 := bstep (se 2 (by rfl) ⟨400596, by rfl⟩ : syracuseStep 1068257 = 801193) B801193
theorem B1068275 : Blo 710320 1068275 := bstep (se 1 (by rfl) ⟨801206, by rfl⟩ : syracuseStep 1068275 = 1602413) B1602413
theorem B1068305 : Blo 710320 1068305 := bstep (se 2 (by rfl) ⟨400614, by rfl⟩ : syracuseStep 1068305 = 801229) B801229
theorem B1068323 : Blo 710320 1068323 := bstep (se 1 (by rfl) ⟨801242, by rfl⟩ : syracuseStep 1068323 = 1602485) B1602485
theorem B1068353 : Blo 710320 1068353 := bstep (se 2 (by rfl) ⟨400632, by rfl⟩ : syracuseStep 1068353 = 801265) B801265
theorem B1199441 : Blo 710320 1199441 := bstep (se 2 (by rfl) ⟨449790, by rfl⟩ : syracuseStep 1199441 = 899581) B899581
theorem B1068371 : Blo 710320 1068371 := bstep (se 1 (by rfl) ⟨801278, by rfl⟩ : syracuseStep 1068371 = 1602557) B1602557
theorem B1068401 : Blo 710320 1068401 := bstep (se 2 (by rfl) ⟨400650, by rfl⟩ : syracuseStep 1068401 = 801301) B801301
theorem B1068419 : Blo 710320 1068419 := bstep (se 1 (by rfl) ⟨801314, by rfl⟩ : syracuseStep 1068419 = 1602629) B1602629
theorem B1068449 : Blo 710320 1068449 := bstep (se 2 (by rfl) ⟨400668, by rfl⟩ : syracuseStep 1068449 = 801337) B801337
theorem B1068467 : Blo 710320 1068467 := bstep (se 1 (by rfl) ⟨801350, by rfl⟩ : syracuseStep 1068467 = 1602701) B1602701
theorem B1199569 : Blo 710320 1199569 := bstep (se 2 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 1199569 = 899677) B899677
theorem B1068497 : Blo 710320 1068497 := bstep (se 2 (by rfl) ⟨400686, by rfl⟩ : syracuseStep 1068497 = 801373) B801373
theorem B1068515 : Blo 710320 1068515 := bstep (se 1 (by rfl) ⟨801386, by rfl⟩ : syracuseStep 1068515 = 1602773) B1602773
theorem B2706929 : Blo 710320 2706929 := bstep (se 2 (by rfl) ⟨1015098, by rfl⟩ : syracuseStep 2706929 = 2030197) B2030197
theorem B1199603 : Blo 710320 1199603 := bstep (se 1 (by rfl) ⟨899702, by rfl⟩ : syracuseStep 1199603 = 1799405) B1799405
theorem B1068545 : Blo 710320 1068545 := bstep (se 2 (by rfl) ⟨400704, by rfl⟩ : syracuseStep 1068545 = 801409) B801409
theorem B2280973 : Blo 710320 2280973 := bstep (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) B855365
theorem B1068563 : Blo 710320 1068563 := bstep (se 1 (by rfl) ⟨801422, by rfl⟩ : syracuseStep 1068563 = 1602845) B1602845
theorem B1068593 : Blo 710320 1068593 := bstep (se 2 (by rfl) ⟨400722, by rfl⟩ : syracuseStep 1068593 = 801445) B801445
theorem B1068611 : Blo 710320 1068611 := bstep (se 1 (by rfl) ⟨801458, by rfl⟩ : syracuseStep 1068611 = 1602917) B1602917
theorem B1920593 : Blo 710320 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1068641 : Blo 710320 1068641 := bstep (se 2 (by rfl) ⟨400740, by rfl⟩ : syracuseStep 1068641 = 801481) B801481
theorem B1199731 : Blo 710320 1199731 := bstep (se 1 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 1199731 = 1799597) B1799597
theorem B1068659 : Blo 710320 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B1068689 : Blo 710320 1068689 := bstep (se 2 (by rfl) ⟨400758, by rfl⟩ : syracuseStep 1068689 = 801517) B801517
theorem B1068707 : Blo 710320 1068707 := bstep (se 1 (by rfl) ⟨801530, by rfl⟩ : syracuseStep 1068707 = 1603061) B1603061
theorem B1068737 : Blo 710320 1068737 := bstep (se 2 (by rfl) ⟨400776, by rfl⟩ : syracuseStep 1068737 = 801553) B801553
theorem B1068755 : Blo 710320 1068755 := bstep (se 1 (by rfl) ⟨801566, by rfl⟩ : syracuseStep 1068755 = 1603133) B1603133
theorem B6082289 : Blo 710320 6082289 := bstep (se 2 (by rfl) ⟨2280858, by rfl⟩ : syracuseStep 6082289 = 4561717) B4561717
theorem B1068785 : Blo 710320 1068785 := bstep (se 2 (by rfl) ⟨400794, by rfl⟩ : syracuseStep 1068785 = 801589) B801589
theorem B1199873 : Blo 710320 1199873 := bstep (se 2 (by rfl) ⟨449952, by rfl⟩ : syracuseStep 1199873 = 899905) B899905
theorem B1068803 : Blo 710320 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B1068833 : Blo 710320 1068833 := bstep (se 2 (by rfl) ⟨400812, by rfl⟩ : syracuseStep 1068833 = 801625) B801625
theorem B1068851 : Blo 710320 1068851 := bstep (se 1 (by rfl) ⟨801638, by rfl⟩ : syracuseStep 1068851 = 1603277) B1603277
theorem B1068881 : Blo 710320 1068881 := bstep (se 2 (by rfl) ⟨400830, by rfl⟩ : syracuseStep 1068881 = 801661) B801661
theorem B1068899 : Blo 710320 1068899 := bstep (se 1 (by rfl) ⟨801674, by rfl⟩ : syracuseStep 1068899 = 1603349) B1603349
theorem B1200001 : Blo 710320 1200001 := bstep (se 2 (by rfl) ⟨450000, by rfl⟩ : syracuseStep 1200001 = 900001) B900001
theorem B1068929 : Blo 710320 1068929 := bstep (se 2 (by rfl) ⟨400848, by rfl⟩ : syracuseStep 1068929 = 801697) B801697
theorem B1068947 : Blo 710320 1068947 := bstep (se 1 (by rfl) ⟨801710, by rfl⟩ : syracuseStep 1068947 = 1603421) B1603421
theorem B1200035 : Blo 710320 1200035 := bstep (se 1 (by rfl) ⟨900026, by rfl⟩ : syracuseStep 1200035 = 1800053) B1800053
theorem B1068977 : Blo 710320 1068977 := bstep (se 2 (by rfl) ⟨400866, by rfl⟩ : syracuseStep 1068977 = 801733) B801733
theorem B1068995 : Blo 710320 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B1069025 : Blo 710320 1069025 := bstep (se 2 (by rfl) ⟨400884, by rfl⟩ : syracuseStep 1069025 = 801769) B801769
theorem B1069043 : Blo 710320 1069043 := bstep (se 1 (by rfl) ⟨801782, by rfl⟩ : syracuseStep 1069043 = 1603565) B1603565
theorem B1069073 : Blo 710320 1069073 := bstep (se 2 (by rfl) ⟨400902, by rfl⟩ : syracuseStep 1069073 = 801805) B801805
theorem B1200163 : Blo 710320 1200163 := bstep (se 1 (by rfl) ⟨900122, by rfl⟩ : syracuseStep 1200163 = 1800245) B1800245
theorem B1069091 : Blo 710320 1069091 := bstep (se 1 (by rfl) ⟨801818, by rfl⟩ : syracuseStep 1069091 = 1603637) B1603637
theorem B1069121 : Blo 710320 1069121 := bstep (se 2 (by rfl) ⟨400920, by rfl⟩ : syracuseStep 1069121 = 801841) B801841
theorem B1626193 : Blo 710320 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1069139 : Blo 710320 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B1069169 : Blo 710320 1069169 := bstep (se 2 (by rfl) ⟨400938, by rfl⟩ : syracuseStep 1069169 = 801877) B801877
theorem B1069187 : Blo 710320 1069187 := bstep (se 1 (by rfl) ⟨801890, by rfl⟩ : syracuseStep 1069187 = 1603781) B1603781
theorem B3657869 : Blo 710320 3657869 := bstep (se 3 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 3657869 = 1371701) B1371701
theorem B1069217 : Blo 710320 1069217 := bstep (se 2 (by rfl) ⟨400956, by rfl⟩ : syracuseStep 1069217 = 801913) B801913
theorem B1200305 : Blo 710320 1200305 := bstep (se 2 (by rfl) ⟨450114, by rfl⟩ : syracuseStep 1200305 = 900229) B900229
theorem B1069235 : Blo 710320 1069235 := bstep (se 1 (by rfl) ⟨801926, by rfl⟩ : syracuseStep 1069235 = 1603853) B1603853
theorem B9752773 : Blo 710320 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B1069265 : Blo 710320 1069265 := bstep (se 2 (by rfl) ⟨400974, by rfl⟩ : syracuseStep 1069265 = 801949) B801949
theorem B1069283 : Blo 710320 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B1069313 : Blo 710320 1069313 := bstep (se 2 (by rfl) ⟨400992, by rfl⟩ : syracuseStep 1069313 = 801985) B801985
theorem B1069331 : Blo 710320 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B4051235 : Blo 710320 4051235 := bstep (se 1 (by rfl) ⟨3038426, by rfl⟩ : syracuseStep 4051235 = 6076853) B6076853
theorem B1200433 : Blo 710320 1200433 := bstep (se 2 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 1200433 = 900325) B900325
theorem B1069361 : Blo 710320 1069361 := bstep (se 2 (by rfl) ⟨401010, by rfl⟩ : syracuseStep 1069361 = 802021) B802021
theorem B1069379 : Blo 710320 1069379 := bstep (se 1 (by rfl) ⟨802034, by rfl⟩ : syracuseStep 1069379 = 1604069) B1604069
theorem B1200467 : Blo 710320 1200467 := bstep (se 1 (by rfl) ⟨900350, by rfl⟩ : syracuseStep 1200467 = 1800701) B1800701
theorem B1069409 : Blo 710320 1069409 := bstep (se 2 (by rfl) ⟨401028, by rfl⟩ : syracuseStep 1069409 = 802057) B802057
theorem B1069427 : Blo 710320 1069427 := bstep (se 1 (by rfl) ⟨802070, by rfl⟩ : syracuseStep 1069427 = 1604141) B1604141
theorem B1069457 : Blo 710320 1069457 := bstep (se 2 (by rfl) ⟨401046, by rfl⟩ : syracuseStep 1069457 = 802093) B802093
theorem B1069475 : Blo 710320 1069475 := bstep (se 1 (by rfl) ⟨802106, by rfl⟩ : syracuseStep 1069475 = 1604213) B1604213
theorem B1069505 : Blo 710320 1069505 := bstep (se 2 (by rfl) ⟨401064, by rfl⟩ : syracuseStep 1069505 = 802129) B802129
theorem B1200595 : Blo 710320 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B1069523 : Blo 710320 1069523 := bstep (se 1 (by rfl) ⟨802142, by rfl⟩ : syracuseStep 1069523 = 1604285) B1604285
theorem B1069553 : Blo 710320 1069553 := bstep (se 2 (by rfl) ⟨401082, by rfl⟩ : syracuseStep 1069553 = 802165) B802165
theorem B1069571 : Blo 710320 1069571 := bstep (se 1 (by rfl) ⟨802178, by rfl⟩ : syracuseStep 1069571 = 1604357) B1604357
theorem B1069601 : Blo 710320 1069601 := bstep (se 2 (by rfl) ⟨401100, by rfl⟩ : syracuseStep 1069601 = 802201) B802201
theorem B3854897 : Blo 710320 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B1069619 : Blo 710320 1069619 := bstep (se 1 (by rfl) ⟨802214, by rfl⟩ : syracuseStep 1069619 = 1604429) B1604429
theorem B1069649 : Blo 710320 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B1200737 : Blo 710320 1200737 := bstep (se 2 (by rfl) ⟨450276, by rfl⟩ : syracuseStep 1200737 = 900553) B900553
theorem B1069667 : Blo 710320 1069667 := bstep (se 1 (by rfl) ⟨802250, by rfl⟩ : syracuseStep 1069667 = 1604501) B1604501
theorem B1069697 : Blo 710320 1069697 := bstep (se 2 (by rfl) ⟨401136, by rfl⟩ : syracuseStep 1069697 = 802273) B802273
theorem B5395085 : Blo 710320 5395085 := bstep (se 3 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 5395085 = 2023157) B2023157
theorem B8245901 : Blo 710320 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B1069715 : Blo 710320 1069715 := bstep (se 1 (by rfl) ⟨802286, by rfl⟩ : syracuseStep 1069715 = 1604573) B1604573
theorem B1069745 : Blo 710320 1069745 := bstep (se 2 (by rfl) ⟨401154, by rfl⟩ : syracuseStep 1069745 = 802309) B802309
theorem B1069763 : Blo 710320 1069763 := bstep (se 1 (by rfl) ⟨802322, by rfl⟩ : syracuseStep 1069763 = 1604645) B1604645
theorem B1200865 : Blo 710320 1200865 := bstep (se 2 (by rfl) ⟨450324, by rfl⟩ : syracuseStep 1200865 = 900649) B900649
theorem B1069793 : Blo 710320 1069793 := bstep (se 2 (by rfl) ⟨401172, by rfl⟩ : syracuseStep 1069793 = 802345) B802345
theorem B7688945 : Blo 710320 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1069811 : Blo 710320 1069811 := bstep (se 1 (by rfl) ⟨802358, by rfl⟩ : syracuseStep 1069811 = 1604717) B1604717
theorem B1200899 : Blo 710320 1200899 := bstep (se 1 (by rfl) ⟨900674, by rfl⟩ : syracuseStep 1200899 = 1801349) B1801349
theorem B1069841 : Blo 710320 1069841 := bstep (se 2 (by rfl) ⟨401190, by rfl⟩ : syracuseStep 1069841 = 802381) B802381
theorem B1069859 : Blo 710320 1069859 := bstep (se 1 (by rfl) ⟨802394, by rfl⟩ : syracuseStep 1069859 = 1604789) B1604789
theorem B1069889 : Blo 710320 1069889 := bstep (se 2 (by rfl) ⟨401208, by rfl⟩ : syracuseStep 1069889 = 802417) B802417
theorem B1069907 : Blo 710320 1069907 := bstep (se 1 (by rfl) ⟨802430, by rfl⟩ : syracuseStep 1069907 = 1604861) B1604861
theorem B1069937 : Blo 710320 1069937 := bstep (se 2 (by rfl) ⟨401226, by rfl⟩ : syracuseStep 1069937 = 802453) B802453
theorem B1201027 : Blo 710320 1201027 := bstep (se 1 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 1201027 = 1801541) B1801541
theorem B1069955 : Blo 710320 1069955 := bstep (se 1 (by rfl) ⟨802466, by rfl⟩ : syracuseStep 1069955 = 1604933) B1604933
theorem B1069985 : Blo 710320 1069985 := bstep (se 2 (by rfl) ⟨401244, by rfl⟩ : syracuseStep 1069985 = 802489) B802489
theorem B2708387 : Blo 710320 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B1070003 : Blo 710320 1070003 := bstep (se 1 (by rfl) ⟨802502, by rfl⟩ : syracuseStep 1070003 = 1605005) B1605005
theorem B1070033 : Blo 710320 1070033 := bstep (se 2 (by rfl) ⟨401262, by rfl⟩ : syracuseStep 1070033 = 802525) B802525
theorem B1070051 : Blo 710320 1070051 := bstep (se 1 (by rfl) ⟨802538, by rfl⟩ : syracuseStep 1070051 = 1605077) B1605077
theorem B1070081 : Blo 710320 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B1201169 : Blo 710320 1201169 := bstep (se 2 (by rfl) ⟨450438, by rfl⟩ : syracuseStep 1201169 = 900877) B900877
theorem B1070099 : Blo 710320 1070099 := bstep (se 1 (by rfl) ⟨802574, by rfl⟩ : syracuseStep 1070099 = 1605149) B1605149
theorem B1070129 : Blo 710320 1070129 := bstep (se 2 (by rfl) ⟨401298, by rfl⟩ : syracuseStep 1070129 = 802597) B802597
theorem B1758275 : Blo 710320 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1070147 : Blo 710320 1070147 := bstep (se 1 (by rfl) ⟨802610, by rfl⟩ : syracuseStep 1070147 = 1605221) B1605221
theorem B1070177 : Blo 710320 1070177 := bstep (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) B802633
theorem B1070195 : Blo 710320 1070195 := bstep (se 1 (by rfl) ⟨802646, by rfl⟩ : syracuseStep 1070195 = 1605293) B1605293
theorem B1201297 : Blo 710320 1201297 := bstep (se 2 (by rfl) ⟨450486, by rfl⟩ : syracuseStep 1201297 = 900973) B900973
theorem B1070225 : Blo 710320 1070225 := bstep (se 2 (by rfl) ⟨401334, by rfl⟩ : syracuseStep 1070225 = 802669) B802669
theorem B1070243 : Blo 710320 1070243 := bstep (se 1 (by rfl) ⟨802682, by rfl⟩ : syracuseStep 1070243 = 1605365) B1605365
theorem B1201331 : Blo 710320 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B1070273 : Blo 710320 1070273 := bstep (se 2 (by rfl) ⟨401352, by rfl⟩ : syracuseStep 1070273 = 802705) B802705
theorem B2282705 : Blo 710320 2282705 := bstep (se 2 (by rfl) ⟨856014, by rfl⟩ : syracuseStep 2282705 = 1712029) B1712029
theorem B1070291 : Blo 710320 1070291 := bstep (se 1 (by rfl) ⟨802718, by rfl⟩ : syracuseStep 1070291 = 1605437) B1605437
theorem B1070321 : Blo 710320 1070321 := bstep (se 2 (by rfl) ⟨401370, by rfl⟩ : syracuseStep 1070321 = 802741) B802741
theorem B1070339 : Blo 710320 1070339 := bstep (se 1 (by rfl) ⟨802754, by rfl⟩ : syracuseStep 1070339 = 1605509) B1605509
theorem B1070369 : Blo 710320 1070369 := bstep (se 2 (by rfl) ⟨401388, by rfl⟩ : syracuseStep 1070369 = 802777) B802777
theorem B1201459 : Blo 710320 1201459 := bstep (se 1 (by rfl) ⟨901094, by rfl⟩ : syracuseStep 1201459 = 1802189) B1802189
theorem B1070387 : Blo 710320 1070387 := bstep (se 1 (by rfl) ⟨802790, by rfl⟩ : syracuseStep 1070387 = 1605581) B1605581
theorem B1070417 : Blo 710320 1070417 := bstep (se 2 (by rfl) ⟨401406, by rfl⟩ : syracuseStep 1070417 = 802813) B802813
theorem B1070435 : Blo 710320 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B1070465 : Blo 710320 1070465 := bstep (se 2 (by rfl) ⟨401424, by rfl⟩ : syracuseStep 1070465 = 802849) B802849
theorem B15422861 : Blo 710320 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B1070483 : Blo 710320 1070483 := bstep (se 1 (by rfl) ⟨802862, by rfl⟩ : syracuseStep 1070483 = 1605725) B1605725
theorem B1070513 : Blo 710320 1070513 := bstep (se 2 (by rfl) ⟨401442, by rfl⟩ : syracuseStep 1070513 = 802885) B802885
theorem B1201601 : Blo 710320 1201601 := bstep (se 2 (by rfl) ⟨450600, by rfl⟩ : syracuseStep 1201601 = 901201) B901201
theorem B1070531 : Blo 710320 1070531 := bstep (se 1 (by rfl) ⟨802898, by rfl⟩ : syracuseStep 1070531 = 1605797) B1605797
theorem B1070561 : Blo 710320 1070561 := bstep (se 2 (by rfl) ⟨401460, by rfl⟩ : syracuseStep 1070561 = 802921) B802921
theorem B1070579 : Blo 710320 1070579 := bstep (se 1 (by rfl) ⟨802934, by rfl⟩ : syracuseStep 1070579 = 1605869) B1605869
theorem B1070609 : Blo 710320 1070609 := bstep (se 2 (by rfl) ⟨401478, by rfl⟩ : syracuseStep 1070609 = 802957) B802957
theorem B1070627 : Blo 710320 1070627 := bstep (se 1 (by rfl) ⟨802970, by rfl⟩ : syracuseStep 1070627 = 1605941) B1605941
theorem B1201729 : Blo 710320 1201729 := bstep (se 2 (by rfl) ⟨450648, by rfl⟩ : syracuseStep 1201729 = 901297) B901297
theorem B1070657 : Blo 710320 1070657 := bstep (se 2 (by rfl) ⟨401496, by rfl⟩ : syracuseStep 1070657 = 802993) B802993
theorem B1070675 : Blo 710320 1070675 := bstep (se 1 (by rfl) ⟨803006, by rfl⟩ : syracuseStep 1070675 = 1606013) B1606013
theorem B1201763 : Blo 710320 1201763 := bstep (se 1 (by rfl) ⟨901322, by rfl⟩ : syracuseStep 1201763 = 1802645) B1802645
theorem B1922669 : Blo 710320 1922669 := bstep (se 3 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 1922669 = 721001) B721001
theorem B1070705 : Blo 710320 1070705 := bstep (se 2 (by rfl) ⟨401514, by rfl⟩ : syracuseStep 1070705 = 803029) B803029
theorem B1070723 : Blo 710320 1070723 := bstep (se 1 (by rfl) ⟨803042, by rfl⟩ : syracuseStep 1070723 = 1606085) B1606085
theorem B1070753 : Blo 710320 1070753 := bstep (se 2 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 1070753 = 803065) B803065
theorem B710323 : Blo 710320 710323 := bstep (se 1 (by rfl) ⟨532742, by rfl⟩ : syracuseStep 710323 = 1065485) B1065485
theorem B1070771 : Blo 710320 1070771 := bstep (se 1 (by rfl) ⟨803078, by rfl⟩ : syracuseStep 1070771 = 1606157) B1606157
theorem B710339 : Blo 710320 710339 := bstep (se 1 (by rfl) ⟨532754, by rfl⟩ : syracuseStep 710339 = 1065509) B1065509
theorem B1070801 : Blo 710320 1070801 := bstep (se 2 (by rfl) ⟨401550, by rfl⟩ : syracuseStep 1070801 = 803101) B803101
theorem B710355 : Blo 710320 710355 := bstep (se 1 (by rfl) ⟨532766, by rfl⟩ : syracuseStep 710355 = 1065533) B1065533
theorem B710371 : Blo 710320 710371 := bstep (se 1 (by rfl) ⟨532778, by rfl⟩ : syracuseStep 710371 = 1065557) B1065557
theorem B1201891 : Blo 710320 1201891 := bstep (se 1 (by rfl) ⟨901418, by rfl⟩ : syracuseStep 1201891 = 1802837) B1802837
theorem B1070819 : Blo 710320 1070819 := bstep (se 1 (by rfl) ⟨803114, by rfl⟩ : syracuseStep 1070819 = 1606229) B1606229
theorem B710387 : Blo 710320 710387 := bstep (se 1 (by rfl) ⟨532790, by rfl⟩ : syracuseStep 710387 = 1065581) B1065581
theorem B1070849 : Blo 710320 1070849 := bstep (se 2 (by rfl) ⟨401568, by rfl⟩ : syracuseStep 1070849 = 803137) B803137
theorem B710403 : Blo 710320 710403 := bstep (se 1 (by rfl) ⟨532802, by rfl⟩ : syracuseStep 710403 = 1065605) B1065605
theorem B710419 : Blo 710320 710419 := bstep (se 1 (by rfl) ⟨532814, by rfl⟩ : syracuseStep 710419 = 1065629) B1065629
theorem B1070867 : Blo 710320 1070867 := bstep (se 1 (by rfl) ⟨803150, by rfl⟩ : syracuseStep 1070867 = 1606301) B1606301
theorem B710435 : Blo 710320 710435 := bstep (se 1 (by rfl) ⟨532826, by rfl⟩ : syracuseStep 710435 = 1065653) B1065653
theorem B1070897 : Blo 710320 1070897 := bstep (se 2 (by rfl) ⟨401586, by rfl⟩ : syracuseStep 1070897 = 803173) B803173
theorem B710451 : Blo 710320 710451 := bstep (se 1 (by rfl) ⟨532838, by rfl⟩ : syracuseStep 710451 = 1065677) B1065677
theorem B710467 : Blo 710320 710467 := bstep (se 1 (by rfl) ⟨532850, by rfl⟩ : syracuseStep 710467 = 1065701) B1065701
theorem B2283331 : Blo 710320 2283331 := bstep (se 1 (by rfl) ⟨1712498, by rfl⟩ : syracuseStep 2283331 = 3424997) B3424997
theorem B1070915 : Blo 710320 1070915 := bstep (se 1 (by rfl) ⟨803186, by rfl⟩ : syracuseStep 1070915 = 1606373) B1606373
theorem B710483 : Blo 710320 710483 := bstep (se 1 (by rfl) ⟨532862, by rfl⟩ : syracuseStep 710483 = 1065725) B1065725
theorem B1070945 : Blo 710320 1070945 := bstep (se 2 (by rfl) ⟨401604, by rfl⟩ : syracuseStep 1070945 = 803209) B803209
theorem B710499 : Blo 710320 710499 := bstep (se 1 (by rfl) ⟨532874, by rfl⟩ : syracuseStep 710499 = 1065749) B1065749
theorem B1202033 : Blo 710320 1202033 := bstep (se 2 (by rfl) ⟨450762, by rfl⟩ : syracuseStep 1202033 = 901525) B901525
theorem B710515 : Blo 710320 710515 := bstep (se 1 (by rfl) ⟨532886, by rfl⟩ : syracuseStep 710515 = 1065773) B1065773
theorem B1070963 : Blo 710320 1070963 := bstep (se 1 (by rfl) ⟨803222, by rfl⟩ : syracuseStep 1070963 = 1606445) B1606445
theorem B710531 : Blo 710320 710531 := bstep (se 1 (by rfl) ⟨532898, by rfl⟩ : syracuseStep 710531 = 1065797) B1065797
theorem B2709389 : Blo 710320 2709389 := bstep (se 3 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 2709389 = 1016021) B1016021
theorem B1070993 : Blo 710320 1070993 := bstep (se 2 (by rfl) ⟨401622, by rfl⟩ : syracuseStep 1070993 = 803245) B803245
theorem B710547 : Blo 710320 710547 := bstep (se 1 (by rfl) ⟨532910, by rfl⟩ : syracuseStep 710547 = 1065821) B1065821
theorem B710563 : Blo 710320 710563 := bstep (se 1 (by rfl) ⟨532922, by rfl⟩ : syracuseStep 710563 = 1065845) B1065845
theorem B1071011 : Blo 710320 1071011 := bstep (se 1 (by rfl) ⟨803258, by rfl⟩ : syracuseStep 1071011 = 1606517) B1606517
theorem B710579 : Blo 710320 710579 := bstep (se 1 (by rfl) ⟨532934, by rfl⟩ : syracuseStep 710579 = 1065869) B1065869
theorem B1071041 : Blo 710320 1071041 := bstep (se 2 (by rfl) ⟨401640, by rfl⟩ : syracuseStep 1071041 = 803281) B803281
theorem B710595 : Blo 710320 710595 := bstep (se 1 (by rfl) ⟨532946, by rfl⟩ : syracuseStep 710595 = 1065893) B1065893
theorem B710611 : Blo 710320 710611 := bstep (se 1 (by rfl) ⟨532958, by rfl⟩ : syracuseStep 710611 = 1065917) B1065917
theorem B1071059 : Blo 710320 1071059 := bstep (se 1 (by rfl) ⟨803294, by rfl⟩ : syracuseStep 1071059 = 1606589) B1606589
theorem B710627 : Blo 710320 710627 := bstep (se 1 (by rfl) ⟨532970, by rfl⟩ : syracuseStep 710627 = 1065941) B1065941
theorem B1202161 : Blo 710320 1202161 := bstep (se 2 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 1202161 = 901621) B901621
theorem B1071089 : Blo 710320 1071089 := bstep (se 2 (by rfl) ⟨401658, by rfl⟩ : syracuseStep 1071089 = 803317) B803317
theorem B710643 : Blo 710320 710643 := bstep (se 1 (by rfl) ⟨532982, by rfl⟩ : syracuseStep 710643 = 1065965) B1065965
theorem B710659 : Blo 710320 710659 := bstep (se 1 (by rfl) ⟨532994, by rfl⟩ : syracuseStep 710659 = 1065989) B1065989
theorem B1071107 : Blo 710320 1071107 := bstep (se 1 (by rfl) ⟨803330, by rfl⟩ : syracuseStep 1071107 = 1606661) B1606661
theorem B710675 : Blo 710320 710675 := bstep (se 1 (by rfl) ⟨533006, by rfl⟩ : syracuseStep 710675 = 1066013) B1066013
theorem B1202195 : Blo 710320 1202195 := bstep (se 1 (by rfl) ⟨901646, by rfl⟩ : syracuseStep 1202195 = 1803293) B1803293
theorem B1071137 : Blo 710320 1071137 := bstep (se 2 (by rfl) ⟨401676, by rfl⟩ : syracuseStep 1071137 = 803353) B803353
theorem B710691 : Blo 710320 710691 := bstep (se 1 (by rfl) ⟨533018, by rfl⟩ : syracuseStep 710691 = 1066037) B1066037
theorem B710707 : Blo 710320 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B1071155 : Blo 710320 1071155 := bstep (se 1 (by rfl) ⟨803366, by rfl⟩ : syracuseStep 1071155 = 1606733) B1606733
theorem B710723 : Blo 710320 710723 := bstep (se 1 (by rfl) ⟨533042, by rfl⟩ : syracuseStep 710723 = 1066085) B1066085
theorem B1071185 : Blo 710320 1071185 := bstep (se 2 (by rfl) ⟨401694, by rfl⟩ : syracuseStep 1071185 = 803389) B803389
theorem B710739 : Blo 710320 710739 := bstep (se 1 (by rfl) ⟨533054, by rfl⟩ : syracuseStep 710739 = 1066109) B1066109
theorem B710755 : Blo 710320 710755 := bstep (se 1 (by rfl) ⟨533066, by rfl⟩ : syracuseStep 710755 = 1066133) B1066133
theorem B1071203 : Blo 710320 1071203 := bstep (se 1 (by rfl) ⟨803402, by rfl⟩ : syracuseStep 1071203 = 1606805) B1606805
theorem B710771 : Blo 710320 710771 := bstep (se 1 (by rfl) ⟨533078, by rfl⟩ : syracuseStep 710771 = 1066157) B1066157
theorem B1071233 : Blo 710320 1071233 := bstep (se 2 (by rfl) ⟨401712, by rfl⟩ : syracuseStep 1071233 = 803425) B803425
theorem B710787 : Blo 710320 710787 := bstep (se 1 (by rfl) ⟨533090, by rfl⟩ : syracuseStep 710787 = 1066181) B1066181
theorem B710803 : Blo 710320 710803 := bstep (se 1 (by rfl) ⟨533102, by rfl⟩ : syracuseStep 710803 = 1066205) B1066205
theorem B1202323 : Blo 710320 1202323 := bstep (se 1 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 1202323 = 1803485) B1803485
theorem B1071251 : Blo 710320 1071251 := bstep (se 1 (by rfl) ⟨803438, by rfl⟩ : syracuseStep 1071251 = 1606877) B1606877
theorem B710819 : Blo 710320 710819 := bstep (se 1 (by rfl) ⟨533114, by rfl⟩ : syracuseStep 710819 = 1066229) B1066229
theorem B1071281 : Blo 710320 1071281 := bstep (se 2 (by rfl) ⟨401730, by rfl⟩ : syracuseStep 1071281 = 803461) B803461
theorem B710835 : Blo 710320 710835 := bstep (se 1 (by rfl) ⟨533126, by rfl⟩ : syracuseStep 710835 = 1066253) B1066253
theorem B710851 : Blo 710320 710851 := bstep (se 1 (by rfl) ⟨533138, by rfl⟩ : syracuseStep 710851 = 1066277) B1066277
theorem B1071299 : Blo 710320 1071299 := bstep (se 1 (by rfl) ⟨803474, by rfl⟩ : syracuseStep 1071299 = 1606949) B1606949
theorem B710867 : Blo 710320 710867 := bstep (se 1 (by rfl) ⟨533150, by rfl⟩ : syracuseStep 710867 = 1066301) B1066301
theorem B1071329 : Blo 710320 1071329 := bstep (se 2 (by rfl) ⟨401748, by rfl⟩ : syracuseStep 1071329 = 803497) B803497
theorem B710883 : Blo 710320 710883 := bstep (se 1 (by rfl) ⟨533162, by rfl⟩ : syracuseStep 710883 = 1066325) B1066325
theorem B710899 : Blo 710320 710899 := bstep (se 1 (by rfl) ⟨533174, by rfl⟩ : syracuseStep 710899 = 1066349) B1066349
theorem B1071347 : Blo 710320 1071347 := bstep (se 1 (by rfl) ⟨803510, by rfl⟩ : syracuseStep 1071347 = 1607021) B1607021
theorem B710915 : Blo 710320 710915 := bstep (se 1 (by rfl) ⟨533186, by rfl⟩ : syracuseStep 710915 = 1066373) B1066373
theorem B1071377 : Blo 710320 1071377 := bstep (se 2 (by rfl) ⟨401766, by rfl⟩ : syracuseStep 1071377 = 803533) B803533
theorem B710931 : Blo 710320 710931 := bstep (se 1 (by rfl) ⟨533198, by rfl⟩ : syracuseStep 710931 = 1066397) B1066397
theorem B1202465 : Blo 710320 1202465 := bstep (se 2 (by rfl) ⟨450924, by rfl⟩ : syracuseStep 1202465 = 901849) B901849
theorem B710947 : Blo 710320 710947 := bstep (se 1 (by rfl) ⟨533210, by rfl⟩ : syracuseStep 710947 = 1066421) B1066421
theorem B1071395 : Blo 710320 1071395 := bstep (se 1 (by rfl) ⟨803546, by rfl⟩ : syracuseStep 1071395 = 1607093) B1607093
theorem B710963 : Blo 710320 710963 := bstep (se 1 (by rfl) ⟨533222, by rfl⟩ : syracuseStep 710963 = 1066445) B1066445
theorem B1071425 : Blo 710320 1071425 := bstep (se 2 (by rfl) ⟨401784, by rfl⟩ : syracuseStep 1071425 = 803569) B803569
theorem B710979 : Blo 710320 710979 := bstep (se 1 (by rfl) ⟨533234, by rfl⟩ : syracuseStep 710979 = 1066469) B1066469
theorem B710995 : Blo 710320 710995 := bstep (se 1 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 710995 = 1066493) B1066493
theorem B1071443 : Blo 710320 1071443 := bstep (se 1 (by rfl) ⟨803582, by rfl⟩ : syracuseStep 1071443 = 1607165) B1607165
theorem B711011 : Blo 710320 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B1071473 : Blo 710320 1071473 := bstep (se 2 (by rfl) ⟨401802, by rfl⟩ : syracuseStep 1071473 = 803605) B803605
theorem B711027 : Blo 710320 711027 := bstep (se 1 (by rfl) ⟨533270, by rfl⟩ : syracuseStep 711027 = 1066541) B1066541
theorem B711043 : Blo 710320 711043 := bstep (se 1 (by rfl) ⟨533282, by rfl⟩ : syracuseStep 711043 = 1066565) B1066565
theorem B711059 : Blo 710320 711059 := bstep (se 1 (by rfl) ⟨533294, by rfl⟩ : syracuseStep 711059 = 1066589) B1066589
theorem B1202593 : Blo 710320 1202593 := bstep (se 2 (by rfl) ⟨450972, by rfl⟩ : syracuseStep 1202593 = 901945) B901945
theorem B711075 : Blo 710320 711075 := bstep (se 1 (by rfl) ⟨533306, by rfl⟩ : syracuseStep 711075 = 1066613) B1066613
theorem B711091 : Blo 710320 711091 := bstep (se 1 (by rfl) ⟨533318, by rfl⟩ : syracuseStep 711091 = 1066637) B1066637
theorem B711107 : Blo 710320 711107 := bstep (se 1 (by rfl) ⟨533330, by rfl⟩ : syracuseStep 711107 = 1066661) B1066661
theorem B1202627 : Blo 710320 1202627 := bstep (se 1 (by rfl) ⟨901970, by rfl⟩ : syracuseStep 1202627 = 1803941) B1803941
theorem B711123 : Blo 710320 711123 := bstep (se 1 (by rfl) ⟨533342, by rfl⟩ : syracuseStep 711123 = 1066685) B1066685
theorem B16407011 : Blo 710320 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B711139 : Blo 710320 711139 := bstep (se 1 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 711139 = 1066709) B1066709
theorem B711155 : Blo 710320 711155 := bstep (se 1 (by rfl) ⟨533366, by rfl⟩ : syracuseStep 711155 = 1066733) B1066733
theorem B711171 : Blo 710320 711171 := bstep (se 1 (by rfl) ⟨533378, by rfl⟩ : syracuseStep 711171 = 1066757) B1066757
theorem B1628675 : Blo 710320 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B711187 : Blo 710320 711187 := bstep (se 1 (by rfl) ⟨533390, by rfl⟩ : syracuseStep 711187 = 1066781) B1066781
theorem B711203 : Blo 710320 711203 := bstep (se 1 (by rfl) ⟨533402, by rfl⟩ : syracuseStep 711203 = 1066805) B1066805
theorem B711219 : Blo 710320 711219 := bstep (se 1 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 711219 = 1066829) B1066829
theorem B711235 : Blo 710320 711235 := bstep (se 1 (by rfl) ⟨533426, by rfl⟩ : syracuseStep 711235 = 1066853) B1066853
theorem B1202755 : Blo 710320 1202755 := bstep (se 1 (by rfl) ⟨902066, by rfl⟩ : syracuseStep 1202755 = 1804133) B1804133
theorem B4938317 : Blo 710320 4938317 := bstep (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) B1851869
theorem B711251 : Blo 710320 711251 := bstep (se 1 (by rfl) ⟨533438, by rfl⟩ : syracuseStep 711251 = 1066877) B1066877
theorem B711267 : Blo 710320 711267 := bstep (se 1 (by rfl) ⟨533450, by rfl⟩ : syracuseStep 711267 = 1066901) B1066901
theorem B711283 : Blo 710320 711283 := bstep (se 1 (by rfl) ⟨533462, by rfl⟩ : syracuseStep 711283 = 1066925) B1066925
theorem B711299 : Blo 710320 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B711315 : Blo 710320 711315 := bstep (se 1 (by rfl) ⟨533486, by rfl⟩ : syracuseStep 711315 = 1066973) B1066973
theorem B711331 : Blo 710320 711331 := bstep (se 1 (by rfl) ⟨533498, by rfl⟩ : syracuseStep 711331 = 1066997) B1066997
theorem B711347 : Blo 710320 711347 := bstep (se 1 (by rfl) ⟨533510, by rfl⟩ : syracuseStep 711347 = 1067021) B1067021
theorem B711363 : Blo 710320 711363 := bstep (se 1 (by rfl) ⟨533522, by rfl⟩ : syracuseStep 711363 = 1067045) B1067045
theorem B1202897 : Blo 710320 1202897 := bstep (se 2 (by rfl) ⟨451086, by rfl⟩ : syracuseStep 1202897 = 902173) B902173
theorem B711379 : Blo 710320 711379 := bstep (se 1 (by rfl) ⟨533534, by rfl⟩ : syracuseStep 711379 = 1067069) B1067069
theorem B711395 : Blo 710320 711395 := bstep (se 1 (by rfl) ⟨533546, by rfl⟩ : syracuseStep 711395 = 1067093) B1067093
theorem B711411 : Blo 710320 711411 := bstep (se 1 (by rfl) ⟨533558, by rfl⟩ : syracuseStep 711411 = 1067117) B1067117
theorem B711427 : Blo 710320 711427 := bstep (se 1 (by rfl) ⟨533570, by rfl⟩ : syracuseStep 711427 = 1067141) B1067141
theorem B711443 : Blo 710320 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B711459 : Blo 710320 711459 := bstep (se 1 (by rfl) ⟨533594, by rfl⟩ : syracuseStep 711459 = 1067189) B1067189
theorem B711475 : Blo 710320 711475 := bstep (se 1 (by rfl) ⟨533606, by rfl⟩ : syracuseStep 711475 = 1067213) B1067213
theorem B711491 : Blo 710320 711491 := bstep (se 1 (by rfl) ⟨533618, by rfl⟩ : syracuseStep 711491 = 1067237) B1067237
theorem B1203025 : Blo 710320 1203025 := bstep (se 2 (by rfl) ⟨451134, by rfl⟩ : syracuseStep 1203025 = 902269) B902269
theorem B711507 : Blo 710320 711507 := bstep (se 1 (by rfl) ⟨533630, by rfl⟩ : syracuseStep 711507 = 1067261) B1067261
theorem B711523 : Blo 710320 711523 := bstep (se 1 (by rfl) ⟨533642, by rfl⟩ : syracuseStep 711523 = 1067285) B1067285
theorem B711539 : Blo 710320 711539 := bstep (se 1 (by rfl) ⟨533654, by rfl⟩ : syracuseStep 711539 = 1067309) B1067309
theorem B1203059 : Blo 710320 1203059 := bstep (se 1 (by rfl) ⟨902294, by rfl⟩ : syracuseStep 1203059 = 1804589) B1804589
theorem B711555 : Blo 710320 711555 := bstep (se 1 (by rfl) ⟨533666, by rfl⟩ : syracuseStep 711555 = 1067333) B1067333
theorem B711571 : Blo 710320 711571 := bstep (se 1 (by rfl) ⟨533678, by rfl⟩ : syracuseStep 711571 = 1067357) B1067357
theorem B711587 : Blo 710320 711587 := bstep (se 1 (by rfl) ⟨533690, by rfl⟩ : syracuseStep 711587 = 1067381) B1067381
theorem B711603 : Blo 710320 711603 := bstep (se 1 (by rfl) ⟨533702, by rfl⟩ : syracuseStep 711603 = 1067405) B1067405
theorem B711619 : Blo 710320 711619 := bstep (se 1 (by rfl) ⟨533714, by rfl⟩ : syracuseStep 711619 = 1067429) B1067429
theorem B711635 : Blo 710320 711635 := bstep (se 1 (by rfl) ⟨533726, by rfl⟩ : syracuseStep 711635 = 1067453) B1067453
theorem B711651 : Blo 710320 711651 := bstep (se 1 (by rfl) ⟨533738, by rfl⟩ : syracuseStep 711651 = 1067477) B1067477
theorem B711667 : Blo 710320 711667 := bstep (se 1 (by rfl) ⟨533750, by rfl⟩ : syracuseStep 711667 = 1067501) B1067501
theorem B1203187 : Blo 710320 1203187 := bstep (se 1 (by rfl) ⟨902390, by rfl⟩ : syracuseStep 1203187 = 1804781) B1804781
theorem B711683 : Blo 710320 711683 := bstep (se 1 (by rfl) ⟨533762, by rfl⟩ : syracuseStep 711683 = 1067525) B1067525
theorem B2284561 : Blo 710320 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B711699 : Blo 710320 711699 := bstep (se 1 (by rfl) ⟨533774, by rfl⟩ : syracuseStep 711699 = 1067549) B1067549
theorem B711715 : Blo 710320 711715 := bstep (se 1 (by rfl) ⟨533786, by rfl⟩ : syracuseStep 711715 = 1067573) B1067573
theorem B711731 : Blo 710320 711731 := bstep (se 1 (by rfl) ⟨533798, by rfl⟩ : syracuseStep 711731 = 1067597) B1067597
theorem B711747 : Blo 710320 711747 := bstep (se 1 (by rfl) ⟨533810, by rfl⟩ : syracuseStep 711747 = 1067621) B1067621
theorem B711763 : Blo 710320 711763 := bstep (se 1 (by rfl) ⟨533822, by rfl⟩ : syracuseStep 711763 = 1067645) B1067645
theorem B711779 : Blo 710320 711779 := bstep (se 1 (by rfl) ⟨533834, by rfl⟩ : syracuseStep 711779 = 1067669) B1067669
theorem B711795 : Blo 710320 711795 := bstep (se 1 (by rfl) ⟨533846, by rfl⟩ : syracuseStep 711795 = 1067693) B1067693
theorem B1203329 : Blo 710320 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B711811 : Blo 710320 711811 := bstep (se 1 (by rfl) ⟨533858, by rfl⟩ : syracuseStep 711811 = 1067717) B1067717
theorem B711827 : Blo 710320 711827 := bstep (se 1 (by rfl) ⟨533870, by rfl⟩ : syracuseStep 711827 = 1067741) B1067741
theorem B711843 : Blo 710320 711843 := bstep (se 1 (by rfl) ⟨533882, by rfl⟩ : syracuseStep 711843 = 1067765) B1067765
theorem B711859 : Blo 710320 711859 := bstep (se 1 (by rfl) ⟨533894, by rfl⟩ : syracuseStep 711859 = 1067789) B1067789
theorem B711875 : Blo 710320 711875 := bstep (se 1 (by rfl) ⟨533906, by rfl⟩ : syracuseStep 711875 = 1067813) B1067813
theorem B711891 : Blo 710320 711891 := bstep (se 1 (by rfl) ⟨533918, by rfl⟩ : syracuseStep 711891 = 1067837) B1067837
theorem B711907 : Blo 710320 711907 := bstep (se 1 (by rfl) ⟨533930, by rfl⟩ : syracuseStep 711907 = 1067861) B1067861
theorem B711923 : Blo 710320 711923 := bstep (se 1 (by rfl) ⟨533942, by rfl⟩ : syracuseStep 711923 = 1067885) B1067885
theorem B1203457 : Blo 710320 1203457 := bstep (se 2 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 1203457 = 902593) B902593
theorem B1924355 : Blo 710320 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B711939 : Blo 710320 711939 := bstep (se 1 (by rfl) ⟨533954, by rfl⟩ : syracuseStep 711939 = 1067909) B1067909
theorem B711955 : Blo 710320 711955 := bstep (se 1 (by rfl) ⟨533966, by rfl⟩ : syracuseStep 711955 = 1067933) B1067933
theorem B711971 : Blo 710320 711971 := bstep (se 1 (by rfl) ⟨533978, by rfl⟩ : syracuseStep 711971 = 1067957) B1067957
theorem B1203491 : Blo 710320 1203491 := bstep (se 1 (by rfl) ⟨902618, by rfl⟩ : syracuseStep 1203491 = 1805237) B1805237
theorem B2055473 : Blo 710320 2055473 := bstep (se 2 (by rfl) ⟨770802, by rfl⟩ : syracuseStep 2055473 = 1541605) B1541605
theorem B711987 : Blo 710320 711987 := bstep (se 1 (by rfl) ⟨533990, by rfl⟩ : syracuseStep 711987 = 1067981) B1067981
theorem B712003 : Blo 710320 712003 := bstep (se 1 (by rfl) ⟨534002, by rfl⟩ : syracuseStep 712003 = 1068005) B1068005
theorem B712019 : Blo 710320 712019 := bstep (se 1 (by rfl) ⟨534014, by rfl⟩ : syracuseStep 712019 = 1068029) B1068029
theorem B8314211 : Blo 710320 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B3038563 : Blo 710320 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B712035 : Blo 710320 712035 := bstep (se 1 (by rfl) ⟨534026, by rfl⟩ : syracuseStep 712035 = 1068053) B1068053
theorem B712051 : Blo 710320 712051 := bstep (se 1 (by rfl) ⟨534038, by rfl⟩ : syracuseStep 712051 = 1068077) B1068077
theorem B712067 : Blo 710320 712067 := bstep (se 1 (by rfl) ⟨534050, by rfl⟩ : syracuseStep 712067 = 1068101) B1068101
theorem B712083 : Blo 710320 712083 := bstep (se 1 (by rfl) ⟨534062, by rfl⟩ : syracuseStep 712083 = 1068125) B1068125
theorem B1203619 : Blo 710320 1203619 := bstep (se 1 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 1203619 = 1805429) B1805429
theorem B712099 : Blo 710320 712099 := bstep (se 1 (by rfl) ⟨534074, by rfl⟩ : syracuseStep 712099 = 1068149) B1068149
theorem B712115 : Blo 710320 712115 := bstep (se 1 (by rfl) ⟨534086, by rfl⟩ : syracuseStep 712115 = 1068173) B1068173
theorem B712131 : Blo 710320 712131 := bstep (se 1 (by rfl) ⟨534098, by rfl⟩ : syracuseStep 712131 = 1068197) B1068197
theorem B712147 : Blo 710320 712147 := bstep (se 1 (by rfl) ⟨534110, by rfl⟩ : syracuseStep 712147 = 1068221) B1068221
theorem B712163 : Blo 710320 712163 := bstep (se 1 (by rfl) ⟨534122, by rfl⟩ : syracuseStep 712163 = 1068245) B1068245
theorem B5398001 : Blo 710320 5398001 := bstep (se 2 (by rfl) ⟨2024250, by rfl⟩ : syracuseStep 5398001 = 4048501) B4048501
theorem B712179 : Blo 710320 712179 := bstep (se 1 (by rfl) ⟨534134, by rfl⟩ : syracuseStep 712179 = 1068269) B1068269
theorem B712195 : Blo 710320 712195 := bstep (se 1 (by rfl) ⟨534146, by rfl⟩ : syracuseStep 712195 = 1068293) B1068293
theorem B712211 : Blo 710320 712211 := bstep (se 1 (by rfl) ⟨534158, by rfl⟩ : syracuseStep 712211 = 1068317) B1068317
theorem B712227 : Blo 710320 712227 := bstep (se 1 (by rfl) ⟨534170, by rfl⟩ : syracuseStep 712227 = 1068341) B1068341
theorem B1203761 : Blo 710320 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B712243 : Blo 710320 712243 := bstep (se 1 (by rfl) ⟨534182, by rfl⟩ : syracuseStep 712243 = 1068365) B1068365
theorem B712259 : Blo 710320 712259 := bstep (se 1 (by rfl) ⟨534194, by rfl⟩ : syracuseStep 712259 = 1068389) B1068389
theorem B712275 : Blo 710320 712275 := bstep (se 1 (by rfl) ⟨534206, by rfl⟩ : syracuseStep 712275 = 1068413) B1068413
theorem B712291 : Blo 710320 712291 := bstep (se 1 (by rfl) ⟨534218, by rfl⟩ : syracuseStep 712291 = 1068437) B1068437
theorem B2285165 : Blo 710320 2285165 := bstep (se 3 (by rfl) ⟨428468, by rfl⟩ : syracuseStep 2285165 = 856937) B856937
theorem B712307 : Blo 710320 712307 := bstep (se 1 (by rfl) ⟨534230, by rfl⟩ : syracuseStep 712307 = 1068461) B1068461
theorem B712323 : Blo 710320 712323 := bstep (se 1 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 712323 = 1068485) B1068485
theorem B6086285 : Blo 710320 6086285 := bstep (se 3 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 6086285 = 2282357) B2282357
theorem B712339 : Blo 710320 712339 := bstep (se 1 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 712339 = 1068509) B1068509
theorem B712355 : Blo 710320 712355 := bstep (se 1 (by rfl) ⟨534266, by rfl⟩ : syracuseStep 712355 = 1068533) B1068533
theorem B1203889 : Blo 710320 1203889 := bstep (se 2 (by rfl) ⟨451458, by rfl⟩ : syracuseStep 1203889 = 902917) B902917
theorem B712371 : Blo 710320 712371 := bstep (se 1 (by rfl) ⟨534278, by rfl⟩ : syracuseStep 712371 = 1068557) B1068557
theorem B712387 : Blo 710320 712387 := bstep (se 1 (by rfl) ⟨534290, by rfl⟩ : syracuseStep 712387 = 1068581) B1068581
theorem B3464909 : Blo 710320 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B1138385 : Blo 710320 1138385 := bstep (se 2 (by rfl) ⟨426894, by rfl⟩ : syracuseStep 1138385 = 853789) B853789
theorem B712403 : Blo 710320 712403 := bstep (se 1 (by rfl) ⟨534302, by rfl⟩ : syracuseStep 712403 = 1068605) B1068605
theorem B1203923 : Blo 710320 1203923 := bstep (se 1 (by rfl) ⟨902942, by rfl⟩ : syracuseStep 1203923 = 1805885) B1805885
theorem B712419 : Blo 710320 712419 := bstep (se 1 (by rfl) ⟨534314, by rfl⟩ : syracuseStep 712419 = 1068629) B1068629
theorem B712435 : Blo 710320 712435 := bstep (se 1 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 712435 = 1068653) B1068653
theorem B712451 : Blo 710320 712451 := bstep (se 1 (by rfl) ⟨534338, by rfl⟩ : syracuseStep 712451 = 1068677) B1068677
theorem B2023181 : Blo 710320 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B712467 : Blo 710320 712467 := bstep (se 1 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 712467 = 1068701) B1068701
theorem B712483 : Blo 710320 712483 := bstep (se 1 (by rfl) ⟨534362, by rfl⟩ : syracuseStep 712483 = 1068725) B1068725
theorem B712499 : Blo 710320 712499 := bstep (se 1 (by rfl) ⟨534374, by rfl⟩ : syracuseStep 712499 = 1068749) B1068749
theorem B712515 : Blo 710320 712515 := bstep (se 1 (by rfl) ⟨534386, by rfl⟩ : syracuseStep 712515 = 1068773) B1068773
theorem B712531 : Blo 710320 712531 := bstep (se 1 (by rfl) ⟨534398, by rfl⟩ : syracuseStep 712531 = 1068797) B1068797
theorem B1204051 : Blo 710320 1204051 := bstep (se 1 (by rfl) ⟨903038, by rfl⟩ : syracuseStep 1204051 = 1806077) B1806077
theorem B712547 : Blo 710320 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B712563 : Blo 710320 712563 := bstep (se 1 (by rfl) ⟨534422, by rfl⟩ : syracuseStep 712563 = 1068845) B1068845
theorem B712579 : Blo 710320 712579 := bstep (se 1 (by rfl) ⟨534434, by rfl⟩ : syracuseStep 712579 = 1068869) B1068869
theorem B1925005 : Blo 710320 1925005 := bstep (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) B721877
theorem B712595 : Blo 710320 712595 := bstep (se 1 (by rfl) ⟨534446, by rfl⟩ : syracuseStep 712595 = 1068893) B1068893
theorem B712611 : Blo 710320 712611 := bstep (se 1 (by rfl) ⟨534458, by rfl⟩ : syracuseStep 712611 = 1068917) B1068917
theorem B712627 : Blo 710320 712627 := bstep (se 1 (by rfl) ⟨534470, by rfl⟩ : syracuseStep 712627 = 1068941) B1068941
theorem B712643 : Blo 710320 712643 := bstep (se 1 (by rfl) ⟨534482, by rfl⟩ : syracuseStep 712643 = 1068965) B1068965
theorem B3596237 : Blo 710320 3596237 := bstep (se 3 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 3596237 = 1348589) B1348589
theorem B2711501 : Blo 710320 2711501 := bstep (se 3 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 2711501 = 1016813) B1016813
theorem B712659 : Blo 710320 712659 := bstep (se 1 (by rfl) ⟨534494, by rfl⟩ : syracuseStep 712659 = 1068989) B1068989
theorem B1204193 : Blo 710320 1204193 := bstep (se 2 (by rfl) ⟨451572, by rfl⟩ : syracuseStep 1204193 = 903145) B903145
theorem B712675 : Blo 710320 712675 := bstep (se 1 (by rfl) ⟨534506, by rfl⟩ : syracuseStep 712675 = 1069013) B1069013
theorem B712691 : Blo 710320 712691 := bstep (se 1 (by rfl) ⟨534518, by rfl⟩ : syracuseStep 712691 = 1069037) B1069037
theorem B712707 : Blo 710320 712707 := bstep (se 1 (by rfl) ⟨534530, by rfl⟩ : syracuseStep 712707 = 1069061) B1069061
theorem B712723 : Blo 710320 712723 := bstep (se 1 (by rfl) ⟨534542, by rfl⟩ : syracuseStep 712723 = 1069085) B1069085
theorem B712739 : Blo 710320 712739 := bstep (se 1 (by rfl) ⟨534554, by rfl⟩ : syracuseStep 712739 = 1069109) B1069109
theorem B712755 : Blo 710320 712755 := bstep (se 1 (by rfl) ⟨534566, by rfl⟩ : syracuseStep 712755 = 1069133) B1069133
theorem B712771 : Blo 710320 712771 := bstep (se 1 (by rfl) ⟨534578, by rfl⟩ : syracuseStep 712771 = 1069157) B1069157
theorem B712787 : Blo 710320 712787 := bstep (se 1 (by rfl) ⟨534590, by rfl⟩ : syracuseStep 712787 = 1069181) B1069181
theorem B1204321 : Blo 710320 1204321 := bstep (se 2 (by rfl) ⟨451620, by rfl⟩ : syracuseStep 1204321 = 903241) B903241
theorem B712803 : Blo 710320 712803 := bstep (se 1 (by rfl) ⟨534602, by rfl⟩ : syracuseStep 712803 = 1069205) B1069205
theorem B712819 : Blo 710320 712819 := bstep (se 1 (by rfl) ⟨534614, by rfl⟩ : syracuseStep 712819 = 1069229) B1069229
theorem B712835 : Blo 710320 712835 := bstep (se 1 (by rfl) ⟨534626, by rfl⟩ : syracuseStep 712835 = 1069253) B1069253
theorem B1204355 : Blo 710320 1204355 := bstep (se 1 (by rfl) ⟨903266, by rfl⟩ : syracuseStep 1204355 = 1806533) B1806533
theorem B712851 : Blo 710320 712851 := bstep (se 1 (by rfl) ⟨534638, by rfl⟩ : syracuseStep 712851 = 1069277) B1069277
theorem B712867 : Blo 710320 712867 := bstep (se 1 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 712867 = 1069301) B1069301
theorem B712883 : Blo 710320 712883 := bstep (se 1 (by rfl) ⟨534662, by rfl⟩ : syracuseStep 712883 = 1069325) B1069325
theorem B712899 : Blo 710320 712899 := bstep (se 1 (by rfl) ⟨534674, by rfl⟩ : syracuseStep 712899 = 1069349) B1069349
theorem B712915 : Blo 710320 712915 := bstep (se 1 (by rfl) ⟨534686, by rfl⟩ : syracuseStep 712915 = 1069373) B1069373
theorem B13000931 : Blo 710320 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B712931 : Blo 710320 712931 := bstep (se 1 (by rfl) ⟨534698, by rfl⟩ : syracuseStep 712931 = 1069397) B1069397
theorem B712947 : Blo 710320 712947 := bstep (se 1 (by rfl) ⟨534710, by rfl⟩ : syracuseStep 712947 = 1069421) B1069421
theorem B712963 : Blo 710320 712963 := bstep (se 1 (by rfl) ⟨534722, by rfl⟩ : syracuseStep 712963 = 1069445) B1069445
theorem B1204483 : Blo 710320 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B712979 : Blo 710320 712979 := bstep (se 1 (by rfl) ⟨534734, by rfl⟩ : syracuseStep 712979 = 1069469) B1069469
theorem B712995 : Blo 710320 712995 := bstep (se 1 (by rfl) ⟨534746, by rfl⟩ : syracuseStep 712995 = 1069493) B1069493
theorem B713011 : Blo 710320 713011 := bstep (se 1 (by rfl) ⟨534758, by rfl⟩ : syracuseStep 713011 = 1069517) B1069517
theorem B713027 : Blo 710320 713027 := bstep (se 1 (by rfl) ⟨534770, by rfl⟩ : syracuseStep 713027 = 1069541) B1069541
theorem B713043 : Blo 710320 713043 := bstep (se 1 (by rfl) ⟨534782, by rfl⟩ : syracuseStep 713043 = 1069565) B1069565
theorem B713059 : Blo 710320 713059 := bstep (se 1 (by rfl) ⟨534794, by rfl⟩ : syracuseStep 713059 = 1069589) B1069589
theorem B713075 : Blo 710320 713075 := bstep (se 1 (by rfl) ⟨534806, by rfl⟩ : syracuseStep 713075 = 1069613) B1069613
theorem B713091 : Blo 710320 713091 := bstep (se 1 (by rfl) ⟨534818, by rfl⟩ : syracuseStep 713091 = 1069637) B1069637
theorem B1204625 : Blo 710320 1204625 := bstep (se 2 (by rfl) ⟨451734, by rfl⟩ : syracuseStep 1204625 = 903469) B903469
theorem B713107 : Blo 710320 713107 := bstep (se 1 (by rfl) ⟨534830, by rfl⟩ : syracuseStep 713107 = 1069661) B1069661
theorem B713123 : Blo 710320 713123 := bstep (se 1 (by rfl) ⟨534842, by rfl⟩ : syracuseStep 713123 = 1069685) B1069685
theorem B713139 : Blo 710320 713139 := bstep (se 1 (by rfl) ⟨534854, by rfl⟩ : syracuseStep 713139 = 1069709) B1069709
theorem B713155 : Blo 710320 713155 := bstep (se 1 (by rfl) ⟨534866, by rfl⟩ : syracuseStep 713155 = 1069733) B1069733
theorem B713171 : Blo 710320 713171 := bstep (se 1 (by rfl) ⟨534878, by rfl⟩ : syracuseStep 713171 = 1069757) B1069757
theorem B713187 : Blo 710320 713187 := bstep (se 1 (by rfl) ⟨534890, by rfl⟩ : syracuseStep 713187 = 1069781) B1069781
theorem B713203 : Blo 710320 713203 := bstep (se 1 (by rfl) ⟨534902, by rfl⟩ : syracuseStep 713203 = 1069805) B1069805
theorem B713219 : Blo 710320 713219 := bstep (se 1 (by rfl) ⟨534914, by rfl⟩ : syracuseStep 713219 = 1069829) B1069829
theorem B6840845 : Blo 710320 6840845 := bstep (se 3 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 6840845 = 2565317) B2565317
theorem B1204753 : Blo 710320 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B713235 : Blo 710320 713235 := bstep (se 1 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 713235 = 1069853) B1069853
theorem B713251 : Blo 710320 713251 := bstep (se 1 (by rfl) ⟨534938, by rfl⟩ : syracuseStep 713251 = 1069877) B1069877
theorem B713267 : Blo 710320 713267 := bstep (se 1 (by rfl) ⟨534950, by rfl⟩ : syracuseStep 713267 = 1069901) B1069901
theorem B1204787 : Blo 710320 1204787 := bstep (se 1 (by rfl) ⟨903590, by rfl⟩ : syracuseStep 1204787 = 1807181) B1807181
theorem B713283 : Blo 710320 713283 := bstep (se 1 (by rfl) ⟨534962, by rfl⟩ : syracuseStep 713283 = 1069925) B1069925
theorem B713299 : Blo 710320 713299 := bstep (se 1 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 713299 = 1069949) B1069949
theorem B713315 : Blo 710320 713315 := bstep (se 1 (by rfl) ⟨534986, by rfl⟩ : syracuseStep 713315 = 1069973) B1069973
theorem B713331 : Blo 710320 713331 := bstep (se 1 (by rfl) ⟨534998, by rfl⟩ : syracuseStep 713331 = 1069997) B1069997
theorem B713347 : Blo 710320 713347 := bstep (se 1 (by rfl) ⟨535010, by rfl⟩ : syracuseStep 713347 = 1070021) B1070021
theorem B713363 : Blo 710320 713363 := bstep (se 1 (by rfl) ⟨535022, by rfl⟩ : syracuseStep 713363 = 1070045) B1070045
theorem B713379 : Blo 710320 713379 := bstep (se 1 (by rfl) ⟨535034, by rfl⟩ : syracuseStep 713379 = 1070069) B1070069
theorem B713395 : Blo 710320 713395 := bstep (se 1 (by rfl) ⟨535046, by rfl⟩ : syracuseStep 713395 = 1070093) B1070093
theorem B1204915 : Blo 710320 1204915 := bstep (se 1 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 1204915 = 1807373) B1807373
theorem B713411 : Blo 710320 713411 := bstep (se 1 (by rfl) ⟨535058, by rfl⟩ : syracuseStep 713411 = 1070117) B1070117
theorem B713427 : Blo 710320 713427 := bstep (se 1 (by rfl) ⟨535070, by rfl⟩ : syracuseStep 713427 = 1070141) B1070141
theorem B713443 : Blo 710320 713443 := bstep (se 1 (by rfl) ⟨535082, by rfl⟩ : syracuseStep 713443 = 1070165) B1070165
theorem B6841073 : Blo 710320 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B713459 : Blo 710320 713459 := bstep (se 1 (by rfl) ⟨535094, by rfl⟩ : syracuseStep 713459 = 1070189) B1070189
theorem B713475 : Blo 710320 713475 := bstep (se 1 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 713475 = 1070213) B1070213
theorem B713491 : Blo 710320 713491 := bstep (se 1 (by rfl) ⟨535118, by rfl⟩ : syracuseStep 713491 = 1070237) B1070237
theorem B713507 : Blo 710320 713507 := bstep (se 1 (by rfl) ⟨535130, by rfl⟩ : syracuseStep 713507 = 1070261) B1070261
theorem B713523 : Blo 710320 713523 := bstep (se 1 (by rfl) ⟨535142, by rfl⟩ : syracuseStep 713523 = 1070285) B1070285
theorem B1205057 : Blo 710320 1205057 := bstep (se 2 (by rfl) ⟨451896, by rfl⟩ : syracuseStep 1205057 = 903793) B903793
theorem B713539 : Blo 710320 713539 := bstep (se 1 (by rfl) ⟨535154, by rfl⟩ : syracuseStep 713539 = 1070309) B1070309
theorem B713555 : Blo 710320 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B713571 : Blo 710320 713571 := bstep (se 1 (by rfl) ⟨535178, by rfl⟩ : syracuseStep 713571 = 1070357) B1070357
theorem B713587 : Blo 710320 713587 := bstep (se 1 (by rfl) ⟨535190, by rfl⟩ : syracuseStep 713587 = 1070381) B1070381
theorem B713603 : Blo 710320 713603 := bstep (se 1 (by rfl) ⟨535202, by rfl⟩ : syracuseStep 713603 = 1070405) B1070405
theorem B713619 : Blo 710320 713619 := bstep (se 1 (by rfl) ⟨535214, by rfl⟩ : syracuseStep 713619 = 1070429) B1070429
theorem B713635 : Blo 710320 713635 := bstep (se 1 (by rfl) ⟨535226, by rfl⟩ : syracuseStep 713635 = 1070453) B1070453
theorem B2024365 : Blo 710320 2024365 := bstep (se 3 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 2024365 = 759137) B759137
theorem B713651 : Blo 710320 713651 := bstep (se 1 (by rfl) ⟨535238, by rfl⟩ : syracuseStep 713651 = 1070477) B1070477
theorem B1205185 : Blo 710320 1205185 := bstep (se 2 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 1205185 = 903889) B903889
theorem B713667 : Blo 710320 713667 := bstep (se 1 (by rfl) ⟨535250, by rfl⟩ : syracuseStep 713667 = 1070501) B1070501
theorem B1598417 : Blo 710320 1598417 := bstep (se 2 (by rfl) ⟨599406, by rfl⟩ : syracuseStep 1598417 = 1198813) B1198813
theorem B713683 : Blo 710320 713683 := bstep (se 1 (by rfl) ⟨535262, by rfl⟩ : syracuseStep 713683 = 1070525) B1070525
theorem B1598435 : Blo 710320 1598435 := bstep (se 1 (by rfl) ⟨1198826, by rfl⟩ : syracuseStep 1598435 = 2397653) B2397653
theorem B713699 : Blo 710320 713699 := bstep (se 1 (by rfl) ⟨535274, by rfl⟩ : syracuseStep 713699 = 1070549) B1070549
theorem B1205219 : Blo 710320 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B713715 : Blo 710320 713715 := bstep (se 1 (by rfl) ⟨535286, by rfl⟩ : syracuseStep 713715 = 1070573) B1070573
theorem B812035 : Blo 710320 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B713731 : Blo 710320 713731 := bstep (se 1 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 713731 = 1070597) B1070597
theorem B713747 : Blo 710320 713747 := bstep (se 1 (by rfl) ⟨535310, by rfl⟩ : syracuseStep 713747 = 1070621) B1070621
theorem B713763 : Blo 710320 713763 := bstep (se 1 (by rfl) ⟨535322, by rfl⟩ : syracuseStep 713763 = 1070645) B1070645
theorem B713779 : Blo 710320 713779 := bstep (se 1 (by rfl) ⟨535334, by rfl⟩ : syracuseStep 713779 = 1070669) B1070669
theorem B713795 : Blo 710320 713795 := bstep (se 1 (by rfl) ⟨535346, by rfl⟩ : syracuseStep 713795 = 1070693) B1070693
theorem B713811 : Blo 710320 713811 := bstep (se 1 (by rfl) ⟨535358, by rfl⟩ : syracuseStep 713811 = 1070717) B1070717
theorem B713827 : Blo 710320 713827 := bstep (se 1 (by rfl) ⟨535370, by rfl⟩ : syracuseStep 713827 = 1070741) B1070741
theorem B1205347 : Blo 710320 1205347 := bstep (se 1 (by rfl) ⟨904010, by rfl⟩ : syracuseStep 1205347 = 1808021) B1808021
theorem B713843 : Blo 710320 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B713859 : Blo 710320 713859 := bstep (se 1 (by rfl) ⟨535394, by rfl⟩ : syracuseStep 713859 = 1070789) B1070789
theorem B713875 : Blo 710320 713875 := bstep (se 1 (by rfl) ⟨535406, by rfl⟩ : syracuseStep 713875 = 1070813) B1070813
theorem B713891 : Blo 710320 713891 := bstep (se 1 (by rfl) ⟨535418, by rfl⟩ : syracuseStep 713891 = 1070837) B1070837
theorem B2221229 : Blo 710320 2221229 := bstep (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) B832961
theorem B713907 : Blo 710320 713907 := bstep (se 1 (by rfl) ⟨535430, by rfl⟩ : syracuseStep 713907 = 1070861) B1070861
theorem B713923 : Blo 710320 713923 := bstep (se 1 (by rfl) ⟨535442, by rfl⟩ : syracuseStep 713923 = 1070885) B1070885
theorem B1139923 : Blo 710320 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B713939 : Blo 710320 713939 := bstep (se 1 (by rfl) ⟨535454, by rfl⟩ : syracuseStep 713939 = 1070909) B1070909
theorem B9233635 : Blo 710320 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B713955 : Blo 710320 713955 := bstep (se 1 (by rfl) ⟨535466, by rfl⟩ : syracuseStep 713955 = 1070933) B1070933
theorem B1598705 : Blo 710320 1598705 := bstep (se 2 (by rfl) ⟨599514, by rfl⟩ : syracuseStep 1598705 = 1199029) B1199029
theorem B713971 : Blo 710320 713971 := bstep (se 1 (by rfl) ⟨535478, by rfl⟩ : syracuseStep 713971 = 1070957) B1070957
theorem B1139969 : Blo 710320 1139969 := bstep (se 2 (by rfl) ⟨427488, by rfl⟩ : syracuseStep 1139969 = 854977) B854977
theorem B1598723 : Blo 710320 1598723 := bstep (se 1 (by rfl) ⟨1199042, by rfl⟩ : syracuseStep 1598723 = 2398085) B2398085
theorem B713987 : Blo 710320 713987 := bstep (se 1 (by rfl) ⟨535490, by rfl⟩ : syracuseStep 713987 = 1070981) B1070981
theorem B714003 : Blo 710320 714003 := bstep (se 1 (by rfl) ⟨535502, by rfl⟩ : syracuseStep 714003 = 1071005) B1071005
theorem B714019 : Blo 710320 714019 := bstep (se 1 (by rfl) ⟨535514, by rfl⟩ : syracuseStep 714019 = 1071029) B1071029
theorem B714035 : Blo 710320 714035 := bstep (se 1 (by rfl) ⟨535526, by rfl⟩ : syracuseStep 714035 = 1071053) B1071053
theorem B1926467 : Blo 710320 1926467 := bstep (se 1 (by rfl) ⟨1444850, by rfl⟩ : syracuseStep 1926467 = 2889701) B2889701
theorem B714051 : Blo 710320 714051 := bstep (se 1 (by rfl) ⟨535538, by rfl⟩ : syracuseStep 714051 = 1071077) B1071077
theorem B714067 : Blo 710320 714067 := bstep (se 1 (by rfl) ⟨535550, by rfl⟩ : syracuseStep 714067 = 1071101) B1071101
theorem B714083 : Blo 710320 714083 := bstep (se 1 (by rfl) ⟨535562, by rfl⟩ : syracuseStep 714083 = 1071125) B1071125
theorem B714099 : Blo 710320 714099 := bstep (se 1 (by rfl) ⟨535574, by rfl⟩ : syracuseStep 714099 = 1071149) B1071149
theorem B714115 : Blo 710320 714115 := bstep (se 1 (by rfl) ⟨535586, by rfl⟩ : syracuseStep 714115 = 1071173) B1071173
theorem B714131 : Blo 710320 714131 := bstep (se 1 (by rfl) ⟨535598, by rfl⟩ : syracuseStep 714131 = 1071197) B1071197
theorem B714147 : Blo 710320 714147 := bstep (se 1 (by rfl) ⟨535610, by rfl⟩ : syracuseStep 714147 = 1071221) B1071221
theorem B714163 : Blo 710320 714163 := bstep (se 1 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 714163 = 1071245) B1071245
theorem B714179 : Blo 710320 714179 := bstep (se 1 (by rfl) ⟨535634, by rfl⟩ : syracuseStep 714179 = 1071269) B1071269
theorem B1926605 : Blo 710320 1926605 := bstep (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) B722477
theorem B714195 : Blo 710320 714195 := bstep (se 1 (by rfl) ⟨535646, by rfl⟩ : syracuseStep 714195 = 1071293) B1071293
theorem B714211 : Blo 710320 714211 := bstep (se 1 (by rfl) ⟨535658, by rfl⟩ : syracuseStep 714211 = 1071317) B1071317
theorem B714227 : Blo 710320 714227 := bstep (se 1 (by rfl) ⟨535670, by rfl⟩ : syracuseStep 714227 = 1071341) B1071341
theorem B714243 : Blo 710320 714243 := bstep (se 1 (by rfl) ⟨535682, by rfl⟩ : syracuseStep 714243 = 1071365) B1071365
theorem B1598993 : Blo 710320 1598993 := bstep (se 2 (by rfl) ⟨599622, by rfl⟩ : syracuseStep 1598993 = 1199245) B1199245
theorem B714259 : Blo 710320 714259 := bstep (se 1 (by rfl) ⟨535694, by rfl⟩ : syracuseStep 714259 = 1071389) B1071389
theorem B1599011 : Blo 710320 1599011 := bstep (se 1 (by rfl) ⟨1199258, by rfl⟩ : syracuseStep 1599011 = 2398517) B2398517
theorem B714275 : Blo 710320 714275 := bstep (se 1 (by rfl) ⟨535706, by rfl⟩ : syracuseStep 714275 = 1071413) B1071413
theorem B714291 : Blo 710320 714291 := bstep (se 1 (by rfl) ⟨535718, by rfl⟩ : syracuseStep 714291 = 1071437) B1071437
theorem B714307 : Blo 710320 714307 := bstep (se 1 (by rfl) ⟨535730, by rfl⟩ : syracuseStep 714307 = 1071461) B1071461
theorem B812659 : Blo 710320 812659 := bstep (se 1 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 812659 = 1218989) B1218989
theorem B3041009 : Blo 710320 3041009 := bstep (se 2 (by rfl) ⟨1140378, by rfl⟩ : syracuseStep 3041009 = 2280757) B2280757
theorem B1599281 : Blo 710320 1599281 := bstep (se 2 (by rfl) ⟨599730, by rfl⟩ : syracuseStep 1599281 = 1199461) B1199461
theorem B1599299 : Blo 710320 1599299 := bstep (se 1 (by rfl) ⟨1199474, by rfl⟩ : syracuseStep 1599299 = 2398949) B2398949
theorem B2025425 : Blo 710320 2025425 := bstep (se 2 (by rfl) ⟨759534, by rfl⟩ : syracuseStep 2025425 = 1519069) B1519069
theorem B5138417 : Blo 710320 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B1599569 : Blo 710320 1599569 := bstep (se 2 (by rfl) ⟨599838, by rfl⟩ : syracuseStep 1599569 = 1199677) B1199677
theorem B1599587 : Blo 710320 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B1140961 : Blo 710320 1140961 := bstep (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) B855721
theorem B1599857 : Blo 710320 1599857 := bstep (se 2 (by rfl) ⟨599946, by rfl⟩ : syracuseStep 1599857 = 1199893) B1199893
theorem B1599875 : Blo 710320 1599875 := bstep (se 1 (by rfl) ⟨1199906, by rfl⟩ : syracuseStep 1599875 = 2399813) B2399813
theorem B15362581 : Blo 710320 15362581 := bstep (se 6 (by rfl) ⟨360060, by rfl⟩ : syracuseStep 15362581 = 720121) B720121
theorem B2026097 : Blo 710320 2026097 := bstep (se 2 (by rfl) ⟨759786, by rfl⟩ : syracuseStep 2026097 = 1519573) B1519573
theorem B5139085 : Blo 710320 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B1600145 : Blo 710320 1600145 := bstep (se 2 (by rfl) ⟨600054, by rfl⟩ : syracuseStep 1600145 = 1200109) B1200109
theorem B1141409 : Blo 710320 1141409 := bstep (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) B856057
theorem B1600163 : Blo 710320 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B1370801 : Blo 710320 1370801 := bstep (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) B1028101
theorem B8121059 : Blo 710320 8121059 := bstep (se 1 (by rfl) ⟨6090794, by rfl⟩ : syracuseStep 8121059 = 12181589) B12181589
theorem B3599153 : Blo 710320 3599153 := bstep (se 2 (by rfl) ⟨1349682, by rfl⟩ : syracuseStep 3599153 = 2699365) B2699365
theorem B1600433 : Blo 710320 1600433 := bstep (se 2 (by rfl) ⟨600162, by rfl⟩ : syracuseStep 1600433 = 1200325) B1200325
theorem B1600451 : Blo 710320 1600451 := bstep (se 1 (by rfl) ⟨1200338, by rfl⟩ : syracuseStep 1600451 = 2400677) B2400677
theorem B10251461 : Blo 710320 10251461 := bstep (se 4 (by rfl) ⟨961074, by rfl⟩ : syracuseStep 10251461 = 1922149) B1922149
theorem B1600721 : Blo 710320 1600721 := bstep (se 2 (by rfl) ⟨600270, by rfl⟩ : syracuseStep 1600721 = 1200541) B1200541
theorem B1600739 : Blo 710320 1600739 := bstep (se 1 (by rfl) ⟨1200554, by rfl⟩ : syracuseStep 1600739 = 2401109) B2401109
theorem B2026883 : Blo 710320 2026883 := bstep (se 1 (by rfl) ⟨1520162, by rfl⟩ : syracuseStep 2026883 = 3040325) B3040325
theorem B1601009 : Blo 710320 1601009 := bstep (se 2 (by rfl) ⟨600378, by rfl⟩ : syracuseStep 1601009 = 1200757) B1200757
theorem B1601027 : Blo 710320 1601027 := bstep (se 1 (by rfl) ⟨1200770, by rfl⟩ : syracuseStep 1601027 = 2401541) B2401541
theorem B1142275 : Blo 710320 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B2027213 : Blo 710320 2027213 := bstep (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) B760205
theorem B1044193 : Blo 710320 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B1601297 : Blo 710320 1601297 := bstep (se 2 (by rfl) ⟨600486, by rfl⟩ : syracuseStep 1601297 = 1200973) B1200973
theorem B2027281 : Blo 710320 2027281 := bstep (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) B1520461
theorem B1601315 : Blo 710320 1601315 := bstep (se 1 (by rfl) ⟨1200986, by rfl⟩ : syracuseStep 1601315 = 2401973) B2401973
theorem B1011619 : Blo 710320 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B5140493 : Blo 710320 5140493 := bstep (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) B1927685
theorem B2027555 : Blo 710320 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B1601585 : Blo 710320 1601585 := bstep (se 2 (by rfl) ⟨600594, by rfl⟩ : syracuseStep 1601585 = 1201189) B1201189
theorem B1601603 : Blo 710320 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B1142947 : Blo 710320 1142947 := bstep (se 1 (by rfl) ⟨857210, by rfl⟩ : syracuseStep 1142947 = 1714421) B1714421
theorem B1798321 : Blo 710320 1798321 := bstep (se 2 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 1798321 = 1348741) B1348741
theorem B1142993 : Blo 710320 1142993 := bstep (se 2 (by rfl) ⟨428622, by rfl⟩ : syracuseStep 1142993 = 857245) B857245
theorem B3600611 : Blo 710320 3600611 := bstep (se 1 (by rfl) ⟨2700458, by rfl⟩ : syracuseStep 3600611 = 5400917) B5400917
theorem B1011955 : Blo 710320 1011955 := bstep (se 1 (by rfl) ⟨758966, by rfl⟩ : syracuseStep 1011955 = 1517933) B1517933
theorem B1601873 : Blo 710320 1601873 := bstep (se 2 (by rfl) ⟨600702, by rfl⟩ : syracuseStep 1601873 = 1201405) B1201405
theorem B1601891 : Blo 710320 1601891 := bstep (se 1 (by rfl) ⟨1201418, by rfl⟩ : syracuseStep 1601891 = 2402837) B2402837
theorem B1798595 : Blo 710320 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B1602161 : Blo 710320 1602161 := bstep (se 2 (by rfl) ⟨600810, by rfl⟩ : syracuseStep 1602161 = 1201621) B1201621
theorem B1798787 : Blo 710320 1798787 := bstep (se 1 (by rfl) ⟨1349090, by rfl⟩ : syracuseStep 1798787 = 2698181) B2698181
theorem B1602179 : Blo 710320 1602179 := bstep (se 1 (by rfl) ⟨1201634, by rfl⟩ : syracuseStep 1602179 = 2403269) B2403269
theorem B4453069 : Blo 710320 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B1143505 : Blo 710320 1143505 := bstep (se 2 (by rfl) ⟨428814, by rfl⟩ : syracuseStep 1143505 = 857629) B857629
theorem B1012513 : Blo 710320 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B1372963 : Blo 710320 1372963 := bstep (se 1 (by rfl) ⟨1029722, by rfl⟩ : syracuseStep 1372963 = 2059445) B2059445
theorem B1012547 : Blo 710320 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B2028397 : Blo 710320 2028397 := bstep (se 3 (by rfl) ⟨380324, by rfl⟩ : syracuseStep 2028397 = 760649) B760649
theorem B1602449 : Blo 710320 1602449 := bstep (se 2 (by rfl) ⟨600918, by rfl⟩ : syracuseStep 1602449 = 1201837) B1201837
theorem B1602467 : Blo 710320 1602467 := bstep (se 1 (by rfl) ⟨1201850, by rfl⟩ : syracuseStep 1602467 = 2403701) B2403701
theorem B1831889 : Blo 710320 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B4060165 : Blo 710320 4060165 := bstep (se 4 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 4060165 = 761281) B761281
theorem B3601421 : Blo 710320 3601421 := bstep (se 3 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 3601421 = 1350533) B1350533
theorem B2028557 : Blo 710320 2028557 := bstep (se 3 (by rfl) ⟨380354, by rfl⟩ : syracuseStep 2028557 = 760709) B760709
theorem B9270413 : Blo 710320 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B1602737 : Blo 710320 1602737 := bstep (se 2 (by rfl) ⟨601026, by rfl⟩ : syracuseStep 1602737 = 1202053) B1202053
theorem B1602755 : Blo 710320 1602755 := bstep (se 1 (by rfl) ⟨1202066, by rfl⟩ : syracuseStep 1602755 = 2404133) B2404133
theorem B2028739 : Blo 710320 2028739 := bstep (se 1 (by rfl) ⟨1521554, by rfl⟩ : syracuseStep 2028739 = 3043109) B3043109
theorem B1144049 : Blo 710320 1144049 := bstep (se 2 (by rfl) ⟨429018, by rfl⟩ : syracuseStep 1144049 = 858037) B858037
theorem B1930499 : Blo 710320 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B2061571 : Blo 710320 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B1013105 : Blo 710320 1013105 := bstep (se 2 (by rfl) ⟨379914, by rfl⟩ : syracuseStep 1013105 = 759829) B759829
theorem B3044749 : Blo 710320 3044749 := bstep (se 3 (by rfl) ⟨570890, by rfl⟩ : syracuseStep 3044749 = 1141781) B1141781
theorem B8648117 : Blo 710320 8648117 := bstep (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) B810761
theorem B1013185 : Blo 710320 1013185 := bstep (se 2 (by rfl) ⟨379944, by rfl⟩ : syracuseStep 1013185 = 759889) B759889
theorem B1603025 : Blo 710320 1603025 := bstep (se 2 (by rfl) ⟨601134, by rfl⟩ : syracuseStep 1603025 = 1202269) B1202269
theorem B1603043 : Blo 710320 1603043 := bstep (se 1 (by rfl) ⟨1202282, by rfl⟩ : syracuseStep 1603043 = 2404565) B2404565
theorem B1799729 : Blo 710320 1799729 := bstep (se 2 (by rfl) ⟨674898, by rfl⟩ : syracuseStep 1799729 = 1349797) B1349797
theorem B4617805 : Blo 710320 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B1799779 : Blo 710320 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B1799921 : Blo 710320 1799921 := bstep (se 2 (by rfl) ⟨674970, by rfl⟩ : syracuseStep 1799921 = 1349941) B1349941
theorem B1603313 : Blo 710320 1603313 := bstep (se 2 (by rfl) ⟨601242, by rfl⟩ : syracuseStep 1603313 = 1202485) B1202485
theorem B1603331 : Blo 710320 1603331 := bstep (se 1 (by rfl) ⟨1202498, by rfl⟩ : syracuseStep 1603331 = 2404997) B2404997
theorem B1603601 : Blo 710320 1603601 := bstep (se 2 (by rfl) ⟨601350, by rfl⟩ : syracuseStep 1603601 = 1202701) B1202701
theorem B1603619 : Blo 710320 1603619 := bstep (se 1 (by rfl) ⟨1202714, by rfl⟩ : syracuseStep 1603619 = 2405429) B2405429
theorem B1013971 : Blo 710320 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B1603889 : Blo 710320 1603889 := bstep (se 2 (by rfl) ⟨601458, by rfl⟩ : syracuseStep 1603889 = 1202917) B1202917
theorem B1603907 : Blo 710320 1603907 := bstep (se 1 (by rfl) ⟨1202930, by rfl⟩ : syracuseStep 1603907 = 2405861) B2405861
theorem B2030129 : Blo 710320 2030129 := bstep (se 2 (by rfl) ⟨761298, by rfl⟩ : syracuseStep 2030129 = 1522597) B1522597
theorem B1604177 : Blo 710320 1604177 := bstep (se 2 (by rfl) ⟨601566, by rfl⟩ : syracuseStep 1604177 = 1203133) B1203133
theorem B1604195 : Blo 710320 1604195 := bstep (se 1 (by rfl) ⟨1203146, by rfl⟩ : syracuseStep 1604195 = 2406293) B2406293
theorem B1014449 : Blo 710320 1014449 := bstep (se 2 (by rfl) ⟨380418, by rfl⟩ : syracuseStep 1014449 = 760837) B760837
theorem B1800913 : Blo 710320 1800913 := bstep (se 2 (by rfl) ⟨675342, by rfl⟩ : syracuseStep 1800913 = 1350685) B1350685
theorem B1080067 : Blo 710320 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B4324109 : Blo 710320 4324109 := bstep (se 3 (by rfl) ⟨810770, by rfl⟩ : syracuseStep 4324109 = 1621541) B1621541
theorem B1014563 : Blo 710320 1014563 := bstep (se 1 (by rfl) ⟨760922, by rfl⟩ : syracuseStep 1014563 = 1521845) B1521845
theorem B1604465 : Blo 710320 1604465 := bstep (se 2 (by rfl) ⟨601674, by rfl⟩ : syracuseStep 1604465 = 1203349) B1203349
theorem B1014643 : Blo 710320 1014643 := bstep (se 1 (by rfl) ⟨760982, by rfl⟩ : syracuseStep 1014643 = 1521965) B1521965
theorem B1604483 : Blo 710320 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B4062149 : Blo 710320 4062149 := bstep (se 4 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 4062149 = 761653) B761653
theorem B1801187 : Blo 710320 1801187 := bstep (se 1 (by rfl) ⟨1350890, by rfl⟩ : syracuseStep 1801187 = 2701781) B2701781
theorem B2259971 : Blo 710320 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B1440803 : Blo 710320 1440803 := bstep (se 1 (by rfl) ⟨1080602, by rfl⟩ : syracuseStep 1440803 = 2161205) B2161205
theorem B1604753 : Blo 710320 1604753 := bstep (se 2 (by rfl) ⟨601782, by rfl⟩ : syracuseStep 1604753 = 1203565) B1203565
theorem B1080481 : Blo 710320 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B1801379 : Blo 710320 1801379 := bstep (se 1 (by rfl) ⟨1351034, by rfl⟩ : syracuseStep 1801379 = 2702069) B2702069
theorem B1604771 : Blo 710320 1604771 := bstep (se 1 (by rfl) ⟨1203578, by rfl⟩ : syracuseStep 1604771 = 2407157) B2407157
theorem B4554053 : Blo 710320 4554053 := bstep (se 4 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 4554053 = 853885) B853885
theorem B1015201 : Blo 710320 1015201 := bstep (se 2 (by rfl) ⟨380700, by rfl⟩ : syracuseStep 1015201 = 761401) B761401
theorem B1605041 : Blo 710320 1605041 := bstep (se 2 (by rfl) ⟨601890, by rfl⟩ : syracuseStep 1605041 = 1203781) B1203781
theorem B1605059 : Blo 710320 1605059 := bstep (se 1 (by rfl) ⟨1203794, by rfl⟩ : syracuseStep 1605059 = 2407589) B2407589
theorem B1080785 : Blo 710320 1080785 := bstep (se 2 (by rfl) ⟨405294, by rfl⟩ : syracuseStep 1080785 = 810589) B810589
theorem B2031085 : Blo 710320 2031085 := bstep (se 3 (by rfl) ⟨380828, by rfl⟩ : syracuseStep 2031085 = 761657) B761657
theorem B6094349 : Blo 710320 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B1605329 : Blo 710320 1605329 := bstep (se 2 (by rfl) ⟨601998, by rfl⟩ : syracuseStep 1605329 = 1203997) B1203997
theorem B2031313 : Blo 710320 2031313 := bstep (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) B1523485
theorem B1605347 : Blo 710320 1605347 := bstep (se 1 (by rfl) ⟨1204010, by rfl⟩ : syracuseStep 1605347 = 2408021) B2408021
theorem B3604337 : Blo 710320 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B2031473 : Blo 710320 2031473 := bstep (se 2 (by rfl) ⟨761802, by rfl⟩ : syracuseStep 2031473 = 1523605) B1523605
theorem B2031587 : Blo 710320 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B1605617 : Blo 710320 1605617 := bstep (se 2 (by rfl) ⟨602106, by rfl⟩ : syracuseStep 1605617 = 1204213) B1204213
theorem B1605707 : Blo 710320 1605707 := bstep (se 1 (by rfl) ⟨1204280, by rfl⟩ : syracuseStep 1605707 = 2408561) B2408561
theorem B1605761 : Blo 710320 1605761 := bstep (se 2 (by rfl) ⟨602160, by rfl⟩ : syracuseStep 1605761 = 1204321) B1204321
theorem B1605977 : Blo 710320 1605977 := bstep (se 2 (by rfl) ⟨602241, by rfl⟩ : syracuseStep 1605977 = 1204483) B1204483
theorem B1081739 : Blo 710320 1081739 := bstep (se 1 (by rfl) ⟨811304, by rfl⟩ : syracuseStep 1081739 = 1622609) B1622609
theorem B1802675 : Blo 710320 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B1606067 : Blo 710320 1606067 := bstep (se 1 (by rfl) ⟨1204550, by rfl⟩ : syracuseStep 1606067 = 2409101) B2409101
theorem B1606103 : Blo 710320 1606103 := bstep (se 1 (by rfl) ⟨1204577, by rfl⟩ : syracuseStep 1606103 = 2409155) B2409155
theorem B10289699 : Blo 710320 10289699 := bstep (se 1 (by rfl) ⟨7717274, by rfl⟩ : syracuseStep 10289699 = 15434549) B15434549
theorem B1606283 : Blo 710320 1606283 := bstep (se 1 (by rfl) ⟨1204712, by rfl⟩ : syracuseStep 1606283 = 2409425) B2409425
theorem B1606337 : Blo 710320 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B1802969 : Blo 710320 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B1082135 : Blo 710320 1082135 := bstep (se 1 (by rfl) ⟨811601, by rfl⟩ : syracuseStep 1082135 = 1623203) B1623203
theorem B1606553 : Blo 710320 1606553 := bstep (se 2 (by rfl) ⟨602457, by rfl⟩ : syracuseStep 1606553 = 1204915) B1204915
theorem B1606643 : Blo 710320 1606643 := bstep (se 1 (by rfl) ⟨1204982, by rfl⟩ : syracuseStep 1606643 = 2409965) B2409965
theorem B1606679 : Blo 710320 1606679 := bstep (se 1 (by rfl) ⟨1205009, by rfl⟩ : syracuseStep 1606679 = 2410019) B2410019
theorem B2032715 : Blo 710320 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B1016921 : Blo 710320 1016921 := bstep (se 2 (by rfl) ⟨381345, by rfl⟩ : syracuseStep 1016921 = 762691) B762691
theorem B4064357 : Blo 710320 4064357 := bstep (se 4 (by rfl) ⟨381033, by rfl⟩ : syracuseStep 4064357 = 762067) B762067
theorem B4457651 : Blo 710320 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B1606859 : Blo 710320 1606859 := bstep (se 1 (by rfl) ⟨1205144, by rfl⟩ : syracuseStep 1606859 = 2410289) B2410289
theorem B1606913 : Blo 710320 1606913 := bstep (se 2 (by rfl) ⟨602592, by rfl⟩ : syracuseStep 1606913 = 1205185) B1205185
theorem B2033113 : Blo 710320 2033113 := bstep (se 2 (by rfl) ⟨762417, by rfl⟩ : syracuseStep 2033113 = 1524835) B1524835
theorem B1607129 : Blo 710320 1607129 := bstep (se 2 (by rfl) ⟨602673, by rfl⟩ : syracuseStep 1607129 = 1205347) B1205347
theorem B4064813 : Blo 710320 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B1607219 : Blo 710320 1607219 := bstep (se 1 (by rfl) ⟨1205414, by rfl⟩ : syracuseStep 1607219 = 2410829) B2410829
theorem B7702091 : Blo 710320 7702091 := bstep (se 1 (by rfl) ⟨5776568, by rfl⟩ : syracuseStep 7702091 = 11553137) B11553137
theorem B1083545 : Blo 710320 1083545 := bstep (se 2 (by rfl) ⟨406329, by rfl⟩ : syracuseStep 1083545 = 812659) B812659
theorem B4065497 : Blo 710320 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B1804619 : Blo 710320 1804619 := bstep (se 1 (by rfl) ⟨1353464, by rfl⟩ : syracuseStep 1804619 = 2706929) B2706929
theorem B6490469 : Blo 710320 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B1280395 : Blo 710320 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B8096273 : Blo 710320 8096273 := bstep (se 2 (by rfl) ⟨3036102, by rfl⟩ : syracuseStep 8096273 = 6072205) B6072205
theorem B4885037 : Blo 710320 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B2886209 : Blo 710320 2886209 := bstep (se 2 (by rfl) ⟨1082328, by rfl⟩ : syracuseStep 2886209 = 2164657) B2164657
theorem B723799 : Blo 710320 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B2165825 : Blo 710320 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B1805591 : Blo 710320 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B3050797 : Blo 710320 3050797 := bstep (se 3 (by rfl) ⟨572024, by rfl⟩ : syracuseStep 3050797 = 1144049) B1144049
theorem B3607901 : Blo 710320 3607901 := bstep (se 3 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 3607901 = 1352963) B1352963
theorem B20483441 : Blo 710320 20483441 := bstep (se 2 (by rfl) ⟨7681290, by rfl⟩ : syracuseStep 20483441 = 15362581) B15362581
theorem B6852113 : Blo 710320 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B6098449 : Blo 710320 6098449 := bstep (se 2 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 6098449 = 4573837) B4573837
theorem B1281779 : Blo 710320 1281779 := bstep (se 1 (by rfl) ⟨961334, by rfl⟩ : syracuseStep 1281779 = 1922669) B1922669
theorem B1543961 : Blo 710320 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B6098723 : Blo 710320 6098723 := bstep (se 1 (by rfl) ⟨4574042, by rfl⟩ : syracuseStep 6098723 = 9148085) B9148085
theorem B1806259 : Blo 710320 1806259 := bstep (se 1 (by rfl) ⟨1354694, by rfl⟩ : syracuseStep 1806259 = 2709389) B2709389
theorem B1806401 : Blo 710320 1806401 := bstep (se 2 (by rfl) ⟨677400, by rfl⟩ : syracuseStep 1806401 = 1354801) B1354801
theorem B1085783 : Blo 710320 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B17305973 : Blo 710320 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B1446283 : Blo 710320 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B1282753 : Blo 710320 1282753 := bstep (se 2 (by rfl) ⟨481032, by rfl⟩ : syracuseStep 1282753 = 962065) B962065
theorem B1282817 : Blo 710320 1282817 := bstep (se 2 (by rfl) ⟨481056, by rfl⟩ : syracuseStep 1282817 = 962113) B962113
theorem B1643275 : Blo 710320 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B1348787 : Blo 710320 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B1348825 : Blo 710320 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B13702445 : Blo 710320 13702445 := bstep (se 3 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 13702445 = 5138417) B5138417
theorem B2397491 : Blo 710320 2397491 := bstep (se 1 (by rfl) ⟨1798118, by rfl⟩ : syracuseStep 2397491 = 3596237) B3596237
theorem B1807667 : Blo 710320 1807667 := bstep (se 1 (by rfl) ⟨1355750, by rfl⟩ : syracuseStep 1807667 = 2711501) B2711501
theorem B4330853 : Blo 710320 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B8099189 : Blo 710320 8099189 := bstep (se 5 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 8099189 = 759299) B759299
theorem B3610007 : Blo 710320 3610007 := bstep (se 1 (by rfl) ⟨2707505, by rfl⟩ : syracuseStep 3610007 = 5415011) B5415011
theorem B2168257 : Blo 710320 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B2561483 : Blo 710320 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B2397761 : Blo 710320 2397761 := bstep (se 2 (by rfl) ⟨899160, by rfl⟩ : syracuseStep 2397761 = 1798321) B1798321
theorem B1349273 : Blo 710320 1349273 := bstep (se 2 (by rfl) ⟨505977, by rfl⟩ : syracuseStep 1349273 = 1011955) B1011955
theorem B4560563 : Blo 710320 4560563 := bstep (se 1 (by rfl) ⟨3420422, by rfl⟩ : syracuseStep 4560563 = 6840845) B6840845
theorem B4560715 : Blo 710320 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B17536945 : Blo 710320 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B2398301 : Blo 710320 2398301 := bstep (se 3 (by rfl) ⟨449681, by rfl⟩ : syracuseStep 2398301 = 899363) B899363
theorem B759979 : Blo 710320 759979 := bstep (se 1 (by rfl) ⟨569984, by rfl⟩ : syracuseStep 759979 = 1139969) B1139969
theorem B1284311 : Blo 710320 1284311 := bstep (se 1 (by rfl) ⟨963233, by rfl⟩ : syracuseStep 1284311 = 1926467) B1926467
theorem B5937425 : Blo 710320 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B1350017 : Blo 710320 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B1350283 : Blo 710320 1350283 := bstep (se 1 (by rfl) ⟨1012712, by rfl⟩ : syracuseStep 1350283 = 2025425) B2025425
theorem B5413553 : Blo 710320 5413553 := bstep (se 2 (by rfl) ⟨2030082, by rfl⟩ : syracuseStep 5413553 = 4060165) B4060165
theorem B2595673 : Blo 710320 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B1350731 : Blo 710320 1350731 := bstep (se 1 (by rfl) ⟨1013048, by rfl⟩ : syracuseStep 1350731 = 2026097) B2026097
theorem B5414039 : Blo 710320 5414039 := bstep (se 1 (by rfl) ⟨4060529, by rfl⟩ : syracuseStep 5414039 = 8121059) B8121059
theorem B2399435 : Blo 710320 2399435 := bstep (se 1 (by rfl) ⟨1799576, by rfl⟩ : syracuseStep 2399435 = 3599153) B3599153
theorem B1711307 : Blo 710320 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B1350913 : Blo 710320 1350913 := bstep (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) B1013185
theorem B2563501 : Blo 710320 2563501 := bstep (se 3 (by rfl) ⟨480656, by rfl⟩ : syracuseStep 2563501 = 961313) B961313
theorem B2399705 : Blo 710320 2399705 := bstep (se 2 (by rfl) ⟨899889, by rfl⟩ : syracuseStep 2399705 = 1799779) B1799779
theorem B3284525 : Blo 710320 3284525 := bstep (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) B1231697
theorem B1351255 : Blo 710320 1351255 := bstep (se 1 (by rfl) ⟨1013441, by rfl⟩ : syracuseStep 1351255 = 2026883) B2026883
theorem B1351475 : Blo 710320 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B1711961 : Blo 710320 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B2891693 : Blo 710320 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B1351703 : Blo 710320 1351703 := bstep (se 1 (by rfl) ⟨1013777, by rfl⟩ : syracuseStep 1351703 = 2027555) B2027555
theorem B761995 : Blo 710320 761995 := bstep (se 1 (by rfl) ⟨571496, by rfl⟩ : syracuseStep 761995 = 1142993) B1142993
theorem B3416215 : Blo 710320 3416215 := bstep (se 1 (by rfl) ⟨2562161, by rfl⟩ : syracuseStep 3416215 = 5124323) B5124323
theorem B2400407 : Blo 710320 2400407 := bstep (se 1 (by rfl) ⟨1800305, by rfl⟩ : syracuseStep 2400407 = 3600611) B3600611
theorem B1351961 : Blo 710320 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B1286617 : Blo 710320 1286617 := bstep (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) B964963
theorem B1712729 : Blo 710320 1712729 := bstep (se 2 (by rfl) ⟨642273, by rfl⟩ : syracuseStep 1712729 = 1284547) B1284547
theorem B2400947 : Blo 710320 2400947 := bstep (se 1 (by rfl) ⟨1800710, by rfl⟩ : syracuseStep 2400947 = 3601421) B3601421
theorem B1352371 : Blo 710320 1352371 := bstep (se 1 (by rfl) ⟨1014278, by rfl⟩ : syracuseStep 1352371 = 2028557) B2028557
theorem B1286999 : Blo 710320 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B6169445 : Blo 710320 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B3613571 : Blo 710320 3613571 := bstep (se 1 (by rfl) ⟨2710178, by rfl⟩ : syracuseStep 3613571 = 5420357) B5420357
theorem B2401217 : Blo 710320 2401217 := bstep (se 2 (by rfl) ⟨900456, by rfl⟩ : syracuseStep 2401217 = 1800913) B1800913
theorem B2892761 : Blo 710320 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B1352857 : Blo 710320 1352857 := bstep (se 2 (by rfl) ⟨507321, by rfl⟩ : syracuseStep 1352857 = 1014643) B1014643
theorem B2893121 : Blo 710320 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B2401757 : Blo 710320 2401757 := bstep (se 3 (by rfl) ⟨450329, by rfl⟩ : syracuseStep 2401757 = 900659) B900659
theorem B1353419 : Blo 710320 1353419 := bstep (se 1 (by rfl) ⟨1015064, by rfl⟩ : syracuseStep 1353419 = 2030129) B2030129
theorem B1353601 : Blo 710320 1353601 := bstep (se 2 (by rfl) ⟨507600, by rfl⟩ : syracuseStep 1353601 = 1015201) B1015201
theorem B2566039 : Blo 710320 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B2697239 : Blo 710320 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B1517591 : Blo 710320 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B960535 : Blo 710320 960535 := bstep (se 1 (by rfl) ⟨720401, by rfl⟩ : syracuseStep 960535 = 1440803) B1440803
theorem B3254417 : Blo 710320 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B1517771 : Blo 710320 1517771 := bstep (se 1 (by rfl) ⟨1138328, by rfl⟩ : syracuseStep 1517771 = 2276657) B2276657
theorem B2566673 : Blo 710320 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B2402891 : Blo 710320 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B1354315 : Blo 710320 1354315 := bstep (se 1 (by rfl) ⟨1015736, by rfl⟩ : syracuseStep 1354315 = 2031473) B2031473
theorem B1354391 : Blo 710320 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B2697907 : Blo 710320 2697907 := bstep (se 1 (by rfl) ⟨2023430, by rfl⟩ : syracuseStep 2697907 = 4046861) B4046861
theorem B961303 : Blo 710320 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B6073163 : Blo 710320 6073163 := bstep (se 1 (by rfl) ⟨4554872, by rfl⟩ : syracuseStep 6073163 = 9109745) B9109745
theorem B2403161 : Blo 710320 2403161 := bstep (se 2 (by rfl) ⟨901185, by rfl⟩ : syracuseStep 2403161 = 1802371) B1802371
theorem B27438101 : Blo 710320 27438101 := bstep (se 6 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 27438101 = 1286161) B1286161
theorem B1355059 : Blo 710320 1355059 := bstep (se 1 (by rfl) ⟨1016294, by rfl⟩ : syracuseStep 1355059 = 2032589) B2032589
theorem B2403863 : Blo 710320 2403863 := bstep (se 1 (by rfl) ⟨1802897, by rfl⟩ : syracuseStep 2403863 = 3605795) B3605795
theorem B1355287 : Blo 710320 1355287 := bstep (se 1 (by rfl) ⟨1016465, by rfl⟩ : syracuseStep 1355287 = 2032931) B2032931
theorem B1355393 : Blo 710320 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B1355545 : Blo 710320 1355545 := bstep (se 2 (by rfl) ⟨508329, by rfl⟩ : syracuseStep 1355545 = 1016659) B1016659
theorem B1519411 : Blo 710320 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B2699153 : Blo 710320 2699153 := bstep (se 2 (by rfl) ⟨1012182, by rfl⟩ : syracuseStep 2699153 = 2024365) B2024365
theorem B15446051 : Blo 710320 15446051 := bstep (se 1 (by rfl) ⟨11584538, by rfl⟩ : syracuseStep 15446051 = 23169077) B23169077
theorem B2404403 : Blo 710320 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B1519897 : Blo 710320 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B3420461 : Blo 710320 3420461 := bstep (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) B1282673
theorem B2404673 : Blo 710320 2404673 := bstep (se 2 (by rfl) ⟨901752, by rfl⟩ : syracuseStep 2404673 = 1803505) B1803505
theorem B799159 : Blo 710320 799159 := bstep (se 1 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 799159 = 1198739) B1198739
theorem B22196753 : Blo 710320 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B2699851 : Blo 710320 2699851 := bstep (se 1 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 2699851 = 4049777) B4049777
theorem B799339 : Blo 710320 799339 := bstep (se 1 (by rfl) ⟨599504, by rfl⟩ : syracuseStep 799339 = 1199009) B1199009
theorem B5780173 : Blo 710320 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B799447 : Blo 710320 799447 := bstep (se 1 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 799447 = 1199171) B1199171
theorem B2700125 : Blo 710320 2700125 := bstep (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) B1012547
theorem B2405213 : Blo 710320 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B799627 : Blo 710320 799627 := bstep (se 1 (by rfl) ⟨599720, by rfl⟩ : syracuseStep 799627 = 1199441) B1199441
theorem B799735 : Blo 710320 799735 := bstep (se 1 (by rfl) ⟨599801, by rfl⟩ : syracuseStep 799735 = 1199603) B1199603
theorem B799915 : Blo 710320 799915 := bstep (se 1 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 799915 = 1199873) B1199873
theorem B800023 : Blo 710320 800023 := bstep (se 1 (by rfl) ⟨600017, by rfl⟩ : syracuseStep 800023 = 1200035) B1200035
theorem B2438579 : Blo 710320 2438579 := bstep (se 1 (by rfl) ⟨1828934, by rfl⟩ : syracuseStep 2438579 = 3657869) B3657869
theorem B6862259 : Blo 710320 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B800203 : Blo 710320 800203 := bstep (se 1 (by rfl) ⟨600152, by rfl⟩ : syracuseStep 800203 = 1200305) B1200305
theorem B2700823 : Blo 710320 2700823 := bstep (se 1 (by rfl) ⟨2025617, by rfl⟩ : syracuseStep 2700823 = 4051235) B4051235
theorem B800311 : Blo 710320 800311 := bstep (se 1 (by rfl) ⟨600233, by rfl⟩ : syracuseStep 800311 = 1200467) B1200467
theorem B1521281 : Blo 710320 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B2569931 : Blo 710320 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B800491 : Blo 710320 800491 := bstep (se 1 (by rfl) ⟨600368, by rfl⟩ : syracuseStep 800491 = 1200737) B1200737
theorem B5125963 : Blo 710320 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B800599 : Blo 710320 800599 := bstep (se 1 (by rfl) ⟨600449, by rfl⟩ : syracuseStep 800599 = 1200899) B1200899
theorem B2406347 : Blo 710320 2406347 := bstep (se 1 (by rfl) ⟨1804760, by rfl⟩ : syracuseStep 2406347 = 3609521) B3609521
theorem B800779 : Blo 710320 800779 := bstep (se 1 (by rfl) ⟨600584, by rfl⟩ : syracuseStep 800779 = 1201169) B1201169
theorem B899095 : Blo 710320 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B800887 : Blo 710320 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B3848323 : Blo 710320 3848323 := bstep (se 1 (by rfl) ⟨2886242, by rfl⟩ : syracuseStep 3848323 = 5772485) B5772485
theorem B1521803 : Blo 710320 1521803 := bstep (se 1 (by rfl) ⟨1141352, by rfl⟩ : syracuseStep 1521803 = 2282705) B2282705
theorem B2406617 : Blo 710320 2406617 := bstep (se 2 (by rfl) ⟨902481, by rfl⟩ : syracuseStep 2406617 = 1804963) B1804963
theorem B5421329 : Blo 710320 5421329 := bstep (se 2 (by rfl) ⟨2032998, by rfl⟩ : syracuseStep 5421329 = 4065997) B4065997
theorem B801067 : Blo 710320 801067 := bstep (se 1 (by rfl) ⟨600800, by rfl⟩ : syracuseStep 801067 = 1201601) B1201601
theorem B2701613 : Blo 710320 2701613 := bstep (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) B1013105
theorem B801175 : Blo 710320 801175 := bstep (se 1 (by rfl) ⟨600881, by rfl⟩ : syracuseStep 801175 = 1201763) B1201763
theorem B12368305 : Blo 710320 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B10271245 : Blo 710320 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B801355 : Blo 710320 801355 := bstep (se 1 (by rfl) ⟨601016, by rfl⟩ : syracuseStep 801355 = 1202033) B1202033
theorem B801463 : Blo 710320 801463 := bstep (se 1 (by rfl) ⟨601097, by rfl⟩ : syracuseStep 801463 = 1202195) B1202195
theorem B4045585 : Blo 710320 4045585 := bstep (se 2 (by rfl) ⟨1517094, by rfl⟩ : syracuseStep 4045585 = 3034189) B3034189
theorem B801643 : Blo 710320 801643 := bstep (se 1 (by rfl) ⟨601232, by rfl⟩ : syracuseStep 801643 = 1202465) B1202465
theorem B2407319 : Blo 710320 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B801751 : Blo 710320 801751 := bstep (se 1 (by rfl) ⟨601313, by rfl⟩ : syracuseStep 801751 = 1202627) B1202627
theorem B1621003 : Blo 710320 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B3292211 : Blo 710320 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B801931 : Blo 710320 801931 := bstep (se 1 (by rfl) ⟨601448, by rfl⟩ : syracuseStep 801931 = 1202897) B1202897
theorem B802039 : Blo 710320 802039 := bstep (se 1 (by rfl) ⟨601529, by rfl⟩ : syracuseStep 802039 = 1203059) B1203059
theorem B1523033 : Blo 710320 1523033 := bstep (se 2 (by rfl) ⟨571137, by rfl⟩ : syracuseStep 1523033 = 1142275) B1142275
theorem B802219 : Blo 710320 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B2407859 : Blo 710320 2407859 := bstep (se 1 (by rfl) ⟨1805894, by rfl⟩ : syracuseStep 2407859 = 3611789) B3611789
theorem B802327 : Blo 710320 802327 := bstep (se 1 (by rfl) ⟨601745, by rfl⟩ : syracuseStep 802327 = 1203491) B1203491
theorem B1392257 : Blo 710320 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B2703041 : Blo 710320 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B2408129 : Blo 710320 2408129 := bstep (se 2 (by rfl) ⟨903048, by rfl⟩ : syracuseStep 2408129 = 1806097) B1806097
theorem B802507 : Blo 710320 802507 := bstep (se 1 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 802507 = 1203761) B1203761
theorem B900811 : Blo 710320 900811 := bstep (se 1 (by rfl) ⟨675608, by rfl⟩ : syracuseStep 900811 = 1351217) B1351217
theorem B1523443 : Blo 710320 1523443 := bstep (se 1 (by rfl) ⟨1142582, by rfl⟩ : syracuseStep 1523443 = 2285165) B2285165
theorem B2309939 : Blo 710320 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B802615 : Blo 710320 802615 := bstep (se 1 (by rfl) ⟨601961, by rfl⟩ : syracuseStep 802615 = 1203923) B1203923
theorem B5128037 : Blo 710320 5128037 := bstep (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) B961507
theorem B802795 : Blo 710320 802795 := bstep (se 1 (by rfl) ⟨602096, by rfl⟩ : syracuseStep 802795 = 1204193) B1204193
theorem B802903 : Blo 710320 802903 := bstep (se 1 (by rfl) ⟨602177, by rfl⟩ : syracuseStep 802903 = 1204355) B1204355
theorem B8667287 : Blo 710320 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B1523929 : Blo 710320 1523929 := bstep (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) B1142947
theorem B2408669 : Blo 710320 2408669 := bstep (se 3 (by rfl) ⟨451625, by rfl⟩ : syracuseStep 2408669 = 903251) B903251
theorem B803083 : Blo 710320 803083 := bstep (se 1 (by rfl) ⟨602312, by rfl⟩ : syracuseStep 803083 = 1204625) B1204625
theorem B803191 : Blo 710320 803191 := bstep (se 1 (by rfl) ⟨602393, by rfl⟩ : syracuseStep 803191 = 1204787) B1204787
theorem B2638253 : Blo 710320 2638253 := bstep (se 3 (by rfl) ⟨494672, by rfl⟩ : syracuseStep 2638253 = 989345) B989345
theorem B1065497 : Blo 710320 1065497 := bstep (se 2 (by rfl) ⟨399561, by rfl⟩ : syracuseStep 1065497 = 799123) B799123
theorem B803371 : Blo 710320 803371 := bstep (se 1 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 803371 = 1205057) B1205057
theorem B1065611 : Blo 710320 1065611 := bstep (se 1 (by rfl) ⟨799208, by rfl⟩ : syracuseStep 1065611 = 1598417) B1598417
theorem B1065623 : Blo 710320 1065623 := bstep (se 1 (by rfl) ⟨799217, by rfl⟩ : syracuseStep 1065623 = 1598435) B1598435
theorem B901783 : Blo 710320 901783 := bstep (se 1 (by rfl) ⟨676337, by rfl⟩ : syracuseStep 901783 = 1352675) B1352675
theorem B803479 : Blo 710320 803479 := bstep (se 1 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 803479 = 1205219) B1205219
theorem B1065689 : Blo 710320 1065689 := bstep (se 2 (by rfl) ⟨399633, by rfl⟩ : syracuseStep 1065689 = 799267) B799267
theorem B8110853 : Blo 710320 8110853 := bstep (se 4 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 8110853 = 1520785) B1520785
theorem B1065803 : Blo 710320 1065803 := bstep (se 1 (by rfl) ⟨799352, by rfl⟩ : syracuseStep 1065803 = 1598705) B1598705
theorem B1065815 : Blo 710320 1065815 := bstep (se 1 (by rfl) ⟨799361, by rfl⟩ : syracuseStep 1065815 = 1598723) B1598723
theorem B1065881 : Blo 710320 1065881 := bstep (se 2 (by rfl) ⟨399705, by rfl⟩ : syracuseStep 1065881 = 799411) B799411
theorem B8111027 : Blo 710320 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B1524673 : Blo 710320 1524673 := bstep (se 2 (by rfl) ⟨571752, by rfl⟩ : syracuseStep 1524673 = 1143505) B1143505
theorem B1065995 : Blo 710320 1065995 := bstep (se 1 (by rfl) ⟨799496, by rfl⟩ : syracuseStep 1065995 = 1598993) B1598993
theorem B1066007 : Blo 710320 1066007 := bstep (se 1 (by rfl) ⟨799505, by rfl⟩ : syracuseStep 1066007 = 1599011) B1599011
theorem B1066073 : Blo 710320 1066073 := bstep (se 2 (by rfl) ⟨399777, by rfl⟩ : syracuseStep 1066073 = 799555) B799555
theorem B2704529 : Blo 710320 2704529 := bstep (se 2 (by rfl) ⟨1014198, by rfl⟩ : syracuseStep 2704529 = 2028397) B2028397
theorem B1066187 : Blo 710320 1066187 := bstep (se 1 (by rfl) ⟨799640, by rfl⟩ : syracuseStep 1066187 = 1599281) B1599281
theorem B1066199 : Blo 710320 1066199 := bstep (se 1 (by rfl) ⟨799649, by rfl⟩ : syracuseStep 1066199 = 1599299) B1599299
theorem B1066265 : Blo 710320 1066265 := bstep (se 2 (by rfl) ⟨399849, by rfl⟩ : syracuseStep 1066265 = 799699) B799699
theorem B2409803 : Blo 710320 2409803 := bstep (se 1 (by rfl) ⟨1807352, by rfl⟩ : syracuseStep 2409803 = 3614705) B3614705
theorem B1066379 : Blo 710320 1066379 := bstep (se 1 (by rfl) ⟨799784, by rfl⟩ : syracuseStep 1066379 = 1599569) B1599569
theorem B1066391 : Blo 710320 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B902603 : Blo 710320 902603 := bstep (se 1 (by rfl) ⟨676952, by rfl⟩ : syracuseStep 902603 = 1353905) B1353905
theorem B1066457 : Blo 710320 1066457 := bstep (se 2 (by rfl) ⟨399921, by rfl⟩ : syracuseStep 1066457 = 799843) B799843
theorem B1066571 : Blo 710320 1066571 := bstep (se 1 (by rfl) ⟨799928, by rfl⟩ : syracuseStep 1066571 = 1599857) B1599857
theorem B5490251 : Blo 710320 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B1066583 : Blo 710320 1066583 := bstep (se 1 (by rfl) ⟨799937, by rfl⟩ : syracuseStep 1066583 = 1599875) B1599875
theorem B2704985 : Blo 710320 2704985 := bstep (se 2 (by rfl) ⟨1014369, by rfl⟩ : syracuseStep 2704985 = 2028739) B2028739
theorem B2410073 : Blo 710320 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B1066649 : Blo 710320 1066649 := bstep (se 2 (by rfl) ⟨399993, by rfl⟩ : syracuseStep 1066649 = 799987) B799987
theorem B1066763 : Blo 710320 1066763 := bstep (se 1 (by rfl) ⟨800072, by rfl⟩ : syracuseStep 1066763 = 1600145) B1600145
theorem B1066775 : Blo 710320 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B3655469 : Blo 710320 3655469 := bstep (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) B1370801
theorem B2705197 : Blo 710320 2705197 := bstep (se 3 (by rfl) ⟨507224, by rfl⟩ : syracuseStep 2705197 = 1014449) B1014449
theorem B1066841 : Blo 710320 1066841 := bstep (se 2 (by rfl) ⟨400065, by rfl⟩ : syracuseStep 1066841 = 800131) B800131
theorem B13846373 : Blo 710320 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B1066955 : Blo 710320 1066955 := bstep (se 1 (by rfl) ⟨800216, by rfl⟩ : syracuseStep 1066955 = 1600433) B1600433
theorem B1066967 : Blo 710320 1066967 := bstep (se 1 (by rfl) ⟨800225, by rfl⟩ : syracuseStep 1066967 = 1600451) B1600451
theorem B1067033 : Blo 710320 1067033 := bstep (se 2 (by rfl) ⟨400137, by rfl⟩ : syracuseStep 1067033 = 800275) B800275
theorem B2705501 : Blo 710320 2705501 := bstep (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) B1014563
theorem B4049027 : Blo 710320 4049027 := bstep (se 1 (by rfl) ⟨3036770, by rfl⟩ : syracuseStep 4049027 = 6073541) B6073541
theorem B6834307 : Blo 710320 6834307 := bstep (se 1 (by rfl) ⟨5125730, by rfl⟩ : syracuseStep 6834307 = 10251461) B10251461
theorem B1067147 : Blo 710320 1067147 := bstep (se 1 (by rfl) ⟨800360, by rfl⟩ : syracuseStep 1067147 = 1600721) B1600721
theorem B903307 : Blo 710320 903307 := bstep (se 1 (by rfl) ⟨677480, by rfl⟩ : syracuseStep 903307 = 1354961) B1354961
theorem B1067159 : Blo 710320 1067159 := bstep (se 1 (by rfl) ⟨800369, by rfl⟩ : syracuseStep 1067159 = 1600739) B1600739
theorem B1067225 : Blo 710320 1067225 := bstep (se 2 (by rfl) ⟨400209, by rfl⟩ : syracuseStep 1067225 = 800419) B800419
theorem B2410775 : Blo 710320 2410775 := bstep (se 1 (by rfl) ⟨1808081, by rfl⟩ : syracuseStep 2410775 = 3616163) B3616163
theorem B1067339 : Blo 710320 1067339 := bstep (se 1 (by rfl) ⟨800504, by rfl⟩ : syracuseStep 1067339 = 1601009) B1601009
theorem B1067351 : Blo 710320 1067351 := bstep (se 1 (by rfl) ⟨800513, by rfl⟩ : syracuseStep 1067351 = 1601027) B1601027
theorem B903575 : Blo 710320 903575 := bstep (se 1 (by rfl) ⟨677681, by rfl⟩ : syracuseStep 903575 = 1355363) B1355363
theorem B1067417 : Blo 710320 1067417 := bstep (se 2 (by rfl) ⟨400281, by rfl⟩ : syracuseStep 1067417 = 800563) B800563
theorem B2279897 : Blo 710320 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B1067531 : Blo 710320 1067531 := bstep (se 1 (by rfl) ⟨800648, by rfl⟩ : syracuseStep 1067531 = 1601297) B1601297
theorem B1067543 : Blo 710320 1067543 := bstep (se 1 (by rfl) ⟨800657, by rfl⟩ : syracuseStep 1067543 = 1601315) B1601315
theorem B1067609 : Blo 710320 1067609 := bstep (se 2 (by rfl) ⟨400353, by rfl⟩ : syracuseStep 1067609 = 800707) B800707
theorem B3426995 : Blo 710320 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B1067723 : Blo 710320 1067723 := bstep (se 1 (by rfl) ⟨800792, by rfl⟩ : syracuseStep 1067723 = 1601585) B1601585
theorem B1067735 : Blo 710320 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B1067801 : Blo 710320 1067801 := bstep (se 2 (by rfl) ⟨400425, by rfl⟩ : syracuseStep 1067801 = 800851) B800851
theorem B1067915 : Blo 710320 1067915 := bstep (se 1 (by rfl) ⟨800936, by rfl⟩ : syracuseStep 1067915 = 1601873) B1601873
theorem B1067927 : Blo 710320 1067927 := bstep (se 1 (by rfl) ⟨800945, by rfl⟩ : syracuseStep 1067927 = 1601891) B1601891
theorem B1199063 : Blo 710320 1199063 := bstep (se 1 (by rfl) ⟨899297, by rfl⟩ : syracuseStep 1199063 = 1798595) B1798595
theorem B1067993 : Blo 710320 1067993 := bstep (se 2 (by rfl) ⟨400497, by rfl⟩ : syracuseStep 1067993 = 800995) B800995
theorem B3296321 : Blo 710320 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B1068107 : Blo 710320 1068107 := bstep (se 1 (by rfl) ⟨801080, by rfl⟩ : syracuseStep 1068107 = 1602161) B1602161
theorem B1199191 : Blo 710320 1199191 := bstep (se 1 (by rfl) ⟨899393, by rfl⟩ : syracuseStep 1199191 = 1798787) B1798787
theorem B1068119 : Blo 710320 1068119 := bstep (se 1 (by rfl) ⟨801089, by rfl⟩ : syracuseStep 1068119 = 1602179) B1602179
theorem B1068185 : Blo 710320 1068185 := bstep (se 2 (by rfl) ⟨400569, by rfl⟩ : syracuseStep 1068185 = 801139) B801139
theorem B1068299 : Blo 710320 1068299 := bstep (se 1 (by rfl) ⟨801224, by rfl⟩ : syracuseStep 1068299 = 1602449) B1602449
theorem B1068311 : Blo 710320 1068311 := bstep (se 1 (by rfl) ⟨801233, by rfl⟩ : syracuseStep 1068311 = 1602467) B1602467
theorem B1068377 : Blo 710320 1068377 := bstep (se 2 (by rfl) ⟨400641, by rfl⟩ : syracuseStep 1068377 = 801283) B801283
theorem B5131613 : Blo 710320 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B6180275 : Blo 710320 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B1068491 : Blo 710320 1068491 := bstep (se 1 (by rfl) ⟨801368, by rfl⟩ : syracuseStep 1068491 = 1602737) B1602737
theorem B1068503 : Blo 710320 1068503 := bstep (se 1 (by rfl) ⟨801377, by rfl⟩ : syracuseStep 1068503 = 1602755) B1602755
theorem B1068569 : Blo 710320 1068569 := bstep (se 2 (by rfl) ⟨400713, by rfl⟩ : syracuseStep 1068569 = 801427) B801427
theorem B22171229 : Blo 710320 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B1068683 : Blo 710320 1068683 := bstep (se 1 (by rfl) ⟨801512, by rfl⟩ : syracuseStep 1068683 = 1603025) B1603025
theorem B1068695 : Blo 710320 1068695 := bstep (se 1 (by rfl) ⟨801521, by rfl⟩ : syracuseStep 1068695 = 1603043) B1603043
theorem B1199819 : Blo 710320 1199819 := bstep (se 1 (by rfl) ⟨899864, by rfl⟩ : syracuseStep 1199819 = 1799729) B1799729
theorem B1068761 : Blo 710320 1068761 := bstep (se 2 (by rfl) ⟨400785, by rfl⟩ : syracuseStep 1068761 = 801571) B801571
theorem B1199947 : Blo 710320 1199947 := bstep (se 1 (by rfl) ⟨899960, by rfl⟩ : syracuseStep 1199947 = 1799921) B1799921
theorem B1068875 : Blo 710320 1068875 := bstep (se 1 (by rfl) ⟨801656, by rfl⟩ : syracuseStep 1068875 = 1603313) B1603313
theorem B1068887 : Blo 710320 1068887 := bstep (se 1 (by rfl) ⟨801665, by rfl⟩ : syracuseStep 1068887 = 1603331) B1603331
theorem B1068953 : Blo 710320 1068953 := bstep (se 2 (by rfl) ⟨400857, by rfl⟩ : syracuseStep 1068953 = 801715) B801715
theorem B1200089 : Blo 710320 1200089 := bstep (se 2 (by rfl) ⟨450033, by rfl⟩ : syracuseStep 1200089 = 900067) B900067
theorem B1069067 : Blo 710320 1069067 := bstep (se 1 (by rfl) ⟨801800, by rfl⟩ : syracuseStep 1069067 = 1603601) B1603601
theorem B1069079 : Blo 710320 1069079 := bstep (se 1 (by rfl) ⟨801809, by rfl⟩ : syracuseStep 1069079 = 1603619) B1603619
theorem B2281537 : Blo 710320 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B1200217 : Blo 710320 1200217 := bstep (se 2 (by rfl) ⟨450081, by rfl⟩ : syracuseStep 1200217 = 900163) B900163
theorem B1069145 : Blo 710320 1069145 := bstep (se 2 (by rfl) ⟨400929, by rfl⟩ : syracuseStep 1069145 = 801859) B801859
theorem B4575325 : Blo 710320 4575325 := bstep (se 3 (by rfl) ⟨857873, by rfl⟩ : syracuseStep 4575325 = 1715747) B1715747
theorem B1069259 : Blo 710320 1069259 := bstep (se 1 (by rfl) ⟨801944, by rfl⟩ : syracuseStep 1069259 = 1603889) B1603889
theorem B1069271 : Blo 710320 1069271 := bstep (se 1 (by rfl) ⟨801953, by rfl⟩ : syracuseStep 1069271 = 1603907) B1603907
theorem B1069337 : Blo 710320 1069337 := bstep (se 2 (by rfl) ⟨401001, by rfl⟩ : syracuseStep 1069337 = 802003) B802003
theorem B1069451 : Blo 710320 1069451 := bstep (se 1 (by rfl) ⟨802088, by rfl⟩ : syracuseStep 1069451 = 1604177) B1604177
theorem B1069463 : Blo 710320 1069463 := bstep (se 1 (by rfl) ⟨802097, by rfl⟩ : syracuseStep 1069463 = 1604195) B1604195
theorem B4051417 : Blo 710320 4051417 := bstep (se 2 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 4051417 = 3038563) B3038563
theorem B1069529 : Blo 710320 1069529 := bstep (se 2 (by rfl) ⟨401073, by rfl⟩ : syracuseStep 1069529 = 802147) B802147
theorem B3035693 : Blo 710320 3035693 := bstep (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) B1138385
theorem B1069643 : Blo 710320 1069643 := bstep (se 1 (by rfl) ⟨802232, by rfl⟩ : syracuseStep 1069643 = 1604465) B1604465
theorem B1069655 : Blo 710320 1069655 := bstep (se 1 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 1069655 = 1604483) B1604483
theorem B2708099 : Blo 710320 2708099 := bstep (se 1 (by rfl) ⟨2031074, by rfl⟩ : syracuseStep 2708099 = 4062149) B4062149
theorem B2708113 : Blo 710320 2708113 := bstep (se 2 (by rfl) ⟨1015542, by rfl⟩ : syracuseStep 2708113 = 2031085) B2031085
theorem B1200791 : Blo 710320 1200791 := bstep (se 1 (by rfl) ⟨900593, by rfl⟩ : syracuseStep 1200791 = 1801187) B1801187
theorem B1069721 : Blo 710320 1069721 := bstep (se 2 (by rfl) ⟨401145, by rfl⟩ : syracuseStep 1069721 = 802291) B802291
theorem B1069835 : Blo 710320 1069835 := bstep (se 1 (by rfl) ⟨802376, by rfl⟩ : syracuseStep 1069835 = 1604753) B1604753
theorem B1200919 : Blo 710320 1200919 := bstep (se 1 (by rfl) ⟨900689, by rfl⟩ : syracuseStep 1200919 = 1801379) B1801379
theorem B1069847 : Blo 710320 1069847 := bstep (se 1 (by rfl) ⟨802385, by rfl⟩ : syracuseStep 1069847 = 1604771) B1604771
theorem B1069913 : Blo 710320 1069913 := bstep (se 2 (by rfl) ⟨401217, by rfl⟩ : syracuseStep 1069913 = 802435) B802435
theorem B3036035 : Blo 710320 3036035 := bstep (se 1 (by rfl) ⟨2277026, by rfl⟩ : syracuseStep 3036035 = 4554053) B4554053
theorem B2708417 : Blo 710320 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B1070027 : Blo 710320 1070027 := bstep (se 1 (by rfl) ⟨802520, by rfl⟩ : syracuseStep 1070027 = 1605041) B1605041
theorem B1070039 : Blo 710320 1070039 := bstep (se 1 (by rfl) ⟨802529, by rfl⟩ : syracuseStep 1070039 = 1605059) B1605059
theorem B51958745 : Blo 710320 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B1070105 : Blo 710320 1070105 := bstep (se 2 (by rfl) ⟨401289, by rfl⟩ : syracuseStep 1070105 = 802579) B802579
theorem B1070219 : Blo 710320 1070219 := bstep (se 1 (by rfl) ⟨802664, by rfl⟩ : syracuseStep 1070219 = 1605329) B1605329
theorem B1070231 : Blo 710320 1070231 := bstep (se 1 (by rfl) ⟨802673, by rfl⟩ : syracuseStep 1070231 = 1605347) B1605347
theorem B1070297 : Blo 710320 1070297 := bstep (se 2 (by rfl) ⟨401361, by rfl⟩ : syracuseStep 1070297 = 802723) B802723
theorem B1070411 : Blo 710320 1070411 := bstep (se 1 (by rfl) ⟨802808, by rfl⟩ : syracuseStep 1070411 = 1605617) B1605617
theorem B1070423 : Blo 710320 1070423 := bstep (se 1 (by rfl) ⟨802817, by rfl⟩ : syracuseStep 1070423 = 1605635) B1605635
theorem B1201547 : Blo 710320 1201547 := bstep (se 1 (by rfl) ⟨901160, by rfl⟩ : syracuseStep 1201547 = 1802321) B1802321
theorem B4052375 : Blo 710320 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B1070489 : Blo 710320 1070489 := bstep (se 2 (by rfl) ⟨401433, by rfl⟩ : syracuseStep 1070489 = 802867) B802867
theorem B1201675 : Blo 710320 1201675 := bstep (se 1 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 1201675 = 1802513) B1802513
theorem B1070603 : Blo 710320 1070603 := bstep (se 1 (by rfl) ⟨802952, by rfl⟩ : syracuseStep 1070603 = 1605905) B1605905
theorem B12998161 : Blo 710320 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B1070615 : Blo 710320 1070615 := bstep (se 1 (by rfl) ⟨802961, by rfl⟩ : syracuseStep 1070615 = 1605923) B1605923
theorem B1070681 : Blo 710320 1070681 := bstep (se 2 (by rfl) ⟨401505, by rfl⟩ : syracuseStep 1070681 = 803011) B803011
theorem B2709085 : Blo 710320 2709085 := bstep (se 3 (by rfl) ⟨507953, by rfl⟩ : syracuseStep 2709085 = 1015907) B1015907
theorem B1201817 : Blo 710320 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B710327 : Blo 710320 710327 := bstep (se 1 (by rfl) ⟨532745, by rfl⟩ : syracuseStep 710327 = 1065491) B1065491
theorem B710347 : Blo 710320 710347 := bstep (se 1 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 710347 = 1065521) B1065521
theorem B1070795 : Blo 710320 1070795 := bstep (se 1 (by rfl) ⟨803096, by rfl⟩ : syracuseStep 1070795 = 1606193) B1606193
theorem B710359 : Blo 710320 710359 := bstep (se 1 (by rfl) ⟨532769, by rfl⟩ : syracuseStep 710359 = 1065539) B1065539
theorem B1070807 : Blo 710320 1070807 := bstep (se 1 (by rfl) ⟨803105, by rfl⟩ : syracuseStep 1070807 = 1606211) B1606211
theorem B710379 : Blo 710320 710379 := bstep (se 1 (by rfl) ⟨532784, by rfl⟩ : syracuseStep 710379 = 1065569) B1065569
theorem B710391 : Blo 710320 710391 := bstep (se 1 (by rfl) ⟨532793, by rfl⟩ : syracuseStep 710391 = 1065587) B1065587
theorem B710411 : Blo 710320 710411 := bstep (se 1 (by rfl) ⟨532808, by rfl⟩ : syracuseStep 710411 = 1065617) B1065617
theorem B710423 : Blo 710320 710423 := bstep (se 1 (by rfl) ⟨532817, by rfl⟩ : syracuseStep 710423 = 1065635) B1065635
theorem B1201945 : Blo 710320 1201945 := bstep (se 2 (by rfl) ⟨450729, by rfl⟩ : syracuseStep 1201945 = 901459) B901459
theorem B1070873 : Blo 710320 1070873 := bstep (se 2 (by rfl) ⟨401577, by rfl⟩ : syracuseStep 1070873 = 803155) B803155
theorem B710443 : Blo 710320 710443 := bstep (se 1 (by rfl) ⟨532832, by rfl⟩ : syracuseStep 710443 = 1065665) B1065665
theorem B710455 : Blo 710320 710455 := bstep (se 1 (by rfl) ⟨532841, by rfl⟩ : syracuseStep 710455 = 1065683) B1065683
theorem B710475 : Blo 710320 710475 := bstep (se 1 (by rfl) ⟨532856, by rfl⟩ : syracuseStep 710475 = 1065713) B1065713
theorem B710487 : Blo 710320 710487 := bstep (se 1 (by rfl) ⟨532865, by rfl⟩ : syracuseStep 710487 = 1065731) B1065731
theorem B710507 : Blo 710320 710507 := bstep (se 1 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 710507 = 1065761) B1065761
theorem B743275 : Blo 710320 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B710519 : Blo 710320 710519 := bstep (se 1 (by rfl) ⟨532889, by rfl⟩ : syracuseStep 710519 = 1065779) B1065779
theorem B710539 : Blo 710320 710539 := bstep (se 1 (by rfl) ⟨532904, by rfl⟩ : syracuseStep 710539 = 1065809) B1065809
theorem B1070987 : Blo 710320 1070987 := bstep (se 1 (by rfl) ⟨803240, by rfl⟩ : syracuseStep 1070987 = 1606481) B1606481
theorem B710551 : Blo 710320 710551 := bstep (se 1 (by rfl) ⟨532913, by rfl⟩ : syracuseStep 710551 = 1065827) B1065827
theorem B1070999 : Blo 710320 1070999 := bstep (se 1 (by rfl) ⟨803249, by rfl⟩ : syracuseStep 1070999 = 1606499) B1606499
theorem B710571 : Blo 710320 710571 := bstep (se 1 (by rfl) ⟨532928, by rfl⟩ : syracuseStep 710571 = 1065857) B1065857
theorem B710583 : Blo 710320 710583 := bstep (se 1 (by rfl) ⟨532937, by rfl⟩ : syracuseStep 710583 = 1065875) B1065875
theorem B710603 : Blo 710320 710603 := bstep (se 1 (by rfl) ⟨532952, by rfl⟩ : syracuseStep 710603 = 1065905) B1065905
theorem B710615 : Blo 710320 710615 := bstep (se 1 (by rfl) ⟨532961, by rfl⟩ : syracuseStep 710615 = 1065923) B1065923
theorem B1071065 : Blo 710320 1071065 := bstep (se 2 (by rfl) ⟨401649, by rfl⟩ : syracuseStep 1071065 = 803299) B803299
theorem B710635 : Blo 710320 710635 := bstep (se 1 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 710635 = 1065953) B1065953
theorem B710647 : Blo 710320 710647 := bstep (se 1 (by rfl) ⟨532985, by rfl⟩ : syracuseStep 710647 = 1065971) B1065971
theorem B710667 : Blo 710320 710667 := bstep (se 1 (by rfl) ⟨533000, by rfl⟩ : syracuseStep 710667 = 1066001) B1066001
theorem B710679 : Blo 710320 710679 := bstep (se 1 (by rfl) ⟨533009, by rfl⟩ : syracuseStep 710679 = 1066019) B1066019
theorem B710699 : Blo 710320 710699 := bstep (se 1 (by rfl) ⟨533024, by rfl⟩ : syracuseStep 710699 = 1066049) B1066049
theorem B710711 : Blo 710320 710711 := bstep (se 1 (by rfl) ⟨533033, by rfl⟩ : syracuseStep 710711 = 1066067) B1066067
theorem B710731 : Blo 710320 710731 := bstep (se 1 (by rfl) ⟨533048, by rfl⟩ : syracuseStep 710731 = 1066097) B1066097
theorem B1071179 : Blo 710320 1071179 := bstep (se 1 (by rfl) ⟨803384, by rfl⟩ : syracuseStep 1071179 = 1606769) B1606769
theorem B710743 : Blo 710320 710743 := bstep (se 1 (by rfl) ⟨533057, by rfl⟩ : syracuseStep 710743 = 1066115) B1066115
theorem B1071191 : Blo 710320 1071191 := bstep (se 1 (by rfl) ⟨803393, by rfl⟩ : syracuseStep 1071191 = 1606787) B1606787
theorem B710763 : Blo 710320 710763 := bstep (se 1 (by rfl) ⟨533072, by rfl⟩ : syracuseStep 710763 = 1066145) B1066145
theorem B710775 : Blo 710320 710775 := bstep (se 1 (by rfl) ⟨533081, by rfl⟩ : syracuseStep 710775 = 1066163) B1066163
theorem B710795 : Blo 710320 710795 := bstep (se 1 (by rfl) ⟨533096, by rfl⟩ : syracuseStep 710795 = 1066193) B1066193
theorem B710807 : Blo 710320 710807 := bstep (se 1 (by rfl) ⟨533105, by rfl⟩ : syracuseStep 710807 = 1066211) B1066211
theorem B1071257 : Blo 710320 1071257 := bstep (se 2 (by rfl) ⟨401721, by rfl⟩ : syracuseStep 1071257 = 803443) B803443
theorem B710827 : Blo 710320 710827 := bstep (se 1 (by rfl) ⟨533120, by rfl⟩ : syracuseStep 710827 = 1066241) B1066241
theorem B710839 : Blo 710320 710839 := bstep (se 1 (by rfl) ⟨533129, by rfl⟩ : syracuseStep 710839 = 1066259) B1066259
theorem B710859 : Blo 710320 710859 := bstep (se 1 (by rfl) ⟨533144, by rfl⟩ : syracuseStep 710859 = 1066289) B1066289
theorem B710871 : Blo 710320 710871 := bstep (se 1 (by rfl) ⟨533153, by rfl⟩ : syracuseStep 710871 = 1066307) B1066307
theorem B710891 : Blo 710320 710891 := bstep (se 1 (by rfl) ⟨533168, by rfl⟩ : syracuseStep 710891 = 1066337) B1066337
theorem B710903 : Blo 710320 710903 := bstep (se 1 (by rfl) ⟨533177, by rfl⟩ : syracuseStep 710903 = 1066355) B1066355
theorem B710923 : Blo 710320 710923 := bstep (se 1 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 710923 = 1066385) B1066385
theorem B1071371 : Blo 710320 1071371 := bstep (se 1 (by rfl) ⟨803528, by rfl⟩ : syracuseStep 1071371 = 1607057) B1607057
theorem B710935 : Blo 710320 710935 := bstep (se 1 (by rfl) ⟨533201, by rfl⟩ : syracuseStep 710935 = 1066403) B1066403
theorem B1071383 : Blo 710320 1071383 := bstep (se 1 (by rfl) ⟨803537, by rfl⟩ : syracuseStep 1071383 = 1607075) B1607075
theorem B710955 : Blo 710320 710955 := bstep (se 1 (by rfl) ⟨533216, by rfl⟩ : syracuseStep 710955 = 1066433) B1066433
theorem B13031725 : Blo 710320 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B1300787 : Blo 710320 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B710967 : Blo 710320 710967 := bstep (se 1 (by rfl) ⟨533225, by rfl⟩ : syracuseStep 710967 = 1066451) B1066451
theorem B710987 : Blo 710320 710987 := bstep (se 1 (by rfl) ⟨533240, by rfl⟩ : syracuseStep 710987 = 1066481) B1066481
theorem B710999 : Blo 710320 710999 := bstep (se 1 (by rfl) ⟨533249, by rfl⟩ : syracuseStep 710999 = 1066499) B1066499
theorem B1202519 : Blo 710320 1202519 := bstep (se 1 (by rfl) ⟨901889, by rfl⟩ : syracuseStep 1202519 = 1803779) B1803779
theorem B1071449 : Blo 710320 1071449 := bstep (se 2 (by rfl) ⟨401793, by rfl⟩ : syracuseStep 1071449 = 803587) B803587
theorem B711019 : Blo 710320 711019 := bstep (se 1 (by rfl) ⟨533264, by rfl⟩ : syracuseStep 711019 = 1066529) B1066529
theorem B711031 : Blo 710320 711031 := bstep (se 1 (by rfl) ⟨533273, by rfl⟩ : syracuseStep 711031 = 1066547) B1066547
theorem B711051 : Blo 710320 711051 := bstep (se 1 (by rfl) ⟨533288, by rfl⟩ : syracuseStep 711051 = 1066577) B1066577
theorem B711063 : Blo 710320 711063 := bstep (se 1 (by rfl) ⟨533297, by rfl⟩ : syracuseStep 711063 = 1066595) B1066595
theorem B711083 : Blo 710320 711083 := bstep (se 1 (by rfl) ⟨533312, by rfl⟩ : syracuseStep 711083 = 1066625) B1066625
theorem B711095 : Blo 710320 711095 := bstep (se 1 (by rfl) ⟨533321, by rfl⟩ : syracuseStep 711095 = 1066643) B1066643
theorem B711115 : Blo 710320 711115 := bstep (se 1 (by rfl) ⟨533336, by rfl⟩ : syracuseStep 711115 = 1066673) B1066673
theorem B711127 : Blo 710320 711127 := bstep (se 1 (by rfl) ⟨533345, by rfl⟩ : syracuseStep 711127 = 1066691) B1066691
theorem B1202647 : Blo 710320 1202647 := bstep (se 1 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 1202647 = 1803971) B1803971
theorem B711147 : Blo 710320 711147 := bstep (se 1 (by rfl) ⟨533360, by rfl⟩ : syracuseStep 711147 = 1066721) B1066721
theorem B711159 : Blo 710320 711159 := bstep (se 1 (by rfl) ⟨533369, by rfl⟩ : syracuseStep 711159 = 1066739) B1066739
theorem B711179 : Blo 710320 711179 := bstep (se 1 (by rfl) ⟨533384, by rfl⟩ : syracuseStep 711179 = 1066769) B1066769
theorem B711191 : Blo 710320 711191 := bstep (se 1 (by rfl) ⟨533393, by rfl⟩ : syracuseStep 711191 = 1066787) B1066787
theorem B711211 : Blo 710320 711211 := bstep (se 1 (by rfl) ⟨533408, by rfl⟩ : syracuseStep 711211 = 1066817) B1066817
theorem B711223 : Blo 710320 711223 := bstep (se 1 (by rfl) ⟨533417, by rfl⟩ : syracuseStep 711223 = 1066835) B1066835
theorem B711243 : Blo 710320 711243 := bstep (se 1 (by rfl) ⟨533432, by rfl⟩ : syracuseStep 711243 = 1066865) B1066865
theorem B711255 : Blo 710320 711255 := bstep (se 1 (by rfl) ⟨533441, by rfl⟩ : syracuseStep 711255 = 1066883) B1066883
theorem B711275 : Blo 710320 711275 := bstep (se 1 (by rfl) ⟨533456, by rfl⟩ : syracuseStep 711275 = 1066913) B1066913
theorem B711287 : Blo 710320 711287 := bstep (se 1 (by rfl) ⟨533465, by rfl⟩ : syracuseStep 711287 = 1066931) B1066931
theorem B711307 : Blo 710320 711307 := bstep (se 1 (by rfl) ⟨533480, by rfl⟩ : syracuseStep 711307 = 1066961) B1066961
theorem B711319 : Blo 710320 711319 := bstep (se 1 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 711319 = 1066979) B1066979
theorem B711339 : Blo 710320 711339 := bstep (se 1 (by rfl) ⟨533504, by rfl⟩ : syracuseStep 711339 = 1067009) B1067009
theorem B711351 : Blo 710320 711351 := bstep (se 1 (by rfl) ⟨533513, by rfl⟩ : syracuseStep 711351 = 1067027) B1067027
theorem B711371 : Blo 710320 711371 := bstep (se 1 (by rfl) ⟨533528, by rfl⟩ : syracuseStep 711371 = 1067057) B1067057
theorem B711383 : Blo 710320 711383 := bstep (se 1 (by rfl) ⟨533537, by rfl⟩ : syracuseStep 711383 = 1067075) B1067075
theorem B711403 : Blo 710320 711403 := bstep (se 1 (by rfl) ⟨533552, by rfl⟩ : syracuseStep 711403 = 1067105) B1067105
theorem B711415 : Blo 710320 711415 := bstep (se 1 (by rfl) ⟨533561, by rfl⟩ : syracuseStep 711415 = 1067123) B1067123
theorem B711435 : Blo 710320 711435 := bstep (se 1 (by rfl) ⟨533576, by rfl⟩ : syracuseStep 711435 = 1067153) B1067153
theorem B711447 : Blo 710320 711447 := bstep (se 1 (by rfl) ⟨533585, by rfl⟩ : syracuseStep 711447 = 1067171) B1067171
theorem B711467 : Blo 710320 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B711479 : Blo 710320 711479 := bstep (se 1 (by rfl) ⟨533609, by rfl⟩ : syracuseStep 711479 = 1067219) B1067219
theorem B711499 : Blo 710320 711499 := bstep (se 1 (by rfl) ⟨533624, by rfl⟩ : syracuseStep 711499 = 1067249) B1067249
theorem B711511 : Blo 710320 711511 := bstep (se 1 (by rfl) ⟨533633, by rfl⟩ : syracuseStep 711511 = 1067267) B1067267
theorem B2710361 : Blo 710320 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B711531 : Blo 710320 711531 := bstep (se 1 (by rfl) ⟨533648, by rfl⟩ : syracuseStep 711531 = 1067297) B1067297
theorem B711543 : Blo 710320 711543 := bstep (se 1 (by rfl) ⟨533657, by rfl⟩ : syracuseStep 711543 = 1067315) B1067315
theorem B711563 : Blo 710320 711563 := bstep (se 1 (by rfl) ⟨533672, by rfl⟩ : syracuseStep 711563 = 1067345) B1067345
theorem B711575 : Blo 710320 711575 := bstep (se 1 (by rfl) ⟨533681, by rfl⟩ : syracuseStep 711575 = 1067363) B1067363
theorem B711595 : Blo 710320 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B711607 : Blo 710320 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B711627 : Blo 710320 711627 := bstep (se 1 (by rfl) ⟨533720, by rfl⟩ : syracuseStep 711627 = 1067441) B1067441
theorem B711639 : Blo 710320 711639 := bstep (se 1 (by rfl) ⟨533729, by rfl⟩ : syracuseStep 711639 = 1067459) B1067459
theorem B12311513 : Blo 710320 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B711659 : Blo 710320 711659 := bstep (se 1 (by rfl) ⟨533744, by rfl⟩ : syracuseStep 711659 = 1067489) B1067489
theorem B711671 : Blo 710320 711671 := bstep (se 1 (by rfl) ⟨533753, by rfl⟩ : syracuseStep 711671 = 1067507) B1067507
theorem B711691 : Blo 710320 711691 := bstep (se 1 (by rfl) ⟨533768, by rfl⟩ : syracuseStep 711691 = 1067537) B1067537
theorem B711703 : Blo 710320 711703 := bstep (se 1 (by rfl) ⟨533777, by rfl⟩ : syracuseStep 711703 = 1067555) B1067555
theorem B711723 : Blo 710320 711723 := bstep (se 1 (by rfl) ⟨533792, by rfl⟩ : syracuseStep 711723 = 1067585) B1067585
theorem B711735 : Blo 710320 711735 := bstep (se 1 (by rfl) ⟨533801, by rfl⟩ : syracuseStep 711735 = 1067603) B1067603
theorem B711755 : Blo 710320 711755 := bstep (se 1 (by rfl) ⟨533816, by rfl⟩ : syracuseStep 711755 = 1067633) B1067633
theorem B1203275 : Blo 710320 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B711767 : Blo 710320 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B2776153 : Blo 710320 2776153 := bstep (se 2 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 2776153 = 2082115) B2082115
theorem B711787 : Blo 710320 711787 := bstep (se 1 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 711787 = 1067681) B1067681
theorem B711799 : Blo 710320 711799 := bstep (se 1 (by rfl) ⟨533849, by rfl⟩ : syracuseStep 711799 = 1067699) B1067699
theorem B711819 : Blo 710320 711819 := bstep (se 1 (by rfl) ⟨533864, by rfl⟩ : syracuseStep 711819 = 1067729) B1067729
theorem B711831 : Blo 710320 711831 := bstep (se 1 (by rfl) ⟨533873, by rfl⟩ : syracuseStep 711831 = 1067747) B1067747
theorem B711851 : Blo 710320 711851 := bstep (se 1 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 711851 = 1067777) B1067777
theorem B711863 : Blo 710320 711863 := bstep (se 1 (by rfl) ⟨533897, by rfl⟩ : syracuseStep 711863 = 1067795) B1067795
theorem B3038411 : Blo 710320 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B711883 : Blo 710320 711883 := bstep (se 1 (by rfl) ⟨533912, by rfl⟩ : syracuseStep 711883 = 1067825) B1067825
theorem B1203403 : Blo 710320 1203403 := bstep (se 1 (by rfl) ⟨902552, by rfl⟩ : syracuseStep 1203403 = 1805105) B1805105
theorem B711895 : Blo 710320 711895 := bstep (se 1 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 711895 = 1067843) B1067843
theorem B711915 : Blo 710320 711915 := bstep (se 1 (by rfl) ⟨533936, by rfl⟩ : syracuseStep 711915 = 1067873) B1067873
theorem B711927 : Blo 710320 711927 := bstep (se 1 (by rfl) ⟨533945, by rfl⟩ : syracuseStep 711927 = 1067891) B1067891
theorem B711947 : Blo 710320 711947 := bstep (se 1 (by rfl) ⟨533960, by rfl⟩ : syracuseStep 711947 = 1067921) B1067921
theorem B711959 : Blo 710320 711959 := bstep (se 1 (by rfl) ⟨533969, by rfl⟩ : syracuseStep 711959 = 1067939) B1067939
theorem B711979 : Blo 710320 711979 := bstep (se 1 (by rfl) ⟨533984, by rfl⟩ : syracuseStep 711979 = 1067969) B1067969
theorem B711991 : Blo 710320 711991 := bstep (se 1 (by rfl) ⟨533993, by rfl⟩ : syracuseStep 711991 = 1067987) B1067987
theorem B712011 : Blo 710320 712011 := bstep (se 1 (by rfl) ⟨534008, by rfl⟩ : syracuseStep 712011 = 1068017) B1068017
theorem B712023 : Blo 710320 712023 := bstep (se 1 (by rfl) ⟨534017, by rfl⟩ : syracuseStep 712023 = 1068035) B1068035
theorem B1203545 : Blo 710320 1203545 := bstep (se 2 (by rfl) ⟨451329, by rfl⟩ : syracuseStep 1203545 = 902659) B902659
theorem B712043 : Blo 710320 712043 := bstep (se 1 (by rfl) ⟨534032, by rfl⟩ : syracuseStep 712043 = 1068065) B1068065
theorem B712055 : Blo 710320 712055 := bstep (se 1 (by rfl) ⟨534041, by rfl⟩ : syracuseStep 712055 = 1068083) B1068083
theorem B712075 : Blo 710320 712075 := bstep (se 1 (by rfl) ⟨534056, by rfl⟩ : syracuseStep 712075 = 1068113) B1068113
theorem B712087 : Blo 710320 712087 := bstep (se 1 (by rfl) ⟨534065, by rfl⟩ : syracuseStep 712087 = 1068131) B1068131
theorem B712107 : Blo 710320 712107 := bstep (se 1 (by rfl) ⟨534080, by rfl⟩ : syracuseStep 712107 = 1068161) B1068161
theorem B712119 : Blo 710320 712119 := bstep (se 1 (by rfl) ⟨534089, by rfl⟩ : syracuseStep 712119 = 1068179) B1068179
theorem B712139 : Blo 710320 712139 := bstep (se 1 (by rfl) ⟨534104, by rfl⟩ : syracuseStep 712139 = 1068209) B1068209
theorem B712151 : Blo 710320 712151 := bstep (se 1 (by rfl) ⟨534113, by rfl⟩ : syracuseStep 712151 = 1068227) B1068227
theorem B1203673 : Blo 710320 1203673 := bstep (se 2 (by rfl) ⟨451377, by rfl⟩ : syracuseStep 1203673 = 902755) B902755
theorem B712171 : Blo 710320 712171 := bstep (se 1 (by rfl) ⟨534128, by rfl⟩ : syracuseStep 712171 = 1068257) B1068257
theorem B712183 : Blo 710320 712183 := bstep (se 1 (by rfl) ⟨534137, by rfl⟩ : syracuseStep 712183 = 1068275) B1068275
theorem B712203 : Blo 710320 712203 := bstep (se 1 (by rfl) ⟨534152, by rfl⟩ : syracuseStep 712203 = 1068305) B1068305
theorem B712215 : Blo 710320 712215 := bstep (se 1 (by rfl) ⟨534161, by rfl⟩ : syracuseStep 712215 = 1068323) B1068323
theorem B712235 : Blo 710320 712235 := bstep (se 1 (by rfl) ⟨534176, by rfl⟩ : syracuseStep 712235 = 1068353) B1068353
theorem B712247 : Blo 710320 712247 := bstep (se 1 (by rfl) ⟨534185, by rfl⟩ : syracuseStep 712247 = 1068371) B1068371
theorem B712267 : Blo 710320 712267 := bstep (se 1 (by rfl) ⟨534200, by rfl⟩ : syracuseStep 712267 = 1068401) B1068401
theorem B712279 : Blo 710320 712279 := bstep (se 1 (by rfl) ⟨534209, by rfl⟩ : syracuseStep 712279 = 1068419) B1068419
theorem B712299 : Blo 710320 712299 := bstep (se 1 (by rfl) ⟨534224, by rfl⟩ : syracuseStep 712299 = 1068449) B1068449
theorem B712311 : Blo 710320 712311 := bstep (se 1 (by rfl) ⟨534233, by rfl⟩ : syracuseStep 712311 = 1068467) B1068467
theorem B712331 : Blo 710320 712331 := bstep (se 1 (by rfl) ⟨534248, by rfl⟩ : syracuseStep 712331 = 1068497) B1068497
theorem B712343 : Blo 710320 712343 := bstep (se 1 (by rfl) ⟨534257, by rfl⟩ : syracuseStep 712343 = 1068515) B1068515
theorem B712363 : Blo 710320 712363 := bstep (se 1 (by rfl) ⟨534272, by rfl⟩ : syracuseStep 712363 = 1068545) B1068545
theorem B712375 : Blo 710320 712375 := bstep (se 1 (by rfl) ⟨534281, by rfl⟩ : syracuseStep 712375 = 1068563) B1068563
theorem B1138379 : Blo 710320 1138379 := bstep (se 1 (by rfl) ⟨853784, by rfl⟩ : syracuseStep 1138379 = 1707569) B1707569
theorem B712395 : Blo 710320 712395 := bstep (se 1 (by rfl) ⟨534296, by rfl⟩ : syracuseStep 712395 = 1068593) B1068593
theorem B712407 : Blo 710320 712407 := bstep (se 1 (by rfl) ⟨534305, by rfl⟩ : syracuseStep 712407 = 1068611) B1068611
theorem B712427 : Blo 710320 712427 := bstep (se 1 (by rfl) ⟨534320, by rfl⟩ : syracuseStep 712427 = 1068641) B1068641
theorem B17325809 : Blo 710320 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B712439 : Blo 710320 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B712459 : Blo 710320 712459 := bstep (se 1 (by rfl) ⟨534344, by rfl⟩ : syracuseStep 712459 = 1068689) B1068689
theorem B712471 : Blo 710320 712471 := bstep (se 1 (by rfl) ⟨534353, by rfl⟩ : syracuseStep 712471 = 1068707) B1068707
theorem B712491 : Blo 710320 712491 := bstep (se 1 (by rfl) ⟨534368, by rfl⟩ : syracuseStep 712491 = 1068737) B1068737
theorem B712503 : Blo 710320 712503 := bstep (se 1 (by rfl) ⟨534377, by rfl⟩ : syracuseStep 712503 = 1068755) B1068755
theorem B4054859 : Blo 710320 4054859 := bstep (se 1 (by rfl) ⟨3041144, by rfl⟩ : syracuseStep 4054859 = 6082289) B6082289
theorem B712523 : Blo 710320 712523 := bstep (se 1 (by rfl) ⟨534392, by rfl⟩ : syracuseStep 712523 = 1068785) B1068785
theorem B712535 : Blo 710320 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B712555 : Blo 710320 712555 := bstep (se 1 (by rfl) ⟨534416, by rfl⟩ : syracuseStep 712555 = 1068833) B1068833
theorem B712567 : Blo 710320 712567 := bstep (se 1 (by rfl) ⟨534425, by rfl⟩ : syracuseStep 712567 = 1068851) B1068851
theorem B712587 : Blo 710320 712587 := bstep (se 1 (by rfl) ⟨534440, by rfl⟩ : syracuseStep 712587 = 1068881) B1068881
theorem B712599 : Blo 710320 712599 := bstep (se 1 (by rfl) ⟨534449, by rfl⟩ : syracuseStep 712599 = 1068899) B1068899
theorem B712619 : Blo 710320 712619 := bstep (se 1 (by rfl) ⟨534464, by rfl⟩ : syracuseStep 712619 = 1068929) B1068929
theorem B712631 : Blo 710320 712631 := bstep (se 1 (by rfl) ⟨534473, by rfl⟩ : syracuseStep 712631 = 1068947) B1068947
theorem B712651 : Blo 710320 712651 := bstep (se 1 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 712651 = 1068977) B1068977
theorem B712663 : Blo 710320 712663 := bstep (se 1 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 712663 = 1068995) B1068995
theorem B4874201 : Blo 710320 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B712683 : Blo 710320 712683 := bstep (se 1 (by rfl) ⟨534512, by rfl⟩ : syracuseStep 712683 = 1069025) B1069025
theorem B712695 : Blo 710320 712695 := bstep (se 1 (by rfl) ⟨534521, by rfl⟩ : syracuseStep 712695 = 1069043) B1069043
theorem B712715 : Blo 710320 712715 := bstep (se 1 (by rfl) ⟨534536, by rfl⟩ : syracuseStep 712715 = 1069073) B1069073
theorem B712727 : Blo 710320 712727 := bstep (se 1 (by rfl) ⟨534545, by rfl⟩ : syracuseStep 712727 = 1069091) B1069091
theorem B1204247 : Blo 710320 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B712747 : Blo 710320 712747 := bstep (se 1 (by rfl) ⟨534560, by rfl⟩ : syracuseStep 712747 = 1069121) B1069121
theorem B712759 : Blo 710320 712759 := bstep (se 1 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 712759 = 1069139) B1069139
theorem B712779 : Blo 710320 712779 := bstep (se 1 (by rfl) ⟨534584, by rfl⟩ : syracuseStep 712779 = 1069169) B1069169
theorem B712791 : Blo 710320 712791 := bstep (se 1 (by rfl) ⟨534593, by rfl⟩ : syracuseStep 712791 = 1069187) B1069187
theorem B712811 : Blo 710320 712811 := bstep (se 1 (by rfl) ⟨534608, by rfl⟩ : syracuseStep 712811 = 1069217) B1069217
theorem B712823 : Blo 710320 712823 := bstep (se 1 (by rfl) ⟨534617, by rfl⟩ : syracuseStep 712823 = 1069235) B1069235
theorem B712843 : Blo 710320 712843 := bstep (se 1 (by rfl) ⟨534632, by rfl⟩ : syracuseStep 712843 = 1069265) B1069265
theorem B3039383 : Blo 710320 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B712855 : Blo 710320 712855 := bstep (se 1 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 712855 = 1069283) B1069283
theorem B1204375 : Blo 710320 1204375 := bstep (se 1 (by rfl) ⟨903281, by rfl⟩ : syracuseStep 1204375 = 1806563) B1806563
theorem B712875 : Blo 710320 712875 := bstep (se 1 (by rfl) ⟨534656, by rfl⟩ : syracuseStep 712875 = 1069313) B1069313
theorem B712887 : Blo 710320 712887 := bstep (se 1 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 712887 = 1069331) B1069331
theorem B712907 : Blo 710320 712907 := bstep (se 1 (by rfl) ⟨534680, by rfl⟩ : syracuseStep 712907 = 1069361) B1069361
theorem B2318539 : Blo 710320 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B712919 : Blo 710320 712919 := bstep (se 1 (by rfl) ⟨534689, by rfl⟩ : syracuseStep 712919 = 1069379) B1069379
theorem B712939 : Blo 710320 712939 := bstep (se 1 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 712939 = 1069409) B1069409
theorem B712951 : Blo 710320 712951 := bstep (se 1 (by rfl) ⟨534713, by rfl⟩ : syracuseStep 712951 = 1069427) B1069427
theorem B712971 : Blo 710320 712971 := bstep (se 1 (by rfl) ⟨534728, by rfl⟩ : syracuseStep 712971 = 1069457) B1069457
theorem B3596561 : Blo 710320 3596561 := bstep (se 2 (by rfl) ⟨1348710, by rfl⟩ : syracuseStep 3596561 = 2697421) B2697421
theorem B712983 : Blo 710320 712983 := bstep (se 1 (by rfl) ⟨534737, by rfl⟩ : syracuseStep 712983 = 1069475) B1069475
theorem B713003 : Blo 710320 713003 := bstep (se 1 (by rfl) ⟨534752, by rfl⟩ : syracuseStep 713003 = 1069505) B1069505
theorem B713015 : Blo 710320 713015 := bstep (se 1 (by rfl) ⟨534761, by rfl⟩ : syracuseStep 713015 = 1069523) B1069523
theorem B713035 : Blo 710320 713035 := bstep (se 1 (by rfl) ⟨534776, by rfl⟩ : syracuseStep 713035 = 1069553) B1069553
theorem B713047 : Blo 710320 713047 := bstep (se 1 (by rfl) ⟨534785, by rfl⟩ : syracuseStep 713047 = 1069571) B1069571
theorem B713067 : Blo 710320 713067 := bstep (se 1 (by rfl) ⟨534800, by rfl⟩ : syracuseStep 713067 = 1069601) B1069601
theorem B713079 : Blo 710320 713079 := bstep (se 1 (by rfl) ⟨534809, by rfl⟩ : syracuseStep 713079 = 1069619) B1069619
theorem B713099 : Blo 710320 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B713111 : Blo 710320 713111 := bstep (se 1 (by rfl) ⟨534833, by rfl⟩ : syracuseStep 713111 = 1069667) B1069667
theorem B713131 : Blo 710320 713131 := bstep (se 1 (by rfl) ⟨534848, by rfl⟩ : syracuseStep 713131 = 1069697) B1069697
theorem B3596723 : Blo 710320 3596723 := bstep (se 1 (by rfl) ⟨2697542, by rfl⟩ : syracuseStep 3596723 = 5395085) B5395085
theorem B5497267 : Blo 710320 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B2711987 : Blo 710320 2711987 := bstep (se 1 (by rfl) ⟨2033990, by rfl⟩ : syracuseStep 2711987 = 4067981) B4067981
theorem B713143 : Blo 710320 713143 := bstep (se 1 (by rfl) ⟨534857, by rfl⟩ : syracuseStep 713143 = 1069715) B1069715
theorem B2712001 : Blo 710320 2712001 := bstep (se 2 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 2712001 = 2034001) B2034001
theorem B713163 : Blo 710320 713163 := bstep (se 1 (by rfl) ⟨534872, by rfl⟩ : syracuseStep 713163 = 1069745) B1069745
theorem B5923277 : Blo 710320 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B713175 : Blo 710320 713175 := bstep (se 1 (by rfl) ⟨534881, by rfl⟩ : syracuseStep 713175 = 1069763) B1069763
theorem B713195 : Blo 710320 713195 := bstep (se 1 (by rfl) ⟨534896, by rfl⟩ : syracuseStep 713195 = 1069793) B1069793
theorem B713207 : Blo 710320 713207 := bstep (se 1 (by rfl) ⟨534905, by rfl⟩ : syracuseStep 713207 = 1069811) B1069811
theorem B713227 : Blo 710320 713227 := bstep (se 1 (by rfl) ⟨534920, by rfl⟩ : syracuseStep 713227 = 1069841) B1069841
theorem B713239 : Blo 710320 713239 := bstep (se 1 (by rfl) ⟨534929, by rfl⟩ : syracuseStep 713239 = 1069859) B1069859
theorem B713259 : Blo 710320 713259 := bstep (se 1 (by rfl) ⟨534944, by rfl⟩ : syracuseStep 713259 = 1069889) B1069889
theorem B713271 : Blo 710320 713271 := bstep (se 1 (by rfl) ⟨534953, by rfl⟩ : syracuseStep 713271 = 1069907) B1069907
theorem B713291 : Blo 710320 713291 := bstep (se 1 (by rfl) ⟨534968, by rfl⟩ : syracuseStep 713291 = 1069937) B1069937
theorem B713303 : Blo 710320 713303 := bstep (se 1 (by rfl) ⟨534977, by rfl⟩ : syracuseStep 713303 = 1069955) B1069955
theorem B713323 : Blo 710320 713323 := bstep (se 1 (by rfl) ⟨534992, by rfl⟩ : syracuseStep 713323 = 1069985) B1069985
theorem B713335 : Blo 710320 713335 := bstep (se 1 (by rfl) ⟨535001, by rfl⟩ : syracuseStep 713335 = 1070003) B1070003
theorem B713355 : Blo 710320 713355 := bstep (se 1 (by rfl) ⟨535016, by rfl⟩ : syracuseStep 713355 = 1070033) B1070033
theorem B713367 : Blo 710320 713367 := bstep (se 1 (by rfl) ⟨535025, by rfl⟩ : syracuseStep 713367 = 1070051) B1070051
theorem B713387 : Blo 710320 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B713399 : Blo 710320 713399 := bstep (se 1 (by rfl) ⟨535049, by rfl⟩ : syracuseStep 713399 = 1070099) B1070099
theorem B713419 : Blo 710320 713419 := bstep (se 1 (by rfl) ⟨535064, by rfl⟩ : syracuseStep 713419 = 1070129) B1070129
theorem B1172183 : Blo 710320 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B713431 : Blo 710320 713431 := bstep (se 1 (by rfl) ⟨535073, by rfl⟩ : syracuseStep 713431 = 1070147) B1070147
theorem B713451 : Blo 710320 713451 := bstep (se 1 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 713451 = 1070177) B1070177
theorem B713463 : Blo 710320 713463 := bstep (se 1 (by rfl) ⟨535097, by rfl⟩ : syracuseStep 713463 = 1070195) B1070195
theorem B713483 : Blo 710320 713483 := bstep (se 1 (by rfl) ⟨535112, by rfl⟩ : syracuseStep 713483 = 1070225) B1070225
theorem B1205003 : Blo 710320 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B713495 : Blo 710320 713495 := bstep (se 1 (by rfl) ⟨535121, by rfl⟩ : syracuseStep 713495 = 1070243) B1070243
theorem B713515 : Blo 710320 713515 := bstep (se 1 (by rfl) ⟨535136, by rfl⟩ : syracuseStep 713515 = 1070273) B1070273
theorem B3040051 : Blo 710320 3040051 := bstep (se 1 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 3040051 = 4560077) B4560077
theorem B713527 : Blo 710320 713527 := bstep (se 1 (by rfl) ⟨535145, by rfl⟩ : syracuseStep 713527 = 1070291) B1070291
theorem B1598273 : Blo 710320 1598273 := bstep (se 2 (by rfl) ⟨599352, by rfl⟩ : syracuseStep 1598273 = 1198705) B1198705
theorem B713547 : Blo 710320 713547 := bstep (se 1 (by rfl) ⟨535160, by rfl⟩ : syracuseStep 713547 = 1070321) B1070321
theorem B713559 : Blo 710320 713559 := bstep (se 1 (by rfl) ⟨535169, by rfl⟩ : syracuseStep 713559 = 1070339) B1070339
theorem B713579 : Blo 710320 713579 := bstep (se 1 (by rfl) ⟨535184, by rfl⟩ : syracuseStep 713579 = 1070369) B1070369
theorem B713591 : Blo 710320 713591 := bstep (se 1 (by rfl) ⟨535193, by rfl⟩ : syracuseStep 713591 = 1070387) B1070387
theorem B713611 : Blo 710320 713611 := bstep (se 1 (by rfl) ⟨535208, by rfl⟩ : syracuseStep 713611 = 1070417) B1070417
theorem B1205131 : Blo 710320 1205131 := bstep (se 1 (by rfl) ⟨903848, by rfl⟩ : syracuseStep 1205131 = 1807697) B1807697
theorem B713623 : Blo 710320 713623 := bstep (se 1 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 713623 = 1070435) B1070435
theorem B713643 : Blo 710320 713643 := bstep (se 1 (by rfl) ⟨535232, by rfl⟩ : syracuseStep 713643 = 1070465) B1070465
theorem B10281907 : Blo 710320 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B713655 : Blo 710320 713655 := bstep (se 1 (by rfl) ⟨535241, by rfl⟩ : syracuseStep 713655 = 1070483) B1070483
theorem B713675 : Blo 710320 713675 := bstep (se 1 (by rfl) ⟨535256, by rfl⟩ : syracuseStep 713675 = 1070513) B1070513
theorem B713687 : Blo 710320 713687 := bstep (se 1 (by rfl) ⟨535265, by rfl⟩ : syracuseStep 713687 = 1070531) B1070531
theorem B713707 : Blo 710320 713707 := bstep (se 1 (by rfl) ⟨535280, by rfl⟩ : syracuseStep 713707 = 1070561) B1070561
theorem B713719 : Blo 710320 713719 := bstep (se 1 (by rfl) ⟨535289, by rfl⟩ : syracuseStep 713719 = 1070579) B1070579
theorem B713739 : Blo 710320 713739 := bstep (se 1 (by rfl) ⟨535304, by rfl⟩ : syracuseStep 713739 = 1070609) B1070609
theorem B713751 : Blo 710320 713751 := bstep (se 1 (by rfl) ⟨535313, by rfl⟩ : syracuseStep 713751 = 1070627) B1070627
theorem B1598489 : Blo 710320 1598489 := bstep (se 2 (by rfl) ⟨599433, by rfl⟩ : syracuseStep 1598489 = 1198867) B1198867
theorem B1205273 : Blo 710320 1205273 := bstep (se 2 (by rfl) ⟨451977, by rfl⟩ : syracuseStep 1205273 = 903955) B903955
theorem B713771 : Blo 710320 713771 := bstep (se 1 (by rfl) ⟨535328, by rfl⟩ : syracuseStep 713771 = 1070657) B1070657
theorem B713783 : Blo 710320 713783 := bstep (se 1 (by rfl) ⟨535337, by rfl⟩ : syracuseStep 713783 = 1070675) B1070675
theorem B713803 : Blo 710320 713803 := bstep (se 1 (by rfl) ⟨535352, by rfl⟩ : syracuseStep 713803 = 1070705) B1070705
theorem B713815 : Blo 710320 713815 := bstep (se 1 (by rfl) ⟨535361, by rfl⟩ : syracuseStep 713815 = 1070723) B1070723
theorem B713835 : Blo 710320 713835 := bstep (se 1 (by rfl) ⟨535376, by rfl⟩ : syracuseStep 713835 = 1070753) B1070753
theorem B1598579 : Blo 710320 1598579 := bstep (se 1 (by rfl) ⟨1198934, by rfl⟩ : syracuseStep 1598579 = 2397869) B2397869
theorem B713847 : Blo 710320 713847 := bstep (se 1 (by rfl) ⟨535385, by rfl⟩ : syracuseStep 713847 = 1070771) B1070771
theorem B713867 : Blo 710320 713867 := bstep (se 1 (by rfl) ⟨535400, by rfl⟩ : syracuseStep 713867 = 1070801) B1070801
theorem B1598615 : Blo 710320 1598615 := bstep (se 1 (by rfl) ⟨1198961, by rfl⟩ : syracuseStep 1598615 = 2397923) B2397923
theorem B713879 : Blo 710320 713879 := bstep (se 1 (by rfl) ⟨535409, by rfl⟩ : syracuseStep 713879 = 1070819) B1070819
theorem B1205401 : Blo 710320 1205401 := bstep (se 2 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 1205401 = 904051) B904051
theorem B713899 : Blo 710320 713899 := bstep (se 1 (by rfl) ⟨535424, by rfl⟩ : syracuseStep 713899 = 1070849) B1070849
theorem B713911 : Blo 710320 713911 := bstep (se 1 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 713911 = 1070867) B1070867
theorem B713931 : Blo 710320 713931 := bstep (se 1 (by rfl) ⟨535448, by rfl⟩ : syracuseStep 713931 = 1070897) B1070897
theorem B5137613 : Blo 710320 5137613 := bstep (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) B1926605
theorem B713943 : Blo 710320 713943 := bstep (se 1 (by rfl) ⟨535457, by rfl⟩ : syracuseStep 713943 = 1070915) B1070915
theorem B713963 : Blo 710320 713963 := bstep (se 1 (by rfl) ⟨535472, by rfl⟩ : syracuseStep 713963 = 1070945) B1070945
theorem B713975 : Blo 710320 713975 := bstep (se 1 (by rfl) ⟨535481, by rfl⟩ : syracuseStep 713975 = 1070963) B1070963
theorem B713995 : Blo 710320 713995 := bstep (se 1 (by rfl) ⟨535496, by rfl⟩ : syracuseStep 713995 = 1070993) B1070993
theorem B714007 : Blo 710320 714007 := bstep (se 1 (by rfl) ⟨535505, by rfl⟩ : syracuseStep 714007 = 1071011) B1071011
theorem B714027 : Blo 710320 714027 := bstep (se 1 (by rfl) ⟨535520, by rfl⟩ : syracuseStep 714027 = 1071041) B1071041
theorem B714039 : Blo 710320 714039 := bstep (se 1 (by rfl) ⟨535529, by rfl⟩ : syracuseStep 714039 = 1071059) B1071059
theorem B1598795 : Blo 710320 1598795 := bstep (se 1 (by rfl) ⟨1199096, by rfl⟩ : syracuseStep 1598795 = 2398193) B2398193
theorem B714059 : Blo 710320 714059 := bstep (se 1 (by rfl) ⟨535544, by rfl⟩ : syracuseStep 714059 = 1071089) B1071089
theorem B714071 : Blo 710320 714071 := bstep (se 1 (by rfl) ⟨535553, by rfl⟩ : syracuseStep 714071 = 1071107) B1071107
theorem B714091 : Blo 710320 714091 := bstep (se 1 (by rfl) ⟨535568, by rfl⟩ : syracuseStep 714091 = 1071137) B1071137
theorem B714103 : Blo 710320 714103 := bstep (se 1 (by rfl) ⟨535577, by rfl⟩ : syracuseStep 714103 = 1071155) B1071155
theorem B1598849 : Blo 710320 1598849 := bstep (se 2 (by rfl) ⟨599568, by rfl⟩ : syracuseStep 1598849 = 1199137) B1199137
theorem B714123 : Blo 710320 714123 := bstep (se 1 (by rfl) ⟨535592, by rfl⟩ : syracuseStep 714123 = 1071185) B1071185
theorem B1926551 : Blo 710320 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B714135 : Blo 710320 714135 := bstep (se 1 (by rfl) ⟨535601, by rfl⟩ : syracuseStep 714135 = 1071203) B1071203
theorem B714155 : Blo 710320 714155 := bstep (se 1 (by rfl) ⟨535616, by rfl⟩ : syracuseStep 714155 = 1071233) B1071233
theorem B714167 : Blo 710320 714167 := bstep (se 1 (by rfl) ⟨535625, by rfl⟩ : syracuseStep 714167 = 1071251) B1071251
theorem B714187 : Blo 710320 714187 := bstep (se 1 (by rfl) ⟨535640, by rfl⟩ : syracuseStep 714187 = 1071281) B1071281
theorem B714199 : Blo 710320 714199 := bstep (se 1 (by rfl) ⟨535649, by rfl⟩ : syracuseStep 714199 = 1071299) B1071299
theorem B714219 : Blo 710320 714219 := bstep (se 1 (by rfl) ⟨535664, by rfl⟩ : syracuseStep 714219 = 1071329) B1071329
theorem B714231 : Blo 710320 714231 := bstep (se 1 (by rfl) ⟨535673, by rfl⟩ : syracuseStep 714231 = 1071347) B1071347
theorem B714251 : Blo 710320 714251 := bstep (se 1 (by rfl) ⟨535688, by rfl⟩ : syracuseStep 714251 = 1071377) B1071377
theorem B714263 : Blo 710320 714263 := bstep (se 1 (by rfl) ⟨535697, by rfl⟩ : syracuseStep 714263 = 1071395) B1071395
theorem B714283 : Blo 710320 714283 := bstep (se 1 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 714283 = 1071425) B1071425
theorem B714295 : Blo 710320 714295 := bstep (se 1 (by rfl) ⟨535721, by rfl⟩ : syracuseStep 714295 = 1071443) B1071443
theorem B714315 : Blo 710320 714315 := bstep (se 1 (by rfl) ⟨535736, by rfl⟩ : syracuseStep 714315 = 1071473) B1071473
theorem B1599065 : Blo 710320 1599065 := bstep (se 2 (by rfl) ⟨599649, by rfl⟩ : syracuseStep 1599065 = 1199299) B1199299
theorem B10938007 : Blo 710320 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B1599155 : Blo 710320 1599155 := bstep (se 1 (by rfl) ⟨1199366, by rfl⟩ : syracuseStep 1599155 = 2398733) B2398733
theorem B1599191 : Blo 710320 1599191 := bstep (se 1 (by rfl) ⟨1199393, by rfl⟩ : syracuseStep 1599191 = 2398787) B2398787
theorem B9135989 : Blo 710320 9135989 := bstep (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) B856499
theorem B1599371 : Blo 710320 1599371 := bstep (se 1 (by rfl) ⟨1199528, by rfl⟩ : syracuseStep 1599371 = 2399057) B2399057
theorem B1599425 : Blo 710320 1599425 := bstep (se 2 (by rfl) ⟨599784, by rfl⟩ : syracuseStep 1599425 = 1199569) B1199569
theorem B3041297 : Blo 710320 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B1927243 : Blo 710320 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B1599641 : Blo 710320 1599641 := bstep (se 2 (by rfl) ⟨599865, by rfl⟩ : syracuseStep 1599641 = 1199731) B1199731
theorem B1370315 : Blo 710320 1370315 := bstep (se 1 (by rfl) ⟨1027736, by rfl⟩ : syracuseStep 1370315 = 2055473) B2055473
theorem B1599731 : Blo 710320 1599731 := bstep (se 1 (by rfl) ⟨1199798, by rfl⟩ : syracuseStep 1599731 = 2399597) B2399597
theorem B1599767 : Blo 710320 1599767 := bstep (se 1 (by rfl) ⟨1199825, by rfl⟩ : syracuseStep 1599767 = 2399651) B2399651
theorem B3598667 : Blo 710320 3598667 := bstep (se 1 (by rfl) ⟨2699000, by rfl⟩ : syracuseStep 3598667 = 5398001) B5398001
theorem B4057523 : Blo 710320 4057523 := bstep (se 1 (by rfl) ⟨3043142, by rfl⟩ : syracuseStep 4057523 = 6086285) B6086285
theorem B1599947 : Blo 710320 1599947 := bstep (se 1 (by rfl) ⟨1199960, by rfl⟩ : syracuseStep 1599947 = 2399921) B2399921
theorem B1600001 : Blo 710320 1600001 := bstep (se 2 (by rfl) ⟨600000, by rfl⟩ : syracuseStep 1600001 = 1200001) B1200001
theorem B2026073 : Blo 710320 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B1600217 : Blo 710320 1600217 := bstep (se 2 (by rfl) ⟨600081, by rfl⟩ : syracuseStep 1600217 = 1200163) B1200163
theorem B1600307 : Blo 710320 1600307 := bstep (se 1 (by rfl) ⟨1200230, by rfl⟩ : syracuseStep 1600307 = 2400461) B2400461
theorem B1600343 : Blo 710320 1600343 := bstep (se 1 (by rfl) ⟨1200257, by rfl⟩ : syracuseStep 1600343 = 2400515) B2400515
theorem B13003697 : Blo 710320 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B1600523 : Blo 710320 1600523 := bstep (se 1 (by rfl) ⟨1200392, by rfl⟩ : syracuseStep 1600523 = 2400785) B2400785
theorem B1600577 : Blo 710320 1600577 := bstep (se 2 (by rfl) ⟨600216, by rfl⟩ : syracuseStep 1600577 = 1200433) B1200433
theorem B1928281 : Blo 710320 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B1600793 : Blo 710320 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B1600883 : Blo 710320 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B1600919 : Blo 710320 1600919 := bstep (se 1 (by rfl) ⟨1200689, by rfl⟩ : syracuseStep 1600919 = 2401379) B2401379
theorem B1928627 : Blo 710320 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1601099 : Blo 710320 1601099 := bstep (se 1 (by rfl) ⟨1200824, by rfl⟩ : syracuseStep 1601099 = 2401649) B2401649
theorem B1601153 : Blo 710320 1601153 := bstep (se 2 (by rfl) ⟨600432, by rfl⟩ : syracuseStep 1601153 = 1200865) B1200865
theorem B1928897 : Blo 710320 1928897 := bstep (se 2 (by rfl) ⟨723336, by rfl⟩ : syracuseStep 1928897 = 1446673) B1446673
theorem B1830617 : Blo 710320 1830617 := bstep (se 2 (by rfl) ⟨686481, by rfl⟩ : syracuseStep 1830617 = 1372963) B1372963
theorem B2027339 : Blo 710320 2027339 := bstep (se 1 (by rfl) ⟨1520504, by rfl⟩ : syracuseStep 2027339 = 3041009) B3041009
theorem B1601369 : Blo 710320 1601369 := bstep (se 2 (by rfl) ⟨600513, by rfl⟩ : syracuseStep 1601369 = 1201027) B1201027
theorem B4058981 : Blo 710320 4058981 := bstep (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) B761059
theorem B1601459 : Blo 710320 1601459 := bstep (se 1 (by rfl) ⟨1201094, by rfl⟩ : syracuseStep 1601459 = 2402189) B2402189
theorem B1601495 : Blo 710320 1601495 := bstep (se 1 (by rfl) ⟨1201121, by rfl⟩ : syracuseStep 1601495 = 2402243) B2402243
theorem B3600449 : Blo 710320 3600449 := bstep (se 2 (by rfl) ⟨1350168, by rfl⟩ : syracuseStep 3600449 = 2700337) B2700337
theorem B17789003 : Blo 710320 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B1601675 : Blo 710320 1601675 := bstep (se 1 (by rfl) ⟨1201256, by rfl⟩ : syracuseStep 1601675 = 2402513) B2402513
theorem B4944023 : Blo 710320 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B1601729 : Blo 710320 1601729 := bstep (se 2 (by rfl) ⟨600648, by rfl⟩ : syracuseStep 1601729 = 1201297) B1201297
theorem B2748761 : Blo 710320 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B1601945 : Blo 710320 1601945 := bstep (se 2 (by rfl) ⟨600729, by rfl⟩ : syracuseStep 1601945 = 1201459) B1201459
theorem B3043757 : Blo 710320 3043757 := bstep (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) B1141409
theorem B1012171 : Blo 710320 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B1602035 : Blo 710320 1602035 := bstep (se 1 (by rfl) ⟨1201526, by rfl⟩ : syracuseStep 1602035 = 2403053) B2403053
theorem B4059665 : Blo 710320 4059665 := bstep (se 2 (by rfl) ⟨1522374, by rfl⟩ : syracuseStep 4059665 = 3044749) B3044749
theorem B1602071 : Blo 710320 1602071 := bstep (se 1 (by rfl) ⟨1201553, by rfl⟩ : syracuseStep 1602071 = 2403107) B2403107
theorem B1143371 : Blo 710320 1143371 := bstep (se 1 (by rfl) ⟨857528, by rfl⟩ : syracuseStep 1143371 = 1715057) B1715057
theorem B1798807 : Blo 710320 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B1602251 : Blo 710320 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B11530957 : Blo 710320 11530957 := bstep (se 3 (by rfl) ⟨2162054, by rfl⟩ : syracuseStep 11530957 = 4324109) B4324109
theorem B1012439 : Blo 710320 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B1602305 : Blo 710320 1602305 := bstep (se 2 (by rfl) ⟨600864, by rfl⟩ : syracuseStep 1602305 = 1201729) B1201729
theorem B6157073 : Blo 710320 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B9237365 : Blo 710320 9237365 := bstep (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) B866003
theorem B1143767 : Blo 710320 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B1602521 : Blo 710320 1602521 := bstep (se 2 (by rfl) ⟨600945, by rfl⟩ : syracuseStep 1602521 = 1201891) B1201891
theorem B10417169 : Blo 710320 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B1602611 : Blo 710320 1602611 := bstep (se 1 (by rfl) ⟨1201958, by rfl⟩ : syracuseStep 1602611 = 2403917) B2403917
theorem B1799243 : Blo 710320 1799243 := bstep (se 1 (by rfl) ⟨1349432, by rfl⟩ : syracuseStep 1799243 = 2698865) B2698865
theorem B1602647 : Blo 710320 1602647 := bstep (se 1 (by rfl) ⟨1201985, by rfl⟩ : syracuseStep 1602647 = 2403971) B2403971
theorem B3044441 : Blo 710320 3044441 := bstep (se 2 (by rfl) ⟨1141665, by rfl⟩ : syracuseStep 3044441 = 2283331) B2283331
theorem B1602827 : Blo 710320 1602827 := bstep (se 1 (by rfl) ⟨1202120, by rfl⟩ : syracuseStep 1602827 = 2404241) B2404241
theorem B1602881 : Blo 710320 1602881 := bstep (se 2 (by rfl) ⟨601080, by rfl⟩ : syracuseStep 1602881 = 1202161) B1202161
theorem B1799617 : Blo 710320 1799617 := bstep (se 2 (by rfl) ⟨674856, by rfl⟩ : syracuseStep 1799617 = 1349713) B1349713
theorem B2192861 : Blo 710320 2192861 := bstep (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) B822323
theorem B1603097 : Blo 710320 1603097 := bstep (se 2 (by rfl) ⟨601161, by rfl⟩ : syracuseStep 1603097 = 1202323) B1202323
theorem B1603187 : Blo 710320 1603187 := bstep (se 1 (by rfl) ⟨1202390, by rfl⟩ : syracuseStep 1603187 = 2404781) B2404781
theorem B1603223 : Blo 710320 1603223 := bstep (se 1 (by rfl) ⟨1202417, by rfl⟩ : syracuseStep 1603223 = 2404835) B2404835
theorem B1013401 : Blo 710320 1013401 := bstep (se 2 (by rfl) ⟨380025, by rfl⟩ : syracuseStep 1013401 = 760051) B760051
theorem B1603403 : Blo 710320 1603403 := bstep (se 1 (by rfl) ⟨1202552, by rfl⟩ : syracuseStep 1603403 = 2405105) B2405105
theorem B1603457 : Blo 710320 1603457 := bstep (se 2 (by rfl) ⟨601296, by rfl⟩ : syracuseStep 1603457 = 1202593) B1202593
theorem B3602393 : Blo 710320 3602393 := bstep (se 2 (by rfl) ⟨1350897, by rfl⟩ : syracuseStep 3602393 = 2701795) B2701795
theorem B1800215 : Blo 710320 1800215 := bstep (se 1 (by rfl) ⟨1350161, by rfl⟩ : syracuseStep 1800215 = 2700323) B2700323
theorem B1603673 : Blo 710320 1603673 := bstep (se 2 (by rfl) ⟨601377, by rfl⟩ : syracuseStep 1603673 = 1202755) B1202755
theorem B5142629 : Blo 710320 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B1603763 : Blo 710320 1603763 := bstep (se 1 (by rfl) ⟨1202822, by rfl⟩ : syracuseStep 1603763 = 2405645) B2405645
theorem B1603799 : Blo 710320 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B5765411 : Blo 710320 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B3045707 : Blo 710320 3045707 := bstep (se 1 (by rfl) ⟨2284280, by rfl⟩ : syracuseStep 3045707 = 4568561) B4568561
theorem B1440089 : Blo 710320 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B94959985 : Blo 710320 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B1603979 : Blo 710320 1603979 := bstep (se 1 (by rfl) ⟨1202984, by rfl⟩ : syracuseStep 1603979 = 2405969) B2405969
theorem B1604033 : Blo 710320 1604033 := bstep (se 2 (by rfl) ⟨601512, by rfl⟩ : syracuseStep 1604033 = 1203025) B1203025
theorem B1538713 : Blo 710320 1538713 := bstep (se 2 (by rfl) ⟨577017, by rfl⟩ : syracuseStep 1538713 = 1154035) B1154035
theorem B1604249 : Blo 710320 1604249 := bstep (se 2 (by rfl) ⟨601593, by rfl⟩ : syracuseStep 1604249 = 1203187) B1203187
theorem B3046081 : Blo 710320 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B1604339 : Blo 710320 1604339 := bstep (se 1 (by rfl) ⟨1203254, by rfl⟩ : syracuseStep 1604339 = 2406509) B2406509
theorem B1604375 : Blo 710320 1604375 := bstep (se 1 (by rfl) ⟨1203281, by rfl⟩ : syracuseStep 1604375 = 2406563) B2406563
theorem B1801025 : Blo 710320 1801025 := bstep (se 2 (by rfl) ⟨675384, by rfl⟩ : syracuseStep 1801025 = 1350769) B1350769
theorem B1440641 : Blo 710320 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B1604555 : Blo 710320 1604555 := bstep (se 1 (by rfl) ⟨1203416, by rfl⟩ : syracuseStep 1604555 = 2406833) B2406833
theorem B1604609 : Blo 710320 1604609 := bstep (se 2 (by rfl) ⟨601728, by rfl⟩ : syracuseStep 1604609 = 1203457) B1203457
theorem B3046423 : Blo 710320 3046423 := bstep (se 1 (by rfl) ⟨2284817, by rfl⟩ : syracuseStep 3046423 = 4569635) B4569635
theorem B1014859 : Blo 710320 1014859 := bstep (se 1 (by rfl) ⟨761144, by rfl⟩ : syracuseStep 1014859 = 1522289) B1522289
theorem B1014871 : Blo 710320 1014871 := bstep (se 1 (by rfl) ⟨761153, by rfl⟩ : syracuseStep 1014871 = 1522307) B1522307
theorem B1604825 : Blo 710320 1604825 := bstep (se 2 (by rfl) ⟨601809, by rfl⟩ : syracuseStep 1604825 = 1203619) B1203619
theorem B1604915 : Blo 710320 1604915 := bstep (se 1 (by rfl) ⟨1203686, by rfl⟩ : syracuseStep 1604915 = 2407373) B2407373
theorem B1604951 : Blo 710320 1604951 := bstep (se 1 (by rfl) ⟨1203713, by rfl⟩ : syracuseStep 1604951 = 2407427) B2407427
theorem B1506647 : Blo 710320 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B1801561 : Blo 710320 1801561 := bstep (se 2 (by rfl) ⟨675585, by rfl⟩ : syracuseStep 1801561 = 1351171) B1351171
theorem B10255733 : Blo 710320 10255733 := bstep (se 5 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 10255733 = 961475) B961475
theorem B1605131 : Blo 710320 1605131 := bstep (se 1 (by rfl) ⟨1203848, by rfl⟩ : syracuseStep 1605131 = 2407697) B2407697
theorem B3604013 : Blo 710320 3604013 := bstep (se 3 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 3604013 = 1351505) B1351505
theorem B1605185 : Blo 710320 1605185 := bstep (se 2 (by rfl) ⟨601944, by rfl⟩ : syracuseStep 1605185 = 1203889) B1203889
theorem B720523 : Blo 710320 720523 := bstep (se 1 (by rfl) ⟨540392, by rfl⟩ : syracuseStep 720523 = 1080785) B1080785
theorem B4062899 : Blo 710320 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B1605401 : Blo 710320 1605401 := bstep (se 2 (by rfl) ⟨602025, by rfl⟩ : syracuseStep 1605401 = 1204051) B1204051
theorem B1605491 : Blo 710320 1605491 := bstep (se 1 (by rfl) ⟨1204118, by rfl⟩ : syracuseStep 1605491 = 2408237) B2408237
theorem B1605527 : Blo 710320 1605527 := bstep (se 1 (by rfl) ⟨1204145, by rfl⟩ : syracuseStep 1605527 = 2408291) B2408291
theorem B1605779 : Blo 710320 1605779 := bstep (se 1 (by rfl) ⟨1204334, by rfl⟩ : syracuseStep 1605779 = 2408669) B2408669
theorem B1015993 : Blo 710320 1015993 := bstep (se 2 (by rfl) ⟨380997, by rfl⟩ : syracuseStep 1015993 = 761995) B761995
theorem B4554953 : Blo 710320 4554953 := bstep (se 2 (by rfl) ⟨1708107, by rfl⟩ : syracuseStep 4554953 = 3416215) B3416215
theorem B1605833 : Blo 710320 1605833 := bstep (se 2 (by rfl) ⟨602187, by rfl⟩ : syracuseStep 1605833 = 1204375) B1204375
theorem B721159 : Blo 710320 721159 := bstep (se 1 (by rfl) ⟨540869, by rfl⟩ : syracuseStep 721159 = 1081739) B1081739
theorem B2031905 : Blo 710320 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B5407235 : Blo 710320 5407235 := bstep (se 1 (by rfl) ⟨4055426, by rfl⟩ : syracuseStep 5407235 = 8110853) B8110853
theorem B721423 : Blo 710320 721423 := bstep (se 1 (by rfl) ⟨541067, by rfl⟩ : syracuseStep 721423 = 1082135) B1082135
theorem B1803019 : Blo 710320 1803019 := bstep (se 1 (by rfl) ⟨1352264, by rfl⟩ : syracuseStep 1803019 = 2704529) B2704529
theorem B1606535 : Blo 710320 1606535 := bstep (se 1 (by rfl) ⟨1204901, by rfl⟩ : syracuseStep 1606535 = 2409803) B2409803
theorem B1803161 : Blo 710320 1803161 := bstep (se 2 (by rfl) ⟨676185, by rfl⟩ : syracuseStep 1803161 = 1352371) B1352371
theorem B1803323 : Blo 710320 1803323 := bstep (se 1 (by rfl) ⟨1352492, by rfl⟩ : syracuseStep 1803323 = 2704985) B2704985
theorem B1606715 : Blo 710320 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B1606841 : Blo 710320 1606841 := bstep (se 2 (by rfl) ⟨602565, by rfl⟩ : syracuseStep 1606841 = 1205131) B1205131
theorem B2032897 : Blo 710320 2032897 := bstep (se 2 (by rfl) ⟨762336, by rfl⟩ : syracuseStep 2032897 = 1524673) B1524673
theorem B1803667 : Blo 710320 1803667 := bstep (se 1 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 1803667 = 2705501) B2705501
theorem B722363 : Blo 710320 722363 := bstep (se 1 (by rfl) ⟨541772, by rfl⟩ : syracuseStep 722363 = 1083545) B1083545
theorem B1607183 : Blo 710320 1607183 := bstep (se 1 (by rfl) ⟨1205387, by rfl⟩ : syracuseStep 1607183 = 2410775) B2410775
theorem B1803809 : Blo 710320 1803809 := bstep (se 2 (by rfl) ⟨676428, by rfl⟩ : syracuseStep 1803809 = 1352857) B1352857
theorem B1607201 : Blo 710320 1607201 := bstep (se 2 (by rfl) ⟨602700, by rfl⟩ : syracuseStep 1607201 = 1205401) B1205401
theorem B2197547 : Blo 710320 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B3606929 : Blo 710320 3606929 := bstep (se 2 (by rfl) ⟨1352598, by rfl⟩ : syracuseStep 3606929 = 2705197) B2705197
theorem B14780819 : Blo 710320 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B21629405 : Blo 710320 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B854519 : Blo 710320 854519 := bstep (se 1 (by rfl) ⟨640889, by rfl⟩ : syracuseStep 854519 = 1281779) B1281779
theorem B1804801 : Blo 710320 1804801 := bstep (se 2 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 1804801 = 1353601) B1353601
theorem B4065815 : Blo 710320 4065815 := bstep (se 1 (by rfl) ⟨3049361, by rfl⟩ : syracuseStep 4065815 = 6098723) B6098723
theorem B3050045 : Blo 710320 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B1280713 : Blo 710320 1280713 := bstep (se 2 (by rfl) ⟨480267, by rfl⟩ : syracuseStep 1280713 = 960535) B960535
theorem B9112409 : Blo 710320 9112409 := bstep (se 2 (by rfl) ⟨3417153, by rfl⟩ : syracuseStep 9112409 = 6834307) B6834307
theorem B11537315 : Blo 710320 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B1805399 : Blo 710320 1805399 := bstep (se 1 (by rfl) ⟨1354049, by rfl⟩ : syracuseStep 1805399 = 2708099) B2708099
theorem B1707193 : Blo 710320 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B1805611 : Blo 710320 1805611 := bstep (se 1 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 1805611 = 2708417) B2708417
theorem B34639163 : Blo 710320 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B1805753 : Blo 710320 1805753 := bstep (se 2 (by rfl) ⟨677157, by rfl⟩ : syracuseStep 1805753 = 1354315) B1354315
theorem B2887235 : Blo 710320 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B1707655 : Blo 710320 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B1281737 : Blo 710320 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B856207 : Blo 710320 856207 := bstep (se 1 (by rfl) ⟨642155, by rfl⟩ : syracuseStep 856207 = 1284311) B1284311
theorem B4067729 : Blo 710320 4067729 := bstep (se 2 (by rfl) ⟨1525398, by rfl⟩ : syracuseStep 4067729 = 3050797) B3050797
theorem B1806745 : Blo 710320 1806745 := bstep (se 2 (by rfl) ⟨677529, by rfl⟩ : syracuseStep 1806745 = 1355059) B1355059
theorem B3609035 : Blo 710320 3609035 := bstep (se 1 (by rfl) ⟨2706776, by rfl⟩ : syracuseStep 3609035 = 5413553) B5413553
theorem B1806907 : Blo 710320 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B8131265 : Blo 710320 8131265 := bstep (se 2 (by rfl) ⟨3049224, by rfl⟩ : syracuseStep 8131265 = 6098449) B6098449
theorem B1807049 : Blo 710320 1807049 := bstep (se 2 (by rfl) ⟨677643, by rfl⟩ : syracuseStep 1807049 = 1355287) B1355287
theorem B3609359 : Blo 710320 3609359 := bstep (se 1 (by rfl) ⟨2707019, by rfl⟩ : syracuseStep 3609359 = 5414039) B5414039
theorem B1807393 : Blo 710320 1807393 := bstep (se 2 (by rfl) ⟨677772, by rfl⟩ : syracuseStep 1807393 = 1355545) B1355545
theorem B3249467 : Blo 710320 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B6100433 : Blo 710320 6100433 := bstep (se 2 (by rfl) ⟨2287662, by rfl⟩ : syracuseStep 6100433 = 4575325) B4575325
theorem B2397707 : Blo 710320 2397707 := bstep (se 1 (by rfl) ⟨1798280, by rfl⟩ : syracuseStep 2397707 = 3596561) B3596561
theorem B2397815 : Blo 710320 2397815 := bstep (se 1 (by rfl) ⟨1798361, by rfl⟩ : syracuseStep 2397815 = 3596723) B3596723
theorem B1807991 : Blo 710320 1807991 := bstep (se 1 (by rfl) ⟨1355993, by rfl⟩ : syracuseStep 1807991 = 2711987) B2711987
theorem B5412581 : Blo 710320 5412581 := bstep (se 4 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 5412581 = 1014859) B1014859
theorem B857999 : Blo 710320 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B1349561 : Blo 710320 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B3610817 : Blo 710320 3610817 := bstep (se 2 (by rfl) ⟨1354056, by rfl⟩ : syracuseStep 3610817 = 2708113) B2708113
theorem B2398409 : Blo 710320 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B1710337 : Blo 710320 1710337 := bstep (se 2 (by rfl) ⟨641376, by rfl⟩ : syracuseStep 1710337 = 1282753) B1282753
theorem B17307917 : Blo 710320 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B15374609 : Blo 710320 15374609 := bstep (se 2 (by rfl) ⟨5765478, by rfl⟩ : syracuseStep 15374609 = 11530957) B11530957
theorem B7706897 : Blo 710320 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B2169611 : Blo 710320 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B2399111 : Blo 710320 2399111 := bstep (se 1 (by rfl) ⟨1799333, by rfl⟩ : syracuseStep 2399111 = 3598667) B3598667
theorem B1711115 : Blo 710320 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B2399489 : Blo 710320 2399489 := bstep (se 2 (by rfl) ⟨899808, by rfl⟩ : syracuseStep 2399489 = 1799617) B1799617
theorem B2891009 : Blo 710320 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B18292067 : Blo 710320 18292067 := bstep (se 1 (by rfl) ⟨13719050, by rfl⟩ : syracuseStep 18292067 = 27438101) B27438101
theorem B3612113 : Blo 710320 3612113 := bstep (se 2 (by rfl) ⟨1354542, by rfl⟩ : syracuseStep 3612113 = 2709085) B2709085
theorem B1285751 : Blo 710320 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B1285931 : Blo 710320 1285931 := bstep (se 1 (by rfl) ⟨964448, by rfl⟩ : syracuseStep 1285931 = 1928897) B1928897
theorem B34676525 : Blo 710320 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B991033 : Blo 710320 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B1220411 : Blo 710320 1220411 := bstep (se 1 (by rfl) ⟨915308, by rfl⟩ : syracuseStep 1220411 = 1830617) B1830617
theorem B1351559 : Blo 710320 1351559 := bstep (se 1 (by rfl) ⟨1013669, by rfl⟩ : syracuseStep 1351559 = 2027339) B2027339
theorem B10297367 : Blo 710320 10297367 := bstep (se 1 (by rfl) ⟨7723025, by rfl⟩ : syracuseStep 10297367 = 15446051) B15446051
theorem B2400299 : Blo 710320 2400299 := bstep (se 1 (by rfl) ⟨1800224, by rfl⟩ : syracuseStep 2400299 = 3600449) B3600449
theorem B5775533 : Blo 710320 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B762247 : Blo 710320 762247 := bstep (se 1 (by rfl) ⟨571685, by rfl⟩ : syracuseStep 762247 = 1143371) B1143371
theorem B17375633 : Blo 710320 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B4104715 : Blo 710320 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B4563485 : Blo 710320 4563485 := bstep (se 3 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 4563485 = 1711307) B1711307
theorem B16491073 : Blo 710320 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B58336037 : Blo 710320 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B1713287 : Blo 710320 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B2401595 : Blo 710320 2401595 := bstep (se 1 (by rfl) ⟨1801196, by rfl⟩ : syracuseStep 2401595 = 3602393) B3602393
theorem B1353161 : Blo 710320 1353161 := bstep (se 2 (by rfl) ⟨507435, by rfl⟩ : syracuseStep 1353161 = 1014871) B1014871
theorem B3614219 : Blo 710320 3614219 := bstep (se 1 (by rfl) ⟨2710664, by rfl⟩ : syracuseStep 3614219 = 5421329) B5421329
theorem B3843607 : Blo 710320 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B960059 : Blo 710320 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B3614381 : Blo 710320 3614381 := bstep (se 3 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 3614381 = 1355393) B1355393
theorem B2402081 : Blo 710320 2402081 := bstep (se 2 (by rfl) ⟨900780, by rfl⟩ : syracuseStep 2402081 = 1801561) B1801561
theorem B3418001 : Blo 710320 3418001 := bstep (se 2 (by rfl) ⟨1281750, by rfl⟩ : syracuseStep 3418001 = 2563501) B2563501
theorem B960427 : Blo 710320 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B960697 : Blo 710320 960697 := bstep (se 2 (by rfl) ⟨360261, by rfl⟩ : syracuseStep 960697 = 720523) B720523
theorem B2402675 : Blo 710320 2402675 := bstep (se 1 (by rfl) ⟨1802006, by rfl⟩ : syracuseStep 2402675 = 3604013) B3604013
theorem B928171 : Blo 710320 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B3418691 : Blo 710320 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B5778191 : Blo 710320 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B3091385 : Blo 710320 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B6859799 : Blo 710320 6859799 := bstep (se 1 (by rfl) ⟨5144849, by rfl⟩ : syracuseStep 6859799 = 10289699) B10289699
theorem B8105021 : Blo 710320 8105021 := bstep (se 3 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 8105021 = 3039383) B3039383
theorem B3616001 : Blo 710320 3616001 := bstep (se 2 (by rfl) ⟨1356000, by rfl⟩ : syracuseStep 3616001 = 2712001) B2712001
theorem B1715489 : Blo 710320 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B1355143 : Blo 710320 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B2895421 : Blo 710320 2895421 := bstep (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) B1085783
theorem B2436979 : Blo 710320 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B13709209 : Blo 710320 13709209 := bstep (se 2 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 13709209 = 10281907) B10281907
theorem B2699351 : Blo 710320 2699351 := bstep (se 1 (by rfl) ⟨2024513, by rfl⟩ : syracuseStep 2699351 = 4049027) B4049027
theorem B1519931 : Blo 710320 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B3256691 : Blo 710320 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B2699837 : Blo 710320 2699837 := bstep (se 3 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 2699837 = 1012439) B1012439
theorem B799375 : Blo 710320 799375 := bstep (se 1 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 799375 = 1199063) B1199063
theorem B3420845 : Blo 710320 3420845 := bstep (se 3 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 3420845 = 1282817) B1282817
theorem B2405267 : Blo 710320 2405267 := bstep (se 1 (by rfl) ⟨1803950, by rfl⟩ : syracuseStep 2405267 = 3607901) B3607901
theorem B4568075 : Blo 710320 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B799879 : Blo 710320 799879 := bstep (se 1 (by rfl) ⟨599909, by rfl⟩ : syracuseStep 799879 = 1199819) B1199819
theorem B3421385 : Blo 710320 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B800059 : Blo 710320 800059 := bstep (se 1 (by rfl) ⟨600044, by rfl⟩ : syracuseStep 800059 = 1200089) B1200089
theorem B2569657 : Blo 710320 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B800527 : Blo 710320 800527 := bstep (se 1 (by rfl) ⟨600395, by rfl⟩ : syracuseStep 800527 = 1200791) B1200791
theorem B899191 : Blo 710320 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B801031 : Blo 710320 801031 := bstep (se 1 (by rfl) ⟨600773, by rfl⟩ : syracuseStep 801031 = 1201547) B1201547
theorem B2701583 : Blo 710320 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B2406671 : Blo 710320 2406671 := bstep (se 1 (by rfl) ⟨1805003, by rfl⟩ : syracuseStep 2406671 = 3610007) B3610007
theorem B899515 : Blo 710320 899515 := bstep (se 1 (by rfl) ⟨674636, by rfl⟩ : syracuseStep 899515 = 1349273) B1349273
theorem B801211 : Blo 710320 801211 := bstep (se 1 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 801211 = 1201817) B1201817
theorem B2406941 : Blo 710320 2406941 := bstep (se 3 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 2406941 = 902603) B902603
theorem B2571041 : Blo 710320 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B867191 : Blo 710320 867191 := bstep (se 1 (by rfl) ⟨650393, by rfl⟩ : syracuseStep 867191 = 1300787) B1300787
theorem B801679 : Blo 710320 801679 := bstep (se 1 (by rfl) ⟨601259, by rfl⟩ : syracuseStep 801679 = 1202519) B1202519
theorem B900011 : Blo 710320 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B8207675 : Blo 710320 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B900487 : Blo 710320 900487 := bstep (se 1 (by rfl) ⟨675365, by rfl⟩ : syracuseStep 900487 = 1350731) B1350731
theorem B802183 : Blo 710320 802183 := bstep (se 1 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 802183 = 1203275) B1203275
theorem B802363 : Blo 710320 802363 := bstep (se 1 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 802363 = 1203545) B1203545
theorem B11550539 : Blo 710320 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B900983 : Blo 710320 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B2703239 : Blo 710320 2703239 := bstep (se 1 (by rfl) ⟨2027429, by rfl⟩ : syracuseStep 2703239 = 4054859) B4054859
theorem B2408345 : Blo 710320 2408345 := bstep (se 2 (by rfl) ⟨903129, by rfl⟩ : syracuseStep 2408345 = 1806259) B1806259
theorem B901135 : Blo 710320 901135 := bstep (se 1 (by rfl) ⟨675851, by rfl⟩ : syracuseStep 901135 = 1351703) B1351703
theorem B802831 : Blo 710320 802831 := bstep (se 1 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 802831 = 1204247) B1204247
theorem B901307 : Blo 710320 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B3948851 : Blo 710320 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B803335 : Blo 710320 803335 := bstep (se 1 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 803335 = 1205003) B1205003
theorem B3654173 : Blo 710320 3654173 := bstep (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) B1370315
theorem B1065515 : Blo 710320 1065515 := bstep (se 1 (by rfl) ⟨799136, by rfl⟩ : syracuseStep 1065515 = 1598273) B1598273
theorem B4112963 : Blo 710320 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B1065545 : Blo 710320 1065545 := bstep (se 2 (by rfl) ⟨399579, by rfl⟩ : syracuseStep 1065545 = 799159) B799159
theorem B2409047 : Blo 710320 2409047 := bstep (se 1 (by rfl) ⟨1806785, by rfl⟩ : syracuseStep 2409047 = 3613571) B3613571
theorem B1065659 : Blo 710320 1065659 := bstep (se 1 (by rfl) ⟨799244, by rfl⟩ : syracuseStep 1065659 = 1598489) B1598489
theorem B803515 : Blo 710320 803515 := bstep (se 1 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 803515 = 1205273) B1205273
theorem B1065719 : Blo 710320 1065719 := bstep (se 1 (by rfl) ⟨799289, by rfl⟩ : syracuseStep 1065719 = 1598579) B1598579
theorem B1065743 : Blo 710320 1065743 := bstep (se 1 (by rfl) ⟨799307, by rfl⟩ : syracuseStep 1065743 = 1598615) B1598615
theorem B3425075 : Blo 710320 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B1065785 : Blo 710320 1065785 := bstep (se 2 (by rfl) ⟨399669, by rfl⟩ : syracuseStep 1065785 = 799339) B799339
theorem B1065863 : Blo 710320 1065863 := bstep (se 1 (by rfl) ⟨799397, by rfl⟩ : syracuseStep 1065863 = 1598795) B1598795
theorem B1065899 : Blo 710320 1065899 := bstep (se 1 (by rfl) ⟨799424, by rfl⟩ : syracuseStep 1065899 = 1598849) B1598849
theorem B1065929 : Blo 710320 1065929 := bstep (se 2 (by rfl) ⟨399723, by rfl⟩ : syracuseStep 1065929 = 799447) B799447
theorem B1066043 : Blo 710320 1066043 := bstep (se 1 (by rfl) ⟨799532, by rfl⟩ : syracuseStep 1066043 = 1599065) B1599065
theorem B2409533 : Blo 710320 2409533 := bstep (se 3 (by rfl) ⟨451787, by rfl⟩ : syracuseStep 2409533 = 903575) B903575
theorem B1066103 : Blo 710320 1066103 := bstep (se 1 (by rfl) ⟨799577, by rfl⟩ : syracuseStep 1066103 = 1599155) B1599155
theorem B902279 : Blo 710320 902279 := bstep (se 1 (by rfl) ⟨676709, by rfl⟩ : syracuseStep 902279 = 1353419) B1353419
theorem B1066127 : Blo 710320 1066127 := bstep (se 1 (by rfl) ⟨799595, by rfl⟩ : syracuseStep 1066127 = 1599191) B1599191
theorem B1066169 : Blo 710320 1066169 := bstep (se 2 (by rfl) ⟨399813, by rfl⟩ : syracuseStep 1066169 = 799627) B799627
theorem B1066247 : Blo 710320 1066247 := bstep (se 1 (by rfl) ⟨799685, by rfl⟩ : syracuseStep 1066247 = 1599371) B1599371
theorem B1066283 : Blo 710320 1066283 := bstep (se 1 (by rfl) ⟨799712, by rfl⟩ : syracuseStep 1066283 = 1599425) B1599425
theorem B1066313 : Blo 710320 1066313 := bstep (se 2 (by rfl) ⟨399867, by rfl⟩ : syracuseStep 1066313 = 799735) B799735
theorem B1066427 : Blo 710320 1066427 := bstep (se 1 (by rfl) ⟨799820, by rfl⟩ : syracuseStep 1066427 = 1599641) B1599641
theorem B1066487 : Blo 710320 1066487 := bstep (se 1 (by rfl) ⟨799865, by rfl⟩ : syracuseStep 1066487 = 1599731) B1599731
theorem B1066511 : Blo 710320 1066511 := bstep (se 1 (by rfl) ⟨799883, by rfl⟩ : syracuseStep 1066511 = 1599767) B1599767
theorem B1066553 : Blo 710320 1066553 := bstep (se 2 (by rfl) ⟨399957, by rfl⟩ : syracuseStep 1066553 = 799915) B799915
theorem B2705015 : Blo 710320 2705015 := bstep (se 1 (by rfl) ⟨2028761, by rfl⟩ : syracuseStep 2705015 = 4057523) B4057523
theorem B1066631 : Blo 710320 1066631 := bstep (se 1 (by rfl) ⟨799973, by rfl⟩ : syracuseStep 1066631 = 1599947) B1599947
theorem B1066667 : Blo 710320 1066667 := bstep (se 1 (by rfl) ⟨800000, by rfl⟩ : syracuseStep 1066667 = 1600001) B1600001
theorem B1066697 : Blo 710320 1066697 := bstep (se 2 (by rfl) ⟨400011, by rfl⟩ : syracuseStep 1066697 = 800023) B800023
theorem B902927 : Blo 710320 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B1066811 : Blo 710320 1066811 := bstep (se 1 (by rfl) ⟨800108, by rfl⟩ : syracuseStep 1066811 = 1600217) B1600217
theorem B1066871 : Blo 710320 1066871 := bstep (se 1 (by rfl) ⟨800153, by rfl⟩ : syracuseStep 1066871 = 1600307) B1600307
theorem B4048775 : Blo 710320 4048775 := bstep (se 1 (by rfl) ⟨3036581, by rfl⟩ : syracuseStep 4048775 = 6073163) B6073163
theorem B1066895 : Blo 710320 1066895 := bstep (se 1 (by rfl) ⟨800171, by rfl⟩ : syracuseStep 1066895 = 1600343) B1600343
theorem B1066937 : Blo 710320 1066937 := bstep (se 2 (by rfl) ⟨400101, by rfl⟩ : syracuseStep 1066937 = 800203) B800203
theorem B1067015 : Blo 710320 1067015 := bstep (se 1 (by rfl) ⟨800261, by rfl⟩ : syracuseStep 1067015 = 1600523) B1600523
theorem B1067051 : Blo 710320 1067051 := bstep (se 1 (by rfl) ⟨800288, by rfl⟩ : syracuseStep 1067051 = 1600577) B1600577
theorem B1067081 : Blo 710320 1067081 := bstep (se 2 (by rfl) ⟨400155, by rfl⟩ : syracuseStep 1067081 = 800311) B800311
theorem B1067195 : Blo 710320 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B12503285 : Blo 710320 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B1067255 : Blo 710320 1067255 := bstep (se 1 (by rfl) ⟨800441, by rfl⟩ : syracuseStep 1067255 = 1600883) B1600883
theorem B1067279 : Blo 710320 1067279 := bstep (se 1 (by rfl) ⟨800459, by rfl⟩ : syracuseStep 1067279 = 1600919) B1600919
theorem B1067321 : Blo 710320 1067321 := bstep (se 2 (by rfl) ⟨400245, by rfl⟩ : syracuseStep 1067321 = 800491) B800491
theorem B1067399 : Blo 710320 1067399 := bstep (se 1 (by rfl) ⟨800549, by rfl⟩ : syracuseStep 1067399 = 1601099) B1601099
theorem B1067435 : Blo 710320 1067435 := bstep (se 1 (by rfl) ⟨800576, by rfl⟩ : syracuseStep 1067435 = 1601153) B1601153
theorem B6834617 : Blo 710320 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B6080953 : Blo 710320 6080953 := bstep (se 2 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 6080953 = 4560715) B4560715
theorem B1067465 : Blo 710320 1067465 := bstep (se 2 (by rfl) ⟨400299, by rfl⟩ : syracuseStep 1067465 = 800599) B800599
theorem B1067579 : Blo 710320 1067579 := bstep (se 1 (by rfl) ⟨800684, by rfl⟩ : syracuseStep 1067579 = 1601369) B1601369
theorem B23382593 : Blo 710320 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B2705987 : Blo 710320 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B1067639 : Blo 710320 1067639 := bstep (se 1 (by rfl) ⟨800729, by rfl⟩ : syracuseStep 1067639 = 1601459) B1601459
theorem B1067663 : Blo 710320 1067663 := bstep (se 1 (by rfl) ⟨800747, by rfl⟩ : syracuseStep 1067663 = 1601495) B1601495
theorem B1067705 : Blo 710320 1067705 := bstep (se 2 (by rfl) ⟨400389, by rfl⟩ : syracuseStep 1067705 = 800779) B800779
theorem B1198793 : Blo 710320 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B1067783 : Blo 710320 1067783 := bstep (se 1 (by rfl) ⟨800837, by rfl⟩ : syracuseStep 1067783 = 1601675) B1601675
theorem B3296015 : Blo 710320 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B1067819 : Blo 710320 1067819 := bstep (se 1 (by rfl) ⟨800864, by rfl⟩ : syracuseStep 1067819 = 1601729) B1601729
theorem B1067849 : Blo 710320 1067849 := bstep (se 2 (by rfl) ⟨400443, by rfl⟩ : syracuseStep 1067849 = 800887) B800887
theorem B5131097 : Blo 710320 5131097 := bstep (se 2 (by rfl) ⟨1924161, by rfl⟩ : syracuseStep 5131097 = 3848323) B3848323
theorem B2280307 : Blo 710320 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B1067963 : Blo 710320 1067963 := bstep (se 1 (by rfl) ⟨800972, by rfl⟩ : syracuseStep 1067963 = 1601945) B1601945
theorem B1068023 : Blo 710320 1068023 := bstep (se 1 (by rfl) ⟨801017, by rfl⟩ : syracuseStep 1068023 = 1602035) B1602035
theorem B14797835 : Blo 710320 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B2706443 : Blo 710320 2706443 := bstep (se 1 (by rfl) ⟨2029832, by rfl⟩ : syracuseStep 2706443 = 4059665) B4059665
theorem B1068047 : Blo 710320 1068047 := bstep (se 1 (by rfl) ⟨801035, by rfl⟩ : syracuseStep 1068047 = 1602071) B1602071
theorem B1068089 : Blo 710320 1068089 := bstep (se 2 (by rfl) ⟨400533, by rfl⟩ : syracuseStep 1068089 = 801067) B801067
theorem B1068167 : Blo 710320 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B1068203 : Blo 710320 1068203 := bstep (se 1 (by rfl) ⟨801152, by rfl⟩ : syracuseStep 1068203 = 1602305) B1602305
theorem B1068233 : Blo 710320 1068233 := bstep (se 2 (by rfl) ⟨400587, by rfl⟩ : syracuseStep 1068233 = 801175) B801175
theorem B1068347 : Blo 710320 1068347 := bstep (se 1 (by rfl) ⟨801260, by rfl⟩ : syracuseStep 1068347 = 1602521) B1602521
theorem B1068407 : Blo 710320 1068407 := bstep (se 1 (by rfl) ⟨801305, by rfl⟩ : syracuseStep 1068407 = 1602611) B1602611
theorem B1199495 : Blo 710320 1199495 := bstep (se 1 (by rfl) ⟨899621, by rfl⟩ : syracuseStep 1199495 = 1799243) B1799243
theorem B1068431 : Blo 710320 1068431 := bstep (se 1 (by rfl) ⟨801323, by rfl⟩ : syracuseStep 1068431 = 1602647) B1602647
theorem B1068473 : Blo 710320 1068473 := bstep (se 2 (by rfl) ⟨400677, by rfl⟩ : syracuseStep 1068473 = 801355) B801355
theorem B1068551 : Blo 710320 1068551 := bstep (se 1 (by rfl) ⟨801413, by rfl⟩ : syracuseStep 1068551 = 1602827) B1602827
theorem B2051617 : Blo 710320 2051617 := bstep (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) B1538713
theorem B1068587 : Blo 710320 1068587 := bstep (se 1 (by rfl) ⟨801440, by rfl⟩ : syracuseStep 1068587 = 1602881) B1602881
theorem B4017725 : Blo 710320 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B1068617 : Blo 710320 1068617 := bstep (se 2 (by rfl) ⟨400731, by rfl⟩ : syracuseStep 1068617 = 801463) B801463
theorem B13684301 : Blo 710320 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B1625719 : Blo 710320 1625719 := bstep (se 1 (by rfl) ⟨1219289, by rfl⟩ : syracuseStep 1625719 = 2438579) B2438579
theorem B4574839 : Blo 710320 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B1461907 : Blo 710320 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B1068731 : Blo 710320 1068731 := bstep (se 1 (by rfl) ⟨801548, by rfl⟩ : syracuseStep 1068731 = 1603097) B1603097
theorem B5394113 : Blo 710320 5394113 := bstep (se 2 (by rfl) ⟨2022792, by rfl⟩ : syracuseStep 5394113 = 4045585) B4045585
theorem B1068791 : Blo 710320 1068791 := bstep (se 1 (by rfl) ⟨801593, by rfl⟩ : syracuseStep 1068791 = 1603187) B1603187
theorem B1068815 : Blo 710320 1068815 := bstep (se 1 (by rfl) ⟨801611, by rfl⟩ : syracuseStep 1068815 = 1603223) B1603223
theorem B3460897 : Blo 710320 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B1068857 : Blo 710320 1068857 := bstep (se 2 (by rfl) ⟨400821, by rfl⟩ : syracuseStep 1068857 = 801643) B801643
theorem B1068935 : Blo 710320 1068935 := bstep (se 1 (by rfl) ⟨801701, by rfl⟩ : syracuseStep 1068935 = 1603403) B1603403
theorem B1068971 : Blo 710320 1068971 := bstep (se 1 (by rfl) ⟨801728, by rfl⟩ : syracuseStep 1068971 = 1603457) B1603457
theorem B1069001 : Blo 710320 1069001 := bstep (se 2 (by rfl) ⟨400875, by rfl⟩ : syracuseStep 1069001 = 801751) B801751
theorem B1200143 : Blo 710320 1200143 := bstep (se 1 (by rfl) ⟨900107, by rfl⟩ : syracuseStep 1200143 = 1800215) B1800215
theorem B1069115 : Blo 710320 1069115 := bstep (se 1 (by rfl) ⟨801836, by rfl⟩ : syracuseStep 1069115 = 1603673) B1603673
theorem B3428419 : Blo 710320 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B1069175 : Blo 710320 1069175 := bstep (se 1 (by rfl) ⟨801881, by rfl⟩ : syracuseStep 1069175 = 1603763) B1603763
theorem B1069199 : Blo 710320 1069199 := bstep (se 1 (by rfl) ⟨801899, by rfl⟩ : syracuseStep 1069199 = 1603799) B1603799
theorem B1069241 : Blo 710320 1069241 := bstep (se 2 (by rfl) ⟨400965, by rfl⟩ : syracuseStep 1069241 = 801931) B801931
theorem B1069319 : Blo 710320 1069319 := bstep (se 1 (by rfl) ⟨801989, by rfl⟩ : syracuseStep 1069319 = 1603979) B1603979
theorem B1069355 : Blo 710320 1069355 := bstep (se 1 (by rfl) ⟨802016, by rfl⟩ : syracuseStep 1069355 = 1604033) B1604033
theorem B1069385 : Blo 710320 1069385 := bstep (se 2 (by rfl) ⟨401019, by rfl⟩ : syracuseStep 1069385 = 802039) B802039
theorem B1069499 : Blo 710320 1069499 := bstep (se 1 (by rfl) ⟨802124, by rfl⟩ : syracuseStep 1069499 = 1604249) B1604249
theorem B1069559 : Blo 710320 1069559 := bstep (se 1 (by rfl) ⟨802169, by rfl⟩ : syracuseStep 1069559 = 1604339) B1604339
theorem B1069583 : Blo 710320 1069583 := bstep (se 1 (by rfl) ⟨802187, by rfl⟩ : syracuseStep 1069583 = 1604375) B1604375
theorem B3035677 : Blo 710320 3035677 := bstep (se 3 (by rfl) ⟨569189, by rfl⟩ : syracuseStep 3035677 = 1138379) B1138379
theorem B1200683 : Blo 710320 1200683 := bstep (se 1 (by rfl) ⟨900512, by rfl⟩ : syracuseStep 1200683 = 1801025) B1801025
theorem B1069625 : Blo 710320 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B1069703 : Blo 710320 1069703 := bstep (se 1 (by rfl) ⟨802277, by rfl⟩ : syracuseStep 1069703 = 1604555) B1604555
theorem B1069739 : Blo 710320 1069739 := bstep (se 1 (by rfl) ⟨802304, by rfl⟩ : syracuseStep 1069739 = 1604609) B1604609
theorem B1069769 : Blo 710320 1069769 := bstep (se 2 (by rfl) ⟨401163, by rfl⟩ : syracuseStep 1069769 = 802327) B802327
theorem B4117229 : Blo 710320 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B1069883 : Blo 710320 1069883 := bstep (se 1 (by rfl) ⟨802412, by rfl⟩ : syracuseStep 1069883 = 1604825) B1604825
theorem B1069943 : Blo 710320 1069943 := bstep (se 1 (by rfl) ⟨802457, by rfl⟩ : syracuseStep 1069943 = 1604915) B1604915
theorem B1069967 : Blo 710320 1069967 := bstep (se 1 (by rfl) ⟨802475, by rfl⟩ : syracuseStep 1069967 = 1604951) B1604951
theorem B6837155 : Blo 710320 6837155 := bstep (se 1 (by rfl) ⟨5127866, by rfl⟩ : syracuseStep 6837155 = 10255733) B10255733
theorem B1201081 : Blo 710320 1201081 := bstep (se 2 (by rfl) ⟨450405, by rfl⟩ : syracuseStep 1201081 = 900811) B900811
theorem B1070009 : Blo 710320 1070009 := bstep (se 2 (by rfl) ⟨401253, by rfl⟩ : syracuseStep 1070009 = 802507) B802507
theorem B1070087 : Blo 710320 1070087 := bstep (se 1 (by rfl) ⟨802565, by rfl⟩ : syracuseStep 1070087 = 1605131) B1605131
theorem B1070123 : Blo 710320 1070123 := bstep (se 1 (by rfl) ⟨802592, by rfl⟩ : syracuseStep 1070123 = 1605185) B1605185
theorem B1070153 : Blo 710320 1070153 := bstep (se 2 (by rfl) ⟨401307, by rfl⟩ : syracuseStep 1070153 = 802615) B802615
theorem B2708599 : Blo 710320 2708599 := bstep (se 1 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 2708599 = 4062899) B4062899
theorem B1070267 : Blo 710320 1070267 := bstep (se 1 (by rfl) ⟨802700, by rfl⟩ : syracuseStep 1070267 = 1605401) B1605401
theorem B1070327 : Blo 710320 1070327 := bstep (se 1 (by rfl) ⟨802745, by rfl⟩ : syracuseStep 1070327 = 1605491) B1605491
theorem B1070351 : Blo 710320 1070351 := bstep (se 1 (by rfl) ⟨802763, by rfl⟩ : syracuseStep 1070351 = 1605527) B1605527
theorem B1070393 : Blo 710320 1070393 := bstep (se 2 (by rfl) ⟨401397, by rfl⟩ : syracuseStep 1070393 = 802795) B802795
theorem B1070471 : Blo 710320 1070471 := bstep (se 1 (by rfl) ⟨802853, by rfl⟩ : syracuseStep 1070471 = 1605707) B1605707
theorem B1070507 : Blo 710320 1070507 := bstep (se 1 (by rfl) ⟨802880, by rfl⟩ : syracuseStep 1070507 = 1605761) B1605761
theorem B1070537 : Blo 710320 1070537 := bstep (se 2 (by rfl) ⟨401451, by rfl⟩ : syracuseStep 1070537 = 802903) B802903
theorem B1070651 : Blo 710320 1070651 := bstep (se 1 (by rfl) ⟨802988, by rfl⟩ : syracuseStep 1070651 = 1605977) B1605977
theorem B1758835 : Blo 710320 1758835 := bstep (se 1 (by rfl) ⟨1319126, by rfl⟩ : syracuseStep 1758835 = 2638253) B2638253
theorem B1201783 : Blo 710320 1201783 := bstep (se 1 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 1201783 = 1802675) B1802675
theorem B1070711 : Blo 710320 1070711 := bstep (se 1 (by rfl) ⟨803033, by rfl⟩ : syracuseStep 1070711 = 1606067) B1606067
theorem B1070735 : Blo 710320 1070735 := bstep (se 1 (by rfl) ⟨803051, by rfl⟩ : syracuseStep 1070735 = 1606103) B1606103
theorem B1070777 : Blo 710320 1070777 := bstep (se 2 (by rfl) ⟨401541, by rfl⟩ : syracuseStep 1070777 = 803083) B803083
theorem B710331 : Blo 710320 710331 := bstep (se 1 (by rfl) ⟨532748, by rfl⟩ : syracuseStep 710331 = 1065497) B1065497
theorem B710407 : Blo 710320 710407 := bstep (se 1 (by rfl) ⟨532805, by rfl⟩ : syracuseStep 710407 = 1065611) B1065611
theorem B1070855 : Blo 710320 1070855 := bstep (se 1 (by rfl) ⟨803141, by rfl⟩ : syracuseStep 1070855 = 1606283) B1606283
theorem B710415 : Blo 710320 710415 := bstep (se 1 (by rfl) ⟨532811, by rfl⟩ : syracuseStep 710415 = 1065623) B1065623
theorem B1070891 : Blo 710320 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B710459 : Blo 710320 710459 := bstep (se 1 (by rfl) ⟨532844, by rfl⟩ : syracuseStep 710459 = 1065689) B1065689
theorem B1201979 : Blo 710320 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B1070921 : Blo 710320 1070921 := bstep (se 2 (by rfl) ⟨401595, by rfl⟩ : syracuseStep 1070921 = 803191) B803191
theorem B710535 : Blo 710320 710535 := bstep (se 1 (by rfl) ⟨532901, by rfl⟩ : syracuseStep 710535 = 1065803) B1065803
theorem B710543 : Blo 710320 710543 := bstep (se 1 (by rfl) ⟨532907, by rfl⟩ : syracuseStep 710543 = 1065815) B1065815
theorem B7329689 : Blo 710320 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B710587 : Blo 710320 710587 := bstep (se 1 (by rfl) ⟨532940, by rfl⟩ : syracuseStep 710587 = 1065881) B1065881
theorem B1071035 : Blo 710320 1071035 := bstep (se 1 (by rfl) ⟨803276, by rfl⟩ : syracuseStep 1071035 = 1606553) B1606553
theorem B1071095 : Blo 710320 1071095 := bstep (se 1 (by rfl) ⟨803321, by rfl⟩ : syracuseStep 1071095 = 1606643) B1606643
theorem B710663 : Blo 710320 710663 := bstep (se 1 (by rfl) ⟨532997, by rfl⟩ : syracuseStep 710663 = 1065995) B1065995
theorem B710671 : Blo 710320 710671 := bstep (se 1 (by rfl) ⟨533003, by rfl⟩ : syracuseStep 710671 = 1066007) B1066007
theorem B1071119 : Blo 710320 1071119 := bstep (se 1 (by rfl) ⟨803339, by rfl⟩ : syracuseStep 1071119 = 1606679) B1606679
theorem B1071161 : Blo 710320 1071161 := bstep (se 2 (by rfl) ⟨401685, by rfl⟩ : syracuseStep 1071161 = 803371) B803371
theorem B710715 : Blo 710320 710715 := bstep (se 1 (by rfl) ⟨533036, by rfl⟩ : syracuseStep 710715 = 1066073) B1066073
theorem B2709571 : Blo 710320 2709571 := bstep (se 1 (by rfl) ⟨2032178, by rfl⟩ : syracuseStep 2709571 = 4064357) B4064357
theorem B710791 : Blo 710320 710791 := bstep (se 1 (by rfl) ⟨533093, by rfl⟩ : syracuseStep 710791 = 1066187) B1066187
theorem B1071239 : Blo 710320 1071239 := bstep (se 1 (by rfl) ⟨803429, by rfl⟩ : syracuseStep 1071239 = 1606859) B1606859
theorem B710799 : Blo 710320 710799 := bstep (se 1 (by rfl) ⟨533099, by rfl⟩ : syracuseStep 710799 = 1066199) B1066199
theorem B1071275 : Blo 710320 1071275 := bstep (se 1 (by rfl) ⟨803456, by rfl⟩ : syracuseStep 1071275 = 1606913) B1606913
theorem B710843 : Blo 710320 710843 := bstep (se 1 (by rfl) ⟨533132, by rfl⟩ : syracuseStep 710843 = 1066265) B1066265
theorem B1202377 : Blo 710320 1202377 := bstep (se 2 (by rfl) ⟨450891, by rfl⟩ : syracuseStep 1202377 = 901783) B901783
theorem B1071305 : Blo 710320 1071305 := bstep (se 2 (by rfl) ⟨401739, by rfl⟩ : syracuseStep 1071305 = 803479) B803479
theorem B710919 : Blo 710320 710919 := bstep (se 1 (by rfl) ⟨533189, by rfl⟩ : syracuseStep 710919 = 1066379) B1066379
theorem B710927 : Blo 710320 710927 := bstep (se 1 (by rfl) ⟨533195, by rfl⟩ : syracuseStep 710927 = 1066391) B1066391
theorem B710971 : Blo 710320 710971 := bstep (se 1 (by rfl) ⟨533228, by rfl⟩ : syracuseStep 710971 = 1066457) B1066457
theorem B1071419 : Blo 710320 1071419 := bstep (se 1 (by rfl) ⟨803564, by rfl⟩ : syracuseStep 1071419 = 1607129) B1607129
theorem B2709875 : Blo 710320 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B1071479 : Blo 710320 1071479 := bstep (se 1 (by rfl) ⟨803609, by rfl⟩ : syracuseStep 1071479 = 1607219) B1607219
theorem B711047 : Blo 710320 711047 := bstep (se 1 (by rfl) ⟨533285, by rfl⟩ : syracuseStep 711047 = 1066571) B1066571
theorem B5134727 : Blo 710320 5134727 := bstep (se 1 (by rfl) ⟨3851045, by rfl⟩ : syracuseStep 5134727 = 7702091) B7702091
theorem B3660167 : Blo 710320 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B711055 : Blo 710320 711055 := bstep (se 1 (by rfl) ⟨533291, by rfl⟩ : syracuseStep 711055 = 1066583) B1066583
theorem B4053401 : Blo 710320 4053401 := bstep (se 2 (by rfl) ⟨1520025, by rfl⟩ : syracuseStep 4053401 = 3040051) B3040051
theorem B711099 : Blo 710320 711099 := bstep (se 1 (by rfl) ⟨533324, by rfl⟩ : syracuseStep 711099 = 1066649) B1066649
theorem B8116685 : Blo 710320 8116685 := bstep (se 3 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 8116685 = 3043757) B3043757
theorem B711175 : Blo 710320 711175 := bstep (se 1 (by rfl) ⟨533381, by rfl⟩ : syracuseStep 711175 = 1066763) B1066763
theorem B711183 : Blo 710320 711183 := bstep (se 1 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 711183 = 1066775) B1066775
theorem B711227 : Blo 710320 711227 := bstep (se 1 (by rfl) ⟨533420, by rfl⟩ : syracuseStep 711227 = 1066841) B1066841
theorem B9230915 : Blo 710320 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B711303 : Blo 710320 711303 := bstep (se 1 (by rfl) ⟨533477, by rfl⟩ : syracuseStep 711303 = 1066955) B1066955
theorem B711311 : Blo 710320 711311 := bstep (se 1 (by rfl) ⟨533483, by rfl⟩ : syracuseStep 711311 = 1066967) B1066967
theorem B711355 : Blo 710320 711355 := bstep (se 1 (by rfl) ⟨533516, by rfl⟩ : syracuseStep 711355 = 1067033) B1067033
theorem B711431 : Blo 710320 711431 := bstep (se 1 (by rfl) ⟨533573, by rfl⟩ : syracuseStep 711431 = 1067147) B1067147
theorem B711439 : Blo 710320 711439 := bstep (se 1 (by rfl) ⟨533579, by rfl⟩ : syracuseStep 711439 = 1067159) B1067159
theorem B711483 : Blo 710320 711483 := bstep (se 1 (by rfl) ⟨533612, by rfl⟩ : syracuseStep 711483 = 1067225) B1067225
theorem B2710331 : Blo 710320 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B711559 : Blo 710320 711559 := bstep (se 1 (by rfl) ⟨533669, by rfl⟩ : syracuseStep 711559 = 1067339) B1067339
theorem B1203079 : Blo 710320 1203079 := bstep (se 1 (by rfl) ⟨902309, by rfl⟩ : syracuseStep 1203079 = 1804619) B1804619
theorem B711567 : Blo 710320 711567 := bstep (se 1 (by rfl) ⟨533675, by rfl⟩ : syracuseStep 711567 = 1067351) B1067351
theorem B711611 : Blo 710320 711611 := bstep (se 1 (by rfl) ⟨533708, by rfl⟩ : syracuseStep 711611 = 1067417) B1067417
theorem B711687 : Blo 710320 711687 := bstep (se 1 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 711687 = 1067531) B1067531
theorem B5397515 : Blo 710320 5397515 := bstep (se 1 (by rfl) ⟨4048136, by rfl⟩ : syracuseStep 5397515 = 8096273) B8096273
theorem B711695 : Blo 710320 711695 := bstep (se 1 (by rfl) ⟨533771, by rfl⟩ : syracuseStep 711695 = 1067543) B1067543
theorem B1924139 : Blo 710320 1924139 := bstep (se 1 (by rfl) ⟨1443104, by rfl⟩ : syracuseStep 1924139 = 2886209) B2886209
theorem B711739 : Blo 710320 711739 := bstep (se 1 (by rfl) ⟨533804, by rfl⟩ : syracuseStep 711739 = 1067609) B1067609
theorem B711815 : Blo 710320 711815 := bstep (se 1 (by rfl) ⟨533861, by rfl⟩ : syracuseStep 711815 = 1067723) B1067723
theorem B711823 : Blo 710320 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B711867 : Blo 710320 711867 := bstep (se 1 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 711867 = 1067801) B1067801
theorem B711943 : Blo 710320 711943 := bstep (se 1 (by rfl) ⟨533957, by rfl⟩ : syracuseStep 711943 = 1067915) B1067915
theorem B711951 : Blo 710320 711951 := bstep (se 1 (by rfl) ⟨533963, by rfl⟩ : syracuseStep 711951 = 1067927) B1067927
theorem B2710817 : Blo 710320 2710817 := bstep (se 2 (by rfl) ⟨1016556, by rfl⟩ : syracuseStep 2710817 = 2033113) B2033113
theorem B711995 : Blo 710320 711995 := bstep (se 1 (by rfl) ⟨533996, by rfl⟩ : syracuseStep 711995 = 1067993) B1067993
theorem B712071 : Blo 710320 712071 := bstep (se 1 (by rfl) ⟨534053, by rfl⟩ : syracuseStep 712071 = 1068107) B1068107
theorem B712079 : Blo 710320 712079 := bstep (se 1 (by rfl) ⟨534059, by rfl⟩ : syracuseStep 712079 = 1068119) B1068119
theorem B712123 : Blo 710320 712123 := bstep (se 1 (by rfl) ⟨534092, by rfl⟩ : syracuseStep 712123 = 1068185) B1068185
theorem B98557397 : Blo 710320 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B712199 : Blo 710320 712199 := bstep (se 1 (by rfl) ⟨534149, by rfl⟩ : syracuseStep 712199 = 1068299) B1068299
theorem B712207 : Blo 710320 712207 := bstep (se 1 (by rfl) ⟨534155, by rfl⟩ : syracuseStep 712207 = 1068311) B1068311
theorem B1203727 : Blo 710320 1203727 := bstep (se 1 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 1203727 = 1805591) B1805591
theorem B712251 : Blo 710320 712251 := bstep (se 1 (by rfl) ⟨534188, by rfl⟩ : syracuseStep 712251 = 1068377) B1068377
theorem B13655627 : Blo 710320 13655627 := bstep (se 1 (by rfl) ⟨10241720, by rfl⟩ : syracuseStep 13655627 = 20483441) B20483441
theorem B4120183 : Blo 710320 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B712327 : Blo 710320 712327 := bstep (se 1 (by rfl) ⟨534245, by rfl⟩ : syracuseStep 712327 = 1068491) B1068491
theorem B712335 : Blo 710320 712335 := bstep (se 1 (by rfl) ⟨534251, by rfl⟩ : syracuseStep 712335 = 1068503) B1068503
theorem B712379 : Blo 710320 712379 := bstep (se 1 (by rfl) ⟨534284, by rfl⟩ : syracuseStep 712379 = 1068569) B1068569
theorem B712455 : Blo 710320 712455 := bstep (se 1 (by rfl) ⟨534341, by rfl⟩ : syracuseStep 712455 = 1068683) B1068683
theorem B712463 : Blo 710320 712463 := bstep (se 1 (by rfl) ⟨534347, by rfl⟩ : syracuseStep 712463 = 1068695) B1068695
theorem B712507 : Blo 710320 712507 := bstep (se 1 (by rfl) ⟨534380, by rfl⟩ : syracuseStep 712507 = 1068761) B1068761
theorem B712583 : Blo 710320 712583 := bstep (se 1 (by rfl) ⟨534437, by rfl⟩ : syracuseStep 712583 = 1068875) B1068875
theorem B712591 : Blo 710320 712591 := bstep (se 1 (by rfl) ⟨534443, by rfl⟩ : syracuseStep 712591 = 1068887) B1068887
theorem B712635 : Blo 710320 712635 := bstep (se 1 (by rfl) ⟨534476, by rfl⟩ : syracuseStep 712635 = 1068953) B1068953
theorem B712711 : Blo 710320 712711 := bstep (se 1 (by rfl) ⟨534533, by rfl⟩ : syracuseStep 712711 = 1069067) B1069067
theorem B712719 : Blo 710320 712719 := bstep (se 1 (by rfl) ⟨534539, by rfl⟩ : syracuseStep 712719 = 1069079) B1069079
theorem B1204267 : Blo 710320 1204267 := bstep (se 1 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 1204267 = 1806401) B1806401
theorem B712763 : Blo 710320 712763 := bstep (se 1 (by rfl) ⟨534572, by rfl⟩ : syracuseStep 712763 = 1069145) B1069145
theorem B712839 : Blo 710320 712839 := bstep (se 1 (by rfl) ⟨534629, by rfl⟩ : syracuseStep 712839 = 1069259) B1069259
theorem B712847 : Blo 710320 712847 := bstep (se 1 (by rfl) ⟨534635, by rfl⟩ : syracuseStep 712847 = 1069271) B1069271
theorem B1204409 : Blo 710320 1204409 := bstep (se 2 (by rfl) ⟨451653, by rfl⟩ : syracuseStep 1204409 = 903307) B903307
theorem B712891 : Blo 710320 712891 := bstep (se 1 (by rfl) ⟨534668, by rfl⟩ : syracuseStep 712891 = 1069337) B1069337
theorem B2711789 : Blo 710320 2711789 := bstep (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) B1016921
theorem B712967 : Blo 710320 712967 := bstep (se 1 (by rfl) ⟨534725, by rfl⟩ : syracuseStep 712967 = 1069451) B1069451
theorem B712975 : Blo 710320 712975 := bstep (se 1 (by rfl) ⟨534731, by rfl⟩ : syracuseStep 712975 = 1069463) B1069463
theorem B713019 : Blo 710320 713019 := bstep (se 1 (by rfl) ⟨534764, by rfl⟩ : syracuseStep 713019 = 1069529) B1069529
theorem B2023795 : Blo 710320 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B713095 : Blo 710320 713095 := bstep (se 1 (by rfl) ⟨534821, by rfl⟩ : syracuseStep 713095 = 1069643) B1069643
theorem B713103 : Blo 710320 713103 := bstep (se 1 (by rfl) ⟨534827, by rfl⟩ : syracuseStep 713103 = 1069655) B1069655
theorem B713147 : Blo 710320 713147 := bstep (se 1 (by rfl) ⟨534860, by rfl⟩ : syracuseStep 713147 = 1069721) B1069721
theorem B11887069 : Blo 710320 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B713223 : Blo 710320 713223 := bstep (se 1 (by rfl) ⟨534917, by rfl⟩ : syracuseStep 713223 = 1069835) B1069835
theorem B713231 : Blo 710320 713231 := bstep (se 1 (by rfl) ⟨534923, by rfl⟩ : syracuseStep 713231 = 1069847) B1069847
theorem B713275 : Blo 710320 713275 := bstep (se 1 (by rfl) ⟨534956, by rfl⟩ : syracuseStep 713275 = 1069913) B1069913
theorem B2024023 : Blo 710320 2024023 := bstep (se 1 (by rfl) ⟨1518017, by rfl⟩ : syracuseStep 2024023 = 3036035) B3036035
theorem B713351 : Blo 710320 713351 := bstep (se 1 (by rfl) ⟨535013, by rfl⟩ : syracuseStep 713351 = 1070027) B1070027
theorem B713359 : Blo 710320 713359 := bstep (se 1 (by rfl) ⟨535019, by rfl⟩ : syracuseStep 713359 = 1070039) B1070039
theorem B713403 : Blo 710320 713403 := bstep (se 1 (by rfl) ⟨535052, by rfl⟩ : syracuseStep 713403 = 1070105) B1070105
theorem B713479 : Blo 710320 713479 := bstep (se 1 (by rfl) ⟨535109, by rfl⟩ : syracuseStep 713479 = 1070219) B1070219
theorem B713487 : Blo 710320 713487 := bstep (se 1 (by rfl) ⟨535115, by rfl⟩ : syracuseStep 713487 = 1070231) B1070231
theorem B713531 : Blo 710320 713531 := bstep (se 1 (by rfl) ⟨535148, by rfl⟩ : syracuseStep 713531 = 1070297) B1070297
theorem B9134963 : Blo 710320 9134963 := bstep (se 1 (by rfl) ⟨6851222, by rfl⟩ : syracuseStep 9134963 = 13702445) B13702445
theorem B1598327 : Blo 710320 1598327 := bstep (se 1 (by rfl) ⟨1198745, by rfl⟩ : syracuseStep 1598327 = 2397491) B2397491
theorem B1205111 : Blo 710320 1205111 := bstep (se 1 (by rfl) ⟨903833, by rfl⟩ : syracuseStep 1205111 = 1807667) B1807667
theorem B713607 : Blo 710320 713607 := bstep (se 1 (by rfl) ⟨535205, by rfl⟩ : syracuseStep 713607 = 1070411) B1070411
theorem B713615 : Blo 710320 713615 := bstep (se 1 (by rfl) ⟨535211, by rfl⟩ : syracuseStep 713615 = 1070423) B1070423
theorem B3597209 : Blo 710320 3597209 := bstep (se 2 (by rfl) ⟨1348953, by rfl⟩ : syracuseStep 3597209 = 2697907) B2697907
theorem B5399459 : Blo 710320 5399459 := bstep (se 1 (by rfl) ⟨4049594, by rfl⟩ : syracuseStep 5399459 = 8099189) B8099189
theorem B713659 : Blo 710320 713659 := bstep (se 1 (by rfl) ⟨535244, by rfl⟩ : syracuseStep 713659 = 1070489) B1070489
theorem B713735 : Blo 710320 713735 := bstep (se 1 (by rfl) ⟨535301, by rfl⟩ : syracuseStep 713735 = 1070603) B1070603
theorem B713743 : Blo 710320 713743 := bstep (se 1 (by rfl) ⟨535307, by rfl⟩ : syracuseStep 713743 = 1070615) B1070615
theorem B1598507 : Blo 710320 1598507 := bstep (se 1 (by rfl) ⟨1198880, by rfl⟩ : syracuseStep 1598507 = 2397761) B2397761
theorem B713787 : Blo 710320 713787 := bstep (se 1 (by rfl) ⟨535340, by rfl⟩ : syracuseStep 713787 = 1070681) B1070681
theorem B5137469 : Blo 710320 5137469 := bstep (se 3 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 5137469 = 1926551) B1926551
theorem B3040375 : Blo 710320 3040375 := bstep (se 1 (by rfl) ⟨2280281, by rfl⟩ : syracuseStep 3040375 = 4560563) B4560563
theorem B713863 : Blo 710320 713863 := bstep (se 1 (by rfl) ⟨535397, by rfl⟩ : syracuseStep 713863 = 1070795) B1070795
theorem B713871 : Blo 710320 713871 := bstep (se 1 (by rfl) ⟨535403, by rfl⟩ : syracuseStep 713871 = 1070807) B1070807
theorem B713915 : Blo 710320 713915 := bstep (se 1 (by rfl) ⟨535436, by rfl⟩ : syracuseStep 713915 = 1070873) B1070873
theorem B713991 : Blo 710320 713991 := bstep (se 1 (by rfl) ⟨535493, by rfl⟩ : syracuseStep 713991 = 1070987) B1070987
theorem B713999 : Blo 710320 713999 := bstep (se 1 (by rfl) ⟨535499, by rfl⟩ : syracuseStep 713999 = 1070999) B1070999
theorem B714043 : Blo 710320 714043 := bstep (se 1 (by rfl) ⟨535532, by rfl⟩ : syracuseStep 714043 = 1071065) B1071065
theorem B714119 : Blo 710320 714119 := bstep (se 1 (by rfl) ⟨535589, by rfl⟩ : syracuseStep 714119 = 1071179) B1071179
theorem B714127 : Blo 710320 714127 := bstep (se 1 (by rfl) ⟨535595, by rfl⟩ : syracuseStep 714127 = 1071191) B1071191
theorem B1598867 : Blo 710320 1598867 := bstep (se 1 (by rfl) ⟨1199150, by rfl⟩ : syracuseStep 1598867 = 2398301) B2398301
theorem B714171 : Blo 710320 714171 := bstep (se 1 (by rfl) ⟨535628, by rfl⟩ : syracuseStep 714171 = 1071257) B1071257
theorem B1598921 : Blo 710320 1598921 := bstep (se 2 (by rfl) ⟨599595, by rfl⟩ : syracuseStep 1598921 = 1199191) B1199191
theorem B714247 : Blo 710320 714247 := bstep (se 1 (by rfl) ⟨535685, by rfl⟩ : syracuseStep 714247 = 1071371) B1071371
theorem B3958283 : Blo 710320 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B714255 : Blo 710320 714255 := bstep (se 1 (by rfl) ⟨535691, by rfl⟩ : syracuseStep 714255 = 1071383) B1071383
theorem B714299 : Blo 710320 714299 := bstep (se 1 (by rfl) ⟨535724, by rfl⟩ : syracuseStep 714299 = 1071449) B1071449
theorem B4056749 : Blo 710320 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B3860261 : Blo 710320 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B1599623 : Blo 710320 1599623 := bstep (se 1 (by rfl) ⟨1199717, by rfl⟩ : syracuseStep 1599623 = 2399435) B2399435
theorem B2025607 : Blo 710320 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B1599803 : Blo 710320 1599803 := bstep (se 1 (by rfl) ⟨1199852, by rfl⟩ : syracuseStep 1599803 = 2399705) B2399705
theorem B2189683 : Blo 710320 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B2025881 : Blo 710320 2025881 := bstep (se 2 (by rfl) ⟨759705, by rfl⟩ : syracuseStep 2025881 = 1519411) B1519411
theorem B1599929 : Blo 710320 1599929 := bstep (se 2 (by rfl) ⟨599973, by rfl⟩ : syracuseStep 1599929 = 1199947) B1199947
theorem B1141307 : Blo 710320 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B1927795 : Blo 710320 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B3042049 : Blo 710320 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B1600271 : Blo 710320 1600271 := bstep (se 1 (by rfl) ⟨1200203, by rfl⟩ : syracuseStep 1600271 = 2400407) B2400407
theorem B1600289 : Blo 710320 1600289 := bstep (se 2 (by rfl) ⟨600108, by rfl⟩ : syracuseStep 1600289 = 1200217) B1200217
theorem B2026529 : Blo 710320 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B1141819 : Blo 710320 1141819 := bstep (se 1 (by rfl) ⟨856364, by rfl⟩ : syracuseStep 1141819 = 1712729) B1712729
theorem B1600631 : Blo 710320 1600631 := bstep (se 1 (by rfl) ⟨1200473, by rfl⟩ : syracuseStep 1600631 = 2400947) B2400947
theorem B1928377 : Blo 710320 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B5401889 : Blo 710320 5401889 := bstep (se 2 (by rfl) ⟨2025708, by rfl⟩ : syracuseStep 5401889 = 4051417) B4051417
theorem B1600811 : Blo 710320 1600811 := bstep (se 1 (by rfl) ⟨1200608, by rfl⟩ : syracuseStep 1600811 = 2401217) B2401217
theorem B1928507 : Blo 710320 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B3599801 : Blo 710320 3599801 := bstep (se 2 (by rfl) ⟨1349925, by rfl⟩ : syracuseStep 3599801 = 2699851) B2699851
theorem B1928747 : Blo 710320 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B1601171 : Blo 710320 1601171 := bstep (se 1 (by rfl) ⟨1200878, by rfl⟩ : syracuseStep 1601171 = 2401757) B2401757
theorem B2191033 : Blo 710320 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B1601225 : Blo 710320 1601225 := bstep (se 2 (by rfl) ⟨600459, by rfl⟩ : syracuseStep 1601225 = 1200919) B1200919
theorem B6090659 : Blo 710320 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B2027531 : Blo 710320 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B1798159 : Blo 710320 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B1011727 : Blo 710320 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B1011847 : Blo 710320 1011847 := bstep (se 1 (by rfl) ⟨758885, by rfl⟩ : syracuseStep 1011847 = 1517771) B1517771
theorem B5402861 : Blo 710320 5402861 := bstep (se 3 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 5402861 = 2026073) B2026073
theorem B1798433 : Blo 710320 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B1601927 : Blo 710320 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B9138653 : Blo 710320 9138653 := bstep (se 3 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 9138653 = 3426995) B3426995
theorem B1602107 : Blo 710320 1602107 := bstep (se 1 (by rfl) ⟨1201580, by rfl⟩ : syracuseStep 1602107 = 2403161) B2403161
theorem B1602233 : Blo 710320 1602233 := bstep (se 2 (by rfl) ⟨600837, by rfl⟩ : syracuseStep 1602233 = 1201675) B1201675
theorem B17330881 : Blo 710320 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B3601097 : Blo 710320 3601097 := bstep (se 2 (by rfl) ⟨1350411, by rfl⟩ : syracuseStep 3601097 = 2700823) B2700823
theorem B1602575 : Blo 710320 1602575 := bstep (se 1 (by rfl) ⟨1201931, by rfl⟩ : syracuseStep 1602575 = 2403863) B2403863
theorem B1602593 : Blo 710320 1602593 := bstep (se 2 (by rfl) ⟨600972, by rfl⟩ : syracuseStep 1602593 = 1201945) B1201945
theorem B1799435 : Blo 710320 1799435 := bstep (se 1 (by rfl) ⟨1349576, by rfl⟩ : syracuseStep 1799435 = 2699153) B2699153
theorem B1602935 : Blo 710320 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B11859335 : Blo 710320 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B8779229 : Blo 710320 8779229 := bstep (se 3 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 8779229 = 3292211) B3292211
theorem B1603115 : Blo 710320 1603115 := bstep (se 1 (by rfl) ⟨1202336, by rfl⟩ : syracuseStep 1603115 = 2404673) B2404673
theorem B1013305 : Blo 710320 1013305 := bstep (se 2 (by rfl) ⟨379989, by rfl⟩ : syracuseStep 1013305 = 759979) B759979
theorem B1832507 : Blo 710320 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B126613313 : Blo 710320 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B1800083 : Blo 710320 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B1603475 : Blo 710320 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B6158243 : Blo 710320 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B1603529 : Blo 710320 1603529 := bstep (se 2 (by rfl) ⟨601323, by rfl⟩ : syracuseStep 1603529 = 1202647) B1202647
theorem B6944779 : Blo 710320 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B13694993 : Blo 710320 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B2029627 : Blo 710320 2029627 := bstep (se 1 (by rfl) ⟨1522220, by rfl⟩ : syracuseStep 2029627 = 3044441) B3044441
theorem B5404805 : Blo 710320 5404805 := bstep (se 4 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 5404805 = 1013401) B1013401
theorem B1800377 : Blo 710320 1800377 := bstep (se 2 (by rfl) ⟨675141, by rfl⟩ : syracuseStep 1800377 = 1350283) B1350283
theorem B4061441 : Blo 710320 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B1604231 : Blo 710320 1604231 := bstep (se 1 (by rfl) ⟨1203173, by rfl⟩ : syracuseStep 1604231 = 2406347) B2406347
theorem B2161337 : Blo 710320 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B4061897 : Blo 710320 4061897 := bstep (se 2 (by rfl) ⟨1523211, by rfl⟩ : syracuseStep 4061897 = 3046423) B3046423
theorem B1014535 : Blo 710320 1014535 := bstep (se 1 (by rfl) ⟨760901, by rfl⟩ : syracuseStep 1014535 = 1521803) B1521803
theorem B3701537 : Blo 710320 3701537 := bstep (se 2 (by rfl) ⟨1388076, by rfl⟩ : syracuseStep 3701537 = 2776153) B2776153
theorem B1604411 : Blo 710320 1604411 := bstep (se 1 (by rfl) ⟨1203308, by rfl⟩ : syracuseStep 1604411 = 2406617) B2406617
theorem B1801075 : Blo 710320 1801075 := bstep (se 1 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 1801075 = 2701613) B2701613
theorem B2030471 : Blo 710320 2030471 := bstep (se 1 (by rfl) ⟨1522853, by rfl⟩ : syracuseStep 2030471 = 3045707) B3045707
theorem B1604537 : Blo 710320 1604537 := bstep (se 2 (by rfl) ⟨601701, by rfl⟩ : syracuseStep 1604537 = 1203403) B1203403
theorem B1801217 : Blo 710320 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B1604879 : Blo 710320 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B1604897 : Blo 710320 1604897 := bstep (se 2 (by rfl) ⟨601836, by rfl⟩ : syracuseStep 1604897 = 1203673) B1203673
theorem B1801673 : Blo 710320 1801673 := bstep (se 2 (by rfl) ⟨675627, by rfl⟩ : syracuseStep 1801673 = 1351255) B1351255
theorem B1015355 : Blo 710320 1015355 := bstep (se 1 (by rfl) ⟨761516, by rfl⟩ : syracuseStep 1015355 = 1523033) B1523033
theorem B1605239 : Blo 710320 1605239 := bstep (se 1 (by rfl) ⟨1203929, by rfl⟩ : syracuseStep 1605239 = 2407859) B2407859
theorem B2031257 : Blo 710320 2031257 := bstep (se 2 (by rfl) ⟨761721, by rfl⟩ : syracuseStep 2031257 = 1523443) B1523443
theorem B1802027 : Blo 710320 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B1605419 : Blo 710320 1605419 := bstep (se 1 (by rfl) ⟨1204064, by rfl⟩ : syracuseStep 1605419 = 2408129) B2408129
theorem B5406749 : Blo 710320 5406749 := bstep (se 3 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 5406749 = 2027531) B2027531
theorem B1605689 : Blo 710320 1605689 := bstep (se 2 (by rfl) ⟨602133, by rfl⟩ : syracuseStep 1605689 = 1204267) B1204267
theorem B3604823 : Blo 710320 3604823 := bstep (se 1 (by rfl) ⟨2703617, by rfl⟩ : syracuseStep 3604823 = 5407235) B5407235
theorem B1606031 : Blo 710320 1606031 := bstep (se 1 (by rfl) ⟨1204523, by rfl⟩ : syracuseStep 1606031 = 2409047) B2409047
theorem B1016329 : Blo 710320 1016329 := bstep (se 2 (by rfl) ⟨381123, by rfl⟩ : syracuseStep 1016329 = 762247) B762247
theorem B5472953 : Blo 710320 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B1606355 : Blo 710320 1606355 := bstep (se 1 (by rfl) ⟨1204766, by rfl⟩ : syracuseStep 1606355 = 2409533) B2409533
theorem B21988097 : Blo 710320 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B8684509 : Blo 710320 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B1803343 : Blo 710320 1803343 := bstep (se 1 (by rfl) ⟨1352507, by rfl⟩ : syracuseStep 1803343 = 2705015) B2705015
theorem B4556411 : Blo 710320 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B14419603 : Blo 710320 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B2033363 : Blo 710320 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B1803991 : Blo 710320 1803991 := bstep (se 1 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 1803991 = 2705987) B2705987
theorem B2197343 : Blo 710320 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B9865223 : Blo 710320 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B1804295 : Blo 710320 1804295 := bstep (se 1 (by rfl) ⟨1353221, by rfl⟩ : syracuseStep 1804295 = 2706443) B2706443
theorem B4950245 : Blo 710320 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B854491 : Blo 710320 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B1280569 : Blo 710320 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B1280929 : Blo 710320 1280929 := bstep (se 2 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 1280929 = 960697) B960697
theorem B2919577 : Blo 710320 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B4558103 : Blo 710320 4558103 := bstep (se 1 (by rfl) ⟨3418577, by rfl⟩ : syracuseStep 4558103 = 6837155) B6837155
theorem B2166311 : Blo 710320 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B1707617 : Blo 710320 1707617 := bstep (se 2 (by rfl) ⟨640356, by rfl⟩ : syracuseStep 1707617 = 1280713) B1280713
theorem B4066955 : Blo 710320 4066955 := bstep (se 1 (by rfl) ⟨3050216, by rfl⟩ : syracuseStep 4066955 = 6100433) B6100433
theorem B3608387 : Blo 710320 3608387 := bstep (se 1 (by rfl) ⟨2706290, by rfl⟩ : syracuseStep 3608387 = 5412581) B5412581
theorem B4886459 : Blo 710320 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B2560157 : Blo 710320 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B11538611 : Blo 710320 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B1806583 : Blo 710320 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B5411123 : Blo 710320 5411123 := bstep (se 1 (by rfl) ⟨4058342, by rfl⟩ : syracuseStep 5411123 = 8116685) B8116685
theorem B1446407 : Blo 710320 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B1806857 : Blo 710320 1806857 := bstep (se 2 (by rfl) ⟨677571, by rfl⟩ : syracuseStep 1806857 = 1355143) B1355143
theorem B1806887 : Blo 710320 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B7705205 : Blo 710320 7705205 := bstep (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) B722363
theorem B1282759 : Blo 710320 1282759 := bstep (se 1 (by rfl) ⟨962069, by rfl⟩ : syracuseStep 1282759 = 1924139) B1924139
theorem B2167625 : Blo 710320 2167625 := bstep (se 2 (by rfl) ⟨812859, by rfl⟩ : syracuseStep 2167625 = 1625719) B1625719
theorem B6099785 : Blo 710320 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B1807211 : Blo 710320 1807211 := bstep (se 1 (by rfl) ⟨1355408, by rfl⟩ : syracuseStep 1807211 = 2710817) B2710817
theorem B12194711 : Blo 710320 12194711 := bstep (se 1 (by rfl) ⟨9146033, by rfl⟩ : syracuseStep 12194711 = 18292067) B18292067
theorem B65704931 : Blo 710320 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B3249305 : Blo 710320 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B857287 : Blo 710320 857287 := bstep (se 1 (by rfl) ⟨642965, by rfl⟩ : syracuseStep 857287 = 1285931) B1285931
theorem B9114869 : Blo 710320 9114869 := bstep (se 5 (by rfl) ⟨427259, by rfl⟩ : syracuseStep 9114869 = 854519) B854519
theorem B2397545 : Blo 710320 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B1348969 : Blo 710320 1348969 := bstep (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) B1011727
theorem B1807859 : Blo 710320 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B1349129 : Blo 710320 1349129 := bstep (se 2 (by rfl) ⟨505923, by rfl⟩ : syracuseStep 1349129 = 1011847) B1011847
theorem B2398139 : Blo 710320 2398139 := bstep (se 1 (by rfl) ⟨1798604, by rfl⟩ : syracuseStep 2398139 = 3597209) B3597209
theorem B23107841 : Blo 710320 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B21142037 : Blo 710320 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B3611465 : Blo 710320 3611465 := bstep (se 2 (by rfl) ⟨1354299, by rfl⟩ : syracuseStep 3611465 = 2708599) B2708599
theorem B9116509 : Blo 710320 9116509 := bstep (se 3 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 9116509 = 3418691) B3418691
theorem B1350587 : Blo 710320 1350587 := bstep (se 1 (by rfl) ⟨1012940, by rfl⟩ : syracuseStep 1350587 = 2025881) B2025881
theorem B760871 : Blo 710320 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B1351019 : Blo 710320 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B1351073 : Blo 710320 1351073 := bstep (se 2 (by rfl) ⟨506652, by rfl⟩ : syracuseStep 1351073 = 1013305) B1013305
theorem B6856109 : Blo 710320 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B2399867 : Blo 710320 2399867 := bstep (se 1 (by rfl) ⟨1799900, by rfl⟩ : syracuseStep 2399867 = 3599801) B3599801
theorem B1285831 : Blo 710320 1285831 := bstep (se 1 (by rfl) ⟨964373, by rfl⟩ : syracuseStep 1285831 = 1928747) B1928747
theorem B2400029 : Blo 710320 2400029 := bstep (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) B900011
theorem B3612761 : Blo 710320 3612761 := bstep (se 2 (by rfl) ⟨1354785, by rfl⟩ : syracuseStep 3612761 = 2709571) B2709571
theorem B2400731 : Blo 710320 2400731 := bstep (se 1 (by rfl) ⟨1800548, by rfl⟩ : syracuseStep 2400731 = 3601097) B3601097
theorem B7709357 : Blo 710320 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B7906223 : Blo 710320 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B1352713 : Blo 710320 1352713 := bstep (se 2 (by rfl) ⟨507267, by rfl⟩ : syracuseStep 1352713 = 1014535) B1014535
theorem B1221671 : Blo 710320 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B2401433 : Blo 710320 2401433 := bstep (se 2 (by rfl) ⟨900537, by rfl⟩ : syracuseStep 2401433 = 1801075) B1801075
theorem B9250037 : Blo 710320 9250037 := bstep (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) B867191
theorem B4105495 : Blo 710320 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B2467691 : Blo 710320 2467691 := bstep (se 1 (by rfl) ⟨1850768, by rfl⟩ : syracuseStep 2467691 = 3701537) B3701537
theorem B1353647 : Blo 710320 1353647 := bstep (se 1 (by rfl) ⟨1015235, by rfl⟩ : syracuseStep 1353647 = 2030471) B2030471
theorem B2402621 : Blo 710320 2402621 := bstep (se 3 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 2402621 = 900983) B900983
theorem B1354171 : Blo 710320 1354171 := bstep (se 1 (by rfl) ⟨1015628, by rfl⟩ : syracuseStep 1354171 = 2031257) B2031257
theorem B1354657 : Blo 710320 1354657 := bstep (se 2 (by rfl) ⟨507996, by rfl⟩ : syracuseStep 1354657 = 1015993) B1015993
theorem B2698393 : Blo 710320 2698393 := bstep (se 2 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 2698393 = 2023795) B2023795
theorem B2403485 : Blo 710320 2403485 := bstep (se 3 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 2403485 = 901307) B901307
theorem B961897 : Blo 710320 961897 := bstep (se 2 (by rfl) ⟨360711, by rfl⟩ : syracuseStep 961897 = 721423) B721423
theorem B5418413 : Blo 710320 5418413 := bstep (se 3 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 5418413 = 2031905) B2031905
theorem B2698697 : Blo 710320 2698697 := bstep (se 2 (by rfl) ⟨1012011, by rfl⟩ : syracuseStep 2698697 = 2024023) B2024023
theorem B10530269 : Blo 710320 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B2404025 : Blo 710320 2404025 := bstep (se 2 (by rfl) ⟨901509, by rfl⟩ : syracuseStep 2404025 = 1803019) B1803019
theorem B2699183 : Blo 710320 2699183 := bstep (se 1 (by rfl) ⟨2024387, by rfl⟩ : syracuseStep 2699183 = 4048775) B4048775
theorem B9744461 : Blo 710320 9744461 := bstep (se 3 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 9744461 = 3654173) B3654173
theorem B8335523 : Blo 710320 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B2404619 : Blo 710320 2404619 := bstep (se 1 (by rfl) ⟨1803464, by rfl⟩ : syracuseStep 2404619 = 3606929) B3606929
theorem B799195 : Blo 710320 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B2404889 : Blo 710320 2404889 := bstep (se 2 (by rfl) ⟨901833, by rfl⟩ : syracuseStep 2404889 = 1803667) B1803667
theorem B6074939 : Blo 710320 6074939 := bstep (se 1 (by rfl) ⟨4556204, by rfl⟩ : syracuseStep 6074939 = 9112409) B9112409
theorem B3420731 : Blo 710320 3420731 := bstep (se 1 (by rfl) ⟨2565548, by rfl⟩ : syracuseStep 3420731 = 5131097) B5131097
theorem B5124809 : Blo 710320 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B799663 : Blo 710320 799663 := bstep (se 1 (by rfl) ⟨599747, by rfl⟩ : syracuseStep 799663 = 1199495) B1199495
theorem B9122867 : Blo 710320 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B800095 : Blo 710320 800095 := bstep (se 1 (by rfl) ⟨600071, by rfl⟩ : syracuseStep 800095 = 1200143) B1200143
theorem B2700809 : Blo 710320 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B2406023 : Blo 710320 2406023 := bstep (se 1 (by rfl) ⟨1804517, by rfl⟩ : syracuseStep 2406023 = 3609035) B3609035
theorem B2406077 : Blo 710320 2406077 := bstep (se 3 (by rfl) ⟨451139, by rfl⟩ : syracuseStep 2406077 = 902279) B902279
theorem B800455 : Blo 710320 800455 := bstep (se 1 (by rfl) ⟨600341, by rfl⟩ : syracuseStep 800455 = 1200683) B1200683
theorem B5420843 : Blo 710320 5420843 := bstep (se 1 (by rfl) ⟨4065632, by rfl⟩ : syracuseStep 5420843 = 8131265) B8131265
theorem B2406239 : Blo 710320 2406239 := bstep (se 1 (by rfl) ⟨1804679, by rfl⟩ : syracuseStep 2406239 = 3609359) B3609359
theorem B8107937 : Blo 710320 8107937 := bstep (se 2 (by rfl) ⟨3040476, by rfl⟩ : syracuseStep 8107937 = 6080953) B6080953
theorem B2406401 : Blo 710320 2406401 := bstep (se 2 (by rfl) ⟨902400, by rfl⟩ : syracuseStep 2406401 = 1804801) B1804801
theorem B2570393 : Blo 710320 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B801319 : Blo 710320 801319 := bstep (se 1 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 801319 = 1201979) B1201979
theorem B2407211 : Blo 710320 2407211 := bstep (se 1 (by rfl) ⟨1805408, by rfl⟩ : syracuseStep 2407211 = 3610817) B3610817
theorem B2276257 : Blo 710320 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B3423151 : Blo 710320 3423151 := bstep (se 1 (by rfl) ⟨2567363, by rfl⟩ : syracuseStep 3423151 = 5134727) B5134727
theorem B2702267 : Blo 710320 2702267 := bstep (se 1 (by rfl) ⟨2026700, by rfl⟩ : syracuseStep 2702267 = 4053401) B4053401
theorem B2407481 : Blo 710320 2407481 := bstep (se 2 (by rfl) ⟨902805, by rfl⟩ : syracuseStep 2407481 = 1805611) B1805611
theorem B2407805 : Blo 710320 2407805 := bstep (se 3 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 2407805 = 902927) B902927
theorem B2735489 : Blo 710320 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B2276873 : Blo 710320 2276873 := bstep (se 2 (by rfl) ⟨853827, by rfl⟩ : syracuseStep 2276873 = 1707655) B1707655
theorem B2408075 : Blo 710320 2408075 := bstep (se 1 (by rfl) ⟨1806056, by rfl⟩ : syracuseStep 2408075 = 3612113) B3612113
theorem B901039 : Blo 710320 901039 := bstep (se 1 (by rfl) ⟨675779, by rfl⟩ : syracuseStep 901039 = 1351559) B1351559
theorem B6864911 : Blo 710320 6864911 := bstep (se 1 (by rfl) ⟨5148683, by rfl⟩ : syracuseStep 6864911 = 10297367) B10297367
theorem B4571225 : Blo 710320 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B3850355 : Blo 710320 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B802939 : Blo 710320 802939 := bstep (se 1 (by rfl) ⟨602204, by rfl⟩ : syracuseStep 802939 = 1204409) B1204409
theorem B15384725 : Blo 710320 15384725 := bstep (se 6 (by rfl) ⟨360579, by rfl⟩ : syracuseStep 15384725 = 721159) B721159
theorem B11583755 : Blo 710320 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B2408993 : Blo 710320 2408993 := bstep (se 2 (by rfl) ⟨903372, by rfl⟩ : syracuseStep 2408993 = 1806745) B1806745
theorem B1065551 : Blo 710320 1065551 := bstep (se 1 (by rfl) ⟨799163, by rfl⟩ : syracuseStep 1065551 = 1598327) B1598327
theorem B803407 : Blo 710320 803407 := bstep (se 1 (by rfl) ⟨602555, by rfl⟩ : syracuseStep 803407 = 1205111) B1205111
theorem B1065671 : Blo 710320 1065671 := bstep (se 1 (by rfl) ⟨799253, by rfl⟩ : syracuseStep 1065671 = 1598507) B1598507
theorem B4047569 : Blo 710320 4047569 := bstep (se 2 (by rfl) ⟨1517838, by rfl⟩ : syracuseStep 4047569 = 3035677) B3035677
theorem B3424979 : Blo 710320 3424979 := bstep (se 1 (by rfl) ⟨2568734, by rfl⟩ : syracuseStep 3424979 = 5137469) B5137469
theorem B2409209 : Blo 710320 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B1065833 : Blo 710320 1065833 := bstep (se 2 (by rfl) ⟨399687, by rfl⟩ : syracuseStep 1065833 = 799375) B799375
theorem B1065911 : Blo 710320 1065911 := bstep (se 1 (by rfl) ⟨799433, by rfl⟩ : syracuseStep 1065911 = 1598867) B1598867
theorem B1065947 : Blo 710320 1065947 := bstep (se 1 (by rfl) ⟨799460, by rfl⟩ : syracuseStep 1065947 = 1598921) B1598921
theorem B902107 : Blo 710320 902107 := bstep (se 1 (by rfl) ⟨676580, by rfl⟩ : syracuseStep 902107 = 1353161) B1353161
theorem B2638855 : Blo 710320 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B2409479 : Blo 710320 2409479 := bstep (se 1 (by rfl) ⟨1807109, by rfl⟩ : syracuseStep 2409479 = 3614219) B3614219
theorem B2704499 : Blo 710320 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B2409587 : Blo 710320 2409587 := bstep (se 1 (by rfl) ⟨1807190, by rfl⟩ : syracuseStep 2409587 = 3614381) B3614381
theorem B2573507 : Blo 710320 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B2278667 : Blo 710320 2278667 := bstep (se 1 (by rfl) ⟨1709000, by rfl⟩ : syracuseStep 2278667 = 3418001) B3418001
theorem B2409857 : Blo 710320 2409857 := bstep (se 2 (by rfl) ⟨903696, by rfl⟩ : syracuseStep 2409857 = 1807393) B1807393
theorem B1066415 : Blo 710320 1066415 := bstep (se 1 (by rfl) ⟨799811, by rfl⟩ : syracuseStep 1066415 = 1599623) B1599623
theorem B1066505 : Blo 710320 1066505 := bstep (se 2 (by rfl) ⟨399939, by rfl⟩ : syracuseStep 1066505 = 799879) B799879
theorem B1066535 : Blo 710320 1066535 := bstep (se 1 (by rfl) ⟨799901, by rfl⟩ : syracuseStep 1066535 = 1599803) B1599803
theorem B1066619 : Blo 710320 1066619 := bstep (se 1 (by rfl) ⟨799964, by rfl⟩ : syracuseStep 1066619 = 1599929) B1599929
theorem B1066745 : Blo 710320 1066745 := bstep (se 2 (by rfl) ⟨400029, by rfl⟩ : syracuseStep 1066745 = 800059) B800059
theorem B1066847 : Blo 710320 1066847 := bstep (se 1 (by rfl) ⟨800135, by rfl⟩ : syracuseStep 1066847 = 1600271) B1600271
theorem B3852127 : Blo 710320 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B1066859 : Blo 710320 1066859 := bstep (se 1 (by rfl) ⟨800144, by rfl⟩ : syracuseStep 1066859 = 1600289) B1600289
theorem B3426209 : Blo 710320 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B4573199 : Blo 710320 4573199 := bstep (se 1 (by rfl) ⟨3429899, by rfl⟩ : syracuseStep 4573199 = 6859799) B6859799
theorem B1067087 : Blo 710320 1067087 := bstep (se 1 (by rfl) ⟨800315, by rfl⟩ : syracuseStep 1067087 = 1600631) B1600631
theorem B2345113 : Blo 710320 2345113 := bstep (se 2 (by rfl) ⟨879417, by rfl⟩ : syracuseStep 2345113 = 1758835) B1758835
theorem B2410667 : Blo 710320 2410667 := bstep (se 1 (by rfl) ⟨1808000, by rfl⟩ : syracuseStep 2410667 = 3616001) B3616001
theorem B1067207 : Blo 710320 1067207 := bstep (se 1 (by rfl) ⟨800405, by rfl⟩ : syracuseStep 1067207 = 1600811) B1600811
theorem B1067369 : Blo 710320 1067369 := bstep (se 2 (by rfl) ⟨400263, by rfl⟩ : syracuseStep 1067369 = 800527) B800527
theorem B1067447 : Blo 710320 1067447 := bstep (se 1 (by rfl) ⟨800585, by rfl⟩ : syracuseStep 1067447 = 1601171) B1601171
theorem B1067483 : Blo 710320 1067483 := bstep (se 1 (by rfl) ⟨800612, by rfl⟩ : syracuseStep 1067483 = 1601225) B1601225
theorem B8243693 : Blo 710320 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B9259705 : Blo 710320 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B2706169 : Blo 710320 2706169 := bstep (se 2 (by rfl) ⟨1014813, by rfl⟩ : syracuseStep 2706169 = 2029627) B2029627
theorem B1198921 : Blo 710320 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B1198955 : Blo 710320 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B1067951 : Blo 710320 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B2280449 : Blo 710320 2280449 := bstep (se 2 (by rfl) ⟨855168, by rfl⟩ : syracuseStep 2280449 = 1710337) B1710337
theorem B1068041 : Blo 710320 1068041 := bstep (se 2 (by rfl) ⟨400515, by rfl⟩ : syracuseStep 1068041 = 801031) B801031
theorem B1068071 : Blo 710320 1068071 := bstep (se 1 (by rfl) ⟨801053, by rfl⟩ : syracuseStep 1068071 = 1602107) B1602107
theorem B2280563 : Blo 710320 2280563 := bstep (se 1 (by rfl) ⟨1710422, by rfl⟩ : syracuseStep 2280563 = 3420845) B3420845
theorem B1068155 : Blo 710320 1068155 := bstep (se 1 (by rfl) ⟨801116, by rfl⟩ : syracuseStep 1068155 = 1602233) B1602233
theorem B1199353 : Blo 710320 1199353 := bstep (se 2 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 1199353 = 899515) B899515
theorem B1068281 : Blo 710320 1068281 := bstep (se 2 (by rfl) ⟨400605, by rfl⟩ : syracuseStep 1068281 = 801211) B801211
theorem B1068383 : Blo 710320 1068383 := bstep (se 1 (by rfl) ⟨801287, by rfl⟩ : syracuseStep 1068383 = 1602575) B1602575
theorem B1068395 : Blo 710320 1068395 := bstep (se 1 (by rfl) ⟨801296, by rfl⟩ : syracuseStep 1068395 = 1602593) B1602593
theorem B2280923 : Blo 710320 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B1199623 : Blo 710320 1199623 := bstep (se 1 (by rfl) ⟨899717, by rfl⟩ : syracuseStep 1199623 = 1799435) B1799435
theorem B1068623 : Blo 710320 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B11685509 : Blo 710320 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B5852819 : Blo 710320 5852819 := bstep (se 1 (by rfl) ⟨4389614, by rfl⟩ : syracuseStep 5852819 = 8779229) B8779229
theorem B1068743 : Blo 710320 1068743 := bstep (se 1 (by rfl) ⟨801557, by rfl⟩ : syracuseStep 1068743 = 1603115) B1603115
theorem B1068905 : Blo 710320 1068905 := bstep (se 2 (by rfl) ⟨400839, by rfl⟩ : syracuseStep 1068905 = 801679) B801679
theorem B1200055 : Blo 710320 1200055 := bstep (se 1 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 1200055 = 1800083) B1800083
theorem B1068983 : Blo 710320 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B1069019 : Blo 710320 1069019 := bstep (se 1 (by rfl) ⟨801764, by rfl⟩ : syracuseStep 1069019 = 1603529) B1603529
theorem B9129995 : Blo 710320 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B1200251 : Blo 710320 1200251 := bstep (se 1 (by rfl) ⟨900188, by rfl⟩ : syracuseStep 1200251 = 1800377) B1800377
theorem B2707613 : Blo 710320 2707613 := bstep (se 3 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 2707613 = 1015355) B1015355
theorem B2707627 : Blo 710320 2707627 := bstep (se 1 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 2707627 = 4061441) B4061441
theorem B3428669 : Blo 710320 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B1069487 : Blo 710320 1069487 := bstep (se 1 (by rfl) ⟨802115, by rfl⟩ : syracuseStep 1069487 = 1604231) B1604231
theorem B2707931 : Blo 710320 2707931 := bstep (se 1 (by rfl) ⟨2030948, by rfl⟩ : syracuseStep 2707931 = 4061897) B4061897
theorem B1200649 : Blo 710320 1200649 := bstep (se 2 (by rfl) ⟨450243, by rfl⟩ : syracuseStep 1200649 = 900487) B900487
theorem B1069577 : Blo 710320 1069577 := bstep (se 2 (by rfl) ⟨401091, by rfl⟩ : syracuseStep 1069577 = 802183) B802183
theorem B1069607 : Blo 710320 1069607 := bstep (se 1 (by rfl) ⟨802205, by rfl⟩ : syracuseStep 1069607 = 1604411) B1604411
theorem B1069691 : Blo 710320 1069691 := bstep (se 1 (by rfl) ⟨802268, by rfl⟩ : syracuseStep 1069691 = 1604537) B1604537
theorem B1200811 : Blo 710320 1200811 := bstep (se 1 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 1200811 = 1801217) B1801217
theorem B1069817 : Blo 710320 1069817 := bstep (se 2 (by rfl) ⟨401181, by rfl⟩ : syracuseStep 1069817 = 802363) B802363
theorem B5493577 : Blo 710320 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B1069919 : Blo 710320 1069919 := bstep (se 1 (by rfl) ⟨802439, by rfl⟩ : syracuseStep 1069919 = 1604879) B1604879
theorem B1069931 : Blo 710320 1069931 := bstep (se 1 (by rfl) ⟨802448, by rfl⟩ : syracuseStep 1069931 = 1604897) B1604897
theorem B1201115 : Blo 710320 1201115 := bstep (se 1 (by rfl) ⟨900836, by rfl⟩ : syracuseStep 1201115 = 1801673) B1801673
theorem B1070159 : Blo 710320 1070159 := bstep (se 1 (by rfl) ⟨802619, by rfl⟩ : syracuseStep 1070159 = 1605239) B1605239
theorem B1201351 : Blo 710320 1201351 := bstep (se 1 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 1201351 = 1802027) B1802027
theorem B1070279 : Blo 710320 1070279 := bstep (se 1 (by rfl) ⟨802709, by rfl⟩ : syracuseStep 1070279 = 1605419) B1605419
theorem B1201513 : Blo 710320 1201513 := bstep (se 2 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 1201513 = 901135) B901135
theorem B1070441 : Blo 710320 1070441 := bstep (se 2 (by rfl) ⟨401415, by rfl⟩ : syracuseStep 1070441 = 802831) B802831
theorem B1070519 : Blo 710320 1070519 := bstep (se 1 (by rfl) ⟨802889, by rfl⟩ : syracuseStep 1070519 = 1605779) B1605779
theorem B3036635 : Blo 710320 3036635 := bstep (se 1 (by rfl) ⟨2277476, by rfl⟩ : syracuseStep 3036635 = 4554953) B4554953
theorem B1070555 : Blo 710320 1070555 := bstep (se 1 (by rfl) ⟨802916, by rfl⟩ : syracuseStep 1070555 = 1605833) B1605833
theorem B710343 : Blo 710320 710343 := bstep (se 1 (by rfl) ⟨532757, by rfl⟩ : syracuseStep 710343 = 1065515) B1065515
theorem B2741975 : Blo 710320 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B710363 : Blo 710320 710363 := bstep (se 1 (by rfl) ⟨532772, by rfl⟩ : syracuseStep 710363 = 1065545) B1065545
theorem B710439 : Blo 710320 710439 := bstep (se 1 (by rfl) ⟨532829, by rfl⟩ : syracuseStep 710439 = 1065659) B1065659
theorem B710479 : Blo 710320 710479 := bstep (se 1 (by rfl) ⟨532859, by rfl⟩ : syracuseStep 710479 = 1065719) B1065719
theorem B710495 : Blo 710320 710495 := bstep (se 1 (by rfl) ⟨532871, by rfl⟩ : syracuseStep 710495 = 1065743) B1065743
theorem B2283383 : Blo 710320 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B710523 : Blo 710320 710523 := bstep (se 1 (by rfl) ⟨532892, by rfl⟩ : syracuseStep 710523 = 1065785) B1065785
theorem B710575 : Blo 710320 710575 := bstep (se 1 (by rfl) ⟨532931, by rfl⟩ : syracuseStep 710575 = 1065863) B1065863
theorem B1071023 : Blo 710320 1071023 := bstep (se 1 (by rfl) ⟨803267, by rfl⟩ : syracuseStep 1071023 = 1606535) B1606535
theorem B1202107 : Blo 710320 1202107 := bstep (se 1 (by rfl) ⟨901580, by rfl⟩ : syracuseStep 1202107 = 1803161) B1803161
theorem B710599 : Blo 710320 710599 := bstep (se 1 (by rfl) ⟨532949, by rfl⟩ : syracuseStep 710599 = 1065899) B1065899
theorem B15849425 : Blo 710320 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B710619 : Blo 710320 710619 := bstep (se 1 (by rfl) ⟨532964, by rfl⟩ : syracuseStep 710619 = 1065929) B1065929
theorem B1071113 : Blo 710320 1071113 := bstep (se 2 (by rfl) ⟨401667, by rfl⟩ : syracuseStep 1071113 = 803335) B803335
theorem B710695 : Blo 710320 710695 := bstep (se 1 (by rfl) ⟨533021, by rfl⟩ : syracuseStep 710695 = 1066043) B1066043
theorem B1202215 : Blo 710320 1202215 := bstep (se 1 (by rfl) ⟨901661, by rfl⟩ : syracuseStep 1202215 = 1803323) B1803323
theorem B1071143 : Blo 710320 1071143 := bstep (se 1 (by rfl) ⟨803357, by rfl⟩ : syracuseStep 1071143 = 1606715) B1606715
theorem B710735 : Blo 710320 710735 := bstep (se 1 (by rfl) ⟨533051, by rfl⟩ : syracuseStep 710735 = 1066103) B1066103
theorem B710751 : Blo 710320 710751 := bstep (se 1 (by rfl) ⟨533063, by rfl⟩ : syracuseStep 710751 = 1066127) B1066127
theorem B710779 : Blo 710320 710779 := bstep (se 1 (by rfl) ⟨533084, by rfl⟩ : syracuseStep 710779 = 1066169) B1066169
theorem B1071227 : Blo 710320 1071227 := bstep (se 1 (by rfl) ⟨803420, by rfl⟩ : syracuseStep 1071227 = 1606841) B1606841
theorem B4053149 : Blo 710320 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B710831 : Blo 710320 710831 := bstep (se 1 (by rfl) ⟨533123, by rfl⟩ : syracuseStep 710831 = 1066247) B1066247
theorem B710855 : Blo 710320 710855 := bstep (se 1 (by rfl) ⟨533141, by rfl⟩ : syracuseStep 710855 = 1066283) B1066283
theorem B710875 : Blo 710320 710875 := bstep (se 1 (by rfl) ⟨533156, by rfl⟩ : syracuseStep 710875 = 1066313) B1066313
theorem B1071353 : Blo 710320 1071353 := bstep (se 2 (by rfl) ⟨401757, by rfl⟩ : syracuseStep 1071353 = 803515) B803515
theorem B710951 : Blo 710320 710951 := bstep (se 1 (by rfl) ⟨533213, by rfl⟩ : syracuseStep 710951 = 1066427) B1066427
theorem B710991 : Blo 710320 710991 := bstep (se 1 (by rfl) ⟨533243, by rfl⟩ : syracuseStep 710991 = 1066487) B1066487
theorem B711007 : Blo 710320 711007 := bstep (se 1 (by rfl) ⟨533255, by rfl⟩ : syracuseStep 711007 = 1066511) B1066511
theorem B1071455 : Blo 710320 1071455 := bstep (se 1 (by rfl) ⟨803591, by rfl⟩ : syracuseStep 1071455 = 1607183) B1607183
theorem B1202539 : Blo 710320 1202539 := bstep (se 1 (by rfl) ⟨901904, by rfl⟩ : syracuseStep 1202539 = 1803809) B1803809
theorem B1071467 : Blo 710320 1071467 := bstep (se 1 (by rfl) ⟨803600, by rfl⟩ : syracuseStep 1071467 = 1607201) B1607201
theorem B711035 : Blo 710320 711035 := bstep (se 1 (by rfl) ⟨533276, by rfl⟩ : syracuseStep 711035 = 1066553) B1066553
theorem B711087 : Blo 710320 711087 := bstep (se 1 (by rfl) ⟨533315, by rfl⟩ : syracuseStep 711087 = 1066631) B1066631
theorem B711111 : Blo 710320 711111 := bstep (se 1 (by rfl) ⟨533333, by rfl⟩ : syracuseStep 711111 = 1066667) B1066667
theorem B711131 : Blo 710320 711131 := bstep (se 1 (by rfl) ⟨533348, by rfl⟩ : syracuseStep 711131 = 1066697) B1066697
theorem B711207 : Blo 710320 711207 := bstep (se 1 (by rfl) ⟨533405, by rfl⟩ : syracuseStep 711207 = 1066811) B1066811
theorem B711247 : Blo 710320 711247 := bstep (se 1 (by rfl) ⟨533435, by rfl⟩ : syracuseStep 711247 = 1066871) B1066871
theorem B711263 : Blo 710320 711263 := bstep (se 1 (by rfl) ⟨533447, by rfl⟩ : syracuseStep 711263 = 1066895) B1066895
theorem B711291 : Blo 710320 711291 := bstep (se 1 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 711291 = 1066937) B1066937
theorem B711343 : Blo 710320 711343 := bstep (se 1 (by rfl) ⟨533507, by rfl⟩ : syracuseStep 711343 = 1067015) B1067015
theorem B711367 : Blo 710320 711367 := bstep (se 1 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 711367 = 1067051) B1067051
theorem B1465031 : Blo 710320 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B711387 : Blo 710320 711387 := bstep (se 1 (by rfl) ⟨533540, by rfl⟩ : syracuseStep 711387 = 1067081) B1067081
theorem B711463 : Blo 710320 711463 := bstep (se 1 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 711463 = 1067195) B1067195
theorem B4053833 : Blo 710320 4053833 := bstep (se 2 (by rfl) ⟨1520187, by rfl⟩ : syracuseStep 4053833 = 3040375) B3040375
theorem B711503 : Blo 710320 711503 := bstep (se 1 (by rfl) ⟨533627, by rfl⟩ : syracuseStep 711503 = 1067255) B1067255
theorem B711519 : Blo 710320 711519 := bstep (se 1 (by rfl) ⟨533639, by rfl⟩ : syracuseStep 711519 = 1067279) B1067279
theorem B711547 : Blo 710320 711547 := bstep (se 1 (by rfl) ⟨533660, by rfl⟩ : syracuseStep 711547 = 1067321) B1067321
theorem B711599 : Blo 710320 711599 := bstep (se 1 (by rfl) ⟨533699, by rfl⟩ : syracuseStep 711599 = 1067399) B1067399
theorem B711623 : Blo 710320 711623 := bstep (se 1 (by rfl) ⟨533717, by rfl⟩ : syracuseStep 711623 = 1067435) B1067435
theorem B711643 : Blo 710320 711643 := bstep (se 1 (by rfl) ⟨533732, by rfl⟩ : syracuseStep 711643 = 1067465) B1067465
theorem B2710529 : Blo 710320 2710529 := bstep (se 2 (by rfl) ⟨1016448, by rfl⟩ : syracuseStep 2710529 = 2032897) B2032897
theorem B2710543 : Blo 710320 2710543 := bstep (se 1 (by rfl) ⟨2032907, by rfl⟩ : syracuseStep 2710543 = 4065815) B4065815
theorem B711719 : Blo 710320 711719 := bstep (se 1 (by rfl) ⟨533789, by rfl⟩ : syracuseStep 711719 = 1067579) B1067579
theorem B15588395 : Blo 710320 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B711759 : Blo 710320 711759 := bstep (se 1 (by rfl) ⟨533819, by rfl⟩ : syracuseStep 711759 = 1067639) B1067639
theorem B711775 : Blo 710320 711775 := bstep (se 1 (by rfl) ⟨533831, by rfl⟩ : syracuseStep 711775 = 1067663) B1067663
theorem B711803 : Blo 710320 711803 := bstep (se 1 (by rfl) ⟨533852, by rfl⟩ : syracuseStep 711803 = 1067705) B1067705
theorem B711855 : Blo 710320 711855 := bstep (se 1 (by rfl) ⟨533891, by rfl⟩ : syracuseStep 711855 = 1067783) B1067783
theorem B711879 : Blo 710320 711879 := bstep (se 1 (by rfl) ⟨533909, by rfl⟩ : syracuseStep 711879 = 1067819) B1067819
theorem B711899 : Blo 710320 711899 := bstep (se 1 (by rfl) ⟨533924, by rfl⟩ : syracuseStep 711899 = 1067849) B1067849
theorem B7691543 : Blo 710320 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B711975 : Blo 710320 711975 := bstep (se 1 (by rfl) ⟨533981, by rfl⟩ : syracuseStep 711975 = 1067963) B1067963
theorem B712015 : Blo 710320 712015 := bstep (se 1 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 712015 = 1068023) B1068023
theorem B712031 : Blo 710320 712031 := bstep (se 1 (by rfl) ⟨534023, by rfl⟩ : syracuseStep 712031 = 1068047) B1068047
theorem B712059 : Blo 710320 712059 := bstep (se 1 (by rfl) ⟨534044, by rfl⟩ : syracuseStep 712059 = 1068089) B1068089
theorem B1203599 : Blo 710320 1203599 := bstep (se 1 (by rfl) ⟨902699, by rfl⟩ : syracuseStep 1203599 = 1805399) B1805399
theorem B712111 : Blo 710320 712111 := bstep (se 1 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 712111 = 1068167) B1068167
theorem B712135 : Blo 710320 712135 := bstep (se 1 (by rfl) ⟨534101, by rfl⟩ : syracuseStep 712135 = 1068203) B1068203
theorem B712155 : Blo 710320 712155 := bstep (se 1 (by rfl) ⟨534116, by rfl⟩ : syracuseStep 712155 = 1068233) B1068233
theorem B23092775 : Blo 710320 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B712231 : Blo 710320 712231 := bstep (se 1 (by rfl) ⟨534173, by rfl⟩ : syracuseStep 712231 = 1068347) B1068347
theorem B712271 : Blo 710320 712271 := bstep (se 1 (by rfl) ⟨534203, by rfl⟩ : syracuseStep 712271 = 1068407) B1068407
theorem B712287 : Blo 710320 712287 := bstep (se 1 (by rfl) ⟨534215, by rfl⟩ : syracuseStep 712287 = 1068431) B1068431
theorem B712315 : Blo 710320 712315 := bstep (se 1 (by rfl) ⟨534236, by rfl⟩ : syracuseStep 712315 = 1068473) B1068473
theorem B1203835 : Blo 710320 1203835 := bstep (se 1 (by rfl) ⟨902876, by rfl⟩ : syracuseStep 1203835 = 1805753) B1805753
theorem B712367 : Blo 710320 712367 := bstep (se 1 (by rfl) ⟨534275, by rfl⟩ : syracuseStep 712367 = 1068551) B1068551
theorem B712391 : Blo 710320 712391 := bstep (se 1 (by rfl) ⟨534293, by rfl⟩ : syracuseStep 712391 = 1068587) B1068587
theorem B2678483 : Blo 710320 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B1924823 : Blo 710320 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B712411 : Blo 710320 712411 := bstep (se 1 (by rfl) ⟨534308, by rfl⟩ : syracuseStep 712411 = 1068617) B1068617
theorem B712487 : Blo 710320 712487 := bstep (se 1 (by rfl) ⟨534365, by rfl⟩ : syracuseStep 712487 = 1068731) B1068731
theorem B3596075 : Blo 710320 3596075 := bstep (se 1 (by rfl) ⟨2697056, by rfl⟩ : syracuseStep 3596075 = 5394113) B5394113
theorem B712527 : Blo 710320 712527 := bstep (se 1 (by rfl) ⟨534395, by rfl⟩ : syracuseStep 712527 = 1068791) B1068791
theorem B712543 : Blo 710320 712543 := bstep (se 1 (by rfl) ⟨534407, by rfl⟩ : syracuseStep 712543 = 1068815) B1068815
theorem B712571 : Blo 710320 712571 := bstep (se 1 (by rfl) ⟨534428, by rfl⟩ : syracuseStep 712571 = 1068857) B1068857
theorem B712623 : Blo 710320 712623 := bstep (se 1 (by rfl) ⟨534467, by rfl⟩ : syracuseStep 712623 = 1068935) B1068935
theorem B712647 : Blo 710320 712647 := bstep (se 1 (by rfl) ⟨534485, by rfl⟩ : syracuseStep 712647 = 1068971) B1068971
theorem B712667 : Blo 710320 712667 := bstep (se 1 (by rfl) ⟨534500, by rfl⟩ : syracuseStep 712667 = 1069001) B1069001
theorem B712743 : Blo 710320 712743 := bstep (se 1 (by rfl) ⟨534557, by rfl⟩ : syracuseStep 712743 = 1069115) B1069115
theorem B712783 : Blo 710320 712783 := bstep (se 1 (by rfl) ⟨534587, by rfl⟩ : syracuseStep 712783 = 1069175) B1069175
theorem B712799 : Blo 710320 712799 := bstep (se 1 (by rfl) ⟨534599, by rfl⟩ : syracuseStep 712799 = 1069199) B1069199
theorem B712827 : Blo 710320 712827 := bstep (se 1 (by rfl) ⟨534620, by rfl⟩ : syracuseStep 712827 = 1069241) B1069241
theorem B712879 : Blo 710320 712879 := bstep (se 1 (by rfl) ⟨534659, by rfl⟩ : syracuseStep 712879 = 1069319) B1069319
theorem B712903 : Blo 710320 712903 := bstep (se 1 (by rfl) ⟨534677, by rfl⟩ : syracuseStep 712903 = 1069355) B1069355
theorem B712923 : Blo 710320 712923 := bstep (se 1 (by rfl) ⟨534692, by rfl⟩ : syracuseStep 712923 = 1069385) B1069385
theorem B2711819 : Blo 710320 2711819 := bstep (se 1 (by rfl) ⟨2033864, by rfl⟩ : syracuseStep 2711819 = 4067729) B4067729
theorem B712999 : Blo 710320 712999 := bstep (se 1 (by rfl) ⟨534749, by rfl⟩ : syracuseStep 712999 = 1069499) B1069499
theorem B713039 : Blo 710320 713039 := bstep (se 1 (by rfl) ⟨534779, by rfl⟩ : syracuseStep 713039 = 1069559) B1069559
theorem B713055 : Blo 710320 713055 := bstep (se 1 (by rfl) ⟨534791, by rfl⟩ : syracuseStep 713055 = 1069583) B1069583
theorem B713083 : Blo 710320 713083 := bstep (se 1 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 713083 = 1069625) B1069625
theorem B713135 : Blo 710320 713135 := bstep (se 1 (by rfl) ⟨534851, by rfl⟩ : syracuseStep 713135 = 1069703) B1069703
theorem B713159 : Blo 710320 713159 := bstep (se 1 (by rfl) ⟨534869, by rfl⟩ : syracuseStep 713159 = 1069739) B1069739
theorem B713179 : Blo 710320 713179 := bstep (se 1 (by rfl) ⟨534884, by rfl⟩ : syracuseStep 713179 = 1069769) B1069769
theorem B1204699 : Blo 710320 1204699 := bstep (se 1 (by rfl) ⟨903524, by rfl⟩ : syracuseStep 1204699 = 1807049) B1807049
theorem B2744819 : Blo 710320 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B713255 : Blo 710320 713255 := bstep (se 1 (by rfl) ⟨534941, by rfl⟩ : syracuseStep 713255 = 1069883) B1069883
theorem B713295 : Blo 710320 713295 := bstep (se 1 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 713295 = 1069943) B1069943
theorem B713311 : Blo 710320 713311 := bstep (se 1 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 713311 = 1069967) B1069967
theorem B713339 : Blo 710320 713339 := bstep (se 1 (by rfl) ⟨535004, by rfl⟩ : syracuseStep 713339 = 1070009) B1070009
theorem B713391 : Blo 710320 713391 := bstep (se 1 (by rfl) ⟨535043, by rfl⟩ : syracuseStep 713391 = 1070087) B1070087
theorem B713415 : Blo 710320 713415 := bstep (se 1 (by rfl) ⟨535061, by rfl⟩ : syracuseStep 713415 = 1070123) B1070123
theorem B713435 : Blo 710320 713435 := bstep (se 1 (by rfl) ⟨535076, by rfl⟩ : syracuseStep 713435 = 1070153) B1070153
theorem B713511 : Blo 710320 713511 := bstep (se 1 (by rfl) ⟨535133, by rfl⟩ : syracuseStep 713511 = 1070267) B1070267
theorem B713551 : Blo 710320 713551 := bstep (se 1 (by rfl) ⟨535163, by rfl⟩ : syracuseStep 713551 = 1070327) B1070327
theorem B713567 : Blo 710320 713567 := bstep (se 1 (by rfl) ⟨535175, by rfl⟩ : syracuseStep 713567 = 1070351) B1070351
theorem B713595 : Blo 710320 713595 := bstep (se 1 (by rfl) ⟨535196, by rfl⟩ : syracuseStep 713595 = 1070393) B1070393
theorem B713647 : Blo 710320 713647 := bstep (se 1 (by rfl) ⟨535235, by rfl⟩ : syracuseStep 713647 = 1070471) B1070471
theorem B713671 : Blo 710320 713671 := bstep (se 1 (by rfl) ⟨535253, by rfl⟩ : syracuseStep 713671 = 1070507) B1070507
theorem B713691 : Blo 710320 713691 := bstep (se 1 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 713691 = 1070537) B1070537
theorem B4056065 : Blo 710320 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B1598471 : Blo 710320 1598471 := bstep (se 1 (by rfl) ⟨1198853, by rfl⟩ : syracuseStep 1598471 = 2397707) B2397707
theorem B713767 : Blo 710320 713767 := bstep (se 1 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 713767 = 1070651) B1070651
theorem B1598543 : Blo 710320 1598543 := bstep (se 1 (by rfl) ⟨1198907, by rfl⟩ : syracuseStep 1598543 = 2397815) B2397815
theorem B713807 : Blo 710320 713807 := bstep (se 1 (by rfl) ⟨535355, by rfl⟩ : syracuseStep 713807 = 1070711) B1070711
theorem B1205327 : Blo 710320 1205327 := bstep (se 1 (by rfl) ⟨903995, by rfl⟩ : syracuseStep 1205327 = 1807991) B1807991
theorem B713823 : Blo 710320 713823 := bstep (se 1 (by rfl) ⟨535367, by rfl⟩ : syracuseStep 713823 = 1070735) B1070735
theorem B713851 : Blo 710320 713851 := bstep (se 1 (by rfl) ⟨535388, by rfl⟩ : syracuseStep 713851 = 1070777) B1070777
theorem B3040409 : Blo 710320 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B713903 : Blo 710320 713903 := bstep (se 1 (by rfl) ⟨535427, by rfl⟩ : syracuseStep 713903 = 1070855) B1070855
theorem B713927 : Blo 710320 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B713947 : Blo 710320 713947 := bstep (se 1 (by rfl) ⟨535460, by rfl⟩ : syracuseStep 713947 = 1070921) B1070921
theorem B714023 : Blo 710320 714023 := bstep (se 1 (by rfl) ⟨535517, by rfl⟩ : syracuseStep 714023 = 1071035) B1071035
theorem B714063 : Blo 710320 714063 := bstep (se 1 (by rfl) ⟨535547, by rfl⟩ : syracuseStep 714063 = 1071095) B1071095
theorem B714079 : Blo 710320 714079 := bstep (se 1 (by rfl) ⟨535559, by rfl⟩ : syracuseStep 714079 = 1071119) B1071119
theorem B714107 : Blo 710320 714107 := bstep (se 1 (by rfl) ⟨535580, by rfl⟩ : syracuseStep 714107 = 1071161) B1071161
theorem B714159 : Blo 710320 714159 := bstep (se 1 (by rfl) ⟨535619, by rfl⟩ : syracuseStep 714159 = 1071239) B1071239
theorem B714183 : Blo 710320 714183 := bstep (se 1 (by rfl) ⟨535637, by rfl⟩ : syracuseStep 714183 = 1071275) B1071275
theorem B1598939 : Blo 710320 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B714203 : Blo 710320 714203 := bstep (se 1 (by rfl) ⟨535652, by rfl⟩ : syracuseStep 714203 = 1071305) B1071305
theorem B10249739 : Blo 710320 10249739 := bstep (se 1 (by rfl) ⟨7687304, by rfl⟩ : syracuseStep 10249739 = 15374609) B15374609
theorem B5137931 : Blo 710320 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B714279 : Blo 710320 714279 := bstep (se 1 (by rfl) ⟨535709, by rfl⟩ : syracuseStep 714279 = 1071419) B1071419
theorem B714319 : Blo 710320 714319 := bstep (se 1 (by rfl) ⟨535739, by rfl⟩ : syracuseStep 714319 = 1071479) B1071479
theorem B6153943 : Blo 710320 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B1599407 : Blo 710320 1599407 := bstep (se 1 (by rfl) ⟨1199555, by rfl⟩ : syracuseStep 1599407 = 2399111) B2399111
theorem B3598343 : Blo 710320 3598343 := bstep (se 1 (by rfl) ⟨2698757, by rfl⟩ : syracuseStep 3598343 = 5397515) B5397515
theorem B1140743 : Blo 710320 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B3860561 : Blo 710320 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B1599659 : Blo 710320 1599659 := bstep (se 1 (by rfl) ⟨1199744, by rfl⟩ : syracuseStep 1599659 = 2399489) B2399489
theorem B2287997 : Blo 710320 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B4614529 : Blo 710320 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B9103751 : Blo 710320 9103751 := bstep (se 1 (by rfl) ⟨6827813, by rfl⟩ : syracuseStep 9103751 = 13655627) B13655627
theorem B3598829 : Blo 710320 3598829 := bstep (se 3 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 3598829 = 1349561) B1349561
theorem B18278945 : Blo 710320 18278945 := bstep (se 2 (by rfl) ⟨6854604, by rfl⟩ : syracuseStep 18278945 = 13709209) B13709209
theorem B813607 : Blo 710320 813607 := bstep (se 1 (by rfl) ⟨610205, by rfl⟩ : syracuseStep 813607 = 1220411) B1220411
theorem B1600199 : Blo 710320 1600199 := bstep (se 1 (by rfl) ⟨1200149, by rfl⟩ : syracuseStep 1600199 = 2400299) B2400299
theorem B1141609 : Blo 710320 1141609 := bstep (se 2 (by rfl) ⟨428103, by rfl⟩ : syracuseStep 1141609 = 856207) B856207
theorem B6089701 : Blo 710320 6089701 := bstep (se 4 (by rfl) ⟨570909, by rfl⟩ : syracuseStep 6089701 = 1141819) B1141819
theorem B3042323 : Blo 710320 3042323 := bstep (se 1 (by rfl) ⟨2281742, by rfl⟩ : syracuseStep 3042323 = 4563485) B4563485
theorem B38890691 : Blo 710320 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B6089975 : Blo 710320 6089975 := bstep (se 1 (by rfl) ⟨4567481, by rfl⟩ : syracuseStep 6089975 = 9134963) B9134963
theorem B3599639 : Blo 710320 3599639 := bstep (se 1 (by rfl) ⟨2699729, by rfl⟩ : syracuseStep 3599639 = 5399459) B5399459
theorem B1142191 : Blo 710320 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B1601063 : Blo 710320 1601063 := bstep (se 1 (by rfl) ⟨1200797, by rfl⟩ : syracuseStep 1601063 = 2401595) B2401595
theorem B10284677 : Blo 710320 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B9760445 : Blo 710320 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B39415517 : Blo 710320 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B1601387 : Blo 710320 1601387 := bstep (se 1 (by rfl) ⟨1201040, by rfl⟩ : syracuseStep 1601387 = 2402081) B2402081
theorem B1601441 : Blo 710320 1601441 := bstep (se 2 (by rfl) ⟨600540, by rfl⟩ : syracuseStep 1601441 = 1201081) B1201081
theorem B1601783 : Blo 710320 1601783 := bstep (se 1 (by rfl) ⟨1201337, by rfl⟩ : syracuseStep 1601783 = 2402675) B2402675
theorem B5763565 : Blo 710320 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B5403347 : Blo 710320 5403347 := bstep (se 1 (by rfl) ⟨4052510, by rfl⟩ : syracuseStep 5403347 = 8105021) B8105021
theorem B1602377 : Blo 710320 1602377 := bstep (se 2 (by rfl) ⟨600891, by rfl⟩ : syracuseStep 1602377 = 1201783) B1201783
theorem B3601259 : Blo 710320 3601259 := bstep (se 1 (by rfl) ⟨2700944, by rfl⟩ : syracuseStep 3601259 = 5401889) B5401889
theorem B1143659 : Blo 710320 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B4060439 : Blo 710320 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B1799567 : Blo 710320 1799567 := bstep (se 1 (by rfl) ⟨1349675, by rfl⟩ : syracuseStep 1799567 = 2699351) B2699351
theorem B3601907 : Blo 710320 3601907 := bstep (se 1 (by rfl) ⟨2701430, by rfl⟩ : syracuseStep 3601907 = 5402861) B5402861
theorem B1603169 : Blo 710320 1603169 := bstep (se 2 (by rfl) ⟨601188, by rfl⟩ : syracuseStep 1603169 = 1202377) B1202377
theorem B6092435 : Blo 710320 6092435 := bstep (se 1 (by rfl) ⟨4569326, by rfl⟩ : syracuseStep 6092435 = 9138653) B9138653
theorem B1799891 : Blo 710320 1799891 := bstep (se 1 (by rfl) ⟨1349918, by rfl⟩ : syracuseStep 1799891 = 2699837) B2699837
theorem B1603511 : Blo 710320 1603511 := bstep (se 1 (by rfl) ⟨1202633, by rfl⟩ : syracuseStep 1603511 = 2405267) B2405267
theorem B3045383 : Blo 710320 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B7796837 : Blo 710320 7796837 := bstep (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) B1461907
theorem B5142685 : Blo 710320 5142685 := bstep (se 3 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 5142685 = 1928507) B1928507
theorem B1604105 : Blo 710320 1604105 := bstep (se 2 (by rfl) ⟨601539, by rfl⟩ : syracuseStep 1604105 = 1203079) B1203079
theorem B84408875 : Blo 710320 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B3603203 : Blo 710320 3603203 := bstep (se 1 (by rfl) ⟨2702402, by rfl⟩ : syracuseStep 3603203 = 5404805) B5404805
theorem B1801055 : Blo 710320 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B1604447 : Blo 710320 1604447 := bstep (se 1 (by rfl) ⟨1203335, by rfl⟩ : syracuseStep 1604447 = 2406671) B2406671
theorem B1604627 : Blo 710320 1604627 := bstep (se 1 (by rfl) ⟨1203470, by rfl⟩ : syracuseStep 1604627 = 2406941) B2406941
theorem B1604969 : Blo 710320 1604969 := bstep (se 2 (by rfl) ⟨601863, by rfl⟩ : syracuseStep 1604969 = 1203727) B1203727
theorem B92470733 : Blo 710320 92470733 := bstep (se 3 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 92470733 = 34676525) B34676525
theorem B5471783 : Blo 710320 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B7700359 : Blo 710320 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B1802159 : Blo 710320 1802159 := bstep (se 1 (by rfl) ⟨1351619, by rfl⟩ : syracuseStep 1802159 = 2703239) B2703239
theorem B1605563 : Blo 710320 1605563 := bstep (se 1 (by rfl) ⟨1204172, by rfl⟩ : syracuseStep 1605563 = 2408345) B2408345
theorem B3604499 : Blo 710320 3604499 := bstep (se 1 (by rfl) ⟨2703374, by rfl⟩ : syracuseStep 3604499 = 5406749) B5406749
theorem B3047483 : Blo 710320 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B10256483 : Blo 710320 10256483 := bstep (se 1 (by rfl) ⟨7692362, by rfl⟩ : syracuseStep 10256483 = 15384725) B15384725
theorem B1605995 : Blo 710320 1605995 := bstep (se 1 (by rfl) ⟨1204496, by rfl⟩ : syracuseStep 1605995 = 2408993) B2408993
theorem B1606139 : Blo 710320 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B1606265 : Blo 710320 1606265 := bstep (se 2 (by rfl) ⟨602349, by rfl⟩ : syracuseStep 1606265 = 1204699) B1204699
theorem B1606319 : Blo 710320 1606319 := bstep (se 1 (by rfl) ⟨1204739, by rfl⟩ : syracuseStep 1606319 = 2409479) B2409479
theorem B1802999 : Blo 710320 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B1606391 : Blo 710320 1606391 := bstep (se 1 (by rfl) ⟨1204793, by rfl⟩ : syracuseStep 1606391 = 2409587) B2409587
theorem B9143117 : Blo 710320 9143117 := bstep (se 3 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 9143117 = 3428669) B3428669
theorem B1606571 : Blo 710320 1606571 := bstep (se 1 (by rfl) ⟨1204928, by rfl⟩ : syracuseStep 1606571 = 2409857) B2409857
theorem B3048799 : Blo 710320 3048799 := bstep (se 1 (by rfl) ⟨2286599, by rfl⟩ : syracuseStep 3048799 = 4573199) B4573199
theorem B1803617 : Blo 710320 1803617 := bstep (se 2 (by rfl) ⟨676356, by rfl⟩ : syracuseStep 1803617 = 1352713) B1352713
theorem B1607111 : Blo 710320 1607111 := bstep (se 1 (by rfl) ⟨1205333, by rfl⟩ : syracuseStep 1607111 = 2410667) B2410667
theorem B5473993 : Blo 710320 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B3049757 : Blo 710320 3049757 := bstep (se 3 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 3049757 = 1143659) B1143659
theorem B3901879 : Blo 710320 3901879 := bstep (se 1 (by rfl) ⟨2926409, by rfl⟩ : syracuseStep 3901879 = 5852819) B5852819
theorem B1706771 : Blo 710320 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B1805075 : Blo 710320 1805075 := bstep (se 1 (by rfl) ⟨1353806, by rfl⟩ : syracuseStep 1805075 = 2707613) B2707613
theorem B3607415 : Blo 710320 3607415 := bstep (se 1 (by rfl) ⟨2705561, by rfl⟩ : syracuseStep 3607415 = 5411123) B5411123
theorem B1805287 : Blo 710320 1805287 := bstep (se 1 (by rfl) ⟨1353965, by rfl⟩ : syracuseStep 1805287 = 2707931) B2707931
theorem B1445083 : Blo 710320 1445083 := bstep (se 1 (by rfl) ⟨1083812, by rfl⟩ : syracuseStep 1445083 = 2167625) B2167625
theorem B4066523 : Blo 710320 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B1805561 : Blo 710320 1805561 := bstep (se 2 (by rfl) ⟨677085, by rfl⟩ : syracuseStep 1805561 = 1354171) B1354171
theorem B8129807 : Blo 710320 8129807 := bstep (se 1 (by rfl) ⟨6097355, by rfl⟩ : syracuseStep 8129807 = 12194711) B12194711
theorem B1707425 : Blo 710320 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B2166203 : Blo 710320 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B3608225 : Blo 710320 3608225 := bstep (se 2 (by rfl) ⟨1353084, by rfl⟩ : syracuseStep 3608225 = 2706169) B2706169
theorem B1707905 : Blo 710320 1707905 := bstep (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) B1280929
theorem B1806209 : Blo 710320 1806209 := bstep (se 2 (by rfl) ⟨677328, by rfl⟩ : syracuseStep 1806209 = 1354657) B1354657
theorem B15405227 : Blo 710320 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B14094691 : Blo 710320 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B1282529 : Blo 710320 1282529 := bstep (se 2 (by rfl) ⟨480948, by rfl⟩ : syracuseStep 1282529 = 961897) B961897
theorem B1807019 : Blo 710320 1807019 := bstep (se 1 (by rfl) ⟨1355264, by rfl⟩ : syracuseStep 1807019 = 2710529) B2710529
theorem B10392263 : Blo 710320 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B1283215 : Blo 710320 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B2397383 : Blo 710320 2397383 := bstep (se 1 (by rfl) ⟨1798037, by rfl⟩ : syracuseStep 2397383 = 3596075) B3596075
theorem B1807879 : Blo 710320 1807879 := bstep (se 1 (by rfl) ⟨1355909, by rfl⟩ : syracuseStep 1807879 = 2711819) B2711819
theorem B3610169 : Blo 710320 3610169 := bstep (se 2 (by rfl) ⟨1353813, by rfl⟩ : syracuseStep 3610169 = 2707627) B2707627
theorem B6166691 : Blo 710320 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B1645127 : Blo 710320 1645127 := bstep (se 1 (by rfl) ⟨1233845, by rfl⟩ : syracuseStep 1645127 = 2467691) B2467691
theorem B2398895 : Blo 710320 2398895 := bstep (se 1 (by rfl) ⟨1799171, by rfl⟩ : syracuseStep 2398895 = 3598343) B3598343
theorem B6069167 : Blo 710320 6069167 := bstep (se 1 (by rfl) ⟨4551875, by rfl⟩ : syracuseStep 6069167 = 9103751) B9103751
theorem B2399219 : Blo 710320 2399219 := bstep (se 1 (by rfl) ⟨1799414, by rfl⟩ : syracuseStep 2399219 = 3598829) B3598829
theorem B3906749 : Blo 710320 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B25927127 : Blo 710320 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B2399759 : Blo 710320 2399759 := bstep (se 1 (by rfl) ⟨1799819, by rfl⟩ : syracuseStep 2399759 = 3599639) B3599639
theorem B3612275 : Blo 710320 3612275 := bstep (se 1 (by rfl) ⟨2709206, by rfl⟩ : syracuseStep 3612275 = 5418413) B5418413
theorem B7020179 : Blo 710320 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B6856451 : Blo 710320 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B6496307 : Blo 710320 6496307 := bstep (se 1 (by rfl) ⟨4872230, by rfl⟩ : syracuseStep 6496307 = 9744461) B9744461
theorem B6856913 : Blo 710320 6856913 := bstep (se 2 (by rfl) ⟨2571342, by rfl⟩ : syracuseStep 6856913 = 5142685) B5142685
theorem B3416539 : Blo 710320 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B2400839 : Blo 710320 2400839 := bstep (se 1 (by rfl) ⟨1800629, by rfl⟩ : syracuseStep 2400839 = 3601259) B3601259
theorem B2401271 : Blo 710320 2401271 := bstep (se 1 (by rfl) ⟨1800953, by rfl⟩ : syracuseStep 2401271 = 3601907) B3601907
theorem B3613895 : Blo 710320 3613895 := bstep (se 1 (by rfl) ⟨2710421, by rfl⟩ : syracuseStep 3613895 = 5420843) B5420843
theorem B4564201 : Blo 710320 4564201 := bstep (se 2 (by rfl) ⟨1711575, by rfl⟩ : syracuseStep 4564201 = 3423151) B3423151
theorem B3614057 : Blo 710320 3614057 := bstep (se 2 (by rfl) ⟨1355271, by rfl⟩ : syracuseStep 3614057 = 2710543) B2710543
theorem B1713595 : Blo 710320 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B5776829 : Blo 710320 5776829 := bstep (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) B2166311
theorem B56272583 : Blo 710320 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B2402135 : Blo 710320 2402135 := bstep (se 1 (by rfl) ⟨1801601, by rfl⟩ : syracuseStep 2402135 = 3603203) B3603203
theorem B1714441 : Blo 710320 1714441 := bstep (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) B1285831
theorem B61647155 : Blo 710320 61647155 := bstep (se 1 (by rfl) ⟨46235366, by rfl⟩ : syracuseStep 61647155 = 92470733) B92470733
theorem B1517915 : Blo 710320 1517915 := bstep (se 1 (by rfl) ⟨1138436, by rfl⟩ : syracuseStep 1517915 = 2276873) B2276873
theorem B3647855 : Blo 710320 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B10267145 : Blo 710320 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B2566903 : Blo 710320 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B2403215 : Blo 710320 2403215 := bstep (se 1 (by rfl) ⟨1802411, by rfl⟩ : syracuseStep 2403215 = 3604823) B3604823
theorem B3648635 : Blo 710320 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B2698379 : Blo 710320 2698379 := bstep (se 1 (by rfl) ⟨2023784, by rfl⟩ : syracuseStep 2698379 = 4047569) B4047569
theorem B14658731 : Blo 710320 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B1355105 : Blo 710320 1355105 := bstep (se 2 (by rfl) ⟨508164, by rfl⟩ : syracuseStep 1355105 = 1016329) B1016329
theorem B1715671 : Blo 710320 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B1519111 : Blo 710320 1519111 := bstep (se 1 (by rfl) ⟨1139333, by rfl⟩ : syracuseStep 1519111 = 2278667) B2278667
theorem B11579345 : Blo 710320 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B3518473 : Blo 710320 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B2404457 : Blo 710320 2404457 := bstep (se 2 (by rfl) ⟨901671, by rfl⟩ : syracuseStep 2404457 = 1803343) B1803343
theorem B799303 : Blo 710320 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B1520299 : Blo 710320 1520299 := bstep (se 1 (by rfl) ⟨1140224, by rfl⟩ : syracuseStep 1520299 = 2280449) B2280449
theorem B1520375 : Blo 710320 1520375 := bstep (se 1 (by rfl) ⟨1140281, by rfl⟩ : syracuseStep 1520375 = 2280563) B2280563
theorem B8205257 : Blo 710320 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B2405321 : Blo 710320 2405321 := bstep (se 2 (by rfl) ⟨901995, by rfl⟩ : syracuseStep 2405321 = 1803991) B1803991
theorem B1520615 : Blo 710320 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B21083261 : Blo 710320 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B2405591 : Blo 710320 2405591 := bstep (se 1 (by rfl) ⟨1804193, by rfl⟩ : syracuseStep 2405591 = 3608387) B3608387
theorem B3257639 : Blo 710320 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B800167 : Blo 710320 800167 := bstep (se 1 (by rfl) ⟨600125, by rfl⟩ : syracuseStep 800167 = 1200251) B1200251
theorem B3126817 : Blo 710320 3126817 := bstep (se 2 (by rfl) ⟨1172556, by rfl⟩ : syracuseStep 3126817 = 2345113) B2345113
theorem B964271 : Blo 710320 964271 := bstep (se 1 (by rfl) ⟨723203, by rfl⟩ : syracuseStep 964271 = 1446407) B1446407
theorem B800743 : Blo 710320 800743 := bstep (se 1 (by rfl) ⟨600557, by rfl⟩ : syracuseStep 800743 = 1201115) B1201115
theorem B6076579 : Blo 710320 6076579 := bstep (se 1 (by rfl) ⟨4557434, by rfl⟩ : syracuseStep 6076579 = 9114869) B9114869
theorem B899419 : Blo 710320 899419 := bstep (se 1 (by rfl) ⟨674564, by rfl⟩ : syracuseStep 899419 = 1349129) B1349129
theorem B1522145 : Blo 710320 1522145 := bstep (se 2 (by rfl) ⟨570804, by rfl⟩ : syracuseStep 1522145 = 1141609) B1141609
theorem B1522255 : Blo 710320 1522255 := bstep (se 1 (by rfl) ⟨1141691, by rfl⟩ : syracuseStep 1522255 = 2283383) B2283383
theorem B10566283 : Blo 710320 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B2702099 : Blo 710320 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B2702555 : Blo 710320 2702555 := bstep (se 1 (by rfl) ⟨2026916, by rfl⟩ : syracuseStep 2702555 = 4053833) B4053833
theorem B2407643 : Blo 710320 2407643 := bstep (se 1 (by rfl) ⟨1805732, by rfl⟩ : syracuseStep 2407643 = 3611465) B3611465
theorem B5422301 : Blo 710320 5422301 := bstep (se 3 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 5422301 = 2033363) B2033363
theorem B900391 : Blo 710320 900391 := bstep (se 1 (by rfl) ⟨675293, by rfl⟩ : syracuseStep 900391 = 1350587) B1350587
theorem B5127695 : Blo 710320 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B802399 : Blo 710320 802399 := bstep (se 1 (by rfl) ⟨601799, by rfl⟩ : syracuseStep 802399 = 1203599) B1203599
theorem B900715 : Blo 710320 900715 := bstep (se 1 (by rfl) ⟨675536, by rfl⟩ : syracuseStep 900715 = 1351073) B1351073
theorem B4570739 : Blo 710320 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B1785655 : Blo 710320 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B2408507 : Blo 710320 2408507 := bstep (se 1 (by rfl) ⟨1806380, by rfl⟩ : syracuseStep 2408507 = 3612761) B3612761
theorem B2408777 : Blo 710320 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B1065593 : Blo 710320 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B7684753 : Blo 710320 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B2704043 : Blo 710320 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B1065647 : Blo 710320 1065647 := bstep (se 1 (by rfl) ⟨799235, by rfl⟩ : syracuseStep 1065647 = 1598471) B1598471
theorem B1065695 : Blo 710320 1065695 := bstep (se 1 (by rfl) ⟨799271, by rfl⟩ : syracuseStep 1065695 = 1598543) B1598543
theorem B803551 : Blo 710320 803551 := bstep (se 1 (by rfl) ⟨602663, by rfl⟩ : syracuseStep 803551 = 1205327) B1205327
theorem B1065959 : Blo 710320 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B6833159 : Blo 710320 6833159 := bstep (se 1 (by rfl) ⟨5124869, by rfl⟩ : syracuseStep 6833159 = 10249739) B10249739
theorem B3425287 : Blo 710320 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B4572197 : Blo 710320 4572197 := bstep (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) B857287
theorem B7324769 : Blo 710320 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B1066217 : Blo 710320 1066217 := bstep (se 2 (by rfl) ⟨399831, by rfl⟩ : syracuseStep 1066217 = 799663) B799663
theorem B1066271 : Blo 710320 1066271 := bstep (se 1 (by rfl) ⟨799703, by rfl⟩ : syracuseStep 1066271 = 1599407) B1599407
theorem B902431 : Blo 710320 902431 := bstep (se 1 (by rfl) ⟨676823, by rfl⟩ : syracuseStep 902431 = 1353647) B1353647
theorem B2573707 : Blo 710320 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B1066439 : Blo 710320 1066439 := bstep (se 1 (by rfl) ⟨799829, by rfl⟩ : syracuseStep 1066439 = 1599659) B1599659
theorem B1525331 : Blo 710320 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B1066793 : Blo 710320 1066793 := bstep (se 2 (by rfl) ⟨400047, by rfl⟩ : syracuseStep 1066793 = 800095) B800095
theorem B1066799 : Blo 710320 1066799 := bstep (se 1 (by rfl) ⟨800099, by rfl⟩ : syracuseStep 1066799 = 1600199) B1600199
theorem B1067273 : Blo 710320 1067273 := bstep (se 2 (by rfl) ⟨400227, by rfl⟩ : syracuseStep 1067273 = 800455) B800455
theorem B1067375 : Blo 710320 1067375 := bstep (se 1 (by rfl) ⟨800531, by rfl⟩ : syracuseStep 1067375 = 1601063) B1601063
theorem B6506963 : Blo 710320 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B1067591 : Blo 710320 1067591 := bstep (se 1 (by rfl) ⟨800693, by rfl⟩ : syracuseStep 1067591 = 1601387) B1601387
theorem B1067627 : Blo 710320 1067627 := bstep (se 1 (by rfl) ⟨800720, by rfl⟩ : syracuseStep 1067627 = 1601441) B1601441
theorem B5557015 : Blo 710320 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B1067855 : Blo 710320 1067855 := bstep (se 1 (by rfl) ⟨800891, by rfl⟩ : syracuseStep 1067855 = 1601783) B1601783
theorem B4049959 : Blo 710320 4049959 := bstep (se 1 (by rfl) ⟨3037469, by rfl⟩ : syracuseStep 4049959 = 6074939) B6074939
theorem B2280487 : Blo 710320 2280487 := bstep (se 1 (by rfl) ⟨1710365, by rfl⟩ : syracuseStep 2280487 = 3420731) B3420731
theorem B1068251 : Blo 710320 1068251 := bstep (se 1 (by rfl) ⟨801188, by rfl⟩ : syracuseStep 1068251 = 1602377) B1602377
theorem B6081911 : Blo 710320 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B1068425 : Blo 710320 1068425 := bstep (se 2 (by rfl) ⟨400659, by rfl⟩ : syracuseStep 1068425 = 801319) B801319
theorem B2706959 : Blo 710320 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B1199711 : Blo 710320 1199711 := bstep (se 1 (by rfl) ⟨899783, by rfl⟩ : syracuseStep 1199711 = 1799567) B1799567
theorem B7294637 : Blo 710320 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B1068779 : Blo 710320 1068779 := bstep (se 1 (by rfl) ⟨801584, by rfl⟩ : syracuseStep 1068779 = 1603169) B1603169
theorem B1199927 : Blo 710320 1199927 := bstep (se 1 (by rfl) ⟨899945, by rfl⟩ : syracuseStep 1199927 = 1799891) B1799891
theorem B3035009 : Blo 710320 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B1069007 : Blo 710320 1069007 := bstep (se 1 (by rfl) ⟨801755, by rfl⟩ : syracuseStep 1069007 = 1603511) B1603511
theorem B5197891 : Blo 710320 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B1069403 : Blo 710320 1069403 := bstep (se 1 (by rfl) ⟨802052, by rfl⟩ : syracuseStep 1069403 = 1604105) B1604105
theorem B1200703 : Blo 710320 1200703 := bstep (se 1 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 1200703 = 1801055) B1801055
theorem B1069631 : Blo 710320 1069631 := bstep (se 1 (by rfl) ⟨802223, by rfl⟩ : syracuseStep 1069631 = 1604447) B1604447
theorem B1069751 : Blo 710320 1069751 := bstep (se 1 (by rfl) ⟨802313, by rfl⟩ : syracuseStep 1069751 = 1604627) B1604627
theorem B1069979 : Blo 710320 1069979 := bstep (se 1 (by rfl) ⟨802484, by rfl⟩ : syracuseStep 1069979 = 1604969) B1604969
theorem B1201385 : Blo 710320 1201385 := bstep (se 2 (by rfl) ⟨450519, by rfl⟩ : syracuseStep 1201385 = 901039) B901039
theorem B1201439 : Blo 710320 1201439 := bstep (se 1 (by rfl) ⟨901079, by rfl⟩ : syracuseStep 1201439 = 1802159) B1802159
theorem B1070375 : Blo 710320 1070375 := bstep (se 1 (by rfl) ⟨802781, by rfl⟩ : syracuseStep 1070375 = 1605563) B1605563
theorem B4576607 : Blo 710320 4576607 := bstep (se 1 (by rfl) ⟨3432455, by rfl⟩ : syracuseStep 4576607 = 6864911) B6864911
theorem B1070459 : Blo 710320 1070459 := bstep (se 1 (by rfl) ⟨802844, by rfl⟩ : syracuseStep 1070459 = 1605689) B1605689
theorem B1070585 : Blo 710320 1070585 := bstep (se 2 (by rfl) ⟨401469, by rfl⟩ : syracuseStep 1070585 = 802939) B802939
theorem B7722503 : Blo 710320 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1070687 : Blo 710320 1070687 := bstep (se 1 (by rfl) ⟨803015, by rfl⟩ : syracuseStep 1070687 = 1606031) B1606031
theorem B710367 : Blo 710320 710367 := bstep (se 1 (by rfl) ⟨532775, by rfl⟩ : syracuseStep 710367 = 1065551) B1065551
theorem B710447 : Blo 710320 710447 := bstep (se 1 (by rfl) ⟨532835, by rfl⟩ : syracuseStep 710447 = 1065671) B1065671
theorem B2283319 : Blo 710320 2283319 := bstep (se 1 (by rfl) ⟨1712489, by rfl⟩ : syracuseStep 2283319 = 3424979) B3424979
theorem B1070903 : Blo 710320 1070903 := bstep (se 1 (by rfl) ⟨803177, by rfl⟩ : syracuseStep 1070903 = 1606355) B1606355
theorem B710555 : Blo 710320 710555 := bstep (se 1 (by rfl) ⟨532916, by rfl⟩ : syracuseStep 710555 = 1065833) B1065833
theorem B710607 : Blo 710320 710607 := bstep (se 1 (by rfl) ⟨532955, by rfl⟩ : syracuseStep 710607 = 1065911) B1065911
theorem B710631 : Blo 710320 710631 := bstep (se 1 (by rfl) ⟨532973, by rfl⟩ : syracuseStep 710631 = 1065947) B1065947
theorem B1071209 : Blo 710320 1071209 := bstep (se 2 (by rfl) ⟨401703, by rfl⟩ : syracuseStep 1071209 = 803407) B803407
theorem B17356949 : Blo 710320 17356949 := bstep (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) B813607
theorem B710943 : Blo 710320 710943 := bstep (se 1 (by rfl) ⟨533207, by rfl⟩ : syracuseStep 710943 = 1066415) B1066415
theorem B711003 : Blo 710320 711003 := bstep (se 1 (by rfl) ⟨533252, by rfl⟩ : syracuseStep 711003 = 1066505) B1066505
theorem B711023 : Blo 710320 711023 := bstep (se 1 (by rfl) ⟨533267, by rfl⟩ : syracuseStep 711023 = 1066535) B1066535
theorem B711079 : Blo 710320 711079 := bstep (se 1 (by rfl) ⟨533309, by rfl⟩ : syracuseStep 711079 = 1066619) B1066619
theorem B3037607 : Blo 710320 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B711163 : Blo 710320 711163 := bstep (se 1 (by rfl) ⟨533372, by rfl⟩ : syracuseStep 711163 = 1066745) B1066745
theorem B711231 : Blo 710320 711231 := bstep (se 1 (by rfl) ⟨533423, by rfl⟩ : syracuseStep 711231 = 1066847) B1066847
theorem B1464895 : Blo 710320 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B711239 : Blo 710320 711239 := bstep (se 1 (by rfl) ⟨533429, by rfl⟩ : syracuseStep 711239 = 1066859) B1066859
theorem B2284139 : Blo 710320 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B1202809 : Blo 710320 1202809 := bstep (se 2 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 1202809 = 902107) B902107
theorem B6576815 : Blo 710320 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B1202863 : Blo 710320 1202863 := bstep (se 1 (by rfl) ⟨902147, by rfl⟩ : syracuseStep 1202863 = 1804295) B1804295
theorem B711391 : Blo 710320 711391 := bstep (se 1 (by rfl) ⟨533543, by rfl⟩ : syracuseStep 711391 = 1067087) B1067087
theorem B711471 : Blo 710320 711471 := bstep (se 1 (by rfl) ⟨533603, by rfl⟩ : syracuseStep 711471 = 1067207) B1067207
theorem B711579 : Blo 710320 711579 := bstep (se 1 (by rfl) ⟨533684, by rfl⟩ : syracuseStep 711579 = 1067369) B1067369
theorem B711631 : Blo 710320 711631 := bstep (se 1 (by rfl) ⟨533723, by rfl⟩ : syracuseStep 711631 = 1067447) B1067447
theorem B711655 : Blo 710320 711655 := bstep (se 1 (by rfl) ⟨533741, by rfl⟩ : syracuseStep 711655 = 1067483) B1067483
theorem B5495795 : Blo 710320 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B711967 : Blo 710320 711967 := bstep (se 1 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 711967 = 1067951) B1067951
theorem B712027 : Blo 710320 712027 := bstep (se 1 (by rfl) ⟨534020, by rfl⟩ : syracuseStep 712027 = 1068041) B1068041
theorem B712047 : Blo 710320 712047 := bstep (se 1 (by rfl) ⟨534035, by rfl⟩ : syracuseStep 712047 = 1068071) B1068071
theorem B712103 : Blo 710320 712103 := bstep (se 1 (by rfl) ⟨534077, by rfl⟩ : syracuseStep 712103 = 1068155) B1068155
theorem B712187 : Blo 710320 712187 := bstep (se 1 (by rfl) ⟨534140, by rfl⟩ : syracuseStep 712187 = 1068281) B1068281
theorem B3038735 : Blo 710320 3038735 := bstep (se 1 (by rfl) ⟨2279051, by rfl⟩ : syracuseStep 3038735 = 4558103) B4558103
theorem B712255 : Blo 710320 712255 := bstep (se 1 (by rfl) ⟨534191, by rfl⟩ : syracuseStep 712255 = 1068383) B1068383
theorem B712263 : Blo 710320 712263 := bstep (se 1 (by rfl) ⟨534197, by rfl⟩ : syracuseStep 712263 = 1068395) B1068395
theorem B712415 : Blo 710320 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1138411 : Blo 710320 1138411 := bstep (se 1 (by rfl) ⟨853808, by rfl⟩ : syracuseStep 1138411 = 1707617) B1707617
theorem B7790339 : Blo 710320 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B2711303 : Blo 710320 2711303 := bstep (se 1 (by rfl) ⟨2033477, by rfl⟩ : syracuseStep 2711303 = 4066955) B4066955
theorem B712495 : Blo 710320 712495 := bstep (se 1 (by rfl) ⟨534371, by rfl⟩ : syracuseStep 712495 = 1068743) B1068743
theorem B712603 : Blo 710320 712603 := bstep (se 1 (by rfl) ⟨534452, by rfl⟩ : syracuseStep 712603 = 1068905) B1068905
theorem B712655 : Blo 710320 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B712679 : Blo 710320 712679 := bstep (se 1 (by rfl) ⟨534509, by rfl⟩ : syracuseStep 712679 = 1069019) B1069019
theorem B6086663 : Blo 710320 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B7692407 : Blo 710320 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B712991 : Blo 710320 712991 := bstep (se 1 (by rfl) ⟨534743, by rfl⟩ : syracuseStep 712991 = 1069487) B1069487
theorem B713051 : Blo 710320 713051 := bstep (se 1 (by rfl) ⟨534788, by rfl⟩ : syracuseStep 713051 = 1069577) B1069577
theorem B1204571 : Blo 710320 1204571 := bstep (se 1 (by rfl) ⟨903428, by rfl⟩ : syracuseStep 1204571 = 1806857) B1806857
theorem B713071 : Blo 710320 713071 := bstep (se 1 (by rfl) ⟨534803, by rfl⟩ : syracuseStep 713071 = 1069607) B1069607
theorem B1204591 : Blo 710320 1204591 := bstep (se 1 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 1204591 = 1806887) B1806887
theorem B5136803 : Blo 710320 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B713127 : Blo 710320 713127 := bstep (se 1 (by rfl) ⟨534845, by rfl⟩ : syracuseStep 713127 = 1069691) B1069691
theorem B713211 : Blo 710320 713211 := bstep (se 1 (by rfl) ⟨534908, by rfl⟩ : syracuseStep 713211 = 1069817) B1069817
theorem B6152705 : Blo 710320 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B713279 : Blo 710320 713279 := bstep (se 1 (by rfl) ⟨534959, by rfl⟩ : syracuseStep 713279 = 1069919) B1069919
theorem B713287 : Blo 710320 713287 := bstep (se 1 (by rfl) ⟨534965, by rfl⟩ : syracuseStep 713287 = 1069931) B1069931
theorem B1204807 : Blo 710320 1204807 := bstep (se 1 (by rfl) ⟨903605, by rfl⟩ : syracuseStep 1204807 = 1807211) B1807211
theorem B1139321 : Blo 710320 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B43803287 : Blo 710320 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B713439 : Blo 710320 713439 := bstep (se 1 (by rfl) ⟨535079, by rfl⟩ : syracuseStep 713439 = 1070159) B1070159
theorem B713519 : Blo 710320 713519 := bstep (se 1 (by rfl) ⟨535139, by rfl⟩ : syracuseStep 713519 = 1070279) B1070279
theorem B1598363 : Blo 710320 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B713627 : Blo 710320 713627 := bstep (se 1 (by rfl) ⟨535220, by rfl⟩ : syracuseStep 713627 = 1070441) B1070441
theorem B12346273 : Blo 710320 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B713679 : Blo 710320 713679 := bstep (se 1 (by rfl) ⟨535259, by rfl⟩ : syracuseStep 713679 = 1070519) B1070519
theorem B2024423 : Blo 710320 2024423 := bstep (se 1 (by rfl) ⟨1518317, by rfl⟩ : syracuseStep 2024423 = 3036635) B3036635
theorem B713703 : Blo 710320 713703 := bstep (se 1 (by rfl) ⟨535277, by rfl⟩ : syracuseStep 713703 = 1070555) B1070555
theorem B1205239 : Blo 710320 1205239 := bstep (se 1 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 1205239 = 1807859) B1807859
theorem B6841381 : Blo 710320 6841381 := bstep (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) B1282759
theorem B1598561 : Blo 710320 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B1827983 : Blo 710320 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B714015 : Blo 710320 714015 := bstep (se 1 (by rfl) ⟨535511, by rfl⟩ : syracuseStep 714015 = 1071023) B1071023
theorem B1598759 : Blo 710320 1598759 := bstep (se 1 (by rfl) ⟨1199069, by rfl⟩ : syracuseStep 1598759 = 2398139) B2398139
theorem B8119601 : Blo 710320 8119601 := bstep (se 2 (by rfl) ⟨3044850, by rfl⟩ : syracuseStep 8119601 = 6089701) B6089701
theorem B714075 : Blo 710320 714075 := bstep (se 1 (by rfl) ⟨535556, by rfl⟩ : syracuseStep 714075 = 1071113) B1071113
theorem B714095 : Blo 710320 714095 := bstep (se 1 (by rfl) ⟨535571, by rfl⟩ : syracuseStep 714095 = 1071143) B1071143
theorem B714151 : Blo 710320 714151 := bstep (se 1 (by rfl) ⟨535613, by rfl⟩ : syracuseStep 714151 = 1071227) B1071227
theorem B714235 : Blo 710320 714235 := bstep (se 1 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 714235 = 1071353) B1071353
theorem B3892769 : Blo 710320 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B3597857 : Blo 710320 3597857 := bstep (se 2 (by rfl) ⟨1349196, by rfl⟩ : syracuseStep 3597857 = 2698393) B2698393
theorem B714303 : Blo 710320 714303 := bstep (se 1 (by rfl) ⟨535727, by rfl⟩ : syracuseStep 714303 = 1071455) B1071455
theorem B714311 : Blo 710320 714311 := bstep (se 1 (by rfl) ⟨535733, by rfl⟩ : syracuseStep 714311 = 1071467) B1071467
theorem B1599137 : Blo 710320 1599137 := bstep (se 2 (by rfl) ⟨599676, by rfl⟩ : syracuseStep 1599137 = 1199353) B1199353
theorem B1599497 : Blo 710320 1599497 := bstep (se 2 (by rfl) ⟨599811, by rfl⟩ : syracuseStep 1599497 = 1199623) B1199623
theorem B15395183 : Blo 710320 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B1599911 : Blo 710320 1599911 := bstep (se 1 (by rfl) ⟨1199933, by rfl⟩ : syracuseStep 1599911 = 2399867) B2399867
theorem B1600019 : Blo 710320 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B1600073 : Blo 710320 1600073 := bstep (se 2 (by rfl) ⟨600027, by rfl⟩ : syracuseStep 1600073 = 1200055) B1200055
theorem B3041981 : Blo 710320 3041981 := bstep (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) B1140743
theorem B1600487 : Blo 710320 1600487 := bstep (se 1 (by rfl) ⟨1200365, by rfl⟩ : syracuseStep 1600487 = 2400731) B2400731
theorem B1829879 : Blo 710320 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B5139571 : Blo 710320 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B13200653 : Blo 710320 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B1600865 : Blo 710320 1600865 := bstep (se 2 (by rfl) ⟨600324, by rfl⟩ : syracuseStep 1600865 = 1200649) B1200649
theorem B814447 : Blo 710320 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B1600955 : Blo 710320 1600955 := bstep (se 1 (by rfl) ⟨1200716, by rfl⟩ : syracuseStep 1600955 = 2401433) B2401433
theorem B2026939 : Blo 710320 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B1601081 : Blo 710320 1601081 := bstep (se 2 (by rfl) ⟨600405, by rfl⟩ : syracuseStep 1601081 = 1200811) B1200811
theorem B1601747 : Blo 710320 1601747 := bstep (se 1 (by rfl) ⟨1201310, by rfl⟩ : syracuseStep 1601747 = 2402621) B2402621
theorem B1601801 : Blo 710320 1601801 := bstep (se 2 (by rfl) ⟨600675, by rfl⟩ : syracuseStep 1601801 = 1201351) B1201351
theorem B12185963 : Blo 710320 12185963 := bstep (se 1 (by rfl) ⟨9139472, by rfl⟩ : syracuseStep 12185963 = 18278945) B18278945
theorem B1798625 : Blo 710320 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B1602017 : Blo 710320 1602017 := bstep (se 2 (by rfl) ⟨600756, by rfl⟩ : syracuseStep 1602017 = 1201513) B1201513
theorem B2028215 : Blo 710320 2028215 := bstep (se 1 (by rfl) ⟨1521161, by rfl⟩ : syracuseStep 2028215 = 3042323) B3042323
theorem B1602323 : Blo 710320 1602323 := bstep (se 1 (by rfl) ⟨1201742, by rfl⟩ : syracuseStep 1602323 = 2403485) B2403485
theorem B4059983 : Blo 710320 4059983 := bstep (se 1 (by rfl) ⟨3044987, by rfl⟩ : syracuseStep 4059983 = 6089975) B6089975
theorem B6091685 : Blo 710320 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B1799131 : Blo 710320 1799131 := bstep (se 1 (by rfl) ⟨1349348, by rfl⟩ : syracuseStep 1799131 = 2698697) B2698697
theorem B1602683 : Blo 710320 1602683 := bstep (se 1 (by rfl) ⟨1202012, by rfl⟩ : syracuseStep 1602683 = 2404025) B2404025
theorem B26277011 : Blo 710320 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B1602809 : Blo 710320 1602809 := bstep (se 2 (by rfl) ⟨601053, by rfl⟩ : syracuseStep 1602809 = 1202107) B1202107
theorem B1799455 : Blo 710320 1799455 := bstep (se 1 (by rfl) ⟨1349591, by rfl⟩ : syracuseStep 1799455 = 2699183) B2699183
theorem B1602953 : Blo 710320 1602953 := bstep (se 2 (by rfl) ⟨601107, by rfl⟩ : syracuseStep 1602953 = 1202215) B1202215
theorem B2028989 : Blo 710320 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B1603079 : Blo 710320 1603079 := bstep (se 1 (by rfl) ⟨1202309, by rfl⟩ : syracuseStep 1603079 = 2404619) B2404619
theorem B1603259 : Blo 710320 1603259 := bstep (se 1 (by rfl) ⟨1202444, by rfl⟩ : syracuseStep 1603259 = 2404889) B2404889
theorem B3602231 : Blo 710320 3602231 := bstep (se 1 (by rfl) ⟨2701673, by rfl⟩ : syracuseStep 3602231 = 5403347) B5403347
theorem B1603385 : Blo 710320 1603385 := bstep (se 2 (by rfl) ⟨601269, by rfl⟩ : syracuseStep 1603385 = 1202539) B1202539
theorem B76904549 : Blo 710320 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B3602717 : Blo 710320 3602717 := bstep (se 3 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 3602717 = 1351019) B1351019
theorem B1800539 : Blo 710320 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B1604015 : Blo 710320 1604015 := bstep (se 1 (by rfl) ⟨1203011, by rfl⟩ : syracuseStep 1604015 = 2406023) B2406023
theorem B4061623 : Blo 710320 4061623 := bstep (se 1 (by rfl) ⟨3046217, by rfl⟩ : syracuseStep 4061623 = 6092435) B6092435
theorem B12155345 : Blo 710320 12155345 := bstep (se 2 (by rfl) ⟨4558254, by rfl⟩ : syracuseStep 12155345 = 9116509) B9116509
theorem B1604051 : Blo 710320 1604051 := bstep (se 1 (by rfl) ⟨1203038, by rfl⟩ : syracuseStep 1604051 = 2406077) B2406077
theorem B1604159 : Blo 710320 1604159 := bstep (se 1 (by rfl) ⟨1203119, by rfl⟩ : syracuseStep 1604159 = 2406239) B2406239
theorem B5405291 : Blo 710320 5405291 := bstep (se 1 (by rfl) ⟨4053968, by rfl⟩ : syracuseStep 5405291 = 8107937) B8107937
theorem B1604267 : Blo 710320 1604267 := bstep (se 1 (by rfl) ⟨1203200, by rfl⟩ : syracuseStep 1604267 = 2406401) B2406401
theorem B2030255 : Blo 710320 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B20544677 : Blo 710320 20544677 := bstep (se 4 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 20544677 = 3852127) B3852127
theorem B1604807 : Blo 710320 1604807 := bstep (se 1 (by rfl) ⟨1203605, by rfl⟩ : syracuseStep 1604807 = 2407211) B2407211
theorem B1801511 : Blo 710320 1801511 := bstep (se 1 (by rfl) ⟨1351133, by rfl⟩ : syracuseStep 1801511 = 2702267) B2702267
theorem B1604987 : Blo 710320 1604987 := bstep (se 1 (by rfl) ⟨1203740, by rfl⟩ : syracuseStep 1604987 = 2407481) B2407481
theorem B1605113 : Blo 710320 1605113 := bstep (se 2 (by rfl) ⟨601917, by rfl⟩ : syracuseStep 1605113 = 1203835) B1203835
theorem B1605203 : Blo 710320 1605203 := bstep (se 1 (by rfl) ⟨1203902, by rfl⟩ : syracuseStep 1605203 = 2407805) B2407805
theorem B1605383 : Blo 710320 1605383 := bstep (se 1 (by rfl) ⟨1204037, by rfl⟩ : syracuseStep 1605383 = 2408075) B2408075
theorem B2031655 : Blo 710320 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B1605671 : Blo 710320 1605671 := bstep (se 1 (by rfl) ⟨1204253, by rfl⟩ : syracuseStep 1605671 = 2408507) B2408507
theorem B1605851 : Blo 710320 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B1802695 : Blo 710320 1802695 := bstep (se 1 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 1802695 = 2704043) B2704043
theorem B1606121 : Blo 710320 1606121 := bstep (se 2 (by rfl) ⟨602295, by rfl⟩ : syracuseStep 1606121 = 1204591) B1204591
theorem B6095411 : Blo 710320 6095411 := bstep (se 1 (by rfl) ⟨4571558, by rfl⟩ : syracuseStep 6095411 = 9143117) B9143117
theorem B4555385 : Blo 710320 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B4555439 : Blo 710320 4555439 := bstep (se 1 (by rfl) ⟨3416579, by rfl⟩ : syracuseStep 4555439 = 6833159) B6833159
theorem B3048131 : Blo 710320 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B4883179 : Blo 710320 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B1606409 : Blo 710320 1606409 := bstep (se 2 (by rfl) ⟨602403, by rfl⟩ : syracuseStep 1606409 = 1204807) B1204807
theorem B1016887 : Blo 710320 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B1606985 : Blo 710320 1606985 := bstep (se 2 (by rfl) ⟨602619, by rfl⟩ : syracuseStep 1606985 = 1205239) B1205239
theorem B2033171 : Blo 710320 2033171 := bstep (se 1 (by rfl) ⟨1524878, by rfl⟩ : syracuseStep 2033171 = 3049757) B3049757
theorem B4065065 : Blo 710320 4065065 := bstep (se 2 (by rfl) ⟨1524399, by rfl⟩ : syracuseStep 4065065 = 3048799) B3048799
theorem B75171685 : Blo 710320 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B1804639 : Blo 710320 1804639 := bstep (se 1 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 1804639 = 2706959) B2706959
theorem B855019 : Blo 710320 855019 := bstep (se 1 (by rfl) ⟨641264, by rfl⟩ : syracuseStep 855019 = 1282529) B1282529
theorem B3051071 : Blo 710320 3051071 := bstep (se 1 (by rfl) ⟨2288303, by rfl⟩ : syracuseStep 3051071 = 4576607) B4576607
theorem B5148335 : Blo 710320 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B5410637 : Blo 710320 5410637 := bstep (se 3 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 5410637 = 2028989) B2028989
theorem B11571299 : Blo 710320 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B6852761 : Blo 710320 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B1085929 : Blo 710320 1085929 := bstep (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) B814447
theorem B1807535 : Blo 710320 1807535 := bstep (se 1 (by rfl) ⟨1355651, by rfl⟩ : syracuseStep 1807535 = 2711303) B2711303
theorem B4691297 : Blo 710320 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B4330871 : Blo 710320 4330871 := bstep (se 1 (by rfl) ⟨3248153, by rfl⟩ : syracuseStep 4330871 = 6496307) B6496307
theorem B4101803 : Blo 710320 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B759547 : Blo 710320 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B29202191 : Blo 710320 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B1349615 : Blo 710320 1349615 := bstep (se 1 (by rfl) ⟨1012211, by rfl⟩ : syracuseStep 1349615 = 2024423) B2024423
theorem B1218655 : Blo 710320 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B5413067 : Blo 710320 5413067 := bstep (se 1 (by rfl) ⟨4059800, by rfl⟩ : syracuseStep 5413067 = 8119601) B8119601
theorem B2595179 : Blo 710320 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B2398571 : Blo 710320 2398571 := bstep (se 1 (by rfl) ⟨1798928, by rfl⟩ : syracuseStep 2398571 = 3597857) B3597857
theorem B7707109 : Blo 710320 7707109 := bstep (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) B1445083
theorem B2398841 : Blo 710320 2398841 := bstep (se 2 (by rfl) ⟨899565, by rfl⟩ : syracuseStep 2398841 = 1799131) B1799131
theorem B1710953 : Blo 710320 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B41098103 : Blo 710320 41098103 := bstep (se 1 (by rfl) ⟨30823577, by rfl⟩ : syracuseStep 41098103 = 61647155) B61647155
theorem B2431903 : Blo 710320 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B10263455 : Blo 710320 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B2399273 : Blo 710320 2399273 := bstep (se 2 (by rfl) ⟨899727, by rfl⟩ : syracuseStep 2399273 = 1799455) B1799455
theorem B1219919 : Blo 710320 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B4169089 : Blo 710320 4169089 := bstep (se 2 (by rfl) ⟨1563408, by rfl⟩ : syracuseStep 4169089 = 3126817) B3126817
theorem B2432423 : Blo 710320 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B9772487 : Blo 710320 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B8102105 : Blo 710320 8102105 := bstep (se 2 (by rfl) ⟨3038289, by rfl⟩ : syracuseStep 8102105 = 6076579) B6076579
theorem B1352143 : Blo 710320 1352143 := bstep (se 1 (by rfl) ⟨1014107, by rfl⟩ : syracuseStep 1352143 = 2028215) B2028215
theorem B5415497 : Blo 710320 5415497 := bstep (se 2 (by rfl) ⟨2030811, by rfl⟩ : syracuseStep 5415497 = 4061623) B4061623
theorem B5776541 : Blo 710320 5776541 := bstep (se 3 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 5776541 = 2166203) B2166203
theorem B2401487 : Blo 710320 2401487 := bstep (se 1 (by rfl) ⟨1801115, by rfl⟩ : syracuseStep 2401487 = 3602231) B3602231
theorem B2401811 : Blo 710320 2401811 := bstep (se 1 (by rfl) ⟨1801358, by rfl⟩ : syracuseStep 2401811 = 3602717) B3602717
theorem B8103563 : Blo 710320 8103563 := bstep (se 1 (by rfl) ⟨6077672, by rfl⟩ : syracuseStep 8103563 = 12155345) B12155345
theorem B1353503 : Blo 710320 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B3614867 : Blo 710320 3614867 := bstep (se 1 (by rfl) ⟨2711150, by rfl⟩ : syracuseStep 3614867 = 5422301) B5422301
theorem B1517881 : Blo 710320 1517881 := bstep (se 2 (by rfl) ⟨569205, by rfl⟩ : syracuseStep 1517881 = 1138411) B1138411
theorem B3418463 : Blo 710320 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B2402999 : Blo 710320 2402999 := bstep (se 1 (by rfl) ⟨1802249, by rfl⟩ : syracuseStep 2402999 = 3604499) B3604499
theorem B4567049 : Blo 710320 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B9121841 : Blo 710320 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B4337975 : Blo 710320 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B2404943 : Blo 710320 2404943 := bstep (se 1 (by rfl) ⟨1803707, by rfl⟩ : syracuseStep 2404943 = 3607415) B3607415
theorem B5419871 : Blo 710320 5419871 := bstep (se 1 (by rfl) ⟨4064903, by rfl⟩ : syracuseStep 5419871 = 8129807) B8129807
theorem B799807 : Blo 710320 799807 := bstep (se 1 (by rfl) ⟨599855, by rfl⟩ : syracuseStep 799807 = 1199711) B1199711
theorem B2405483 : Blo 710320 2405483 := bstep (se 1 (by rfl) ⟨1804112, by rfl⟩ : syracuseStep 2405483 = 3608225) B3608225
theorem B4863091 : Blo 710320 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B799951 : Blo 710320 799951 := bstep (se 1 (by rfl) ⟨599963, by rfl⟩ : syracuseStep 799951 = 1199927) B1199927
theorem B10270151 : Blo 710320 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B34748149 : Blo 710320 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B6928175 : Blo 710320 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B800923 : Blo 710320 800923 := bstep (se 1 (by rfl) ⟨600692, by rfl⟩ : syracuseStep 800923 = 1201385) B1201385
theorem B800959 : Blo 710320 800959 := bstep (se 1 (by rfl) ⟨600719, by rfl⟩ : syracuseStep 800959 = 1201439) B1201439
theorem B3422537 : Blo 710320 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B2406779 : Blo 710320 2406779 := bstep (se 1 (by rfl) ⟨1805084, by rfl⟩ : syracuseStep 2406779 = 3610169) B3610169
theorem B2407049 : Blo 710320 2407049 := bstep (se 2 (by rfl) ⟨902643, by rfl⟩ : syracuseStep 2407049 = 1805287) B1805287
theorem B4111127 : Blo 710320 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B29637413 : Blo 710320 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B1096751 : Blo 710320 1096751 := bstep (se 1 (by rfl) ⟨822563, by rfl⟩ : syracuseStep 1096751 = 1645127) B1645127
theorem B2571389 : Blo 710320 2571389 := bstep (se 3 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 2571389 = 964271) B964271
theorem B150060221 : Blo 710320 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B2702585 : Blo 710320 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B4046111 : Blo 710320 4046111 := bstep (se 1 (by rfl) ⟨3034583, by rfl⟩ : syracuseStep 4046111 = 6069167) B6069167
theorem B65846789 : Blo 710320 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B17284751 : Blo 710320 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B2408183 : Blo 710320 2408183 := bstep (se 1 (by rfl) ⟨1806137, by rfl⟩ : syracuseStep 2408183 = 3612275) B3612275
theorem B5193559 : Blo 710320 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B4570967 : Blo 710320 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B5128271 : Blo 710320 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B6930521 : Blo 710320 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B4571275 : Blo 710320 4571275 := bstep (se 1 (by rfl) ⟨3428456, by rfl⟩ : syracuseStep 4571275 = 6856913) B6856913
theorem B803047 : Blo 710320 803047 := bstep (se 1 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 803047 = 1204571) B1204571
theorem B3424535 : Blo 710320 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B1065575 : Blo 710320 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B1065707 : Blo 710320 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B1065737 : Blo 710320 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B2409263 : Blo 710320 2409263 := bstep (se 1 (by rfl) ⟨1806947, by rfl⟩ : syracuseStep 2409263 = 3613895) B3613895
theorem B1065839 : Blo 710320 1065839 := bstep (se 1 (by rfl) ⟨799379, by rfl⟩ : syracuseStep 1065839 = 1598759) B1598759
theorem B2409371 : Blo 710320 2409371 := bstep (se 1 (by rfl) ⟨1807028, by rfl⟩ : syracuseStep 2409371 = 3614057) B3614057
theorem B3851219 : Blo 710320 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B1066091 : Blo 710320 1066091 := bstep (se 1 (by rfl) ⟨799568, by rfl⟩ : syracuseStep 1066091 = 1599137) B1599137
theorem B1066331 : Blo 710320 1066331 := bstep (se 1 (by rfl) ⟨799748, by rfl⟩ : syracuseStep 1066331 = 1599497) B1599497
theorem B1066607 : Blo 710320 1066607 := bstep (se 1 (by rfl) ⟨799955, by rfl⟩ : syracuseStep 1066607 = 1599911) B1599911
theorem B1066679 : Blo 710320 1066679 := bstep (se 1 (by rfl) ⟨800009, by rfl⟩ : syracuseStep 1066679 = 1600019) B1600019
theorem B1066715 : Blo 710320 1066715 := bstep (se 1 (by rfl) ⟨800036, by rfl⟩ : syracuseStep 1066715 = 1600073) B1600073
theorem B1066889 : Blo 710320 1066889 := bstep (se 2 (by rfl) ⟨400083, by rfl⟩ : syracuseStep 1066889 = 800167) B800167
theorem B1066991 : Blo 710320 1066991 := bstep (se 1 (by rfl) ⟨800243, by rfl⟩ : syracuseStep 1066991 = 1600487) B1600487
theorem B2410505 : Blo 710320 2410505 := bstep (se 2 (by rfl) ⟨903939, by rfl⟩ : syracuseStep 2410505 = 1807879) B1807879
theorem B8800435 : Blo 710320 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B1067243 : Blo 710320 1067243 := bstep (se 1 (by rfl) ⟨800432, by rfl⟩ : syracuseStep 1067243 = 1600865) B1600865
theorem B903403 : Blo 710320 903403 := bstep (se 1 (by rfl) ⟨677552, by rfl⟩ : syracuseStep 903403 = 1355105) B1355105
theorem B1067303 : Blo 710320 1067303 := bstep (se 1 (by rfl) ⟨800477, by rfl⟩ : syracuseStep 1067303 = 1600955) B1600955
theorem B1067387 : Blo 710320 1067387 := bstep (se 1 (by rfl) ⟨800540, by rfl⟩ : syracuseStep 1067387 = 1601081) B1601081
theorem B1067657 : Blo 710320 1067657 := bstep (se 2 (by rfl) ⟨400371, by rfl⟩ : syracuseStep 1067657 = 800743) B800743
theorem B7719563 : Blo 710320 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B1067831 : Blo 710320 1067831 := bstep (se 1 (by rfl) ⟨800873, by rfl⟩ : syracuseStep 1067831 = 1601747) B1601747
theorem B1067867 : Blo 710320 1067867 := bstep (se 1 (by rfl) ⟨800900, by rfl⟩ : syracuseStep 1067867 = 1601801) B1601801
theorem B1199083 : Blo 710320 1199083 := bstep (se 1 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 1199083 = 1798625) B1798625
theorem B1068011 : Blo 710320 1068011 := bstep (se 1 (by rfl) ⟨801008, by rfl⟩ : syracuseStep 1068011 = 1602017) B1602017
theorem B1199225 : Blo 710320 1199225 := bstep (se 2 (by rfl) ⟨449709, by rfl⟩ : syracuseStep 1199225 = 899419) B899419
theorem B1068215 : Blo 710320 1068215 := bstep (se 1 (by rfl) ⟨801161, by rfl⟩ : syracuseStep 1068215 = 1602323) B1602323
theorem B2706655 : Blo 710320 2706655 := bstep (se 1 (by rfl) ⟨2029991, by rfl⟩ : syracuseStep 2706655 = 4059983) B4059983
theorem B1068455 : Blo 710320 1068455 := bstep (se 1 (by rfl) ⟨801341, by rfl⟩ : syracuseStep 1068455 = 1602683) B1602683
theorem B1953193 : Blo 710320 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B17518007 : Blo 710320 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B1068539 : Blo 710320 1068539 := bstep (se 1 (by rfl) ⟨801404, by rfl⟩ : syracuseStep 1068539 = 1602809) B1602809
theorem B1068635 : Blo 710320 1068635 := bstep (se 1 (by rfl) ⟨801476, by rfl⟩ : syracuseStep 1068635 = 1602953) B1602953
theorem B1068719 : Blo 710320 1068719 := bstep (se 1 (by rfl) ⟨801539, by rfl⟩ : syracuseStep 1068719 = 1603079) B1603079
theorem B1068839 : Blo 710320 1068839 := bstep (se 1 (by rfl) ⟨801629, by rfl⟩ : syracuseStep 1068839 = 1603259) B1603259
theorem B1068923 : Blo 710320 1068923 := bstep (se 1 (by rfl) ⟨801692, by rfl⟩ : syracuseStep 1068923 = 1603385) B1603385
theorem B51269699 : Blo 710320 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B1200359 : Blo 710320 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B1069343 : Blo 710320 1069343 := bstep (se 1 (by rfl) ⟨802007, by rfl⟩ : syracuseStep 1069343 = 1604015) B1604015
theorem B9523493 : Blo 710320 9523493 := bstep (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) B1785655
theorem B1069367 : Blo 710320 1069367 := bstep (se 1 (by rfl) ⟨802025, by rfl⟩ : syracuseStep 1069367 = 1604051) B1604051
theorem B1069439 : Blo 710320 1069439 := bstep (se 1 (by rfl) ⟨802079, by rfl⟩ : syracuseStep 1069439 = 1604159) B1604159
theorem B1200521 : Blo 710320 1200521 := bstep (se 2 (by rfl) ⟨450195, by rfl⟩ : syracuseStep 1200521 = 900391) B900391
theorem B1069511 : Blo 710320 1069511 := bstep (se 1 (by rfl) ⟨802133, by rfl⟩ : syracuseStep 1069511 = 1604267) B1604267
theorem B1069865 : Blo 710320 1069865 := bstep (se 2 (by rfl) ⟨401199, by rfl⟩ : syracuseStep 1069865 = 802399) B802399
theorem B1069871 : Blo 710320 1069871 := bstep (se 1 (by rfl) ⟨802403, by rfl⟩ : syracuseStep 1069871 = 1604807) B1604807
theorem B1200953 : Blo 710320 1200953 := bstep (se 2 (by rfl) ⟨450357, by rfl⟩ : syracuseStep 1200953 = 900715) B900715
theorem B1201007 : Blo 710320 1201007 := bstep (se 1 (by rfl) ⟨900755, by rfl⟩ : syracuseStep 1201007 = 1801511) B1801511
theorem B1069991 : Blo 710320 1069991 := bstep (se 1 (by rfl) ⟨802493, by rfl⟩ : syracuseStep 1069991 = 1604987) B1604987
theorem B1070075 : Blo 710320 1070075 := bstep (se 1 (by rfl) ⟨802556, by rfl⟩ : syracuseStep 1070075 = 1605113) B1605113
theorem B1070135 : Blo 710320 1070135 := bstep (se 1 (by rfl) ⟨802601, by rfl⟩ : syracuseStep 1070135 = 1605203) B1605203
theorem B1070255 : Blo 710320 1070255 := bstep (se 1 (by rfl) ⟨802691, by rfl⟩ : syracuseStep 1070255 = 1605383) B1605383
theorem B6837655 : Blo 710320 6837655 := bstep (se 1 (by rfl) ⟨5128241, by rfl⟩ : syracuseStep 6837655 = 10256483) B10256483
theorem B1070663 : Blo 710320 1070663 := bstep (se 1 (by rfl) ⟨802997, by rfl⟩ : syracuseStep 1070663 = 1605995) B1605995
theorem B1070759 : Blo 710320 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B710395 : Blo 710320 710395 := bstep (se 1 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 710395 = 1065593) B1065593
theorem B1070843 : Blo 710320 1070843 := bstep (se 1 (by rfl) ⟨803132, by rfl⟩ : syracuseStep 1070843 = 1606265) B1606265
theorem B710431 : Blo 710320 710431 := bstep (se 1 (by rfl) ⟨532823, by rfl⟩ : syracuseStep 710431 = 1065647) B1065647
theorem B1070879 : Blo 710320 1070879 := bstep (se 1 (by rfl) ⟨803159, by rfl⟩ : syracuseStep 1070879 = 1606319) B1606319
theorem B710463 : Blo 710320 710463 := bstep (se 1 (by rfl) ⟨532847, by rfl⟩ : syracuseStep 710463 = 1065695) B1065695
theorem B1201999 : Blo 710320 1201999 := bstep (se 1 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 1201999 = 1802999) B1802999
theorem B1070927 : Blo 710320 1070927 := bstep (se 1 (by rfl) ⟨803195, by rfl⟩ : syracuseStep 1070927 = 1606391) B1606391
theorem B1071047 : Blo 710320 1071047 := bstep (se 1 (by rfl) ⟨803285, by rfl⟩ : syracuseStep 1071047 = 1606571) B1606571
theorem B710639 : Blo 710320 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B710811 : Blo 710320 710811 := bstep (se 1 (by rfl) ⟨533108, by rfl⟩ : syracuseStep 710811 = 1066217) B1066217
theorem B710847 : Blo 710320 710847 := bstep (se 1 (by rfl) ⟨533135, by rfl⟩ : syracuseStep 710847 = 1066271) B1066271
theorem B10246337 : Blo 710320 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B1202411 : Blo 710320 1202411 := bstep (se 1 (by rfl) ⟨901808, by rfl⟩ : syracuseStep 1202411 = 1803617) B1803617
theorem B1071401 : Blo 710320 1071401 := bstep (se 2 (by rfl) ⟨401775, by rfl⟩ : syracuseStep 1071401 = 803551) B803551
theorem B710959 : Blo 710320 710959 := bstep (se 1 (by rfl) ⟨533219, by rfl⟩ : syracuseStep 710959 = 1066439) B1066439
theorem B1071407 : Blo 710320 1071407 := bstep (se 1 (by rfl) ⟨803555, by rfl⟩ : syracuseStep 1071407 = 1607111) B1607111
theorem B711195 : Blo 710320 711195 := bstep (se 1 (by rfl) ⟨533396, by rfl⟩ : syracuseStep 711195 = 1066793) B1066793
theorem B711199 : Blo 710320 711199 := bstep (se 1 (by rfl) ⟨533399, by rfl⟩ : syracuseStep 711199 = 1066799) B1066799
theorem B711515 : Blo 710320 711515 := bstep (se 1 (by rfl) ⟨533636, by rfl⟩ : syracuseStep 711515 = 1067273) B1067273
theorem B711583 : Blo 710320 711583 := bstep (se 1 (by rfl) ⟨533687, by rfl⟩ : syracuseStep 711583 = 1067375) B1067375
theorem B6085601 : Blo 710320 6085601 := bstep (se 2 (by rfl) ⟨2282100, by rfl⟩ : syracuseStep 6085601 = 4564201) B4564201
theorem B1203241 : Blo 710320 1203241 := bstep (se 2 (by rfl) ⟨451215, by rfl⟩ : syracuseStep 1203241 = 902431) B902431
theorem B711727 : Blo 710320 711727 := bstep (se 1 (by rfl) ⟨533795, by rfl⟩ : syracuseStep 711727 = 1067591) B1067591
theorem B711751 : Blo 710320 711751 := bstep (se 1 (by rfl) ⟨533813, by rfl⟩ : syracuseStep 711751 = 1067627) B1067627
theorem B1203383 : Blo 710320 1203383 := bstep (se 1 (by rfl) ⟨902537, by rfl⟩ : syracuseStep 1203383 = 1805075) B1805075
theorem B3431609 : Blo 710320 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B711903 : Blo 710320 711903 := bstep (se 1 (by rfl) ⟨533927, by rfl⟩ : syracuseStep 711903 = 1067855) B1067855
theorem B2284793 : Blo 710320 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B4054333 : Blo 710320 4054333 := bstep (se 3 (by rfl) ⟨760187, by rfl⟩ : syracuseStep 4054333 = 1520375) B1520375
theorem B712167 : Blo 710320 712167 := bstep (se 1 (by rfl) ⟨534125, by rfl⟩ : syracuseStep 712167 = 1068251) B1068251
theorem B2711015 : Blo 710320 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B1203707 : Blo 710320 1203707 := bstep (se 1 (by rfl) ⟨902780, by rfl⟩ : syracuseStep 1203707 = 1805561) B1805561
theorem B4054607 : Blo 710320 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B712283 : Blo 710320 712283 := bstep (se 1 (by rfl) ⟨534212, by rfl⟩ : syracuseStep 712283 = 1068425) B1068425
theorem B7298657 : Blo 710320 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B1138283 : Blo 710320 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B712519 : Blo 710320 712519 := bstep (se 1 (by rfl) ⟨534389, by rfl⟩ : syracuseStep 712519 = 1068779) B1068779
theorem B21880685 : Blo 710320 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B1204139 : Blo 710320 1204139 := bstep (se 1 (by rfl) ⟨903104, by rfl⟩ : syracuseStep 1204139 = 1806209) B1806209
theorem B712671 : Blo 710320 712671 := bstep (se 1 (by rfl) ⟨534503, by rfl⟩ : syracuseStep 712671 = 1069007) B1069007
theorem B712935 : Blo 710320 712935 := bstep (se 1 (by rfl) ⟨534701, by rfl⟩ : syracuseStep 712935 = 1069403) B1069403
theorem B56222029 : Blo 710320 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B2285921 : Blo 710320 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B713087 : Blo 710320 713087 := bstep (se 1 (by rfl) ⟨534815, by rfl⟩ : syracuseStep 713087 = 1069631) B1069631
theorem B1204679 : Blo 710320 1204679 := bstep (se 1 (by rfl) ⟨903509, by rfl⟩ : syracuseStep 1204679 = 1807019) B1807019
theorem B713167 : Blo 710320 713167 := bstep (se 1 (by rfl) ⟨534875, by rfl⟩ : syracuseStep 713167 = 1069751) B1069751
theorem B5202505 : Blo 710320 5202505 := bstep (se 2 (by rfl) ⟨1950939, by rfl⟩ : syracuseStep 5202505 = 3901879) B3901879
theorem B713319 : Blo 710320 713319 := bstep (se 1 (by rfl) ⟨534989, by rfl⟩ : syracuseStep 713319 = 1069979) B1069979
theorem B1598255 : Blo 710320 1598255 := bstep (se 1 (by rfl) ⟨1198691, by rfl⟩ : syracuseStep 1598255 = 2397383) B2397383
theorem B713583 : Blo 710320 713583 := bstep (se 1 (by rfl) ⟨535187, by rfl⟩ : syracuseStep 713583 = 1070375) B1070375
theorem B713639 : Blo 710320 713639 := bstep (se 1 (by rfl) ⟨535229, by rfl⟩ : syracuseStep 713639 = 1070459) B1070459
theorem B713723 : Blo 710320 713723 := bstep (se 1 (by rfl) ⟨535292, by rfl⟩ : syracuseStep 713723 = 1070585) B1070585
theorem B713791 : Blo 710320 713791 := bstep (se 1 (by rfl) ⟨535343, by rfl⟩ : syracuseStep 713791 = 1070687) B1070687
theorem B713935 : Blo 710320 713935 := bstep (se 1 (by rfl) ⟨535451, by rfl⟩ : syracuseStep 713935 = 1070903) B1070903
theorem B5399945 : Blo 710320 5399945 := bstep (se 2 (by rfl) ⟨2024979, by rfl⟩ : syracuseStep 5399945 = 4049959) B4049959
theorem B3040649 : Blo 710320 3040649 := bstep (se 2 (by rfl) ⟨1140243, by rfl⟩ : syracuseStep 3040649 = 2280487) B2280487
theorem B714139 : Blo 710320 714139 := bstep (se 1 (by rfl) ⟨535604, by rfl⟩ : syracuseStep 714139 = 1071209) B1071209
theorem B2025071 : Blo 710320 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B1599263 : Blo 710320 1599263 := bstep (se 1 (by rfl) ⟨1199447, by rfl⟩ : syracuseStep 1599263 = 2398895) B2398895
theorem B4384543 : Blo 710320 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B2287561 : Blo 710320 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B1599479 : Blo 710320 1599479 := bstep (se 1 (by rfl) ⟨1199609, by rfl⟩ : syracuseStep 1599479 = 2399219) B2399219
theorem B3663863 : Blo 710320 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B2025481 : Blo 710320 2025481 := bstep (se 2 (by rfl) ⟨759555, by rfl⟩ : syracuseStep 2025481 = 1519111) B1519111
theorem B1599839 : Blo 710320 1599839 := bstep (se 1 (by rfl) ⟨1199879, by rfl⟩ : syracuseStep 1599839 = 2399759) B2399759
theorem B2025823 : Blo 710320 2025823 := bstep (se 1 (by rfl) ⟨1519367, by rfl⟩ : syracuseStep 2025823 = 3038735) B3038735
theorem B4680119 : Blo 710320 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B4057775 : Blo 710320 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B1600559 : Blo 710320 1600559 := bstep (se 1 (by rfl) ⟨1200419, by rfl⟩ : syracuseStep 1600559 = 2400839) B2400839
theorem B1600847 : Blo 710320 1600847 := bstep (se 1 (by rfl) ⟨1200635, by rfl⟩ : syracuseStep 1600847 = 2401271) B2401271
theorem B1600937 : Blo 710320 1600937 := bstep (se 2 (by rfl) ⟨600351, by rfl⟩ : syracuseStep 1600937 = 1200703) B1200703
theorem B2027065 : Blo 710320 2027065 := bstep (se 2 (by rfl) ⟨760149, by rfl⟩ : syracuseStep 2027065 = 1520299) B1520299
theorem B1601423 : Blo 710320 1601423 := bstep (se 1 (by rfl) ⟨1201067, by rfl⟩ : syracuseStep 1601423 = 2402135) B2402135
theorem B1011943 : Blo 710320 1011943 := bstep (se 1 (by rfl) ⟨758957, by rfl⟩ : syracuseStep 1011943 = 1517915) B1517915
theorem B6091037 : Blo 710320 6091037 := bstep (se 3 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 6091037 = 2284139) B2284139
theorem B6844763 : Blo 710320 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B2027987 : Blo 710320 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B1602143 : Blo 710320 1602143 := bstep (se 1 (by rfl) ⟨1201607, by rfl⟩ : syracuseStep 1602143 = 2403215) B2403215
theorem B4551389 : Blo 710320 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B1798919 : Blo 710320 1798919 := bstep (se 1 (by rfl) ⟨1349189, by rfl⟩ : syracuseStep 1798919 = 2698379) B2698379
theorem B3044425 : Blo 710320 3044425 := bstep (se 2 (by rfl) ⟨1141659, by rfl⟩ : syracuseStep 3044425 = 2283319) B2283319
theorem B1602971 : Blo 710320 1602971 := bstep (se 1 (by rfl) ⟨1202228, by rfl⟩ : syracuseStep 1602971 = 2404457) B2404457
theorem B8123975 : Blo 710320 8123975 := bstep (se 1 (by rfl) ⟨6092981, by rfl⟩ : syracuseStep 8123975 = 12185963) B12185963
theorem B10417997 : Blo 710320 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B4061123 : Blo 710320 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B1603547 : Blo 710320 1603547 := bstep (se 1 (by rfl) ⟨1202660, by rfl⟩ : syracuseStep 1603547 = 2405321) B2405321
theorem B1013743 : Blo 710320 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B2029673 : Blo 710320 2029673 := bstep (se 2 (by rfl) ⟨761127, by rfl⟩ : syracuseStep 2029673 = 1522255) B1522255
theorem B1603727 : Blo 710320 1603727 := bstep (se 1 (by rfl) ⟨1202795, by rfl⟩ : syracuseStep 1603727 = 2405591) B2405591
theorem B1603745 : Blo 710320 1603745 := bstep (se 2 (by rfl) ⟨601404, by rfl⟩ : syracuseStep 1603745 = 1202809) B1202809
theorem B14088377 : Blo 710320 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B1603817 : Blo 710320 1603817 := bstep (se 2 (by rfl) ⟨601431, by rfl⟩ : syracuseStep 1603817 = 1202863) B1202863
theorem B1014763 : Blo 710320 1014763 := bstep (se 1 (by rfl) ⟨761072, by rfl⟩ : syracuseStep 1014763 = 1522145) B1522145
theorem B3603527 : Blo 710320 3603527 := bstep (se 1 (by rfl) ⟨2702645, by rfl⟩ : syracuseStep 3603527 = 5405291) B5405291
theorem B1801399 : Blo 710320 1801399 := bstep (se 1 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 1801399 = 2702099) B2702099
theorem B13696451 : Blo 710320 13696451 := bstep (se 1 (by rfl) ⟨10272338, by rfl⟩ : syracuseStep 13696451 = 20544677) B20544677
theorem B1801703 : Blo 710320 1801703 := bstep (se 1 (by rfl) ⟨1351277, by rfl⟩ : syracuseStep 1801703 = 2702555) B2702555
theorem B1605095 : Blo 710320 1605095 := bstep (se 1 (by rfl) ⟨1203821, by rfl⟩ : syracuseStep 1605095 = 2407643) B2407643
theorem B8093357 : Blo 710320 8093357 := bstep (se 3 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 8093357 = 3035009) B3035009
theorem B4554413 : Blo 710320 4554413 := bstep (se 3 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 4554413 = 1707905) B1707905
theorem B3047159 : Blo 710320 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B4620347 : Blo 710320 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B6095033 : Blo 710320 6095033 := bstep (se 2 (by rfl) ⟨2285637, by rfl⟩ : syracuseStep 6095033 = 4571275) B4571275
theorem B4063607 : Blo 710320 4063607 := bstep (se 1 (by rfl) ⟨3047705, by rfl⟩ : syracuseStep 4063607 = 6095411) B6095411
theorem B1606175 : Blo 710320 1606175 := bstep (se 1 (by rfl) ⟨1204631, by rfl⟩ : syracuseStep 1606175 = 2409263) B2409263
theorem B1606247 : Blo 710320 1606247 := bstep (se 1 (by rfl) ⟨1204685, by rfl⟩ : syracuseStep 1606247 = 2409371) B2409371
theorem B1802857 : Blo 710320 1802857 := bstep (se 2 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 1802857 = 1352143) B1352143
theorem B11567933 : Blo 710320 11567933 := bstep (se 3 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 11567933 = 4337975) B4337975
theorem B18252701 : Blo 710320 18252701 := bstep (se 3 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 18252701 = 6844763) B6844763
theorem B1607003 : Blo 710320 1607003 := bstep (se 1 (by rfl) ⟨1205252, by rfl⟩ : syracuseStep 1607003 = 2410505) B2410505
theorem B8128349 : Blo 710320 8128349 := bstep (se 3 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 8128349 = 3048131) B3048131
theorem B2034047 : Blo 710320 2034047 := bstep (se 1 (by rfl) ⟨1525535, by rfl⟩ : syracuseStep 2034047 = 3051071) B3051071
theorem B3607091 : Blo 710320 3607091 := bstep (se 1 (by rfl) ⟨2705318, by rfl⟩ : syracuseStep 3607091 = 5410637) B5410637
theorem B3050081 : Blo 710320 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B11733913 : Blo 710320 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B2887247 : Blo 710320 2887247 := bstep (se 1 (by rfl) ⟨2165435, by rfl⟩ : syracuseStep 2887247 = 4330871) B4330871
theorem B19468127 : Blo 710320 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B3608711 : Blo 710320 3608711 := bstep (se 1 (by rfl) ⟨2706533, by rfl⟩ : syracuseStep 3608711 = 5413067) B5413067
theorem B3608873 : Blo 710320 3608873 := bstep (se 2 (by rfl) ⟨1353327, by rfl⟩ : syracuseStep 3608873 = 2706655) B2706655
theorem B27398735 : Blo 710320 27398735 := bstep (se 1 (by rfl) ⟨20549051, by rfl⟩ : syracuseStep 27398735 = 41098103) B41098103
theorem B1807343 : Blo 710320 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B758855 : Blo 710320 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B4560101 : Blo 710320 4560101 := bstep (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) B855019
theorem B14587123 : Blo 710320 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B3610331 : Blo 710320 3610331 := bstep (se 1 (by rfl) ⟨2707748, by rfl⟩ : syracuseStep 3610331 = 5415497) B5415497
theorem B1350047 : Blo 710320 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B3120079 : Blo 710320 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B20585501 : Blo 710320 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B9116873 : Blo 710320 9116873 := bstep (se 2 (by rfl) ⟨3418827, by rfl⟩ : syracuseStep 9116873 = 6837655) B6837655
theorem B1351657 : Blo 710320 1351657 := bstep (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) B1013743
theorem B2924669 : Blo 710320 2924669 := bstep (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) B1096751
theorem B1351991 : Blo 710320 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B3613247 : Blo 710320 3613247 := bstep (se 1 (by rfl) ⟨2709935, by rfl⟩ : syracuseStep 3613247 = 5419871) B5419871
theorem B3253117 : Blo 710320 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B5415983 : Blo 710320 5415983 := bstep (se 1 (by rfl) ⟨4061987, by rfl⟩ : syracuseStep 5415983 = 8123975) B8123975
theorem B1353017 : Blo 710320 1353017 := bstep (se 2 (by rfl) ⟨507381, by rfl⟩ : syracuseStep 1353017 = 1014763) B1014763
theorem B1353115 : Blo 710320 1353115 := bstep (se 1 (by rfl) ⟨1014836, by rfl⟩ : syracuseStep 1353115 = 2029673) B2029673
theorem B2401865 : Blo 710320 2401865 := bstep (se 2 (by rfl) ⟨900699, by rfl⟩ : syracuseStep 2401865 = 1801399) B1801399
theorem B2402351 : Blo 710320 2402351 := bstep (se 1 (by rfl) ⟨1801763, by rfl⟩ : syracuseStep 2402351 = 3603527) B3603527
theorem B1714259 : Blo 710320 1714259 := bstep (se 1 (by rfl) ⟨1285694, by rfl⟩ : syracuseStep 1714259 = 2571389) B2571389
theorem B2697407 : Blo 710320 2697407 := bstep (se 1 (by rfl) ⟨2023055, by rfl⟩ : syracuseStep 2697407 = 4046111) B4046111
theorem B6924745 : Blo 710320 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B3418847 : Blo 710320 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B136719197 : Blo 710320 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B2403593 : Blo 710320 2403593 := bstep (se 2 (by rfl) ⟨901347, by rfl⟩ : syracuseStep 2403593 = 1802695) B1802695
theorem B2567479 : Blo 710320 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B1355447 : Blo 710320 1355447 := bstep (se 1 (by rfl) ⟨1016585, by rfl⟩ : syracuseStep 1355447 = 2033171) B2033171
theorem B1355849 : Blo 710320 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B799483 : Blo 710320 799483 := bstep (se 1 (by rfl) ⟨599612, by rfl⟩ : syracuseStep 799483 = 1199225) B1199225
theorem B11678671 : Blo 710320 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B5846057 : Blo 710320 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B2700641 : Blo 710320 2700641 := bstep (se 2 (by rfl) ⟨1012740, by rfl⟩ : syracuseStep 2700641 = 2025481) B2025481
theorem B7714199 : Blo 710320 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B4568507 : Blo 710320 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B800239 : Blo 710320 800239 := bstep (se 1 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 800239 = 1200359) B1200359
theorem B800347 : Blo 710320 800347 := bstep (se 1 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 800347 = 1200521) B1200521
theorem B2701097 : Blo 710320 2701097 := bstep (se 2 (by rfl) ⟨1012911, by rfl⟩ : syracuseStep 2701097 = 2025823) B2025823
theorem B2406185 : Blo 710320 2406185 := bstep (se 2 (by rfl) ⟨902319, by rfl⟩ : syracuseStep 2406185 = 1804639) B1804639
theorem B800635 : Blo 710320 800635 := bstep (se 1 (by rfl) ⟨600476, by rfl⟩ : syracuseStep 800635 = 1200953) B1200953
theorem B800671 : Blo 710320 800671 := bstep (se 1 (by rfl) ⟨600503, by rfl⟩ : syracuseStep 800671 = 1201007) B1201007
theorem B3127531 : Blo 710320 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B2734535 : Blo 710320 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B899743 : Blo 710320 899743 := bstep (se 1 (by rfl) ⟨674807, by rfl⟩ : syracuseStep 899743 = 1349615) B1349615
theorem B6830891 : Blo 710320 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B801607 : Blo 710320 801607 := bstep (se 1 (by rfl) ⟨601205, by rfl⟩ : syracuseStep 801607 = 1202411) B1202411
theorem B2604257 : Blo 710320 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B2702753 : Blo 710320 2702753 := bstep (se 2 (by rfl) ⟨1013532, by rfl⟩ : syracuseStep 2702753 = 2027065) B2027065
theorem B802255 : Blo 710320 802255 := bstep (se 1 (by rfl) ⟨601691, by rfl⟩ : syracuseStep 802255 = 1203383) B1203383
theorem B1523195 : Blo 710320 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B1621615 : Blo 710320 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B802471 : Blo 710320 802471 := bstep (se 1 (by rfl) ⟨601853, by rfl⟩ : syracuseStep 802471 = 1203707) B1203707
theorem B2703071 : Blo 710320 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B4865771 : Blo 710320 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B802759 : Blo 710320 802759 := bstep (se 1 (by rfl) ⟨602069, by rfl⟩ : syracuseStep 802759 = 1204139) B1204139
theorem B1523947 : Blo 710320 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B803119 : Blo 710320 803119 := bstep (se 1 (by rfl) ⟨602339, by rfl⟩ : syracuseStep 803119 = 1204679) B1204679
theorem B37569005 : Blo 710320 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B1065503 : Blo 710320 1065503 := bstep (se 1 (by rfl) ⟨799127, by rfl⟩ : syracuseStep 1065503 = 1598255) B1598255
theorem B3851027 : Blo 710320 3851027 := bstep (se 1 (by rfl) ⟨2888270, by rfl⟩ : syracuseStep 3851027 = 5776541) B5776541
theorem B1066175 : Blo 710320 1066175 := bstep (se 1 (by rfl) ⟨799631, by rfl⟩ : syracuseStep 1066175 = 1599263) B1599263
theorem B902335 : Blo 710320 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B1066319 : Blo 710320 1066319 := bstep (se 1 (by rfl) ⟨799739, by rfl⟩ : syracuseStep 1066319 = 1599479) B1599479
theorem B2442575 : Blo 710320 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B1066409 : Blo 710320 1066409 := bstep (se 2 (by rfl) ⟨399903, by rfl⟩ : syracuseStep 1066409 = 799807) B799807
theorem B2409911 : Blo 710320 2409911 := bstep (se 1 (by rfl) ⟨1807433, by rfl⟩ : syracuseStep 2409911 = 3614867) B3614867
theorem B1066559 : Blo 710320 1066559 := bstep (se 1 (by rfl) ⟨799919, by rfl⟩ : syracuseStep 1066559 = 1599839) B1599839
theorem B2278975 : Blo 710320 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B1066601 : Blo 710320 1066601 := bstep (se 2 (by rfl) ⟨399975, by rfl⟩ : syracuseStep 1066601 = 799951) B799951
theorem B2705183 : Blo 710320 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B22235141 : Blo 710320 22235141 := bstep (se 4 (by rfl) ⟨2084544, by rfl⟩ : syracuseStep 22235141 = 4169089) B4169089
theorem B1067039 : Blo 710320 1067039 := bstep (se 1 (by rfl) ⟨800279, by rfl⟩ : syracuseStep 1067039 = 1600559) B1600559
theorem B1067231 : Blo 710320 1067231 := bstep (se 1 (by rfl) ⟨800423, by rfl⟩ : syracuseStep 1067231 = 1600847) B1600847
theorem B1067291 : Blo 710320 1067291 := bstep (se 1 (by rfl) ⟨800468, by rfl⟩ : syracuseStep 1067291 = 1600937) B1600937
theorem B1067615 : Blo 710320 1067615 := bstep (se 1 (by rfl) ⟨800711, by rfl⟩ : syracuseStep 1067615 = 1601423) B1601423
theorem B6081227 : Blo 710320 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B1624873 : Blo 710320 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B1067897 : Blo 710320 1067897 := bstep (se 2 (by rfl) ⟨400461, by rfl⟩ : syracuseStep 1067897 = 800923) B800923
theorem B1067945 : Blo 710320 1067945 := bstep (se 2 (by rfl) ⟨400479, by rfl⟩ : syracuseStep 1067945 = 800959) B800959
theorem B1068095 : Blo 710320 1068095 := bstep (se 1 (by rfl) ⟨801071, by rfl⟩ : syracuseStep 1068095 = 1602143) B1602143
theorem B3034259 : Blo 710320 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B1199279 : Blo 710320 1199279 := bstep (se 1 (by rfl) ⟨899459, by rfl⟩ : syracuseStep 1199279 = 1798919) B1798919
theorem B10276145 : Blo 710320 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B1068647 : Blo 710320 1068647 := bstep (se 1 (by rfl) ⟨801485, by rfl⟩ : syracuseStep 1068647 = 1602971) B1602971
theorem B2707415 : Blo 710320 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B4050917 : Blo 710320 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B1069031 : Blo 710320 1069031 := bstep (se 1 (by rfl) ⟨801773, by rfl⟩ : syracuseStep 1069031 = 1603547) B1603547
theorem B1069151 : Blo 710320 1069151 := bstep (se 1 (by rfl) ⟨801863, by rfl⟩ : syracuseStep 1069151 = 1603727) B1603727
theorem B1069163 : Blo 710320 1069163 := bstep (se 1 (by rfl) ⟨801872, by rfl⟩ : syracuseStep 1069163 = 1603745) B1603745
theorem B1069211 : Blo 710320 1069211 := bstep (se 1 (by rfl) ⟨801908, by rfl⟩ : syracuseStep 1069211 = 1603817) B1603817
theorem B2281691 : Blo 710320 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B2740751 : Blo 710320 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B9130967 : Blo 710320 9130967 := bstep (se 1 (by rfl) ⟨6848225, by rfl⟩ : syracuseStep 9130967 = 13696451) B13696451
theorem B1201135 : Blo 710320 1201135 := bstep (se 1 (by rfl) ⟨900851, by rfl⟩ : syracuseStep 1201135 = 1801703) B1801703
theorem B1070063 : Blo 710320 1070063 := bstep (se 1 (by rfl) ⟨802547, by rfl⟩ : syracuseStep 1070063 = 1605095) B1605095
theorem B43897859 : Blo 710320 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B11523167 : Blo 710320 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B5395571 : Blo 710320 5395571 := bstep (se 1 (by rfl) ⟨4046678, by rfl⟩ : syracuseStep 5395571 = 8093357) B8093357
theorem B3036275 : Blo 710320 3036275 := bstep (se 1 (by rfl) ⟨2277206, by rfl⟩ : syracuseStep 3036275 = 4554413) B4554413
theorem B1070447 : Blo 710320 1070447 := bstep (se 1 (by rfl) ⟨802835, by rfl⟩ : syracuseStep 1070447 = 1605671) B1605671
theorem B2708873 : Blo 710320 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B1070567 : Blo 710320 1070567 := bstep (se 1 (by rfl) ⟨802925, by rfl⟩ : syracuseStep 1070567 = 1605851) B1605851
theorem B2283023 : Blo 710320 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B1070729 : Blo 710320 1070729 := bstep (se 2 (by rfl) ⟨401523, by rfl⟩ : syracuseStep 1070729 = 803047) B803047
theorem B1070747 : Blo 710320 1070747 := bstep (se 1 (by rfl) ⟨803060, by rfl⟩ : syracuseStep 1070747 = 1606121) B1606121
theorem B710383 : Blo 710320 710383 := bstep (se 1 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 710383 = 1065575) B1065575
theorem B3036923 : Blo 710320 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B3036959 : Blo 710320 3036959 := bstep (se 1 (by rfl) ⟨2277719, by rfl⟩ : syracuseStep 3036959 = 4555439) B4555439
theorem B710471 : Blo 710320 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B710491 : Blo 710320 710491 := bstep (se 1 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 710491 = 1065737) B1065737
theorem B1070939 : Blo 710320 1070939 := bstep (se 1 (by rfl) ⟨803204, by rfl⟩ : syracuseStep 1070939 = 1606409) B1606409
theorem B710559 : Blo 710320 710559 := bstep (se 1 (by rfl) ⟨532919, by rfl⟩ : syracuseStep 710559 = 1065839) B1065839
theorem B710727 : Blo 710320 710727 := bstep (se 1 (by rfl) ⟨533045, by rfl⟩ : syracuseStep 710727 = 1066091) B1066091
theorem B6936673 : Blo 710320 6936673 := bstep (se 2 (by rfl) ⟨2601252, by rfl⟩ : syracuseStep 6936673 = 5202505) B5202505
theorem B1071323 : Blo 710320 1071323 := bstep (se 1 (by rfl) ⟨803492, by rfl⟩ : syracuseStep 1071323 = 1606985) B1606985
theorem B710887 : Blo 710320 710887 := bstep (se 1 (by rfl) ⟨533165, by rfl⟩ : syracuseStep 710887 = 1066331) B1066331
theorem B6510905 : Blo 710320 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B711071 : Blo 710320 711071 := bstep (se 1 (by rfl) ⟨533303, by rfl⟩ : syracuseStep 711071 = 1066607) B1066607
theorem B711119 : Blo 710320 711119 := bstep (se 1 (by rfl) ⟨533339, by rfl⟩ : syracuseStep 711119 = 1066679) B1066679
theorem B711143 : Blo 710320 711143 := bstep (se 1 (by rfl) ⟨533357, by rfl⟩ : syracuseStep 711143 = 1066715) B1066715
theorem B2710043 : Blo 710320 2710043 := bstep (se 1 (by rfl) ⟨2032532, by rfl⟩ : syracuseStep 2710043 = 4065065) B4065065
theorem B5397029 : Blo 710320 5397029 := bstep (se 4 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 5397029 = 1011943) B1011943
theorem B711259 : Blo 710320 711259 := bstep (se 1 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 711259 = 1066889) B1066889
theorem B711327 : Blo 710320 711327 := bstep (se 1 (by rfl) ⟨533495, by rfl⟩ : syracuseStep 711327 = 1066991) B1066991
theorem B711495 : Blo 710320 711495 := bstep (se 1 (by rfl) ⟨533621, by rfl⟩ : syracuseStep 711495 = 1067243) B1067243
theorem B711535 : Blo 710320 711535 := bstep (se 1 (by rfl) ⟨533651, by rfl⟩ : syracuseStep 711535 = 1067303) B1067303
theorem B711591 : Blo 710320 711591 := bstep (se 1 (by rfl) ⟨533693, by rfl⟩ : syracuseStep 711591 = 1067387) B1067387
theorem B299850821 : Blo 710320 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B711771 : Blo 710320 711771 := bstep (se 1 (by rfl) ⟨533828, by rfl⟩ : syracuseStep 711771 = 1067657) B1067657
theorem B711887 : Blo 710320 711887 := bstep (se 1 (by rfl) ⟨533915, by rfl⟩ : syracuseStep 711887 = 1067831) B1067831
theorem B711911 : Blo 710320 711911 := bstep (se 1 (by rfl) ⟨533933, by rfl⟩ : syracuseStep 711911 = 1067867) B1067867
theorem B712007 : Blo 710320 712007 := bstep (se 1 (by rfl) ⟨534005, by rfl⟩ : syracuseStep 712007 = 1068011) B1068011
theorem B712143 : Blo 710320 712143 := bstep (se 1 (by rfl) ⟨534107, by rfl⟩ : syracuseStep 712143 = 1068215) B1068215
theorem B712303 : Blo 710320 712303 := bstep (se 1 (by rfl) ⟨534227, by rfl⟩ : syracuseStep 712303 = 1068455) B1068455
theorem B712359 : Blo 710320 712359 := bstep (se 1 (by rfl) ⟨534269, by rfl⟩ : syracuseStep 712359 = 1068539) B1068539
theorem B712423 : Blo 710320 712423 := bstep (se 1 (by rfl) ⟨534317, by rfl⟩ : syracuseStep 712423 = 1068635) B1068635
theorem B712479 : Blo 710320 712479 := bstep (se 1 (by rfl) ⟨534359, by rfl⟩ : syracuseStep 712479 = 1068719) B1068719
theorem B3432223 : Blo 710320 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B100228913 : Blo 710320 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B712559 : Blo 710320 712559 := bstep (se 1 (by rfl) ⟨534419, by rfl⟩ : syracuseStep 712559 = 1068839) B1068839
theorem B5791621 : Blo 710320 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B712615 : Blo 710320 712615 := bstep (se 1 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 712615 = 1068923) B1068923
theorem B712895 : Blo 710320 712895 := bstep (se 1 (by rfl) ⟨534671, by rfl⟩ : syracuseStep 712895 = 1069343) B1069343
theorem B6348995 : Blo 710320 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B712911 : Blo 710320 712911 := bstep (se 1 (by rfl) ⟨534683, by rfl⟩ : syracuseStep 712911 = 1069367) B1069367
theorem B712959 : Blo 710320 712959 := bstep (se 1 (by rfl) ⟨534719, by rfl⟩ : syracuseStep 712959 = 1069439) B1069439
theorem B713007 : Blo 710320 713007 := bstep (se 1 (by rfl) ⟨534755, by rfl⟩ : syracuseStep 713007 = 1069511) B1069511
theorem B1204537 : Blo 710320 1204537 := bstep (se 2 (by rfl) ⟨451701, by rfl⟩ : syracuseStep 1204537 = 903403) B903403
theorem B2023841 : Blo 710320 2023841 := bstep (se 2 (by rfl) ⟨758940, by rfl⟩ : syracuseStep 2023841 = 1517881) B1517881
theorem B713243 : Blo 710320 713243 := bstep (se 1 (by rfl) ⟨534932, by rfl⟩ : syracuseStep 713243 = 1069865) B1069865
theorem B713247 : Blo 710320 713247 := bstep (se 1 (by rfl) ⟨534935, by rfl⟩ : syracuseStep 713247 = 1069871) B1069871
theorem B713327 : Blo 710320 713327 := bstep (se 1 (by rfl) ⟨534995, by rfl⟩ : syracuseStep 713327 = 1069991) B1069991
theorem B713383 : Blo 710320 713383 := bstep (se 1 (by rfl) ⟨535037, by rfl⟩ : syracuseStep 713383 = 1070075) B1070075
theorem B713423 : Blo 710320 713423 := bstep (se 1 (by rfl) ⟨535067, by rfl⟩ : syracuseStep 713423 = 1070135) B1070135
theorem B713503 : Blo 710320 713503 := bstep (se 1 (by rfl) ⟨535127, by rfl⟩ : syracuseStep 713503 = 1070255) B1070255
theorem B1205023 : Blo 710320 1205023 := bstep (se 1 (by rfl) ⟨903767, by rfl⟩ : syracuseStep 1205023 = 1807535) B1807535
theorem B713775 : Blo 710320 713775 := bstep (se 1 (by rfl) ⟨535331, by rfl⟩ : syracuseStep 713775 = 1070663) B1070663
theorem B713839 : Blo 710320 713839 := bstep (se 1 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 713839 = 1070759) B1070759
theorem B713895 : Blo 710320 713895 := bstep (se 1 (by rfl) ⟨535421, by rfl⟩ : syracuseStep 713895 = 1070843) B1070843
theorem B713919 : Blo 710320 713919 := bstep (se 1 (by rfl) ⟨535439, by rfl⟩ : syracuseStep 713919 = 1070879) B1070879
theorem B713951 : Blo 710320 713951 := bstep (se 1 (by rfl) ⟨535463, by rfl⟩ : syracuseStep 713951 = 1070927) B1070927
theorem B714031 : Blo 710320 714031 := bstep (se 1 (by rfl) ⟨535523, by rfl⟩ : syracuseStep 714031 = 1071047) B1071047
theorem B1598777 : Blo 710320 1598777 := bstep (se 2 (by rfl) ⟨599541, by rfl⟩ : syracuseStep 1598777 = 1199083) B1199083
theorem B714267 : Blo 710320 714267 := bstep (se 1 (by rfl) ⟨535700, by rfl⟩ : syracuseStep 714267 = 1071401) B1071401
theorem B714271 : Blo 710320 714271 := bstep (se 1 (by rfl) ⟨535703, by rfl⟩ : syracuseStep 714271 = 1071407) B1071407
theorem B1730119 : Blo 710320 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B1599047 : Blo 710320 1599047 := bstep (se 1 (by rfl) ⟨1199285, by rfl⟩ : syracuseStep 1599047 = 2398571) B2398571
theorem B1599227 : Blo 710320 1599227 := bstep (se 1 (by rfl) ⟨1199420, by rfl⟩ : syracuseStep 1599227 = 2398841) B2398841
theorem B1140635 : Blo 710320 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B6842303 : Blo 710320 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B4057067 : Blo 710320 4057067 := bstep (se 1 (by rfl) ⟨3042800, by rfl⟩ : syracuseStep 4057067 = 6085601) B6085601
theorem B1599515 : Blo 710320 1599515 := bstep (se 1 (by rfl) ⟨1199636, by rfl⟩ : syracuseStep 1599515 = 2399273) B2399273
theorem B2287739 : Blo 710320 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B27781325 : Blo 710320 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B6514991 : Blo 710320 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B5401403 : Blo 710320 5401403 := bstep (se 1 (by rfl) ⟨4051052, by rfl⟩ : syracuseStep 5401403 = 8102105) B8102105
theorem B1600991 : Blo 710320 1600991 := bstep (se 1 (by rfl) ⟨1200743, by rfl⟩ : syracuseStep 1600991 = 2401487) B2401487
theorem B3599963 : Blo 710320 3599963 := bstep (se 1 (by rfl) ⟨2699972, by rfl⟩ : syracuseStep 3599963 = 5399945) B5399945
theorem B2027099 : Blo 710320 2027099 := bstep (se 1 (by rfl) ⟨1520324, by rfl⟩ : syracuseStep 2027099 = 3040649) B3040649
theorem B1601207 : Blo 710320 1601207 := bstep (se 1 (by rfl) ⟨1200905, by rfl⟩ : syracuseStep 1601207 = 2401811) B2401811
theorem B5402375 : Blo 710320 5402375 := bstep (se 1 (by rfl) ⟨4051781, by rfl⟩ : syracuseStep 5402375 = 8103563) B8103563
theorem B4059233 : Blo 710320 4059233 := bstep (se 2 (by rfl) ⟨1522212, by rfl⟩ : syracuseStep 4059233 = 3044425) B3044425
theorem B6484121 : Blo 710320 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B1601999 : Blo 710320 1601999 := bstep (se 1 (by rfl) ⟨1201499, by rfl⟩ : syracuseStep 1601999 = 2402999) B2402999
theorem B46330865 : Blo 710320 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B1602665 : Blo 710320 1602665 := bstep (se 2 (by rfl) ⟨600999, by rfl⟩ : syracuseStep 1602665 = 1201999) B1201999
theorem B3044699 : Blo 710320 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B4060691 : Blo 710320 4060691 := bstep (se 1 (by rfl) ⟨3045518, by rfl⟩ : syracuseStep 4060691 = 6091037) B6091037
theorem B1603295 : Blo 710320 1603295 := bstep (se 1 (by rfl) ⟨1202471, by rfl⟩ : syracuseStep 1603295 = 2404943) B2404943
theorem B1603655 : Blo 710320 1603655 := bstep (se 1 (by rfl) ⟨1202741, by rfl⟩ : syracuseStep 1603655 = 2405483) B2405483
theorem B6846767 : Blo 710320 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B4618783 : Blo 710320 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B3242537 : Blo 710320 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B1604321 : Blo 710320 1604321 := bstep (se 2 (by rfl) ⟨601620, by rfl⟩ : syracuseStep 1604321 = 1203241) B1203241
theorem B1604519 : Blo 710320 1604519 := bstep (se 1 (by rfl) ⟨1203389, by rfl⟩ : syracuseStep 1604519 = 2406779) B2406779
theorem B5405777 : Blo 710320 5405777 := bstep (se 2 (by rfl) ⟨2027166, by rfl⟩ : syracuseStep 5405777 = 4054333) B4054333
theorem B1604699 : Blo 710320 1604699 := bstep (se 1 (by rfl) ⟨1203524, by rfl⟩ : syracuseStep 1604699 = 2407049) B2407049
theorem B19758275 : Blo 710320 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B100040147 : Blo 710320 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B1801723 : Blo 710320 1801723 := bstep (se 1 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 1801723 = 2702585) B2702585
theorem B2031439 : Blo 710320 2031439 := bstep (se 1 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 2031439 = 3047159) B3047159
theorem B1605455 : Blo 710320 1605455 := bstep (se 1 (by rfl) ⟨1204091, by rfl⟩ : syracuseStep 1605455 = 2408183) B2408183
theorem B3047311 : Blo 710320 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B3080231 : Blo 710320 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B4063355 : Blo 710320 4063355 := bstep (se 1 (by rfl) ⟨3047516, by rfl⟩ : syracuseStep 4063355 = 6095033) B6095033
theorem B2031929 : Blo 710320 2031929 := bstep (se 2 (by rfl) ⟨761973, by rfl⟩ : syracuseStep 2031929 = 1523947) B1523947
theorem B1606049 : Blo 710320 1606049 := bstep (se 2 (by rfl) ⟨602268, by rfl⟩ : syracuseStep 1606049 = 1204537) B1204537
theorem B3605309 : Blo 710320 3605309 := bstep (se 3 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 3605309 = 1351991) B1351991
theorem B1606607 : Blo 710320 1606607 := bstep (se 1 (by rfl) ⟨1204955, by rfl⟩ : syracuseStep 1606607 = 2409911) B2409911
theorem B1606697 : Blo 710320 1606697 := bstep (se 2 (by rfl) ⟨602511, by rfl⟩ : syracuseStep 1606697 = 1205023) B1205023
theorem B1803455 : Blo 710320 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B2033387 : Blo 710320 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B1804153 : Blo 710320 1804153 := bstep (se 2 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 1804153 = 1353115) B1353115
theorem B6850763 : Blo 710320 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B12978751 : Blo 710320 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B1804943 : Blo 710320 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B29265239 : Blo 710320 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B1805915 : Blo 710320 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B2166497 : Blo 710320 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1806695 : Blo 710320 1806695 := bstep (se 1 (by rfl) ⟨1355021, by rfl⟩ : syracuseStep 1806695 = 2710043) B2710043
theorem B66819275 : Blo 710320 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B4232663 : Blo 710320 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B29234677 : Blo 710320 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B1349227 : Blo 710320 1349227 := bstep (se 1 (by rfl) ⟨1011920, by rfl⟩ : syracuseStep 1349227 = 2023841) B2023841
theorem B3610655 : Blo 710320 3610655 := bstep (se 1 (by rfl) ⟨2707991, by rfl⟩ : syracuseStep 3610655 = 5415983) B5415983
theorem B760423 : Blo 710320 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B15571561 : Blo 710320 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B4561535 : Blo 710320 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B18520883 : Blo 710320 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B2399975 : Blo 710320 2399975 := bstep (se 1 (by rfl) ⟨1799981, by rfl⟩ : syracuseStep 2399975 = 3599963) B3599963
theorem B1351399 : Blo 710320 1351399 := bstep (se 1 (by rfl) ⟨1013549, by rfl⟩ : syracuseStep 1351399 = 2027099) B2027099
theorem B9248897 : Blo 710320 9248897 := bstep (se 2 (by rfl) ⟨3468336, by rfl⟩ : syracuseStep 9248897 = 6936673) B6936673
theorem B4170041 : Blo 710320 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B4564511 : Blo 710320 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B2402297 : Blo 710320 2402297 := bstep (se 2 (by rfl) ⟨900861, by rfl⟩ : syracuseStep 2402297 = 1801723) B1801723
theorem B66693431 : Blo 710320 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B25046003 : Blo 710320 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B2567351 : Blo 710320 2567351 := bstep (se 1 (by rfl) ⟨1925513, by rfl⟩ : syracuseStep 2567351 = 3851027) B3851027
theorem B7711955 : Blo 710320 7711955 := bstep (se 1 (by rfl) ⟨5783966, by rfl⟩ : syracuseStep 7711955 = 11567933) B11567933
theorem B12168467 : Blo 710320 12168467 := bstep (se 1 (by rfl) ⟨9126350, by rfl⟩ : syracuseStep 12168467 = 18252701) B18252701
theorem B2403809 : Blo 710320 2403809 := bstep (se 2 (by rfl) ⟨901428, by rfl⟩ : syracuseStep 2403809 = 1802857) B1802857
theorem B4337489 : Blo 710320 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B5418899 : Blo 710320 5418899 := bstep (se 1 (by rfl) ⟨4064174, by rfl⟩ : syracuseStep 5418899 = 8128349) B8128349
theorem B14823427 : Blo 710320 14823427 := bstep (se 1 (by rfl) ⟨11117570, by rfl⟩ : syracuseStep 14823427 = 22235141) B22235141
theorem B1356031 : Blo 710320 1356031 := bstep (se 1 (by rfl) ⟨1017023, by rfl⟩ : syracuseStep 1356031 = 2034047) B2034047
theorem B2404727 : Blo 710320 2404727 := bstep (se 1 (by rfl) ⟨1803545, by rfl⟩ : syracuseStep 2404727 = 3607091) B3607091
theorem B2306825 : Blo 710320 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B799519 : Blo 710320 799519 := bstep (se 1 (by rfl) ⟨599639, by rfl⟩ : syracuseStep 799519 = 1199279) B1199279
theorem B2700611 : Blo 710320 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B2405807 : Blo 710320 2405807 := bstep (se 1 (by rfl) ⟨1804355, by rfl⟩ : syracuseStep 2405807 = 3608711) B3608711
theorem B1521127 : Blo 710320 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B2405915 : Blo 710320 2405915 := bstep (se 1 (by rfl) ⟨1804436, by rfl⟩ : syracuseStep 2405915 = 3608873) B3608873
theorem B18265823 : Blo 710320 18265823 := bstep (se 1 (by rfl) ⟨13699367, by rfl⟩ : syracuseStep 18265823 = 27398735) B27398735
theorem B7682111 : Blo 710320 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B2406887 : Blo 710320 2406887 := bstep (se 1 (by rfl) ⟨1805165, by rfl⟩ : syracuseStep 2406887 = 3610331) B3610331
theorem B4340603 : Blo 710320 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B3423305 : Blo 710320 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B199900547 : Blo 710320 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B6077915 : Blo 710320 6077915 := bstep (se 1 (by rfl) ⟨4558436, by rfl⟩ : syracuseStep 6077915 = 9116873) B9116873
theorem B1949779 : Blo 710320 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B2408831 : Blo 710320 2408831 := bstep (se 1 (by rfl) ⟨1806623, by rfl⟩ : syracuseStep 2408831 = 3613247) B3613247
theorem B1065851 : Blo 710320 1065851 := bstep (se 1 (by rfl) ⟨799388, by rfl⟩ : syracuseStep 1065851 = 1598777) B1598777
theorem B902011 : Blo 710320 902011 := bstep (se 1 (by rfl) ⟨676508, by rfl⟩ : syracuseStep 902011 = 1353017) B1353017
theorem B1065977 : Blo 710320 1065977 := bstep (se 2 (by rfl) ⟨399741, by rfl⟩ : syracuseStep 1065977 = 799483) B799483
theorem B1066031 : Blo 710320 1066031 := bstep (se 1 (by rfl) ⟨799523, by rfl⟩ : syracuseStep 1066031 = 1599047) B1599047
theorem B1066151 : Blo 710320 1066151 := bstep (se 1 (by rfl) ⟨799613, by rfl⟩ : syracuseStep 1066151 = 1599227) B1599227
theorem B2704711 : Blo 710320 2704711 := bstep (se 1 (by rfl) ⟨2028533, by rfl⟩ : syracuseStep 2704711 = 4057067) B4057067
theorem B1066343 : Blo 710320 1066343 := bstep (se 1 (by rfl) ⟨799757, by rfl⟩ : syracuseStep 1066343 = 1599515) B1599515
theorem B1525159 : Blo 710320 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B4343327 : Blo 710320 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B19449497 : Blo 710320 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B2279231 : Blo 710320 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B91146131 : Blo 710320 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B1066985 : Blo 710320 1066985 := bstep (se 2 (by rfl) ⟨400119, by rfl⟩ : syracuseStep 1066985 = 800239) B800239
theorem B1067129 : Blo 710320 1067129 := bstep (se 2 (by rfl) ⟨400173, by rfl⟩ : syracuseStep 1067129 = 800347) B800347
theorem B1067327 : Blo 710320 1067327 := bstep (se 1 (by rfl) ⟨800495, by rfl⟩ : syracuseStep 1067327 = 1600991) B1600991
theorem B1067471 : Blo 710320 1067471 := bstep (se 1 (by rfl) ⟨800603, by rfl⟩ : syracuseStep 1067471 = 1601207) B1601207
theorem B903631 : Blo 710320 903631 := bstep (se 1 (by rfl) ⟨677723, by rfl⟩ : syracuseStep 903631 = 1355447) B1355447
theorem B1067513 : Blo 710320 1067513 := bstep (se 2 (by rfl) ⟨400317, by rfl⟩ : syracuseStep 1067513 = 800635) B800635
theorem B1067561 : Blo 710320 1067561 := bstep (se 2 (by rfl) ⟨400335, by rfl⟩ : syracuseStep 1067561 = 800671) B800671
theorem B903899 : Blo 710320 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B2706155 : Blo 710320 2706155 := bstep (se 1 (by rfl) ⟨2029616, by rfl⟩ : syracuseStep 2706155 = 4059233) B4059233
theorem B1067999 : Blo 710320 1067999 := bstep (se 1 (by rfl) ⟨800999, by rfl⟩ : syracuseStep 1067999 = 1601999) B1601999
theorem B30887243 : Blo 710320 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B1068443 : Blo 710320 1068443 := bstep (se 1 (by rfl) ⟨801332, by rfl⟩ : syracuseStep 1068443 = 1602665) B1602665
theorem B1199657 : Blo 710320 1199657 := bstep (se 2 (by rfl) ⟨449871, by rfl⟩ : syracuseStep 1199657 = 899743) B899743
theorem B2707127 : Blo 710320 2707127 := bstep (se 1 (by rfl) ⟨2030345, by rfl⟩ : syracuseStep 2707127 = 4060691) B4060691
theorem B1068809 : Blo 710320 1068809 := bstep (se 2 (by rfl) ⟨400803, by rfl⟩ : syracuseStep 1068809 = 801607) B801607
theorem B1068863 : Blo 710320 1068863 := bstep (se 1 (by rfl) ⟨801647, by rfl⟩ : syracuseStep 1068863 = 1603295) B1603295
theorem B1069103 : Blo 710320 1069103 := bstep (se 1 (by rfl) ⟨801827, by rfl⟩ : syracuseStep 1069103 = 1603655) B1603655
theorem B18305189 : Blo 710320 18305189 := bstep (se 4 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 18305189 = 3432223) B3432223
theorem B1823023 : Blo 710320 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B1069547 : Blo 710320 1069547 := bstep (se 1 (by rfl) ⟨802160, by rfl⟩ : syracuseStep 1069547 = 1604321) B1604321
theorem B1069673 : Blo 710320 1069673 := bstep (se 2 (by rfl) ⟨401127, by rfl⟩ : syracuseStep 1069673 = 802255) B802255
theorem B1069679 : Blo 710320 1069679 := bstep (se 1 (by rfl) ⟨802259, by rfl⟩ : syracuseStep 1069679 = 1604519) B1604519
theorem B1069799 : Blo 710320 1069799 := bstep (se 1 (by rfl) ⟨802349, by rfl⟩ : syracuseStep 1069799 = 1604699) B1604699
theorem B1069961 : Blo 710320 1069961 := bstep (se 2 (by rfl) ⟨401235, by rfl⟩ : syracuseStep 1069961 = 802471) B802471
theorem B2708585 : Blo 710320 2708585 := bstep (se 2 (by rfl) ⟨1015719, by rfl⟩ : syracuseStep 2708585 = 2031439) B2031439
theorem B7722161 : Blo 710320 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B1070303 : Blo 710320 1070303 := bstep (se 1 (by rfl) ⟨802727, by rfl⟩ : syracuseStep 1070303 = 1605455) B1605455
theorem B1070345 : Blo 710320 1070345 := bstep (se 2 (by rfl) ⟨401379, by rfl⟩ : syracuseStep 1070345 = 802759) B802759
theorem B2709071 : Blo 710320 2709071 := bstep (se 1 (by rfl) ⟨2031803, by rfl⟩ : syracuseStep 2709071 = 4063607) B4063607
theorem B710335 : Blo 710320 710335 := bstep (se 1 (by rfl) ⟨532751, by rfl⟩ : syracuseStep 710335 = 1065503) B1065503
theorem B1070783 : Blo 710320 1070783 := bstep (se 1 (by rfl) ⟨803087, by rfl⟩ : syracuseStep 1070783 = 1606175) B1606175
theorem B1070825 : Blo 710320 1070825 := bstep (se 2 (by rfl) ⟨401559, by rfl⟩ : syracuseStep 1070825 = 803119) B803119
theorem B1070831 : Blo 710320 1070831 := bstep (se 1 (by rfl) ⟨803123, by rfl⟩ : syracuseStep 1070831 = 1606247) B1606247
theorem B710783 : Blo 710320 710783 := bstep (se 1 (by rfl) ⟨533087, by rfl⟩ : syracuseStep 710783 = 1066175) B1066175
theorem B710879 : Blo 710320 710879 := bstep (se 1 (by rfl) ⟨533159, by rfl⟩ : syracuseStep 710879 = 1066319) B1066319
theorem B1628383 : Blo 710320 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B1071335 : Blo 710320 1071335 := bstep (se 1 (by rfl) ⟨803501, by rfl⟩ : syracuseStep 1071335 = 1607003) B1607003
theorem B710939 : Blo 710320 710939 := bstep (se 1 (by rfl) ⟨533204, by rfl⟩ : syracuseStep 710939 = 1066409) B1066409
theorem B711039 : Blo 710320 711039 := bstep (se 1 (by rfl) ⟨533279, by rfl⟩ : syracuseStep 711039 = 1066559) B1066559
theorem B711067 : Blo 710320 711067 := bstep (se 1 (by rfl) ⟨533300, by rfl⟩ : syracuseStep 711067 = 1066601) B1066601
theorem B711359 : Blo 710320 711359 := bstep (se 1 (by rfl) ⟨533519, by rfl⟩ : syracuseStep 711359 = 1067039) B1067039
theorem B711487 : Blo 710320 711487 := bstep (se 1 (by rfl) ⟨533615, by rfl⟩ : syracuseStep 711487 = 1067231) B1067231
theorem B711527 : Blo 710320 711527 := bstep (se 1 (by rfl) ⟨533645, by rfl⟩ : syracuseStep 711527 = 1067291) B1067291
theorem B1203113 : Blo 710320 1203113 := bstep (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) B902335
theorem B711743 : Blo 710320 711743 := bstep (se 1 (by rfl) ⟨533807, by rfl⟩ : syracuseStep 711743 = 1067615) B1067615
theorem B4054151 : Blo 710320 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B711931 : Blo 710320 711931 := bstep (se 1 (by rfl) ⟨533948, by rfl⟩ : syracuseStep 711931 = 1067897) B1067897
theorem B711963 : Blo 710320 711963 := bstep (se 1 (by rfl) ⟨533972, by rfl⟩ : syracuseStep 711963 = 1067945) B1067945
theorem B712063 : Blo 710320 712063 := bstep (se 1 (by rfl) ⟨534047, by rfl⟩ : syracuseStep 712063 = 1068095) B1068095
theorem B3038633 : Blo 710320 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B2022839 : Blo 710320 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B1924831 : Blo 710320 1924831 := bstep (se 1 (by rfl) ⟨1443623, by rfl⟩ : syracuseStep 1924831 = 2887247) B2887247
theorem B712431 : Blo 710320 712431 := bstep (se 1 (by rfl) ⟨534323, by rfl⟩ : syracuseStep 712431 = 1068647) B1068647
theorem B712687 : Blo 710320 712687 := bstep (se 1 (by rfl) ⟨534515, by rfl⟩ : syracuseStep 712687 = 1069031) B1069031
theorem B712767 : Blo 710320 712767 := bstep (se 1 (by rfl) ⟨534575, by rfl⟩ : syracuseStep 712767 = 1069151) B1069151
theorem B712775 : Blo 710320 712775 := bstep (se 1 (by rfl) ⟨534581, by rfl⟩ : syracuseStep 712775 = 1069163) B1069163
theorem B712807 : Blo 710320 712807 := bstep (se 1 (by rfl) ⟨534605, by rfl⟩ : syracuseStep 712807 = 1069211) B1069211
theorem B2023613 : Blo 710320 2023613 := bstep (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) B758855
theorem B9232993 : Blo 710320 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B6087311 : Blo 710320 6087311 := bstep (se 1 (by rfl) ⟨4565483, by rfl⟩ : syracuseStep 6087311 = 9130967) B9130967
theorem B713375 : Blo 710320 713375 := bstep (se 1 (by rfl) ⟨535031, by rfl⟩ : syracuseStep 713375 = 1070063) B1070063
theorem B1204895 : Blo 710320 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B3597047 : Blo 710320 3597047 := bstep (se 1 (by rfl) ⟨2697785, by rfl⟩ : syracuseStep 3597047 = 5395571) B5395571
theorem B2024183 : Blo 710320 2024183 := bstep (se 1 (by rfl) ⟨1518137, by rfl⟩ : syracuseStep 2024183 = 3036275) B3036275
theorem B3040067 : Blo 710320 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B713631 : Blo 710320 713631 := bstep (se 1 (by rfl) ⟨535223, by rfl⟩ : syracuseStep 713631 = 1070447) B1070447
theorem B713711 : Blo 710320 713711 := bstep (se 1 (by rfl) ⟨535283, by rfl⟩ : syracuseStep 713711 = 1070567) B1070567
theorem B713819 : Blo 710320 713819 := bstep (se 1 (by rfl) ⟨535364, by rfl⟩ : syracuseStep 713819 = 1070729) B1070729
theorem B713831 : Blo 710320 713831 := bstep (se 1 (by rfl) ⟨535373, by rfl⟩ : syracuseStep 713831 = 1070747) B1070747
theorem B2024615 : Blo 710320 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B2024639 : Blo 710320 2024639 := bstep (se 1 (by rfl) ⟨1518479, by rfl⟩ : syracuseStep 2024639 = 3036959) B3036959
theorem B713959 : Blo 710320 713959 := bstep (se 1 (by rfl) ⟨535469, by rfl⟩ : syracuseStep 713959 = 1070939) B1070939
theorem B6088061 : Blo 710320 6088061 := bstep (se 3 (by rfl) ⟨1141511, by rfl⟩ : syracuseStep 6088061 = 2283023) B2283023
theorem B714215 : Blo 710320 714215 := bstep (se 1 (by rfl) ⟨535661, by rfl⟩ : syracuseStep 714215 = 1071323) B1071323
theorem B3598019 : Blo 710320 3598019 := bstep (se 1 (by rfl) ⟨2698514, by rfl⟩ : syracuseStep 3598019 = 5397029) B5397029
theorem B13723667 : Blo 710320 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B62580869 : Blo 710320 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B1601243 : Blo 710320 1601243 := bstep (se 1 (by rfl) ⟨1200932, by rfl⟩ : syracuseStep 1601243 = 2401865) B2401865
theorem B3600125 : Blo 710320 3600125 := bstep (se 3 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 3600125 = 1350047) B1350047
theorem B1601513 : Blo 710320 1601513 := bstep (se 2 (by rfl) ⟨600567, by rfl⟩ : syracuseStep 1601513 = 1201135) B1201135
theorem B1601567 : Blo 710320 1601567 := bstep (se 1 (by rfl) ⟨1201175, by rfl⟩ : syracuseStep 1601567 = 2402351) B2402351
theorem B1142839 : Blo 710320 1142839 := bstep (se 1 (by rfl) ⟨857129, by rfl⟩ : syracuseStep 1142839 = 1714259) B1714259
theorem B1798271 : Blo 710320 1798271 := bstep (se 1 (by rfl) ⟨1348703, by rfl⟩ : syracuseStep 1798271 = 2697407) B2697407
theorem B3600935 : Blo 710320 3600935 := bstep (se 1 (by rfl) ⟨2700701, by rfl⟩ : syracuseStep 3600935 = 5401403) B5401403
theorem B1602395 : Blo 710320 1602395 := bstep (se 1 (by rfl) ⟨1201796, by rfl⟩ : syracuseStep 1602395 = 2403593) B2403593
theorem B3601583 : Blo 710320 3601583 := bstep (se 1 (by rfl) ⟨2701187, by rfl⟩ : syracuseStep 3601583 = 5402375) B5402375
theorem B4322747 : Blo 710320 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B3897371 : Blo 710320 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B6158377 : Blo 710320 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B2029799 : Blo 710320 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B1800427 : Blo 710320 1800427 := bstep (se 1 (by rfl) ⟨1350320, by rfl⟩ : syracuseStep 1800427 = 2700641) B2700641
theorem B5142799 : Blo 710320 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B3045671 : Blo 710320 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B1800731 : Blo 710320 1800731 := bstep (se 1 (by rfl) ⟨1350548, by rfl⟩ : syracuseStep 1800731 = 2701097) B2701097
theorem B1604123 : Blo 710320 1604123 := bstep (se 1 (by rfl) ⟨1203092, by rfl⟩ : syracuseStep 1604123 = 2406185) B2406185
theorem B4160105 : Blo 710320 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B2161691 : Blo 710320 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B4553927 : Blo 710320 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B12975389 : Blo 710320 12975389 := bstep (se 3 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 12975389 = 4865771) B4865771
theorem B3603851 : Blo 710320 3603851 := bstep (se 1 (by rfl) ⟨2702888, by rfl⟩ : syracuseStep 3603851 = 5405777) B5405777
theorem B13172183 : Blo 710320 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B2162153 : Blo 710320 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B1736171 : Blo 710320 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1801835 : Blo 710320 1801835 := bstep (se 1 (by rfl) ⟨1351376, by rfl⟩ : syracuseStep 1801835 = 2702753) B2702753
theorem B1015463 : Blo 710320 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B1802047 : Blo 710320 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B4063081 : Blo 710320 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B1802209 : Blo 710320 1802209 := bstep (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) B1351657
theorem B1605887 : Blo 710320 1605887 := bstep (se 1 (by rfl) ⟨1204415, by rfl⟩ : syracuseStep 1605887 = 2408831) B2408831
theorem B3606281 : Blo 710320 3606281 := bstep (se 2 (by rfl) ⟨1352355, by rfl⟩ : syracuseStep 3606281 = 2704711) B2704711
theorem B1804103 : Blo 710320 1804103 := bstep (se 1 (by rfl) ⟨1353077, by rfl⟩ : syracuseStep 1804103 = 2706155) B2706155
theorem B1804751 : Blo 710320 1804751 := bstep (se 1 (by rfl) ⟨1353563, by rfl⟩ : syracuseStep 1804751 = 2707127) B2707127
theorem B1444331 : Blo 710320 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B1805723 : Blo 710320 1805723 := bstep (se 1 (by rfl) ⟨1354292, by rfl⟩ : syracuseStep 1805723 = 2708585) B2708585
theorem B17305001 : Blo 710320 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B5148107 : Blo 710320 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B2821775 : Blo 710320 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B1806047 : Blo 710320 1806047 := bstep (se 1 (by rfl) ⟨1354535, by rfl⟩ : syracuseStep 1806047 = 2709071) B2709071
theorem B1348559 : Blo 710320 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B19764569 : Blo 710320 19764569 := bstep (se 2 (by rfl) ⟨7411713, by rfl⟩ : syracuseStep 19764569 = 14823427) B14823427
theorem B6165931 : Blo 710320 6165931 := bstep (se 1 (by rfl) ⟨4624448, by rfl⟩ : syracuseStep 6165931 = 9248897) B9248897
theorem B1349075 : Blo 710320 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B1808041 : Blo 710320 1808041 := bstep (se 2 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 1808041 = 1356031) B1356031
theorem B2430697 : Blo 710320 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B2398031 : Blo 710320 2398031 := bstep (se 1 (by rfl) ⟨1798523, by rfl⟩ : syracuseStep 2398031 = 3597047) B3597047
theorem B1349455 : Blo 710320 1349455 := bstep (se 1 (by rfl) ⟨1012091, by rfl⟩ : syracuseStep 1349455 = 2024183) B2024183
theorem B1349759 : Blo 710320 1349759 := bstep (se 1 (by rfl) ⟨1012319, by rfl⟩ : syracuseStep 1349759 = 2024639) B2024639
theorem B2398679 : Blo 710320 2398679 := bstep (se 1 (by rfl) ⟨1799009, by rfl⟩ : syracuseStep 2398679 = 3598019) B3598019
theorem B9149111 : Blo 710320 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B41720579 : Blo 710320 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B12164093 : Blo 710320 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B1711567 : Blo 710320 1711567 := bstep (se 1 (by rfl) ⟨1283675, by rfl⟩ : syracuseStep 1711567 = 2567351) B2567351
theorem B8134181 : Blo 710320 8134181 := bstep (se 4 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 8134181 = 1525159) B1525159
theorem B2400083 : Blo 710320 2400083 := bstep (se 1 (by rfl) ⟨1800062, by rfl⟩ : syracuseStep 2400083 = 3600125) B3600125
theorem B2891659 : Blo 710320 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B3612599 : Blo 710320 3612599 := bstep (se 1 (by rfl) ⟨2709449, by rfl⟩ : syracuseStep 3612599 = 5418899) B5418899
theorem B2171177 : Blo 710320 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B2400569 : Blo 710320 2400569 := bstep (se 2 (by rfl) ⟨900213, by rfl⟩ : syracuseStep 2400569 = 1800427) B1800427
theorem B6857065 : Blo 710320 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B2400623 : Blo 710320 2400623 := bstep (se 1 (by rfl) ⟨1800467, by rfl⟩ : syracuseStep 2400623 = 3600935) B3600935
theorem B2401055 : Blo 710320 2401055 := bstep (se 1 (by rfl) ⟨1800791, by rfl⟩ : syracuseStep 2401055 = 3601583) B3601583
theorem B2598247 : Blo 710320 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B5121407 : Blo 710320 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B1353199 : Blo 710320 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B2893735 : Blo 710320 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B2402567 : Blo 710320 2402567 := bstep (se 1 (by rfl) ⟨1801925, by rfl⟩ : syracuseStep 2402567 = 3603851) B3603851
theorem B2566441 : Blo 710320 2566441 := bstep (se 2 (by rfl) ⟨962415, by rfl⟩ : syracuseStep 2566441 = 1924831) B1924831
theorem B1157447 : Blo 710320 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B2402729 : Blo 710320 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B5417441 : Blo 710320 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B2402945 : Blo 710320 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B2599705 : Blo 710320 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B1354619 : Blo 710320 1354619 := bstep (se 1 (by rfl) ⟨1015964, by rfl⟩ : syracuseStep 1354619 = 2031929) B2031929
theorem B2403539 : Blo 710320 2403539 := bstep (se 1 (by rfl) ⟨1802654, by rfl⟩ : syracuseStep 2403539 = 3605309) B3605309
theorem B2895551 : Blo 710320 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B1355591 : Blo 710320 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B1519487 : Blo 710320 1519487 := bstep (se 1 (by rfl) ⟨1139615, by rfl⟩ : syracuseStep 1519487 = 2279231) B2279231
theorem B60764087 : Blo 710320 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B4567175 : Blo 710320 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B20591495 : Blo 710320 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B19510159 : Blo 710320 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B799771 : Blo 710320 799771 := bstep (se 1 (by rfl) ⟨599828, by rfl⟩ : syracuseStep 799771 = 1199657) B1199657
theorem B2405537 : Blo 710320 2405537 := bstep (se 2 (by rfl) ⟨902076, by rfl⟩ : syracuseStep 2405537 = 1804153) B1804153
theorem B12203459 : Blo 710320 12203459 := bstep (se 1 (by rfl) ⟨9152594, by rfl⟩ : syracuseStep 12203459 = 18305189) B18305189
theorem B44546183 : Blo 710320 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2407103 : Blo 710320 2407103 := bstep (se 1 (by rfl) ⟨1805327, by rfl⟩ : syracuseStep 2407103 = 3610655) B3610655
theorem B802075 : Blo 710320 802075 := bstep (se 1 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 802075 = 1203113) B1203113
theorem B2702767 : Blo 710320 2702767 := bstep (se 1 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 2702767 = 4054151) B4054151
theorem B1523785 : Blo 710320 1523785 := bstep (se 2 (by rfl) ⟨571419, by rfl⟩ : syracuseStep 1523785 = 1142839) B1142839
theorem B803263 : Blo 710320 803263 := bstep (se 1 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 803263 = 1204895) B1204895
theorem B1066025 : Blo 710320 1066025 := bstep (se 2 (by rfl) ⟨399759, by rfl⟩ : syracuseStep 1066025 = 799519) B799519
theorem B2410397 : Blo 710320 2410397 := bstep (se 3 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 2410397 = 903899) B903899
theorem B38979569 : Blo 710320 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B16697335 : Blo 710320 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B8112311 : Blo 710320 8112311 := bstep (se 1 (by rfl) ⟨6084233, by rfl⟩ : syracuseStep 8112311 = 12168467) B12168467
theorem B1067495 : Blo 710320 1067495 := bstep (se 1 (by rfl) ⟨800621, by rfl⟩ : syracuseStep 1067495 = 1601243) B1601243
theorem B1067675 : Blo 710320 1067675 := bstep (se 1 (by rfl) ⟨800756, by rfl⟩ : syracuseStep 1067675 = 1601513) B1601513
theorem B1067711 : Blo 710320 1067711 := bstep (se 1 (by rfl) ⟨800783, by rfl⟩ : syracuseStep 1067711 = 1601567) B1601567
theorem B8211169 : Blo 710320 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B1198847 : Blo 710320 1198847 := bstep (se 1 (by rfl) ⟨899135, by rfl⟩ : syracuseStep 1198847 = 1798271) B1798271
theorem B1068263 : Blo 710320 1068263 := bstep (se 1 (by rfl) ⟨801197, by rfl⟩ : syracuseStep 1068263 = 1602395) B1602395
theorem B20762081 : Blo 710320 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B12177215 : Blo 710320 12177215 := bstep (se 1 (by rfl) ⟨9132911, by rfl⟩ : syracuseStep 12177215 = 18265823) B18265823
theorem B1200487 : Blo 710320 1200487 := bstep (se 1 (by rfl) ⟨900365, by rfl⟩ : syracuseStep 1200487 = 1800731) B1800731
theorem B1069415 : Blo 710320 1069415 := bstep (se 1 (by rfl) ⟨802061, by rfl⟩ : syracuseStep 1069415 = 1604123) B1604123
theorem B2773403 : Blo 710320 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B2707901 : Blo 710320 2707901 := bstep (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) B1015463
theorem B2282203 : Blo 710320 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B3035951 : Blo 710320 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B4051943 : Blo 710320 4051943 := bstep (se 1 (by rfl) ⟨3038957, by rfl⟩ : syracuseStep 4051943 = 6077915) B6077915
theorem B1201223 : Blo 710320 1201223 := bstep (se 1 (by rfl) ⟨900917, by rfl⟩ : syracuseStep 1201223 = 1801835) B1801835
theorem B2053487 : Blo 710320 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B2708903 : Blo 710320 2708903 := bstep (se 1 (by rfl) ⟨2031677, by rfl⟩ : syracuseStep 2708903 = 4063355) B4063355
theorem B1070699 : Blo 710320 1070699 := bstep (se 1 (by rfl) ⟨803024, by rfl⟩ : syracuseStep 1070699 = 1606049) B1606049
theorem B710567 : Blo 710320 710567 := bstep (se 1 (by rfl) ⟨532925, by rfl⟩ : syracuseStep 710567 = 1065851) B1065851
theorem B1071071 : Blo 710320 1071071 := bstep (se 1 (by rfl) ⟨803303, by rfl⟩ : syracuseStep 1071071 = 1606607) B1606607
theorem B710651 : Blo 710320 710651 := bstep (se 1 (by rfl) ⟨532988, by rfl⟩ : syracuseStep 710651 = 1065977) B1065977
theorem B1071131 : Blo 710320 1071131 := bstep (se 1 (by rfl) ⟨803348, by rfl⟩ : syracuseStep 1071131 = 1606697) B1606697
theorem B710687 : Blo 710320 710687 := bstep (se 1 (by rfl) ⟨533015, by rfl⟩ : syracuseStep 710687 = 1066031) B1066031
theorem B710767 : Blo 710320 710767 := bstep (se 1 (by rfl) ⟨533075, by rfl⟩ : syracuseStep 710767 = 1066151) B1066151
theorem B1202303 : Blo 710320 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B710895 : Blo 710320 710895 := bstep (se 1 (by rfl) ⟨533171, by rfl⟩ : syracuseStep 710895 = 1066343) B1066343
theorem B12966331 : Blo 710320 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B1202681 : Blo 710320 1202681 := bstep (se 2 (by rfl) ⟨451005, by rfl⟩ : syracuseStep 1202681 = 902011) B902011
theorem B711323 : Blo 710320 711323 := bstep (se 1 (by rfl) ⟨533492, by rfl⟩ : syracuseStep 711323 = 1066985) B1066985
theorem B711419 : Blo 710320 711419 := bstep (se 1 (by rfl) ⟨533564, by rfl⟩ : syracuseStep 711419 = 1067129) B1067129
theorem B711551 : Blo 710320 711551 := bstep (se 1 (by rfl) ⟨533663, by rfl⟩ : syracuseStep 711551 = 1067327) B1067327
theorem B711647 : Blo 710320 711647 := bstep (se 1 (by rfl) ⟨533735, by rfl⟩ : syracuseStep 711647 = 1067471) B1067471
theorem B711675 : Blo 710320 711675 := bstep (se 1 (by rfl) ⟨533756, by rfl⟩ : syracuseStep 711675 = 1067513) B1067513
theorem B711707 : Blo 710320 711707 := bstep (se 1 (by rfl) ⟨533780, by rfl⟩ : syracuseStep 711707 = 1067561) B1067561
theorem B1203295 : Blo 710320 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B711999 : Blo 710320 711999 := bstep (se 1 (by rfl) ⟨533999, by rfl⟩ : syracuseStep 711999 = 1067999) B1067999
theorem B712295 : Blo 710320 712295 := bstep (se 1 (by rfl) ⟨534221, by rfl⟩ : syracuseStep 712295 = 1068443) B1068443
theorem B1203943 : Blo 710320 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B712539 : Blo 710320 712539 := bstep (se 1 (by rfl) ⟨534404, by rfl⟩ : syracuseStep 712539 = 1068809) B1068809
theorem B712575 : Blo 710320 712575 := bstep (se 1 (by rfl) ⟨534431, by rfl⟩ : syracuseStep 712575 = 1068863) B1068863
theorem B712735 : Blo 710320 712735 := bstep (se 1 (by rfl) ⟨534551, by rfl⟩ : syracuseStep 712735 = 1069103) B1069103
theorem B1204463 : Blo 710320 1204463 := bstep (se 1 (by rfl) ⟨903347, by rfl⟩ : syracuseStep 1204463 = 1806695) B1806695
theorem B713031 : Blo 710320 713031 := bstep (se 1 (by rfl) ⟨534773, by rfl⟩ : syracuseStep 713031 = 1069547) B1069547
theorem B713115 : Blo 710320 713115 := bstep (se 1 (by rfl) ⟨534836, by rfl⟩ : syracuseStep 713115 = 1069673) B1069673
theorem B713119 : Blo 710320 713119 := bstep (se 1 (by rfl) ⟨534839, by rfl⟩ : syracuseStep 713119 = 1069679) B1069679
theorem B5398973 : Blo 710320 5398973 := bstep (se 3 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 5398973 = 2024615) B2024615
theorem B713199 : Blo 710320 713199 := bstep (se 1 (by rfl) ⟨534899, by rfl⟩ : syracuseStep 713199 = 1069799) B1069799
theorem B49242629 : Blo 710320 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B713307 : Blo 710320 713307 := bstep (se 1 (by rfl) ⟨534980, by rfl⟩ : syracuseStep 713307 = 1069961) B1069961
theorem B1204841 : Blo 710320 1204841 := bstep (se 2 (by rfl) ⟨451815, by rfl⟩ : syracuseStep 1204841 = 903631) B903631
theorem B713535 : Blo 710320 713535 := bstep (se 1 (by rfl) ⟨535151, by rfl⟩ : syracuseStep 713535 = 1070303) B1070303
theorem B713563 : Blo 710320 713563 := bstep (se 1 (by rfl) ⟨535172, by rfl⟩ : syracuseStep 713563 = 1070345) B1070345
theorem B713855 : Blo 710320 713855 := bstep (se 1 (by rfl) ⟨535391, by rfl⟩ : syracuseStep 713855 = 1070783) B1070783
theorem B713883 : Blo 710320 713883 := bstep (se 1 (by rfl) ⟨535412, by rfl⟩ : syracuseStep 713883 = 1070825) B1070825
theorem B713887 : Blo 710320 713887 := bstep (se 1 (by rfl) ⟨535415, by rfl⟩ : syracuseStep 713887 = 1070831) B1070831
theorem B714223 : Blo 710320 714223 := bstep (se 1 (by rfl) ⟨535667, by rfl⟩ : syracuseStep 714223 = 1071335) B1071335
theorem B12347255 : Blo 710320 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B2025755 : Blo 710320 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B1599983 : Blo 710320 1599983 := bstep (se 1 (by rfl) ⟨1199987, by rfl⟩ : syracuseStep 1599983 = 2399975) B2399975
theorem B2780027 : Blo 710320 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B4058207 : Blo 710320 4058207 := bstep (se 1 (by rfl) ⟨3043655, by rfl⟩ : syracuseStep 4058207 = 6087311) B6087311
theorem B2026711 : Blo 710320 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B4058707 : Blo 710320 4058707 := bstep (se 1 (by rfl) ⟨3044030, by rfl⟩ : syracuseStep 4058707 = 6088061) B6088061
theorem B3043007 : Blo 710320 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B1601531 : Blo 710320 1601531 := bstep (se 1 (by rfl) ⟨1201148, by rfl⟩ : syracuseStep 1601531 = 2402297) B2402297
theorem B44462287 : Blo 710320 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B2028169 : Blo 710320 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B5141303 : Blo 710320 5141303 := bstep (se 1 (by rfl) ⟨3855977, by rfl⟩ : syracuseStep 5141303 = 7711955) B7711955
theorem B1798969 : Blo 710320 1798969 := bstep (se 2 (by rfl) ⟨674613, by rfl⟩ : syracuseStep 1798969 = 1349227) B1349227
theorem B1602539 : Blo 710320 1602539 := bstep (se 1 (by rfl) ⟨1201904, by rfl⟩ : syracuseStep 1602539 = 2403809) B2403809
theorem B1603151 : Blo 710320 1603151 := bstep (se 1 (by rfl) ⟨1202363, by rfl⟩ : syracuseStep 1603151 = 2404727) B2404727
theorem B1537883 : Blo 710320 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B1013897 : Blo 710320 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1800407 : Blo 710320 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B1603871 : Blo 710320 1603871 := bstep (se 1 (by rfl) ⟨1202903, by rfl⟩ : syracuseStep 1603871 = 2405807) B2405807
theorem B2881831 : Blo 710320 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B1603943 : Blo 710320 1603943 := bstep (se 1 (by rfl) ⟨1202957, by rfl⟩ : syracuseStep 1603943 = 2405915) B2405915
theorem B2030447 : Blo 710320 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1604591 : Blo 710320 1604591 := bstep (se 1 (by rfl) ⟨1203443, by rfl⟩ : syracuseStep 1604591 = 2406887) B2406887
theorem B1441127 : Blo 710320 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B8650259 : Blo 710320 8650259 := bstep (se 1 (by rfl) ⟨6487694, by rfl⟩ : syracuseStep 8650259 = 12975389) B12975389
theorem B133267031 : Blo 710320 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B1801865 : Blo 710320 1801865 := bstep (se 2 (by rfl) ⟨675699, by rfl⟩ : syracuseStep 1801865 = 1351399) B1351399
theorem B8781455 : Blo 710320 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B1441435 : Blo 710320 1441435 := bstep (se 1 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 1441435 = 2162153) B2162153
theorem B2031713 : Blo 710320 2031713 := bstep (se 2 (by rfl) ⟨761892, by rfl⟩ : syracuseStep 2031713 = 1523785) B1523785
theorem B9142753 : Blo 710320 9142753 := bstep (se 2 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 9142753 = 6857065) B6857065
theorem B1606931 : Blo 710320 1606931 := bstep (se 1 (by rfl) ⟨1205198, by rfl⟩ : syracuseStep 1606931 = 2410397) B2410397
theorem B25986379 : Blo 710320 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B5408207 : Blo 710320 5408207 := bstep (se 1 (by rfl) ⟨4056155, by rfl⟩ : syracuseStep 5408207 = 8112311) B8112311
theorem B1804265 : Blo 710320 1804265 := bstep (se 2 (by rfl) ⟨676599, by rfl⟩ : syracuseStep 1804265 = 1353199) B1353199
theorem B11536667 : Blo 710320 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B1805267 : Blo 710320 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B13176379 : Blo 710320 13176379 := bstep (se 1 (by rfl) ⟨9882284, by rfl⟩ : syracuseStep 13176379 = 19764569) B19764569
theorem B1805935 : Blo 710320 1805935 := bstep (se 1 (by rfl) ⟨1354451, by rfl⟩ : syracuseStep 1805935 = 2708903) B2708903
theorem B10948225 : Blo 710320 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B6099407 : Blo 710320 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B5411609 : Blo 710320 5411609 := bstep (se 2 (by rfl) ⟨2029353, by rfl⟩ : syracuseStep 5411609 = 4058707) B4058707
theorem B1447451 : Blo 710320 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B3086525 : Blo 710320 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B2398625 : Blo 710320 2398625 := bstep (se 2 (by rfl) ⟨899484, by rfl⟩ : syracuseStep 2398625 = 1798969) B1798969
theorem B8231503 : Blo 710320 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B1350503 : Blo 710320 1350503 := bstep (se 1 (by rfl) ⟨1012877, by rfl⟩ : syracuseStep 1350503 = 2025755) B2025755
theorem B3611627 : Blo 710320 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B5414525 : Blo 710320 5414525 := bstep (se 3 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 5414525 = 2030447) B2030447
theorem B40509391 : Blo 710320 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B3842441 : Blo 710320 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B8135639 : Blo 710320 8135639 := bstep (se 1 (by rfl) ⟨6101729, by rfl⟩ : syracuseStep 8135639 = 12203459) B12203459
theorem B1025255 : Blo 710320 1025255 := bstep (se 1 (by rfl) ⟨768941, by rfl⟩ : syracuseStep 1025255 = 1537883) B1537883
theorem B29697455 : Blo 710320 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B960751 : Blo 710320 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B88844687 : Blo 710320 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B2404187 : Blo 710320 2404187 := bstep (se 1 (by rfl) ⟨1803140, by rfl⟩ : syracuseStep 2404187 = 3606281) B3606281
theorem B799231 : Blo 710320 799231 := bstep (se 1 (by rfl) ⟨599423, by rfl⟩ : syracuseStep 799231 = 1198847) B1198847
theorem B13841387 : Blo 710320 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B22263113 : Blo 710320 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B1848935 : Blo 710320 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B3421921 : Blo 710320 3421921 := bstep (se 2 (by rfl) ⟨1283220, by rfl⟩ : syracuseStep 3421921 = 2566441) B2566441
theorem B899039 : Blo 710320 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B2701295 : Blo 710320 2701295 := bstep (se 1 (by rfl) ⟨2025971, by rfl⟩ : syracuseStep 2701295 = 4051943) B4051943
theorem B800815 : Blo 710320 800815 := bstep (se 1 (by rfl) ⟨600611, by rfl⟩ : syracuseStep 800815 = 1201223) B1201223
theorem B899839 : Blo 710320 899839 := bstep (se 1 (by rfl) ⟨674879, by rfl⟩ : syracuseStep 899839 = 1349759) B1349759
theorem B801535 : Blo 710320 801535 := bstep (se 1 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 801535 = 1202303) B1202303
theorem B2702281 : Blo 710320 2702281 := bstep (se 2 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 2702281 = 2026711) B2026711
theorem B801787 : Blo 710320 801787 := bstep (se 1 (by rfl) ⟨601340, by rfl⟩ : syracuseStep 801787 = 1202681) B1202681
theorem B8109395 : Blo 710320 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B5422787 : Blo 710320 5422787 := bstep (se 1 (by rfl) ⟨4067090, by rfl⟩ : syracuseStep 5422787 = 8134181) B8134181
theorem B2408399 : Blo 710320 2408399 := bstep (se 1 (by rfl) ⟨1806299, by rfl⟩ : syracuseStep 2408399 = 3612599) B3612599
theorem B802975 : Blo 710320 802975 := bstep (se 1 (by rfl) ⟨602231, by rfl⟩ : syracuseStep 802975 = 1204463) B1204463
theorem B2703725 : Blo 710320 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B803227 : Blo 710320 803227 := bstep (se 1 (by rfl) ⟨602420, by rfl⟩ : syracuseStep 803227 = 1204841) B1204841
theorem B2704225 : Blo 710320 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B3851549 : Blo 710320 3851549 := bstep (se 3 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 3851549 = 1444331) B1444331
theorem B1066361 : Blo 710320 1066361 := bstep (se 2 (by rfl) ⟨399885, by rfl⟩ : syracuseStep 1066361 = 799771) B799771
theorem B1066655 : Blo 710320 1066655 := bstep (se 1 (by rfl) ⟨799991, by rfl⟩ : syracuseStep 1066655 = 1599983) B1599983
theorem B1853351 : Blo 710320 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B903079 : Blo 710320 903079 := bstep (se 1 (by rfl) ⟨677309, by rfl⟩ : syracuseStep 903079 = 1354619) B1354619
theorem B2705471 : Blo 710320 2705471 := bstep (se 1 (by rfl) ⟨2029103, by rfl⟩ : syracuseStep 2705471 = 4058207) B4058207
theorem B2410721 : Blo 710320 2410721 := bstep (se 2 (by rfl) ⟨904020, by rfl⟩ : syracuseStep 2410721 = 1808041) B1808041
theorem B903727 : Blo 710320 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B1067687 : Blo 710320 1067687 := bstep (se 1 (by rfl) ⟨800765, by rfl⟩ : syracuseStep 1067687 = 1601531) B1601531
theorem B3427535 : Blo 710320 3427535 := bstep (se 1 (by rfl) ⟨2570651, by rfl⟩ : syracuseStep 3427535 = 5141303) B5141303
theorem B17288441 : Blo 710320 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B1068359 : Blo 710320 1068359 := bstep (se 1 (by rfl) ⟨801269, by rfl⟩ : syracuseStep 1068359 = 1602539) B1602539
theorem B1068767 : Blo 710320 1068767 := bstep (se 1 (by rfl) ⟨801575, by rfl⟩ : syracuseStep 1068767 = 1603151) B1603151
theorem B1200271 : Blo 710320 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1069247 : Blo 710320 1069247 := bstep (se 1 (by rfl) ⟨801935, by rfl⟩ : syracuseStep 1069247 = 1603871) B1603871
theorem B1069295 : Blo 710320 1069295 := bstep (se 1 (by rfl) ⟨801971, by rfl⟩ : syracuseStep 1069295 = 1603943) B1603943
theorem B1069433 : Blo 710320 1069433 := bstep (se 2 (by rfl) ⟨401037, by rfl⟩ : syracuseStep 1069433 = 802075) B802075
theorem B7524733 : Blo 710320 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B2282089 : Blo 710320 2282089 := bstep (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) B1711567
theorem B1069727 : Blo 710320 1069727 := bstep (se 1 (by rfl) ⟨802295, by rfl⟩ : syracuseStep 1069727 = 1604591) B1604591
theorem B1921913 : Blo 710320 1921913 := bstep (se 2 (by rfl) ⟨720717, by rfl⟩ : syracuseStep 1921913 = 1441435) B1441435
theorem B1201243 : Blo 710320 1201243 := bstep (se 1 (by rfl) ⟨900932, by rfl⟩ : syracuseStep 1201243 = 1801865) B1801865
theorem B5854303 : Blo 710320 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B3855545 : Blo 710320 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B1070591 : Blo 710320 1070591 := bstep (se 1 (by rfl) ⟨802943, by rfl⟩ : syracuseStep 1070591 = 1605887) B1605887
theorem B1071017 : Blo 710320 1071017 := bstep (se 2 (by rfl) ⟨401631, by rfl⟩ : syracuseStep 1071017 = 803263) B803263
theorem B710683 : Blo 710320 710683 := bstep (se 1 (by rfl) ⟨533012, by rfl⟩ : syracuseStep 710683 = 1066025) B1066025
theorem B237132197 : Blo 710320 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B1202735 : Blo 710320 1202735 := bstep (se 1 (by rfl) ⟨902051, by rfl⟩ : syracuseStep 1202735 = 1804103) B1804103
theorem B1203167 : Blo 710320 1203167 := bstep (se 1 (by rfl) ⟨902375, by rfl⟩ : syracuseStep 1203167 = 1804751) B1804751
theorem B711663 : Blo 710320 711663 := bstep (se 1 (by rfl) ⟨533747, by rfl⟩ : syracuseStep 711663 = 1067495) B1067495
theorem B711783 : Blo 710320 711783 := bstep (se 1 (by rfl) ⟨533837, by rfl⟩ : syracuseStep 711783 = 1067675) B1067675
theorem B711807 : Blo 710320 711807 := bstep (se 1 (by rfl) ⟨533855, by rfl⟩ : syracuseStep 711807 = 1067711) B1067711
theorem B3464329 : Blo 710320 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B712175 : Blo 710320 712175 := bstep (se 1 (by rfl) ⟨534131, by rfl⟩ : syracuseStep 712175 = 1068263) B1068263
theorem B1203815 : Blo 710320 1203815 := bstep (se 1 (by rfl) ⟨902861, by rfl⟩ : syracuseStep 1203815 = 1805723) B1805723
theorem B3432071 : Blo 710320 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B1204031 : Blo 710320 1204031 := bstep (se 1 (by rfl) ⟨903023, by rfl⟩ : syracuseStep 1204031 = 1806047) B1806047
theorem B8118143 : Blo 710320 8118143 := bstep (se 1 (by rfl) ⟨6088607, by rfl⟩ : syracuseStep 8118143 = 12177215) B12177215
theorem B3858313 : Blo 710320 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B712943 : Blo 710320 712943 := bstep (se 1 (by rfl) ⟨534707, by rfl⟩ : syracuseStep 712943 = 1069415) B1069415
theorem B2023967 : Blo 710320 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B1368991 : Blo 710320 1368991 := bstep (se 1 (by rfl) ⟨1026743, by rfl⟩ : syracuseStep 1368991 = 2053487) B2053487
theorem B13657085 : Blo 710320 13657085 := bstep (se 3 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 13657085 = 5121407) B5121407
theorem B3466273 : Blo 710320 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B713799 : Blo 710320 713799 := bstep (se 1 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 713799 = 1070699) B1070699
theorem B3597533 : Blo 710320 3597533 := bstep (se 3 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 3597533 = 1349075) B1349075
theorem B1598687 : Blo 710320 1598687 := bstep (se 1 (by rfl) ⟨1199015, by rfl⟩ : syracuseStep 1598687 = 2398031) B2398031
theorem B714047 : Blo 710320 714047 := bstep (se 1 (by rfl) ⟨535535, by rfl⟩ : syracuseStep 714047 = 1071071) B1071071
theorem B714087 : Blo 710320 714087 := bstep (se 1 (by rfl) ⟨535565, by rfl⟩ : syracuseStep 714087 = 1071131) B1071131
theorem B1599119 : Blo 710320 1599119 := bstep (se 1 (by rfl) ⟨1199339, by rfl⟩ : syracuseStep 1599119 = 2398679) B2398679
theorem B27813719 : Blo 710320 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B1600055 : Blo 710320 1600055 := bstep (se 1 (by rfl) ⟨1200041, by rfl⟩ : syracuseStep 1600055 = 2400083) B2400083
theorem B1600379 : Blo 710320 1600379 := bstep (se 1 (by rfl) ⟨1200284, by rfl⟩ : syracuseStep 1600379 = 2400569) B2400569
theorem B1600415 : Blo 710320 1600415 := bstep (se 1 (by rfl) ⟨1200311, by rfl⟩ : syracuseStep 1600415 = 2400623) B2400623
theorem B3599315 : Blo 710320 3599315 := bstep (se 1 (by rfl) ⟨2699486, by rfl⟩ : syracuseStep 3599315 = 5398973) B5398973
theorem B32828419 : Blo 710320 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B1600649 : Blo 710320 1600649 := bstep (se 2 (by rfl) ⟨600243, by rfl⟩ : syracuseStep 1600649 = 1200487) B1200487
theorem B1600703 : Blo 710320 1600703 := bstep (se 1 (by rfl) ⟨1200527, by rfl⟩ : syracuseStep 1600703 = 2401055) B2401055
theorem B3042937 : Blo 710320 3042937 := bstep (se 2 (by rfl) ⟨1141101, by rfl⟩ : syracuseStep 3042937 = 2282203) B2282203
theorem B26013545 : Blo 710320 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B1601711 : Blo 710320 1601711 := bstep (se 1 (by rfl) ⟨1201283, by rfl⟩ : syracuseStep 1601711 = 2402567) B2402567
theorem B1601819 : Blo 710320 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B1601963 : Blo 710320 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B8221241 : Blo 710320 8221241 := bstep (se 2 (by rfl) ⟨3082965, by rfl⟩ : syracuseStep 8221241 = 6165931) B6165931
theorem B1602359 : Blo 710320 1602359 := bstep (se 1 (by rfl) ⟨1201769, by rfl⟩ : syracuseStep 1602359 = 2403539) B2403539
theorem B3240929 : Blo 710320 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B1799273 : Blo 710320 1799273 := bstep (se 2 (by rfl) ⟨674727, by rfl⟩ : syracuseStep 1799273 = 1349455) B1349455
theorem B2028671 : Blo 710320 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B1930367 : Blo 710320 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B1012991 : Blo 710320 1012991 := bstep (se 1 (by rfl) ⟨759743, by rfl⟩ : syracuseStep 1012991 = 1519487) B1519487
theorem B3044783 : Blo 710320 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B13727663 : Blo 710320 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B1603691 : Blo 710320 1603691 := bstep (se 1 (by rfl) ⟨1202768, by rfl⟩ : syracuseStep 1603691 = 2405537) B2405537
theorem B1604393 : Blo 710320 1604393 := bstep (se 2 (by rfl) ⟨601647, by rfl⟩ : syracuseStep 1604393 = 1203295) B1203295
theorem B1604735 : Blo 710320 1604735 := bstep (se 1 (by rfl) ⟨1203551, by rfl⟩ : syracuseStep 1604735 = 2407103) B2407103
theorem B3603689 : Blo 710320 3603689 := bstep (se 2 (by rfl) ⟨1351383, by rfl⟩ : syracuseStep 3603689 = 2702767) B2702767
theorem B1605257 : Blo 710320 1605257 := bstep (se 2 (by rfl) ⟨601971, by rfl⟩ : syracuseStep 1605257 = 1203943) B1203943
theorem B5766839 : Blo 710320 5766839 := bstep (se 1 (by rfl) ⟨4325129, by rfl⟩ : syracuseStep 5766839 = 8650259) B8650259
theorem B1802483 : Blo 710320 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B12190337 : Blo 710320 12190337 := bstep (se 2 (by rfl) ⟨4571376, by rfl⟩ : syracuseStep 12190337 = 9142753) B9142753
theorem B3605471 : Blo 710320 3605471 := bstep (se 1 (by rfl) ⟨2704103, by rfl⟩ : syracuseStep 3605471 = 5408207) B5408207
theorem B3605633 : Blo 710320 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B1803647 : Blo 710320 1803647 := bstep (se 1 (by rfl) ⟨1352735, by rfl⟩ : syracuseStep 1803647 = 2705471) B2705471
theorem B4621697 : Blo 710320 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B1607147 : Blo 710320 1607147 := bstep (se 1 (by rfl) ⟨1205360, by rfl⟩ : syracuseStep 1607147 = 2410721) B2410721
theorem B4066271 : Blo 710320 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B3607739 : Blo 710320 3607739 := bstep (se 1 (by rfl) ⟨2705804, by rfl⟩ : syracuseStep 3607739 = 5411609) B5411609
theorem B1281275 : Blo 710320 1281275 := bstep (se 1 (by rfl) ⟨960956, by rfl⟩ : syracuseStep 1281275 = 1921913) B1921913
theorem B17568505 : Blo 710320 17568505 := bstep (se 2 (by rfl) ⟨6588189, by rfl⟩ : syracuseStep 17568505 = 13176379) B13176379
theorem B3609683 : Blo 710320 3609683 := bstep (se 1 (by rfl) ⟨2707262, by rfl⟩ : syracuseStep 3609683 = 5414525) B5414525
theorem B2397437 : Blo 710320 2397437 := bstep (se 3 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 2397437 = 899039) B899039
theorem B5412095 : Blo 710320 5412095 := bstep (se 1 (by rfl) ⟨4059071, by rfl⟩ : syracuseStep 5412095 = 8118143) B8118143
theorem B175084901 : Blo 710320 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B2561627 : Blo 710320 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B1349311 : Blo 710320 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B10032977 : Blo 710320 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B2398355 : Blo 710320 2398355 := bstep (se 1 (by rfl) ⟨1798766, by rfl⟩ : syracuseStep 2398355 = 3597533) B3597533
theorem B7805737 : Blo 710320 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B2399543 : Blo 710320 2399543 := bstep (se 1 (by rfl) ⟨1799657, by rfl⟩ : syracuseStep 2399543 = 3599315) B3599315
theorem B4562561 : Blo 710320 4562561 := bstep (se 2 (by rfl) ⟨1710960, by rfl⟩ : syracuseStep 4562561 = 3421921) B3421921
theorem B17342363 : Blo 710320 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B5480827 : Blo 710320 5480827 := bstep (se 1 (by rfl) ⟨4110620, by rfl⟩ : syracuseStep 5480827 = 8221241) B8221241
theorem B1352447 : Blo 710320 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B1286911 : Blo 710320 1286911 := bstep (se 1 (by rfl) ⟨965183, by rfl⟩ : syracuseStep 1286911 = 1930367) B1930367
theorem B9151775 : Blo 710320 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B2402459 : Blo 710320 2402459 := bstep (se 1 (by rfl) ⟨1801844, by rfl⟩ : syracuseStep 2402459 = 3603689) B3603689
theorem B3844559 : Blo 710320 3844559 := bstep (se 1 (by rfl) ⟨2883419, by rfl⟩ : syracuseStep 3844559 = 5766839) B5766839
theorem B3615191 : Blo 710320 3615191 := bstep (se 1 (by rfl) ⟨2711393, by rfl⟩ : syracuseStep 3615191 = 5422787) B5422787
theorem B54012521 : Blo 710320 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B1354475 : Blo 710320 1354475 := bstep (se 1 (by rfl) ⟨1015856, by rfl⟩ : syracuseStep 1354475 = 2031713) B2031713
theorem B2567699 : Blo 710320 2567699 := bstep (se 1 (by rfl) ⟨1925774, by rfl⟩ : syracuseStep 2567699 = 3851549) B3851549
theorem B5124005 : Blo 710320 5124005 := bstep (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) B960751
theorem B34648505 : Blo 710320 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B2734013 : Blo 710320 2734013 := bstep (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) B1025255
theorem B2701309 : Blo 710320 2701309 := bstep (se 3 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 2701309 = 1012991) B1012991
theorem B2570363 : Blo 710320 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B964967 : Blo 710320 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B158088131 : Blo 710320 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B801823 : Blo 710320 801823 := bstep (se 1 (by rfl) ⟨601367, by rfl⟩ : syracuseStep 801823 = 1202735) B1202735
theorem B900335 : Blo 710320 900335 := bstep (se 1 (by rfl) ⟨675251, by rfl⟩ : syracuseStep 900335 = 1350503) B1350503
theorem B802111 : Blo 710320 802111 := bstep (se 1 (by rfl) ⟨601583, by rfl⟩ : syracuseStep 802111 = 1203167) B1203167
theorem B2407751 : Blo 710320 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B2407913 : Blo 710320 2407913 := bstep (se 2 (by rfl) ⟨902967, by rfl⟩ : syracuseStep 2407913 = 1805935) B1805935
theorem B14597633 : Blo 710320 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B802543 : Blo 710320 802543 := bstep (se 1 (by rfl) ⟨601907, by rfl⟩ : syracuseStep 802543 = 1203815) B1203815
theorem B802687 : Blo 710320 802687 := bstep (se 1 (by rfl) ⟨602015, by rfl⟩ : syracuseStep 802687 = 1204031) B1204031
theorem B5423759 : Blo 710320 5423759 := bstep (se 1 (by rfl) ⟨4067819, by rfl⟩ : syracuseStep 5423759 = 8135639) B8135639
theorem B1065641 : Blo 710320 1065641 := bstep (se 2 (by rfl) ⟨399615, by rfl⟩ : syracuseStep 1065641 = 799231) B799231
theorem B1065791 : Blo 710320 1065791 := bstep (se 1 (by rfl) ⟨799343, by rfl⟩ : syracuseStep 1065791 = 1598687) B1598687
theorem B1066079 : Blo 710320 1066079 := bstep (se 1 (by rfl) ⟨799559, by rfl⟩ : syracuseStep 1066079 = 1599119) B1599119
theorem B59229791 : Blo 710320 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B1066703 : Blo 710320 1066703 := bstep (se 1 (by rfl) ⟨800027, by rfl⟩ : syracuseStep 1066703 = 1600055) B1600055
theorem B1066919 : Blo 710320 1066919 := bstep (se 1 (by rfl) ⟨800189, by rfl⟩ : syracuseStep 1066919 = 1600379) B1600379
theorem B1066943 : Blo 710320 1066943 := bstep (se 1 (by rfl) ⟨800207, by rfl⟩ : syracuseStep 1066943 = 1600415) B1600415
theorem B1067099 : Blo 710320 1067099 := bstep (se 1 (by rfl) ⟨800324, by rfl⟩ : syracuseStep 1067099 = 1600649) B1600649
theorem B1067135 : Blo 710320 1067135 := bstep (se 1 (by rfl) ⟨800351, by rfl⟩ : syracuseStep 1067135 = 1600703) B1600703
theorem B1067753 : Blo 710320 1067753 := bstep (se 2 (by rfl) ⟨400407, by rfl⟩ : syracuseStep 1067753 = 800815) B800815
theorem B1067807 : Blo 710320 1067807 := bstep (se 1 (by rfl) ⟨800855, by rfl⟩ : syracuseStep 1067807 = 1601711) B1601711
theorem B1067879 : Blo 710320 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B1067975 : Blo 710320 1067975 := bstep (se 1 (by rfl) ⟨800981, by rfl⟩ : syracuseStep 1067975 = 1601963) B1601963
theorem B1068239 : Blo 710320 1068239 := bstep (se 1 (by rfl) ⟨801179, by rfl⟩ : syracuseStep 1068239 = 1602359) B1602359
theorem B9227591 : Blo 710320 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B1199515 : Blo 710320 1199515 := bstep (se 1 (by rfl) ⟨899636, by rfl⟩ : syracuseStep 1199515 = 1799273) B1799273
theorem B1199785 : Blo 710320 1199785 := bstep (se 2 (by rfl) ⟨449919, by rfl⟩ : syracuseStep 1199785 = 899839) B899839
theorem B1068713 : Blo 710320 1068713 := bstep (se 2 (by rfl) ⟨400767, by rfl⟩ : syracuseStep 1068713 = 801535) B801535
theorem B1232623 : Blo 710320 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B1069049 : Blo 710320 1069049 := bstep (se 2 (by rfl) ⟨400893, by rfl⟩ : syracuseStep 1069049 = 801787) B801787
theorem B1069127 : Blo 710320 1069127 := bstep (se 1 (by rfl) ⟨801845, by rfl⟩ : syracuseStep 1069127 = 1603691) B1603691
theorem B1069595 : Blo 710320 1069595 := bstep (se 1 (by rfl) ⟨802196, by rfl⟩ : syracuseStep 1069595 = 1604393) B1604393
theorem B1069823 : Blo 710320 1069823 := bstep (se 1 (by rfl) ⟨802367, by rfl⟩ : syracuseStep 1069823 = 1604735) B1604735
theorem B1070171 : Blo 710320 1070171 := bstep (se 1 (by rfl) ⟨802628, by rfl⟩ : syracuseStep 1070171 = 1605257) B1605257
theorem B1070633 : Blo 710320 1070633 := bstep (se 2 (by rfl) ⟨401487, by rfl⟩ : syracuseStep 1070633 = 802975) B802975
theorem B1070969 : Blo 710320 1070969 := bstep (se 2 (by rfl) ⟨401613, by rfl⟩ : syracuseStep 1070969 = 803227) B803227
theorem B1071287 : Blo 710320 1071287 := bstep (se 1 (by rfl) ⟨803465, by rfl⟩ : syracuseStep 1071287 = 1606931) B1606931
theorem B710907 : Blo 710320 710907 := bstep (se 1 (by rfl) ⟨533180, by rfl⟩ : syracuseStep 710907 = 1066361) B1066361
theorem B711103 : Blo 710320 711103 := bstep (se 1 (by rfl) ⟨533327, by rfl⟩ : syracuseStep 711103 = 1066655) B1066655
theorem B1235567 : Blo 710320 1235567 := bstep (se 1 (by rfl) ⟨926675, by rfl⟩ : syracuseStep 1235567 = 1853351) B1853351
theorem B1202843 : Blo 710320 1202843 := bstep (se 1 (by rfl) ⟨902132, by rfl⟩ : syracuseStep 1202843 = 1804265) B1804265
theorem B7691111 : Blo 710320 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B711791 : Blo 710320 711791 := bstep (se 1 (by rfl) ⟨533843, by rfl⟩ : syracuseStep 711791 = 1067687) B1067687
theorem B1203511 : Blo 710320 1203511 := bstep (se 1 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 1203511 = 1805267) B1805267
theorem B2285023 : Blo 710320 2285023 := bstep (se 1 (by rfl) ⟨1713767, by rfl⟩ : syracuseStep 2285023 = 3427535) B3427535
theorem B11525627 : Blo 710320 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B712239 : Blo 710320 712239 := bstep (se 1 (by rfl) ⟨534179, by rfl⟩ : syracuseStep 712239 = 1068359) B1068359
theorem B712511 : Blo 710320 712511 := bstep (se 1 (by rfl) ⟨534383, by rfl⟩ : syracuseStep 712511 = 1068767) B1068767
theorem B1204105 : Blo 710320 1204105 := bstep (se 2 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 1204105 = 903079) B903079
theorem B8642477 : Blo 710320 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B712831 : Blo 710320 712831 := bstep (se 1 (by rfl) ⟨534623, by rfl⟩ : syracuseStep 712831 = 1069247) B1069247
theorem B712863 : Blo 710320 712863 := bstep (se 1 (by rfl) ⟨534647, by rfl⟩ : syracuseStep 712863 = 1069295) B1069295
theorem B712955 : Blo 710320 712955 := bstep (se 1 (by rfl) ⟨534716, by rfl⟩ : syracuseStep 712955 = 1069433) B1069433
theorem B713151 : Blo 710320 713151 := bstep (se 1 (by rfl) ⟨534863, by rfl⟩ : syracuseStep 713151 = 1069727) B1069727
theorem B1204969 : Blo 710320 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B713727 : Blo 710320 713727 := bstep (se 1 (by rfl) ⟨535295, by rfl⟩ : syracuseStep 713727 = 1070591) B1070591
theorem B79193213 : Blo 710320 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B714011 : Blo 710320 714011 := bstep (se 1 (by rfl) ⟨535508, by rfl⟩ : syracuseStep 714011 = 1071017) B1071017
theorem B2057683 : Blo 710320 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B1599083 : Blo 710320 1599083 := bstep (se 1 (by rfl) ⟨1199312, by rfl⟩ : syracuseStep 1599083 = 2398625) B2398625
theorem B4057249 : Blo 710320 4057249 := bstep (se 2 (by rfl) ⟨1521468, by rfl⟩ : syracuseStep 4057249 = 3042937) B3042937
theorem B7301285 : Blo 710320 7301285 := bstep (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) B1368991
theorem B2288047 : Blo 710320 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B1600361 : Blo 710320 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B9104723 : Blo 710320 9104723 := bstep (se 1 (by rfl) ⟨6828542, by rfl⟩ : syracuseStep 9104723 = 13657085) B13657085
theorem B3042785 : Blo 710320 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B18542479 : Blo 710320 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B1601657 : Blo 710320 1601657 := bstep (se 2 (by rfl) ⟨600621, by rfl⟩ : syracuseStep 1601657 = 1201243) B1201243
theorem B1602791 : Blo 710320 1602791 := bstep (se 1 (by rfl) ⟨1202093, by rfl⟩ : syracuseStep 1602791 = 2404187) B2404187
theorem B10975337 : Blo 710320 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B14842075 : Blo 710320 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B2029855 : Blo 710320 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B3603041 : Blo 710320 3603041 := bstep (se 2 (by rfl) ⟨1351140, by rfl⟩ : syracuseStep 3603041 = 2702281) B2702281
theorem B1800863 : Blo 710320 1800863 := bstep (se 1 (by rfl) ⟨1350647, by rfl⟩ : syracuseStep 1800863 = 2701295) B2701295
theorem B4619105 : Blo 710320 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B5406263 : Blo 710320 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B5144417 : Blo 710320 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B1605599 : Blo 710320 1605599 := bstep (se 1 (by rfl) ⟨1204199, by rfl⟩ : syracuseStep 1605599 = 2408399) B2408399
theorem B8126891 : Blo 710320 8126891 := bstep (se 1 (by rfl) ⟨6095168, by rfl⟩ : syracuseStep 8126891 = 12190337) B12190337
theorem B3081131 : Blo 710320 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B1606625 : Blo 710320 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B39486527 : Blo 710320 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B29231077 : Blo 710320 29231077 := bstep (se 4 (by rfl) ⟨2740413, by rfl⟩ : syracuseStep 29231077 = 5480827) B5480827
theorem B854183 : Blo 710320 854183 := bstep (se 1 (by rfl) ⟨640637, by rfl⟩ : syracuseStep 854183 = 1281275) B1281275
theorem B5409665 : Blo 710320 5409665 := bstep (se 2 (by rfl) ⟨2028624, by rfl⟩ : syracuseStep 5409665 = 4057249) B4057249
theorem B3050729 : Blo 710320 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B3608063 : Blo 710320 3608063 := bstep (se 1 (by rfl) ⟨2706047, by rfl⟩ : syracuseStep 3608063 = 5412095) B5412095
theorem B116723267 : Blo 710320 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B1707751 : Blo 710320 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B6688651 : Blo 710320 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B823711 : Blo 710320 823711 := bstep (se 1 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 823711 = 1235567) B1235567
theorem B1643497 : Blo 710320 1643497 := bstep (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) B1232623
theorem B52795475 : Blo 710320 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B6101183 : Blo 710320 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B2563039 : Blo 710320 2563039 := bstep (se 1 (by rfl) ⟨1922279, by rfl⟩ : syracuseStep 2563039 = 3844559) B3844559
theorem B6069815 : Blo 710320 6069815 := bstep (se 1 (by rfl) ⟨4552361, by rfl⟩ : syracuseStep 6069815 = 9104723) B9104723
theorem B1711799 : Blo 710320 1711799 := bstep (se 1 (by rfl) ⟨1283849, by rfl⟩ : syracuseStep 1711799 = 2567699) B2567699
theorem B3416003 : Blo 710320 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2400893 : Blo 710320 2400893 := bstep (se 3 (by rfl) ⟨450167, by rfl⟩ : syracuseStep 2400893 = 900335) B900335
theorem B7316891 : Blo 710320 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B1713575 : Blo 710320 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B2402027 : Blo 710320 2402027 := bstep (se 1 (by rfl) ⟨1801520, by rfl⟩ : syracuseStep 2402027 = 3603041) B3603041
theorem B105392087 : Blo 710320 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B3615839 : Blo 710320 3615839 := bstep (se 1 (by rfl) ⟨2711879, by rfl⟩ : syracuseStep 3615839 = 5423759) B5423759
theorem B2403647 : Blo 710320 2403647 := bstep (se 1 (by rfl) ⟨1802735, by rfl⟩ : syracuseStep 2403647 = 3605471) B3605471
theorem B2403755 : Blo 710320 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B2405159 : Blo 710320 2405159 := bstep (se 1 (by rfl) ⟨1803869, by rfl⟩ : syracuseStep 2405159 = 3607739) B3607739
theorem B2406455 : Blo 710320 2406455 := bstep (se 1 (by rfl) ⟨1804841, by rfl⟩ : syracuseStep 2406455 = 3609683) B3609683
theorem B6863525 : Blo 710320 6863525 := bstep (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) B1286911
theorem B801895 : Blo 710320 801895 := bstep (se 1 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 801895 = 1202843) B1202843
theorem B5127407 : Blo 710320 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B7683751 : Blo 710320 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B24723305 : Blo 710320 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B901631 : Blo 710320 901631 := bstep (se 1 (by rfl) ⟨676223, by rfl⟩ : syracuseStep 901631 = 1352447) B1352447
theorem B2573245 : Blo 710320 2573245 := bstep (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) B964967
theorem B1066055 : Blo 710320 1066055 := bstep (se 1 (by rfl) ⟨799541, by rfl⟩ : syracuseStep 1066055 = 1599083) B1599083
theorem B4867523 : Blo 710320 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B2410127 : Blo 710320 2410127 := bstep (se 1 (by rfl) ⟨1807595, by rfl⟩ : syracuseStep 2410127 = 3615191) B3615191
theorem B902983 : Blo 710320 902983 := bstep (se 1 (by rfl) ⟨677237, by rfl⟩ : syracuseStep 902983 = 1354475) B1354475
theorem B1066907 : Blo 710320 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B1067771 : Blo 710320 1067771 := bstep (se 1 (by rfl) ⟨800828, by rfl⟩ : syracuseStep 1067771 = 1601657) B1601657
theorem B2706473 : Blo 710320 2706473 := bstep (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) B2029855
theorem B1068527 : Blo 710320 1068527 := bstep (se 1 (by rfl) ⟨801395, by rfl⟩ : syracuseStep 1068527 = 1602791) B1602791
theorem B10407649 : Blo 710320 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B1822675 : Blo 710320 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B1069097 : Blo 710320 1069097 := bstep (se 2 (by rfl) ⟨400911, by rfl⟩ : syracuseStep 1069097 = 801823) B801823
theorem B1069481 : Blo 710320 1069481 := bstep (se 2 (by rfl) ⟨401055, by rfl⟩ : syracuseStep 1069481 = 802111) B802111
theorem B1200575 : Blo 710320 1200575 := bstep (se 1 (by rfl) ⟨900431, by rfl⟩ : syracuseStep 1200575 = 1800863) B1800863
theorem B1070057 : Blo 710320 1070057 := bstep (se 2 (by rfl) ⟨401271, by rfl⟩ : syracuseStep 1070057 = 802543) B802543
theorem B1070249 : Blo 710320 1070249 := bstep (se 2 (by rfl) ⟨401343, by rfl⟩ : syracuseStep 1070249 = 802687) B802687
theorem B3429611 : Blo 710320 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B1070399 : Blo 710320 1070399 := bstep (se 1 (by rfl) ⟨802799, by rfl⟩ : syracuseStep 1070399 = 1605599) B1605599
theorem B1201655 : Blo 710320 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B710427 : Blo 710320 710427 := bstep (se 1 (by rfl) ⟨532820, by rfl⟩ : syracuseStep 710427 = 1065641) B1065641
theorem B710527 : Blo 710320 710527 := bstep (se 1 (by rfl) ⟨532895, by rfl⟩ : syracuseStep 710527 = 1065791) B1065791
theorem B710719 : Blo 710320 710719 := bstep (se 1 (by rfl) ⟨533039, by rfl⟩ : syracuseStep 710719 = 1066079) B1066079
theorem B1202431 : Blo 710320 1202431 := bstep (se 1 (by rfl) ⟨901823, by rfl⟩ : syracuseStep 1202431 = 1803647) B1803647
theorem B1071431 : Blo 710320 1071431 := bstep (se 1 (by rfl) ⟨803573, by rfl⟩ : syracuseStep 1071431 = 1607147) B1607147
theorem B711135 : Blo 710320 711135 := bstep (se 1 (by rfl) ⟨533351, by rfl⟩ : syracuseStep 711135 = 1066703) B1066703
theorem B711279 : Blo 710320 711279 := bstep (se 1 (by rfl) ⟨533459, by rfl⟩ : syracuseStep 711279 = 1066919) B1066919
theorem B711295 : Blo 710320 711295 := bstep (se 1 (by rfl) ⟨533471, by rfl⟩ : syracuseStep 711295 = 1066943) B1066943
theorem B711399 : Blo 710320 711399 := bstep (se 1 (by rfl) ⟨533549, by rfl⟩ : syracuseStep 711399 = 1067099) B1067099
theorem B711423 : Blo 710320 711423 := bstep (se 1 (by rfl) ⟨533567, by rfl⟩ : syracuseStep 711423 = 1067135) B1067135
theorem B711835 : Blo 710320 711835 := bstep (se 1 (by rfl) ⟨533876, by rfl⟩ : syracuseStep 711835 = 1067753) B1067753
theorem B711871 : Blo 710320 711871 := bstep (se 1 (by rfl) ⟨533903, by rfl⟩ : syracuseStep 711871 = 1067807) B1067807
theorem B711919 : Blo 710320 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B2743577 : Blo 710320 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B711983 : Blo 710320 711983 := bstep (se 1 (by rfl) ⟨533987, by rfl⟩ : syracuseStep 711983 = 1067975) B1067975
theorem B2710847 : Blo 710320 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B712159 : Blo 710320 712159 := bstep (se 1 (by rfl) ⟨534119, by rfl⟩ : syracuseStep 712159 = 1068239) B1068239
theorem B6151727 : Blo 710320 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B712475 : Blo 710320 712475 := bstep (se 1 (by rfl) ⟨534356, by rfl⟩ : syracuseStep 712475 = 1068713) B1068713
theorem B712699 : Blo 710320 712699 := bstep (se 1 (by rfl) ⟨534524, by rfl⟩ : syracuseStep 712699 = 1069049) B1069049
theorem B712751 : Blo 710320 712751 := bstep (se 1 (by rfl) ⟨534563, by rfl⟩ : syracuseStep 712751 = 1069127) B1069127
theorem B713063 : Blo 710320 713063 := bstep (se 1 (by rfl) ⟨534797, by rfl⟩ : syracuseStep 713063 = 1069595) B1069595
theorem B713215 : Blo 710320 713215 := bstep (se 1 (by rfl) ⟨534911, by rfl⟩ : syracuseStep 713215 = 1069823) B1069823
theorem B713447 : Blo 710320 713447 := bstep (se 1 (by rfl) ⟨535085, by rfl⟩ : syracuseStep 713447 = 1070171) B1070171
theorem B1598291 : Blo 710320 1598291 := bstep (se 1 (by rfl) ⟨1198718, by rfl⟩ : syracuseStep 1598291 = 2397437) B2397437
theorem B713755 : Blo 710320 713755 := bstep (se 1 (by rfl) ⟨535316, by rfl⟩ : syracuseStep 713755 = 1070633) B1070633
theorem B713979 : Blo 710320 713979 := bstep (se 1 (by rfl) ⟨535484, by rfl⟩ : syracuseStep 713979 = 1070969) B1070969
theorem B1598903 : Blo 710320 1598903 := bstep (se 1 (by rfl) ⟨1199177, by rfl⟩ : syracuseStep 1598903 = 2398355) B2398355
theorem B714191 : Blo 710320 714191 := bstep (se 1 (by rfl) ⟨535643, by rfl⟩ : syracuseStep 714191 = 1071287) B1071287
theorem B1599353 : Blo 710320 1599353 := bstep (se 2 (by rfl) ⟨599757, by rfl⟩ : syracuseStep 1599353 = 1199515) B1199515
theorem B1599695 : Blo 710320 1599695 := bstep (se 1 (by rfl) ⟨1199771, by rfl⟩ : syracuseStep 1599695 = 2399543) B2399543
theorem B1599713 : Blo 710320 1599713 := bstep (se 2 (by rfl) ⟨599892, by rfl⟩ : syracuseStep 1599713 = 1199785) B1199785
theorem B3041707 : Blo 710320 3041707 := bstep (se 1 (by rfl) ⟨2281280, by rfl⟩ : syracuseStep 3041707 = 4562561) B4562561
theorem B11561575 : Blo 710320 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B5761651 : Blo 710320 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B23424673 : Blo 710320 23424673 := bstep (se 2 (by rfl) ⟨8784252, by rfl⟩ : syracuseStep 23424673 = 17568505) B17568505
theorem B1601639 : Blo 710320 1601639 := bstep (se 1 (by rfl) ⟨1201229, by rfl⟩ : syracuseStep 1601639 = 2402459) B2402459
theorem B36008347 : Blo 710320 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B1799081 : Blo 710320 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B2028523 : Blo 710320 2028523 := bstep (se 1 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 2028523 = 3042785) B3042785
theorem B3601745 : Blo 710320 3601745 := bstep (se 2 (by rfl) ⟨1350654, by rfl⟩ : syracuseStep 3601745 = 2701309) B2701309
theorem B19789433 : Blo 710320 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B23099003 : Blo 710320 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B1604681 : Blo 710320 1604681 := bstep (se 2 (by rfl) ⟨601755, by rfl⟩ : syracuseStep 1604681 = 1203511) B1203511
theorem B3079403 : Blo 710320 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B3046697 : Blo 710320 3046697 := bstep (se 2 (by rfl) ⟨1142511, by rfl⟩ : syracuseStep 3046697 = 2285023) B2285023
theorem B1605167 : Blo 710320 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B1605275 : Blo 710320 1605275 := bstep (se 1 (by rfl) ⟨1203956, by rfl⟩ : syracuseStep 1605275 = 2407913) B2407913
theorem B9731755 : Blo 710320 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B3604175 : Blo 710320 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B1605473 : Blo 710320 1605473 := bstep (se 2 (by rfl) ⟨602052, by rfl⟩ : syracuseStep 1605473 = 1204105) B1204105
theorem B3245015 : Blo 710320 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B1606751 : Blo 710320 1606751 := bstep (se 1 (by rfl) ⟨1205063, by rfl⟩ : syracuseStep 1606751 = 2410127) B2410127
theorem B3606443 : Blo 710320 3606443 := bstep (se 1 (by rfl) ⟨2704832, by rfl⟩ : syracuseStep 3606443 = 5409665) B5409665
theorem B1804315 : Blo 710320 1804315 := bstep (se 1 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 1804315 = 2706473) B2706473
theorem B2033819 : Blo 710320 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B35196983 : Blo 710320 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B4067455 : Blo 710320 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B1807231 : Blo 710320 1807231 := bstep (se 1 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 1807231 = 2710847) B2710847
theorem B31232897 : Blo 710320 31232897 := bstep (se 2 (by rfl) ⟨11712336, by rfl⟩ : syracuseStep 31232897 = 23424673) B23424673
theorem B4101151 : Blo 710320 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B8918201 : Blo 710320 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B2430233 : Blo 710320 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B48011129 : Blo 710320 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B70261391 : Blo 710320 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B2401163 : Blo 710320 2401163 := bstep (se 1 (by rfl) ⟨1800872, by rfl⟩ : syracuseStep 2401163 = 3601745) B3601745
theorem B3417385 : Blo 710320 3417385 := bstep (se 2 (by rfl) ⟨1281519, by rfl⟩ : syracuseStep 3417385 = 2563039) B2563039
theorem B3418271 : Blo 710320 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B2402783 : Blo 710320 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B5417927 : Blo 710320 5417927 := bstep (se 1 (by rfl) ⟨4063445, by rfl⟩ : syracuseStep 5417927 = 8126891) B8126891
theorem B26324351 : Blo 710320 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B2404349 : Blo 710320 2404349 := bstep (se 3 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 2404349 = 901631) B901631
theorem B2405375 : Blo 710320 2405375 := bstep (se 1 (by rfl) ⟨1804031, by rfl⟩ : syracuseStep 2405375 = 3608063) B3608063
theorem B38974769 : Blo 710320 38974769 := bstep (se 2 (by rfl) ⟨14615538, by rfl⟩ : syracuseStep 38974769 = 29231077) B29231077
theorem B800383 : Blo 710320 800383 := bstep (se 1 (by rfl) ⟨600287, by rfl⟩ : syracuseStep 800383 = 1200575) B1200575
theorem B15415433 : Blo 710320 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B7682201 : Blo 710320 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B801103 : Blo 710320 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B4569533 : Blo 710320 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B13876865 : Blo 710320 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B2277001 : Blo 710320 2277001 := bstep (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) B1707751
theorem B4046543 : Blo 710320 4046543 := bstep (se 1 (by rfl) ⟨3034907, by rfl⟩ : syracuseStep 4046543 = 6069815) B6069815
theorem B8765317 : Blo 710320 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B2277335 : Blo 710320 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B2277821 : Blo 710320 2277821 := bstep (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) B854183
theorem B1098281 : Blo 710320 1098281 := bstep (se 2 (by rfl) ⟨411855, by rfl⟩ : syracuseStep 1098281 = 823711) B823711
theorem B1065527 : Blo 710320 1065527 := bstep (se 1 (by rfl) ⟨799145, by rfl⟩ : syracuseStep 1065527 = 1598291) B1598291
theorem B1065935 : Blo 710320 1065935 := bstep (se 1 (by rfl) ⟨799451, by rfl⟩ : syracuseStep 1065935 = 1598903) B1598903
theorem B1066235 : Blo 710320 1066235 := bstep (se 1 (by rfl) ⟨799676, by rfl⟩ : syracuseStep 1066235 = 1599353) B1599353
theorem B2704697 : Blo 710320 2704697 := bstep (se 2 (by rfl) ⟨1014261, by rfl⟩ : syracuseStep 2704697 = 2028523) B2028523
theorem B1066463 : Blo 710320 1066463 := bstep (se 1 (by rfl) ⟨799847, by rfl⟩ : syracuseStep 1066463 = 1599695) B1599695
theorem B1066475 : Blo 710320 1066475 := bstep (se 1 (by rfl) ⟨799856, by rfl⟩ : syracuseStep 1066475 = 1599713) B1599713
theorem B2410559 : Blo 710320 2410559 := bstep (se 1 (by rfl) ⟨1807919, by rfl⟩ : syracuseStep 2410559 = 3615839) B3615839
theorem B1067759 : Blo 710320 1067759 := bstep (se 1 (by rfl) ⟨800819, by rfl⟩ : syracuseStep 1067759 = 1601639) B1601639
theorem B1199387 : Blo 710320 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B40980005 : Blo 710320 40980005 := bstep (se 4 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 40980005 = 7683751) B7683751
theorem B13192955 : Blo 710320 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B1069193 : Blo 710320 1069193 := bstep (se 2 (by rfl) ⟨400947, by rfl⟩ : syracuseStep 1069193 = 801895) B801895
theorem B4575683 : Blo 710320 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B1069787 : Blo 710320 1069787 := bstep (se 1 (by rfl) ⟨802340, by rfl⟩ : syracuseStep 1069787 = 1604681) B1604681
theorem B2052935 : Blo 710320 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1070111 : Blo 710320 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1070183 : Blo 710320 1070183 := bstep (se 1 (by rfl) ⟨802637, by rfl⟩ : syracuseStep 1070183 = 1605275) B1605275
theorem B1070315 : Blo 710320 1070315 := bstep (se 1 (by rfl) ⟨802736, by rfl⟩ : syracuseStep 1070315 = 1605473) B1605473
theorem B2054087 : Blo 710320 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B1071083 : Blo 710320 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B710703 : Blo 710320 710703 := bstep (se 1 (by rfl) ⟨533027, by rfl⟩ : syracuseStep 710703 = 1066055) B1066055
theorem B3430993 : Blo 710320 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B711271 : Blo 710320 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B711847 : Blo 710320 711847 := bstep (se 1 (by rfl) ⟨533885, by rfl⟩ : syracuseStep 711847 = 1067771) B1067771
theorem B712351 : Blo 710320 712351 := bstep (se 1 (by rfl) ⟨534263, by rfl⟩ : syracuseStep 712351 = 1068527) B1068527
theorem B77815511 : Blo 710320 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B1203977 : Blo 710320 1203977 := bstep (se 2 (by rfl) ⟨451491, by rfl⟩ : syracuseStep 1203977 = 902983) B902983
theorem B712731 : Blo 710320 712731 := bstep (se 1 (by rfl) ⟨534548, by rfl⟩ : syracuseStep 712731 = 1069097) B1069097
theorem B712987 : Blo 710320 712987 := bstep (se 1 (by rfl) ⟨534740, by rfl⟩ : syracuseStep 712987 = 1069481) B1069481
theorem B4055609 : Blo 710320 4055609 := bstep (se 2 (by rfl) ⟨1520853, by rfl⟩ : syracuseStep 4055609 = 3041707) B3041707
theorem B713371 : Blo 710320 713371 := bstep (se 1 (by rfl) ⟨535028, by rfl⟩ : syracuseStep 713371 = 1070057) B1070057
theorem B713499 : Blo 710320 713499 := bstep (se 1 (by rfl) ⟨535124, by rfl⟩ : syracuseStep 713499 = 1070249) B1070249
theorem B2286407 : Blo 710320 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B713599 : Blo 710320 713599 := bstep (se 1 (by rfl) ⟨535199, by rfl⟩ : syracuseStep 713599 = 1070399) B1070399
theorem B714287 : Blo 710320 714287 := bstep (se 1 (by rfl) ⟨535715, by rfl⟩ : syracuseStep 714287 = 1071431) B1071431
theorem B1829051 : Blo 710320 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B1141199 : Blo 710320 1141199 := bstep (se 1 (by rfl) ⟨855899, by rfl⟩ : syracuseStep 1141199 = 1711799) B1711799
theorem B1600595 : Blo 710320 1600595 := bstep (se 1 (by rfl) ⟨1200446, by rfl⟩ : syracuseStep 1600595 = 2400893) B2400893
theorem B4877927 : Blo 710320 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B1601351 : Blo 710320 1601351 := bstep (se 1 (by rfl) ⟨1201013, by rfl⟩ : syracuseStep 1601351 = 2402027) B2402027
theorem B1602431 : Blo 710320 1602431 := bstep (se 1 (by rfl) ⟨1201823, by rfl⟩ : syracuseStep 1602431 = 2403647) B2403647
theorem B1602503 : Blo 710320 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B1603241 : Blo 710320 1603241 := bstep (se 2 (by rfl) ⟨601215, by rfl⟩ : syracuseStep 1603241 = 1202431) B1202431
theorem B1603439 : Blo 710320 1603439 := bstep (se 1 (by rfl) ⟨1202579, by rfl⟩ : syracuseStep 1603439 = 2405159) B2405159
theorem B15399335 : Blo 710320 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B1604303 : Blo 710320 1604303 := bstep (se 1 (by rfl) ⟨1203227, by rfl⟩ : syracuseStep 1604303 = 2406455) B2406455
theorem B2031131 : Blo 710320 2031131 := bstep (se 1 (by rfl) ⟨1523348, by rfl⟩ : syracuseStep 2031131 = 3046697) B3046697
theorem B12975673 : Blo 710320 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B16482203 : Blo 710320 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B2163343 : Blo 710320 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B1803131 : Blo 710320 1803131 := bstep (se 1 (by rfl) ⟨1352348, by rfl⟩ : syracuseStep 1803131 = 2704697) B2704697
theorem B1607039 : Blo 710320 1607039 := bstep (se 1 (by rfl) ⟨1205279, by rfl⟩ : syracuseStep 1607039 = 2410559) B2410559
theorem B4556513 : Blo 710320 4556513 := bstep (se 2 (by rfl) ⟨1708692, by rfl⟩ : syracuseStep 4556513 = 3417385) B3417385
theorem B23464655 : Blo 710320 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B3050455 : Blo 710320 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B51877007 : Blo 710320 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B1219367 : Blo 710320 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B760799 : Blo 710320 760799 := bstep (se 1 (by rfl) ⟨570599, by rfl⟩ : syracuseStep 760799 = 1141199) B1141199
theorem B3611951 : Blo 710320 3611951 := bstep (se 1 (by rfl) ⟨2708963, by rfl⟩ : syracuseStep 3611951 = 5417927) B5417927
theorem B3251951 : Blo 710320 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B5121467 : Blo 710320 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B10266223 : Blo 710320 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B1354087 : Blo 710320 1354087 := bstep (se 1 (by rfl) ⟨1015565, by rfl⟩ : syracuseStep 1354087 = 2031131) B2031131
theorem B9251243 : Blo 710320 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B2697695 : Blo 710320 2697695 := bstep (se 1 (by rfl) ⟨2023271, by rfl⟩ : syracuseStep 2697695 = 4046543) B4046543
theorem B10988135 : Blo 710320 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B1518223 : Blo 710320 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B732187 : Blo 710320 732187 := bstep (se 1 (by rfl) ⟨549140, by rfl⟩ : syracuseStep 732187 = 1098281) B1098281
theorem B6074189 : Blo 710320 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B2404295 : Blo 710320 2404295 := bstep (se 1 (by rfl) ⟨1803221, by rfl⟩ : syracuseStep 2404295 = 3606443) B3606443
theorem B1355879 : Blo 710320 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B799591 : Blo 710320 799591 := bstep (se 1 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 799591 = 1199387) B1199387
theorem B8795303 : Blo 710320 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B2405753 : Blo 710320 2405753 := bstep (se 2 (by rfl) ⟨902157, by rfl⟩ : syracuseStep 2405753 = 1804315) B1804315
theorem B20821931 : Blo 710320 20821931 := bstep (se 1 (by rfl) ⟨15616448, by rfl⟩ : syracuseStep 20821931 = 31232897) B31232897
theorem B5945467 : Blo 710320 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B1620155 : Blo 710320 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B46840927 : Blo 710320 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B802651 : Blo 710320 802651 := bstep (se 1 (by rfl) ⟨601988, by rfl⟩ : syracuseStep 802651 = 1203977) B1203977
theorem B5423273 : Blo 710320 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B2703739 : Blo 710320 2703739 := bstep (se 1 (by rfl) ⟨2027804, by rfl⟩ : syracuseStep 2703739 = 4055609) B4055609
theorem B1524271 : Blo 710320 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B2409641 : Blo 710320 2409641 := bstep (se 2 (by rfl) ⟨903615, by rfl⟩ : syracuseStep 2409641 = 1807231) B1807231
theorem B2278847 : Blo 710320 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B1067063 : Blo 710320 1067063 := bstep (se 1 (by rfl) ⟨800297, by rfl⟩ : syracuseStep 1067063 = 1600595) B1600595
theorem B1067177 : Blo 710320 1067177 := bstep (se 2 (by rfl) ⟨400191, by rfl⟩ : syracuseStep 1067177 = 800383) B800383
theorem B17549567 : Blo 710320 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B1067567 : Blo 710320 1067567 := bstep (se 1 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 1067567 = 1601351) B1601351
theorem B1068137 : Blo 710320 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B1068287 : Blo 710320 1068287 := bstep (se 1 (by rfl) ⟨801215, by rfl⟩ : syracuseStep 1068287 = 1602431) B1602431
theorem B1068335 : Blo 710320 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B4574657 : Blo 710320 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B1068827 : Blo 710320 1068827 := bstep (se 1 (by rfl) ⟨801620, by rfl⟩ : syracuseStep 1068827 = 1603241) B1603241
theorem B1068959 : Blo 710320 1068959 := bstep (se 1 (by rfl) ⟨801719, by rfl⟩ : syracuseStep 1068959 = 1603439) B1603439
theorem B10276955 : Blo 710320 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B1069535 : Blo 710320 1069535 := bstep (se 1 (by rfl) ⟨802151, by rfl⟩ : syracuseStep 1069535 = 1604303) B1604303
theorem B3036001 : Blo 710320 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B11687089 : Blo 710320 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B710351 : Blo 710320 710351 := bstep (se 1 (by rfl) ⟨532763, by rfl⟩ : syracuseStep 710351 = 1065527) B1065527
theorem B710623 : Blo 710320 710623 := bstep (se 1 (by rfl) ⟨532967, by rfl⟩ : syracuseStep 710623 = 1065935) B1065935
theorem B1071167 : Blo 710320 1071167 := bstep (se 1 (by rfl) ⟨803375, by rfl⟩ : syracuseStep 1071167 = 1606751) B1606751
theorem B710823 : Blo 710320 710823 := bstep (se 1 (by rfl) ⟨533117, by rfl⟩ : syracuseStep 710823 = 1066235) B1066235
theorem B710975 : Blo 710320 710975 := bstep (se 1 (by rfl) ⟨533231, by rfl⟩ : syracuseStep 710975 = 1066463) B1066463
theorem B710983 : Blo 710320 710983 := bstep (se 1 (by rfl) ⟨533237, by rfl⟩ : syracuseStep 710983 = 1066475) B1066475
theorem B711839 : Blo 710320 711839 := bstep (se 1 (by rfl) ⟨533879, by rfl⟩ : syracuseStep 711839 = 1067759) B1067759
theorem B27320003 : Blo 710320 27320003 := bstep (se 1 (by rfl) ⟨20490002, by rfl⟩ : syracuseStep 27320003 = 40980005) B40980005
theorem B712795 : Blo 710320 712795 := bstep (se 1 (by rfl) ⟨534596, by rfl⟩ : syracuseStep 712795 = 1069193) B1069193
theorem B713191 : Blo 710320 713191 := bstep (se 1 (by rfl) ⟨534893, by rfl⟩ : syracuseStep 713191 = 1069787) B1069787
theorem B1368623 : Blo 710320 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B713407 : Blo 710320 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B713455 : Blo 710320 713455 := bstep (se 1 (by rfl) ⟨535091, by rfl⟩ : syracuseStep 713455 = 1070183) B1070183
theorem B713543 : Blo 710320 713543 := bstep (se 1 (by rfl) ⟨535157, by rfl⟩ : syracuseStep 713543 = 1070315) B1070315
theorem B32007419 : Blo 710320 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B1369391 : Blo 710320 1369391 := bstep (se 1 (by rfl) ⟨1027043, by rfl⟩ : syracuseStep 1369391 = 2054087) B2054087
theorem B714055 : Blo 710320 714055 := bstep (se 1 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 714055 = 1071083) B1071083
theorem B1600775 : Blo 710320 1600775 := bstep (se 1 (by rfl) ⟨1200581, by rfl⟩ : syracuseStep 1600775 = 2401163) B2401163
theorem B5468201 : Blo 710320 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B1601855 : Blo 710320 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B1602899 : Blo 710320 1602899 := bstep (se 1 (by rfl) ⟨1202174, by rfl⟩ : syracuseStep 1602899 = 2404349) B2404349
theorem B1603583 : Blo 710320 1603583 := bstep (se 1 (by rfl) ⟨1202687, by rfl⟩ : syracuseStep 1603583 = 2405375) B2405375
theorem B25983179 : Blo 710320 25983179 := bstep (se 1 (by rfl) ⟨19487384, by rfl⟩ : syracuseStep 25983179 = 38974769) B38974769
theorem B3046355 : Blo 710320 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B17300897 : Blo 710320 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B3604985 : Blo 710320 3604985 := bstep (se 2 (by rfl) ⟨1351869, by rfl⟩ : syracuseStep 3604985 = 2703739) B2703739
theorem B2032361 : Blo 710320 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B1606427 : Blo 710320 1606427 := bstep (se 1 (by rfl) ⟨1204820, by rfl⟩ : syracuseStep 1606427 = 2409641) B2409641
theorem B2884457 : Blo 710320 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B11699711 : Blo 710320 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B6851303 : Blo 710320 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B1805449 : Blo 710320 1805449 := bstep (se 2 (by rfl) ⟨677043, by rfl⟩ : syracuseStep 1805449 = 1354087) B1354087
theorem B4067273 : Blo 710320 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B2167967 : Blo 710320 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B21338279 : Blo 710320 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B3414311 : Blo 710320 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B6167495 : Blo 710320 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B3645467 : Blo 710320 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B12199085 : Blo 710320 12199085 := bstep (se 3 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 12199085 = 4574657) B4574657
theorem B3615515 : Blo 710320 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B3615677 : Blo 710320 3615677 := bstep (se 3 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 3615677 = 1355879) B1355879
theorem B1519231 : Blo 710320 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B15643103 : Blo 710320 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B34584671 : Blo 710320 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B2407967 : Blo 710320 2407967 := bstep (se 1 (by rfl) ⟨1805975, by rfl⟩ : syracuseStep 2407967 = 3611951) B3611951
theorem B4048001 : Blo 710320 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B1066121 : Blo 710320 1066121 := bstep (se 2 (by rfl) ⟨399795, by rfl⟩ : syracuseStep 1066121 = 799591) B799591
theorem B15582785 : Blo 710320 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B7325423 : Blo 710320 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B1067183 : Blo 710320 1067183 := bstep (se 1 (by rfl) ⟨800387, by rfl⟩ : syracuseStep 1067183 = 1600775) B1600775
theorem B4049459 : Blo 710320 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B1067903 : Blo 710320 1067903 := bstep (se 1 (by rfl) ⟨800927, by rfl⟩ : syracuseStep 1067903 = 1601855) B1601855
theorem B1068599 : Blo 710320 1068599 := bstep (se 1 (by rfl) ⟨801449, by rfl⟩ : syracuseStep 1068599 = 1602899) B1602899
theorem B13881287 : Blo 710320 13881287 := bstep (se 1 (by rfl) ⟨10410965, by rfl⟩ : syracuseStep 13881287 = 20821931) B20821931
theorem B1069055 : Blo 710320 1069055 := bstep (se 1 (by rfl) ⟨801791, by rfl⟩ : syracuseStep 1069055 = 1603583) B1603583
theorem B17322119 : Blo 710320 17322119 := bstep (se 1 (by rfl) ⟨12991589, by rfl⟩ : syracuseStep 17322119 = 25983179) B25983179
theorem B1070201 : Blo 710320 1070201 := bstep (se 2 (by rfl) ⟨401325, by rfl⟩ : syracuseStep 1070201 = 802651) B802651
theorem B1202087 : Blo 710320 1202087 := bstep (se 1 (by rfl) ⟨901565, by rfl⟩ : syracuseStep 1202087 = 1803131) B1803131
theorem B1071359 : Blo 710320 1071359 := bstep (se 1 (by rfl) ⟨803519, by rfl⟩ : syracuseStep 1071359 = 1607039) B1607039
theorem B3037675 : Blo 710320 3037675 := bstep (se 1 (by rfl) ⟨2278256, by rfl⟩ : syracuseStep 3037675 = 4556513) B4556513
theorem B711375 : Blo 710320 711375 := bstep (se 1 (by rfl) ⟨533531, by rfl⟩ : syracuseStep 711375 = 1067063) B1067063
theorem B711451 : Blo 710320 711451 := bstep (se 1 (by rfl) ⟨533588, by rfl⟩ : syracuseStep 711451 = 1067177) B1067177
theorem B711711 : Blo 710320 711711 := bstep (se 1 (by rfl) ⟨533783, by rfl⟩ : syracuseStep 711711 = 1067567) B1067567
theorem B712091 : Blo 710320 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B13688297 : Blo 710320 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B712191 : Blo 710320 712191 := bstep (se 1 (by rfl) ⟨534143, by rfl⟩ : syracuseStep 712191 = 1068287) B1068287
theorem B712223 : Blo 710320 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B712551 : Blo 710320 712551 := bstep (se 1 (by rfl) ⟨534413, by rfl⟩ : syracuseStep 712551 = 1068827) B1068827
theorem B712639 : Blo 710320 712639 := bstep (se 1 (by rfl) ⟨534479, by rfl⟩ : syracuseStep 712639 = 1068959) B1068959
theorem B713023 : Blo 710320 713023 := bstep (se 1 (by rfl) ⟨534767, by rfl⟩ : syracuseStep 713023 = 1069535) B1069535
theorem B14606837 : Blo 710320 14606837 := bstep (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) B1369391
theorem B2024297 : Blo 710320 2024297 := bstep (se 2 (by rfl) ⟨759111, by rfl⟩ : syracuseStep 2024297 = 1518223) B1518223
theorem B976249 : Blo 710320 976249 := bstep (se 2 (by rfl) ⟨366093, by rfl⟩ : syracuseStep 976249 = 732187) B732187
theorem B714111 : Blo 710320 714111 := bstep (se 1 (by rfl) ⟨535583, by rfl⟩ : syracuseStep 714111 = 1071167) B1071167
theorem B812911 : Blo 710320 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B18213335 : Blo 710320 18213335 := bstep (se 1 (by rfl) ⟨13660001, by rfl⟩ : syracuseStep 18213335 = 27320003) B27320003
theorem B912415 : Blo 710320 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1798463 : Blo 710320 1798463 := bstep (se 1 (by rfl) ⟨1348847, by rfl⟩ : syracuseStep 1798463 = 2697695) B2697695
theorem B2028797 : Blo 710320 2028797 := bstep (se 3 (by rfl) ⟨380399, by rfl⟩ : syracuseStep 2028797 = 760799) B760799
theorem B1602863 : Blo 710320 1602863 := bstep (se 1 (by rfl) ⟨1202147, by rfl⟩ : syracuseStep 1602863 = 2404295) B2404295
theorem B7927289 : Blo 710320 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B5863535 : Blo 710320 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B1603835 : Blo 710320 1603835 := bstep (se 1 (by rfl) ⟨1202876, by rfl⟩ : syracuseStep 1603835 = 2405753) B2405753
theorem B1080103 : Blo 710320 1080103 := bstep (se 1 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 1080103 = 1620155) B1620155
theorem B62454569 : Blo 710320 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B2030903 : Blo 710320 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B11533931 : Blo 710320 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B7799807 : Blo 710320 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B4883615 : Blo 710320 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B41714941 : Blo 710320 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B1083881 : Blo 710320 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B1445311 : Blo 710320 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B1216553 : Blo 710320 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B14225519 : Blo 710320 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B9737891 : Blo 710320 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B1349531 : Blo 710320 1349531 := bstep (se 1 (by rfl) ⟨1012148, by rfl⟩ : syracuseStep 1349531 = 2024297) B2024297
theorem B8132723 : Blo 710320 8132723 := bstep (se 1 (by rfl) ⟨6099542, by rfl⟩ : syracuseStep 8132723 = 12199085) B12199085
theorem B1352531 : Blo 710320 1352531 := bstep (se 1 (by rfl) ⟨1014398, by rfl⟩ : syracuseStep 1352531 = 2028797) B2028797
theorem B3909023 : Blo 710320 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B1353935 : Blo 710320 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B2403323 : Blo 710320 2403323 := bstep (se 1 (by rfl) ⟨1802492, by rfl⟩ : syracuseStep 2403323 = 3604985) B3604985
theorem B1354907 : Blo 710320 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B2698667 : Blo 710320 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B2699639 : Blo 710320 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B4567535 : Blo 710320 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B9254191 : Blo 710320 9254191 := bstep (se 1 (by rfl) ⟨6940643, by rfl⟩ : syracuseStep 9254191 = 13881287) B13881287
theorem B11548079 : Blo 710320 11548079 := bstep (se 1 (by rfl) ⟨8661059, by rfl⟩ : syracuseStep 11548079 = 17322119) B17322119
theorem B801391 : Blo 710320 801391 := bstep (se 1 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 801391 = 1202087) B1202087
theorem B2407265 : Blo 710320 2407265 := bstep (se 2 (by rfl) ⟨902724, by rfl⟩ : syracuseStep 2407265 = 1805449) B1805449
theorem B2276207 : Blo 710320 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B4111663 : Blo 710320 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B9125531 : Blo 710320 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B84557749 : Blo 710320 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B166216373 : Blo 710320 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B12142223 : Blo 710320 12142223 := bstep (se 1 (by rfl) ⟨9106667, by rfl⟩ : syracuseStep 12142223 = 18213335) B18213335
theorem B2410343 : Blo 710320 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B2410451 : Blo 710320 2410451 := bstep (se 1 (by rfl) ⟨1807838, by rfl⟩ : syracuseStep 2410451 = 3615677) B3615677
theorem B166545517 : Blo 710320 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B1198975 : Blo 710320 1198975 := bstep (se 1 (by rfl) ⟨899231, by rfl⟩ : syracuseStep 1198975 = 1798463) B1798463
theorem B4050233 : Blo 710320 4050233 := bstep (se 2 (by rfl) ⟨1518837, by rfl⟩ : syracuseStep 4050233 = 3037675) B3037675
theorem B1068575 : Blo 710320 1068575 := bstep (se 1 (by rfl) ⟨801431, by rfl⟩ : syracuseStep 1068575 = 1602863) B1602863
theorem B23056447 : Blo 710320 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B1069223 : Blo 710320 1069223 := bstep (se 1 (by rfl) ⟨801917, by rfl⟩ : syracuseStep 1069223 = 1603835) B1603835
theorem B7689287 : Blo 710320 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B38884981 : Blo 710320 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B1070951 : Blo 710320 1070951 := bstep (se 1 (by rfl) ⟨803213, by rfl⟩ : syracuseStep 1070951 = 1606427) B1606427
theorem B710747 : Blo 710320 710747 := bstep (se 1 (by rfl) ⟨533060, by rfl⟩ : syracuseStep 710747 = 1066121) B1066121
theorem B711455 : Blo 710320 711455 := bstep (se 1 (by rfl) ⟨533591, by rfl⟩ : syracuseStep 711455 = 1067183) B1067183
theorem B1301665 : Blo 710320 1301665 := bstep (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) B976249
theorem B711935 : Blo 710320 711935 := bstep (se 1 (by rfl) ⟨533951, by rfl⟩ : syracuseStep 711935 = 1067903) B1067903
theorem B7691885 : Blo 710320 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B712399 : Blo 710320 712399 := bstep (se 1 (by rfl) ⟨534299, by rfl⟩ : syracuseStep 712399 = 1068599) B1068599
theorem B2711515 : Blo 710320 2711515 := bstep (se 1 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 2711515 = 4067273) B4067273
theorem B712703 : Blo 710320 712703 := bstep (se 1 (by rfl) ⟨534527, by rfl⟩ : syracuseStep 712703 = 1069055) B1069055
theorem B713467 : Blo 710320 713467 := bstep (se 1 (by rfl) ⟨535100, by rfl⟩ : syracuseStep 713467 = 1070201) B1070201
theorem B714239 : Blo 710320 714239 := bstep (se 1 (by rfl) ⟨535679, by rfl⟩ : syracuseStep 714239 = 1071359) B1071359
theorem B2025641 : Blo 710320 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B1440137 : Blo 710320 1440137 := bstep (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) B1080103
theorem B1605311 : Blo 710320 1605311 := bstep (se 1 (by rfl) ⟨1203983, by rfl⟩ : syracuseStep 1605311 = 2407967) B2407967
theorem B3244141 : Blo 710320 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B8094815 : Blo 710320 8094815 := bstep (se 1 (by rfl) ⟨6071111, by rfl⟩ : syracuseStep 8094815 = 12142223) B12142223
theorem B1606895 : Blo 710320 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B1606967 : Blo 710320 1606967 := bstep (se 1 (by rfl) ⟨1205225, by rfl⟩ : syracuseStep 1606967 = 2410451) B2410451
theorem B6491927 : Blo 710320 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B30741929 : Blo 710320 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B3610493 : Blo 710320 3610493 := bstep (se 3 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 3610493 = 1353935) B1353935
theorem B3840365 : Blo 710320 3840365 := bstep (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) B1440137
theorem B2890349 : Blo 710320 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B1350427 : Blo 710320 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B51846641 : Blo 710320 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B3613085 : Blo 710320 3613085 := bstep (se 3 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 3613085 = 1354907) B1354907
theorem B5482217 : Blo 710320 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B1517471 : Blo 710320 1517471 := bstep (se 1 (by rfl) ⟨1138103, by rfl⟩ : syracuseStep 1517471 = 2276207) B2276207
theorem B3615353 : Blo 710320 3615353 := bstep (se 2 (by rfl) ⟨1355757, by rfl⟩ : syracuseStep 3615353 = 2711515) B2711515
theorem B3255743 : Blo 710320 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B55619921 : Blo 710320 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B2700155 : Blo 710320 2700155 := bstep (se 1 (by rfl) ⟨2025116, by rfl⟩ : syracuseStep 2700155 = 4050233) B4050233
theorem B9483679 : Blo 710320 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B899687 : Blo 710320 899687 := bstep (se 1 (by rfl) ⟨674765, by rfl⟩ : syracuseStep 899687 = 1349531) B1349531
theorem B5421815 : Blo 710320 5421815 := bstep (se 1 (by rfl) ⟨4066361, by rfl⟩ : syracuseStep 5421815 = 8132723) B8132723
theorem B5127923 : Blo 710320 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B901687 : Blo 710320 901687 := bstep (se 1 (by rfl) ⟨676265, by rfl⟩ : syracuseStep 901687 = 1352531) B1352531
theorem B2606015 : Blo 710320 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B12338921 : Blo 710320 12338921 := bstep (se 2 (by rfl) ⟨4627095, by rfl⟩ : syracuseStep 12338921 = 9254191) B9254191
theorem B1068521 : Blo 710320 1068521 := bstep (se 2 (by rfl) ⟨400695, by rfl⟩ : syracuseStep 1068521 = 801391) B801391
theorem B6083687 : Blo 710320 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B1070207 : Blo 710320 1070207 := bstep (se 1 (by rfl) ⟨802655, by rfl⟩ : syracuseStep 1070207 = 1605311) B1605311
theorem B112743665 : Blo 710320 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B110810915 : Blo 710320 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B5199871 : Blo 710320 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B712383 : Blo 710320 712383 := bstep (se 1 (by rfl) ⟨534287, by rfl⟩ : syracuseStep 712383 = 1068575) B1068575
theorem B712815 : Blo 710320 712815 := bstep (se 1 (by rfl) ⟨534611, by rfl⟩ : syracuseStep 712815 = 1069223) B1069223
theorem B222060689 : Blo 710320 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B20504765 : Blo 710320 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B1598633 : Blo 710320 1598633 := bstep (se 2 (by rfl) ⟨599487, by rfl⟩ : syracuseStep 1598633 = 1198975) B1198975
theorem B713967 : Blo 710320 713967 := bstep (se 1 (by rfl) ⟨535475, by rfl⟩ : syracuseStep 713967 = 1070951) B1070951
theorem B1927081 : Blo 710320 1927081 := bstep (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) B1445311
theorem B1602215 : Blo 710320 1602215 := bstep (se 1 (by rfl) ⟨1201661, by rfl⟩ : syracuseStep 1602215 = 2403323) B2403323
theorem B1799111 : Blo 710320 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B1799759 : Blo 710320 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B3045023 : Blo 710320 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B7698719 : Blo 710320 7698719 := bstep (se 1 (by rfl) ⟨5774039, by rfl⟩ : syracuseStep 7698719 = 11548079) B11548079
theorem B1735553 : Blo 710320 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1604843 : Blo 710320 1604843 := bstep (se 1 (by rfl) ⟨1203632, by rfl⟩ : syracuseStep 1604843 = 2407265) B2407265
theorem B4325521 : Blo 710320 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B8225947 : Blo 710320 8225947 := bstep (se 1 (by rfl) ⟨6169460, by rfl⟩ : syracuseStep 8225947 = 12338921) B12338921
theorem B6949373 : Blo 710320 6949373 := bstep (se 3 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 6949373 = 2606015) B2606015
theorem B4327951 : Blo 710320 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B2560243 : Blo 710320 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B13669843 : Blo 710320 13669843 := bstep (se 1 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 13669843 = 20504765) B20504765
theorem B2399165 : Blo 710320 2399165 := bstep (se 3 (by rfl) ⟨449843, by rfl⟩ : syracuseStep 2399165 = 899687) B899687
theorem B2170495 : Blo 710320 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B4628141 : Blo 710320 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B3614543 : Blo 710320 3614543 := bstep (se 1 (by rfl) ⟨2710907, by rfl⟩ : syracuseStep 3614543 = 5421815) B5421815
theorem B3418615 : Blo 710320 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B2569441 : Blo 710320 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B20494619 : Blo 710320 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B73873943 : Blo 710320 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B2406995 : Blo 710320 2406995 := bstep (se 1 (by rfl) ⟨1805246, by rfl⟩ : syracuseStep 2406995 = 3610493) B3610493
theorem B2408723 : Blo 710320 2408723 := bstep (se 1 (by rfl) ⟨1806542, by rfl⟩ : syracuseStep 2408723 = 3613085) B3613085
theorem B1065755 : Blo 710320 1065755 := bstep (se 1 (by rfl) ⟨799316, by rfl⟩ : syracuseStep 1065755 = 1598633) B1598633
theorem B3654811 : Blo 710320 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B2410235 : Blo 710320 2410235 := bstep (se 1 (by rfl) ⟨1807676, by rfl⟩ : syracuseStep 2410235 = 3615353) B3615353
theorem B50579621 : Blo 710320 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B6933161 : Blo 710320 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B37079947 : Blo 710320 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B1068143 : Blo 710320 1068143 := bstep (se 1 (by rfl) ⟨801107, by rfl⟩ : syracuseStep 1068143 = 1602215) B1602215
theorem B1199407 : Blo 710320 1199407 := bstep (se 1 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 1199407 = 1799111) B1799111
theorem B1199839 : Blo 710320 1199839 := bstep (se 1 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 1199839 = 1799759) B1799759
theorem B5132479 : Blo 710320 5132479 := bstep (se 1 (by rfl) ⟨3849359, by rfl⟩ : syracuseStep 5132479 = 7698719) B7698719
theorem B1069895 : Blo 710320 1069895 := bstep (se 1 (by rfl) ⟨802421, by rfl⟩ : syracuseStep 1069895 = 1604843) B1604843
theorem B5396543 : Blo 710320 5396543 := bstep (se 1 (by rfl) ⟨4047407, by rfl⟩ : syracuseStep 5396543 = 8094815) B8094815
theorem B1202249 : Blo 710320 1202249 := bstep (se 2 (by rfl) ⟨450843, by rfl⟩ : syracuseStep 1202249 = 901687) B901687
theorem B1071263 : Blo 710320 1071263 := bstep (se 1 (by rfl) ⟨803447, by rfl⟩ : syracuseStep 1071263 = 1606895) B1606895
theorem B1071311 : Blo 710320 1071311 := bstep (se 1 (by rfl) ⟨803483, by rfl⟩ : syracuseStep 1071311 = 1606967) B1606967
theorem B712347 : Blo 710320 712347 := bstep (se 1 (by rfl) ⟨534260, by rfl⟩ : syracuseStep 712347 = 1068521) B1068521
theorem B4055791 : Blo 710320 4055791 := bstep (se 1 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 4055791 = 6083687) B6083687
theorem B713471 : Blo 710320 713471 := bstep (se 1 (by rfl) ⟨535103, by rfl⟩ : syracuseStep 713471 = 1070207) B1070207
theorem B75162443 : Blo 710320 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B1926899 : Blo 710320 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B34564427 : Blo 710320 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B148040459 : Blo 710320 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B1011647 : Blo 710320 1011647 := bstep (se 1 (by rfl) ⟨758735, by rfl⟩ : syracuseStep 1011647 = 1517471) B1517471
theorem B1800103 : Blo 710320 1800103 := bstep (se 1 (by rfl) ⟨1350077, by rfl⟩ : syracuseStep 1800103 = 2700155) B2700155
theorem B1800569 : Blo 710320 1800569 := bstep (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) B1350427
theorem B2030015 : Blo 710320 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B1605815 : Blo 710320 1605815 := bstep (se 1 (by rfl) ⟨1204361, by rfl⟩ : syracuseStep 1605815 = 2408723) B2408723
theorem B5767361 : Blo 710320 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B5407721 : Blo 710320 5407721 := bstep (se 2 (by rfl) ⟨2027895, by rfl⟩ : syracuseStep 5407721 = 4055791) B4055791
theorem B1606823 : Blo 710320 1606823 := bstep (se 1 (by rfl) ⟨1205117, by rfl⟩ : syracuseStep 1606823 = 2410235) B2410235
theorem B33719747 : Blo 710320 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B4558153 : Blo 710320 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B5770601 : Blo 710320 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B197759717 : Blo 710320 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B3085427 : Blo 710320 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B3413657 : Blo 710320 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B1284599 : Blo 710320 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B23042951 : Blo 710320 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B18488429 : Blo 710320 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B18226457 : Blo 710320 18226457 := bstep (se 2 (by rfl) ⟨6834921, by rfl⟩ : syracuseStep 18226457 = 13669843) B13669843
theorem B2400137 : Blo 710320 2400137 := bstep (se 2 (by rfl) ⟨900051, by rfl⟩ : syracuseStep 2400137 = 1800103) B1800103
theorem B11575973 : Blo 710320 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B1353343 : Blo 710320 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B2697725 : Blo 710320 2697725 := bstep (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) B1011647
theorem B801499 : Blo 710320 801499 := bstep (se 1 (by rfl) ⟨601124, by rfl⟩ : syracuseStep 801499 = 1202249) B1202249
theorem B2409695 : Blo 710320 2409695 := bstep (se 1 (by rfl) ⟨1807271, by rfl⟩ : syracuseStep 2409695 = 3614543) B3614543
theorem B18531661 : Blo 710320 18531661 := bstep (se 3 (by rfl) ⟨3474686, by rfl⟩ : syracuseStep 18531661 = 6949373) B6949373
theorem B3425921 : Blo 710320 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B1200379 : Blo 710320 1200379 := bstep (se 1 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 1200379 = 1800569) B1800569
theorem B710503 : Blo 710320 710503 := bstep (se 1 (by rfl) ⟨532877, by rfl⟩ : syracuseStep 710503 = 1065755) B1065755
theorem B4873081 : Blo 710320 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B10967929 : Blo 710320 10967929 := bstep (se 2 (by rfl) ⟨4112973, by rfl⟩ : syracuseStep 10967929 = 8225947) B8225947
theorem B712095 : Blo 710320 712095 := bstep (se 1 (by rfl) ⟨534071, by rfl⟩ : syracuseStep 712095 = 1068143) B1068143
theorem B713263 : Blo 710320 713263 := bstep (se 1 (by rfl) ⟨534947, by rfl⟩ : syracuseStep 713263 = 1069895) B1069895
theorem B3597695 : Blo 710320 3597695 := bstep (se 1 (by rfl) ⟨2698271, by rfl⟩ : syracuseStep 3597695 = 5396543) B5396543
theorem B714175 : Blo 710320 714175 := bstep (se 1 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 714175 = 1071263) B1071263
theorem B714207 : Blo 710320 714207 := bstep (se 1 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 714207 = 1071311) B1071311
theorem B1599209 : Blo 710320 1599209 := bstep (se 2 (by rfl) ⟨599703, by rfl⟩ : syracuseStep 1599209 = 1199407) B1199407
theorem B1599443 : Blo 710320 1599443 := bstep (se 1 (by rfl) ⟨1199582, by rfl⟩ : syracuseStep 1599443 = 2399165) B2399165
theorem B1599785 : Blo 710320 1599785 := bstep (se 2 (by rfl) ⟨599919, by rfl⟩ : syracuseStep 1599785 = 1199839) B1199839
theorem B6843305 : Blo 710320 6843305 := bstep (se 2 (by rfl) ⟨2566239, by rfl⟩ : syracuseStep 6843305 = 5132479) B5132479
theorem B98693639 : Blo 710320 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B801732725 : Blo 710320 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B13663079 : Blo 710320 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B49249295 : Blo 710320 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B1604663 : Blo 710320 1604663 := bstep (se 1 (by rfl) ⟨1203497, by rfl⟩ : syracuseStep 1604663 = 2406995) B2406995
theorem B3605147 : Blo 710320 3605147 := bstep (se 1 (by rfl) ⟨2703860, by rfl⟩ : syracuseStep 3605147 = 5407721) B5407721
theorem B1606463 : Blo 710320 1606463 := bstep (se 1 (by rfl) ⟨1204847, by rfl⟩ : syracuseStep 1606463 = 2409695) B2409695
theorem B24708881 : Blo 710320 24708881 := bstep (se 2 (by rfl) ⟨9265830, by rfl⟩ : syracuseStep 24708881 = 18531661) B18531661
theorem B1804457 : Blo 710320 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B89919325 : Blo 710320 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B856399 : Blo 710320 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B58495621 : Blo 710320 58495621 := bstep (se 4 (by rfl) ⟨5483964, by rfl⟩ : syracuseStep 58495621 = 10967929) B10967929
theorem B12325619 : Blo 710320 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B2398463 : Blo 710320 2398463 := bstep (se 1 (by rfl) ⟨1798847, by rfl⟩ : syracuseStep 2398463 = 3597695) B3597695
theorem B4562203 : Blo 710320 4562203 := bstep (se 1 (by rfl) ⟨3421652, by rfl⟩ : syracuseStep 4562203 = 6843305) B6843305
theorem B6497441 : Blo 710320 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B534488483 : Blo 710320 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B3844907 : Blo 710320 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B3847067 : Blo 710320 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B131839811 : Blo 710320 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B2275771 : Blo 710320 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B6077537 : Blo 710320 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B7717315 : Blo 710320 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B1066139 : Blo 710320 1066139 := bstep (se 1 (by rfl) ⟨799604, by rfl⟩ : syracuseStep 1066139 = 1599209) B1599209
theorem B1066295 : Blo 710320 1066295 := bstep (se 1 (by rfl) ⟨799721, by rfl⟩ : syracuseStep 1066295 = 1599443) B1599443
theorem B1066523 : Blo 710320 1066523 := bstep (se 1 (by rfl) ⟨799892, by rfl⟩ : syracuseStep 1066523 = 1599785) B1599785
theorem B1068665 : Blo 710320 1068665 := bstep (se 2 (by rfl) ⟨400749, by rfl⟩ : syracuseStep 1068665 = 801499) B801499
theorem B1069775 : Blo 710320 1069775 := bstep (se 1 (by rfl) ⟨802331, by rfl⟩ : syracuseStep 1069775 = 1604663) B1604663
theorem B1070543 : Blo 710320 1070543 := bstep (se 1 (by rfl) ⟨802907, by rfl⟩ : syracuseStep 1070543 = 1605815) B1605815
theorem B1071215 : Blo 710320 1071215 := bstep (se 1 (by rfl) ⟨803411, by rfl⟩ : syracuseStep 1071215 = 1606823) B1606823
theorem B2283947 : Blo 710320 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B2056951 : Blo 710320 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B15361967 : Blo 710320 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B12150971 : Blo 710320 12150971 := bstep (se 1 (by rfl) ⟨9113228, by rfl⟩ : syracuseStep 12150971 = 18226457) B18226457
theorem B1600091 : Blo 710320 1600091 := bstep (se 1 (by rfl) ⟨1200068, by rfl⟩ : syracuseStep 1600091 = 2400137) B2400137
theorem B1600505 : Blo 710320 1600505 := bstep (se 2 (by rfl) ⟨600189, by rfl⟩ : syracuseStep 1600505 = 1200379) B1200379
theorem B1798483 : Blo 710320 1798483 := bstep (se 1 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 1798483 = 2697725) B2697725
theorem B65795759 : Blo 710320 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B9108719 : Blo 710320 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B32832863 : Blo 710320 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B10289753 : Blo 710320 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B32868317 : Blo 710320 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B2397977 : Blo 710320 2397977 := bstep (se 2 (by rfl) ⟨899241, by rfl⟩ : syracuseStep 2397977 = 1798483) B1798483
theorem B4331627 : Blo 710320 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B77994161 : Blo 710320 77994161 := bstep (se 2 (by rfl) ⟨29247810, by rfl⟩ : syracuseStep 77994161 = 58495621) B58495621
theorem B356325655 : Blo 710320 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B8100647 : Blo 710320 8100647 := bstep (se 1 (by rfl) ⟨6075485, by rfl⟩ : syracuseStep 8100647 = 12150971) B12150971
theorem B2563271 : Blo 710320 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B2564711 : Blo 710320 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B87893207 : Blo 710320 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B479569733 : Blo 710320 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B6072479 : Blo 710320 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B2403431 : Blo 710320 2403431 := bstep (se 1 (by rfl) ⟨1802573, by rfl⟩ : syracuseStep 2403431 = 3605147) B3605147
theorem B1522631 : Blo 710320 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B10241311 : Blo 710320 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B1066727 : Blo 710320 1066727 := bstep (se 1 (by rfl) ⟨800045, by rfl⟩ : syracuseStep 1066727 = 1600091) B1600091
theorem B1067003 : Blo 710320 1067003 := bstep (se 1 (by rfl) ⟨800252, by rfl⟩ : syracuseStep 1067003 = 1600505) B1600505
theorem B3034361 : Blo 710320 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B43863839 : Blo 710320 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B6082937 : Blo 710320 6082937 := bstep (se 2 (by rfl) ⟨2281101, by rfl⟩ : syracuseStep 6082937 = 4562203) B4562203
theorem B4051691 : Blo 710320 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B1070975 : Blo 710320 1070975 := bstep (se 1 (by rfl) ⟨803231, by rfl⟩ : syracuseStep 1070975 = 1606463) B1606463
theorem B710759 : Blo 710320 710759 := bstep (se 1 (by rfl) ⟨533069, by rfl⟩ : syracuseStep 710759 = 1066139) B1066139
theorem B710863 : Blo 710320 710863 := bstep (se 1 (by rfl) ⟨533147, by rfl⟩ : syracuseStep 710863 = 1066295) B1066295
theorem B2742601 : Blo 710320 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B711015 : Blo 710320 711015 := bstep (se 1 (by rfl) ⟨533261, by rfl⟩ : syracuseStep 711015 = 1066523) B1066523
theorem B16472587 : Blo 710320 16472587 := bstep (se 1 (by rfl) ⟨12354440, by rfl⟩ : syracuseStep 16472587 = 24708881) B24708881
theorem B1202971 : Blo 710320 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B712443 : Blo 710320 712443 := bstep (se 1 (by rfl) ⟨534332, by rfl⟩ : syracuseStep 712443 = 1068665) B1068665
theorem B713183 : Blo 710320 713183 := bstep (se 1 (by rfl) ⟨534887, by rfl⟩ : syracuseStep 713183 = 1069775) B1069775
theorem B713695 : Blo 710320 713695 := bstep (se 1 (by rfl) ⟨535271, by rfl⟩ : syracuseStep 713695 = 1070543) B1070543
theorem B714143 : Blo 710320 714143 := bstep (se 1 (by rfl) ⟨535607, by rfl⟩ : syracuseStep 714143 = 1071215) B1071215
theorem B1598975 : Blo 710320 1598975 := bstep (se 1 (by rfl) ⟨1199231, by rfl⟩ : syracuseStep 1598975 = 2398463) B2398463
theorem B1141865 : Blo 710320 1141865 := bstep (se 2 (by rfl) ⟨428199, by rfl⟩ : syracuseStep 1141865 = 856399) B856399
theorem B21888575 : Blo 710320 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B2887751 : Blo 710320 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B1708847 : Blo 710320 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B1709807 : Blo 710320 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B58595471 : Blo 710320 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B761243 : Blo 710320 761243 := bstep (se 1 (by rfl) ⟨570932, by rfl⟩ : syracuseStep 761243 = 1141865) B1141865
theorem B21963449 : Blo 710320 21963449 := bstep (se 2 (by rfl) ⟨8236293, by rfl⟩ : syracuseStep 21963449 = 16472587) B16472587
theorem B14592383 : Blo 710320 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B6859835 : Blo 710320 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B29242559 : Blo 710320 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B2701127 : Blo 710320 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B1065983 : Blo 710320 1065983 := bstep (se 1 (by rfl) ⟨799487, by rfl⟩ : syracuseStep 1065983 = 1598975) B1598975
theorem B4048319 : Blo 710320 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B3656801 : Blo 710320 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B711151 : Blo 710320 711151 := bstep (se 1 (by rfl) ⟨533363, by rfl⟩ : syracuseStep 711151 = 1066727) B1066727
theorem B21912211 : Blo 710320 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B711335 : Blo 710320 711335 := bstep (se 1 (by rfl) ⟨533501, by rfl⟩ : syracuseStep 711335 = 1067003) B1067003
theorem B13655081 : Blo 710320 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B2022907 : Blo 710320 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B4055291 : Blo 710320 4055291 := bstep (se 1 (by rfl) ⟨3041468, by rfl⟩ : syracuseStep 4055291 = 6082937) B6082937
theorem B1598651 : Blo 710320 1598651 := bstep (se 1 (by rfl) ⟨1198988, by rfl⟩ : syracuseStep 1598651 = 2397977) B2397977
theorem B713983 : Blo 710320 713983 := bstep (se 1 (by rfl) ⟨535487, by rfl⟩ : syracuseStep 713983 = 1070975) B1070975
theorem B51996107 : Blo 710320 51996107 := bstep (se 1 (by rfl) ⟨38997080, by rfl⟩ : syracuseStep 51996107 = 77994161) B77994161
theorem B5400431 : Blo 710320 5400431 := bstep (se 1 (by rfl) ⟨4050323, by rfl⟩ : syracuseStep 5400431 = 8100647) B8100647
theorem B319713155 : Blo 710320 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B1602287 : Blo 710320 1602287 := bstep (se 1 (by rfl) ⟨1201715, by rfl⟩ : syracuseStep 1602287 = 2403431) B2403431
theorem B475100873 : Blo 710320 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B1603961 : Blo 710320 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B1015087 : Blo 710320 1015087 := bstep (se 1 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 1015087 = 1522631) B1522631
theorem B7700669 : Blo 710320 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B39063647 : Blo 710320 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B4559485 : Blo 710320 4559485 := bstep (se 3 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 4559485 = 1709807) B1709807
theorem B1353449 : Blo 710320 1353449 := bstep (se 2 (by rfl) ⟨507543, by rfl⟩ : syracuseStep 1353449 = 1015087) B1015087
theorem B2697209 : Blo 710320 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B2698879 : Blo 710320 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B2437867 : Blo 710320 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B116865125 : Blo 710320 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B2703527 : Blo 710320 2703527 := bstep (se 1 (by rfl) ⟨2027645, by rfl⟩ : syracuseStep 2703527 = 4055291) B4055291
theorem B1065767 : Blo 710320 1065767 := bstep (se 1 (by rfl) ⟨799325, by rfl⟩ : syracuseStep 1065767 = 1598651) B1598651
theorem B4573223 : Blo 710320 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B213142103 : Blo 710320 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B1068191 : Blo 710320 1068191 := bstep (se 1 (by rfl) ⟨801143, by rfl⟩ : syracuseStep 1068191 = 1602287) B1602287
theorem B1069307 : Blo 710320 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B710655 : Blo 710320 710655 := bstep (se 1 (by rfl) ⟨532991, by rfl⟩ : syracuseStep 710655 = 1065983) B1065983
theorem B1139231 : Blo 710320 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B9103387 : Blo 710320 9103387 := bstep (se 1 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 9103387 = 13655081) B13655081
theorem B14642299 : Blo 710320 14642299 := bstep (se 1 (by rfl) ⟨10981724, by rfl⟩ : syracuseStep 14642299 = 21963449) B21963449
theorem B34664071 : Blo 710320 34664071 := bstep (se 1 (by rfl) ⟨25998053, by rfl⟩ : syracuseStep 34664071 = 51996107) B51996107
theorem B3600287 : Blo 710320 3600287 := bstep (se 1 (by rfl) ⟨2700215, by rfl⟩ : syracuseStep 3600287 = 5400431) B5400431
theorem B9728255 : Blo 710320 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B19495039 : Blo 710320 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B2029981 : Blo 710320 2029981 := bstep (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) B761243
theorem B316733915 : Blo 710320 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B1800751 : Blo 710320 1800751 := bstep (se 1 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 1800751 = 2701127) B2701127
theorem B1802351 : Blo 710320 1802351 := bstep (se 1 (by rfl) ⟨1351763, by rfl⟩ : syracuseStep 1802351 = 2703527) B2703527
theorem B3048815 : Blo 710320 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B3609197 : Blo 710320 3609197 := bstep (se 3 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 3609197 = 1353449) B1353449
theorem B2400191 : Blo 710320 2400191 := bstep (se 1 (by rfl) ⟨1800143, by rfl⟩ : syracuseStep 2400191 = 3600287) B3600287
theorem B25993385 : Blo 710320 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B2401001 : Blo 710320 2401001 := bstep (se 2 (by rfl) ⟨900375, by rfl⟩ : syracuseStep 2401001 = 1800751) B1800751
theorem B142094735 : Blo 710320 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B12137849 : Blo 710320 12137849 := bstep (se 2 (by rfl) ⟨4551693, by rfl⟩ : syracuseStep 12137849 = 9103387) B9103387
theorem B46218761 : Blo 710320 46218761 := bstep (se 2 (by rfl) ⟨17332035, by rfl⟩ : syracuseStep 46218761 = 34664071) B34664071
theorem B6079313 : Blo 710320 6079313 := bstep (se 2 (by rfl) ⟨2279742, by rfl⟩ : syracuseStep 6079313 = 4559485) B4559485
theorem B2706641 : Blo 710320 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B77910083 : Blo 710320 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B5133779 : Blo 710320 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B710511 : Blo 710320 710511 := bstep (se 1 (by rfl) ⟨532883, by rfl⟩ : syracuseStep 710511 = 1065767) B1065767
theorem B3037949 : Blo 710320 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B712127 : Blo 710320 712127 := bstep (se 1 (by rfl) ⟨534095, by rfl⟩ : syracuseStep 712127 = 1068191) B1068191
theorem B26042431 : Blo 710320 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B712871 : Blo 710320 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B13001957 : Blo 710320 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B19523065 : Blo 710320 19523065 := bstep (se 2 (by rfl) ⟨7321149, by rfl⟩ : syracuseStep 19523065 = 14642299) B14642299
theorem B3598505 : Blo 710320 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B1798139 : Blo 710320 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B6485503 : Blo 710320 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B211155943 : Blo 710320 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B2032543 : Blo 710320 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B1804427 : Blo 710320 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B51940055 : Blo 710320 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B2399003 : Blo 710320 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B30812507 : Blo 710320 30812507 := bstep (se 1 (by rfl) ⟨23109380, by rfl⟩ : syracuseStep 30812507 = 46218761) B46218761
theorem B26030753 : Blo 710320 26030753 := bstep (se 2 (by rfl) ⟨9761532, by rfl⟩ : syracuseStep 26030753 = 19523065) B19523065
theorem B2406131 : Blo 710320 2406131 := bstep (se 1 (by rfl) ⟨1804598, by rfl⟩ : syracuseStep 2406131 = 3609197) B3609197
theorem B3422519 : Blo 710320 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B8667971 : Blo 710320 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B1198759 : Blo 710320 1198759 := bstep (se 1 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 1198759 = 1798139) B1798139
theorem B1201567 : Blo 710320 1201567 := bstep (se 1 (by rfl) ⟨901175, by rfl⟩ : syracuseStep 1201567 = 1802351) B1802351
theorem B34723241 : Blo 710320 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B4052875 : Blo 710320 4052875 := bstep (se 1 (by rfl) ⟨3039656, by rfl⟩ : syracuseStep 4052875 = 6079313) B6079313
theorem B2025299 : Blo 710320 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B1600127 : Blo 710320 1600127 := bstep (se 1 (by rfl) ⟨1200095, by rfl⟩ : syracuseStep 1600127 = 2400191) B2400191
theorem B17328923 : Blo 710320 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B1600667 : Blo 710320 1600667 := bstep (se 1 (by rfl) ⟨1200500, by rfl⟩ : syracuseStep 1600667 = 2401001) B2401001
theorem B8647337 : Blo 710320 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B94729823 : Blo 710320 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B8091899 : Blo 710320 8091899 := bstep (se 1 (by rfl) ⟨6068924, by rfl⟩ : syracuseStep 8091899 = 12137849) B12137849
theorem B281541257 : Blo 710320 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B1350199 : Blo 710320 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B63153215 : Blo 710320 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B5778647 : Blo 710320 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B23148827 : Blo 710320 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B1066751 : Blo 710320 1066751 := bstep (se 1 (by rfl) ⟨800063, by rfl⟩ : syracuseStep 1066751 = 1600127) B1600127
theorem B11552615 : Blo 710320 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B1067111 : Blo 710320 1067111 := bstep (se 1 (by rfl) ⟨800333, by rfl⟩ : syracuseStep 1067111 = 1600667) B1600667
theorem B17353835 : Blo 710320 17353835 := bstep (se 1 (by rfl) ⟨13015376, by rfl⟩ : syracuseStep 17353835 = 26030753) B26030753
theorem B5394599 : Blo 710320 5394599 := bstep (se 1 (by rfl) ⟨4045949, by rfl⟩ : syracuseStep 5394599 = 8091899) B8091899
theorem B2281679 : Blo 710320 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B2710057 : Blo 710320 2710057 := bstep (se 2 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 2710057 = 2032543) B2032543
theorem B1202951 : Blo 710320 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B34626703 : Blo 710320 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B1598345 : Blo 710320 1598345 := bstep (se 2 (by rfl) ⟨599379, by rfl⟩ : syracuseStep 1598345 = 1198759) B1198759
theorem B1599335 : Blo 710320 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B20541671 : Blo 710320 20541671 := bstep (se 1 (by rfl) ⟨15406253, by rfl⟩ : syracuseStep 20541671 = 30812507) B30812507
theorem B1602089 : Blo 710320 1602089 := bstep (se 2 (by rfl) ⟨600783, by rfl⟩ : syracuseStep 1602089 = 1201567) B1201567
theorem B5403833 : Blo 710320 5403833 := bstep (se 2 (by rfl) ⟨2026437, by rfl⟩ : syracuseStep 5403833 = 4052875) B4052875
theorem B5764891 : Blo 710320 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B1604087 : Blo 710320 1604087 := bstep (se 1 (by rfl) ⟨1203065, by rfl⟩ : syracuseStep 1604087 = 2406131) B2406131
theorem B187694171 : Blo 710320 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B7701743 : Blo 710320 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B11569223 : Blo 710320 11569223 := bstep (se 1 (by rfl) ⟨8676917, by rfl⟩ : syracuseStep 11569223 = 17353835) B17353835
theorem B3613409 : Blo 710320 3613409 := bstep (se 2 (by rfl) ⟨1355028, by rfl⟩ : syracuseStep 3613409 = 2710057) B2710057
theorem B1521119 : Blo 710320 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B801967 : Blo 710320 801967 := bstep (se 1 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 801967 = 1202951) B1202951
theorem B1065563 : Blo 710320 1065563 := bstep (se 1 (by rfl) ⟨799172, by rfl⟩ : syracuseStep 1065563 = 1598345) B1598345
theorem B1066223 : Blo 710320 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B3852431 : Blo 710320 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B7686521 : Blo 710320 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B1068059 : Blo 710320 1068059 := bstep (se 1 (by rfl) ⟨801044, by rfl⟩ : syracuseStep 1068059 = 1602089) B1602089
theorem B1069391 : Blo 710320 1069391 := bstep (se 1 (by rfl) ⟨802043, by rfl⟩ : syracuseStep 1069391 = 1604087) B1604087
theorem B125129447 : Blo 710320 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B711167 : Blo 710320 711167 := bstep (se 1 (by rfl) ⟨533375, by rfl⟩ : syracuseStep 711167 = 1066751) B1066751
theorem B711407 : Blo 710320 711407 := bstep (se 1 (by rfl) ⟨533555, by rfl⟩ : syracuseStep 711407 = 1067111) B1067111
theorem B3596399 : Blo 710320 3596399 := bstep (se 1 (by rfl) ⟨2697299, by rfl⟩ : syracuseStep 3596399 = 5394599) B5394599
theorem B42102143 : Blo 710320 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B13694447 : Blo 710320 13694447 := bstep (se 1 (by rfl) ⟨10270835, by rfl⟩ : syracuseStep 13694447 = 20541671) B20541671
theorem B1800265 : Blo 710320 1800265 := bstep (se 2 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 1800265 = 1350199) B1350199
theorem B3602555 : Blo 710320 3602555 := bstep (se 1 (by rfl) ⟨2701916, by rfl⟩ : syracuseStep 3602555 = 5403833) B5403833
theorem B15432551 : Blo 710320 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B46168937 : Blo 710320 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B2397599 : Blo 710320 2397599 := bstep (se 1 (by rfl) ⟨1798199, by rfl⟩ : syracuseStep 2397599 = 3596399) B3596399
theorem B2400353 : Blo 710320 2400353 := bstep (se 2 (by rfl) ⟨900132, by rfl⟩ : syracuseStep 2400353 = 1800265) B1800265
theorem B2401703 : Blo 710320 2401703 := bstep (se 1 (by rfl) ⟨1801277, by rfl⟩ : syracuseStep 2401703 = 3602555) B3602555
theorem B30779291 : Blo 710320 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B7712815 : Blo 710320 7712815 := bstep (se 1 (by rfl) ⟨5784611, by rfl⟩ : syracuseStep 7712815 = 11569223) B11569223
theorem B2568287 : Blo 710320 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B5124347 : Blo 710320 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B2408939 : Blo 710320 2408939 := bstep (se 1 (by rfl) ⟨1806704, by rfl⟩ : syracuseStep 2408939 = 3613409) B3613409
theorem B28068095 : Blo 710320 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B9129631 : Blo 710320 9129631 := bstep (se 1 (by rfl) ⟨6847223, by rfl⟩ : syracuseStep 9129631 = 13694447) B13694447
theorem B1069289 : Blo 710320 1069289 := bstep (se 2 (by rfl) ⟨400983, by rfl⟩ : syracuseStep 1069289 = 801967) B801967
theorem B710375 : Blo 710320 710375 := bstep (se 1 (by rfl) ⟨532781, by rfl⟩ : syracuseStep 710375 = 1065563) B1065563
theorem B710815 : Blo 710320 710815 := bstep (se 1 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 710815 = 1066223) B1066223
theorem B712039 : Blo 710320 712039 := bstep (se 1 (by rfl) ⟨534029, by rfl⟩ : syracuseStep 712039 = 1068059) B1068059
theorem B712927 : Blo 710320 712927 := bstep (se 1 (by rfl) ⟨534695, by rfl⟩ : syracuseStep 712927 = 1069391) B1069391
theorem B83419631 : Blo 710320 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B20537981 : Blo 710320 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B4056317 : Blo 710320 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B10288367 : Blo 710320 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B1605959 : Blo 710320 1605959 := bstep (se 1 (by rfl) ⟨1204469, by rfl⟩ : syracuseStep 1605959 = 2408939) B2408939
theorem B18712063 : Blo 710320 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B55613087 : Blo 710320 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B20519527 : Blo 710320 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B1712191 : Blo 710320 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B3416231 : Blo 710320 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B6858911 : Blo 710320 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B12172841 : Blo 710320 12172841 := bstep (se 2 (by rfl) ⟨4564815, by rfl⟩ : syracuseStep 12172841 = 9129631) B9129631
theorem B2704211 : Blo 710320 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B712859 : Blo 710320 712859 := bstep (se 1 (by rfl) ⟨534644, by rfl⟩ : syracuseStep 712859 = 1069289) B1069289
theorem B1598399 : Blo 710320 1598399 := bstep (se 1 (by rfl) ⟨1198799, by rfl⟩ : syracuseStep 1598399 = 2397599) B2397599
theorem B10283753 : Blo 710320 10283753 := bstep (se 2 (by rfl) ⟨3856407, by rfl⟩ : syracuseStep 10283753 = 7712815) B7712815
theorem B1600235 : Blo 710320 1600235 := bstep (se 1 (by rfl) ⟨1200176, by rfl⟩ : syracuseStep 1600235 = 2400353) B2400353
theorem B13691987 : Blo 710320 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B1601135 : Blo 710320 1601135 := bstep (se 1 (by rfl) ⟨1200851, by rfl⟩ : syracuseStep 1601135 = 2401703) B2401703
theorem B1802807 : Blo 710320 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B6855835 : Blo 710320 6855835 := bstep (se 1 (by rfl) ⟨5141876, by rfl⟩ : syracuseStep 6855835 = 10283753) B10283753
theorem B24949417 : Blo 710320 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B37075391 : Blo 710320 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B2277487 : Blo 710320 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B1065599 : Blo 710320 1065599 := bstep (se 1 (by rfl) ⟨799199, by rfl⟩ : syracuseStep 1065599 = 1598399) B1598399
theorem B4572607 : Blo 710320 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B1066823 : Blo 710320 1066823 := bstep (se 1 (by rfl) ⟨800117, by rfl⟩ : syracuseStep 1066823 = 1600235) B1600235
theorem B9127991 : Blo 710320 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B1067423 : Blo 710320 1067423 := bstep (se 1 (by rfl) ⟨800567, by rfl⟩ : syracuseStep 1067423 = 1601135) B1601135
theorem B8115227 : Blo 710320 8115227 := bstep (se 1 (by rfl) ⟨6086420, by rfl⟩ : syracuseStep 8115227 = 12172841) B12172841
theorem B2282921 : Blo 710320 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B1070639 : Blo 710320 1070639 := bstep (se 1 (by rfl) ⟨802979, by rfl⟩ : syracuseStep 1070639 = 1605959) B1605959
theorem B27359369 : Blo 710320 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B6096809 : Blo 710320 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B5410151 : Blo 710320 5410151 := bstep (se 1 (by rfl) ⟨4057613, by rfl⟩ : syracuseStep 5410151 = 8115227) B8115227
theorem B33265889 : Blo 710320 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B24716927 : Blo 710320 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B1521947 : Blo 710320 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B18239579 : Blo 710320 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B1201871 : Blo 710320 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B710399 : Blo 710320 710399 := bstep (se 1 (by rfl) ⟨532799, by rfl⟩ : syracuseStep 710399 = 1065599) B1065599
theorem B12146597 : Blo 710320 12146597 := bstep (se 4 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 12146597 = 2277487) B2277487
theorem B711215 : Blo 710320 711215 := bstep (se 1 (by rfl) ⟨533411, by rfl⟩ : syracuseStep 711215 = 1066823) B1066823
theorem B6085327 : Blo 710320 6085327 := bstep (se 1 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 6085327 = 9127991) B9127991
theorem B711615 : Blo 710320 711615 := bstep (se 1 (by rfl) ⟨533711, by rfl⟩ : syracuseStep 711615 = 1067423) B1067423
theorem B713759 : Blo 710320 713759 := bstep (se 1 (by rfl) ⟨535319, by rfl⟩ : syracuseStep 713759 = 1070639) B1070639
theorem B9141113 : Blo 710320 9141113 := bstep (se 2 (by rfl) ⟨3427917, by rfl⟩ : syracuseStep 9141113 = 6855835) B6855835
theorem B4064539 : Blo 710320 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B3606767 : Blo 710320 3606767 := bstep (se 1 (by rfl) ⟨2705075, by rfl⟩ : syracuseStep 3606767 = 5410151) B5410151
theorem B12159719 : Blo 710320 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B8097731 : Blo 710320 8097731 := bstep (se 1 (by rfl) ⟨6073298, by rfl⟩ : syracuseStep 8097731 = 12146597) B12146597
theorem B801247 : Blo 710320 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B65911805 : Blo 710320 65911805 := bstep (se 3 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 65911805 = 24716927) B24716927
theorem B8113769 : Blo 710320 8113769 := bstep (se 2 (by rfl) ⟨3042663, by rfl⟩ : syracuseStep 8113769 = 6085327) B6085327
theorem B22177259 : Blo 710320 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B4058525 : Blo 710320 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B6094075 : Blo 710320 6094075 := bstep (se 1 (by rfl) ⟨4570556, by rfl⟩ : syracuseStep 6094075 = 9141113) B9141113
theorem B5409179 : Blo 710320 5409179 := bstep (se 1 (by rfl) ⟨4056884, by rfl⟩ : syracuseStep 5409179 = 8113769) B8113769
theorem B14784839 : Blo 710320 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B2404511 : Blo 710320 2404511 := bstep (se 1 (by rfl) ⟨1803383, by rfl⟩ : syracuseStep 2404511 = 3606767) B3606767
theorem B5419385 : Blo 710320 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B8106479 : Blo 710320 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B2705683 : Blo 710320 2705683 := bstep (se 1 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 2705683 = 4058525) B4058525
theorem B1068329 : Blo 710320 1068329 := bstep (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) B801247
theorem B5398487 : Blo 710320 5398487 := bstep (se 1 (by rfl) ⟨4048865, by rfl⟩ : syracuseStep 5398487 = 8097731) B8097731
theorem B8125433 : Blo 710320 8125433 := bstep (se 2 (by rfl) ⟨3047037, by rfl⟩ : syracuseStep 8125433 = 6094075) B6094075
theorem B43941203 : Blo 710320 43941203 := bstep (se 1 (by rfl) ⟨32955902, by rfl⟩ : syracuseStep 43941203 = 65911805) B65911805
theorem B3606119 : Blo 710320 3606119 := bstep (se 1 (by rfl) ⟨2704589, by rfl⟩ : syracuseStep 3606119 = 5409179) B5409179
theorem B3607577 : Blo 710320 3607577 := bstep (se 2 (by rfl) ⟨1352841, by rfl⟩ : syracuseStep 3607577 = 2705683) B2705683
theorem B3612923 : Blo 710320 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B5416955 : Blo 710320 5416955 := bstep (se 1 (by rfl) ⟨4062716, by rfl⟩ : syracuseStep 5416955 = 8125433) B8125433
theorem B712219 : Blo 710320 712219 := bstep (se 1 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 712219 = 1068329) B1068329
theorem B9856559 : Blo 710320 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B3598991 : Blo 710320 3598991 := bstep (se 1 (by rfl) ⟨2699243, by rfl⟩ : syracuseStep 3598991 = 5398487) B5398487
theorem B1603007 : Blo 710320 1603007 := bstep (se 1 (by rfl) ⟨1202255, by rfl⟩ : syracuseStep 1603007 = 2404511) B2404511
theorem B5404319 : Blo 710320 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B29294135 : Blo 710320 29294135 := bstep (se 1 (by rfl) ⟨21970601, by rfl⟩ : syracuseStep 29294135 = 43941203) B43941203
theorem B3611303 : Blo 710320 3611303 := bstep (se 1 (by rfl) ⟨2708477, by rfl⟩ : syracuseStep 3611303 = 5416955) B5416955
theorem B2399327 : Blo 710320 2399327 := bstep (se 1 (by rfl) ⟨1799495, by rfl⟩ : syracuseStep 2399327 = 3598991) B3598991
theorem B2404079 : Blo 710320 2404079 := bstep (se 1 (by rfl) ⟨1803059, by rfl⟩ : syracuseStep 2404079 = 3606119) B3606119
theorem B2405051 : Blo 710320 2405051 := bstep (se 1 (by rfl) ⟨1803788, by rfl⟩ : syracuseStep 2405051 = 3607577) B3607577
theorem B2408615 : Blo 710320 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B6571039 : Blo 710320 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B1068671 : Blo 710320 1068671 := bstep (se 1 (by rfl) ⟨801503, by rfl⟩ : syracuseStep 1068671 = 1603007) B1603007
theorem B3602879 : Blo 710320 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B19529423 : Blo 710320 19529423 := bstep (se 1 (by rfl) ⟨14647067, by rfl⟩ : syracuseStep 19529423 = 29294135) B29294135
theorem B1605743 : Blo 710320 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B2401919 : Blo 710320 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B13019615 : Blo 710320 13019615 := bstep (se 1 (by rfl) ⟨9764711, by rfl⟩ : syracuseStep 13019615 = 19529423) B19529423
theorem B8761385 : Blo 710320 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B2407535 : Blo 710320 2407535 := bstep (se 1 (by rfl) ⟨1805651, by rfl⟩ : syracuseStep 2407535 = 3611303) B3611303
theorem B712447 : Blo 710320 712447 := bstep (se 1 (by rfl) ⟨534335, by rfl⟩ : syracuseStep 712447 = 1068671) B1068671
theorem B1599551 : Blo 710320 1599551 := bstep (se 1 (by rfl) ⟨1199663, by rfl⟩ : syracuseStep 1599551 = 2399327) B2399327
theorem B1602719 : Blo 710320 1602719 := bstep (se 1 (by rfl) ⟨1202039, by rfl⟩ : syracuseStep 1602719 = 2404079) B2404079
theorem B1603367 : Blo 710320 1603367 := bstep (se 1 (by rfl) ⟨1202525, by rfl⟩ : syracuseStep 1603367 = 2405051) B2405051
theorem B5840923 : Blo 710320 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B1066367 : Blo 710320 1066367 := bstep (se 1 (by rfl) ⟨799775, by rfl⟩ : syracuseStep 1066367 = 1599551) B1599551
theorem B1068479 : Blo 710320 1068479 := bstep (se 1 (by rfl) ⟨801359, by rfl⟩ : syracuseStep 1068479 = 1602719) B1602719
theorem B1068911 : Blo 710320 1068911 := bstep (se 1 (by rfl) ⟨801683, by rfl⟩ : syracuseStep 1068911 = 1603367) B1603367
theorem B1070495 : Blo 710320 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B1601279 : Blo 710320 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B8679743 : Blo 710320 8679743 := bstep (se 1 (by rfl) ⟨6509807, by rfl⟩ : syracuseStep 8679743 = 13019615) B13019615
theorem B1605023 : Blo 710320 1605023 := bstep (se 1 (by rfl) ⟨1203767, by rfl⟩ : syracuseStep 1605023 = 2407535) B2407535
theorem B1067519 : Blo 710320 1067519 := bstep (se 1 (by rfl) ⟨800639, by rfl⟩ : syracuseStep 1067519 = 1601279) B1601279
theorem B5786495 : Blo 710320 5786495 := bstep (se 1 (by rfl) ⟨4339871, by rfl⟩ : syracuseStep 5786495 = 8679743) B8679743
theorem B1070015 : Blo 710320 1070015 := bstep (se 1 (by rfl) ⟨802511, by rfl⟩ : syracuseStep 1070015 = 1605023) B1605023
theorem B7787897 : Blo 710320 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B710911 : Blo 710320 710911 := bstep (se 1 (by rfl) ⟨533183, by rfl⟩ : syracuseStep 710911 = 1066367) B1066367
theorem B712319 : Blo 710320 712319 := bstep (se 1 (by rfl) ⟨534239, by rfl⟩ : syracuseStep 712319 = 1068479) B1068479
theorem B712607 : Blo 710320 712607 := bstep (se 1 (by rfl) ⟨534455, by rfl⟩ : syracuseStep 712607 = 1068911) B1068911
theorem B713663 : Blo 710320 713663 := bstep (se 1 (by rfl) ⟨535247, by rfl⟩ : syracuseStep 713663 = 1070495) B1070495
theorem B5191931 : Blo 710320 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B711679 : Blo 710320 711679 := bstep (se 1 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 711679 = 1067519) B1067519
theorem B3857663 : Blo 710320 3857663 := bstep (se 1 (by rfl) ⟨2893247, by rfl⟩ : syracuseStep 3857663 = 5786495) B5786495
theorem B713343 : Blo 710320 713343 := bstep (se 1 (by rfl) ⟨535007, by rfl⟩ : syracuseStep 713343 = 1070015) B1070015
theorem B3461287 : Blo 710320 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B10287101 : Blo 710320 10287101 := bstep (se 3 (by rfl) ⟨1928831, by rfl⟩ : syracuseStep 10287101 = 3857663) B3857663
theorem B6858067 : Blo 710320 6858067 := bstep (se 1 (by rfl) ⟨5143550, by rfl⟩ : syracuseStep 6858067 = 10287101) B10287101
theorem B4615049 : Blo 710320 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B9144089 : Blo 710320 9144089 := bstep (se 2 (by rfl) ⟨3429033, by rfl⟩ : syracuseStep 9144089 = 6858067) B6858067
theorem B3076699 : Blo 710320 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B6096059 : Blo 710320 6096059 := bstep (se 1 (by rfl) ⟨4572044, by rfl⟩ : syracuseStep 6096059 = 9144089) B9144089
theorem B4102265 : Blo 710320 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B4064039 : Blo 710320 4064039 := bstep (se 1 (by rfl) ⟨3048029, by rfl⟩ : syracuseStep 4064039 = 6096059) B6096059
theorem B10939373 : Blo 710320 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B7292915 : Blo 710320 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B2709359 : Blo 710320 2709359 := bstep (se 1 (by rfl) ⟨2032019, by rfl⟩ : syracuseStep 2709359 = 4064039) B4064039
theorem B1806239 : Blo 710320 1806239 := bstep (se 1 (by rfl) ⟨1354679, by rfl⟩ : syracuseStep 1806239 = 2709359) B2709359
theorem B4861943 : Blo 710320 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B1204159 : Blo 710320 1204159 := bstep (se 1 (by rfl) ⟨903119, by rfl⟩ : syracuseStep 1204159 = 1806239) B1806239
theorem B3241295 : Blo 710320 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B2160863 : Blo 710320 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B1605545 : Blo 710320 1605545 := bstep (se 2 (by rfl) ⟨602079, by rfl⟩ : syracuseStep 1605545 = 1204159) B1204159
theorem B1070363 : Blo 710320 1070363 := bstep (se 1 (by rfl) ⟨802772, by rfl⟩ : syracuseStep 1070363 = 1605545) B1605545
theorem B1440575 : Blo 710320 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B960383 : Blo 710320 960383 := bstep (se 1 (by rfl) ⟨720287, by rfl⟩ : syracuseStep 960383 = 1440575) B1440575
theorem B713575 : Blo 710320 713575 := bstep (se 1 (by rfl) ⟨535181, by rfl⟩ : syracuseStep 713575 = 1070363) B1070363
theorem B2561021 : Blo 710320 2561021 := bstep (se 3 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 2561021 = 960383) B960383
theorem B1707347 : Blo 710320 1707347 := bstep (se 1 (by rfl) ⟨1280510, by rfl⟩ : syracuseStep 1707347 = 2561021) B2561021
theorem B1138231 : Blo 710320 1138231 := bstep (se 1 (by rfl) ⟨853673, by rfl⟩ : syracuseStep 1138231 = 1707347) B1707347
theorem B6070565 : Blo 710320 6070565 := bstep (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) B1138231
theorem B4047043 : Blo 710320 4047043 := bstep (se 1 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 4047043 = 6070565) B6070565
theorem B5396057 : Blo 710320 5396057 := bstep (se 2 (by rfl) ⟨2023521, by rfl⟩ : syracuseStep 5396057 = 4047043) B4047043
theorem B3597371 : Blo 710320 3597371 := bstep (se 1 (by rfl) ⟨2698028, by rfl⟩ : syracuseStep 3597371 = 5396057) B5396057
theorem B2398247 : Blo 710320 2398247 := bstep (se 1 (by rfl) ⟨1798685, by rfl⟩ : syracuseStep 2398247 = 3597371) B3597371
theorem B1598831 : Blo 710320 1598831 := bstep (se 1 (by rfl) ⟨1199123, by rfl⟩ : syracuseStep 1598831 = 2398247) B2398247
theorem B1065887 : Blo 710320 1065887 := bstep (se 1 (by rfl) ⟨799415, by rfl⟩ : syracuseStep 1065887 = 1598831) B1598831
theorem B710591 : Blo 710320 710591 := bstep (se 1 (by rfl) ⟨532943, by rfl⟩ : syracuseStep 710591 = 1065887) B1065887

theorem C0 (j : ℕ) (h1 : 177580 ≤ j) (h2 : j ≤ 178279) : Blo 710320 (4 * j + 3) := by
  interval_cases j
  · exact B710323
  · exact B710327
  · exact B710331
  · exact B710335
  · exact B710339
  · exact B710343
  · exact B710347
  · exact B710351
  · exact B710355
  · exact B710359
  · exact B710363
  · exact B710367
  · exact B710371
  · exact B710375
  · exact B710379
  · exact B710383
  · exact B710387
  · exact B710391
  · exact B710395
  · exact B710399
  · exact B710403
  · exact B710407
  · exact B710411
  · exact B710415
  · exact B710419
  · exact B710423
  · exact B710427
  · exact B710431
  · exact B710435
  · exact B710439
  · exact B710443
  · exact B710447
  · exact B710451
  · exact B710455
  · exact B710459
  · exact B710463
  · exact B710467
  · exact B710471
  · exact B710475
  · exact B710479
  · exact B710483
  · exact B710487
  · exact B710491
  · exact B710495
  · exact B710499
  · exact B710503
  · exact B710507
  · exact B710511
  · exact B710515
  · exact B710519
  · exact B710523
  · exact B710527
  · exact B710531
  · exact B710535
  · exact B710539
  · exact B710543
  · exact B710547
  · exact B710551
  · exact B710555
  · exact B710559
  · exact B710563
  · exact B710567
  · exact B710571
  · exact B710575
  · exact B710579
  · exact B710583
  · exact B710587
  · exact B710591
  · exact B710595
  · exact B710599
  · exact B710603
  · exact B710607
  · exact B710611
  · exact B710615
  · exact B710619
  · exact B710623
  · exact B710627
  · exact B710631
  · exact B710635
  · exact B710639
  · exact B710643
  · exact B710647
  · exact B710651
  · exact B710655
  · exact B710659
  · exact B710663
  · exact B710667
  · exact B710671
  · exact B710675
  · exact B710679
  · exact B710683
  · exact B710687
  · exact B710691
  · exact B710695
  · exact B710699
  · exact B710703
  · exact B710707
  · exact B710711
  · exact B710715
  · exact B710719
  · exact B710723
  · exact B710727
  · exact B710731
  · exact B710735
  · exact B710739
  · exact B710743
  · exact B710747
  · exact B710751
  · exact B710755
  · exact B710759
  · exact B710763
  · exact B710767
  · exact B710771
  · exact B710775
  · exact B710779
  · exact B710783
  · exact B710787
  · exact B710791
  · exact B710795
  · exact B710799
  · exact B710803
  · exact B710807
  · exact B710811
  · exact B710815
  · exact B710819
  · exact B710823
  · exact B710827
  · exact B710831
  · exact B710835
  · exact B710839
  · exact B710843
  · exact B710847
  · exact B710851
  · exact B710855
  · exact B710859
  · exact B710863
  · exact B710867
  · exact B710871
  · exact B710875
  · exact B710879
  · exact B710883
  · exact B710887
  · exact B710891
  · exact B710895
  · exact B710899
  · exact B710903
  · exact B710907
  · exact B710911
  · exact B710915
  · exact B710919
  · exact B710923
  · exact B710927
  · exact B710931
  · exact B710935
  · exact B710939
  · exact B710943
  · exact B710947
  · exact B710951
  · exact B710955
  · exact B710959
  · exact B710963
  · exact B710967
  · exact B710971
  · exact B710975
  · exact B710979
  · exact B710983
  · exact B710987
  · exact B710991
  · exact B710995
  · exact B710999
  · exact B711003
  · exact B711007
  · exact B711011
  · exact B711015
  · exact B711019
  · exact B711023
  · exact B711027
  · exact B711031
  · exact B711035
  · exact B711039
  · exact B711043
  · exact B711047
  · exact B711051
  · exact B711055
  · exact B711059
  · exact B711063
  · exact B711067
  · exact B711071
  · exact B711075
  · exact B711079
  · exact B711083
  · exact B711087
  · exact B711091
  · exact B711095
  · exact B711099
  · exact B711103
  · exact B711107
  · exact B711111
  · exact B711115
  · exact B711119
  · exact B711123
  · exact B711127
  · exact B711131
  · exact B711135
  · exact B711139
  · exact B711143
  · exact B711147
  · exact B711151
  · exact B711155
  · exact B711159
  · exact B711163
  · exact B711167
  · exact B711171
  · exact B711175
  · exact B711179
  · exact B711183
  · exact B711187
  · exact B711191
  · exact B711195
  · exact B711199
  · exact B711203
  · exact B711207
  · exact B711211
  · exact B711215
  · exact B711219
  · exact B711223
  · exact B711227
  · exact B711231
  · exact B711235
  · exact B711239
  · exact B711243
  · exact B711247
  · exact B711251
  · exact B711255
  · exact B711259
  · exact B711263
  · exact B711267
  · exact B711271
  · exact B711275
  · exact B711279
  · exact B711283
  · exact B711287
  · exact B711291
  · exact B711295
  · exact B711299
  · exact B711303
  · exact B711307
  · exact B711311
  · exact B711315
  · exact B711319
  · exact B711323
  · exact B711327
  · exact B711331
  · exact B711335
  · exact B711339
  · exact B711343
  · exact B711347
  · exact B711351
  · exact B711355
  · exact B711359
  · exact B711363
  · exact B711367
  · exact B711371
  · exact B711375
  · exact B711379
  · exact B711383
  · exact B711387
  · exact B711391
  · exact B711395
  · exact B711399
  · exact B711403
  · exact B711407
  · exact B711411
  · exact B711415
  · exact B711419
  · exact B711423
  · exact B711427
  · exact B711431
  · exact B711435
  · exact B711439
  · exact B711443
  · exact B711447
  · exact B711451
  · exact B711455
  · exact B711459
  · exact B711463
  · exact B711467
  · exact B711471
  · exact B711475
  · exact B711479
  · exact B711483
  · exact B711487
  · exact B711491
  · exact B711495
  · exact B711499
  · exact B711503
  · exact B711507
  · exact B711511
  · exact B711515
  · exact B711519
  · exact B711523
  · exact B711527
  · exact B711531
  · exact B711535
  · exact B711539
  · exact B711543
  · exact B711547
  · exact B711551
  · exact B711555
  · exact B711559
  · exact B711563
  · exact B711567
  · exact B711571
  · exact B711575
  · exact B711579
  · exact B711583
  · exact B711587
  · exact B711591
  · exact B711595
  · exact B711599
  · exact B711603
  · exact B711607
  · exact B711611
  · exact B711615
  · exact B711619
  · exact B711623
  · exact B711627
  · exact B711631
  · exact B711635
  · exact B711639
  · exact B711643
  · exact B711647
  · exact B711651
  · exact B711655
  · exact B711659
  · exact B711663
  · exact B711667
  · exact B711671
  · exact B711675
  · exact B711679
  · exact B711683
  · exact B711687
  · exact B711691
  · exact B711695
  · exact B711699
  · exact B711703
  · exact B711707
  · exact B711711
  · exact B711715
  · exact B711719
  · exact B711723
  · exact B711727
  · exact B711731
  · exact B711735
  · exact B711739
  · exact B711743
  · exact B711747
  · exact B711751
  · exact B711755
  · exact B711759
  · exact B711763
  · exact B711767
  · exact B711771
  · exact B711775
  · exact B711779
  · exact B711783
  · exact B711787
  · exact B711791
  · exact B711795
  · exact B711799
  · exact B711803
  · exact B711807
  · exact B711811
  · exact B711815
  · exact B711819
  · exact B711823
  · exact B711827
  · exact B711831
  · exact B711835
  · exact B711839
  · exact B711843
  · exact B711847
  · exact B711851
  · exact B711855
  · exact B711859
  · exact B711863
  · exact B711867
  · exact B711871
  · exact B711875
  · exact B711879
  · exact B711883
  · exact B711887
  · exact B711891
  · exact B711895
  · exact B711899
  · exact B711903
  · exact B711907
  · exact B711911
  · exact B711915
  · exact B711919
  · exact B711923
  · exact B711927
  · exact B711931
  · exact B711935
  · exact B711939
  · exact B711943
  · exact B711947
  · exact B711951
  · exact B711955
  · exact B711959
  · exact B711963
  · exact B711967
  · exact B711971
  · exact B711975
  · exact B711979
  · exact B711983
  · exact B711987
  · exact B711991
  · exact B711995
  · exact B711999
  · exact B712003
  · exact B712007
  · exact B712011
  · exact B712015
  · exact B712019
  · exact B712023
  · exact B712027
  · exact B712031
  · exact B712035
  · exact B712039
  · exact B712043
  · exact B712047
  · exact B712051
  · exact B712055
  · exact B712059
  · exact B712063
  · exact B712067
  · exact B712071
  · exact B712075
  · exact B712079
  · exact B712083
  · exact B712087
  · exact B712091
  · exact B712095
  · exact B712099
  · exact B712103
  · exact B712107
  · exact B712111
  · exact B712115
  · exact B712119
  · exact B712123
  · exact B712127
  · exact B712131
  · exact B712135
  · exact B712139
  · exact B712143
  · exact B712147
  · exact B712151
  · exact B712155
  · exact B712159
  · exact B712163
  · exact B712167
  · exact B712171
  · exact B712175
  · exact B712179
  · exact B712183
  · exact B712187
  · exact B712191
  · exact B712195
  · exact B712199
  · exact B712203
  · exact B712207
  · exact B712211
  · exact B712215
  · exact B712219
  · exact B712223
  · exact B712227
  · exact B712231
  · exact B712235
  · exact B712239
  · exact B712243
  · exact B712247
  · exact B712251
  · exact B712255
  · exact B712259
  · exact B712263
  · exact B712267
  · exact B712271
  · exact B712275
  · exact B712279
  · exact B712283
  · exact B712287
  · exact B712291
  · exact B712295
  · exact B712299
  · exact B712303
  · exact B712307
  · exact B712311
  · exact B712315
  · exact B712319
  · exact B712323
  · exact B712327
  · exact B712331
  · exact B712335
  · exact B712339
  · exact B712343
  · exact B712347
  · exact B712351
  · exact B712355
  · exact B712359
  · exact B712363
  · exact B712367
  · exact B712371
  · exact B712375
  · exact B712379
  · exact B712383
  · exact B712387
  · exact B712391
  · exact B712395
  · exact B712399
  · exact B712403
  · exact B712407
  · exact B712411
  · exact B712415
  · exact B712419
  · exact B712423
  · exact B712427
  · exact B712431
  · exact B712435
  · exact B712439
  · exact B712443
  · exact B712447
  · exact B712451
  · exact B712455
  · exact B712459
  · exact B712463
  · exact B712467
  · exact B712471
  · exact B712475
  · exact B712479
  · exact B712483
  · exact B712487
  · exact B712491
  · exact B712495
  · exact B712499
  · exact B712503
  · exact B712507
  · exact B712511
  · exact B712515
  · exact B712519
  · exact B712523
  · exact B712527
  · exact B712531
  · exact B712535
  · exact B712539
  · exact B712543
  · exact B712547
  · exact B712551
  · exact B712555
  · exact B712559
  · exact B712563
  · exact B712567
  · exact B712571
  · exact B712575
  · exact B712579
  · exact B712583
  · exact B712587
  · exact B712591
  · exact B712595
  · exact B712599
  · exact B712603
  · exact B712607
  · exact B712611
  · exact B712615
  · exact B712619
  · exact B712623
  · exact B712627
  · exact B712631
  · exact B712635
  · exact B712639
  · exact B712643
  · exact B712647
  · exact B712651
  · exact B712655
  · exact B712659
  · exact B712663
  · exact B712667
  · exact B712671
  · exact B712675
  · exact B712679
  · exact B712683
  · exact B712687
  · exact B712691
  · exact B712695
  · exact B712699
  · exact B712703
  · exact B712707
  · exact B712711
  · exact B712715
  · exact B712719
  · exact B712723
  · exact B712727
  · exact B712731
  · exact B712735
  · exact B712739
  · exact B712743
  · exact B712747
  · exact B712751
  · exact B712755
  · exact B712759
  · exact B712763
  · exact B712767
  · exact B712771
  · exact B712775
  · exact B712779
  · exact B712783
  · exact B712787
  · exact B712791
  · exact B712795
  · exact B712799
  · exact B712803
  · exact B712807
  · exact B712811
  · exact B712815
  · exact B712819
  · exact B712823
  · exact B712827
  · exact B712831
  · exact B712835
  · exact B712839
  · exact B712843
  · exact B712847
  · exact B712851
  · exact B712855
  · exact B712859
  · exact B712863
  · exact B712867
  · exact B712871
  · exact B712875
  · exact B712879
  · exact B712883
  · exact B712887
  · exact B712891
  · exact B712895
  · exact B712899
  · exact B712903
  · exact B712907
  · exact B712911
  · exact B712915
  · exact B712919
  · exact B712923
  · exact B712927
  · exact B712931
  · exact B712935
  · exact B712939
  · exact B712943
  · exact B712947
  · exact B712951
  · exact B712955
  · exact B712959
  · exact B712963
  · exact B712967
  · exact B712971
  · exact B712975
  · exact B712979
  · exact B712983
  · exact B712987
  · exact B712991
  · exact B712995
  · exact B712999
  · exact B713003
  · exact B713007
  · exact B713011
  · exact B713015
  · exact B713019
  · exact B713023
  · exact B713027
  · exact B713031
  · exact B713035
  · exact B713039
  · exact B713043
  · exact B713047
  · exact B713051
  · exact B713055
  · exact B713059
  · exact B713063
  · exact B713067
  · exact B713071
  · exact B713075
  · exact B713079
  · exact B713083
  · exact B713087
  · exact B713091
  · exact B713095
  · exact B713099
  · exact B713103
  · exact B713107
  · exact B713111
  · exact B713115
  · exact B713119

theorem C1 (j : ℕ) (h1 : 178280 ≤ j) (h2 : j ≤ 178579) : Blo 710320 (4 * j + 3) := by
  interval_cases j
  · exact B713123
  · exact B713127
  · exact B713131
  · exact B713135
  · exact B713139
  · exact B713143
  · exact B713147
  · exact B713151
  · exact B713155
  · exact B713159
  · exact B713163
  · exact B713167
  · exact B713171
  · exact B713175
  · exact B713179
  · exact B713183
  · exact B713187
  · exact B713191
  · exact B713195
  · exact B713199
  · exact B713203
  · exact B713207
  · exact B713211
  · exact B713215
  · exact B713219
  · exact B713223
  · exact B713227
  · exact B713231
  · exact B713235
  · exact B713239
  · exact B713243
  · exact B713247
  · exact B713251
  · exact B713255
  · exact B713259
  · exact B713263
  · exact B713267
  · exact B713271
  · exact B713275
  · exact B713279
  · exact B713283
  · exact B713287
  · exact B713291
  · exact B713295
  · exact B713299
  · exact B713303
  · exact B713307
  · exact B713311
  · exact B713315
  · exact B713319
  · exact B713323
  · exact B713327
  · exact B713331
  · exact B713335
  · exact B713339
  · exact B713343
  · exact B713347
  · exact B713351
  · exact B713355
  · exact B713359
  · exact B713363
  · exact B713367
  · exact B713371
  · exact B713375
  · exact B713379
  · exact B713383
  · exact B713387
  · exact B713391
  · exact B713395
  · exact B713399
  · exact B713403
  · exact B713407
  · exact B713411
  · exact B713415
  · exact B713419
  · exact B713423
  · exact B713427
  · exact B713431
  · exact B713435
  · exact B713439
  · exact B713443
  · exact B713447
  · exact B713451
  · exact B713455
  · exact B713459
  · exact B713463
  · exact B713467
  · exact B713471
  · exact B713475
  · exact B713479
  · exact B713483
  · exact B713487
  · exact B713491
  · exact B713495
  · exact B713499
  · exact B713503
  · exact B713507
  · exact B713511
  · exact B713515
  · exact B713519
  · exact B713523
  · exact B713527
  · exact B713531
  · exact B713535
  · exact B713539
  · exact B713543
  · exact B713547
  · exact B713551
  · exact B713555
  · exact B713559
  · exact B713563
  · exact B713567
  · exact B713571
  · exact B713575
  · exact B713579
  · exact B713583
  · exact B713587
  · exact B713591
  · exact B713595
  · exact B713599
  · exact B713603
  · exact B713607
  · exact B713611
  · exact B713615
  · exact B713619
  · exact B713623
  · exact B713627
  · exact B713631
  · exact B713635
  · exact B713639
  · exact B713643
  · exact B713647
  · exact B713651
  · exact B713655
  · exact B713659
  · exact B713663
  · exact B713667
  · exact B713671
  · exact B713675
  · exact B713679
  · exact B713683
  · exact B713687
  · exact B713691
  · exact B713695
  · exact B713699
  · exact B713703
  · exact B713707
  · exact B713711
  · exact B713715
  · exact B713719
  · exact B713723
  · exact B713727
  · exact B713731
  · exact B713735
  · exact B713739
  · exact B713743
  · exact B713747
  · exact B713751
  · exact B713755
  · exact B713759
  · exact B713763
  · exact B713767
  · exact B713771
  · exact B713775
  · exact B713779
  · exact B713783
  · exact B713787
  · exact B713791
  · exact B713795
  · exact B713799
  · exact B713803
  · exact B713807
  · exact B713811
  · exact B713815
  · exact B713819
  · exact B713823
  · exact B713827
  · exact B713831
  · exact B713835
  · exact B713839
  · exact B713843
  · exact B713847
  · exact B713851
  · exact B713855
  · exact B713859
  · exact B713863
  · exact B713867
  · exact B713871
  · exact B713875
  · exact B713879
  · exact B713883
  · exact B713887
  · exact B713891
  · exact B713895
  · exact B713899
  · exact B713903
  · exact B713907
  · exact B713911
  · exact B713915
  · exact B713919
  · exact B713923
  · exact B713927
  · exact B713931
  · exact B713935
  · exact B713939
  · exact B713943
  · exact B713947
  · exact B713951
  · exact B713955
  · exact B713959
  · exact B713963
  · exact B713967
  · exact B713971
  · exact B713975
  · exact B713979
  · exact B713983
  · exact B713987
  · exact B713991
  · exact B713995
  · exact B713999
  · exact B714003
  · exact B714007
  · exact B714011
  · exact B714015
  · exact B714019
  · exact B714023
  · exact B714027
  · exact B714031
  · exact B714035
  · exact B714039
  · exact B714043
  · exact B714047
  · exact B714051
  · exact B714055
  · exact B714059
  · exact B714063
  · exact B714067
  · exact B714071
  · exact B714075
  · exact B714079
  · exact B714083
  · exact B714087
  · exact B714091
  · exact B714095
  · exact B714099
  · exact B714103
  · exact B714107
  · exact B714111
  · exact B714115
  · exact B714119
  · exact B714123
  · exact B714127
  · exact B714131
  · exact B714135
  · exact B714139
  · exact B714143
  · exact B714147
  · exact B714151
  · exact B714155
  · exact B714159
  · exact B714163
  · exact B714167
  · exact B714171
  · exact B714175
  · exact B714179
  · exact B714183
  · exact B714187
  · exact B714191
  · exact B714195
  · exact B714199
  · exact B714203
  · exact B714207
  · exact B714211
  · exact B714215
  · exact B714219
  · exact B714223
  · exact B714227
  · exact B714231
  · exact B714235
  · exact B714239
  · exact B714243
  · exact B714247
  · exact B714251
  · exact B714255
  · exact B714259
  · exact B714263
  · exact B714267
  · exact B714271
  · exact B714275
  · exact B714279
  · exact B714283
  · exact B714287
  · exact B714291
  · exact B714295
  · exact B714299
  · exact B714303
  · exact B714307
  · exact B714311
  · exact B714315
  · exact B714319

theorem solution (m : ℕ) (hlo : 710320 ≤ m) (hhi : m ≤ 714320) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 177580 ≤ j := by omega
    have hj2 : j ≤ 178579 := by omega
    have hb : Blo 710320 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 178280 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
