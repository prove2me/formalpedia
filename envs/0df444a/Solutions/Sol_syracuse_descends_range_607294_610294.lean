-- Prove2me | solution 1 for syracuse_descends_range_607294_610294
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:30.168674+00:00
-- url     : https://prove2.me/submissions/4218e163-b454-4ed6-8164-9a68cd4f7c52

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


theorem B770077 : Blo 607294 770077 := bbase (se 3 (by rfl) ⟨144389, by rfl⟩ : syracuseStep 770077 = 288779) (by norm_num)
theorem B1736741 : Blo 607294 1736741 := bbase (se 4 (by rfl) ⟨162819, by rfl⟩ : syracuseStep 1736741 = 325639) (by norm_num)
theorem B1302581 : Blo 607294 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B1368125 : Blo 607294 1368125 := bbase (se 3 (by rfl) ⟨256523, by rfl⟩ : syracuseStep 1368125 = 513047) (by norm_num)
theorem B3465301 : Blo 607294 3465301 := bbase (se 8 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 3465301 = 40609) (by norm_num)
theorem B1540205 : Blo 607294 1540205 := bbase (se 3 (by rfl) ⟨288788, by rfl⟩ : syracuseStep 1540205 = 577577) (by norm_num)
theorem B1368197 : Blo 607294 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B1237133 : Blo 607294 1237133 := bbase (se 3 (by rfl) ⟨231962, by rfl⟩ : syracuseStep 1237133 = 463925) (by norm_num)
theorem B1646741 : Blo 607294 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B2056373 : Blo 607294 2056373 := bbase (se 5 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 2056373 = 192785) (by norm_num)
theorem B770249 : Blo 607294 770249 := bbase (se 2 (by rfl) ⟨288843, by rfl⟩ : syracuseStep 770249 = 577687) (by norm_num)
theorem B1368269 : Blo 607294 1368269 := bbase (se 3 (by rfl) ⟨256550, by rfl⟩ : syracuseStep 1368269 = 513101) (by norm_num)
theorem B975053 : Blo 607294 975053 := bbase (se 3 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 975053 = 365645) (by norm_num)
theorem B1040629 : Blo 607294 1040629 := bbase (se 5 (by rfl) ⟨48779, by rfl⟩ : syracuseStep 1040629 = 97559) (by norm_num)
theorem B770305 : Blo 607294 770305 := bbase (se 2 (by rfl) ⟨288864, by rfl⟩ : syracuseStep 770305 = 577729) (by norm_num)
theorem B3285269 : Blo 607294 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B1368341 : Blo 607294 1368341 := bbase (se 6 (by rfl) ⟨32070, by rfl⟩ : syracuseStep 1368341 = 64141) (by norm_num)
theorem B1540397 : Blo 607294 1540397 := bbase (se 3 (by rfl) ⟨288824, by rfl⟩ : syracuseStep 1540397 = 577649) (by norm_num)
theorem B1155397 : Blo 607294 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B1040725 : Blo 607294 1040725 := bbase (se 10 (by rfl) ⟨1524, by rfl⟩ : syracuseStep 1040725 = 3049) (by norm_num)
theorem B732769 : Blo 607294 732769 := bbase (se 2 (by rfl) ⟨274788, by rfl⟩ : syracuseStep 732769 = 549577) (by norm_num)
theorem B1368413 : Blo 607294 1368413 := bbase (se 3 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 1368413 = 513155) (by norm_num)
theorem B770401 : Blo 607294 770401 := bbase (se 2 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 770401 = 577801) (by norm_num)
theorem B1368485 : Blo 607294 1368485 := bbase (se 4 (by rfl) ⟨128295, by rfl⟩ : syracuseStep 1368485 = 256591) (by norm_num)
theorem B2310565 : Blo 607294 2310565 := bbase (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) (by norm_num)
theorem B975277 : Blo 607294 975277 := bbase (se 3 (by rfl) ⟨182864, by rfl⟩ : syracuseStep 975277 = 365729) (by norm_num)
theorem B1155541 : Blo 607294 1155541 := bbase (se 7 (by rfl) ⟨13541, by rfl⟩ : syracuseStep 1155541 = 27083) (by norm_num)
theorem B1171925 : Blo 607294 1171925 := bbase (se 7 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 1171925 = 27467) (by norm_num)
theorem B8028629 : Blo 607294 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B3088853 : Blo 607294 3088853 := bbase (se 7 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 3088853 = 72395) (by norm_num)
theorem B1368557 : Blo 607294 1368557 := bbase (se 3 (by rfl) ⟨256604, by rfl⟩ : syracuseStep 1368557 = 513209) (by norm_num)
theorem B729589 : Blo 607294 729589 := bbase (se 5 (by rfl) ⟨34199, by rfl⟩ : syracuseStep 729589 = 68399) (by norm_num)
theorem B770573 : Blo 607294 770573 := bbase (se 3 (by rfl) ⟨144482, by rfl⟩ : syracuseStep 770573 = 288965) (by norm_num)
theorem B7225877 : Blo 607294 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B1368629 : Blo 607294 1368629 := bbase (se 5 (by rfl) ⟨64154, by rfl⟩ : syracuseStep 1368629 = 128309) (by norm_num)
theorem B713281 : Blo 607294 713281 := bbase (se 2 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 713281 = 534961) (by norm_num)
theorem B770629 : Blo 607294 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B2056805 : Blo 607294 2056805 := bbase (se 4 (by rfl) ⟨192825, by rfl⟩ : syracuseStep 2056805 = 385651) (by norm_num)
theorem B1155701 : Blo 607294 1155701 := bbase (se 5 (by rfl) ⟨54173, by rfl⟩ : syracuseStep 1155701 = 108347) (by norm_num)
theorem B1368701 : Blo 607294 1368701 := bbase (se 3 (by rfl) ⟨256631, by rfl⟩ : syracuseStep 1368701 = 513263) (by norm_num)
theorem B1540741 : Blo 607294 1540741 := bbase (se 4 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 1540741 = 288889) (by norm_num)
theorem B11870869 : Blo 607294 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B770725 : Blo 607294 770725 := bbase (se 4 (by rfl) ⟨72255, by rfl⟩ : syracuseStep 770725 = 144511) (by norm_num)
theorem B5415605 : Blo 607294 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B926389 : Blo 607294 926389 := bbase (se 5 (by rfl) ⟨43424, by rfl⟩ : syracuseStep 926389 = 86849) (by norm_num)
theorem B1368773 : Blo 607294 1368773 := bbase (se 4 (by rfl) ⟨128322, by rfl⟩ : syracuseStep 1368773 = 256645) (by norm_num)
theorem B1737413 : Blo 607294 1737413 := bbase (se 4 (by rfl) ⟨162882, by rfl⟩ : syracuseStep 1737413 = 325765) (by norm_num)
theorem B729805 : Blo 607294 729805 := bbase (se 3 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 729805 = 273677) (by norm_num)
theorem B2310869 : Blo 607294 2310869 := bbase (se 7 (by rfl) ⟨27080, by rfl⟩ : syracuseStep 2310869 = 54161) (by norm_num)
theorem B1057517 : Blo 607294 1057517 := bbase (se 3 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 1057517 = 396569) (by norm_num)
theorem B1540853 : Blo 607294 1540853 := bbase (se 5 (by rfl) ⟨72227, by rfl⟩ : syracuseStep 1540853 = 144455) (by norm_num)
theorem B1155845 : Blo 607294 1155845 := bbase (se 4 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 1155845 = 216721) (by norm_num)
theorem B1368845 : Blo 607294 1368845 := bbase (se 3 (by rfl) ⟨256658, by rfl⟩ : syracuseStep 1368845 = 513317) (by norm_num)
theorem B770897 : Blo 607294 770897 := bbase (se 2 (by rfl) ⟨289086, by rfl⟩ : syracuseStep 770897 = 578173) (by norm_num)
theorem B1368917 : Blo 607294 1368917 := bbase (se 9 (by rfl) ⟨4010, by rfl⟩ : syracuseStep 1368917 = 8021) (by norm_num)
theorem B3081077 : Blo 607294 3081077 := bbase (se 5 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 3081077 = 288851) (by norm_num)
theorem B770953 : Blo 607294 770953 := bbase (se 2 (by rfl) ⟨289107, by rfl⟩ : syracuseStep 770953 = 578215) (by norm_num)
theorem B1368989 : Blo 607294 1368989 := bbase (se 3 (by rfl) ⟨256685, by rfl⟩ : syracuseStep 1368989 = 513371) (by norm_num)
theorem B1024933 : Blo 607294 1024933 := bbase (se 4 (by rfl) ⟨96087, by rfl⟩ : syracuseStep 1024933 = 192175) (by norm_num)
theorem B1541045 : Blo 607294 1541045 := bbase (se 5 (by rfl) ⟨72236, by rfl⟩ : syracuseStep 1541045 = 144473) (by norm_num)
theorem B1369061 : Blo 607294 1369061 := bbase (se 4 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 1369061 = 256699) (by norm_num)
theorem B771049 : Blo 607294 771049 := bbase (se 2 (by rfl) ⟨289143, by rfl⟩ : syracuseStep 771049 = 578287) (by norm_num)
theorem B1025021 : Blo 607294 1025021 := bbase (se 3 (by rfl) ⟨192191, by rfl⟩ : syracuseStep 1025021 = 384383) (by norm_num)
theorem B2057237 : Blo 607294 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B1156133 : Blo 607294 1156133 := bbase (se 4 (by rfl) ⟨108387, by rfl⟩ : syracuseStep 1156133 = 216775) (by norm_num)
theorem B1369133 : Blo 607294 1369133 := bbase (se 3 (by rfl) ⟨256712, by rfl⟩ : syracuseStep 1369133 = 513425) (by norm_num)
theorem B1459253 : Blo 607294 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B1369205 : Blo 607294 1369205 := bbase (se 5 (by rfl) ⟨64181, by rfl⟩ : syracuseStep 1369205 = 128363) (by norm_num)
theorem B1737845 : Blo 607294 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B1025149 : Blo 607294 1025149 := bbase (se 3 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 1025149 = 384431) (by norm_num)
theorem B8316053 : Blo 607294 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B771221 : Blo 607294 771221 := bbase (se 6 (by rfl) ⟨18075, by rfl⟩ : syracuseStep 771221 = 36151) (by norm_num)
theorem B1098917 : Blo 607294 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B1369277 : Blo 607294 1369277 := bbase (se 3 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 1369277 = 513479) (by norm_num)
theorem B1156285 : Blo 607294 1156285 := bbase (se 3 (by rfl) ⟨216803, by rfl⟩ : syracuseStep 1156285 = 433607) (by norm_num)
theorem B771277 : Blo 607294 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B1025237 : Blo 607294 1025237 := bbase (se 7 (by rfl) ⟨12014, by rfl⟩ : syracuseStep 1025237 = 24029) (by norm_num)
theorem B1729781 : Blo 607294 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B1369349 : Blo 607294 1369349 := bbase (se 4 (by rfl) ⟨128376, by rfl⟩ : syracuseStep 1369349 = 256753) (by norm_num)
theorem B1541389 : Blo 607294 1541389 := bbase (se 3 (by rfl) ⟨289010, by rfl⟩ : syracuseStep 1541389 = 578021) (by norm_num)
theorem B2606357 : Blo 607294 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B730405 : Blo 607294 730405 := bbase (se 4 (by rfl) ⟨68475, by rfl⟩ : syracuseStep 730405 = 136951) (by norm_num)
theorem B771373 : Blo 607294 771373 := bbase (se 3 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 771373 = 289265) (by norm_num)
theorem B5276981 : Blo 607294 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1369421 : Blo 607294 1369421 := bbase (se 3 (by rfl) ⟨256766, by rfl⟩ : syracuseStep 1369421 = 513533) (by norm_num)
theorem B1025365 : Blo 607294 1025365 := bbase (se 12 (by rfl) ⟨375, by rfl⟩ : syracuseStep 1025365 = 751) (by norm_num)
theorem B615805 : Blo 607294 615805 := bbase (se 3 (by rfl) ⟨115463, by rfl⟩ : syracuseStep 615805 = 230927) (by norm_num)
theorem B1541501 : Blo 607294 1541501 := bbase (se 3 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 1541501 = 578063) (by norm_num)
theorem B2598277 : Blo 607294 2598277 := bbase (se 4 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 2598277 = 487177) (by norm_num)
theorem B2598293 : Blo 607294 2598293 := bbase (se 6 (by rfl) ⟨60897, by rfl⟩ : syracuseStep 2598293 = 121795) (by norm_num)
theorem B1369493 : Blo 607294 1369493 := bbase (se 6 (by rfl) ⟨32097, by rfl⟩ : syracuseStep 1369493 = 64195) (by norm_num)
theorem B1025453 : Blo 607294 1025453 := bbase (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) (by norm_num)
theorem B2057669 : Blo 607294 2057669 := bbase (se 4 (by rfl) ⟨192906, by rfl⟩ : syracuseStep 2057669 = 385813) (by norm_num)
theorem B771545 : Blo 607294 771545 := bbase (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) (by norm_num)
theorem B1369565 : Blo 607294 1369565 := bbase (se 3 (by rfl) ⟨256793, by rfl⟩ : syracuseStep 1369565 = 513587) (by norm_num)
theorem B648685 : Blo 607294 648685 := bbase (se 3 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 648685 = 243257) (by norm_num)
theorem B1156589 : Blo 607294 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B771601 : Blo 607294 771601 := bbase (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) (by norm_num)
theorem B1369637 : Blo 607294 1369637 := bbase (se 4 (by rfl) ⟨128403, by rfl⟩ : syracuseStep 1369637 = 256807) (by norm_num)
theorem B1025581 : Blo 607294 1025581 := bbase (se 3 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 1025581 = 384593) (by norm_num)
theorem B1541693 : Blo 607294 1541693 := bbase (se 3 (by rfl) ⟨289067, by rfl⟩ : syracuseStep 1541693 = 578135) (by norm_num)
theorem B910949 : Blo 607294 910949 := bbase (se 4 (by rfl) ⟨85401, by rfl⟩ : syracuseStep 910949 = 170803) (by norm_num)
theorem B1369709 : Blo 607294 1369709 := bbase (se 3 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 1369709 = 513641) (by norm_num)
theorem B771697 : Blo 607294 771697 := bbase (se 2 (by rfl) ⟨289386, by rfl⟩ : syracuseStep 771697 = 578773) (by norm_num)
theorem B910973 : Blo 607294 910973 := bbase (se 3 (by rfl) ⟨170807, by rfl⟩ : syracuseStep 910973 = 341615) (by norm_num)
theorem B1025669 : Blo 607294 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B910997 : Blo 607294 910997 := bbase (se 6 (by rfl) ⟨21351, by rfl⟩ : syracuseStep 910997 = 42703) (by norm_num)
theorem B820901 : Blo 607294 820901 := bbase (se 4 (by rfl) ⟨76959, by rfl⟩ : syracuseStep 820901 = 153919) (by norm_num)
theorem B911021 : Blo 607294 911021 := bbase (se 3 (by rfl) ⟨170816, by rfl⟩ : syracuseStep 911021 = 341633) (by norm_num)
theorem B1369781 : Blo 607294 1369781 := bbase (se 5 (by rfl) ⟨64208, by rfl⟩ : syracuseStep 1369781 = 128417) (by norm_num)
theorem B911045 : Blo 607294 911045 := bbase (se 4 (by rfl) ⟨85410, by rfl⟩ : syracuseStep 911045 = 170821) (by norm_num)
theorem B911069 : Blo 607294 911069 := bbase (se 3 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 911069 = 341651) (by norm_num)
theorem B2926309 : Blo 607294 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B911093 : Blo 607294 911093 := bbase (se 5 (by rfl) ⟨42707, by rfl⟩ : syracuseStep 911093 = 85415) (by norm_num)
theorem B3892981 : Blo 607294 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B1369853 : Blo 607294 1369853 := bbase (se 3 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 1369853 = 513695) (by norm_num)
theorem B927485 : Blo 607294 927485 := bbase (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) (by norm_num)
theorem B1025797 : Blo 607294 1025797 := bbase (se 4 (by rfl) ⟨96168, by rfl⟩ : syracuseStep 1025797 = 192337) (by norm_num)
theorem B911117 : Blo 607294 911117 := bbase (se 3 (by rfl) ⟨170834, by rfl⟩ : syracuseStep 911117 = 341669) (by norm_num)
theorem B771869 : Blo 607294 771869 := bbase (se 3 (by rfl) ⟨144725, by rfl⟩ : syracuseStep 771869 = 289451) (by norm_num)
theorem B911141 : Blo 607294 911141 := bbase (se 4 (by rfl) ⟨85419, by rfl⟩ : syracuseStep 911141 = 170839) (by norm_num)
theorem B976693 : Blo 607294 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B911165 : Blo 607294 911165 := bbase (se 3 (by rfl) ⟨170843, by rfl⟩ : syracuseStep 911165 = 341687) (by norm_num)
theorem B1369925 : Blo 607294 1369925 := bbase (se 4 (by rfl) ⟨128430, by rfl⟩ : syracuseStep 1369925 = 256861) (by norm_num)
theorem B911189 : Blo 607294 911189 := bbase (se 9 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 911189 = 5339) (by norm_num)
theorem B1025885 : Blo 607294 1025885 := bbase (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) (by norm_num)
theorem B771925 : Blo 607294 771925 := bbase (se 9 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 771925 = 4523) (by norm_num)
theorem B2049893 : Blo 607294 2049893 := bbase (se 4 (by rfl) ⟨192177, by rfl⟩ : syracuseStep 2049893 = 384355) (by norm_num)
theorem B911213 : Blo 607294 911213 := bbase (se 3 (by rfl) ⟨170852, by rfl⟩ : syracuseStep 911213 = 341705) (by norm_num)
theorem B2058101 : Blo 607294 2058101 := bbase (se 5 (by rfl) ⟨96473, by rfl⟩ : syracuseStep 2058101 = 192947) (by norm_num)
theorem B911237 : Blo 607294 911237 := bbase (se 4 (by rfl) ⟨85428, by rfl⟩ : syracuseStep 911237 = 170857) (by norm_num)
theorem B1369997 : Blo 607294 1369997 := bbase (se 3 (by rfl) ⟨256874, by rfl⟩ : syracuseStep 1369997 = 513749) (by norm_num)
theorem B1542037 : Blo 607294 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B911261 : Blo 607294 911261 := bbase (se 3 (by rfl) ⟨170861, by rfl⟩ : syracuseStep 911261 = 341723) (by norm_num)
theorem B911285 : Blo 607294 911285 := bbase (se 5 (by rfl) ⟨42716, by rfl⟩ : syracuseStep 911285 = 85433) (by norm_num)
theorem B772021 : Blo 607294 772021 := bbase (se 5 (by rfl) ⟨36188, by rfl⟩ : syracuseStep 772021 = 72377) (by norm_num)
theorem B911309 : Blo 607294 911309 := bbase (se 3 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 911309 = 341741) (by norm_num)
theorem B1370069 : Blo 607294 1370069 := bbase (se 7 (by rfl) ⟨16055, by rfl⟩ : syracuseStep 1370069 = 32111) (by norm_num)
theorem B1026013 : Blo 607294 1026013 := bbase (se 3 (by rfl) ⟨192377, by rfl⟩ : syracuseStep 1026013 = 384755) (by norm_num)
theorem B911333 : Blo 607294 911333 := bbase (se 4 (by rfl) ⟨85437, by rfl⟩ : syracuseStep 911333 = 170875) (by norm_num)
theorem B5195765 : Blo 607294 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B911357 : Blo 607294 911357 := bbase (se 3 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 911357 = 341759) (by norm_num)
theorem B1542149 : Blo 607294 1542149 := bbase (se 4 (by rfl) ⟨144576, by rfl⟩ : syracuseStep 1542149 = 289153) (by norm_num)
theorem B911381 : Blo 607294 911381 := bbase (se 6 (by rfl) ⟨21360, by rfl⟩ : syracuseStep 911381 = 42721) (by norm_num)
theorem B8775701 : Blo 607294 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B3467285 : Blo 607294 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B657433 : Blo 607294 657433 := bbase (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) (by norm_num)
theorem B1001501 : Blo 607294 1001501 := bbase (se 3 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 1001501 = 375563) (by norm_num)
theorem B1370141 : Blo 607294 1370141 := bbase (se 3 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 1370141 = 513803) (by norm_num)
theorem B1173541 : Blo 607294 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B911405 : Blo 607294 911405 := bbase (se 3 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 911405 = 341777) (by norm_num)
theorem B1026101 : Blo 607294 1026101 := bbase (se 5 (by rfl) ⟨48098, by rfl⟩ : syracuseStep 1026101 = 96197) (by norm_num)
theorem B976949 : Blo 607294 976949 := bbase (se 5 (by rfl) ⟨45794, by rfl⟩ : syracuseStep 976949 = 91589) (by norm_num)
theorem B911429 : Blo 607294 911429 := bbase (se 4 (by rfl) ⟨85446, by rfl⟩ : syracuseStep 911429 = 170893) (by norm_num)
theorem B4384853 : Blo 607294 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B911453 : Blo 607294 911453 := bbase (se 3 (by rfl) ⟨170897, by rfl⟩ : syracuseStep 911453 = 341795) (by norm_num)
theorem B4631093 : Blo 607294 4631093 := bbase (se 5 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 4631093 = 434165) (by norm_num)
theorem B772193 : Blo 607294 772193 := bbase (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) (by norm_num)
theorem B1370213 : Blo 607294 1370213 := bbase (se 4 (by rfl) ⟨128457, by rfl⟩ : syracuseStep 1370213 = 256915) (by norm_num)
theorem B911477 : Blo 607294 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B821381 : Blo 607294 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B3082373 : Blo 607294 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B911501 : Blo 607294 911501 := bbase (se 3 (by rfl) ⟨170906, by rfl⟩ : syracuseStep 911501 = 341813) (by norm_num)
theorem B657553 : Blo 607294 657553 := bbase (se 2 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 657553 = 493165) (by norm_num)
theorem B772249 : Blo 607294 772249 := bbase (se 2 (by rfl) ⟨289593, by rfl⟩ : syracuseStep 772249 = 579187) (by norm_num)
theorem B911525 : Blo 607294 911525 := bbase (se 4 (by rfl) ⟨85455, by rfl⟩ : syracuseStep 911525 = 170911) (by norm_num)
theorem B1370285 : Blo 607294 1370285 := bbase (se 3 (by rfl) ⟨256928, by rfl⟩ : syracuseStep 1370285 = 513857) (by norm_num)
theorem B1026229 : Blo 607294 1026229 := bbase (se 5 (by rfl) ⟨48104, by rfl⟩ : syracuseStep 1026229 = 96209) (by norm_num)
theorem B911549 : Blo 607294 911549 := bbase (se 3 (by rfl) ⟨170915, by rfl⟩ : syracuseStep 911549 = 341831) (by norm_num)
theorem B1542341 : Blo 607294 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B911573 : Blo 607294 911573 := bbase (se 7 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 911573 = 21365) (by norm_num)
theorem B1157341 : Blo 607294 1157341 := bbase (se 3 (by rfl) ⟨217001, by rfl⟩ : syracuseStep 1157341 = 434003) (by norm_num)
theorem B911597 : Blo 607294 911597 := bbase (se 3 (by rfl) ⟨170924, by rfl⟩ : syracuseStep 911597 = 341849) (by norm_num)
theorem B1370357 : Blo 607294 1370357 := bbase (se 5 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 1370357 = 128471) (by norm_num)
theorem B977141 : Blo 607294 977141 := bbase (se 5 (by rfl) ⟨45803, by rfl⟩ : syracuseStep 977141 = 91607) (by norm_num)
theorem B772345 : Blo 607294 772345 := bbase (se 2 (by rfl) ⟨289629, by rfl⟩ : syracuseStep 772345 = 579259) (by norm_num)
theorem B911621 : Blo 607294 911621 := bbase (se 4 (by rfl) ⟨85464, by rfl⟩ : syracuseStep 911621 = 170929) (by norm_num)
theorem B1026317 : Blo 607294 1026317 := bbase (se 3 (by rfl) ⟨192434, by rfl⟩ : syracuseStep 1026317 = 384869) (by norm_num)
theorem B2050325 : Blo 607294 2050325 := bbase (se 6 (by rfl) ⟨48054, by rfl⟩ : syracuseStep 2050325 = 96109) (by norm_num)
theorem B911645 : Blo 607294 911645 := bbase (se 3 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 911645 = 341867) (by norm_num)
theorem B649505 : Blo 607294 649505 := bbase (se 2 (by rfl) ⟨243564, by rfl⟩ : syracuseStep 649505 = 487129) (by norm_num)
theorem B2058533 : Blo 607294 2058533 := bbase (se 4 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 2058533 = 385975) (by norm_num)
theorem B657709 : Blo 607294 657709 := bbase (se 3 (by rfl) ⟨123320, by rfl⟩ : syracuseStep 657709 = 246641) (by norm_num)
theorem B911669 : Blo 607294 911669 := bbase (se 5 (by rfl) ⟨42734, by rfl⟩ : syracuseStep 911669 = 85469) (by norm_num)
theorem B1370429 : Blo 607294 1370429 := bbase (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) (by norm_num)
theorem B911693 : Blo 607294 911693 := bbase (se 3 (by rfl) ⟨170942, by rfl⟩ : syracuseStep 911693 = 341885) (by norm_num)
theorem B911717 : Blo 607294 911717 := bbase (se 4 (by rfl) ⟨85473, by rfl⟩ : syracuseStep 911717 = 170947) (by norm_num)
theorem B1157485 : Blo 607294 1157485 := bbase (se 3 (by rfl) ⟨217028, by rfl⟩ : syracuseStep 1157485 = 434057) (by norm_num)
theorem B4385141 : Blo 607294 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B911741 : Blo 607294 911741 := bbase (se 3 (by rfl) ⟨170951, by rfl⟩ : syracuseStep 911741 = 341903) (by norm_num)
theorem B1386877 : Blo 607294 1386877 := bbase (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) (by norm_num)
theorem B1370501 : Blo 607294 1370501 := bbase (se 4 (by rfl) ⟨128484, by rfl⟩ : syracuseStep 1370501 = 256969) (by norm_num)
theorem B1026445 : Blo 607294 1026445 := bbase (se 3 (by rfl) ⟨192458, by rfl⟩ : syracuseStep 1026445 = 384917) (by norm_num)
theorem B911765 : Blo 607294 911765 := bbase (se 6 (by rfl) ⟨21369, by rfl⟩ : syracuseStep 911765 = 42739) (by norm_num)
theorem B1730965 : Blo 607294 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B2632085 : Blo 607294 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B731549 : Blo 607294 731549 := bbase (se 3 (by rfl) ⟨137165, by rfl⟩ : syracuseStep 731549 = 274331) (by norm_num)
theorem B911789 : Blo 607294 911789 := bbase (se 3 (by rfl) ⟨170960, by rfl⟩ : syracuseStep 911789 = 341921) (by norm_num)
theorem B2574773 : Blo 607294 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B911813 : Blo 607294 911813 := bbase (se 4 (by rfl) ⟨85482, by rfl⟩ : syracuseStep 911813 = 170965) (by norm_num)
theorem B731597 : Blo 607294 731597 := bbase (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) (by norm_num)
theorem B1370573 : Blo 607294 1370573 := bbase (se 3 (by rfl) ⟨256982, by rfl⟩ : syracuseStep 1370573 = 513965) (by norm_num)
theorem B911837 : Blo 607294 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B1026533 : Blo 607294 1026533 := bbase (se 4 (by rfl) ⟨96237, by rfl⟩ : syracuseStep 1026533 = 192475) (by norm_num)
theorem B911861 : Blo 607294 911861 := bbase (se 5 (by rfl) ⟨42743, by rfl⟩ : syracuseStep 911861 = 85487) (by norm_num)
theorem B911885 : Blo 607294 911885 := bbase (se 3 (by rfl) ⟨170978, by rfl⟩ : syracuseStep 911885 = 341957) (by norm_num)
theorem B1157645 : Blo 607294 1157645 := bbase (se 3 (by rfl) ⟨217058, by rfl⟩ : syracuseStep 1157645 = 434117) (by norm_num)
theorem B1370645 : Blo 607294 1370645 := bbase (se 6 (by rfl) ⟨32124, by rfl⟩ : syracuseStep 1370645 = 64249) (by norm_num)
theorem B1542685 : Blo 607294 1542685 := bbase (se 3 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 1542685 = 578507) (by norm_num)
theorem B3074597 : Blo 607294 3074597 := bbase (se 4 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 3074597 = 576487) (by norm_num)
theorem B911909 : Blo 607294 911909 := bbase (se 4 (by rfl) ⟨85491, by rfl⟩ : syracuseStep 911909 = 170983) (by norm_num)
theorem B731693 : Blo 607294 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B617009 : Blo 607294 617009 := bbase (se 2 (by rfl) ⟨231378, by rfl⟩ : syracuseStep 617009 = 462757) (by norm_num)
theorem B1731125 : Blo 607294 1731125 := bbase (se 5 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 1731125 = 162293) (by norm_num)
theorem B911933 : Blo 607294 911933 := bbase (se 3 (by rfl) ⟨170987, by rfl⟩ : syracuseStep 911933 = 341975) (by norm_num)
theorem B911957 : Blo 607294 911957 := bbase (se 8 (by rfl) ⟨5343, by rfl⟩ : syracuseStep 911957 = 10687) (by norm_num)
theorem B1370717 : Blo 607294 1370717 := bbase (se 3 (by rfl) ⟨257009, by rfl⟩ : syracuseStep 1370717 = 514019) (by norm_num)
theorem B1026661 : Blo 607294 1026661 := bbase (se 4 (by rfl) ⟨96249, by rfl⟩ : syracuseStep 1026661 = 192499) (by norm_num)
theorem B911981 : Blo 607294 911981 := bbase (se 3 (by rfl) ⟨170996, by rfl⟩ : syracuseStep 911981 = 341993) (by norm_num)
theorem B739961 : Blo 607294 739961 := bbase (se 2 (by rfl) ⟨277485, by rfl⟩ : syracuseStep 739961 = 554971) (by norm_num)
theorem B912005 : Blo 607294 912005 := bbase (se 4 (by rfl) ⟨85500, by rfl⟩ : syracuseStep 912005 = 171001) (by norm_num)
theorem B1542797 : Blo 607294 1542797 := bbase (se 3 (by rfl) ⟨289274, by rfl⟩ : syracuseStep 1542797 = 578549) (by norm_num)
theorem B912029 : Blo 607294 912029 := bbase (se 3 (by rfl) ⟨171005, by rfl⟩ : syracuseStep 912029 = 342011) (by norm_num)
theorem B1157789 : Blo 607294 1157789 := bbase (se 3 (by rfl) ⟨217085, by rfl⟩ : syracuseStep 1157789 = 434171) (by norm_num)
theorem B1370789 : Blo 607294 1370789 := bbase (se 4 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 1370789 = 257023) (by norm_num)
theorem B912053 : Blo 607294 912053 := bbase (se 5 (by rfl) ⟨42752, by rfl⟩ : syracuseStep 912053 = 85505) (by norm_num)
theorem B1952437 : Blo 607294 1952437 := bbase (se 5 (by rfl) ⟨91520, by rfl⟩ : syracuseStep 1952437 = 183041) (by norm_num)
theorem B1026749 : Blo 607294 1026749 := bbase (se 3 (by rfl) ⟨192515, by rfl⟩ : syracuseStep 1026749 = 385031) (by norm_num)
theorem B2050757 : Blo 607294 2050757 := bbase (se 4 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 2050757 = 384517) (by norm_num)
theorem B912077 : Blo 607294 912077 := bbase (se 3 (by rfl) ⟨171014, by rfl⟩ : syracuseStep 912077 = 342029) (by norm_num)
theorem B731857 : Blo 607294 731857 := bbase (se 2 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 731857 = 548893) (by norm_num)
theorem B2058965 : Blo 607294 2058965 := bbase (se 7 (by rfl) ⟨24128, by rfl⟩ : syracuseStep 2058965 = 48257) (by norm_num)
theorem B649949 : Blo 607294 649949 := bbase (se 3 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 649949 = 243731) (by norm_num)
theorem B912101 : Blo 607294 912101 := bbase (se 4 (by rfl) ⟨85509, by rfl⟩ : syracuseStep 912101 = 171019) (by norm_num)
theorem B1370861 : Blo 607294 1370861 := bbase (se 3 (by rfl) ⟨257036, by rfl⟩ : syracuseStep 1370861 = 514073) (by norm_num)
theorem B912125 : Blo 607294 912125 := bbase (se 3 (by rfl) ⟨171023, by rfl⟩ : syracuseStep 912125 = 342047) (by norm_num)
theorem B912149 : Blo 607294 912149 := bbase (se 6 (by rfl) ⟨21378, by rfl⟩ : syracuseStep 912149 = 42757) (by norm_num)
theorem B2312981 : Blo 607294 2312981 := bbase (se 6 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 2312981 = 108421) (by norm_num)
theorem B1731365 : Blo 607294 1731365 := bbase (se 4 (by rfl) ⟨162315, by rfl⟩ : syracuseStep 1731365 = 324631) (by norm_num)
theorem B912173 : Blo 607294 912173 := bbase (se 3 (by rfl) ⟨171032, by rfl⟩ : syracuseStep 912173 = 342065) (by norm_num)
theorem B1370933 : Blo 607294 1370933 := bbase (se 5 (by rfl) ⟨64262, by rfl⟩ : syracuseStep 1370933 = 128525) (by norm_num)
theorem B1026877 : Blo 607294 1026877 := bbase (se 3 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 1026877 = 385079) (by norm_num)
theorem B912197 : Blo 607294 912197 := bbase (se 4 (by rfl) ⟨85518, by rfl⟩ : syracuseStep 912197 = 171037) (by norm_num)
theorem B772933 : Blo 607294 772933 := bbase (se 4 (by rfl) ⟨72462, by rfl⟩ : syracuseStep 772933 = 144925) (by norm_num)
theorem B1542989 : Blo 607294 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B912221 : Blo 607294 912221 := bbase (se 3 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 912221 = 342083) (by norm_num)
theorem B912245 : Blo 607294 912245 := bbase (se 5 (by rfl) ⟨42761, by rfl⟩ : syracuseStep 912245 = 85523) (by norm_num)
theorem B1371005 : Blo 607294 1371005 := bbase (se 3 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 1371005 = 514127) (by norm_num)
theorem B912269 : Blo 607294 912269 := bbase (se 3 (by rfl) ⟨171050, by rfl⟩ : syracuseStep 912269 = 342101) (by norm_num)
theorem B1297301 : Blo 607294 1297301 := bbase (se 6 (by rfl) ⟨30405, by rfl⟩ : syracuseStep 1297301 = 60811) (by norm_num)
theorem B1026965 : Blo 607294 1026965 := bbase (se 6 (by rfl) ⟨24069, by rfl⟩ : syracuseStep 1026965 = 48139) (by norm_num)
theorem B912293 : Blo 607294 912293 := bbase (se 4 (by rfl) ⟨85527, by rfl⟩ : syracuseStep 912293 = 171055) (by norm_num)
theorem B732073 : Blo 607294 732073 := bbase (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) (by norm_num)
theorem B912317 : Blo 607294 912317 := bbase (se 3 (by rfl) ⟨171059, by rfl⟩ : syracuseStep 912317 = 342119) (by norm_num)
theorem B1158077 : Blo 607294 1158077 := bbase (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) (by norm_num)
theorem B1371077 : Blo 607294 1371077 := bbase (se 4 (by rfl) ⟨128538, by rfl⟩ : syracuseStep 1371077 = 257077) (by norm_num)
theorem B2190293 : Blo 607294 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B912341 : Blo 607294 912341 := bbase (se 7 (by rfl) ⟨10691, by rfl⟩ : syracuseStep 912341 = 21383) (by norm_num)
theorem B4623317 : Blo 607294 4623317 := bbase (se 7 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 4623317 = 108359) (by norm_num)
theorem B650197 : Blo 607294 650197 := bbase (se 7 (by rfl) ⟨7619, by rfl⟩ : syracuseStep 650197 = 15239) (by norm_num)
theorem B1731557 : Blo 607294 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B912365 : Blo 607294 912365 := bbase (se 3 (by rfl) ⟨171068, by rfl⟩ : syracuseStep 912365 = 342137) (by norm_num)
theorem B781309 : Blo 607294 781309 := bbase (se 3 (by rfl) ⟨146495, by rfl⟩ : syracuseStep 781309 = 292991) (by norm_num)
theorem B1461253 : Blo 607294 1461253 := bbase (se 4 (by rfl) ⟨136992, by rfl⟩ : syracuseStep 1461253 = 273985) (by norm_num)
theorem B912389 : Blo 607294 912389 := bbase (se 4 (by rfl) ⟨85536, by rfl⟩ : syracuseStep 912389 = 171073) (by norm_num)
theorem B1371149 : Blo 607294 1371149 := bbase (se 3 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 1371149 = 514181) (by norm_num)
theorem B1027093 : Blo 607294 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B912413 : Blo 607294 912413 := bbase (se 3 (by rfl) ⟨171077, by rfl⟩ : syracuseStep 912413 = 342155) (by norm_num)
theorem B912437 : Blo 607294 912437 := bbase (se 5 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 912437 = 85541) (by norm_num)
theorem B2313269 : Blo 607294 2313269 := bbase (se 5 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 2313269 = 216869) (by norm_num)
theorem B937021 : Blo 607294 937021 := bbase (se 3 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 937021 = 351383) (by norm_num)
theorem B912461 : Blo 607294 912461 := bbase (se 3 (by rfl) ⟨171086, by rfl⟩ : syracuseStep 912461 = 342173) (by norm_num)
theorem B732241 : Blo 607294 732241 := bbase (se 2 (by rfl) ⟨274590, by rfl⟩ : syracuseStep 732241 = 549181) (by norm_num)
theorem B1371221 : Blo 607294 1371221 := bbase (se 8 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 1371221 = 16069) (by norm_num)
theorem B1158229 : Blo 607294 1158229 := bbase (se 8 (by rfl) ⟨6786, by rfl⟩ : syracuseStep 1158229 = 13573) (by norm_num)
theorem B912485 : Blo 607294 912485 := bbase (se 4 (by rfl) ⟨85545, by rfl⟩ : syracuseStep 912485 = 171091) (by norm_num)
theorem B1027181 : Blo 607294 1027181 := bbase (se 3 (by rfl) ⟨192596, by rfl⟩ : syracuseStep 1027181 = 385193) (by norm_num)
theorem B2051189 : Blo 607294 2051189 := bbase (se 5 (by rfl) ⟨96149, by rfl⟩ : syracuseStep 2051189 = 192299) (by norm_num)
theorem B1559669 : Blo 607294 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B912509 : Blo 607294 912509 := bbase (se 3 (by rfl) ⟨171095, by rfl⟩ : syracuseStep 912509 = 342191) (by norm_num)
theorem B1297541 : Blo 607294 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B2059397 : Blo 607294 2059397 := bbase (se 4 (by rfl) ⟨193068, by rfl⟩ : syracuseStep 2059397 = 386137) (by norm_num)
theorem B912533 : Blo 607294 912533 := bbase (se 6 (by rfl) ⟨21387, by rfl⟩ : syracuseStep 912533 = 42775) (by norm_num)
theorem B1371293 : Blo 607294 1371293 := bbase (se 3 (by rfl) ⟨257117, by rfl⟩ : syracuseStep 1371293 = 514235) (by norm_num)
theorem B1543333 : Blo 607294 1543333 := bbase (se 4 (by rfl) ⟨144687, by rfl⟩ : syracuseStep 1543333 = 289375) (by norm_num)
theorem B912557 : Blo 607294 912557 := bbase (se 3 (by rfl) ⟨171104, by rfl⟩ : syracuseStep 912557 = 342209) (by norm_num)
theorem B912581 : Blo 607294 912581 := bbase (se 4 (by rfl) ⟨85554, by rfl⟩ : syracuseStep 912581 = 171109) (by norm_num)
theorem B683221 : Blo 607294 683221 := bbase (se 7 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 683221 = 16013) (by norm_num)
theorem B912605 : Blo 607294 912605 := bbase (se 3 (by rfl) ⟨171113, by rfl⟩ : syracuseStep 912605 = 342227) (by norm_num)
theorem B658661 : Blo 607294 658661 := bbase (se 4 (by rfl) ⟨61749, by rfl⟩ : syracuseStep 658661 = 123499) (by norm_num)
theorem B1371365 : Blo 607294 1371365 := bbase (se 4 (by rfl) ⟨128565, by rfl⟩ : syracuseStep 1371365 = 257131) (by norm_num)
theorem B1027309 : Blo 607294 1027309 := bbase (se 3 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 1027309 = 385241) (by norm_num)
theorem B2632949 : Blo 607294 2632949 := bbase (se 5 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 2632949 = 246839) (by norm_num)
theorem B912629 : Blo 607294 912629 := bbase (se 5 (by rfl) ⟨42779, by rfl⟩ : syracuseStep 912629 = 85559) (by norm_num)
theorem B822517 : Blo 607294 822517 := bbase (se 5 (by rfl) ⟨38555, by rfl⟩ : syracuseStep 822517 = 77111) (by norm_num)
theorem B683257 : Blo 607294 683257 := bbase (se 2 (by rfl) ⟨256221, by rfl⟩ : syracuseStep 683257 = 512443) (by norm_num)
theorem B912653 : Blo 607294 912653 := bbase (se 3 (by rfl) ⟨171122, by rfl⟩ : syracuseStep 912653 = 342245) (by norm_num)
theorem B1543445 : Blo 607294 1543445 := bbase (se 6 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 1543445 = 72349) (by norm_num)
theorem B683293 : Blo 607294 683293 := bbase (se 3 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 683293 = 256235) (by norm_num)
theorem B912677 : Blo 607294 912677 := bbase (se 4 (by rfl) ⟨85563, by rfl⟩ : syracuseStep 912677 = 171127) (by norm_num)
theorem B1371437 : Blo 607294 1371437 := bbase (se 3 (by rfl) ⟨257144, by rfl⟩ : syracuseStep 1371437 = 514289) (by norm_num)
theorem B912701 : Blo 607294 912701 := bbase (se 3 (by rfl) ⟨171131, by rfl⟩ : syracuseStep 912701 = 342263) (by norm_num)
theorem B683329 : Blo 607294 683329 := bbase (se 2 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 683329 = 512497) (by norm_num)
theorem B1027397 : Blo 607294 1027397 := bbase (se 4 (by rfl) ⟨96318, by rfl⟩ : syracuseStep 1027397 = 192637) (by norm_num)
theorem B6663509 : Blo 607294 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B912725 : Blo 607294 912725 := bbase (se 11 (by rfl) ⟨668, by rfl⟩ : syracuseStep 912725 = 1337) (by norm_num)
theorem B683365 : Blo 607294 683365 := bbase (se 4 (by rfl) ⟨64065, by rfl⟩ : syracuseStep 683365 = 128131) (by norm_num)
theorem B1486181 : Blo 607294 1486181 := bbase (se 4 (by rfl) ⟨139329, by rfl⟩ : syracuseStep 1486181 = 278659) (by norm_num)
theorem B912749 : Blo 607294 912749 := bbase (se 3 (by rfl) ⟨171140, by rfl⟩ : syracuseStep 912749 = 342281) (by norm_num)
theorem B4615541 : Blo 607294 4615541 := bbase (se 5 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 4615541 = 432707) (by norm_num)
theorem B1371509 : Blo 607294 1371509 := bbase (se 5 (by rfl) ⟨64289, by rfl⟩ : syracuseStep 1371509 = 128579) (by norm_num)
theorem B912773 : Blo 607294 912773 := bbase (se 4 (by rfl) ⟨85572, by rfl⟩ : syracuseStep 912773 = 171145) (by norm_num)
theorem B650629 : Blo 607294 650629 := bbase (se 4 (by rfl) ⟨60996, by rfl⟩ : syracuseStep 650629 = 121993) (by norm_num)
theorem B683401 : Blo 607294 683401 := bbase (se 2 (by rfl) ⟨256275, by rfl⟩ : syracuseStep 683401 = 512551) (by norm_num)
theorem B3083669 : Blo 607294 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B912797 : Blo 607294 912797 := bbase (se 3 (by rfl) ⟨171149, by rfl⟩ : syracuseStep 912797 = 342299) (by norm_num)
theorem B683437 : Blo 607294 683437 := bbase (se 3 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 683437 = 256289) (by norm_num)
theorem B912821 : Blo 607294 912821 := bbase (se 5 (by rfl) ⟨42788, by rfl⟩ : syracuseStep 912821 = 85577) (by norm_num)
theorem B1371581 : Blo 607294 1371581 := bbase (se 3 (by rfl) ⟨257171, by rfl⟩ : syracuseStep 1371581 = 514343) (by norm_num)
theorem B1027525 : Blo 607294 1027525 := bbase (se 4 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 1027525 = 192661) (by norm_num)
theorem B912845 : Blo 607294 912845 := bbase (se 3 (by rfl) ⟨171158, by rfl⟩ : syracuseStep 912845 = 342317) (by norm_num)
theorem B650701 : Blo 607294 650701 := bbase (se 3 (by rfl) ⟨122006, by rfl⟩ : syracuseStep 650701 = 244013) (by norm_num)
theorem B683473 : Blo 607294 683473 := bbase (se 2 (by rfl) ⟨256302, by rfl⟩ : syracuseStep 683473 = 512605) (by norm_num)
theorem B1543637 : Blo 607294 1543637 := bbase (se 7 (by rfl) ⟨18089, by rfl⟩ : syracuseStep 1543637 = 36179) (by norm_num)
theorem B912869 : Blo 607294 912869 := bbase (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) (by norm_num)
theorem B683509 : Blo 607294 683509 := bbase (se 5 (by rfl) ⟨32039, by rfl⟩ : syracuseStep 683509 = 64079) (by norm_num)
theorem B912893 : Blo 607294 912893 := bbase (se 3 (by rfl) ⟨171167, by rfl⟩ : syracuseStep 912893 = 342335) (by norm_num)
theorem B1371653 : Blo 607294 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B912917 : Blo 607294 912917 := bbase (se 6 (by rfl) ⟨21396, by rfl⟩ : syracuseStep 912917 = 42793) (by norm_num)
theorem B683545 : Blo 607294 683545 := bbase (se 2 (by rfl) ⟨256329, by rfl⟩ : syracuseStep 683545 = 512659) (by norm_num)
theorem B1027613 : Blo 607294 1027613 := bbase (se 3 (by rfl) ⟨192677, by rfl⟩ : syracuseStep 1027613 = 385355) (by norm_num)
theorem B2051621 : Blo 607294 2051621 := bbase (se 4 (by rfl) ⟨192339, by rfl⟩ : syracuseStep 2051621 = 384679) (by norm_num)
theorem B912941 : Blo 607294 912941 := bbase (se 3 (by rfl) ⟨171176, by rfl⟩ : syracuseStep 912941 = 342353) (by norm_num)
theorem B4574773 : Blo 607294 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B683581 : Blo 607294 683581 := bbase (se 3 (by rfl) ⟨128171, by rfl⟩ : syracuseStep 683581 = 256343) (by norm_num)
theorem B912965 : Blo 607294 912965 := bbase (se 4 (by rfl) ⟨85590, by rfl⟩ : syracuseStep 912965 = 171181) (by norm_num)
theorem B1371725 : Blo 607294 1371725 := bbase (se 3 (by rfl) ⟨257198, by rfl⟩ : syracuseStep 1371725 = 514397) (by norm_num)
theorem B912989 : Blo 607294 912989 := bbase (se 3 (by rfl) ⟨171185, by rfl⟩ : syracuseStep 912989 = 342371) (by norm_num)
theorem B683617 : Blo 607294 683617 := bbase (se 2 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 683617 = 512713) (by norm_num)
theorem B2600549 : Blo 607294 2600549 := bbase (se 4 (by rfl) ⟨243801, by rfl⟩ : syracuseStep 2600549 = 487603) (by norm_num)
theorem B913013 : Blo 607294 913013 := bbase (se 5 (by rfl) ⟨42797, by rfl⟩ : syracuseStep 913013 = 85595) (by norm_num)
theorem B1298045 : Blo 607294 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B781949 : Blo 607294 781949 := bbase (se 3 (by rfl) ⟨146615, by rfl⟩ : syracuseStep 781949 = 293231) (by norm_num)
theorem B683653 : Blo 607294 683653 := bbase (se 4 (by rfl) ⟨64092, by rfl⟩ : syracuseStep 683653 = 128185) (by norm_num)
theorem B1298053 : Blo 607294 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B822917 : Blo 607294 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B913037 : Blo 607294 913037 := bbase (se 3 (by rfl) ⟨171194, by rfl⟩ : syracuseStep 913037 = 342389) (by norm_num)
theorem B1371797 : Blo 607294 1371797 := bbase (se 6 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 1371797 = 64303) (by norm_num)
theorem B1068701 : Blo 607294 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B1027741 : Blo 607294 1027741 := bbase (se 3 (by rfl) ⟨192701, by rfl⟩ : syracuseStep 1027741 = 385403) (by norm_num)
theorem B913061 : Blo 607294 913061 := bbase (se 4 (by rfl) ⟨85599, by rfl⟩ : syracuseStep 913061 = 171199) (by norm_num)
theorem B683689 : Blo 607294 683689 := bbase (se 2 (by rfl) ⟨256383, by rfl⟩ : syracuseStep 683689 = 512767) (by norm_num)
theorem B1044149 : Blo 607294 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B913085 : Blo 607294 913085 := bbase (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) (by norm_num)
theorem B683725 : Blo 607294 683725 := bbase (se 3 (by rfl) ⟨128198, by rfl⟩ : syracuseStep 683725 = 256397) (by norm_num)
theorem B913109 : Blo 607294 913109 := bbase (se 7 (by rfl) ⟨10700, by rfl⟩ : syracuseStep 913109 = 21401) (by norm_num)
theorem B1371869 : Blo 607294 1371869 := bbase (se 3 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 1371869 = 514451) (by norm_num)
theorem B913133 : Blo 607294 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B683761 : Blo 607294 683761 := bbase (se 2 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 683761 = 512821) (by norm_num)
theorem B1027829 : Blo 607294 1027829 := bbase (se 5 (by rfl) ⟨48179, by rfl⟩ : syracuseStep 1027829 = 96359) (by norm_num)
theorem B913157 : Blo 607294 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B683797 : Blo 607294 683797 := bbase (se 6 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 683797 = 32053) (by norm_num)
theorem B1568533 : Blo 607294 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B913181 : Blo 607294 913181 := bbase (se 3 (by rfl) ⟨171221, by rfl⟩ : syracuseStep 913181 = 342443) (by norm_num)
theorem B1371941 : Blo 607294 1371941 := bbase (se 4 (by rfl) ⟨128619, by rfl⟩ : syracuseStep 1371941 = 257239) (by norm_num)
theorem B1543981 : Blo 607294 1543981 := bbase (se 3 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 1543981 = 578993) (by norm_num)
theorem B3075893 : Blo 607294 3075893 := bbase (se 5 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 3075893 = 288365) (by norm_num)
theorem B913205 : Blo 607294 913205 := bbase (se 5 (by rfl) ⟨42806, by rfl⟩ : syracuseStep 913205 = 85613) (by norm_num)
theorem B683833 : Blo 607294 683833 := bbase (se 2 (by rfl) ⟨256437, by rfl⟩ : syracuseStep 683833 = 512875) (by norm_num)
theorem B986941 : Blo 607294 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B651073 : Blo 607294 651073 := bbase (se 2 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 651073 = 488305) (by norm_num)
theorem B913229 : Blo 607294 913229 := bbase (se 3 (by rfl) ⟨171230, by rfl⟩ : syracuseStep 913229 = 342461) (by norm_num)
theorem B741209 : Blo 607294 741209 := bbase (se 2 (by rfl) ⟨277953, by rfl⟩ : syracuseStep 741209 = 555907) (by norm_num)
theorem B683869 : Blo 607294 683869 := bbase (se 3 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 683869 = 256451) (by norm_num)
theorem B913253 : Blo 607294 913253 := bbase (se 4 (by rfl) ⟨85617, by rfl⟩ : syracuseStep 913253 = 171235) (by norm_num)
theorem B1372013 : Blo 607294 1372013 := bbase (se 3 (by rfl) ⟨257252, by rfl⟩ : syracuseStep 1372013 = 514505) (by norm_num)
theorem B1027957 : Blo 607294 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B913277 : Blo 607294 913277 := bbase (se 3 (by rfl) ⟨171239, by rfl⟩ : syracuseStep 913277 = 342479) (by norm_num)
theorem B683905 : Blo 607294 683905 := bbase (se 2 (by rfl) ⟨256464, by rfl⟩ : syracuseStep 683905 = 512929) (by norm_num)
theorem B913301 : Blo 607294 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B1544093 : Blo 607294 1544093 := bbase (se 3 (by rfl) ⟨289517, by rfl⟩ : syracuseStep 1544093 = 579035) (by norm_num)
theorem B683941 : Blo 607294 683941 := bbase (se 4 (by rfl) ⟨64119, by rfl⟩ : syracuseStep 683941 = 128239) (by norm_num)
theorem B913325 : Blo 607294 913325 := bbase (se 3 (by rfl) ⟨171248, by rfl⟩ : syracuseStep 913325 = 342497) (by norm_num)
theorem B1372085 : Blo 607294 1372085 := bbase (se 5 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 1372085 = 128633) (by norm_num)
theorem B1732549 : Blo 607294 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B913349 : Blo 607294 913349 := bbase (se 4 (by rfl) ⟨85626, by rfl⟩ : syracuseStep 913349 = 171253) (by norm_num)
theorem B683977 : Blo 607294 683977 := bbase (se 2 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 683977 = 512983) (by norm_num)
theorem B1028045 : Blo 607294 1028045 := bbase (se 3 (by rfl) ⟨192758, by rfl⟩ : syracuseStep 1028045 = 385517) (by norm_num)
theorem B2052053 : Blo 607294 2052053 := bbase (se 7 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 2052053 = 48095) (by norm_num)
theorem B913373 : Blo 607294 913373 := bbase (se 3 (by rfl) ⟨171257, by rfl⟩ : syracuseStep 913373 = 342515) (by norm_num)
theorem B684013 : Blo 607294 684013 := bbase (se 3 (by rfl) ⟨128252, by rfl⟩ : syracuseStep 684013 = 256505) (by norm_num)
theorem B913397 : Blo 607294 913397 := bbase (se 5 (by rfl) ⟨42815, by rfl⟩ : syracuseStep 913397 = 85631) (by norm_num)
theorem B1372157 : Blo 607294 1372157 := bbase (se 3 (by rfl) ⟨257279, by rfl⟩ : syracuseStep 1372157 = 514559) (by norm_num)
theorem B913421 : Blo 607294 913421 := bbase (se 3 (by rfl) ⟨171266, by rfl⟩ : syracuseStep 913421 = 342533) (by norm_num)
theorem B684049 : Blo 607294 684049 := bbase (se 2 (by rfl) ⟨256518, by rfl⟩ : syracuseStep 684049 = 513037) (by norm_num)
theorem B913445 : Blo 607294 913445 := bbase (se 4 (by rfl) ⟨85635, by rfl⟩ : syracuseStep 913445 = 171271) (by norm_num)
theorem B684085 : Blo 607294 684085 := bbase (se 5 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 684085 = 64133) (by norm_num)
theorem B913469 : Blo 607294 913469 := bbase (se 3 (by rfl) ⟨171275, by rfl⟩ : syracuseStep 913469 = 342551) (by norm_num)
theorem B1372229 : Blo 607294 1372229 := bbase (se 4 (by rfl) ⟨128646, by rfl⟩ : syracuseStep 1372229 = 257293) (by norm_num)
theorem B1028173 : Blo 607294 1028173 := bbase (se 3 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 1028173 = 385565) (by norm_num)
theorem B913493 : Blo 607294 913493 := bbase (se 8 (by rfl) ⟨5352, by rfl⟩ : syracuseStep 913493 = 10705) (by norm_num)
theorem B684121 : Blo 607294 684121 := bbase (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) (by norm_num)
theorem B1544285 : Blo 607294 1544285 := bbase (se 3 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 1544285 = 579107) (by norm_num)
theorem B913517 : Blo 607294 913517 := bbase (se 3 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 913517 = 342569) (by norm_num)
theorem B684157 : Blo 607294 684157 := bbase (se 3 (by rfl) ⟨128279, by rfl⟩ : syracuseStep 684157 = 256559) (by norm_num)
theorem B913541 : Blo 607294 913541 := bbase (se 4 (by rfl) ⟨85644, by rfl⟩ : syracuseStep 913541 = 171289) (by norm_num)
theorem B1372301 : Blo 607294 1372301 := bbase (se 3 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 1372301 = 514613) (by norm_num)
theorem B913565 : Blo 607294 913565 := bbase (se 3 (by rfl) ⟨171293, by rfl⟩ : syracuseStep 913565 = 342587) (by norm_num)
theorem B684193 : Blo 607294 684193 := bbase (se 2 (by rfl) ⟨256572, by rfl⟩ : syracuseStep 684193 = 513145) (by norm_num)
theorem B1028261 : Blo 607294 1028261 := bbase (se 4 (by rfl) ⟨96399, by rfl⟩ : syracuseStep 1028261 = 192799) (by norm_num)
theorem B913589 : Blo 607294 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B3469493 : Blo 607294 3469493 := bbase (se 5 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 3469493 = 325265) (by norm_num)
theorem B651449 : Blo 607294 651449 := bbase (se 2 (by rfl) ⟨244293, by rfl⟩ : syracuseStep 651449 = 488587) (by norm_num)
theorem B684229 : Blo 607294 684229 := bbase (se 4 (by rfl) ⟨64146, by rfl⟩ : syracuseStep 684229 = 128293) (by norm_num)
theorem B913613 : Blo 607294 913613 := bbase (se 3 (by rfl) ⟨171302, by rfl⟩ : syracuseStep 913613 = 342605) (by norm_num)
theorem B2314453 : Blo 607294 2314453 := bbase (se 7 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 2314453 = 54245) (by norm_num)
theorem B1372373 : Blo 607294 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B913637 : Blo 607294 913637 := bbase (se 4 (by rfl) ⟨85653, by rfl⟩ : syracuseStep 913637 = 171307) (by norm_num)
theorem B684265 : Blo 607294 684265 := bbase (se 2 (by rfl) ⟨256599, by rfl⟩ : syracuseStep 684265 = 513199) (by norm_num)
theorem B913661 : Blo 607294 913661 := bbase (se 3 (by rfl) ⟨171311, by rfl⟩ : syracuseStep 913661 = 342623) (by norm_num)
theorem B651521 : Blo 607294 651521 := bbase (se 2 (by rfl) ⟨244320, by rfl⟩ : syracuseStep 651521 = 488641) (by norm_num)
theorem B1158533 : Blo 607294 1158533 := bbase (se 4 (by rfl) ⟨108612, by rfl⟩ : syracuseStep 1158533 = 217225) (by norm_num)
theorem B684301 : Blo 607294 684301 := bbase (se 3 (by rfl) ⟨128306, by rfl⟩ : syracuseStep 684301 = 256613) (by norm_num)
theorem B913685 : Blo 607294 913685 := bbase (se 6 (by rfl) ⟨21414, by rfl⟩ : syracuseStep 913685 = 42829) (by norm_num)
theorem B1372445 : Blo 607294 1372445 := bbase (se 3 (by rfl) ⟨257333, by rfl⟩ : syracuseStep 1372445 = 514667) (by norm_num)
theorem B1028389 : Blo 607294 1028389 := bbase (se 4 (by rfl) ⟨96411, by rfl⟩ : syracuseStep 1028389 = 192823) (by norm_num)
theorem B913709 : Blo 607294 913709 := bbase (se 3 (by rfl) ⟨171320, by rfl⟩ : syracuseStep 913709 = 342641) (by norm_num)
theorem B684337 : Blo 607294 684337 := bbase (se 2 (by rfl) ⟨256626, by rfl⟩ : syracuseStep 684337 = 513253) (by norm_num)
theorem B1585469 : Blo 607294 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B913733 : Blo 607294 913733 := bbase (se 4 (by rfl) ⟨85662, by rfl⟩ : syracuseStep 913733 = 171325) (by norm_num)
theorem B782669 : Blo 607294 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B684373 : Blo 607294 684373 := bbase (se 10 (by rfl) ⟨1002, by rfl⟩ : syracuseStep 684373 = 2005) (by norm_num)
theorem B5566805 : Blo 607294 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B913757 : Blo 607294 913757 := bbase (se 3 (by rfl) ⟨171329, by rfl⟩ : syracuseStep 913757 = 342659) (by norm_num)
theorem B1372517 : Blo 607294 1372517 := bbase (se 4 (by rfl) ⟨128673, by rfl⟩ : syracuseStep 1372517 = 257347) (by norm_num)
theorem B1462637 : Blo 607294 1462637 := bbase (se 3 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 1462637 = 548489) (by norm_num)
theorem B913781 : Blo 607294 913781 := bbase (se 5 (by rfl) ⟨42833, by rfl⟩ : syracuseStep 913781 = 85667) (by norm_num)
theorem B684409 : Blo 607294 684409 := bbase (se 2 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 684409 = 513307) (by norm_num)
theorem B1028477 : Blo 607294 1028477 := bbase (se 3 (by rfl) ⟨192839, by rfl⟩ : syracuseStep 1028477 = 385679) (by norm_num)
theorem B2052485 : Blo 607294 2052485 := bbase (se 4 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 2052485 = 384841) (by norm_num)
theorem B913805 : Blo 607294 913805 := bbase (se 3 (by rfl) ⟨171338, by rfl⟩ : syracuseStep 913805 = 342677) (by norm_num)
theorem B684445 : Blo 607294 684445 := bbase (se 3 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 684445 = 256667) (by norm_num)
theorem B913829 : Blo 607294 913829 := bbase (se 4 (by rfl) ⟨85671, by rfl⟩ : syracuseStep 913829 = 171343) (by norm_num)
theorem B823717 : Blo 607294 823717 := bbase (se 4 (by rfl) ⟨77223, by rfl⟩ : syracuseStep 823717 = 154447) (by norm_num)
theorem B2929061 : Blo 607294 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B864685 : Blo 607294 864685 := bbase (se 3 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 864685 = 324257) (by norm_num)
theorem B1372589 : Blo 607294 1372589 := bbase (se 3 (by rfl) ⟨257360, by rfl⟩ : syracuseStep 1372589 = 514721) (by norm_num)
theorem B913853 : Blo 607294 913853 := bbase (se 3 (by rfl) ⟨171347, by rfl⟩ : syracuseStep 913853 = 342695) (by norm_num)
theorem B684481 : Blo 607294 684481 := bbase (se 2 (by rfl) ⟨256680, by rfl⟩ : syracuseStep 684481 = 513361) (by norm_num)
theorem B651709 : Blo 607294 651709 := bbase (se 3 (by rfl) ⟨122195, by rfl⟩ : syracuseStep 651709 = 244391) (by norm_num)
theorem B913877 : Blo 607294 913877 := bbase (se 7 (by rfl) ⟨10709, by rfl⟩ : syracuseStep 913877 = 21419) (by norm_num)
theorem B684517 : Blo 607294 684517 := bbase (se 4 (by rfl) ⟨64173, by rfl⟩ : syracuseStep 684517 = 128347) (by norm_num)
theorem B913901 : Blo 607294 913901 := bbase (se 3 (by rfl) ⟨171356, by rfl⟩ : syracuseStep 913901 = 342713) (by norm_num)
theorem B1372661 : Blo 607294 1372661 := bbase (se 5 (by rfl) ⟨64343, by rfl⟩ : syracuseStep 1372661 = 128687) (by norm_num)
theorem B1028605 : Blo 607294 1028605 := bbase (se 3 (by rfl) ⟨192863, by rfl⟩ : syracuseStep 1028605 = 385727) (by norm_num)
theorem B913925 : Blo 607294 913925 := bbase (se 4 (by rfl) ⟨85680, by rfl⟩ : syracuseStep 913925 = 171361) (by norm_num)
theorem B2314757 : Blo 607294 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B684553 : Blo 607294 684553 := bbase (se 2 (by rfl) ⟨256707, by rfl⟩ : syracuseStep 684553 = 513415) (by norm_num)
theorem B692749 : Blo 607294 692749 := bbase (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) (by norm_num)
theorem B913949 : Blo 607294 913949 := bbase (se 3 (by rfl) ⟨171365, by rfl⟩ : syracuseStep 913949 = 342731) (by norm_num)
theorem B1544741 : Blo 607294 1544741 := bbase (se 4 (by rfl) ⟨144819, by rfl⟩ : syracuseStep 1544741 = 289639) (by norm_num)
theorem B684589 : Blo 607294 684589 := bbase (se 3 (by rfl) ⟨128360, by rfl⟩ : syracuseStep 684589 = 256721) (by norm_num)
theorem B913973 : Blo 607294 913973 := bbase (se 5 (by rfl) ⟨42842, by rfl⟩ : syracuseStep 913973 = 85685) (by norm_num)
theorem B1372733 : Blo 607294 1372733 := bbase (se 3 (by rfl) ⟨257387, by rfl⟩ : syracuseStep 1372733 = 514775) (by norm_num)
theorem B913997 : Blo 607294 913997 := bbase (se 3 (by rfl) ⟨171374, by rfl⟩ : syracuseStep 913997 = 342749) (by norm_num)
theorem B684625 : Blo 607294 684625 := bbase (se 2 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 684625 = 513469) (by norm_num)
theorem B1028693 : Blo 607294 1028693 := bbase (se 8 (by rfl) ⟨6027, by rfl⟩ : syracuseStep 1028693 = 12055) (by norm_num)
theorem B914021 : Blo 607294 914021 := bbase (se 4 (by rfl) ⟨85689, by rfl⟩ : syracuseStep 914021 = 171379) (by norm_num)
theorem B2306677 : Blo 607294 2306677 := bbase (se 5 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 2306677 = 216251) (by norm_num)
theorem B684661 : Blo 607294 684661 := bbase (se 5 (by rfl) ⟨32093, by rfl⟩ : syracuseStep 684661 = 64187) (by norm_num)
theorem B914045 : Blo 607294 914045 := bbase (se 3 (by rfl) ⟨171383, by rfl⟩ : syracuseStep 914045 = 342767) (by norm_num)
theorem B1372805 : Blo 607294 1372805 := bbase (se 4 (by rfl) ⟨128700, by rfl⟩ : syracuseStep 1372805 = 257401) (by norm_num)
theorem B1249933 : Blo 607294 1249933 := bbase (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) (by norm_num)
theorem B914069 : Blo 607294 914069 := bbase (se 6 (by rfl) ⟨21423, by rfl⟩ : syracuseStep 914069 = 42847) (by norm_num)
theorem B684697 : Blo 607294 684697 := bbase (se 2 (by rfl) ⟨256761, by rfl⟩ : syracuseStep 684697 = 513523) (by norm_num)
theorem B3084965 : Blo 607294 3084965 := bbase (se 4 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 3084965 = 578431) (by norm_num)
theorem B914093 : Blo 607294 914093 := bbase (se 3 (by rfl) ⟨171392, by rfl⟩ : syracuseStep 914093 = 342785) (by norm_num)
theorem B5083829 : Blo 607294 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B684733 : Blo 607294 684733 := bbase (se 3 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 684733 = 256775) (by norm_num)
theorem B914117 : Blo 607294 914117 := bbase (se 4 (by rfl) ⟨85698, by rfl⟩ : syracuseStep 914117 = 171397) (by norm_num)
theorem B1372877 : Blo 607294 1372877 := bbase (se 3 (by rfl) ⟨257414, by rfl⟩ : syracuseStep 1372877 = 514829) (by norm_num)
theorem B1028821 : Blo 607294 1028821 := bbase (se 7 (by rfl) ⟨12056, by rfl⟩ : syracuseStep 1028821 = 24113) (by norm_num)
theorem B914141 : Blo 607294 914141 := bbase (se 3 (by rfl) ⟨171401, by rfl⟩ : syracuseStep 914141 = 342803) (by norm_num)
theorem B684769 : Blo 607294 684769 := bbase (se 2 (by rfl) ⟨256788, by rfl⟩ : syracuseStep 684769 = 513577) (by norm_num)
theorem B1299181 : Blo 607294 1299181 := bbase (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) (by norm_num)
theorem B914165 : Blo 607294 914165 := bbase (se 5 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 914165 = 85703) (by norm_num)
theorem B684805 : Blo 607294 684805 := bbase (se 4 (by rfl) ⟨64200, by rfl⟩ : syracuseStep 684805 = 128401) (by norm_num)
theorem B914189 : Blo 607294 914189 := bbase (se 3 (by rfl) ⟨171410, by rfl⟩ : syracuseStep 914189 = 342821) (by norm_num)
theorem B1946389 : Blo 607294 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B1372949 : Blo 607294 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B1463069 : Blo 607294 1463069 := bbase (se 3 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 1463069 = 548651) (by norm_num)
theorem B914213 : Blo 607294 914213 := bbase (se 4 (by rfl) ⟨85707, by rfl⟩ : syracuseStep 914213 = 171415) (by norm_num)
theorem B684841 : Blo 607294 684841 := bbase (se 2 (by rfl) ⟨256815, by rfl⟩ : syracuseStep 684841 = 513631) (by norm_num)
theorem B1028909 : Blo 607294 1028909 := bbase (se 3 (by rfl) ⟨192920, by rfl⟩ : syracuseStep 1028909 = 385841) (by norm_num)
theorem B2052917 : Blo 607294 2052917 := bbase (se 5 (by rfl) ⟨96230, by rfl⟩ : syracuseStep 2052917 = 192461) (by norm_num)
theorem B914237 : Blo 607294 914237 := bbase (se 3 (by rfl) ⟨171419, by rfl⟩ : syracuseStep 914237 = 342839) (by norm_num)
theorem B684877 : Blo 607294 684877 := bbase (se 3 (by rfl) ⟨128414, by rfl⟩ : syracuseStep 684877 = 256829) (by norm_num)
theorem B914261 : Blo 607294 914261 := bbase (se 9 (by rfl) ⟨2678, by rfl⟩ : syracuseStep 914261 = 5357) (by norm_num)
theorem B824149 : Blo 607294 824149 := bbase (se 9 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 824149 = 4829) (by norm_num)
theorem B3298133 : Blo 607294 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B1373021 : Blo 607294 1373021 := bbase (se 3 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 1373021 = 514883) (by norm_num)
theorem B914285 : Blo 607294 914285 := bbase (se 3 (by rfl) ⟨171428, by rfl⟩ : syracuseStep 914285 = 342857) (by norm_num)
theorem B684913 : Blo 607294 684913 := bbase (se 2 (by rfl) ⟨256842, by rfl⟩ : syracuseStep 684913 = 513685) (by norm_num)
theorem B914309 : Blo 607294 914309 := bbase (se 4 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 914309 = 171433) (by norm_num)
theorem B5198741 : Blo 607294 5198741 := bbase (se 6 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 5198741 = 243691) (by norm_num)
theorem B684949 : Blo 607294 684949 := bbase (se 6 (by rfl) ⟨16053, by rfl⟩ : syracuseStep 684949 = 32107) (by norm_num)
theorem B865181 : Blo 607294 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B914333 : Blo 607294 914333 := bbase (se 3 (by rfl) ⟨171437, by rfl⟩ : syracuseStep 914333 = 342875) (by norm_num)
theorem B2306981 : Blo 607294 2306981 := bbase (se 4 (by rfl) ⟨216279, by rfl⟩ : syracuseStep 2306981 = 432559) (by norm_num)
theorem B1373093 : Blo 607294 1373093 := bbase (se 4 (by rfl) ⟨128727, by rfl⟩ : syracuseStep 1373093 = 257455) (by norm_num)
theorem B1029037 : Blo 607294 1029037 := bbase (se 3 (by rfl) ⟨192944, by rfl⟩ : syracuseStep 1029037 = 385889) (by norm_num)
theorem B914357 : Blo 607294 914357 := bbase (se 5 (by rfl) ⟨42860, by rfl⟩ : syracuseStep 914357 = 85721) (by norm_num)
theorem B684985 : Blo 607294 684985 := bbase (se 2 (by rfl) ⟨256869, by rfl⟩ : syracuseStep 684985 = 513739) (by norm_num)
theorem B914381 : Blo 607294 914381 := bbase (se 3 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 914381 = 342893) (by norm_num)
theorem B685021 : Blo 607294 685021 := bbase (se 3 (by rfl) ⟨128441, by rfl⟩ : syracuseStep 685021 = 256883) (by norm_num)
theorem B914405 : Blo 607294 914405 := bbase (se 4 (by rfl) ⟨85725, by rfl⟩ : syracuseStep 914405 = 171451) (by norm_num)
theorem B832501 : Blo 607294 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B1782773 : Blo 607294 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B914429 : Blo 607294 914429 := bbase (se 3 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 914429 = 342911) (by norm_num)
theorem B685057 : Blo 607294 685057 := bbase (se 2 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 685057 = 513793) (by norm_num)
theorem B1029125 : Blo 607294 1029125 := bbase (se 4 (by rfl) ⟨96480, by rfl⟩ : syracuseStep 1029125 = 192961) (by norm_num)
theorem B1733653 : Blo 607294 1733653 := bbase (se 6 (by rfl) ⟨40632, by rfl⟩ : syracuseStep 1733653 = 81265) (by norm_num)
theorem B914453 : Blo 607294 914453 := bbase (se 6 (by rfl) ⟨21432, by rfl⟩ : syracuseStep 914453 = 42865) (by norm_num)
theorem B685093 : Blo 607294 685093 := bbase (se 4 (by rfl) ⟨64227, by rfl⟩ : syracuseStep 685093 = 128455) (by norm_num)
theorem B914477 : Blo 607294 914477 := bbase (se 3 (by rfl) ⟨171464, by rfl⟩ : syracuseStep 914477 = 342929) (by norm_num)
theorem B3077189 : Blo 607294 3077189 := bbase (se 4 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 3077189 = 576973) (by norm_num)
theorem B914501 : Blo 607294 914501 := bbase (se 4 (by rfl) ⟨85734, by rfl⟩ : syracuseStep 914501 = 171469) (by norm_num)
theorem B685129 : Blo 607294 685129 := bbase (se 2 (by rfl) ⟨256923, by rfl⟩ : syracuseStep 685129 = 513847) (by norm_num)
theorem B914525 : Blo 607294 914525 := bbase (se 3 (by rfl) ⟨171473, by rfl⟩ : syracuseStep 914525 = 342947) (by norm_num)
theorem B1299557 : Blo 607294 1299557 := bbase (se 4 (by rfl) ⟨121833, by rfl⟩ : syracuseStep 1299557 = 243667) (by norm_num)
theorem B685165 : Blo 607294 685165 := bbase (se 3 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 685165 = 256937) (by norm_num)
theorem B914549 : Blo 607294 914549 := bbase (se 5 (by rfl) ⟨42869, by rfl⟩ : syracuseStep 914549 = 85739) (by norm_num)
theorem B1029253 : Blo 607294 1029253 := bbase (se 4 (by rfl) ⟨96492, by rfl⟩ : syracuseStep 1029253 = 192985) (by norm_num)
theorem B914573 : Blo 607294 914573 := bbase (se 3 (by rfl) ⟨171482, by rfl⟩ : syracuseStep 914573 = 342965) (by norm_num)
theorem B685201 : Blo 607294 685201 := bbase (se 2 (by rfl) ⟨256950, by rfl⟩ : syracuseStep 685201 = 513901) (by norm_num)
theorem B914597 : Blo 607294 914597 := bbase (se 4 (by rfl) ⟨85743, by rfl⟩ : syracuseStep 914597 = 171487) (by norm_num)
theorem B685237 : Blo 607294 685237 := bbase (se 5 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 685237 = 64241) (by norm_num)
theorem B914621 : Blo 607294 914621 := bbase (se 3 (by rfl) ⟨171491, by rfl⟩ : syracuseStep 914621 = 342983) (by norm_num)
theorem B914645 : Blo 607294 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B685273 : Blo 607294 685273 := bbase (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) (by norm_num)
theorem B1029341 : Blo 607294 1029341 := bbase (se 3 (by rfl) ⟨193001, by rfl⟩ : syracuseStep 1029341 = 386003) (by norm_num)
theorem B2053349 : Blo 607294 2053349 := bbase (se 4 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 2053349 = 385003) (by norm_num)
theorem B914669 : Blo 607294 914669 := bbase (se 3 (by rfl) ⟨171500, by rfl⟩ : syracuseStep 914669 = 343001) (by norm_num)
theorem B685309 : Blo 607294 685309 := bbase (se 3 (by rfl) ⟨128495, by rfl⟩ : syracuseStep 685309 = 256991) (by norm_num)
theorem B914693 : Blo 607294 914693 := bbase (se 4 (by rfl) ⟨85752, by rfl⟩ : syracuseStep 914693 = 171505) (by norm_num)
theorem B9385237 : Blo 607294 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B1544629 : Blo 607294 1544629 := bbase (se 5 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 1544629 = 144809) (by norm_num)
theorem B914717 : Blo 607294 914717 := bbase (se 3 (by rfl) ⟨171509, by rfl⟩ : syracuseStep 914717 = 343019) (by norm_num)
theorem B685345 : Blo 607294 685345 := bbase (se 2 (by rfl) ⟨257004, by rfl⟩ : syracuseStep 685345 = 514009) (by norm_num)
theorem B914741 : Blo 607294 914741 := bbase (se 5 (by rfl) ⟨42878, by rfl⟩ : syracuseStep 914741 = 85757) (by norm_num)
theorem B685381 : Blo 607294 685381 := bbase (se 4 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 685381 = 128509) (by norm_num)
theorem B914765 : Blo 607294 914765 := bbase (se 3 (by rfl) ⟨171518, by rfl⟩ : syracuseStep 914765 = 343037) (by norm_num)
theorem B1029469 : Blo 607294 1029469 := bbase (se 3 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 1029469 = 386051) (by norm_num)
theorem B914789 : Blo 607294 914789 := bbase (se 4 (by rfl) ⟨85761, by rfl⟩ : syracuseStep 914789 = 171523) (by norm_num)
theorem B685417 : Blo 607294 685417 := bbase (se 2 (by rfl) ⟨257031, by rfl⟩ : syracuseStep 685417 = 514063) (by norm_num)
theorem B914813 : Blo 607294 914813 := bbase (se 3 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 914813 = 343055) (by norm_num)
theorem B685453 : Blo 607294 685453 := bbase (se 3 (by rfl) ⟨128522, by rfl⟩ : syracuseStep 685453 = 257045) (by norm_num)
theorem B7804309 : Blo 607294 7804309 := bbase (se 6 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 7804309 = 365827) (by norm_num)
theorem B914837 : Blo 607294 914837 := bbase (se 6 (by rfl) ⟨21441, by rfl⟩ : syracuseStep 914837 = 42883) (by norm_num)
theorem B914861 : Blo 607294 914861 := bbase (se 3 (by rfl) ⟨171536, by rfl⟩ : syracuseStep 914861 = 343073) (by norm_num)
theorem B685489 : Blo 607294 685489 := bbase (se 2 (by rfl) ⟨257058, by rfl⟩ : syracuseStep 685489 = 514117) (by norm_num)
theorem B1029557 : Blo 607294 1029557 := bbase (se 5 (by rfl) ⟨48260, by rfl⟩ : syracuseStep 1029557 = 96521) (by norm_num)
theorem B865733 : Blo 607294 865733 := bbase (se 4 (by rfl) ⟨81162, by rfl⟩ : syracuseStep 865733 = 162325) (by norm_num)
theorem B914885 : Blo 607294 914885 := bbase (se 4 (by rfl) ⟨85770, by rfl⟩ : syracuseStep 914885 = 171541) (by norm_num)
theorem B2594261 : Blo 607294 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B685525 : Blo 607294 685525 := bbase (se 7 (by rfl) ⟨8033, by rfl⟩ : syracuseStep 685525 = 16067) (by norm_num)
theorem B1537501 : Blo 607294 1537501 := bbase (se 3 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 1537501 = 576563) (by norm_num)
theorem B1095133 : Blo 607294 1095133 := bbase (se 3 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 1095133 = 410675) (by norm_num)
theorem B914909 : Blo 607294 914909 := bbase (se 3 (by rfl) ⟨171545, by rfl⟩ : syracuseStep 914909 = 343091) (by norm_num)
theorem B1390061 : Blo 607294 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B914933 : Blo 607294 914933 := bbase (se 5 (by rfl) ⟨42887, by rfl⟩ : syracuseStep 914933 = 85775) (by norm_num)
theorem B685561 : Blo 607294 685561 := bbase (se 2 (by rfl) ⟨257085, by rfl⟩ : syracuseStep 685561 = 514171) (by norm_num)
theorem B914957 : Blo 607294 914957 := bbase (se 3 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 914957 = 343109) (by norm_num)
theorem B1054237 : Blo 607294 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B685597 : Blo 607294 685597 := bbase (se 3 (by rfl) ⟨128549, by rfl⟩ : syracuseStep 685597 = 257099) (by norm_num)
theorem B914981 : Blo 607294 914981 := bbase (se 4 (by rfl) ⟨85779, by rfl⟩ : syracuseStep 914981 = 171559) (by norm_num)
theorem B1029685 : Blo 607294 1029685 := bbase (se 5 (by rfl) ⟨48266, by rfl⟩ : syracuseStep 1029685 = 96533) (by norm_num)
theorem B915005 : Blo 607294 915005 := bbase (se 3 (by rfl) ⟨171563, by rfl⟩ : syracuseStep 915005 = 343127) (by norm_num)
theorem B685633 : Blo 607294 685633 := bbase (se 2 (by rfl) ⟨257112, by rfl⟩ : syracuseStep 685633 = 514225) (by norm_num)
theorem B1537613 : Blo 607294 1537613 := bbase (se 3 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 1537613 = 576605) (by norm_num)
theorem B915029 : Blo 607294 915029 := bbase (se 8 (by rfl) ⟨5361, by rfl⟩ : syracuseStep 915029 = 10723) (by norm_num)
theorem B685669 : Blo 607294 685669 := bbase (se 4 (by rfl) ⟨64281, by rfl⟩ : syracuseStep 685669 = 128563) (by norm_num)
theorem B2471525 : Blo 607294 2471525 := bbase (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) (by norm_num)
theorem B915053 : Blo 607294 915053 := bbase (se 3 (by rfl) ⟨171572, by rfl⟩ : syracuseStep 915053 = 343145) (by norm_num)
theorem B915077 : Blo 607294 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B685705 : Blo 607294 685705 := bbase (se 2 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 685705 = 514279) (by norm_num)
theorem B1029773 : Blo 607294 1029773 := bbase (se 3 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 1029773 = 386165) (by norm_num)
theorem B2053781 : Blo 607294 2053781 := bbase (se 6 (by rfl) ⟨48135, by rfl⟩ : syracuseStep 2053781 = 96271) (by norm_num)
theorem B915101 : Blo 607294 915101 := bbase (se 3 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 915101 = 343163) (by norm_num)
theorem B685741 : Blo 607294 685741 := bbase (se 3 (by rfl) ⟨128576, by rfl⟩ : syracuseStep 685741 = 257153) (by norm_num)
theorem B915125 : Blo 607294 915125 := bbase (se 5 (by rfl) ⟨42896, by rfl⟩ : syracuseStep 915125 = 85793) (by norm_num)
theorem B2594501 : Blo 607294 2594501 := bbase (se 4 (by rfl) ⟨243234, by rfl⟩ : syracuseStep 2594501 = 486469) (by norm_num)
theorem B915149 : Blo 607294 915149 := bbase (se 3 (by rfl) ⟨171590, by rfl⟩ : syracuseStep 915149 = 343181) (by norm_num)
theorem B685777 : Blo 607294 685777 := bbase (se 2 (by rfl) ⟨257166, by rfl⟩ : syracuseStep 685777 = 514333) (by norm_num)
theorem B5846741 : Blo 607294 5846741 := bbase (se 7 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 5846741 = 137033) (by norm_num)
theorem B915173 : Blo 607294 915173 := bbase (se 4 (by rfl) ⟨85797, by rfl⟩ : syracuseStep 915173 = 171595) (by norm_num)
theorem B685813 : Blo 607294 685813 := bbase (se 5 (by rfl) ⟨32147, by rfl⟩ : syracuseStep 685813 = 64295) (by norm_num)
theorem B915197 : Blo 607294 915197 := bbase (se 3 (by rfl) ⟨171599, by rfl⟩ : syracuseStep 915197 = 343199) (by norm_num)
theorem B1537805 : Blo 607294 1537805 := bbase (se 3 (by rfl) ⟨288338, by rfl⟩ : syracuseStep 1537805 = 576677) (by norm_num)
theorem B915221 : Blo 607294 915221 := bbase (se 6 (by rfl) ⟨21450, by rfl⟩ : syracuseStep 915221 = 42901) (by norm_num)
theorem B685849 : Blo 607294 685849 := bbase (se 2 (by rfl) ⟨257193, by rfl⟩ : syracuseStep 685849 = 514387) (by norm_num)
theorem B915245 : Blo 607294 915245 := bbase (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) (by norm_num)
theorem B685885 : Blo 607294 685885 := bbase (se 3 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 685885 = 257207) (by norm_num)
theorem B915269 : Blo 607294 915269 := bbase (se 4 (by rfl) ⟨85806, by rfl⟩ : syracuseStep 915269 = 171613) (by norm_num)
theorem B915293 : Blo 607294 915293 := bbase (se 3 (by rfl) ⟨171617, by rfl⟩ : syracuseStep 915293 = 343235) (by norm_num)
theorem B685921 : Blo 607294 685921 := bbase (se 2 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 685921 = 514441) (by norm_num)
theorem B915317 : Blo 607294 915317 := bbase (se 5 (by rfl) ⟨42905, by rfl⟩ : syracuseStep 915317 = 85811) (by norm_num)
theorem B685957 : Blo 607294 685957 := bbase (se 4 (by rfl) ⟨64308, by rfl⟩ : syracuseStep 685957 = 128617) (by norm_num)
theorem B915341 : Blo 607294 915341 := bbase (se 3 (by rfl) ⟨171626, by rfl⟩ : syracuseStep 915341 = 343253) (by norm_num)
theorem B915365 : Blo 607294 915365 := bbase (se 4 (by rfl) ⟨85815, by rfl⟩ : syracuseStep 915365 = 171631) (by norm_num)
theorem B685993 : Blo 607294 685993 := bbase (se 2 (by rfl) ⟨257247, by rfl⟩ : syracuseStep 685993 = 514495) (by norm_num)
theorem B3086261 : Blo 607294 3086261 := bbase (se 5 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 3086261 = 289337) (by norm_num)
theorem B915389 : Blo 607294 915389 := bbase (se 3 (by rfl) ⟨171635, by rfl⟩ : syracuseStep 915389 = 343271) (by norm_num)
theorem B686029 : Blo 607294 686029 := bbase (se 3 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 686029 = 257261) (by norm_num)
theorem B915413 : Blo 607294 915413 := bbase (se 7 (by rfl) ⟨10727, by rfl⟩ : syracuseStep 915413 = 21455) (by norm_num)
theorem B915437 : Blo 607294 915437 := bbase (se 3 (by rfl) ⟨171644, by rfl⟩ : syracuseStep 915437 = 343289) (by norm_num)
theorem B686065 : Blo 607294 686065 := bbase (se 2 (by rfl) ⟨257274, by rfl⟩ : syracuseStep 686065 = 514549) (by norm_num)
theorem B686101 : Blo 607294 686101 := bbase (se 6 (by rfl) ⟨16080, by rfl⟩ : syracuseStep 686101 = 32161) (by norm_num)
theorem B686137 : Blo 607294 686137 := bbase (se 2 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 686137 = 514603) (by norm_num)
theorem B2054213 : Blo 607294 2054213 := bbase (se 4 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 2054213 = 385165) (by norm_num)
theorem B2193493 : Blo 607294 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B16660565 : Blo 607294 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B702553 : Blo 607294 702553 := bbase (se 2 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 702553 = 526915) (by norm_num)
theorem B686173 : Blo 607294 686173 := bbase (se 3 (by rfl) ⟨128657, by rfl⟩ : syracuseStep 686173 = 257315) (by norm_num)
theorem B1538149 : Blo 607294 1538149 := bbase (se 4 (by rfl) ⟨144201, by rfl⟩ : syracuseStep 1538149 = 288403) (by norm_num)
theorem B686209 : Blo 607294 686209 := bbase (se 2 (by rfl) ⟨257328, by rfl⟩ : syracuseStep 686209 = 514657) (by norm_num)
theorem B686245 : Blo 607294 686245 := bbase (se 4 (by rfl) ⟨64335, by rfl⟩ : syracuseStep 686245 = 128671) (by norm_num)
theorem B4159669 : Blo 607294 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B866485 : Blo 607294 866485 := bbase (se 5 (by rfl) ⟨40616, by rfl⟩ : syracuseStep 866485 = 81233) (by norm_num)
theorem B1054909 : Blo 607294 1054909 := bbase (se 3 (by rfl) ⟨197795, by rfl⟩ : syracuseStep 1054909 = 395591) (by norm_num)
theorem B686281 : Blo 607294 686281 := bbase (se 2 (by rfl) ⟨257355, by rfl⟩ : syracuseStep 686281 = 514711) (by norm_num)
theorem B1538261 : Blo 607294 1538261 := bbase (se 7 (by rfl) ⟨18026, by rfl⟩ : syracuseStep 1538261 = 36053) (by norm_num)
theorem B686317 : Blo 607294 686317 := bbase (se 3 (by rfl) ⟨128684, by rfl⟩ : syracuseStep 686317 = 257369) (by norm_num)
theorem B1095925 : Blo 607294 1095925 := bbase (se 5 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 1095925 = 102743) (by norm_num)
theorem B1128701 : Blo 607294 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B686353 : Blo 607294 686353 := bbase (se 2 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 686353 = 514765) (by norm_num)
theorem B686389 : Blo 607294 686389 := bbase (se 5 (by rfl) ⟨32174, by rfl⟩ : syracuseStep 686389 = 64349) (by norm_num)
theorem B3078485 : Blo 607294 3078485 := bbase (se 10 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 3078485 = 9019) (by norm_num)
theorem B989525 : Blo 607294 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B1759573 : Blo 607294 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B686425 : Blo 607294 686425 := bbase (se 2 (by rfl) ⟨257409, by rfl⟩ : syracuseStep 686425 = 514819) (by norm_num)
theorem B973181 : Blo 607294 973181 := bbase (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) (by norm_num)
theorem B686461 : Blo 607294 686461 := bbase (se 3 (by rfl) ⟨128711, by rfl⟩ : syracuseStep 686461 = 257423) (by norm_num)
theorem B1538453 : Blo 607294 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B686497 : Blo 607294 686497 := bbase (se 2 (by rfl) ⟨257436, by rfl⟩ : syracuseStep 686497 = 514873) (by norm_num)
theorem B1153453 : Blo 607294 1153453 := bbase (se 3 (by rfl) ⟨216272, by rfl⟩ : syracuseStep 1153453 = 432545) (by norm_num)
theorem B1366469 : Blo 607294 1366469 := bbase (se 4 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 1366469 = 256213) (by norm_num)
theorem B686533 : Blo 607294 686533 := bbase (se 4 (by rfl) ⟨64362, by rfl⟩ : syracuseStep 686533 = 128725) (by norm_num)
theorem B686569 : Blo 607294 686569 := bbase (se 2 (by rfl) ⟨257463, by rfl⟩ : syracuseStep 686569 = 514927) (by norm_num)
theorem B2054645 : Blo 607294 2054645 := bbase (se 5 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 2054645 = 192623) (by norm_num)
theorem B1735157 : Blo 607294 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B1038845 : Blo 607294 1038845 := bbase (se 3 (by rfl) ⟨194783, by rfl⟩ : syracuseStep 1038845 = 389567) (by norm_num)
theorem B1366541 : Blo 607294 1366541 := bbase (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) (by norm_num)
theorem B4946453 : Blo 607294 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B1096229 : Blo 607294 1096229 := bbase (se 4 (by rfl) ⟨102771, by rfl⟩ : syracuseStep 1096229 = 205543) (by norm_num)
theorem B694829 : Blo 607294 694829 := bbase (se 3 (by rfl) ⟨130280, by rfl⟩ : syracuseStep 694829 = 260561) (by norm_num)
theorem B1153597 : Blo 607294 1153597 := bbase (se 3 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 1153597 = 432599) (by norm_num)
theorem B2316869 : Blo 607294 2316869 := bbase (se 4 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 2316869 = 434413) (by norm_num)
theorem B1366613 : Blo 607294 1366613 := bbase (se 8 (by rfl) ⟨8007, by rfl⟩ : syracuseStep 1366613 = 16015) (by norm_num)
theorem B2775653 : Blo 607294 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B768629 : Blo 607294 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B924293 : Blo 607294 924293 := bbase (se 4 (by rfl) ⟨86652, by rfl⟩ : syracuseStep 924293 = 173305) (by norm_num)
theorem B694921 : Blo 607294 694921 := bbase (se 2 (by rfl) ⟨260595, by rfl⟩ : syracuseStep 694921 = 521191) (by norm_num)
theorem B948893 : Blo 607294 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B1366685 : Blo 607294 1366685 := bbase (se 3 (by rfl) ⟨256253, by rfl⟩ : syracuseStep 1366685 = 512507) (by norm_num)
theorem B768685 : Blo 607294 768685 := bbase (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) (by norm_num)
theorem B1301197 : Blo 607294 1301197 := bbase (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) (by norm_num)
theorem B1153757 : Blo 607294 1153757 := bbase (se 3 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 1153757 = 432659) (by norm_num)
theorem B1366757 : Blo 607294 1366757 := bbase (se 4 (by rfl) ⟨128133, by rfl⟩ : syracuseStep 1366757 = 256267) (by norm_num)
theorem B1538797 : Blo 607294 1538797 := bbase (se 3 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 1538797 = 577049) (by norm_num)
theorem B2931461 : Blo 607294 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B768781 : Blo 607294 768781 := bbase (se 3 (by rfl) ⟨144146, by rfl⟩ : syracuseStep 768781 = 288293) (by norm_num)
theorem B1366829 : Blo 607294 1366829 := bbase (se 3 (by rfl) ⟨256280, by rfl⟩ : syracuseStep 1366829 = 512561) (by norm_num)
theorem B973637 : Blo 607294 973637 := bbase (se 4 (by rfl) ⟨91278, by rfl⟩ : syracuseStep 973637 = 182557) (by norm_num)
theorem B1170245 : Blo 607294 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B1096517 : Blo 607294 1096517 := bbase (se 4 (by rfl) ⟨102798, by rfl⟩ : syracuseStep 1096517 = 205597) (by norm_num)
theorem B1538909 : Blo 607294 1538909 := bbase (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) (by norm_num)
theorem B2317157 : Blo 607294 2317157 := bbase (se 4 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 2317157 = 434467) (by norm_num)
theorem B1153901 : Blo 607294 1153901 := bbase (se 3 (by rfl) ⟨216356, by rfl⟩ : syracuseStep 1153901 = 432713) (by norm_num)
theorem B1366901 : Blo 607294 1366901 := bbase (se 5 (by rfl) ⟨64073, by rfl⟩ : syracuseStep 1366901 = 128147) (by norm_num)
theorem B2055077 : Blo 607294 2055077 := bbase (se 4 (by rfl) ⟨192663, by rfl⟩ : syracuseStep 2055077 = 385327) (by norm_num)
theorem B3464117 : Blo 607294 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B768953 : Blo 607294 768953 := bbase (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) (by norm_num)
theorem B1366973 : Blo 607294 1366973 := bbase (se 3 (by rfl) ⟨256307, by rfl⟩ : syracuseStep 1366973 = 512615) (by norm_num)
theorem B867277 : Blo 607294 867277 := bbase (se 3 (by rfl) ⟨162614, by rfl⟩ : syracuseStep 867277 = 325229) (by norm_num)
theorem B1391573 : Blo 607294 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B2309093 : Blo 607294 2309093 := bbase (se 4 (by rfl) ⟨216477, by rfl⟩ : syracuseStep 2309093 = 432955) (by norm_num)
theorem B769009 : Blo 607294 769009 := bbase (se 2 (by rfl) ⟨288378, by rfl⟩ : syracuseStep 769009 = 576757) (by norm_num)
theorem B1367045 : Blo 607294 1367045 := bbase (se 4 (by rfl) ⟨128160, by rfl⟩ : syracuseStep 1367045 = 256321) (by norm_num)
theorem B2923541 : Blo 607294 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B1539101 : Blo 607294 1539101 := bbase (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) (by norm_num)
theorem B1170485 : Blo 607294 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B2194501 : Blo 607294 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B1367117 : Blo 607294 1367117 := bbase (se 3 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 1367117 = 512669) (by norm_num)
theorem B769105 : Blo 607294 769105 := bbase (se 2 (by rfl) ⟨288414, by rfl⟩ : syracuseStep 769105 = 576829) (by norm_num)
theorem B695413 : Blo 607294 695413 := bbase (se 5 (by rfl) ⟨32597, by rfl⟩ : syracuseStep 695413 = 65195) (by norm_num)
theorem B1154189 : Blo 607294 1154189 := bbase (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) (by norm_num)
theorem B1367189 : Blo 607294 1367189 := bbase (se 6 (by rfl) ⟨32043, by rfl⟩ : syracuseStep 1367189 = 64087) (by norm_num)
theorem B3087557 : Blo 607294 3087557 := bbase (se 4 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 3087557 = 578917) (by norm_num)
theorem B1408213 : Blo 607294 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B1252565 : Blo 607294 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1367261 : Blo 607294 1367261 := bbase (se 3 (by rfl) ⟨256361, by rfl⟩ : syracuseStep 1367261 = 512723) (by norm_num)
theorem B769277 : Blo 607294 769277 := bbase (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) (by norm_num)
theorem B2309381 : Blo 607294 2309381 := bbase (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) (by norm_num)
theorem B695569 : Blo 607294 695569 := bbase (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) (by norm_num)
theorem B867613 : Blo 607294 867613 := bbase (se 3 (by rfl) ⟨162677, by rfl⟩ : syracuseStep 867613 = 325355) (by norm_num)
theorem B1367333 : Blo 607294 1367333 := bbase (se 4 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 1367333 = 256375) (by norm_num)
theorem B1154341 : Blo 607294 1154341 := bbase (se 4 (by rfl) ⟨108219, by rfl⟩ : syracuseStep 1154341 = 216439) (by norm_num)
theorem B769333 : Blo 607294 769333 := bbase (se 5 (by rfl) ⟨36062, by rfl⟩ : syracuseStep 769333 = 72125) (by norm_num)
theorem B2055509 : Blo 607294 2055509 := bbase (se 11 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 2055509 = 3011) (by norm_num)
theorem B1367405 : Blo 607294 1367405 := bbase (se 3 (by rfl) ⟨256388, by rfl⟩ : syracuseStep 1367405 = 512777) (by norm_num)
theorem B1539445 : Blo 607294 1539445 := bbase (se 5 (by rfl) ⟨72161, by rfl⟩ : syracuseStep 1539445 = 144323) (by norm_num)
theorem B769429 : Blo 607294 769429 := bbase (se 6 (by rfl) ⟨18033, by rfl⟩ : syracuseStep 769429 = 36067) (by norm_num)
theorem B1367477 : Blo 607294 1367477 := bbase (se 5 (by rfl) ⟨64100, by rfl⟩ : syracuseStep 1367477 = 128201) (by norm_num)
theorem B3292597 : Blo 607294 3292597 := bbase (se 5 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 3292597 = 308681) (by norm_num)
theorem B1539557 : Blo 607294 1539557 := bbase (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) (by norm_num)
theorem B867829 : Blo 607294 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B1367549 : Blo 607294 1367549 := bbase (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) (by norm_num)
theorem B9895445 : Blo 607294 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B2604581 : Blo 607294 2604581 := bbase (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) (by norm_num)
theorem B1236541 : Blo 607294 1236541 := bbase (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) (by norm_num)
theorem B769601 : Blo 607294 769601 := bbase (se 2 (by rfl) ⟨288600, by rfl⟩ : syracuseStep 769601 = 577201) (by norm_num)
theorem B1367621 : Blo 607294 1367621 := bbase (se 4 (by rfl) ⟨128214, by rfl⟩ : syracuseStep 1367621 = 256429) (by norm_num)
theorem B1302085 : Blo 607294 1302085 := bbase (se 4 (by rfl) ⟨122070, by rfl⟩ : syracuseStep 1302085 = 244141) (by norm_num)
theorem B1154645 : Blo 607294 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B1097309 : Blo 607294 1097309 := bbase (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) (by norm_num)
theorem B3079781 : Blo 607294 3079781 := bbase (se 4 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 3079781 = 577459) (by norm_num)
theorem B1949285 : Blo 607294 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B769657 : Blo 607294 769657 := bbase (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) (by norm_num)
theorem B3959765 : Blo 607294 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B1367693 : Blo 607294 1367693 := bbase (se 3 (by rfl) ⟨256442, by rfl⟩ : syracuseStep 1367693 = 512885) (by norm_num)
theorem B1539749 : Blo 607294 1539749 := bbase (se 4 (by rfl) ⟨144351, by rfl⟩ : syracuseStep 1539749 = 288703) (by norm_num)
theorem B1367765 : Blo 607294 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B769753 : Blo 607294 769753 := bbase (se 2 (by rfl) ⟨288657, by rfl⟩ : syracuseStep 769753 = 577315) (by norm_num)
theorem B1097453 : Blo 607294 1097453 := bbase (se 3 (by rfl) ⟨205772, by rfl⟩ : syracuseStep 1097453 = 411545) (by norm_num)
theorem B2055941 : Blo 607294 2055941 := bbase (se 4 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 2055941 = 385489) (by norm_num)
theorem B1367837 : Blo 607294 1367837 := bbase (se 3 (by rfl) ⟨256469, by rfl⟩ : syracuseStep 1367837 = 512939) (by norm_num)
theorem B1367909 : Blo 607294 1367909 := bbase (se 4 (by rfl) ⟨128241, by rfl⟩ : syracuseStep 1367909 = 256483) (by norm_num)
theorem B868205 : Blo 607294 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B1056629 : Blo 607294 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B1097597 : Blo 607294 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B769925 : Blo 607294 769925 := bbase (se 4 (by rfl) ⟨72180, by rfl⟩ : syracuseStep 769925 = 144361) (by norm_num)
theorem B3899285 : Blo 607294 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B1367981 : Blo 607294 1367981 := bbase (se 3 (by rfl) ⟨256496, by rfl⟩ : syracuseStep 1367981 = 512993) (by norm_num)
theorem B3694517 : Blo 607294 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B2596789 : Blo 607294 2596789 := bbase (se 5 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 2596789 = 243449) (by norm_num)
theorem B769981 : Blo 607294 769981 := bbase (se 3 (by rfl) ⟨144371, by rfl⟩ : syracuseStep 769981 = 288743) (by norm_num)
theorem B1097669 : Blo 607294 1097669 := bbase (se 4 (by rfl) ⟨102906, by rfl⟩ : syracuseStep 1097669 = 205813) (by norm_num)
theorem B1368053 : Blo 607294 1368053 := bbase (se 5 (by rfl) ⟨64127, by rfl⟩ : syracuseStep 1368053 = 128255) (by norm_num)
theorem B1540093 : Blo 607294 1540093 := bbase (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) (by norm_num)
theorem B876577 : Blo 607294 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B1564721 : Blo 607294 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B4620401 : Blo 607294 4620401 := bstep (se 2 (by rfl) ⟨1732650, by rfl⟩ : syracuseStep 4620401 = 3465301) B3465301
theorem B2924657 : Blo 607294 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B3891341 : Blo 607294 3891341 := bstep (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) B1459253
theorem B3473549 : Blo 607294 3473549 := bstep (se 3 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 3473549 = 1302581) B1302581
theorem B876737 : Blo 607294 876737 := bstep (se 2 (by rfl) ⟨328776, by rfl⟩ : syracuseStep 876737 = 657553) B657553
theorem B1056979 : Blo 607294 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B3711203 : Blo 607294 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B5546225 : Blo 607294 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B1368305 : Blo 607294 1368305 := bstep (se 2 (by rfl) ⟨513114, by rfl⟩ : syracuseStep 1368305 = 1026229) B1026229
theorem B1155313 : Blo 607294 1155313 := bstep (se 2 (by rfl) ⟨433242, by rfl⟩ : syracuseStep 1155313 = 866485) B866485
theorem B975091 : Blo 607294 975091 := bstep (se 1 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 975091 = 1462637) B1462637
theorem B1368323 : Blo 607294 1368323 := bstep (se 1 (by rfl) ⟨1026242, by rfl⟩ : syracuseStep 1368323 = 2052485) B2052485
theorem B26665237 : Blo 607294 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B4817251 : Blo 607294 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B4391309 : Blo 607294 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B2056589 : Blo 607294 2056589 := bstep (se 3 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 2056589 = 771221) B771221
theorem B770467 : Blo 607294 770467 := bstep (se 1 (by rfl) ⟨577850, by rfl⟩ : syracuseStep 770467 = 1155701) B1155701
theorem B1540529 : Blo 607294 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B2056643 : Blo 607294 2056643 := bstep (se 1 (by rfl) ⟨1542482, by rfl⟩ : syracuseStep 2056643 = 3084965) B3084965
theorem B1540579 : Blo 607294 1540579 := bstep (se 1 (by rfl) ⟨1155434, by rfl⟩ : syracuseStep 1540579 = 2310869) B2310869
theorem B1737197 : Blo 607294 1737197 := bstep (se 3 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 1737197 = 651449) B651449
theorem B770563 : Blo 607294 770563 := bstep (se 1 (by rfl) ⟨577922, by rfl⟩ : syracuseStep 770563 = 1155845) B1155845
theorem B3908101 : Blo 607294 3908101 := bstep (se 4 (by rfl) ⟨366384, by rfl⟩ : syracuseStep 3908101 = 732769) B732769
theorem B1368593 : Blo 607294 1368593 := bstep (se 2 (by rfl) ⟨513222, by rfl⟩ : syracuseStep 1368593 = 1026445) B1026445
theorem B1368611 : Blo 607294 1368611 := bstep (se 1 (by rfl) ⟨1026458, by rfl⟩ : syracuseStep 1368611 = 2052917) B2052917
theorem B3080753 : Blo 607294 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B1098289 : Blo 607294 1098289 := bstep (se 2 (by rfl) ⟨411858, by rfl⟩ : syracuseStep 1098289 = 823717) B823717
theorem B12485173 : Blo 607294 12485173 := bstep (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) B1170485
theorem B3465827 : Blo 607294 3465827 := bstep (se 1 (by rfl) ⟨2599370, by rfl⟩ : syracuseStep 3465827 = 5198741) B5198741
theorem B1540721 : Blo 607294 1540721 := bstep (se 2 (by rfl) ⟨577770, by rfl⟩ : syracuseStep 1540721 = 1155541) B1155541
theorem B2605709 : Blo 607294 2605709 := bstep (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) B977141
theorem B1188515 : Blo 607294 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B1737389 : Blo 607294 1737389 := bstep (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) B651521
theorem B2056913 : Blo 607294 2056913 := bstep (se 2 (by rfl) ⟨771342, by rfl⟩ : syracuseStep 2056913 = 1542685) B1542685
theorem B951041 : Blo 607294 951041 := bstep (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) B713281
theorem B1368881 : Blo 607294 1368881 := bstep (se 2 (by rfl) ⟨513330, by rfl⟩ : syracuseStep 1368881 = 1026661) B1026661
theorem B1368899 : Blo 607294 1368899 := bstep (se 1 (by rfl) ⟨1026674, by rfl⟩ : syracuseStep 1368899 = 2053349) B2053349
theorem B926561 : Blo 607294 926561 := bstep (se 2 (by rfl) ⟨347460, by rfl⟩ : syracuseStep 926561 = 694921) B694921
theorem B15827825 : Blo 607294 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B1024913 : Blo 607294 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B975809 : Blo 607294 975809 := bstep (se 2 (by rfl) ⟨365928, by rfl⟩ : syracuseStep 975809 = 731857) B731857
theorem B4940741 : Blo 607294 4940741 := bstep (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) B926389
theorem B1729507 : Blo 607294 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B771059 : Blo 607294 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B1025041 : Blo 607294 1025041 := bstep (se 2 (by rfl) ⟨384390, by rfl⟩ : syracuseStep 1025041 = 768781) B768781
theorem B1025075 : Blo 607294 1025075 := bstep (se 1 (by rfl) ⟨768806, by rfl⟩ : syracuseStep 1025075 = 1537613) B1537613
theorem B607299 : Blo 607294 607299 := bstep (se 1 (by rfl) ⟨455474, by rfl⟩ : syracuseStep 607299 = 910949) B910949
theorem B1647683 : Blo 607294 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B1950797 : Blo 607294 1950797 := bstep (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) B731549
theorem B1369169 : Blo 607294 1369169 := bstep (se 2 (by rfl) ⟨513438, by rfl⟩ : syracuseStep 1369169 = 1026877) B1026877
theorem B607315 : Blo 607294 607315 := bstep (se 1 (by rfl) ⟨455486, by rfl⟩ : syracuseStep 607315 = 910973) B910973
theorem B607331 : Blo 607294 607331 := bstep (se 1 (by rfl) ⟨455498, by rfl⟩ : syracuseStep 607331 = 910997) B910997
theorem B1369187 : Blo 607294 1369187 := bstep (se 1 (by rfl) ⟨1026890, by rfl⟩ : syracuseStep 1369187 = 2053781) B2053781
theorem B1098865 : Blo 607294 1098865 := bstep (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) B824149
theorem B607347 : Blo 607294 607347 := bstep (se 1 (by rfl) ⟨455510, by rfl⟩ : syracuseStep 607347 = 911021) B911021
theorem B607363 : Blo 607294 607363 := bstep (se 1 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 607363 = 911045) B911045
theorem B1729667 : Blo 607294 1729667 := bstep (se 1 (by rfl) ⟨1297250, by rfl⟩ : syracuseStep 1729667 = 2594501) B2594501
theorem B607379 : Blo 607294 607379 := bstep (se 1 (by rfl) ⟨455534, by rfl⟩ : syracuseStep 607379 = 911069) B911069
theorem B607395 : Blo 607294 607395 := bstep (se 1 (by rfl) ⟨455546, by rfl⟩ : syracuseStep 607395 = 911093) B911093
theorem B607411 : Blo 607294 607411 := bstep (se 1 (by rfl) ⟨455558, by rfl⟩ : syracuseStep 607411 = 911117) B911117
theorem B1025203 : Blo 607294 1025203 := bstep (se 1 (by rfl) ⟨768902, by rfl⟩ : syracuseStep 1025203 = 1537805) B1537805
theorem B607427 : Blo 607294 607427 := bstep (se 1 (by rfl) ⟨455570, by rfl⟩ : syracuseStep 607427 = 911141) B911141
theorem B1950925 : Blo 607294 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B607443 : Blo 607294 607443 := bstep (se 1 (by rfl) ⟨455582, by rfl⟩ : syracuseStep 607443 = 911165) B911165
theorem B607459 : Blo 607294 607459 := bstep (se 1 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 607459 = 911189) B911189
theorem B976097 : Blo 607294 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B2057453 : Blo 607294 2057453 := bstep (se 3 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 2057453 = 771545) B771545
theorem B607475 : Blo 607294 607475 := bstep (se 1 (by rfl) ⟨455606, by rfl⟩ : syracuseStep 607475 = 911213) B911213
theorem B607491 : Blo 607294 607491 := bstep (se 1 (by rfl) ⟨455618, by rfl⟩ : syracuseStep 607491 = 911237) B911237
theorem B1156369 : Blo 607294 1156369 := bstep (se 2 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 1156369 = 867277) B867277
theorem B607507 : Blo 607294 607507 := bstep (se 1 (by rfl) ⟨455630, by rfl⟩ : syracuseStep 607507 = 911261) B911261
theorem B607523 : Blo 607294 607523 := bstep (se 1 (by rfl) ⟨455642, by rfl⟩ : syracuseStep 607523 = 911285) B911285
theorem B2057507 : Blo 607294 2057507 := bstep (se 1 (by rfl) ⟨1543130, by rfl⟩ : syracuseStep 2057507 = 3086261) B3086261
theorem B607539 : Blo 607294 607539 := bstep (se 1 (by rfl) ⟨455654, by rfl⟩ : syracuseStep 607539 = 911309) B911309
theorem B1025345 : Blo 607294 1025345 := bstep (se 2 (by rfl) ⟨384504, by rfl⟩ : syracuseStep 1025345 = 769009) B769009
theorem B607555 : Blo 607294 607555 := bstep (se 1 (by rfl) ⟨455666, by rfl⟩ : syracuseStep 607555 = 911333) B911333
theorem B1041745 : Blo 607294 1041745 := bstep (se 2 (by rfl) ⟨390654, by rfl⟩ : syracuseStep 1041745 = 781309) B781309
theorem B607571 : Blo 607294 607571 := bstep (se 1 (by rfl) ⟨455678, by rfl⟩ : syracuseStep 607571 = 911357) B911357
theorem B607587 : Blo 607294 607587 := bstep (se 1 (by rfl) ⟨455690, by rfl⟩ : syracuseStep 607587 = 911381) B911381
theorem B5850467 : Blo 607294 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B2311523 : Blo 607294 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B1369457 : Blo 607294 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B2311537 : Blo 607294 2311537 := bstep (se 2 (by rfl) ⟨866826, by rfl⟩ : syracuseStep 2311537 = 1733653) B1733653
theorem B607603 : Blo 607294 607603 := bstep (se 1 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 607603 = 911405) B911405
theorem B607619 : Blo 607294 607619 := bstep (se 1 (by rfl) ⟨455714, by rfl⟩ : syracuseStep 607619 = 911429) B911429
theorem B1369475 : Blo 607294 1369475 := bstep (se 1 (by rfl) ⟨1027106, by rfl⟩ : syracuseStep 1369475 = 2054213) B2054213
theorem B607635 : Blo 607294 607635 := bstep (se 1 (by rfl) ⟨455726, by rfl⟩ : syracuseStep 607635 = 911453) B911453
theorem B607651 : Blo 607294 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B2926001 : Blo 607294 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B607667 : Blo 607294 607667 := bstep (se 1 (by rfl) ⟨455750, by rfl⟩ : syracuseStep 607667 = 911501) B911501
theorem B1025473 : Blo 607294 1025473 := bstep (se 2 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 1025473 = 769105) B769105
theorem B607683 : Blo 607294 607683 := bstep (se 1 (by rfl) ⟨455762, by rfl⟩ : syracuseStep 607683 = 911525) B911525
theorem B976321 : Blo 607294 976321 := bstep (se 2 (by rfl) ⟨366120, by rfl⟩ : syracuseStep 976321 = 732241) B732241
theorem B1951181 : Blo 607294 1951181 := bstep (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) B731693
theorem B1852877 : Blo 607294 1852877 := bstep (se 3 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 1852877 = 694829) B694829
theorem B607699 : Blo 607294 607699 := bstep (se 1 (by rfl) ⟨455774, by rfl⟩ : syracuseStep 607699 = 911549) B911549
theorem B1025507 : Blo 607294 1025507 := bstep (se 1 (by rfl) ⟨769130, by rfl⟩ : syracuseStep 1025507 = 1538261) B1538261
theorem B607715 : Blo 607294 607715 := bstep (se 1 (by rfl) ⟨455786, by rfl⟩ : syracuseStep 607715 = 911573) B911573
theorem B607731 : Blo 607294 607731 := bstep (se 1 (by rfl) ⟨455798, by rfl⟩ : syracuseStep 607731 = 911597) B911597
theorem B927217 : Blo 607294 927217 := bstep (se 2 (by rfl) ⟨347706, by rfl⟩ : syracuseStep 927217 = 695413) B695413
theorem B607747 : Blo 607294 607747 := bstep (se 1 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 607747 = 911621) B911621
theorem B607763 : Blo 607294 607763 := bstep (se 1 (by rfl) ⟨455822, by rfl⟩ : syracuseStep 607763 = 911645) B911645
theorem B607779 : Blo 607294 607779 := bstep (se 1 (by rfl) ⟨455834, by rfl⟩ : syracuseStep 607779 = 911669) B911669
theorem B2057777 : Blo 607294 2057777 := bstep (se 2 (by rfl) ⟨771666, by rfl⟩ : syracuseStep 2057777 = 1543333) B1543333
theorem B607795 : Blo 607294 607795 := bstep (se 1 (by rfl) ⟨455846, by rfl⟩ : syracuseStep 607795 = 911693) B911693
theorem B607811 : Blo 607294 607811 := bstep (se 1 (by rfl) ⟨455858, by rfl⟩ : syracuseStep 607811 = 911717) B911717
theorem B3507781 : Blo 607294 3507781 := bstep (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) B657709
theorem B1541713 : Blo 607294 1541713 := bstep (se 2 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 1541713 = 1156285) B1156285
theorem B607827 : Blo 607294 607827 := bstep (se 1 (by rfl) ⟨455870, by rfl⟩ : syracuseStep 607827 = 911741) B911741
theorem B1025635 : Blo 607294 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B607843 : Blo 607294 607843 := bstep (se 1 (by rfl) ⟨455882, by rfl⟩ : syracuseStep 607843 = 911765) B911765
theorem B1754723 : Blo 607294 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B910961 : Blo 607294 910961 := bstep (se 2 (by rfl) ⟨341610, by rfl⟩ : syracuseStep 910961 = 683221) B683221
theorem B1877617 : Blo 607294 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B607859 : Blo 607294 607859 := bstep (se 1 (by rfl) ⟨455894, by rfl⟩ : syracuseStep 607859 = 911789) B911789
theorem B910979 : Blo 607294 910979 := bstep (se 1 (by rfl) ⟨683234, by rfl⟩ : syracuseStep 910979 = 1366469) B1366469
theorem B607875 : Blo 607294 607875 := bstep (se 1 (by rfl) ⟨455906, by rfl⟩ : syracuseStep 607875 = 911813) B911813
theorem B2049677 : Blo 607294 2049677 := bstep (se 3 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 2049677 = 768629) B768629
theorem B1369745 : Blo 607294 1369745 := bstep (se 2 (by rfl) ⟨513654, by rfl⟩ : syracuseStep 1369745 = 1027309) B1027309
theorem B607891 : Blo 607294 607891 := bstep (se 1 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 607891 = 911837) B911837
theorem B911009 : Blo 607294 911009 := bstep (se 2 (by rfl) ⟨341628, by rfl⟩ : syracuseStep 911009 = 683257) B683257
theorem B607907 : Blo 607294 607907 := bstep (se 1 (by rfl) ⟨455930, by rfl⟩ : syracuseStep 607907 = 911861) B911861
theorem B1369763 : Blo 607294 1369763 := bstep (se 1 (by rfl) ⟨1027322, by rfl⟩ : syracuseStep 1369763 = 2054645) B2054645
theorem B1156771 : Blo 607294 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B911027 : Blo 607294 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B607923 : Blo 607294 607923 := bstep (se 1 (by rfl) ⟨455942, by rfl⟩ : syracuseStep 607923 = 911885) B911885
theorem B771763 : Blo 607294 771763 := bstep (se 1 (by rfl) ⟨578822, by rfl⟩ : syracuseStep 771763 = 1157645) B1157645
theorem B927425 : Blo 607294 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B2049731 : Blo 607294 2049731 := bstep (se 1 (by rfl) ⟨1537298, by rfl⟩ : syracuseStep 2049731 = 3074597) B3074597
theorem B607939 : Blo 607294 607939 := bstep (se 1 (by rfl) ⟨455954, by rfl⟩ : syracuseStep 607939 = 911909) B911909
theorem B730819 : Blo 607294 730819 := bstep (se 1 (by rfl) ⟨548114, by rfl⟩ : syracuseStep 730819 = 1096229) B1096229
theorem B911057 : Blo 607294 911057 := bstep (se 2 (by rfl) ⟨341646, by rfl⟩ : syracuseStep 911057 = 683293) B683293
theorem B607955 : Blo 607294 607955 := bstep (se 1 (by rfl) ⟨455966, by rfl⟩ : syracuseStep 607955 = 911933) B911933
theorem B1156817 : Blo 607294 1156817 := bstep (se 2 (by rfl) ⟨433806, by rfl⟩ : syracuseStep 1156817 = 867613) B867613
theorem B911075 : Blo 607294 911075 := bstep (se 1 (by rfl) ⟨683306, by rfl⟩ : syracuseStep 911075 = 1366613) B1366613
theorem B607971 : Blo 607294 607971 := bstep (se 1 (by rfl) ⟨455978, by rfl⟩ : syracuseStep 607971 = 911957) B911957
theorem B1025777 : Blo 607294 1025777 := bstep (se 2 (by rfl) ⟨384666, by rfl⟩ : syracuseStep 1025777 = 769333) B769333
theorem B607987 : Blo 607294 607987 := bstep (se 1 (by rfl) ⟨455990, by rfl⟩ : syracuseStep 607987 = 911981) B911981
theorem B911105 : Blo 607294 911105 := bstep (se 2 (by rfl) ⟨341664, by rfl⟩ : syracuseStep 911105 = 683329) B683329
theorem B616195 : Blo 607294 616195 := bstep (se 1 (by rfl) ⟨462146, by rfl⟩ : syracuseStep 616195 = 924293) B924293
theorem B608003 : Blo 607294 608003 := bstep (se 1 (by rfl) ⟨456002, by rfl⟩ : syracuseStep 608003 = 912005) B912005
theorem B2189069 : Blo 607294 2189069 := bstep (se 3 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 2189069 = 820901) B820901
theorem B911123 : Blo 607294 911123 := bstep (se 1 (by rfl) ⟨683342, by rfl⟩ : syracuseStep 911123 = 1366685) B1366685
theorem B608019 : Blo 607294 608019 := bstep (se 1 (by rfl) ⟨456014, by rfl⟩ : syracuseStep 608019 = 912029) B912029
theorem B771859 : Blo 607294 771859 := bstep (se 1 (by rfl) ⟨578894, by rfl⟩ : syracuseStep 771859 = 1157789) B1157789
theorem B608035 : Blo 607294 608035 := bstep (se 1 (by rfl) ⟨456026, by rfl⟩ : syracuseStep 608035 = 912053) B912053
theorem B911153 : Blo 607294 911153 := bstep (se 2 (by rfl) ⟨341682, by rfl⟩ : syracuseStep 911153 = 683365) B683365
theorem B608051 : Blo 607294 608051 := bstep (se 1 (by rfl) ⟨456038, by rfl⟩ : syracuseStep 608051 = 912077) B912077
theorem B911171 : Blo 607294 911171 := bstep (se 1 (by rfl) ⟨683378, by rfl⟩ : syracuseStep 911171 = 1366757) B1366757
theorem B608067 : Blo 607294 608067 := bstep (se 1 (by rfl) ⟨456050, by rfl⟩ : syracuseStep 608067 = 912101) B912101
theorem B608083 : Blo 607294 608083 := bstep (se 1 (by rfl) ⟨456062, by rfl⟩ : syracuseStep 608083 = 912125) B912125
theorem B911201 : Blo 607294 911201 := bstep (se 2 (by rfl) ⟨341700, by rfl⟩ : syracuseStep 911201 = 683401) B683401
theorem B608099 : Blo 607294 608099 := bstep (se 1 (by rfl) ⟨456074, by rfl⟩ : syracuseStep 608099 = 912149) B912149
theorem B1541987 : Blo 607294 1541987 := bstep (se 1 (by rfl) ⟨1156490, by rfl⟩ : syracuseStep 1541987 = 2312981) B2312981
theorem B1025905 : Blo 607294 1025905 := bstep (se 2 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 1025905 = 769429) B769429
theorem B10405745 : Blo 607294 10405745 := bstep (se 2 (by rfl) ⟨3902154, by rfl⟩ : syracuseStep 10405745 = 7804309) B7804309
theorem B911219 : Blo 607294 911219 := bstep (se 1 (by rfl) ⟨683414, by rfl⟩ : syracuseStep 911219 = 1366829) B1366829
theorem B608115 : Blo 607294 608115 := bstep (se 1 (by rfl) ⟨456086, by rfl⟩ : syracuseStep 608115 = 912173) B912173
theorem B649091 : Blo 607294 649091 := bstep (se 1 (by rfl) ⟨486818, by rfl⟩ : syracuseStep 649091 = 973637) B973637
theorem B608131 : Blo 607294 608131 := bstep (se 1 (by rfl) ⟨456098, by rfl⟩ : syracuseStep 608131 = 912197) B912197
theorem B731011 : Blo 607294 731011 := bstep (se 1 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 731011 = 1096517) B1096517
theorem B911249 : Blo 607294 911249 := bstep (se 2 (by rfl) ⟨341718, by rfl⟩ : syracuseStep 911249 = 683437) B683437
theorem B1025939 : Blo 607294 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B608147 : Blo 607294 608147 := bstep (se 1 (by rfl) ⟨456110, by rfl⟩ : syracuseStep 608147 = 912221) B912221
theorem B911267 : Blo 607294 911267 := bstep (se 1 (by rfl) ⟨683450, by rfl⟩ : syracuseStep 911267 = 1366901) B1366901
theorem B608163 : Blo 607294 608163 := bstep (se 1 (by rfl) ⟨456122, by rfl⟩ : syracuseStep 608163 = 912245) B912245
theorem B1370033 : Blo 607294 1370033 := bstep (se 2 (by rfl) ⟨513762, by rfl⟩ : syracuseStep 1370033 = 1027525) B1027525
theorem B608179 : Blo 607294 608179 := bstep (se 1 (by rfl) ⟨456134, by rfl⟩ : syracuseStep 608179 = 912269) B912269
theorem B911297 : Blo 607294 911297 := bstep (se 2 (by rfl) ⟨341736, by rfl⟩ : syracuseStep 911297 = 683473) B683473
theorem B608195 : Blo 607294 608195 := bstep (se 1 (by rfl) ⟨456146, by rfl⟩ : syracuseStep 608195 = 912293) B912293
theorem B1370051 : Blo 607294 1370051 := bstep (se 1 (by rfl) ⟨1027538, by rfl⟩ : syracuseStep 1370051 = 2055077) B2055077
theorem B2050001 : Blo 607294 2050001 := bstep (se 2 (by rfl) ⟨768750, by rfl⟩ : syracuseStep 2050001 = 1537501) B1537501
theorem B1460177 : Blo 607294 1460177 := bstep (se 2 (by rfl) ⟨547566, by rfl⟩ : syracuseStep 1460177 = 1095133) B1095133
theorem B911315 : Blo 607294 911315 := bstep (se 1 (by rfl) ⟨683486, by rfl⟩ : syracuseStep 911315 = 1366973) B1366973
theorem B608211 : Blo 607294 608211 := bstep (se 1 (by rfl) ⟨456158, by rfl⟩ : syracuseStep 608211 = 912317) B912317
theorem B1460195 : Blo 607294 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B608227 : Blo 607294 608227 := bstep (se 1 (by rfl) ⟨456170, by rfl⟩ : syracuseStep 608227 = 912341) B912341
theorem B3082211 : Blo 607294 3082211 := bstep (se 1 (by rfl) ⟨2311658, by rfl⟩ : syracuseStep 3082211 = 4623317) B4623317
theorem B2639843 : Blo 607294 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B911345 : Blo 607294 911345 := bstep (se 2 (by rfl) ⟨341754, by rfl⟩ : syracuseStep 911345 = 683509) B683509
theorem B1157105 : Blo 607294 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B608243 : Blo 607294 608243 := bstep (se 1 (by rfl) ⟨456182, by rfl⟩ : syracuseStep 608243 = 912365) B912365
theorem B911363 : Blo 607294 911363 := bstep (se 1 (by rfl) ⟨683522, by rfl⟩ : syracuseStep 911363 = 1367045) B1367045
theorem B608259 : Blo 607294 608259 := bstep (se 1 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 608259 = 912389) B912389
theorem B1026067 : Blo 607294 1026067 := bstep (se 1 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 1026067 = 1539101) B1539101
theorem B608275 : Blo 607294 608275 := bstep (se 1 (by rfl) ⟨456206, by rfl⟩ : syracuseStep 608275 = 912413) B912413
theorem B911393 : Blo 607294 911393 := bstep (se 2 (by rfl) ⟨341772, by rfl⟩ : syracuseStep 911393 = 683545) B683545
theorem B608291 : Blo 607294 608291 := bstep (se 1 (by rfl) ⟨456218, by rfl⟩ : syracuseStep 608291 = 912437) B912437
theorem B1542179 : Blo 607294 1542179 := bstep (se 1 (by rfl) ⟨1156634, by rfl⟩ : syracuseStep 1542179 = 2313269) B2313269
theorem B911411 : Blo 607294 911411 := bstep (se 1 (by rfl) ⟨683558, by rfl⟩ : syracuseStep 911411 = 1367117) B1367117
theorem B608307 : Blo 607294 608307 := bstep (se 1 (by rfl) ⟨456230, by rfl⟩ : syracuseStep 608307 = 912461) B912461
theorem B608323 : Blo 607294 608323 := bstep (se 1 (by rfl) ⟨456242, by rfl⟩ : syracuseStep 608323 = 912485) B912485
theorem B3901517 : Blo 607294 3901517 := bstep (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) B1463069
theorem B911441 : Blo 607294 911441 := bstep (se 2 (by rfl) ⟨341790, by rfl⟩ : syracuseStep 911441 = 683581) B683581
theorem B2058317 : Blo 607294 2058317 := bstep (se 3 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 2058317 = 771869) B771869
theorem B608339 : Blo 607294 608339 := bstep (se 1 (by rfl) ⟨456254, by rfl⟩ : syracuseStep 608339 = 912509) B912509
theorem B1648721 : Blo 607294 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B911459 : Blo 607294 911459 := bstep (se 1 (by rfl) ⟨683594, by rfl⟩ : syracuseStep 911459 = 1367189) B1367189
theorem B608355 : Blo 607294 608355 := bstep (se 1 (by rfl) ⟨456266, by rfl⟩ : syracuseStep 608355 = 912533) B912533
theorem B608371 : Blo 607294 608371 := bstep (se 1 (by rfl) ⟨456278, by rfl⟩ : syracuseStep 608371 = 912557) B912557
theorem B911489 : Blo 607294 911489 := bstep (se 2 (by rfl) ⟨341808, by rfl⟩ : syracuseStep 911489 = 683617) B683617
theorem B608387 : Blo 607294 608387 := bstep (se 1 (by rfl) ⟨456290, by rfl⟩ : syracuseStep 608387 = 912581) B912581
theorem B2058371 : Blo 607294 2058371 := bstep (se 1 (by rfl) ⟨1543778, by rfl⟩ : syracuseStep 2058371 = 3087557) B3087557
theorem B911507 : Blo 607294 911507 := bstep (se 1 (by rfl) ⟨683630, by rfl⟩ : syracuseStep 911507 = 1367261) B1367261
theorem B608403 : Blo 607294 608403 := bstep (se 1 (by rfl) ⟨456302, by rfl⟩ : syracuseStep 608403 = 912605) B912605
theorem B1026209 : Blo 607294 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B1755299 : Blo 607294 1755299 := bstep (se 1 (by rfl) ⟨1316474, by rfl⟩ : syracuseStep 1755299 = 2632949) B2632949
theorem B608419 : Blo 607294 608419 := bstep (se 1 (by rfl) ⟨456314, by rfl⟩ : syracuseStep 608419 = 912629) B912629
theorem B911537 : Blo 607294 911537 := bstep (se 2 (by rfl) ⟨341826, by rfl⟩ : syracuseStep 911537 = 683653) B683653
theorem B1730737 : Blo 607294 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B608435 : Blo 607294 608435 := bstep (se 1 (by rfl) ⟨456326, by rfl⟩ : syracuseStep 608435 = 912653) B912653
theorem B911555 : Blo 607294 911555 := bstep (se 1 (by rfl) ⟨683666, by rfl⟩ : syracuseStep 911555 = 1367333) B1367333
theorem B608451 : Blo 607294 608451 := bstep (se 1 (by rfl) ⟨456338, by rfl⟩ : syracuseStep 608451 = 912677) B912677
theorem B1370321 : Blo 607294 1370321 := bstep (se 2 (by rfl) ⟨513870, by rfl⟩ : syracuseStep 1370321 = 1027741) B1027741
theorem B608467 : Blo 607294 608467 := bstep (se 1 (by rfl) ⟨456350, by rfl⟩ : syracuseStep 608467 = 912701) B912701
theorem B5352419 : Blo 607294 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B911585 : Blo 607294 911585 := bstep (se 2 (by rfl) ⟨341844, by rfl⟩ : syracuseStep 911585 = 683689) B683689
theorem B4442339 : Blo 607294 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B608483 : Blo 607294 608483 := bstep (se 1 (by rfl) ⟨456362, by rfl⟩ : syracuseStep 608483 = 912725) B912725
theorem B1370339 : Blo 607294 1370339 := bstep (se 1 (by rfl) ⟨1027754, by rfl⟩ : syracuseStep 1370339 = 2055509) B2055509
theorem B1976557 : Blo 607294 1976557 := bstep (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) B741209
theorem B911603 : Blo 607294 911603 := bstep (se 1 (by rfl) ⟨683702, by rfl⟩ : syracuseStep 911603 = 1367405) B1367405
theorem B608499 : Blo 607294 608499 := bstep (se 1 (by rfl) ⟨456374, by rfl⟩ : syracuseStep 608499 = 912749) B912749
theorem B608515 : Blo 607294 608515 := bstep (se 1 (by rfl) ⟨456386, by rfl⟩ : syracuseStep 608515 = 912773) B912773
theorem B772355 : Blo 607294 772355 := bstep (se 1 (by rfl) ⟨579266, by rfl⟩ : syracuseStep 772355 = 1158533) B1158533
theorem B911633 : Blo 607294 911633 := bstep (se 2 (by rfl) ⟨341862, by rfl⟩ : syracuseStep 911633 = 683725) B683725
theorem B608531 : Blo 607294 608531 := bstep (se 1 (by rfl) ⟨456398, by rfl⟩ : syracuseStep 608531 = 912797) B912797
theorem B1026337 : Blo 607294 1026337 := bstep (se 2 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 1026337 = 769753) B769753
theorem B911651 : Blo 607294 911651 := bstep (se 1 (by rfl) ⟨683738, by rfl⟩ : syracuseStep 911651 = 1367477) B1367477
theorem B608547 : Blo 607294 608547 := bstep (se 1 (by rfl) ⟨456410, by rfl⟩ : syracuseStep 608547 = 912821) B912821
theorem B3901745 : Blo 607294 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B608563 : Blo 607294 608563 := bstep (se 1 (by rfl) ⟨456422, by rfl⟩ : syracuseStep 608563 = 912845) B912845
theorem B6932789 : Blo 607294 6932789 := bstep (se 5 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 6932789 = 649949) B649949
theorem B911681 : Blo 607294 911681 := bstep (se 2 (by rfl) ⟨341880, by rfl⟩ : syracuseStep 911681 = 683761) B683761
theorem B1026371 : Blo 607294 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B608579 : Blo 607294 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B3475781 : Blo 607294 3475781 := bstep (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) B651709
theorem B911699 : Blo 607294 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B608595 : Blo 607294 608595 := bstep (se 1 (by rfl) ⟨456446, by rfl⟩ : syracuseStep 608595 = 912893) B912893
theorem B2926925 : Blo 607294 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B608611 : Blo 607294 608611 := bstep (se 1 (by rfl) ⟨456458, by rfl⟩ : syracuseStep 608611 = 912917) B912917
theorem B6596963 : Blo 607294 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B911729 : Blo 607294 911729 := bstep (se 2 (by rfl) ⟨341898, by rfl⟩ : syracuseStep 911729 = 683797) B683797
theorem B2091377 : Blo 607294 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B608627 : Blo 607294 608627 := bstep (se 1 (by rfl) ⟨456470, by rfl⟩ : syracuseStep 608627 = 912941) B912941
theorem B911747 : Blo 607294 911747 := bstep (se 1 (by rfl) ⟨683810, by rfl⟩ : syracuseStep 911747 = 1367621) B1367621
theorem B608643 : Blo 607294 608643 := bstep (se 1 (by rfl) ⟨456482, by rfl⟩ : syracuseStep 608643 = 912965) B912965
theorem B3459469 : Blo 607294 3459469 := bstep (se 3 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 3459469 = 1297301) B1297301
theorem B608659 : Blo 607294 608659 := bstep (se 1 (by rfl) ⟨456494, by rfl⟩ : syracuseStep 608659 = 912989) B912989
theorem B731539 : Blo 607294 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B911777 : Blo 607294 911777 := bstep (se 2 (by rfl) ⟨341916, by rfl⟩ : syracuseStep 911777 = 683833) B683833
theorem B608675 : Blo 607294 608675 := bstep (se 1 (by rfl) ⟨456506, by rfl⟩ : syracuseStep 608675 = 913013) B913013
theorem B911795 : Blo 607294 911795 := bstep (se 1 (by rfl) ⟨683846, by rfl⟩ : syracuseStep 911795 = 1367693) B1367693
theorem B608691 : Blo 607294 608691 := bstep (se 1 (by rfl) ⟨456518, by rfl⟩ : syracuseStep 608691 = 913037) B913037
theorem B1026499 : Blo 607294 1026499 := bstep (se 1 (by rfl) ⟨769874, by rfl⟩ : syracuseStep 1026499 = 1539749) B1539749
theorem B608707 : Blo 607294 608707 := bstep (se 1 (by rfl) ⟨456530, by rfl⟩ : syracuseStep 608707 = 913061) B913061
theorem B3467717 : Blo 607294 3467717 := bstep (se 4 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 3467717 = 650197) B650197
theorem B911825 : Blo 607294 911825 := bstep (se 2 (by rfl) ⟨341934, by rfl⟩ : syracuseStep 911825 = 683869) B683869
theorem B608723 : Blo 607294 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B911843 : Blo 607294 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B608739 : Blo 607294 608739 := bstep (se 1 (by rfl) ⟨456554, by rfl⟩ : syracuseStep 608739 = 913109) B913109
theorem B2050541 : Blo 607294 2050541 := bstep (se 3 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 2050541 = 768953) B768953
theorem B1370609 : Blo 607294 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B608755 : Blo 607294 608755 := bstep (se 1 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 608755 = 913133) B913133
theorem B731635 : Blo 607294 731635 := bstep (se 1 (by rfl) ⟨548726, by rfl⟩ : syracuseStep 731635 = 1097453) B1097453
theorem B911873 : Blo 607294 911873 := bstep (se 2 (by rfl) ⟨341952, by rfl⟩ : syracuseStep 911873 = 683905) B683905
theorem B608771 : Blo 607294 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B1370627 : Blo 607294 1370627 := bstep (se 1 (by rfl) ⟨1027970, by rfl⟩ : syracuseStep 1370627 = 2055941) B2055941
theorem B2927117 : Blo 607294 2927117 := bstep (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) B1097669
theorem B911891 : Blo 607294 911891 := bstep (se 1 (by rfl) ⟨683918, by rfl⟩ : syracuseStep 911891 = 1367837) B1367837
theorem B608787 : Blo 607294 608787 := bstep (se 1 (by rfl) ⟨456590, by rfl⟩ : syracuseStep 608787 = 913181) B913181
theorem B2050595 : Blo 607294 2050595 := bstep (se 1 (by rfl) ⟨1537946, by rfl⟩ : syracuseStep 2050595 = 3075893) B3075893
theorem B608803 : Blo 607294 608803 := bstep (se 1 (by rfl) ⟨456602, by rfl⟩ : syracuseStep 608803 = 913205) B913205
theorem B911921 : Blo 607294 911921 := bstep (se 2 (by rfl) ⟨341970, by rfl⟩ : syracuseStep 911921 = 683941) B683941
theorem B608819 : Blo 607294 608819 := bstep (se 1 (by rfl) ⟨456614, by rfl⟩ : syracuseStep 608819 = 913229) B913229
theorem B911939 : Blo 607294 911939 := bstep (se 1 (by rfl) ⟨683954, by rfl⟩ : syracuseStep 911939 = 1367909) B1367909
theorem B608835 : Blo 607294 608835 := bstep (se 1 (by rfl) ⟨456626, by rfl⟩ : syracuseStep 608835 = 913253) B913253
theorem B1026641 : Blo 607294 1026641 := bstep (se 2 (by rfl) ⟨384990, by rfl⟩ : syracuseStep 1026641 = 769981) B769981
theorem B608851 : Blo 607294 608851 := bstep (se 1 (by rfl) ⟨456638, by rfl⟩ : syracuseStep 608851 = 913277) B913277
theorem B911969 : Blo 607294 911969 := bstep (se 2 (by rfl) ⟨341988, by rfl⟩ : syracuseStep 911969 = 683977) B683977
theorem B2599523 : Blo 607294 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B608867 : Blo 607294 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B911987 : Blo 607294 911987 := bstep (se 1 (by rfl) ⟨683990, by rfl⟩ : syracuseStep 911987 = 1367981) B1367981
theorem B608883 : Blo 607294 608883 := bstep (se 1 (by rfl) ⟨456662, by rfl⟩ : syracuseStep 608883 = 913325) B913325
theorem B608899 : Blo 607294 608899 := bstep (se 1 (by rfl) ⟨456674, by rfl⟩ : syracuseStep 608899 = 913349) B913349
theorem B912017 : Blo 607294 912017 := bstep (se 2 (by rfl) ⟨342006, by rfl⟩ : syracuseStep 912017 = 684013) B684013
theorem B608915 : Blo 607294 608915 := bstep (se 1 (by rfl) ⟨456686, by rfl⟩ : syracuseStep 608915 = 913373) B913373
theorem B912035 : Blo 607294 912035 := bstep (se 1 (by rfl) ⟨684026, by rfl⟩ : syracuseStep 912035 = 1368053) B1368053
theorem B608931 : Blo 607294 608931 := bstep (se 1 (by rfl) ⟨456698, by rfl⟩ : syracuseStep 608931 = 913397) B913397
theorem B608947 : Blo 607294 608947 := bstep (se 1 (by rfl) ⟨456710, by rfl⟩ : syracuseStep 608947 = 913421) B913421
theorem B912065 : Blo 607294 912065 := bstep (se 2 (by rfl) ⟨342024, by rfl⟩ : syracuseStep 912065 = 684049) B684049
theorem B608963 : Blo 607294 608963 := bstep (se 1 (by rfl) ⟨456722, by rfl⟩ : syracuseStep 608963 = 913445) B913445
theorem B1157827 : Blo 607294 1157827 := bstep (se 1 (by rfl) ⟨868370, by rfl⟩ : syracuseStep 1157827 = 1736741) B1736741
theorem B1026769 : Blo 607294 1026769 := bstep (se 2 (by rfl) ⟨385038, by rfl⟩ : syracuseStep 1026769 = 770077) B770077
theorem B912083 : Blo 607294 912083 := bstep (se 1 (by rfl) ⟨684062, by rfl⟩ : syracuseStep 912083 = 1368125) B1368125
theorem B608979 : Blo 607294 608979 := bstep (se 1 (by rfl) ⟨456734, by rfl⟩ : syracuseStep 608979 = 913469) B913469
theorem B608995 : Blo 607294 608995 := bstep (se 1 (by rfl) ⟨456746, by rfl⟩ : syracuseStep 608995 = 913493) B913493
theorem B912113 : Blo 607294 912113 := bstep (se 2 (by rfl) ⟨342042, by rfl⟩ : syracuseStep 912113 = 684085) B684085
theorem B1026803 : Blo 607294 1026803 := bstep (se 1 (by rfl) ⟨770102, by rfl⟩ : syracuseStep 1026803 = 1540205) B1540205
theorem B609011 : Blo 607294 609011 := bstep (se 1 (by rfl) ⟨456758, by rfl⟩ : syracuseStep 609011 = 913517) B913517
theorem B912131 : Blo 607294 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B609027 : Blo 607294 609027 := bstep (se 1 (by rfl) ⟨456770, by rfl⟩ : syracuseStep 609027 = 913541) B913541
theorem B3083021 : Blo 607294 3083021 := bstep (se 3 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 3083021 = 1156133) B1156133
theorem B1370897 : Blo 607294 1370897 := bstep (se 2 (by rfl) ⟨514086, by rfl⟩ : syracuseStep 1370897 = 1028173) B1028173
theorem B609043 : Blo 607294 609043 := bstep (se 1 (by rfl) ⟨456782, by rfl⟩ : syracuseStep 609043 = 913565) B913565
theorem B936737 : Blo 607294 936737 := bstep (se 2 (by rfl) ⟨351276, by rfl⟩ : syracuseStep 936737 = 702553) B702553
theorem B912161 : Blo 607294 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B609059 : Blo 607294 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B2312995 : Blo 607294 2312995 := bstep (se 1 (by rfl) ⟨1734746, by rfl⟩ : syracuseStep 2312995 = 3469493) B3469493
theorem B1370915 : Blo 607294 1370915 := bstep (se 1 (by rfl) ⟨1028186, by rfl⟩ : syracuseStep 1370915 = 2056373) B2056373
theorem B2050865 : Blo 607294 2050865 := bstep (se 2 (by rfl) ⟨769074, by rfl⟩ : syracuseStep 2050865 = 1538149) B1538149
theorem B912179 : Blo 607294 912179 := bstep (se 1 (by rfl) ⟨684134, by rfl⟩ : syracuseStep 912179 = 1368269) B1368269
theorem B650035 : Blo 607294 650035 := bstep (se 1 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 650035 = 975053) B975053
theorem B609075 : Blo 607294 609075 := bstep (se 1 (by rfl) ⟨456806, by rfl⟩ : syracuseStep 609075 = 913613) B913613
theorem B609091 : Blo 607294 609091 := bstep (se 1 (by rfl) ⟨456818, by rfl⟩ : syracuseStep 609091 = 913637) B913637
theorem B912209 : Blo 607294 912209 := bstep (se 2 (by rfl) ⟨342078, by rfl⟩ : syracuseStep 912209 = 684157) B684157
theorem B609107 : Blo 607294 609107 := bstep (se 1 (by rfl) ⟨456830, by rfl⟩ : syracuseStep 609107 = 913661) B913661
theorem B2190179 : Blo 607294 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B912227 : Blo 607294 912227 := bstep (se 1 (by rfl) ⟨684170, by rfl⟩ : syracuseStep 912227 = 1368341) B1368341
theorem B609123 : Blo 607294 609123 := bstep (se 1 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 609123 = 913685) B913685
theorem B1026931 : Blo 607294 1026931 := bstep (se 1 (by rfl) ⟨770198, by rfl⟩ : syracuseStep 1026931 = 1540397) B1540397
theorem B609139 : Blo 607294 609139 := bstep (se 1 (by rfl) ⟨456854, by rfl⟩ : syracuseStep 609139 = 913709) B913709
theorem B912257 : Blo 607294 912257 := bstep (se 2 (by rfl) ⟨342096, by rfl⟩ : syracuseStep 912257 = 684193) B684193
theorem B609155 : Blo 607294 609155 := bstep (se 1 (by rfl) ⟨456866, by rfl⟩ : syracuseStep 609155 = 913733) B913733
theorem B912275 : Blo 607294 912275 := bstep (se 1 (by rfl) ⟨684206, by rfl⟩ : syracuseStep 912275 = 1368413) B1368413
theorem B609171 : Blo 607294 609171 := bstep (se 1 (by rfl) ⟨456878, by rfl⟩ : syracuseStep 609171 = 913757) B913757
theorem B609187 : Blo 607294 609187 := bstep (se 1 (by rfl) ⟨456890, by rfl⟩ : syracuseStep 609187 = 913781) B913781
theorem B912305 : Blo 607294 912305 := bstep (se 2 (by rfl) ⟨342114, by rfl⟩ : syracuseStep 912305 = 684229) B684229
theorem B2059181 : Blo 607294 2059181 := bstep (se 3 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 2059181 = 772193) B772193
theorem B609203 : Blo 607294 609203 := bstep (se 1 (by rfl) ⟨456902, by rfl⟩ : syracuseStep 609203 = 913805) B913805
theorem B912323 : Blo 607294 912323 := bstep (se 1 (by rfl) ⟨684242, by rfl⟩ : syracuseStep 912323 = 1368485) B1368485
theorem B609219 : Blo 607294 609219 := bstep (se 1 (by rfl) ⟨456914, by rfl⟩ : syracuseStep 609219 = 913829) B913829
theorem B1952707 : Blo 607294 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B1543121 : Blo 607294 1543121 := bstep (se 2 (by rfl) ⟨578670, by rfl⟩ : syracuseStep 1543121 = 1157341) B1157341
theorem B609235 : Blo 607294 609235 := bstep (se 1 (by rfl) ⟨456926, by rfl⟩ : syracuseStep 609235 = 913853) B913853
theorem B912353 : Blo 607294 912353 := bstep (se 2 (by rfl) ⟨342132, by rfl⟩ : syracuseStep 912353 = 684265) B684265
theorem B781283 : Blo 607294 781283 := bstep (se 1 (by rfl) ⟨585962, by rfl⟩ : syracuseStep 781283 = 1171925) B1171925
theorem B609251 : Blo 607294 609251 := bstep (se 1 (by rfl) ⟨456938, by rfl⟩ : syracuseStep 609251 = 913877) B913877
theorem B1461233 : Blo 607294 1461233 := bstep (se 2 (by rfl) ⟨547962, by rfl⟩ : syracuseStep 1461233 = 1095925) B1095925
theorem B1387505 : Blo 607294 1387505 := bstep (se 2 (by rfl) ⟨520314, by rfl⟩ : syracuseStep 1387505 = 1040629) B1040629
theorem B912371 : Blo 607294 912371 := bstep (se 1 (by rfl) ⟨684278, by rfl⟩ : syracuseStep 912371 = 1368557) B1368557
theorem B609267 : Blo 607294 609267 := bstep (se 1 (by rfl) ⟨456950, by rfl⟩ : syracuseStep 609267 = 913901) B913901
theorem B1027073 : Blo 607294 1027073 := bstep (se 2 (by rfl) ⟨385152, by rfl⟩ : syracuseStep 1027073 = 770305) B770305
theorem B609283 : Blo 607294 609283 := bstep (se 1 (by rfl) ⟨456962, by rfl⟩ : syracuseStep 609283 = 913925) B913925
theorem B1543171 : Blo 607294 1543171 := bstep (se 1 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 1543171 = 2314757) B2314757
theorem B2190349 : Blo 607294 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B912401 : Blo 607294 912401 := bstep (se 2 (by rfl) ⟨342150, by rfl⟩ : syracuseStep 912401 = 684301) B684301
theorem B609299 : Blo 607294 609299 := bstep (se 1 (by rfl) ⟨456974, by rfl⟩ : syracuseStep 609299 = 913949) B913949
theorem B912419 : Blo 607294 912419 := bstep (se 1 (by rfl) ⟨684314, by rfl⟩ : syracuseStep 912419 = 1368629) B1368629
theorem B609315 : Blo 607294 609315 := bstep (se 1 (by rfl) ⟨456986, by rfl⟩ : syracuseStep 609315 = 913973) B913973
theorem B609331 : Blo 607294 609331 := bstep (se 1 (by rfl) ⟨456998, by rfl⟩ : syracuseStep 609331 = 913997) B913997
theorem B1371185 : Blo 607294 1371185 := bstep (se 2 (by rfl) ⟨514194, by rfl⟩ : syracuseStep 1371185 = 1028389) B1028389
theorem B912449 : Blo 607294 912449 := bstep (se 2 (by rfl) ⟨342168, by rfl⟩ : syracuseStep 912449 = 684337) B684337
theorem B609347 : Blo 607294 609347 := bstep (se 1 (by rfl) ⟨457010, by rfl⟩ : syracuseStep 609347 = 914021) B914021
theorem B1371203 : Blo 607294 1371203 := bstep (se 1 (by rfl) ⟨1028402, by rfl⟩ : syracuseStep 1371203 = 2056805) B2056805
theorem B912467 : Blo 607294 912467 := bstep (se 1 (by rfl) ⟨684350, by rfl⟩ : syracuseStep 912467 = 1368701) B1368701
theorem B609363 : Blo 607294 609363 := bstep (se 1 (by rfl) ⟨457022, by rfl⟩ : syracuseStep 609363 = 914045) B914045
theorem B609379 : Blo 607294 609379 := bstep (se 1 (by rfl) ⟨457034, by rfl⟩ : syracuseStep 609379 = 914069) B914069
theorem B912497 : Blo 607294 912497 := bstep (se 2 (by rfl) ⟨342186, by rfl⟩ : syracuseStep 912497 = 684373) B684373
theorem B1387633 : Blo 607294 1387633 := bstep (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) B1040725
theorem B609395 : Blo 607294 609395 := bstep (se 1 (by rfl) ⟨457046, by rfl⟩ : syracuseStep 609395 = 914093) B914093
theorem B2346097 : Blo 607294 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B1027201 : Blo 607294 1027201 := bstep (se 2 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 1027201 = 770401) B770401
theorem B912515 : Blo 607294 912515 := bstep (se 1 (by rfl) ⟨684386, by rfl⟩ : syracuseStep 912515 = 1368773) B1368773
theorem B609411 : Blo 607294 609411 := bstep (se 1 (by rfl) ⟨457058, by rfl⟩ : syracuseStep 609411 = 914117) B914117
theorem B1158275 : Blo 607294 1158275 := bstep (se 1 (by rfl) ⟨868706, by rfl⟩ : syracuseStep 1158275 = 1737413) B1737413
theorem B1543313 : Blo 607294 1543313 := bstep (se 2 (by rfl) ⟨578742, by rfl⟩ : syracuseStep 1543313 = 1157485) B1157485
theorem B609427 : Blo 607294 609427 := bstep (se 1 (by rfl) ⟨457070, by rfl⟩ : syracuseStep 609427 = 914141) B914141
theorem B912545 : Blo 607294 912545 := bstep (se 2 (by rfl) ⟨342204, by rfl⟩ : syracuseStep 912545 = 684409) B684409
theorem B1027235 : Blo 607294 1027235 := bstep (se 1 (by rfl) ⟨770426, by rfl⟩ : syracuseStep 1027235 = 1540853) B1540853
theorem B609443 : Blo 607294 609443 := bstep (se 1 (by rfl) ⟨457082, by rfl⟩ : syracuseStep 609443 = 914165) B914165
theorem B912563 : Blo 607294 912563 := bstep (se 1 (by rfl) ⟨684422, by rfl⟩ : syracuseStep 912563 = 1368845) B1368845
theorem B609459 : Blo 607294 609459 := bstep (se 1 (by rfl) ⟨457094, by rfl⟩ : syracuseStep 609459 = 914189) B914189
theorem B609475 : Blo 607294 609475 := bstep (se 1 (by rfl) ⟨457106, by rfl⟩ : syracuseStep 609475 = 914213) B914213
theorem B912593 : Blo 607294 912593 := bstep (se 2 (by rfl) ⟨342222, by rfl⟩ : syracuseStep 912593 = 684445) B684445
theorem B609491 : Blo 607294 609491 := bstep (se 1 (by rfl) ⟨457118, by rfl⟩ : syracuseStep 609491 = 914237) B914237
theorem B912611 : Blo 607294 912611 := bstep (se 1 (by rfl) ⟨684458, by rfl⟩ : syracuseStep 912611 = 1368917) B1368917
theorem B609507 : Blo 607294 609507 := bstep (se 1 (by rfl) ⟨457130, by rfl⟩ : syracuseStep 609507 = 914261) B914261
theorem B2198755 : Blo 607294 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B609523 : Blo 607294 609523 := bstep (se 1 (by rfl) ⟨457142, by rfl⟩ : syracuseStep 609523 = 914285) B914285
theorem B912641 : Blo 607294 912641 := bstep (se 2 (by rfl) ⟨342240, by rfl⟩ : syracuseStep 912641 = 684481) B684481
theorem B609539 : Blo 607294 609539 := bstep (se 1 (by rfl) ⟨457154, by rfl⟩ : syracuseStep 609539 = 914309) B914309
theorem B912659 : Blo 607294 912659 := bstep (se 1 (by rfl) ⟨684494, by rfl⟩ : syracuseStep 912659 = 1368989) B1368989
theorem B609555 : Blo 607294 609555 := bstep (se 1 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 609555 = 914333) B914333
theorem B1027363 : Blo 607294 1027363 := bstep (se 1 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 1027363 = 1541045) B1541045
theorem B609571 : Blo 607294 609571 := bstep (se 1 (by rfl) ⟨457178, by rfl⟩ : syracuseStep 609571 = 914357) B914357
theorem B912689 : Blo 607294 912689 := bstep (se 2 (by rfl) ⟨342258, by rfl⟩ : syracuseStep 912689 = 684517) B684517
theorem B609587 : Blo 607294 609587 := bstep (se 1 (by rfl) ⟨457190, by rfl⟩ : syracuseStep 609587 = 914381) B914381
theorem B912707 : Blo 607294 912707 := bstep (se 1 (by rfl) ⟨684530, by rfl⟩ : syracuseStep 912707 = 1369061) B1369061
theorem B609603 : Blo 607294 609603 := bstep (se 1 (by rfl) ⟨457202, by rfl⟩ : syracuseStep 609603 = 914405) B914405
theorem B2051405 : Blo 607294 2051405 := bstep (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) B769277
theorem B3009869 : Blo 607294 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B1371473 : Blo 607294 1371473 := bstep (se 2 (by rfl) ⟨514302, by rfl⟩ : syracuseStep 1371473 = 1028605) B1028605
theorem B683347 : Blo 607294 683347 := bstep (se 1 (by rfl) ⟨512510, by rfl⟩ : syracuseStep 683347 = 1025021) B1025021
theorem B609619 : Blo 607294 609619 := bstep (se 1 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 609619 = 914429) B914429
theorem B912737 : Blo 607294 912737 := bstep (se 2 (by rfl) ⟨342276, by rfl⟩ : syracuseStep 912737 = 684553) B684553
theorem B1371491 : Blo 607294 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B609635 : Blo 607294 609635 := bstep (se 1 (by rfl) ⟨457226, by rfl⟩ : syracuseStep 609635 = 914453) B914453
theorem B912755 : Blo 607294 912755 := bstep (se 1 (by rfl) ⟨684566, by rfl⟩ : syracuseStep 912755 = 1369133) B1369133
theorem B609651 : Blo 607294 609651 := bstep (se 1 (by rfl) ⟨457238, by rfl⟩ : syracuseStep 609651 = 914477) B914477
theorem B2051459 : Blo 607294 2051459 := bstep (se 1 (by rfl) ⟨1538594, by rfl⟩ : syracuseStep 2051459 = 3077189) B3077189
theorem B609667 : Blo 607294 609667 := bstep (se 1 (by rfl) ⟨457250, by rfl⟩ : syracuseStep 609667 = 914501) B914501
theorem B6950285 : Blo 607294 6950285 := bstep (se 3 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 6950285 = 2606357) B2606357
theorem B912785 : Blo 607294 912785 := bstep (se 2 (by rfl) ⟨342294, by rfl⟩ : syracuseStep 912785 = 684589) B684589
theorem B609683 : Blo 607294 609683 := bstep (se 1 (by rfl) ⟨457262, by rfl⟩ : syracuseStep 609683 = 914525) B914525
theorem B912803 : Blo 607294 912803 := bstep (se 1 (by rfl) ⟨684602, by rfl⟩ : syracuseStep 912803 = 1369205) B1369205
theorem B609699 : Blo 607294 609699 := bstep (se 1 (by rfl) ⟨457274, by rfl⟩ : syracuseStep 609699 = 914549) B914549
theorem B1158563 : Blo 607294 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B1732013 : Blo 607294 1732013 := bstep (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) B649505
theorem B1027505 : Blo 607294 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B609715 : Blo 607294 609715 := bstep (se 1 (by rfl) ⟨457286, by rfl⟩ : syracuseStep 609715 = 914573) B914573
theorem B912833 : Blo 607294 912833 := bstep (se 2 (by rfl) ⟨342312, by rfl⟩ : syracuseStep 912833 = 684625) B684625
theorem B609731 : Blo 607294 609731 := bstep (se 1 (by rfl) ⟨457298, by rfl⟩ : syracuseStep 609731 = 914597) B914597
theorem B732611 : Blo 607294 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B912851 : Blo 607294 912851 := bstep (se 1 (by rfl) ⟨684638, by rfl⟩ : syracuseStep 912851 = 1369277) B1369277
theorem B609747 : Blo 607294 609747 := bstep (se 1 (by rfl) ⟨457310, by rfl⟩ : syracuseStep 609747 = 914621) B914621
theorem B683491 : Blo 607294 683491 := bstep (se 1 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 683491 = 1025237) B1025237
theorem B609763 : Blo 607294 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B3075569 : Blo 607294 3075569 := bstep (se 2 (by rfl) ⟨1153338, by rfl⟩ : syracuseStep 3075569 = 2306677) B2306677
theorem B912881 : Blo 607294 912881 := bstep (se 2 (by rfl) ⟨342330, by rfl⟩ : syracuseStep 912881 = 684661) B684661
theorem B609779 : Blo 607294 609779 := bstep (se 1 (by rfl) ⟨457334, by rfl⟩ : syracuseStep 609779 = 914669) B914669
theorem B912899 : Blo 607294 912899 := bstep (se 1 (by rfl) ⟨684674, by rfl⟩ : syracuseStep 912899 = 1369349) B1369349
theorem B609795 : Blo 607294 609795 := bstep (se 1 (by rfl) ⟨457346, by rfl⟩ : syracuseStep 609795 = 914693) B914693
theorem B609811 : Blo 607294 609811 := bstep (se 1 (by rfl) ⟨457358, by rfl⟩ : syracuseStep 609811 = 914717) B914717
theorem B912929 : Blo 607294 912929 := bstep (se 2 (by rfl) ⟨342348, by rfl⟩ : syracuseStep 912929 = 684697) B684697
theorem B3517987 : Blo 607294 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B609827 : Blo 607294 609827 := bstep (se 1 (by rfl) ⟨457370, by rfl⟩ : syracuseStep 609827 = 914741) B914741
theorem B1027633 : Blo 607294 1027633 := bstep (se 2 (by rfl) ⟨385362, by rfl⟩ : syracuseStep 1027633 = 770725) B770725
theorem B912947 : Blo 607294 912947 := bstep (se 1 (by rfl) ⟨684710, by rfl⟩ : syracuseStep 912947 = 1369421) B1369421
theorem B609843 : Blo 607294 609843 := bstep (se 1 (by rfl) ⟨457382, by rfl⟩ : syracuseStep 609843 = 914765) B914765
theorem B609859 : Blo 607294 609859 := bstep (se 1 (by rfl) ⟨457394, by rfl⟩ : syracuseStep 609859 = 914789) B914789
theorem B912977 : Blo 607294 912977 := bstep (se 2 (by rfl) ⟨342366, by rfl⟩ : syracuseStep 912977 = 684733) B684733
theorem B1027667 : Blo 607294 1027667 := bstep (se 1 (by rfl) ⟨770750, by rfl⟩ : syracuseStep 1027667 = 1541501) B1541501
theorem B609875 : Blo 607294 609875 := bstep (se 1 (by rfl) ⟨457406, by rfl⟩ : syracuseStep 609875 = 914813) B914813
theorem B1732195 : Blo 607294 1732195 := bstep (se 1 (by rfl) ⟨1299146, by rfl⟩ : syracuseStep 1732195 = 2598293) B2598293
theorem B912995 : Blo 607294 912995 := bstep (se 1 (by rfl) ⟨684746, by rfl⟩ : syracuseStep 912995 = 1369493) B1369493
theorem B609891 : Blo 607294 609891 := bstep (se 1 (by rfl) ⟨457418, by rfl⟩ : syracuseStep 609891 = 914837) B914837
theorem B1371761 : Blo 607294 1371761 := bstep (se 2 (by rfl) ⟨514410, by rfl⟩ : syracuseStep 1371761 = 1028821) B1028821
theorem B683635 : Blo 607294 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B609907 : Blo 607294 609907 := bstep (se 1 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 609907 = 914861) B914861
theorem B913025 : Blo 607294 913025 := bstep (se 2 (by rfl) ⟨342384, by rfl⟩ : syracuseStep 913025 = 684769) B684769
theorem B1371779 : Blo 607294 1371779 := bstep (se 1 (by rfl) ⟨1028834, by rfl⟩ : syracuseStep 1371779 = 2057669) B2057669
theorem B609923 : Blo 607294 609923 := bstep (se 1 (by rfl) ⟨457442, by rfl⟩ : syracuseStep 609923 = 914885) B914885
theorem B2051729 : Blo 607294 2051729 := bstep (se 2 (by rfl) ⟨769398, by rfl⟩ : syracuseStep 2051729 = 1538797) B1538797
theorem B1732241 : Blo 607294 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B913043 : Blo 607294 913043 := bstep (se 1 (by rfl) ⟨684782, by rfl⟩ : syracuseStep 913043 = 1369565) B1369565
theorem B609939 : Blo 607294 609939 := bstep (se 1 (by rfl) ⟨457454, by rfl⟩ : syracuseStep 609939 = 914909) B914909
theorem B609955 : Blo 607294 609955 := bstep (se 1 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 609955 = 914933) B914933
theorem B913073 : Blo 607294 913073 := bstep (se 2 (by rfl) ⟨342402, by rfl⟩ : syracuseStep 913073 = 684805) B684805
theorem B609971 : Blo 607294 609971 := bstep (se 1 (by rfl) ⟨457478, by rfl⟩ : syracuseStep 609971 = 914957) B914957
theorem B913091 : Blo 607294 913091 := bstep (se 1 (by rfl) ⟨684818, by rfl⟩ : syracuseStep 913091 = 1369637) B1369637
theorem B609987 : Blo 607294 609987 := bstep (se 1 (by rfl) ⟨457490, by rfl⟩ : syracuseStep 609987 = 914981) B914981
theorem B1027795 : Blo 607294 1027795 := bstep (se 1 (by rfl) ⟨770846, by rfl⟩ : syracuseStep 1027795 = 1541693) B1541693
theorem B610003 : Blo 607294 610003 := bstep (se 1 (by rfl) ⟨457502, by rfl⟩ : syracuseStep 610003 = 915005) B915005
theorem B913121 : Blo 607294 913121 := bstep (se 2 (by rfl) ⟨342420, by rfl⟩ : syracuseStep 913121 = 684841) B684841
theorem B610019 : Blo 607294 610019 := bstep (se 1 (by rfl) ⟨457514, by rfl⟩ : syracuseStep 610019 = 915029) B915029
theorem B913139 : Blo 607294 913139 := bstep (se 1 (by rfl) ⟨684854, by rfl⟩ : syracuseStep 913139 = 1369709) B1369709
theorem B610035 : Blo 607294 610035 := bstep (se 1 (by rfl) ⟨457526, by rfl⟩ : syracuseStep 610035 = 915053) B915053
theorem B683779 : Blo 607294 683779 := bstep (se 1 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 683779 = 1025669) B1025669
theorem B610051 : Blo 607294 610051 := bstep (se 1 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 610051 = 915077) B915077
theorem B913169 : Blo 607294 913169 := bstep (se 2 (by rfl) ⟨342438, by rfl⟩ : syracuseStep 913169 = 684877) B684877
theorem B610067 : Blo 607294 610067 := bstep (se 1 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 610067 = 915101) B915101
theorem B913187 : Blo 607294 913187 := bstep (se 1 (by rfl) ⟨684890, by rfl⟩ : syracuseStep 913187 = 1369781) B1369781
theorem B610083 : Blo 607294 610083 := bstep (se 1 (by rfl) ⟨457562, by rfl⟩ : syracuseStep 610083 = 915125) B915125
theorem B610099 : Blo 607294 610099 := bstep (se 1 (by rfl) ⟨457574, by rfl⟩ : syracuseStep 610099 = 915149) B915149
theorem B913217 : Blo 607294 913217 := bstep (se 2 (by rfl) ⟨342456, by rfl⟩ : syracuseStep 913217 = 684913) B684913
theorem B610115 : Blo 607294 610115 := bstep (se 1 (by rfl) ⟨457586, by rfl⟩ : syracuseStep 610115 = 915173) B915173
theorem B913235 : Blo 607294 913235 := bstep (se 1 (by rfl) ⟨684926, by rfl⟩ : syracuseStep 913235 = 1369853) B1369853
theorem B618323 : Blo 607294 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B610131 : Blo 607294 610131 := bstep (se 1 (by rfl) ⟨457598, by rfl⟩ : syracuseStep 610131 = 915197) B915197
theorem B1027937 : Blo 607294 1027937 := bstep (se 2 (by rfl) ⟨385476, by rfl⟩ : syracuseStep 1027937 = 770953) B770953
theorem B610147 : Blo 607294 610147 := bstep (se 1 (by rfl) ⟨457610, by rfl⟩ : syracuseStep 610147 = 915221) B915221
theorem B913265 : Blo 607294 913265 := bstep (se 2 (by rfl) ⟨342474, by rfl⟩ : syracuseStep 913265 = 684949) B684949
theorem B610163 : Blo 607294 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B913283 : Blo 607294 913283 := bstep (se 1 (by rfl) ⟨684962, by rfl⟩ : syracuseStep 913283 = 1369925) B1369925
theorem B610179 : Blo 607294 610179 := bstep (se 1 (by rfl) ⟨457634, by rfl⟩ : syracuseStep 610179 = 915269) B915269
theorem B1372049 : Blo 607294 1372049 := bstep (se 2 (by rfl) ⟨514518, by rfl⟩ : syracuseStep 1372049 = 1029037) B1029037
theorem B683923 : Blo 607294 683923 := bstep (se 1 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 683923 = 1025885) B1025885
theorem B610195 : Blo 607294 610195 := bstep (se 1 (by rfl) ⟨457646, by rfl⟩ : syracuseStep 610195 = 915293) B915293
theorem B913313 : Blo 607294 913313 := bstep (se 2 (by rfl) ⟨342492, by rfl⟩ : syracuseStep 913313 = 684985) B684985
theorem B1372067 : Blo 607294 1372067 := bstep (se 1 (by rfl) ⟨1029050, by rfl⟩ : syracuseStep 1372067 = 2058101) B2058101
theorem B610211 : Blo 607294 610211 := bstep (se 1 (by rfl) ⟨457658, by rfl⟩ : syracuseStep 610211 = 915317) B915317
theorem B913331 : Blo 607294 913331 := bstep (se 1 (by rfl) ⟨684998, by rfl⟩ : syracuseStep 913331 = 1369997) B1369997
theorem B610227 : Blo 607294 610227 := bstep (se 1 (by rfl) ⟨457670, by rfl⟩ : syracuseStep 610227 = 915341) B915341
theorem B610243 : Blo 607294 610243 := bstep (se 1 (by rfl) ⟨457682, by rfl⟩ : syracuseStep 610243 = 915365) B915365
theorem B4386757 : Blo 607294 4386757 := bstep (se 4 (by rfl) ⟨411258, by rfl⟩ : syracuseStep 4386757 = 822517) B822517
theorem B3706829 : Blo 607294 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B913361 : Blo 607294 913361 := bstep (se 2 (by rfl) ⟨342510, by rfl⟩ : syracuseStep 913361 = 685021) B685021
theorem B610259 : Blo 607294 610259 := bstep (se 1 (by rfl) ⟨457694, by rfl⟩ : syracuseStep 610259 = 915389) B915389
theorem B1028065 : Blo 607294 1028065 := bstep (se 2 (by rfl) ⟨385524, by rfl⟩ : syracuseStep 1028065 = 771049) B771049
theorem B913379 : Blo 607294 913379 := bstep (se 1 (by rfl) ⟨685034, by rfl⟩ : syracuseStep 913379 = 1370069) B1370069
theorem B610275 : Blo 607294 610275 := bstep (se 1 (by rfl) ⟨457706, by rfl⟩ : syracuseStep 610275 = 915413) B915413
theorem B610291 : Blo 607294 610291 := bstep (se 1 (by rfl) ⟨457718, by rfl⟩ : syracuseStep 610291 = 915437) B915437
theorem B913409 : Blo 607294 913409 := bstep (se 2 (by rfl) ⟨342528, by rfl⟩ : syracuseStep 913409 = 685057) B685057
theorem B1028099 : Blo 607294 1028099 := bstep (se 1 (by rfl) ⟨771074, by rfl⟩ : syracuseStep 1028099 = 1542149) B1542149
theorem B667667 : Blo 607294 667667 := bstep (se 1 (by rfl) ⟨500750, by rfl⟩ : syracuseStep 667667 = 1001501) B1001501
theorem B913427 : Blo 607294 913427 := bstep (se 1 (by rfl) ⟨685070, by rfl⟩ : syracuseStep 913427 = 1370141) B1370141
theorem B684067 : Blo 607294 684067 := bstep (se 1 (by rfl) ⟨513050, by rfl⟩ : syracuseStep 684067 = 1026101) B1026101
theorem B651299 : Blo 607294 651299 := bstep (se 1 (by rfl) ⟨488474, by rfl⟩ : syracuseStep 651299 = 976949) B976949
theorem B913457 : Blo 607294 913457 := bstep (se 2 (by rfl) ⟨342546, by rfl⟩ : syracuseStep 913457 = 685093) B685093
theorem B913475 : Blo 607294 913475 := bstep (se 1 (by rfl) ⟨685106, by rfl⟩ : syracuseStep 913475 = 1370213) B1370213
theorem B1249361 : Blo 607294 1249361 := bstep (se 2 (by rfl) ⟨468510, by rfl⟩ : syracuseStep 1249361 = 937021) B937021
theorem B913505 : Blo 607294 913505 := bstep (se 2 (by rfl) ⟨342564, by rfl⟩ : syracuseStep 913505 = 685129) B685129
theorem B1544305 : Blo 607294 1544305 := bstep (se 2 (by rfl) ⟨579114, by rfl⟩ : syracuseStep 1544305 = 1158229) B1158229
theorem B913523 : Blo 607294 913523 := bstep (se 1 (by rfl) ⟨685142, by rfl⟩ : syracuseStep 913523 = 1370285) B1370285
theorem B1028227 : Blo 607294 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B913553 : Blo 607294 913553 := bstep (se 2 (by rfl) ⟨342582, by rfl⟩ : syracuseStep 913553 = 685165) B685165
theorem B913571 : Blo 607294 913571 := bstep (se 1 (by rfl) ⟨685178, by rfl⟩ : syracuseStep 913571 = 1370357) B1370357
theorem B2052269 : Blo 607294 2052269 := bstep (se 3 (by rfl) ⟨384800, by rfl⟩ : syracuseStep 2052269 = 769601) B769601
theorem B1372337 : Blo 607294 1372337 := bstep (se 2 (by rfl) ⟨514626, by rfl⟩ : syracuseStep 1372337 = 1029253) B1029253
theorem B684211 : Blo 607294 684211 := bstep (se 1 (by rfl) ⟨513158, by rfl⟩ : syracuseStep 684211 = 1026317) B1026317
theorem B913601 : Blo 607294 913601 := bstep (se 2 (by rfl) ⟨342600, by rfl⟩ : syracuseStep 913601 = 685201) B685201
theorem B1372355 : Blo 607294 1372355 := bstep (se 1 (by rfl) ⟨1029266, by rfl⟩ : syracuseStep 1372355 = 2058533) B2058533
theorem B913619 : Blo 607294 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B2052323 : Blo 607294 2052323 := bstep (se 1 (by rfl) ⟨1539242, by rfl⟩ : syracuseStep 2052323 = 3078485) B3078485
theorem B659683 : Blo 607294 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B913649 : Blo 607294 913649 := bstep (se 2 (by rfl) ⟨342618, by rfl⟩ : syracuseStep 913649 = 685237) B685237
theorem B913667 : Blo 607294 913667 := bstep (se 1 (by rfl) ⟨685250, by rfl⟩ : syracuseStep 913667 = 1370501) B1370501
theorem B1028369 : Blo 607294 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B913697 : Blo 607294 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B1716515 : Blo 607294 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B913715 : Blo 607294 913715 := bstep (se 1 (by rfl) ⟨685286, by rfl⟩ : syracuseStep 913715 = 1370573) B1370573
theorem B684355 : Blo 607294 684355 := bstep (se 1 (by rfl) ⟨513266, by rfl⟩ : syracuseStep 684355 = 1026533) B1026533
theorem B3461453 : Blo 607294 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B2085197 : Blo 607294 2085197 := bstep (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) B781949
theorem B913745 : Blo 607294 913745 := bstep (se 2 (by rfl) ⟨342654, by rfl⟩ : syracuseStep 913745 = 685309) B685309
theorem B692563 : Blo 607294 692563 := bstep (se 1 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 692563 = 1038845) B1038845
theorem B913763 : Blo 607294 913763 := bstep (se 1 (by rfl) ⟨685322, by rfl⟩ : syracuseStep 913763 = 1370645) B1370645
theorem B3297635 : Blo 607294 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B12513649 : Blo 607294 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B913793 : Blo 607294 913793 := bstep (se 2 (by rfl) ⟨342672, by rfl⟩ : syracuseStep 913793 = 685345) B685345
theorem B1544579 : Blo 607294 1544579 := bstep (se 1 (by rfl) ⟨1158434, by rfl⟩ : syracuseStep 1544579 = 2316869) B2316869
theorem B1028497 : Blo 607294 1028497 := bstep (se 2 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 1028497 = 771373) B771373
theorem B913811 : Blo 607294 913811 := bstep (se 1 (by rfl) ⟨685358, by rfl⟩ : syracuseStep 913811 = 1370717) B1370717
theorem B913841 : Blo 607294 913841 := bstep (se 2 (by rfl) ⟨342690, by rfl⟩ : syracuseStep 913841 = 685381) B685381
theorem B1028531 : Blo 607294 1028531 := bstep (se 1 (by rfl) ⟨771398, by rfl⟩ : syracuseStep 1028531 = 1542797) B1542797
theorem B913859 : Blo 607294 913859 := bstep (se 1 (by rfl) ⟨685394, by rfl⟩ : syracuseStep 913859 = 1370789) B1370789
theorem B1372625 : Blo 607294 1372625 := bstep (se 2 (by rfl) ⟨514734, by rfl⟩ : syracuseStep 1372625 = 1029469) B1029469
theorem B684499 : Blo 607294 684499 := bstep (se 1 (by rfl) ⟨513374, by rfl⟩ : syracuseStep 684499 = 1026749) B1026749
theorem B913889 : Blo 607294 913889 := bstep (se 2 (by rfl) ⟨342708, by rfl⟩ : syracuseStep 913889 = 685417) B685417
theorem B1372643 : Blo 607294 1372643 := bstep (se 1 (by rfl) ⟨1029482, by rfl⟩ : syracuseStep 1372643 = 2058965) B2058965
theorem B2052593 : Blo 607294 2052593 := bstep (se 2 (by rfl) ⟨769722, by rfl⟩ : syracuseStep 2052593 = 1539445) B1539445
theorem B913907 : Blo 607294 913907 := bstep (se 1 (by rfl) ⟨685430, by rfl⟩ : syracuseStep 913907 = 1370861) B1370861
theorem B1954307 : Blo 607294 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B913937 : Blo 607294 913937 := bstep (se 2 (by rfl) ⟨342726, by rfl⟩ : syracuseStep 913937 = 685453) B685453
theorem B913955 : Blo 607294 913955 := bstep (se 1 (by rfl) ⟨685466, by rfl⟩ : syracuseStep 913955 = 1370933) B1370933
theorem B1028659 : Blo 607294 1028659 := bstep (se 1 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 1028659 = 1542989) B1542989
theorem B913985 : Blo 607294 913985 := bstep (se 2 (by rfl) ⟨342744, by rfl⟩ : syracuseStep 913985 = 685489) B685489
theorem B1544771 : Blo 607294 1544771 := bstep (se 1 (by rfl) ⟨1158578, by rfl⟩ : syracuseStep 1544771 = 2317157) B2317157
theorem B914003 : Blo 607294 914003 := bstep (se 1 (by rfl) ⟨685502, by rfl⟩ : syracuseStep 914003 = 1371005) B1371005
theorem B684643 : Blo 607294 684643 := bstep (se 1 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 684643 = 1026965) B1026965
theorem B914033 : Blo 607294 914033 := bstep (se 2 (by rfl) ⟨342762, by rfl⟩ : syracuseStep 914033 = 685525) B685525
theorem B914051 : Blo 607294 914051 := bstep (se 1 (by rfl) ⟨685538, by rfl⟩ : syracuseStep 914051 = 1371077) B1371077
theorem B864913 : Blo 607294 864913 := bstep (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) B648685
theorem B914081 : Blo 607294 914081 := bstep (se 2 (by rfl) ⟨342780, by rfl⟩ : syracuseStep 914081 = 685561) B685561
theorem B914099 : Blo 607294 914099 := bstep (se 1 (by rfl) ⟨685574, by rfl⟩ : syracuseStep 914099 = 1371149) B1371149
theorem B1028801 : Blo 607294 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B1405649 : Blo 607294 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B914129 : Blo 607294 914129 := bstep (se 2 (by rfl) ⟨342798, by rfl⟩ : syracuseStep 914129 = 685597) B685597
theorem B914147 : Blo 607294 914147 := bstep (se 1 (by rfl) ⟨685610, by rfl⟩ : syracuseStep 914147 = 1371221) B1371221
theorem B6099697 : Blo 607294 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B1372913 : Blo 607294 1372913 := bstep (se 2 (by rfl) ⟨514842, by rfl⟩ : syracuseStep 1372913 = 1029685) B1029685
theorem B684787 : Blo 607294 684787 := bstep (se 1 (by rfl) ⟨513590, by rfl⟩ : syracuseStep 684787 = 1027181) B1027181
theorem B914177 : Blo 607294 914177 := bstep (se 2 (by rfl) ⟨342816, by rfl⟩ : syracuseStep 914177 = 685633) B685633
theorem B865027 : Blo 607294 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B1372931 : Blo 607294 1372931 := bstep (se 1 (by rfl) ⟨1029698, by rfl⟩ : syracuseStep 1372931 = 2059397) B2059397
theorem B914195 : Blo 607294 914195 := bstep (se 1 (by rfl) ⟨685646, by rfl⟩ : syracuseStep 914195 = 1371293) B1371293
theorem B914225 : Blo 607294 914225 := bstep (se 2 (by rfl) ⟨342834, by rfl⟩ : syracuseStep 914225 = 685669) B685669
theorem B1028929 : Blo 607294 1028929 := bstep (se 2 (by rfl) ⟨385848, by rfl⟩ : syracuseStep 1028929 = 771697) B771697
theorem B914243 : Blo 607294 914243 := bstep (se 1 (by rfl) ⟨685682, by rfl⟩ : syracuseStep 914243 = 1371365) B1371365
theorem B914273 : Blo 607294 914273 := bstep (se 2 (by rfl) ⟨342852, by rfl⟩ : syracuseStep 914273 = 685705) B685705
theorem B1028963 : Blo 607294 1028963 := bstep (se 1 (by rfl) ⟨771722, by rfl⟩ : syracuseStep 1028963 = 1543445) B1543445
theorem B914291 : Blo 607294 914291 := bstep (se 1 (by rfl) ⟨685718, by rfl⟩ : syracuseStep 914291 = 1371437) B1371437
theorem B684931 : Blo 607294 684931 := bstep (se 1 (by rfl) ⟨513698, by rfl⟩ : syracuseStep 684931 = 1027397) B1027397
theorem B914321 : Blo 607294 914321 := bstep (se 2 (by rfl) ⟨342870, by rfl⟩ : syracuseStep 914321 = 685741) B685741
theorem B3077027 : Blo 607294 3077027 := bstep (se 1 (by rfl) ⟨2307770, by rfl⟩ : syracuseStep 3077027 = 4615541) B4615541
theorem B914339 : Blo 607294 914339 := bstep (se 1 (by rfl) ⟨685754, by rfl⟩ : syracuseStep 914339 = 1371509) B1371509
theorem B914369 : Blo 607294 914369 := bstep (se 2 (by rfl) ⟨342888, by rfl⟩ : syracuseStep 914369 = 685777) B685777
theorem B2315213 : Blo 607294 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B914387 : Blo 607294 914387 := bstep (se 1 (by rfl) ⟨685790, by rfl⟩ : syracuseStep 914387 = 1371581) B1371581
theorem B1029091 : Blo 607294 1029091 := bstep (se 1 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 1029091 = 1543637) B1543637
theorem B5190641 : Blo 607294 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B914417 : Blo 607294 914417 := bstep (se 2 (by rfl) ⟨342906, by rfl⟩ : syracuseStep 914417 = 685813) B685813
theorem B914435 : Blo 607294 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B2053133 : Blo 607294 2053133 := bstep (se 3 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 2053133 = 769925) B769925
theorem B685075 : Blo 607294 685075 := bstep (se 1 (by rfl) ⟨513806, by rfl⟩ : syracuseStep 685075 = 1027613) B1027613
theorem B914465 : Blo 607294 914465 := bstep (se 2 (by rfl) ⟨342924, by rfl⟩ : syracuseStep 914465 = 685849) B685849
theorem B914483 : Blo 607294 914483 := bstep (se 1 (by rfl) ⟨685862, by rfl⟩ : syracuseStep 914483 = 1371725) B1371725
theorem B7025717 : Blo 607294 7025717 := bstep (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) B658661
theorem B2053187 : Blo 607294 2053187 := bstep (se 1 (by rfl) ⟨1539890, by rfl⟩ : syracuseStep 2053187 = 3079781) B3079781
theorem B1299523 : Blo 607294 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B1733699 : Blo 607294 1733699 := bstep (se 1 (by rfl) ⟨1300274, by rfl⟩ : syracuseStep 1733699 = 2600549) B2600549
theorem B2307149 : Blo 607294 2307149 := bstep (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) B865181
theorem B1315921 : Blo 607294 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B914513 : Blo 607294 914513 := bstep (se 2 (by rfl) ⟨342942, by rfl⟩ : syracuseStep 914513 = 685885) B685885
theorem B914531 : Blo 607294 914531 := bstep (se 1 (by rfl) ⟨685898, by rfl⟩ : syracuseStep 914531 = 1371797) B1371797
theorem B1029233 : Blo 607294 1029233 := bstep (se 2 (by rfl) ⟨385962, by rfl⟩ : syracuseStep 1029233 = 771925) B771925
theorem B914561 : Blo 607294 914561 := bstep (se 2 (by rfl) ⟨342960, by rfl⟩ : syracuseStep 914561 = 685921) B685921
theorem B914579 : Blo 607294 914579 := bstep (se 1 (by rfl) ⟨685934, by rfl⟩ : syracuseStep 914579 = 1371869) B1371869
theorem B685219 : Blo 607294 685219 := bstep (se 1 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 685219 = 1027829) B1027829
theorem B914609 : Blo 607294 914609 := bstep (se 2 (by rfl) ⟨342978, by rfl⟩ : syracuseStep 914609 = 685957) B685957
theorem B914627 : Blo 607294 914627 := bstep (se 1 (by rfl) ⟨685970, by rfl⟩ : syracuseStep 914627 = 1371941) B1371941
theorem B914657 : Blo 607294 914657 := bstep (se 2 (by rfl) ⟨342996, by rfl⟩ : syracuseStep 914657 = 685993) B685993
theorem B3462385 : Blo 607294 3462385 := bstep (se 2 (by rfl) ⟨1298394, by rfl⟩ : syracuseStep 3462385 = 2596789) B2596789
theorem B1029361 : Blo 607294 1029361 := bstep (se 2 (by rfl) ⟨386010, by rfl⟩ : syracuseStep 1029361 = 772021) B772021
theorem B914675 : Blo 607294 914675 := bstep (se 1 (by rfl) ⟨686006, by rfl⟩ : syracuseStep 914675 = 1372013) B1372013
theorem B4617485 : Blo 607294 4617485 := bstep (se 3 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 4617485 = 1731557) B1731557
theorem B914705 : Blo 607294 914705 := bstep (se 2 (by rfl) ⟨343014, by rfl⟩ : syracuseStep 914705 = 686029) B686029
theorem B1029395 : Blo 607294 1029395 := bstep (se 1 (by rfl) ⟨772046, by rfl⟩ : syracuseStep 1029395 = 1544093) B1544093
theorem B13137173 : Blo 607294 13137173 := bstep (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) B615805
theorem B2463011 : Blo 607294 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B914723 : Blo 607294 914723 := bstep (se 1 (by rfl) ⟨686042, by rfl⟩ : syracuseStep 914723 = 1372085) B1372085
theorem B685363 : Blo 607294 685363 := bstep (se 1 (by rfl) ⟨514022, by rfl⟩ : syracuseStep 685363 = 1028045) B1028045
theorem B914753 : Blo 607294 914753 := bstep (se 2 (by rfl) ⟨343032, by rfl⟩ : syracuseStep 914753 = 686065) B686065
theorem B2053457 : Blo 607294 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B914771 : Blo 607294 914771 := bstep (se 1 (by rfl) ⟨686078, by rfl⟩ : syracuseStep 914771 = 1372157) B1372157
theorem B914801 : Blo 607294 914801 := bstep (se 2 (by rfl) ⟨343050, by rfl⟩ : syracuseStep 914801 = 686101) B686101
theorem B914819 : Blo 607294 914819 := bstep (se 1 (by rfl) ⟨686114, by rfl⟩ : syracuseStep 914819 = 1372229) B1372229
theorem B1029523 : Blo 607294 1029523 := bstep (se 1 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 1029523 = 1544285) B1544285
theorem B914849 : Blo 607294 914849 := bstep (se 2 (by rfl) ⟨343068, by rfl⟩ : syracuseStep 914849 = 686137) B686137
theorem B914867 : Blo 607294 914867 := bstep (se 1 (by rfl) ⟨686150, by rfl⟩ : syracuseStep 914867 = 1372301) B1372301
theorem B824755 : Blo 607294 824755 := bstep (se 1 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 824755 = 1237133) B1237133
theorem B685507 : Blo 607294 685507 := bstep (se 1 (by rfl) ⟨514130, by rfl⟩ : syracuseStep 685507 = 1028261) B1028261
theorem B914897 : Blo 607294 914897 := bstep (se 2 (by rfl) ⟨343086, by rfl⟩ : syracuseStep 914897 = 686173) B686173
theorem B914915 : Blo 607294 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B914945 : Blo 607294 914945 := bstep (se 2 (by rfl) ⟨343104, by rfl⟩ : syracuseStep 914945 = 686209) B686209
theorem B914963 : Blo 607294 914963 := bstep (se 1 (by rfl) ⟨686222, by rfl⟩ : syracuseStep 914963 = 1372445) B1372445
theorem B1029665 : Blo 607294 1029665 := bstep (se 2 (by rfl) ⟨386124, by rfl⟩ : syracuseStep 1029665 = 772249) B772249
theorem B914993 : Blo 607294 914993 := bstep (se 2 (by rfl) ⟨343122, by rfl⟩ : syracuseStep 914993 = 686245) B686245
theorem B915011 : Blo 607294 915011 := bstep (se 1 (by rfl) ⟨686258, by rfl⟩ : syracuseStep 915011 = 1372517) B1372517
theorem B685651 : Blo 607294 685651 := bstep (se 1 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 685651 = 1028477) B1028477
theorem B915041 : Blo 607294 915041 := bstep (se 2 (by rfl) ⟨343140, by rfl⟩ : syracuseStep 915041 = 686281) B686281
theorem B3085937 : Blo 607294 3085937 := bstep (se 2 (by rfl) ⟨1157226, by rfl⟩ : syracuseStep 3085937 = 2314453) B2314453
theorem B915059 : Blo 607294 915059 := bstep (se 1 (by rfl) ⟨686294, by rfl⟩ : syracuseStep 915059 = 1372589) B1372589
theorem B4159117 : Blo 607294 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B915089 : Blo 607294 915089 := bstep (se 2 (by rfl) ⟨343158, by rfl⟩ : syracuseStep 915089 = 686317) B686317
theorem B1029793 : Blo 607294 1029793 := bstep (se 2 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 1029793 = 772345) B772345
theorem B915107 : Blo 607294 915107 := bstep (se 1 (by rfl) ⟨686330, by rfl⟩ : syracuseStep 915107 = 1372661) B1372661
theorem B915137 : Blo 607294 915137 := bstep (se 2 (by rfl) ⟨343176, by rfl⟩ : syracuseStep 915137 = 686353) B686353
theorem B6944453 : Blo 607294 6944453 := bstep (se 4 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 6944453 = 1302085) B1302085
theorem B1029827 : Blo 607294 1029827 := bstep (se 1 (by rfl) ⟨772370, by rfl⟩ : syracuseStep 1029827 = 1544741) B1544741
theorem B3077837 : Blo 607294 3077837 := bstep (se 3 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 3077837 = 1154189) B1154189
theorem B2059235 : Blo 607294 2059235 := bstep (se 1 (by rfl) ⟨1544426, by rfl⟩ : syracuseStep 2059235 = 3088853) B3088853
theorem B915155 : Blo 607294 915155 := bstep (se 1 (by rfl) ⟨686366, by rfl⟩ : syracuseStep 915155 = 1372733) B1372733
theorem B685795 : Blo 607294 685795 := bstep (se 1 (by rfl) ⟨514346, by rfl⟩ : syracuseStep 685795 = 1028693) B1028693
theorem B915185 : Blo 607294 915185 := bstep (se 2 (by rfl) ⟨343194, by rfl⟩ : syracuseStep 915185 = 686389) B686389
theorem B915203 : Blo 607294 915203 := bstep (se 1 (by rfl) ⟨686402, by rfl⟩ : syracuseStep 915203 = 1372805) B1372805
theorem B3610403 : Blo 607294 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B915233 : Blo 607294 915233 := bstep (se 2 (by rfl) ⟨343212, by rfl⟩ : syracuseStep 915233 = 686425) B686425
theorem B3389219 : Blo 607294 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B915251 : Blo 607294 915251 := bstep (se 1 (by rfl) ⟨686438, by rfl⟩ : syracuseStep 915251 = 1372877) B1372877
theorem B1849169 : Blo 607294 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B915281 : Blo 607294 915281 := bstep (se 2 (by rfl) ⟨343230, by rfl⟩ : syracuseStep 915281 = 686461) B686461
theorem B915299 : Blo 607294 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B2053997 : Blo 607294 2053997 := bstep (se 3 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 2053997 = 770249) B770249
theorem B2307953 : Blo 607294 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B685939 : Blo 607294 685939 := bstep (se 1 (by rfl) ⟨514454, by rfl⟩ : syracuseStep 685939 = 1028909) B1028909
theorem B915329 : Blo 607294 915329 := bstep (se 2 (by rfl) ⟨343248, by rfl⟩ : syracuseStep 915329 = 686497) B686497
theorem B1537937 : Blo 607294 1537937 := bstep (se 2 (by rfl) ⟨576726, by rfl⟩ : syracuseStep 1537937 = 1153453) B1153453
theorem B1300369 : Blo 607294 1300369 := bstep (se 2 (by rfl) ⟨487638, by rfl⟩ : syracuseStep 1300369 = 975277) B975277
theorem B915347 : Blo 607294 915347 := bstep (se 1 (by rfl) ⟨686510, by rfl⟩ : syracuseStep 915347 = 1373021) B1373021
theorem B2054051 : Blo 607294 2054051 := bstep (se 1 (by rfl) ⟨1540538, by rfl⟩ : syracuseStep 2054051 = 3081077) B3081077
theorem B915377 : Blo 607294 915377 := bstep (se 2 (by rfl) ⟨343266, by rfl⟩ : syracuseStep 915377 = 686533) B686533
theorem B1537987 : Blo 607294 1537987 := bstep (se 1 (by rfl) ⟨1153490, by rfl⟩ : syracuseStep 1537987 = 2306981) B2306981
theorem B915395 : Blo 607294 915395 := bstep (se 1 (by rfl) ⟨686546, by rfl⟩ : syracuseStep 915395 = 1373093) B1373093
theorem B915425 : Blo 607294 915425 := bstep (se 2 (by rfl) ⟨343284, by rfl⟩ : syracuseStep 915425 = 686569) B686569
theorem B972785 : Blo 607294 972785 := bstep (se 2 (by rfl) ⟨364794, by rfl⟩ : syracuseStep 972785 = 729589) B729589
theorem B686083 : Blo 607294 686083 := bstep (se 1 (by rfl) ⟨514562, by rfl⟩ : syracuseStep 686083 = 1029125) B1029125
theorem B923665 : Blo 607294 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B866371 : Blo 607294 866371 := bstep (se 1 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 866371 = 1299557) B1299557
theorem B1538129 : Blo 607294 1538129 := bstep (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) B1153597
theorem B5544035 : Blo 607294 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B686227 : Blo 607294 686227 := bstep (se 1 (by rfl) ⟨514670, by rfl⟩ : syracuseStep 686227 = 1029341) B1029341
theorem B1153187 : Blo 607294 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B2054321 : Blo 607294 2054321 := bstep (se 2 (by rfl) ⟨770370, by rfl⟩ : syracuseStep 2054321 = 1540741) B1540741
theorem B2087117 : Blo 607294 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B2603249 : Blo 607294 2603249 := bstep (se 2 (by rfl) ⟨976218, by rfl⟩ : syracuseStep 2603249 = 1952437) B1952437
theorem B973073 : Blo 607294 973073 := bstep (se 2 (by rfl) ⟨364902, by rfl⟩ : syracuseStep 973073 = 729805) B729805
theorem B1734929 : Blo 607294 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B686371 : Blo 607294 686371 := bstep (se 1 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 686371 = 1029557) B1029557
theorem B5626181 : Blo 607294 5626181 := bstep (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) B1054909
theorem B2595149 : Blo 607294 2595149 := bstep (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) B973181
theorem B2595185 : Blo 607294 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B1030577 : Blo 607294 1030577 := bstep (se 2 (by rfl) ⟨386466, by rfl⟩ : syracuseStep 1030577 = 772933) B772933
theorem B686515 : Blo 607294 686515 := bstep (se 1 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 686515 = 1029773) B1029773
theorem B3897827 : Blo 607294 3897827 := bstep (se 1 (by rfl) ⟨2923370, by rfl⟩ : syracuseStep 3897827 = 5846741) B5846741
theorem B2308621 : Blo 607294 2308621 := bstep (se 3 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 2308621 = 865733) B865733
theorem B1366577 : Blo 607294 1366577 := bstep (se 2 (by rfl) ⟨512466, by rfl⟩ : syracuseStep 1366577 = 1024933) B1024933
theorem B1366595 : Blo 607294 1366595 := bstep (se 1 (by rfl) ⟨1024946, by rfl⟩ : syracuseStep 1366595 = 2049893) B2049893
theorem B3463843 : Blo 607294 3463843 := bstep (se 1 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 3463843 = 5195765) B5195765
theorem B1948337 : Blo 607294 1948337 := bstep (se 2 (by rfl) ⟨730626, by rfl⟩ : syracuseStep 1948337 = 1461253) B1461253
theorem B2054861 : Blo 607294 2054861 := bstep (se 3 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 2054861 = 770573) B770573
theorem B2923235 : Blo 607294 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B11107043 : Blo 607294 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B2054915 : Blo 607294 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B1645357 : Blo 607294 1645357 := bstep (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) B617009
theorem B1366865 : Blo 607294 1366865 := bstep (se 2 (by rfl) ⟨512574, by rfl⟩ : syracuseStep 1366865 = 1025149) B1025149
theorem B1366883 : Blo 607294 1366883 := bstep (se 1 (by rfl) ⟨1025162, by rfl⟩ : syracuseStep 1366883 = 2050325) B2050325
theorem B2923427 : Blo 607294 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B2194445 : Blo 607294 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B2055185 : Blo 607294 2055185 := bstep (se 2 (by rfl) ⟨770694, by rfl⟩ : syracuseStep 2055185 = 1541389) B1541389
theorem B2059505 : Blo 607294 2059505 := bstep (se 2 (by rfl) ⟨772314, by rfl⟩ : syracuseStep 2059505 = 1544629) B1544629
theorem B1154083 : Blo 607294 1154083 := bstep (se 1 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 1154083 = 1731125) B1731125
theorem B3087395 : Blo 607294 3087395 := bstep (se 1 (by rfl) ⟨2315546, by rfl⟩ : syracuseStep 3087395 = 4631093) B4631093
theorem B973873 : Blo 607294 973873 := bstep (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) B730405
theorem B1539121 : Blo 607294 1539121 := bstep (se 2 (by rfl) ⟨577170, by rfl⟩ : syracuseStep 1539121 = 1154341) B1154341
theorem B1850435 : Blo 607294 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B2530381 : Blo 607294 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B2849869 : Blo 607294 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1367153 : Blo 607294 1367153 := bstep (se 2 (by rfl) ⟨512682, by rfl⟩ : syracuseStep 1367153 = 1025365) B1025365
theorem B1367171 : Blo 607294 1367171 := bstep (se 1 (by rfl) ⟨1025378, by rfl⟩ : syracuseStep 1367171 = 2050757) B2050757
theorem B2784397 : Blo 607294 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B769171 : Blo 607294 769171 := bstep (se 1 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 769171 = 1153757) B1153757
theorem B3464369 : Blo 607294 3464369 := bstep (se 2 (by rfl) ⟨1299138, by rfl⟩ : syracuseStep 3464369 = 2598277) B2598277
theorem B867505 : Blo 607294 867505 := bstep (se 2 (by rfl) ⟨325314, by rfl⟩ : syracuseStep 867505 = 650629) B650629
theorem B1154243 : Blo 607294 1154243 := bstep (se 1 (by rfl) ⟨865682, by rfl⟩ : syracuseStep 1154243 = 1731365) B1731365
theorem B4390129 : Blo 607294 4390129 := bstep (se 2 (by rfl) ⟨1646298, by rfl⟩ : syracuseStep 4390129 = 3292597) B3292597
theorem B769267 : Blo 607294 769267 := bstep (se 1 (by rfl) ⟨576950, by rfl⟩ : syracuseStep 769267 = 1153901) B1153901
theorem B867601 : Blo 607294 867601 := bstep (se 2 (by rfl) ⟨325350, by rfl⟩ : syracuseStep 867601 = 650701) B650701
theorem B2309411 : Blo 607294 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B1539395 : Blo 607294 1539395 := bstep (se 1 (by rfl) ⟨1154546, by rfl⟩ : syracuseStep 1539395 = 2309093) B2309093
theorem B1949027 : Blo 607294 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B1367441 : Blo 607294 1367441 := bstep (se 2 (by rfl) ⟨512790, by rfl⟩ : syracuseStep 1367441 = 1025581) B1025581
theorem B1367459 : Blo 607294 1367459 := bstep (se 1 (by rfl) ⟨1025594, by rfl⟩ : syracuseStep 1367459 = 2051189) B2051189
theorem B835043 : Blo 607294 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B1539587 : Blo 607294 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B3120653 : Blo 607294 3120653 := bstep (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) B1170245
theorem B2055725 : Blo 607294 2055725 := bstep (se 3 (by rfl) ⟨385448, by rfl⟩ : syracuseStep 2055725 = 770897) B770897
theorem B990787 : Blo 607294 990787 := bstep (se 1 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 990787 = 1486181) B1486181
theorem B4611653 : Blo 607294 4611653 := bstep (se 4 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 4611653 = 864685) B864685
theorem B2055779 : Blo 607294 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B2817677 : Blo 607294 2817677 := bstep (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) B1056629
theorem B1367729 : Blo 607294 1367729 := bstep (se 2 (by rfl) ⟨512898, by rfl⟩ : syracuseStep 1367729 = 1025797) B1025797
theorem B1367747 : Blo 607294 1367747 := bstep (se 1 (by rfl) ⟨1025810, by rfl⟩ : syracuseStep 1367747 = 2051621) B2051621
theorem B1736387 : Blo 607294 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B31571669 : Blo 607294 31571669 := bstep (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) B739961
theorem B769763 : Blo 607294 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B1302257 : Blo 607294 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B868097 : Blo 607294 868097 := bstep (se 2 (by rfl) ⟨325536, by rfl⟩ : syracuseStep 868097 = 651073) B651073
theorem B11280181 : Blo 607294 11280181 := bstep (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) B1057517
theorem B3088205 : Blo 607294 3088205 := bstep (se 3 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 3088205 = 1158077) B1158077
theorem B2056049 : Blo 607294 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B2058641 : Blo 607294 2058641 := bstep (se 2 (by rfl) ⟨771990, by rfl⟩ : syracuseStep 2058641 = 1543981) B1543981
theorem B3710861 : Blo 607294 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B2310065 : Blo 607294 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B4440005 : Blo 607294 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B1368017 : Blo 607294 1368017 := bstep (se 2 (by rfl) ⟨513006, by rfl⟩ : syracuseStep 1368017 = 1026013) B1026013
theorem B1368035 : Blo 607294 1368035 := bstep (se 1 (by rfl) ⟨1026026, by rfl⟩ : syracuseStep 1368035 = 2052053) B2052053
theorem B1368089 : Blo 607294 1368089 := bstep (se 2 (by rfl) ⟨513033, by rfl⟩ : syracuseStep 1368089 = 1026067) B1026067
theorem B3080267 : Blo 607294 3080267 := bstep (se 1 (by rfl) ⟨2310200, by rfl⟩ : syracuseStep 3080267 = 4620401) B4620401
theorem B1949771 : Blo 607294 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B1155161 : Blo 607294 1155161 := bstep (se 2 (by rfl) ⟨433185, by rfl⟩ : syracuseStep 1155161 = 866371) B866371
theorem B1736797 : Blo 607294 1736797 := bstep (se 3 (by rfl) ⟨325649, by rfl⟩ : syracuseStep 1736797 = 651299) B651299
theorem B1368179 : Blo 607294 1368179 := bstep (se 1 (by rfl) ⟨1026134, by rfl⟩ : syracuseStep 1368179 = 2052269) B2052269
theorem B18735245 : Blo 607294 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B1368215 : Blo 607294 1368215 := bstep (se 1 (by rfl) ⟨1026161, by rfl⟩ : syracuseStep 1368215 = 2052323) B2052323
theorem B2474135 : Blo 607294 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B5193989 : Blo 607294 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B1540417 : Blo 607294 1540417 := bstep (se 2 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 1540417 = 1155313) B1155313
theorem B1368395 : Blo 607294 1368395 := bstep (se 1 (by rfl) ⟨1026296, by rfl⟩ : syracuseStep 1368395 = 2052593) B2052593
theorem B35553649 : Blo 607294 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B1368449 : Blo 607294 1368449 := bstep (se 2 (by rfl) ⟨513168, by rfl⟩ : syracuseStep 1368449 = 1026337) B1026337
theorem B2310551 : Blo 607294 2310551 := bstep (se 1 (by rfl) ⟨1732913, by rfl⟩ : syracuseStep 2310551 = 3465827) B3465827
theorem B1737139 : Blo 607294 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B4612625 : Blo 607294 4612625 := bstep (se 2 (by rfl) ⟨1729734, by rfl⟩ : syracuseStep 4612625 = 3459469) B3459469
theorem B975385 : Blo 607294 975385 := bstep (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) B731539
theorem B10551883 : Blo 607294 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B1368665 : Blo 607294 1368665 := bstep (se 2 (by rfl) ⟨513249, by rfl⟩ : syracuseStep 1368665 = 1026499) B1026499
theorem B3293827 : Blo 607294 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B1371095 : Blo 607294 1371095 := bstep (se 1 (by rfl) ⟨1028321, by rfl⟩ : syracuseStep 1371095 = 2056643) B2056643
theorem B5210801 : Blo 607294 5210801 := bstep (se 2 (by rfl) ⟨1954050, by rfl⟩ : syracuseStep 5210801 = 3908101) B3908101
theorem B1368755 : Blo 607294 1368755 := bstep (se 1 (by rfl) ⟨1026566, by rfl⟩ : syracuseStep 1368755 = 2053133) B2053133
theorem B1368791 : Blo 607294 1368791 := bstep (se 1 (by rfl) ⟨1026593, by rfl⟩ : syracuseStep 1368791 = 2053187) B2053187
theorem B1155799 : Blo 607294 1155799 := bstep (se 1 (by rfl) ⟨866849, by rfl⟩ : syracuseStep 1155799 = 1733699) B1733699
theorem B1098455 : Blo 607294 1098455 := bstep (se 1 (by rfl) ⟨823841, by rfl⟩ : syracuseStep 1098455 = 1647683) B1647683
theorem B16646897 : Blo 607294 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B8758115 : Blo 607294 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B6595445 : Blo 607294 6595445 := bstep (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) B618323
theorem B1368971 : Blo 607294 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B3900311 : Blo 607294 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B1541015 : Blo 607294 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B1369025 : Blo 607294 1369025 := bstep (se 2 (by rfl) ⟨513384, by rfl⟩ : syracuseStep 1369025 = 1026769) B1026769
theorem B607307 : Blo 607294 607307 := bstep (se 1 (by rfl) ⟨455480, by rfl⟩ : syracuseStep 607307 = 910961) B910961
theorem B2057291 : Blo 607294 2057291 := bstep (se 1 (by rfl) ⟨1542968, by rfl⟩ : syracuseStep 2057291 = 3085937) B3085937
theorem B607319 : Blo 607294 607319 := bstep (se 1 (by rfl) ⟨455489, by rfl⟩ : syracuseStep 607319 = 910979) B910979
theorem B3089501 : Blo 607294 3089501 := bstep (se 3 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 3089501 = 1158563) B1158563
theorem B5637221 : Blo 607294 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B607339 : Blo 607294 607339 := bstep (se 1 (by rfl) ⟨455504, by rfl⟩ : syracuseStep 607339 = 911009) B911009
theorem B607351 : Blo 607294 607351 := bstep (se 1 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 607351 = 911027) B911027
theorem B4629635 : Blo 607294 4629635 := bstep (se 1 (by rfl) ⟨3472226, by rfl⟩ : syracuseStep 4629635 = 6944453) B6944453
theorem B607371 : Blo 607294 607371 := bstep (se 1 (by rfl) ⟨455528, by rfl⟩ : syracuseStep 607371 = 911057) B911057
theorem B771211 : Blo 607294 771211 := bstep (se 1 (by rfl) ⟨578408, by rfl⟩ : syracuseStep 771211 = 1156817) B1156817
theorem B607383 : Blo 607294 607383 := bstep (se 1 (by rfl) ⟨455537, by rfl⟩ : syracuseStep 607383 = 911075) B911075
theorem B1369241 : Blo 607294 1369241 := bstep (se 2 (by rfl) ⟨513465, by rfl⟩ : syracuseStep 1369241 = 1026931) B1026931
theorem B607403 : Blo 607294 607403 := bstep (se 1 (by rfl) ⟨455552, by rfl⟩ : syracuseStep 607403 = 911105) B911105
theorem B1459379 : Blo 607294 1459379 := bstep (se 1 (by rfl) ⟨1094534, by rfl⟩ : syracuseStep 1459379 = 2189069) B2189069
theorem B607415 : Blo 607294 607415 := bstep (se 1 (by rfl) ⟨455561, by rfl⟩ : syracuseStep 607415 = 911123) B911123
theorem B607435 : Blo 607294 607435 := bstep (se 1 (by rfl) ⟨455576, by rfl⟩ : syracuseStep 607435 = 911153) B911153
theorem B607447 : Blo 607294 607447 := bstep (se 1 (by rfl) ⟨455585, by rfl⟩ : syracuseStep 607447 = 911171) B911171
theorem B607467 : Blo 607294 607467 := bstep (se 1 (by rfl) ⟨455600, by rfl⟩ : syracuseStep 607467 = 911201) B911201
theorem B1369331 : Blo 607294 1369331 := bstep (se 1 (by rfl) ⟨1026998, by rfl⟩ : syracuseStep 1369331 = 2053997) B2053997
theorem B607479 : Blo 607294 607479 := bstep (se 1 (by rfl) ⟨455609, by rfl⟩ : syracuseStep 607479 = 911219) B911219
theorem B32531717 : Blo 607294 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B607499 : Blo 607294 607499 := bstep (se 1 (by rfl) ⟨455624, by rfl⟩ : syracuseStep 607499 = 911249) B911249
theorem B1025291 : Blo 607294 1025291 := bstep (se 1 (by rfl) ⟨768968, by rfl⟩ : syracuseStep 1025291 = 1537937) B1537937
theorem B607511 : Blo 607294 607511 := bstep (se 1 (by rfl) ⟨455633, by rfl⟩ : syracuseStep 607511 = 911267) B911267
theorem B1369367 : Blo 607294 1369367 := bstep (se 1 (by rfl) ⟨1027025, by rfl⟩ : syracuseStep 1369367 = 2054051) B2054051
theorem B607531 : Blo 607294 607531 := bstep (se 1 (by rfl) ⟨455648, by rfl⟩ : syracuseStep 607531 = 911297) B911297
theorem B607543 : Blo 607294 607543 := bstep (se 1 (by rfl) ⟨455657, by rfl⟩ : syracuseStep 607543 = 911315) B911315
theorem B648523 : Blo 607294 648523 := bstep (se 1 (by rfl) ⟨486392, by rfl⟩ : syracuseStep 648523 = 972785) B972785
theorem B607563 : Blo 607294 607563 := bstep (se 1 (by rfl) ⟨455672, by rfl⟩ : syracuseStep 607563 = 911345) B911345
theorem B607575 : Blo 607294 607575 := bstep (se 1 (by rfl) ⟨455681, by rfl⟩ : syracuseStep 607575 = 911363) B911363
theorem B2057561 : Blo 607294 2057561 := bstep (se 2 (by rfl) ⟨771585, by rfl⟩ : syracuseStep 2057561 = 1543171) B1543171
theorem B5211485 : Blo 607294 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B607595 : Blo 607294 607595 := bstep (se 1 (by rfl) ⟨455696, by rfl⟩ : syracuseStep 607595 = 911393) B911393
theorem B607607 : Blo 607294 607607 := bstep (se 1 (by rfl) ⟨455705, by rfl⟩ : syracuseStep 607607 = 911411) B911411
theorem B607627 : Blo 607294 607627 := bstep (se 1 (by rfl) ⟨455720, by rfl⟩ : syracuseStep 607627 = 911441) B911441
theorem B1025419 : Blo 607294 1025419 := bstep (se 1 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 1025419 = 1538129) B1538129
theorem B607639 : Blo 607294 607639 := bstep (se 1 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 607639 = 911459) B911459
theorem B3696023 : Blo 607294 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B607659 : Blo 607294 607659 := bstep (se 1 (by rfl) ⟨455744, by rfl⟩ : syracuseStep 607659 = 911489) B911489
theorem B607671 : Blo 607294 607671 := bstep (se 1 (by rfl) ⟨455753, by rfl⟩ : syracuseStep 607671 = 911507) B911507
theorem B1754561 : Blo 607294 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B607691 : Blo 607294 607691 := bstep (se 1 (by rfl) ⟨455768, by rfl⟩ : syracuseStep 607691 = 911537) B911537
theorem B1369547 : Blo 607294 1369547 := bstep (se 1 (by rfl) ⟨1027160, by rfl⟩ : syracuseStep 1369547 = 2054321) B2054321
theorem B607703 : Blo 607294 607703 := bstep (se 1 (by rfl) ⟨455777, by rfl⟩ : syracuseStep 607703 = 911555) B911555
theorem B607723 : Blo 607294 607723 := bstep (se 1 (by rfl) ⟨455792, by rfl⟩ : syracuseStep 607723 = 911585) B911585
theorem B607735 : Blo 607294 607735 := bstep (se 1 (by rfl) ⟨455801, by rfl⟩ : syracuseStep 607735 = 911603) B911603
theorem B1369601 : Blo 607294 1369601 := bstep (se 2 (by rfl) ⟨513600, by rfl⟩ : syracuseStep 1369601 = 1027201) B1027201
theorem B607755 : Blo 607294 607755 := bstep (se 1 (by rfl) ⟨455816, by rfl⟩ : syracuseStep 607755 = 911633) B911633
theorem B1156619 : Blo 607294 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B3712529 : Blo 607294 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B607767 : Blo 607294 607767 := bstep (se 1 (by rfl) ⟨455825, by rfl⟩ : syracuseStep 607767 = 911651) B911651
theorem B1025561 : Blo 607294 1025561 := bstep (se 2 (by rfl) ⟨384585, by rfl⟩ : syracuseStep 1025561 = 769171) B769171
theorem B4621859 : Blo 607294 4621859 := bstep (se 1 (by rfl) ⟨3466394, by rfl⟩ : syracuseStep 4621859 = 6932789) B6932789
theorem B607787 : Blo 607294 607787 := bstep (se 1 (by rfl) ⟨455840, by rfl⟩ : syracuseStep 607787 = 911681) B911681
theorem B1730099 : Blo 607294 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B1951283 : Blo 607294 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B607799 : Blo 607294 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B1156673 : Blo 607294 1156673 := bstep (se 2 (by rfl) ⟨433752, by rfl⟩ : syracuseStep 1156673 = 867505) B867505
theorem B1730123 : Blo 607294 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B607819 : Blo 607294 607819 := bstep (se 1 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 607819 = 911729) B911729
theorem B607831 : Blo 607294 607831 := bstep (se 1 (by rfl) ⟨455873, by rfl⟩ : syracuseStep 607831 = 911747) B911747
theorem B607851 : Blo 607294 607851 := bstep (se 1 (by rfl) ⟨455888, by rfl⟩ : syracuseStep 607851 = 911777) B911777
theorem B607863 : Blo 607294 607863 := bstep (se 1 (by rfl) ⟨455897, by rfl⟩ : syracuseStep 607863 = 911795) B911795
theorem B2311811 : Blo 607294 2311811 := bstep (se 1 (by rfl) ⟨1733858, by rfl⟩ : syracuseStep 2311811 = 3467717) B3467717
theorem B607883 : Blo 607294 607883 := bstep (se 1 (by rfl) ⟨455912, by rfl⟩ : syracuseStep 607883 = 911825) B911825
theorem B607895 : Blo 607294 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B2598551 : Blo 607294 2598551 := bstep (se 1 (by rfl) ⟨1948913, by rfl⟩ : syracuseStep 2598551 = 3897827) B3897827
theorem B1025689 : Blo 607294 1025689 := bstep (se 2 (by rfl) ⟨384633, by rfl⟩ : syracuseStep 1025689 = 769267) B769267
theorem B607915 : Blo 607294 607915 := bstep (se 1 (by rfl) ⟨455936, by rfl⟩ : syracuseStep 607915 = 911873) B911873
theorem B607927 : Blo 607294 607927 := bstep (se 1 (by rfl) ⟨455945, by rfl⟩ : syracuseStep 607927 = 911891) B911891
theorem B1541825 : Blo 607294 1541825 := bstep (se 2 (by rfl) ⟨578184, by rfl⟩ : syracuseStep 1541825 = 1156369) B1156369
theorem B911051 : Blo 607294 911051 := bstep (se 1 (by rfl) ⟨683288, by rfl⟩ : syracuseStep 911051 = 1366577) B1366577
theorem B607947 : Blo 607294 607947 := bstep (se 1 (by rfl) ⟨455960, by rfl⟩ : syracuseStep 607947 = 911921) B911921
theorem B7513805 : Blo 607294 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B911063 : Blo 607294 911063 := bstep (se 1 (by rfl) ⟨683297, by rfl⟩ : syracuseStep 911063 = 1366595) B1366595
theorem B607959 : Blo 607294 607959 := bstep (se 1 (by rfl) ⟨455969, by rfl⟩ : syracuseStep 607959 = 911939) B911939
theorem B1369817 : Blo 607294 1369817 := bstep (se 2 (by rfl) ⟨513681, by rfl⟩ : syracuseStep 1369817 = 1027363) B1027363
theorem B607979 : Blo 607294 607979 := bstep (se 1 (by rfl) ⟨455984, by rfl⟩ : syracuseStep 607979 = 911969) B911969
theorem B607991 : Blo 607294 607991 := bstep (se 1 (by rfl) ⟨455993, by rfl⟩ : syracuseStep 607991 = 911987) B911987
theorem B608011 : Blo 607294 608011 := bstep (se 1 (by rfl) ⟨456008, by rfl⟩ : syracuseStep 608011 = 912017) B912017
theorem B608023 : Blo 607294 608023 := bstep (se 1 (by rfl) ⟨456017, by rfl⟩ : syracuseStep 608023 = 912035) B912035
theorem B911129 : Blo 607294 911129 := bstep (se 2 (by rfl) ⟨341673, by rfl⟩ : syracuseStep 911129 = 683347) B683347
theorem B608043 : Blo 607294 608043 := bstep (se 1 (by rfl) ⟨456032, by rfl⟩ : syracuseStep 608043 = 912065) B912065
theorem B1369907 : Blo 607294 1369907 := bstep (se 1 (by rfl) ⟨1027430, by rfl⟩ : syracuseStep 1369907 = 2054861) B2054861
theorem B608055 : Blo 607294 608055 := bstep (se 1 (by rfl) ⟨456041, by rfl⟩ : syracuseStep 608055 = 912083) B912083
theorem B3082049 : Blo 607294 3082049 := bstep (se 2 (by rfl) ⟨1155768, by rfl⟩ : syracuseStep 3082049 = 2311537) B2311537
theorem B608075 : Blo 607294 608075 := bstep (se 1 (by rfl) ⟨456056, by rfl⟩ : syracuseStep 608075 = 912113) B912113
theorem B608087 : Blo 607294 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B1369943 : Blo 607294 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B25692005 : Blo 607294 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B624491 : Blo 607294 624491 := bstep (se 1 (by rfl) ⟨468368, by rfl⟩ : syracuseStep 624491 = 936737) B936737
theorem B608107 : Blo 607294 608107 := bstep (se 1 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 608107 = 912161) B912161
theorem B608119 : Blo 607294 608119 := bstep (se 1 (by rfl) ⟨456089, by rfl⟩ : syracuseStep 608119 = 912179) B912179
theorem B911243 : Blo 607294 911243 := bstep (se 1 (by rfl) ⟨683432, by rfl⟩ : syracuseStep 911243 = 1366865) B1366865
theorem B608139 : Blo 607294 608139 := bstep (se 1 (by rfl) ⟨456104, by rfl⟩ : syracuseStep 608139 = 912209) B912209
theorem B911255 : Blo 607294 911255 := bstep (se 1 (by rfl) ⟨683441, by rfl⟩ : syracuseStep 911255 = 1366883) B1366883
theorem B1460119 : Blo 607294 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B608151 : Blo 607294 608151 := bstep (se 1 (by rfl) ⟨456113, by rfl⟩ : syracuseStep 608151 = 912227) B912227
theorem B608171 : Blo 607294 608171 := bstep (se 1 (by rfl) ⟨456128, by rfl⟩ : syracuseStep 608171 = 912257) B912257
theorem B608183 : Blo 607294 608183 := bstep (se 1 (by rfl) ⟨456137, by rfl⟩ : syracuseStep 608183 = 912275) B912275
theorem B608203 : Blo 607294 608203 := bstep (se 1 (by rfl) ⟨456152, by rfl⟩ : syracuseStep 608203 = 912305) B912305
theorem B608215 : Blo 607294 608215 := bstep (se 1 (by rfl) ⟨456161, by rfl⟩ : syracuseStep 608215 = 912323) B912323
theorem B911321 : Blo 607294 911321 := bstep (se 2 (by rfl) ⟨341745, by rfl⟩ : syracuseStep 911321 = 683491) B683491
theorem B608235 : Blo 607294 608235 := bstep (se 1 (by rfl) ⟨456176, by rfl⟩ : syracuseStep 608235 = 912353) B912353
theorem B608247 : Blo 607294 608247 := bstep (se 1 (by rfl) ⟨456185, by rfl⟩ : syracuseStep 608247 = 912371) B912371
theorem B608267 : Blo 607294 608267 := bstep (se 1 (by rfl) ⟨456200, by rfl⟩ : syracuseStep 608267 = 912401) B912401
theorem B1370123 : Blo 607294 1370123 := bstep (se 1 (by rfl) ⟨1027592, by rfl⟩ : syracuseStep 1370123 = 2055185) B2055185
theorem B608279 : Blo 607294 608279 := bstep (se 1 (by rfl) ⟨456209, by rfl⟩ : syracuseStep 608279 = 912419) B912419
theorem B2058263 : Blo 607294 2058263 := bstep (se 1 (by rfl) ⟨1543697, by rfl⟩ : syracuseStep 2058263 = 3087395) B3087395
theorem B608299 : Blo 607294 608299 := bstep (se 1 (by rfl) ⟨456224, by rfl⟩ : syracuseStep 608299 = 912449) B912449
theorem B608311 : Blo 607294 608311 := bstep (se 1 (by rfl) ⟨456233, by rfl⟩ : syracuseStep 608311 = 912467) B912467
theorem B1370177 : Blo 607294 1370177 := bstep (se 2 (by rfl) ⟨513816, by rfl⟩ : syracuseStep 1370177 = 1027633) B1027633
theorem B911435 : Blo 607294 911435 := bstep (se 1 (by rfl) ⟨683576, by rfl⟩ : syracuseStep 911435 = 1367153) B1367153
theorem B608331 : Blo 607294 608331 := bstep (se 1 (by rfl) ⟨456248, by rfl⟩ : syracuseStep 608331 = 912497) B912497
theorem B911447 : Blo 607294 911447 := bstep (se 1 (by rfl) ⟨683585, by rfl⟩ : syracuseStep 911447 = 1367171) B1367171
theorem B608343 : Blo 607294 608343 := bstep (se 1 (by rfl) ⟨456257, by rfl⟩ : syracuseStep 608343 = 912515) B912515
theorem B772183 : Blo 607294 772183 := bstep (se 1 (by rfl) ⟨579137, by rfl⟩ : syracuseStep 772183 = 1158275) B1158275
theorem B1321049 : Blo 607294 1321049 := bstep (se 2 (by rfl) ⟨495393, by rfl⟩ : syracuseStep 1321049 = 990787) B990787
theorem B608363 : Blo 607294 608363 := bstep (se 1 (by rfl) ⟨456272, by rfl⟩ : syracuseStep 608363 = 912545) B912545
theorem B608375 : Blo 607294 608375 := bstep (se 1 (by rfl) ⟨456281, by rfl⟩ : syracuseStep 608375 = 912563) B912563
theorem B608395 : Blo 607294 608395 := bstep (se 1 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 608395 = 912593) B912593
theorem B608407 : Blo 607294 608407 := bstep (se 1 (by rfl) ⟨456305, by rfl⟩ : syracuseStep 608407 = 912611) B912611
theorem B911513 : Blo 607294 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B608427 : Blo 607294 608427 := bstep (se 1 (by rfl) ⟨456320, by rfl⟩ : syracuseStep 608427 = 912641) B912641
theorem B608439 : Blo 607294 608439 := bstep (se 1 (by rfl) ⟨456329, by rfl⟩ : syracuseStep 608439 = 912659) B912659
theorem B608459 : Blo 607294 608459 := bstep (se 1 (by rfl) ⟨456344, by rfl⟩ : syracuseStep 608459 = 912689) B912689
theorem B1026263 : Blo 607294 1026263 := bstep (se 1 (by rfl) ⟨769697, by rfl⟩ : syracuseStep 1026263 = 1539395) B1539395
theorem B608471 : Blo 607294 608471 := bstep (se 1 (by rfl) ⟨456353, by rfl⟩ : syracuseStep 608471 = 912707) B912707
theorem B1542361 : Blo 607294 1542361 := bstep (se 2 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 1542361 = 1156771) B1156771
theorem B608491 : Blo 607294 608491 := bstep (se 1 (by rfl) ⟨456368, by rfl⟩ : syracuseStep 608491 = 912737) B912737
theorem B608503 : Blo 607294 608503 := bstep (se 1 (by rfl) ⟨456377, by rfl⟩ : syracuseStep 608503 = 912755) B912755
theorem B911627 : Blo 607294 911627 := bstep (se 1 (by rfl) ⟨683720, by rfl⟩ : syracuseStep 911627 = 1367441) B1367441
theorem B608523 : Blo 607294 608523 := bstep (se 1 (by rfl) ⟨456392, by rfl⟩ : syracuseStep 608523 = 912785) B912785
theorem B911639 : Blo 607294 911639 := bstep (se 1 (by rfl) ⟨683729, by rfl⟩ : syracuseStep 911639 = 1367459) B1367459
theorem B608535 : Blo 607294 608535 := bstep (se 1 (by rfl) ⟨456401, by rfl⟩ : syracuseStep 608535 = 912803) B912803
theorem B1370393 : Blo 607294 1370393 := bstep (se 2 (by rfl) ⟨513897, by rfl⟩ : syracuseStep 1370393 = 1027795) B1027795
theorem B608555 : Blo 607294 608555 := bstep (se 1 (by rfl) ⟨456416, by rfl⟩ : syracuseStep 608555 = 912833) B912833
theorem B608567 : Blo 607294 608567 := bstep (se 1 (by rfl) ⟨456425, by rfl⟩ : syracuseStep 608567 = 912851) B912851
theorem B2050379 : Blo 607294 2050379 := bstep (se 1 (by rfl) ⟨1537784, by rfl⟩ : syracuseStep 2050379 = 3075569) B3075569
theorem B608587 : Blo 607294 608587 := bstep (se 1 (by rfl) ⟨456440, by rfl⟩ : syracuseStep 608587 = 912881) B912881
theorem B1026391 : Blo 607294 1026391 := bstep (se 1 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 1026391 = 1539587) B1539587
theorem B608599 : Blo 607294 608599 := bstep (se 1 (by rfl) ⟨456449, by rfl⟩ : syracuseStep 608599 = 912899) B912899
theorem B911705 : Blo 607294 911705 := bstep (se 2 (by rfl) ⟨341889, by rfl⟩ : syracuseStep 911705 = 683779) B683779
theorem B821593 : Blo 607294 821593 := bstep (se 2 (by rfl) ⟨308097, by rfl⟩ : syracuseStep 821593 = 616195) B616195
theorem B1730909 : Blo 607294 1730909 := bstep (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) B649091
theorem B608619 : Blo 607294 608619 := bstep (se 1 (by rfl) ⟨456464, by rfl⟩ : syracuseStep 608619 = 912929) B912929
theorem B1370483 : Blo 607294 1370483 := bstep (se 1 (by rfl) ⟨1027862, by rfl⟩ : syracuseStep 1370483 = 2055725) B2055725
theorem B608631 : Blo 607294 608631 := bstep (se 1 (by rfl) ⟨456473, by rfl⟩ : syracuseStep 608631 = 912947) B912947
theorem B3074435 : Blo 607294 3074435 := bstep (se 1 (by rfl) ⟨2305826, by rfl⟩ : syracuseStep 3074435 = 4611653) B4611653
theorem B608651 : Blo 607294 608651 := bstep (se 1 (by rfl) ⟨456488, by rfl⟩ : syracuseStep 608651 = 912977) B912977
theorem B608663 : Blo 607294 608663 := bstep (se 1 (by rfl) ⟨456497, by rfl⟩ : syracuseStep 608663 = 912995) B912995
theorem B1370519 : Blo 607294 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B608683 : Blo 607294 608683 := bstep (se 1 (by rfl) ⟨456512, by rfl⟩ : syracuseStep 608683 = 913025) B913025
theorem B608695 : Blo 607294 608695 := bstep (se 1 (by rfl) ⟨456521, by rfl⟩ : syracuseStep 608695 = 913043) B913043
theorem B911819 : Blo 607294 911819 := bstep (se 1 (by rfl) ⟨683864, by rfl⟩ : syracuseStep 911819 = 1367729) B1367729
theorem B608715 : Blo 607294 608715 := bstep (se 1 (by rfl) ⟨456536, by rfl⟩ : syracuseStep 608715 = 913073) B913073
theorem B911831 : Blo 607294 911831 := bstep (se 1 (by rfl) ⟨683873, by rfl⟩ : syracuseStep 911831 = 1367747) B1367747
theorem B608727 : Blo 607294 608727 := bstep (se 1 (by rfl) ⟨456545, by rfl⟩ : syracuseStep 608727 = 913091) B913091
theorem B1157591 : Blo 607294 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B21047779 : Blo 607294 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B608747 : Blo 607294 608747 := bstep (se 1 (by rfl) ⟨456560, by rfl⟩ : syracuseStep 608747 = 913121) B913121
theorem B608759 : Blo 607294 608759 := bstep (se 1 (by rfl) ⟨456569, by rfl⟩ : syracuseStep 608759 = 913139) B913139
theorem B608779 : Blo 607294 608779 := bstep (se 1 (by rfl) ⟨456584, by rfl⟩ : syracuseStep 608779 = 913169) B913169
theorem B608791 : Blo 607294 608791 := bstep (se 1 (by rfl) ⟨456593, by rfl⟩ : syracuseStep 608791 = 913187) B913187
theorem B911897 : Blo 607294 911897 := bstep (se 2 (by rfl) ⟨341961, by rfl⟩ : syracuseStep 911897 = 683923) B683923
theorem B608811 : Blo 607294 608811 := bstep (se 1 (by rfl) ⟨456608, by rfl⟩ : syracuseStep 608811 = 913217) B913217
theorem B608823 : Blo 607294 608823 := bstep (se 1 (by rfl) ⟨456617, by rfl⟩ : syracuseStep 608823 = 913235) B913235
theorem B608843 : Blo 607294 608843 := bstep (se 1 (by rfl) ⟨456632, by rfl⟩ : syracuseStep 608843 = 913265) B913265
theorem B1370699 : Blo 607294 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B608855 : Blo 607294 608855 := bstep (se 1 (by rfl) ⟨456641, by rfl⟩ : syracuseStep 608855 = 913283) B913283
theorem B2050649 : Blo 607294 2050649 := bstep (se 2 (by rfl) ⟨768993, by rfl⟩ : syracuseStep 2050649 = 1537987) B1537987
theorem B2083421 : Blo 607294 2083421 := bstep (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) B781283
theorem B3902053 : Blo 607294 3902053 := bstep (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) B731635
theorem B608875 : Blo 607294 608875 := bstep (se 1 (by rfl) ⟨456656, by rfl⟩ : syracuseStep 608875 = 913313) B913313
theorem B608887 : Blo 607294 608887 := bstep (se 1 (by rfl) ⟨456665, by rfl⟩ : syracuseStep 608887 = 913331) B913331
theorem B1370753 : Blo 607294 1370753 := bstep (se 2 (by rfl) ⟨514032, by rfl⟩ : syracuseStep 1370753 = 1028065) B1028065
theorem B2960003 : Blo 607294 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B912011 : Blo 607294 912011 := bstep (se 1 (by rfl) ⟨684008, by rfl⟩ : syracuseStep 912011 = 1368017) B1368017
theorem B608907 : Blo 607294 608907 := bstep (se 1 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 608907 = 913361) B913361
theorem B912023 : Blo 607294 912023 := bstep (se 1 (by rfl) ⟨684017, by rfl⟩ : syracuseStep 912023 = 1368035) B1368035
theorem B608919 : Blo 607294 608919 := bstep (se 1 (by rfl) ⟨456689, by rfl⟩ : syracuseStep 608919 = 913379) B913379
theorem B608939 : Blo 607294 608939 := bstep (se 1 (by rfl) ⟨456704, by rfl⟩ : syracuseStep 608939 = 913409) B913409
theorem B608951 : Blo 607294 608951 := bstep (se 1 (by rfl) ⟨456713, by rfl⟩ : syracuseStep 608951 = 913427) B913427
theorem B1231553 : Blo 607294 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B608971 : Blo 607294 608971 := bstep (se 1 (by rfl) ⟨456728, by rfl⟩ : syracuseStep 608971 = 913457) B913457
theorem B1043147 : Blo 607294 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B608983 : Blo 607294 608983 := bstep (se 1 (by rfl) ⟨456737, by rfl⟩ : syracuseStep 608983 = 913475) B913475
theorem B912089 : Blo 607294 912089 := bstep (se 2 (by rfl) ⟨342033, by rfl⟩ : syracuseStep 912089 = 684067) B684067
theorem B1780445 : Blo 607294 1780445 := bstep (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) B667667
theorem B609003 : Blo 607294 609003 := bstep (se 1 (by rfl) ⟨456752, by rfl⟩ : syracuseStep 609003 = 913505) B913505
theorem B609015 : Blo 607294 609015 := bstep (se 1 (by rfl) ⟨456761, by rfl⟩ : syracuseStep 609015 = 913523) B913523
theorem B609035 : Blo 607294 609035 := bstep (se 1 (by rfl) ⟨456776, by rfl⟩ : syracuseStep 609035 = 913553) B913553
theorem B609047 : Blo 607294 609047 := bstep (se 1 (by rfl) ⟨456785, by rfl⟩ : syracuseStep 609047 = 913571) B913571
theorem B609067 : Blo 607294 609067 := bstep (se 1 (by rfl) ⟨456800, by rfl⟩ : syracuseStep 609067 = 913601) B913601
theorem B609079 : Blo 607294 609079 := bstep (se 1 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 609079 = 913619) B913619
theorem B2059073 : Blo 607294 2059073 := bstep (se 2 (by rfl) ⟨772152, by rfl⟩ : syracuseStep 2059073 = 1544305) B1544305
theorem B3697483 : Blo 607294 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B912203 : Blo 607294 912203 := bstep (se 1 (by rfl) ⟨684152, by rfl⟩ : syracuseStep 912203 = 1368305) B1368305
theorem B609099 : Blo 607294 609099 := bstep (se 1 (by rfl) ⟨456824, by rfl⟩ : syracuseStep 609099 = 913649) B913649
theorem B912215 : Blo 607294 912215 := bstep (se 1 (by rfl) ⟨684161, by rfl⟩ : syracuseStep 912215 = 1368323) B1368323
theorem B609111 : Blo 607294 609111 := bstep (se 1 (by rfl) ⟨456833, by rfl⟩ : syracuseStep 609111 = 913667) B913667
theorem B1370969 : Blo 607294 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B609131 : Blo 607294 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B609143 : Blo 607294 609143 := bstep (se 1 (by rfl) ⟨456857, by rfl⟩ : syracuseStep 609143 = 913715) B913715
theorem B609163 : Blo 607294 609163 := bstep (se 1 (by rfl) ⟨456872, by rfl⟩ : syracuseStep 609163 = 913745) B913745
theorem B609175 : Blo 607294 609175 := bstep (se 1 (by rfl) ⟨456881, by rfl⟩ : syracuseStep 609175 = 913763) B913763
theorem B2198423 : Blo 607294 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B912281 : Blo 607294 912281 := bstep (se 2 (by rfl) ⟨342105, by rfl⟩ : syracuseStep 912281 = 684211) B684211
theorem B609195 : Blo 607294 609195 := bstep (se 1 (by rfl) ⟨456896, by rfl⟩ : syracuseStep 609195 = 913793) B913793
theorem B2927539 : Blo 607294 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B1371059 : Blo 607294 1371059 := bstep (se 1 (by rfl) ⟨1028294, by rfl⟩ : syracuseStep 1371059 = 2056589) B2056589
theorem B609207 : Blo 607294 609207 := bstep (se 1 (by rfl) ⟨456905, by rfl⟩ : syracuseStep 609207 = 913811) B913811
theorem B1027019 : Blo 607294 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B609227 : Blo 607294 609227 := bstep (se 1 (by rfl) ⟨456920, by rfl⟩ : syracuseStep 609227 = 913841) B913841
theorem B609239 : Blo 607294 609239 := bstep (se 1 (by rfl) ⟨456929, by rfl⟩ : syracuseStep 609239 = 913859) B913859
theorem B609259 : Blo 607294 609259 := bstep (se 1 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 609259 = 913889) B913889
theorem B609271 : Blo 607294 609271 := bstep (se 1 (by rfl) ⟨456953, by rfl⟩ : syracuseStep 609271 = 913907) B913907
theorem B1158131 : Blo 607294 1158131 := bstep (se 1 (by rfl) ⟨868598, by rfl⟩ : syracuseStep 1158131 = 1737197) B1737197
theorem B912395 : Blo 607294 912395 := bstep (se 1 (by rfl) ⟨684296, by rfl⟩ : syracuseStep 912395 = 1368593) B1368593
theorem B609291 : Blo 607294 609291 := bstep (se 1 (by rfl) ⟨456968, by rfl⟩ : syracuseStep 609291 = 913937) B913937
theorem B912407 : Blo 607294 912407 := bstep (se 1 (by rfl) ⟨684305, by rfl⟩ : syracuseStep 912407 = 1368611) B1368611
theorem B609303 : Blo 607294 609303 := bstep (se 1 (by rfl) ⟨456977, by rfl⟩ : syracuseStep 609303 = 913955) B913955
theorem B609323 : Blo 607294 609323 := bstep (se 1 (by rfl) ⟨456992, by rfl⟩ : syracuseStep 609323 = 913985) B913985
theorem B609335 : Blo 607294 609335 := bstep (se 1 (by rfl) ⟨457001, by rfl⟩ : syracuseStep 609335 = 914003) B914003
theorem B1099673 : Blo 607294 1099673 := bstep (se 2 (by rfl) ⟨412377, by rfl⟩ : syracuseStep 1099673 = 824755) B824755
theorem B15199301 : Blo 607294 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1027147 : Blo 607294 1027147 := bstep (se 1 (by rfl) ⟨770360, by rfl⟩ : syracuseStep 1027147 = 1540721) B1540721
theorem B609355 : Blo 607294 609355 := bstep (se 1 (by rfl) ⟨457016, by rfl⟩ : syracuseStep 609355 = 914033) B914033
theorem B609367 : Blo 607294 609367 := bstep (se 1 (by rfl) ⟨457025, by rfl⟩ : syracuseStep 609367 = 914051) B914051
theorem B912473 : Blo 607294 912473 := bstep (se 2 (by rfl) ⟨342177, by rfl⟩ : syracuseStep 912473 = 684355) B684355
theorem B609387 : Blo 607294 609387 := bstep (se 1 (by rfl) ⟨457040, by rfl⟩ : syracuseStep 609387 = 914081) B914081
theorem B609399 : Blo 607294 609399 := bstep (se 1 (by rfl) ⟨457049, by rfl⟩ : syracuseStep 609399 = 914099) B914099
theorem B937099 : Blo 607294 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B609419 : Blo 607294 609419 := bstep (se 1 (by rfl) ⟨457064, by rfl⟩ : syracuseStep 609419 = 914129) B914129
theorem B1371275 : Blo 607294 1371275 := bstep (se 1 (by rfl) ⟨1028456, by rfl⟩ : syracuseStep 1371275 = 2056913) B2056913
theorem B609431 : Blo 607294 609431 := bstep (se 1 (by rfl) ⟨457073, by rfl⟩ : syracuseStep 609431 = 914147) B914147
theorem B609451 : Blo 607294 609451 := bstep (se 1 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 609451 = 914177) B914177
theorem B2337965 : Blo 607294 2337965 := bstep (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) B876737
theorem B609463 : Blo 607294 609463 := bstep (se 1 (by rfl) ⟨457097, by rfl⟩ : syracuseStep 609463 = 914195) B914195
theorem B1371329 : Blo 607294 1371329 := bstep (se 2 (by rfl) ⟨514248, by rfl⟩ : syracuseStep 1371329 = 1028497) B1028497
theorem B912587 : Blo 607294 912587 := bstep (se 1 (by rfl) ⟨684440, by rfl⟩ : syracuseStep 912587 = 1368881) B1368881
theorem B609483 : Blo 607294 609483 := bstep (se 1 (by rfl) ⟨457112, by rfl⟩ : syracuseStep 609483 = 914225) B914225
theorem B912599 : Blo 607294 912599 := bstep (se 1 (by rfl) ⟨684449, by rfl⟩ : syracuseStep 912599 = 1368899) B1368899
theorem B609495 : Blo 607294 609495 := bstep (se 1 (by rfl) ⟨457121, by rfl⟩ : syracuseStep 609495 = 914243) B914243
theorem B1027289 : Blo 607294 1027289 := bstep (se 2 (by rfl) ⟨385233, by rfl⟩ : syracuseStep 1027289 = 770467) B770467
theorem B617707 : Blo 607294 617707 := bstep (se 1 (by rfl) ⟨463280, by rfl⟩ : syracuseStep 617707 = 926561) B926561
theorem B609515 : Blo 607294 609515 := bstep (se 1 (by rfl) ⟨457136, by rfl⟩ : syracuseStep 609515 = 914273) B914273
theorem B609527 : Blo 607294 609527 := bstep (se 1 (by rfl) ⟨457145, by rfl⟩ : syracuseStep 609527 = 914291) B914291
theorem B5860613 : Blo 607294 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B683275 : Blo 607294 683275 := bstep (se 1 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 683275 = 1024913) B1024913
theorem B609547 : Blo 607294 609547 := bstep (se 1 (by rfl) ⟨457160, by rfl⟩ : syracuseStep 609547 = 914321) B914321
theorem B2051351 : Blo 607294 2051351 := bstep (se 1 (by rfl) ⟨1538513, by rfl⟩ : syracuseStep 2051351 = 3077027) B3077027
theorem B609559 : Blo 607294 609559 := bstep (se 1 (by rfl) ⟨457169, by rfl⟩ : syracuseStep 609559 = 914339) B914339
theorem B912665 : Blo 607294 912665 := bstep (se 2 (by rfl) ⟨342249, by rfl⟩ : syracuseStep 912665 = 684499) B684499
theorem B650539 : Blo 607294 650539 := bstep (se 1 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 650539 = 975809) B975809
theorem B609579 : Blo 607294 609579 := bstep (se 1 (by rfl) ⟨457184, by rfl⟩ : syracuseStep 609579 = 914369) B914369
theorem B1543475 : Blo 607294 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B609591 : Blo 607294 609591 := bstep (se 1 (by rfl) ⟨457193, by rfl⟩ : syracuseStep 609591 = 914387) B914387
theorem B3460427 : Blo 607294 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B609611 : Blo 607294 609611 := bstep (se 1 (by rfl) ⟨457208, by rfl⟩ : syracuseStep 609611 = 914417) B914417
theorem B1027417 : Blo 607294 1027417 := bstep (se 2 (by rfl) ⟨385281, by rfl⟩ : syracuseStep 1027417 = 770563) B770563
theorem B609623 : Blo 607294 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B2059613 : Blo 607294 2059613 := bstep (se 3 (by rfl) ⟨386177, by rfl⟩ : syracuseStep 2059613 = 772355) B772355
theorem B609643 : Blo 607294 609643 := bstep (se 1 (by rfl) ⟨457232, by rfl⟩ : syracuseStep 609643 = 914465) B914465
theorem B683383 : Blo 607294 683383 := bstep (se 1 (by rfl) ⟨512537, by rfl⟩ : syracuseStep 683383 = 1025075) B1025075
theorem B609655 : Blo 607294 609655 := bstep (se 1 (by rfl) ⟨457241, by rfl⟩ : syracuseStep 609655 = 914483) B914483
theorem B912779 : Blo 607294 912779 := bstep (se 1 (by rfl) ⟨684584, by rfl⟩ : syracuseStep 912779 = 1369169) B1369169
theorem B609675 : Blo 607294 609675 := bstep (se 1 (by rfl) ⟨457256, by rfl⟩ : syracuseStep 609675 = 914513) B914513
theorem B912791 : Blo 607294 912791 := bstep (se 1 (by rfl) ⟨684593, by rfl⟩ : syracuseStep 912791 = 1369187) B1369187
theorem B609687 : Blo 607294 609687 := bstep (se 1 (by rfl) ⟨457265, by rfl⟩ : syracuseStep 609687 = 914531) B914531
theorem B1371545 : Blo 607294 1371545 := bstep (se 2 (by rfl) ⟨514329, by rfl⟩ : syracuseStep 1371545 = 1028659) B1028659
theorem B609707 : Blo 607294 609707 := bstep (se 1 (by rfl) ⟨457280, by rfl⟩ : syracuseStep 609707 = 914561) B914561
theorem B609719 : Blo 607294 609719 := bstep (se 1 (by rfl) ⟨457289, by rfl⟩ : syracuseStep 609719 = 914579) B914579
theorem B609739 : Blo 607294 609739 := bstep (se 1 (by rfl) ⟨457304, by rfl⟩ : syracuseStep 609739 = 914609) B914609
theorem B609751 : Blo 607294 609751 := bstep (se 1 (by rfl) ⟨457313, by rfl⟩ : syracuseStep 609751 = 914627) B914627
theorem B912857 : Blo 607294 912857 := bstep (se 2 (by rfl) ⟨342321, by rfl⟩ : syracuseStep 912857 = 684643) B684643
theorem B609771 : Blo 607294 609771 := bstep (se 1 (by rfl) ⟨457328, by rfl⟩ : syracuseStep 609771 = 914657) B914657
theorem B1371635 : Blo 607294 1371635 := bstep (se 1 (by rfl) ⟨1028726, by rfl⟩ : syracuseStep 1371635 = 2057453) B2057453
theorem B609783 : Blo 607294 609783 := bstep (se 1 (by rfl) ⟨457337, by rfl⟩ : syracuseStep 609783 = 914675) B914675
theorem B609803 : Blo 607294 609803 := bstep (se 1 (by rfl) ⟨457352, by rfl⟩ : syracuseStep 609803 = 914705) B914705
theorem B1642007 : Blo 607294 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B1371671 : Blo 607294 1371671 := bstep (se 1 (by rfl) ⟨1028753, by rfl⟩ : syracuseStep 1371671 = 2057507) B2057507
theorem B609815 : Blo 607294 609815 := bstep (se 1 (by rfl) ⟨457361, by rfl⟩ : syracuseStep 609815 = 914723) B914723
theorem B683563 : Blo 607294 683563 := bstep (se 1 (by rfl) ⟨512672, by rfl⟩ : syracuseStep 683563 = 1025345) B1025345
theorem B609835 : Blo 607294 609835 := bstep (se 1 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 609835 = 914753) B914753
theorem B609847 : Blo 607294 609847 := bstep (se 1 (by rfl) ⟨457385, by rfl⟩ : syracuseStep 609847 = 914771) B914771
theorem B912971 : Blo 607294 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B609867 : Blo 607294 609867 := bstep (se 1 (by rfl) ⟨457400, by rfl⟩ : syracuseStep 609867 = 914801) B914801
theorem B2058803 : Blo 607294 2058803 := bstep (se 1 (by rfl) ⟨1544102, by rfl⟩ : syracuseStep 2058803 = 3088205) B3088205
theorem B912983 : Blo 607294 912983 := bstep (se 1 (by rfl) ⟨684737, by rfl⟩ : syracuseStep 912983 = 1369475) B1369475
theorem B609879 : Blo 607294 609879 := bstep (se 1 (by rfl) ⟨457409, by rfl⟩ : syracuseStep 609879 = 914819) B914819
theorem B5197405 : Blo 607294 5197405 := bstep (se 3 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 5197405 = 1949027) B1949027
theorem B1543769 : Blo 607294 1543769 := bstep (se 2 (by rfl) ⟨578913, by rfl⟩ : syracuseStep 1543769 = 1157827) B1157827
theorem B609899 : Blo 607294 609899 := bstep (se 1 (by rfl) ⟨457424, by rfl⟩ : syracuseStep 609899 = 914849) B914849
theorem B609911 : Blo 607294 609911 := bstep (se 1 (by rfl) ⟨457433, by rfl⟩ : syracuseStep 609911 = 914867) B914867
theorem B609931 : Blo 607294 609931 := bstep (se 1 (by rfl) ⟨457448, by rfl⟩ : syracuseStep 609931 = 914897) B914897
theorem B683671 : Blo 607294 683671 := bstep (se 1 (by rfl) ⟨512753, by rfl⟩ : syracuseStep 683671 = 1025507) B1025507
theorem B609943 : Blo 607294 609943 := bstep (se 1 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 609943 = 914915) B914915
theorem B913049 : Blo 607294 913049 := bstep (se 2 (by rfl) ⟨342393, by rfl⟩ : syracuseStep 913049 = 684787) B684787
theorem B609963 : Blo 607294 609963 := bstep (se 1 (by rfl) ⟨457472, by rfl⟩ : syracuseStep 609963 = 914945) B914945
theorem B609975 : Blo 607294 609975 := bstep (se 1 (by rfl) ⟨457481, by rfl⟩ : syracuseStep 609975 = 914963) B914963
theorem B1371851 : Blo 607294 1371851 := bstep (se 1 (by rfl) ⟨1028888, by rfl⟩ : syracuseStep 1371851 = 2057777) B2057777
theorem B609995 : Blo 607294 609995 := bstep (se 1 (by rfl) ⟨457496, by rfl⟩ : syracuseStep 609995 = 914993) B914993
theorem B610007 : Blo 607294 610007 := bstep (se 1 (by rfl) ⟨457505, by rfl⟩ : syracuseStep 610007 = 915011) B915011
theorem B3083993 : Blo 607294 3083993 := bstep (se 2 (by rfl) ⟨1156497, by rfl⟩ : syracuseStep 3083993 = 2312995) B2312995
theorem B610027 : Blo 607294 610027 := bstep (se 1 (by rfl) ⟨457520, by rfl⟩ : syracuseStep 610027 = 915041) B915041
theorem B610039 : Blo 607294 610039 := bstep (se 1 (by rfl) ⟨457529, by rfl⟩ : syracuseStep 610039 = 915059) B915059
theorem B1371905 : Blo 607294 1371905 := bstep (se 2 (by rfl) ⟨514464, by rfl⟩ : syracuseStep 1371905 = 1028929) B1028929
theorem B913163 : Blo 607294 913163 := bstep (se 1 (by rfl) ⟨684872, by rfl⟩ : syracuseStep 913163 = 1369745) B1369745
theorem B610059 : Blo 607294 610059 := bstep (se 1 (by rfl) ⟨457544, by rfl⟩ : syracuseStep 610059 = 915089) B915089
theorem B913175 : Blo 607294 913175 := bstep (se 1 (by rfl) ⟨684881, by rfl⟩ : syracuseStep 913175 = 1369763) B1369763
theorem B610071 : Blo 607294 610071 := bstep (se 1 (by rfl) ⟨457553, by rfl⟩ : syracuseStep 610071 = 915107) B915107
theorem B7802669 : Blo 607294 7802669 := bstep (se 3 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 7802669 = 2926001) B2926001
theorem B2748205 : Blo 607294 2748205 := bstep (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) B1030577
theorem B618283 : Blo 607294 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B2051891 : Blo 607294 2051891 := bstep (se 1 (by rfl) ⟨1538918, by rfl⟩ : syracuseStep 2051891 = 3077837) B3077837
theorem B610103 : Blo 607294 610103 := bstep (se 1 (by rfl) ⟨457577, by rfl⟩ : syracuseStep 610103 = 915155) B915155
theorem B683851 : Blo 607294 683851 := bstep (se 1 (by rfl) ⟨512888, by rfl⟩ : syracuseStep 683851 = 1025777) B1025777
theorem B610123 : Blo 607294 610123 := bstep (se 1 (by rfl) ⟨457592, by rfl⟩ : syracuseStep 610123 = 915185) B915185
theorem B610135 : Blo 607294 610135 := bstep (se 1 (by rfl) ⟨457601, by rfl⟩ : syracuseStep 610135 = 915203) B915203
theorem B913241 : Blo 607294 913241 := bstep (se 2 (by rfl) ⟨342465, by rfl⟩ : syracuseStep 913241 = 684931) B684931
theorem B1953629 : Blo 607294 1953629 := bstep (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) B732611
theorem B3518309 : Blo 607294 3518309 := bstep (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) B659683
theorem B11726693 : Blo 607294 11726693 := bstep (se 4 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 11726693 = 2198755) B2198755
theorem B610155 : Blo 607294 610155 := bstep (se 1 (by rfl) ⟨457616, by rfl⟩ : syracuseStep 610155 = 915233) B915233
theorem B610167 : Blo 607294 610167 := bstep (se 1 (by rfl) ⟨457625, by rfl⟩ : syracuseStep 610167 = 915251) B915251
theorem B610187 : Blo 607294 610187 := bstep (se 1 (by rfl) ⟨457640, by rfl⟩ : syracuseStep 610187 = 915281) B915281
theorem B1027991 : Blo 607294 1027991 := bstep (se 1 (by rfl) ⟨770993, by rfl⟩ : syracuseStep 1027991 = 1541987) B1541987
theorem B610199 : Blo 607294 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B610219 : Blo 607294 610219 := bstep (se 1 (by rfl) ⟨457664, by rfl⟩ : syracuseStep 610219 = 915329) B915329
theorem B683959 : Blo 607294 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B610231 : Blo 607294 610231 := bstep (se 1 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 610231 = 915347) B915347
theorem B913355 : Blo 607294 913355 := bstep (se 1 (by rfl) ⟨685016, by rfl⟩ : syracuseStep 913355 = 1370033) B1370033
theorem B610251 : Blo 607294 610251 := bstep (se 1 (by rfl) ⟨457688, by rfl⟩ : syracuseStep 610251 = 915377) B915377
theorem B913367 : Blo 607294 913367 := bstep (se 1 (by rfl) ⟨685025, by rfl⟩ : syracuseStep 913367 = 1370051) B1370051
theorem B2306009 : Blo 607294 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B1372121 : Blo 607294 1372121 := bstep (se 2 (by rfl) ⟨514545, by rfl⟩ : syracuseStep 1372121 = 1029091) B1029091
theorem B610263 : Blo 607294 610263 := bstep (se 1 (by rfl) ⟨457697, by rfl⟩ : syracuseStep 610263 = 915395) B915395
theorem B610283 : Blo 607294 610283 := bstep (se 1 (by rfl) ⟨457712, by rfl⟩ : syracuseStep 610283 = 915425) B915425
theorem B2920465 : Blo 607294 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B1028119 : Blo 607294 1028119 := bstep (se 1 (by rfl) ⟨771089, by rfl⟩ : syracuseStep 1028119 = 1542179) B1542179
theorem B913433 : Blo 607294 913433 := bstep (se 2 (by rfl) ⟨342537, by rfl⟩ : syracuseStep 913433 = 685075) B685075
theorem B2601011 : Blo 607294 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B1372211 : Blo 607294 1372211 := bstep (se 1 (by rfl) ⟨1029158, by rfl⟩ : syracuseStep 1372211 = 2058317) B2058317
theorem B2052161 : Blo 607294 2052161 := bstep (se 2 (by rfl) ⟨769560, by rfl⟩ : syracuseStep 2052161 = 1539121) B1539121
theorem B1372247 : Blo 607294 1372247 := bstep (se 1 (by rfl) ⟨1029185, by rfl⟩ : syracuseStep 1372247 = 2058371) B2058371
theorem B1732697 : Blo 607294 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B684139 : Blo 607294 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B913547 : Blo 607294 913547 := bstep (se 1 (by rfl) ⟨685160, by rfl⟩ : syracuseStep 913547 = 1370321) B1370321
theorem B2961559 : Blo 607294 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B913559 : Blo 607294 913559 := bstep (se 1 (by rfl) ⟨685169, by rfl⟩ : syracuseStep 913559 = 1370339) B1370339
theorem B2601163 : Blo 607294 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B684247 : Blo 607294 684247 := bstep (se 1 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 684247 = 1026371) B1026371
theorem B913625 : Blo 607294 913625 := bstep (se 2 (by rfl) ⟨342609, by rfl⟩ : syracuseStep 913625 = 685219) B685219
theorem B1372427 : Blo 607294 1372427 := bstep (se 1 (by rfl) ⟨1029320, by rfl⟩ : syracuseStep 1372427 = 2058641) B2058641
theorem B2601233 : Blo 607294 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B4616513 : Blo 607294 4616513 := bstep (se 2 (by rfl) ⟨1731192, by rfl⟩ : syracuseStep 4616513 = 3462385) B3462385
theorem B5853505 : Blo 607294 5853505 := bstep (se 2 (by rfl) ⟨2195064, by rfl⟩ : syracuseStep 5853505 = 4390129) B4390129
theorem B1372481 : Blo 607294 1372481 := bstep (se 2 (by rfl) ⟨514680, by rfl⟩ : syracuseStep 1372481 = 1029361) B1029361
theorem B913739 : Blo 607294 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B913751 : Blo 607294 913751 := bstep (se 1 (by rfl) ⟨685313, by rfl⟩ : syracuseStep 913751 = 1370627) B1370627
theorem B684427 : Blo 607294 684427 := bstep (se 1 (by rfl) ⟨513320, by rfl⟩ : syracuseStep 684427 = 1026641) B1026641
theorem B1733015 : Blo 607294 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B913817 : Blo 607294 913817 := bstep (se 2 (by rfl) ⟨342681, by rfl⟩ : syracuseStep 913817 = 685363) B685363
theorem B1388993 : Blo 607294 1388993 := bstep (se 2 (by rfl) ⟨520872, by rfl⟩ : syracuseStep 1388993 = 1041745) B1041745
theorem B1298891 : Blo 607294 1298891 := bstep (se 1 (by rfl) ⟨974168, by rfl⟩ : syracuseStep 1298891 = 1948337) B1948337
theorem B4633037 : Blo 607294 4633037 := bstep (se 3 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 4633037 = 1737389) B1737389
theorem B684535 : Blo 607294 684535 := bstep (se 1 (by rfl) ⟨513401, by rfl⟩ : syracuseStep 684535 = 1026803) B1026803
theorem B913931 : Blo 607294 913931 := bstep (se 1 (by rfl) ⟨685448, by rfl⟩ : syracuseStep 913931 = 1370897) B1370897
theorem B913943 : Blo 607294 913943 := bstep (se 1 (by rfl) ⟨685457, by rfl⟩ : syracuseStep 913943 = 1370915) B1370915
theorem B1372697 : Blo 607294 1372697 := bstep (se 2 (by rfl) ⟨514761, by rfl⟩ : syracuseStep 1372697 = 1029523) B1029523
theorem B914009 : Blo 607294 914009 := bstep (se 2 (by rfl) ⟨342753, by rfl⟩ : syracuseStep 914009 = 685507) B685507
theorem B2052701 : Blo 607294 2052701 := bstep (se 3 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 2052701 = 769763) B769763
theorem B1372787 : Blo 607294 1372787 := bstep (se 1 (by rfl) ⟨1029590, by rfl⟩ : syracuseStep 1372787 = 2059181) B2059181
theorem B1028747 : Blo 607294 1028747 := bstep (se 1 (by rfl) ⟨771560, by rfl⟩ : syracuseStep 1028747 = 1543121) B1543121
theorem B3568279 : Blo 607294 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B1372823 : Blo 607294 1372823 := bstep (se 1 (by rfl) ⟨1029617, by rfl⟩ : syracuseStep 1372823 = 2059235) B2059235
theorem B684715 : Blo 607294 684715 := bstep (se 1 (by rfl) ⟨513536, by rfl⟩ : syracuseStep 684715 = 1027073) B1027073
theorem B2536109 : Blo 607294 2536109 := bstep (se 3 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 2536109 = 951041) B951041
theorem B2314925 : Blo 607294 2314925 := bstep (se 3 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 2314925 = 868097) B868097
theorem B1462963 : Blo 607294 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B914123 : Blo 607294 914123 := bstep (se 1 (by rfl) ⟨685592, by rfl⟩ : syracuseStep 914123 = 1371185) B1371185
theorem B1233623 : Blo 607294 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B914135 : Blo 607294 914135 := bstep (se 1 (by rfl) ⟨685601, by rfl⟩ : syracuseStep 914135 = 1371203) B1371203
theorem B4690649 : Blo 607294 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B1028875 : Blo 607294 1028875 := bstep (se 1 (by rfl) ⟨771656, by rfl⟩ : syracuseStep 1028875 = 1543313) B1543313
theorem B684823 : Blo 607294 684823 := bstep (se 1 (by rfl) ⟨513617, by rfl⟩ : syracuseStep 684823 = 1027235) B1027235
theorem B914201 : Blo 607294 914201 := bstep (se 2 (by rfl) ⟨342825, by rfl⟩ : syracuseStep 914201 = 685651) B685651
theorem B2503489 : Blo 607294 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B1373003 : Blo 607294 1373003 := bstep (se 1 (by rfl) ⟨1029752, by rfl⟩ : syracuseStep 1373003 = 2059505) B2059505
theorem B1373057 : Blo 607294 1373057 := bstep (se 2 (by rfl) ⟨514896, by rfl⟩ : syracuseStep 1373057 = 1029793) B1029793
theorem B914315 : Blo 607294 914315 := bstep (se 1 (by rfl) ⟨685736, by rfl⟩ : syracuseStep 914315 = 1371473) B1371473
theorem B914327 : Blo 607294 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B1029017 : Blo 607294 1029017 := bstep (se 2 (by rfl) ⟨385881, by rfl⟩ : syracuseStep 1029017 = 771763) B771763
theorem B4633523 : Blo 607294 4633523 := bstep (se 1 (by rfl) ⟨3475142, by rfl⟩ : syracuseStep 4633523 = 6950285) B6950285
theorem B685003 : Blo 607294 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B914393 : Blo 607294 914393 := bstep (se 2 (by rfl) ⟨342897, by rfl⟩ : syracuseStep 914393 = 685795) B685795
theorem B1029145 : Blo 607294 1029145 := bstep (se 2 (by rfl) ⟨385929, by rfl⟩ : syracuseStep 1029145 = 771859) B771859
theorem B685111 : Blo 607294 685111 := bstep (se 1 (by rfl) ⟨513833, by rfl⟩ : syracuseStep 685111 = 1027667) B1027667
theorem B914507 : Blo 607294 914507 := bstep (se 1 (by rfl) ⟨685880, by rfl⟩ : syracuseStep 914507 = 1371761) B1371761
theorem B914519 : Blo 607294 914519 := bstep (se 1 (by rfl) ⟨685889, by rfl⟩ : syracuseStep 914519 = 1371779) B1371779
theorem B914585 : Blo 607294 914585 := bstep (se 2 (by rfl) ⟨342969, by rfl⟩ : syracuseStep 914585 = 685939) B685939
theorem B1733825 : Blo 607294 1733825 := bstep (se 2 (by rfl) ⟨650184, by rfl⟩ : syracuseStep 1733825 = 1300369) B1300369
theorem B685291 : Blo 607294 685291 := bstep (se 1 (by rfl) ⟨513968, by rfl⟩ : syracuseStep 685291 = 1027937) B1027937
theorem B4945157 : Blo 607294 4945157 := bstep (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) B927217
theorem B914699 : Blo 607294 914699 := bstep (se 1 (by rfl) ⟨686024, by rfl⟩ : syracuseStep 914699 = 1372049) B1372049
theorem B914711 : Blo 607294 914711 := bstep (se 1 (by rfl) ⟨686033, by rfl⟩ : syracuseStep 914711 = 1372067) B1372067
theorem B3085613 : Blo 607294 3085613 := bstep (se 3 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 3085613 = 1157105) B1157105
theorem B2471219 : Blo 607294 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B685399 : Blo 607294 685399 := bstep (se 1 (by rfl) ⟨514049, by rfl⟩ : syracuseStep 685399 = 1028099) B1028099
theorem B914777 : Blo 607294 914777 := bstep (se 2 (by rfl) ⟨343041, by rfl⟩ : syracuseStep 914777 = 686083) B686083
theorem B1168769 : Blo 607294 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B832907 : Blo 607294 832907 := bstep (se 1 (by rfl) ⟨624680, by rfl⟩ : syracuseStep 832907 = 1249361) B1249361
theorem B2594227 : Blo 607294 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B2315699 : Blo 607294 2315699 := bstep (se 1 (by rfl) ⟨1736774, by rfl⟩ : syracuseStep 2315699 = 3473549) B3473549
theorem B914891 : Blo 607294 914891 := bstep (se 1 (by rfl) ⟨686168, by rfl⟩ : syracuseStep 914891 = 1372337) B1372337
theorem B914903 : Blo 607294 914903 := bstep (se 1 (by rfl) ⟨686177, by rfl⟩ : syracuseStep 914903 = 1372355) B1372355
theorem B685579 : Blo 607294 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1144343 : Blo 607294 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B914969 : Blo 607294 914969 := bstep (se 2 (by rfl) ⟨343113, by rfl⟩ : syracuseStep 914969 = 686227) B686227
theorem B4396589 : Blo 607294 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B2307635 : Blo 607294 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B2307649 : Blo 607294 2307649 := bstep (se 2 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 2307649 = 1730737) B1730737
theorem B610091 : Blo 607294 610091 := bstep (se 1 (by rfl) ⟨457568, by rfl⟩ : syracuseStep 610091 = 915137) B915137
theorem B1029719 : Blo 607294 1029719 := bstep (se 1 (by rfl) ⟨772289, by rfl⟩ : syracuseStep 1029719 = 1544579) B1544579
theorem B685687 : Blo 607294 685687 := bstep (se 1 (by rfl) ⟨514265, by rfl⟩ : syracuseStep 685687 = 1028531) B1028531
theorem B915083 : Blo 607294 915083 := bstep (se 1 (by rfl) ⟨686312, by rfl⟩ : syracuseStep 915083 = 1372625) B1372625
theorem B2635409 : Blo 607294 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B915095 : Blo 607294 915095 := bstep (se 1 (by rfl) ⟨686321, by rfl⟩ : syracuseStep 915095 = 1372643) B1372643
theorem B1300121 : Blo 607294 1300121 := bstep (se 2 (by rfl) ⟨487545, by rfl⟩ : syracuseStep 1300121 = 975091) B975091
theorem B2053835 : Blo 607294 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B1029847 : Blo 607294 1029847 := bstep (se 1 (by rfl) ⟨772385, by rfl⟩ : syracuseStep 1029847 = 1544771) B1544771
theorem B915161 : Blo 607294 915161 := bstep (se 2 (by rfl) ⟨343185, by rfl⟩ : syracuseStep 915161 = 686371) B686371
theorem B923417 : Blo 607294 923417 := bstep (se 2 (by rfl) ⟨346281, by rfl⟩ : syracuseStep 923417 = 692563) B692563
theorem B685867 : Blo 607294 685867 := bstep (se 1 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 685867 = 1028801) B1028801
theorem B16684865 : Blo 607294 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B915275 : Blo 607294 915275 := bstep (se 1 (by rfl) ⟨686456, by rfl⟩ : syracuseStep 915275 = 1372913) B1372913
theorem B915287 : Blo 607294 915287 := bstep (se 1 (by rfl) ⟨686465, by rfl⟩ : syracuseStep 915287 = 1372931) B1372931
theorem B685975 : Blo 607294 685975 := bstep (se 1 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 685975 = 1028963) B1028963
theorem B915353 : Blo 607294 915353 := bstep (se 2 (by rfl) ⟨343257, by rfl⟩ : syracuseStep 915353 = 686515) B686515
theorem B2602925 : Blo 607294 2602925 := bstep (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) B976097
theorem B2054105 : Blo 607294 2054105 := bstep (se 2 (by rfl) ⟨770289, by rfl⟩ : syracuseStep 2054105 = 1540579) B1540579
theorem B3078161 : Blo 607294 3078161 := bstep (se 2 (by rfl) ⟨1154310, by rfl⟩ : syracuseStep 3078161 = 2308621) B2308621
theorem B2594861 : Blo 607294 2594861 := bstep (se 3 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 2594861 = 973073) B973073
theorem B1538099 : Blo 607294 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B1300531 : Blo 607294 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B1464385 : Blo 607294 1464385 := bstep (se 2 (by rfl) ⟨549144, by rfl⟩ : syracuseStep 1464385 = 1098289) B1098289
theorem B22181957 : Blo 607294 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B686155 : Blo 607294 686155 := bstep (se 1 (by rfl) ⟨514616, by rfl⟩ : syracuseStep 686155 = 1029233) B1029233
theorem B1153111 : Blo 607294 1153111 := bstep (se 1 (by rfl) ⟨864833, by rfl⟩ : syracuseStep 1153111 = 1729667) B1729667
theorem B3078323 : Blo 607294 3078323 := bstep (se 1 (by rfl) ⟨2308742, by rfl⟩ : syracuseStep 3078323 = 4617485) B4617485
theorem B686263 : Blo 607294 686263 := bstep (se 1 (by rfl) ⟨514697, by rfl⟩ : syracuseStep 686263 = 1029395) B1029395
theorem B1153217 : Blo 607294 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B5560525 : Blo 607294 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B4618457 : Blo 607294 4618457 := bstep (se 2 (by rfl) ⟨1731921, by rfl⟩ : syracuseStep 4618457 = 3463843) B3463843
theorem B5577005 : Blo 607294 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B1300787 : Blo 607294 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B1235251 : Blo 607294 1235251 := bstep (se 1 (by rfl) ⟨926438, by rfl⟩ : syracuseStep 1235251 = 1852877) B1852877
theorem B1153369 : Blo 607294 1153369 := bstep (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) B865027
theorem B686443 : Blo 607294 686443 := bstep (se 1 (by rfl) ⟨514832, by rfl⟩ : syracuseStep 686443 = 1029665) B1029665
theorem B2193809 : Blo 607294 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B1169815 : Blo 607294 1169815 := bstep (se 1 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 1169815 = 1754723) B1754723
theorem B866713 : Blo 607294 866713 := bstep (se 2 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 866713 = 650035) B650035
theorem B1366451 : Blo 607294 1366451 := bstep (se 1 (by rfl) ⟨1024838, by rfl⟩ : syracuseStep 1366451 = 2049677) B2049677
theorem B1366487 : Blo 607294 1366487 := bstep (se 1 (by rfl) ⟨1024865, by rfl⟩ : syracuseStep 1366487 = 2049731) B2049731
theorem B686551 : Blo 607294 686551 := bstep (se 1 (by rfl) ⟨514913, by rfl⟩ : syracuseStep 686551 = 1029827) B1029827
theorem B2406935 : Blo 607294 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B2259479 : Blo 607294 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B1538635 : Blo 607294 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B6937163 : Blo 607294 6937163 := bstep (se 1 (by rfl) ⟨5202872, by rfl⟩ : syracuseStep 6937163 = 10405745) B10405745
theorem B2603609 : Blo 607294 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B2226781 : Blo 607294 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B1366667 : Blo 607294 1366667 := bstep (se 1 (by rfl) ⟨1025000, by rfl⟩ : syracuseStep 1366667 = 2050001) B2050001
theorem B973451 : Blo 607294 973451 := bstep (se 1 (by rfl) ⟨730088, by rfl⟩ : syracuseStep 973451 = 1460177) B1460177
theorem B973463 : Blo 607294 973463 := bstep (se 1 (by rfl) ⟨730097, by rfl⟩ : syracuseStep 973463 = 1460195) B1460195
theorem B2054807 : Blo 607294 2054807 := bstep (se 1 (by rfl) ⟨1541105, by rfl⟩ : syracuseStep 2054807 = 3082211) B3082211
theorem B1759895 : Blo 607294 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B1366721 : Blo 607294 1366721 := bstep (se 2 (by rfl) ⟨512520, by rfl⟩ : syracuseStep 1366721 = 1025041) B1025041
theorem B8321741 : Blo 607294 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B7805645 : Blo 607294 7805645 := bstep (se 3 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 7805645 = 2927117) B2927117
theorem B1538777 : Blo 607294 1538777 := bstep (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) B1154083
theorem B4627205 : Blo 607294 4627205 := bstep (se 4 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 4627205 = 867601) B867601
theorem B3373841 : Blo 607294 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B768791 : Blo 607294 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B1170199 : Blo 607294 1170199 := bstep (se 1 (by rfl) ⟨877649, by rfl⟩ : syracuseStep 1170199 = 1755299) B1755299
theorem B1391411 : Blo 607294 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B1850177 : Blo 607294 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B3128129 : Blo 607294 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B1735499 : Blo 607294 1735499 := bstep (se 1 (by rfl) ⟨1301624, by rfl⟩ : syracuseStep 1735499 = 2603249) B2603249
theorem B3750787 : Blo 607294 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B2317187 : Blo 607294 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B4397975 : Blo 607294 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B1366937 : Blo 607294 1366937 := bstep (se 2 (by rfl) ⟨512601, by rfl⟩ : syracuseStep 1366937 = 1025203) B1025203
theorem B1367027 : Blo 607294 1367027 := bstep (se 1 (by rfl) ⟨1025270, by rfl⟩ : syracuseStep 1367027 = 2050541) B2050541
theorem B1367063 : Blo 607294 1367063 := bstep (se 1 (by rfl) ⟨1025297, by rfl⟩ : syracuseStep 1367063 = 2050595) B2050595
theorem B3169373 : Blo 607294 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B1948823 : Blo 607294 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B7404695 : Blo 607294 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B2055347 : Blo 607294 2055347 := bstep (se 1 (by rfl) ⟨1541510, by rfl⟩ : syracuseStep 2055347 = 3083021) B3083021
theorem B1367243 : Blo 607294 1367243 := bstep (se 1 (by rfl) ⟨1025432, by rfl⟩ : syracuseStep 1367243 = 2050865) B2050865
theorem B1367297 : Blo 607294 1367297 := bstep (se 2 (by rfl) ⟨512736, by rfl⟩ : syracuseStep 1367297 = 1025473) B1025473
theorem B1301761 : Blo 607294 1301761 := bstep (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) B976321
theorem B1948951 : Blo 607294 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B974155 : Blo 607294 974155 := bstep (se 1 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 974155 = 1461233) B1461233
theorem B925003 : Blo 607294 925003 := bstep (se 1 (by rfl) ⟨693752, by rfl⟩ : syracuseStep 925003 = 1387505) B1387505
theorem B4677041 : Blo 607294 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B2055617 : Blo 607294 2055617 := bstep (se 2 (by rfl) ⟨770856, by rfl⟩ : syracuseStep 2055617 = 1541713) B1541713
theorem B2309579 : Blo 607294 2309579 := bstep (se 1 (by rfl) ⟨1732184, by rfl⟩ : syracuseStep 2309579 = 3464369) B3464369
theorem B769495 : Blo 607294 769495 := bstep (se 1 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 769495 = 1154243) B1154243
theorem B1367513 : Blo 607294 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B2309593 : Blo 607294 2309593 := bstep (se 2 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 2309593 = 1732195) B1732195
theorem B1539607 : Blo 607294 1539607 := bstep (se 1 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 1539607 = 2309411) B2309411
theorem B4931117 : Blo 607294 4931117 := bstep (se 3 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 4931117 = 1849169) B1849169
theorem B1367603 : Blo 607294 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B2006579 : Blo 607294 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B1367639 : Blo 607294 1367639 := bstep (se 1 (by rfl) ⟨1025729, by rfl⟩ : syracuseStep 1367639 = 2051459) B2051459
theorem B974425 : Blo 607294 974425 := bstep (se 2 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 974425 = 730819) B730819
theorem B1154675 : Blo 607294 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B15040241 : Blo 607294 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B1367819 : Blo 607294 1367819 := bstep (se 1 (by rfl) ⟨1025864, by rfl⟩ : syracuseStep 1367819 = 2051729) B2051729
theorem B1154827 : Blo 607294 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B1367873 : Blo 607294 1367873 := bstep (se 2 (by rfl) ⟨512952, by rfl⟩ : syracuseStep 1367873 = 1025905) B1025905
theorem B868171 : Blo 607294 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B974681 : Blo 607294 974681 := bstep (se 2 (by rfl) ⟨365505, by rfl⟩ : syracuseStep 974681 = 731011) B731011
theorem B5849009 : Blo 607294 5849009 := bstep (se 2 (by rfl) ⟨2193378, by rfl⟩ : syracuseStep 5849009 = 4386757) B4386757
theorem B2473907 : Blo 607294 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1540043 : Blo 607294 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B2056157 : Blo 607294 2056157 := bstep (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) B771059
theorem B1368107 : Blo 607294 1368107 := bstep (se 1 (by rfl) ⟨1026080, by rfl⟩ : syracuseStep 1368107 = 2052161) B2052161
theorem B1155131 : Blo 607294 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B5202053 : Blo 607294 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B3948745 : Blo 607294 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B3080429 : Blo 607294 3080429 := bstep (se 3 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 3080429 = 1155161) B1155161
theorem B1540367 : Blo 607294 1540367 := bstep (se 1 (by rfl) ⟨1155275, by rfl⟩ : syracuseStep 1540367 = 2310551) B2310551
theorem B7414033 : Blo 607294 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B2056481 : Blo 607294 2056481 := bstep (se 2 (by rfl) ⟨771180, by rfl⟩ : syracuseStep 2056481 = 1542361) B1542361
theorem B3088691 : Blo 607294 3088691 := bstep (se 1 (by rfl) ⟨2316518, by rfl⟩ : syracuseStep 3088691 = 4633037) B4633037
theorem B1368467 : Blo 607294 1368467 := bstep (se 1 (by rfl) ⟨1026350, by rfl⟩ : syracuseStep 1368467 = 2052701) B2052701
theorem B1647001 : Blo 607294 1647001 := bstep (se 2 (by rfl) ⟨617625, by rfl⟩ : syracuseStep 1647001 = 1235251) B1235251
theorem B1368521 : Blo 607294 1368521 := bstep (se 2 (by rfl) ⟨513195, by rfl⟩ : syracuseStep 1368521 = 1026391) B1026391
theorem B3473867 : Blo 607294 3473867 := bstep (se 1 (by rfl) ⟨2605400, by rfl⟩ : syracuseStep 3473867 = 5210801) B5210801
theorem B1155617 : Blo 607294 1155617 := bstep (se 2 (by rfl) ⟨433356, by rfl⟩ : syracuseStep 1155617 = 866713) B866713
theorem B3089015 : Blo 607294 3089015 := bstep (se 1 (by rfl) ⟨2316761, by rfl⟩ : syracuseStep 3089015 = 4633523) B4633523
theorem B4997861 : Blo 607294 4997861 := bstep (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) B937099
theorem B1155883 : Blo 607294 1155883 := bstep (se 1 (by rfl) ⟨866912, by rfl⟩ : syracuseStep 1155883 = 1733825) B1733825
theorem B5202737 : Blo 607294 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B2057075 : Blo 607294 2057075 := bstep (se 1 (by rfl) ⟨1542806, by rfl⟩ : syracuseStep 2057075 = 3085613) B3085613
theorem B1647479 : Blo 607294 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B3474323 : Blo 607294 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B1950617 : Blo 607294 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B1541065 : Blo 607294 1541065 := bstep (se 2 (by rfl) ⟨577899, by rfl⟩ : syracuseStep 1541065 = 1155799) B1155799
theorem B2475019 : Blo 607294 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B762895 : Blo 607294 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B3081239 : Blo 607294 3081239 := bstep (se 1 (by rfl) ⟨2310929, by rfl⟩ : syracuseStep 3081239 = 4621859) B4621859
theorem B2221085 : Blo 607294 2221085 := bstep (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) B832907
theorem B771115 : Blo 607294 771115 := bstep (se 1 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 771115 = 1156673) B1156673
theorem B5850157 : Blo 607294 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B4621373 : Blo 607294 4621373 := bstep (se 3 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 4621373 = 1733015) B1733015
theorem B1541207 : Blo 607294 1541207 := bstep (se 1 (by rfl) ⟨1155905, by rfl⟩ : syracuseStep 1541207 = 2311811) B2311811
theorem B6661237 : Blo 607294 6661237 := bstep (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) B624491
theorem B607367 : Blo 607294 607367 := bstep (se 1 (by rfl) ⟨455525, by rfl⟩ : syracuseStep 607367 = 911051) B911051
theorem B1369223 : Blo 607294 1369223 := bstep (se 1 (by rfl) ⟨1026917, by rfl⟩ : syracuseStep 1369223 = 2053835) B2053835
theorem B607375 : Blo 607294 607375 := bstep (se 1 (by rfl) ⟨455531, by rfl⟩ : syracuseStep 607375 = 911063) B911063
theorem B4678829 : Blo 607294 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B3703981 : Blo 607294 3703981 := bstep (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) B1388993
theorem B615611 : Blo 607294 615611 := bstep (se 1 (by rfl) ⟨461708, by rfl⟩ : syracuseStep 615611 = 923417) B923417
theorem B607419 : Blo 607294 607419 := bstep (se 1 (by rfl) ⟨455564, by rfl⟩ : syracuseStep 607419 = 911129) B911129
theorem B607495 : Blo 607294 607495 := bstep (se 1 (by rfl) ⟨455621, by rfl⟩ : syracuseStep 607495 = 911243) B911243
theorem B607503 : Blo 607294 607503 := bstep (se 1 (by rfl) ⟨455627, by rfl⟩ : syracuseStep 607503 = 911255) B911255
theorem B607547 : Blo 607294 607547 := bstep (se 1 (by rfl) ⟨455660, by rfl⟩ : syracuseStep 607547 = 911321) B911321
theorem B1369403 : Blo 607294 1369403 := bstep (se 1 (by rfl) ⟨1027052, by rfl⟩ : syracuseStep 1369403 = 2054105) B2054105
theorem B1729907 : Blo 607294 1729907 := bstep (se 1 (by rfl) ⟨1297430, by rfl⟩ : syracuseStep 1729907 = 2594861) B2594861
theorem B1025399 : Blo 607294 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B14787971 : Blo 607294 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B607623 : Blo 607294 607623 := bstep (se 1 (by rfl) ⟨455717, by rfl⟩ : syracuseStep 607623 = 911435) B911435
theorem B607631 : Blo 607294 607631 := bstep (se 1 (by rfl) ⟨455723, by rfl⟩ : syracuseStep 607631 = 911447) B911447
theorem B1369529 : Blo 607294 1369529 := bstep (se 2 (by rfl) ⟨513573, by rfl⟩ : syracuseStep 1369529 = 1027147) B1027147
theorem B607675 : Blo 607294 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B4613597 : Blo 607294 4613597 := bstep (se 3 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 4613597 = 1730099) B1730099
theorem B607751 : Blo 607294 607751 := bstep (se 1 (by rfl) ⟨455813, by rfl⟩ : syracuseStep 607751 = 911627) B911627
theorem B607759 : Blo 607294 607759 := bstep (se 1 (by rfl) ⟨455819, by rfl⟩ : syracuseStep 607759 = 911639) B911639
theorem B607803 : Blo 607294 607803 := bstep (se 1 (by rfl) ⟨455852, by rfl⟩ : syracuseStep 607803 = 911705) B911705
theorem B2049623 : Blo 607294 2049623 := bstep (se 1 (by rfl) ⟨1537217, by rfl⟩ : syracuseStep 2049623 = 3074435) B3074435
theorem B910967 : Blo 607294 910967 := bstep (se 1 (by rfl) ⟨683225, by rfl⟩ : syracuseStep 910967 = 1366451) B1366451
theorem B607879 : Blo 607294 607879 := bstep (se 1 (by rfl) ⟨455909, by rfl⟩ : syracuseStep 607879 = 911819) B911819
theorem B910991 : Blo 607294 910991 := bstep (se 1 (by rfl) ⟨683243, by rfl⟩ : syracuseStep 910991 = 1366487) B1366487
theorem B607887 : Blo 607294 607887 := bstep (se 1 (by rfl) ⟨455915, by rfl⟩ : syracuseStep 607887 = 911831) B911831
theorem B911033 : Blo 607294 911033 := bstep (se 2 (by rfl) ⟨341637, by rfl⟩ : syracuseStep 911033 = 683275) B683275
theorem B607931 : Blo 607294 607931 := bstep (se 1 (by rfl) ⟨455948, by rfl⟩ : syracuseStep 607931 = 911897) B911897
theorem B2598601 : Blo 607294 2598601 := bstep (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) B1948951
theorem B4933349 : Blo 607294 4933349 := bstep (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) B925003
theorem B911111 : Blo 607294 911111 := bstep (se 1 (by rfl) ⟨683333, by rfl⟩ : syracuseStep 911111 = 1366667) B1366667
theorem B648967 : Blo 607294 648967 := bstep (se 1 (by rfl) ⟨486725, by rfl⟩ : syracuseStep 648967 = 973451) B973451
theorem B608007 : Blo 607294 608007 := bstep (se 1 (by rfl) ⟨456005, by rfl⟩ : syracuseStep 608007 = 912011) B912011
theorem B608015 : Blo 607294 608015 := bstep (se 1 (by rfl) ⟨456011, by rfl⟩ : syracuseStep 608015 = 912023) B912023
theorem B1369871 : Blo 607294 1369871 := bstep (se 1 (by rfl) ⟨1027403, by rfl⟩ : syracuseStep 1369871 = 2054807) B2054807
theorem B1173263 : Blo 607294 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B1369889 : Blo 607294 1369889 := bstep (se 2 (by rfl) ⟨513708, by rfl⟩ : syracuseStep 1369889 = 1027417) B1027417
theorem B911147 : Blo 607294 911147 := bstep (se 1 (by rfl) ⟨683360, by rfl⟩ : syracuseStep 911147 = 1366721) B1366721
theorem B821035 : Blo 607294 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B5547827 : Blo 607294 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B5203763 : Blo 607294 5203763 := bstep (se 1 (by rfl) ⟨3902822, by rfl⟩ : syracuseStep 5203763 = 7805645) B7805645
theorem B1025851 : Blo 607294 1025851 := bstep (se 1 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 1025851 = 1538777) B1538777
theorem B608059 : Blo 607294 608059 := bstep (se 1 (by rfl) ⟨456044, by rfl⟩ : syracuseStep 608059 = 912089) B912089
theorem B911177 : Blo 607294 911177 := bstep (se 2 (by rfl) ⟨341691, by rfl⟩ : syracuseStep 911177 = 683383) B683383
theorem B26388341 : Blo 607294 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B927607 : Blo 607294 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B608135 : Blo 607294 608135 := bstep (se 1 (by rfl) ⟨456101, by rfl⟩ : syracuseStep 608135 = 912203) B912203
theorem B1156999 : Blo 607294 1156999 := bstep (se 1 (by rfl) ⟨867749, by rfl⟩ : syracuseStep 1156999 = 1735499) B1735499
theorem B608143 : Blo 607294 608143 := bstep (se 1 (by rfl) ⟨456107, by rfl⟩ : syracuseStep 608143 = 912215) B912215
theorem B3458969 : Blo 607294 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B911291 : Blo 607294 911291 := bstep (se 1 (by rfl) ⟨683468, by rfl⟩ : syracuseStep 911291 = 1366937) B1366937
theorem B608187 : Blo 607294 608187 := bstep (se 1 (by rfl) ⟨456140, by rfl⟩ : syracuseStep 608187 = 912281) B912281
theorem B1025993 : Blo 607294 1025993 := bstep (se 2 (by rfl) ⟨384747, by rfl⟩ : syracuseStep 1025993 = 769495) B769495
theorem B911351 : Blo 607294 911351 := bstep (se 1 (by rfl) ⟨683513, by rfl⟩ : syracuseStep 911351 = 1367027) B1367027
theorem B772087 : Blo 607294 772087 := bstep (se 1 (by rfl) ⟨579065, by rfl⟩ : syracuseStep 772087 = 1158131) B1158131
theorem B608263 : Blo 607294 608263 := bstep (se 1 (by rfl) ⟨456197, by rfl⟩ : syracuseStep 608263 = 912395) B912395
theorem B911375 : Blo 607294 911375 := bstep (se 1 (by rfl) ⟨683531, by rfl⟩ : syracuseStep 911375 = 1367063) B1367063
theorem B608271 : Blo 607294 608271 := bstep (se 1 (by rfl) ⟨456203, by rfl⟩ : syracuseStep 608271 = 912407) B912407
theorem B911417 : Blo 607294 911417 := bstep (se 2 (by rfl) ⟨341781, by rfl⟩ : syracuseStep 911417 = 683563) B683563
theorem B608315 : Blo 607294 608315 := bstep (se 1 (by rfl) ⟨456236, by rfl⟩ : syracuseStep 608315 = 912473) B912473
theorem B2050109 : Blo 607294 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B1558643 : Blo 607294 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B1370231 : Blo 607294 1370231 := bstep (se 1 (by rfl) ⟨1027673, by rfl⟩ : syracuseStep 1370231 = 2055347) B2055347
theorem B911495 : Blo 607294 911495 := bstep (se 1 (by rfl) ⟨683621, by rfl⟩ : syracuseStep 911495 = 1367243) B1367243
theorem B608391 : Blo 607294 608391 := bstep (se 1 (by rfl) ⟨456293, by rfl⟩ : syracuseStep 608391 = 912587) B912587
theorem B608399 : Blo 607294 608399 := bstep (se 1 (by rfl) ⟨456299, by rfl⟩ : syracuseStep 608399 = 912599) B912599
theorem B911531 : Blo 607294 911531 := bstep (se 1 (by rfl) ⟨683648, by rfl⟩ : syracuseStep 911531 = 1367297) B1367297
theorem B608443 : Blo 607294 608443 := bstep (se 1 (by rfl) ⟨456332, by rfl⟩ : syracuseStep 608443 = 912665) B912665
theorem B911561 : Blo 607294 911561 := bstep (se 2 (by rfl) ⟨341835, by rfl⟩ : syracuseStep 911561 = 683671) B683671
theorem B608519 : Blo 607294 608519 := bstep (se 1 (by rfl) ⟨456389, by rfl⟩ : syracuseStep 608519 = 912779) B912779
theorem B68512013 : Blo 607294 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B608527 : Blo 607294 608527 := bstep (se 1 (by rfl) ⟨456395, by rfl⟩ : syracuseStep 608527 = 912791) B912791
theorem B1370411 : Blo 607294 1370411 := bstep (se 1 (by rfl) ⟨1027808, by rfl⟩ : syracuseStep 1370411 = 2055617) B2055617
theorem B911675 : Blo 607294 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B608571 : Blo 607294 608571 := bstep (se 1 (by rfl) ⟨456428, by rfl⟩ : syracuseStep 608571 = 912857) B912857
theorem B3287411 : Blo 607294 3287411 := bstep (se 1 (by rfl) ⟨2465558, by rfl⟩ : syracuseStep 3287411 = 4931117) B4931117
theorem B911735 : Blo 607294 911735 := bstep (se 1 (by rfl) ⟨683801, by rfl⟩ : syracuseStep 911735 = 1367603) B1367603
theorem B1337719 : Blo 607294 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B608647 : Blo 607294 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B911759 : Blo 607294 911759 := bstep (se 1 (by rfl) ⟨683819, by rfl⟩ : syracuseStep 911759 = 1367639) B1367639
theorem B608655 : Blo 607294 608655 := bstep (se 1 (by rfl) ⟨456491, by rfl⟩ : syracuseStep 608655 = 912983) B912983
theorem B3664273 : Blo 607294 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B911801 : Blo 607294 911801 := bstep (se 2 (by rfl) ⟨341925, by rfl⟩ : syracuseStep 911801 = 683851) B683851
theorem B608699 : Blo 607294 608699 := bstep (se 1 (by rfl) ⟨456524, by rfl⟩ : syracuseStep 608699 = 913049) B913049
theorem B1157561 : Blo 607294 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B911879 : Blo 607294 911879 := bstep (se 1 (by rfl) ⟨683909, by rfl⟩ : syracuseStep 911879 = 1367819) B1367819
theorem B608775 : Blo 607294 608775 := bstep (se 1 (by rfl) ⟨456581, by rfl⟩ : syracuseStep 608775 = 913163) B913163
theorem B608783 : Blo 607294 608783 := bstep (se 1 (by rfl) ⟨456587, by rfl⟩ : syracuseStep 608783 = 913175) B913175
theorem B911915 : Blo 607294 911915 := bstep (se 1 (by rfl) ⟨683936, by rfl⟩ : syracuseStep 911915 = 1367873) B1367873
theorem B649787 : Blo 607294 649787 := bstep (se 1 (by rfl) ⟨487340, by rfl⟩ : syracuseStep 649787 = 974681) B974681
theorem B608827 : Blo 607294 608827 := bstep (se 1 (by rfl) ⟨456620, by rfl⟩ : syracuseStep 608827 = 913241) B913241
theorem B2345539 : Blo 607294 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B7817795 : Blo 607294 7817795 := bstep (se 1 (by rfl) ⟨5863346, by rfl⟩ : syracuseStep 7817795 = 11726693) B11726693
theorem B911945 : Blo 607294 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B1026695 : Blo 607294 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B608903 : Blo 607294 608903 := bstep (se 1 (by rfl) ⟨456677, by rfl⟩ : syracuseStep 608903 = 913355) B913355
theorem B608911 : Blo 607294 608911 := bstep (se 1 (by rfl) ⟨456683, by rfl⟩ : syracuseStep 608911 = 913367) B913367
theorem B1370771 : Blo 607294 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B912059 : Blo 607294 912059 := bstep (se 1 (by rfl) ⟨684044, by rfl⟩ : syracuseStep 912059 = 1368089) B1368089
theorem B608955 : Blo 607294 608955 := bstep (se 1 (by rfl) ⟨456716, by rfl⟩ : syracuseStep 608955 = 913433) B913433
theorem B1370825 : Blo 607294 1370825 := bstep (se 2 (by rfl) ⟨514059, by rfl⟩ : syracuseStep 1370825 = 1028119) B1028119
theorem B912119 : Blo 607294 912119 := bstep (se 1 (by rfl) ⟨684089, by rfl⟩ : syracuseStep 912119 = 1368179) B1368179
theorem B1952513 : Blo 607294 1952513 := bstep (se 2 (by rfl) ⟨732192, by rfl⟩ : syracuseStep 1952513 = 1464385) B1464385
theorem B15575813 : Blo 607294 15575813 := bstep (se 4 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 15575813 = 2920465) B2920465
theorem B609031 : Blo 607294 609031 := bstep (se 1 (by rfl) ⟨456773, by rfl⟩ : syracuseStep 609031 = 913547) B913547
theorem B912143 : Blo 607294 912143 := bstep (se 1 (by rfl) ⟨684107, by rfl⟩ : syracuseStep 912143 = 1368215) B1368215
theorem B609039 : Blo 607294 609039 := bstep (se 1 (by rfl) ⟨456779, by rfl⟩ : syracuseStep 609039 = 913559) B913559
theorem B1649423 : Blo 607294 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B912185 : Blo 607294 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B609083 : Blo 607294 609083 := bstep (se 1 (by rfl) ⟨456812, by rfl⟩ : syracuseStep 609083 = 913625) B913625
theorem B912263 : Blo 607294 912263 := bstep (se 1 (by rfl) ⟨684197, by rfl⟩ : syracuseStep 912263 = 1368395) B1368395
theorem B609159 : Blo 607294 609159 := bstep (se 1 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 609159 = 913739) B913739
theorem B609167 : Blo 607294 609167 := bstep (se 1 (by rfl) ⟨456875, by rfl⟩ : syracuseStep 609167 = 913751) B913751
theorem B912299 : Blo 607294 912299 := bstep (se 1 (by rfl) ⟨684224, by rfl⟩ : syracuseStep 912299 = 1368449) B1368449
theorem B3468217 : Blo 607294 3468217 := bstep (se 2 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 3468217 = 2601163) B2601163
theorem B609211 : Blo 607294 609211 := bstep (se 1 (by rfl) ⟨456908, by rfl⟩ : syracuseStep 609211 = 913817) B913817
theorem B912329 : Blo 607294 912329 := bstep (se 2 (by rfl) ⟨342123, by rfl⟩ : syracuseStep 912329 = 684247) B684247
theorem B609287 : Blo 607294 609287 := bstep (se 1 (by rfl) ⟨456965, by rfl⟩ : syracuseStep 609287 = 913931) B913931
theorem B3075083 : Blo 607294 3075083 := bstep (se 1 (by rfl) ⟨2306312, by rfl⟩ : syracuseStep 3075083 = 4612625) B4612625
theorem B609295 : Blo 607294 609295 := bstep (se 1 (by rfl) ⟨456971, by rfl⟩ : syracuseStep 609295 = 913943) B913943
theorem B912443 : Blo 607294 912443 := bstep (se 1 (by rfl) ⟨684332, by rfl⟩ : syracuseStep 912443 = 1368665) B1368665
theorem B609339 : Blo 607294 609339 := bstep (se 1 (by rfl) ⟨457004, by rfl⟩ : syracuseStep 609339 = 914009) B914009
theorem B1690739 : Blo 607294 1690739 := bstep (se 1 (by rfl) ⟨1268054, by rfl⟩ : syracuseStep 1690739 = 2536109) B2536109
theorem B912503 : Blo 607294 912503 := bstep (se 1 (by rfl) ⟨684377, by rfl⟩ : syracuseStep 912503 = 1368755) B1368755
theorem B1543283 : Blo 607294 1543283 := bstep (se 1 (by rfl) ⟨1157462, by rfl⟩ : syracuseStep 1543283 = 2314925) B2314925
theorem B609415 : Blo 607294 609415 := bstep (se 1 (by rfl) ⟨457061, by rfl⟩ : syracuseStep 609415 = 914123) B914123
theorem B912527 : Blo 607294 912527 := bstep (se 1 (by rfl) ⟨684395, by rfl⟩ : syracuseStep 912527 = 1368791) B1368791
theorem B822415 : Blo 607294 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B609423 : Blo 607294 609423 := bstep (se 1 (by rfl) ⟨457067, by rfl⟩ : syracuseStep 609423 = 914135) B914135
theorem B3075245 : Blo 607294 3075245 := bstep (se 3 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 3075245 = 1153217) B1153217
theorem B912569 : Blo 607294 912569 := bstep (se 2 (by rfl) ⟨342213, by rfl⟩ : syracuseStep 912569 = 684427) B684427
theorem B609467 : Blo 607294 609467 := bstep (se 1 (by rfl) ⟨457100, by rfl⟩ : syracuseStep 609467 = 914201) B914201
theorem B1559753 : Blo 607294 1559753 := bstep (se 2 (by rfl) ⟨584907, by rfl⟩ : syracuseStep 1559753 = 1169815) B1169815
theorem B912647 : Blo 607294 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B609543 : Blo 607294 609543 := bstep (se 1 (by rfl) ⟨457157, by rfl⟩ : syracuseStep 609543 = 914315) B914315
theorem B2600207 : Blo 607294 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B1027343 : Blo 607294 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B609551 : Blo 607294 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B912683 : Blo 607294 912683 := bstep (se 1 (by rfl) ⟨684512, by rfl⟩ : syracuseStep 912683 = 1369025) B1369025
theorem B609595 : Blo 607294 609595 := bstep (se 1 (by rfl) ⟨457196, by rfl⟩ : syracuseStep 609595 = 914393) B914393
theorem B912713 : Blo 607294 912713 := bstep (se 2 (by rfl) ⟨342267, by rfl⟩ : syracuseStep 912713 = 684535) B684535
theorem B17567077 : Blo 607294 17567077 := bstep (se 4 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 17567077 = 3293827) B3293827
theorem B1371527 : Blo 607294 1371527 := bstep (se 1 (by rfl) ⟨1028645, by rfl⟩ : syracuseStep 1371527 = 2057291) B2057291
theorem B609671 : Blo 607294 609671 := bstep (se 1 (by rfl) ⟨457253, by rfl⟩ : syracuseStep 609671 = 914507) B914507
theorem B609679 : Blo 607294 609679 := bstep (se 1 (by rfl) ⟨457259, by rfl⟩ : syracuseStep 609679 = 914519) B914519
theorem B2059667 : Blo 607294 2059667 := bstep (se 1 (by rfl) ⟨1544750, by rfl⟩ : syracuseStep 2059667 = 3089501) B3089501
theorem B2051513 : Blo 607294 2051513 := bstep (se 2 (by rfl) ⟨769317, by rfl⟩ : syracuseStep 2051513 = 1538635) B1538635
theorem B14069177 : Blo 607294 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B912827 : Blo 607294 912827 := bstep (se 1 (by rfl) ⟨684620, by rfl⟩ : syracuseStep 912827 = 1369241) B1369241
theorem B609723 : Blo 607294 609723 := bstep (se 1 (by rfl) ⟨457292, by rfl⟩ : syracuseStep 609723 = 914585) B914585
theorem B2969041 : Blo 607294 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B912887 : Blo 607294 912887 := bstep (se 1 (by rfl) ⟨684665, by rfl⟩ : syracuseStep 912887 = 1369331) B1369331
theorem B3296771 : Blo 607294 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B683527 : Blo 607294 683527 := bstep (se 1 (by rfl) ⟨512645, by rfl⟩ : syracuseStep 683527 = 1025291) B1025291
theorem B609799 : Blo 607294 609799 := bstep (se 1 (by rfl) ⟨457349, by rfl⟩ : syracuseStep 609799 = 914699) B914699
theorem B912911 : Blo 607294 912911 := bstep (se 1 (by rfl) ⟨684683, by rfl⟩ : syracuseStep 912911 = 1369367) B1369367
theorem B609807 : Blo 607294 609807 := bstep (se 1 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 609807 = 914711) B914711
theorem B912953 : Blo 607294 912953 := bstep (se 2 (by rfl) ⟨342357, by rfl⟩ : syracuseStep 912953 = 684715) B684715
theorem B1371707 : Blo 607294 1371707 := bstep (se 1 (by rfl) ⟨1028780, by rfl⟩ : syracuseStep 1371707 = 2057561) B2057561
theorem B609851 : Blo 607294 609851 := bstep (se 1 (by rfl) ⟨457388, by rfl⟩ : syracuseStep 609851 = 914777) B914777
theorem B1543799 : Blo 607294 1543799 := bstep (se 1 (by rfl) ⟨1157849, by rfl⟩ : syracuseStep 1543799 = 2315699) B2315699
theorem B913031 : Blo 607294 913031 := bstep (se 1 (by rfl) ⟨684773, by rfl⟩ : syracuseStep 913031 = 1369547) B1369547
theorem B609927 : Blo 607294 609927 := bstep (se 1 (by rfl) ⟨457445, by rfl⟩ : syracuseStep 609927 = 914891) B914891
theorem B609935 : Blo 607294 609935 := bstep (se 1 (by rfl) ⟨457451, by rfl⟩ : syracuseStep 609935 = 914903) B914903
theorem B913067 : Blo 607294 913067 := bstep (se 1 (by rfl) ⟨684800, by rfl⟩ : syracuseStep 913067 = 1369601) B1369601
theorem B3116717 : Blo 607294 3116717 := bstep (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) B1168769
theorem B1371833 : Blo 607294 1371833 := bstep (se 2 (by rfl) ⟨514437, by rfl⟩ : syracuseStep 1371833 = 1028875) B1028875
theorem B683707 : Blo 607294 683707 := bstep (se 1 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 683707 = 1025561) B1025561
theorem B609979 : Blo 607294 609979 := bstep (se 1 (by rfl) ⟨457484, by rfl⟩ : syracuseStep 609979 = 914969) B914969
theorem B1560265 : Blo 607294 1560265 := bstep (se 2 (by rfl) ⟨585099, by rfl⟩ : syracuseStep 1560265 = 1170199) B1170199
theorem B913097 : Blo 607294 913097 := bstep (se 2 (by rfl) ⟨342411, by rfl⟩ : syracuseStep 913097 = 684823) B684823
theorem B3337985 : Blo 607294 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B610055 : Blo 607294 610055 := bstep (se 1 (by rfl) ⟨457541, by rfl⟩ : syracuseStep 610055 = 915083) B915083
theorem B1756939 : Blo 607294 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B1732367 : Blo 607294 1732367 := bstep (se 1 (by rfl) ⟨1299275, by rfl⟩ : syracuseStep 1732367 = 2598551) B2598551
theorem B610063 : Blo 607294 610063 := bstep (se 1 (by rfl) ⟨457547, by rfl⟩ : syracuseStep 610063 = 915095) B915095
theorem B1027883 : Blo 607294 1027883 := bstep (se 1 (by rfl) ⟨770912, by rfl⟩ : syracuseStep 1027883 = 1541825) B1541825
theorem B5009203 : Blo 607294 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B913211 : Blo 607294 913211 := bstep (se 1 (by rfl) ⟨684908, by rfl⟩ : syracuseStep 913211 = 1369817) B1369817
theorem B610107 : Blo 607294 610107 := bstep (se 1 (by rfl) ⟨457580, by rfl⟩ : syracuseStep 610107 = 915161) B915161
theorem B5001049 : Blo 607294 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B913271 : Blo 607294 913271 := bstep (se 1 (by rfl) ⟨684953, by rfl⟩ : syracuseStep 913271 = 1369907) B1369907
theorem B610183 : Blo 607294 610183 := bstep (se 1 (by rfl) ⟨457637, by rfl⟩ : syracuseStep 610183 = 915275) B915275
theorem B913295 : Blo 607294 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B610191 : Blo 607294 610191 := bstep (se 1 (by rfl) ⟨457643, by rfl⟩ : syracuseStep 610191 = 915287) B915287
theorem B3903385 : Blo 607294 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B913337 : Blo 607294 913337 := bstep (se 2 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 913337 = 685003) B685003
theorem B610235 : Blo 607294 610235 := bstep (se 1 (by rfl) ⟨457676, by rfl⟩ : syracuseStep 610235 = 915353) B915353
theorem B733115 : Blo 607294 733115 := bstep (se 1 (by rfl) ⟨549836, by rfl⟩ : syracuseStep 733115 = 1099673) B1099673
theorem B913415 : Blo 607294 913415 := bstep (se 1 (by rfl) ⟨685061, by rfl⟩ : syracuseStep 913415 = 1370123) B1370123
theorem B2052107 : Blo 607294 2052107 := bstep (se 1 (by rfl) ⟨1539080, by rfl⟩ : syracuseStep 2052107 = 3078161) B3078161
theorem B1372175 : Blo 607294 1372175 := bstep (se 1 (by rfl) ⟨1029131, by rfl⟩ : syracuseStep 1372175 = 2058263) B2058263
theorem B3084317 : Blo 607294 3084317 := bstep (se 3 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 3084317 = 1156619) B1156619
theorem B1372193 : Blo 607294 1372193 := bstep (se 2 (by rfl) ⟨514572, by rfl⟩ : syracuseStep 1372193 = 1029145) B1029145
theorem B913451 : Blo 607294 913451 := bstep (se 1 (by rfl) ⟨685088, by rfl⟩ : syracuseStep 913451 = 1370177) B1370177
theorem B913481 : Blo 607294 913481 := bstep (se 2 (by rfl) ⟨342555, by rfl⟩ : syracuseStep 913481 = 685111) B685111
theorem B2052215 : Blo 607294 2052215 := bstep (se 1 (by rfl) ⟨1539161, by rfl⟩ : syracuseStep 2052215 = 3078323) B3078323
theorem B684175 : Blo 607294 684175 := bstep (se 1 (by rfl) ⟨513131, by rfl⟩ : syracuseStep 684175 = 1026263) B1026263
theorem B1028281 : Blo 607294 1028281 := bstep (se 2 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 1028281 = 771211) B771211
theorem B913595 : Blo 607294 913595 := bstep (se 1 (by rfl) ⟨685196, by rfl⟩ : syracuseStep 913595 = 1370393) B1370393
theorem B3297509 : Blo 607294 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B913655 : Blo 607294 913655 := bstep (se 1 (by rfl) ⟨685241, by rfl⟩ : syracuseStep 913655 = 1370483) B1370483
theorem B913679 : Blo 607294 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B913721 : Blo 607294 913721 := bstep (se 2 (by rfl) ⟨342645, by rfl⟩ : syracuseStep 913721 = 685291) B685291
theorem B823609 : Blo 607294 823609 := bstep (se 2 (by rfl) ⟨308853, by rfl⟩ : syracuseStep 823609 = 617707) B617707
theorem B1372535 : Blo 607294 1372535 := bstep (se 1 (by rfl) ⟨1029401, by rfl⟩ : syracuseStep 1372535 = 2058803) B2058803
theorem B4624775 : Blo 607294 4624775 := bstep (se 1 (by rfl) ⟨3468581, by rfl⟩ : syracuseStep 4624775 = 6937163) B6937163
theorem B913799 : Blo 607294 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B1388947 : Blo 607294 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B913835 : Blo 607294 913835 := bstep (se 1 (by rfl) ⟨685376, by rfl⟩ : syracuseStep 913835 = 1370753) B1370753
theorem B864697 : Blo 607294 864697 := bstep (se 2 (by rfl) ⟨324261, by rfl⟩ : syracuseStep 864697 = 648523) B648523
theorem B1298873 : Blo 607294 1298873 := bstep (se 2 (by rfl) ⟨487077, by rfl⟩ : syracuseStep 1298873 = 974155) B974155
theorem B913865 : Blo 607294 913865 := bstep (se 2 (by rfl) ⟨342699, by rfl⟩ : syracuseStep 913865 = 685399) B685399
theorem B3084803 : Blo 607294 3084803 := bstep (se 1 (by rfl) ⟨2313602, by rfl⟩ : syracuseStep 3084803 = 4627205) B4627205
theorem B2249227 : Blo 607294 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1233451 : Blo 607294 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B2085419 : Blo 607294 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B1372715 : Blo 607294 1372715 := bstep (se 1 (by rfl) ⟨1029536, by rfl⟩ : syracuseStep 1372715 = 2059073) B2059073
theorem B913979 : Blo 607294 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B2929213 : Blo 607294 2929213 := bstep (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) B1098455
theorem B1544791 : Blo 607294 1544791 := bstep (se 1 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 1544791 = 2317187) B2317187
theorem B914039 : Blo 607294 914039 := bstep (se 1 (by rfl) ⟨685529, by rfl⟩ : syracuseStep 914039 = 1371059) B1371059
theorem B684679 : Blo 607294 684679 := bstep (se 1 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 684679 = 1027019) B1027019
theorem B914063 : Blo 607294 914063 := bstep (se 1 (by rfl) ⟨685547, by rfl⟩ : syracuseStep 914063 = 1371095) B1371095
theorem B3522797 : Blo 607294 3522797 := bstep (se 3 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 3522797 = 1321049) B1321049
theorem B914105 : Blo 607294 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B2052809 : Blo 607294 2052809 := bstep (se 2 (by rfl) ⟨769803, by rfl⟩ : syracuseStep 2052809 = 1539607) B1539607
theorem B3076865 : Blo 607294 3076865 := bstep (se 2 (by rfl) ⟨1153824, by rfl⟩ : syracuseStep 3076865 = 2307649) B2307649
theorem B914183 : Blo 607294 914183 := bstep (se 1 (by rfl) ⟨685637, by rfl⟩ : syracuseStep 914183 = 1371275) B1371275
theorem B1299215 : Blo 607294 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B4936463 : Blo 607294 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B1299233 : Blo 607294 1299233 := bstep (se 2 (by rfl) ⟨487212, by rfl⟩ : syracuseStep 1299233 = 974425) B974425
theorem B914219 : Blo 607294 914219 := bstep (se 1 (by rfl) ⟨685664, by rfl⟩ : syracuseStep 914219 = 1371329) B1371329
theorem B684859 : Blo 607294 684859 := bstep (se 1 (by rfl) ⟨513644, by rfl⟩ : syracuseStep 684859 = 1027289) B1027289
theorem B914249 : Blo 607294 914249 := bstep (se 2 (by rfl) ⟨342843, by rfl⟩ : syracuseStep 914249 = 685687) B685687
theorem B1028983 : Blo 607294 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B2306951 : Blo 607294 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B1373075 : Blo 607294 1373075 := bstep (se 1 (by rfl) ⟨1029806, by rfl⟩ : syracuseStep 1373075 = 2059613) B2059613
theorem B914363 : Blo 607294 914363 := bstep (se 1 (by rfl) ⟨685772, by rfl⟩ : syracuseStep 914363 = 1371545) B1371545
theorem B1373129 : Blo 607294 1373129 := bstep (se 2 (by rfl) ⟨514923, by rfl⟩ : syracuseStep 1373129 = 1029847) B1029847
theorem B3118027 : Blo 607294 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B914423 : Blo 607294 914423 := bstep (se 1 (by rfl) ⟨685817, by rfl⟩ : syracuseStep 914423 = 1371635) B1371635
theorem B1094671 : Blo 607294 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B914447 : Blo 607294 914447 := bstep (se 1 (by rfl) ⟨685835, by rfl⟩ : syracuseStep 914447 = 1371671) B1371671
theorem B914489 : Blo 607294 914489 := bstep (se 2 (by rfl) ⟨342933, by rfl⟩ : syracuseStep 914489 = 685867) B685867
theorem B1029179 : Blo 607294 1029179 := bstep (se 1 (by rfl) ⟨771884, by rfl⟩ : syracuseStep 1029179 = 1543769) B1543769
theorem B914567 : Blo 607294 914567 := bstep (se 1 (by rfl) ⟨685925, by rfl⟩ : syracuseStep 914567 = 1371851) B1371851
theorem B914603 : Blo 607294 914603 := bstep (se 1 (by rfl) ⟨685952, by rfl⟩ : syracuseStep 914603 = 1371905) B1371905
theorem B1946825 : Blo 607294 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B914633 : Blo 607294 914633 := bstep (se 2 (by rfl) ⟨342987, by rfl⟩ : syracuseStep 914633 = 685975) B685975
theorem B685327 : Blo 607294 685327 := bstep (se 1 (by rfl) ⟨513995, by rfl⟩ : syracuseStep 685327 = 1027991) B1027991
theorem B1537339 : Blo 607294 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B914747 : Blo 607294 914747 := bstep (se 1 (by rfl) ⟨686060, by rfl⟩ : syracuseStep 914747 = 1372121) B1372121
theorem B1734007 : Blo 607294 1734007 := bstep (se 1 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 1734007 = 2601011) B2601011
theorem B914807 : Blo 607294 914807 := bstep (se 1 (by rfl) ⟨686105, by rfl⟩ : syracuseStep 914807 = 1372211) B1372211
theorem B2053511 : Blo 607294 2053511 := bstep (se 1 (by rfl) ⟨1540133, by rfl⟩ : syracuseStep 2053511 = 3080267) B3080267
theorem B914831 : Blo 607294 914831 := bstep (se 1 (by rfl) ⟨686123, by rfl⟩ : syracuseStep 914831 = 1372247) B1372247
theorem B1734041 : Blo 607294 1734041 := bstep (se 2 (by rfl) ⟨650265, by rfl⟩ : syracuseStep 1734041 = 1300531) B1300531
theorem B12490163 : Blo 607294 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B914873 : Blo 607294 914873 := bstep (se 2 (by rfl) ⟨343077, by rfl⟩ : syracuseStep 914873 = 686155) B686155
theorem B1537481 : Blo 607294 1537481 := bstep (se 2 (by rfl) ⟨576555, by rfl⟩ : syracuseStep 1537481 = 1153111) B1153111
theorem B1029577 : Blo 607294 1029577 := bstep (se 2 (by rfl) ⟨386091, by rfl⟩ : syracuseStep 1029577 = 772183) B772183
theorem B2315729 : Blo 607294 2315729 := bstep (se 2 (by rfl) ⟨868398, by rfl⟩ : syracuseStep 2315729 = 1736797) B1736797
theorem B3462659 : Blo 607294 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B914951 : Blo 607294 914951 := bstep (se 1 (by rfl) ⟨686213, by rfl⟩ : syracuseStep 914951 = 1372427) B1372427
theorem B1734155 : Blo 607294 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B5199389 : Blo 607294 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B3077675 : Blo 607294 3077675 := bstep (se 1 (by rfl) ⟨2308256, by rfl⟩ : syracuseStep 3077675 = 4616513) B4616513
theorem B914987 : Blo 607294 914987 := bstep (se 1 (by rfl) ⟨686240, by rfl⟩ : syracuseStep 914987 = 1372481) B1372481
theorem B915017 : Blo 607294 915017 := bstep (se 2 (by rfl) ⟨343131, by rfl⟩ : syracuseStep 915017 = 686263) B686263
theorem B8451661 : Blo 607294 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B865927 : Blo 607294 865927 := bstep (se 1 (by rfl) ⟨649445, by rfl⟩ : syracuseStep 865927 = 1298891) B1298891
theorem B915131 : Blo 607294 915131 := bstep (se 1 (by rfl) ⟨686348, by rfl⟩ : syracuseStep 915131 = 1372697) B1372697
theorem B915191 : Blo 607294 915191 := bstep (se 1 (by rfl) ⟨686393, by rfl⟩ : syracuseStep 915191 = 1372787) B1372787
theorem B2053889 : Blo 607294 2053889 := bstep (se 2 (by rfl) ⟨770208, by rfl⟩ : syracuseStep 2053889 = 1540417) B1540417
theorem B7804673 : Blo 607294 7804673 := bstep (se 2 (by rfl) ⟨2926752, by rfl⟩ : syracuseStep 7804673 = 5853505) B5853505
theorem B685831 : Blo 607294 685831 := bstep (se 1 (by rfl) ⟨514373, by rfl⟩ : syracuseStep 685831 = 1028747) B1028747
theorem B915215 : Blo 607294 915215 := bstep (se 1 (by rfl) ⟨686411, by rfl⟩ : syracuseStep 915215 = 1372823) B1372823
theorem B1537825 : Blo 607294 1537825 := bstep (se 2 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 1537825 = 1153369) B1153369
theorem B1095457 : Blo 607294 1095457 := bstep (se 2 (by rfl) ⟨410796, by rfl⟩ : syracuseStep 1095457 = 821593) B821593
theorem B915257 : Blo 607294 915257 := bstep (se 2 (by rfl) ⟨343221, by rfl⟩ : syracuseStep 915257 = 686443) B686443
theorem B3127099 : Blo 607294 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B47404865 : Blo 607294 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B11097931 : Blo 607294 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B915335 : Blo 607294 915335 := bstep (se 1 (by rfl) ⟨686501, by rfl⟩ : syracuseStep 915335 = 1373003) B1373003
theorem B5838743 : Blo 607294 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B2316185 : Blo 607294 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B4396963 : Blo 607294 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B915371 : Blo 607294 915371 := bstep (se 1 (by rfl) ⟨686528, by rfl⟩ : syracuseStep 915371 = 1373057) B1373057
theorem B686011 : Blo 607294 686011 := bstep (se 1 (by rfl) ⟨514508, by rfl⟩ : syracuseStep 686011 = 1029017) B1029017
theorem B915401 : Blo 607294 915401 := bstep (se 2 (by rfl) ⟨343275, by rfl⟩ : syracuseStep 915401 = 686551) B686551
theorem B28063705 : Blo 607294 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B86751245 : Blo 607294 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B15628301 : Blo 607294 15628301 := bstep (se 3 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 15628301 = 5860613) B5860613
theorem B3758147 : Blo 607294 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B3086423 : Blo 607294 3086423 := bstep (se 1 (by rfl) ⟨2314817, by rfl⟩ : syracuseStep 3086423 = 4629635) B4629635
theorem B972919 : Blo 607294 972919 := bstep (se 1 (by rfl) ⟨729689, by rfl⟩ : syracuseStep 972919 = 1459379) B1459379
theorem B4757705 : Blo 607294 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B2464015 : Blo 607294 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B2931059 : Blo 607294 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B1538423 : Blo 607294 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1300855 : Blo 607294 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B1153415 : Blo 607294 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B686479 : Blo 607294 686479 := bstep (se 1 (by rfl) ⟨514859, by rfl⟩ : syracuseStep 686479 = 1029719) B1029719
theorem B4929977 : Blo 607294 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B866747 : Blo 607294 866747 := bstep (se 1 (by rfl) ⟨650060, by rfl⟩ : syracuseStep 866747 = 1300121) B1300121
theorem B2054699 : Blo 607294 2054699 := bstep (se 1 (by rfl) ⟨1541024, by rfl⟩ : syracuseStep 2054699 = 3082049) B3082049
theorem B11123243 : Blo 607294 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B3086909 : Blo 607294 3086909 := bstep (se 3 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 3086909 = 1157591) B1157591
theorem B1735283 : Blo 607294 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B3078971 : Blo 607294 3078971 := bstep (se 1 (by rfl) ⟨2309228, by rfl⟩ : syracuseStep 3078971 = 4618457) B4618457
theorem B3718003 : Blo 607294 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B867191 : Blo 607294 867191 := bstep (se 1 (by rfl) ⟨650393, by rfl⟩ : syracuseStep 867191 = 1300787) B1300787
theorem B1366919 : Blo 607294 1366919 := bstep (se 1 (by rfl) ⟨1025189, by rfl⟩ : syracuseStep 1366919 = 2050379) B2050379
theorem B1153939 : Blo 607294 1153939 := bstep (se 1 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 1153939 = 1730909) B1730909
theorem B3079133 : Blo 607294 3079133 := bstep (se 3 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 3079133 = 1154675) B1154675
theorem B1735681 : Blo 607294 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B1604623 : Blo 607294 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B1506319 : Blo 607294 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B867385 : Blo 607294 867385 := bstep (se 2 (by rfl) ⟨325269, by rfl⟩ : syracuseStep 867385 = 650539) B650539
theorem B1367099 : Blo 607294 1367099 := bstep (se 1 (by rfl) ⟨1025324, by rfl⟩ : syracuseStep 1367099 = 2050649) B2050649
theorem B1735739 : Blo 607294 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B2595901 : Blo 607294 2595901 := bstep (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) B973463
theorem B1973335 : Blo 607294 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B695431 : Blo 607294 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B1186963 : Blo 607294 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B1367225 : Blo 607294 1367225 := bstep (se 2 (by rfl) ⟨512709, by rfl⟩ : syracuseStep 1367225 = 1025419) B1025419
theorem B1465615 : Blo 607294 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B2931983 : Blo 607294 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B3079457 : Blo 607294 3079457 := bstep (se 2 (by rfl) ⟨1154796, by rfl⟩ : syracuseStep 3079457 = 2309593) B2309593
theorem B10132867 : Blo 607294 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B6929873 : Blo 607294 6929873 := bstep (se 2 (by rfl) ⟨2598702, by rfl⟩ : syracuseStep 6929873 = 5197405) B5197405
theorem B1367567 : Blo 607294 1367567 := bstep (se 1 (by rfl) ⟨1025675, by rfl⟩ : syracuseStep 1367567 = 2051351) B2051351
theorem B1367585 : Blo 607294 1367585 := bstep (se 2 (by rfl) ⟨512844, by rfl⟩ : syracuseStep 1367585 = 1025689) B1025689
theorem B1539719 : Blo 607294 1539719 := bstep (se 1 (by rfl) ⟨1154789, by rfl⟩ : syracuseStep 1539719 = 2309579) B2309579
theorem B1539769 : Blo 607294 1539769 := bstep (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) B1154827
theorem B2055995 : Blo 607294 2055995 := bstep (se 1 (by rfl) ⟨1541996, by rfl⟩ : syracuseStep 2055995 = 3083993) B3083993
theorem B10026827 : Blo 607294 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B5201779 : Blo 607294 5201779 := bstep (se 1 (by rfl) ⟨3901334, by rfl⟩ : syracuseStep 5201779 = 7802669) B7802669
theorem B1367927 : Blo 607294 1367927 := bstep (se 1 (by rfl) ⟨1025945, by rfl⟩ : syracuseStep 1367927 = 2051891) B2051891
theorem B1302419 : Blo 607294 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B3899339 : Blo 607294 3899339 := bstep (se 1 (by rfl) ⟨2924504, by rfl⟩ : syracuseStep 3899339 = 5849009) B5849009
theorem B1368071 : Blo 607294 1368071 := bstep (se 1 (by rfl) ⟨1026053, by rfl⟩ : syracuseStep 1368071 = 2052107) B2052107
theorem B2056211 : Blo 607294 2056211 := bstep (se 1 (by rfl) ⟨1542158, by rfl⟩ : syracuseStep 2056211 = 3084317) B3084317
theorem B770087 : Blo 607294 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B1368143 : Blo 607294 1368143 := bstep (se 1 (by rfl) ⟨1026107, by rfl⟩ : syracuseStep 1368143 = 2052215) B2052215
theorem B6578405 : Blo 607294 6578405 := bstep (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) B1233451
theorem B2056535 : Blo 607294 2056535 := bstep (se 1 (by rfl) ⟨1542401, by rfl⟩ : syracuseStep 2056535 = 3084803) B3084803
theorem B3285353 : Blo 607294 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B770411 : Blo 607294 770411 := bstep (se 1 (by rfl) ⟨577808, by rfl⟩ : syracuseStep 770411 = 1155617) B1155617
theorem B1098145 : Blo 607294 1098145 := bstep (se 2 (by rfl) ⟨411804, by rfl⟩ : syracuseStep 1098145 = 823609) B823609
theorem B1368539 : Blo 607294 1368539 := bstep (se 1 (by rfl) ⟨1026404, by rfl⟩ : syracuseStep 1368539 = 2052809) B2052809
theorem B1851929 : Blo 607294 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B2196001 : Blo 607294 2196001 := bstep (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) B1647001
theorem B1098319 : Blo 607294 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B3080915 : Blo 607294 3080915 := bstep (se 1 (by rfl) ⟨2310686, by rfl⟩ : syracuseStep 3080915 = 4621373) B4621373
theorem B1369007 : Blo 607294 1369007 := bstep (se 1 (by rfl) ⟨1026755, by rfl⟩ : syracuseStep 1369007 = 2053511) B2053511
theorem B1156027 : Blo 607294 1156027 := bstep (se 1 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 1156027 = 1734041) B1734041
theorem B1024987 : Blo 607294 1024987 := bstep (se 1 (by rfl) ⟨768740, by rfl⟩ : syracuseStep 1024987 = 1537481) B1537481
theorem B1156103 : Blo 607294 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B3466259 : Blo 607294 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B1541177 : Blo 607294 1541177 := bstep (se 2 (by rfl) ⟨577941, by rfl⟩ : syracuseStep 1541177 = 1155883) B1155883
theorem B607311 : Blo 607294 607311 := bstep (se 1 (by rfl) ⟨455483, by rfl⟩ : syracuseStep 607311 = 910967) B910967
theorem B607327 : Blo 607294 607327 := bstep (se 1 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 607327 = 910991) B910991
theorem B607355 : Blo 607294 607355 := bstep (se 1 (by rfl) ⟨455516, by rfl⟩ : syracuseStep 607355 = 911033) B911033
theorem B4957337 : Blo 607294 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B2311325 : Blo 607294 2311325 := bstep (se 3 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 2311325 = 866747) B866747
theorem B2198339 : Blo 607294 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B1369259 : Blo 607294 1369259 := bstep (se 1 (by rfl) ⟨1026944, by rfl⟩ : syracuseStep 1369259 = 2053889) B2053889
theorem B607407 : Blo 607294 607407 := bstep (se 1 (by rfl) ⟨455555, by rfl⟩ : syracuseStep 607407 = 911111) B911111
theorem B5203115 : Blo 607294 5203115 := bstep (se 1 (by rfl) ⟨3902336, by rfl⟩ : syracuseStep 5203115 = 7804673) B7804673
theorem B607431 : Blo 607294 607431 := bstep (se 1 (by rfl) ⟨455573, by rfl⟩ : syracuseStep 607431 = 911147) B911147
theorem B607451 : Blo 607294 607451 := bstep (se 1 (by rfl) ⟨455588, by rfl⟩ : syracuseStep 607451 = 911177) B911177
theorem B3892495 : Blo 607294 3892495 := bstep (se 1 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 3892495 = 5838743) B5838743
theorem B607527 : Blo 607294 607527 := bstep (se 1 (by rfl) ⟨455645, by rfl⟩ : syracuseStep 607527 = 911291) B911291
theorem B607567 : Blo 607294 607567 := bstep (se 1 (by rfl) ⟨455675, by rfl⟩ : syracuseStep 607567 = 911351) B911351
theorem B607583 : Blo 607294 607583 := bstep (se 1 (by rfl) ⟨455687, by rfl⟩ : syracuseStep 607583 = 911375) B911375
theorem B1459561 : Blo 607294 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B2139497 : Blo 607294 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B1017193 : Blo 607294 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B607611 : Blo 607294 607611 := bstep (se 1 (by rfl) ⟨455708, by rfl⟩ : syracuseStep 607611 = 911417) B911417
theorem B2057615 : Blo 607294 2057615 := bstep (se 1 (by rfl) ⟨1543211, by rfl⟩ : syracuseStep 2057615 = 3086423) B3086423
theorem B7800209 : Blo 607294 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B1156513 : Blo 607294 1156513 := bstep (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) B867385
theorem B607663 : Blo 607294 607663 := bstep (se 1 (by rfl) ⟨455747, by rfl⟩ : syracuseStep 607663 = 911495) B911495
theorem B607687 : Blo 607294 607687 := bstep (se 1 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 607687 = 911531) B911531
theorem B2631113 : Blo 607294 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B607707 : Blo 607294 607707 := bstep (se 1 (by rfl) ⟨455780, by rfl⟩ : syracuseStep 607707 = 911561) B911561
theorem B3171803 : Blo 607294 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B8881649 : Blo 607294 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B607783 : Blo 607294 607783 := bstep (se 1 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 607783 = 911675) B911675
theorem B1025615 : Blo 607294 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B607823 : Blo 607294 607823 := bstep (se 1 (by rfl) ⟨455867, by rfl⟩ : syracuseStep 607823 = 911735) B911735
theorem B607839 : Blo 607294 607839 := bstep (se 1 (by rfl) ⟨455879, by rfl⟩ : syracuseStep 607839 = 911759) B911759
theorem B607867 : Blo 607294 607867 := bstep (se 1 (by rfl) ⟨455900, by rfl⟩ : syracuseStep 607867 = 911801) B911801
theorem B3286651 : Blo 607294 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B771707 : Blo 607294 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B607919 : Blo 607294 607919 := bstep (se 1 (by rfl) ⟨455939, by rfl⟩ : syracuseStep 607919 = 911879) B911879
theorem B607943 : Blo 607294 607943 := bstep (se 1 (by rfl) ⟨455957, by rfl⟩ : syracuseStep 607943 = 911915) B911915
theorem B1369799 : Blo 607294 1369799 := bstep (se 1 (by rfl) ⟨1027349, by rfl⟩ : syracuseStep 1369799 = 2054699) B2054699
theorem B7415495 : Blo 607294 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B2057939 : Blo 607294 2057939 := bstep (se 1 (by rfl) ⟨1543454, by rfl⟩ : syracuseStep 2057939 = 3086909) B3086909
theorem B5211863 : Blo 607294 5211863 := bstep (se 1 (by rfl) ⟨3908897, by rfl⟩ : syracuseStep 5211863 = 7817795) B7817795
theorem B607963 : Blo 607294 607963 := bstep (se 1 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 607963 = 911945) B911945
theorem B1156855 : Blo 607294 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B2049785 : Blo 607294 2049785 := bstep (se 2 (by rfl) ⟨768669, by rfl⟩ : syracuseStep 2049785 = 1537339) B1537339
theorem B608039 : Blo 607294 608039 := bstep (se 1 (by rfl) ⟨456029, by rfl⟩ : syracuseStep 608039 = 912059) B912059
theorem B23422769 : Blo 607294 23422769 := bstep (se 2 (by rfl) ⟨8783538, by rfl⟩ : syracuseStep 23422769 = 17567077) B17567077
theorem B2312009 : Blo 607294 2312009 := bstep (se 2 (by rfl) ⟨867003, by rfl⟩ : syracuseStep 2312009 = 1734007) B1734007
theorem B608079 : Blo 607294 608079 := bstep (se 1 (by rfl) ⟨456059, by rfl⟩ : syracuseStep 608079 = 912119) B912119
theorem B13510489 : Blo 607294 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B608095 : Blo 607294 608095 := bstep (se 1 (by rfl) ⟨456071, by rfl⟩ : syracuseStep 608095 = 912143) B912143
theorem B608123 : Blo 607294 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B911279 : Blo 607294 911279 := bstep (se 1 (by rfl) ⟨683459, by rfl⟩ : syracuseStep 911279 = 1366919) B1366919
theorem B608175 : Blo 607294 608175 := bstep (se 1 (by rfl) ⟨456131, by rfl⟩ : syracuseStep 608175 = 912263) B912263
theorem B3958721 : Blo 607294 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B608199 : Blo 607294 608199 := bstep (se 1 (by rfl) ⟨456149, by rfl⟩ : syracuseStep 608199 = 912299) B912299
theorem B608219 : Blo 607294 608219 := bstep (se 1 (by rfl) ⟨456164, by rfl⟩ : syracuseStep 608219 = 912329) B912329
theorem B2050055 : Blo 607294 2050055 := bstep (se 1 (by rfl) ⟨1537541, by rfl⟩ : syracuseStep 2050055 = 3075083) B3075083
theorem B911369 : Blo 607294 911369 := bstep (se 2 (by rfl) ⟨341763, by rfl⟩ : syracuseStep 911369 = 683527) B683527
theorem B911399 : Blo 607294 911399 := bstep (se 1 (by rfl) ⟨683549, by rfl⟩ : syracuseStep 911399 = 1367099) B1367099
theorem B608295 : Blo 607294 608295 := bstep (se 1 (by rfl) ⟨456221, by rfl⟩ : syracuseStep 608295 = 912443) B912443
theorem B1157159 : Blo 607294 1157159 := bstep (se 1 (by rfl) ⟨867869, by rfl⟩ : syracuseStep 1157159 = 1735739) B1735739
theorem B608335 : Blo 607294 608335 := bstep (se 1 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 608335 = 912503) B912503
theorem B608351 : Blo 607294 608351 := bstep (se 1 (by rfl) ⟨456263, by rfl⟩ : syracuseStep 608351 = 912527) B912527
theorem B2050163 : Blo 607294 2050163 := bstep (se 1 (by rfl) ⟨1537622, by rfl⟩ : syracuseStep 2050163 = 3075245) B3075245
theorem B911483 : Blo 607294 911483 := bstep (se 1 (by rfl) ⟨683612, by rfl⟩ : syracuseStep 911483 = 1367225) B1367225
theorem B608379 : Blo 607294 608379 := bstep (se 1 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 608379 = 912569) B912569
theorem B126412973 : Blo 607294 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B608431 : Blo 607294 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B608455 : Blo 607294 608455 := bstep (se 1 (by rfl) ⟨456341, by rfl⟩ : syracuseStep 608455 = 912683) B912683
theorem B608475 : Blo 607294 608475 := bstep (se 1 (by rfl) ⟨456356, by rfl⟩ : syracuseStep 608475 = 912713) B912713
theorem B911609 : Blo 607294 911609 := bstep (se 2 (by rfl) ⟨341853, by rfl⟩ : syracuseStep 911609 = 683707) B683707
theorem B608551 : Blo 607294 608551 := bstep (se 1 (by rfl) ⟨456413, by rfl⟩ : syracuseStep 608551 = 912827) B912827
theorem B2312509 : Blo 607294 2312509 := bstep (se 3 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 2312509 = 867191) B867191
theorem B608591 : Blo 607294 608591 := bstep (se 1 (by rfl) ⟨456443, by rfl⟩ : syracuseStep 608591 = 912887) B912887
theorem B2197847 : Blo 607294 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B911711 : Blo 607294 911711 := bstep (se 1 (by rfl) ⟨683783, by rfl⟩ : syracuseStep 911711 = 1367567) B1367567
theorem B608607 : Blo 607294 608607 := bstep (se 1 (by rfl) ⟨456455, by rfl⟩ : syracuseStep 608607 = 912911) B912911
theorem B911723 : Blo 607294 911723 := bstep (se 1 (by rfl) ⟨683792, by rfl⟩ : syracuseStep 911723 = 1367585) B1367585
theorem B608635 : Blo 607294 608635 := bstep (se 1 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 608635 = 912953) B912953
theorem B2050433 : Blo 607294 2050433 := bstep (se 2 (by rfl) ⟨768912, by rfl⟩ : syracuseStep 2050433 = 1537825) B1537825
theorem B1460609 : Blo 607294 1460609 := bstep (se 2 (by rfl) ⟨547728, by rfl⟩ : syracuseStep 1460609 = 1095457) B1095457
theorem B6678937 : Blo 607294 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B1026479 : Blo 607294 1026479 := bstep (se 1 (by rfl) ⟨769859, by rfl⟩ : syracuseStep 1026479 = 1539719) B1539719
theorem B608687 : Blo 607294 608687 := bstep (se 1 (by rfl) ⟨456515, by rfl⟩ : syracuseStep 608687 = 913031) B913031
theorem B14797241 : Blo 607294 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B608711 : Blo 607294 608711 := bstep (se 1 (by rfl) ⟨456533, by rfl⟩ : syracuseStep 608711 = 913067) B913067
theorem B608731 : Blo 607294 608731 := bstep (se 1 (by rfl) ⟨456548, by rfl⟩ : syracuseStep 608731 = 913097) B913097
theorem B1542665 : Blo 607294 1542665 := bstep (se 2 (by rfl) ⟨578499, by rfl⟩ : syracuseStep 1542665 = 1156999) B1156999
theorem B5204513 : Blo 607294 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B608807 : Blo 607294 608807 := bstep (se 1 (by rfl) ⟨456605, by rfl⟩ : syracuseStep 608807 = 913211) B913211
theorem B1370663 : Blo 607294 1370663 := bstep (se 1 (by rfl) ⟨1027997, by rfl⟩ : syracuseStep 1370663 = 2055995) B2055995
theorem B911951 : Blo 607294 911951 := bstep (se 1 (by rfl) ⟨683963, by rfl⟩ : syracuseStep 911951 = 1367927) B1367927
theorem B608847 : Blo 607294 608847 := bstep (se 1 (by rfl) ⟨456635, by rfl⟩ : syracuseStep 608847 = 913271) B913271
theorem B608863 : Blo 607294 608863 := bstep (se 1 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 608863 = 913295) B913295
theorem B608891 : Blo 607294 608891 := bstep (se 1 (by rfl) ⟨456668, by rfl⟩ : syracuseStep 608891 = 913337) B913337
theorem B2599559 : Blo 607294 2599559 := bstep (se 1 (by rfl) ⟨1949669, by rfl⟩ : syracuseStep 2599559 = 3899339) B3899339
theorem B608943 : Blo 607294 608943 := bstep (se 1 (by rfl) ⟨456707, by rfl⟩ : syracuseStep 608943 = 913415) B913415
theorem B912071 : Blo 607294 912071 := bstep (se 1 (by rfl) ⟨684053, by rfl⟩ : syracuseStep 912071 = 1368107) B1368107
theorem B608967 : Blo 607294 608967 := bstep (se 1 (by rfl) ⟨456725, by rfl⟩ : syracuseStep 608967 = 913451) B913451
theorem B608987 : Blo 607294 608987 := bstep (se 1 (by rfl) ⟨456740, by rfl⟩ : syracuseStep 608987 = 913481) B913481
theorem B11995877 : Blo 607294 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B13200101 : Blo 607294 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B3468035 : Blo 607294 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B609063 : Blo 607294 609063 := bstep (se 1 (by rfl) ⟨456797, by rfl⟩ : syracuseStep 609063 = 913595) B913595
theorem B1297225 : Blo 607294 1297225 := bstep (se 2 (by rfl) ⟨486459, by rfl⟩ : syracuseStep 1297225 = 972919) B972919
theorem B609103 : Blo 607294 609103 := bstep (se 1 (by rfl) ⟨456827, by rfl⟩ : syracuseStep 609103 = 913655) B913655
theorem B1026911 : Blo 607294 1026911 := bstep (se 1 (by rfl) ⟨770183, by rfl⟩ : syracuseStep 1026911 = 1540367) B1540367
theorem B609119 : Blo 607294 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B912233 : Blo 607294 912233 := bstep (se 2 (by rfl) ⟨342087, by rfl⟩ : syracuseStep 912233 = 684175) B684175
theorem B1370987 : Blo 607294 1370987 := bstep (se 1 (by rfl) ⟨1028240, by rfl⟩ : syracuseStep 1370987 = 2056481) B2056481
theorem B2059127 : Blo 607294 2059127 := bstep (se 1 (by rfl) ⟨1544345, by rfl⟩ : syracuseStep 2059127 = 3088691) B3088691
theorem B609147 : Blo 607294 609147 := bstep (se 1 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 609147 = 913721) B913721
theorem B1371041 : Blo 607294 1371041 := bstep (se 2 (by rfl) ⟨514140, by rfl⟩ : syracuseStep 1371041 = 1028281) B1028281
theorem B3083183 : Blo 607294 3083183 := bstep (se 1 (by rfl) ⟨2312387, by rfl⟩ : syracuseStep 3083183 = 4624775) B4624775
theorem B609199 : Blo 607294 609199 := bstep (se 1 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 609199 = 913799) B913799
theorem B912311 : Blo 607294 912311 := bstep (se 1 (by rfl) ⟨684233, by rfl⟩ : syracuseStep 912311 = 1368467) B1368467
theorem B609223 : Blo 607294 609223 := bstep (se 1 (by rfl) ⟨456917, by rfl⟩ : syracuseStep 609223 = 913835) B913835
theorem B912347 : Blo 607294 912347 := bstep (se 1 (by rfl) ⟨684260, by rfl⟩ : syracuseStep 912347 = 1368521) B1368521
theorem B4156381 : Blo 607294 4156381 := bstep (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) B1558643
theorem B609243 : Blo 607294 609243 := bstep (se 1 (by rfl) ⟨456932, by rfl⟩ : syracuseStep 609243 = 913865) B913865
theorem B609319 : Blo 607294 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B609359 : Blo 607294 609359 := bstep (se 1 (by rfl) ⟨457019, by rfl⟩ : syracuseStep 609359 = 914039) B914039
theorem B2059343 : Blo 607294 2059343 := bstep (se 1 (by rfl) ⟨1544507, by rfl⟩ : syracuseStep 2059343 = 3089015) B3089015
theorem B609375 : Blo 607294 609375 := bstep (se 1 (by rfl) ⟨457031, by rfl⟩ : syracuseStep 609375 = 914063) B914063
theorem B609403 : Blo 607294 609403 := bstep (se 1 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 609403 = 914105) B914105
theorem B1641629 : Blo 607294 1641629 := bstep (se 3 (by rfl) ⟨307805, by rfl⟩ : syracuseStep 1641629 = 615611) B615611
theorem B2051243 : Blo 607294 2051243 := bstep (se 1 (by rfl) ⟨1538432, by rfl⟩ : syracuseStep 2051243 = 3076865) B3076865
theorem B609455 : Blo 607294 609455 := bstep (se 1 (by rfl) ⟨457091, by rfl⟩ : syracuseStep 609455 = 914183) B914183
theorem B4885697 : Blo 607294 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B609479 : Blo 607294 609479 := bstep (se 1 (by rfl) ⟨457109, by rfl⟩ : syracuseStep 609479 = 914219) B914219
theorem B3468491 : Blo 607294 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B609499 : Blo 607294 609499 := bstep (se 1 (by rfl) ⟨457124, by rfl⟩ : syracuseStep 609499 = 914249) B914249
theorem B1371383 : Blo 607294 1371383 := bstep (se 1 (by rfl) ⟨1028537, by rfl⟩ : syracuseStep 1371383 = 2057075) B2057075
theorem B609575 : Blo 607294 609575 := bstep (se 1 (by rfl) ⟨457181, by rfl⟩ : syracuseStep 609575 = 914363) B914363
theorem B609615 : Blo 607294 609615 := bstep (se 1 (by rfl) ⟨457211, by rfl⟩ : syracuseStep 609615 = 914423) B914423
theorem B609631 : Blo 607294 609631 := bstep (se 1 (by rfl) ⟨457223, by rfl⟩ : syracuseStep 609631 = 914447) B914447
theorem B609659 : Blo 607294 609659 := bstep (se 1 (by rfl) ⟨457244, by rfl⟩ : syracuseStep 609659 = 914489) B914489
theorem B1027471 : Blo 607294 1027471 := bstep (se 1 (by rfl) ⟨770603, by rfl⟩ : syracuseStep 1027471 = 1541207) B1541207
theorem B912815 : Blo 607294 912815 := bstep (se 1 (by rfl) ⟨684611, by rfl⟩ : syracuseStep 912815 = 1369223) B1369223
theorem B609711 : Blo 607294 609711 := bstep (se 1 (by rfl) ⟨457283, by rfl⟩ : syracuseStep 609711 = 914567) B914567
theorem B609735 : Blo 607294 609735 := bstep (se 1 (by rfl) ⟨457301, by rfl⟩ : syracuseStep 609735 = 914603) B914603
theorem B2059721 : Blo 607294 2059721 := bstep (se 2 (by rfl) ⟨772395, by rfl⟩ : syracuseStep 2059721 = 1544791) B1544791
theorem B1297883 : Blo 607294 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B609755 : Blo 607294 609755 := bstep (se 1 (by rfl) ⟨457316, by rfl⟩ : syracuseStep 609755 = 914633) B914633
theorem B912905 : Blo 607294 912905 := bstep (se 2 (by rfl) ⟨342339, by rfl⟩ : syracuseStep 912905 = 684679) B684679
theorem B912935 : Blo 607294 912935 := bstep (se 1 (by rfl) ⟨684701, by rfl⟩ : syracuseStep 912935 = 1369403) B1369403
theorem B609831 : Blo 607294 609831 := bstep (se 1 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 609831 = 914747) B914747
theorem B683599 : Blo 607294 683599 := bstep (se 1 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 683599 = 1025399) B1025399
theorem B609871 : Blo 607294 609871 := bstep (se 1 (by rfl) ⟨457403, by rfl⟩ : syracuseStep 609871 = 914807) B914807
theorem B9858647 : Blo 607294 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B609887 : Blo 607294 609887 := bstep (se 1 (by rfl) ⟨457415, by rfl⟩ : syracuseStep 609887 = 914831) B914831
theorem B8326775 : Blo 607294 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B913019 : Blo 607294 913019 := bstep (se 1 (by rfl) ⟨684764, by rfl⟩ : syracuseStep 913019 = 1369529) B1369529
theorem B609915 : Blo 607294 609915 := bstep (se 1 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 609915 = 914873) B914873
theorem B1543819 : Blo 607294 1543819 := bstep (se 1 (by rfl) ⟨1157864, by rfl⟩ : syracuseStep 1543819 = 2315729) B2315729
theorem B3075731 : Blo 607294 3075731 := bstep (se 1 (by rfl) ⟨2306798, by rfl⟩ : syracuseStep 3075731 = 4613597) B4613597
theorem B609967 : Blo 607294 609967 := bstep (se 1 (by rfl) ⟨457475, by rfl⟩ : syracuseStep 609967 = 914951) B914951
theorem B2051783 : Blo 607294 2051783 := bstep (se 1 (by rfl) ⟨1538837, by rfl⟩ : syracuseStep 2051783 = 3077675) B3077675
theorem B609991 : Blo 607294 609991 := bstep (se 1 (by rfl) ⟨457493, by rfl⟩ : syracuseStep 609991 = 914987) B914987
theorem B610011 : Blo 607294 610011 := bstep (se 1 (by rfl) ⟨457508, by rfl⟩ : syracuseStep 610011 = 915017) B915017
theorem B913145 : Blo 607294 913145 := bstep (se 2 (by rfl) ⟨342429, by rfl⟩ : syracuseStep 913145 = 684859) B684859
theorem B610087 : Blo 607294 610087 := bstep (se 1 (by rfl) ⟨457565, by rfl⟩ : syracuseStep 610087 = 915131) B915131
theorem B3288899 : Blo 607294 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B1371977 : Blo 607294 1371977 := bstep (se 2 (by rfl) ⟨514491, by rfl⟩ : syracuseStep 1371977 = 1028983) B1028983
theorem B610127 : Blo 607294 610127 := bstep (se 1 (by rfl) ⟨457595, by rfl⟩ : syracuseStep 610127 = 915191) B915191
theorem B913247 : Blo 607294 913247 := bstep (se 1 (by rfl) ⟨684935, by rfl⟩ : syracuseStep 913247 = 1369871) B1369871
theorem B610143 : Blo 607294 610143 := bstep (se 1 (by rfl) ⟨457607, by rfl⟩ : syracuseStep 610143 = 915215) B915215
theorem B913259 : Blo 607294 913259 := bstep (se 1 (by rfl) ⟨684944, by rfl⟩ : syracuseStep 913259 = 1369889) B1369889
theorem B3698551 : Blo 607294 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B3469175 : Blo 607294 3469175 := bstep (se 1 (by rfl) ⟨2601881, by rfl⟩ : syracuseStep 3469175 = 5203763) B5203763
theorem B610171 : Blo 607294 610171 := bstep (se 1 (by rfl) ⟨457628, by rfl⟩ : syracuseStep 610171 = 915257) B915257
theorem B4624289 : Blo 607294 4624289 := bstep (se 2 (by rfl) ⟨1734108, by rfl⟩ : syracuseStep 4624289 = 3468217) B3468217
theorem B17592227 : Blo 607294 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B610223 : Blo 607294 610223 := bstep (se 1 (by rfl) ⟨457667, by rfl⟩ : syracuseStep 610223 = 915335) B915335
theorem B4157369 : Blo 607294 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B2305979 : Blo 607294 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B1544123 : Blo 607294 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B610247 : Blo 607294 610247 := bstep (se 1 (by rfl) ⟨457685, by rfl⟩ : syracuseStep 610247 = 915371) B915371
theorem B683995 : Blo 607294 683995 := bstep (se 1 (by rfl) ⟨512996, by rfl⟩ : syracuseStep 683995 = 1025993) B1025993
theorem B610267 : Blo 607294 610267 := bstep (se 1 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 610267 = 915401) B915401
theorem B2314241 : Blo 607294 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B1028153 : Blo 607294 1028153 := bstep (se 2 (by rfl) ⟨385557, by rfl⟩ : syracuseStep 1028153 = 771115) B771115
theorem B913487 : Blo 607294 913487 := bstep (se 1 (by rfl) ⟨685115, by rfl⟩ : syracuseStep 913487 = 1370231) B1370231
theorem B3461201 : Blo 607294 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B1732765 : Blo 607294 1732765 := bstep (se 3 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 1732765 = 649787) B649787
theorem B45674675 : Blo 607294 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B913607 : Blo 607294 913607 := bstep (se 1 (by rfl) ⟨685205, by rfl⟩ : syracuseStep 913607 = 1370411) B1370411
theorem B4378853 : Blo 607294 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B2191607 : Blo 607294 2191607 := bstep (se 1 (by rfl) ⟨1643705, by rfl⟩ : syracuseStep 2191607 = 3287411) B3287411
theorem B1954039 : Blo 607294 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B913769 : Blo 607294 913769 := bstep (se 2 (by rfl) ⟨342663, by rfl⟩ : syracuseStep 913769 = 685327) B685327
theorem B1954153 : Blo 607294 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B684463 : Blo 607294 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B913847 : Blo 607294 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B913883 : Blo 607294 913883 := bstep (se 1 (by rfl) ⟨685412, by rfl⟩ : syracuseStep 913883 = 1370825) B1370825
theorem B10383875 : Blo 607294 10383875 := bstep (se 1 (by rfl) ⟨7787906, by rfl⟩ : syracuseStep 10383875 = 15575813) B15575813
theorem B2052647 : Blo 607294 2052647 := bstep (se 1 (by rfl) ⟨1539485, by rfl⟩ : syracuseStep 2052647 = 3078971) B3078971
theorem B1372769 : Blo 607294 1372769 := bstep (se 2 (by rfl) ⟨514788, by rfl⟩ : syracuseStep 1372769 = 1029577) B1029577
theorem B2052755 : Blo 607294 2052755 := bstep (se 1 (by rfl) ⟨1539566, by rfl⟩ : syracuseStep 2052755 = 3079133) B3079133
theorem B1127159 : Blo 607294 1127159 := bstep (se 1 (by rfl) ⟨845369, by rfl⟩ : syracuseStep 1127159 = 1690739) B1690739
theorem B1028855 : Blo 607294 1028855 := bstep (se 1 (by rfl) ⟨771641, by rfl⟩ : syracuseStep 1028855 = 1543283) B1543283
theorem B11268881 : Blo 607294 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B1733471 : Blo 607294 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B684895 : Blo 607294 684895 := bstep (se 1 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 684895 = 1027343) B1027343
theorem B1954655 : Blo 607294 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2052971 : Blo 607294 2052971 := bstep (se 1 (by rfl) ⟨1539728, by rfl⟩ : syracuseStep 2052971 = 3079457) B3079457
theorem B2053025 : Blo 607294 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B914351 : Blo 607294 914351 := bstep (se 1 (by rfl) ⟨685763, by rfl⟩ : syracuseStep 914351 = 1371527) B1371527
theorem B1373111 : Blo 607294 1373111 := bstep (se 1 (by rfl) ⟨1029833, by rfl⟩ : syracuseStep 1373111 = 2059667) B2059667
theorem B865289 : Blo 607294 865289 := bstep (se 2 (by rfl) ⟨324483, by rfl⟩ : syracuseStep 865289 = 648967) B648967
theorem B914441 : Blo 607294 914441 := bstep (se 2 (by rfl) ⟨342915, by rfl⟩ : syracuseStep 914441 = 685831) B685831
theorem B914471 : Blo 607294 914471 := bstep (se 1 (by rfl) ⟨685853, by rfl⟩ : syracuseStep 914471 = 1371707) B1371707
theorem B53310517 : Blo 607294 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B1029199 : Blo 607294 1029199 := bstep (se 1 (by rfl) ⟨771899, by rfl⟩ : syracuseStep 1029199 = 1543799) B1543799
theorem B2077811 : Blo 607294 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B914555 : Blo 607294 914555 := bstep (se 1 (by rfl) ⟨685916, by rfl⟩ : syracuseStep 914555 = 1371833) B1371833
theorem B6935705 : Blo 607294 6935705 := bstep (se 2 (by rfl) ⟨2600889, by rfl⟩ : syracuseStep 6935705 = 5201779) B5201779
theorem B1954973 : Blo 607294 1954973 := bstep (se 3 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 1954973 = 733115) B733115
theorem B2225323 : Blo 607294 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B685255 : Blo 607294 685255 := bstep (se 1 (by rfl) ⟨513941, by rfl⟩ : syracuseStep 685255 = 1027883) B1027883
theorem B5862617 : Blo 607294 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B914681 : Blo 607294 914681 := bstep (se 2 (by rfl) ⟨343005, by rfl⟩ : syracuseStep 914681 = 686011) B686011
theorem B37418273 : Blo 607294 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B1029449 : Blo 607294 1029449 := bstep (se 2 (by rfl) ⟨386043, by rfl⟩ : syracuseStep 1029449 = 772087) B772087
theorem B914783 : Blo 607294 914783 := bstep (se 1 (by rfl) ⟨686087, by rfl⟩ : syracuseStep 914783 = 1372175) B1372175
theorem B914795 : Blo 607294 914795 := bstep (se 1 (by rfl) ⟨686096, by rfl⟩ : syracuseStep 914795 = 1372193) B1372193
theorem B8033701 : Blo 607294 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B2053619 : Blo 607294 2053619 := bstep (se 1 (by rfl) ⟨1540214, by rfl⟩ : syracuseStep 2053619 = 3080429) B3080429
theorem B2348531 : Blo 607294 2348531 := bstep (se 1 (by rfl) ⟨1761398, by rfl⟩ : syracuseStep 2348531 = 3522797) B3522797
theorem B915023 : Blo 607294 915023 := bstep (se 1 (by rfl) ⟨686267, by rfl⟩ : syracuseStep 915023 = 1372535) B1372535
theorem B5264993 : Blo 607294 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B2315911 : Blo 607294 2315911 := bstep (se 1 (by rfl) ⟨1736933, by rfl⟩ : syracuseStep 2315911 = 3473867) B3473867
theorem B9885377 : Blo 607294 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B1390279 : Blo 607294 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B915143 : Blo 607294 915143 := bstep (se 1 (by rfl) ⟨686357, by rfl⟩ : syracuseStep 915143 = 1372715) B1372715
theorem B1734473 : Blo 607294 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B1783625 : Blo 607294 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B866143 : Blo 607294 866143 := bstep (se 1 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 866143 = 1299215) B1299215
theorem B3290975 : Blo 607294 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B915305 : Blo 607294 915305 := bstep (se 2 (by rfl) ⟨343239, by rfl⟩ : syracuseStep 915305 = 686479) B686479
theorem B866155 : Blo 607294 866155 := bstep (se 1 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 866155 = 1299233) B1299233
theorem B1152929 : Blo 607294 1152929 := bstep (se 2 (by rfl) ⟨432348, by rfl⟩ : syracuseStep 1152929 = 864697) B864697
theorem B1537967 : Blo 607294 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B2316215 : Blo 607294 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B915383 : Blo 607294 915383 := bstep (se 1 (by rfl) ⟨686537, by rfl⟩ : syracuseStep 915383 = 1373075) B1373075
theorem B1300411 : Blo 607294 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B915419 : Blo 607294 915419 := bstep (se 1 (by rfl) ⟨686564, by rfl⟩ : syracuseStep 915419 = 1373129) B1373129
theorem B2054159 : Blo 607294 2054159 := bstep (se 1 (by rfl) ⟨1540619, by rfl⟩ : syracuseStep 2054159 = 3081239) B3081239
theorem B1480723 : Blo 607294 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B3708965 : Blo 607294 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B686119 : Blo 607294 686119 := bstep (se 1 (by rfl) ⟨514589, by rfl⟩ : syracuseStep 686119 = 1029179) B1029179
theorem B3905617 : Blo 607294 3905617 := bstep (se 2 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 3905617 = 2929213) B2929213
theorem B3127385 : Blo 607294 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B6330469 : Blo 607294 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B3119219 : Blo 607294 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1153271 : Blo 607294 1153271 := bstep (se 1 (by rfl) ⟨864953, by rfl⟩ : syracuseStep 1153271 = 1729907) B1729907
theorem B2308439 : Blo 607294 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B8321413 : Blo 607294 8321413 := bstep (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) B1560265
theorem B1366415 : Blo 607294 1366415 := bstep (se 1 (by rfl) ⟨1024811, by rfl⟩ : syracuseStep 1366415 = 2049623) B2049623
theorem B3463661 : Blo 607294 3463661 := bstep (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) B1298873
theorem B1538585 : Blo 607294 1538585 := bstep (se 2 (by rfl) ⟨576969, by rfl⟩ : syracuseStep 1538585 = 1153939) B1153939
theorem B2054753 : Blo 607294 2054753 := bstep (se 2 (by rfl) ⟨770532, by rfl⟩ : syracuseStep 2054753 = 1541065) B1541065
theorem B57834163 : Blo 607294 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B10418867 : Blo 607294 10418867 := bstep (se 1 (by rfl) ⟨7814150, by rfl⟩ : syracuseStep 10418867 = 15628301) B15628301
theorem B1366739 : Blo 607294 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B2505431 : Blo 607294 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B1096553 : Blo 607294 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B4938641 : Blo 607294 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B768943 : Blo 607294 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B1301675 : Blo 607294 1301675 := bstep (se 1 (by rfl) ⟨976256, by rfl⟩ : syracuseStep 1301675 = 1952513) B1952513
theorem B3128701 : Blo 607294 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B4398461 : Blo 607294 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B1039835 : Blo 607294 1039835 := bstep (se 1 (by rfl) ⟨779876, by rfl⟩ : syracuseStep 1039835 = 1559753) B1559753
theorem B1154569 : Blo 607294 1154569 := bstep (se 2 (by rfl) ⟨432963, by rfl⟩ : syracuseStep 1154569 = 865927) B865927
theorem B3464801 : Blo 607294 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B1367675 : Blo 607294 1367675 := bstep (se 1 (by rfl) ⟨1025756, by rfl⟩ : syracuseStep 1367675 = 2051513) B2051513
theorem B9379451 : Blo 607294 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B4619915 : Blo 607294 4619915 := bstep (se 1 (by rfl) ⟨3464936, by rfl⟩ : syracuseStep 4619915 = 6929873) B6929873
theorem B2342585 : Blo 607294 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B3473117 : Blo 607294 3473117 := bstep (se 3 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 3473117 = 1302419) B1302419
theorem B1367801 : Blo 607294 1367801 := bstep (se 2 (by rfl) ⟨512925, by rfl⟩ : syracuseStep 1367801 = 1025851) B1025851
theorem B4169465 : Blo 607294 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B6668065 : Blo 607294 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B1236809 : Blo 607294 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1154911 : Blo 607294 1154911 := bstep (se 1 (by rfl) ⟨866183, by rfl⟩ : syracuseStep 1154911 = 1732367) B1732367
theorem B6684551 : Blo 607294 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B7897189 : Blo 607294 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B30449783 : Blo 607294 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B2310353 : Blo 607294 2310353 := bstep (se 2 (by rfl) ⟨866382, by rfl⟩ : syracuseStep 2310353 = 1732765) B1732765
theorem B2605385 : Blo 607294 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B6922583 : Blo 607294 6922583 := bstep (se 1 (by rfl) ⟨5191937, by rfl⟩ : syracuseStep 6922583 = 10383875) B10383875
theorem B1368431 : Blo 607294 1368431 := bstep (se 1 (by rfl) ⟨1026323, by rfl⟩ : syracuseStep 1368431 = 2052647) B2052647
theorem B1368503 : Blo 607294 1368503 := bstep (se 1 (by rfl) ⟨1026377, by rfl⟩ : syracuseStep 1368503 = 2052755) B2052755
theorem B4171601 : Blo 607294 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B2605537 : Blo 607294 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B7512587 : Blo 607294 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B8905249 : Blo 607294 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B1155647 : Blo 607294 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1303103 : Blo 607294 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B1368647 : Blo 607294 1368647 := bstep (se 1 (by rfl) ⟨1026485, by rfl⟩ : syracuseStep 1368647 = 2052971) B2052971
theorem B1368683 : Blo 607294 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B770735 : Blo 607294 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B2310839 : Blo 607294 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B1385207 : Blo 607294 1385207 := bstep (se 1 (by rfl) ⟨1038905, by rfl⟩ : syracuseStep 1385207 = 2077811) B2077811
theorem B1540883 : Blo 607294 1540883 := bstep (se 1 (by rfl) ⟨1155662, by rfl⟩ : syracuseStep 1540883 = 2311325) B2311325
theorem B3908411 : Blo 607294 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B24945515 : Blo 607294 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B77112217 : Blo 607294 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B1426331 : Blo 607294 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B1754075 : Blo 607294 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B1369079 : Blo 607294 1369079 := bstep (se 1 (by rfl) ⟨1026809, by rfl⟩ : syracuseStep 1369079 = 2053619) B2053619
theorem B1565687 : Blo 607294 1565687 := bstep (se 1 (by rfl) ⟨1174265, by rfl⟩ : syracuseStep 1565687 = 2348531) B2348531
theorem B1729633 : Blo 607294 1729633 := bstep (se 2 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 1729633 = 1297225) B1297225
theorem B3474575 : Blo 607294 3474575 := bstep (se 1 (by rfl) ⟨2605931, by rfl⟩ : syracuseStep 3474575 = 5211863) B5211863
theorem B15615179 : Blo 607294 15615179 := bstep (se 1 (by rfl) ⟨11711384, by rfl⟩ : syracuseStep 15615179 = 23422769) B23422769
theorem B1541339 : Blo 607294 1541339 := bstep (se 1 (by rfl) ⟨1156004, by rfl⟩ : syracuseStep 1541339 = 2312009) B2312009
theorem B1025257 : Blo 607294 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B1541369 : Blo 607294 1541369 := bstep (se 2 (by rfl) ⟨578013, by rfl⟩ : syracuseStep 1541369 = 1156027) B1156027
theorem B607519 : Blo 607294 607519 := bstep (se 1 (by rfl) ⟨455639, by rfl⟩ : syracuseStep 607519 = 911279) B911279
theorem B1025311 : Blo 607294 1025311 := bstep (se 1 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 1025311 = 1537967) B1537967
theorem B2639147 : Blo 607294 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B607579 : Blo 607294 607579 := bstep (se 1 (by rfl) ⟨455684, by rfl⟩ : syracuseStep 607579 = 911369) B911369
theorem B1369439 : Blo 607294 1369439 := bstep (se 1 (by rfl) ⟨1027079, by rfl⟩ : syracuseStep 1369439 = 2054159) B2054159
theorem B607599 : Blo 607294 607599 := bstep (se 1 (by rfl) ⟨455699, by rfl⟩ : syracuseStep 607599 = 911399) B911399
theorem B771439 : Blo 607294 771439 := bstep (se 1 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 771439 = 1157159) B1157159
theorem B607655 : Blo 607294 607655 := bstep (se 1 (by rfl) ⟨455741, by rfl⟩ : syracuseStep 607655 = 911483) B911483
theorem B607739 : Blo 607294 607739 := bstep (se 1 (by rfl) ⟨455804, by rfl⟩ : syracuseStep 607739 = 911609) B911609
theorem B35563013 : Blo 607294 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B607807 : Blo 607294 607807 := bstep (se 1 (by rfl) ⟨455855, by rfl⟩ : syracuseStep 607807 = 911711) B911711
theorem B607815 : Blo 607294 607815 := bstep (se 1 (by rfl) ⟨455861, by rfl⟩ : syracuseStep 607815 = 911723) B911723
theorem B910943 : Blo 607294 910943 := bstep (se 1 (by rfl) ⟨683207, by rfl⟩ : syracuseStep 910943 = 1366415) B1366415
theorem B9864827 : Blo 607294 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B2057885 : Blo 607294 2057885 := bstep (se 3 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 2057885 = 771707) B771707
theorem B1025723 : Blo 607294 1025723 := bstep (se 1 (by rfl) ⟨769292, by rfl⟩ : syracuseStep 1025723 = 1538585) B1538585
theorem B607967 : Blo 607294 607967 := bstep (se 1 (by rfl) ⟨455975, by rfl⟩ : syracuseStep 607967 = 911951) B911951
theorem B1369835 : Blo 607294 1369835 := bstep (se 1 (by rfl) ⟨1027376, by rfl⟩ : syracuseStep 1369835 = 2054753) B2054753
theorem B608047 : Blo 607294 608047 := bstep (se 1 (by rfl) ⟨456035, by rfl⟩ : syracuseStep 608047 = 912071) B912071
theorem B911159 : Blo 607294 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B7997251 : Blo 607294 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B8800067 : Blo 607294 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B2312023 : Blo 607294 2312023 := bstep (se 1 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 2312023 = 3468035) B3468035
theorem B1369961 : Blo 607294 1369961 := bstep (se 2 (by rfl) ⟨513735, by rfl⟩ : syracuseStep 1369961 = 1027471) B1027471
theorem B1542017 : Blo 607294 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B608155 : Blo 607294 608155 := bstep (se 1 (by rfl) ⟨456116, by rfl⟩ : syracuseStep 608155 = 912233) B912233
theorem B731035 : Blo 607294 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B608207 : Blo 607294 608207 := bstep (se 1 (by rfl) ⟨456155, by rfl⟩ : syracuseStep 608207 = 912311) B912311
theorem B608231 : Blo 607294 608231 := bstep (se 1 (by rfl) ⟨456173, by rfl⟩ : syracuseStep 608231 = 912347) B912347
theorem B911465 : Blo 607294 911465 := bstep (se 2 (by rfl) ⟨341799, by rfl⟩ : syracuseStep 911465 = 683599) B683599
theorem B2312327 : Blo 607294 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B2058425 : Blo 607294 2058425 := bstep (se 2 (by rfl) ⟨771909, by rfl⟩ : syracuseStep 2058425 = 1543819) B1543819
theorem B1853705 : Blo 607294 1853705 := bstep (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) B1390279
theorem B608543 : Blo 607294 608543 := bstep (se 1 (by rfl) ⟨456407, by rfl⟩ : syracuseStep 608543 = 912815) B912815
theorem B1542473 : Blo 607294 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B608603 : Blo 607294 608603 := bstep (se 1 (by rfl) ⟨456452, by rfl⟩ : syracuseStep 608603 = 912905) B912905
theorem B608623 : Blo 607294 608623 := bstep (se 1 (by rfl) ⟨456467, by rfl⟩ : syracuseStep 608623 = 912935) B912935
theorem B6572431 : Blo 607294 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B911783 : Blo 607294 911783 := bstep (se 1 (by rfl) ⟨683837, by rfl⟩ : syracuseStep 911783 = 1367675) B1367675
theorem B608679 : Blo 607294 608679 := bstep (se 1 (by rfl) ⟨456509, by rfl⟩ : syracuseStep 608679 = 913019) B913019
theorem B6252967 : Blo 607294 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B2050487 : Blo 607294 2050487 := bstep (se 1 (by rfl) ⟨1537865, by rfl⟩ : syracuseStep 2050487 = 3075731) B3075731
theorem B911867 : Blo 607294 911867 := bstep (se 1 (by rfl) ⟨683900, by rfl⟩ : syracuseStep 911867 = 1367801) B1367801
theorem B608763 : Blo 607294 608763 := bstep (se 1 (by rfl) ⟨456572, by rfl⟩ : syracuseStep 608763 = 913145) B913145
theorem B2779643 : Blo 607294 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B608831 : Blo 607294 608831 := bstep (se 1 (by rfl) ⟨456623, by rfl⟩ : syracuseStep 608831 = 913247) B913247
theorem B608839 : Blo 607294 608839 := bstep (se 1 (by rfl) ⟨456629, by rfl⟩ : syracuseStep 608839 = 913259) B913259
theorem B2312783 : Blo 607294 2312783 := bstep (se 1 (by rfl) ⟨1734587, by rfl⟩ : syracuseStep 2312783 = 3469175) B3469175
theorem B3082859 : Blo 607294 3082859 := bstep (se 1 (by rfl) ⟨2312144, by rfl⟩ : syracuseStep 3082859 = 4624289) B4624289
theorem B911993 : Blo 607294 911993 := bstep (se 2 (by rfl) ⟨341997, by rfl⟩ : syracuseStep 911993 = 683995) B683995
theorem B2771579 : Blo 607294 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B1542827 : Blo 607294 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B912047 : Blo 607294 912047 := bstep (se 1 (by rfl) ⟨684035, by rfl⟩ : syracuseStep 912047 = 1368071) B1368071
theorem B1370807 : Blo 607294 1370807 := bstep (se 1 (by rfl) ⟨1028105, by rfl⟩ : syracuseStep 1370807 = 2056211) B2056211
theorem B912095 : Blo 607294 912095 := bstep (se 1 (by rfl) ⟨684071, by rfl⟩ : syracuseStep 912095 = 1368143) B1368143
theorem B608991 : Blo 607294 608991 := bstep (se 1 (by rfl) ⟨456743, by rfl⟩ : syracuseStep 608991 = 913487) B913487
theorem B609071 : Blo 607294 609071 := bstep (se 1 (by rfl) ⟨456803, by rfl⟩ : syracuseStep 609071 = 913607) B913607
theorem B8440625 : Blo 607294 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B2919235 : Blo 607294 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B4385603 : Blo 607294 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B1461071 : Blo 607294 1461071 := bstep (se 1 (by rfl) ⟨1095803, by rfl⟩ : syracuseStep 1461071 = 2191607) B2191607
theorem B1371023 : Blo 607294 1371023 := bstep (se 1 (by rfl) ⟨1028267, by rfl⟩ : syracuseStep 1371023 = 2056535) B2056535
theorem B2190235 : Blo 607294 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B609179 : Blo 607294 609179 := bstep (se 1 (by rfl) ⟨456884, by rfl⟩ : syracuseStep 609179 = 913769) B913769
theorem B284322757 : Blo 607294 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B609231 : Blo 607294 609231 := bstep (se 1 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 609231 = 913847) B913847
theorem B912359 : Blo 607294 912359 := bstep (se 1 (by rfl) ⟨684269, by rfl⟩ : syracuseStep 912359 = 1368539) B1368539
theorem B609255 : Blo 607294 609255 := bstep (se 1 (by rfl) ⟨456941, by rfl⟩ : syracuseStep 609255 = 913883) B913883
theorem B5213261 : Blo 607294 5213261 := bstep (se 3 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 5213261 = 1954973) B1954973
theorem B3083345 : Blo 607294 3083345 := bstep (se 2 (by rfl) ⟨1156254, by rfl⟩ : syracuseStep 3083345 = 2312509) B2312509
theorem B13028525 : Blo 607294 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B11095217 : Blo 607294 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B912617 : Blo 607294 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B912671 : Blo 607294 912671 := bstep (se 1 (by rfl) ⟨684503, by rfl⟩ : syracuseStep 912671 = 1369007) B1369007
theorem B609567 : Blo 607294 609567 := bstep (se 1 (by rfl) ⟨457175, by rfl⟩ : syracuseStep 609567 = 914351) B914351
theorem B609627 : Blo 607294 609627 := bstep (se 1 (by rfl) ⟨457220, by rfl⟩ : syracuseStep 609627 = 914441) B914441
theorem B609647 : Blo 607294 609647 := bstep (se 1 (by rfl) ⟨457235, by rfl⟩ : syracuseStep 609647 = 914471) B914471
theorem B1027451 : Blo 607294 1027451 := bstep (se 1 (by rfl) ⟨770588, by rfl⟩ : syracuseStep 1027451 = 1541177) B1541177
theorem B2928001 : Blo 607294 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B609703 : Blo 607294 609703 := bstep (se 1 (by rfl) ⟨457277, by rfl⟩ : syracuseStep 609703 = 914555) B914555
theorem B4623803 : Blo 607294 4623803 := bstep (se 1 (by rfl) ⟨3467852, by rfl⟩ : syracuseStep 4623803 = 6935705) B6935705
theorem B3304891 : Blo 607294 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B912839 : Blo 607294 912839 := bstep (se 1 (by rfl) ⟨684629, by rfl⟩ : syracuseStep 912839 = 1369259) B1369259
theorem B3468743 : Blo 607294 3468743 := bstep (se 1 (by rfl) ⟨2601557, by rfl⟩ : syracuseStep 3468743 = 5203115) B5203115
theorem B609787 : Blo 607294 609787 := bstep (se 1 (by rfl) ⟨457340, by rfl⟩ : syracuseStep 609787 = 914681) B914681
theorem B609855 : Blo 607294 609855 := bstep (se 1 (by rfl) ⟨457391, by rfl⟩ : syracuseStep 609855 = 914783) B914783
theorem B609863 : Blo 607294 609863 := bstep (se 1 (by rfl) ⟨457397, by rfl⟩ : syracuseStep 609863 = 914795) B914795
theorem B1371743 : Blo 607294 1371743 := bstep (se 1 (by rfl) ⟨1028807, by rfl⟩ : syracuseStep 1371743 = 2057615) B2057615
theorem B683743 : Blo 607294 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B610015 : Blo 607294 610015 := bstep (se 1 (by rfl) ⟨457511, by rfl⟩ : syracuseStep 610015 = 915023) B915023
theorem B3509995 : Blo 607294 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B913193 : Blo 607294 913193 := bstep (se 2 (by rfl) ⟨342447, by rfl⟩ : syracuseStep 913193 = 684895) B684895
theorem B6590251 : Blo 607294 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B913199 : Blo 607294 913199 := bstep (se 1 (by rfl) ⟨684899, by rfl⟩ : syracuseStep 913199 = 1369799) B1369799
theorem B4943663 : Blo 607294 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B1371959 : Blo 607294 1371959 := bstep (se 1 (by rfl) ⟨1028969, by rfl⟩ : syracuseStep 1371959 = 2057939) B2057939
theorem B610203 : Blo 607294 610203 := bstep (se 1 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 610203 = 915305) B915305
theorem B2772893 : Blo 607294 2772893 := bstep (se 3 (by rfl) ⟨519917, by rfl⟩ : syracuseStep 2772893 = 1039835) B1039835
theorem B8458141 : Blo 607294 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B1544143 : Blo 607294 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B610255 : Blo 607294 610255 := bstep (se 1 (by rfl) ⟨457691, by rfl⟩ : syracuseStep 610255 = 915383) B915383
theorem B5541841 : Blo 607294 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B610279 : Blo 607294 610279 := bstep (se 1 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 610279 = 915419) B915419
theorem B2084923 : Blo 607294 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B1372265 : Blo 607294 1372265 := bstep (se 2 (by rfl) ⟨514599, by rfl⟩ : syracuseStep 1372265 = 1029199) B1029199
theorem B84275315 : Blo 607294 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B913673 : Blo 607294 913673 := bstep (se 2 (by rfl) ⟨342627, by rfl⟩ : syracuseStep 913673 = 685255) B685255
theorem B684319 : Blo 607294 684319 := bstep (se 1 (by rfl) ⟨513239, by rfl⟩ : syracuseStep 684319 = 1026479) B1026479
theorem B1028443 : Blo 607294 1028443 := bstep (se 1 (by rfl) ⟨771332, by rfl⟩ : syracuseStep 1028443 = 1542665) B1542665
theorem B5189993 : Blo 607294 5189993 := bstep (se 2 (by rfl) ⟨1946247, by rfl⟩ : syracuseStep 5189993 = 3892495) B3892495
theorem B3469675 : Blo 607294 3469675 := bstep (se 1 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 3469675 = 5204513) B5204513
theorem B913775 : Blo 607294 913775 := bstep (se 1 (by rfl) ⟨685331, by rfl⟩ : syracuseStep 913775 = 1370663) B1370663
theorem B1733039 : Blo 607294 1733039 := bstep (se 1 (by rfl) ⟨1299779, by rfl⟩ : syracuseStep 1733039 = 2599559) B2599559
theorem B1946081 : Blo 607294 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B1356257 : Blo 607294 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B10711601 : Blo 607294 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B6681149 : Blo 607294 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B684607 : Blo 607294 684607 := bstep (se 1 (by rfl) ⟨513455, by rfl⟩ : syracuseStep 684607 = 1026911) B1026911
theorem B913991 : Blo 607294 913991 := bstep (se 1 (by rfl) ⟨685493, by rfl⟩ : syracuseStep 913991 = 1370987) B1370987
theorem B1372751 : Blo 607294 1372751 := bstep (se 1 (by rfl) ⟨1029563, by rfl⟩ : syracuseStep 1372751 = 2059127) B2059127
theorem B914027 : Blo 607294 914027 := bstep (se 1 (by rfl) ⟨685520, by rfl⟩ : syracuseStep 914027 = 1371041) B1371041
theorem B1372895 : Blo 607294 1372895 := bstep (se 1 (by rfl) ⟨1029671, by rfl⟩ : syracuseStep 1372895 = 2059343) B2059343
theorem B1094419 : Blo 607294 1094419 := bstep (se 1 (by rfl) ⟨820814, by rfl⟩ : syracuseStep 1094419 = 1641629) B1641629
theorem B914255 : Blo 607294 914255 := bstep (se 1 (by rfl) ⟨685691, by rfl⟩ : syracuseStep 914255 = 1371383) B1371383
theorem B4625261 : Blo 607294 4625261 := bstep (se 3 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 4625261 = 1734473) B1734473
theorem B4756333 : Blo 607294 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B3298157 : Blo 607294 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1373147 : Blo 607294 1373147 := bstep (se 1 (by rfl) ⟨1029860, by rfl⟩ : syracuseStep 1373147 = 2059721) B2059721
theorem B865255 : Blo 607294 865255 := bstep (se 1 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 865255 = 1297883) B1297883
theorem B5551183 : Blo 607294 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B1561723 : Blo 607294 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B2315411 : Blo 607294 2315411 := bstep (se 1 (by rfl) ⟨1736558, by rfl⟩ : syracuseStep 2315411 = 3473117) B3473117
theorem B2192599 : Blo 607294 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B914651 : Blo 607294 914651 := bstep (se 1 (by rfl) ⟨685988, by rfl⟩ : syracuseStep 914651 = 1371977) B1371977
theorem B1733881 : Blo 607294 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B11728151 : Blo 607294 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B1537319 : Blo 607294 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B1029415 : Blo 607294 1029415 := bstep (se 1 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 1029415 = 1544123) B1544123
theorem B2307437 : Blo 607294 2307437 := bstep (se 3 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 2307437 = 865289) B865289
theorem B685435 : Blo 607294 685435 := bstep (se 1 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 685435 = 1028153) B1028153
theorem B914825 : Blo 607294 914825 := bstep (se 2 (by rfl) ⟨343059, by rfl⟩ : syracuseStep 914825 = 686119) B686119
theorem B2307467 : Blo 607294 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B2053565 : Blo 607294 2053565 := bstep (se 3 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 2053565 = 770087) B770087
theorem B5207489 : Blo 607294 5207489 := bstep (se 2 (by rfl) ⟨1952808, by rfl⟩ : syracuseStep 5207489 = 3905617) B3905617
theorem B610095 : Blo 607294 610095 := bstep (se 1 (by rfl) ⟨457571, by rfl⟩ : syracuseStep 610095 = 915143) B915143
theorem B1234619 : Blo 607294 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B915179 : Blo 607294 915179 := bstep (se 1 (by rfl) ⟨686384, by rfl⟩ : syracuseStep 915179 = 1372769) B1372769
theorem B3471133 : Blo 607294 3471133 := bstep (se 3 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 3471133 = 1301675) B1301675
theorem B2053943 : Blo 607294 2053943 := bstep (se 1 (by rfl) ⟨1540457, by rfl⟩ : syracuseStep 2053943 = 3080915) B3080915
theorem B751439 : Blo 607294 751439 := bstep (se 1 (by rfl) ⟨563579, by rfl⟩ : syracuseStep 751439 = 1127159) B1127159
theorem B685903 : Blo 607294 685903 := bstep (se 1 (by rfl) ⟨514427, by rfl⟩ : syracuseStep 685903 = 1028855) B1028855
theorem B1464193 : Blo 607294 1464193 := bstep (se 2 (by rfl) ⟨549072, by rfl⟩ : syracuseStep 1464193 = 1098145) B1098145
theorem B915407 : Blo 607294 915407 := bstep (se 1 (by rfl) ⟨686555, by rfl⟩ : syracuseStep 915407 = 1373111) B1373111
theorem B1464425 : Blo 607294 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B686299 : Blo 607294 686299 := bstep (se 1 (by rfl) ⟨514724, by rfl⟩ : syracuseStep 686299 = 1029449) B1029449
theorem B11868389 : Blo 607294 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B5200139 : Blo 607294 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B2054429 : Blo 607294 2054429 := bstep (se 3 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 2054429 = 770411) B770411
theorem B5921099 : Blo 607294 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B1366523 : Blo 607294 1366523 := bstep (se 1 (by rfl) ⟨1024892, by rfl⟩ : syracuseStep 1366523 = 2049785) B2049785
theorem B2193983 : Blo 607294 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B768619 : Blo 607294 768619 := bstep (se 1 (by rfl) ⟨576464, by rfl⟩ : syracuseStep 768619 = 1152929) B1152929
theorem B1366649 : Blo 607294 1366649 := bstep (se 2 (by rfl) ⟨512493, by rfl⟩ : syracuseStep 1366649 = 1024987) B1024987
theorem B1366703 : Blo 607294 1366703 := bstep (se 1 (by rfl) ⟨1025027, by rfl⟩ : syracuseStep 1366703 = 2050055) B2050055
theorem B2472643 : Blo 607294 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B1366775 : Blo 607294 1366775 := bstep (se 1 (by rfl) ⟨1025081, by rfl⟩ : syracuseStep 1366775 = 2050163) B2050163
theorem B2079479 : Blo 607294 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B768847 : Blo 607294 768847 := bstep (se 1 (by rfl) ⟨576635, by rfl⟩ : syracuseStep 768847 = 1153271) B1153271
theorem B1538959 : Blo 607294 1538959 := bstep (se 1 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 1538959 = 2308439) B2308439
theorem B1465231 : Blo 607294 1465231 := bstep (se 1 (by rfl) ⟨1098923, by rfl⟩ : syracuseStep 1465231 = 2197847) B2197847
theorem B1366955 : Blo 607294 1366955 := bstep (se 1 (by rfl) ⟨1025216, by rfl⟩ : syracuseStep 1366955 = 2050433) B2050433
theorem B973739 : Blo 607294 973739 := bstep (se 1 (by rfl) ⟨730304, by rfl⟩ : syracuseStep 973739 = 1460609) B1460609
theorem B2309107 : Blo 607294 2309107 := bstep (se 1 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 2309107 = 3463661) B3463661
theorem B6945911 : Blo 607294 6945911 := bstep (se 1 (by rfl) ⟨5209433, by rfl⟩ : syracuseStep 6945911 = 10418867) B10418867
theorem B4619429 : Blo 607294 4619429 := bstep (se 4 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 4619429 = 866143) B866143
theorem B1465559 : Blo 607294 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B3292427 : Blo 607294 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B2055455 : Blo 607294 2055455 := bstep (se 1 (by rfl) ⟨1541591, by rfl⟩ : syracuseStep 2055455 = 3083183) B3083183
theorem B1539425 : Blo 607294 1539425 := bstep (se 2 (by rfl) ⟨577284, by rfl⟩ : syracuseStep 1539425 = 1154569) B1154569
theorem B1367495 : Blo 607294 1367495 := bstep (se 1 (by rfl) ⟨1025621, by rfl⟩ : syracuseStep 1367495 = 2051243) B2051243
theorem B4382201 : Blo 607294 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B3087881 : Blo 607294 3087881 := bstep (se 2 (by rfl) ⟨1157955, by rfl⟩ : syracuseStep 3087881 = 2315911) B2315911
theorem B2932307 : Blo 607294 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B2309867 : Blo 607294 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B3079943 : Blo 607294 3079943 := bstep (se 1 (by rfl) ⟨2309957, by rfl⟩ : syracuseStep 3079943 = 4619915) B4619915
theorem B18013985 : Blo 607294 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1539881 : Blo 607294 1539881 := bstep (se 2 (by rfl) ⟨577455, by rfl⟩ : syracuseStep 1539881 = 1154911) B1154911
theorem B1367855 : Blo 607294 1367855 := bstep (se 1 (by rfl) ⟨1025891, by rfl⟩ : syracuseStep 1367855 = 2051783) B2051783
theorem B1154873 : Blo 607294 1154873 := bstep (se 2 (by rfl) ⟨433077, by rfl⟩ : syracuseStep 1154873 = 866155) B866155
theorem B4931401 : Blo 607294 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B4456367 : Blo 607294 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B20299855 : Blo 607294 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B1540235 : Blo 607294 1540235 := bstep (se 1 (by rfl) ⟨1155176, by rfl⟩ : syracuseStep 1540235 = 2310353) B2310353
theorem B1736923 : Blo 607294 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B1155359 : Blo 607294 1155359 := bstep (se 1 (by rfl) ⟨866519, by rfl⟩ : syracuseStep 1155359 = 1733039) B1733039
theorem B868735 : Blo 607294 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B29606309 : Blo 607294 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B1540559 : Blo 607294 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B2605607 : Blo 607294 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B16630343 : Blo 607294 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B950887 : Blo 607294 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B3474049 : Blo 607294 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B7037725 : Blo 607294 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B1024825 : Blo 607294 1024825 := bstep (se 2 (by rfl) ⟨384309, by rfl⟩ : syracuseStep 1024825 = 768619) B768619
theorem B1024879 : Blo 607294 1024879 := bstep (se 1 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 1024879 = 1537319) B1537319
theorem B1369043 : Blo 607294 1369043 := bstep (se 1 (by rfl) ⟨1026782, by rfl⟩ : syracuseStep 1369043 = 2053565) B2053565
theorem B23708675 : Blo 607294 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B1459225 : Blo 607294 1459225 := bstep (se 2 (by rfl) ⟨547209, by rfl⟩ : syracuseStep 1459225 = 1094419) B1094419
theorem B607295 : Blo 607294 607295 := bstep (se 1 (by rfl) ⟨455471, by rfl⟩ : syracuseStep 607295 = 910943) B910943
theorem B3892313 : Blo 607294 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B1025129 : Blo 607294 1025129 := bstep (se 2 (by rfl) ⟨384423, by rfl⟩ : syracuseStep 1025129 = 768847) B768847
theorem B6341777 : Blo 607294 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B607439 : Blo 607294 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B1369295 : Blo 607294 1369295 := bstep (se 1 (by rfl) ⟨1026971, by rfl⟩ : syracuseStep 1369295 = 2053943) B2053943
theorem B5866711 : Blo 607294 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B607643 : Blo 607294 607643 := bstep (se 1 (by rfl) ⟨455732, by rfl⟩ : syracuseStep 607643 = 911465) B911465
theorem B976283 : Blo 607294 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B1541551 : Blo 607294 1541551 := bstep (se 1 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 1541551 = 2312327) B2312327
theorem B3081725 : Blo 607294 3081725 := bstep (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) B1155647
theorem B3466759 : Blo 607294 3466759 := bstep (se 1 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 3466759 = 5200139) B5200139
theorem B1369619 : Blo 607294 1369619 := bstep (se 1 (by rfl) ⟨1027214, by rfl⟩ : syracuseStep 1369619 = 2054429) B2054429
theorem B607855 : Blo 607294 607855 := bstep (se 1 (by rfl) ⟨455891, by rfl⟩ : syracuseStep 607855 = 911783) B911783
theorem B2311841 : Blo 607294 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B911015 : Blo 607294 911015 := bstep (se 1 (by rfl) ⟨683261, by rfl⟩ : syracuseStep 911015 = 1366523) B1366523
theorem B607911 : Blo 607294 607911 := bstep (se 1 (by rfl) ⟨455933, by rfl⟩ : syracuseStep 607911 = 911867) B911867
theorem B1541855 : Blo 607294 1541855 := bstep (se 1 (by rfl) ⟨1156391, by rfl⟩ : syracuseStep 1541855 = 2312783) B2312783
theorem B911099 : Blo 607294 911099 := bstep (se 1 (by rfl) ⟨683324, by rfl⟩ : syracuseStep 911099 = 1366649) B1366649
theorem B607995 : Blo 607294 607995 := bstep (se 1 (by rfl) ⟨455996, by rfl⟩ : syracuseStep 607995 = 911993) B911993
theorem B911135 : Blo 607294 911135 := bstep (se 1 (by rfl) ⟨683351, by rfl⟩ : syracuseStep 911135 = 1366703) B1366703
theorem B608031 : Blo 607294 608031 := bstep (se 1 (by rfl) ⟨456023, by rfl⟩ : syracuseStep 608031 = 912047) B912047
theorem B608063 : Blo 607294 608063 := bstep (se 1 (by rfl) ⟨456047, by rfl⟩ : syracuseStep 608063 = 912095) B912095
theorem B911183 : Blo 607294 911183 := bstep (se 1 (by rfl) ⟨683387, by rfl⟩ : syracuseStep 911183 = 1366775) B1366775
theorem B1386319 : Blo 607294 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B911303 : Blo 607294 911303 := bstep (se 1 (by rfl) ⟨683477, by rfl⟩ : syracuseStep 911303 = 1366955) B1366955
theorem B608239 : Blo 607294 608239 := bstep (se 1 (by rfl) ⟨456179, by rfl⟩ : syracuseStep 608239 = 912359) B912359
theorem B4630607 : Blo 607294 4630607 := bstep (se 1 (by rfl) ⟨3472955, by rfl⟩ : syracuseStep 4630607 = 6945911) B6945911
theorem B8685683 : Blo 607294 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B977039 : Blo 607294 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B608411 : Blo 607294 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B608447 : Blo 607294 608447 := bstep (se 1 (by rfl) ⟨456335, by rfl⟩ : syracuseStep 608447 = 912671) B912671
theorem B1370303 : Blo 607294 1370303 := bstep (se 1 (by rfl) ⟨1027727, by rfl⟩ : syracuseStep 1370303 = 2055455) B2055455
theorem B1026283 : Blo 607294 1026283 := bstep (se 1 (by rfl) ⟨769712, by rfl⟩ : syracuseStep 1026283 = 1539425) B1539425
theorem B3082535 : Blo 607294 3082535 := bstep (se 1 (by rfl) ⟨2311901, by rfl⟩ : syracuseStep 3082535 = 4623803) B4623803
theorem B911657 : Blo 607294 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B911663 : Blo 607294 911663 := bstep (se 1 (by rfl) ⟨683747, by rfl⟩ : syracuseStep 911663 = 1367495) B1367495
theorem B608559 : Blo 607294 608559 := bstep (se 1 (by rfl) ⟨456419, by rfl⟩ : syracuseStep 608559 = 912839) B912839
theorem B2312495 : Blo 607294 2312495 := bstep (se 1 (by rfl) ⟨1734371, by rfl⟩ : syracuseStep 2312495 = 3468743) B3468743
theorem B4679993 : Blo 607294 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B2058587 : Blo 607294 2058587 := bstep (se 1 (by rfl) ⟨1543940, by rfl⟩ : syracuseStep 2058587 = 3087881) B3087881
theorem B3082697 : Blo 607294 3082697 := bstep (se 2 (by rfl) ⟨1156011, by rfl⟩ : syracuseStep 3082697 = 2312023) B2312023
theorem B1952257 : Blo 607294 1952257 := bstep (se 2 (by rfl) ⟨732096, by rfl⟩ : syracuseStep 1952257 = 1464193) B1464193
theorem B1026587 : Blo 607294 1026587 := bstep (se 1 (by rfl) ⟨769940, by rfl⟩ : syracuseStep 1026587 = 1539881) B1539881
theorem B608795 : Blo 607294 608795 := bstep (se 1 (by rfl) ⟨456596, by rfl⟩ : syracuseStep 608795 = 913193) B913193
theorem B911903 : Blo 607294 911903 := bstep (se 1 (by rfl) ⟨683927, by rfl⟩ : syracuseStep 911903 = 1367855) B1367855
theorem B608799 : Blo 607294 608799 := bstep (se 1 (by rfl) ⟨456599, by rfl⟩ : syracuseStep 608799 = 913199) B913199
theorem B3295775 : Blo 607294 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B2058857 : Blo 607294 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B56183543 : Blo 607294 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B10529585 : Blo 607294 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B609115 : Blo 607294 609115 := bstep (se 1 (by rfl) ⟨456836, by rfl⟩ : syracuseStep 609115 = 913673) B913673
theorem B4615055 : Blo 607294 4615055 := bstep (se 1 (by rfl) ⟨3461291, by rfl⟩ : syracuseStep 4615055 = 6922583) B6922583
theorem B3459995 : Blo 607294 3459995 := bstep (se 1 (by rfl) ⟨2594996, by rfl⟩ : syracuseStep 3459995 = 5189993) B5189993
theorem B912287 : Blo 607294 912287 := bstep (se 1 (by rfl) ⟨684215, by rfl⟩ : syracuseStep 912287 = 1368431) B1368431
theorem B609183 : Blo 607294 609183 := bstep (se 1 (by rfl) ⟨456887, by rfl⟩ : syracuseStep 609183 = 913775) B913775
theorem B912335 : Blo 607294 912335 := bstep (se 1 (by rfl) ⟨684251, by rfl⟩ : syracuseStep 912335 = 1368503) B1368503
theorem B11119589 : Blo 607294 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B1297387 : Blo 607294 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B904171 : Blo 607294 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B5008391 : Blo 607294 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B912425 : Blo 607294 912425 := bstep (se 2 (by rfl) ⟨342159, by rfl⟩ : syracuseStep 912425 = 684319) B684319
theorem B912431 : Blo 607294 912431 := bstep (se 1 (by rfl) ⟨684323, by rfl⟩ : syracuseStep 912431 = 1368647) B1368647
theorem B609327 : Blo 607294 609327 := bstep (se 1 (by rfl) ⟨456995, by rfl⟩ : syracuseStep 609327 = 913991) B913991
theorem B912455 : Blo 607294 912455 := bstep (se 1 (by rfl) ⟨684341, by rfl⟩ : syracuseStep 912455 = 1368683) B1368683
theorem B609351 : Blo 607294 609351 := bstep (se 1 (by rfl) ⟨457013, by rfl⟩ : syracuseStep 609351 = 914027) B914027
theorem B1371257 : Blo 607294 1371257 := bstep (se 2 (by rfl) ⟨514221, by rfl⟩ : syracuseStep 1371257 = 1028443) B1028443
theorem B1027255 : Blo 607294 1027255 := bstep (se 1 (by rfl) ⟨770441, by rfl⟩ : syracuseStep 1027255 = 1540883) B1540883
theorem B609503 : Blo 607294 609503 := bstep (se 1 (by rfl) ⟨457127, by rfl⟩ : syracuseStep 609503 = 914255) B914255
theorem B3083507 : Blo 607294 3083507 := bstep (se 1 (by rfl) ⟨2312630, by rfl⟩ : syracuseStep 3083507 = 4625261) B4625261
theorem B2198771 : Blo 607294 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B912719 : Blo 607294 912719 := bstep (se 1 (by rfl) ⟨684539, by rfl⟩ : syracuseStep 912719 = 1369079) B1369079
theorem B4943213 : Blo 607294 4943213 := bstep (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) B1853705
theorem B11873665 : Blo 607294 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B912809 : Blo 607294 912809 := bstep (se 2 (by rfl) ⟨342303, by rfl⟩ : syracuseStep 912809 = 684607) B684607
theorem B1543607 : Blo 607294 1543607 := bstep (se 1 (by rfl) ⟨1157705, by rfl⟩ : syracuseStep 1543607 = 2315411) B2315411
theorem B1027559 : Blo 607294 1027559 := bstep (se 1 (by rfl) ⟨770669, by rfl⟩ : syracuseStep 1027559 = 1541339) B1541339
theorem B609767 : Blo 607294 609767 := bstep (se 1 (by rfl) ⟨457325, by rfl⟩ : syracuseStep 609767 = 914651) B914651
theorem B1027579 : Blo 607294 1027579 := bstep (se 1 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 1027579 = 1541369) B1541369
theorem B7818767 : Blo 607294 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B912959 : Blo 607294 912959 := bstep (se 1 (by rfl) ⟨684719, by rfl⟩ : syracuseStep 912959 = 1369439) B1369439
theorem B3296857 : Blo 607294 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B609883 : Blo 607294 609883 := bstep (se 1 (by rfl) ⟨457412, by rfl⟩ : syracuseStep 609883 = 914825) B914825
theorem B1371923 : Blo 607294 1371923 := bstep (se 1 (by rfl) ⟨1028942, by rfl⟩ : syracuseStep 1371923 = 2057885) B2057885
theorem B683815 : Blo 607294 683815 := bstep (se 1 (by rfl) ⟨512861, by rfl⟩ : syracuseStep 683815 = 1025723) B1025723
theorem B823079 : Blo 607294 823079 := bstep (se 1 (by rfl) ⟨617309, by rfl⟩ : syracuseStep 823079 = 1234619) B1234619
theorem B913223 : Blo 607294 913223 := bstep (se 1 (by rfl) ⟨684917, by rfl⟩ : syracuseStep 913223 = 1369835) B1369835
theorem B610119 : Blo 607294 610119 := bstep (se 1 (by rfl) ⟨457589, by rfl⟩ : syracuseStep 610119 = 915179) B915179
theorem B2051945 : Blo 607294 2051945 := bstep (se 2 (by rfl) ⟨769479, by rfl⟩ : syracuseStep 2051945 = 1538959) B1538959
theorem B1953641 : Blo 607294 1953641 := bstep (se 2 (by rfl) ⟨732615, by rfl⟩ : syracuseStep 1953641 = 1465231) B1465231
theorem B2920313 : Blo 607294 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B2781067 : Blo 607294 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B913307 : Blo 607294 913307 := bstep (se 1 (by rfl) ⟨684980, by rfl⟩ : syracuseStep 913307 = 1369961) B1369961
theorem B1028011 : Blo 607294 1028011 := bstep (se 1 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 1028011 = 1542017) B1542017
theorem B379097009 : Blo 607294 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B610271 : Blo 607294 610271 := bstep (se 1 (by rfl) ⟨457703, by rfl⟩ : syracuseStep 610271 = 915407) B915407
theorem B1372283 : Blo 607294 1372283 := bstep (se 1 (by rfl) ⟨1029212, by rfl⟩ : syracuseStep 1372283 = 2058425) B2058425
theorem B2306177 : Blo 607294 2306177 := bstep (se 2 (by rfl) ⟨864816, by rfl⟩ : syracuseStep 2306177 = 1729633) B1729633
theorem B1028315 : Blo 607294 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B3475507 : Blo 607294 3475507 := bstep (se 1 (by rfl) ⟨2606630, by rfl⟩ : syracuseStep 3475507 = 5213261) B5213261
theorem B1462655 : Blo 607294 1462655 := bstep (se 1 (by rfl) ⟨1096991, by rfl⟩ : syracuseStep 1462655 = 2193983) B2193983
theorem B1372553 : Blo 607294 1372553 := bstep (se 2 (by rfl) ⟨514707, by rfl⟩ : syracuseStep 1372553 = 1029415) B1029415
theorem B1847719 : Blo 607294 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B1028551 : Blo 607294 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B913871 : Blo 607294 913871 := bstep (se 1 (by rfl) ⟨685403, by rfl⟩ : syracuseStep 913871 = 1370807) B1370807
theorem B1028585 : Blo 607294 1028585 := bstep (se 2 (by rfl) ⟨385719, by rfl⟩ : syracuseStep 1028585 = 771439) B771439
theorem B913913 : Blo 607294 913913 := bstep (se 2 (by rfl) ⟨342717, by rfl⟩ : syracuseStep 913913 = 685435) B685435
theorem B3904001 : Blo 607294 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B914015 : Blo 607294 914015 := bstep (se 1 (by rfl) ⟨685511, by rfl⟩ : syracuseStep 914015 = 1371023) B1371023
theorem B2003837 : Blo 607294 2003837 := bstep (se 3 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 2003837 = 751439) B751439
theorem B684967 : Blo 607294 684967 := bstep (se 1 (by rfl) ⟨513725, by rfl⟩ : syracuseStep 684967 = 1027451) B1027451
theorem B2921467 : Blo 607294 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B1954871 : Blo 607294 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B8787001 : Blo 607294 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B914495 : Blo 607294 914495 := bstep (se 1 (by rfl) ⟨685871, by rfl⟩ : syracuseStep 914495 = 1371743) B1371743
theorem B10663001 : Blo 607294 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B6575201 : Blo 607294 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B914537 : Blo 607294 914537 := bstep (se 2 (by rfl) ⟨342951, by rfl⟩ : syracuseStep 914537 = 685903) B685903
theorem B2053295 : Blo 607294 2053295 := bstep (se 1 (by rfl) ⟨1539971, by rfl⟩ : syracuseStep 2053295 = 3079943) B3079943
theorem B914639 : Blo 607294 914639 := bstep (se 1 (by rfl) ⟨685979, by rfl⟩ : syracuseStep 914639 = 1371959) B1371959
theorem B11277521 : Blo 607294 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B1848595 : Blo 607294 1848595 := bstep (se 1 (by rfl) ⟨1386446, by rfl⟩ : syracuseStep 1848595 = 2772893) B2772893
theorem B2970911 : Blo 607294 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B4175165 : Blo 607294 4175165 := bstep (se 3 (by rfl) ⟨782843, by rfl⟩ : syracuseStep 4175165 = 1565687) B1565687
theorem B914843 : Blo 607294 914843 := bstep (se 1 (by rfl) ⟨686132, by rfl⟩ : syracuseStep 914843 = 1372265) B1372265
theorem B915065 : Blo 607294 915065 := bstep (se 2 (by rfl) ⟨343149, by rfl⟩ : syracuseStep 915065 = 686299) B686299
theorem B7141067 : Blo 607294 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B4454099 : Blo 607294 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B915167 : Blo 607294 915167 := bstep (se 1 (by rfl) ⟨686375, by rfl⟩ : syracuseStep 915167 = 1372751) B1372751
theorem B4626233 : Blo 607294 4626233 := bstep (se 2 (by rfl) ⟨1734837, by rfl⟩ : syracuseStep 4626233 = 3469675) B3469675
theorem B915263 : Blo 607294 915263 := bstep (se 1 (by rfl) ⟨686447, by rfl⟩ : syracuseStep 915263 = 1372895) B1372895
theorem B923471 : Blo 607294 923471 := bstep (se 1 (by rfl) ⟨692603, by rfl⟩ : syracuseStep 923471 = 1385207) B1385207
theorem B8763241 : Blo 607294 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B8337289 : Blo 607294 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B8329189 : Blo 607294 8329189 := bstep (se 4 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 8329189 = 1561723) B1561723
theorem B1169383 : Blo 607294 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B915431 : Blo 607294 915431 := bstep (se 1 (by rfl) ⟨686573, by rfl⟩ : syracuseStep 915431 = 1373147) B1373147
theorem B2316383 : Blo 607294 2316383 := bstep (se 1 (by rfl) ⟨1737287, by rfl⟩ : syracuseStep 2316383 = 3474575) B3474575
theorem B10410119 : Blo 607294 10410119 := bstep (se 1 (by rfl) ⟨7807589, by rfl⟩ : syracuseStep 10410119 = 15615179) B15615179
theorem B1538291 : Blo 607294 1538291 := bstep (se 1 (by rfl) ⟨1153718, by rfl⟩ : syracuseStep 1538291 = 2307437) B2307437
theorem B1538311 : Blo 607294 1538311 := bstep (se 1 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 1538311 = 2307467) B2307467
theorem B3471659 : Blo 607294 3471659 := bstep (se 1 (by rfl) ⟨2603744, by rfl⟩ : syracuseStep 3471659 = 5207489) B5207489
theorem B6576551 : Blo 607294 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B102816289 : Blo 607294 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B1153673 : Blo 607294 1153673 := bstep (se 2 (by rfl) ⟨432627, by rfl⟩ : syracuseStep 1153673 = 865255) B865255
theorem B3078809 : Blo 607294 3078809 := bstep (se 2 (by rfl) ⟨1154553, by rfl⟩ : syracuseStep 3078809 = 2309107) B2309107
theorem B7412381 : Blo 607294 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B7912259 : Blo 607294 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B3947399 : Blo 607294 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B2923465 : Blo 607294 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B1366991 : Blo 607294 1366991 := bstep (se 1 (by rfl) ⟨1025243, by rfl⟩ : syracuseStep 1366991 = 2050487) B2050487
theorem B1367009 : Blo 607294 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B1367081 : Blo 607294 1367081 := bstep (se 2 (by rfl) ⟨512655, by rfl⟩ : syracuseStep 1367081 = 1025311) B1025311
theorem B2055239 : Blo 607294 2055239 := bstep (se 1 (by rfl) ⟨1541429, by rfl⟩ : syracuseStep 2055239 = 3082859) B3082859
theorem B2055293 : Blo 607294 2055293 := bstep (se 3 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 2055293 = 770735) B770735
theorem B5627083 : Blo 607294 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B2923735 : Blo 607294 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B974047 : Blo 607294 974047 := bstep (se 1 (by rfl) ⟨730535, by rfl⟩ : syracuseStep 974047 = 1461071) B1461071
theorem B4406521 : Blo 607294 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B2055563 : Blo 607294 2055563 := bstep (se 1 (by rfl) ⟨1541672, by rfl⟩ : syracuseStep 2055563 = 3083345) B3083345
theorem B3079619 : Blo 607294 3079619 := bstep (se 1 (by rfl) ⟨2309714, by rfl⟩ : syracuseStep 3079619 = 4619429) B4619429
theorem B7396811 : Blo 607294 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B3898853 : Blo 607294 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B2194951 : Blo 607294 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B4628177 : Blo 607294 4628177 := bstep (se 2 (by rfl) ⟨1735566, by rfl⟩ : syracuseStep 4628177 = 3471133) B3471133
theorem B29556485 : Blo 607294 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B2596637 : Blo 607294 2596637 := bstep (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) B973739
theorem B1539911 : Blo 607294 1539911 := bstep (se 1 (by rfl) ⟨1154933, by rfl⟩ : syracuseStep 1539911 = 2309867) B2309867
theorem B12009323 : Blo 607294 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B769915 : Blo 607294 769915 := bstep (se 1 (by rfl) ⟨577436, by rfl⟩ : syracuseStep 769915 = 1154873) B1154873
theorem B27066473 : Blo 607294 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B770239 : Blo 607294 770239 := bstep (se 1 (by rfl) ⟨577679, by rfl⟩ : syracuseStep 770239 = 1155359) B1155359
theorem B10379501 : Blo 607294 10379501 := bstep (se 3 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 10379501 = 3892313) B3892313
theorem B1368377 : Blo 607294 1368377 := bstep (se 2 (by rfl) ⟨513141, by rfl⟩ : syracuseStep 1368377 = 1026283) B1026283
theorem B1737071 : Blo 607294 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B1303247 : Blo 607294 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B4383467 : Blo 607294 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B4227851 : Blo 607294 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B1368863 : Blo 607294 1368863 := bstep (se 1 (by rfl) ⟨1026647, by rfl⟩ : syracuseStep 1368863 = 2053295) B2053295
theorem B3900413 : Blo 607294 3900413 := bstep (se 3 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 3900413 = 1462655) B1462655
theorem B1541227 : Blo 607294 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B607343 : Blo 607294 607343 := bstep (se 1 (by rfl) ⟨455507, by rfl⟩ : syracuseStep 607343 = 911015) B911015
theorem B4760711 : Blo 607294 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B607399 : Blo 607294 607399 := bstep (se 1 (by rfl) ⟨455549, by rfl⟩ : syracuseStep 607399 = 911099) B911099
theorem B607423 : Blo 607294 607423 := bstep (se 1 (by rfl) ⟨455567, by rfl⟩ : syracuseStep 607423 = 911135) B911135
theorem B615647 : Blo 607294 615647 := bstep (se 1 (by rfl) ⟨461735, by rfl⟩ : syracuseStep 615647 = 923471) B923471
theorem B607455 : Blo 607294 607455 := bstep (se 1 (by rfl) ⟨455591, by rfl⟩ : syracuseStep 607455 = 911183) B911183
theorem B607535 : Blo 607294 607535 := bstep (se 1 (by rfl) ⟨455651, by rfl⟩ : syracuseStep 607535 = 911303) B911303
theorem B1729849 : Blo 607294 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B1205561 : Blo 607294 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B11716001 : Blo 607294 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B6940079 : Blo 607294 6940079 := bstep (se 1 (by rfl) ⟨5205059, by rfl⟩ : syracuseStep 6940079 = 10410119) B10410119
theorem B1025527 : Blo 607294 1025527 := bstep (se 1 (by rfl) ⟨769145, by rfl⟩ : syracuseStep 1025527 = 1538291) B1538291
theorem B607771 : Blo 607294 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B607775 : Blo 607294 607775 := bstep (se 1 (by rfl) ⟨455831, by rfl⟩ : syracuseStep 607775 = 911663) B911663
theorem B1541663 : Blo 607294 1541663 := bstep (se 1 (by rfl) ⟨1156247, by rfl⟩ : syracuseStep 1541663 = 2312495) B2312495
theorem B1369673 : Blo 607294 1369673 := bstep (se 2 (by rfl) ⟨513627, by rfl⟩ : syracuseStep 1369673 = 1027255) B1027255
theorem B4384367 : Blo 607294 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B607935 : Blo 607294 607935 := bstep (se 1 (by rfl) ⟨455951, by rfl⟩ : syracuseStep 607935 = 911903) B911903
theorem B4941587 : Blo 607294 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B37455695 : Blo 607294 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B2631599 : Blo 607294 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B608191 : Blo 607294 608191 := bstep (se 1 (by rfl) ⟨456143, by rfl⟩ : syracuseStep 608191 = 912287) B912287
theorem B911327 : Blo 607294 911327 := bstep (se 1 (by rfl) ⟨683495, by rfl⟩ : syracuseStep 911327 = 1366991) B1366991
theorem B608223 : Blo 607294 608223 := bstep (se 1 (by rfl) ⟨456167, by rfl⟩ : syracuseStep 608223 = 912335) B912335
theorem B911339 : Blo 607294 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B1370105 : Blo 607294 1370105 := bstep (se 2 (by rfl) ⟨513789, by rfl⟩ : syracuseStep 1370105 = 1027579) B1027579
theorem B4622345 : Blo 607294 4622345 := bstep (se 2 (by rfl) ⟨1733379, by rfl⟩ : syracuseStep 4622345 = 3466759) B3466759
theorem B2926601 : Blo 607294 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B911387 : Blo 607294 911387 := bstep (se 1 (by rfl) ⟨683540, by rfl⟩ : syracuseStep 911387 = 1367081) B1367081
theorem B608283 : Blo 607294 608283 := bstep (se 1 (by rfl) ⟨456212, by rfl⟩ : syracuseStep 608283 = 912425) B912425
theorem B608287 : Blo 607294 608287 := bstep (se 1 (by rfl) ⟨456215, by rfl⟩ : syracuseStep 608287 = 912431) B912431
theorem B608303 : Blo 607294 608303 := bstep (se 1 (by rfl) ⟨456227, by rfl⟩ : syracuseStep 608303 = 912455) B912455
theorem B1370159 : Blo 607294 1370159 := bstep (se 1 (by rfl) ⟨1027619, by rfl⟩ : syracuseStep 1370159 = 2055239) B2055239
theorem B1370195 : Blo 607294 1370195 := bstep (se 1 (by rfl) ⟨1027646, by rfl⟩ : syracuseStep 1370195 = 2055293) B2055293
theorem B608479 : Blo 607294 608479 := bstep (se 1 (by rfl) ⟨456359, by rfl⟩ : syracuseStep 608479 = 912719) B912719
theorem B3295475 : Blo 607294 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B1370375 : Blo 607294 1370375 := bstep (se 1 (by rfl) ⟨1027781, by rfl⟩ : syracuseStep 1370375 = 2055563) B2055563
theorem B608539 : Blo 607294 608539 := bstep (se 1 (by rfl) ⟨456404, by rfl⟩ : syracuseStep 608539 = 912809) B912809
theorem B2599235 : Blo 607294 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B5343565 : Blo 607294 5343565 := bstep (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) B2003837
theorem B608639 : Blo 607294 608639 := bstep (se 1 (by rfl) ⟨456479, by rfl⟩ : syracuseStep 608639 = 912959) B912959
theorem B911753 : Blo 607294 911753 := bstep (se 2 (by rfl) ⟨341907, by rfl⟩ : syracuseStep 911753 = 683815) B683815
theorem B11684321 : Blo 607294 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B1026553 : Blo 607294 1026553 := bstep (se 2 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 1026553 = 769915) B769915
theorem B19704323 : Blo 607294 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B1731091 : Blo 607294 1731091 := bstep (se 1 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 1731091 = 2596637) B2596637
theorem B1026607 : Blo 607294 1026607 := bstep (se 1 (by rfl) ⟨769955, by rfl⟩ : syracuseStep 1026607 = 1539911) B1539911
theorem B608815 : Blo 607294 608815 := bstep (se 1 (by rfl) ⟨456611, by rfl⟩ : syracuseStep 608815 = 913223) B913223
theorem B1370681 : Blo 607294 1370681 := bstep (se 2 (by rfl) ⟨514005, by rfl⟩ : syracuseStep 1370681 = 1028011) B1028011
theorem B8006215 : Blo 607294 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B608871 : Blo 607294 608871 := bstep (se 1 (by rfl) ⟨456653, by rfl⟩ : syracuseStep 608871 = 913307) B913307
theorem B1559177 : Blo 607294 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B1026823 : Blo 607294 1026823 := bstep (se 1 (by rfl) ⟨770117, by rfl⟩ : syracuseStep 1026823 = 1540235) B1540235
theorem B5212511 : Blo 607294 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B19737539 : Blo 607294 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B1027039 : Blo 607294 1027039 := bstep (se 1 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 1027039 = 1540559) B1540559
theorem B609247 : Blo 607294 609247 := bstep (se 1 (by rfl) ⟨456935, by rfl⟩ : syracuseStep 609247 = 913871) B913871
theorem B609275 : Blo 607294 609275 := bstep (se 1 (by rfl) ⟨456956, by rfl⟩ : syracuseStep 609275 = 913913) B913913
theorem B2051081 : Blo 607294 2051081 := bstep (se 2 (by rfl) ⟨769155, by rfl⟩ : syracuseStep 2051081 = 1538311) B1538311
theorem B11086895 : Blo 607294 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B609343 : Blo 607294 609343 := bstep (se 1 (by rfl) ⟨457007, by rfl⟩ : syracuseStep 609343 = 914015) B914015
theorem B1158313 : Blo 607294 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B1371401 : Blo 607294 1371401 := bstep (se 2 (by rfl) ⟨514275, by rfl⟩ : syracuseStep 1371401 = 1028551) B1028551
theorem B912695 : Blo 607294 912695 := bstep (se 1 (by rfl) ⟨684521, by rfl⟩ : syracuseStep 912695 = 1369043) B1369043
theorem B15805783 : Blo 607294 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B609663 : Blo 607294 609663 := bstep (se 1 (by rfl) ⟨457247, by rfl⟩ : syracuseStep 609663 = 914495) B914495
theorem B137088385 : Blo 607294 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B683419 : Blo 607294 683419 := bstep (se 1 (by rfl) ⟨512564, by rfl⟩ : syracuseStep 683419 = 1025129) B1025129
theorem B609691 : Blo 607294 609691 := bstep (se 1 (by rfl) ⟨457268, by rfl⟩ : syracuseStep 609691 = 914537) B914537
theorem B912863 : Blo 607294 912863 := bstep (se 1 (by rfl) ⟨684647, by rfl⟩ : syracuseStep 912863 = 1369295) B1369295
theorem B609759 : Blo 607294 609759 := bstep (se 1 (by rfl) ⟨457319, by rfl⟩ : syracuseStep 609759 = 914639) B914639
theorem B4632065 : Blo 607294 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B650855 : Blo 607294 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B609895 : Blo 607294 609895 := bstep (se 1 (by rfl) ⟨457421, by rfl⟩ : syracuseStep 609895 = 914843) B914843
theorem B913079 : Blo 607294 913079 := bstep (se 1 (by rfl) ⟨684809, by rfl⟩ : syracuseStep 913079 = 1369619) B1369619
theorem B9383633 : Blo 607294 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B610043 : Blo 607294 610043 := bstep (se 1 (by rfl) ⟨457532, by rfl⟩ : syracuseStep 610043 = 915065) B915065
theorem B31289125 : Blo 607294 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B2969399 : Blo 607294 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B1027903 : Blo 607294 1027903 := bstep (se 1 (by rfl) ⟨770927, by rfl⟩ : syracuseStep 1027903 = 1541855) B1541855
theorem B610111 : Blo 607294 610111 := bstep (se 1 (by rfl) ⟨457583, by rfl⟩ : syracuseStep 610111 = 915167) B915167
theorem B3084155 : Blo 607294 3084155 := bstep (se 1 (by rfl) ⟨2313116, by rfl⟩ : syracuseStep 3084155 = 4626233) B4626233
theorem B610175 : Blo 607294 610175 := bstep (se 1 (by rfl) ⟨457631, by rfl⟩ : syracuseStep 610175 = 915263) B915263
theorem B913289 : Blo 607294 913289 := bstep (se 2 (by rfl) ⟨342483, by rfl⟩ : syracuseStep 913289 = 684967) B684967
theorem B610287 : Blo 607294 610287 := bstep (se 1 (by rfl) ⟨457715, by rfl⟩ : syracuseStep 610287 = 915431) B915431
theorem B3895289 : Blo 607294 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B1945633 : Blo 607294 1945633 := bstep (se 2 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 1945633 = 1459225) B1459225
theorem B1544255 : Blo 607294 1544255 := bstep (se 1 (by rfl) ⟨1158191, by rfl⟩ : syracuseStep 1544255 = 2316383) B2316383
theorem B651359 : Blo 607294 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B913535 : Blo 607294 913535 := bstep (se 1 (by rfl) ⟨685151, by rfl⟩ : syracuseStep 913535 = 1370303) B1370303
theorem B2314439 : Blo 607294 2314439 := bstep (se 1 (by rfl) ⟨1735829, by rfl⟩ : syracuseStep 2314439 = 3471659) B3471659
theorem B1372391 : Blo 607294 1372391 := bstep (se 1 (by rfl) ⟨1029293, by rfl⟩ : syracuseStep 1372391 = 2058587) B2058587
theorem B1298729 : Blo 607294 1298729 := bstep (se 2 (by rfl) ⟨487023, by rfl⟩ : syracuseStep 1298729 = 974047) B974047
theorem B684391 : Blo 607294 684391 := bstep (se 1 (by rfl) ⟨513293, by rfl⟩ : syracuseStep 684391 = 1026587) B1026587
theorem B1372571 : Blo 607294 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B2052539 : Blo 607294 2052539 := bstep (se 1 (by rfl) ⟨1539404, by rfl⟩ : syracuseStep 2052539 = 3078809) B3078809
theorem B15831553 : Blo 607294 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B3076703 : Blo 607294 3076703 := bstep (se 1 (by rfl) ⟨2307527, by rfl⟩ : syracuseStep 3076703 = 4615055) B4615055
theorem B2306663 : Blo 607294 2306663 := bstep (se 1 (by rfl) ⟨1729997, by rfl⟩ : syracuseStep 2306663 = 3459995) B3459995
theorem B3338927 : Blo 607294 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B914171 : Blo 607294 914171 := bstep (se 1 (by rfl) ⟨685628, by rfl⟩ : syracuseStep 914171 = 1371257) B1371257
theorem B4395809 : Blo 607294 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B1029071 : Blo 607294 1029071 := bstep (se 1 (by rfl) ⟨771803, by rfl⟩ : syracuseStep 1029071 = 1543607) B1543607
theorem B2053079 : Blo 607294 2053079 := bstep (se 1 (by rfl) ⟨1539809, by rfl⟩ : syracuseStep 2053079 = 3079619) B3079619
theorem B685039 : Blo 607294 685039 := bstep (se 1 (by rfl) ⟨513779, by rfl⟩ : syracuseStep 685039 = 1027559) B1027559
theorem B1848425 : Blo 607294 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B3085451 : Blo 607294 3085451 := bstep (se 1 (by rfl) ⟨2314088, by rfl⟩ : syracuseStep 3085451 = 4628177) B4628177
theorem B914615 : Blo 607294 914615 := bstep (se 1 (by rfl) ⟨685961, by rfl⟩ : syracuseStep 914615 = 1371923) B1371923
theorem B3708089 : Blo 607294 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B1946875 : Blo 607294 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B11105585 : Blo 607294 11105585 := bstep (se 2 (by rfl) ⟨4164594, by rfl⟩ : syracuseStep 11105585 = 8329189) B8329189
theorem B4634009 : Blo 607294 4634009 := bstep (se 2 (by rfl) ⟨1737753, by rfl⟩ : syracuseStep 4634009 = 3475507) B3475507
theorem B914855 : Blo 607294 914855 := bstep (se 1 (by rfl) ⟨686141, by rfl⟩ : syracuseStep 914855 = 1372283) B1372283
theorem B1537451 : Blo 607294 1537451 := bstep (se 1 (by rfl) ⟨1153088, by rfl⟩ : syracuseStep 1537451 = 2306177) B2306177
theorem B685543 : Blo 607294 685543 := bstep (se 1 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 685543 = 1028315) B1028315
theorem B915035 : Blo 607294 915035 := bstep (se 1 (by rfl) ⟨686276, by rfl⟩ : syracuseStep 915035 = 1372553) B1372553
theorem B2315897 : Blo 607294 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B685723 : Blo 607294 685723 := bstep (se 1 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 685723 = 1028585) B1028585
theorem B2602667 : Blo 607294 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B2463625 : Blo 607294 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B2603009 : Blo 607294 2603009 := bstep (se 2 (by rfl) ⟨976128, by rfl⟩ : syracuseStep 2603009 = 1952257) B1952257
theorem B7108667 : Blo 607294 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B1267849 : Blo 607294 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B7518347 : Blo 607294 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B1980607 : Blo 607294 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B2783443 : Blo 607294 2783443 := bstep (se 1 (by rfl) ⟨2087582, by rfl⟩ : syracuseStep 2783443 = 4175165) B4175165
theorem B2054483 : Blo 607294 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B1366433 : Blo 607294 1366433 := bstep (se 2 (by rfl) ⟨512412, by rfl⟩ : syracuseStep 1366433 = 1024825) B1024825
theorem B1366505 : Blo 607294 1366505 := bstep (se 2 (by rfl) ⟨512439, by rfl⟩ : syracuseStep 1366505 = 1024879) B1024879
theorem B3897953 : Blo 607294 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B3087071 : Blo 607294 3087071 := bstep (se 1 (by rfl) ⟨2315303, by rfl⟩ : syracuseStep 3087071 = 4630607) B4630607
theorem B5790455 : Blo 607294 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B8788733 : Blo 607294 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B2055023 : Blo 607294 2055023 := bstep (se 1 (by rfl) ⟨1541267, by rfl⟩ : syracuseStep 2055023 = 3082535) B3082535
theorem B3119995 : Blo 607294 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B7502777 : Blo 607294 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B3898313 : Blo 607294 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B2055131 : Blo 607294 2055131 := bstep (se 1 (by rfl) ⟨1541348, by rfl⟩ : syracuseStep 2055131 = 3082697) B3082697
theorem B2464793 : Blo 607294 2464793 := bstep (se 2 (by rfl) ⟨924297, by rfl⟩ : syracuseStep 2464793 = 1848595) B1848595
theorem B769115 : Blo 607294 769115 := bstep (se 1 (by rfl) ⟨576836, by rfl⟩ : syracuseStep 769115 = 1153673) B1153673
theorem B7019723 : Blo 607294 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B5274839 : Blo 607294 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B2055401 : Blo 607294 2055401 := bstep (se 2 (by rfl) ⟨770775, by rfl⟩ : syracuseStep 2055401 = 1541551) B1541551
theorem B7413059 : Blo 607294 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B2194877 : Blo 607294 2194877 := bstep (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) B823079
theorem B2055671 : Blo 607294 2055671 := bstep (se 1 (by rfl) ⟨1541753, by rfl⟩ : syracuseStep 2055671 = 3083507) B3083507
theorem B1465847 : Blo 607294 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B5875361 : Blo 607294 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B4931207 : Blo 607294 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B11116385 : Blo 607294 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B1367963 : Blo 607294 1367963 := bstep (se 1 (by rfl) ⟨1025972, by rfl⟩ : syracuseStep 1367963 = 2051945) B2051945
theorem B1302427 : Blo 607294 1302427 := bstep (se 1 (by rfl) ⟨976820, by rfl⟩ : syracuseStep 1302427 = 1953641) B1953641
theorem B252731339 : Blo 607294 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B2924552213 : Blo 607294 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B1736957 : Blo 607294 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B3711257 : Blo 607294 3711257 := bstep (se 2 (by rfl) ⟨1391721, by rfl⟩ : syracuseStep 3711257 = 2783443) B2783443
theorem B1368359 : Blo 607294 1368359 := bstep (se 1 (by rfl) ⟨1026269, by rfl⟩ : syracuseStep 1368359 = 2052539) B2052539
theorem B2818567 : Blo 607294 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B14066237 : Blo 607294 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B1368719 : Blo 607294 1368719 := bstep (se 1 (by rfl) ⟨1026539, by rfl⟩ : syracuseStep 1368719 = 2053079) B2053079
theorem B1368737 : Blo 607294 1368737 := bstep (se 2 (by rfl) ⟨513276, by rfl⟩ : syracuseStep 1368737 = 1026553) B1026553
theorem B1368809 : Blo 607294 1368809 := bstep (se 2 (by rfl) ⟨513303, by rfl⟩ : syracuseStep 1368809 = 1026607) B1026607
theorem B2056967 : Blo 607294 2056967 := bstep (se 1 (by rfl) ⟨1542725, by rfl⟩ : syracuseStep 2056967 = 3085451) B3085451
theorem B10674953 : Blo 607294 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B19768157 : Blo 607294 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B3089339 : Blo 607294 3089339 := bstep (se 1 (by rfl) ⟨2317004, by rfl⟩ : syracuseStep 3089339 = 4634009) B4634009
theorem B1024967 : Blo 607294 1024967 := bstep (se 1 (by rfl) ⟨768725, by rfl⟩ : syracuseStep 1024967 = 1537451) B1537451
theorem B1369097 : Blo 607294 1369097 := bstep (se 2 (by rfl) ⟨513411, by rfl⟩ : syracuseStep 1369097 = 1026823) B1026823
theorem B3916907 : Blo 607294 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B24970463 : Blo 607294 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B1754399 : Blo 607294 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B1369385 : Blo 607294 1369385 := bstep (se 2 (by rfl) ⟨513519, by rfl⟩ : syracuseStep 1369385 = 1027039) B1027039
theorem B607551 : Blo 607294 607551 := bstep (se 1 (by rfl) ⟨455663, by rfl⟩ : syracuseStep 607551 = 911327) B911327
theorem B607559 : Blo 607294 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B3081563 : Blo 607294 3081563 := bstep (se 1 (by rfl) ⟨2311172, by rfl⟩ : syracuseStep 3081563 = 4622345) B4622345
theorem B1951067 : Blo 607294 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B607591 : Blo 607294 607591 := bstep (se 1 (by rfl) ⟨455693, by rfl⟩ : syracuseStep 607591 = 911387) B911387
theorem B977231 : Blo 607294 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B2196983 : Blo 607294 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B1369655 : Blo 607294 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B3475007 : Blo 607294 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B607835 : Blo 607294 607835 := bstep (se 1 (by rfl) ⟨455876, by rfl⟩ : syracuseStep 607835 = 911753) B911753
theorem B910955 : Blo 607294 910955 := bstep (se 1 (by rfl) ⟨683216, by rfl⟩ : syracuseStep 910955 = 1366433) B1366433
theorem B911003 : Blo 607294 911003 := bstep (se 1 (by rfl) ⟨683252, by rfl⟩ : syracuseStep 911003 = 1366505) B1366505
theorem B2598635 : Blo 607294 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B2058047 : Blo 607294 2058047 := bstep (se 1 (by rfl) ⟨1543535, by rfl⟩ : syracuseStep 2058047 = 3087071) B3087071
theorem B3860303 : Blo 607294 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B911225 : Blo 607294 911225 := bstep (se 2 (by rfl) ⟨341709, by rfl⟩ : syracuseStep 911225 = 683419) B683419
theorem B3475325 : Blo 607294 3475325 := bstep (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) B1303247
theorem B1370015 : Blo 607294 1370015 := bstep (se 1 (by rfl) ⟨1027511, by rfl⟩ : syracuseStep 1370015 = 2055023) B2055023
theorem B13158359 : Blo 607294 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B2598875 : Blo 607294 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B1370087 : Blo 607294 1370087 := bstep (se 1 (by rfl) ⟨1027565, by rfl⟩ : syracuseStep 1370087 = 2055131) B2055131
theorem B7391263 : Blo 607294 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B4679815 : Blo 607294 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B1370267 : Blo 607294 1370267 := bstep (se 1 (by rfl) ⟨1027700, by rfl⟩ : syracuseStep 1370267 = 2055401) B2055401
theorem B608463 : Blo 607294 608463 := bstep (se 1 (by rfl) ⟨456347, by rfl⟩ : syracuseStep 608463 = 912695) B912695
theorem B608575 : Blo 607294 608575 := bstep (se 1 (by rfl) ⟨456431, by rfl⟩ : syracuseStep 608575 = 912863) B912863
theorem B1370447 : Blo 607294 1370447 := bstep (se 1 (by rfl) ⟨1027835, by rfl⟩ : syracuseStep 1370447 = 2055671) B2055671
theorem B1370537 : Blo 607294 1370537 := bstep (se 2 (by rfl) ⟨513951, by rfl⟩ : syracuseStep 1370537 = 1027903) B1027903
theorem B3287471 : Blo 607294 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B608719 : Blo 607294 608719 := bstep (se 1 (by rfl) ⟨456539, by rfl⟩ : syracuseStep 608719 = 913079) B913079
theorem B608859 : Blo 607294 608859 := bstep (se 1 (by rfl) ⟨456644, by rfl⟩ : syracuseStep 608859 = 913289) B913289
theorem B911975 : Blo 607294 911975 := bstep (se 1 (by rfl) ⟨683981, by rfl⟩ : syracuseStep 911975 = 1367963) B1367963
theorem B168487559 : Blo 607294 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B609023 : Blo 607294 609023 := bstep (se 1 (by rfl) ⟨456767, by rfl⟩ : syracuseStep 609023 = 913535) B913535
theorem B1542959 : Blo 607294 1542959 := bstep (se 1 (by rfl) ⟨1157219, by rfl⟩ : syracuseStep 1542959 = 2314439) B2314439
theorem B912251 : Blo 607294 912251 := bstep (se 1 (by rfl) ⟨684188, by rfl⟩ : syracuseStep 912251 = 1368377) B1368377
theorem B2050973 : Blo 607294 2050973 := bstep (se 3 (by rfl) ⟨384557, by rfl⟩ : syracuseStep 2050973 = 769115) B769115
theorem B1158047 : Blo 607294 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1026985 : Blo 607294 1026985 := bstep (se 2 (by rfl) ⟨385119, by rfl⟩ : syracuseStep 1026985 = 770239) B770239
theorem B2640809 : Blo 607294 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B2051135 : Blo 607294 2051135 := bstep (se 1 (by rfl) ⟨1538351, by rfl⟩ : syracuseStep 2051135 = 3076703) B3076703
theorem B912521 : Blo 607294 912521 := bstep (se 2 (by rfl) ⟨342195, by rfl⟩ : syracuseStep 912521 = 684391) B684391
theorem B609447 : Blo 607294 609447 := bstep (se 1 (by rfl) ⟨457085, by rfl⟩ : syracuseStep 609447 = 914171) B914171
theorem B912575 : Blo 607294 912575 := bstep (se 1 (by rfl) ⟨684431, by rfl⟩ : syracuseStep 912575 = 1368863) B1368863
theorem B1641725 : Blo 607294 1641725 := bstep (se 3 (by rfl) ⟨307823, by rfl⟩ : syracuseStep 1641725 = 615647) B615647
theorem B2600275 : Blo 607294 2600275 := bstep (se 1 (by rfl) ⟨1950206, by rfl⟩ : syracuseStep 2600275 = 3900413) B3900413
theorem B6761861 : Blo 607294 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B3173807 : Blo 607294 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B609743 : Blo 607294 609743 := bstep (se 1 (by rfl) ⟨457307, by rfl⟩ : syracuseStep 609743 = 914615) B914615
theorem B3214829 : Blo 607294 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B7810667 : Blo 607294 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B609903 : Blo 607294 609903 := bstep (se 1 (by rfl) ⟨457427, by rfl⟩ : syracuseStep 609903 = 914855) B914855
theorem B1027775 : Blo 607294 1027775 := bstep (se 1 (by rfl) ⟨770831, by rfl⟩ : syracuseStep 1027775 = 1541663) B1541663
theorem B913115 : Blo 607294 913115 := bstep (se 1 (by rfl) ⟨684836, by rfl⟩ : syracuseStep 913115 = 1369673) B1369673
theorem B610023 : Blo 607294 610023 := bstep (se 1 (by rfl) ⟨457517, by rfl⟩ : syracuseStep 610023 = 915035) B915035
theorem B1543931 : Blo 607294 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B5853005 : Blo 607294 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B5859155 : Blo 607294 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B913385 : Blo 607294 913385 := bstep (se 2 (by rfl) ⟨342519, by rfl⟩ : syracuseStep 913385 = 685039) B685039
theorem B913403 : Blo 607294 913403 := bstep (se 1 (by rfl) ⟨685052, by rfl⟩ : syracuseStep 913403 = 1370105) B1370105
theorem B913439 : Blo 607294 913439 := bstep (se 1 (by rfl) ⟨685079, by rfl⟩ : syracuseStep 913439 = 1370159) B1370159
theorem B4739111 : Blo 607294 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B913463 : Blo 607294 913463 := bstep (se 1 (by rfl) ⟨685097, by rfl⟩ : syracuseStep 913463 = 1370195) B1370195
theorem B913583 : Blo 607294 913583 := bstep (se 1 (by rfl) ⟨685187, by rfl⟩ : syracuseStep 913583 = 1370375) B1370375
theorem B1732823 : Blo 607294 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B1544417 : Blo 607294 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B13136215 : Blo 607294 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B913787 : Blo 607294 913787 := bstep (se 1 (by rfl) ⟨685340, by rfl⟩ : syracuseStep 913787 = 1370681) B1370681
theorem B2306465 : Blo 607294 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B21074377 : Blo 607294 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B5001851 : Blo 607294 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B914057 : Blo 607294 914057 := bstep (se 2 (by rfl) ⟨342771, by rfl⟩ : syracuseStep 914057 = 685543) B685543
theorem B1643195 : Blo 607294 1643195 := bstep (se 1 (by rfl) ⟨1232396, by rfl⟩ : syracuseStep 1643195 = 2464793) B2464793
theorem B13177565 : Blo 607294 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B7918397 : Blo 607294 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B914267 : Blo 607294 914267 := bstep (se 1 (by rfl) ⟨685700, by rfl⟩ : syracuseStep 914267 = 1371401) B1371401
theorem B914297 : Blo 607294 914297 := bstep (se 2 (by rfl) ⟨342861, by rfl⟩ : syracuseStep 914297 = 685723) B685723
theorem B41718833 : Blo 607294 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B6255755 : Blo 607294 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B7410923 : Blo 607294 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B1029503 : Blo 607294 1029503 := bstep (se 1 (by rfl) ⟨772127, by rfl⟩ : syracuseStep 1029503 = 1544255) B1544255
theorem B2594177 : Blo 607294 2594177 := bstep (se 2 (by rfl) ⟨972816, by rfl⟩ : syracuseStep 2594177 = 1945633) B1945633
theorem B18044315 : Blo 607294 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B914927 : Blo 607294 914927 := bstep (se 1 (by rfl) ⟨686195, by rfl⟩ : syracuseStep 914927 = 1372391) B1372391
theorem B6919667 : Blo 607294 6919667 := bstep (se 1 (by rfl) ⟨5189750, by rfl⟩ : syracuseStep 6919667 = 10379501) B10379501
theorem B865819 : Blo 607294 865819 := bstep (se 1 (by rfl) ⟨649364, by rfl⟩ : syracuseStep 865819 = 1298729) B1298729
theorem B915047 : Blo 607294 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B4929133 : Blo 607294 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B1537775 : Blo 607294 1537775 := bstep (se 1 (by rfl) ⟨1153331, by rfl⟩ : syracuseStep 1537775 = 2306663) B2306663
theorem B7124753 : Blo 607294 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B2225951 : Blo 607294 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B2922311 : Blo 607294 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B2930539 : Blo 607294 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B686047 : Blo 607294 686047 := bstep (se 1 (by rfl) ⟨514535, by rfl⟩ : syracuseStep 686047 = 1029071) B1029071
theorem B21108737 : Blo 607294 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B2308121 : Blo 607294 2308121 := bstep (se 2 (by rfl) ⟨865545, by rfl⟩ : syracuseStep 2308121 = 1731091) B1731091
theorem B2472059 : Blo 607294 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B7403723 : Blo 607294 7403723 := bstep (se 1 (by rfl) ⟨5552792, by rfl⟩ : syracuseStep 7403723 = 11105585) B11105585
theorem B4626719 : Blo 607294 4626719 := bstep (se 1 (by rfl) ⟨3470039, by rfl⟩ : syracuseStep 4626719 = 6940079) B6940079
theorem B2922911 : Blo 607294 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B1735111 : Blo 607294 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B4159993 : Blo 607294 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B1735339 : Blo 607294 1735339 := bstep (se 1 (by rfl) ⟨1301504, by rfl⟩ : syracuseStep 1735339 = 2603009) B2603009
theorem B5012231 : Blo 607294 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B2054969 : Blo 607294 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B1735613 : Blo 607294 1735613 := bstep (se 3 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 1735613 = 650855) B650855
theorem B7789547 : Blo 607294 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B2595833 : Blo 607294 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B1039451 : Blo 607294 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B1367369 : Blo 607294 1367369 := bstep (se 2 (by rfl) ⟨512763, by rfl⟩ : syracuseStep 1367369 = 1025527) B1025527
theorem B1367387 : Blo 607294 1367387 := bstep (se 1 (by rfl) ⟨1025540, by rfl⟩ : syracuseStep 1367387 = 2051081) B2051081
theorem B3088043 : Blo 607294 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B3284833 : Blo 607294 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B1736569 : Blo 607294 1736569 := bstep (se 2 (by rfl) ⟨651213, by rfl⟩ : syracuseStep 1736569 = 1302427) B1302427
theorem B2056103 : Blo 607294 2056103 := bstep (se 1 (by rfl) ⟨1542077, by rfl⟩ : syracuseStep 2056103 = 3084155) B3084155
theorem B2596859 : Blo 607294 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B9855017 : Blo 607294 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B1155215 : Blo 607294 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B2474171 : Blo 607294 2474171 := bstep (se 1 (by rfl) ⟨1855628, by rfl⟩ : syracuseStep 2474171 = 3711257) B3711257
theorem B3334567 : Blo 607294 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B17514953 : Blo 607294 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B28099169 : Blo 607294 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B5546657 : Blo 607294 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B27812555 : Blo 607294 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B4678397 : Blo 607294 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B4170503 : Blo 607294 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B16646975 : Blo 607294 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B4940615 : Blo 607294 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B1729451 : Blo 607294 1729451 := bstep (se 1 (by rfl) ⟨1297088, by rfl⟩ : syracuseStep 1729451 = 2594177) B2594177
theorem B4613111 : Blo 607294 4613111 := bstep (se 1 (by rfl) ⟨3459833, by rfl⟩ : syracuseStep 4613111 = 6919667) B6919667
theorem B607303 : Blo 607294 607303 := bstep (se 1 (by rfl) ⟨455477, by rfl⟩ : syracuseStep 607303 = 910955) B910955
theorem B607335 : Blo 607294 607335 := bstep (se 1 (by rfl) ⟨455501, by rfl⟩ : syracuseStep 607335 = 911003) B911003
theorem B8766589 : Blo 607294 8766589 := bstep (se 3 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 8766589 = 3287471) B3287471
theorem B8463485 : Blo 607294 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B1025183 : Blo 607294 1025183 := bstep (se 1 (by rfl) ⟨768887, by rfl⟩ : syracuseStep 1025183 = 1537775) B1537775
theorem B1483967 : Blo 607294 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B1369313 : Blo 607294 1369313 := bstep (se 2 (by rfl) ⟨513492, by rfl⟩ : syracuseStep 1369313 = 1026985) B1026985
theorem B607483 : Blo 607294 607483 := bstep (se 1 (by rfl) ⟨455612, by rfl⟩ : syracuseStep 607483 = 911225) B911225
theorem B1648039 : Blo 607294 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B607983 : Blo 607294 607983 := bstep (se 1 (by rfl) ⟨455987, by rfl⟩ : syracuseStep 607983 = 911975) B911975
theorem B3467033 : Blo 607294 3467033 := bstep (se 2 (by rfl) ⟨1300137, by rfl⟩ : syracuseStep 3467033 = 2600275) B2600275
theorem B1369979 : Blo 607294 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B608167 : Blo 607294 608167 := bstep (se 1 (by rfl) ⟨456125, by rfl⟩ : syracuseStep 608167 = 912251) B912251
theorem B772031 : Blo 607294 772031 := bstep (se 1 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 772031 = 1158047) B1158047
theorem B1157075 : Blo 607294 1157075 := bstep (se 1 (by rfl) ⟨867806, by rfl⟩ : syracuseStep 1157075 = 1735613) B1735613
theorem B1730555 : Blo 607294 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B18999341 : Blo 607294 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B608347 : Blo 607294 608347 := bstep (se 1 (by rfl) ⟨456260, by rfl⟩ : syracuseStep 608347 = 912521) B912521
theorem B608383 : Blo 607294 608383 := bstep (se 1 (by rfl) ⟨456287, by rfl⟩ : syracuseStep 608383 = 912575) B912575
theorem B6572177 : Blo 607294 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B911579 : Blo 607294 911579 := bstep (se 1 (by rfl) ⟨683684, by rfl⟩ : syracuseStep 911579 = 1367369) B1367369
theorem B911591 : Blo 607294 911591 := bstep (se 1 (by rfl) ⟨683693, by rfl⟩ : syracuseStep 911591 = 1367387) B1367387
theorem B4507907 : Blo 607294 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B2058695 : Blo 607294 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B608743 : Blo 607294 608743 := bstep (se 1 (by rfl) ⟨456557, by rfl⟩ : syracuseStep 608743 = 913115) B913115
theorem B3902003 : Blo 607294 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B1370735 : Blo 607294 1370735 := bstep (se 1 (by rfl) ⟨1028051, by rfl⟩ : syracuseStep 1370735 = 2056103) B2056103
theorem B608923 : Blo 607294 608923 := bstep (se 1 (by rfl) ⟨456692, by rfl⟩ : syracuseStep 608923 = 913385) B913385
theorem B1731239 : Blo 607294 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B608935 : Blo 607294 608935 := bstep (se 1 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 608935 = 913403) B913403
theorem B608959 : Blo 607294 608959 := bstep (se 1 (by rfl) ⟨456719, by rfl⟩ : syracuseStep 608959 = 913439) B913439
theorem B608975 : Blo 607294 608975 := bstep (se 1 (by rfl) ⟨456731, by rfl⟩ : syracuseStep 608975 = 913463) B913463
theorem B53463797 : Blo 607294 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B609055 : Blo 607294 609055 := bstep (se 1 (by rfl) ⟨456791, by rfl⟩ : syracuseStep 609055 = 913583) B913583
theorem B1157971 : Blo 607294 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B912239 : Blo 607294 912239 := bstep (se 1 (by rfl) ⟨684179, by rfl⟩ : syracuseStep 912239 = 1368359) B1368359
theorem B2771869 : Blo 607294 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B609191 : Blo 607294 609191 := bstep (se 1 (by rfl) ⟨456893, by rfl⟩ : syracuseStep 609191 = 913787) B913787
theorem B609371 : Blo 607294 609371 := bstep (se 1 (by rfl) ⟨457028, by rfl⟩ : syracuseStep 609371 = 914057) B914057
theorem B912479 : Blo 607294 912479 := bstep (se 1 (by rfl) ⟨684359, by rfl⟩ : syracuseStep 912479 = 1368719) B1368719
theorem B912491 : Blo 607294 912491 := bstep (se 1 (by rfl) ⟨684368, by rfl⟩ : syracuseStep 912491 = 1368737) B1368737
theorem B8785043 : Blo 607294 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B912539 : Blo 607294 912539 := bstep (se 1 (by rfl) ⟨684404, by rfl⟩ : syracuseStep 912539 = 1368809) B1368809
theorem B1371311 : Blo 607294 1371311 := bstep (se 1 (by rfl) ⟨1028483, by rfl⟩ : syracuseStep 1371311 = 2056967) B2056967
theorem B5278931 : Blo 607294 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B609511 : Blo 607294 609511 := bstep (se 1 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 609511 = 914267) B914267
theorem B609531 : Blo 607294 609531 := bstep (se 1 (by rfl) ⟨457148, by rfl⟩ : syracuseStep 609531 = 914297) B914297
theorem B2313481 : Blo 607294 2313481 := bstep (se 2 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 2313481 = 1735111) B1735111
theorem B683311 : Blo 607294 683311 := bstep (se 1 (by rfl) ⟨512483, by rfl⟩ : syracuseStep 683311 = 1024967) B1024967
theorem B912731 : Blo 607294 912731 := bstep (se 1 (by rfl) ⟨684548, by rfl⟩ : syracuseStep 912731 = 1369097) B1369097
theorem B912923 : Blo 607294 912923 := bstep (se 1 (by rfl) ⟨684692, by rfl⟩ : syracuseStep 912923 = 1369385) B1369385
theorem B2313785 : Blo 607294 2313785 := bstep (se 2 (by rfl) ⟨867669, by rfl⟩ : syracuseStep 2313785 = 1735339) B1735339
theorem B12029543 : Blo 607294 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B609951 : Blo 607294 609951 := bstep (se 1 (by rfl) ⟨457463, by rfl⟩ : syracuseStep 609951 = 914927) B914927
theorem B913103 : Blo 607294 913103 := bstep (se 1 (by rfl) ⟨684827, by rfl⟩ : syracuseStep 913103 = 1369655) B1369655
theorem B610031 : Blo 607294 610031 := bstep (se 1 (by rfl) ⟨457523, by rfl⟩ : syracuseStep 610031 = 915047) B915047
theorem B1732423 : Blo 607294 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B1372031 : Blo 607294 1372031 := bstep (se 1 (by rfl) ⟨1029023, by rfl⟩ : syracuseStep 1372031 = 2058047) B2058047
theorem B913343 : Blo 607294 913343 := bstep (se 1 (by rfl) ⟨685007, by rfl⟩ : syracuseStep 913343 = 1370015) B1370015
theorem B1732583 : Blo 607294 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B913391 : Blo 607294 913391 := bstep (se 1 (by rfl) ⟨685043, by rfl⟩ : syracuseStep 913391 = 1370087) B1370087
theorem B913511 : Blo 607294 913511 := bstep (se 1 (by rfl) ⟨685133, by rfl⟩ : syracuseStep 913511 = 1370267) B1370267
theorem B4935815 : Blo 607294 4935815 := bstep (se 1 (by rfl) ⟨3701861, by rfl⟩ : syracuseStep 4935815 = 7403723) B7403723
theorem B3084479 : Blo 607294 3084479 := bstep (se 1 (by rfl) ⟨2313359, by rfl⟩ : syracuseStep 3084479 = 4626719) B4626719
theorem B913631 : Blo 607294 913631 := bstep (se 1 (by rfl) ⟨685223, by rfl⟩ : syracuseStep 913631 = 1370447) B1370447
theorem B651487 : Blo 607294 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B913691 : Blo 607294 913691 := bstep (se 1 (by rfl) ⟨685268, by rfl⟩ : syracuseStep 913691 = 1370537) B1370537
theorem B112325039 : Blo 607294 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B1028639 : Blo 607294 1028639 := bstep (se 1 (by rfl) ⟨771479, by rfl⟩ : syracuseStep 1028639 = 1542959) B1542959
theorem B1094483 : Blo 607294 1094483 := bstep (se 1 (by rfl) ⟨820862, by rfl⟩ : syracuseStep 1094483 = 1641725) B1641725
theorem B10294141 : Blo 607294 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B2143219 : Blo 607294 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B5207111 : Blo 607294 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B7042157 : Blo 607294 7042157 := bstep (se 3 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 7042157 = 2640809) B2640809
theorem B685183 : Blo 607294 685183 := bstep (se 1 (by rfl) ⟨513887, by rfl⟩ : syracuseStep 685183 = 1027775) B1027775
theorem B4379777 : Blo 607294 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B2315425 : Blo 607294 2315425 := bstep (se 2 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 2315425 = 1736569) B1736569
theorem B1029287 : Blo 607294 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B914729 : Blo 607294 914729 := bstep (se 2 (by rfl) ⟨343023, by rfl⟩ : syracuseStep 914729 = 686047) B686047
theorem B1949701475 : Blo 607294 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B3159407 : Blo 607294 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1029611 : Blo 607294 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B6239753 : Blo 607294 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B1537643 : Blo 607294 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B9377491 : Blo 607294 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B1095463 : Blo 607294 1095463 := bstep (se 1 (by rfl) ⟨821597, by rfl⟩ : syracuseStep 1095463 = 1643195) B1643195
theorem B7116635 : Blo 607294 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B13178771 : Blo 607294 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B3758089 : Blo 607294 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B2611271 : Blo 607294 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B2054375 : Blo 607294 2054375 := bstep (se 1 (by rfl) ⟨1540781, by rfl⟩ : syracuseStep 2054375 = 3081563) B3081563
theorem B1300711 : Blo 607294 1300711 := bstep (se 1 (by rfl) ⟨975533, by rfl⟩ : syracuseStep 1300711 = 1951067) B1951067
theorem B686335 : Blo 607294 686335 := bstep (se 1 (by rfl) ⟨514751, by rfl⟩ : syracuseStep 686335 = 1029503) B1029503
theorem B1464655 : Blo 607294 1464655 := bstep (se 1 (by rfl) ⟨1098491, by rfl⟩ : syracuseStep 1464655 = 2196983) B2196983
theorem B2316671 : Blo 607294 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B1948207 : Blo 607294 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B3906103 : Blo 607294 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B2316883 : Blo 607294 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B8772239 : Blo 607294 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B14072491 : Blo 607294 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B1538747 : Blo 607294 1538747 := bstep (se 1 (by rfl) ⟨1154060, by rfl⟩ : syracuseStep 1538747 = 2308121) B2308121
theorem B1948607 : Blo 607294 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B1367315 : Blo 607294 1367315 := bstep (se 1 (by rfl) ⟨1025486, by rfl⟩ : syracuseStep 1367315 = 2050973) B2050973
theorem B2059559 : Blo 607294 2059559 := bstep (se 1 (by rfl) ⟨1544669, by rfl⟩ : syracuseStep 2059559 = 3089339) B3089339
theorem B5193031 : Blo 607294 5193031 := bstep (se 1 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 5193031 = 7789547) B7789547
theorem B1154425 : Blo 607294 1154425 := bstep (se 2 (by rfl) ⟨432909, by rfl⟩ : syracuseStep 1154425 = 865819) B865819
theorem B1367423 : Blo 607294 1367423 := bstep (se 1 (by rfl) ⟨1025567, by rfl⟩ : syracuseStep 1367423 = 2051135) B2051135
theorem B3907385 : Blo 607294 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B6570011 : Blo 607294 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B770143 : Blo 607294 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B2056319 : Blo 607294 2056319 := bstep (se 1 (by rfl) ⟨1542239, by rfl⟩ : syracuseStep 2056319 = 3084479) B3084479
theorem B74883359 : Blo 607294 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B868649 : Blo 607294 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B22569293 : Blo 607294 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B3957245 : Blo 607294 3957245 := bstep (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) B1483967
theorem B3293743 : Blo 607294 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B729655 : Blo 607294 729655 := bstep (se 1 (by rfl) ⟨547241, by rfl⟩ : syracuseStep 729655 = 1094483) B1094483
theorem B2597609 : Blo 607294 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B4694771 : Blo 607294 4694771 := bstep (se 1 (by rfl) ⟨3521078, by rfl⟩ : syracuseStep 4694771 = 7042157) B7042157
theorem B3089177 : Blo 607294 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B2106271 : Blo 607294 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B1025095 : Blo 607294 1025095 := bstep (se 1 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 1025095 = 1537643) B1537643
theorem B2311355 : Blo 607294 2311355 := bstep (se 1 (by rfl) ⟨1733516, by rfl⟩ : syracuseStep 2311355 = 3467033) B3467033
theorem B3695825 : Blo 607294 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B4744423 : Blo 607294 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B771383 : Blo 607294 771383 := bstep (se 1 (by rfl) ⟨578537, by rfl⟩ : syracuseStep 771383 = 1157075) B1157075
theorem B12666227 : Blo 607294 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B607719 : Blo 607294 607719 := bstep (se 1 (by rfl) ⟨455789, by rfl⟩ : syracuseStep 607719 = 911579) B911579
theorem B607727 : Blo 607294 607727 := bstep (se 1 (by rfl) ⟨455795, by rfl⟩ : syracuseStep 607727 = 911591) B911591
theorem B1369583 : Blo 607294 1369583 := bstep (se 1 (by rfl) ⟨1027187, by rfl⟩ : syracuseStep 1369583 = 2054375) B2054375
theorem B5842469 : Blo 607294 5842469 := bstep (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) B1095463
theorem B911081 : Blo 607294 911081 := bstep (se 2 (by rfl) ⟨341655, by rfl⟩ : syracuseStep 911081 = 683311) B683311
theorem B6924041 : Blo 607294 6924041 := bstep (se 2 (by rfl) ⟨2596515, by rfl⟩ : syracuseStep 6924041 = 5193031) B5193031
theorem B1025831 : Blo 607294 1025831 := bstep (se 1 (by rfl) ⟨769373, by rfl⟩ : syracuseStep 1025831 = 1538747) B1538747
theorem B2197385 : Blo 607294 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B608159 : Blo 607294 608159 := bstep (se 1 (by rfl) ⟨456119, by rfl⟩ : syracuseStep 608159 = 912239) B912239
theorem B608319 : Blo 607294 608319 := bstep (se 1 (by rfl) ⟨456239, by rfl⟩ : syracuseStep 608319 = 912479) B912479
theorem B608327 : Blo 607294 608327 := bstep (se 1 (by rfl) ⟨456245, by rfl⟩ : syracuseStep 608327 = 912491) B912491
theorem B608359 : Blo 607294 608359 := bstep (se 1 (by rfl) ⟨456269, by rfl⟩ : syracuseStep 608359 = 912539) B912539
theorem B911543 : Blo 607294 911543 := bstep (se 1 (by rfl) ⟨683657, by rfl⟩ : syracuseStep 911543 = 1367315) B1367315
theorem B608487 : Blo 607294 608487 := bstep (se 1 (by rfl) ⟨456365, by rfl⟩ : syracuseStep 608487 = 912731) B912731
theorem B911615 : Blo 607294 911615 := bstep (se 1 (by rfl) ⟨683711, by rfl⟩ : syracuseStep 911615 = 1367423) B1367423
theorem B12503321 : Blo 607294 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B608615 : Blo 607294 608615 := bstep (se 1 (by rfl) ⟨456461, by rfl⟩ : syracuseStep 608615 = 912923) B912923
theorem B1542523 : Blo 607294 1542523 := bstep (se 1 (by rfl) ⟨1156892, by rfl⟩ : syracuseStep 1542523 = 2313785) B2313785
theorem B608735 : Blo 607294 608735 := bstep (se 1 (by rfl) ⟨456551, by rfl⟩ : syracuseStep 608735 = 913103) B913103
theorem B2058749 : Blo 607294 2058749 := bstep (se 3 (by rfl) ⟨386015, by rfl⟩ : syracuseStep 2058749 = 772031) B772031
theorem B608895 : Blo 607294 608895 := bstep (se 1 (by rfl) ⟨456671, by rfl⟩ : syracuseStep 608895 = 913343) B913343
theorem B608927 : Blo 607294 608927 := bstep (se 1 (by rfl) ⟨456695, by rfl⟩ : syracuseStep 608927 = 913391) B913391
theorem B609007 : Blo 607294 609007 := bstep (se 1 (by rfl) ⟨456755, by rfl⟩ : syracuseStep 609007 = 913511) B913511
theorem B1649447 : Blo 607294 1649447 := bstep (se 1 (by rfl) ⟨1237085, by rfl⟩ : syracuseStep 1649447 = 2474171) B2474171
theorem B609087 : Blo 607294 609087 := bstep (se 1 (by rfl) ⟨456815, by rfl⟩ : syracuseStep 609087 = 913631) B913631
theorem B609127 : Blo 607294 609127 := bstep (se 1 (by rfl) ⟨456845, by rfl⟩ : syracuseStep 609127 = 913691) B913691
theorem B11676635 : Blo 607294 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B1952873 : Blo 607294 1952873 := bstep (se 2 (by rfl) ⟨732327, by rfl⟩ : syracuseStep 1952873 = 1464655) B1464655
theorem B18541703 : Blo 607294 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B2780335 : Blo 607294 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B3075407 : Blo 607294 3075407 := bstep (se 1 (by rfl) ⟨2306555, by rfl⟩ : syracuseStep 3075407 = 4613111) B4613111
theorem B12021085 : Blo 607294 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B2919851 : Blo 607294 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B683455 : Blo 607294 683455 := bstep (se 1 (by rfl) ⟨512591, by rfl⟩ : syracuseStep 683455 = 1025183) B1025183
theorem B912875 : Blo 607294 912875 := bstep (se 1 (by rfl) ⟨684656, by rfl⟩ : syracuseStep 912875 = 1369313) B1369313
theorem B609819 : Blo 607294 609819 := bstep (se 1 (by rfl) ⟨457364, by rfl⟩ : syracuseStep 609819 = 914729) B914729
theorem B18763321 : Blo 607294 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B5199203933 : Blo 607294 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B1543961 : Blo 607294 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B13725521 : Blo 607294 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B913319 : Blo 607294 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B8785847 : Blo 607294 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B1740847 : Blo 607294 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B913577 : Blo 607294 913577 := bstep (se 2 (by rfl) ⟨342591, by rfl⟩ : syracuseStep 913577 = 685183) B685183
theorem B1544447 : Blo 607294 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1372463 : Blo 607294 1372463 := bstep (se 1 (by rfl) ⟨1029347, by rfl⟩ : syracuseStep 1372463 = 2058695) B2058695
theorem B3084641 : Blo 607294 3084641 := bstep (se 2 (by rfl) ⟨1156740, by rfl⟩ : syracuseStep 3084641 = 2313481) B2313481
theorem B2601335 : Blo 607294 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B913823 : Blo 607294 913823 := bstep (se 1 (by rfl) ⟨685367, by rfl⟩ : syracuseStep 913823 = 1370735) B1370735
theorem B14791085 : Blo 607294 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B1299071 : Blo 607294 1299071 := bstep (se 1 (by rfl) ⟨974303, by rfl⟩ : syracuseStep 1299071 = 1948607) B1948607
theorem B914207 : Blo 607294 914207 := bstep (se 1 (by rfl) ⟨685655, by rfl⟩ : syracuseStep 914207 = 1371311) B1371311
theorem B3519287 : Blo 607294 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B1373039 : Blo 607294 1373039 := bstep (se 1 (by rfl) ⟨1029779, by rfl⟩ : syracuseStep 1373039 = 2059559) B2059559
theorem B914687 : Blo 607294 914687 := bstep (se 1 (by rfl) ⟨686015, by rfl⟩ : syracuseStep 914687 = 1372031) B1372031
theorem B5010785 : Blo 607294 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B3290543 : Blo 607294 3290543 := bstep (se 1 (by rfl) ⟨2467907, by rfl⟩ : syracuseStep 3290543 = 4935815) B4935815
theorem B1734281 : Blo 607294 1734281 := bstep (se 2 (by rfl) ⟨650355, by rfl⟩ : syracuseStep 1734281 = 1300711) B1300711
theorem B915113 : Blo 607294 915113 := bstep (se 2 (by rfl) ⟨343167, by rfl⟩ : syracuseStep 915113 = 686335) B686335
theorem B685759 : Blo 607294 685759 := bstep (se 1 (by rfl) ⟨514319, by rfl⟩ : syracuseStep 685759 = 1028639) B1028639
theorem B18732779 : Blo 607294 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B3118931 : Blo 607294 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B11097983 : Blo 607294 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B4446089 : Blo 607294 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B1152967 : Blo 607294 1152967 := bstep (se 1 (by rfl) ⟨864725, by rfl⟩ : syracuseStep 1152967 = 1729451) B1729451
theorem B3471407 : Blo 607294 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B5208137 : Blo 607294 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B686191 : Blo 607294 686191 := bstep (se 1 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 686191 = 1029287) B1029287
theorem B686407 : Blo 607294 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B4159835 : Blo 607294 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B2857625 : Blo 607294 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B1153703 : Blo 607294 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B4381451 : Blo 607294 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B11688785 : Blo 607294 11688785 := bstep (se 2 (by rfl) ⟨4383294, by rfl⟩ : syracuseStep 11688785 = 8766589) B8766589
theorem B3087233 : Blo 607294 3087233 := bstep (se 2 (by rfl) ⟨1157712, by rfl⟩ : syracuseStep 3087233 = 2315425) B2315425
theorem B5848159 : Blo 607294 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B1154159 : Blo 607294 1154159 := bstep (se 1 (by rfl) ⟨865619, by rfl⟩ : syracuseStep 1154159 = 1731239) B1731239
theorem B1539233 : Blo 607294 1539233 := bstep (se 2 (by rfl) ⟨577212, by rfl⟩ : syracuseStep 1539233 = 1154425) B1154425
theorem B35642531 : Blo 607294 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B5856695 : Blo 607294 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B8019695 : Blo 607294 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B2309897 : Blo 607294 2309897 := bstep (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) B1732423
theorem B2604923 : Blo 607294 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B1155055 : Blo 607294 1155055 := bstep (se 1 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 1155055 = 1732583) B1732583
theorem B49922239 : Blo 607294 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B2056427 : Blo 607294 2056427 := bstep (se 1 (by rfl) ⟨1542320, by rfl⟩ : syracuseStep 2056427 = 3084641) B3084641
theorem B3891493 : Blo 607294 3891493 := bstep (se 4 (by rfl) ⟨364827, by rfl⟩ : syracuseStep 3891493 = 729655) B729655
theorem B2638163 : Blo 607294 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B3129847 : Blo 607294 3129847 := bstep (se 1 (by rfl) ⟨2347385, by rfl⟩ : syracuseStep 3129847 = 4694771) B4694771
theorem B2056697 : Blo 607294 2056697 := bstep (se 2 (by rfl) ⟨771261, by rfl⟩ : syracuseStep 2056697 = 1542523) B1542523
theorem B9855533 : Blo 607294 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B4391657 : Blo 607294 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B1540903 : Blo 607294 1540903 := bstep (se 1 (by rfl) ⟨1155677, by rfl⟩ : syracuseStep 1540903 = 2311355) B2311355
theorem B2057021 : Blo 607294 2057021 := bstep (se 3 (by rfl) ⟨385691, by rfl⟩ : syracuseStep 2057021 = 771383) B771383
theorem B14828453 : Blo 607294 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B33776605 : Blo 607294 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B1156187 : Blo 607294 1156187 := bstep (se 1 (by rfl) ⟨867140, by rfl⟩ : syracuseStep 1156187 = 1734281) B1734281
theorem B607387 : Blo 607294 607387 := bstep (se 1 (by rfl) ⟨455540, by rfl⟩ : syracuseStep 607387 = 911081) B911081
theorem B607695 : Blo 607294 607695 := bstep (se 1 (by rfl) ⟨455771, by rfl⟩ : syracuseStep 607695 = 911543) B911543
theorem B607743 : Blo 607294 607743 := bstep (se 1 (by rfl) ⟨455807, by rfl⟩ : syracuseStep 607743 = 911615) B911615
theorem B6325897 : Blo 607294 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B7792523 : Blo 607294 7792523 := bstep (se 1 (by rfl) ⟨5844392, by rfl⟩ : syracuseStep 7792523 = 11688785) B11688785
theorem B911273 : Blo 607294 911273 := bstep (se 2 (by rfl) ⟨341727, by rfl⟩ : syracuseStep 911273 = 683455) B683455
theorem B2058155 : Blo 607294 2058155 := bstep (se 1 (by rfl) ⟨1543616, by rfl⟩ : syracuseStep 2058155 = 3087233) B3087233
theorem B7784423 : Blo 607294 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B1026155 : Blo 607294 1026155 := bstep (se 1 (by rfl) ⟨769616, by rfl⟩ : syracuseStep 1026155 = 1539233) B1539233
theorem B2050271 : Blo 607294 2050271 := bstep (se 1 (by rfl) ⟨1537703, by rfl⟩ : syracuseStep 2050271 = 3075407) B3075407
theorem B608583 : Blo 607294 608583 := bstep (se 1 (by rfl) ⟨456437, by rfl⟩ : syracuseStep 608583 = 912875) B912875
theorem B3466135955 : Blo 607294 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B608879 : Blo 607294 608879 := bstep (se 1 (by rfl) ⟨456659, by rfl⟩ : syracuseStep 608879 = 913319) B913319
theorem B2321129 : Blo 607294 2321129 := bstep (se 2 (by rfl) ⟨870423, by rfl⟩ : syracuseStep 2321129 = 1740847) B1740847
theorem B1370879 : Blo 607294 1370879 := bstep (se 1 (by rfl) ⟨1028159, by rfl⟩ : syracuseStep 1370879 = 2056319) B2056319
theorem B609051 : Blo 607294 609051 := bstep (se 1 (by rfl) ⟨456788, by rfl⟩ : syracuseStep 609051 = 913577) B913577
theorem B1026857 : Blo 607294 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B1099631 : Blo 607294 1099631 := bstep (se 1 (by rfl) ⟨824723, by rfl⟩ : syracuseStep 1099631 = 1649447) B1649447
theorem B609215 : Blo 607294 609215 := bstep (se 1 (by rfl) ⟨456911, by rfl⟩ : syracuseStep 609215 = 913823) B913823
theorem B2059451 : Blo 607294 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B609471 : Blo 607294 609471 := bstep (se 1 (by rfl) ⟨457103, by rfl⟩ : syracuseStep 609471 = 914207) B914207
theorem B2346191 : Blo 607294 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B609791 : Blo 607294 609791 := bstep (se 1 (by rfl) ⟨457343, by rfl⟩ : syracuseStep 609791 = 914687) B914687
theorem B913055 : Blo 607294 913055 := bstep (se 1 (by rfl) ⟨684791, by rfl⟩ : syracuseStep 913055 = 1369583) B1369583
theorem B3894979 : Blo 607294 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B610075 : Blo 607294 610075 := bstep (se 1 (by rfl) ⟨457556, by rfl⟩ : syracuseStep 610075 = 915113) B915113
theorem B12488519 : Blo 607294 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B4616027 : Blo 607294 4616027 := bstep (se 1 (by rfl) ⟨3462020, by rfl⟩ : syracuseStep 4616027 = 6924041) B6924041
theorem B683887 : Blo 607294 683887 := bstep (se 1 (by rfl) ⟨512915, by rfl⟩ : syracuseStep 683887 = 1025831) B1025831
theorem B2314271 : Blo 607294 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B8335547 : Blo 607294 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B2773223 : Blo 607294 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B1372499 : Blo 607294 1372499 := bstep (se 1 (by rfl) ⟨1029374, by rfl⟩ : syracuseStep 1372499 = 2058749) B2058749
theorem B1905083 : Blo 607294 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B3076541 : Blo 607294 3076541 := bstep (se 3 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 3076541 = 1153703) B1153703
theorem B16028113 : Blo 607294 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B2920967 : Blo 607294 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B6926957 : Blo 607294 6926957 := bstep (se 3 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 6926957 = 2597609) B2597609
theorem B21385853 : Blo 607294 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B23761687 : Blo 607294 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B914345 : Blo 607294 914345 := bstep (se 2 (by rfl) ⟨342879, by rfl⟩ : syracuseStep 914345 = 685759) B685759
theorem B1946567 : Blo 607294 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B3904463 : Blo 607294 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B29594621 : Blo 607294 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B1029307 : Blo 607294 1029307 := bstep (se 1 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 1029307 = 1543961) B1543961
theorem B1537289 : Blo 607294 1537289 := bstep (se 2 (by rfl) ⟨576483, by rfl⟩ : syracuseStep 1537289 = 1152967) B1152967
theorem B4380007 : Blo 607294 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B914921 : Blo 607294 914921 := bstep (se 2 (by rfl) ⟨343095, by rfl⟩ : syracuseStep 914921 = 686191) B686191
theorem B1029631 : Blo 607294 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B914975 : Blo 607294 914975 := bstep (se 1 (by rfl) ⟨686231, by rfl⟩ : syracuseStep 914975 = 1372463) B1372463
theorem B15046195 : Blo 607294 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B1734223 : Blo 607294 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B9860723 : Blo 607294 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B866047 : Blo 607294 866047 := bstep (se 1 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 866047 = 1299071) B1299071
theorem B915209 : Blo 607294 915209 := bstep (se 2 (by rfl) ⟨343203, by rfl⟩ : syracuseStep 915209 = 686407) B686407
theorem B915359 : Blo 607294 915359 := bstep (se 1 (by rfl) ⟨686519, by rfl⟩ : syracuseStep 915359 = 1373039) B1373039
theorem B2316397 : Blo 607294 2316397 := bstep (se 3 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 2316397 = 868649) B868649
theorem B3340523 : Blo 607294 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B2193695 : Blo 607294 2193695 := bstep (se 1 (by rfl) ⟨1645271, by rfl⟩ : syracuseStep 2193695 = 3290543) B3290543
theorem B2808361 : Blo 607294 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B2079287 : Blo 607294 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B2964059 : Blo 607294 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1464923 : Blo 607294 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B3472091 : Blo 607294 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B1366793 : Blo 607294 1366793 := bstep (se 2 (by rfl) ⟨512547, by rfl⟩ : syracuseStep 1366793 = 1025095) B1025095
theorem B7797545 : Blo 607294 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B1301915 : Blo 607294 1301915 := bstep (se 1 (by rfl) ⟨976436, by rfl⟩ : syracuseStep 1301915 = 1952873) B1952873
theorem B769439 : Blo 607294 769439 := bstep (se 1 (by rfl) ⟨577079, by rfl⟩ : syracuseStep 769439 = 1154159) B1154159
theorem B25017761 : Blo 607294 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B12361135 : Blo 607294 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B1539931 : Blo 607294 1539931 := bstep (se 1 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 1539931 = 2309897) B2309897
theorem B9150347 : Blo 607294 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B1736615 : Blo 607294 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B5857231 : Blo 607294 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B1540073 : Blo 607294 1540073 := bstep (se 2 (by rfl) ⟨577527, by rfl⟩ : syracuseStep 1540073 = 1155055) B1155055
theorem B3088529 : Blo 607294 3088529 := bstep (se 2 (by rfl) ⟨1158198, by rfl⟩ : syracuseStep 3088529 = 2316397) B2316397
theorem B1270055 : Blo 607294 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B3744481 : Blo 607294 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B770791 : Blo 607294 770791 := bstep (se 1 (by rfl) ⟨578093, by rfl⟩ : syracuseStep 770791 = 1156187) B1156187
theorem B1024859 : Blo 607294 1024859 := bstep (se 1 (by rfl) ⟨768644, by rfl⟩ : syracuseStep 1024859 = 1537289) B1537289
theorem B5195015 : Blo 607294 5195015 := bstep (se 1 (by rfl) ⟨3896261, by rfl⟩ : syracuseStep 5195015 = 7792523) B7792523
theorem B607515 : Blo 607294 607515 := bstep (se 1 (by rfl) ⟨455636, by rfl⟩ : syracuseStep 607515 = 911273) B911273
theorem B26281421 : Blo 607294 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B1386191 : Blo 607294 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B1976039 : Blo 607294 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B911195 : Blo 607294 911195 := bstep (se 1 (by rfl) ⟨683396, by rfl⟩ : syracuseStep 911195 = 1366793) B1366793
theorem B2312297 : Blo 607294 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B733087 : Blo 607294 733087 := bstep (se 1 (by rfl) ⟨549815, by rfl⟩ : syracuseStep 733087 = 1099631) B1099631
theorem B608703 : Blo 607294 608703 := bstep (se 1 (by rfl) ⟨456527, by rfl⟩ : syracuseStep 608703 = 913055) B913055
theorem B911849 : Blo 607294 911849 := bstep (se 2 (by rfl) ⟨341943, by rfl⟩ : syracuseStep 911849 = 683887) B683887
theorem B8325679 : Blo 607294 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B7809641 : Blo 607294 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B1157743 : Blo 607294 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B1026715 : Blo 607294 1026715 := bstep (se 1 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 1026715 = 1540073) B1540073
theorem B1542847 : Blo 607294 1542847 := bstep (se 1 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 1542847 = 2314271) B2314271
theorem B5557031 : Blo 607294 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B1370951 : Blo 607294 1370951 := bstep (se 1 (by rfl) ⟨1028213, by rfl⟩ : syracuseStep 1370951 = 2056427) B2056427
theorem B66562985 : Blo 607294 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B2051027 : Blo 607294 2051027 := bstep (se 1 (by rfl) ⟨1538270, by rfl⟩ : syracuseStep 2051027 = 3076541) B3076541
theorem B1371131 : Blo 607294 1371131 := bstep (se 1 (by rfl) ⟨1028348, by rfl⟩ : syracuseStep 1371131 = 2056697) B2056697
theorem B5188657 : Blo 607294 5188657 := bstep (se 2 (by rfl) ⟨1945746, by rfl⟩ : syracuseStep 5188657 = 3891493) B3891493
theorem B14257235 : Blo 607294 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B2927771 : Blo 607294 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B1371347 : Blo 607294 1371347 := bstep (se 1 (by rfl) ⟨1028510, by rfl⟩ : syracuseStep 1371347 = 2057021) B2057021
theorem B609563 : Blo 607294 609563 := bstep (se 1 (by rfl) ⟨457172, by rfl⟩ : syracuseStep 609563 = 914345) B914345
theorem B8908061 : Blo 607294 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B1297711 : Blo 607294 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B19729747 : Blo 607294 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B609947 : Blo 607294 609947 := bstep (se 1 (by rfl) ⟨457460, by rfl⟩ : syracuseStep 609947 = 914921) B914921
theorem B609983 : Blo 607294 609983 := bstep (se 1 (by rfl) ⟨457487, by rfl⟩ : syracuseStep 609983 = 914975) B914975
theorem B31682249 : Blo 607294 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B6573815 : Blo 607294 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B2051837 : Blo 607294 2051837 := bstep (se 3 (by rfl) ⟨384719, by rfl⟩ : syracuseStep 2051837 = 769439) B769439
theorem B610139 : Blo 607294 610139 := bstep (se 1 (by rfl) ⟨457604, by rfl⟩ : syracuseStep 610139 = 915209) B915209
theorem B610239 : Blo 607294 610239 := bstep (se 1 (by rfl) ⟨457679, by rfl⟩ : syracuseStep 610239 = 915359) B915359
theorem B1372103 : Blo 607294 1372103 := bstep (se 1 (by rfl) ⟨1029077, by rfl⟩ : syracuseStep 1372103 = 2058155) B2058155
theorem B5189615 : Blo 607294 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B684103 : Blo 607294 684103 := bstep (se 1 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 684103 = 1026155) B1026155
theorem B1462463 : Blo 607294 1462463 := bstep (se 1 (by rfl) ⟨1096847, by rfl⟩ : syracuseStep 1462463 = 2193695) B2193695
theorem B1372409 : Blo 607294 1372409 := bstep (se 2 (by rfl) ⟨514653, by rfl⟩ : syracuseStep 1372409 = 1029307) B1029307
theorem B2314727 : Blo 607294 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B913919 : Blo 607294 913919 := bstep (se 1 (by rfl) ⟨685439, by rfl⟩ : syracuseStep 913919 = 1370879) B1370879
theorem B5198363 : Blo 607294 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B684571 : Blo 607294 684571 := bstep (se 1 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 684571 = 1026857) B1026857
theorem B1372841 : Blo 607294 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B1372967 : Blo 607294 1372967 := bstep (se 1 (by rfl) ⟨1029725, by rfl⟩ : syracuseStep 1372967 = 2059451) B2059451
theorem B8434529 : Blo 607294 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B24400925 : Blo 607294 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B2053241 : Blo 607294 2053241 := bstep (se 2 (by rfl) ⟨769965, by rfl⟩ : syracuseStep 2053241 = 1539931) B1539931
theorem B3077351 : Blo 607294 3077351 := bstep (se 1 (by rfl) ⟨2308013, by rfl⟩ : syracuseStep 3077351 = 4616027) B4616027
theorem B16692517 : Blo 607294 16692517 := bstep (se 4 (by rfl) ⟨1564923, by rfl⟩ : syracuseStep 16692517 = 3129847) B3129847
theorem B1848815 : Blo 607294 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B1758775 : Blo 607294 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B914999 : Blo 607294 914999 := bstep (se 1 (by rfl) ⟨686249, by rfl⟩ : syracuseStep 914999 = 1372499) B1372499
theorem B1947311 : Blo 607294 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B4617971 : Blo 607294 4617971 := bstep (se 1 (by rfl) ⟨3463478, by rfl⟩ : syracuseStep 4617971 = 6926957) B6926957
theorem B21370817 : Blo 607294 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B9885635 : Blo 607294 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B2602975 : Blo 607294 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B2054537 : Blo 607294 2054537 := bstep (se 2 (by rfl) ⟨770451, by rfl⟩ : syracuseStep 2054537 = 1540903) B1540903
theorem B1366847 : Blo 607294 1366847 := bstep (se 1 (by rfl) ⟨1025135, by rfl⟩ : syracuseStep 1366847 = 2050271) B2050271
theorem B3906461 : Blo 607294 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B2310757303 : Blo 607294 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B5840009 : Blo 607294 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B1547419 : Blo 607294 1547419 := bstep (se 1 (by rfl) ⟨1160564, by rfl⟩ : syracuseStep 1547419 = 2321129) B2321129
theorem B16481513 : Blo 607294 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B20061593 : Blo 607294 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B1564127 : Blo 607294 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B5193305 : Blo 607294 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B867943 : Blo 607294 867943 := bstep (se 1 (by rfl) ⟨650957, by rfl⟩ : syracuseStep 867943 = 1301915) B1301915
theorem B16678507 : Blo 607294 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B1154729 : Blo 607294 1154729 := bstep (se 2 (by rfl) ⟨433023, by rfl⟩ : syracuseStep 1154729 = 866047) B866047
theorem B180141893 : Blo 607294 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B974975 : Blo 607294 974975 := bstep (se 1 (by rfl) ⟨731231, by rfl⟩ : syracuseStep 974975 = 1462463) B1462463
theorem B3465575 : Blo 607294 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B43950701 : Blo 607294 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B11100905 : Blo 607294 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B1368827 : Blo 607294 1368827 := bstep (se 1 (by rfl) ⟨1026620, by rfl⟩ : syracuseStep 1368827 = 2053241) B2053241
theorem B1368953 : Blo 607294 1368953 := bstep (se 2 (by rfl) ⟨513357, by rfl⟩ : syracuseStep 1368953 = 1026715) B1026715
theorem B2057129 : Blo 607294 2057129 := bstep (se 2 (by rfl) ⟨771423, by rfl⟩ : syracuseStep 2057129 = 1542847) B1542847
theorem B607463 : Blo 607294 607463 := bstep (se 1 (by rfl) ⟨455597, by rfl⟩ : syracuseStep 607463 = 911195) B911195
theorem B1541531 : Blo 607294 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B1369691 : Blo 607294 1369691 := bstep (se 1 (by rfl) ⟨1027268, by rfl⟩ : syracuseStep 1369691 = 2054537) B2054537
theorem B607899 : Blo 607294 607899 := bstep (se 1 (by rfl) ⟨455924, by rfl⟩ : syracuseStep 607899 = 911849) B911849
theorem B26306329 : Blo 607294 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B3704687 : Blo 607294 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B3696509 : Blo 607294 3696509 := bstep (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) B1386191
theorem B911231 : Blo 607294 911231 := bstep (se 1 (by rfl) ⟨683423, by rfl⟩ : syracuseStep 911231 = 1366847) B1366847
theorem B9504823 : Blo 607294 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B2345033 : Blo 607294 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B3893339 : Blo 607294 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B1951847 : Blo 607294 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B1157257 : Blo 607294 1157257 := bstep (se 2 (by rfl) ⟨433971, by rfl⟩ : syracuseStep 1157257 = 867943) B867943
theorem B1042751 : Blo 607294 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B21121499 : Blo 607294 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B977449 : Blo 607294 977449 := bstep (se 2 (by rfl) ⟨366543, by rfl⟩ : syracuseStep 977449 = 733087) B733087
theorem B3459743 : Blo 607294 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B912137 : Blo 607294 912137 := bstep (se 2 (by rfl) ⟨342051, by rfl⟩ : syracuseStep 912137 = 684103) B684103
theorem B2059019 : Blo 607294 2059019 := bstep (se 1 (by rfl) ⟨1544264, by rfl⟩ : syracuseStep 2059019 = 3088529) B3088529
theorem B846703 : Blo 607294 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B1543151 : Blo 607294 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B609279 : Blo 607294 609279 := bstep (se 1 (by rfl) ⟨456959, by rfl⟩ : syracuseStep 609279 = 913919) B913919
theorem B683239 : Blo 607294 683239 := bstep (se 1 (by rfl) ⟨512429, by rfl⟩ : syracuseStep 683239 = 1024859) B1024859
theorem B5623019 : Blo 607294 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B912761 : Blo 607294 912761 := bstep (se 2 (by rfl) ⟨342285, by rfl⟩ : syracuseStep 912761 = 684571) B684571
theorem B1543657 : Blo 607294 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B2051567 : Blo 607294 2051567 := bstep (se 1 (by rfl) ⟨1538675, by rfl⟩ : syracuseStep 2051567 = 3077351) B3077351
theorem B4992641 : Blo 607294 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B1027721 : Blo 607294 1027721 := bstep (se 2 (by rfl) ⟨385395, by rfl⟩ : syracuseStep 1027721 = 770791) B770791
theorem B1232543 : Blo 607294 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B609999 : Blo 607294 609999 := bstep (se 1 (by rfl) ⟨457499, by rfl⟩ : syracuseStep 609999 = 914999) B914999
theorem B1298207 : Blo 607294 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B6590423 : Blo 607294 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B6918209 : Blo 607294 6918209 := bstep (se 2 (by rfl) ⟨2594328, by rfl⟩ : syracuseStep 6918209 = 5188657) B5188657
theorem B5206427 : Blo 607294 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B913967 : Blo 607294 913967 := bstep (se 1 (by rfl) ⟨685475, by rfl⟩ : syracuseStep 913967 = 1370951) B1370951
theorem B914087 : Blo 607294 914087 := bstep (se 1 (by rfl) ⟨685565, by rfl⟩ : syracuseStep 914087 = 1371131) B1371131
theorem B914231 : Blo 607294 914231 := bstep (se 1 (by rfl) ⟨685673, by rfl⟩ : syracuseStep 914231 = 1371347) B1371347
theorem B22238009 : Blo 607294 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B13374395 : Blo 607294 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B3462203 : Blo 607294 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B56988845 : Blo 607294 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B3470633 : Blo 607294 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B914735 : Blo 607294 914735 := bstep (se 1 (by rfl) ⟨686051, by rfl⟩ : syracuseStep 914735 = 1372103) B1372103
theorem B914939 : Blo 607294 914939 := bstep (se 1 (by rfl) ⟨686204, by rfl⟩ : syracuseStep 914939 = 1372409) B1372409
theorem B915227 : Blo 607294 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B915311 : Blo 607294 915311 := bstep (se 1 (by rfl) ⟨686483, by rfl⟩ : syracuseStep 915311 = 1372967) B1372967
theorem B16267283 : Blo 607294 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B23754829 : Blo 607294 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B3463343 : Blo 607294 3463343 := bstep (se 1 (by rfl) ⟨2597507, by rfl⟩ : syracuseStep 3463343 = 5195015) B5195015
theorem B17520947 : Blo 607294 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B1317359 : Blo 607294 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B3078647 : Blo 607294 3078647 := bstep (se 1 (by rfl) ⟨2308985, by rfl⟩ : syracuseStep 3078647 = 4617971) B4617971
theorem B3081009737 : Blo 607294 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B2063225 : Blo 607294 2063225 := bstep (se 2 (by rfl) ⟨773709, by rfl⟩ : syracuseStep 2063225 = 1547419) B1547419
theorem B6921125 : Blo 607294 6921125 := bstep (se 4 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 6921125 = 1297711) B1297711
theorem B22256689 : Blo 607294 22256689 := bstep (se 2 (by rfl) ⟨8346258, by rfl⟩ : syracuseStep 22256689 = 16692517) B16692517
theorem B2604307 : Blo 607294 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B44375323 : Blo 607294 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B1367351 : Blo 607294 1367351 := bstep (se 1 (by rfl) ⟨1025513, by rfl⟩ : syracuseStep 1367351 = 2051027) B2051027
theorem B769819 : Blo 607294 769819 := bstep (se 1 (by rfl) ⟨577364, by rfl⟩ : syracuseStep 769819 = 1154729) B1154729
theorem B4382543 : Blo 607294 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B1367891 : Blo 607294 1367891 := bstep (se 1 (by rfl) ⟨1025918, by rfl⟩ : syracuseStep 1367891 = 2051837) B2051837
theorem B120094595 : Blo 607294 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B4612139 : Blo 607294 4612139 := bstep (se 1 (by rfl) ⟨3459104, by rfl⟩ : syracuseStep 4612139 = 6918209) B6918209
theorem B12673097 : Blo 607294 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B2310383 : Blo 607294 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B1303265 : Blo 607294 1303265 := bstep (se 2 (by rfl) ⟨488724, by rfl⟩ : syracuseStep 1303265 = 977449) B977449
theorem B607487 : Blo 607294 607487 := bstep (se 1 (by rfl) ⟨455615, by rfl⟩ : syracuseStep 607487 = 911231) B911231
theorem B910985 : Blo 607294 910985 := bstep (se 2 (by rfl) ⟨341619, by rfl⟩ : syracuseStep 910985 = 683239) B683239
theorem B878239 : Blo 607294 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B3286781 : Blo 607294 3286781 := bstep (se 3 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 3286781 = 1232543) B1232543
theorem B608091 : Blo 607294 608091 := bstep (se 1 (by rfl) ⟨456068, by rfl⟩ : syracuseStep 608091 = 912137) B912137
theorem B4515749 : Blo 607294 4515749 := bstep (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) B846703
theorem B4614083 : Blo 607294 4614083 := bstep (se 1 (by rfl) ⟨3460562, by rfl⟩ : syracuseStep 4614083 = 6921125) B6921125
theorem B2058209 : Blo 607294 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B911567 : Blo 607294 911567 := bstep (se 1 (by rfl) ⟨683675, by rfl⟩ : syracuseStep 911567 = 1367351) B1367351
theorem B608507 : Blo 607294 608507 := bstep (se 1 (by rfl) ⟨456380, by rfl⟩ : syracuseStep 608507 = 912761) B912761
theorem B1026425 : Blo 607294 1026425 := bstep (se 2 (by rfl) ⟨384909, by rfl⟩ : syracuseStep 1026425 = 769819) B769819
theorem B3328427 : Blo 607294 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B911927 : Blo 607294 911927 := bstep (se 1 (by rfl) ⟨683945, by rfl⟩ : syracuseStep 911927 = 1367891) B1367891
theorem B80063063 : Blo 607294 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B4393615 : Blo 607294 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B31673105 : Blo 607294 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B1543009 : Blo 607294 1543009 := bstep (se 2 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 1543009 = 1157257) B1157257
theorem B2599933 : Blo 607294 2599933 := bstep (se 3 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 2599933 = 974975) B974975
theorem B609311 : Blo 607294 609311 := bstep (se 1 (by rfl) ⟨456983, by rfl⟩ : syracuseStep 609311 = 913967) B913967
theorem B609391 : Blo 607294 609391 := bstep (se 1 (by rfl) ⟨457043, by rfl⟩ : syracuseStep 609391 = 914087) B914087
theorem B7400603 : Blo 607294 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B912551 : Blo 607294 912551 := bstep (se 1 (by rfl) ⟨684413, by rfl⟩ : syracuseStep 912551 = 1368827) B1368827
theorem B609487 : Blo 607294 609487 := bstep (se 1 (by rfl) ⟨457115, by rfl⟩ : syracuseStep 609487 = 914231) B914231
theorem B912635 : Blo 607294 912635 := bstep (se 1 (by rfl) ⟨684476, by rfl⟩ : syracuseStep 912635 = 1368953) B1368953
theorem B1371419 : Blo 607294 1371419 := bstep (se 1 (by rfl) ⟨1028564, by rfl⟩ : syracuseStep 1371419 = 2057129) B2057129
theorem B8916263 : Blo 607294 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B2780669 : Blo 607294 2780669 := bstep (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) B1042751
theorem B2313755 : Blo 607294 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B609823 : Blo 607294 609823 := bstep (se 1 (by rfl) ⟨457367, by rfl⟩ : syracuseStep 609823 = 914735) B914735
theorem B1027687 : Blo 607294 1027687 := bstep (se 1 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 1027687 = 1541531) B1541531
theorem B609959 : Blo 607294 609959 := bstep (se 1 (by rfl) ⟨457469, by rfl⟩ : syracuseStep 609959 = 914939) B914939
theorem B913127 : Blo 607294 913127 := bstep (se 1 (by rfl) ⟨684845, by rfl⟩ : syracuseStep 913127 = 1369691) B1369691
theorem B610151 : Blo 607294 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B2469791 : Blo 607294 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B29675585 : Blo 607294 29675585 := bstep (se 2 (by rfl) ⟨11128344, by rfl⟩ : syracuseStep 29675585 = 22256689) B22256689
theorem B2052431 : Blo 607294 2052431 := bstep (se 1 (by rfl) ⟨1539323, by rfl⟩ : syracuseStep 2052431 = 3078647) B3078647
theorem B59167097 : Blo 607294 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B2306495 : Blo 607294 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B1372679 : Blo 607294 1372679 := bstep (se 1 (by rfl) ⟨1029509, by rfl⟩ : syracuseStep 1372679 = 2059019) B2059019
theorem B1028767 : Blo 607294 1028767 := bstep (se 1 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 1028767 = 1543151) B1543151
theorem B3461885 : Blo 607294 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B3748679 : Blo 607294 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B11686781 : Blo 607294 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B35075105 : Blo 607294 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B685147 : Blo 607294 685147 := bstep (se 1 (by rfl) ⟨513860, by rfl⟩ : syracuseStep 685147 = 1027721) B1027721
theorem B3470951 : Blo 607294 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B29300467 : Blo 607294 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B14825339 : Blo 607294 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B2308135 : Blo 607294 2308135 := bstep (se 1 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 2308135 = 3462203) B3462203
theorem B37992563 : Blo 607294 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B610207 : Blo 607294 610207 := bstep (se 1 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 610207 = 915311) B915311
theorem B2464339 : Blo 607294 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B10844855 : Blo 607294 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B1563355 : Blo 607294 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B2595559 : Blo 607294 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B1301231 : Blo 607294 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B2308895 : Blo 607294 2308895 := bstep (se 1 (by rfl) ⟨1731671, by rfl⟩ : syracuseStep 2308895 = 3463343) B3463343
theorem B8216025965 : Blo 607294 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B11680631 : Blo 607294 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B14080999 : Blo 607294 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B3472409 : Blo 607294 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B1375483 : Blo 607294 1375483 := bstep (se 1 (by rfl) ⟨1031612, by rfl⟩ : syracuseStep 1375483 = 2063225) B2063225
theorem B1367711 : Blo 607294 1367711 := bstep (se 1 (by rfl) ⟨1025783, by rfl⟩ : syracuseStep 1367711 = 2051567) B2051567
theorem B19783723 : Blo 607294 19783723 := bstep (se 1 (by rfl) ⟨14837792, by rfl⟩ : syracuseStep 19783723 = 29675585) B29675585
theorem B1540255 : Blo 607294 1540255 := bstep (se 1 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 1540255 = 2310383) B2310383
theorem B1368287 : Blo 607294 1368287 := bstep (se 1 (by rfl) ⟨1026215, by rfl⟩ : syracuseStep 1368287 = 2052431) B2052431
theorem B39444731 : Blo 607294 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B19734941 : Blo 607294 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B868843 : Blo 607294 868843 := bstep (se 1 (by rfl) ⟨651632, by rfl⟩ : syracuseStep 868843 = 1303265) B1303265
theorem B2499119 : Blo 607294 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B7791187 : Blo 607294 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B3285785 : Blo 607294 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B5858153 : Blo 607294 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B607323 : Blo 607294 607323 := bstep (se 1 (by rfl) ⟨455492, by rfl⟩ : syracuseStep 607323 = 910985) B910985
theorem B2057345 : Blo 607294 2057345 := bstep (se 2 (by rfl) ⟨771504, by rfl⟩ : syracuseStep 2057345 = 1543009) B1543009
theorem B3466577 : Blo 607294 3466577 := bstep (se 2 (by rfl) ⟨1299966, by rfl⟩ : syracuseStep 3466577 = 2599933) B2599933
theorem B607711 : Blo 607294 607711 := bstep (se 1 (by rfl) ⟨455783, by rfl⟩ : syracuseStep 607711 = 911567) B911567
theorem B607951 : Blo 607294 607951 := bstep (se 1 (by rfl) ⟨455963, by rfl⟩ : syracuseStep 607951 = 911927) B911927
theorem B608367 : Blo 607294 608367 := bstep (se 1 (by rfl) ⟨456275, by rfl⟩ : syracuseStep 608367 = 912551) B912551
theorem B1370249 : Blo 607294 1370249 := bstep (se 2 (by rfl) ⟨513843, by rfl⟩ : syracuseStep 1370249 = 1027687) B1027687
theorem B608423 : Blo 607294 608423 := bstep (se 1 (by rfl) ⟨456317, by rfl⟩ : syracuseStep 608423 = 912635) B912635
theorem B1853779 : Blo 607294 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B1542503 : Blo 607294 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B911807 : Blo 607294 911807 := bstep (se 1 (by rfl) ⟨683855, by rfl⟩ : syracuseStep 911807 = 1367711) B1367711
theorem B608751 : Blo 607294 608751 := bstep (se 1 (by rfl) ⟨456563, by rfl⟩ : syracuseStep 608751 = 913127) B913127
theorem B3074759 : Blo 607294 3074759 := bstep (se 1 (by rfl) ⟨2306069, by rfl⟩ : syracuseStep 3074759 = 4612139) B4612139
theorem B8448731 : Blo 607294 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B23383403 : Blo 607294 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B1371689 : Blo 607294 1371689 := bstep (se 2 (by rfl) ⟨514383, by rfl⟩ : syracuseStep 1371689 = 1028767) B1028767
theorem B2084473 : Blo 607294 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B3460745 : Blo 607294 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B2313967 : Blo 607294 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B2191187 : Blo 607294 2191187 := bstep (se 1 (by rfl) ⟨1643390, by rfl⟩ : syracuseStep 2191187 = 3286781) B3286781
theorem B9883559 : Blo 607294 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B3010499 : Blo 607294 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B3076055 : Blo 607294 3076055 := bstep (se 1 (by rfl) ⟨2307041, by rfl⟩ : syracuseStep 3076055 = 4614083) B4614083
theorem B1372139 : Blo 607294 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B913529 : Blo 607294 913529 := bstep (se 2 (by rfl) ⟨342573, by rfl⟩ : syracuseStep 913529 = 685147) B685147
theorem B684283 : Blo 607294 684283 := bstep (se 1 (by rfl) ⟨513212, by rfl⟩ : syracuseStep 684283 = 1026425) B1026425
theorem B53375375 : Blo 607294 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B7229903 : Blo 607294 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B21115403 : Blo 607294 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B7787087 : Blo 607294 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B3469949 : Blo 607294 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B2314939 : Blo 607294 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B914279 : Blo 607294 914279 := bstep (se 1 (by rfl) ⟨685709, by rfl⟩ : syracuseStep 914279 = 1371419) B1371419
theorem B5944175 : Blo 607294 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B3077513 : Blo 607294 3077513 := bstep (se 2 (by rfl) ⟨1154067, by rfl⟩ : syracuseStep 3077513 = 2308135) B2308135
theorem B1537663 : Blo 607294 1537663 := bstep (se 1 (by rfl) ⟨1153247, by rfl⟩ : syracuseStep 1537663 = 2306495) B2306495
theorem B915119 : Blo 607294 915119 := bstep (se 1 (by rfl) ⟨686339, by rfl⟩ : syracuseStep 915119 = 1372679) B1372679
theorem B2307923 : Blo 607294 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B18774665 : Blo 607294 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B25328375 : Blo 607294 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B2218951 : Blo 607294 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1833977 : Blo 607294 1833977 := bstep (se 2 (by rfl) ⟨687741, by rfl⟩ : syracuseStep 1833977 = 1375483) B1375483
theorem B1539263 : Blo 607294 1539263 := bstep (se 1 (by rfl) ⟨1154447, by rfl⟩ : syracuseStep 1539263 = 2308895) B2308895
theorem B5477350643 : Blo 607294 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B1170985 : Blo 607294 1170985 := bstep (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) B878239
theorem B39067289 : Blo 607294 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B1646527 : Blo 607294 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B26378297 : Blo 607294 26378297 := bstep (se 2 (by rfl) ⟨9891861, by rfl⟩ : syracuseStep 26378297 = 19783723) B19783723
theorem B26296487 : Blo 607294 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B13156627 : Blo 607294 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B11117189 : Blo 607294 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B10388249 : Blo 607294 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B2311051 : Blo 607294 2311051 := bstep (se 1 (by rfl) ⟨1733288, by rfl⟩ : syracuseStep 2311051 = 3466577) B3466577
theorem B2958601 : Blo 607294 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B607871 : Blo 607294 607871 := bstep (se 1 (by rfl) ⟨455903, by rfl⟩ : syracuseStep 607871 = 911807) B911807
theorem B2049839 : Blo 607294 2049839 := bstep (se 1 (by rfl) ⟨1537379, by rfl⟩ : syracuseStep 2049839 = 3074759) B3074759
theorem B16885583 : Blo 607294 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B1222651 : Blo 607294 1222651 := bstep (se 1 (by rfl) ⟨916988, by rfl⟩ : syracuseStep 1222651 = 1833977) B1833977
theorem B1026175 : Blo 607294 1026175 := bstep (se 1 (by rfl) ⟨769631, by rfl⟩ : syracuseStep 1026175 = 1539263) B1539263
theorem B2050217 : Blo 607294 2050217 := bstep (se 2 (by rfl) ⟨768831, by rfl⟩ : syracuseStep 2050217 = 1537663) B1537663
theorem B26044859 : Blo 607294 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B1460791 : Blo 607294 1460791 := bstep (se 1 (by rfl) ⟨1095593, by rfl⟩ : syracuseStep 1460791 = 2191187) B2191187
theorem B6589039 : Blo 607294 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B2050703 : Blo 607294 2050703 := bstep (se 1 (by rfl) ⟨1538027, by rfl⟩ : syracuseStep 2050703 = 3076055) B3076055
theorem B609019 : Blo 607294 609019 := bstep (se 1 (by rfl) ⟨456764, by rfl⟩ : syracuseStep 609019 = 913529) B913529
theorem B912191 : Blo 607294 912191 := bstep (se 1 (by rfl) ⟨684143, by rfl⟩ : syracuseStep 912191 = 1368287) B1368287
theorem B912377 : Blo 607294 912377 := bstep (se 2 (by rfl) ⟨342141, by rfl⟩ : syracuseStep 912377 = 684283) B684283
theorem B14076935 : Blo 607294 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B1666079 : Blo 607294 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B2313299 : Blo 607294 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B609519 : Blo 607294 609519 := bstep (se 1 (by rfl) ⟨457139, by rfl⟩ : syracuseStep 609519 = 914279) B914279
theorem B1158457 : Blo 607294 1158457 := bstep (se 2 (by rfl) ⟨434421, by rfl⟩ : syracuseStep 1158457 = 868843) B868843
theorem B1371563 : Blo 607294 1371563 := bstep (se 1 (by rfl) ⟨1028672, by rfl⟩ : syracuseStep 1371563 = 2057345) B2057345
theorem B2051675 : Blo 607294 2051675 := bstep (se 1 (by rfl) ⟨1538756, by rfl⟩ : syracuseStep 2051675 = 3077513) B3077513
theorem B610079 : Blo 607294 610079 := bstep (se 1 (by rfl) ⟨457559, by rfl⟩ : syracuseStep 610079 = 915119) B915119
theorem B19279741 : Blo 607294 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B913499 : Blo 607294 913499 := bstep (se 1 (by rfl) ⟨685124, by rfl⟩ : syracuseStep 913499 = 1370249) B1370249
theorem B1028335 : Blo 607294 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B5632487 : Blo 607294 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B1561313 : Blo 607294 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B8762093 : Blo 607294 8762093 := bstep (se 3 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 8762093 = 3285785) B3285785
theorem B3085289 : Blo 607294 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B914459 : Blo 607294 914459 := bstep (se 1 (by rfl) ⟨685844, by rfl⟩ : syracuseStep 914459 = 1371689) B1371689
theorem B2307163 : Blo 607294 2307163 := bstep (se 1 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 2307163 = 3460745) B3460745
theorem B914759 : Blo 607294 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B2053673 : Blo 607294 2053673 := bstep (se 2 (by rfl) ⟨770127, by rfl⟩ : syracuseStep 2053673 = 1540255) B1540255
theorem B35583583 : Blo 607294 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B5191391 : Blo 607294 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B2471705 : Blo 607294 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B3905435 : Blo 607294 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B3962783 : Blo 607294 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B3086585 : Blo 607294 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B1538615 : Blo 607294 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B12516443 : Blo 607294 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B3651567095 : Blo 607294 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B15588935 : Blo 607294 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B2195369 : Blo 607294 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B2006999 : Blo 607294 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B17530991 : Blo 607294 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B1368233 : Blo 607294 1368233 := bstep (se 2 (by rfl) ⟨513087, by rfl⟩ : syracuseStep 1368233 = 1026175) B1026175
theorem B1647803 : Blo 607294 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B5841395 : Blo 607294 5841395 := bstep (se 1 (by rfl) ⟨4381046, by rfl⟩ : syracuseStep 5841395 = 8762093) B8762093
theorem B2056859 : Blo 607294 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B1369115 : Blo 607294 1369115 := bstep (se 1 (by rfl) ⟨1026836, by rfl⟩ : syracuseStep 1369115 = 2053673) B2053673
theorem B69452957 : Blo 607294 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B3081401 : Blo 607294 3081401 := bstep (se 2 (by rfl) ⟨1155525, by rfl⟩ : syracuseStep 3081401 = 2311051) B2311051
theorem B11257055 : Blo 607294 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B2057723 : Blo 607294 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B1025743 : Blo 607294 1025743 := bstep (se 1 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 1025743 = 1538615) B1538615
theorem B608127 : Blo 607294 608127 := bstep (se 1 (by rfl) ⟨456095, by rfl⟩ : syracuseStep 608127 = 912191) B912191
theorem B4163501 : Blo 607294 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B608251 : Blo 607294 608251 := bstep (se 1 (by rfl) ⟨456188, by rfl⟩ : syracuseStep 608251 = 912377) B912377
theorem B1542199 : Blo 607294 1542199 := bstep (se 1 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 1542199 = 2313299) B2313299
theorem B2434378063 : Blo 607294 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B10414493 : Blo 607294 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B1337999 : Blo 607294 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B608999 : Blo 607294 608999 := bstep (se 1 (by rfl) ⟨456749, by rfl⟩ : syracuseStep 608999 = 913499) B913499
theorem B1371113 : Blo 607294 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B3754991 : Blo 607294 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B17542169 : Blo 607294 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B6925499 : Blo 607294 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B609639 : Blo 607294 609639 := bstep (se 1 (by rfl) ⟨457229, by rfl⟩ : syracuseStep 609639 = 914459) B914459
theorem B8785385 : Blo 607294 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B609839 : Blo 607294 609839 := bstep (se 1 (by rfl) ⟨457379, by rfl⟩ : syracuseStep 609839 = 914759) B914759
theorem B3460927 : Blo 607294 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B2641855 : Blo 607294 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B3076217 : Blo 607294 3076217 := bstep (se 2 (by rfl) ⟨1153581, by rfl⟩ : syracuseStep 3076217 = 2307163) B2307163
theorem B3944801 : Blo 607294 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B1544609 : Blo 607294 1544609 := bstep (se 2 (by rfl) ⟨579228, by rfl⟩ : syracuseStep 1544609 = 1158457) B1158457
theorem B9384623 : Blo 607294 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B1110719 : Blo 607294 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B8344295 : Blo 607294 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B47444777 : Blo 607294 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B914375 : Blo 607294 914375 := bstep (se 1 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 914375 = 1371563) B1371563
theorem B10392623 : Blo 607294 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B1463579 : Blo 607294 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B17585531 : Blo 607294 17585531 := bstep (se 1 (by rfl) ⟨13189148, by rfl⟩ : syracuseStep 17585531 = 26378297) B26378297
theorem B7411459 : Blo 607294 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B1947721 : Blo 607294 1947721 := bstep (se 2 (by rfl) ⟨730395, by rfl⟩ : syracuseStep 1947721 = 1460791) B1460791
theorem B1366559 : Blo 607294 1366559 := bstep (se 1 (by rfl) ⟨1024919, by rfl⟩ : syracuseStep 1366559 = 2049839) B2049839
theorem B1366811 : Blo 607294 1366811 := bstep (se 1 (by rfl) ⟨1025108, by rfl⟩ : syracuseStep 1366811 = 2050217) B2050217
theorem B1367135 : Blo 607294 1367135 := bstep (se 1 (by rfl) ⟨1025351, by rfl⟩ : syracuseStep 1367135 = 2050703) B2050703
theorem B1367783 : Blo 607294 1367783 := bstep (se 1 (by rfl) ⟨1025837, by rfl⟩ : syracuseStep 1367783 = 2051675) B2051675
theorem B25706321 : Blo 607294 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B1630201 : Blo 607294 1630201 := bstep (se 2 (by rfl) ⟨611325, by rfl⟩ : syracuseStep 1630201 = 1222651) B1222651
theorem B2056265 : Blo 607294 2056265 := bstep (se 2 (by rfl) ⟨771099, by rfl⟩ : syracuseStep 2056265 = 1542199) B1542199
theorem B2596961 : Blo 607294 2596961 := bstep (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) B1947721
theorem B5562863 : Blo 607294 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B31629851 : Blo 607294 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B46301971 : Blo 607294 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B1098535 : Blo 607294 1098535 := bstep (se 1 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 1098535 = 1647803) B1647803
theorem B7504703 : Blo 607294 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B975719 : Blo 607294 975719 := bstep (se 1 (by rfl) ⟨731789, by rfl⟩ : syracuseStep 975719 = 1463579) B1463579
theorem B11723687 : Blo 607294 11723687 := bstep (se 1 (by rfl) ⟨8792765, by rfl⟩ : syracuseStep 11723687 = 17585531) B17585531
theorem B10519469 : Blo 607294 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B911039 : Blo 607294 911039 := bstep (se 1 (by rfl) ⟨683279, by rfl⟩ : syracuseStep 911039 = 1366559) B1366559
theorem B911207 : Blo 607294 911207 := bstep (se 1 (by rfl) ⟨683405, by rfl⟩ : syracuseStep 911207 = 1366811) B1366811
theorem B911423 : Blo 607294 911423 := bstep (se 1 (by rfl) ⟨683567, by rfl⟩ : syracuseStep 911423 = 1367135) B1367135
theorem B9881945 : Blo 607294 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B4614569 : Blo 607294 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B911855 : Blo 607294 911855 := bstep (se 1 (by rfl) ⟨683891, by rfl⟩ : syracuseStep 911855 = 1367783) B1367783
theorem B2173601 : Blo 607294 2173601 := bstep (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) B1630201
theorem B2050811 : Blo 607294 2050811 := bstep (se 1 (by rfl) ⟨1538108, by rfl⟩ : syracuseStep 2050811 = 3076217) B3076217
theorem B912155 : Blo 607294 912155 := bstep (se 1 (by rfl) ⟨684116, by rfl⟩ : syracuseStep 912155 = 1368233) B1368233
theorem B3894263 : Blo 607294 3894263 := bstep (se 1 (by rfl) ⟨2920697, by rfl⟩ : syracuseStep 3894263 = 5841395) B5841395
theorem B1371239 : Blo 607294 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B3245837417 : Blo 607294 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B609583 : Blo 607294 609583 := bstep (se 1 (by rfl) ⟨457187, by rfl⟩ : syracuseStep 609583 = 914375) B914375
theorem B912743 : Blo 607294 912743 := bstep (se 1 (by rfl) ⟨684557, by rfl⟩ : syracuseStep 912743 = 1369115) B1369115
theorem B1371815 : Blo 607294 1371815 := bstep (se 1 (by rfl) ⟨1028861, by rfl⟩ : syracuseStep 1371815 = 2057723) B2057723
theorem B6942995 : Blo 607294 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B3567997 : Blo 607294 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B2961917 : Blo 607294 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B914075 : Blo 607294 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B2503327 : Blo 607294 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B11694779 : Blo 607294 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B4616999 : Blo 607294 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B11687327 : Blo 607294 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B1029739 : Blo 607294 1029739 := bstep (se 1 (by rfl) ⟨772304, by rfl⟩ : syracuseStep 1029739 = 1544609) B1544609
theorem B6256415 : Blo 607294 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B6928415 : Blo 607294 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B2054267 : Blo 607294 2054267 := bstep (se 1 (by rfl) ⟨1540700, by rfl⟩ : syracuseStep 2054267 = 3081401) B3081401
theorem B2775667 : Blo 607294 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B1367657 : Blo 607294 1367657 := bstep (se 2 (by rfl) ⟨512871, by rfl⟩ : syracuseStep 1367657 = 1025743) B1025743
theorem B5856923 : Blo 607294 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B17137547 : Blo 607294 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B3522473 : Blo 607294 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B4628663 : Blo 607294 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B1974611 : Blo 607294 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B21086567 : Blo 607294 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B7815791 : Blo 607294 7815791 := bstep (se 1 (by rfl) ⟨5861843, by rfl⟩ : syracuseStep 7815791 = 11723687) B11723687
theorem B7012979 : Blo 607294 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B7791551 : Blo 607294 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B61735961 : Blo 607294 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B607359 : Blo 607294 607359 := bstep (se 1 (by rfl) ⟨455519, by rfl⟩ : syracuseStep 607359 = 911039) B911039
theorem B4170943 : Blo 607294 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B607471 : Blo 607294 607471 := bstep (se 1 (by rfl) ⟨455603, by rfl⟩ : syracuseStep 607471 = 911207) B911207
theorem B607615 : Blo 607294 607615 := bstep (se 1 (by rfl) ⟨455711, by rfl⟩ : syracuseStep 607615 = 911423) B911423
theorem B1369511 : Blo 607294 1369511 := bstep (se 1 (by rfl) ⟨1027133, by rfl⟩ : syracuseStep 1369511 = 2054267) B2054267
theorem B6587963 : Blo 607294 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B607903 : Blo 607294 607903 := bstep (se 1 (by rfl) ⟨455927, by rfl⟩ : syracuseStep 607903 = 911855) B911855
theorem B608103 : Blo 607294 608103 := bstep (se 1 (by rfl) ⟨456077, by rfl⟩ : syracuseStep 608103 = 912155) B912155
theorem B608495 : Blo 607294 608495 := bstep (se 1 (by rfl) ⟨456371, by rfl⟩ : syracuseStep 608495 = 912743) B912743
theorem B911771 : Blo 607294 911771 := bstep (se 1 (by rfl) ⟨683828, by rfl⟩ : syracuseStep 911771 = 1367657) B1367657
theorem B1370843 : Blo 607294 1370843 := bstep (se 1 (by rfl) ⟨1028132, by rfl⟩ : syracuseStep 1370843 = 2056265) B2056265
theorem B1731307 : Blo 607294 1731307 := bstep (se 1 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 1731307 = 2596961) B2596961
theorem B609383 : Blo 607294 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B650479 : Blo 607294 650479 := bstep (se 1 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 650479 = 975719) B975719
theorem B3337769 : Blo 607294 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B3076379 : Blo 607294 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B5796269 : Blo 607294 5796269 := bstep (se 3 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 5796269 = 2173601) B2173601
theorem B914159 : Blo 607294 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B1372985 : Blo 607294 1372985 := bstep (se 2 (by rfl) ⟨514869, by rfl⟩ : syracuseStep 1372985 = 1029739) B1029739
theorem B3904615 : Blo 607294 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B914543 : Blo 607294 914543 := bstep (se 1 (by rfl) ⟨685907, by rfl⟩ : syracuseStep 914543 = 1371815) B1371815
theorem B11425031 : Blo 607294 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B2348315 : Blo 607294 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B3708575 : Blo 607294 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B7796519 : Blo 607294 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B4757329 : Blo 607294 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B3077999 : Blo 607294 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B5003135 : Blo 607294 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B3700889 : Blo 607294 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B1464713 : Blo 607294 1464713 := bstep (se 2 (by rfl) ⟨549267, by rfl⟩ : syracuseStep 1464713 = 1098535) B1098535
theorem B4618943 : Blo 607294 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B1367207 : Blo 607294 1367207 := bstep (se 1 (by rfl) ⟨1025405, by rfl⟩ : syracuseStep 1367207 = 2050811) B2050811
theorem B2596175 : Blo 607294 2596175 := bstep (se 1 (by rfl) ⟨1947131, by rfl⟩ : syracuseStep 2596175 = 3894263) B3894263
theorem B2163891611 : Blo 607294 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B14057711 : Blo 607294 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B5210527 : Blo 607294 5210527 := bstep (se 1 (by rfl) ⟨3907895, by rfl⟩ : syracuseStep 5210527 = 7815791) B7815791
theorem B5194367 : Blo 607294 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B41157307 : Blo 607294 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B1565543 : Blo 607294 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B4391975 : Blo 607294 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B3335423 : Blo 607294 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B2467259 : Blo 607294 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B976475 : Blo 607294 976475 := bstep (se 1 (by rfl) ⟨732356, by rfl⟩ : syracuseStep 976475 = 1464713) B1464713
theorem B607847 : Blo 607294 607847 := bstep (se 1 (by rfl) ⟨455885, by rfl⟩ : syracuseStep 607847 = 911771) B911771
theorem B911471 : Blo 607294 911471 := bstep (se 1 (by rfl) ⟨683603, by rfl⟩ : syracuseStep 911471 = 1367207) B1367207
theorem B1730783 : Blo 607294 1730783 := bstep (se 1 (by rfl) ⟨1298087, by rfl⟩ : syracuseStep 1730783 = 2596175) B2596175
theorem B6343105 : Blo 607294 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B2050919 : Blo 607294 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B609439 : Blo 607294 609439 := bstep (se 1 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 609439 = 914159) B914159
theorem B609695 : Blo 607294 609695 := bstep (se 1 (by rfl) ⟨457271, by rfl⟩ : syracuseStep 609695 = 914543) B914543
theorem B913007 : Blo 607294 913007 := bstep (se 1 (by rfl) ⟨684755, by rfl⟩ : syracuseStep 913007 = 1369511) B1369511
theorem B5197679 : Blo 607294 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B2051999 : Blo 607294 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B5206153 : Blo 607294 5206153 := bstep (se 2 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 5206153 = 3904615) B3904615
theorem B913895 : Blo 607294 913895 := bstep (se 1 (by rfl) ⟨685421, by rfl⟩ : syracuseStep 913895 = 1370843) B1370843
theorem B2225179 : Blo 607294 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B3085775 : Blo 607294 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B1316407 : Blo 607294 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B3864179 : Blo 607294 3864179 := bstep (se 1 (by rfl) ⟨2898134, by rfl⟩ : syracuseStep 3864179 = 5796269) B5796269
theorem B4675319 : Blo 607294 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B915323 : Blo 607294 915323 := bstep (se 1 (by rfl) ⟨686492, by rfl⟩ : syracuseStep 915323 = 1372985) B1372985
theorem B7616687 : Blo 607294 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B2308409 : Blo 607294 2308409 := bstep (se 2 (by rfl) ⟨865653, by rfl⟩ : syracuseStep 2308409 = 1731307) B1731307
theorem B2472383 : Blo 607294 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B5561257 : Blo 607294 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B867305 : Blo 607294 867305 := bstep (se 2 (by rfl) ⟨325239, by rfl⟩ : syracuseStep 867305 = 650479) B650479
theorem B3079295 : Blo 607294 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B1442594407 : Blo 607294 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B1043695 : Blo 607294 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B9371807 : Blo 607294 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B6947369 : Blo 607294 6947369 := bstep (se 2 (by rfl) ⟨2605263, by rfl⟩ : syracuseStep 6947369 = 5210527) B5210527
theorem B2057183 : Blo 607294 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B7415009 : Blo 607294 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B2966905 : Blo 607294 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B607647 : Blo 607294 607647 := bstep (se 1 (by rfl) ⟨455735, by rfl⟩ : syracuseStep 607647 = 911471) B911471
theorem B1755209 : Blo 607294 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B1923459209 : Blo 607294 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B608671 : Blo 607294 608671 := bstep (se 1 (by rfl) ⟨456503, by rfl⟩ : syracuseStep 608671 = 913007) B913007
theorem B2312813 : Blo 607294 2312813 := bstep (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) B867305
theorem B6941537 : Blo 607294 6941537 := bstep (se 2 (by rfl) ⟨2603076, by rfl⟩ : syracuseStep 6941537 = 5206153) B5206153
theorem B609263 : Blo 607294 609263 := bstep (se 1 (by rfl) ⟨456947, by rfl⟩ : syracuseStep 609263 = 913895) B913895
theorem B20311165 : Blo 607294 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B8457473 : Blo 607294 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B2927983 : Blo 607294 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B2576119 : Blo 607294 2576119 := bstep (se 1 (by rfl) ⟨1932089, by rfl⟩ : syracuseStep 2576119 = 3864179) B3864179
theorem B3116879 : Blo 607294 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B610215 : Blo 607294 610215 := bstep (se 1 (by rfl) ⟨457661, by rfl⟩ : syracuseStep 610215 = 915323) B915323
theorem B2052863 : Blo 607294 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B3462911 : Blo 607294 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B8894461 : Blo 607294 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B54876409 : Blo 607294 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B1644839 : Blo 607294 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B6593021 : Blo 607294 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B1153855 : Blo 607294 1153855 := bstep (se 1 (by rfl) ⟨865391, by rfl⟩ : syracuseStep 1153855 = 1730783) B1730783
theorem B1538939 : Blo 607294 1538939 := bstep (se 1 (by rfl) ⟨1154204, by rfl⟩ : syracuseStep 1538939 = 2308409) B2308409
theorem B2603933 : Blo 607294 2603933 := bstep (se 3 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 2603933 = 976475) B976475
theorem B1367279 : Blo 607294 1367279 := bstep (se 1 (by rfl) ⟨1025459, by rfl⟩ : syracuseStep 1367279 = 2050919) B2050919
theorem B3465119 : Blo 607294 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B1367999 : Blo 607294 1367999 := bstep (se 1 (by rfl) ⟨1025999, by rfl⟩ : syracuseStep 1367999 = 2051999) B2051999
theorem B1368575 : Blo 607294 1368575 := bstep (se 1 (by rfl) ⟨1026431, by rfl⟩ : syracuseStep 1368575 = 2052863) B2052863
theorem B22553261 : Blo 607294 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B1541875 : Blo 607294 1541875 := bstep (se 1 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 1541875 = 2312813) B2312813
theorem B1025959 : Blo 607294 1025959 := bstep (se 1 (by rfl) ⟨769469, by rfl⟩ : syracuseStep 1025959 = 1538939) B1538939
theorem B911519 : Blo 607294 911519 := bstep (se 1 (by rfl) ⟨683639, by rfl⟩ : syracuseStep 911519 = 1367279) B1367279
theorem B911999 : Blo 607294 911999 := bstep (se 1 (by rfl) ⟨683999, by rfl⟩ : syracuseStep 911999 = 1367999) B1367999
theorem B4680557 : Blo 607294 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B4631579 : Blo 607294 4631579 := bstep (se 1 (by rfl) ⟨3473684, by rfl⟩ : syracuseStep 4631579 = 6947369) B6947369
theorem B1371455 : Blo 607294 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B4943339 : Blo 607294 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B1282306139 : Blo 607294 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B4395347 : Blo 607294 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B3434825 : Blo 607294 3434825 := bstep (se 2 (by rfl) ⟨1288059, by rfl⟩ : syracuseStep 3434825 = 2576119) B2576119
theorem B3903977 : Blo 607294 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B2077919 : Blo 607294 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B11859281 : Blo 607294 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B6247871 : Blo 607294 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B1538473 : Blo 607294 1538473 := bstep (se 2 (by rfl) ⟨576927, by rfl⟩ : syracuseStep 1538473 = 1153855) B1153855
theorem B2308607 : Blo 607294 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B292674181 : Blo 607294 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B27081553 : Blo 607294 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B1096559 : Blo 607294 1096559 := bstep (se 1 (by rfl) ⟨822419, by rfl⟩ : syracuseStep 1096559 = 1644839) B1644839
theorem B1391593 : Blo 607294 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B3955873 : Blo 607294 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B4627691 : Blo 607294 4627691 := bstep (se 1 (by rfl) ⟨3470768, by rfl⟩ : syracuseStep 4627691 = 6941537) B6941537
theorem B1735955 : Blo 607294 1735955 := bstep (se 1 (by rfl) ⟨1301966, by rfl⟩ : syracuseStep 1735955 = 2603933) B2603933
theorem B2310079 : Blo 607294 2310079 := bstep (se 1 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 2310079 = 3465119) B3465119
theorem B1385279 : Blo 607294 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B7906187 : Blo 607294 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B607679 : Blo 607294 607679 := bstep (se 1 (by rfl) ⟨455759, by rfl⟩ : syracuseStep 607679 = 911519) B911519
theorem B607999 : Blo 607294 607999 := bstep (se 1 (by rfl) ⟨455999, by rfl⟩ : syracuseStep 607999 = 911999) B911999
theorem B731039 : Blo 607294 731039 := bstep (se 1 (by rfl) ⟨548279, by rfl⟩ : syracuseStep 731039 = 1096559) B1096559
theorem B1157303 : Blo 607294 1157303 := bstep (se 1 (by rfl) ⟨867977, by rfl⟩ : syracuseStep 1157303 = 1735955) B1735955
theorem B3295559 : Blo 607294 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B15035507 : Blo 607294 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B854870759 : Blo 607294 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B912383 : Blo 607294 912383 := bstep (se 1 (by rfl) ⟨684287, by rfl⟩ : syracuseStep 912383 = 1368575) B1368575
theorem B2051297 : Blo 607294 2051297 := bstep (se 2 (by rfl) ⟨769236, by rfl⟩ : syracuseStep 2051297 = 1538473) B1538473
theorem B4165247 : Blo 607294 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B1855457 : Blo 607294 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B2289883 : Blo 607294 2289883 := bstep (se 1 (by rfl) ⟨1717412, by rfl⟩ : syracuseStep 2289883 = 3434825) B3434825
theorem B3085127 : Blo 607294 3085127 := bstep (se 1 (by rfl) ⟨2313845, by rfl⟩ : syracuseStep 3085127 = 4627691) B4627691
theorem B914303 : Blo 607294 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B2930231 : Blo 607294 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B2602651 : Blo 607294 2602651 := bstep (se 1 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 2602651 = 3903977) B3903977
theorem B390232241 : Blo 607294 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B36108737 : Blo 607294 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B5274497 : Blo 607294 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B1539071 : Blo 607294 1539071 := bstep (se 1 (by rfl) ⟨1154303, by rfl⟩ : syracuseStep 1539071 = 2308607) B2308607
theorem B3120371 : Blo 607294 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B3087719 : Blo 607294 3087719 := bstep (se 1 (by rfl) ⟨2315789, by rfl⟩ : syracuseStep 3087719 = 4631579) B4631579
theorem B2055833 : Blo 607294 2055833 := bstep (se 2 (by rfl) ⟨770937, by rfl⟩ : syracuseStep 2055833 = 1541875) B1541875
theorem B1367945 : Blo 607294 1367945 := bstep (se 2 (by rfl) ⟨512979, by rfl⟩ : syracuseStep 1367945 = 1025959) B1025959
theorem B3080105 : Blo 607294 3080105 := bstep (se 2 (by rfl) ⟨1155039, by rfl⟩ : syracuseStep 3080105 = 2310079) B2310079
theorem B2056751 : Blo 607294 2056751 := bstep (se 1 (by rfl) ⟨1542563, by rfl⟩ : syracuseStep 2056751 = 3085127) B3085127
theorem B260154827 : Blo 607294 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B771535 : Blo 607294 771535 := bstep (se 1 (by rfl) ⟨578651, by rfl⟩ : syracuseStep 771535 = 1157303) B1157303
theorem B2197039 : Blo 607294 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B3516331 : Blo 607294 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B1026047 : Blo 607294 1026047 := bstep (se 1 (by rfl) ⟨769535, by rfl⟩ : syracuseStep 1026047 = 1539071) B1539071
theorem B608255 : Blo 607294 608255 := bstep (se 1 (by rfl) ⟨456191, by rfl⟩ : syracuseStep 608255 = 912383) B912383
theorem B2058479 : Blo 607294 2058479 := bstep (se 1 (by rfl) ⟨1543859, by rfl⟩ : syracuseStep 2058479 = 3087719) B3087719
theorem B1370555 : Blo 607294 1370555 := bstep (se 1 (by rfl) ⟨1027916, by rfl⟩ : syracuseStep 1370555 = 2055833) B2055833
theorem B911963 : Blo 607294 911963 := bstep (se 1 (by rfl) ⟨683972, by rfl⟩ : syracuseStep 911963 = 1367945) B1367945
theorem B609535 : Blo 607294 609535 := bstep (se 1 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 609535 = 914303) B914303
theorem B5270791 : Blo 607294 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B1953487 : Blo 607294 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B24072491 : Blo 607294 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B569913839 : Blo 607294 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B10023671 : Blo 607294 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B3470201 : Blo 607294 3470201 := bstep (se 2 (by rfl) ⟨1301325, by rfl⟩ : syracuseStep 3470201 = 2602651) B2602651
theorem B2053403 : Blo 607294 2053403 := bstep (se 1 (by rfl) ⟨1540052, by rfl⟩ : syracuseStep 2053403 = 3080105) B3080105
theorem B3053177 : Blo 607294 3053177 := bstep (se 2 (by rfl) ⟨1144941, by rfl⟩ : syracuseStep 3053177 = 2289883) B2289883
theorem B923519 : Blo 607294 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B11107325 : Blo 607294 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B1367531 : Blo 607294 1367531 := bstep (se 1 (by rfl) ⟨1025648, by rfl⟩ : syracuseStep 1367531 = 2051297) B2051297
theorem B2080247 : Blo 607294 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B1949437 : Blo 607294 1949437 := bstep (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) B731039
theorem B1236971 : Blo 607294 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B16048327 : Blo 607294 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B1368935 : Blo 607294 1368935 := bstep (se 1 (by rfl) ⟨1026701, by rfl⟩ : syracuseStep 1368935 = 2053403) B2053403
theorem B5547325 : Blo 607294 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B10396997 : Blo 607294 10396997 := bstep (se 4 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 10396997 = 1949437) B1949437
theorem B607975 : Blo 607294 607975 := bstep (se 1 (by rfl) ⟨455981, by rfl⟩ : syracuseStep 607975 = 911963) B911963
theorem B911687 : Blo 607294 911687 := bstep (se 1 (by rfl) ⟨683765, by rfl⟩ : syracuseStep 911687 = 1367531) B1367531
theorem B4688441 : Blo 607294 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B1371167 : Blo 607294 1371167 := bstep (se 1 (by rfl) ⟨1028375, by rfl⟩ : syracuseStep 1371167 = 2056751) B2056751
theorem B2313467 : Blo 607294 2313467 := bstep (se 1 (by rfl) ⟨1735100, by rfl⟩ : syracuseStep 2313467 = 3470201) B3470201
theorem B173436551 : Blo 607294 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B2035451 : Blo 607294 2035451 := bstep (se 1 (by rfl) ⟨1526588, by rfl⟩ : syracuseStep 2035451 = 3053177) B3053177
theorem B684031 : Blo 607294 684031 := bstep (se 1 (by rfl) ⟨513023, by rfl⟩ : syracuseStep 684031 = 1026047) B1026047
theorem B1372319 : Blo 607294 1372319 := bstep (se 1 (by rfl) ⟨1029239, by rfl⟩ : syracuseStep 1372319 = 2058479) B2058479
theorem B913703 : Blo 607294 913703 := bstep (se 1 (by rfl) ⟨685277, by rfl⟩ : syracuseStep 913703 = 1370555) B1370555
theorem B1028713 : Blo 607294 1028713 := bstep (se 2 (by rfl) ⟨385767, by rfl⟩ : syracuseStep 1028713 = 771535) B771535
theorem B2929385 : Blo 607294 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B2462717 : Blo 607294 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B3298589 : Blo 607294 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B29619533 : Blo 607294 29619533 := bstep (se 3 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 29619533 = 11107325) B11107325
theorem B379942559 : Blo 607294 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B6682447 : Blo 607294 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B7027721 : Blo 607294 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B2604649 : Blo 607294 2604649 := bstep (se 2 (by rfl) ⟨976743, by rfl⟩ : syracuseStep 2604649 = 1953487) B1953487
theorem B21397769 : Blo 607294 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B6931331 : Blo 607294 6931331 := bstep (se 1 (by rfl) ⟨5198498, by rfl⟩ : syracuseStep 6931331 = 10396997) B10396997
theorem B607791 : Blo 607294 607791 := bstep (se 1 (by rfl) ⟨455843, by rfl⟩ : syracuseStep 607791 = 911687) B911687
theorem B1542311 : Blo 607294 1542311 := bstep (se 1 (by rfl) ⟨1156733, by rfl⟩ : syracuseStep 1542311 = 2313467) B2313467
theorem B115624367 : Blo 607294 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B912041 : Blo 607294 912041 := bstep (se 2 (by rfl) ⟨342015, by rfl⟩ : syracuseStep 912041 = 684031) B684031
theorem B609135 : Blo 607294 609135 := bstep (se 1 (by rfl) ⟨456851, by rfl⟩ : syracuseStep 609135 = 913703) B913703
theorem B912623 : Blo 607294 912623 := bstep (se 1 (by rfl) ⟨684467, by rfl⟩ : syracuseStep 912623 = 1368935) B1368935
theorem B1641811 : Blo 607294 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B1952923 : Blo 607294 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B1371617 : Blo 607294 1371617 := bstep (se 2 (by rfl) ⟨514356, by rfl⟩ : syracuseStep 1371617 = 1028713) B1028713
theorem B2199059 : Blo 607294 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B19746355 : Blo 607294 19746355 := bstep (se 1 (by rfl) ⟨14809766, by rfl⟩ : syracuseStep 19746355 = 29619533) B29619533
theorem B3125627 : Blo 607294 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B914111 : Blo 607294 914111 := bstep (se 1 (by rfl) ⟨685583, by rfl⟩ : syracuseStep 914111 = 1371167) B1371167
theorem B8909929 : Blo 607294 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B1356967 : Blo 607294 1356967 := bstep (se 1 (by rfl) ⟨1017725, by rfl⟩ : syracuseStep 1356967 = 2035451) B2035451
theorem B914879 : Blo 607294 914879 := bstep (se 1 (by rfl) ⟨686159, by rfl⟩ : syracuseStep 914879 = 1372319) B1372319
theorem B253295039 : Blo 607294 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B7396433 : Blo 607294 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B4685147 : Blo 607294 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B3472865 : Blo 607294 3472865 := bstep (se 2 (by rfl) ⟨1302324, by rfl⟩ : syracuseStep 3472865 = 2604649) B2604649
theorem B4620887 : Blo 607294 4620887 := bstep (se 1 (by rfl) ⟨3465665, by rfl⟩ : syracuseStep 4620887 = 6931331) B6931331
theorem B11879905 : Blo 607294 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B168863359 : Blo 607294 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B2189081 : Blo 607294 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B608027 : Blo 607294 608027 := bstep (se 1 (by rfl) ⟨456020, by rfl⟩ : syracuseStep 608027 = 912041) B912041
theorem B608415 : Blo 607294 608415 := bstep (se 1 (by rfl) ⟨456311, by rfl⟩ : syracuseStep 608415 = 912623) B912623
theorem B3123431 : Blo 607294 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B14265179 : Blo 607294 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B2083751 : Blo 607294 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B609407 : Blo 607294 609407 := bstep (se 1 (by rfl) ⟨457055, by rfl⟩ : syracuseStep 609407 = 914111) B914111
theorem B609919 : Blo 607294 609919 := bstep (se 1 (by rfl) ⟨457439, by rfl⟩ : syracuseStep 609919 = 914879) B914879
theorem B1028207 : Blo 607294 1028207 := bstep (se 1 (by rfl) ⟨771155, by rfl⟩ : syracuseStep 1028207 = 1542311) B1542311
theorem B77082911 : Blo 607294 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B914411 : Blo 607294 914411 := bstep (se 1 (by rfl) ⟨685808, by rfl⟩ : syracuseStep 914411 = 1371617) B1371617
theorem B2315243 : Blo 607294 2315243 := bstep (se 1 (by rfl) ⟨1736432, by rfl⟩ : syracuseStep 2315243 = 3472865) B3472865
theorem B2603897 : Blo 607294 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B1809289 : Blo 607294 1809289 := bstep (se 2 (by rfl) ⟨678483, by rfl⟩ : syracuseStep 1809289 = 1356967) B1356967
theorem B4930955 : Blo 607294 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B26328473 : Blo 607294 26328473 := bstep (se 2 (by rfl) ⟨9873177, by rfl⟩ : syracuseStep 26328473 = 19746355) B19746355
theorem B1466039 : Blo 607294 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B51388607 : Blo 607294 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B3080591 : Blo 607294 3080591 := bstep (se 1 (by rfl) ⟨2310443, by rfl⟩ : syracuseStep 3080591 = 4620887) B4620887
theorem B1459387 : Blo 607294 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B2082287 : Blo 607294 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B225151145 : Blo 607294 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B3287303 : Blo 607294 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B977359 : Blo 607294 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B609607 : Blo 607294 609607 := bstep (se 1 (by rfl) ⟨457205, by rfl⟩ : syracuseStep 609607 = 914411) B914411
theorem B1543495 : Blo 607294 1543495 := bstep (se 1 (by rfl) ⟨1157621, by rfl⟩ : syracuseStep 1543495 = 2315243) B2315243
theorem B2412385 : Blo 607294 2412385 := bstep (se 2 (by rfl) ⟨904644, by rfl⟩ : syracuseStep 2412385 = 1809289) B1809289
theorem B1389167 : Blo 607294 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B15839873 : Blo 607294 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B17552315 : Blo 607294 17552315 := bstep (se 1 (by rfl) ⟨13164236, by rfl⟩ : syracuseStep 17552315 = 26328473) B26328473
theorem B685471 : Blo 607294 685471 := bstep (se 1 (by rfl) ⟨514103, by rfl⟩ : syracuseStep 685471 = 1028207) B1028207
theorem B9510119 : Blo 607294 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B1735931 : Blo 607294 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B34259071 : Blo 607294 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B926111 : Blo 607294 926111 := bstep (se 1 (by rfl) ⟨694583, by rfl⟩ : syracuseStep 926111 = 1389167) B1389167
theorem B10559915 : Blo 607294 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B1303145 : Blo 607294 1303145 := bstep (se 2 (by rfl) ⟨488679, by rfl⟩ : syracuseStep 1303145 = 977359) B977359
theorem B4629149 : Blo 607294 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B7783397 : Blo 607294 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B2057993 : Blo 607294 2057993 := bstep (se 2 (by rfl) ⟨771747, by rfl⟩ : syracuseStep 2057993 = 1543495) B1543495
theorem B11701543 : Blo 607294 11701543 := bstep (se 1 (by rfl) ⟨8776157, by rfl⟩ : syracuseStep 11701543 = 17552315) B17552315
theorem B1388191 : Blo 607294 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B2191535 : Blo 607294 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B2401612213 : Blo 607294 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B12866053 : Blo 607294 12866053 := bstep (se 4 (by rfl) ⟨1206192, by rfl⟩ : syracuseStep 12866053 = 2412385) B2412385
theorem B913961 : Blo 607294 913961 := bstep (se 2 (by rfl) ⟨342735, by rfl⟩ : syracuseStep 913961 = 685471) B685471
theorem B2053727 : Blo 607294 2053727 := bstep (se 1 (by rfl) ⟨1540295, by rfl⟩ : syracuseStep 2053727 = 3080591) B3080591
theorem B6340079 : Blo 607294 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B45678761 : Blo 607294 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B868763 : Blo 607294 868763 := bstep (se 1 (by rfl) ⟨651572, by rfl⟩ : syracuseStep 868763 = 1303145) B1303145
theorem B17154737 : Blo 607294 17154737 := bstep (se 2 (by rfl) ⟨6433026, by rfl⟩ : syracuseStep 17154737 = 12866053) B12866053
theorem B1369151 : Blo 607294 1369151 := bstep (se 1 (by rfl) ⟨1026863, by rfl⟩ : syracuseStep 1369151 = 2053727) B2053727
theorem B1461023 : Blo 607294 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B7039943 : Blo 607294 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B609307 : Blo 607294 609307 := bstep (se 1 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 609307 = 913961) B913961
theorem B3202149617 : Blo 607294 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B5188931 : Blo 607294 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B2469629 : Blo 607294 2469629 := bstep (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) B926111
theorem B1371995 : Blo 607294 1371995 := bstep (se 1 (by rfl) ⟨1028996, by rfl⟩ : syracuseStep 1371995 = 2057993) B2057993
theorem B15602057 : Blo 607294 15602057 := bstep (se 2 (by rfl) ⟨5850771, by rfl⟩ : syracuseStep 15602057 = 11701543) B11701543
theorem B3086099 : Blo 607294 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B16906877 : Blo 607294 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B1850921 : Blo 607294 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B11436491 : Blo 607294 11436491 := bstep (se 1 (by rfl) ⟨8577368, by rfl⟩ : syracuseStep 11436491 = 17154737) B17154737
theorem B2057399 : Blo 607294 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B3459287 : Blo 607294 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B30452507 : Blo 607294 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B912767 : Blo 607294 912767 := bstep (se 1 (by rfl) ⟨684575, by rfl⟩ : syracuseStep 912767 = 1369151) B1369151
theorem B2134766411 : Blo 607294 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B1233947 : Blo 607294 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B914663 : Blo 607294 914663 := bstep (se 1 (by rfl) ⟨685997, by rfl⟩ : syracuseStep 914663 = 1371995) B1371995
theorem B10401371 : Blo 607294 10401371 := bstep (se 1 (by rfl) ⟨7801028, by rfl⟩ : syracuseStep 10401371 = 15602057) B15602057
theorem B2316701 : Blo 607294 2316701 := bstep (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) B868763
theorem B11271251 : Blo 607294 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B974015 : Blo 607294 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B4693295 : Blo 607294 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B1646419 : Blo 607294 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B20301671 : Blo 607294 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B7514167 : Blo 607294 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B649343 : Blo 607294 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B608511 : Blo 607294 608511 := bstep (se 1 (by rfl) ⟨456383, by rfl⟩ : syracuseStep 608511 = 912767) B912767
theorem B822631 : Blo 607294 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B1371599 : Blo 607294 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B609775 : Blo 607294 609775 := bstep (se 1 (by rfl) ⟨457331, by rfl⟩ : syracuseStep 609775 = 914663) B914663
theorem B6934247 : Blo 607294 6934247 := bstep (se 1 (by rfl) ⟨5200685, by rfl⟩ : syracuseStep 6934247 = 10401371) B10401371
theorem B2306191 : Blo 607294 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B1544467 : Blo 607294 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B7624327 : Blo 607294 7624327 := bstep (se 1 (by rfl) ⟨5718245, by rfl⟩ : syracuseStep 7624327 = 11436491) B11436491
theorem B1423177607 : Blo 607294 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B3128863 : Blo 607294 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B2195225 : Blo 607294 2195225 := bstep (se 2 (by rfl) ⟨823209, by rfl⟩ : syracuseStep 2195225 = 1646419) B1646419
theorem B10018889 : Blo 607294 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B13534447 : Blo 607294 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B4171817 : Blo 607294 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B4622831 : Blo 607294 4622831 := bstep (se 1 (by rfl) ⟨3467123, by rfl⟩ : syracuseStep 4622831 = 6934247) B6934247
theorem B3074921 : Blo 607294 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B1731581 : Blo 607294 1731581 := bstep (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) B649343
theorem B2059289 : Blo 607294 2059289 := bstep (se 2 (by rfl) ⟨772233, by rfl⟩ : syracuseStep 2059289 = 1544467) B1544467
theorem B948785071 : Blo 607294 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B914399 : Blo 607294 914399 := bstep (se 1 (by rfl) ⟨685799, by rfl⟩ : syracuseStep 914399 = 1371599) B1371599
theorem B1463483 : Blo 607294 1463483 := bstep (se 1 (by rfl) ⟨1097612, by rfl⟩ : syracuseStep 1463483 = 2195225) B2195225
theorem B1096841 : Blo 607294 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B10165769 : Blo 607294 10165769 := bstep (se 2 (by rfl) ⟨3812163, by rfl⟩ : syracuseStep 10165769 = 7624327) B7624327
theorem B2924909 : Blo 607294 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B975655 : Blo 607294 975655 := bstep (se 1 (by rfl) ⟨731741, by rfl⟩ : syracuseStep 975655 = 1463483) B1463483
theorem B3081887 : Blo 607294 3081887 := bstep (se 1 (by rfl) ⟨2311415, by rfl⟩ : syracuseStep 3081887 = 4622831) B4622831
theorem B2049947 : Blo 607294 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B6777179 : Blo 607294 6777179 := bstep (se 1 (by rfl) ⟨5082884, by rfl⟩ : syracuseStep 6777179 = 10165769) B10165769
theorem B6679259 : Blo 607294 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B609599 : Blo 607294 609599 := bstep (se 1 (by rfl) ⟨457199, by rfl⟩ : syracuseStep 609599 = 914399) B914399
theorem B2781211 : Blo 607294 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B1372859 : Blo 607294 1372859 := bstep (se 1 (by rfl) ⟨1029644, by rfl⟩ : syracuseStep 1372859 = 2059289) B2059289
theorem B1265046761 : Blo 607294 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B18045929 : Blo 607294 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B1154387 : Blo 607294 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B1949939 : Blo 607294 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B4518119 : Blo 607294 4518119 := bstep (se 1 (by rfl) ⟨3388589, by rfl⟩ : syracuseStep 4518119 = 6777179) B6777179
theorem B4452839 : Blo 607294 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B12030619 : Blo 607294 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B3708281 : Blo 607294 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B915239 : Blo 607294 915239 := bstep (se 1 (by rfl) ⟨686429, by rfl⟩ : syracuseStep 915239 = 1372859) B1372859
theorem B843364507 : Blo 607294 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B1300873 : Blo 607294 1300873 := bstep (se 2 (by rfl) ⟨487827, by rfl⟩ : syracuseStep 1300873 = 975655) B975655
theorem B2054591 : Blo 607294 2054591 := bstep (se 1 (by rfl) ⟨1540943, by rfl⟩ : syracuseStep 2054591 = 3081887) B3081887
theorem B1366631 : Blo 607294 1366631 := bstep (se 1 (by rfl) ⟨1024973, by rfl⟩ : syracuseStep 1366631 = 2049947) B2049947
theorem B769591 : Blo 607294 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B16040825 : Blo 607294 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B9888749 : Blo 607294 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B1369727 : Blo 607294 1369727 := bstep (se 1 (by rfl) ⟨1027295, by rfl⟩ : syracuseStep 1369727 = 2054591) B2054591
theorem B911087 : Blo 607294 911087 := bstep (se 1 (by rfl) ⟨683315, by rfl⟩ : syracuseStep 911087 = 1366631) B1366631
theorem B1026121 : Blo 607294 1026121 := bstep (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) B769591
theorem B1124486009 : Blo 607294 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B2968559 : Blo 607294 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B610159 : Blo 607294 610159 := bstep (se 1 (by rfl) ⟨457619, by rfl⟩ : syracuseStep 610159 = 915239) B915239
theorem B3012079 : Blo 607294 3012079 := bstep (se 1 (by rfl) ⟨2259059, by rfl⟩ : syracuseStep 3012079 = 4518119) B4518119
theorem B1299959 : Blo 607294 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B1734497 : Blo 607294 1734497 := bstep (se 2 (by rfl) ⟨650436, by rfl⟩ : syracuseStep 1734497 = 1300873) B1300873
theorem B1368161 : Blo 607294 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B607391 : Blo 607294 607391 := bstep (se 1 (by rfl) ⟨455543, by rfl⟩ : syracuseStep 607391 = 911087) B911087
theorem B1156331 : Blo 607294 1156331 := bstep (se 1 (by rfl) ⟨867248, by rfl⟩ : syracuseStep 1156331 = 1734497) B1734497
theorem B4016105 : Blo 607294 4016105 := bstep (se 2 (by rfl) ⟨1506039, by rfl⟩ : syracuseStep 4016105 = 3012079) B3012079
theorem B10693883 : Blo 607294 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B913151 : Blo 607294 913151 := bstep (se 1 (by rfl) ⟨684863, by rfl⟩ : syracuseStep 913151 = 1369727) B1369727
theorem B1979039 : Blo 607294 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B6592499 : Blo 607294 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B866639 : Blo 607294 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B749657339 : Blo 607294 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B770887 : Blo 607294 770887 := bstep (se 1 (by rfl) ⟨578165, by rfl⟩ : syracuseStep 770887 = 1156331) B1156331
theorem B2311037 : Blo 607294 2311037 := bstep (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) B866639
theorem B5277437 : Blo 607294 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B499771559 : Blo 607294 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B608767 : Blo 607294 608767 := bstep (se 1 (by rfl) ⟨456575, by rfl⟩ : syracuseStep 608767 = 913151) B913151
theorem B912107 : Blo 607294 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B4394999 : Blo 607294 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B7129255 : Blo 607294 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B2677403 : Blo 607294 2677403 := bstep (se 1 (by rfl) ⟨2008052, by rfl⟩ : syracuseStep 2677403 = 4016105) B4016105
theorem B1540691 : Blo 607294 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B608071 : Blo 607294 608071 := bstep (se 1 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 608071 = 912107) B912107
theorem B9505673 : Blo 607294 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B1027849 : Blo 607294 1027849 := bstep (se 2 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 1027849 = 770887) B770887
theorem B3518291 : Blo 607294 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B333181039 : Blo 607294 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B11719997 : Blo 607294 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B1784935 : Blo 607294 1784935 := bstep (se 1 (by rfl) ⟨1338701, by rfl⟩ : syracuseStep 1784935 = 2677403) B2677403
theorem B9519653 : Blo 607294 9519653 := bstep (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) B1784935
theorem B1370465 : Blo 607294 1370465 := bstep (se 2 (by rfl) ⟨513924, by rfl⟩ : syracuseStep 1370465 = 1027849) B1027849
theorem B2345527 : Blo 607294 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B1027127 : Blo 607294 1027127 := bstep (se 1 (by rfl) ⟨770345, by rfl⟩ : syracuseStep 1027127 = 1540691) B1540691
theorem B6337115 : Blo 607294 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B444241385 : Blo 607294 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B7813331 : Blo 607294 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B296160923 : Blo 607294 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B913643 : Blo 607294 913643 := bstep (se 1 (by rfl) ⟨685232, by rfl⟩ : syracuseStep 913643 = 1370465) B1370465
theorem B684751 : Blo 607294 684751 := bstep (se 1 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 684751 = 1027127) B1027127
theorem B6346435 : Blo 607294 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B4224743 : Blo 607294 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B3127369 : Blo 607294 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B5208887 : Blo 607294 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B4169825 : Blo 607294 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B609095 : Blo 607294 609095 := bstep (se 1 (by rfl) ⟨456821, by rfl⟩ : syracuseStep 609095 = 913643) B913643
theorem B913001 : Blo 607294 913001 := bstep (se 2 (by rfl) ⟨342375, by rfl⟩ : syracuseStep 913001 = 684751) B684751
theorem B197440615 : Blo 607294 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B2816495 : Blo 607294 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B3472591 : Blo 607294 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B8461913 : Blo 607294 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B1877663 : Blo 607294 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B4630121 : Blo 607294 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B608667 : Blo 607294 608667 := bstep (se 1 (by rfl) ⟨456500, by rfl⟩ : syracuseStep 608667 = 913001) B913001
theorem B2779883 : Blo 607294 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B263254153 : Blo 607294 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B22565101 : Blo 607294 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B1853255 : Blo 607294 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B351005537 : Blo 607294 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B30086801 : Blo 607294 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B3086747 : Blo 607294 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B1251775 : Blo 607294 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B2057831 : Blo 607294 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B20057867 : Blo 607294 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B1669033 : Blo 607294 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B1235503 : Blo 607294 1235503 := bstep (se 1 (by rfl) ⟨926627, by rfl⟩ : syracuseStep 1235503 = 1853255) B1853255
theorem B234003691 : Blo 607294 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B13371911 : Blo 607294 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B6589349 : Blo 607294 6589349 := bstep (se 4 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 6589349 = 1235503) B1235503
theorem B1371887 : Blo 607294 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B312004921 : Blo 607294 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B2225377 : Blo 607294 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B416006561 : Blo 607294 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B8914607 : Blo 607294 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B4392899 : Blo 607294 4392899 := bstep (se 1 (by rfl) ⟨3294674, by rfl⟩ : syracuseStep 4392899 = 6589349) B6589349
theorem B914591 : Blo 607294 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B11868677 : Blo 607294 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B609727 : Blo 607294 609727 := bstep (se 1 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 609727 = 914591) B914591
theorem B5943071 : Blo 607294 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B2928599 : Blo 607294 2928599 := bstep (se 1 (by rfl) ⟨2196449, by rfl⟩ : syracuseStep 2928599 = 4392899) B4392899
theorem B1109350829 : Blo 607294 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B7912451 : Blo 607294 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B739567219 : Blo 607294 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B1952399 : Blo 607294 1952399 := bstep (se 1 (by rfl) ⟨1464299, by rfl⟩ : syracuseStep 1952399 = 2928599) B2928599
theorem B3962047 : Blo 607294 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B21099869 : Blo 607294 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B14066579 : Blo 607294 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B986089625 : Blo 607294 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B5282729 : Blo 607294 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B1301599 : Blo 607294 1301599 := bstep (se 1 (by rfl) ⟨976199, by rfl⟩ : syracuseStep 1301599 = 1952399) B1952399
theorem B657393083 : Blo 607294 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B1735465 : Blo 607294 1735465 := bstep (se 2 (by rfl) ⟨650799, by rfl⟩ : syracuseStep 1735465 = 1301599) B1301599
theorem B3521819 : Blo 607294 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B37510877 : Blo 607294 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B2313953 : Blo 607294 2313953 := bstep (se 2 (by rfl) ⟨867732, by rfl⟩ : syracuseStep 2313953 = 1735465) B1735465
theorem B100029005 : Blo 607294 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B2347879 : Blo 607294 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B438262055 : Blo 607294 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B3130505 : Blo 607294 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B1542635 : Blo 607294 1542635 := bstep (se 1 (by rfl) ⟨1156976, by rfl⟩ : syracuseStep 1542635 = 2313953) B2313953
theorem B66686003 : Blo 607294 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B292174703 : Blo 607294 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 607294 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B1028423 : Blo 607294 1028423 := bstep (se 1 (by rfl) ⟨771317, by rfl⟩ : syracuseStep 1028423 = 1542635) B1542635
theorem B2087003 : Blo 607294 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B44457335 : Blo 607294 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B5565341 : Blo 607294 5565341 := bstep (se 3 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 5565341 = 2087003) B2087003
theorem B685615 : Blo 607294 685615 := bstep (se 1 (by rfl) ⟨514211, by rfl⟩ : syracuseStep 685615 = 1028423) B1028423
theorem B29638223 : Blo 607294 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B519421693 : Blo 607294 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 607294 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B914153 : Blo 607294 914153 := bstep (se 2 (by rfl) ⟨342807, by rfl⟩ : syracuseStep 914153 = 685615) B685615
theorem B3710227 : Blo 607294 3710227 := bstep (se 1 (by rfl) ⟨2782670, by rfl⟩ : syracuseStep 3710227 = 5565341) B5565341
theorem B19758815 : Blo 607294 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B609435 : Blo 607294 609435 := bstep (se 1 (by rfl) ⟨457076, by rfl⟩ : syracuseStep 609435 = 914153) B914153
theorem B461708171 : Blo 607294 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B4946969 : Blo 607294 4946969 := bstep (se 2 (by rfl) ⟨1855113, by rfl⟩ : syracuseStep 4946969 = 3710227) B3710227
theorem B13172543 : Blo 607294 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B3297979 : Blo 607294 3297979 := bstep (se 1 (by rfl) ⟨2473484, by rfl⟩ : syracuseStep 3297979 = 4946969) B4946969
theorem B307805447 : Blo 607294 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B8781695 : Blo 607294 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B17589221 : Blo 607294 17589221 := bstep (se 4 (by rfl) ⟨1648989, by rfl⟩ : syracuseStep 17589221 = 3297979) B3297979
theorem B205203631 : Blo 607294 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B5854463 : Blo 607294 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B273604841 : Blo 607294 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B11726147 : Blo 607294 11726147 := bstep (se 1 (by rfl) ⟨8794610, by rfl⟩ : syracuseStep 11726147 = 17589221) B17589221
theorem B3902975 : Blo 607294 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B182403227 : Blo 607294 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B7817431 : Blo 607294 7817431 := bstep (se 1 (by rfl) ⟨5863073, by rfl⟩ : syracuseStep 7817431 = 11726147) B11726147
theorem B2601983 : Blo 607294 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B121602151 : Blo 607294 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B10423241 : Blo 607294 10423241 := bstep (se 2 (by rfl) ⟨3908715, by rfl⟩ : syracuseStep 10423241 = 7817431) B7817431
theorem B6938621 : Blo 607294 6938621 := bstep (se 3 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 6938621 = 2601983) B2601983
theorem B648544805 : Blo 607294 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B6948827 : Blo 607294 6948827 := bstep (se 1 (by rfl) ⟨5211620, by rfl⟩ : syracuseStep 6948827 = 10423241) B10423241
theorem B4625747 : Blo 607294 4625747 := bstep (se 1 (by rfl) ⟨3469310, by rfl⟩ : syracuseStep 4625747 = 6938621) B6938621
theorem B3083831 : Blo 607294 3083831 := bstep (se 1 (by rfl) ⟨2312873, by rfl⟩ : syracuseStep 3083831 = 4625747) B4625747
theorem B4632551 : Blo 607294 4632551 := bstep (se 1 (by rfl) ⟨3474413, by rfl⟩ : syracuseStep 4632551 = 6948827) B6948827
theorem B432363203 : Blo 607294 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 607294 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B2055887 : Blo 607294 2055887 := bstep (se 1 (by rfl) ⟨1541915, by rfl⟩ : syracuseStep 2055887 = 3083831) B3083831
theorem B3088367 : Blo 607294 3088367 := bstep (se 1 (by rfl) ⟨2316275, by rfl⟩ : syracuseStep 3088367 = 4632551) B4632551
theorem B192161423 : Blo 607294 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B1370591 : Blo 607294 1370591 := bstep (se 1 (by rfl) ⟨1027943, by rfl⟩ : syracuseStep 1370591 = 2055887) B2055887
theorem B2058911 : Blo 607294 2058911 := bstep (se 1 (by rfl) ⟨1544183, by rfl⟩ : syracuseStep 2058911 = 3088367) B3088367
theorem B128107615 : Blo 607294 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B913727 : Blo 607294 913727 := bstep (se 1 (by rfl) ⟨685295, by rfl⟩ : syracuseStep 913727 = 1370591) B1370591
theorem B1372607 : Blo 607294 1372607 := bstep (se 1 (by rfl) ⟨1029455, by rfl⟩ : syracuseStep 1372607 = 2058911) B2058911
theorem B609151 : Blo 607294 609151 := bstep (se 1 (by rfl) ⟨456863, by rfl⟩ : syracuseStep 609151 = 913727) B913727
theorem B915071 : Blo 607294 915071 := bstep (se 1 (by rfl) ⟨686303, by rfl⟩ : syracuseStep 915071 = 1372607) B1372607
theorem B170810153 : Blo 607294 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B610047 : Blo 607294 610047 := bstep (se 1 (by rfl) ⟨457535, by rfl⟩ : syracuseStep 610047 = 915071) B915071
theorem B113873435 : Blo 607294 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 607294 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 607294 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 607294 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 607294 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 607294 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 607294 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 607294 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 607294 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 607294 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 607294 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 607294 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 607294 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 607294 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 607294 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 607294 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 607294 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 607294 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 607294 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 607294 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 607294 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 607294 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B1948157 : Blo 607294 1948157 := bstep (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) B730559
theorem B1298771 : Blo 607294 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B865847 : Blo 607294 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B2308925 : Blo 607294 2308925 := bstep (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) B865847
theorem B1539283 : Blo 607294 1539283 := bstep (se 1 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 1539283 = 2308925) B2308925
theorem B2052377 : Blo 607294 2052377 := bstep (se 2 (by rfl) ⟨769641, by rfl⟩ : syracuseStep 2052377 = 1539283) B1539283
theorem B1368251 : Blo 607294 1368251 := bstep (se 1 (by rfl) ⟨1026188, by rfl⟩ : syracuseStep 1368251 = 2052377) B2052377
theorem B912167 : Blo 607294 912167 := bstep (se 1 (by rfl) ⟨684125, by rfl⟩ : syracuseStep 912167 = 1368251) B1368251
theorem B608111 : Blo 607294 608111 := bstep (se 1 (by rfl) ⟨456083, by rfl⟩ : syracuseStep 608111 = 912167) B912167

theorem C0 (j : ℕ) (h1 : 151823 ≤ j) (h2 : j ≤ 152522) : Blo 607294 (4 * j + 3) := by
  interval_cases j
  · exact B607295
  · exact B607299
  · exact B607303
  · exact B607307
  · exact B607311
  · exact B607315
  · exact B607319
  · exact B607323
  · exact B607327
  · exact B607331
  · exact B607335
  · exact B607339
  · exact B607343
  · exact B607347
  · exact B607351
  · exact B607355
  · exact B607359
  · exact B607363
  · exact B607367
  · exact B607371
  · exact B607375
  · exact B607379
  · exact B607383
  · exact B607387
  · exact B607391
  · exact B607395
  · exact B607399
  · exact B607403
  · exact B607407
  · exact B607411
  · exact B607415
  · exact B607419
  · exact B607423
  · exact B607427
  · exact B607431
  · exact B607435
  · exact B607439
  · exact B607443
  · exact B607447
  · exact B607451
  · exact B607455
  · exact B607459
  · exact B607463
  · exact B607467
  · exact B607471
  · exact B607475
  · exact B607479
  · exact B607483
  · exact B607487
  · exact B607491
  · exact B607495
  · exact B607499
  · exact B607503
  · exact B607507
  · exact B607511
  · exact B607515
  · exact B607519
  · exact B607523
  · exact B607527
  · exact B607531
  · exact B607535
  · exact B607539
  · exact B607543
  · exact B607547
  · exact B607551
  · exact B607555
  · exact B607559
  · exact B607563
  · exact B607567
  · exact B607571
  · exact B607575
  · exact B607579
  · exact B607583
  · exact B607587
  · exact B607591
  · exact B607595
  · exact B607599
  · exact B607603
  · exact B607607
  · exact B607611
  · exact B607615
  · exact B607619
  · exact B607623
  · exact B607627
  · exact B607631
  · exact B607635
  · exact B607639
  · exact B607643
  · exact B607647
  · exact B607651
  · exact B607655
  · exact B607659
  · exact B607663
  · exact B607667
  · exact B607671
  · exact B607675
  · exact B607679
  · exact B607683
  · exact B607687
  · exact B607691
  · exact B607695
  · exact B607699
  · exact B607703
  · exact B607707
  · exact B607711
  · exact B607715
  · exact B607719
  · exact B607723
  · exact B607727
  · exact B607731
  · exact B607735
  · exact B607739
  · exact B607743
  · exact B607747
  · exact B607751
  · exact B607755
  · exact B607759
  · exact B607763
  · exact B607767
  · exact B607771
  · exact B607775
  · exact B607779
  · exact B607783
  · exact B607787
  · exact B607791
  · exact B607795
  · exact B607799
  · exact B607803
  · exact B607807
  · exact B607811
  · exact B607815
  · exact B607819
  · exact B607823
  · exact B607827
  · exact B607831
  · exact B607835
  · exact B607839
  · exact B607843
  · exact B607847
  · exact B607851
  · exact B607855
  · exact B607859
  · exact B607863
  · exact B607867
  · exact B607871
  · exact B607875
  · exact B607879
  · exact B607883
  · exact B607887
  · exact B607891
  · exact B607895
  · exact B607899
  · exact B607903
  · exact B607907
  · exact B607911
  · exact B607915
  · exact B607919
  · exact B607923
  · exact B607927
  · exact B607931
  · exact B607935
  · exact B607939
  · exact B607943
  · exact B607947
  · exact B607951
  · exact B607955
  · exact B607959
  · exact B607963
  · exact B607967
  · exact B607971
  · exact B607975
  · exact B607979
  · exact B607983
  · exact B607987
  · exact B607991
  · exact B607995
  · exact B607999
  · exact B608003
  · exact B608007
  · exact B608011
  · exact B608015
  · exact B608019
  · exact B608023
  · exact B608027
  · exact B608031
  · exact B608035
  · exact B608039
  · exact B608043
  · exact B608047
  · exact B608051
  · exact B608055
  · exact B608059
  · exact B608063
  · exact B608067
  · exact B608071
  · exact B608075
  · exact B608079
  · exact B608083
  · exact B608087
  · exact B608091
  · exact B608095
  · exact B608099
  · exact B608103
  · exact B608107
  · exact B608111
  · exact B608115
  · exact B608119
  · exact B608123
  · exact B608127
  · exact B608131
  · exact B608135
  · exact B608139
  · exact B608143
  · exact B608147
  · exact B608151
  · exact B608155
  · exact B608159
  · exact B608163
  · exact B608167
  · exact B608171
  · exact B608175
  · exact B608179
  · exact B608183
  · exact B608187
  · exact B608191
  · exact B608195
  · exact B608199
  · exact B608203
  · exact B608207
  · exact B608211
  · exact B608215
  · exact B608219
  · exact B608223
  · exact B608227
  · exact B608231
  · exact B608235
  · exact B608239
  · exact B608243
  · exact B608247
  · exact B608251
  · exact B608255
  · exact B608259
  · exact B608263
  · exact B608267
  · exact B608271
  · exact B608275
  · exact B608279
  · exact B608283
  · exact B608287
  · exact B608291
  · exact B608295
  · exact B608299
  · exact B608303
  · exact B608307
  · exact B608311
  · exact B608315
  · exact B608319
  · exact B608323
  · exact B608327
  · exact B608331
  · exact B608335
  · exact B608339
  · exact B608343
  · exact B608347
  · exact B608351
  · exact B608355
  · exact B608359
  · exact B608363
  · exact B608367
  · exact B608371
  · exact B608375
  · exact B608379
  · exact B608383
  · exact B608387
  · exact B608391
  · exact B608395
  · exact B608399
  · exact B608403
  · exact B608407
  · exact B608411
  · exact B608415
  · exact B608419
  · exact B608423
  · exact B608427
  · exact B608431
  · exact B608435
  · exact B608439
  · exact B608443
  · exact B608447
  · exact B608451
  · exact B608455
  · exact B608459
  · exact B608463
  · exact B608467
  · exact B608471
  · exact B608475
  · exact B608479
  · exact B608483
  · exact B608487
  · exact B608491
  · exact B608495
  · exact B608499
  · exact B608503
  · exact B608507
  · exact B608511
  · exact B608515
  · exact B608519
  · exact B608523
  · exact B608527
  · exact B608531
  · exact B608535
  · exact B608539
  · exact B608543
  · exact B608547
  · exact B608551
  · exact B608555
  · exact B608559
  · exact B608563
  · exact B608567
  · exact B608571
  · exact B608575
  · exact B608579
  · exact B608583
  · exact B608587
  · exact B608591
  · exact B608595
  · exact B608599
  · exact B608603
  · exact B608607
  · exact B608611
  · exact B608615
  · exact B608619
  · exact B608623
  · exact B608627
  · exact B608631
  · exact B608635
  · exact B608639
  · exact B608643
  · exact B608647
  · exact B608651
  · exact B608655
  · exact B608659
  · exact B608663
  · exact B608667
  · exact B608671
  · exact B608675
  · exact B608679
  · exact B608683
  · exact B608687
  · exact B608691
  · exact B608695
  · exact B608699
  · exact B608703
  · exact B608707
  · exact B608711
  · exact B608715
  · exact B608719
  · exact B608723
  · exact B608727
  · exact B608731
  · exact B608735
  · exact B608739
  · exact B608743
  · exact B608747
  · exact B608751
  · exact B608755
  · exact B608759
  · exact B608763
  · exact B608767
  · exact B608771
  · exact B608775
  · exact B608779
  · exact B608783
  · exact B608787
  · exact B608791
  · exact B608795
  · exact B608799
  · exact B608803
  · exact B608807
  · exact B608811
  · exact B608815
  · exact B608819
  · exact B608823
  · exact B608827
  · exact B608831
  · exact B608835
  · exact B608839
  · exact B608843
  · exact B608847
  · exact B608851
  · exact B608855
  · exact B608859
  · exact B608863
  · exact B608867
  · exact B608871
  · exact B608875
  · exact B608879
  · exact B608883
  · exact B608887
  · exact B608891
  · exact B608895
  · exact B608899
  · exact B608903
  · exact B608907
  · exact B608911
  · exact B608915
  · exact B608919
  · exact B608923
  · exact B608927
  · exact B608931
  · exact B608935
  · exact B608939
  · exact B608943
  · exact B608947
  · exact B608951
  · exact B608955
  · exact B608959
  · exact B608963
  · exact B608967
  · exact B608971
  · exact B608975
  · exact B608979
  · exact B608983
  · exact B608987
  · exact B608991
  · exact B608995
  · exact B608999
  · exact B609003
  · exact B609007
  · exact B609011
  · exact B609015
  · exact B609019
  · exact B609023
  · exact B609027
  · exact B609031
  · exact B609035
  · exact B609039
  · exact B609043
  · exact B609047
  · exact B609051
  · exact B609055
  · exact B609059
  · exact B609063
  · exact B609067
  · exact B609071
  · exact B609075
  · exact B609079
  · exact B609083
  · exact B609087
  · exact B609091
  · exact B609095
  · exact B609099
  · exact B609103
  · exact B609107
  · exact B609111
  · exact B609115
  · exact B609119
  · exact B609123
  · exact B609127
  · exact B609131
  · exact B609135
  · exact B609139
  · exact B609143
  · exact B609147
  · exact B609151
  · exact B609155
  · exact B609159
  · exact B609163
  · exact B609167
  · exact B609171
  · exact B609175
  · exact B609179
  · exact B609183
  · exact B609187
  · exact B609191
  · exact B609195
  · exact B609199
  · exact B609203
  · exact B609207
  · exact B609211
  · exact B609215
  · exact B609219
  · exact B609223
  · exact B609227
  · exact B609231
  · exact B609235
  · exact B609239
  · exact B609243
  · exact B609247
  · exact B609251
  · exact B609255
  · exact B609259
  · exact B609263
  · exact B609267
  · exact B609271
  · exact B609275
  · exact B609279
  · exact B609283
  · exact B609287
  · exact B609291
  · exact B609295
  · exact B609299
  · exact B609303
  · exact B609307
  · exact B609311
  · exact B609315
  · exact B609319
  · exact B609323
  · exact B609327
  · exact B609331
  · exact B609335
  · exact B609339
  · exact B609343
  · exact B609347
  · exact B609351
  · exact B609355
  · exact B609359
  · exact B609363
  · exact B609367
  · exact B609371
  · exact B609375
  · exact B609379
  · exact B609383
  · exact B609387
  · exact B609391
  · exact B609395
  · exact B609399
  · exact B609403
  · exact B609407
  · exact B609411
  · exact B609415
  · exact B609419
  · exact B609423
  · exact B609427
  · exact B609431
  · exact B609435
  · exact B609439
  · exact B609443
  · exact B609447
  · exact B609451
  · exact B609455
  · exact B609459
  · exact B609463
  · exact B609467
  · exact B609471
  · exact B609475
  · exact B609479
  · exact B609483
  · exact B609487
  · exact B609491
  · exact B609495
  · exact B609499
  · exact B609503
  · exact B609507
  · exact B609511
  · exact B609515
  · exact B609519
  · exact B609523
  · exact B609527
  · exact B609531
  · exact B609535
  · exact B609539
  · exact B609543
  · exact B609547
  · exact B609551
  · exact B609555
  · exact B609559
  · exact B609563
  · exact B609567
  · exact B609571
  · exact B609575
  · exact B609579
  · exact B609583
  · exact B609587
  · exact B609591
  · exact B609595
  · exact B609599
  · exact B609603
  · exact B609607
  · exact B609611
  · exact B609615
  · exact B609619
  · exact B609623
  · exact B609627
  · exact B609631
  · exact B609635
  · exact B609639
  · exact B609643
  · exact B609647
  · exact B609651
  · exact B609655
  · exact B609659
  · exact B609663
  · exact B609667
  · exact B609671
  · exact B609675
  · exact B609679
  · exact B609683
  · exact B609687
  · exact B609691
  · exact B609695
  · exact B609699
  · exact B609703
  · exact B609707
  · exact B609711
  · exact B609715
  · exact B609719
  · exact B609723
  · exact B609727
  · exact B609731
  · exact B609735
  · exact B609739
  · exact B609743
  · exact B609747
  · exact B609751
  · exact B609755
  · exact B609759
  · exact B609763
  · exact B609767
  · exact B609771
  · exact B609775
  · exact B609779
  · exact B609783
  · exact B609787
  · exact B609791
  · exact B609795
  · exact B609799
  · exact B609803
  · exact B609807
  · exact B609811
  · exact B609815
  · exact B609819
  · exact B609823
  · exact B609827
  · exact B609831
  · exact B609835
  · exact B609839
  · exact B609843
  · exact B609847
  · exact B609851
  · exact B609855
  · exact B609859
  · exact B609863
  · exact B609867
  · exact B609871
  · exact B609875
  · exact B609879
  · exact B609883
  · exact B609887
  · exact B609891
  · exact B609895
  · exact B609899
  · exact B609903
  · exact B609907
  · exact B609911
  · exact B609915
  · exact B609919
  · exact B609923
  · exact B609927
  · exact B609931
  · exact B609935
  · exact B609939
  · exact B609943
  · exact B609947
  · exact B609951
  · exact B609955
  · exact B609959
  · exact B609963
  · exact B609967
  · exact B609971
  · exact B609975
  · exact B609979
  · exact B609983
  · exact B609987
  · exact B609991
  · exact B609995
  · exact B609999
  · exact B610003
  · exact B610007
  · exact B610011
  · exact B610015
  · exact B610019
  · exact B610023
  · exact B610027
  · exact B610031
  · exact B610035
  · exact B610039
  · exact B610043
  · exact B610047
  · exact B610051
  · exact B610055
  · exact B610059
  · exact B610063
  · exact B610067
  · exact B610071
  · exact B610075
  · exact B610079
  · exact B610083
  · exact B610087
  · exact B610091

theorem C1 (j : ℕ) (h1 : 152523 ≤ j) (h2 : j ≤ 152572) : Blo 607294 (4 * j + 3) := by
  interval_cases j
  · exact B610095
  · exact B610099
  · exact B610103
  · exact B610107
  · exact B610111
  · exact B610115
  · exact B610119
  · exact B610123
  · exact B610127
  · exact B610131
  · exact B610135
  · exact B610139
  · exact B610143
  · exact B610147
  · exact B610151
  · exact B610155
  · exact B610159
  · exact B610163
  · exact B610167
  · exact B610171
  · exact B610175
  · exact B610179
  · exact B610183
  · exact B610187
  · exact B610191
  · exact B610195
  · exact B610199
  · exact B610203
  · exact B610207
  · exact B610211
  · exact B610215
  · exact B610219
  · exact B610223
  · exact B610227
  · exact B610231
  · exact B610235
  · exact B610239
  · exact B610243
  · exact B610247
  · exact B610251
  · exact B610255
  · exact B610259
  · exact B610263
  · exact B610267
  · exact B610271
  · exact B610275
  · exact B610279
  · exact B610283
  · exact B610287
  · exact B610291

theorem solution (m : ℕ) (hlo : 607294 ≤ m) (hhi : m ≤ 610294) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 151823 ≤ j := by omega
    have hj2 : j ≤ 152572 := by omega
    have hb : Blo 607294 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 152523 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
