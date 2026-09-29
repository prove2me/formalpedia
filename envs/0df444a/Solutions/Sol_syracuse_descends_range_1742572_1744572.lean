-- Prove2me | solution 1 for syracuse_descends_range_1742572_1744572
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:34:38.208758+00:00
-- url     : https://prove2.me/submissions/7fee5c24-8e8d-4b25-9464-c8a40fc8653f

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


theorem B2940941 : Blo 1742572 2940941 := bbase (se 3 (by rfl) ⟨551426, by rfl⟩ : syracuseStep 2940941 = 1102853) (by norm_num)
theorem B3923981 : Blo 1742572 3923981 := bbase (se 3 (by rfl) ⟨735746, by rfl⟩ : syracuseStep 3923981 = 1471493) (by norm_num)
theorem B3309653 : Blo 1742572 3309653 := bbase (se 8 (by rfl) ⟨19392, by rfl⟩ : syracuseStep 3309653 = 38785) (by norm_num)
theorem B3924053 : Blo 1742572 3924053 := bbase (se 8 (by rfl) ⟨22992, by rfl⟩ : syracuseStep 3924053 = 45985) (by norm_num)
theorem B4415573 : Blo 1742572 4415573 := bbase (se 8 (by rfl) ⟨25872, by rfl⟩ : syracuseStep 4415573 = 51745) (by norm_num)
theorem B2941069 : Blo 1742572 2941069 := bbase (se 3 (by rfl) ⟨551450, by rfl⟩ : syracuseStep 2941069 = 1102901) (by norm_num)
theorem B3924125 : Blo 1742572 3924125 := bbase (se 3 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 3924125 = 1471547) (by norm_num)
theorem B12574901 : Blo 1742572 12574901 := bbase (se 5 (by rfl) ⟨589448, by rfl⟩ : syracuseStep 12574901 = 1178897) (by norm_num)
theorem B2941157 : Blo 1742572 2941157 := bbase (se 4 (by rfl) ⟨275733, by rfl⟩ : syracuseStep 2941157 = 551467) (by norm_num)
theorem B4964581 : Blo 1742572 4964581 := bbase (se 4 (by rfl) ⟨465429, by rfl⟩ : syracuseStep 4964581 = 930859) (by norm_num)
theorem B3309797 : Blo 1742572 3309797 := bbase (se 4 (by rfl) ⟨310293, by rfl⟩ : syracuseStep 3309797 = 620587) (by norm_num)
theorem B3924197 : Blo 1742572 3924197 := bbase (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) (by norm_num)
theorem B16761077 : Blo 1742572 16761077 := bbase (se 5 (by rfl) ⟨785675, by rfl⟩ : syracuseStep 16761077 = 1571351) (by norm_num)
theorem B3924269 : Blo 1742572 3924269 := bbase (se 3 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 3924269 = 1471601) (by norm_num)
theorem B5882165 : Blo 1742572 5882165 := bbase (se 5 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 5882165 = 551453) (by norm_num)
theorem B2941285 : Blo 1742572 2941285 := bbase (se 4 (by rfl) ⟨275745, by rfl⟩ : syracuseStep 2941285 = 551491) (by norm_num)
theorem B3924341 : Blo 1742572 3924341 := bbase (se 5 (by rfl) ⟨183953, by rfl⟩ : syracuseStep 3924341 = 367907) (by norm_num)
theorem B3023237 : Blo 1742572 3023237 := bbase (se 4 (by rfl) ⟨283428, by rfl⟩ : syracuseStep 3023237 = 566857) (by norm_num)
theorem B4415917 : Blo 1742572 4415917 := bbase (se 3 (by rfl) ⟨827984, by rfl⟩ : syracuseStep 4415917 = 1655969) (by norm_num)
theorem B9929141 : Blo 1742572 9929141 := bbase (se 5 (by rfl) ⟨465428, by rfl⟩ : syracuseStep 9929141 = 930857) (by norm_num)
theorem B13246901 : Blo 1742572 13246901 := bbase (se 5 (by rfl) ⟨620948, by rfl⟩ : syracuseStep 13246901 = 1241897) (by norm_num)
theorem B2941373 : Blo 1742572 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B3924413 : Blo 1742572 3924413 := bbase (se 3 (by rfl) ⟨735827, by rfl⟩ : syracuseStep 3924413 = 1471655) (by norm_num)
theorem B8831429 : Blo 1742572 8831429 := bbase (se 4 (by rfl) ⟨827946, by rfl⟩ : syracuseStep 8831429 = 1655893) (by norm_num)
theorem B3310085 : Blo 1742572 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B3924485 : Blo 1742572 3924485 := bbase (se 4 (by rfl) ⟨367920, by rfl⟩ : syracuseStep 3924485 = 735841) (by norm_num)
theorem B2482741 : Blo 1742572 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B2941501 : Blo 1742572 2941501 := bbase (se 3 (by rfl) ⟨551531, by rfl⟩ : syracuseStep 2941501 = 1103063) (by norm_num)
theorem B2122309 : Blo 1742572 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B2982469 : Blo 1742572 2982469 := bbase (se 4 (by rfl) ⟨279606, by rfl⟩ : syracuseStep 2982469 = 559213) (by norm_num)
theorem B3924557 : Blo 1742572 3924557 := bbase (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) (by norm_num)
theorem B2613869 : Blo 1742572 2613869 := bbase (se 3 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 2613869 = 980201) (by norm_num)
theorem B2613893 : Blo 1742572 2613893 := bbase (se 4 (by rfl) ⟨245052, by rfl⟩ : syracuseStep 2613893 = 490105) (by norm_num)
theorem B2941589 : Blo 1742572 2941589 := bbase (se 6 (by rfl) ⟨68943, by rfl⟩ : syracuseStep 2941589 = 137887) (by norm_num)
theorem B3924629 : Blo 1742572 3924629 := bbase (se 6 (by rfl) ⟨91983, by rfl⟩ : syracuseStep 3924629 = 183967) (by norm_num)
theorem B2613917 : Blo 1742572 2613917 := bbase (se 3 (by rfl) ⟨490109, by rfl⟩ : syracuseStep 2613917 = 980219) (by norm_num)
theorem B3310237 : Blo 1742572 3310237 := bbase (se 3 (by rfl) ⟨620669, by rfl⟩ : syracuseStep 3310237 = 1241339) (by norm_num)
theorem B2613941 : Blo 1742572 2613941 := bbase (se 5 (by rfl) ⟨122528, by rfl⟩ : syracuseStep 2613941 = 245057) (by norm_num)
theorem B2613965 : Blo 1742572 2613965 := bbase (se 3 (by rfl) ⟨490118, by rfl⟩ : syracuseStep 2613965 = 980237) (by norm_num)
theorem B3924701 : Blo 1742572 3924701 := bbase (se 3 (by rfl) ⟨735881, by rfl⟩ : syracuseStep 3924701 = 1471763) (by norm_num)
theorem B2613989 : Blo 1742572 2613989 := bbase (se 4 (by rfl) ⟨245061, by rfl⟩ : syracuseStep 2613989 = 490123) (by norm_num)
theorem B5882597 : Blo 1742572 5882597 := bbase (se 4 (by rfl) ⟨551493, by rfl⟩ : syracuseStep 5882597 = 1102987) (by norm_num)
theorem B2237161 : Blo 1742572 2237161 := bbase (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) (by norm_num)
theorem B2614013 : Blo 1742572 2614013 := bbase (se 3 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 2614013 = 980255) (by norm_num)
theorem B5587717 : Blo 1742572 5587717 := bbase (se 4 (by rfl) ⟨523848, by rfl⟩ : syracuseStep 5587717 = 1047697) (by norm_num)
theorem B2614037 : Blo 1742572 2614037 := bbase (se 6 (by rfl) ⟨61266, by rfl⟩ : syracuseStep 2614037 = 122533) (by norm_num)
theorem B2941717 : Blo 1742572 2941717 := bbase (se 6 (by rfl) ⟨68946, by rfl⟩ : syracuseStep 2941717 = 137893) (by norm_num)
theorem B3924773 : Blo 1742572 3924773 := bbase (se 4 (by rfl) ⟨367947, by rfl⟩ : syracuseStep 3924773 = 735895) (by norm_num)
theorem B2614061 : Blo 1742572 2614061 := bbase (se 3 (by rfl) ⟨490136, by rfl⟩ : syracuseStep 2614061 = 980273) (by norm_num)
theorem B2868029 : Blo 1742572 2868029 := bbase (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) (by norm_num)
theorem B2614085 : Blo 1742572 2614085 := bbase (se 4 (by rfl) ⟨245070, by rfl⟩ : syracuseStep 2614085 = 490141) (by norm_num)
theorem B13239125 : Blo 1742572 13239125 := bbase (se 9 (by rfl) ⟨38786, by rfl⟩ : syracuseStep 13239125 = 77573) (by norm_num)
theorem B2614109 : Blo 1742572 2614109 := bbase (se 3 (by rfl) ⟨490145, by rfl⟩ : syracuseStep 2614109 = 980291) (by norm_num)
theorem B2794333 : Blo 1742572 2794333 := bbase (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) (by norm_num)
theorem B8823653 : Blo 1742572 8823653 := bbase (se 4 (by rfl) ⟨827217, by rfl⟩ : syracuseStep 8823653 = 1654435) (by norm_num)
theorem B2941805 : Blo 1742572 2941805 := bbase (se 3 (by rfl) ⟨551588, by rfl⟩ : syracuseStep 2941805 = 1103177) (by norm_num)
theorem B3924845 : Blo 1742572 3924845 := bbase (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) (by norm_num)
theorem B2614133 : Blo 1742572 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B14140277 : Blo 1742572 14140277 := bbase (se 5 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 14140277 = 1325651) (by norm_num)
theorem B2483077 : Blo 1742572 2483077 := bbase (se 4 (by rfl) ⟨232788, by rfl⟩ : syracuseStep 2483077 = 465577) (by norm_num)
theorem B2614157 : Blo 1742572 2614157 := bbase (se 3 (by rfl) ⟨490154, by rfl⟩ : syracuseStep 2614157 = 980309) (by norm_num)
theorem B2614181 : Blo 1742572 2614181 := bbase (se 4 (by rfl) ⟨245079, by rfl⟩ : syracuseStep 2614181 = 490159) (by norm_num)
theorem B3924917 : Blo 1742572 3924917 := bbase (se 5 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 3924917 = 367961) (by norm_num)
theorem B2614205 : Blo 1742572 2614205 := bbase (se 3 (by rfl) ⟨490163, by rfl⟩ : syracuseStep 2614205 = 980327) (by norm_num)
theorem B3310541 : Blo 1742572 3310541 := bbase (se 3 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 3310541 = 1241453) (by norm_num)
theorem B2614229 : Blo 1742572 2614229 := bbase (se 7 (by rfl) ⟨30635, by rfl⟩ : syracuseStep 2614229 = 61271) (by norm_num)
theorem B2614253 : Blo 1742572 2614253 := bbase (se 3 (by rfl) ⟨490172, by rfl⟩ : syracuseStep 2614253 = 980345) (by norm_num)
theorem B2941933 : Blo 1742572 2941933 := bbase (se 3 (by rfl) ⟨551612, by rfl⟩ : syracuseStep 2941933 = 1103225) (by norm_num)
theorem B3924989 : Blo 1742572 3924989 := bbase (se 3 (by rfl) ⟨735935, by rfl⟩ : syracuseStep 3924989 = 1471871) (by norm_num)
theorem B2614277 : Blo 1742572 2614277 := bbase (se 4 (by rfl) ⟨245088, by rfl⟩ : syracuseStep 2614277 = 490177) (by norm_num)
theorem B2614301 : Blo 1742572 2614301 := bbase (se 3 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 2614301 = 980363) (by norm_num)
theorem B2614325 : Blo 1742572 2614325 := bbase (se 5 (by rfl) ⟨122546, by rfl⟩ : syracuseStep 2614325 = 245093) (by norm_num)
theorem B7070773 : Blo 1742572 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B2942021 : Blo 1742572 2942021 := bbase (se 4 (by rfl) ⟨275814, by rfl⟩ : syracuseStep 2942021 = 551629) (by norm_num)
theorem B3925061 : Blo 1742572 3925061 := bbase (se 4 (by rfl) ⟨367974, by rfl⟩ : syracuseStep 3925061 = 735949) (by norm_num)
theorem B2614349 : Blo 1742572 2614349 := bbase (se 3 (by rfl) ⟨490190, by rfl⟩ : syracuseStep 2614349 = 980381) (by norm_num)
theorem B2483293 : Blo 1742572 2483293 := bbase (se 3 (by rfl) ⟨465617, by rfl⟩ : syracuseStep 2483293 = 931235) (by norm_num)
theorem B2614373 : Blo 1742572 2614373 := bbase (se 4 (by rfl) ⟨245097, by rfl⟩ : syracuseStep 2614373 = 490195) (by norm_num)
theorem B5031013 : Blo 1742572 5031013 := bbase (se 4 (by rfl) ⟨471657, by rfl⟩ : syracuseStep 5031013 = 943315) (by norm_num)
theorem B2614397 : Blo 1742572 2614397 := bbase (se 3 (by rfl) ⟨490199, by rfl⟩ : syracuseStep 2614397 = 980399) (by norm_num)
theorem B3925133 : Blo 1742572 3925133 := bbase (se 3 (by rfl) ⟨735962, by rfl⟩ : syracuseStep 3925133 = 1471925) (by norm_num)
theorem B2614421 : Blo 1742572 2614421 := bbase (se 6 (by rfl) ⟨61275, by rfl⟩ : syracuseStep 2614421 = 122551) (by norm_num)
theorem B5883029 : Blo 1742572 5883029 := bbase (se 6 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 5883029 = 275767) (by norm_num)
theorem B2614445 : Blo 1742572 2614445 := bbase (se 3 (by rfl) ⟨490208, by rfl⟩ : syracuseStep 2614445 = 980417) (by norm_num)
theorem B2614469 : Blo 1742572 2614469 := bbase (se 4 (by rfl) ⟨245106, by rfl⟩ : syracuseStep 2614469 = 490213) (by norm_num)
theorem B2942149 : Blo 1742572 2942149 := bbase (se 4 (by rfl) ⟨275826, by rfl⟩ : syracuseStep 2942149 = 551653) (by norm_num)
theorem B3925205 : Blo 1742572 3925205 := bbase (se 7 (by rfl) ⟨45998, by rfl⟩ : syracuseStep 3925205 = 91997) (by norm_num)
theorem B2614493 : Blo 1742572 2614493 := bbase (se 3 (by rfl) ⟨490217, by rfl⟩ : syracuseStep 2614493 = 980435) (by norm_num)
theorem B2614517 : Blo 1742572 2614517 := bbase (se 5 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 2614517 = 245111) (by norm_num)
theorem B4187405 : Blo 1742572 4187405 := bbase (se 3 (by rfl) ⟨785138, by rfl⟩ : syracuseStep 4187405 = 1570277) (by norm_num)
theorem B2614541 : Blo 1742572 2614541 := bbase (se 3 (by rfl) ⟨490226, by rfl⟩ : syracuseStep 2614541 = 980453) (by norm_num)
theorem B2123029 : Blo 1742572 2123029 := bbase (se 6 (by rfl) ⟨49758, by rfl⟩ : syracuseStep 2123029 = 99517) (by norm_num)
theorem B2942237 : Blo 1742572 2942237 := bbase (se 3 (by rfl) ⟨551669, by rfl⟩ : syracuseStep 2942237 = 1103339) (by norm_num)
theorem B3925277 : Blo 1742572 3925277 := bbase (se 3 (by rfl) ⟨735989, by rfl⟩ : syracuseStep 3925277 = 1471979) (by norm_num)
theorem B2614565 : Blo 1742572 2614565 := bbase (se 4 (by rfl) ⟨245115, by rfl⟩ : syracuseStep 2614565 = 490231) (by norm_num)
theorem B2614589 : Blo 1742572 2614589 := bbase (se 3 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 2614589 = 980471) (by norm_num)
theorem B1860941 : Blo 1742572 1860941 := bbase (se 3 (by rfl) ⟨348926, by rfl⟩ : syracuseStep 1860941 = 697853) (by norm_num)
theorem B2614613 : Blo 1742572 2614613 := bbase (se 12 (by rfl) ⟨957, by rfl⟩ : syracuseStep 2614613 = 1915) (by norm_num)
theorem B12739925 : Blo 1742572 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B2614637 : Blo 1742572 2614637 := bbase (se 3 (by rfl) ⟨490244, by rfl⟩ : syracuseStep 2614637 = 980489) (by norm_num)
theorem B2614661 : Blo 1742572 2614661 := bbase (se 4 (by rfl) ⟨245124, by rfl⟩ : syracuseStep 2614661 = 490249) (by norm_num)
theorem B16983445 : Blo 1742572 16983445 := bbase (se 6 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 16983445 = 796099) (by norm_num)
theorem B2614685 : Blo 1742572 2614685 := bbase (se 3 (by rfl) ⟨490253, by rfl⟩ : syracuseStep 2614685 = 980507) (by norm_num)
theorem B2942365 : Blo 1742572 2942365 := bbase (se 3 (by rfl) ⟨551693, by rfl⟩ : syracuseStep 2942365 = 1103387) (by norm_num)
theorem B2614709 : Blo 1742572 2614709 := bbase (se 5 (by rfl) ⟨122564, by rfl⟩ : syracuseStep 2614709 = 245129) (by norm_num)
theorem B2614733 : Blo 1742572 2614733 := bbase (se 3 (by rfl) ⟨490262, by rfl⟩ : syracuseStep 2614733 = 980525) (by norm_num)
theorem B2483669 : Blo 1742572 2483669 := bbase (se 7 (by rfl) ⟨29105, by rfl⟩ : syracuseStep 2483669 = 58211) (by norm_num)
theorem B2614757 : Blo 1742572 2614757 := bbase (se 4 (by rfl) ⟨245133, by rfl⟩ : syracuseStep 2614757 = 490267) (by norm_num)
theorem B2942453 : Blo 1742572 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B2614781 : Blo 1742572 2614781 := bbase (se 3 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 2614781 = 980543) (by norm_num)
theorem B3581453 : Blo 1742572 3581453 := bbase (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) (by norm_num)
theorem B2614805 : Blo 1742572 2614805 := bbase (se 6 (by rfl) ⟨61284, by rfl⟩ : syracuseStep 2614805 = 122569) (by norm_num)
theorem B2614829 : Blo 1742572 2614829 := bbase (se 3 (by rfl) ⟨490280, by rfl⟩ : syracuseStep 2614829 = 980561) (by norm_num)
theorem B2614853 : Blo 1742572 2614853 := bbase (se 4 (by rfl) ⟨245142, by rfl⟩ : syracuseStep 2614853 = 490285) (by norm_num)
theorem B5883461 : Blo 1742572 5883461 := bbase (se 4 (by rfl) ⟨551574, by rfl⟩ : syracuseStep 5883461 = 1103149) (by norm_num)
theorem B8382037 : Blo 1742572 8382037 := bbase (se 8 (by rfl) ⟨49113, by rfl⟩ : syracuseStep 8382037 = 98227) (by norm_num)
theorem B2614877 : Blo 1742572 2614877 := bbase (se 3 (by rfl) ⟨490289, by rfl⟩ : syracuseStep 2614877 = 980579) (by norm_num)
theorem B2614901 : Blo 1742572 2614901 := bbase (se 5 (by rfl) ⟨122573, by rfl⟩ : syracuseStep 2614901 = 245147) (by norm_num)
theorem B2942581 : Blo 1742572 2942581 := bbase (se 5 (by rfl) ⟨137933, by rfl⟩ : syracuseStep 2942581 = 275867) (by norm_num)
theorem B2614925 : Blo 1742572 2614925 := bbase (se 3 (by rfl) ⟨490298, by rfl⟩ : syracuseStep 2614925 = 980597) (by norm_num)
theorem B2614949 : Blo 1742572 2614949 := bbase (se 4 (by rfl) ⟨245151, by rfl⟩ : syracuseStep 2614949 = 490303) (by norm_num)
theorem B2614973 : Blo 1742572 2614973 := bbase (se 3 (by rfl) ⟨490307, by rfl⟩ : syracuseStep 2614973 = 980615) (by norm_num)
theorem B3311293 : Blo 1742572 3311293 := bbase (se 3 (by rfl) ⟨620867, by rfl⟩ : syracuseStep 3311293 = 1241735) (by norm_num)
theorem B4966085 : Blo 1742572 4966085 := bbase (se 4 (by rfl) ⟨465570, by rfl⟩ : syracuseStep 4966085 = 931141) (by norm_num)
theorem B2942669 : Blo 1742572 2942669 := bbase (se 3 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 2942669 = 1103501) (by norm_num)
theorem B2614997 : Blo 1742572 2614997 := bbase (se 7 (by rfl) ⟨30644, by rfl⟩ : syracuseStep 2614997 = 61289) (by norm_num)
theorem B6620885 : Blo 1742572 6620885 := bbase (se 7 (by rfl) ⟨77588, by rfl⟩ : syracuseStep 6620885 = 155177) (by norm_num)
theorem B2615021 : Blo 1742572 2615021 := bbase (se 3 (by rfl) ⟨490316, by rfl⟩ : syracuseStep 2615021 = 980633) (by norm_num)
theorem B14894837 : Blo 1742572 14894837 := bbase (se 5 (by rfl) ⟨698195, by rfl⟩ : syracuseStep 14894837 = 1396391) (by norm_num)
theorem B2615045 : Blo 1742572 2615045 := bbase (se 4 (by rfl) ⟨245160, by rfl⟩ : syracuseStep 2615045 = 490321) (by norm_num)
theorem B1861385 : Blo 1742572 1861385 := bbase (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) (by norm_num)
theorem B7956245 : Blo 1742572 7956245 := bbase (se 6 (by rfl) ⟨186474, by rfl⟩ : syracuseStep 7956245 = 372949) (by norm_num)
theorem B2615069 : Blo 1742572 2615069 := bbase (se 3 (by rfl) ⟨490325, by rfl⟩ : syracuseStep 2615069 = 980651) (by norm_num)
theorem B11167541 : Blo 1742572 11167541 := bbase (se 5 (by rfl) ⟨523478, by rfl⟩ : syracuseStep 11167541 = 1046957) (by norm_num)
theorem B2615093 : Blo 1742572 2615093 := bbase (se 5 (by rfl) ⟨122582, by rfl⟩ : syracuseStep 2615093 = 245165) (by norm_num)
theorem B2615117 : Blo 1742572 2615117 := bbase (se 3 (by rfl) ⟨490334, by rfl⟩ : syracuseStep 2615117 = 980669) (by norm_num)
theorem B2942797 : Blo 1742572 2942797 := bbase (se 3 (by rfl) ⟨551774, by rfl⟩ : syracuseStep 2942797 = 1103549) (by norm_num)
theorem B3311437 : Blo 1742572 3311437 := bbase (se 3 (by rfl) ⟨620894, by rfl⟩ : syracuseStep 3311437 = 1241789) (by norm_num)
theorem B2615141 : Blo 1742572 2615141 := bbase (se 4 (by rfl) ⟨245169, by rfl⟩ : syracuseStep 2615141 = 490339) (by norm_num)
theorem B14886773 : Blo 1742572 14886773 := bbase (se 5 (by rfl) ⟨697817, by rfl⟩ : syracuseStep 14886773 = 1395635) (by norm_num)
theorem B2615165 : Blo 1742572 2615165 := bbase (se 3 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 2615165 = 980687) (by norm_num)
theorem B2205569 : Blo 1742572 2205569 := bbase (se 2 (by rfl) ⟨827088, by rfl⟩ : syracuseStep 2205569 = 1654177) (by norm_num)
theorem B4532117 : Blo 1742572 4532117 := bbase (se 6 (by rfl) ⟨106221, by rfl⟩ : syracuseStep 4532117 = 212443) (by norm_num)
theorem B2869141 : Blo 1742572 2869141 := bbase (se 6 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 2869141 = 134491) (by norm_num)
theorem B2615189 : Blo 1742572 2615189 := bbase (se 6 (by rfl) ⟨61293, by rfl⟩ : syracuseStep 2615189 = 122587) (by norm_num)
theorem B2942885 : Blo 1742572 2942885 := bbase (se 4 (by rfl) ⟨275895, by rfl⟩ : syracuseStep 2942885 = 551791) (by norm_num)
theorem B2615213 : Blo 1742572 2615213 := bbase (se 3 (by rfl) ⟨490352, by rfl⟩ : syracuseStep 2615213 = 980705) (by norm_num)
theorem B4777909 : Blo 1742572 4777909 := bbase (se 5 (by rfl) ⟨223964, by rfl⟩ : syracuseStep 4777909 = 447929) (by norm_num)
theorem B2205625 : Blo 1742572 2205625 := bbase (se 2 (by rfl) ⟨827109, by rfl⟩ : syracuseStep 2205625 = 1654219) (by norm_num)
theorem B2615237 : Blo 1742572 2615237 := bbase (se 4 (by rfl) ⟨245178, by rfl⟩ : syracuseStep 2615237 = 490357) (by norm_num)
theorem B2615261 : Blo 1742572 2615261 := bbase (se 3 (by rfl) ⟨490361, by rfl⟩ : syracuseStep 2615261 = 980723) (by norm_num)
theorem B3975149 : Blo 1742572 3975149 := bbase (se 3 (by rfl) ⟨745340, by rfl⟩ : syracuseStep 3975149 = 1490681) (by norm_num)
theorem B3311597 : Blo 1742572 3311597 := bbase (se 3 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 3311597 = 1241849) (by norm_num)
theorem B5883893 : Blo 1742572 5883893 := bbase (se 5 (by rfl) ⟨275807, by rfl⟩ : syracuseStep 5883893 = 551615) (by norm_num)
theorem B2615285 : Blo 1742572 2615285 := bbase (se 5 (by rfl) ⟨122591, by rfl⟩ : syracuseStep 2615285 = 245183) (by norm_num)
theorem B6621173 : Blo 1742572 6621173 := bbase (se 5 (by rfl) ⟨310367, by rfl⟩ : syracuseStep 6621173 = 620735) (by norm_num)
theorem B1861633 : Blo 1742572 1861633 := bbase (se 2 (by rfl) ⟨698112, by rfl⟩ : syracuseStep 1861633 = 1396225) (by norm_num)
theorem B2615309 : Blo 1742572 2615309 := bbase (se 3 (by rfl) ⟨490370, by rfl⟩ : syracuseStep 2615309 = 980741) (by norm_num)
theorem B2517013 : Blo 1742572 2517013 := bbase (se 6 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 2517013 = 117985) (by norm_num)
theorem B2205721 : Blo 1742572 2205721 := bbase (se 2 (by rfl) ⟨827145, by rfl⟩ : syracuseStep 2205721 = 1654291) (by norm_num)
theorem B2615333 : Blo 1742572 2615333 := bbase (se 4 (by rfl) ⟨245187, by rfl⟩ : syracuseStep 2615333 = 490375) (by norm_num)
theorem B2943013 : Blo 1742572 2943013 := bbase (se 4 (by rfl) ⟨275907, by rfl⟩ : syracuseStep 2943013 = 551815) (by norm_num)
theorem B7956533 : Blo 1742572 7956533 := bbase (se 5 (by rfl) ⟨372962, by rfl⟩ : syracuseStep 7956533 = 745925) (by norm_num)
theorem B2615357 : Blo 1742572 2615357 := bbase (se 3 (by rfl) ⟨490379, by rfl⟩ : syracuseStep 2615357 = 980759) (by norm_num)
theorem B2615381 : Blo 1742572 2615381 := bbase (se 8 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 2615381 = 30649) (by norm_num)
theorem B2615405 : Blo 1742572 2615405 := bbase (se 3 (by rfl) ⟨490388, by rfl⟩ : syracuseStep 2615405 = 980777) (by norm_num)
theorem B8824949 : Blo 1742572 8824949 := bbase (se 5 (by rfl) ⟨413669, by rfl⟩ : syracuseStep 8824949 = 827339) (by norm_num)
theorem B2943101 : Blo 1742572 2943101 := bbase (se 3 (by rfl) ⟨551831, by rfl⟩ : syracuseStep 2943101 = 1103663) (by norm_num)
theorem B3311741 : Blo 1742572 3311741 := bbase (se 3 (by rfl) ⟨620951, by rfl⟩ : syracuseStep 3311741 = 1241903) (by norm_num)
theorem B2615429 : Blo 1742572 2615429 := bbase (se 4 (by rfl) ⟨245196, by rfl⟩ : syracuseStep 2615429 = 490393) (by norm_num)
theorem B7071893 : Blo 1742572 7071893 := bbase (se 6 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 7071893 = 331495) (by norm_num)
theorem B2615453 : Blo 1742572 2615453 := bbase (se 3 (by rfl) ⟨490397, by rfl⟩ : syracuseStep 2615453 = 980795) (by norm_num)
theorem B3582133 : Blo 1742572 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B2615477 : Blo 1742572 2615477 := bbase (se 5 (by rfl) ⟨122600, by rfl⟩ : syracuseStep 2615477 = 245201) (by norm_num)
theorem B2205893 : Blo 1742572 2205893 := bbase (se 4 (by rfl) ⟨206802, by rfl⟩ : syracuseStep 2205893 = 413605) (by norm_num)
theorem B2615501 : Blo 1742572 2615501 := bbase (se 3 (by rfl) ⟨490406, by rfl⟩ : syracuseStep 2615501 = 980813) (by norm_num)
theorem B22341845 : Blo 1742572 22341845 := bbase (se 7 (by rfl) ⟨261818, by rfl⟩ : syracuseStep 22341845 = 523637) (by norm_num)
theorem B2615525 : Blo 1742572 2615525 := bbase (se 4 (by rfl) ⟨245205, by rfl⟩ : syracuseStep 2615525 = 490411) (by norm_num)
theorem B2205949 : Blo 1742572 2205949 := bbase (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) (by norm_num)
theorem B2615549 : Blo 1742572 2615549 := bbase (se 3 (by rfl) ⟨490415, by rfl⟩ : syracuseStep 2615549 = 980831) (by norm_num)
theorem B2943229 : Blo 1742572 2943229 := bbase (se 3 (by rfl) ⟨551855, by rfl⟩ : syracuseStep 2943229 = 1103711) (by norm_num)
theorem B2615573 : Blo 1742572 2615573 := bbase (se 6 (by rfl) ⟨61302, by rfl⟩ : syracuseStep 2615573 = 122605) (by norm_num)
theorem B6285605 : Blo 1742572 6285605 := bbase (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) (by norm_num)
theorem B2615597 : Blo 1742572 2615597 := bbase (se 3 (by rfl) ⟨490424, by rfl⟩ : syracuseStep 2615597 = 980849) (by norm_num)
theorem B2615621 : Blo 1742572 2615621 := bbase (se 4 (by rfl) ⟨245214, by rfl⟩ : syracuseStep 2615621 = 490429) (by norm_num)
theorem B2943317 : Blo 1742572 2943317 := bbase (se 10 (by rfl) ⟨4311, by rfl⟩ : syracuseStep 2943317 = 8623) (by norm_num)
theorem B2206045 : Blo 1742572 2206045 := bbase (se 3 (by rfl) ⟨413633, by rfl⟩ : syracuseStep 2206045 = 827267) (by norm_num)
theorem B2615645 : Blo 1742572 2615645 := bbase (se 3 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 2615645 = 980867) (by norm_num)
theorem B2615669 : Blo 1742572 2615669 := bbase (se 5 (by rfl) ⟨122609, by rfl⟩ : syracuseStep 2615669 = 245219) (by norm_num)
theorem B6367621 : Blo 1742572 6367621 := bbase (se 4 (by rfl) ⟨596964, by rfl⟩ : syracuseStep 6367621 = 1193929) (by norm_num)
theorem B2615693 : Blo 1742572 2615693 := bbase (se 3 (by rfl) ⟨490442, by rfl⟩ : syracuseStep 2615693 = 980885) (by norm_num)
theorem B5884325 : Blo 1742572 5884325 := bbase (se 4 (by rfl) ⟨551655, by rfl⟩ : syracuseStep 5884325 = 1103311) (by norm_num)
theorem B2615717 : Blo 1742572 2615717 := bbase (se 4 (by rfl) ⟨245223, by rfl⟩ : syracuseStep 2615717 = 490447) (by norm_num)
theorem B1862077 : Blo 1742572 1862077 := bbase (se 3 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 1862077 = 698279) (by norm_num)
theorem B2615741 : Blo 1742572 2615741 := bbase (se 3 (by rfl) ⟨490451, by rfl⟩ : syracuseStep 2615741 = 980903) (by norm_num)
theorem B2615765 : Blo 1742572 2615765 := bbase (se 7 (by rfl) ⟨30653, by rfl⟩ : syracuseStep 2615765 = 61307) (by norm_num)
theorem B2943445 : Blo 1742572 2943445 := bbase (se 7 (by rfl) ⟨34493, by rfl⟩ : syracuseStep 2943445 = 68987) (by norm_num)
theorem B1960429 : Blo 1742572 1960429 := bbase (se 3 (by rfl) ⟨367580, by rfl⟩ : syracuseStep 1960429 = 735161) (by norm_num)
theorem B2615789 : Blo 1742572 2615789 := bbase (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) (by norm_num)
theorem B1862137 : Blo 1742572 1862137 := bbase (se 2 (by rfl) ⟨698301, by rfl⟩ : syracuseStep 1862137 = 1396603) (by norm_num)
theorem B2615813 : Blo 1742572 2615813 := bbase (se 4 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 2615813 = 490465) (by norm_num)
theorem B2206217 : Blo 1742572 2206217 := bbase (se 2 (by rfl) ⟨827331, by rfl⟩ : syracuseStep 2206217 = 1654663) (by norm_num)
theorem B1960465 : Blo 1742572 1960465 := bbase (se 2 (by rfl) ⟨735174, by rfl⟩ : syracuseStep 1960465 = 1470349) (by norm_num)
theorem B2615837 : Blo 1742572 2615837 := bbase (se 3 (by rfl) ⟨490469, by rfl⟩ : syracuseStep 2615837 = 980939) (by norm_num)
theorem B2943533 : Blo 1742572 2943533 := bbase (se 3 (by rfl) ⟨551912, by rfl⟩ : syracuseStep 2943533 = 1103825) (by norm_num)
theorem B1960501 : Blo 1742572 1960501 := bbase (se 5 (by rfl) ⟨91898, by rfl⟩ : syracuseStep 1960501 = 183797) (by norm_num)
theorem B2615861 : Blo 1742572 2615861 := bbase (se 5 (by rfl) ⟨122618, by rfl⟩ : syracuseStep 2615861 = 245237) (by norm_num)
theorem B2206273 : Blo 1742572 2206273 := bbase (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) (by norm_num)
theorem B5966405 : Blo 1742572 5966405 := bbase (se 4 (by rfl) ⟨559350, by rfl⟩ : syracuseStep 5966405 = 1118701) (by norm_num)
theorem B2615885 : Blo 1742572 2615885 := bbase (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) (by norm_num)
theorem B9931349 : Blo 1742572 9931349 := bbase (se 8 (by rfl) ⟨58191, by rfl⟩ : syracuseStep 9931349 = 116383) (by norm_num)
theorem B1960537 : Blo 1742572 1960537 := bbase (se 2 (by rfl) ⟨735201, by rfl⟩ : syracuseStep 1960537 = 1470403) (by norm_num)
theorem B2615909 : Blo 1742572 2615909 := bbase (se 4 (by rfl) ⟨245241, by rfl⟩ : syracuseStep 2615909 = 490483) (by norm_num)
theorem B1960573 : Blo 1742572 1960573 := bbase (se 3 (by rfl) ⟨367607, by rfl⟩ : syracuseStep 1960573 = 735215) (by norm_num)
theorem B2615933 : Blo 1742572 2615933 := bbase (se 3 (by rfl) ⟨490487, by rfl⟩ : syracuseStep 2615933 = 980975) (by norm_num)
theorem B2517637 : Blo 1742572 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B2615957 : Blo 1742572 2615957 := bbase (se 6 (by rfl) ⟨61311, by rfl⟩ : syracuseStep 2615957 = 122623) (by norm_num)
theorem B1960609 : Blo 1742572 1960609 := bbase (se 2 (by rfl) ⟨735228, by rfl⟩ : syracuseStep 1960609 = 1470457) (by norm_num)
theorem B2206369 : Blo 1742572 2206369 := bbase (se 2 (by rfl) ⟨827388, by rfl⟩ : syracuseStep 2206369 = 1654777) (by norm_num)
theorem B2615981 : Blo 1742572 2615981 := bbase (se 3 (by rfl) ⟨490496, by rfl⟩ : syracuseStep 2615981 = 980993) (by norm_num)
theorem B2943661 : Blo 1742572 2943661 := bbase (se 3 (by rfl) ⟨551936, by rfl⟩ : syracuseStep 2943661 = 1103873) (by norm_num)
theorem B3721925 : Blo 1742572 3721925 := bbase (se 4 (by rfl) ⟨348930, by rfl⟩ : syracuseStep 3721925 = 697861) (by norm_num)
theorem B1960645 : Blo 1742572 1960645 := bbase (se 4 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 1960645 = 367621) (by norm_num)
theorem B2616005 : Blo 1742572 2616005 := bbase (se 4 (by rfl) ⟨245250, by rfl⟩ : syracuseStep 2616005 = 490501) (by norm_num)
theorem B2616029 : Blo 1742572 2616029 := bbase (se 3 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 2616029 = 981011) (by norm_num)
theorem B7449317 : Blo 1742572 7449317 := bbase (se 4 (by rfl) ⟨698373, by rfl⟩ : syracuseStep 7449317 = 1396747) (by norm_num)
theorem B1960681 : Blo 1742572 1960681 := bbase (se 2 (by rfl) ⟨735255, by rfl⟩ : syracuseStep 1960681 = 1470511) (by norm_num)
theorem B2616053 : Blo 1742572 2616053 := bbase (se 5 (by rfl) ⟨122627, by rfl⟩ : syracuseStep 2616053 = 245255) (by norm_num)
theorem B2943749 : Blo 1742572 2943749 := bbase (se 4 (by rfl) ⟨275976, by rfl⟩ : syracuseStep 2943749 = 551953) (by norm_num)
theorem B1960717 : Blo 1742572 1960717 := bbase (se 3 (by rfl) ⟨367634, by rfl⟩ : syracuseStep 1960717 = 735269) (by norm_num)
theorem B2616077 : Blo 1742572 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B2616101 : Blo 1742572 2616101 := bbase (se 4 (by rfl) ⟨245259, by rfl⟩ : syracuseStep 2616101 = 490519) (by norm_num)
theorem B1960753 : Blo 1742572 1960753 := bbase (se 2 (by rfl) ⟨735282, by rfl⟩ : syracuseStep 1960753 = 1470565) (by norm_num)
theorem B1862453 : Blo 1742572 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B2616125 : Blo 1742572 2616125 := bbase (se 3 (by rfl) ⟨490523, by rfl⟩ : syracuseStep 2616125 = 981047) (by norm_num)
theorem B2206541 : Blo 1742572 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B3722069 : Blo 1742572 3722069 := bbase (se 9 (by rfl) ⟨10904, by rfl⟩ : syracuseStep 3722069 = 21809) (by norm_num)
theorem B1960789 : Blo 1742572 1960789 := bbase (se 9 (by rfl) ⟨5744, by rfl⟩ : syracuseStep 1960789 = 11489) (by norm_num)
theorem B5884757 : Blo 1742572 5884757 := bbase (se 9 (by rfl) ⟨17240, by rfl⟩ : syracuseStep 5884757 = 34481) (by norm_num)
theorem B2616149 : Blo 1742572 2616149 := bbase (se 9 (by rfl) ⟨7664, by rfl⟩ : syracuseStep 2616149 = 15329) (by norm_num)
theorem B2616173 : Blo 1742572 2616173 := bbase (se 3 (by rfl) ⟨490532, by rfl⟩ : syracuseStep 2616173 = 981065) (by norm_num)
theorem B1960825 : Blo 1742572 1960825 := bbase (se 2 (by rfl) ⟨735309, by rfl⟩ : syracuseStep 1960825 = 1470619) (by norm_num)
theorem B2206597 : Blo 1742572 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B2616197 : Blo 1742572 2616197 := bbase (se 4 (by rfl) ⟨245268, by rfl⟩ : syracuseStep 2616197 = 490537) (by norm_num)
theorem B2943877 : Blo 1742572 2943877 := bbase (se 4 (by rfl) ⟨275988, by rfl⟩ : syracuseStep 2943877 = 551977) (by norm_num)
theorem B4475789 : Blo 1742572 4475789 := bbase (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) (by norm_num)
theorem B1960861 : Blo 1742572 1960861 := bbase (se 3 (by rfl) ⟨367661, by rfl⟩ : syracuseStep 1960861 = 735323) (by norm_num)
theorem B2616221 : Blo 1742572 2616221 := bbase (se 3 (by rfl) ⟨490541, by rfl⟩ : syracuseStep 2616221 = 981083) (by norm_num)
theorem B2616245 : Blo 1742572 2616245 := bbase (se 5 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 2616245 = 245273) (by norm_num)
theorem B1960897 : Blo 1742572 1960897 := bbase (se 2 (by rfl) ⟨735336, by rfl⟩ : syracuseStep 1960897 = 1470673) (by norm_num)
theorem B3533765 : Blo 1742572 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B2616269 : Blo 1742572 2616269 := bbase (se 3 (by rfl) ⟨490550, by rfl⟩ : syracuseStep 2616269 = 981101) (by norm_num)
theorem B2943965 : Blo 1742572 2943965 := bbase (se 3 (by rfl) ⟨551993, by rfl⟩ : syracuseStep 2943965 = 1103987) (by norm_num)
theorem B1960933 : Blo 1742572 1960933 := bbase (se 4 (by rfl) ⟨183837, by rfl⟩ : syracuseStep 1960933 = 367675) (by norm_num)
theorem B2206693 : Blo 1742572 2206693 := bbase (se 4 (by rfl) ⟨206877, by rfl⟩ : syracuseStep 2206693 = 413755) (by norm_num)
theorem B2616293 : Blo 1742572 2616293 := bbase (se 4 (by rfl) ⟨245277, by rfl⟩ : syracuseStep 2616293 = 490555) (by norm_num)
theorem B17886197 : Blo 1742572 17886197 := bbase (se 5 (by rfl) ⟨838415, by rfl⟩ : syracuseStep 17886197 = 1676831) (by norm_num)
theorem B2616317 : Blo 1742572 2616317 := bbase (se 3 (by rfl) ⟨490559, by rfl⟩ : syracuseStep 2616317 = 981119) (by norm_num)
theorem B1960969 : Blo 1742572 1960969 := bbase (se 2 (by rfl) ⟨735363, by rfl⟩ : syracuseStep 1960969 = 1470727) (by norm_num)
theorem B3582989 : Blo 1742572 3582989 := bbase (se 3 (by rfl) ⟨671810, by rfl⟩ : syracuseStep 3582989 = 1343621) (by norm_num)
theorem B2616341 : Blo 1742572 2616341 := bbase (se 6 (by rfl) ⟨61320, by rfl⟩ : syracuseStep 2616341 = 122641) (by norm_num)
theorem B7957541 : Blo 1742572 7957541 := bbase (se 4 (by rfl) ⟨746019, by rfl⟩ : syracuseStep 7957541 = 1492039) (by norm_num)
theorem B1961005 : Blo 1742572 1961005 := bbase (se 3 (by rfl) ⟨367688, by rfl⟩ : syracuseStep 1961005 = 735377) (by norm_num)
theorem B2616365 : Blo 1742572 2616365 := bbase (se 3 (by rfl) ⟨490568, by rfl⟩ : syracuseStep 2616365 = 981137) (by norm_num)
theorem B2616389 : Blo 1742572 2616389 := bbase (se 4 (by rfl) ⟨245286, by rfl⟩ : syracuseStep 2616389 = 490573) (by norm_num)
theorem B1961041 : Blo 1742572 1961041 := bbase (se 2 (by rfl) ⟨735390, by rfl⟩ : syracuseStep 1961041 = 1470781) (by norm_num)
theorem B2616413 : Blo 1742572 2616413 := bbase (se 3 (by rfl) ⟨490577, by rfl⟩ : syracuseStep 2616413 = 981155) (by norm_num)
theorem B1961077 : Blo 1742572 1961077 := bbase (se 5 (by rfl) ⟨91925, by rfl⟩ : syracuseStep 1961077 = 183851) (by norm_num)
theorem B2616437 : Blo 1742572 2616437 := bbase (se 5 (by rfl) ⟨122645, by rfl⟩ : syracuseStep 2616437 = 245291) (by norm_num)
theorem B2616461 : Blo 1742572 2616461 := bbase (se 3 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 2616461 = 981173) (by norm_num)
theorem B2206865 : Blo 1742572 2206865 := bbase (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) (by norm_num)
theorem B6622357 : Blo 1742572 6622357 := bbase (se 6 (by rfl) ⟨155211, by rfl⟩ : syracuseStep 6622357 = 310423) (by norm_num)
theorem B1961113 : Blo 1742572 1961113 := bbase (se 2 (by rfl) ⟨735417, by rfl⟩ : syracuseStep 1961113 = 1470835) (by norm_num)
theorem B2616485 : Blo 1742572 2616485 := bbase (se 4 (by rfl) ⟨245295, by rfl⟩ : syracuseStep 2616485 = 490591) (by norm_num)
theorem B6286517 : Blo 1742572 6286517 := bbase (se 5 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 6286517 = 589361) (by norm_num)
theorem B3722429 : Blo 1742572 3722429 := bbase (se 3 (by rfl) ⟨697955, by rfl⟩ : syracuseStep 3722429 = 1395911) (by norm_num)
theorem B1961149 : Blo 1742572 1961149 := bbase (se 3 (by rfl) ⟨367715, by rfl⟩ : syracuseStep 1961149 = 735431) (by norm_num)
theorem B2616509 : Blo 1742572 2616509 := bbase (se 3 (by rfl) ⟨490595, by rfl⟩ : syracuseStep 2616509 = 981191) (by norm_num)
theorem B2206921 : Blo 1742572 2206921 := bbase (se 2 (by rfl) ⟨827595, by rfl⟩ : syracuseStep 2206921 = 1655191) (by norm_num)
theorem B2616533 : Blo 1742572 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B1961185 : Blo 1742572 1961185 := bbase (se 2 (by rfl) ⟨735444, by rfl⟩ : syracuseStep 1961185 = 1470889) (by norm_num)
theorem B2616557 : Blo 1742572 2616557 := bbase (se 3 (by rfl) ⟨490604, by rfl⟩ : syracuseStep 2616557 = 981209) (by norm_num)
theorem B1862897 : Blo 1742572 1862897 := bbase (se 2 (by rfl) ⟨698586, by rfl⟩ : syracuseStep 1862897 = 1397173) (by norm_num)
theorem B4967669 : Blo 1742572 4967669 := bbase (se 5 (by rfl) ⟨232859, by rfl⟩ : syracuseStep 4967669 = 465719) (by norm_num)
theorem B1961221 : Blo 1742572 1961221 := bbase (se 4 (by rfl) ⟨183864, by rfl⟩ : syracuseStep 1961221 = 367729) (by norm_num)
theorem B5885189 : Blo 1742572 5885189 := bbase (se 4 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 5885189 = 1103473) (by norm_num)
theorem B2616581 : Blo 1742572 2616581 := bbase (se 4 (by rfl) ⟨245304, by rfl⟩ : syracuseStep 2616581 = 490609) (by norm_num)
theorem B2616605 : Blo 1742572 2616605 := bbase (se 3 (by rfl) ⟨490613, by rfl⟩ : syracuseStep 2616605 = 981227) (by norm_num)
theorem B1961257 : Blo 1742572 1961257 := bbase (se 2 (by rfl) ⟨735471, by rfl⟩ : syracuseStep 1961257 = 1470943) (by norm_num)
theorem B2207017 : Blo 1742572 2207017 := bbase (se 2 (by rfl) ⟨827631, by rfl⟩ : syracuseStep 2207017 = 1655263) (by norm_num)
theorem B1862957 : Blo 1742572 1862957 := bbase (se 3 (by rfl) ⟨349304, by rfl⟩ : syracuseStep 1862957 = 698609) (by norm_num)
theorem B2616629 : Blo 1742572 2616629 := bbase (se 5 (by rfl) ⟨122654, by rfl⟩ : syracuseStep 2616629 = 245309) (by norm_num)
theorem B1961293 : Blo 1742572 1961293 := bbase (se 3 (by rfl) ⟨367742, by rfl⟩ : syracuseStep 1961293 = 735485) (by norm_num)
theorem B2616653 : Blo 1742572 2616653 := bbase (se 3 (by rfl) ⟨490622, by rfl⟩ : syracuseStep 2616653 = 981245) (by norm_num)
theorem B2616677 : Blo 1742572 2616677 := bbase (se 4 (by rfl) ⟨245313, by rfl⟩ : syracuseStep 2616677 = 490627) (by norm_num)
theorem B1961329 : Blo 1742572 1961329 := bbase (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) (by norm_num)
theorem B2616701 : Blo 1742572 2616701 := bbase (se 3 (by rfl) ⟨490631, by rfl⟩ : syracuseStep 2616701 = 981263) (by norm_num)
theorem B8826245 : Blo 1742572 8826245 := bbase (se 4 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 8826245 = 1654921) (by norm_num)
theorem B1961365 : Blo 1742572 1961365 := bbase (se 6 (by rfl) ⟨45969, by rfl⟩ : syracuseStep 1961365 = 91939) (by norm_num)
theorem B2616725 : Blo 1742572 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B2616749 : Blo 1742572 2616749 := bbase (se 3 (by rfl) ⟨490640, by rfl⟩ : syracuseStep 2616749 = 981281) (by norm_num)
theorem B1961401 : Blo 1742572 1961401 := bbase (se 2 (by rfl) ⟨735525, by rfl⟩ : syracuseStep 1961401 = 1471051) (by norm_num)
theorem B6622661 : Blo 1742572 6622661 := bbase (se 4 (by rfl) ⟨620874, by rfl⟩ : syracuseStep 6622661 = 1241749) (by norm_num)
theorem B2616773 : Blo 1742572 2616773 := bbase (se 4 (by rfl) ⟨245322, by rfl⟩ : syracuseStep 2616773 = 490645) (by norm_num)
theorem B3976661 : Blo 1742572 3976661 := bbase (se 7 (by rfl) ⟨46601, by rfl⟩ : syracuseStep 3976661 = 93203) (by norm_num)
theorem B2207189 : Blo 1742572 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B1961437 : Blo 1742572 1961437 := bbase (se 3 (by rfl) ⟨367769, by rfl⟩ : syracuseStep 1961437 = 735539) (by norm_num)
theorem B2616797 : Blo 1742572 2616797 := bbase (se 3 (by rfl) ⟨490649, by rfl⟩ : syracuseStep 2616797 = 981299) (by norm_num)
theorem B2616821 : Blo 1742572 2616821 := bbase (se 5 (by rfl) ⟨122663, by rfl⟩ : syracuseStep 2616821 = 245327) (by norm_num)
theorem B1961473 : Blo 1742572 1961473 := bbase (se 2 (by rfl) ⟨735552, by rfl⟩ : syracuseStep 1961473 = 1471105) (by norm_num)
theorem B2207245 : Blo 1742572 2207245 := bbase (se 3 (by rfl) ⟨413858, by rfl⟩ : syracuseStep 2207245 = 827717) (by norm_num)
theorem B2616845 : Blo 1742572 2616845 := bbase (se 3 (by rfl) ⟨490658, by rfl⟩ : syracuseStep 2616845 = 981317) (by norm_num)
theorem B1961509 : Blo 1742572 1961509 := bbase (se 4 (by rfl) ⟨183891, by rfl⟩ : syracuseStep 1961509 = 367783) (by norm_num)
theorem B1961545 : Blo 1742572 1961545 := bbase (se 2 (by rfl) ⟨735579, by rfl⟩ : syracuseStep 1961545 = 1471159) (by norm_num)
theorem B2649709 : Blo 1742572 2649709 := bbase (se 3 (by rfl) ⟨496820, by rfl⟩ : syracuseStep 2649709 = 993641) (by norm_num)
theorem B1961581 : Blo 1742572 1961581 := bbase (se 3 (by rfl) ⟨367796, by rfl⟩ : syracuseStep 1961581 = 735593) (by norm_num)
theorem B2207341 : Blo 1742572 2207341 := bbase (se 3 (by rfl) ⟨413876, by rfl⟩ : syracuseStep 2207341 = 827753) (by norm_num)
theorem B1961617 : Blo 1742572 1961617 := bbase (se 2 (by rfl) ⟨735606, by rfl⟩ : syracuseStep 1961617 = 1471213) (by norm_num)
theorem B4411037 : Blo 1742572 4411037 := bbase (se 3 (by rfl) ⟨827069, by rfl⟩ : syracuseStep 4411037 = 1654139) (by norm_num)
theorem B3354293 : Blo 1742572 3354293 := bbase (se 5 (by rfl) ⟨157232, by rfl⟩ : syracuseStep 3354293 = 314465) (by norm_num)
theorem B1961653 : Blo 1742572 1961653 := bbase (se 5 (by rfl) ⟨91952, by rfl⟩ : syracuseStep 1961653 = 183905) (by norm_num)
theorem B5885621 : Blo 1742572 5885621 := bbase (se 5 (by rfl) ⟨275888, by rfl⟩ : syracuseStep 5885621 = 551777) (by norm_num)
theorem B3976901 : Blo 1742572 3976901 := bbase (se 4 (by rfl) ⟨372834, by rfl⟩ : syracuseStep 3976901 = 745669) (by norm_num)
theorem B7450325 : Blo 1742572 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B1961689 : Blo 1742572 1961689 := bbase (se 2 (by rfl) ⟨735633, by rfl⟩ : syracuseStep 1961689 = 1471267) (by norm_num)
theorem B1961725 : Blo 1742572 1961725 := bbase (se 3 (by rfl) ⟨367823, by rfl⟩ : syracuseStep 1961725 = 735647) (by norm_num)
theorem B2207513 : Blo 1742572 2207513 := bbase (se 2 (by rfl) ⟨827817, by rfl⟩ : syracuseStep 2207513 = 1655635) (by norm_num)
theorem B4189981 : Blo 1742572 4189981 := bbase (se 3 (by rfl) ⟨785621, by rfl⟩ : syracuseStep 4189981 = 1571243) (by norm_num)
theorem B1961761 : Blo 1742572 1961761 := bbase (se 2 (by rfl) ⟨735660, by rfl⟩ : syracuseStep 1961761 = 1471321) (by norm_num)
theorem B3141413 : Blo 1742572 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B1961797 : Blo 1742572 1961797 := bbase (se 4 (by rfl) ⟨183918, by rfl⟩ : syracuseStep 1961797 = 367837) (by norm_num)
theorem B2207569 : Blo 1742572 2207569 := bbase (se 2 (by rfl) ⟨827838, by rfl⟩ : syracuseStep 2207569 = 1655677) (by norm_num)
theorem B1961833 : Blo 1742572 1961833 := bbase (se 2 (by rfl) ⟨735687, by rfl⟩ : syracuseStep 1961833 = 1471375) (by norm_num)
theorem B1961869 : Blo 1742572 1961869 := bbase (se 3 (by rfl) ⟨367850, by rfl⟩ : syracuseStep 1961869 = 735701) (by norm_num)
theorem B1961905 : Blo 1742572 1961905 := bbase (se 2 (by rfl) ⟨735714, by rfl⟩ : syracuseStep 1961905 = 1471429) (by norm_num)
theorem B2207665 : Blo 1742572 2207665 := bbase (se 2 (by rfl) ⟨827874, by rfl⟩ : syracuseStep 2207665 = 1655749) (by norm_num)
theorem B1961941 : Blo 1742572 1961941 := bbase (se 7 (by rfl) ⟨22991, by rfl⟩ : syracuseStep 1961941 = 45983) (by norm_num)
theorem B4411381 : Blo 1742572 4411381 := bbase (se 5 (by rfl) ⟨206783, by rfl⟩ : syracuseStep 4411381 = 413567) (by norm_num)
theorem B1961977 : Blo 1742572 1961977 := bbase (se 2 (by rfl) ⟨735741, by rfl⟩ : syracuseStep 1961977 = 1471483) (by norm_num)
theorem B2797589 : Blo 1742572 2797589 := bbase (se 6 (by rfl) ⟨65568, by rfl⟩ : syracuseStep 2797589 = 131137) (by norm_num)
theorem B1962013 : Blo 1742572 1962013 := bbase (se 3 (by rfl) ⟨367877, by rfl⟩ : syracuseStep 1962013 = 735755) (by norm_num)
theorem B3723317 : Blo 1742572 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B1962049 : Blo 1742572 1962049 := bbase (se 2 (by rfl) ⟨735768, by rfl⟩ : syracuseStep 1962049 = 1471537) (by norm_num)
theorem B3534941 : Blo 1742572 3534941 := bbase (se 3 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 3534941 = 1325603) (by norm_num)
theorem B2207837 : Blo 1742572 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B4411493 : Blo 1742572 4411493 := bbase (se 4 (by rfl) ⟨413577, by rfl⟩ : syracuseStep 4411493 = 827155) (by norm_num)
theorem B5886053 : Blo 1742572 5886053 := bbase (se 4 (by rfl) ⟨551817, by rfl⟩ : syracuseStep 5886053 = 1103635) (by norm_num)
theorem B1962085 : Blo 1742572 1962085 := bbase (se 4 (by rfl) ⟨183945, by rfl⟩ : syracuseStep 1962085 = 367891) (by norm_num)
theorem B1962121 : Blo 1742572 1962121 := bbase (se 2 (by rfl) ⟨735795, by rfl⟩ : syracuseStep 1962121 = 1471591) (by norm_num)
theorem B2207893 : Blo 1742572 2207893 := bbase (se 6 (by rfl) ⟨51747, by rfl⟩ : syracuseStep 2207893 = 103495) (by norm_num)
theorem B1962157 : Blo 1742572 1962157 := bbase (se 3 (by rfl) ⟨367904, by rfl⟩ : syracuseStep 1962157 = 735809) (by norm_num)
theorem B1962193 : Blo 1742572 1962193 := bbase (se 2 (by rfl) ⟨735822, by rfl⟩ : syracuseStep 1962193 = 1471645) (by norm_num)
theorem B1962229 : Blo 1742572 1962229 := bbase (se 5 (by rfl) ⟨91979, by rfl⟩ : syracuseStep 1962229 = 183959) (by norm_num)
theorem B1962265 : Blo 1742572 1962265 := bbase (se 2 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 1962265 = 1471699) (by norm_num)
theorem B4411685 : Blo 1742572 4411685 := bbase (se 4 (by rfl) ⟨413595, by rfl⟩ : syracuseStep 4411685 = 827191) (by norm_num)
theorem B3723565 : Blo 1742572 3723565 := bbase (se 3 (by rfl) ⟨698168, by rfl⟩ : syracuseStep 3723565 = 1396337) (by norm_num)
theorem B1962301 : Blo 1742572 1962301 := bbase (se 3 (by rfl) ⟨367931, by rfl⟩ : syracuseStep 1962301 = 735863) (by norm_num)
theorem B1962337 : Blo 1742572 1962337 := bbase (se 2 (by rfl) ⟨735876, by rfl⟩ : syracuseStep 1962337 = 1471753) (by norm_num)
theorem B2355589 : Blo 1742572 2355589 := bbase (se 4 (by rfl) ⟨220836, by rfl⟩ : syracuseStep 2355589 = 441673) (by norm_num)
theorem B1962373 : Blo 1742572 1962373 := bbase (se 4 (by rfl) ⟨183972, by rfl⟩ : syracuseStep 1962373 = 367945) (by norm_num)
theorem B3977629 : Blo 1742572 3977629 := bbase (se 3 (by rfl) ⟨745805, by rfl⟩ : syracuseStep 3977629 = 1491611) (by norm_num)
theorem B1962409 : Blo 1742572 1962409 := bbase (se 2 (by rfl) ⟨735903, by rfl⟩ : syracuseStep 1962409 = 1471807) (by norm_num)
theorem B1962445 : Blo 1742572 1962445 := bbase (se 3 (by rfl) ⟨367958, by rfl⟩ : syracuseStep 1962445 = 735917) (by norm_num)
theorem B1962481 : Blo 1742572 1962481 := bbase (se 2 (by rfl) ⟨735930, by rfl⟩ : syracuseStep 1962481 = 1471861) (by norm_num)
theorem B3355141 : Blo 1742572 3355141 := bbase (se 4 (by rfl) ⟨314544, by rfl⟩ : syracuseStep 3355141 = 629089) (by norm_num)
theorem B11932181 : Blo 1742572 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B5886485 : Blo 1742572 5886485 := bbase (se 6 (by rfl) ⟨137964, by rfl⟩ : syracuseStep 5886485 = 275929) (by norm_num)
theorem B1962517 : Blo 1742572 1962517 := bbase (se 6 (by rfl) ⟨45996, by rfl⟩ : syracuseStep 1962517 = 91993) (by norm_num)
theorem B1962553 : Blo 1742572 1962553 := bbase (se 2 (by rfl) ⟨735957, by rfl⟩ : syracuseStep 1962553 = 1471915) (by norm_num)
theorem B1962589 : Blo 1742572 1962589 := bbase (se 3 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 1962589 = 735971) (by norm_num)
theorem B4412029 : Blo 1742572 4412029 := bbase (se 3 (by rfl) ⟨827255, by rfl⟩ : syracuseStep 4412029 = 1654511) (by norm_num)
theorem B1962625 : Blo 1742572 1962625 := bbase (se 2 (by rfl) ⟨735984, by rfl⟩ : syracuseStep 1962625 = 1471969) (by norm_num)
theorem B8827541 : Blo 1742572 8827541 := bbase (se 6 (by rfl) ⟨206895, by rfl⟩ : syracuseStep 8827541 = 413791) (by norm_num)
theorem B9425621 : Blo 1742572 9425621 := bbase (se 7 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 9425621 = 220913) (by norm_num)
theorem B4412141 : Blo 1742572 4412141 := bbase (se 3 (by rfl) ⟨827276, by rfl⟩ : syracuseStep 4412141 = 1654553) (by norm_num)
theorem B3724069 : Blo 1742572 3724069 := bbase (se 4 (by rfl) ⟨349131, by rfl⟩ : syracuseStep 3724069 = 698263) (by norm_num)
theorem B2093933 : Blo 1742572 2093933 := bbase (se 3 (by rfl) ⟨392612, by rfl⟩ : syracuseStep 2093933 = 785225) (by norm_num)
theorem B3920813 : Blo 1742572 3920813 := bbase (se 3 (by rfl) ⟨735152, by rfl⟩ : syracuseStep 3920813 = 1470305) (by norm_num)
theorem B4412333 : Blo 1742572 4412333 := bbase (se 3 (by rfl) ⟨827312, by rfl⟩ : syracuseStep 4412333 = 1654625) (by norm_num)
theorem B5886917 : Blo 1742572 5886917 := bbase (se 4 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 5886917 = 1103797) (by norm_num)
theorem B4191173 : Blo 1742572 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B2094049 : Blo 1742572 2094049 := bbase (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) (by norm_num)
theorem B3920885 : Blo 1742572 3920885 := bbase (se 5 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 3920885 = 367583) (by norm_num)
theorem B2094121 : Blo 1742572 2094121 := bbase (se 2 (by rfl) ⟨785295, by rfl⟩ : syracuseStep 2094121 = 1570591) (by norm_num)
theorem B3920957 : Blo 1742572 3920957 := bbase (se 3 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 3920957 = 1470359) (by norm_num)
theorem B1766497 : Blo 1742572 1766497 := bbase (se 2 (by rfl) ⟨662436, by rfl⟩ : syracuseStep 1766497 = 1324873) (by norm_num)
theorem B3921029 : Blo 1742572 3921029 := bbase (se 4 (by rfl) ⟨367596, by rfl⟩ : syracuseStep 3921029 = 735193) (by norm_num)
theorem B4191365 : Blo 1742572 4191365 := bbase (se 4 (by rfl) ⟨392940, by rfl⟩ : syracuseStep 4191365 = 785881) (by norm_num)
theorem B2094241 : Blo 1742572 2094241 := bbase (se 2 (by rfl) ⟨785340, by rfl⟩ : syracuseStep 2094241 = 1570681) (by norm_num)
theorem B3978413 : Blo 1742572 3978413 := bbase (se 3 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 3978413 = 1491905) (by norm_num)
theorem B4142269 : Blo 1742572 4142269 := bbase (se 3 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 4142269 = 1553351) (by norm_num)
theorem B3921101 : Blo 1742572 3921101 := bbase (se 3 (by rfl) ⟨735206, by rfl⟩ : syracuseStep 3921101 = 1470413) (by norm_num)
theorem B4412677 : Blo 1742572 4412677 := bbase (se 4 (by rfl) ⟨413688, by rfl⟩ : syracuseStep 4412677 = 827377) (by norm_num)
theorem B3921173 : Blo 1742572 3921173 := bbase (se 6 (by rfl) ⟨91902, by rfl⟩ : syracuseStep 3921173 = 183805) (by norm_num)
theorem B9925973 : Blo 1742572 9925973 := bbase (se 13 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 9925973 = 3635) (by norm_num)
theorem B3921245 : Blo 1742572 3921245 := bbase (se 3 (by rfl) ⟨735233, by rfl⟩ : syracuseStep 3921245 = 1470467) (by norm_num)
theorem B4412789 : Blo 1742572 4412789 := bbase (se 5 (by rfl) ⟨206849, by rfl⟩ : syracuseStep 4412789 = 413699) (by norm_num)
theorem B5887349 : Blo 1742572 5887349 := bbase (se 5 (by rfl) ⟨275969, by rfl⟩ : syracuseStep 5887349 = 551939) (by norm_num)
theorem B3921317 : Blo 1742572 3921317 := bbase (se 4 (by rfl) ⟨367623, by rfl⟩ : syracuseStep 3921317 = 735247) (by norm_num)
theorem B1988021 : Blo 1742572 1988021 := bbase (se 5 (by rfl) ⟨93188, by rfl⟩ : syracuseStep 1988021 = 186377) (by norm_num)
theorem B3921389 : Blo 1742572 3921389 := bbase (se 3 (by rfl) ⟨735260, by rfl⟩ : syracuseStep 3921389 = 1470521) (by norm_num)
theorem B2094625 : Blo 1742572 2094625 := bbase (se 2 (by rfl) ⟨785484, by rfl⟩ : syracuseStep 2094625 = 1570969) (by norm_num)
theorem B3921461 : Blo 1742572 3921461 := bbase (se 5 (by rfl) ⟨183818, by rfl⟩ : syracuseStep 3921461 = 367637) (by norm_num)
theorem B7067189 : Blo 1742572 7067189 := bbase (se 5 (by rfl) ⟨331274, by rfl⟩ : syracuseStep 7067189 = 662549) (by norm_num)
theorem B4412981 : Blo 1742572 4412981 := bbase (se 5 (by rfl) ⟨206858, by rfl⟩ : syracuseStep 4412981 = 413717) (by norm_num)
theorem B3921533 : Blo 1742572 3921533 := bbase (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) (by norm_num)
theorem B3356293 : Blo 1742572 3356293 := bbase (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) (by norm_num)
theorem B2651789 : Blo 1742572 2651789 := bbase (se 3 (by rfl) ⟨497210, by rfl⟩ : syracuseStep 2651789 = 994421) (by norm_num)
theorem B26834581 : Blo 1742572 26834581 := bbase (se 6 (by rfl) ⟨628935, by rfl⟩ : syracuseStep 26834581 = 1257871) (by norm_num)
theorem B3724957 : Blo 1742572 3724957 := bbase (se 3 (by rfl) ⟨698429, by rfl⟩ : syracuseStep 3724957 = 1396859) (by norm_num)
theorem B5584565 : Blo 1742572 5584565 := bbase (se 5 (by rfl) ⟨261776, by rfl⟩ : syracuseStep 5584565 = 523553) (by norm_num)
theorem B3921605 : Blo 1742572 3921605 := bbase (se 4 (by rfl) ⟨367650, by rfl⟩ : syracuseStep 3921605 = 735301) (by norm_num)
theorem B10065653 : Blo 1742572 10065653 := bbase (se 5 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 10065653 = 943655) (by norm_num)
theorem B8378117 : Blo 1742572 8378117 := bbase (se 4 (by rfl) ⟨785448, by rfl⟩ : syracuseStep 8378117 = 1570897) (by norm_num)
theorem B3921677 : Blo 1742572 3921677 := bbase (se 3 (by rfl) ⟨735314, by rfl⟩ : syracuseStep 3921677 = 1470629) (by norm_num)
theorem B5887781 : Blo 1742572 5887781 := bbase (se 4 (by rfl) ⟨551979, by rfl⟩ : syracuseStep 5887781 = 1103959) (by norm_num)
theorem B3921749 : Blo 1742572 3921749 := bbase (se 9 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 3921749 = 22979) (by norm_num)
theorem B4413325 : Blo 1742572 4413325 := bbase (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) (by norm_num)
theorem B3921821 : Blo 1742572 3921821 := bbase (se 3 (by rfl) ⟨735341, by rfl⟩ : syracuseStep 3921821 = 1470683) (by norm_num)
theorem B6616997 : Blo 1742572 6616997 := bbase (se 4 (by rfl) ⟨620343, by rfl⟩ : syracuseStep 6616997 = 1240687) (by norm_num)
theorem B8828837 : Blo 1742572 8828837 := bbase (se 4 (by rfl) ⟨827703, by rfl⟩ : syracuseStep 8828837 = 1655407) (by norm_num)
theorem B3921893 : Blo 1742572 3921893 := bbase (se 4 (by rfl) ⟨367677, by rfl⟩ : syracuseStep 3921893 = 735355) (by norm_num)
theorem B4962293 : Blo 1742572 4962293 := bbase (se 5 (by rfl) ⟨232607, by rfl⟩ : syracuseStep 4962293 = 465215) (by norm_num)
theorem B4413437 : Blo 1742572 4413437 := bbase (se 3 (by rfl) ⟨827519, by rfl⟩ : syracuseStep 4413437 = 1655039) (by norm_num)
theorem B3921965 : Blo 1742572 3921965 := bbase (se 3 (by rfl) ⟨735368, by rfl⟩ : syracuseStep 3921965 = 1470737) (by norm_num)
theorem B3922037 : Blo 1742572 3922037 := bbase (se 5 (by rfl) ⟨183845, by rfl⟩ : syracuseStep 3922037 = 367691) (by norm_num)
theorem B3725453 : Blo 1742572 3725453 := bbase (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) (by norm_num)
theorem B1792153 : Blo 1742572 1792153 := bbase (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) (by norm_num)
theorem B4962485 : Blo 1742572 4962485 := bbase (se 5 (by rfl) ⟨232616, by rfl⟩ : syracuseStep 4962485 = 465233) (by norm_num)
theorem B8943797 : Blo 1742572 8943797 := bbase (se 5 (by rfl) ⟨419240, by rfl⟩ : syracuseStep 8943797 = 838481) (by norm_num)
theorem B3922109 : Blo 1742572 3922109 := bbase (se 3 (by rfl) ⟨735395, by rfl⟩ : syracuseStep 3922109 = 1470791) (by norm_num)
theorem B4413629 : Blo 1742572 4413629 := bbase (se 3 (by rfl) ⟨827555, by rfl⟩ : syracuseStep 4413629 = 1655111) (by norm_num)
theorem B6617285 : Blo 1742572 6617285 := bbase (se 4 (by rfl) ⟨620370, by rfl⟩ : syracuseStep 6617285 = 1240741) (by norm_num)
theorem B2095313 : Blo 1742572 2095313 := bbase (se 2 (by rfl) ⟨785742, by rfl⟩ : syracuseStep 2095313 = 1571485) (by norm_num)
theorem B3922181 : Blo 1742572 3922181 := bbase (se 4 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 3922181 = 735409) (by norm_num)
theorem B2791757 : Blo 1742572 2791757 := bbase (se 3 (by rfl) ⟨523454, by rfl⟩ : syracuseStep 2791757 = 1046909) (by norm_num)
theorem B3922253 : Blo 1742572 3922253 := bbase (se 3 (by rfl) ⟨735422, by rfl⟩ : syracuseStep 3922253 = 1470845) (by norm_num)
theorem B3922325 : Blo 1742572 3922325 := bbase (se 6 (by rfl) ⟨91929, by rfl⟩ : syracuseStep 3922325 = 183859) (by norm_num)
theorem B3922397 : Blo 1742572 3922397 := bbase (se 3 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 3922397 = 1470899) (by norm_num)
theorem B9927157 : Blo 1742572 9927157 := bbase (se 5 (by rfl) ⟨465335, by rfl⟩ : syracuseStep 9927157 = 930671) (by norm_num)
theorem B1767953 : Blo 1742572 1767953 := bbase (se 2 (by rfl) ⟨662982, by rfl⟩ : syracuseStep 1767953 = 1325965) (by norm_num)
theorem B4413973 : Blo 1742572 4413973 := bbase (se 6 (by rfl) ⟨103452, by rfl⟩ : syracuseStep 4413973 = 206905) (by norm_num)
theorem B18856469 : Blo 1742572 18856469 := bbase (se 6 (by rfl) ⟨441948, by rfl⟩ : syracuseStep 18856469 = 883897) (by norm_num)
theorem B3922469 : Blo 1742572 3922469 := bbase (se 4 (by rfl) ⟨367731, by rfl⟩ : syracuseStep 3922469 = 735463) (by norm_num)
theorem B4471405 : Blo 1742572 4471405 := bbase (se 3 (by rfl) ⟨838388, by rfl⟩ : syracuseStep 4471405 = 1676777) (by norm_num)
theorem B3922541 : Blo 1742572 3922541 := bbase (se 3 (by rfl) ⟨735476, by rfl⟩ : syracuseStep 3922541 = 1470953) (by norm_num)
theorem B4414085 : Blo 1742572 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B3922613 : Blo 1742572 3922613 := bbase (se 5 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 3922613 = 367745) (by norm_num)
theorem B3922685 : Blo 1742572 3922685 := bbase (se 3 (by rfl) ⟨735503, by rfl⟩ : syracuseStep 3922685 = 1471007) (by norm_num)
theorem B3308293 : Blo 1742572 3308293 := bbase (se 4 (by rfl) ⟨310152, by rfl⟩ : syracuseStep 3308293 = 620305) (by norm_num)
theorem B3922757 : Blo 1742572 3922757 := bbase (se 4 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 3922757 = 735517) (by norm_num)
theorem B4414277 : Blo 1742572 4414277 := bbase (se 4 (by rfl) ⟨413838, by rfl⟩ : syracuseStep 4414277 = 827677) (by norm_num)
theorem B1768313 : Blo 1742572 1768313 := bbase (se 2 (by rfl) ⟨663117, by rfl⟩ : syracuseStep 1768313 = 1326235) (by norm_num)
theorem B2268037 : Blo 1742572 2268037 := bbase (se 4 (by rfl) ⟨212628, by rfl⟩ : syracuseStep 2268037 = 425257) (by norm_num)
theorem B3922829 : Blo 1742572 3922829 := bbase (se 3 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 3922829 = 1471061) (by norm_num)
theorem B7068581 : Blo 1742572 7068581 := bbase (se 4 (by rfl) ⟨662679, by rfl⟩ : syracuseStep 7068581 = 1325359) (by norm_num)
theorem B5659589 : Blo 1742572 5659589 := bbase (se 4 (by rfl) ⟨530586, by rfl⟩ : syracuseStep 5659589 = 1061173) (by norm_num)
theorem B5585861 : Blo 1742572 5585861 := bbase (se 4 (by rfl) ⟨523674, by rfl⟩ : syracuseStep 5585861 = 1047349) (by norm_num)
theorem B20126677 : Blo 1742572 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B3922901 : Blo 1742572 3922901 := bbase (se 7 (by rfl) ⟨45971, by rfl⟩ : syracuseStep 3922901 = 91943) (by norm_num)
theorem B3922973 : Blo 1742572 3922973 := bbase (se 3 (by rfl) ⟨735557, by rfl⟩ : syracuseStep 3922973 = 1471115) (by norm_num)
theorem B2481197 : Blo 1742572 2481197 := bbase (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) (by norm_num)
theorem B3308597 : Blo 1742572 3308597 := bbase (se 5 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 3308597 = 310181) (by norm_num)
theorem B3923045 : Blo 1742572 3923045 := bbase (se 4 (by rfl) ⟨367785, by rfl⟩ : syracuseStep 3923045 = 735571) (by norm_num)
theorem B4963477 : Blo 1742572 4963477 := bbase (se 6 (by rfl) ⟨116331, by rfl⟩ : syracuseStep 4963477 = 232663) (by norm_num)
theorem B4414621 : Blo 1742572 4414621 := bbase (se 3 (by rfl) ⟨827741, by rfl⟩ : syracuseStep 4414621 = 1655483) (by norm_num)
theorem B3923117 : Blo 1742572 3923117 := bbase (se 3 (by rfl) ⟨735584, by rfl⟩ : syracuseStep 3923117 = 1471169) (by norm_num)
theorem B8830133 : Blo 1742572 8830133 := bbase (se 5 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 8830133 = 827825) (by norm_num)
theorem B2792693 : Blo 1742572 2792693 := bbase (se 5 (by rfl) ⟨130907, by rfl⟩ : syracuseStep 2792693 = 261815) (by norm_num)
theorem B3923189 : Blo 1742572 3923189 := bbase (se 5 (by rfl) ⟨183899, by rfl⟩ : syracuseStep 3923189 = 367799) (by norm_num)
theorem B4414733 : Blo 1742572 4414733 := bbase (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) (by norm_num)
theorem B3923261 : Blo 1742572 3923261 := bbase (se 3 (by rfl) ⟨735611, by rfl⟩ : syracuseStep 3923261 = 1471223) (by norm_num)
theorem B6618469 : Blo 1742572 6618469 := bbase (se 4 (by rfl) ⟨620481, by rfl⟩ : syracuseStep 6618469 = 1240963) (by norm_num)
theorem B3923333 : Blo 1742572 3923333 := bbase (se 4 (by rfl) ⟨367812, by rfl⟩ : syracuseStep 3923333 = 735625) (by norm_num)
theorem B3923405 : Blo 1742572 3923405 := bbase (se 3 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 3923405 = 1471277) (by norm_num)
theorem B4414925 : Blo 1742572 4414925 := bbase (se 3 (by rfl) ⟨827798, by rfl⟩ : syracuseStep 4414925 = 1655597) (by norm_num)
theorem B5881301 : Blo 1742572 5881301 := bbase (se 7 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 5881301 = 137843) (by norm_num)
theorem B4472309 : Blo 1742572 4472309 := bbase (se 5 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 4472309 = 419279) (by norm_num)
theorem B3923477 : Blo 1742572 3923477 := bbase (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) (by norm_num)
theorem B8822357 : Blo 1742572 8822357 := bbase (se 8 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 8822357 = 103387) (by norm_num)
theorem B3923549 : Blo 1742572 3923549 := bbase (se 3 (by rfl) ⟨735665, by rfl⟩ : syracuseStep 3923549 = 1471331) (by norm_num)
theorem B6618773 : Blo 1742572 6618773 := bbase (se 6 (by rfl) ⟨155127, by rfl⟩ : syracuseStep 6618773 = 310255) (by norm_num)
theorem B3923621 : Blo 1742572 3923621 := bbase (se 4 (by rfl) ⟨367839, by rfl⟩ : syracuseStep 3923621 = 735679) (by norm_num)
theorem B11173589 : Blo 1742572 11173589 := bbase (se 7 (by rfl) ⟨130940, by rfl⟩ : syracuseStep 11173589 = 261881) (by norm_num)
theorem B2940637 : Blo 1742572 2940637 := bbase (se 3 (by rfl) ⟨551369, by rfl⟩ : syracuseStep 2940637 = 1102739) (by norm_num)
theorem B3923693 : Blo 1742572 3923693 := bbase (se 3 (by rfl) ⟨735692, by rfl⟩ : syracuseStep 3923693 = 1471385) (by norm_num)
theorem B2481949 : Blo 1742572 2481949 := bbase (se 3 (by rfl) ⟨465365, by rfl⟩ : syracuseStep 2481949 = 930731) (by norm_num)
theorem B3309349 : Blo 1742572 3309349 := bbase (se 4 (by rfl) ⟨310251, by rfl⟩ : syracuseStep 3309349 = 620503) (by norm_num)
theorem B4415269 : Blo 1742572 4415269 := bbase (se 4 (by rfl) ⟨413931, by rfl⟩ : syracuseStep 4415269 = 827863) (by norm_num)
theorem B2940725 : Blo 1742572 2940725 := bbase (se 5 (by rfl) ⟨137846, by rfl⟩ : syracuseStep 2940725 = 275693) (by norm_num)
theorem B7446325 : Blo 1742572 7446325 := bbase (se 5 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 7446325 = 698093) (by norm_num)
theorem B3923765 : Blo 1742572 3923765 := bbase (se 5 (by rfl) ⟨183926, by rfl⟩ : syracuseStep 3923765 = 367853) (by norm_num)
theorem B174407509 : Blo 1742572 174407509 := bbase (se 9 (by rfl) ⟨510959, by rfl⟩ : syracuseStep 174407509 = 1021919) (by norm_num)
theorem B2793341 : Blo 1742572 2793341 := bbase (se 3 (by rfl) ⟨523751, by rfl⟩ : syracuseStep 2793341 = 1047503) (by norm_num)
theorem B3923837 : Blo 1742572 3923837 := bbase (se 3 (by rfl) ⟨735719, by rfl⟩ : syracuseStep 3923837 = 1471439) (by norm_num)
theorem B5881733 : Blo 1742572 5881733 := bbase (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) (by norm_num)
theorem B4415381 : Blo 1742572 4415381 := bbase (se 6 (by rfl) ⟨103485, by rfl⟩ : syracuseStep 4415381 = 206971) (by norm_num)
theorem B2940853 : Blo 1742572 2940853 := bbase (se 5 (by rfl) ⟨137852, by rfl⟩ : syracuseStep 2940853 = 275705) (by norm_num)
theorem B3309493 : Blo 1742572 3309493 := bbase (se 5 (by rfl) ⟨155132, by rfl⟩ : syracuseStep 3309493 = 310265) (by norm_num)
theorem B3923909 : Blo 1742572 3923909 := bbase (se 4 (by rfl) ⟨367866, by rfl⟩ : syracuseStep 3923909 = 735733) (by norm_num)
theorem B2482177 : Blo 1742572 2482177 := bstep (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) B1861633
theorem B2940961 : Blo 1742572 2940961 := bstep (se 2 (by rfl) ⟨1102860, by rfl⟩ : syracuseStep 2940961 = 2205721) B2205721
theorem B2482211 : Blo 1742572 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B3924017 : Blo 1742572 3924017 := bstep (se 2 (by rfl) ⟨1471506, by rfl⟩ : syracuseStep 3924017 = 2943013) B2943013
theorem B2940995 : Blo 1742572 2940995 := bstep (se 1 (by rfl) ⟨2205746, by rfl⟩ : syracuseStep 2940995 = 4411493) B4411493
theorem B3924035 : Blo 1742572 3924035 := bstep (se 1 (by rfl) ⟨2943026, by rfl⟩ : syracuseStep 3924035 = 5886053) B5886053
theorem B11174051 : Blo 1742572 11174051 := bstep (se 1 (by rfl) ⟨8380538, by rfl⟩ : syracuseStep 11174051 = 16761077) B16761077
theorem B2941123 : Blo 1742572 2941123 := bstep (se 1 (by rfl) ⟨2205842, by rfl⟩ : syracuseStep 2941123 = 4411685) B4411685
theorem B2015491 : Blo 1742572 2015491 := bstep (se 1 (by rfl) ⟨1511618, by rfl⟩ : syracuseStep 2015491 = 3023237) B3023237
theorem B6619427 : Blo 1742572 6619427 := bstep (se 1 (by rfl) ⟨4964570, by rfl⟩ : syracuseStep 6619427 = 9929141) B9929141
theorem B8831267 : Blo 1742572 8831267 := bstep (se 1 (by rfl) ⟨6623450, by rfl⟩ : syracuseStep 8831267 = 13246901) B13246901
theorem B6619441 : Blo 1742572 6619441 := bstep (se 2 (by rfl) ⟨2482290, by rfl⟩ : syracuseStep 6619441 = 4964581) B4964581
theorem B2941265 : Blo 1742572 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B3924305 : Blo 1742572 3924305 := bstep (se 2 (by rfl) ⟨1471614, by rfl⟩ : syracuseStep 3924305 = 2943229) B2943229
theorem B7954787 : Blo 1742572 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B3924323 : Blo 1742572 3924323 := bstep (se 1 (by rfl) ⟨2943242, by rfl⟩ : syracuseStep 3924323 = 5886485) B5886485
theorem B4964753 : Blo 1742572 4964753 := bstep (se 2 (by rfl) ⟨1861782, by rfl⟩ : syracuseStep 4964753 = 3723565) B3723565
theorem B2941393 : Blo 1742572 2941393 := bstep (se 2 (by rfl) ⟨1103022, by rfl⟩ : syracuseStep 2941393 = 2206045) B2206045
theorem B6283747 : Blo 1742572 6283747 := bstep (se 1 (by rfl) ⟨4712810, by rfl⟩ : syracuseStep 6283747 = 9425621) B9425621
theorem B2941427 : Blo 1742572 2941427 := bstep (se 1 (by rfl) ⟨2206070, by rfl⟩ : syracuseStep 2941427 = 4412141) B4412141
theorem B5882381 : Blo 1742572 5882381 := bstep (se 3 (by rfl) ⟨1102946, by rfl⟩ : syracuseStep 5882381 = 2205893) B2205893
theorem B5587501 : Blo 1742572 5587501 := bstep (se 3 (by rfl) ⟨1047656, by rfl⟩ : syracuseStep 5587501 = 2095313) B2095313
theorem B5882435 : Blo 1742572 5882435 := bstep (se 1 (by rfl) ⟨4411826, by rfl⟩ : syracuseStep 5882435 = 8823653) B8823653
theorem B23847493 : Blo 1742572 23847493 := bstep (se 4 (by rfl) ⟨2235702, by rfl⟩ : syracuseStep 23847493 = 4471405) B4471405
theorem B2482769 : Blo 1742572 2482769 := bstep (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) B1862077
theorem B3924593 : Blo 1742572 3924593 := bstep (se 2 (by rfl) ⟨1471722, by rfl⟩ : syracuseStep 3924593 = 2943445) B2943445
theorem B2613875 : Blo 1742572 2613875 := bstep (se 1 (by rfl) ⟨1960406, by rfl⟩ : syracuseStep 2613875 = 3920813) B3920813
theorem B2941555 : Blo 1742572 2941555 := bstep (se 1 (by rfl) ⟨2206166, by rfl⟩ : syracuseStep 2941555 = 4412333) B4412333
theorem B3924611 : Blo 1742572 3924611 := bstep (se 1 (by rfl) ⟨2943458, by rfl⟩ : syracuseStep 3924611 = 5886917) B5886917
theorem B2794115 : Blo 1742572 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B2613905 : Blo 1742572 2613905 := bstep (se 2 (by rfl) ⟨980214, by rfl⟩ : syracuseStep 2613905 = 1960429) B1960429
theorem B2482849 : Blo 1742572 2482849 := bstep (se 2 (by rfl) ⟨931068, by rfl⟩ : syracuseStep 2482849 = 1862137) B1862137
theorem B2613923 : Blo 1742572 2613923 := bstep (se 1 (by rfl) ⟨1960442, by rfl⟩ : syracuseStep 2613923 = 3920885) B3920885
theorem B4473521 : Blo 1742572 4473521 := bstep (se 2 (by rfl) ⟨1677570, by rfl⟩ : syracuseStep 4473521 = 3355141) B3355141
theorem B2613953 : Blo 1742572 2613953 := bstep (se 2 (by rfl) ⟨980232, by rfl⟩ : syracuseStep 2613953 = 1960465) B1960465
theorem B2613971 : Blo 1742572 2613971 := bstep (se 1 (by rfl) ⟨1960478, by rfl⟩ : syracuseStep 2613971 = 3920957) B3920957
theorem B2614001 : Blo 1742572 2614001 := bstep (se 2 (by rfl) ⟨980250, by rfl⟩ : syracuseStep 2614001 = 1960501) B1960501
theorem B3310321 : Blo 1742572 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B2941697 : Blo 1742572 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B2614019 : Blo 1742572 2614019 := bstep (se 1 (by rfl) ⟨1960514, by rfl⟩ : syracuseStep 2614019 = 3921029) B3921029
theorem B16761613 : Blo 1742572 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B2614049 : Blo 1742572 2614049 := bstep (se 2 (by rfl) ⟨980268, by rfl⟩ : syracuseStep 2614049 = 1960537) B1960537
theorem B2614067 : Blo 1742572 2614067 := bstep (se 1 (by rfl) ⟨1960550, by rfl⟩ : syracuseStep 2614067 = 3921101) B3921101
theorem B2614097 : Blo 1742572 2614097 := bstep (se 2 (by rfl) ⟨980286, by rfl⟩ : syracuseStep 2614097 = 1960573) B1960573
theorem B5882705 : Blo 1742572 5882705 := bstep (se 2 (by rfl) ⟨2206014, by rfl⟩ : syracuseStep 5882705 = 4412029) B4412029
theorem B2614115 : Blo 1742572 2614115 := bstep (se 1 (by rfl) ⟨1960586, by rfl⟩ : syracuseStep 2614115 = 3921173) B3921173
theorem B2614145 : Blo 1742572 2614145 := bstep (se 2 (by rfl) ⟨980304, by rfl⟩ : syracuseStep 2614145 = 1960609) B1960609
theorem B2941825 : Blo 1742572 2941825 := bstep (se 2 (by rfl) ⟨1103184, by rfl⟩ : syracuseStep 2941825 = 2206369) B2206369
theorem B3924881 : Blo 1742572 3924881 := bstep (se 2 (by rfl) ⟨1471830, by rfl⟩ : syracuseStep 3924881 = 2943661) B2943661
theorem B2614163 : Blo 1742572 2614163 := bstep (se 1 (by rfl) ⟨1960622, by rfl⟩ : syracuseStep 2614163 = 3921245) B3921245
theorem B2941859 : Blo 1742572 2941859 := bstep (se 1 (by rfl) ⟨2206394, by rfl⟩ : syracuseStep 2941859 = 4412789) B4412789
theorem B3924899 : Blo 1742572 3924899 := bstep (se 1 (by rfl) ⟨2943674, by rfl⟩ : syracuseStep 3924899 = 5887349) B5887349
theorem B2614193 : Blo 1742572 2614193 := bstep (se 2 (by rfl) ⟨980322, by rfl⟩ : syracuseStep 2614193 = 1960645) B1960645
theorem B2614211 : Blo 1742572 2614211 := bstep (se 1 (by rfl) ⟨1960658, by rfl⟩ : syracuseStep 2614211 = 3921317) B3921317
theorem B19104709 : Blo 1742572 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B2614241 : Blo 1742572 2614241 := bstep (se 2 (by rfl) ⟨980340, by rfl⟩ : syracuseStep 2614241 = 1960681) B1960681
theorem B2982881 : Blo 1742572 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B2614259 : Blo 1742572 2614259 := bstep (se 1 (by rfl) ⟨1960694, by rfl⟩ : syracuseStep 2614259 = 3921389) B3921389
theorem B2614289 : Blo 1742572 2614289 := bstep (se 2 (by rfl) ⟨980358, by rfl⟩ : syracuseStep 2614289 = 1960717) B1960717
theorem B2614307 : Blo 1742572 2614307 := bstep (se 1 (by rfl) ⟨1960730, by rfl⟩ : syracuseStep 2614307 = 3921461) B3921461
theorem B4711459 : Blo 1742572 4711459 := bstep (se 1 (by rfl) ⟨3533594, by rfl⟩ : syracuseStep 4711459 = 7067189) B7067189
theorem B2941987 : Blo 1742572 2941987 := bstep (se 1 (by rfl) ⟨2206490, by rfl⟩ : syracuseStep 2941987 = 4412981) B4412981
theorem B4965425 : Blo 1742572 4965425 := bstep (se 2 (by rfl) ⟨1862034, by rfl⟩ : syracuseStep 4965425 = 3724069) B3724069
theorem B2614337 : Blo 1742572 2614337 := bstep (se 2 (by rfl) ⟨980376, by rfl⟩ : syracuseStep 2614337 = 1960753) B1960753
theorem B2614355 : Blo 1742572 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B2614385 : Blo 1742572 2614385 := bstep (se 2 (by rfl) ⟨980394, by rfl⟩ : syracuseStep 2614385 = 1960789) B1960789
theorem B2614403 : Blo 1742572 2614403 := bstep (se 1 (by rfl) ⟨1960802, by rfl⟩ : syracuseStep 2614403 = 3921605) B3921605
theorem B3310723 : Blo 1742572 3310723 := bstep (se 1 (by rfl) ⟨2483042, by rfl⟩ : syracuseStep 3310723 = 4966085) B4966085
theorem B5301389 : Blo 1742572 5301389 := bstep (se 3 (by rfl) ⟨994010, by rfl⟩ : syracuseStep 5301389 = 1988021) B1988021
theorem B2614433 : Blo 1742572 2614433 := bstep (se 2 (by rfl) ⟨980412, by rfl⟩ : syracuseStep 2614433 = 1960825) B1960825
theorem B9929891 : Blo 1742572 9929891 := bstep (se 1 (by rfl) ⟨7447418, by rfl⟩ : syracuseStep 9929891 = 14894837) B14894837
theorem B6710435 : Blo 1742572 6710435 := bstep (se 1 (by rfl) ⟨5032826, by rfl⟩ : syracuseStep 6710435 = 10065653) B10065653
theorem B2942129 : Blo 1742572 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B3310769 : Blo 1742572 3310769 := bstep (se 2 (by rfl) ⟨1241538, by rfl⟩ : syracuseStep 3310769 = 2483077) B2483077
theorem B2614451 : Blo 1742572 2614451 := bstep (se 1 (by rfl) ⟨1960838, by rfl⟩ : syracuseStep 2614451 = 3921677) B3921677
theorem B3024049 : Blo 1742572 3024049 := bstep (se 2 (by rfl) ⟨1134018, by rfl⟩ : syracuseStep 3024049 = 2268037) B2268037
theorem B3925169 : Blo 1742572 3925169 := bstep (se 2 (by rfl) ⟨1471938, by rfl⟩ : syracuseStep 3925169 = 2943877) B2943877
theorem B3925187 : Blo 1742572 3925187 := bstep (se 1 (by rfl) ⟨2943890, by rfl⟩ : syracuseStep 3925187 = 5887781) B5887781
theorem B2614481 : Blo 1742572 2614481 := bstep (se 2 (by rfl) ⟨980430, by rfl⟩ : syracuseStep 2614481 = 1960861) B1960861
theorem B2614499 : Blo 1742572 2614499 := bstep (se 1 (by rfl) ⟨1960874, by rfl⟩ : syracuseStep 2614499 = 3921749) B3921749
theorem B2614529 : Blo 1742572 2614529 := bstep (se 2 (by rfl) ⟨980448, by rfl⟩ : syracuseStep 2614529 = 1960897) B1960897
theorem B2614547 : Blo 1742572 2614547 := bstep (se 1 (by rfl) ⟨1960910, by rfl⟩ : syracuseStep 2614547 = 3921821) B3921821
theorem B2614577 : Blo 1742572 2614577 := bstep (se 2 (by rfl) ⟨980466, by rfl⟩ : syracuseStep 2614577 = 1960933) B1960933
theorem B2942257 : Blo 1742572 2942257 := bstep (se 2 (by rfl) ⟨1103346, by rfl⟩ : syracuseStep 2942257 = 2206693) B2206693
theorem B2614595 : Blo 1742572 2614595 := bstep (se 1 (by rfl) ⟨1960946, by rfl⟩ : syracuseStep 2614595 = 3921893) B3921893
theorem B2942291 : Blo 1742572 2942291 := bstep (se 1 (by rfl) ⟨2206718, by rfl⟩ : syracuseStep 2942291 = 4413437) B4413437
theorem B2614625 : Blo 1742572 2614625 := bstep (se 2 (by rfl) ⟨980484, by rfl⟩ : syracuseStep 2614625 = 1960969) B1960969
theorem B5883245 : Blo 1742572 5883245 := bstep (se 3 (by rfl) ⟨1103108, by rfl⟩ : syracuseStep 5883245 = 2206217) B2206217
theorem B2614643 : Blo 1742572 2614643 := bstep (se 1 (by rfl) ⟨1960982, by rfl⟩ : syracuseStep 2614643 = 3921965) B3921965
theorem B2614673 : Blo 1742572 2614673 := bstep (se 2 (by rfl) ⟨980502, by rfl⟩ : syracuseStep 2614673 = 1961005) B1961005
theorem B2614691 : Blo 1742572 2614691 := bstep (se 1 (by rfl) ⟨1961018, by rfl⟩ : syracuseStep 2614691 = 3922037) B3922037
theorem B5883299 : Blo 1742572 5883299 := bstep (se 1 (by rfl) ⟨4412474, by rfl⟩ : syracuseStep 5883299 = 8824949) B8824949
theorem B2483635 : Blo 1742572 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B2614721 : Blo 1742572 2614721 := bstep (se 2 (by rfl) ⟨980520, by rfl⟩ : syracuseStep 2614721 = 1961041) B1961041
theorem B11322821 : Blo 1742572 11322821 := bstep (se 4 (by rfl) ⟨1061514, by rfl⟩ : syracuseStep 11322821 = 2123029) B2123029
theorem B3311057 : Blo 1742572 3311057 := bstep (se 2 (by rfl) ⟨1241646, by rfl⟩ : syracuseStep 3311057 = 2483293) B2483293
theorem B2614739 : Blo 1742572 2614739 := bstep (se 1 (by rfl) ⟨1961054, by rfl⟩ : syracuseStep 2614739 = 3922109) B3922109
theorem B2942419 : Blo 1742572 2942419 := bstep (se 1 (by rfl) ⟨2206814, by rfl⟩ : syracuseStep 2942419 = 4413629) B4413629
theorem B14894563 : Blo 1742572 14894563 := bstep (se 1 (by rfl) ⟨11170922, by rfl⟩ : syracuseStep 14894563 = 22341845) B22341845
theorem B2614769 : Blo 1742572 2614769 := bstep (se 2 (by rfl) ⟨980538, by rfl⟩ : syracuseStep 2614769 = 1961077) B1961077
theorem B2614787 : Blo 1742572 2614787 := bstep (se 1 (by rfl) ⟨1961090, by rfl⟩ : syracuseStep 2614787 = 3922181) B3922181
theorem B2614817 : Blo 1742572 2614817 := bstep (se 2 (by rfl) ⟨980556, by rfl⟩ : syracuseStep 2614817 = 1961113) B1961113
theorem B2614835 : Blo 1742572 2614835 := bstep (se 1 (by rfl) ⟨1961126, by rfl⟩ : syracuseStep 2614835 = 3922253) B3922253
theorem B48342581 : Blo 1742572 48342581 := bstep (se 5 (by rfl) ⟨2266058, by rfl⟩ : syracuseStep 48342581 = 4532117) B4532117
theorem B2614865 : Blo 1742572 2614865 := bstep (se 2 (by rfl) ⟨980574, by rfl⟩ : syracuseStep 2614865 = 1961149) B1961149
theorem B5523025 : Blo 1742572 5523025 := bstep (se 2 (by rfl) ⟨2071134, by rfl⟩ : syracuseStep 5523025 = 4142269) B4142269
theorem B2942561 : Blo 1742572 2942561 := bstep (se 2 (by rfl) ⟨1103460, by rfl⟩ : syracuseStep 2942561 = 2206921) B2206921
theorem B2614883 : Blo 1742572 2614883 := bstep (se 1 (by rfl) ⟨1961162, by rfl⟩ : syracuseStep 2614883 = 3922325) B3922325
theorem B2614913 : Blo 1742572 2614913 := bstep (se 2 (by rfl) ⟨980592, by rfl⟩ : syracuseStep 2614913 = 1961185) B1961185
theorem B2614931 : Blo 1742572 2614931 := bstep (se 1 (by rfl) ⟨1961198, by rfl⟩ : syracuseStep 2614931 = 3922397) B3922397
theorem B5883569 : Blo 1742572 5883569 := bstep (se 2 (by rfl) ⟨2206338, by rfl⟩ : syracuseStep 5883569 = 4412677) B4412677
theorem B2614961 : Blo 1742572 2614961 := bstep (se 2 (by rfl) ⟨980610, by rfl⟩ : syracuseStep 2614961 = 1961221) B1961221
theorem B2614979 : Blo 1742572 2614979 := bstep (se 1 (by rfl) ⟨1961234, by rfl⟩ : syracuseStep 2614979 = 3922469) B3922469
theorem B7071437 : Blo 1742572 7071437 := bstep (se 3 (by rfl) ⟨1325894, by rfl⟩ : syracuseStep 7071437 = 2651789) B2651789
theorem B2615009 : Blo 1742572 2615009 := bstep (se 2 (by rfl) ⟨980628, by rfl⟩ : syracuseStep 2615009 = 1961257) B1961257
theorem B2942689 : Blo 1742572 2942689 := bstep (se 2 (by rfl) ⟨1103508, by rfl⟩ : syracuseStep 2942689 = 2207017) B2207017
theorem B6620899 : Blo 1742572 6620899 := bstep (se 1 (by rfl) ⟨4965674, by rfl⟩ : syracuseStep 6620899 = 9931349) B9931349
theorem B2615027 : Blo 1742572 2615027 := bstep (se 1 (by rfl) ⟨1961270, by rfl⟩ : syracuseStep 2615027 = 3922541) B3922541
theorem B2942723 : Blo 1742572 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B2615057 : Blo 1742572 2615057 := bstep (se 2 (by rfl) ⟨980646, by rfl⟩ : syracuseStep 2615057 = 1961293) B1961293
theorem B2615075 : Blo 1742572 2615075 := bstep (se 1 (by rfl) ⟨1961306, by rfl⟩ : syracuseStep 2615075 = 3922613) B3922613
theorem B8824625 : Blo 1742572 8824625 := bstep (se 2 (by rfl) ⟨3309234, by rfl⟩ : syracuseStep 8824625 = 6618469) B6618469
theorem B2615105 : Blo 1742572 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B4966211 : Blo 1742572 4966211 := bstep (se 1 (by rfl) ⟨3724658, by rfl⟩ : syracuseStep 4966211 = 7449317) B7449317
theorem B2615123 : Blo 1742572 2615123 := bstep (se 1 (by rfl) ⟨1961342, by rfl⟩ : syracuseStep 2615123 = 3922685) B3922685
theorem B22644593 : Blo 1742572 22644593 := bstep (se 2 (by rfl) ⟨8491722, by rfl⟩ : syracuseStep 22644593 = 16983445) B16983445
theorem B2615153 : Blo 1742572 2615153 := bstep (se 2 (by rfl) ⟨980682, by rfl⟩ : syracuseStep 2615153 = 1961365) B1961365
theorem B2615171 : Blo 1742572 2615171 := bstep (se 1 (by rfl) ⟨1961378, by rfl⟩ : syracuseStep 2615171 = 3922757) B3922757
theorem B2942851 : Blo 1742572 2942851 := bstep (se 1 (by rfl) ⟨2207138, by rfl⟩ : syracuseStep 2942851 = 4414277) B4414277
theorem B2615201 : Blo 1742572 2615201 := bstep (se 2 (by rfl) ⟨980700, by rfl⟩ : syracuseStep 2615201 = 1961401) B1961401
theorem B2615219 : Blo 1742572 2615219 := bstep (se 1 (by rfl) ⟨1961414, by rfl⟩ : syracuseStep 2615219 = 3922829) B3922829
theorem B2983859 : Blo 1742572 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B4712387 : Blo 1742572 4712387 := bstep (se 1 (by rfl) ⟨3534290, by rfl⟩ : syracuseStep 4712387 = 7068581) B7068581
theorem B2615249 : Blo 1742572 2615249 := bstep (se 2 (by rfl) ⟨980718, by rfl⟩ : syracuseStep 2615249 = 1961437) B1961437
theorem B2615267 : Blo 1742572 2615267 := bstep (se 1 (by rfl) ⟨1961450, by rfl⟩ : syracuseStep 2615267 = 3922901) B3922901
theorem B2615297 : Blo 1742572 2615297 := bstep (se 2 (by rfl) ⟨980736, by rfl⟩ : syracuseStep 2615297 = 1961473) B1961473
theorem B2942993 : Blo 1742572 2942993 := bstep (se 2 (by rfl) ⟨1103622, by rfl⟩ : syracuseStep 2942993 = 2207245) B2207245
theorem B2615315 : Blo 1742572 2615315 := bstep (se 1 (by rfl) ⟨1961486, by rfl⟩ : syracuseStep 2615315 = 3922973) B3922973
theorem B2205731 : Blo 1742572 2205731 := bstep (se 1 (by rfl) ⟨1654298, by rfl⟩ : syracuseStep 2205731 = 3308597) B3308597
theorem B2615345 : Blo 1742572 2615345 := bstep (se 2 (by rfl) ⟨980754, by rfl⟩ : syracuseStep 2615345 = 1961509) B1961509
theorem B2615363 : Blo 1742572 2615363 := bstep (se 1 (by rfl) ⟨1961522, by rfl⟩ : syracuseStep 2615363 = 3923045) B3923045
theorem B2615393 : Blo 1742572 2615393 := bstep (se 2 (by rfl) ⟨980772, by rfl⟩ : syracuseStep 2615393 = 1961545) B1961545
theorem B11176049 : Blo 1742572 11176049 := bstep (se 2 (by rfl) ⟨4191018, by rfl⟩ : syracuseStep 11176049 = 8382037) B8382037
theorem B2615411 : Blo 1742572 2615411 := bstep (se 1 (by rfl) ⟨1961558, by rfl⟩ : syracuseStep 2615411 = 3923117) B3923117
theorem B4966541 : Blo 1742572 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B3532945 : Blo 1742572 3532945 := bstep (se 2 (by rfl) ⟨1324854, by rfl⟩ : syracuseStep 3532945 = 2649709) B2649709
theorem B2615441 : Blo 1742572 2615441 := bstep (se 2 (by rfl) ⟨980790, by rfl⟩ : syracuseStep 2615441 = 1961581) B1961581
theorem B2943121 : Blo 1742572 2943121 := bstep (se 2 (by rfl) ⟨1103670, by rfl⟩ : syracuseStep 2943121 = 2207341) B2207341
theorem B1861795 : Blo 1742572 1861795 := bstep (se 1 (by rfl) ⟨1396346, by rfl⟩ : syracuseStep 1861795 = 2792693) B2792693
theorem B2615459 : Blo 1742572 2615459 := bstep (se 1 (by rfl) ⟨1961594, by rfl⟩ : syracuseStep 2615459 = 3923189) B3923189
theorem B3311779 : Blo 1742572 3311779 := bstep (se 1 (by rfl) ⟨2483834, by rfl⟩ : syracuseStep 3311779 = 4967669) B4967669
theorem B4475057 : Blo 1742572 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B2943155 : Blo 1742572 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B2615489 : Blo 1742572 2615489 := bstep (se 2 (by rfl) ⟨980808, by rfl⟩ : syracuseStep 2615489 = 1961617) B1961617
theorem B5884109 : Blo 1742572 5884109 := bstep (se 3 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 5884109 = 2206541) B2206541
theorem B4966609 : Blo 1742572 4966609 := bstep (se 2 (by rfl) ⟨1862478, by rfl⟩ : syracuseStep 4966609 = 3724957) B3724957
theorem B2615507 : Blo 1742572 2615507 := bstep (se 1 (by rfl) ⟨1961630, by rfl⟩ : syracuseStep 2615507 = 3923261) B3923261
theorem B2615537 : Blo 1742572 2615537 := bstep (se 2 (by rfl) ⟨980826, by rfl⟩ : syracuseStep 2615537 = 1961653) B1961653
theorem B5884163 : Blo 1742572 5884163 := bstep (se 1 (by rfl) ⟨4413122, by rfl⟩ : syracuseStep 5884163 = 8826245) B8826245
theorem B2615555 : Blo 1742572 2615555 := bstep (se 1 (by rfl) ⟨1961666, by rfl⟩ : syracuseStep 2615555 = 3923333) B3923333
theorem B2615585 : Blo 1742572 2615585 := bstep (se 2 (by rfl) ⟨980844, by rfl⟩ : syracuseStep 2615585 = 1961689) B1961689
theorem B2615603 : Blo 1742572 2615603 := bstep (se 1 (by rfl) ⟨1961702, by rfl⟩ : syracuseStep 2615603 = 3923405) B3923405
theorem B2943283 : Blo 1742572 2943283 := bstep (se 1 (by rfl) ⟨2207462, by rfl⟩ : syracuseStep 2943283 = 4414925) B4414925
theorem B2615633 : Blo 1742572 2615633 := bstep (se 2 (by rfl) ⟨980862, by rfl⟩ : syracuseStep 2615633 = 1961725) B1961725
theorem B2615651 : Blo 1742572 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B2615681 : Blo 1742572 2615681 := bstep (se 2 (by rfl) ⟨980880, by rfl⟩ : syracuseStep 2615681 = 1961761) B1961761
theorem B2615699 : Blo 1742572 2615699 := bstep (se 1 (by rfl) ⟨1961774, by rfl⟩ : syracuseStep 2615699 = 3923549) B3923549
theorem B2615729 : Blo 1742572 2615729 := bstep (se 2 (by rfl) ⟨980898, by rfl⟩ : syracuseStep 2615729 = 1961797) B1961797
theorem B2943425 : Blo 1742572 2943425 := bstep (se 2 (by rfl) ⟨1103784, by rfl⟩ : syracuseStep 2943425 = 2207569) B2207569
theorem B2615747 : Blo 1742572 2615747 := bstep (se 1 (by rfl) ⟨1961810, by rfl⟩ : syracuseStep 2615747 = 3923621) B3923621
theorem B2615777 : Blo 1742572 2615777 := bstep (se 2 (by rfl) ⟨980916, by rfl⟩ : syracuseStep 2615777 = 1961833) B1961833
theorem B7449059 : Blo 1742572 7449059 := bstep (se 1 (by rfl) ⟨5586794, by rfl⟩ : syracuseStep 7449059 = 11173589) B11173589
theorem B4966883 : Blo 1742572 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B2615795 : Blo 1742572 2615795 := bstep (se 1 (by rfl) ⟨1961846, by rfl⟩ : syracuseStep 2615795 = 3923693) B3923693
theorem B15092237 : Blo 1742572 15092237 := bstep (se 3 (by rfl) ⟨2829794, by rfl⟩ : syracuseStep 15092237 = 5659589) B5659589
theorem B9423373 : Blo 1742572 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B5884433 : Blo 1742572 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B2615825 : Blo 1742572 2615825 := bstep (se 2 (by rfl) ⟨980934, by rfl⟩ : syracuseStep 2615825 = 1961869) B1961869
theorem B1960483 : Blo 1742572 1960483 := bstep (se 1 (by rfl) ⟨1470362, by rfl⟩ : syracuseStep 1960483 = 2940725) B2940725
theorem B2615843 : Blo 1742572 2615843 := bstep (se 1 (by rfl) ⟨1961882, by rfl⟩ : syracuseStep 2615843 = 3923765) B3923765
theorem B2615873 : Blo 1742572 2615873 := bstep (se 2 (by rfl) ⟨980952, by rfl⟩ : syracuseStep 2615873 = 1961905) B1961905
theorem B2943553 : Blo 1742572 2943553 := bstep (se 2 (by rfl) ⟨1103832, by rfl⟩ : syracuseStep 2943553 = 2207665) B2207665
theorem B1862227 : Blo 1742572 1862227 := bstep (se 1 (by rfl) ⟨1396670, by rfl⟩ : syracuseStep 1862227 = 2793341) B2793341
theorem B2615891 : Blo 1742572 2615891 := bstep (se 1 (by rfl) ⟨1961918, by rfl⟩ : syracuseStep 2615891 = 3923837) B3923837
theorem B2943587 : Blo 1742572 2943587 := bstep (se 1 (by rfl) ⟨2207690, by rfl⟩ : syracuseStep 2943587 = 4415381) B4415381
theorem B2615921 : Blo 1742572 2615921 := bstep (se 2 (by rfl) ⟨980970, by rfl⟩ : syracuseStep 2615921 = 1961941) B1961941
theorem B2615939 : Blo 1742572 2615939 := bstep (se 1 (by rfl) ⟨1961954, by rfl⟩ : syracuseStep 2615939 = 3923909) B3923909
theorem B47696525 : Blo 1742572 47696525 := bstep (se 3 (by rfl) ⟨8943098, by rfl⟩ : syracuseStep 47696525 = 17886197) B17886197
theorem B2615969 : Blo 1742572 2615969 := bstep (se 2 (by rfl) ⟨980988, by rfl⟩ : syracuseStep 2615969 = 1961977) B1961977
theorem B1960627 : Blo 1742572 1960627 := bstep (se 1 (by rfl) ⟨1470470, by rfl⟩ : syracuseStep 1960627 = 2940941) B2940941
theorem B2615987 : Blo 1742572 2615987 := bstep (se 1 (by rfl) ⟨1961990, by rfl⟩ : syracuseStep 2615987 = 3923981) B3923981
theorem B2616017 : Blo 1742572 2616017 := bstep (se 2 (by rfl) ⟨981006, by rfl⟩ : syracuseStep 2616017 = 1962013) B1962013
theorem B2206435 : Blo 1742572 2206435 := bstep (se 1 (by rfl) ⟨1654826, by rfl⟩ : syracuseStep 2206435 = 3309653) B3309653
theorem B2616035 : Blo 1742572 2616035 := bstep (se 1 (by rfl) ⟨1962026, by rfl⟩ : syracuseStep 2616035 = 3924053) B3924053
theorem B2943715 : Blo 1742572 2943715 := bstep (se 1 (by rfl) ⟨2207786, by rfl⟩ : syracuseStep 2943715 = 4415573) B4415573
theorem B2616065 : Blo 1742572 2616065 := bstep (se 2 (by rfl) ⟨981024, by rfl⟩ : syracuseStep 2616065 = 1962049) B1962049
theorem B2616083 : Blo 1742572 2616083 := bstep (se 1 (by rfl) ⟨1962062, by rfl⟩ : syracuseStep 2616083 = 3924125) B3924125
theorem B8383267 : Blo 1742572 8383267 := bstep (se 1 (by rfl) ⟨6287450, by rfl⟩ : syracuseStep 8383267 = 12574901) B12574901
theorem B2616113 : Blo 1742572 2616113 := bstep (se 2 (by rfl) ⟨981042, by rfl⟩ : syracuseStep 2616113 = 1962085) B1962085
theorem B1960771 : Blo 1742572 1960771 := bstep (se 1 (by rfl) ⟨1470578, by rfl⟩ : syracuseStep 1960771 = 2941157) B2941157
theorem B2206531 : Blo 1742572 2206531 := bstep (se 1 (by rfl) ⟨1654898, by rfl⟩ : syracuseStep 2206531 = 3309797) B3309797
theorem B2616131 : Blo 1742572 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B2616161 : Blo 1742572 2616161 := bstep (se 2 (by rfl) ⟨981060, by rfl⟩ : syracuseStep 2616161 = 1962121) B1962121
theorem B2943857 : Blo 1742572 2943857 := bstep (se 2 (by rfl) ⟨1103946, by rfl⟩ : syracuseStep 2943857 = 2207893) B2207893
theorem B2616179 : Blo 1742572 2616179 := bstep (se 1 (by rfl) ⟨1962134, by rfl⟩ : syracuseStep 2616179 = 3924269) B3924269
theorem B2616209 : Blo 1742572 2616209 := bstep (se 2 (by rfl) ⟨981078, by rfl⟩ : syracuseStep 2616209 = 1962157) B1962157
theorem B2616227 : Blo 1742572 2616227 := bstep (se 1 (by rfl) ⟨1962170, by rfl⟩ : syracuseStep 2616227 = 3924341) B3924341
theorem B2616257 : Blo 1742572 2616257 := bstep (se 2 (by rfl) ⟨981096, by rfl⟩ : syracuseStep 2616257 = 1962193) B1962193
theorem B1960915 : Blo 1742572 1960915 := bstep (se 1 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 1960915 = 2941373) B2941373
theorem B2616275 : Blo 1742572 2616275 := bstep (se 1 (by rfl) ⟨1962206, by rfl⟩ : syracuseStep 2616275 = 3924413) B3924413
theorem B2616305 : Blo 1742572 2616305 := bstep (se 2 (by rfl) ⟨981114, by rfl⟩ : syracuseStep 2616305 = 1962229) B1962229
theorem B2616323 : Blo 1742572 2616323 := bstep (se 1 (by rfl) ⟨1962242, by rfl⟩ : syracuseStep 2616323 = 3924485) B3924485
theorem B11176973 : Blo 1742572 11176973 := bstep (se 3 (by rfl) ⟨2095682, by rfl⟩ : syracuseStep 11176973 = 4191365) B4191365
theorem B2616353 : Blo 1742572 2616353 := bstep (se 2 (by rfl) ⟨981132, by rfl⟩ : syracuseStep 2616353 = 1962265) B1962265
theorem B5884973 : Blo 1742572 5884973 := bstep (se 3 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 5884973 = 2206865) B2206865
theorem B2616371 : Blo 1742572 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B2616401 : Blo 1742572 2616401 := bstep (se 2 (by rfl) ⟨981150, by rfl⟩ : syracuseStep 2616401 = 1962301) B1962301
theorem B1961059 : Blo 1742572 1961059 := bstep (se 1 (by rfl) ⟨1470794, by rfl⟩ : syracuseStep 1961059 = 2941589) B2941589
theorem B5885027 : Blo 1742572 5885027 := bstep (se 1 (by rfl) ⟨4413770, by rfl⟩ : syracuseStep 5885027 = 8827541) B8827541
theorem B2616419 : Blo 1742572 2616419 := bstep (se 1 (by rfl) ⟨1962314, by rfl⟩ : syracuseStep 2616419 = 3924629) B3924629
theorem B2616449 : Blo 1742572 2616449 := bstep (se 2 (by rfl) ⟨981168, by rfl⟩ : syracuseStep 2616449 = 1962337) B1962337
theorem B13233293 : Blo 1742572 13233293 := bstep (se 3 (by rfl) ⟨2481242, by rfl⟩ : syracuseStep 13233293 = 4962485) B4962485
theorem B23850125 : Blo 1742572 23850125 := bstep (se 3 (by rfl) ⟨4471898, by rfl⟩ : syracuseStep 23850125 = 8943797) B8943797
theorem B2616467 : Blo 1742572 2616467 := bstep (se 1 (by rfl) ⟨1962350, by rfl⟩ : syracuseStep 2616467 = 3924701) B3924701
theorem B3140785 : Blo 1742572 3140785 := bstep (se 2 (by rfl) ⟨1177794, by rfl⟩ : syracuseStep 3140785 = 2355589) B2355589
theorem B8490161 : Blo 1742572 8490161 := bstep (se 2 (by rfl) ⟨3183810, by rfl⟩ : syracuseStep 8490161 = 6367621) B6367621
theorem B2616497 : Blo 1742572 2616497 := bstep (se 2 (by rfl) ⟨981186, by rfl⟩ : syracuseStep 2616497 = 1962373) B1962373
theorem B2616515 : Blo 1742572 2616515 := bstep (se 1 (by rfl) ⟨1962386, by rfl⟩ : syracuseStep 2616515 = 3924773) B3924773
theorem B1912019 : Blo 1742572 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B2616545 : Blo 1742572 2616545 := bstep (se 2 (by rfl) ⟨981204, by rfl⟩ : syracuseStep 2616545 = 1962409) B1962409
theorem B8826083 : Blo 1742572 8826083 := bstep (se 1 (by rfl) ⟨6619562, by rfl⟩ : syracuseStep 8826083 = 13239125) B13239125
theorem B1961203 : Blo 1742572 1961203 := bstep (se 1 (by rfl) ⟨1470902, by rfl⟩ : syracuseStep 1961203 = 2941805) B2941805
theorem B2616563 : Blo 1742572 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B2616593 : Blo 1742572 2616593 := bstep (se 2 (by rfl) ⟨981222, by rfl⟩ : syracuseStep 2616593 = 1962445) B1962445
theorem B2616611 : Blo 1742572 2616611 := bstep (se 1 (by rfl) ⟨1962458, by rfl⟩ : syracuseStep 2616611 = 3924917) B3924917
theorem B4967725 : Blo 1742572 4967725 := bstep (se 3 (by rfl) ⟨931448, by rfl⟩ : syracuseStep 4967725 = 1862897) B1862897
theorem B2207027 : Blo 1742572 2207027 := bstep (se 1 (by rfl) ⟨1655270, by rfl⟩ : syracuseStep 2207027 = 3310541) B3310541
theorem B2616641 : Blo 1742572 2616641 := bstep (se 2 (by rfl) ⟨981240, by rfl⟩ : syracuseStep 2616641 = 1962481) B1962481
theorem B2616659 : Blo 1742572 2616659 := bstep (se 1 (by rfl) ⟨1962494, by rfl⟩ : syracuseStep 2616659 = 3924989) B3924989
theorem B5885297 : Blo 1742572 5885297 := bstep (se 2 (by rfl) ⟨2206986, by rfl⟩ : syracuseStep 5885297 = 4413973) B4413973
theorem B2616689 : Blo 1742572 2616689 := bstep (se 2 (by rfl) ⟨981258, by rfl⟩ : syracuseStep 2616689 = 1962517) B1962517
theorem B1961347 : Blo 1742572 1961347 := bstep (se 1 (by rfl) ⟨1471010, by rfl⟩ : syracuseStep 1961347 = 2942021) B2942021
theorem B2616707 : Blo 1742572 2616707 := bstep (se 1 (by rfl) ⟨1962530, by rfl⟩ : syracuseStep 2616707 = 3925061) B3925061
theorem B2616737 : Blo 1742572 2616737 := bstep (se 2 (by rfl) ⟨981276, by rfl⟩ : syracuseStep 2616737 = 1962553) B1962553
theorem B2829745 : Blo 1742572 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B3976625 : Blo 1742572 3976625 := bstep (se 2 (by rfl) ⟨1491234, by rfl⟩ : syracuseStep 3976625 = 2982469) B2982469
theorem B2616755 : Blo 1742572 2616755 := bstep (se 1 (by rfl) ⟨1962566, by rfl⟩ : syracuseStep 2616755 = 3925133) B3925133
theorem B4967885 : Blo 1742572 4967885 := bstep (se 3 (by rfl) ⟨931478, by rfl⟩ : syracuseStep 4967885 = 1862957) B1862957
theorem B2616785 : Blo 1742572 2616785 := bstep (se 2 (by rfl) ⟨981294, by rfl⟩ : syracuseStep 2616785 = 1962589) B1962589
theorem B2616803 : Blo 1742572 2616803 := bstep (se 1 (by rfl) ⟨1962602, by rfl⟩ : syracuseStep 2616803 = 3925205) B3925205
theorem B2616833 : Blo 1742572 2616833 := bstep (se 2 (by rfl) ⟨981312, by rfl⟩ : syracuseStep 2616833 = 1962625) B1962625
theorem B1961491 : Blo 1742572 1961491 := bstep (se 1 (by rfl) ⟨1471118, by rfl⟩ : syracuseStep 1961491 = 2942237) B2942237
theorem B2616851 : Blo 1742572 2616851 := bstep (se 1 (by rfl) ⟨1962638, by rfl⟩ : syracuseStep 2616851 = 3925277) B3925277
theorem B1961635 : Blo 1742572 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B4411057 : Blo 1742572 4411057 := bstep (se 2 (by rfl) ⟨1654146, by rfl⟩ : syracuseStep 4411057 = 3308293) B3308293
theorem B7450289 : Blo 1742572 7450289 := bstep (se 2 (by rfl) ⟨2793858, by rfl⟩ : syracuseStep 7450289 = 5587717) B5587717
theorem B101928725 : Blo 1742572 101928725 := bstep (se 6 (by rfl) ⟨2388954, by rfl⟩ : syracuseStep 101928725 = 4777909) B4777909
theorem B1961779 : Blo 1742572 1961779 := bstep (se 1 (by rfl) ⟨1471334, by rfl⟩ : syracuseStep 1961779 = 2942669) B2942669
theorem B5304163 : Blo 1742572 5304163 := bstep (se 1 (by rfl) ⟨3978122, by rfl⟩ : syracuseStep 5304163 = 7956245) B7956245
theorem B10604429 : Blo 1742572 10604429 := bstep (se 3 (by rfl) ⟨1988330, by rfl⟩ : syracuseStep 10604429 = 3976661) B3976661
theorem B5885837 : Blo 1742572 5885837 := bstep (se 3 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 5885837 = 2207189) B2207189
theorem B6623117 : Blo 1742572 6623117 := bstep (se 3 (by rfl) ⟨1241834, by rfl⟩ : syracuseStep 6623117 = 2483669) B2483669
theorem B9924515 : Blo 1742572 9924515 := bstep (se 1 (by rfl) ⟨7443386, by rfl⟩ : syracuseStep 9924515 = 14886773) B14886773
theorem B4411331 : Blo 1742572 4411331 := bstep (se 1 (by rfl) ⟨3308498, by rfl⟩ : syracuseStep 4411331 = 6616997) B6616997
theorem B1961923 : Blo 1742572 1961923 := bstep (se 1 (by rfl) ⟨1471442, by rfl⟩ : syracuseStep 1961923 = 2942885) B2942885
theorem B5885891 : Blo 1742572 5885891 := bstep (se 1 (by rfl) ⟨4414418, by rfl⟩ : syracuseStep 5885891 = 8828837) B8828837
theorem B2650099 : Blo 1742572 2650099 := bstep (se 1 (by rfl) ⟨1987574, by rfl⟩ : syracuseStep 2650099 = 3975149) B3975149
theorem B2207731 : Blo 1742572 2207731 := bstep (se 1 (by rfl) ⟨1655798, by rfl⟩ : syracuseStep 2207731 = 3311597) B3311597
theorem B8826893 : Blo 1742572 8826893 := bstep (se 3 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 8826893 = 3310085) B3310085
theorem B5304355 : Blo 1742572 5304355 := bstep (se 1 (by rfl) ⟨3978266, by rfl⟩ : syracuseStep 5304355 = 7956533) B7956533
theorem B4714541 : Blo 1742572 4714541 := bstep (se 3 (by rfl) ⟨883976, by rfl⟩ : syracuseStep 4714541 = 1767953) B1767953
theorem B1962067 : Blo 1742572 1962067 := bstep (se 1 (by rfl) ⟨1471550, by rfl⟩ : syracuseStep 1962067 = 2943101) B2943101
theorem B2207827 : Blo 1742572 2207827 := bstep (se 1 (by rfl) ⟨1655870, by rfl⟩ : syracuseStep 2207827 = 3311741) B3311741
theorem B4714595 : Blo 1742572 4714595 := bstep (se 1 (by rfl) ⟨3535946, by rfl⟩ : syracuseStep 4714595 = 7071893) B7071893
theorem B2355329 : Blo 1742572 2355329 := bstep (se 2 (by rfl) ⟨883248, by rfl⟩ : syracuseStep 2355329 = 1766497) B1766497
theorem B4411523 : Blo 1742572 4411523 := bstep (se 1 (by rfl) ⟨3308642, by rfl⟩ : syracuseStep 4411523 = 6617285) B6617285
theorem B5886161 : Blo 1742572 5886161 := bstep (se 2 (by rfl) ⟨2207310, by rfl⟩ : syracuseStep 5886161 = 4414621) B4414621
theorem B1962211 : Blo 1742572 1962211 := bstep (se 1 (by rfl) ⟨1471658, by rfl⟩ : syracuseStep 1962211 = 2943317) B2943317
theorem B12570979 : Blo 1742572 12570979 := bstep (se 1 (by rfl) ⟨9428234, by rfl⟩ : syracuseStep 12570979 = 18856469) B18856469
theorem B1962355 : Blo 1742572 1962355 := bstep (se 1 (by rfl) ⟨1471766, by rfl⟩ : syracuseStep 1962355 = 2943533) B2943533
theorem B3977603 : Blo 1742572 3977603 := bstep (se 1 (by rfl) ⟨2983202, by rfl⟩ : syracuseStep 3977603 = 5966405) B5966405
theorem B1962499 : Blo 1742572 1962499 := bstep (se 1 (by rfl) ⟨1471874, by rfl⟩ : syracuseStep 1962499 = 2943749) B2943749
theorem B3723907 : Blo 1742572 3723907 := bstep (se 1 (by rfl) ⟨2792930, by rfl⟩ : syracuseStep 3723907 = 5585861) B5585861
theorem B1962643 : Blo 1742572 1962643 := bstep (se 1 (by rfl) ⟨1471982, by rfl⟩ : syracuseStep 1962643 = 2943965) B2943965
theorem B2388659 : Blo 1742572 2388659 := bstep (se 1 (by rfl) ⟨1791494, by rfl⟩ : syracuseStep 2388659 = 3582989) B3582989
theorem B5305027 : Blo 1742572 5305027 := bstep (se 1 (by rfl) ⟨3978770, by rfl⟩ : syracuseStep 5305027 = 7957541) B7957541
theorem B5886701 : Blo 1742572 5886701 := bstep (se 3 (by rfl) ⟨1103756, by rfl⟩ : syracuseStep 5886701 = 2207513) B2207513
theorem B5886755 : Blo 1742572 5886755 := bstep (se 1 (by rfl) ⟨4415066, by rfl⟩ : syracuseStep 5886755 = 8830133) B8830133
theorem B4191011 : Blo 1742572 4191011 := bstep (se 1 (by rfl) ⟨3143258, by rfl⟩ : syracuseStep 4191011 = 6286517) B6286517
theorem B21214021 : Blo 1742572 21214021 := bstep (se 4 (by rfl) ⟨1988814, by rfl⟩ : syracuseStep 21214021 = 3977629) B3977629
theorem B35779441 : Blo 1742572 35779441 := bstep (se 2 (by rfl) ⟨13417290, by rfl⟩ : syracuseStep 35779441 = 26834581) B26834581
theorem B9925517 : Blo 1742572 9925517 := bstep (se 3 (by rfl) ⟨1861034, by rfl⟩ : syracuseStep 9925517 = 3722069) B3722069
theorem B5583821 : Blo 1742572 5583821 := bstep (se 3 (by rfl) ⟨1046966, by rfl⟩ : syracuseStep 5583821 = 2093933) B2093933
theorem B3920849 : Blo 1742572 3920849 := bstep (se 2 (by rfl) ⟨1470318, by rfl⟩ : syracuseStep 3920849 = 2940637) B2940637
theorem B3920867 : Blo 1742572 3920867 := bstep (se 1 (by rfl) ⟨2940650, by rfl⟩ : syracuseStep 3920867 = 5881301) B5881301
theorem B4715501 : Blo 1742572 4715501 := bstep (se 3 (by rfl) ⟨884156, by rfl⟩ : syracuseStep 4715501 = 1768313) B1768313
theorem B4412465 : Blo 1742572 4412465 := bstep (se 2 (by rfl) ⟨1654674, by rfl⟩ : syracuseStep 4412465 = 3309349) B3309349
theorem B5887025 : Blo 1742572 5887025 := bstep (se 2 (by rfl) ⟨2207634, by rfl⟩ : syracuseStep 5887025 = 4415269) B4415269
theorem B4412515 : Blo 1742572 4412515 := bstep (se 1 (by rfl) ⟨3309386, by rfl⟩ : syracuseStep 4412515 = 6618773) B6618773
theorem B232543345 : Blo 1742572 232543345 := bstep (se 2 (by rfl) ⟨87203754, by rfl⟩ : syracuseStep 232543345 = 174407509) B174407509
theorem B2651267 : Blo 1742572 2651267 := bstep (se 1 (by rfl) ⟨1988450, by rfl⟩ : syracuseStep 2651267 = 3976901) B3976901
theorem B2094275 : Blo 1742572 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B3921137 : Blo 1742572 3921137 := bstep (se 2 (by rfl) ⟨1470426, by rfl⟩ : syracuseStep 3921137 = 2940853) B2940853
theorem B4412657 : Blo 1742572 4412657 := bstep (se 2 (by rfl) ⟨1654746, by rfl⟩ : syracuseStep 4412657 = 3309493) B3309493
theorem B3921155 : Blo 1742572 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B7460237 : Blo 1742572 7460237 := bstep (se 3 (by rfl) ⟨1398794, by rfl⟩ : syracuseStep 7460237 = 2797589) B2797589
theorem B2356627 : Blo 1742572 2356627 := bstep (se 1 (by rfl) ⟨1767470, by rfl⟩ : syracuseStep 2356627 = 3534941) B3534941
theorem B13424069 : Blo 1742572 13424069 := bstep (se 4 (by rfl) ⟨1258506, by rfl⟩ : syracuseStep 13424069 = 2517013) B2517013
theorem B6616525 : Blo 1742572 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B11171333 : Blo 1742572 11171333 := bstep (se 4 (by rfl) ⟨1047312, by rfl⟩ : syracuseStep 11171333 = 2094625) B2094625
theorem B3921425 : Blo 1742572 3921425 := bstep (se 2 (by rfl) ⟨1470534, by rfl⟩ : syracuseStep 3921425 = 2941069) B2941069
theorem B3921443 : Blo 1742572 3921443 := bstep (se 1 (by rfl) ⟨2941082, by rfl⟩ : syracuseStep 3921443 = 5882165) B5882165
theorem B2389537 : Blo 1742572 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B5887565 : Blo 1742572 5887565 := bstep (se 3 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 5887565 = 2207837) B2207837
theorem B5887619 : Blo 1742572 5887619 := bstep (se 1 (by rfl) ⟨4415714, by rfl⟩ : syracuseStep 5887619 = 8831429) B8831429
theorem B1742579 : Blo 1742572 1742579 := bstep (se 1 (by rfl) ⟨1306934, by rfl⟩ : syracuseStep 1742579 = 2613869) B2613869
theorem B1742595 : Blo 1742572 1742595 := bstep (se 1 (by rfl) ⟨1306946, by rfl⟩ : syracuseStep 1742595 = 2613893) B2613893
theorem B1742611 : Blo 1742572 1742611 := bstep (se 1 (by rfl) ⟨1306958, by rfl⟩ : syracuseStep 1742611 = 2613917) B2613917
theorem B1742627 : Blo 1742572 1742627 := bstep (se 1 (by rfl) ⟨1306970, by rfl⟩ : syracuseStep 1742627 = 2613941) B2613941
theorem B3921713 : Blo 1742572 3921713 := bstep (se 2 (by rfl) ⟨1470642, by rfl⟩ : syracuseStep 3921713 = 2941285) B2941285
theorem B1742643 : Blo 1742572 1742643 := bstep (se 1 (by rfl) ⟨1306982, by rfl⟩ : syracuseStep 1742643 = 2613965) B2613965
theorem B1742659 : Blo 1742572 1742659 := bstep (se 1 (by rfl) ⟨1306994, by rfl⟩ : syracuseStep 1742659 = 2613989) B2613989
theorem B3921731 : Blo 1742572 3921731 := bstep (se 1 (by rfl) ⟨2941298, by rfl⟩ : syracuseStep 3921731 = 5882597) B5882597
theorem B1742675 : Blo 1742572 1742675 := bstep (se 1 (by rfl) ⟨1307006, by rfl⟩ : syracuseStep 1742675 = 2614013) B2614013
theorem B1742691 : Blo 1742572 1742691 := bstep (se 1 (by rfl) ⟨1307018, by rfl⟩ : syracuseStep 1742691 = 2614037) B2614037
theorem B1742707 : Blo 1742572 1742707 := bstep (se 1 (by rfl) ⟨1307030, by rfl⟩ : syracuseStep 1742707 = 2614061) B2614061
theorem B1742723 : Blo 1742572 1742723 := bstep (se 1 (by rfl) ⟨1307042, by rfl⟩ : syracuseStep 1742723 = 2614085) B2614085
theorem B5887889 : Blo 1742572 5887889 := bstep (se 2 (by rfl) ⟨2207958, by rfl⟩ : syracuseStep 5887889 = 4415917) B4415917
theorem B1742739 : Blo 1742572 1742739 := bstep (se 1 (by rfl) ⟨1307054, by rfl⟩ : syracuseStep 1742739 = 2614109) B2614109
theorem B1742755 : Blo 1742572 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B9426851 : Blo 1742572 9426851 := bstep (se 1 (by rfl) ⟨7070138, by rfl⟩ : syracuseStep 9426851 = 14140277) B14140277
theorem B1742771 : Blo 1742572 1742771 := bstep (se 1 (by rfl) ⟨1307078, by rfl⟩ : syracuseStep 1742771 = 2614157) B2614157
theorem B1742787 : Blo 1742572 1742787 := bstep (se 1 (by rfl) ⟨1307090, by rfl⟩ : syracuseStep 1742787 = 2614181) B2614181
theorem B1742803 : Blo 1742572 1742803 := bstep (se 1 (by rfl) ⟨1307102, by rfl⟩ : syracuseStep 1742803 = 2614205) B2614205
theorem B1742819 : Blo 1742572 1742819 := bstep (se 1 (by rfl) ⟨1307114, by rfl⟩ : syracuseStep 1742819 = 2614229) B2614229
theorem B13236209 : Blo 1742572 13236209 := bstep (se 2 (by rfl) ⟨4963578, by rfl⟩ : syracuseStep 13236209 = 9927157) B9927157
theorem B1742835 : Blo 1742572 1742835 := bstep (se 1 (by rfl) ⟨1307126, by rfl⟩ : syracuseStep 1742835 = 2614253) B2614253
theorem B1742851 : Blo 1742572 1742851 := bstep (se 1 (by rfl) ⟨1307138, by rfl⟩ : syracuseStep 1742851 = 2614277) B2614277
theorem B1742867 : Blo 1742572 1742867 := bstep (se 1 (by rfl) ⟨1307150, by rfl⟩ : syracuseStep 1742867 = 2614301) B2614301
theorem B1742883 : Blo 1742572 1742883 := bstep (se 1 (by rfl) ⟨1307162, by rfl⟩ : syracuseStep 1742883 = 2614325) B2614325
theorem B1742899 : Blo 1742572 1742899 := bstep (se 1 (by rfl) ⟨1307174, by rfl⟩ : syracuseStep 1742899 = 2614349) B2614349
theorem B1742915 : Blo 1742572 1742915 := bstep (se 1 (by rfl) ⟨1307186, by rfl⟩ : syracuseStep 1742915 = 2614373) B2614373
theorem B3922001 : Blo 1742572 3922001 := bstep (se 2 (by rfl) ⟨1470750, by rfl⟩ : syracuseStep 3922001 = 2941501) B2941501
theorem B1742931 : Blo 1742572 1742931 := bstep (se 1 (by rfl) ⟨1307198, by rfl⟩ : syracuseStep 1742931 = 2614397) B2614397
theorem B1742947 : Blo 1742572 1742947 := bstep (se 1 (by rfl) ⟨1307210, by rfl⟩ : syracuseStep 1742947 = 2614421) B2614421
theorem B3922019 : Blo 1742572 3922019 := bstep (se 1 (by rfl) ⟨2941514, by rfl⟩ : syracuseStep 3922019 = 5883029) B5883029
theorem B1742963 : Blo 1742572 1742963 := bstep (se 1 (by rfl) ⟨1307222, by rfl⟩ : syracuseStep 1742963 = 2614445) B2614445
theorem B2652275 : Blo 1742572 2652275 := bstep (se 1 (by rfl) ⟨1989206, by rfl⟩ : syracuseStep 2652275 = 3978413) B3978413
theorem B1742979 : Blo 1742572 1742979 := bstep (se 1 (by rfl) ⟨1307234, by rfl⟩ : syracuseStep 1742979 = 2614469) B2614469
theorem B1742995 : Blo 1742572 1742995 := bstep (se 1 (by rfl) ⟨1307246, by rfl⟩ : syracuseStep 1742995 = 2614493) B2614493
theorem B1743011 : Blo 1742572 1743011 := bstep (se 1 (by rfl) ⟨1307258, by rfl⟩ : syracuseStep 1743011 = 2614517) B2614517
theorem B3356849 : Blo 1742572 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B2791603 : Blo 1742572 2791603 := bstep (se 1 (by rfl) ⟨2093702, by rfl⟩ : syracuseStep 2791603 = 4187405) B4187405
theorem B1743027 : Blo 1742572 1743027 := bstep (se 1 (by rfl) ⟨1307270, by rfl⟩ : syracuseStep 1743027 = 2614541) B2614541
theorem B1743043 : Blo 1742572 1743043 := bstep (se 1 (by rfl) ⟨1307282, by rfl⟩ : syracuseStep 1743043 = 2614565) B2614565
theorem B4962509 : Blo 1742572 4962509 := bstep (se 3 (by rfl) ⟨930470, by rfl⟩ : syracuseStep 4962509 = 1860941) B1860941
theorem B7444685 : Blo 1742572 7444685 := bstep (se 3 (by rfl) ⟨1395878, by rfl⟩ : syracuseStep 7444685 = 2791757) B2791757
theorem B4413649 : Blo 1742572 4413649 := bstep (se 2 (by rfl) ⟨1655118, by rfl⟩ : syracuseStep 4413649 = 3310237) B3310237
theorem B1743059 : Blo 1742572 1743059 := bstep (se 1 (by rfl) ⟨1307294, by rfl⟩ : syracuseStep 1743059 = 2614589) B2614589
theorem B6617315 : Blo 1742572 6617315 := bstep (se 1 (by rfl) ⟨4962986, by rfl⟩ : syracuseStep 6617315 = 9925973) B9925973
theorem B1743075 : Blo 1742572 1743075 := bstep (se 1 (by rfl) ⟨1307306, by rfl⟩ : syracuseStep 1743075 = 2614613) B2614613
theorem B8493283 : Blo 1742572 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B1743091 : Blo 1742572 1743091 := bstep (se 1 (by rfl) ⟨1307318, by rfl⟩ : syracuseStep 1743091 = 2614637) B2614637
theorem B1743107 : Blo 1742572 1743107 := bstep (se 1 (by rfl) ⟨1307330, by rfl⟩ : syracuseStep 1743107 = 2614661) B2614661
theorem B1743123 : Blo 1742572 1743123 := bstep (se 1 (by rfl) ⟨1307342, by rfl⟩ : syracuseStep 1743123 = 2614685) B2614685
theorem B1743139 : Blo 1742572 1743139 := bstep (se 1 (by rfl) ⟨1307354, by rfl⟩ : syracuseStep 1743139 = 2614709) B2614709
theorem B1743155 : Blo 1742572 1743155 := bstep (se 1 (by rfl) ⟨1307366, by rfl⟩ : syracuseStep 1743155 = 2614733) B2614733
theorem B1743171 : Blo 1742572 1743171 := bstep (se 1 (by rfl) ⟨1307378, by rfl⟩ : syracuseStep 1743171 = 2614757) B2614757
theorem B1743187 : Blo 1742572 1743187 := bstep (se 1 (by rfl) ⟨1307390, by rfl⟩ : syracuseStep 1743187 = 2614781) B2614781
theorem B1743203 : Blo 1742572 1743203 := bstep (se 1 (by rfl) ⟨1307402, by rfl⟩ : syracuseStep 1743203 = 2614805) B2614805
theorem B3922289 : Blo 1742572 3922289 := bstep (se 2 (by rfl) ⟨1470858, by rfl⟩ : syracuseStep 3922289 = 2941717) B2941717
theorem B1743219 : Blo 1742572 1743219 := bstep (se 1 (by rfl) ⟨1307414, by rfl⟩ : syracuseStep 1743219 = 2614829) B2614829
theorem B1743235 : Blo 1742572 1743235 := bstep (se 1 (by rfl) ⟨1307426, by rfl⟩ : syracuseStep 1743235 = 2614853) B2614853
theorem B3922307 : Blo 1742572 3922307 := bstep (se 1 (by rfl) ⟨2941730, by rfl⟩ : syracuseStep 3922307 = 5883461) B5883461
theorem B1743251 : Blo 1742572 1743251 := bstep (se 1 (by rfl) ⟨1307438, by rfl⟩ : syracuseStep 1743251 = 2614877) B2614877
theorem B1743267 : Blo 1742572 1743267 := bstep (se 1 (by rfl) ⟨1307450, by rfl⟩ : syracuseStep 1743267 = 2614901) B2614901
theorem B1743283 : Blo 1742572 1743283 := bstep (se 1 (by rfl) ⟨1307462, by rfl⟩ : syracuseStep 1743283 = 2614925) B2614925
theorem B1743299 : Blo 1742572 1743299 := bstep (se 1 (by rfl) ⟨1307474, by rfl⟩ : syracuseStep 1743299 = 2614949) B2614949
theorem B3725777 : Blo 1742572 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B1743315 : Blo 1742572 1743315 := bstep (se 1 (by rfl) ⟨1307486, by rfl⟩ : syracuseStep 1743315 = 2614973) B2614973
theorem B1743331 : Blo 1742572 1743331 := bstep (se 1 (by rfl) ⟨1307498, by rfl⟩ : syracuseStep 1743331 = 2614997) B2614997
theorem B4413923 : Blo 1742572 4413923 := bstep (se 1 (by rfl) ⟨3310442, by rfl⟩ : syracuseStep 4413923 = 6620885) B6620885
theorem B1743347 : Blo 1742572 1743347 := bstep (se 1 (by rfl) ⟨1307510, by rfl⟩ : syracuseStep 1743347 = 2615021) B2615021
theorem B1743363 : Blo 1742572 1743363 := bstep (se 1 (by rfl) ⟨1307522, by rfl⟩ : syracuseStep 1743363 = 2615045) B2615045
theorem B5585411 : Blo 1742572 5585411 := bstep (se 1 (by rfl) ⟨4189058, by rfl⟩ : syracuseStep 5585411 = 8378117) B8378117
theorem B1743379 : Blo 1742572 1743379 := bstep (se 1 (by rfl) ⟨1307534, by rfl⟩ : syracuseStep 1743379 = 2615069) B2615069
theorem B7445027 : Blo 1742572 7445027 := bstep (se 1 (by rfl) ⟨5583770, by rfl⟩ : syracuseStep 7445027 = 11167541) B11167541
theorem B1743395 : Blo 1742572 1743395 := bstep (se 1 (by rfl) ⟨1307546, by rfl⟩ : syracuseStep 1743395 = 2615093) B2615093
theorem B1743411 : Blo 1742572 1743411 := bstep (se 1 (by rfl) ⟨1307558, by rfl⟩ : syracuseStep 1743411 = 2615117) B2615117
theorem B1743427 : Blo 1742572 1743427 := bstep (se 1 (by rfl) ⟨1307570, by rfl⟩ : syracuseStep 1743427 = 2615141) B2615141
theorem B1743443 : Blo 1742572 1743443 := bstep (se 1 (by rfl) ⟨1307582, by rfl⟩ : syracuseStep 1743443 = 2615165) B2615165
theorem B1743459 : Blo 1742572 1743459 := bstep (se 1 (by rfl) ⟨1307594, by rfl⟩ : syracuseStep 1743459 = 2615189) B2615189
theorem B26835569 : Blo 1742572 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B1743475 : Blo 1742572 1743475 := bstep (se 1 (by rfl) ⟨1307606, by rfl⟩ : syracuseStep 1743475 = 2615213) B2615213
theorem B2792065 : Blo 1742572 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B1743491 : Blo 1742572 1743491 := bstep (se 1 (by rfl) ⟨1307618, by rfl⟩ : syracuseStep 1743491 = 2615237) B2615237
theorem B3922577 : Blo 1742572 3922577 := bstep (se 2 (by rfl) ⟨1470966, by rfl⟩ : syracuseStep 3922577 = 2941933) B2941933
theorem B1743507 : Blo 1742572 1743507 := bstep (se 1 (by rfl) ⟨1307630, by rfl⟩ : syracuseStep 1743507 = 2615261) B2615261
theorem B3308195 : Blo 1742572 3308195 := bstep (se 1 (by rfl) ⟨2481146, by rfl⟩ : syracuseStep 3308195 = 4962293) B4962293
theorem B3922595 : Blo 1742572 3922595 := bstep (se 1 (by rfl) ⟨2941946, by rfl⟩ : syracuseStep 3922595 = 5883893) B5883893
theorem B1743523 : Blo 1742572 1743523 := bstep (se 1 (by rfl) ⟨1307642, by rfl⟩ : syracuseStep 1743523 = 2615285) B2615285
theorem B4414115 : Blo 1742572 4414115 := bstep (se 1 (by rfl) ⟨3310586, by rfl⟩ : syracuseStep 4414115 = 6621173) B6621173
theorem B1743539 : Blo 1742572 1743539 := bstep (se 1 (by rfl) ⟨1307654, by rfl⟩ : syracuseStep 1743539 = 2615309) B2615309
theorem B1743555 : Blo 1742572 1743555 := bstep (se 1 (by rfl) ⟨1307666, by rfl⟩ : syracuseStep 1743555 = 2615333) B2615333
theorem B9550541 : Blo 1742572 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B1743571 : Blo 1742572 1743571 := bstep (se 1 (by rfl) ⟨1307678, by rfl⟩ : syracuseStep 1743571 = 2615357) B2615357
theorem B2792161 : Blo 1742572 2792161 := bstep (se 2 (by rfl) ⟨1047060, by rfl⟩ : syracuseStep 2792161 = 2094121) B2094121
theorem B1743587 : Blo 1742572 1743587 := bstep (se 1 (by rfl) ⟨1307690, by rfl⟩ : syracuseStep 1743587 = 2615381) B2615381
theorem B9427697 : Blo 1742572 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B1743603 : Blo 1742572 1743603 := bstep (se 1 (by rfl) ⟨1307702, by rfl⟩ : syracuseStep 1743603 = 2615405) B2615405
theorem B1743619 : Blo 1742572 1743619 := bstep (se 1 (by rfl) ⟨1307714, by rfl⟩ : syracuseStep 1743619 = 2615429) B2615429
theorem B1743635 : Blo 1742572 1743635 := bstep (se 1 (by rfl) ⟨1307726, by rfl⟩ : syracuseStep 1743635 = 2615453) B2615453
theorem B1743651 : Blo 1742572 1743651 := bstep (se 1 (by rfl) ⟨1307738, by rfl⟩ : syracuseStep 1743651 = 2615477) B2615477
theorem B6708017 : Blo 1742572 6708017 := bstep (se 2 (by rfl) ⟨2515506, by rfl⟩ : syracuseStep 6708017 = 5031013) B5031013
theorem B1743667 : Blo 1742572 1743667 := bstep (se 1 (by rfl) ⟨1307750, by rfl⟩ : syracuseStep 1743667 = 2615501) B2615501
theorem B1743683 : Blo 1742572 1743683 := bstep (se 1 (by rfl) ⟨1307762, by rfl⟩ : syracuseStep 1743683 = 2615525) B2615525
theorem B1743699 : Blo 1742572 1743699 := bstep (se 1 (by rfl) ⟨1307774, by rfl⟩ : syracuseStep 1743699 = 2615549) B2615549
theorem B1743715 : Blo 1742572 1743715 := bstep (se 1 (by rfl) ⟨1307786, by rfl⟩ : syracuseStep 1743715 = 2615573) B2615573
theorem B6617969 : Blo 1742572 6617969 := bstep (se 2 (by rfl) ⟨2481738, by rfl⟩ : syracuseStep 6617969 = 4963477) B4963477
theorem B8829809 : Blo 1742572 8829809 := bstep (se 2 (by rfl) ⟨3311178, by rfl⟩ : syracuseStep 8829809 = 6622357) B6622357
theorem B1743731 : Blo 1742572 1743731 := bstep (se 1 (by rfl) ⟨1307798, by rfl⟩ : syracuseStep 1743731 = 2615597) B2615597
theorem B2792321 : Blo 1742572 2792321 := bstep (se 2 (by rfl) ⟨1047120, by rfl⟩ : syracuseStep 2792321 = 2094241) B2094241
theorem B1743747 : Blo 1742572 1743747 := bstep (se 1 (by rfl) ⟨1307810, by rfl⟩ : syracuseStep 1743747 = 2615621) B2615621
theorem B1743763 : Blo 1742572 1743763 := bstep (se 1 (by rfl) ⟨1307822, by rfl⟩ : syracuseStep 1743763 = 2615645) B2615645
theorem B1743779 : Blo 1742572 1743779 := bstep (se 1 (by rfl) ⟨1307834, by rfl⟩ : syracuseStep 1743779 = 2615669) B2615669
theorem B3922865 : Blo 1742572 3922865 := bstep (se 2 (by rfl) ⟨1471074, by rfl⟩ : syracuseStep 3922865 = 2942149) B2942149
theorem B1743795 : Blo 1742572 1743795 := bstep (se 1 (by rfl) ⟨1307846, by rfl⟩ : syracuseStep 1743795 = 2615693) B2615693
theorem B3922883 : Blo 1742572 3922883 := bstep (se 1 (by rfl) ⟨2942162, by rfl⟩ : syracuseStep 3922883 = 5884325) B5884325
theorem B1743811 : Blo 1742572 1743811 := bstep (se 1 (by rfl) ⟨1307858, by rfl⟩ : syracuseStep 1743811 = 2615717) B2615717
theorem B1743827 : Blo 1742572 1743827 := bstep (se 1 (by rfl) ⟨1307870, by rfl⟩ : syracuseStep 1743827 = 2615741) B2615741
theorem B1743843 : Blo 1742572 1743843 := bstep (se 1 (by rfl) ⟨1307882, by rfl⟩ : syracuseStep 1743843 = 2615765) B2615765
theorem B1743859 : Blo 1742572 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B1743875 : Blo 1742572 1743875 := bstep (se 1 (by rfl) ⟨1307906, by rfl⟩ : syracuseStep 1743875 = 2615813) B2615813
theorem B1743891 : Blo 1742572 1743891 := bstep (se 1 (by rfl) ⟨1307918, by rfl⟩ : syracuseStep 1743891 = 2615837) B2615837
theorem B1743907 : Blo 1742572 1743907 := bstep (se 1 (by rfl) ⟨1307930, by rfl⟩ : syracuseStep 1743907 = 2615861) B2615861
theorem B1743923 : Blo 1742572 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B1743939 : Blo 1742572 1743939 := bstep (se 1 (by rfl) ⟨1307954, by rfl⟩ : syracuseStep 1743939 = 2615909) B2615909
theorem B1743955 : Blo 1742572 1743955 := bstep (se 1 (by rfl) ⟨1307966, by rfl⟩ : syracuseStep 1743955 = 2615933) B2615933
theorem B1743971 : Blo 1742572 1743971 := bstep (se 1 (by rfl) ⟨1307978, by rfl⟩ : syracuseStep 1743971 = 2615957) B2615957
theorem B1743987 : Blo 1742572 1743987 := bstep (se 1 (by rfl) ⟨1307990, by rfl⟩ : syracuseStep 1743987 = 2615981) B2615981
theorem B2481283 : Blo 1742572 2481283 := bstep (se 1 (by rfl) ⟨1860962, by rfl⟩ : syracuseStep 2481283 = 3721925) B3721925
theorem B1744003 : Blo 1742572 1744003 := bstep (se 1 (by rfl) ⟨1308002, by rfl⟩ : syracuseStep 1744003 = 2616005) B2616005
theorem B14892173 : Blo 1742572 14892173 := bstep (se 3 (by rfl) ⟨2792282, by rfl⟩ : syracuseStep 14892173 = 5584565) B5584565
theorem B1744019 : Blo 1742572 1744019 := bstep (se 1 (by rfl) ⟨1308014, by rfl⟩ : syracuseStep 1744019 = 2616029) B2616029
theorem B1744035 : Blo 1742572 1744035 := bstep (se 1 (by rfl) ⟨1308026, by rfl⟩ : syracuseStep 1744035 = 2616053) B2616053
theorem B1744051 : Blo 1742572 1744051 := bstep (se 1 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 1744051 = 2616077) B2616077
theorem B1744067 : Blo 1742572 1744067 := bstep (se 1 (by rfl) ⟨1308050, by rfl⟩ : syracuseStep 1744067 = 2616101) B2616101
theorem B3923153 : Blo 1742572 3923153 := bstep (se 2 (by rfl) ⟨1471182, by rfl⟩ : syracuseStep 3923153 = 2942365) B2942365
theorem B1744083 : Blo 1742572 1744083 := bstep (se 1 (by rfl) ⟨1308062, by rfl⟩ : syracuseStep 1744083 = 2616125) B2616125
theorem B3923171 : Blo 1742572 3923171 := bstep (se 1 (by rfl) ⟨2942378, by rfl⟩ : syracuseStep 3923171 = 5884757) B5884757
theorem B1744099 : Blo 1742572 1744099 := bstep (se 1 (by rfl) ⟨1308074, by rfl⟩ : syracuseStep 1744099 = 2616149) B2616149
theorem B1744115 : Blo 1742572 1744115 := bstep (se 1 (by rfl) ⟨1308086, by rfl⟩ : syracuseStep 1744115 = 2616173) B2616173
theorem B1744131 : Blo 1742572 1744131 := bstep (se 1 (by rfl) ⟨1308098, by rfl⟩ : syracuseStep 1744131 = 2616197) B2616197
theorem B1744147 : Blo 1742572 1744147 := bstep (se 1 (by rfl) ⟨1308110, by rfl⟩ : syracuseStep 1744147 = 2616221) B2616221
theorem B1744163 : Blo 1742572 1744163 := bstep (se 1 (by rfl) ⟨1308122, by rfl⟩ : syracuseStep 1744163 = 2616245) B2616245
theorem B1744179 : Blo 1742572 1744179 := bstep (se 1 (by rfl) ⟨1308134, by rfl⟩ : syracuseStep 1744179 = 2616269) B2616269
theorem B1744195 : Blo 1742572 1744195 := bstep (se 1 (by rfl) ⟨1308146, by rfl⟩ : syracuseStep 1744195 = 2616293) B2616293
theorem B1744211 : Blo 1742572 1744211 := bstep (se 1 (by rfl) ⟨1308158, by rfl⟩ : syracuseStep 1744211 = 2616317) B2616317
theorem B1744227 : Blo 1742572 1744227 := bstep (se 1 (by rfl) ⟨1308170, by rfl⟩ : syracuseStep 1744227 = 2616341) B2616341
theorem B4963693 : Blo 1742572 4963693 := bstep (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) B1861385
theorem B1744243 : Blo 1742572 1744243 := bstep (se 1 (by rfl) ⟨1308182, by rfl⟩ : syracuseStep 1744243 = 2616365) B2616365
theorem B1744259 : Blo 1742572 1744259 := bstep (se 1 (by rfl) ⟨1308194, by rfl⟩ : syracuseStep 1744259 = 2616389) B2616389
theorem B1744275 : Blo 1742572 1744275 := bstep (se 1 (by rfl) ⟨1308206, by rfl⟩ : syracuseStep 1744275 = 2616413) B2616413
theorem B1744291 : Blo 1742572 1744291 := bstep (se 1 (by rfl) ⟨1308218, by rfl⟩ : syracuseStep 1744291 = 2616437) B2616437
theorem B1744307 : Blo 1742572 1744307 := bstep (se 1 (by rfl) ⟨1308230, by rfl⟩ : syracuseStep 1744307 = 2616461) B2616461
theorem B1744323 : Blo 1742572 1744323 := bstep (se 1 (by rfl) ⟨1308242, by rfl⟩ : syracuseStep 1744323 = 2616485) B2616485
theorem B2481619 : Blo 1742572 2481619 := bstep (se 1 (by rfl) ⟨1861214, by rfl⟩ : syracuseStep 2481619 = 3722429) B3722429
theorem B1744339 : Blo 1742572 1744339 := bstep (se 1 (by rfl) ⟨1308254, by rfl⟩ : syracuseStep 1744339 = 2616509) B2616509
theorem B1744355 : Blo 1742572 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B3923441 : Blo 1742572 3923441 := bstep (se 2 (by rfl) ⟨1471290, by rfl⟩ : syracuseStep 3923441 = 2942581) B2942581
theorem B1744371 : Blo 1742572 1744371 := bstep (se 1 (by rfl) ⟨1308278, by rfl⟩ : syracuseStep 1744371 = 2616557) B2616557
theorem B3923459 : Blo 1742572 3923459 := bstep (se 1 (by rfl) ⟨2942594, by rfl⟩ : syracuseStep 3923459 = 5885189) B5885189
theorem B1744387 : Blo 1742572 1744387 := bstep (se 1 (by rfl) ⟨1308290, by rfl⟩ : syracuseStep 1744387 = 2616581) B2616581
theorem B1744403 : Blo 1742572 1744403 := bstep (se 1 (by rfl) ⟨1308302, by rfl⟩ : syracuseStep 1744403 = 2616605) B2616605
theorem B1744419 : Blo 1742572 1744419 := bstep (se 1 (by rfl) ⟨1308314, by rfl⟩ : syracuseStep 1744419 = 2616629) B2616629
theorem B1744435 : Blo 1742572 1744435 := bstep (se 1 (by rfl) ⟨1308326, by rfl⟩ : syracuseStep 1744435 = 2616653) B2616653
theorem B1744451 : Blo 1742572 1744451 := bstep (se 1 (by rfl) ⟨1308338, by rfl⟩ : syracuseStep 1744451 = 2616677) B2616677
theorem B4415057 : Blo 1742572 4415057 := bstep (se 2 (by rfl) ⟨1655646, by rfl⟩ : syracuseStep 4415057 = 3311293) B3311293
theorem B1744467 : Blo 1742572 1744467 := bstep (se 1 (by rfl) ⟨1308350, by rfl⟩ : syracuseStep 1744467 = 2616701) B2616701
theorem B1744483 : Blo 1742572 1744483 := bstep (se 1 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 1744483 = 2616725) B2616725
theorem B1744499 : Blo 1742572 1744499 := bstep (se 1 (by rfl) ⟨1308374, by rfl⟩ : syracuseStep 1744499 = 2616749) B2616749
theorem B4415107 : Blo 1742572 4415107 := bstep (se 1 (by rfl) ⟨3311330, by rfl⟩ : syracuseStep 4415107 = 6622661) B6622661
theorem B1744515 : Blo 1742572 1744515 := bstep (se 1 (by rfl) ⟨1308386, by rfl⟩ : syracuseStep 1744515 = 2616773) B2616773
theorem B1744531 : Blo 1742572 1744531 := bstep (se 1 (by rfl) ⟨1308398, by rfl⟩ : syracuseStep 1744531 = 2616797) B2616797
theorem B2981539 : Blo 1742572 2981539 := bstep (se 1 (by rfl) ⟨2236154, by rfl⟩ : syracuseStep 2981539 = 4472309) B4472309
theorem B1744547 : Blo 1742572 1744547 := bstep (se 1 (by rfl) ⟨1308410, by rfl⟩ : syracuseStep 1744547 = 2616821) B2616821
theorem B5881517 : Blo 1742572 5881517 := bstep (se 3 (by rfl) ⟨1102784, by rfl⟩ : syracuseStep 5881517 = 2205569) B2205569
theorem B1744563 : Blo 1742572 1744563 := bstep (se 1 (by rfl) ⟨1308422, by rfl⟩ : syracuseStep 1744563 = 2616845) B2616845
theorem B3309265 : Blo 1742572 3309265 := bstep (se 2 (by rfl) ⟨1240974, by rfl⟩ : syracuseStep 3309265 = 2481949) B2481949
theorem B5586641 : Blo 1742572 5586641 := bstep (se 2 (by rfl) ⟨2094990, by rfl⟩ : syracuseStep 5586641 = 4189981) B4189981
theorem B5881571 : Blo 1742572 5881571 := bstep (se 1 (by rfl) ⟨4411178, by rfl⟩ : syracuseStep 5881571 = 8822357) B8822357
theorem B9928433 : Blo 1742572 9928433 := bstep (se 2 (by rfl) ⟨3723162, by rfl⟩ : syracuseStep 9928433 = 7446325) B7446325
theorem B3923729 : Blo 1742572 3923729 := bstep (se 2 (by rfl) ⟨1471398, by rfl⟩ : syracuseStep 3923729 = 2942797) B2942797
theorem B4415249 : Blo 1742572 4415249 := bstep (se 2 (by rfl) ⟨1655718, by rfl⟩ : syracuseStep 4415249 = 3311437) B3311437
theorem B2940691 : Blo 1742572 2940691 := bstep (se 1 (by rfl) ⟨2205518, by rfl⟩ : syracuseStep 2940691 = 4411037) B4411037
theorem B2236195 : Blo 1742572 2236195 := bstep (se 1 (by rfl) ⟨1677146, by rfl⟩ : syracuseStep 2236195 = 3354293) B3354293
theorem B3923747 : Blo 1742572 3923747 := bstep (se 1 (by rfl) ⟨2942810, by rfl⟩ : syracuseStep 3923747 = 5885621) B5885621
theorem B3825521 : Blo 1742572 3825521 := bstep (se 2 (by rfl) ⟨1434570, by rfl⟩ : syracuseStep 3825521 = 2869141) B2869141
theorem B2940833 : Blo 1742572 2940833 := bstep (se 2 (by rfl) ⟨1102812, by rfl⟩ : syracuseStep 2940833 = 2205625) B2205625
theorem B5881841 : Blo 1742572 5881841 := bstep (se 2 (by rfl) ⟨2205690, by rfl⟩ : syracuseStep 5881841 = 4411381) B4411381
theorem B3309569 : Blo 1742572 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B2941015 : Blo 1742572 2941015 := bstep (se 1 (by rfl) ⟨2205761, by rfl⟩ : syracuseStep 2941015 = 4411523) B4411523
theorem B5881949 : Blo 1742572 5881949 := bstep (se 3 (by rfl) ⟨1102865, by rfl⟩ : syracuseStep 5881949 = 2205731) B2205731
theorem B6619229 : Blo 1742572 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B3924107 : Blo 1742572 3924107 := bstep (se 1 (by rfl) ⟨2943080, by rfl⟩ : syracuseStep 3924107 = 5886161) B5886161
theorem B4710593 : Blo 1742572 4710593 := bstep (se 2 (by rfl) ⟨1766472, by rfl⟩ : syracuseStep 4710593 = 3532945) B3532945
theorem B3924161 : Blo 1742572 3924161 := bstep (se 2 (by rfl) ⟨1471560, by rfl⟩ : syracuseStep 3924161 = 2943121) B2943121
theorem B4415705 : Blo 1742572 4415705 := bstep (se 2 (by rfl) ⟨1655889, by rfl⟩ : syracuseStep 4415705 = 3311779) B3311779
theorem B3309835 : Blo 1742572 3309835 := bstep (se 1 (by rfl) ⟨2482376, by rfl⟩ : syracuseStep 3309835 = 4964753) B4964753
theorem B2687321 : Blo 1742572 2687321 := bstep (se 2 (by rfl) ⟨1007745, by rfl⟩ : syracuseStep 2687321 = 2015491) B2015491
theorem B3924377 : Blo 1742572 3924377 := bstep (se 2 (by rfl) ⟨1471641, by rfl⟩ : syracuseStep 3924377 = 2943283) B2943283
theorem B2982347 : Blo 1742572 2982347 := bstep (se 1 (by rfl) ⟨2236760, by rfl⟩ : syracuseStep 2982347 = 4473521) B4473521
theorem B16761305 : Blo 1742572 16761305 := bstep (se 2 (by rfl) ⟨6285489, by rfl⟩ : syracuseStep 16761305 = 12570979) B12570979
theorem B3924467 : Blo 1742572 3924467 := bstep (se 1 (by rfl) ⟨2943350, by rfl⟩ : syracuseStep 3924467 = 5886701) B5886701
theorem B3924503 : Blo 1742572 3924503 := bstep (se 1 (by rfl) ⟨2943377, by rfl⟩ : syracuseStep 3924503 = 5886755) B5886755
theorem B2794007 : Blo 1742572 2794007 := bstep (se 1 (by rfl) ⟨2095505, by rfl⟩ : syracuseStep 2794007 = 4191011) B4191011
theorem B2613899 : Blo 1742572 2613899 := bstep (se 1 (by rfl) ⟨1960424, by rfl⟩ : syracuseStep 2613899 = 3920849) B3920849
theorem B2613911 : Blo 1742572 2613911 := bstep (se 1 (by rfl) ⟨1960433, by rfl⟩ : syracuseStep 2613911 = 3920867) B3920867
theorem B2941643 : Blo 1742572 2941643 := bstep (se 1 (by rfl) ⟨2206232, by rfl⟩ : syracuseStep 2941643 = 4412465) B4412465
theorem B3310283 : Blo 1742572 3310283 := bstep (se 1 (by rfl) ⟨2482712, by rfl⟩ : syracuseStep 3310283 = 4965425) B4965425
theorem B3924683 : Blo 1742572 3924683 := bstep (se 1 (by rfl) ⟨2943512, by rfl⟩ : syracuseStep 3924683 = 5887025) B5887025
theorem B2613977 : Blo 1742572 2613977 := bstep (se 2 (by rfl) ⟨980241, by rfl⟩ : syracuseStep 2613977 = 1960483) B1960483
theorem B3924737 : Blo 1742572 3924737 := bstep (se 2 (by rfl) ⟨1471776, by rfl⟩ : syracuseStep 3924737 = 2943553) B2943553
theorem B6619927 : Blo 1742572 6619927 := bstep (se 1 (by rfl) ⟨4964945, by rfl⟩ : syracuseStep 6619927 = 9929891) B9929891
theorem B4473623 : Blo 1742572 4473623 := bstep (se 1 (by rfl) ⟨3355217, by rfl⟩ : syracuseStep 4473623 = 6710435) B6710435
theorem B2482969 : Blo 1742572 2482969 := bstep (se 2 (by rfl) ⟨931113, by rfl⟩ : syracuseStep 2482969 = 1862227) B1862227
theorem B2614091 : Blo 1742572 2614091 := bstep (se 1 (by rfl) ⟨1960568, by rfl⟩ : syracuseStep 2614091 = 3921137) B3921137
theorem B2941771 : Blo 1742572 2941771 := bstep (se 1 (by rfl) ⟨2206328, by rfl⟩ : syracuseStep 2941771 = 4412657) B4412657
theorem B2614103 : Blo 1742572 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B4965209 : Blo 1742572 4965209 := bstep (se 2 (by rfl) ⟨1861953, by rfl⟩ : syracuseStep 4965209 = 3723907) B3723907
theorem B15901541 : Blo 1742572 15901541 := bstep (se 4 (by rfl) ⟨1490769, by rfl⟩ : syracuseStep 15901541 = 2981539) B2981539
theorem B9929573 : Blo 1742572 9929573 := bstep (se 4 (by rfl) ⟨930897, by rfl⟩ : syracuseStep 9929573 = 1861795) B1861795
theorem B3310465 : Blo 1742572 3310465 := bstep (se 2 (by rfl) ⟨1241424, by rfl⟩ : syracuseStep 3310465 = 2482849) B2482849
theorem B2614169 : Blo 1742572 2614169 := bstep (se 2 (by rfl) ⟨980313, by rfl⟩ : syracuseStep 2614169 = 1960627) B1960627
theorem B4973491 : Blo 1742572 4973491 := bstep (se 1 (by rfl) ⟨3730118, by rfl⟩ : syracuseStep 4973491 = 7460237) B7460237
theorem B2941913 : Blo 1742572 2941913 := bstep (se 2 (by rfl) ⟨1103217, by rfl⟩ : syracuseStep 2941913 = 2206435) B2206435
theorem B3924953 : Blo 1742572 3924953 := bstep (se 2 (by rfl) ⟨1471857, by rfl⟩ : syracuseStep 3924953 = 2943715) B2943715
theorem B7447555 : Blo 1742572 7447555 := bstep (se 1 (by rfl) ⟨5585666, by rfl⟩ : syracuseStep 7447555 = 11171333) B11171333
theorem B2614283 : Blo 1742572 2614283 := bstep (se 1 (by rfl) ⟨1960712, by rfl⟩ : syracuseStep 2614283 = 3921425) B3921425
theorem B22348817 : Blo 1742572 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B2614295 : Blo 1742572 2614295 := bstep (se 1 (by rfl) ⟨1960721, by rfl⟩ : syracuseStep 2614295 = 3921443) B3921443
theorem B32228387 : Blo 1742572 32228387 := bstep (se 1 (by rfl) ⟨24171290, by rfl⟩ : syracuseStep 32228387 = 48342581) B48342581
theorem B3925043 : Blo 1742572 3925043 := bstep (se 1 (by rfl) ⟨2943782, by rfl⟩ : syracuseStep 3925043 = 5887565) B5887565
theorem B3925079 : Blo 1742572 3925079 := bstep (se 1 (by rfl) ⟨2943809, by rfl⟩ : syracuseStep 3925079 = 5887619) B5887619
theorem B2614361 : Blo 1742572 2614361 := bstep (se 2 (by rfl) ⟨980385, by rfl⟩ : syracuseStep 2614361 = 1960771) B1960771
theorem B2942041 : Blo 1742572 2942041 := bstep (se 2 (by rfl) ⟨1103265, by rfl⟩ : syracuseStep 2942041 = 2206531) B2206531
theorem B2614475 : Blo 1742572 2614475 := bstep (se 1 (by rfl) ⟨1960856, by rfl⟩ : syracuseStep 2614475 = 3921713) B3921713
theorem B5883083 : Blo 1742572 5883083 := bstep (se 1 (by rfl) ⟨4412312, by rfl⟩ : syracuseStep 5883083 = 8824625) B8824625
theorem B2614487 : Blo 1742572 2614487 := bstep (se 1 (by rfl) ⟨1960865, by rfl⟩ : syracuseStep 2614487 = 3921731) B3921731
theorem B3310807 : Blo 1742572 3310807 := bstep (se 1 (by rfl) ⟨2483105, by rfl⟩ : syracuseStep 3310807 = 4966211) B4966211
theorem B3925259 : Blo 1742572 3925259 := bstep (se 1 (by rfl) ⟨2943944, by rfl⟩ : syracuseStep 3925259 = 5887889) B5887889
theorem B6284567 : Blo 1742572 6284567 := bstep (se 1 (by rfl) ⟨4713425, by rfl⟩ : syracuseStep 6284567 = 9426851) B9426851
theorem B2614553 : Blo 1742572 2614553 := bstep (se 2 (by rfl) ⟨980457, by rfl⟩ : syracuseStep 2614553 = 1960915) B1960915
theorem B8824139 : Blo 1742572 8824139 := bstep (se 1 (by rfl) ⟨6618104, by rfl⟩ : syracuseStep 8824139 = 13236209) B13236209
theorem B2614667 : Blo 1742572 2614667 := bstep (se 1 (by rfl) ⟨1961000, by rfl⟩ : syracuseStep 2614667 = 3922001) B3922001
theorem B2614679 : Blo 1742572 2614679 := bstep (se 1 (by rfl) ⟨1961009, by rfl⟩ : syracuseStep 2614679 = 3922019) B3922019
theorem B3311027 : Blo 1742572 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B2614745 : Blo 1742572 2614745 := bstep (se 2 (by rfl) ⟨980529, by rfl⟩ : syracuseStep 2614745 = 1961059) B1961059
theorem B5883353 : Blo 1742572 5883353 := bstep (se 2 (by rfl) ⟨2206257, by rfl⟩ : syracuseStep 5883353 = 4412515) B4412515
theorem B6620717 : Blo 1742572 6620717 := bstep (se 3 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 6620717 = 2482769) B2482769
theorem B4187713 : Blo 1742572 4187713 := bstep (se 2 (by rfl) ⟨1570392, by rfl⟩ : syracuseStep 4187713 = 3140785) B3140785
theorem B4032065 : Blo 1742572 4032065 := bstep (se 2 (by rfl) ⟨1512024, by rfl⟩ : syracuseStep 4032065 = 3024049) B3024049
theorem B2614859 : Blo 1742572 2614859 := bstep (se 1 (by rfl) ⟨1961144, by rfl⟩ : syracuseStep 2614859 = 3922289) B3922289
theorem B2614871 : Blo 1742572 2614871 := bstep (se 1 (by rfl) ⟨1961153, by rfl⟩ : syracuseStep 2614871 = 3922307) B3922307
theorem B2942615 : Blo 1742572 2942615 := bstep (se 1 (by rfl) ⟨2206961, by rfl⟩ : syracuseStep 2942615 = 4413923) B4413923
theorem B4966039 : Blo 1742572 4966039 := bstep (se 1 (by rfl) ⟨3724529, by rfl⟩ : syracuseStep 4966039 = 7449059) B7449059
theorem B2614937 : Blo 1742572 2614937 := bstep (se 2 (by rfl) ⟨980601, by rfl⟩ : syracuseStep 2614937 = 1961203) B1961203
theorem B3311255 : Blo 1742572 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B10061491 : Blo 1742572 10061491 := bstep (se 1 (by rfl) ⟨7546118, by rfl⟩ : syracuseStep 10061491 = 15092237) B15092237
theorem B2615051 : Blo 1742572 2615051 := bstep (se 1 (by rfl) ⟨1961288, by rfl⟩ : syracuseStep 2615051 = 3922577) B3922577
theorem B2205463 : Blo 1742572 2205463 := bstep (se 1 (by rfl) ⟨1654097, by rfl⟩ : syracuseStep 2205463 = 3308195) B3308195
theorem B2615063 : Blo 1742572 2615063 := bstep (se 1 (by rfl) ⟨1961297, by rfl⟩ : syracuseStep 2615063 = 3922595) B3922595
theorem B2942743 : Blo 1742572 2942743 := bstep (se 1 (by rfl) ⟨2207057, by rfl⟩ : syracuseStep 2942743 = 4414115) B4414115
theorem B6367027 : Blo 1742572 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B6285131 : Blo 1742572 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B2615129 : Blo 1742572 2615129 := bstep (se 2 (by rfl) ⟨980673, by rfl⟩ : syracuseStep 2615129 = 1961347) B1961347
theorem B25479029 : Blo 1742572 25479029 := bstep (se 5 (by rfl) ⟨1194329, by rfl⟩ : syracuseStep 25479029 = 2388659) B2388659
theorem B3311513 : Blo 1742572 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B1861547 : Blo 1742572 1861547 := bstep (se 1 (by rfl) ⟨1396160, by rfl⟩ : syracuseStep 1861547 = 2792321) B2792321
theorem B2615243 : Blo 1742572 2615243 := bstep (se 1 (by rfl) ⟨1961432, by rfl⟩ : syracuseStep 2615243 = 3922865) B3922865
theorem B2615255 : Blo 1742572 2615255 := bstep (se 1 (by rfl) ⟨1961441, by rfl⟩ : syracuseStep 2615255 = 3922883) B3922883
theorem B19859417 : Blo 1742572 19859417 := bstep (se 2 (by rfl) ⟨7447281, by rfl⟩ : syracuseStep 19859417 = 14894563) B14894563
theorem B2615321 : Blo 1742572 2615321 := bstep (se 2 (by rfl) ⟨980745, by rfl⟩ : syracuseStep 2615321 = 1961491) B1961491
theorem B2615435 : Blo 1742572 2615435 := bstep (se 1 (by rfl) ⟨1961576, by rfl⟩ : syracuseStep 2615435 = 3923153) B3923153
theorem B5884055 : Blo 1742572 5884055 := bstep (se 1 (by rfl) ⟨4413041, by rfl⟩ : syracuseStep 5884055 = 8826083) B8826083
theorem B2615447 : Blo 1742572 2615447 := bstep (se 1 (by rfl) ⟨1961585, by rfl⟩ : syracuseStep 2615447 = 3923171) B3923171
theorem B2615513 : Blo 1742572 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B3311923 : Blo 1742572 3311923 := bstep (se 1 (by rfl) ⟨2483942, by rfl⟩ : syracuseStep 3311923 = 4967885) B4967885
theorem B2615627 : Blo 1742572 2615627 := bstep (se 1 (by rfl) ⟨1961720, by rfl⟩ : syracuseStep 2615627 = 3923441) B3923441
theorem B2615639 : Blo 1742572 2615639 := bstep (se 1 (by rfl) ⟨1961729, by rfl⟩ : syracuseStep 2615639 = 3923459) B3923459
theorem B2943371 : Blo 1742572 2943371 := bstep (se 1 (by rfl) ⟨2207528, by rfl⟩ : syracuseStep 2943371 = 4415057) B4415057
theorem B2615705 : Blo 1742572 2615705 := bstep (se 2 (by rfl) ⟨980889, by rfl⟩ : syracuseStep 2615705 = 1961779) B1961779
theorem B4966859 : Blo 1742572 4966859 := bstep (se 1 (by rfl) ⟨3725144, by rfl⟩ : syracuseStep 4966859 = 7450289) B7450289
theorem B7072217 : Blo 1742572 7072217 := bstep (se 2 (by rfl) ⟨2652081, by rfl⟩ : syracuseStep 7072217 = 5304163) B5304163
theorem B2615819 : Blo 1742572 2615819 := bstep (se 1 (by rfl) ⟨1961864, by rfl⟩ : syracuseStep 2615819 = 3923729) B3923729
theorem B2943499 : Blo 1742572 2943499 := bstep (se 1 (by rfl) ⟨2207624, by rfl⟩ : syracuseStep 2943499 = 4415249) B4415249
theorem B2615831 : Blo 1742572 2615831 := bstep (se 1 (by rfl) ⟨1961873, by rfl⟩ : syracuseStep 2615831 = 3923747) B3923747
theorem B2550347 : Blo 1742572 2550347 := bstep (se 1 (by rfl) ⟨1912760, by rfl⟩ : syracuseStep 2550347 = 3825521) B3825521
theorem B2615897 : Blo 1742572 2615897 := bstep (se 2 (by rfl) ⟨980961, by rfl⟩ : syracuseStep 2615897 = 1961923) B1961923
theorem B1960555 : Blo 1742572 1960555 := bstep (se 1 (by rfl) ⟨1470416, by rfl⟩ : syracuseStep 1960555 = 2940833) B2940833
theorem B3533465 : Blo 1742572 3533465 := bstep (se 2 (by rfl) ⟨1325049, by rfl⟩ : syracuseStep 3533465 = 2650099) B2650099
theorem B2943641 : Blo 1742572 2943641 := bstep (se 2 (by rfl) ⟨1103865, by rfl⟩ : syracuseStep 2943641 = 2207731) B2207731
theorem B5884595 : Blo 1742572 5884595 := bstep (se 1 (by rfl) ⟨4413446, by rfl⟩ : syracuseStep 5884595 = 8826893) B8826893
theorem B2616011 : Blo 1742572 2616011 := bstep (se 1 (by rfl) ⟨1962008, by rfl⟩ : syracuseStep 2616011 = 3924017) B3924017
theorem B1960663 : Blo 1742572 1960663 := bstep (se 1 (by rfl) ⟨1470497, by rfl⟩ : syracuseStep 1960663 = 2940995) B2940995
theorem B2616023 : Blo 1742572 2616023 := bstep (se 1 (by rfl) ⟨1962017, by rfl⟩ : syracuseStep 2616023 = 3924035) B3924035
theorem B7449367 : Blo 1742572 7449367 := bstep (se 1 (by rfl) ⟨5587025, by rfl⟩ : syracuseStep 7449367 = 11174051) B11174051
theorem B2616089 : Blo 1742572 2616089 := bstep (se 2 (by rfl) ⟨981033, by rfl⟩ : syracuseStep 2616089 = 1962067) B1962067
theorem B2943769 : Blo 1742572 2943769 := bstep (se 2 (by rfl) ⟨1103913, by rfl⟩ : syracuseStep 2943769 = 2207827) B2207827
theorem B28289893 : Blo 1742572 28289893 := bstep (se 4 (by rfl) ⟨2652177, by rfl⟩ : syracuseStep 28289893 = 5304355) B5304355
theorem B1960843 : Blo 1742572 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B2616203 : Blo 1742572 2616203 := bstep (se 1 (by rfl) ⟨1962152, by rfl⟩ : syracuseStep 2616203 = 3924305) B3924305
theorem B5303191 : Blo 1742572 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B2616215 : Blo 1742572 2616215 := bstep (se 1 (by rfl) ⟨1962161, by rfl⟩ : syracuseStep 2616215 = 3924323) B3924323
theorem B5884865 : Blo 1742572 5884865 := bstep (se 2 (by rfl) ⟨2206824, by rfl⟩ : syracuseStep 5884865 = 4413649) B4413649
theorem B6622145 : Blo 1742572 6622145 := bstep (se 2 (by rfl) ⟨2483304, by rfl⟩ : syracuseStep 6622145 = 4966609) B4966609
theorem B11324377 : Blo 1742572 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B2616281 : Blo 1742572 2616281 := bstep (se 2 (by rfl) ⟨981105, by rfl⟩ : syracuseStep 2616281 = 1962211) B1962211
theorem B7072733 : Blo 1742572 7072733 := bstep (se 3 (by rfl) ⟨1326137, by rfl⟩ : syracuseStep 7072733 = 2652275) B2652275
theorem B1960951 : Blo 1742572 1960951 := bstep (se 1 (by rfl) ⟨1470713, by rfl⟩ : syracuseStep 1960951 = 2941427) B2941427
theorem B8825921 : Blo 1742572 8825921 := bstep (se 2 (by rfl) ⟨3309720, by rfl⟩ : syracuseStep 8825921 = 6619441) B6619441
theorem B2616395 : Blo 1742572 2616395 := bstep (se 1 (by rfl) ⟨1962296, by rfl⟩ : syracuseStep 2616395 = 3924593) B3924593
theorem B2616407 : Blo 1742572 2616407 := bstep (se 1 (by rfl) ⟨1962305, by rfl⟩ : syracuseStep 2616407 = 3924611) B3924611
theorem B2616473 : Blo 1742572 2616473 := bstep (se 2 (by rfl) ⟨981177, by rfl⟩ : syracuseStep 2616473 = 1962355) B1962355
theorem B1961131 : Blo 1742572 1961131 := bstep (se 1 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 1961131 = 2941697) B2941697
theorem B5098717 : Blo 1742572 5098717 := bstep (se 3 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 5098717 = 1912019) B1912019
theorem B2616587 : Blo 1742572 2616587 := bstep (se 1 (by rfl) ⟨1962440, by rfl⟩ : syracuseStep 2616587 = 3924881) B3924881
theorem B1961239 : Blo 1742572 1961239 := bstep (se 1 (by rfl) ⟨1470929, by rfl⟩ : syracuseStep 1961239 = 2941859) B2941859
theorem B2616599 : Blo 1742572 2616599 := bstep (se 1 (by rfl) ⟨1962449, by rfl⟩ : syracuseStep 2616599 = 3924899) B3924899
theorem B2616665 : Blo 1742572 2616665 := bstep (se 2 (by rfl) ⟨981249, by rfl⟩ : syracuseStep 2616665 = 1962499) B1962499
theorem B7450001 : Blo 1742572 7450001 := bstep (se 2 (by rfl) ⟨2793750, by rfl⟩ : syracuseStep 7450001 = 5587501) B5587501
theorem B31796657 : Blo 1742572 31796657 := bstep (se 2 (by rfl) ⟨11923746, by rfl⟩ : syracuseStep 31796657 = 23847493) B23847493
theorem B3534259 : Blo 1742572 3534259 := bstep (se 1 (by rfl) ⟨2650694, by rfl⟩ : syracuseStep 3534259 = 5301389) B5301389
theorem B1961419 : Blo 1742572 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B2207179 : Blo 1742572 2207179 := bstep (se 1 (by rfl) ⟨1655384, by rfl⟩ : syracuseStep 2207179 = 3310769) B3310769
theorem B2616779 : Blo 1742572 2616779 := bstep (se 1 (by rfl) ⟨1962584, by rfl⟩ : syracuseStep 2616779 = 3925169) B3925169
theorem B2616791 : Blo 1742572 2616791 := bstep (se 1 (by rfl) ⟨1962593, by rfl⟩ : syracuseStep 2616791 = 3925187) B3925187
theorem B5885405 : Blo 1742572 5885405 := bstep (se 3 (by rfl) ⟨1103513, by rfl⟩ : syracuseStep 5885405 = 2207027) B2207027
theorem B3722753 : Blo 1742572 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B2616857 : Blo 1742572 2616857 := bstep (se 2 (by rfl) ⟨981321, by rfl⟩ : syracuseStep 2616857 = 1962643) B1962643
theorem B1961527 : Blo 1742572 1961527 := bstep (se 1 (by rfl) ⟨1471145, by rfl⟩ : syracuseStep 1961527 = 2942291) B2942291
theorem B7073369 : Blo 1742572 7073369 := bstep (se 2 (by rfl) ⟨2652513, by rfl⟩ : syracuseStep 7073369 = 5305027) B5305027
theorem B14888549 : Blo 1742572 14888549 := bstep (se 4 (by rfl) ⟨1395801, by rfl⟩ : syracuseStep 14888549 = 2791603) B2791603
theorem B7548547 : Blo 1742572 7548547 := bstep (se 1 (by rfl) ⟨5661410, by rfl⟩ : syracuseStep 7548547 = 11322821) B11322821
theorem B8949379 : Blo 1742572 8949379 := bstep (se 1 (by rfl) ⟨6712034, by rfl⟩ : syracuseStep 8949379 = 13424069) B13424069
theorem B11177689 : Blo 1742572 11177689 := bstep (se 2 (by rfl) ⟨4191633, by rfl⟩ : syracuseStep 11177689 = 8383267) B8383267
theorem B1961707 : Blo 1742572 1961707 := bstep (se 1 (by rfl) ⟨1471280, by rfl⟩ : syracuseStep 1961707 = 2942561) B2942561
theorem B10604333 : Blo 1742572 10604333 := bstep (se 3 (by rfl) ⟨1988312, by rfl⟩ : syracuseStep 10604333 = 3976625) B3976625
theorem B4714291 : Blo 1742572 4714291 := bstep (se 1 (by rfl) ⟨3535718, by rfl⟩ : syracuseStep 4714291 = 7071437) B7071437
theorem B47705921 : Blo 1742572 47705921 := bstep (se 2 (by rfl) ⟨17889720, by rfl⟩ : syracuseStep 47705921 = 35779441) B35779441
theorem B1961815 : Blo 1742572 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B25472945 : Blo 1742572 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B1961995 : Blo 1742572 1961995 := bstep (se 1 (by rfl) ⟨1471496, by rfl⟩ : syracuseStep 1961995 = 2942993) B2942993
theorem B7450699 : Blo 1742572 7450699 := bstep (se 1 (by rfl) ⟨5588024, by rfl⟩ : syracuseStep 7450699 = 11176049) B11176049
theorem B1962103 : Blo 1742572 1962103 := bstep (se 1 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 1962103 = 2943155) B2943155
theorem B4411543 : Blo 1742572 4411543 := bstep (se 1 (by rfl) ⟨3308657, by rfl⟩ : syracuseStep 4411543 = 6617315) B6617315
theorem B1962283 : Blo 1742572 1962283 := bstep (se 1 (by rfl) ⟨1471712, by rfl⟩ : syracuseStep 1962283 = 2943425) B2943425
theorem B3723607 : Blo 1742572 3723607 := bstep (se 1 (by rfl) ⟨2792705, by rfl⟩ : syracuseStep 3723607 = 5585411) B5585411
theorem B7450973 : Blo 1742572 7450973 := bstep (se 3 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 7450973 = 2794115) B2794115
theorem B6623633 : Blo 1742572 6623633 := bstep (se 2 (by rfl) ⟨2483862, by rfl⟩ : syracuseStep 6623633 = 4967725) B4967725
theorem B1962391 : Blo 1742572 1962391 := bstep (se 1 (by rfl) ⟨1471793, by rfl⟩ : syracuseStep 1962391 = 2943587) B2943587
theorem B31797683 : Blo 1742572 31797683 := bstep (se 1 (by rfl) ⟨23848262, by rfl⟩ : syracuseStep 31797683 = 47696525) B47696525
theorem B3142169 : Blo 1742572 3142169 := bstep (se 2 (by rfl) ⟨1178313, by rfl⟩ : syracuseStep 3142169 = 2356627) B2356627
theorem B3772993 : Blo 1742572 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B4411979 : Blo 1742572 4411979 := bstep (se 1 (by rfl) ⟨3308984, by rfl⟩ : syracuseStep 4411979 = 6617969) B6617969
theorem B5886539 : Blo 1742572 5886539 := bstep (se 1 (by rfl) ⟨4414904, by rfl⟩ : syracuseStep 5886539 = 8829809) B8829809
theorem B1962571 : Blo 1742572 1962571 := bstep (se 1 (by rfl) ⟨1471928, by rfl⟩ : syracuseStep 1962571 = 2943857) B2943857
theorem B7451315 : Blo 1742572 7451315 := bstep (se 1 (by rfl) ⟨5588486, by rfl⟩ : syracuseStep 7451315 = 11176973) B11176973
theorem B5886809 : Blo 1742572 5886809 := bstep (se 2 (by rfl) ⟨2207553, by rfl⟩ : syracuseStep 5886809 = 4415107) B4415107
theorem B4412353 : Blo 1742572 4412353 := bstep (se 2 (by rfl) ⟨1654632, by rfl⟩ : syracuseStep 4412353 = 3309265) B3309265
theorem B8827865 : Blo 1742572 8827865 := bstep (se 2 (by rfl) ⟨3310449, by rfl⟩ : syracuseStep 8827865 = 6620899) B6620899
theorem B3920921 : Blo 1742572 3920921 := bstep (se 2 (by rfl) ⟨1470345, by rfl⟩ : syracuseStep 3920921 = 2940691) B2940691
theorem B3921011 : Blo 1742572 3921011 := bstep (se 1 (by rfl) ⟨2940758, by rfl⟩ : syracuseStep 3921011 = 5881517) B5881517
theorem B3724427 : Blo 1742572 3724427 := bstep (se 1 (by rfl) ⟨2793320, by rfl⟩ : syracuseStep 3724427 = 5586641) B5586641
theorem B3921047 : Blo 1742572 3921047 := bstep (se 1 (by rfl) ⟨2940785, by rfl⟩ : syracuseStep 3921047 = 5881571) B5881571
theorem B14890189 : Blo 1742572 14890189 := bstep (se 3 (by rfl) ⟨2791910, by rfl⟩ : syracuseStep 14890189 = 5583821) B5583821
theorem B6616343 : Blo 1742572 6616343 := bstep (se 1 (by rfl) ⟨4962257, by rfl⟩ : syracuseStep 6616343 = 9924515) B9924515
theorem B3921227 : Blo 1742572 3921227 := bstep (se 1 (by rfl) ⟨2940920, by rfl⟩ : syracuseStep 3921227 = 5881841) B5881841
theorem B3143027 : Blo 1742572 3143027 := bstep (se 1 (by rfl) ⟨2357270, by rfl⟩ : syracuseStep 3143027 = 4714541) B4714541
theorem B3921281 : Blo 1742572 3921281 := bstep (se 2 (by rfl) ⟨1470480, by rfl⟩ : syracuseStep 3921281 = 2940961) B2940961
theorem B3143063 : Blo 1742572 3143063 := bstep (se 1 (by rfl) ⟨2357297, by rfl⟩ : syracuseStep 3143063 = 4714595) B4714595
theorem B4412951 : Blo 1742572 4412951 := bstep (se 1 (by rfl) ⟨3309713, by rfl⟩ : syracuseStep 4412951 = 6619427) B6619427
theorem B5887511 : Blo 1742572 5887511 := bstep (se 1 (by rfl) ⟨4415633, by rfl⟩ : syracuseStep 5887511 = 8831267) B8831267
theorem B2651735 : Blo 1742572 2651735 := bstep (se 1 (by rfl) ⟨1988801, by rfl⟩ : syracuseStep 2651735 = 3977603) B3977603
theorem B3921497 : Blo 1742572 3921497 := bstep (se 2 (by rfl) ⟨1470561, by rfl⟩ : syracuseStep 3921497 = 2941123) B2941123
theorem B6280877 : Blo 1742572 6280877 := bstep (se 3 (by rfl) ⟨1177664, by rfl⟩ : syracuseStep 6280877 = 2355329) B2355329
theorem B3921587 : Blo 1742572 3921587 := bstep (se 1 (by rfl) ⟨2941190, by rfl⟩ : syracuseStep 3921587 = 5882381) B5882381
theorem B3921623 : Blo 1742572 3921623 := bstep (se 1 (by rfl) ⟨2941217, by rfl⟩ : syracuseStep 3921623 = 5882435) B5882435
theorem B1742583 : Blo 1742572 1742583 := bstep (se 1 (by rfl) ⟨1306937, by rfl⟩ : syracuseStep 1742583 = 2613875) B2613875
theorem B1742603 : Blo 1742572 1742603 := bstep (se 1 (by rfl) ⟨1306952, by rfl⟩ : syracuseStep 1742603 = 2613905) B2613905
theorem B1742615 : Blo 1742572 1742615 := bstep (se 1 (by rfl) ⟨1306961, by rfl⟩ : syracuseStep 1742615 = 2613923) B2613923
theorem B1742635 : Blo 1742572 1742635 := bstep (se 1 (by rfl) ⟨1306976, by rfl⟩ : syracuseStep 1742635 = 2613953) B2613953
theorem B22640429 : Blo 1742572 22640429 := bstep (se 3 (by rfl) ⟨4245080, by rfl⟩ : syracuseStep 22640429 = 8490161) B8490161
theorem B8951597 : Blo 1742572 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B1742647 : Blo 1742572 1742647 := bstep (se 1 (by rfl) ⟨1306985, by rfl⟩ : syracuseStep 1742647 = 2613971) B2613971
theorem B1742667 : Blo 1742572 1742667 := bstep (se 1 (by rfl) ⟨1307000, by rfl⟩ : syracuseStep 1742667 = 2614001) B2614001
theorem B1742679 : Blo 1742572 1742679 := bstep (se 1 (by rfl) ⟨1307009, by rfl⟩ : syracuseStep 1742679 = 2614019) B2614019
theorem B5584733 : Blo 1742572 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B1742699 : Blo 1742572 1742699 := bstep (se 1 (by rfl) ⟨1307024, by rfl⟩ : syracuseStep 1742699 = 2614049) B2614049
theorem B1742711 : Blo 1742572 1742711 := bstep (se 1 (by rfl) ⟨1307033, by rfl⟩ : syracuseStep 1742711 = 2614067) B2614067
theorem B1742731 : Blo 1742572 1742731 := bstep (se 1 (by rfl) ⟨1307048, by rfl⟩ : syracuseStep 1742731 = 2614097) B2614097
theorem B3921803 : Blo 1742572 3921803 := bstep (se 1 (by rfl) ⟨2941352, by rfl⟩ : syracuseStep 3921803 = 5882705) B5882705
theorem B1742743 : Blo 1742572 1742743 := bstep (se 1 (by rfl) ⟨1307057, by rfl⟩ : syracuseStep 1742743 = 2614115) B2614115
theorem B1742763 : Blo 1742572 1742763 := bstep (se 1 (by rfl) ⟨1307072, by rfl⟩ : syracuseStep 1742763 = 2614145) B2614145
theorem B6617011 : Blo 1742572 6617011 := bstep (se 1 (by rfl) ⟨4962758, by rfl⟩ : syracuseStep 6617011 = 9925517) B9925517
theorem B1742775 : Blo 1742572 1742775 := bstep (se 1 (by rfl) ⟨1307081, by rfl⟩ : syracuseStep 1742775 = 2614163) B2614163
theorem B3921857 : Blo 1742572 3921857 := bstep (se 2 (by rfl) ⟨1470696, by rfl⟩ : syracuseStep 3921857 = 2941393) B2941393
theorem B1742795 : Blo 1742572 1742795 := bstep (se 1 (by rfl) ⟨1307096, by rfl⟩ : syracuseStep 1742795 = 2614193) B2614193
theorem B1742807 : Blo 1742572 1742807 := bstep (se 1 (by rfl) ⟨1307105, by rfl⟩ : syracuseStep 1742807 = 2614211) B2614211
theorem B8378329 : Blo 1742572 8378329 := bstep (se 2 (by rfl) ⟨3141873, by rfl⟩ : syracuseStep 8378329 = 6283747) B6283747
theorem B1742827 : Blo 1742572 1742827 := bstep (se 1 (by rfl) ⟨1307120, by rfl⟩ : syracuseStep 1742827 = 2614241) B2614241
theorem B1988587 : Blo 1742572 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B1742839 : Blo 1742572 1742839 := bstep (se 1 (by rfl) ⟨1307129, by rfl⟩ : syracuseStep 1742839 = 2614259) B2614259
theorem B1742859 : Blo 1742572 1742859 := bstep (se 1 (by rfl) ⟨1307144, by rfl⟩ : syracuseStep 1742859 = 2614289) B2614289
theorem B12564497 : Blo 1742572 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B1742871 : Blo 1742572 1742871 := bstep (se 1 (by rfl) ⟨1307153, by rfl⟩ : syracuseStep 1742871 = 2614307) B2614307
theorem B1742891 : Blo 1742572 1742891 := bstep (se 1 (by rfl) ⟨1307168, by rfl⟩ : syracuseStep 1742891 = 2614337) B2614337
theorem B1742903 : Blo 1742572 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B1742923 : Blo 1742572 1742923 := bstep (se 1 (by rfl) ⟨1307192, by rfl⟩ : syracuseStep 1742923 = 2614385) B2614385
theorem B1742935 : Blo 1742572 1742935 := bstep (se 1 (by rfl) ⟨1307201, by rfl⟩ : syracuseStep 1742935 = 2614403) B2614403
theorem B1767511 : Blo 1742572 1767511 := bstep (se 1 (by rfl) ⟨1325633, by rfl⟩ : syracuseStep 1767511 = 2651267) B2651267
theorem B1742955 : Blo 1742572 1742955 := bstep (se 1 (by rfl) ⟨1307216, by rfl⟩ : syracuseStep 1742955 = 2614433) B2614433
theorem B1742967 : Blo 1742572 1742967 := bstep (se 1 (by rfl) ⟨1307225, by rfl⟩ : syracuseStep 1742967 = 2614451) B2614451
theorem B1742987 : Blo 1742572 1742987 := bstep (se 1 (by rfl) ⟨1307240, by rfl⟩ : syracuseStep 1742987 = 2614481) B2614481
theorem B1742999 : Blo 1742572 1742999 := bstep (se 1 (by rfl) ⟨1307249, by rfl⟩ : syracuseStep 1742999 = 2614499) B2614499
theorem B3922073 : Blo 1742572 3922073 := bstep (se 2 (by rfl) ⟨1470777, by rfl⟩ : syracuseStep 3922073 = 2941555) B2941555
theorem B1743019 : Blo 1742572 1743019 := bstep (se 1 (by rfl) ⟨1307264, by rfl⟩ : syracuseStep 1743019 = 2614529) B2614529
theorem B1743031 : Blo 1742572 1743031 := bstep (se 1 (by rfl) ⟨1307273, by rfl⟩ : syracuseStep 1743031 = 2614547) B2614547
theorem B1743051 : Blo 1742572 1743051 := bstep (se 1 (by rfl) ⟨1307288, by rfl⟩ : syracuseStep 1743051 = 2614577) B2614577
theorem B1743063 : Blo 1742572 1743063 := bstep (se 1 (by rfl) ⟨1307297, by rfl⟩ : syracuseStep 1743063 = 2614595) B2614595
theorem B1743083 : Blo 1742572 1743083 := bstep (se 1 (by rfl) ⟨1307312, by rfl⟩ : syracuseStep 1743083 = 2614625) B2614625
theorem B3922163 : Blo 1742572 3922163 := bstep (se 1 (by rfl) ⟨2941622, by rfl⟩ : syracuseStep 3922163 = 5883245) B5883245
theorem B1743095 : Blo 1742572 1743095 := bstep (se 1 (by rfl) ⟨1307321, by rfl⟩ : syracuseStep 1743095 = 2614643) B2614643
theorem B1743115 : Blo 1742572 1743115 := bstep (se 1 (by rfl) ⟨1307336, by rfl⟩ : syracuseStep 1743115 = 2614673) B2614673
theorem B1743127 : Blo 1742572 1743127 := bstep (se 1 (by rfl) ⟨1307345, by rfl⟩ : syracuseStep 1743127 = 2614691) B2614691
theorem B3922199 : Blo 1742572 3922199 := bstep (se 1 (by rfl) ⟨2941649, by rfl⟩ : syracuseStep 3922199 = 5883299) B5883299
theorem B1743147 : Blo 1742572 1743147 := bstep (se 1 (by rfl) ⟨1307360, by rfl⟩ : syracuseStep 1743147 = 2614721) B2614721
theorem B1743159 : Blo 1742572 1743159 := bstep (se 1 (by rfl) ⟨1307369, by rfl⟩ : syracuseStep 1743159 = 2614739) B2614739
theorem B4413761 : Blo 1742572 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B1743179 : Blo 1742572 1743179 := bstep (se 1 (by rfl) ⟨1307384, by rfl⟩ : syracuseStep 1743179 = 2614769) B2614769
theorem B1743191 : Blo 1742572 1743191 := bstep (se 1 (by rfl) ⟨1307393, by rfl⟩ : syracuseStep 1743191 = 2614787) B2614787
theorem B1743211 : Blo 1742572 1743211 := bstep (se 1 (by rfl) ⟨1307408, by rfl⟩ : syracuseStep 1743211 = 2614817) B2614817
theorem B1743223 : Blo 1742572 1743223 := bstep (se 1 (by rfl) ⟨1307417, by rfl⟩ : syracuseStep 1743223 = 2614835) B2614835
theorem B1743243 : Blo 1742572 1743243 := bstep (se 1 (by rfl) ⟨1307432, by rfl⟩ : syracuseStep 1743243 = 2614865) B2614865
theorem B1743255 : Blo 1742572 1743255 := bstep (se 1 (by rfl) ⟨1307441, by rfl⟩ : syracuseStep 1743255 = 2614883) B2614883
theorem B1743275 : Blo 1742572 1743275 := bstep (se 1 (by rfl) ⟨1307456, by rfl⟩ : syracuseStep 1743275 = 2614913) B2614913
theorem B28285361 : Blo 1742572 28285361 := bstep (se 2 (by rfl) ⟨10607010, by rfl⟩ : syracuseStep 28285361 = 21214021) B21214021
theorem B1743287 : Blo 1742572 1743287 := bstep (se 1 (by rfl) ⟨1307465, by rfl⟩ : syracuseStep 1743287 = 2614931) B2614931
theorem B3922379 : Blo 1742572 3922379 := bstep (se 1 (by rfl) ⟨2941784, by rfl⟩ : syracuseStep 3922379 = 5883569) B5883569
theorem B1743307 : Blo 1742572 1743307 := bstep (se 1 (by rfl) ⟨1307480, by rfl⟩ : syracuseStep 1743307 = 2614961) B2614961
theorem B1743319 : Blo 1742572 1743319 := bstep (se 1 (by rfl) ⟨1307489, by rfl⟩ : syracuseStep 1743319 = 2614979) B2614979
theorem B1743339 : Blo 1742572 1743339 := bstep (se 1 (by rfl) ⟨1307504, by rfl⟩ : syracuseStep 1743339 = 2615009) B2615009
theorem B1743351 : Blo 1742572 1743351 := bstep (se 1 (by rfl) ⟨1307513, by rfl⟩ : syracuseStep 1743351 = 2615027) B2615027
theorem B3922433 : Blo 1742572 3922433 := bstep (se 2 (by rfl) ⟨1470912, by rfl⟩ : syracuseStep 3922433 = 2941825) B2941825
theorem B14891525 : Blo 1742572 14891525 := bstep (se 4 (by rfl) ⟨1396080, by rfl⟩ : syracuseStep 14891525 = 2792161) B2792161
theorem B1743371 : Blo 1742572 1743371 := bstep (se 1 (by rfl) ⟨1307528, by rfl⟩ : syracuseStep 1743371 = 2615057) B2615057
theorem B1743383 : Blo 1742572 1743383 := bstep (se 1 (by rfl) ⟨1307537, by rfl⟩ : syracuseStep 1743383 = 2615075) B2615075
theorem B1743403 : Blo 1742572 1743403 := bstep (se 1 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 1743403 = 2615105) B2615105
theorem B8829485 : Blo 1742572 8829485 := bstep (se 3 (by rfl) ⟨1655528, by rfl⟩ : syracuseStep 8829485 = 3311057) B3311057
theorem B9935405 : Blo 1742572 9935405 := bstep (se 3 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 9935405 = 3725777) B3725777
theorem B1743415 : Blo 1742572 1743415 := bstep (se 1 (by rfl) ⟨1307561, by rfl⟩ : syracuseStep 1743415 = 2615123) B2615123
theorem B15096395 : Blo 1742572 15096395 := bstep (se 1 (by rfl) ⟨11322296, by rfl⟩ : syracuseStep 15096395 = 22644593) B22644593
theorem B1743435 : Blo 1742572 1743435 := bstep (se 1 (by rfl) ⟨1307576, by rfl⟩ : syracuseStep 1743435 = 2615153) B2615153
theorem B1743447 : Blo 1742572 1743447 := bstep (se 1 (by rfl) ⟨1307585, by rfl⟩ : syracuseStep 1743447 = 2615171) B2615171
theorem B1743467 : Blo 1742572 1743467 := bstep (se 1 (by rfl) ⟨1307600, by rfl⟩ : syracuseStep 1743467 = 2615201) B2615201
theorem B1743479 : Blo 1742572 1743479 := bstep (se 1 (by rfl) ⟨1307609, by rfl⟩ : syracuseStep 1743479 = 2615219) B2615219
theorem B1989239 : Blo 1742572 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B1743499 : Blo 1742572 1743499 := bstep (se 1 (by rfl) ⟨1307624, by rfl⟩ : syracuseStep 1743499 = 2615249) B2615249
theorem B1743511 : Blo 1742572 1743511 := bstep (se 1 (by rfl) ⟨1307633, by rfl⟩ : syracuseStep 1743511 = 2615267) B2615267
theorem B1743531 : Blo 1742572 1743531 := bstep (se 1 (by rfl) ⟨1307648, by rfl⟩ : syracuseStep 1743531 = 2615297) B2615297
theorem B1743543 : Blo 1742572 1743543 := bstep (se 1 (by rfl) ⟨1307657, by rfl⟩ : syracuseStep 1743543 = 2615315) B2615315
theorem B1743563 : Blo 1742572 1743563 := bstep (se 1 (by rfl) ⟨1307672, by rfl⟩ : syracuseStep 1743563 = 2615345) B2615345
theorem B1743575 : Blo 1742572 1743575 := bstep (se 1 (by rfl) ⟨1307681, by rfl⟩ : syracuseStep 1743575 = 2615363) B2615363
theorem B6281945 : Blo 1742572 6281945 := bstep (se 2 (by rfl) ⟨2355729, by rfl⟩ : syracuseStep 6281945 = 4711459) B4711459
theorem B3922649 : Blo 1742572 3922649 := bstep (se 2 (by rfl) ⟨1470993, by rfl⟩ : syracuseStep 3922649 = 2941987) B2941987
theorem B1743595 : Blo 1742572 1743595 := bstep (se 1 (by rfl) ⟨1307696, by rfl⟩ : syracuseStep 1743595 = 2615393) B2615393
theorem B1743607 : Blo 1742572 1743607 := bstep (se 1 (by rfl) ⟨1307705, by rfl⟩ : syracuseStep 1743607 = 2615411) B2615411
theorem B1743627 : Blo 1742572 1743627 := bstep (se 1 (by rfl) ⟨1307720, by rfl⟩ : syracuseStep 1743627 = 2615441) B2615441
theorem B1743639 : Blo 1742572 1743639 := bstep (se 1 (by rfl) ⟨1307729, by rfl⟩ : syracuseStep 1743639 = 2615459) B2615459
theorem B1743659 : Blo 1742572 1743659 := bstep (se 1 (by rfl) ⟨1307744, by rfl⟩ : syracuseStep 1743659 = 2615489) B2615489
theorem B3308339 : Blo 1742572 3308339 := bstep (se 1 (by rfl) ⟨2481254, by rfl⟩ : syracuseStep 3308339 = 4962509) B4962509
theorem B4963123 : Blo 1742572 4963123 := bstep (se 1 (by rfl) ⟨3722342, by rfl⟩ : syracuseStep 4963123 = 7444685) B7444685
theorem B3922739 : Blo 1742572 3922739 := bstep (se 1 (by rfl) ⟨2942054, by rfl⟩ : syracuseStep 3922739 = 5884109) B5884109
theorem B1743671 : Blo 1742572 1743671 := bstep (se 1 (by rfl) ⟨1307753, by rfl⟩ : syracuseStep 1743671 = 2615507) B2615507
theorem B310057793 : Blo 1742572 310057793 := bstep (se 2 (by rfl) ⟨116271672, by rfl⟩ : syracuseStep 310057793 = 232543345) B232543345
theorem B1743691 : Blo 1742572 1743691 := bstep (se 1 (by rfl) ⟨1307768, by rfl⟩ : syracuseStep 1743691 = 2615537) B2615537
theorem B3922775 : Blo 1742572 3922775 := bstep (se 1 (by rfl) ⟨2942081, by rfl⟩ : syracuseStep 3922775 = 5884163) B5884163
theorem B1743703 : Blo 1742572 1743703 := bstep (se 1 (by rfl) ⟨1307777, by rfl⟩ : syracuseStep 1743703 = 2615555) B2615555
theorem B3308377 : Blo 1742572 3308377 := bstep (se 2 (by rfl) ⟨1240641, by rfl⟩ : syracuseStep 3308377 = 2481283) B2481283
theorem B4414297 : Blo 1742572 4414297 := bstep (se 2 (by rfl) ⟨1655361, by rfl⟩ : syracuseStep 4414297 = 3310723) B3310723
theorem B1743723 : Blo 1742572 1743723 := bstep (se 1 (by rfl) ⟨1307792, by rfl⟩ : syracuseStep 1743723 = 2615585) B2615585
theorem B1743735 : Blo 1742572 1743735 := bstep (se 1 (by rfl) ⟨1307801, by rfl⟩ : syracuseStep 1743735 = 2615603) B2615603
theorem B1743755 : Blo 1742572 1743755 := bstep (se 1 (by rfl) ⟨1307816, by rfl⟩ : syracuseStep 1743755 = 2615633) B2615633
theorem B1743767 : Blo 1742572 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B1743787 : Blo 1742572 1743787 := bstep (se 1 (by rfl) ⟨1307840, by rfl⟩ : syracuseStep 1743787 = 2615681) B2615681
theorem B1743799 : Blo 1742572 1743799 := bstep (se 1 (by rfl) ⟨1307849, by rfl⟩ : syracuseStep 1743799 = 2615699) B2615699
theorem B1743819 : Blo 1742572 1743819 := bstep (se 1 (by rfl) ⟨1307864, by rfl⟩ : syracuseStep 1743819 = 2615729) B2615729
theorem B1743831 : Blo 1742572 1743831 := bstep (se 1 (by rfl) ⟨1307873, by rfl⟩ : syracuseStep 1743831 = 2615747) B2615747
theorem B1743851 : Blo 1742572 1743851 := bstep (se 1 (by rfl) ⟨1307888, by rfl⟩ : syracuseStep 1743851 = 2615777) B2615777
theorem B1743863 : Blo 1742572 1743863 := bstep (se 1 (by rfl) ⟨1307897, by rfl⟩ : syracuseStep 1743863 = 2615795) B2615795
theorem B3922955 : Blo 1742572 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B1743883 : Blo 1742572 1743883 := bstep (se 1 (by rfl) ⟨1307912, by rfl⟩ : syracuseStep 1743883 = 2615825) B2615825
theorem B4963351 : Blo 1742572 4963351 := bstep (se 1 (by rfl) ⟨3722513, by rfl⟩ : syracuseStep 4963351 = 7445027) B7445027
theorem B1743895 : Blo 1742572 1743895 := bstep (se 1 (by rfl) ⟨1307921, by rfl⟩ : syracuseStep 1743895 = 2615843) B2615843
theorem B1743915 : Blo 1742572 1743915 := bstep (se 1 (by rfl) ⟨1307936, by rfl⟩ : syracuseStep 1743915 = 2615873) B2615873
theorem B1743927 : Blo 1742572 1743927 := bstep (se 1 (by rfl) ⟨1307945, by rfl⟩ : syracuseStep 1743927 = 2615891) B2615891
theorem B3923009 : Blo 1742572 3923009 := bstep (se 2 (by rfl) ⟨1471128, by rfl⟩ : syracuseStep 3923009 = 2942257) B2942257
theorem B17890379 : Blo 1742572 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B1743947 : Blo 1742572 1743947 := bstep (se 1 (by rfl) ⟨1307960, by rfl⟩ : syracuseStep 1743947 = 2615921) B2615921
theorem B1743959 : Blo 1742572 1743959 := bstep (se 1 (by rfl) ⟨1307969, by rfl⟩ : syracuseStep 1743959 = 2615939) B2615939
theorem B1743979 : Blo 1742572 1743979 := bstep (se 1 (by rfl) ⟨1307984, by rfl⟩ : syracuseStep 1743979 = 2615969) B2615969
theorem B1743991 : Blo 1742572 1743991 := bstep (se 1 (by rfl) ⟨1307993, by rfl⟩ : syracuseStep 1743991 = 2615987) B2615987
theorem B1744011 : Blo 1742572 1744011 := bstep (se 1 (by rfl) ⟨1308008, by rfl⟩ : syracuseStep 1744011 = 2616017) B2616017
theorem B6618257 : Blo 1742572 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B1744023 : Blo 1742572 1744023 := bstep (se 1 (by rfl) ⟨1308017, by rfl⟩ : syracuseStep 1744023 = 2616035) B2616035
theorem B1744043 : Blo 1742572 1744043 := bstep (se 1 (by rfl) ⟨1308032, by rfl⟩ : syracuseStep 1744043 = 2616065) B2616065
theorem B47733941 : Blo 1742572 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B1744055 : Blo 1742572 1744055 := bstep (se 1 (by rfl) ⟨1308041, by rfl⟩ : syracuseStep 1744055 = 2616083) B2616083
theorem B4472011 : Blo 1742572 4472011 := bstep (se 1 (by rfl) ⟨3354008, by rfl⟩ : syracuseStep 4472011 = 6708017) B6708017
theorem B1744075 : Blo 1742572 1744075 := bstep (se 1 (by rfl) ⟨1308056, by rfl⟩ : syracuseStep 1744075 = 2616113) B2616113
theorem B1744087 : Blo 1742572 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B1744107 : Blo 1742572 1744107 := bstep (se 1 (by rfl) ⟨1308080, by rfl⟩ : syracuseStep 1744107 = 2616161) B2616161
theorem B1744119 : Blo 1742572 1744119 := bstep (se 1 (by rfl) ⟨1308089, by rfl⟩ : syracuseStep 1744119 = 2616179) B2616179
theorem B1744139 : Blo 1742572 1744139 := bstep (se 1 (by rfl) ⟨1308104, by rfl⟩ : syracuseStep 1744139 = 2616209) B2616209
theorem B8822033 : Blo 1742572 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B1744151 : Blo 1742572 1744151 := bstep (se 1 (by rfl) ⟨1308113, by rfl⟩ : syracuseStep 1744151 = 2616227) B2616227
theorem B3308825 : Blo 1742572 3308825 := bstep (se 2 (by rfl) ⟨1240809, by rfl⟩ : syracuseStep 3308825 = 2481619) B2481619
theorem B3923225 : Blo 1742572 3923225 := bstep (se 2 (by rfl) ⟨1471209, by rfl⟩ : syracuseStep 3923225 = 2942419) B2942419
theorem B1744171 : Blo 1742572 1744171 := bstep (se 1 (by rfl) ⟨1308128, by rfl⟩ : syracuseStep 1744171 = 2616257) B2616257
theorem B1744183 : Blo 1742572 1744183 := bstep (se 1 (by rfl) ⟨1308137, by rfl⟩ : syracuseStep 1744183 = 2616275) B2616275
theorem B1744203 : Blo 1742572 1744203 := bstep (se 1 (by rfl) ⟨1308152, by rfl⟩ : syracuseStep 1744203 = 2616305) B2616305
theorem B1744215 : Blo 1742572 1744215 := bstep (se 1 (by rfl) ⟨1308161, by rfl⟩ : syracuseStep 1744215 = 2616323) B2616323
theorem B1744235 : Blo 1742572 1744235 := bstep (se 1 (by rfl) ⟨1308176, by rfl⟩ : syracuseStep 1744235 = 2616353) B2616353
theorem B3923315 : Blo 1742572 3923315 := bstep (se 1 (by rfl) ⟨2942486, by rfl⟩ : syracuseStep 3923315 = 5884973) B5884973
theorem B50265461 : Blo 1742572 50265461 := bstep (se 5 (by rfl) ⟨2356193, by rfl⟩ : syracuseStep 50265461 = 4712387) B4712387
theorem B1744247 : Blo 1742572 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B3186049 : Blo 1742572 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B1744267 : Blo 1742572 1744267 := bstep (se 1 (by rfl) ⟨1308200, by rfl⟩ : syracuseStep 1744267 = 2616401) B2616401
theorem B3923351 : Blo 1742572 3923351 := bstep (se 1 (by rfl) ⟨2942513, by rfl⟩ : syracuseStep 3923351 = 5885027) B5885027
theorem B1744279 : Blo 1742572 1744279 := bstep (se 1 (by rfl) ⟨1308209, by rfl⟩ : syracuseStep 1744279 = 2616419) B2616419
theorem B1744299 : Blo 1742572 1744299 := bstep (se 1 (by rfl) ⟨1308224, by rfl⟩ : syracuseStep 1744299 = 2616449) B2616449
theorem B8822195 : Blo 1742572 8822195 := bstep (se 1 (by rfl) ⟨6616646, by rfl⟩ : syracuseStep 8822195 = 13233293) B13233293
theorem B15900083 : Blo 1742572 15900083 := bstep (se 1 (by rfl) ⟨11925062, by rfl⟩ : syracuseStep 15900083 = 23850125) B23850125
theorem B9928115 : Blo 1742572 9928115 := bstep (se 1 (by rfl) ⟨7446086, by rfl⟩ : syracuseStep 9928115 = 14892173) B14892173
theorem B1744311 : Blo 1742572 1744311 := bstep (se 1 (by rfl) ⟨1308233, by rfl⟩ : syracuseStep 1744311 = 2616467) B2616467
theorem B7364033 : Blo 1742572 7364033 := bstep (se 2 (by rfl) ⟨2761512, by rfl⟩ : syracuseStep 7364033 = 5523025) B5523025
theorem B1744331 : Blo 1742572 1744331 := bstep (se 1 (by rfl) ⟨1308248, by rfl⟩ : syracuseStep 1744331 = 2616497) B2616497
theorem B1744343 : Blo 1742572 1744343 := bstep (se 1 (by rfl) ⟨1308257, by rfl⟩ : syracuseStep 1744343 = 2616515) B2616515
theorem B1744363 : Blo 1742572 1744363 := bstep (se 1 (by rfl) ⟨1308272, by rfl⟩ : syracuseStep 1744363 = 2616545) B2616545
theorem B1744375 : Blo 1742572 1744375 := bstep (se 1 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 1744375 = 2616563) B2616563
theorem B1744395 : Blo 1742572 1744395 := bstep (se 1 (by rfl) ⟨1308296, by rfl⟩ : syracuseStep 1744395 = 2616593) B2616593
theorem B1744407 : Blo 1742572 1744407 := bstep (se 1 (by rfl) ⟨1308305, by rfl⟩ : syracuseStep 1744407 = 2616611) B2616611
theorem B1744427 : Blo 1742572 1744427 := bstep (se 1 (by rfl) ⟨1308320, by rfl⟩ : syracuseStep 1744427 = 2616641) B2616641
theorem B1744439 : Blo 1742572 1744439 := bstep (se 1 (by rfl) ⟨1308329, by rfl⟩ : syracuseStep 1744439 = 2616659) B2616659
theorem B5881409 : Blo 1742572 5881409 := bstep (se 2 (by rfl) ⟨2205528, by rfl⟩ : syracuseStep 5881409 = 4411057) B4411057
theorem B3923531 : Blo 1742572 3923531 := bstep (se 1 (by rfl) ⟨2942648, by rfl⟩ : syracuseStep 3923531 = 5885297) B5885297
theorem B1744459 : Blo 1742572 1744459 := bstep (se 1 (by rfl) ⟨1308344, by rfl⟩ : syracuseStep 1744459 = 2616689) B2616689
theorem B1744471 : Blo 1742572 1744471 := bstep (se 1 (by rfl) ⟨1308353, by rfl⟩ : syracuseStep 1744471 = 2616707) B2616707
theorem B1744491 : Blo 1742572 1744491 := bstep (se 1 (by rfl) ⟨1308368, by rfl⟩ : syracuseStep 1744491 = 2616737) B2616737
theorem B1744503 : Blo 1742572 1744503 := bstep (se 1 (by rfl) ⟨1308377, by rfl⟩ : syracuseStep 1744503 = 2616755) B2616755
theorem B3923585 : Blo 1742572 3923585 := bstep (se 2 (by rfl) ⟨1471344, by rfl⟩ : syracuseStep 3923585 = 2942689) B2942689
theorem B1744523 : Blo 1742572 1744523 := bstep (se 1 (by rfl) ⟨1308392, by rfl⟩ : syracuseStep 1744523 = 2616785) B2616785
theorem B1744535 : Blo 1742572 1744535 := bstep (se 1 (by rfl) ⟨1308401, by rfl⟩ : syracuseStep 1744535 = 2616803) B2616803
theorem B1744555 : Blo 1742572 1744555 := bstep (se 1 (by rfl) ⟨1308416, by rfl⟩ : syracuseStep 1744555 = 2616833) B2616833
theorem B1744567 : Blo 1742572 1744567 := bstep (se 1 (by rfl) ⟨1308425, by rfl⟩ : syracuseStep 1744567 = 2616851) B2616851
theorem B2981593 : Blo 1742572 2981593 := bstep (se 2 (by rfl) ⟨1118097, by rfl⟩ : syracuseStep 2981593 = 2236195) B2236195
theorem B50298677 : Blo 1742572 50298677 := bstep (se 5 (by rfl) ⟨2357750, by rfl⟩ : syracuseStep 50298677 = 4715501) B4715501
theorem B6618955 : Blo 1742572 6618955 := bstep (se 1 (by rfl) ⟨4964216, by rfl⟩ : syracuseStep 6618955 = 9928433) B9928433
theorem B3923801 : Blo 1742572 3923801 := bstep (se 2 (by rfl) ⟨1471425, by rfl⟩ : syracuseStep 3923801 = 2942851) B2942851
theorem B67952483 : Blo 1742572 67952483 := bstep (se 1 (by rfl) ⟨50964362, by rfl⟩ : syracuseStep 67952483 = 101928725) B101928725
theorem B7069619 : Blo 1742572 7069619 := bstep (se 1 (by rfl) ⟨5302214, by rfl⟩ : syracuseStep 7069619 = 10604429) B10604429
theorem B3923891 : Blo 1742572 3923891 := bstep (se 1 (by rfl) ⟨2942918, by rfl⟩ : syracuseStep 3923891 = 5885837) B5885837
theorem B4415411 : Blo 1742572 4415411 := bstep (se 1 (by rfl) ⟨3311558, by rfl⟩ : syracuseStep 4415411 = 6623117) B6623117
theorem B2940887 : Blo 1742572 2940887 := bstep (se 1 (by rfl) ⟨2205665, by rfl⟩ : syracuseStep 2940887 = 4411331) B4411331
theorem B3923927 : Blo 1742572 3923927 := bstep (se 1 (by rfl) ⟨2942945, by rfl⟩ : syracuseStep 3923927 = 5885891) B5885891
theorem B5882057 : Blo 1742572 5882057 := bstep (se 2 (by rfl) ⟨2205771, by rfl⟩ : syracuseStep 5882057 = 4411543) B4411543
theorem B4415755 : Blo 1742572 4415755 := bstep (se 1 (by rfl) ⟨3311816, by rfl⟩ : syracuseStep 4415755 = 6623633) B6623633
theorem B11174203 : Blo 1742572 11174203 := bstep (se 1 (by rfl) ⟨8380652, by rfl⟩ : syracuseStep 11174203 = 16761305) B16761305
theorem B2941319 : Blo 1742572 2941319 := bstep (se 1 (by rfl) ⟨2205989, by rfl⟩ : syracuseStep 2941319 = 4411979) B4411979
theorem B3924359 : Blo 1742572 3924359 := bstep (se 1 (by rfl) ⟨2943269, by rfl⟩ : syracuseStep 3924359 = 5886539) B5886539
theorem B4415897 : Blo 1742572 4415897 := bstep (se 2 (by rfl) ⟨1655961, by rfl⟩ : syracuseStep 4415897 = 3311923) B3311923
theorem B4964809 : Blo 1742572 4964809 := bstep (se 2 (by rfl) ⟨1861803, by rfl⟩ : syracuseStep 4964809 = 3723607) B3723607
theorem B2982415 : Blo 1742572 2982415 := bstep (se 1 (by rfl) ⟨2236811, by rfl⟩ : syracuseStep 2982415 = 4473623) B4473623
theorem B3310139 : Blo 1742572 3310139 := bstep (se 1 (by rfl) ⟨2482604, by rfl⟩ : syracuseStep 3310139 = 4965209) B4965209
theorem B3924539 : Blo 1742572 3924539 := bstep (se 1 (by rfl) ⟨2943404, by rfl⟩ : syracuseStep 3924539 = 5886809) B5886809
theorem B10601027 : Blo 1742572 10601027 := bstep (se 1 (by rfl) ⟨7950770, by rfl⟩ : syracuseStep 10601027 = 15901541) B15901541
theorem B6619715 : Blo 1742572 6619715 := bstep (se 1 (by rfl) ⟨4964786, by rfl⟩ : syracuseStep 6619715 = 9929573) B9929573
theorem B3924665 : Blo 1742572 3924665 := bstep (se 2 (by rfl) ⟨1471749, by rfl⟩ : syracuseStep 3924665 = 2943499) B2943499
theorem B2613947 : Blo 1742572 2613947 := bstep (se 1 (by rfl) ⟨1960460, by rfl⟩ : syracuseStep 2613947 = 3920921) B3920921
theorem B2614007 : Blo 1742572 2614007 := bstep (se 1 (by rfl) ⟨1960505, by rfl⟩ : syracuseStep 2614007 = 3921011) B3921011
theorem B5030657 : Blo 1742572 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B2614031 : Blo 1742572 2614031 := bstep (se 1 (by rfl) ⟨1960523, by rfl⟩ : syracuseStep 2614031 = 3921047) B3921047
theorem B2614073 : Blo 1742572 2614073 := bstep (se 2 (by rfl) ⟨980277, by rfl⟩ : syracuseStep 2614073 = 1960555) B1960555
theorem B2614151 : Blo 1742572 2614151 := bstep (se 1 (by rfl) ⟨1960613, by rfl⟩ : syracuseStep 2614151 = 3921227) B3921227
theorem B5882759 : Blo 1742572 5882759 := bstep (se 1 (by rfl) ⟨4412069, by rfl⟩ : syracuseStep 5882759 = 8824139) B8824139
theorem B2614187 : Blo 1742572 2614187 := bstep (se 1 (by rfl) ⟨1960640, by rfl⟩ : syracuseStep 2614187 = 3921281) B3921281
theorem B2614217 : Blo 1742572 2614217 := bstep (se 2 (by rfl) ⟨980331, by rfl⟩ : syracuseStep 2614217 = 1960663) B1960663
theorem B2941967 : Blo 1742572 2941967 := bstep (se 1 (by rfl) ⟨2206475, by rfl⟩ : syracuseStep 2941967 = 4412951) B4412951
theorem B3925007 : Blo 1742572 3925007 := bstep (se 1 (by rfl) ⟨2943755, by rfl⟩ : syracuseStep 3925007 = 5887511) B5887511
theorem B3310625 : Blo 1742572 3310625 := bstep (se 2 (by rfl) ⟨1241484, by rfl⟩ : syracuseStep 3310625 = 2482969) B2482969
theorem B3925025 : Blo 1742572 3925025 := bstep (se 2 (by rfl) ⟨1471884, by rfl⟩ : syracuseStep 3925025 = 2943769) B2943769
theorem B2614331 : Blo 1742572 2614331 := bstep (se 1 (by rfl) ⟨1960748, by rfl⟩ : syracuseStep 2614331 = 3921497) B3921497
theorem B8381501 : Blo 1742572 8381501 := bstep (se 3 (by rfl) ⟨1571531, by rfl⟩ : syracuseStep 8381501 = 3143063) B3143063
theorem B4187251 : Blo 1742572 4187251 := bstep (se 1 (by rfl) ⟨3140438, by rfl⟩ : syracuseStep 4187251 = 6280877) B6280877
theorem B2614391 : Blo 1742572 2614391 := bstep (se 1 (by rfl) ⟨1960793, by rfl⟩ : syracuseStep 2614391 = 3921587) B3921587
theorem B15901829 : Blo 1742572 15901829 := bstep (se 4 (by rfl) ⟨1490796, by rfl⟩ : syracuseStep 15901829 = 2981593) B2981593
theorem B2614415 : Blo 1742572 2614415 := bstep (se 1 (by rfl) ⟨1960811, by rfl⟩ : syracuseStep 2614415 = 3921623) B3921623
theorem B2614457 : Blo 1742572 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B7070921 : Blo 1742572 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B5883137 : Blo 1742572 5883137 := bstep (se 2 (by rfl) ⟨2206176, by rfl⟩ : syracuseStep 5883137 = 4412353) B4412353
theorem B2614535 : Blo 1742572 2614535 := bstep (se 1 (by rfl) ⟨1960901, by rfl⟩ : syracuseStep 2614535 = 3921803) B3921803
theorem B15099169 : Blo 1742572 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B2614571 : Blo 1742572 2614571 := bstep (se 1 (by rfl) ⟨1960928, by rfl⟩ : syracuseStep 2614571 = 3921857) B3921857
theorem B13239611 : Blo 1742572 13239611 := bstep (se 1 (by rfl) ⟨9929708, by rfl⟩ : syracuseStep 13239611 = 19859417) B19859417
theorem B2614601 : Blo 1742572 2614601 := bstep (se 2 (by rfl) ⟨980475, by rfl⟩ : syracuseStep 2614601 = 1960951) B1960951
theorem B9930073 : Blo 1742572 9930073 := bstep (se 2 (by rfl) ⟨3723777, by rfl⟩ : syracuseStep 9930073 = 7447555) B7447555
theorem B2614715 : Blo 1742572 2614715 := bstep (se 1 (by rfl) ⟨1961036, by rfl⟩ : syracuseStep 2614715 = 3922073) B3922073
theorem B2614775 : Blo 1742572 2614775 := bstep (se 1 (by rfl) ⟨1961081, by rfl⟩ : syracuseStep 2614775 = 3922163) B3922163
theorem B2614799 : Blo 1742572 2614799 := bstep (se 1 (by rfl) ⟨1961099, by rfl⟩ : syracuseStep 2614799 = 3922199) B3922199
theorem B2942507 : Blo 1742572 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B2614841 : Blo 1742572 2614841 := bstep (se 2 (by rfl) ⟨980565, by rfl⟩ : syracuseStep 2614841 = 1961131) B1961131
theorem B7071293 : Blo 1742572 7071293 := bstep (se 3 (by rfl) ⟨1325867, by rfl⟩ : syracuseStep 7071293 = 2651735) B2651735
theorem B2614919 : Blo 1742572 2614919 := bstep (se 1 (by rfl) ⟨1961189, by rfl⟩ : syracuseStep 2614919 = 3922379) B3922379
theorem B2614955 : Blo 1742572 2614955 := bstep (se 1 (by rfl) ⟨1961216, by rfl⟩ : syracuseStep 2614955 = 3922433) B3922433
theorem B2614985 : Blo 1742572 2614985 := bstep (se 2 (by rfl) ⟨980619, by rfl⟩ : syracuseStep 2614985 = 1961239) B1961239
theorem B4187963 : Blo 1742572 4187963 := bstep (se 1 (by rfl) ⟨3140972, by rfl⟩ : syracuseStep 4187963 = 6281945) B6281945
theorem B2615099 : Blo 1742572 2615099 := bstep (se 1 (by rfl) ⟨1961324, by rfl⟩ : syracuseStep 2615099 = 3922649) B3922649
theorem B2205559 : Blo 1742572 2205559 := bstep (se 1 (by rfl) ⟨1654169, by rfl⟩ : syracuseStep 2205559 = 3308339) B3308339
theorem B2615159 : Blo 1742572 2615159 := bstep (se 1 (by rfl) ⟨1961369, by rfl⟩ : syracuseStep 2615159 = 3922739) B3922739
theorem B2615183 : Blo 1742572 2615183 := bstep (se 1 (by rfl) ⟨1961387, by rfl⟩ : syracuseStep 2615183 = 3922775) B3922775
theorem B4712345 : Blo 1742572 4712345 := bstep (se 2 (by rfl) ⟨1767129, by rfl⟩ : syracuseStep 4712345 = 3534259) B3534259
theorem B2615225 : Blo 1742572 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B2942905 : Blo 1742572 2942905 := bstep (se 2 (by rfl) ⟨1103589, by rfl⟩ : syracuseStep 2942905 = 2207179) B2207179
theorem B2615303 : Blo 1742572 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B5883947 : Blo 1742572 5883947 := bstep (se 1 (by rfl) ⟨4412960, by rfl⟩ : syracuseStep 5883947 = 8825921) B8825921
theorem B2615339 : Blo 1742572 2615339 := bstep (se 1 (by rfl) ⟨1961504, by rfl⟩ : syracuseStep 2615339 = 3923009) B3923009
theorem B2615369 : Blo 1742572 2615369 := bstep (se 2 (by rfl) ⟨980763, by rfl⟩ : syracuseStep 2615369 = 1961527) B1961527
theorem B2205883 : Blo 1742572 2205883 := bstep (se 1 (by rfl) ⟨1654412, by rfl⟩ : syracuseStep 2205883 = 3308825) B3308825
theorem B2615483 : Blo 1742572 2615483 := bstep (se 1 (by rfl) ⟨1961612, by rfl⟩ : syracuseStep 2615483 = 3923225) B3923225
theorem B6621385 : Blo 1742572 6621385 := bstep (se 2 (by rfl) ⟨2483019, by rfl⟩ : syracuseStep 6621385 = 4966039) B4966039
theorem B2615543 : Blo 1742572 2615543 := bstep (se 1 (by rfl) ⟨1961657, by rfl⟩ : syracuseStep 2615543 = 3923315) B3923315
theorem B4966667 : Blo 1742572 4966667 := bstep (se 1 (by rfl) ⟨3725000, by rfl⟩ : syracuseStep 4966667 = 7450001) B7450001
theorem B2615567 : Blo 1742572 2615567 := bstep (se 1 (by rfl) ⟨1961675, by rfl⟩ : syracuseStep 2615567 = 3923351) B3923351
theorem B14903585 : Blo 1742572 14903585 := bstep (se 2 (by rfl) ⟨5588844, by rfl⟩ : syracuseStep 14903585 = 11177689) B11177689
theorem B4909355 : Blo 1742572 4909355 := bstep (se 1 (by rfl) ⟨3682016, by rfl⟩ : syracuseStep 4909355 = 7364033) B7364033
theorem B2615609 : Blo 1742572 2615609 := bstep (se 2 (by rfl) ⟨980853, by rfl⟩ : syracuseStep 2615609 = 1961707) B1961707
theorem B2615687 : Blo 1742572 2615687 := bstep (se 1 (by rfl) ⟨1961765, by rfl⟩ : syracuseStep 2615687 = 3923531) B3923531
theorem B8489369 : Blo 1742572 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B6285721 : Blo 1742572 6285721 := bstep (se 2 (by rfl) ⟨2357145, by rfl⟩ : syracuseStep 6285721 = 4714291) B4714291
theorem B2615723 : Blo 1742572 2615723 := bstep (se 1 (by rfl) ⟨1961792, by rfl⟩ : syracuseStep 2615723 = 3923585) B3923585
theorem B8825273 : Blo 1742572 8825273 := bstep (se 2 (by rfl) ⟨3309477, by rfl⟩ : syracuseStep 8825273 = 6618955) B6618955
theorem B2615753 : Blo 1742572 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B18852317 : Blo 1742572 18852317 := bstep (se 3 (by rfl) ⟨3534809, by rfl⟩ : syracuseStep 18852317 = 7069619) B7069619
theorem B33532451 : Blo 1742572 33532451 := bstep (se 1 (by rfl) ⟨25149338, by rfl⟩ : syracuseStep 33532451 = 50298677) B50298677
theorem B31803947 : Blo 1742572 31803947 := bstep (se 1 (by rfl) ⟨23852960, by rfl⟩ : syracuseStep 31803947 = 47705921) B47705921
theorem B2615867 : Blo 1742572 2615867 := bstep (se 1 (by rfl) ⟨1961900, by rfl⟩ : syracuseStep 2615867 = 3923801) B3923801
theorem B2615927 : Blo 1742572 2615927 := bstep (se 1 (by rfl) ⟨1961945, by rfl⟩ : syracuseStep 2615927 = 3923891) B3923891
theorem B2943607 : Blo 1742572 2943607 := bstep (se 1 (by rfl) ⟨2207705, by rfl⟩ : syracuseStep 2943607 = 4415411) B4415411
theorem B1960591 : Blo 1742572 1960591 := bstep (se 1 (by rfl) ⟨1470443, by rfl⟩ : syracuseStep 1960591 = 2940887) B2940887
theorem B2615951 : Blo 1742572 2615951 := bstep (se 1 (by rfl) ⟨1961963, by rfl⟩ : syracuseStep 2615951 = 3923927) B3923927
theorem B2206379 : Blo 1742572 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B2615993 : Blo 1742572 2615993 := bstep (se 2 (by rfl) ⟨980997, by rfl⟩ : syracuseStep 2615993 = 1961995) B1961995
theorem B2616071 : Blo 1742572 2616071 := bstep (se 1 (by rfl) ⟨1962053, by rfl⟩ : syracuseStep 2616071 = 3924107) B3924107
theorem B2616107 : Blo 1742572 2616107 := bstep (se 1 (by rfl) ⟨1962080, by rfl⟩ : syracuseStep 2616107 = 3924161) B3924161
theorem B2943803 : Blo 1742572 2943803 := bstep (se 1 (by rfl) ⟨2207852, by rfl⟩ : syracuseStep 2943803 = 4415705) B4415705
theorem B2616137 : Blo 1742572 2616137 := bstep (se 2 (by rfl) ⟨981051, by rfl⟩ : syracuseStep 2616137 = 1962103) B1962103
theorem B4967315 : Blo 1742572 4967315 := bstep (se 1 (by rfl) ⟨3725486, by rfl⟩ : syracuseStep 4967315 = 7450973) B7450973
theorem B2616251 : Blo 1742572 2616251 := bstep (se 1 (by rfl) ⟨1962188, by rfl⟩ : syracuseStep 2616251 = 3924377) B3924377
theorem B2616311 : Blo 1742572 2616311 := bstep (se 1 (by rfl) ⟨1962233, by rfl⟩ : syracuseStep 2616311 = 3924467) B3924467
theorem B2616335 : Blo 1742572 2616335 := bstep (se 1 (by rfl) ⟨1962251, by rfl⟩ : syracuseStep 2616335 = 3924503) B3924503
theorem B1862671 : Blo 1742572 1862671 := bstep (se 1 (by rfl) ⟨1397003, by rfl⟩ : syracuseStep 1862671 = 2794007) B2794007
theorem B9931805 : Blo 1742572 9931805 := bstep (se 3 (by rfl) ⟨1862213, by rfl⟩ : syracuseStep 9931805 = 3724427) B3724427
theorem B2616377 : Blo 1742572 2616377 := bstep (se 2 (by rfl) ⟨981141, by rfl⟩ : syracuseStep 2616377 = 1962283) B1962283
theorem B4967543 : Blo 1742572 4967543 := bstep (se 1 (by rfl) ⟨3725657, by rfl⟩ : syracuseStep 4967543 = 7451315) B7451315
theorem B1961095 : Blo 1742572 1961095 := bstep (se 1 (by rfl) ⟨1470821, by rfl⟩ : syracuseStep 1961095 = 2941643) B2941643
theorem B2206855 : Blo 1742572 2206855 := bstep (se 1 (by rfl) ⟨1655141, by rfl⟩ : syracuseStep 2206855 = 3310283) B3310283
theorem B2616455 : Blo 1742572 2616455 := bstep (se 1 (by rfl) ⟨1962341, by rfl⟩ : syracuseStep 2616455 = 3924683) B3924683
theorem B12561581 : Blo 1742572 12561581 := bstep (se 3 (by rfl) ⟨2355296, by rfl⟩ : syracuseStep 12561581 = 4710593) B4710593
theorem B2616491 : Blo 1742572 2616491 := bstep (se 1 (by rfl) ⟨1962368, by rfl⟩ : syracuseStep 2616491 = 3924737) B3924737
theorem B2616521 : Blo 1742572 2616521 := bstep (se 2 (by rfl) ⟨981195, by rfl⟩ : syracuseStep 2616521 = 1962391) B1962391
theorem B1961275 : Blo 1742572 1961275 := bstep (se 1 (by rfl) ⟨1470956, by rfl⟩ : syracuseStep 1961275 = 2941913) B2941913
theorem B5885243 : Blo 1742572 5885243 := bstep (se 1 (by rfl) ⟨4413932, by rfl⟩ : syracuseStep 5885243 = 8827865) B8827865
theorem B2616635 : Blo 1742572 2616635 := bstep (se 1 (by rfl) ⟨1962476, by rfl⟩ : syracuseStep 2616635 = 3924953) B3924953
theorem B2616695 : Blo 1742572 2616695 := bstep (se 1 (by rfl) ⟨1962521, by rfl⟩ : syracuseStep 2616695 = 3925043) B3925043
theorem B2616719 : Blo 1742572 2616719 := bstep (se 1 (by rfl) ⟨1962539, by rfl⟩ : syracuseStep 2616719 = 3925079) B3925079
theorem B2616761 : Blo 1742572 2616761 := bstep (se 2 (by rfl) ⟨981285, by rfl⟩ : syracuseStep 2616761 = 1962571) B1962571
theorem B2616839 : Blo 1742572 2616839 := bstep (se 1 (by rfl) ⟨1962629, by rfl⟩ : syracuseStep 2616839 = 3925259) B3925259
theorem B4410895 : Blo 1742572 4410895 := bstep (se 1 (by rfl) ⟨3308171, by rfl⟩ : syracuseStep 4410895 = 6616343) B6616343
theorem B2207351 : Blo 1742572 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B8826569 : Blo 1742572 8826569 := bstep (se 2 (by rfl) ⟨3309963, by rfl⟩ : syracuseStep 8826569 = 6619927) B6619927
theorem B9932489 : Blo 1742572 9932489 := bstep (se 2 (by rfl) ⟨3724683, by rfl⟩ : syracuseStep 9932489 = 7449367) B7449367
theorem B1961743 : Blo 1742572 1961743 := bstep (se 1 (by rfl) ⟨1471307, by rfl⟩ : syracuseStep 1961743 = 2942615) B2942615
theorem B2207503 : Blo 1742572 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B4411169 : Blo 1742572 4411169 := bstep (se 2 (by rfl) ⟨1654188, by rfl⟩ : syracuseStep 4411169 = 3308377) B3308377
theorem B5885729 : Blo 1742572 5885729 := bstep (se 2 (by rfl) ⟨2207148, by rfl⟩ : syracuseStep 5885729 = 4414297) B4414297
theorem B37719857 : Blo 1742572 37719857 := bstep (se 2 (by rfl) ⟨14144946, by rfl⟩ : syracuseStep 37719857 = 28289893) B28289893
theorem B5967731 : Blo 1742572 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B4190087 : Blo 1742572 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B3723155 : Blo 1742572 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B16986019 : Blo 1742572 16986019 := bstep (se 1 (by rfl) ⟨12739514, by rfl⟩ : syracuseStep 16986019 = 25479029) B25479029
theorem B2207675 : Blo 1742572 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B8376331 : Blo 1742572 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B10752173 : Blo 1742572 10752173 := bstep (se 3 (by rfl) ⟨2016032, by rfl⟩ : syracuseStep 10752173 = 4032065) B4032065
theorem B1962247 : Blo 1742572 1962247 := bstep (se 1 (by rfl) ⟨1471685, by rfl⟩ : syracuseStep 1962247 = 2943371) B2943371
theorem B19853585 : Blo 1742572 19853585 := bstep (se 2 (by rfl) ⟨7445094, by rfl⟩ : syracuseStep 19853585 = 14890189) B14890189
theorem B4714811 : Blo 1742572 4714811 := bstep (se 1 (by rfl) ⟨3536108, by rfl⟩ : syracuseStep 4714811 = 7072217) B7072217
theorem B5304637 : Blo 1742572 5304637 := bstep (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) B1989239
theorem B5886323 : Blo 1742572 5886323 := bstep (se 1 (by rfl) ⟨4414742, by rfl⟩ : syracuseStep 5886323 = 8829485) B8829485
theorem B6623603 : Blo 1742572 6623603 := bstep (se 1 (by rfl) ⟨4967702, by rfl⟩ : syracuseStep 6623603 = 9935405) B9935405
theorem B10064263 : Blo 1742572 10064263 := bstep (se 1 (by rfl) ⟨7548197, by rfl⟩ : syracuseStep 10064263 = 15096395) B15096395
theorem B2355643 : Blo 1742572 2355643 := bstep (se 1 (by rfl) ⟨1766732, by rfl⟩ : syracuseStep 2355643 = 3533465) B3533465
theorem B1962427 : Blo 1742572 1962427 := bstep (se 1 (by rfl) ⟨1471820, by rfl⟩ : syracuseStep 1962427 = 2943641) B2943641
theorem B4248065 : Blo 1742572 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B206705195 : Blo 1742572 206705195 := bstep (se 1 (by rfl) ⟨155028896, by rfl⟩ : syracuseStep 206705195 = 310057793) B310057793
theorem B4715155 : Blo 1742572 4715155 := bstep (se 1 (by rfl) ⟨3536366, by rfl⟩ : syracuseStep 4715155 = 7072733) B7072733
theorem B5583617 : Blo 1742572 5583617 := bstep (se 2 (by rfl) ⟨2093856, by rfl⟩ : syracuseStep 5583617 = 4187713) B4187713
theorem B4412171 : Blo 1742572 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B31822627 : Blo 1742572 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B10064729 : Blo 1742572 10064729 := bstep (se 2 (by rfl) ⟨3774273, by rfl⟩ : syracuseStep 10064729 = 7548547) B7548547
theorem B11932505 : Blo 1742572 11932505 := bstep (se 2 (by rfl) ⟨4474689, by rfl⟩ : syracuseStep 11932505 = 8949379) B8949379
theorem B13415321 : Blo 1742572 13415321 := bstep (se 2 (by rfl) ⟨5030745, by rfl⟩ : syracuseStep 13415321 = 10061491) B10061491
theorem B33510307 : Blo 1742572 33510307 := bstep (se 1 (by rfl) ⟨25132730, by rfl⟩ : syracuseStep 33510307 = 50265461) B50265461
theorem B21197771 : Blo 1742572 21197771 := bstep (se 1 (by rfl) ⟨15898328, by rfl⟩ : syracuseStep 21197771 = 31796657) B31796657
theorem B3920939 : Blo 1742572 3920939 := bstep (se 1 (by rfl) ⟨2940704, by rfl⟩ : syracuseStep 3920939 = 5881409) B5881409
theorem B4715579 : Blo 1742572 4715579 := bstep (se 1 (by rfl) ⟨3536684, by rfl⟩ : syracuseStep 4715579 = 7073369) B7073369
theorem B9925699 : Blo 1742572 9925699 := bstep (se 1 (by rfl) ⟨7444274, by rfl⟩ : syracuseStep 9925699 = 14888549) B14888549
theorem B11171105 : Blo 1742572 11171105 := bstep (se 2 (by rfl) ⟨4189164, by rfl⟩ : syracuseStep 11171105 = 8378329) B8378329
theorem B2651449 : Blo 1742572 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B3921299 : Blo 1742572 3921299 := bstep (se 1 (by rfl) ⟨2940974, by rfl⟩ : syracuseStep 3921299 = 5881949) B5881949
theorem B4412819 : Blo 1742572 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B9934265 : Blo 1742572 9934265 := bstep (se 2 (by rfl) ⟨3725349, by rfl⟩ : syracuseStep 9934265 = 7450699) B7450699
theorem B3921353 : Blo 1742572 3921353 := bstep (se 2 (by rfl) ⟨1470507, by rfl⟩ : syracuseStep 3921353 = 2941015) B2941015
theorem B2356681 : Blo 1742572 2356681 := bstep (se 2 (by rfl) ⟨883755, by rfl⟩ : syracuseStep 2356681 = 1767511) B1767511
theorem B21198455 : Blo 1742572 21198455 := bstep (se 1 (by rfl) ⟨15898841, by rfl⟩ : syracuseStep 21198455 = 31797683) B31797683
theorem B1988231 : Blo 1742572 1988231 := bstep (se 1 (by rfl) ⟨1491173, by rfl⟩ : syracuseStep 1988231 = 2982347) B2982347
theorem B4413113 : Blo 1742572 4413113 := bstep (se 2 (by rfl) ⟨1654917, by rfl⟩ : syracuseStep 4413113 = 3309835) B3309835
theorem B2094779 : Blo 1742572 2094779 := bstep (se 1 (by rfl) ⟨1571084, by rfl⟩ : syracuseStep 2094779 = 3142169) B3142169
theorem B1742599 : Blo 1742572 1742599 := bstep (se 1 (by rfl) ⟨1306949, by rfl⟩ : syracuseStep 1742599 = 2613899) B2613899
theorem B1742607 : Blo 1742572 1742607 := bstep (se 1 (by rfl) ⟨1306955, by rfl⟩ : syracuseStep 1742607 = 2613911) B2613911
theorem B1742651 : Blo 1742572 1742651 := bstep (se 1 (by rfl) ⟨1306988, by rfl⟩ : syracuseStep 1742651 = 2613977) B2613977
theorem B1742727 : Blo 1742572 1742727 := bstep (se 1 (by rfl) ⟨1307045, by rfl⟩ : syracuseStep 1742727 = 2614091) B2614091
theorem B1742735 : Blo 1742572 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B1742779 : Blo 1742572 1742779 := bstep (se 1 (by rfl) ⟨1307084, by rfl⟩ : syracuseStep 1742779 = 2614169) B2614169
theorem B1742855 : Blo 1742572 1742855 := bstep (se 1 (by rfl) ⟨1307141, by rfl⟩ : syracuseStep 1742855 = 2614283) B2614283
theorem B14899211 : Blo 1742572 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B1742863 : Blo 1742572 1742863 := bstep (se 1 (by rfl) ⟨1307147, by rfl⟩ : syracuseStep 1742863 = 2614295) B2614295
theorem B21485591 : Blo 1742572 21485591 := bstep (se 1 (by rfl) ⟨16114193, by rfl⟩ : syracuseStep 21485591 = 32228387) B32228387
theorem B1742907 : Blo 1742572 1742907 := bstep (se 1 (by rfl) ⟨1307180, by rfl⟩ : syracuseStep 1742907 = 2614361) B2614361
theorem B16758845 : Blo 1742572 16758845 := bstep (se 3 (by rfl) ⟨3142283, by rfl⟩ : syracuseStep 16758845 = 6284567) B6284567
theorem B27203701 : Blo 1742572 27203701 := bstep (se 5 (by rfl) ⟨1275173, by rfl⟩ : syracuseStep 27203701 = 2550347) B2550347
theorem B1742983 : Blo 1742572 1742983 := bstep (se 1 (by rfl) ⟨1307237, by rfl⟩ : syracuseStep 1742983 = 2614475) B2614475
theorem B3922055 : Blo 1742572 3922055 := bstep (se 1 (by rfl) ⟨2941541, by rfl⟩ : syracuseStep 3922055 = 5883083) B5883083
theorem B1742991 : Blo 1742572 1742991 := bstep (se 1 (by rfl) ⟨1307243, by rfl⟩ : syracuseStep 1742991 = 2614487) B2614487
theorem B1743035 : Blo 1742572 1743035 := bstep (se 1 (by rfl) ⟨1307276, by rfl⟩ : syracuseStep 1743035 = 2614553) B2614553
theorem B7166189 : Blo 1742572 7166189 := bstep (se 3 (by rfl) ⟨1343660, by rfl⟩ : syracuseStep 7166189 = 2687321) B2687321
theorem B2095351 : Blo 1742572 2095351 := bstep (se 1 (by rfl) ⟨1571513, by rfl⟩ : syracuseStep 2095351 = 3143027) B3143027
theorem B1743111 : Blo 1742572 1743111 := bstep (se 1 (by rfl) ⟨1307333, by rfl⟩ : syracuseStep 1743111 = 2614667) B2614667
theorem B1743119 : Blo 1742572 1743119 := bstep (se 1 (by rfl) ⟨1307339, by rfl⟩ : syracuseStep 1743119 = 2614679) B2614679
theorem B1743163 : Blo 1742572 1743163 := bstep (se 1 (by rfl) ⟨1307372, by rfl⟩ : syracuseStep 1743163 = 2614745) B2614745
theorem B3922235 : Blo 1742572 3922235 := bstep (se 1 (by rfl) ⟨2941676, by rfl⟩ : syracuseStep 3922235 = 5883353) B5883353
theorem B4413811 : Blo 1742572 4413811 := bstep (se 1 (by rfl) ⟨3310358, by rfl⟩ : syracuseStep 4413811 = 6620717) B6620717
theorem B1743239 : Blo 1742572 1743239 := bstep (se 1 (by rfl) ⟨1307429, by rfl⟩ : syracuseStep 1743239 = 2614859) B2614859
theorem B1743247 : Blo 1742572 1743247 := bstep (se 1 (by rfl) ⟨1307435, by rfl⟩ : syracuseStep 1743247 = 2614871) B2614871
theorem B6617497 : Blo 1742572 6617497 := bstep (se 2 (by rfl) ⟨2481561, by rfl⟩ : syracuseStep 6617497 = 4963123) B4963123
theorem B3922361 : Blo 1742572 3922361 := bstep (se 2 (by rfl) ⟨1470885, by rfl⟩ : syracuseStep 3922361 = 2941771) B2941771
theorem B1743291 : Blo 1742572 1743291 := bstep (se 1 (by rfl) ⟨1307468, by rfl⟩ : syracuseStep 1743291 = 2614937) B2614937
theorem B4413953 : Blo 1742572 4413953 := bstep (se 2 (by rfl) ⟨1655232, by rfl⟩ : syracuseStep 4413953 = 3310465) B3310465
theorem B1743367 : Blo 1742572 1743367 := bstep (se 1 (by rfl) ⟨1307525, by rfl⟩ : syracuseStep 1743367 = 2615051) B2615051
theorem B1743375 : Blo 1742572 1743375 := bstep (se 1 (by rfl) ⟨1307531, by rfl⟩ : syracuseStep 1743375 = 2615063) B2615063
theorem B13244957 : Blo 1742572 13244957 := bstep (se 3 (by rfl) ⟨2483429, by rfl⟩ : syracuseStep 13244957 = 4966859) B4966859
theorem B1743419 : Blo 1742572 1743419 := bstep (se 1 (by rfl) ⟨1307564, by rfl⟩ : syracuseStep 1743419 = 2615129) B2615129
theorem B1743495 : Blo 1742572 1743495 := bstep (se 1 (by rfl) ⟨1307621, by rfl⟩ : syracuseStep 1743495 = 2615243) B2615243
theorem B1743503 : Blo 1742572 1743503 := bstep (se 1 (by rfl) ⟨1307627, by rfl⟩ : syracuseStep 1743503 = 2615255) B2615255
theorem B1743547 : Blo 1742572 1743547 := bstep (se 1 (by rfl) ⟨1307660, by rfl⟩ : syracuseStep 1743547 = 2615321) B2615321
theorem B6617801 : Blo 1742572 6617801 := bstep (se 2 (by rfl) ⟨2481675, by rfl⟩ : syracuseStep 6617801 = 4963351) B4963351
theorem B1743623 : Blo 1742572 1743623 := bstep (se 1 (by rfl) ⟨1307717, by rfl⟩ : syracuseStep 1743623 = 2615435) B2615435
theorem B3922703 : Blo 1742572 3922703 := bstep (se 1 (by rfl) ⟨2942027, by rfl⟩ : syracuseStep 3922703 = 5884055) B5884055
theorem B1743631 : Blo 1742572 1743631 := bstep (se 1 (by rfl) ⟨1307723, by rfl⟩ : syracuseStep 1743631 = 2615447) B2615447
theorem B3922721 : Blo 1742572 3922721 := bstep (se 2 (by rfl) ⟨1471020, by rfl⟩ : syracuseStep 3922721 = 2942041) B2942041
theorem B1743675 : Blo 1742572 1743675 := bstep (se 1 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 1743675 = 2615513) B2615513
theorem B1743751 : Blo 1742572 1743751 := bstep (se 1 (by rfl) ⟨1307813, by rfl⟩ : syracuseStep 1743751 = 2615627) B2615627
theorem B1743759 : Blo 1742572 1743759 := bstep (se 1 (by rfl) ⟨1307819, by rfl⟩ : syracuseStep 1743759 = 2615639) B2615639
theorem B5962681 : Blo 1742572 5962681 := bstep (se 2 (by rfl) ⟨2236005, by rfl⟩ : syracuseStep 5962681 = 4472011) B4472011
theorem B1743803 : Blo 1742572 1743803 := bstep (se 1 (by rfl) ⟨1307852, by rfl⟩ : syracuseStep 1743803 = 2615705) B2615705
theorem B4414409 : Blo 1742572 4414409 := bstep (se 2 (by rfl) ⟨1655403, by rfl⟩ : syracuseStep 4414409 = 3310807) B3310807
theorem B18856907 : Blo 1742572 18856907 := bstep (se 1 (by rfl) ⟨14142680, by rfl⟩ : syracuseStep 18856907 = 28285361) B28285361
theorem B6798289 : Blo 1742572 6798289 := bstep (se 2 (by rfl) ⟨2549358, by rfl⟩ : syracuseStep 6798289 = 5098717) B5098717
theorem B9927683 : Blo 1742572 9927683 := bstep (se 1 (by rfl) ⟨7445762, by rfl⟩ : syracuseStep 9927683 = 14891525) B14891525
theorem B1743879 : Blo 1742572 1743879 := bstep (se 1 (by rfl) ⟨1307909, by rfl⟩ : syracuseStep 1743879 = 2615819) B2615819
theorem B1743887 : Blo 1742572 1743887 := bstep (se 1 (by rfl) ⟨1307915, by rfl⟩ : syracuseStep 1743887 = 2615831) B2615831
theorem B1743931 : Blo 1742572 1743931 := bstep (se 1 (by rfl) ⟨1307948, by rfl⟩ : syracuseStep 1743931 = 2615897) B2615897
theorem B19856501 : Blo 1742572 19856501 := bstep (se 5 (by rfl) ⟨930773, by rfl⟩ : syracuseStep 19856501 = 1861547) B1861547
theorem B3923063 : Blo 1742572 3923063 := bstep (se 1 (by rfl) ⟨2942297, by rfl⟩ : syracuseStep 3923063 = 5884595) B5884595
theorem B1744007 : Blo 1742572 1744007 := bstep (se 1 (by rfl) ⟨1308005, by rfl⟩ : syracuseStep 1744007 = 2616011) B2616011
theorem B1744015 : Blo 1742572 1744015 := bstep (se 1 (by rfl) ⟨1308011, by rfl⟩ : syracuseStep 1744015 = 2616023) B2616023
theorem B1744059 : Blo 1742572 1744059 := bstep (se 1 (by rfl) ⟨1308044, by rfl⟩ : syracuseStep 1744059 = 2616089) B2616089
theorem B1744135 : Blo 1742572 1744135 := bstep (se 1 (by rfl) ⟨1308101, by rfl⟩ : syracuseStep 1744135 = 2616203) B2616203
theorem B1744143 : Blo 1742572 1744143 := bstep (se 1 (by rfl) ⟨1308107, by rfl⟩ : syracuseStep 1744143 = 2616215) B2616215
theorem B3923243 : Blo 1742572 3923243 := bstep (se 1 (by rfl) ⟨2942432, by rfl⟩ : syracuseStep 3923243 = 5884865) B5884865
theorem B4414763 : Blo 1742572 4414763 := bstep (se 1 (by rfl) ⟨3311072, by rfl⟩ : syracuseStep 4414763 = 6622145) B6622145
theorem B1744187 : Blo 1742572 1744187 := bstep (se 1 (by rfl) ⟨1308140, by rfl⟩ : syracuseStep 1744187 = 2616281) B2616281
theorem B11926919 : Blo 1742572 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B1744263 : Blo 1742572 1744263 := bstep (se 1 (by rfl) ⟨1308197, by rfl⟩ : syracuseStep 1744263 = 2616395) B2616395
theorem B1744271 : Blo 1742572 1744271 := bstep (se 1 (by rfl) ⟨1308203, by rfl⟩ : syracuseStep 1744271 = 2616407) B2616407
theorem B1744315 : Blo 1742572 1744315 := bstep (se 1 (by rfl) ⟨1308236, by rfl⟩ : syracuseStep 1744315 = 2616473) B2616473
theorem B60374477 : Blo 1742572 60374477 := bstep (se 3 (by rfl) ⟨11320214, by rfl⟩ : syracuseStep 60374477 = 22640429) B22640429
theorem B1744391 : Blo 1742572 1744391 := bstep (se 1 (by rfl) ⟨1308293, by rfl⟩ : syracuseStep 1744391 = 2616587) B2616587
theorem B5881355 : Blo 1742572 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B1744399 : Blo 1742572 1744399 := bstep (se 1 (by rfl) ⟨1308299, by rfl⟩ : syracuseStep 1744399 = 2616599) B2616599
theorem B1744443 : Blo 1742572 1744443 := bstep (se 1 (by rfl) ⟨1308332, by rfl⟩ : syracuseStep 1744443 = 2616665) B2616665
theorem B26525285 : Blo 1742572 26525285 := bstep (se 4 (by rfl) ⟨2486745, by rfl⟩ : syracuseStep 26525285 = 4973491) B4973491
theorem B5881463 : Blo 1742572 5881463 := bstep (se 1 (by rfl) ⟨4411097, by rfl⟩ : syracuseStep 5881463 = 8822195) B8822195
theorem B10600055 : Blo 1742572 10600055 := bstep (se 1 (by rfl) ⟨7950041, by rfl⟩ : syracuseStep 10600055 = 15900083) B15900083
theorem B6618743 : Blo 1742572 6618743 := bstep (se 1 (by rfl) ⟨4964057, by rfl⟩ : syracuseStep 6618743 = 9928115) B9928115
theorem B1744519 : Blo 1742572 1744519 := bstep (se 1 (by rfl) ⟨1308389, by rfl⟩ : syracuseStep 1744519 = 2616779) B2616779
theorem B1744527 : Blo 1742572 1744527 := bstep (se 1 (by rfl) ⟨1308395, by rfl⟩ : syracuseStep 1744527 = 2616791) B2616791
theorem B3923603 : Blo 1742572 3923603 := bstep (se 1 (by rfl) ⟨2942702, by rfl⟩ : syracuseStep 3923603 = 5885405) B5885405
theorem B2481835 : Blo 1742572 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B1744571 : Blo 1742572 1744571 := bstep (se 1 (by rfl) ⟨1308428, by rfl⟩ : syracuseStep 1744571 = 2616857) B2616857
theorem B2940617 : Blo 1742572 2940617 := bstep (se 2 (by rfl) ⟨1102731, by rfl⟩ : syracuseStep 2940617 = 2205463) B2205463
theorem B3923657 : Blo 1742572 3923657 := bstep (se 2 (by rfl) ⟨1471371, by rfl⟩ : syracuseStep 3923657 = 2942743) B2942743
theorem B67927853 : Blo 1742572 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B7069555 : Blo 1742572 7069555 := bstep (se 1 (by rfl) ⟨5302166, by rfl⟩ : syracuseStep 7069555 = 10604333) B10604333
theorem B45301655 : Blo 1742572 45301655 := bstep (se 1 (by rfl) ⟨33976241, by rfl⟩ : syracuseStep 45301655 = 67952483) B67952483
theorem B8822681 : Blo 1742572 8822681 := bstep (se 2 (by rfl) ⟨3308505, by rfl⟩ : syracuseStep 8822681 = 6617011) B6617011
theorem B7168115 : Blo 1742572 7168115 := bstep (se 1 (by rfl) ⟨5376086, by rfl⟩ : syracuseStep 7168115 = 10752173) B10752173
theorem B3924215 : Blo 1742572 3924215 := bstep (se 1 (by rfl) ⟨2943161, by rfl⟩ : syracuseStep 3924215 = 5886323) B5886323
theorem B4415735 : Blo 1742572 4415735 := bstep (se 1 (by rfl) ⟨3311801, by rfl⟩ : syracuseStep 4415735 = 6623603) B6623603
theorem B2941177 : Blo 1742572 2941177 := bstep (se 2 (by rfl) ⟨1102941, by rfl⟩ : syracuseStep 2941177 = 2205883) B2205883
theorem B33497549 : Blo 1742572 33497549 := bstep (se 3 (by rfl) ⟨6280790, by rfl⟩ : syracuseStep 33497549 = 12561581) B12561581
theorem B2941447 : Blo 1742572 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B13419017 : Blo 1742572 13419017 := bstep (se 2 (by rfl) ⟨5032131, by rfl⟩ : syracuseStep 13419017 = 10064263) B10064263
theorem B8823329 : Blo 1742572 8823329 := bstep (se 2 (by rfl) ⟨3308748, by rfl⟩ : syracuseStep 8823329 = 6617497) B6617497
theorem B8380961 : Blo 1742572 8380961 := bstep (se 2 (by rfl) ⟨3142860, by rfl⟩ : syracuseStep 8380961 = 6285721) B6285721
theorem B6709819 : Blo 1742572 6709819 := bstep (se 1 (by rfl) ⟨5032364, by rfl⟩ : syracuseStep 6709819 = 10064729) B10064729
theorem B7955003 : Blo 1742572 7955003 := bstep (se 1 (by rfl) ⟨5966252, by rfl⟩ : syracuseStep 7955003 = 11932505) B11932505
theorem B6619745 : Blo 1742572 6619745 := bstep (se 2 (by rfl) ⟨2482404, by rfl⟩ : syracuseStep 6619745 = 4964809) B4964809
theorem B14131847 : Blo 1742572 14131847 := bstep (se 1 (by rfl) ⟨10598885, by rfl⟩ : syracuseStep 14131847 = 21197771) B21197771
theorem B2613959 : Blo 1742572 2613959 := bstep (se 1 (by rfl) ⟨1960469, by rfl⟩ : syracuseStep 2613959 = 3920939) B3920939
theorem B5587667 : Blo 1742572 5587667 := bstep (se 1 (by rfl) ⟨4190750, by rfl⟩ : syracuseStep 5587667 = 8381501) B8381501
theorem B10601219 : Blo 1742572 10601219 := bstep (se 1 (by rfl) ⟨7950914, by rfl⟩ : syracuseStep 10601219 = 15901829) B15901829
theorem B3924809 : Blo 1742572 3924809 := bstep (se 2 (by rfl) ⟨1471803, by rfl⟩ : syracuseStep 3924809 = 2943607) B2943607
theorem B2614121 : Blo 1742572 2614121 := bstep (se 2 (by rfl) ⟨980295, by rfl⟩ : syracuseStep 2614121 = 1960591) B1960591
theorem B7447403 : Blo 1742572 7447403 := bstep (se 1 (by rfl) ⟨5585552, by rfl⟩ : syracuseStep 7447403 = 11171105) B11171105
theorem B2614199 : Blo 1742572 2614199 := bstep (se 1 (by rfl) ⟨1960649, by rfl⟩ : syracuseStep 2614199 = 3921299) B3921299
theorem B2941879 : Blo 1742572 2941879 := bstep (se 1 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 2941879 = 4412819) B4412819
theorem B2614235 : Blo 1742572 2614235 := bstep (se 1 (by rfl) ⟨1960676, by rfl⟩ : syracuseStep 2614235 = 3921353) B3921353
theorem B14132303 : Blo 1742572 14132303 := bstep (se 1 (by rfl) ⟨10599227, by rfl⟩ : syracuseStep 14132303 = 21198455) B21198455
theorem B2942075 : Blo 1742572 2942075 := bstep (se 1 (by rfl) ⟨2206556, by rfl⟩ : syracuseStep 2942075 = 4413113) B4413113
theorem B44680409 : Blo 1742572 44680409 := bstep (se 2 (by rfl) ⟨16755153, by rfl⟩ : syracuseStep 44680409 = 33510307) B33510307
theorem B11175205 : Blo 1742572 11175205 := bstep (se 4 (by rfl) ⟨1047675, by rfl⟩ : syracuseStep 11175205 = 2095351) B2095351
theorem B2483561 : Blo 1742572 2483561 := bstep (se 2 (by rfl) ⟨931335, by rfl⟩ : syracuseStep 2483561 = 1862671) B1862671
theorem B2614703 : Blo 1742572 2614703 := bstep (se 1 (by rfl) ⟨1961027, by rfl⟩ : syracuseStep 2614703 = 3922055) B3922055
theorem B3311111 : Blo 1742572 3311111 := bstep (se 1 (by rfl) ⟨2483333, by rfl⟩ : syracuseStep 3311111 = 4966667) B4966667
theorem B2614793 : Blo 1742572 2614793 := bstep (se 2 (by rfl) ⟨980547, by rfl⟩ : syracuseStep 2614793 = 1961095) B1961095
theorem B2942473 : Blo 1742572 2942473 := bstep (se 2 (by rfl) ⟨1103427, by rfl⟩ : syracuseStep 2942473 = 2206855) B2206855
theorem B2614823 : Blo 1742572 2614823 := bstep (se 1 (by rfl) ⟨1961117, by rfl⟩ : syracuseStep 2614823 = 3922235) B3922235
theorem B5883515 : Blo 1742572 5883515 := bstep (se 1 (by rfl) ⟨4412636, by rfl⟩ : syracuseStep 5883515 = 8825273) B8825273
theorem B2614907 : Blo 1742572 2614907 := bstep (se 1 (by rfl) ⟨1961180, by rfl⟩ : syracuseStep 2614907 = 3922361) B3922361
theorem B12568211 : Blo 1742572 12568211 := bstep (se 1 (by rfl) ⟨9426158, by rfl⟩ : syracuseStep 12568211 = 18852317) B18852317
theorem B2942635 : Blo 1742572 2942635 := bstep (se 1 (by rfl) ⟨2206976, by rfl⟩ : syracuseStep 2942635 = 4413953) B4413953
theorem B5301949 : Blo 1742572 5301949 := bstep (se 3 (by rfl) ⟨994115, by rfl⟩ : syracuseStep 5301949 = 1988231) B1988231
theorem B21202631 : Blo 1742572 21202631 := bstep (se 1 (by rfl) ⟨15901973, by rfl⟩ : syracuseStep 21202631 = 31803947) B31803947
theorem B2615033 : Blo 1742572 2615033 := bstep (se 2 (by rfl) ⟨980637, by rfl⟩ : syracuseStep 2615033 = 1961275) B1961275
theorem B5883677 : Blo 1742572 5883677 := bstep (se 3 (by rfl) ⟨1103189, by rfl⟩ : syracuseStep 5883677 = 2206379) B2206379
theorem B13240097 : Blo 1742572 13240097 := bstep (se 2 (by rfl) ⟨4965036, by rfl⟩ : syracuseStep 13240097 = 9930073) B9930073
theorem B2615135 : Blo 1742572 2615135 := bstep (se 1 (by rfl) ⟨1961351, by rfl⟩ : syracuseStep 2615135 = 3922703) B3922703
theorem B2615147 : Blo 1742572 2615147 := bstep (se 1 (by rfl) ⟨1961360, by rfl⟩ : syracuseStep 2615147 = 3922721) B3922721
theorem B3311543 : Blo 1742572 3311543 := bstep (se 1 (by rfl) ⟨2483657, by rfl⟩ : syracuseStep 3311543 = 4967315) B4967315
theorem B2942939 : Blo 1742572 2942939 := bstep (se 1 (by rfl) ⟨2207204, by rfl⟩ : syracuseStep 2942939 = 4414409) B4414409
theorem B6621203 : Blo 1742572 6621203 := bstep (se 1 (by rfl) ⟨4965902, by rfl⟩ : syracuseStep 6621203 = 9931805) B9931805
theorem B2615375 : Blo 1742572 2615375 := bstep (se 1 (by rfl) ⟨1961531, by rfl⟩ : syracuseStep 2615375 = 3923063) B3923063
theorem B3311695 : Blo 1742572 3311695 := bstep (se 1 (by rfl) ⟨2483771, by rfl⟩ : syracuseStep 3311695 = 4967543) B4967543
theorem B11167901 : Blo 1742572 11167901 := bstep (se 3 (by rfl) ⟨2093981, by rfl⟩ : syracuseStep 11167901 = 4187963) B4187963
theorem B2615495 : Blo 1742572 2615495 := bstep (se 1 (by rfl) ⟨1961621, by rfl⟩ : syracuseStep 2615495 = 3923243) B3923243
theorem B2943175 : Blo 1742572 2943175 := bstep (se 1 (by rfl) ⟨2207381, by rfl⟩ : syracuseStep 2943175 = 4414763) B4414763
theorem B40249651 : Blo 1742572 40249651 := bstep (se 1 (by rfl) ⟨30187238, by rfl⟩ : syracuseStep 40249651 = 60374477) B60374477
theorem B2615657 : Blo 1742572 2615657 := bstep (se 2 (by rfl) ⟨980871, by rfl⟩ : syracuseStep 2615657 = 1961743) B1961743
theorem B2943337 : Blo 1742572 2943337 := bstep (se 2 (by rfl) ⟨1103751, by rfl⟩ : syracuseStep 2943337 = 2207503) B2207503
theorem B2615735 : Blo 1742572 2615735 := bstep (se 1 (by rfl) ⟨1961801, by rfl⟩ : syracuseStep 2615735 = 3923603) B3923603
theorem B1960411 : Blo 1742572 1960411 := bstep (se 1 (by rfl) ⟨1470308, by rfl⟩ : syracuseStep 1960411 = 2940617) B2940617
theorem B5884379 : Blo 1742572 5884379 := bstep (se 1 (by rfl) ⟨4413284, by rfl⟩ : syracuseStep 5884379 = 8826569) B8826569
theorem B2615771 : Blo 1742572 2615771 := bstep (se 1 (by rfl) ⟨1961828, by rfl⟩ : syracuseStep 2615771 = 3923657) B3923657
theorem B6621659 : Blo 1742572 6621659 := bstep (se 1 (by rfl) ⟨4966244, by rfl⟩ : syracuseStep 6621659 = 9932489) B9932489
theorem B11168441 : Blo 1742572 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B1960879 : Blo 1742572 1960879 := bstep (se 1 (by rfl) ⟨1470659, by rfl⟩ : syracuseStep 1960879 = 2941319) B2941319
theorem B2616239 : Blo 1742572 2616239 := bstep (se 1 (by rfl) ⟨1962179, by rfl⟩ : syracuseStep 2616239 = 3924359) B3924359
theorem B2943931 : Blo 1742572 2943931 := bstep (se 1 (by rfl) ⟨2207948, by rfl⟩ : syracuseStep 2943931 = 4415897) B4415897
theorem B2616329 : Blo 1742572 2616329 := bstep (se 2 (by rfl) ⟨981123, by rfl⟩ : syracuseStep 2616329 = 1962247) B1962247
theorem B2206759 : Blo 1742572 2206759 := bstep (se 1 (by rfl) ⟨1655069, by rfl⟩ : syracuseStep 2206759 = 3310139) B3310139
theorem B2616359 : Blo 1742572 2616359 := bstep (se 1 (by rfl) ⟨1962269, by rfl⟩ : syracuseStep 2616359 = 3924539) B3924539
theorem B7072849 : Blo 1742572 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B2616443 : Blo 1742572 2616443 := bstep (se 1 (by rfl) ⟨1962332, by rfl⟩ : syracuseStep 2616443 = 3924665) B3924665
theorem B5885081 : Blo 1742572 5885081 := bstep (se 2 (by rfl) ⟨2206905, by rfl⟩ : syracuseStep 5885081 = 4413811) B4413811
theorem B3353771 : Blo 1742572 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B3722411 : Blo 1742572 3722411 := bstep (se 1 (by rfl) ⟨2791808, by rfl⟩ : syracuseStep 3722411 = 5583617) B5583617
theorem B3140857 : Blo 1742572 3140857 := bstep (se 2 (by rfl) ⟨1177821, by rfl⟩ : syracuseStep 3140857 = 2355643) B2355643
theorem B2616569 : Blo 1742572 2616569 := bstep (se 2 (by rfl) ⟨981213, by rfl⟩ : syracuseStep 2616569 = 1962427) B1962427
theorem B1961311 : Blo 1742572 1961311 := bstep (se 1 (by rfl) ⟨1470983, by rfl⟩ : syracuseStep 1961311 = 2941967) B2941967
theorem B2616671 : Blo 1742572 2616671 := bstep (se 1 (by rfl) ⟨1962503, by rfl⟩ : syracuseStep 2616671 = 3925007) B3925007
theorem B3976553 : Blo 1742572 3976553 := bstep (se 2 (by rfl) ⟨1491207, by rfl⟩ : syracuseStep 3976553 = 2982415) B2982415
theorem B2207083 : Blo 1742572 2207083 := bstep (se 1 (by rfl) ⟨1655312, by rfl⟩ : syracuseStep 2207083 = 3310625) B3310625
theorem B2616683 : Blo 1742572 2616683 := bstep (se 1 (by rfl) ⟨1962512, by rfl⟩ : syracuseStep 2616683 = 3925025) B3925025
theorem B4713947 : Blo 1742572 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B8826407 : Blo 1742572 8826407 := bstep (se 1 (by rfl) ⟨6619805, by rfl⟩ : syracuseStep 8826407 = 13239611) B13239611
theorem B6622843 : Blo 1742572 6622843 := bstep (se 1 (by rfl) ⟨4967132, by rfl⟩ : syracuseStep 6622843 = 9934265) B9934265
theorem B1961671 : Blo 1742572 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B4714195 : Blo 1742572 4714195 := bstep (se 1 (by rfl) ⟨3535646, by rfl⟩ : syracuseStep 4714195 = 7071293) B7071293
theorem B42430169 : Blo 1742572 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B7950241 : Blo 1742572 7950241 := bstep (se 2 (by rfl) ⟨2981340, by rfl⟩ : syracuseStep 7950241 = 5962681) B5962681
theorem B3141563 : Blo 1742572 3141563 := bstep (se 1 (by rfl) ⟨2356172, by rfl⟩ : syracuseStep 3141563 = 4712345) B4712345
theorem B9064385 : Blo 1742572 9064385 := bstep (se 2 (by rfl) ⟨3399144, by rfl⟩ : syracuseStep 9064385 = 6798289) B6798289
theorem B9932807 : Blo 1742572 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B14323727 : Blo 1742572 14323727 := bstep (se 1 (by rfl) ⟨10742795, by rfl⟩ : syracuseStep 14323727 = 21485591) B21485591
theorem B13234265 : Blo 1742572 13234265 := bstep (se 2 (by rfl) ⟨4962849, by rfl⟩ : syracuseStep 13234265 = 9925699) B9925699
theorem B5583001 : Blo 1742572 5583001 := bstep (se 2 (by rfl) ⟨2093625, by rfl⟩ : syracuseStep 5583001 = 4187251) B4187251
theorem B3272903 : Blo 1742572 3272903 := bstep (se 1 (by rfl) ⟨2454677, by rfl⟩ : syracuseStep 3272903 = 4909355) B4909355
theorem B5886269 : Blo 1742572 5886269 := bstep (se 3 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 5886269 = 2207351) B2207351
theorem B20132225 : Blo 1742572 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B3535265 : Blo 1742572 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B4411867 : Blo 1742572 4411867 := bstep (se 1 (by rfl) ⟨3308900, by rfl⟩ : syracuseStep 4411867 = 6617801) B6617801
theorem B1962535 : Blo 1742572 1962535 := bstep (se 1 (by rfl) ⟨1471901, by rfl⟩ : syracuseStep 1962535 = 2943803) B2943803
theorem B3142241 : Blo 1742572 3142241 := bstep (se 2 (by rfl) ⟨1178340, by rfl⟩ : syracuseStep 3142241 = 2356681) B2356681
theorem B12571271 : Blo 1742572 12571271 := bstep (se 1 (by rfl) ⟨9428453, by rfl⟩ : syracuseStep 12571271 = 18856907) B18856907
theorem B7951279 : Blo 1742572 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B3920903 : Blo 1742572 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B17683523 : Blo 1742572 17683523 := bstep (se 1 (by rfl) ⟨13262642, by rfl⟩ : syracuseStep 17683523 = 26525285) B26525285
theorem B3920975 : Blo 1742572 3920975 := bstep (se 1 (by rfl) ⟨2940731, by rfl⟩ : syracuseStep 3920975 = 5881463) B5881463
theorem B7066703 : Blo 1742572 7066703 := bstep (se 1 (by rfl) ⟨5300027, by rfl⟩ : syracuseStep 7066703 = 10600055) B10600055
theorem B4412495 : Blo 1742572 4412495 := bstep (se 1 (by rfl) ⟨3309371, by rfl⟩ : syracuseStep 4412495 = 6618743) B6618743
theorem B9426073 : Blo 1742572 9426073 := bstep (se 2 (by rfl) ⟨3534777, by rfl⟩ : syracuseStep 9426073 = 7069555) B7069555
theorem B5887133 : Blo 1742572 5887133 := bstep (se 3 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 5887133 = 2207675) B2207675
theorem B25146571 : Blo 1742572 25146571 := bstep (se 1 (by rfl) ⟨18859928, by rfl⟩ : syracuseStep 25146571 = 37719857) B37719857
theorem B22648025 : Blo 1742572 22648025 := bstep (se 2 (by rfl) ⟨8493009, by rfl⟩ : syracuseStep 22648025 = 16986019) B16986019
theorem B3978487 : Blo 1742572 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B30201103 : Blo 1742572 30201103 := bstep (se 1 (by rfl) ⟨22650827, by rfl⟩ : syracuseStep 30201103 = 45301655) B45301655
theorem B3921371 : Blo 1742572 3921371 := bstep (se 1 (by rfl) ⟨2941028, by rfl⟩ : syracuseStep 3921371 = 5882057) B5882057
theorem B36271601 : Blo 1742572 36271601 := bstep (se 2 (by rfl) ⟨13601850, by rfl⟩ : syracuseStep 36271601 = 27203701) B27203701
theorem B13235723 : Blo 1742572 13235723 := bstep (se 1 (by rfl) ⟨9926792, by rfl⟩ : syracuseStep 13235723 = 19853585) B19853585
theorem B3143207 : Blo 1742572 3143207 := bstep (se 1 (by rfl) ⟨2357405, by rfl⟩ : syracuseStep 3143207 = 4714811) B4714811
theorem B8828513 : Blo 1742572 8828513 := bstep (se 2 (by rfl) ⟨3310692, by rfl⟩ : syracuseStep 8828513 = 6621385) B6621385
theorem B5887673 : Blo 1742572 5887673 := bstep (se 2 (by rfl) ⟨2207877, by rfl⟩ : syracuseStep 5887673 = 4415755) B4415755
theorem B137803463 : Blo 1742572 137803463 := bstep (se 1 (by rfl) ⟨103352597, by rfl⟩ : syracuseStep 137803463 = 206705195) B206705195
theorem B7067351 : Blo 1742572 7067351 := bstep (se 1 (by rfl) ⟨5300513, by rfl⟩ : syracuseStep 7067351 = 10601027) B10601027
theorem B4413143 : Blo 1742572 4413143 := bstep (se 1 (by rfl) ⟨3309857, by rfl⟩ : syracuseStep 4413143 = 6619715) B6619715
theorem B14898937 : Blo 1742572 14898937 := bstep (se 2 (by rfl) ⟨5587101, by rfl⟩ : syracuseStep 14898937 = 11174203) B11174203
theorem B1742631 : Blo 1742572 1742631 := bstep (se 1 (by rfl) ⟨1306973, by rfl⟩ : syracuseStep 1742631 = 2613947) B2613947
theorem B1742671 : Blo 1742572 1742671 := bstep (se 1 (by rfl) ⟨1307003, by rfl⟩ : syracuseStep 1742671 = 2614007) B2614007
theorem B1742687 : Blo 1742572 1742687 := bstep (se 1 (by rfl) ⟨1307015, by rfl⟩ : syracuseStep 1742687 = 2614031) B2614031
theorem B1742715 : Blo 1742572 1742715 := bstep (se 1 (by rfl) ⟨1307036, by rfl⟩ : syracuseStep 1742715 = 2614073) B2614073
theorem B1742767 : Blo 1742572 1742767 := bstep (se 1 (by rfl) ⟨1307075, by rfl⟩ : syracuseStep 1742767 = 2614151) B2614151
theorem B3921839 : Blo 1742572 3921839 := bstep (se 1 (by rfl) ⟨2941379, by rfl⟩ : syracuseStep 3921839 = 5882759) B5882759
theorem B8943547 : Blo 1742572 8943547 := bstep (se 1 (by rfl) ⟨6707660, by rfl⟩ : syracuseStep 8943547 = 13415321) B13415321
theorem B1742791 : Blo 1742572 1742791 := bstep (se 1 (by rfl) ⟨1307093, by rfl⟩ : syracuseStep 1742791 = 2614187) B2614187
theorem B19109837 : Blo 1742572 19109837 := bstep (se 3 (by rfl) ⟨3583094, by rfl⟩ : syracuseStep 19109837 = 7166189) B7166189
theorem B1742811 : Blo 1742572 1742811 := bstep (se 1 (by rfl) ⟨1307108, by rfl⟩ : syracuseStep 1742811 = 2614217) B2614217
theorem B1742887 : Blo 1742572 1742887 := bstep (se 1 (by rfl) ⟨1307165, by rfl⟩ : syracuseStep 1742887 = 2614331) B2614331
theorem B3143719 : Blo 1742572 3143719 := bstep (se 1 (by rfl) ⟨2357789, by rfl⟩ : syracuseStep 3143719 = 4715579) B4715579
theorem B1742927 : Blo 1742572 1742927 := bstep (se 1 (by rfl) ⟨1307195, by rfl⟩ : syracuseStep 1742927 = 2614391) B2614391
theorem B1742943 : Blo 1742572 1742943 := bstep (se 1 (by rfl) ⟨1307207, by rfl⟩ : syracuseStep 1742943 = 2614415) B2614415
theorem B25147493 : Blo 1742572 25147493 := bstep (se 4 (by rfl) ⟨2357577, by rfl⟩ : syracuseStep 25147493 = 4715155) B4715155
theorem B1742971 : Blo 1742572 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B3922091 : Blo 1742572 3922091 := bstep (se 1 (by rfl) ⟨2941568, by rfl⟩ : syracuseStep 3922091 = 5883137) B5883137
theorem B1743023 : Blo 1742572 1743023 := bstep (se 1 (by rfl) ⟨1307267, by rfl⟩ : syracuseStep 1743023 = 2614535) B2614535
theorem B1743047 : Blo 1742572 1743047 := bstep (se 1 (by rfl) ⟨1307285, by rfl⟩ : syracuseStep 1743047 = 2614571) B2614571
theorem B1743067 : Blo 1742572 1743067 := bstep (se 1 (by rfl) ⟨1307300, by rfl⟩ : syracuseStep 1743067 = 2614601) B2614601
theorem B1743143 : Blo 1742572 1743143 := bstep (se 1 (by rfl) ⟨1307357, by rfl⟩ : syracuseStep 1743143 = 2614715) B2614715
theorem B1743183 : Blo 1742572 1743183 := bstep (se 1 (by rfl) ⟨1307387, by rfl⟩ : syracuseStep 1743183 = 2614775) B2614775
theorem B1743199 : Blo 1742572 1743199 := bstep (se 1 (by rfl) ⟨1307399, by rfl⟩ : syracuseStep 1743199 = 2614799) B2614799
theorem B1743227 : Blo 1742572 1743227 := bstep (se 1 (by rfl) ⟨1307420, by rfl⟩ : syracuseStep 1743227 = 2614841) B2614841
theorem B1743279 : Blo 1742572 1743279 := bstep (se 1 (by rfl) ⟨1307459, by rfl⟩ : syracuseStep 1743279 = 2614919) B2614919
theorem B1743303 : Blo 1742572 1743303 := bstep (se 1 (by rfl) ⟨1307477, by rfl⟩ : syracuseStep 1743303 = 2614955) B2614955
theorem B1743323 : Blo 1742572 1743323 := bstep (se 1 (by rfl) ⟨1307492, by rfl⟩ : syracuseStep 1743323 = 2614985) B2614985
theorem B1743399 : Blo 1742572 1743399 := bstep (se 1 (by rfl) ⟨1307549, by rfl⟩ : syracuseStep 1743399 = 2615099) B2615099
theorem B1743439 : Blo 1742572 1743439 := bstep (se 1 (by rfl) ⟨1307579, by rfl⟩ : syracuseStep 1743439 = 2615159) B2615159
theorem B1743455 : Blo 1742572 1743455 := bstep (se 1 (by rfl) ⟨1307591, by rfl⟩ : syracuseStep 1743455 = 2615183) B2615183
theorem B1743483 : Blo 1742572 1743483 := bstep (se 1 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 1743483 = 2615225) B2615225
theorem B11328173 : Blo 1742572 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B1743535 : Blo 1742572 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B3922631 : Blo 1742572 3922631 := bstep (se 1 (by rfl) ⟨2941973, by rfl⟩ : syracuseStep 3922631 = 5883947) B5883947
theorem B1743559 : Blo 1742572 1743559 := bstep (se 1 (by rfl) ⟨1307669, by rfl⟩ : syracuseStep 1743559 = 2615339) B2615339
theorem B11172563 : Blo 1742572 11172563 := bstep (se 1 (by rfl) ⟨8379422, by rfl⟩ : syracuseStep 11172563 = 16758845) B16758845
theorem B1743579 : Blo 1742572 1743579 := bstep (se 1 (by rfl) ⟨1307684, by rfl⟩ : syracuseStep 1743579 = 2615369) B2615369
theorem B1743655 : Blo 1742572 1743655 := bstep (se 1 (by rfl) ⟨1307741, by rfl⟩ : syracuseStep 1743655 = 2615483) B2615483
theorem B1743695 : Blo 1742572 1743695 := bstep (se 1 (by rfl) ⟨1307771, by rfl⟩ : syracuseStep 1743695 = 2615543) B2615543
theorem B1743711 : Blo 1742572 1743711 := bstep (se 1 (by rfl) ⟨1307783, by rfl⟩ : syracuseStep 1743711 = 2615567) B2615567
theorem B9935723 : Blo 1742572 9935723 := bstep (se 1 (by rfl) ⟨7451792, by rfl⟩ : syracuseStep 9935723 = 14903585) B14903585
theorem B1743739 : Blo 1742572 1743739 := bstep (se 1 (by rfl) ⟨1307804, by rfl⟩ : syracuseStep 1743739 = 2615609) B2615609
theorem B1743791 : Blo 1742572 1743791 := bstep (se 1 (by rfl) ⟨1307843, by rfl⟩ : syracuseStep 1743791 = 2615687) B2615687
theorem B5659579 : Blo 1742572 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B1743815 : Blo 1742572 1743815 := bstep (se 1 (by rfl) ⟨1307861, by rfl⟩ : syracuseStep 1743815 = 2615723) B2615723
theorem B1743835 : Blo 1742572 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B8829971 : Blo 1742572 8829971 := bstep (se 1 (by rfl) ⟨6622478, by rfl⟩ : syracuseStep 8829971 = 13244957) B13244957
theorem B22354967 : Blo 1742572 22354967 := bstep (se 1 (by rfl) ⟨16766225, by rfl⟩ : syracuseStep 22354967 = 33532451) B33532451
theorem B1743911 : Blo 1742572 1743911 := bstep (se 1 (by rfl) ⟨1307933, by rfl⟩ : syracuseStep 1743911 = 2615867) B2615867
theorem B1743951 : Blo 1742572 1743951 := bstep (se 1 (by rfl) ⟨1307963, by rfl⟩ : syracuseStep 1743951 = 2615927) B2615927
theorem B1743967 : Blo 1742572 1743967 := bstep (se 1 (by rfl) ⟨1307975, by rfl⟩ : syracuseStep 1743967 = 2615951) B2615951
theorem B1743995 : Blo 1742572 1743995 := bstep (se 1 (by rfl) ⟨1307996, by rfl⟩ : syracuseStep 1743995 = 2615993) B2615993
theorem B5586077 : Blo 1742572 5586077 := bstep (se 3 (by rfl) ⟨1047389, by rfl⟩ : syracuseStep 5586077 = 2094779) B2094779
theorem B1744047 : Blo 1742572 1744047 := bstep (se 1 (by rfl) ⟨1308035, by rfl⟩ : syracuseStep 1744047 = 2616071) B2616071
theorem B1744071 : Blo 1742572 1744071 := bstep (se 1 (by rfl) ⟨1308053, by rfl⟩ : syracuseStep 1744071 = 2616107) B2616107
theorem B1744091 : Blo 1742572 1744091 := bstep (se 1 (by rfl) ⟨1308068, by rfl⟩ : syracuseStep 1744091 = 2616137) B2616137
theorem B1744167 : Blo 1742572 1744167 := bstep (se 1 (by rfl) ⟨1308125, by rfl⟩ : syracuseStep 1744167 = 2616251) B2616251
theorem B1744207 : Blo 1742572 1744207 := bstep (se 1 (by rfl) ⟨1308155, by rfl⟩ : syracuseStep 1744207 = 2616311) B2616311
theorem B6618455 : Blo 1742572 6618455 := bstep (se 1 (by rfl) ⟨4963841, by rfl⟩ : syracuseStep 6618455 = 9927683) B9927683
theorem B1744223 : Blo 1742572 1744223 := bstep (se 1 (by rfl) ⟨1308167, by rfl⟩ : syracuseStep 1744223 = 2616335) B2616335
theorem B5881193 : Blo 1742572 5881193 := bstep (se 2 (by rfl) ⟨2205447, by rfl⟩ : syracuseStep 5881193 = 4410895) B4410895
theorem B1744251 : Blo 1742572 1744251 := bstep (se 1 (by rfl) ⟨1308188, by rfl⟩ : syracuseStep 1744251 = 2616377) B2616377
theorem B13237667 : Blo 1742572 13237667 := bstep (se 1 (by rfl) ⟨9928250, by rfl⟩ : syracuseStep 13237667 = 19856501) B19856501
theorem B1744303 : Blo 1742572 1744303 := bstep (se 1 (by rfl) ⟨1308227, by rfl⟩ : syracuseStep 1744303 = 2616455) B2616455
theorem B1744327 : Blo 1742572 1744327 := bstep (se 1 (by rfl) ⟨1308245, by rfl⟩ : syracuseStep 1744327 = 2616491) B2616491
theorem B181140941 : Blo 1742572 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1744347 : Blo 1742572 1744347 := bstep (se 1 (by rfl) ⟨1308260, by rfl⟩ : syracuseStep 1744347 = 2616521) B2616521
theorem B3923495 : Blo 1742572 3923495 := bstep (se 1 (by rfl) ⟨2942621, by rfl⟩ : syracuseStep 3923495 = 5885243) B5885243
theorem B1744423 : Blo 1742572 1744423 := bstep (se 1 (by rfl) ⟨1308317, by rfl⟩ : syracuseStep 1744423 = 2616635) B2616635
theorem B3309113 : Blo 1742572 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B1744463 : Blo 1742572 1744463 := bstep (se 1 (by rfl) ⟨1308347, by rfl⟩ : syracuseStep 1744463 = 2616695) B2616695
theorem B1744479 : Blo 1742572 1744479 := bstep (se 1 (by rfl) ⟨1308359, by rfl⟩ : syracuseStep 1744479 = 2616719) B2616719
theorem B1744507 : Blo 1742572 1744507 := bstep (se 1 (by rfl) ⟨1308380, by rfl⟩ : syracuseStep 1744507 = 2616761) B2616761
theorem B1744559 : Blo 1742572 1744559 := bstep (se 1 (by rfl) ⟨1308419, by rfl⟩ : syracuseStep 1744559 = 2616839) B2616839
theorem B11173565 : Blo 1742572 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B2940745 : Blo 1742572 2940745 := bstep (se 2 (by rfl) ⟨1102779, by rfl⟩ : syracuseStep 2940745 = 2205559) B2205559
theorem B2940779 : Blo 1742572 2940779 := bstep (se 1 (by rfl) ⟨2205584, by rfl⟩ : syracuseStep 2940779 = 4411169) B4411169
theorem B3923819 : Blo 1742572 3923819 := bstep (se 1 (by rfl) ⟨2942864, by rfl⟩ : syracuseStep 3923819 = 5885729) B5885729
theorem B3923873 : Blo 1742572 3923873 := bstep (se 2 (by rfl) ⟨1471452, by rfl⟩ : syracuseStep 3923873 = 2942905) B2942905
theorem B2482103 : Blo 1742572 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B5881787 : Blo 1742572 5881787 := bstep (se 1 (by rfl) ⟨4411340, by rfl⟩ : syracuseStep 5881787 = 8822681) B8822681
theorem B8822843 : Blo 1742572 8822843 := bstep (se 1 (by rfl) ⟨6617132, by rfl⟩ : syracuseStep 8822843 = 13234265) B13234265
theorem B4415593 : Blo 1742572 4415593 := bstep (se 2 (by rfl) ⟨1655847, by rfl⟩ : syracuseStep 4415593 = 3311695) B3311695
theorem B3924179 : Blo 1742572 3924179 := bstep (se 1 (by rfl) ⟨2943134, by rfl⟩ : syracuseStep 3924179 = 5886269) B5886269
theorem B3924233 : Blo 1742572 3924233 := bstep (se 2 (by rfl) ⟨1471587, by rfl⟩ : syracuseStep 3924233 = 2943175) B2943175
theorem B22331699 : Blo 1742572 22331699 := bstep (se 1 (by rfl) ⟨16748774, by rfl⟩ : syracuseStep 22331699 = 33497549) B33497549
theorem B8946011 : Blo 1742572 8946011 := bstep (se 1 (by rfl) ⟨6709508, by rfl⟩ : syracuseStep 8946011 = 13419017) B13419017
theorem B5882219 : Blo 1742572 5882219 := bstep (se 1 (by rfl) ⟨4411664, by rfl⟩ : syracuseStep 5882219 = 8823329) B8823329
theorem B5587307 : Blo 1742572 5587307 := bstep (se 1 (by rfl) ⟨4190480, by rfl⟩ : syracuseStep 5587307 = 8380961) B8380961
theorem B53666201 : Blo 1742572 53666201 := bstep (se 2 (by rfl) ⟨20124825, by rfl⟩ : syracuseStep 53666201 = 40249651) B40249651
theorem B9421231 : Blo 1742572 9421231 := bstep (se 1 (by rfl) ⟨7065923, by rfl⟩ : syracuseStep 9421231 = 14131847) B14131847
theorem B8380847 : Blo 1742572 8380847 := bstep (se 1 (by rfl) ⟨6285635, by rfl⟩ : syracuseStep 8380847 = 12571271) B12571271
theorem B3924449 : Blo 1742572 3924449 := bstep (se 2 (by rfl) ⟨1471668, by rfl⟩ : syracuseStep 3924449 = 2943337) B2943337
theorem B4964935 : Blo 1742572 4964935 := bstep (se 1 (by rfl) ⟨3723701, by rfl⟩ : syracuseStep 4964935 = 7447403) B7447403
theorem B2613881 : Blo 1742572 2613881 := bstep (se 2 (by rfl) ⟨980205, by rfl⟩ : syracuseStep 2613881 = 1960411) B1960411
theorem B5882489 : Blo 1742572 5882489 := bstep (se 2 (by rfl) ⟨2205933, by rfl⟩ : syracuseStep 5882489 = 4411867) B4411867
theorem B2613935 : Blo 1742572 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B11789015 : Blo 1742572 11789015 := bstep (se 1 (by rfl) ⟨8841761, by rfl⟩ : syracuseStep 11789015 = 17683523) B17683523
theorem B2613983 : Blo 1742572 2613983 := bstep (se 1 (by rfl) ⟨1960487, by rfl⟩ : syracuseStep 2613983 = 3920975) B3920975
theorem B9421535 : Blo 1742572 9421535 := bstep (se 1 (by rfl) ⟨7066151, by rfl⟩ : syracuseStep 9421535 = 14132303) B14132303
theorem B4711135 : Blo 1742572 4711135 := bstep (se 1 (by rfl) ⟨3533351, by rfl⟩ : syracuseStep 4711135 = 7066703) B7066703
theorem B2941663 : Blo 1742572 2941663 := bstep (se 1 (by rfl) ⟨2206247, by rfl⟩ : syracuseStep 2941663 = 4412495) B4412495
theorem B8946425 : Blo 1742572 8946425 := bstep (se 2 (by rfl) ⟨3354909, by rfl⟩ : syracuseStep 8946425 = 6709819) B6709819
theorem B3924755 : Blo 1742572 3924755 := bstep (se 1 (by rfl) ⟨2943566, by rfl⟩ : syracuseStep 3924755 = 5887133) B5887133
theorem B29786939 : Blo 1742572 29786939 := bstep (se 1 (by rfl) ⟨22340204, by rfl⟩ : syracuseStep 29786939 = 44680409) B44680409
theorem B15098683 : Blo 1742572 15098683 := bstep (se 1 (by rfl) ⟨11324012, by rfl⟩ : syracuseStep 15098683 = 22648025) B22648025
theorem B2614247 : Blo 1742572 2614247 := bstep (se 1 (by rfl) ⟨1960685, by rfl⟩ : syracuseStep 2614247 = 3921371) B3921371
theorem B8823815 : Blo 1742572 8823815 := bstep (se 1 (by rfl) ⟨6617861, by rfl⟩ : syracuseStep 8823815 = 13235723) B13235723
theorem B3925115 : Blo 1742572 3925115 := bstep (se 1 (by rfl) ⟨2943836, by rfl⟩ : syracuseStep 3925115 = 5887673) B5887673
theorem B2942095 : Blo 1742572 2942095 := bstep (se 1 (by rfl) ⟨2206571, by rfl⟩ : syracuseStep 2942095 = 4413143) B4413143
theorem B2614505 : Blo 1742572 2614505 := bstep (se 2 (by rfl) ⟨980439, by rfl⟩ : syracuseStep 2614505 = 1960879) B1960879
theorem B10601705 : Blo 1742572 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B7546105 : Blo 1742572 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B3925241 : Blo 1742572 3925241 := bstep (se 2 (by rfl) ⟨1471965, by rfl⟩ : syracuseStep 3925241 = 2943931) B2943931
theorem B2614559 : Blo 1742572 2614559 := bstep (se 1 (by rfl) ⟨1960919, by rfl⟩ : syracuseStep 2614559 = 3921839) B3921839
theorem B12739891 : Blo 1742572 12739891 := bstep (se 1 (by rfl) ⟨9554918, by rfl⟩ : syracuseStep 12739891 = 19109837) B19109837
theorem B2942345 : Blo 1742572 2942345 := bstep (se 2 (by rfl) ⟨1103379, by rfl⟩ : syracuseStep 2942345 = 2206759) B2206759
theorem B9430465 : Blo 1742572 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B2614727 : Blo 1742572 2614727 := bstep (se 1 (by rfl) ⟨1961045, by rfl⟩ : syracuseStep 2614727 = 3922091) B3922091
theorem B8824301 : Blo 1742572 8824301 := bstep (se 3 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 8824301 = 3309113) B3309113
theorem B12568097 : Blo 1742572 12568097 := bstep (se 2 (by rfl) ⟨4713036, by rfl⟩ : syracuseStep 12568097 = 9426073) B9426073
theorem B4187809 : Blo 1742572 4187809 := bstep (se 2 (by rfl) ⟨1570428, by rfl⟩ : syracuseStep 4187809 = 3140857) B3140857
theorem B2615081 : Blo 1742572 2615081 := bstep (se 2 (by rfl) ⟨980655, by rfl⟩ : syracuseStep 2615081 = 1961311) B1961311
theorem B2615087 : Blo 1742572 2615087 := bstep (se 1 (by rfl) ⟨1961315, by rfl⟩ : syracuseStep 2615087 = 3922631) B3922631
theorem B7448375 : Blo 1742572 7448375 := bstep (se 1 (by rfl) ⟨5586281, by rfl⟩ : syracuseStep 7448375 = 11172563) B11172563
theorem B2942777 : Blo 1742572 2942777 := bstep (se 2 (by rfl) ⟨1103541, by rfl⟩ : syracuseStep 2942777 = 2207083) B2207083
theorem B14903311 : Blo 1742572 14903311 := bstep (se 1 (by rfl) ⟨11177483, by rfl⟩ : syracuseStep 14903311 = 22354967) B22354967
theorem B2615561 : Blo 1742572 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B8825111 : Blo 1742572 8825111 := bstep (se 1 (by rfl) ⟨6618833, by rfl⟩ : syracuseStep 8825111 = 13237667) B13237667
theorem B6285593 : Blo 1742572 6285593 := bstep (se 2 (by rfl) ⟨2357097, by rfl⟩ : syracuseStep 6285593 = 4714195) B4714195
theorem B120760627 : Blo 1742572 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B5884271 : Blo 1742572 5884271 := bstep (se 1 (by rfl) ⟨4413203, by rfl⟩ : syracuseStep 5884271 = 8826407) B8826407
theorem B2615663 : Blo 1742572 2615663 := bstep (se 1 (by rfl) ⟨1961747, by rfl⟩ : syracuseStep 2615663 = 3923495) B3923495
theorem B7449043 : Blo 1742572 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B1960519 : Blo 1742572 1960519 := bstep (se 1 (by rfl) ⟨1470389, by rfl⟩ : syracuseStep 1960519 = 2940779) B2940779
theorem B2615879 : Blo 1742572 2615879 := bstep (se 1 (by rfl) ⟨1961909, by rfl⟩ : syracuseStep 2615879 = 3923819) B3923819
theorem B2615915 : Blo 1742572 2615915 := bstep (se 1 (by rfl) ⟨1961936, by rfl⟩ : syracuseStep 2615915 = 3923873) B3923873
theorem B6621871 : Blo 1742572 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B2181935 : Blo 1742572 2181935 := bstep (se 1 (by rfl) ⟨1636451, by rfl⟩ : syracuseStep 2181935 = 3272903) B3272903
theorem B2616143 : Blo 1742572 2616143 := bstep (se 1 (by rfl) ⟨1962107, by rfl⟩ : syracuseStep 2616143 = 3924215) B3924215
theorem B2943823 : Blo 1742572 2943823 := bstep (se 1 (by rfl) ⟨2207867, by rfl⟩ : syracuseStep 2943823 = 4415735) B4415735
theorem B13421483 : Blo 1742572 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B19114973 : Blo 1742572 19114973 := bstep (se 3 (by rfl) ⟨3584057, by rfl⟩ : syracuseStep 19114973 = 7168115) B7168115
theorem B5303335 : Blo 1742572 5303335 := bstep (se 1 (by rfl) ⟨3977501, by rfl⟩ : syracuseStep 5303335 = 7955003) B7955003
theorem B2616539 : Blo 1742572 2616539 := bstep (se 1 (by rfl) ⟨1962404, by rfl⟩ : syracuseStep 2616539 = 3924809) B3924809
theorem B2616713 : Blo 1742572 2616713 := bstep (se 2 (by rfl) ⟨981267, by rfl⟩ : syracuseStep 2616713 = 1962535) B1962535
theorem B1961383 : Blo 1742572 1961383 := bstep (se 1 (by rfl) ⟨1471037, by rfl⟩ : syracuseStep 1961383 = 2942075) B2942075
theorem B10604141 : Blo 1742572 10604141 := bstep (se 3 (by rfl) ⟨1988276, by rfl⟩ : syracuseStep 10604141 = 3976553) B3976553
theorem B6622829 : Blo 1742572 6622829 := bstep (se 3 (by rfl) ⟨1241780, by rfl⟩ : syracuseStep 6622829 = 2483561) B2483561
theorem B2207407 : Blo 1742572 2207407 := bstep (se 1 (by rfl) ⟨1655555, by rfl⟩ : syracuseStep 2207407 = 3311111) B3311111
theorem B5885675 : Blo 1742572 5885675 := bstep (se 1 (by rfl) ⟨4414256, by rfl⟩ : syracuseStep 5885675 = 8828513) B8828513
theorem B14135087 : Blo 1742572 14135087 := bstep (se 1 (by rfl) ⟨10601315, by rfl⟩ : syracuseStep 14135087 = 21202631) B21202631
theorem B91868975 : Blo 1742572 91868975 := bstep (se 1 (by rfl) ⟨68901731, by rfl⟩ : syracuseStep 91868975 = 137803463) B137803463
theorem B8826731 : Blo 1742572 8826731 := bstep (se 1 (by rfl) ⟨6620048, by rfl⟩ : syracuseStep 8826731 = 13240097) B13240097
theorem B1961959 : Blo 1742572 1961959 := bstep (se 1 (by rfl) ⟨1471469, by rfl⟩ : syracuseStep 1961959 = 2942939) B2942939
theorem B16764995 : Blo 1742572 16764995 := bstep (se 1 (by rfl) ⟨12573746, by rfl⟩ : syracuseStep 16764995 = 25147493) B25147493
theorem B5304649 : Blo 1742572 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B40268137 : Blo 1742572 40268137 := bstep (se 2 (by rfl) ⟨15100551, by rfl⟩ : syracuseStep 40268137 = 30201103) B30201103
theorem B18846269 : Blo 1742572 18846269 := bstep (se 3 (by rfl) ⟨3533675, by rfl⟩ : syracuseStep 18846269 = 7067351) B7067351
theorem B6623815 : Blo 1742572 6623815 := bstep (se 1 (by rfl) ⟨4967861, by rfl⟩ : syracuseStep 6623815 = 9935723) B9935723
theorem B5886647 : Blo 1742572 5886647 := bstep (se 1 (by rfl) ⟨4414985, by rfl⟩ : syracuseStep 5886647 = 8829971) B8829971
theorem B3724051 : Blo 1742572 3724051 := bstep (se 1 (by rfl) ⟨2793038, by rfl⟩ : syracuseStep 3724051 = 5586077) B5586077
theorem B4412303 : Blo 1742572 4412303 := bstep (se 1 (by rfl) ⟨3309227, by rfl⟩ : syracuseStep 4412303 = 6618455) B6618455
theorem B3920795 : Blo 1742572 3920795 := bstep (se 1 (by rfl) ⟨2940596, by rfl⟩ : syracuseStep 3920795 = 5881193) B5881193
theorem B3142631 : Blo 1742572 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B3920993 : Blo 1742572 3920993 := bstep (se 2 (by rfl) ⟨1470372, by rfl⟩ : syracuseStep 3920993 = 2940745) B2940745
theorem B8377501 : Blo 1742572 8377501 := bstep (se 3 (by rfl) ⟨1570781, by rfl⟩ : syracuseStep 8377501 = 3141563) B3141563
theorem B11924729 : Blo 1742572 11924729 := bstep (se 2 (by rfl) ⟨4471773, by rfl⟩ : syracuseStep 11924729 = 8943547) B8943547
theorem B3921191 : Blo 1742572 3921191 := bstep (se 1 (by rfl) ⟨2940893, by rfl⟩ : syracuseStep 3921191 = 5881787) B5881787
theorem B6042923 : Blo 1742572 6042923 := bstep (se 1 (by rfl) ⟨4532192, by rfl⟩ : syracuseStep 6042923 = 9064385) B9064385
theorem B38196605 : Blo 1742572 38196605 := bstep (se 3 (by rfl) ⟨7161863, by rfl⟩ : syracuseStep 38196605 = 14323727) B14323727
theorem B4191625 : Blo 1742572 4191625 := bstep (se 2 (by rfl) ⟨1571859, by rfl⟩ : syracuseStep 4191625 = 3143719) B3143719
theorem B7444001 : Blo 1742572 7444001 := bstep (se 2 (by rfl) ⟨2791500, by rfl⟩ : syracuseStep 7444001 = 5583001) B5583001
theorem B3921569 : Blo 1742572 3921569 := bstep (se 2 (by rfl) ⟨1470588, by rfl⟩ : syracuseStep 3921569 = 2941177) B2941177
theorem B4413163 : Blo 1742572 4413163 := bstep (se 1 (by rfl) ⟨3309872, by rfl⟩ : syracuseStep 4413163 = 6619745) B6619745
theorem B2094827 : Blo 1742572 2094827 := bstep (se 1 (by rfl) ⟨1571120, by rfl⟩ : syracuseStep 2094827 = 3142241) B3142241
theorem B1742639 : Blo 1742572 1742639 := bstep (se 1 (by rfl) ⟨1306979, by rfl⟩ : syracuseStep 1742639 = 2613959) B2613959
theorem B3725111 : Blo 1742572 3725111 := bstep (se 1 (by rfl) ⟨2793833, by rfl⟩ : syracuseStep 3725111 = 5587667) B5587667
theorem B7067479 : Blo 1742572 7067479 := bstep (se 1 (by rfl) ⟨5300609, by rfl⟩ : syracuseStep 7067479 = 10601219) B10601219
theorem B1742747 : Blo 1742572 1742747 := bstep (se 1 (by rfl) ⟨1307060, by rfl⟩ : syracuseStep 1742747 = 2614121) B2614121
theorem B1742799 : Blo 1742572 1742799 := bstep (se 1 (by rfl) ⟨1307099, by rfl⟩ : syracuseStep 1742799 = 2614199) B2614199
theorem B1742823 : Blo 1742572 1742823 := bstep (se 1 (by rfl) ⟨1307117, by rfl⟩ : syracuseStep 1742823 = 2614235) B2614235
theorem B3921929 : Blo 1742572 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B1743135 : Blo 1742572 1743135 := bstep (se 1 (by rfl) ⟨1307351, by rfl⟩ : syracuseStep 1743135 = 2614703) B2614703
theorem B24181067 : Blo 1742572 24181067 := bstep (se 1 (by rfl) ⟨18135800, by rfl⟩ : syracuseStep 24181067 = 36271601) B36271601
theorem B1743195 : Blo 1742572 1743195 := bstep (se 1 (by rfl) ⟨1307396, by rfl⟩ : syracuseStep 1743195 = 2614793) B2614793
theorem B1743215 : Blo 1742572 1743215 := bstep (se 1 (by rfl) ⟨1307411, by rfl⟩ : syracuseStep 1743215 = 2614823) B2614823
theorem B2095471 : Blo 1742572 2095471 := bstep (se 1 (by rfl) ⟨1571603, by rfl⟩ : syracuseStep 2095471 = 3143207) B3143207
theorem B3922343 : Blo 1742572 3922343 := bstep (se 1 (by rfl) ⟨2941757, by rfl⟩ : syracuseStep 3922343 = 5883515) B5883515
theorem B1743271 : Blo 1742572 1743271 := bstep (se 1 (by rfl) ⟨1307453, by rfl⟩ : syracuseStep 1743271 = 2614907) B2614907
theorem B9427373 : Blo 1742572 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B8378807 : Blo 1742572 8378807 := bstep (se 1 (by rfl) ⟨6284105, by rfl⟩ : syracuseStep 8378807 = 12568211) B12568211
theorem B1743355 : Blo 1742572 1743355 := bstep (se 1 (by rfl) ⟨1307516, by rfl⟩ : syracuseStep 1743355 = 2615033) B2615033
theorem B3922451 : Blo 1742572 3922451 := bstep (se 1 (by rfl) ⟨2941838, by rfl⟩ : syracuseStep 3922451 = 5883677) B5883677
theorem B1743423 : Blo 1742572 1743423 := bstep (se 1 (by rfl) ⟨1307567, by rfl⟩ : syracuseStep 1743423 = 2615135) B2615135
theorem B1743431 : Blo 1742572 1743431 := bstep (se 1 (by rfl) ⟨1307573, by rfl⟩ : syracuseStep 1743431 = 2615147) B2615147
theorem B3922505 : Blo 1742572 3922505 := bstep (se 2 (by rfl) ⟨1470939, by rfl⟩ : syracuseStep 3922505 = 2941879) B2941879
theorem B4414135 : Blo 1742572 4414135 := bstep (se 1 (by rfl) ⟨3310601, by rfl⟩ : syracuseStep 4414135 = 6621203) B6621203
theorem B1743583 : Blo 1742572 1743583 := bstep (se 1 (by rfl) ⟨1307687, by rfl⟩ : syracuseStep 1743583 = 2615375) B2615375
theorem B7445267 : Blo 1742572 7445267 := bstep (se 1 (by rfl) ⟨5583950, by rfl⟩ : syracuseStep 7445267 = 11167901) B11167901
theorem B1743663 : Blo 1742572 1743663 := bstep (se 1 (by rfl) ⟨1307747, by rfl⟩ : syracuseStep 1743663 = 2615495) B2615495
theorem B1743771 : Blo 1742572 1743771 := bstep (se 1 (by rfl) ⟨1307828, by rfl⟩ : syracuseStep 1743771 = 2615657) B2615657
theorem B33528761 : Blo 1742572 33528761 := bstep (se 2 (by rfl) ⟨12573285, by rfl⟩ : syracuseStep 33528761 = 25146571) B25146571
theorem B1743823 : Blo 1742572 1743823 := bstep (se 1 (by rfl) ⟨1307867, by rfl⟩ : syracuseStep 1743823 = 2615735) B2615735
theorem B3922919 : Blo 1742572 3922919 := bstep (se 1 (by rfl) ⟨2942189, by rfl⟩ : syracuseStep 3922919 = 5884379) B5884379
theorem B1743847 : Blo 1742572 1743847 := bstep (se 1 (by rfl) ⟨1307885, by rfl⟩ : syracuseStep 1743847 = 2615771) B2615771
theorem B4414439 : Blo 1742572 4414439 := bstep (se 1 (by rfl) ⟨3310829, by rfl⟩ : syracuseStep 4414439 = 6621659) B6621659
theorem B14900273 : Blo 1742572 14900273 := bstep (se 2 (by rfl) ⟨5587602, by rfl⟩ : syracuseStep 14900273 = 11175205) B11175205
theorem B7552115 : Blo 1742572 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B7445627 : Blo 1742572 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B1744159 : Blo 1742572 1744159 := bstep (se 1 (by rfl) ⟨1308119, by rfl⟩ : syracuseStep 1744159 = 2616239) B2616239
theorem B1744219 : Blo 1742572 1744219 := bstep (se 1 (by rfl) ⟨1308164, by rfl⟩ : syracuseStep 1744219 = 2616329) B2616329
theorem B3923297 : Blo 1742572 3923297 := bstep (se 2 (by rfl) ⟨1471236, by rfl⟩ : syracuseStep 3923297 = 2942473) B2942473
theorem B1744239 : Blo 1742572 1744239 := bstep (se 1 (by rfl) ⟨1308179, by rfl⟩ : syracuseStep 1744239 = 2616359) B2616359
theorem B1744295 : Blo 1742572 1744295 := bstep (se 1 (by rfl) ⟨1308221, by rfl⟩ : syracuseStep 1744295 = 2616443) B2616443
theorem B3923387 : Blo 1742572 3923387 := bstep (se 1 (by rfl) ⟨2942540, by rfl⟩ : syracuseStep 3923387 = 5885081) B5885081
theorem B2235847 : Blo 1742572 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B2481607 : Blo 1742572 2481607 := bstep (se 1 (by rfl) ⟨1861205, by rfl⟩ : syracuseStep 2481607 = 3722411) B3722411
theorem B8830457 : Blo 1742572 8830457 := bstep (se 2 (by rfl) ⟨3311421, by rfl⟩ : syracuseStep 8830457 = 6622843) B6622843
theorem B1744379 : Blo 1742572 1744379 := bstep (se 1 (by rfl) ⟨1308284, by rfl⟩ : syracuseStep 1744379 = 2616569) B2616569
theorem B3923513 : Blo 1742572 3923513 := bstep (se 2 (by rfl) ⟨1471317, by rfl⟩ : syracuseStep 3923513 = 2942635) B2942635
theorem B1744447 : Blo 1742572 1744447 := bstep (se 1 (by rfl) ⟨1308335, by rfl⟩ : syracuseStep 1744447 = 2616671) B2616671
theorem B1744455 : Blo 1742572 1744455 := bstep (se 1 (by rfl) ⟨1308341, by rfl⟩ : syracuseStep 1744455 = 2616683) B2616683
theorem B7069265 : Blo 1742572 7069265 := bstep (se 2 (by rfl) ⟨2650974, by rfl⟩ : syracuseStep 7069265 = 5301949) B5301949
theorem B19865249 : Blo 1742572 19865249 := bstep (se 2 (by rfl) ⟨7449468, by rfl⟩ : syracuseStep 19865249 = 14898937) B14898937
theorem B28286779 : Blo 1742572 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B6618941 : Blo 1742572 6618941 := bstep (se 3 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 6618941 = 2482103) B2482103
theorem B8830781 : Blo 1742572 8830781 := bstep (se 3 (by rfl) ⟨1655771, by rfl⟩ : syracuseStep 8830781 = 3311543) B3311543
theorem B10600321 : Blo 1742572 10600321 := bstep (se 2 (by rfl) ⟨3975120, by rfl⟩ : syracuseStep 10600321 = 7950241) B7950241
theorem B5881895 : Blo 1742572 5881895 := bstep (se 1 (by rfl) ⟨4411421, by rfl⟩ : syracuseStep 5881895 = 8822843) B8822843
theorem B5587231 : Blo 1742572 5587231 := bstep (se 1 (by rfl) ⟨4190423, by rfl⟩ : syracuseStep 5587231 = 8380847) B8380847
theorem B161014169 : Blo 1742572 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B3924431 : Blo 1742572 3924431 := bstep (se 1 (by rfl) ⟨2943323, by rfl⟩ : syracuseStep 3924431 = 5886647) B5886647
theorem B53690849 : Blo 1742572 53690849 := bstep (se 2 (by rfl) ⟨20134068, by rfl⟩ : syracuseStep 53690849 = 40268137) B40268137
theorem B2793961 : Blo 1742572 2793961 := bstep (se 2 (by rfl) ⟨1047735, by rfl⟩ : syracuseStep 2793961 = 2095471) B2095471
theorem B5964283 : Blo 1742572 5964283 := bstep (se 1 (by rfl) ⟨4473212, by rfl⟩ : syracuseStep 5964283 = 8946425) B8946425
theorem B19857959 : Blo 1742572 19857959 := bstep (se 1 (by rfl) ⟨14893469, by rfl⟩ : syracuseStep 19857959 = 29786939) B29786939
theorem B2941535 : Blo 1742572 2941535 := bstep (se 1 (by rfl) ⟨2206151, by rfl⟩ : syracuseStep 2941535 = 4412303) B4412303
theorem B2613863 : Blo 1742572 2613863 := bstep (se 1 (by rfl) ⟨1960397, by rfl⟩ : syracuseStep 2613863 = 3920795) B3920795
theorem B28271213 : Blo 1742572 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B5882543 : Blo 1742572 5882543 := bstep (se 1 (by rfl) ⟨4411907, by rfl⟩ : syracuseStep 5882543 = 8823815) B8823815
theorem B2613995 : Blo 1742572 2613995 := bstep (se 1 (by rfl) ⟨1960496, by rfl⟩ : syracuseStep 2613995 = 3920993) B3920993
theorem B2614025 : Blo 1742572 2614025 := bstep (se 2 (by rfl) ⟨980259, by rfl⟩ : syracuseStep 2614025 = 1960519) B1960519
theorem B6619913 : Blo 1742572 6619913 := bstep (se 2 (by rfl) ⟨2482467, by rfl⟩ : syracuseStep 6619913 = 4964935) B4964935
theorem B8831753 : Blo 1742572 8831753 := bstep (se 2 (by rfl) ⟨3311907, by rfl⟩ : syracuseStep 8831753 = 6623815) B6623815
theorem B2614127 : Blo 1742572 2614127 := bstep (se 1 (by rfl) ⟨1960595, by rfl⟩ : syracuseStep 2614127 = 3921191) B3921191
theorem B23856029 : Blo 1742572 23856029 := bstep (se 3 (by rfl) ⟨4473005, by rfl⟩ : syracuseStep 23856029 = 8946011) B8946011
theorem B5882867 : Blo 1742572 5882867 := bstep (se 1 (by rfl) ⟨4412150, by rfl⟩ : syracuseStep 5882867 = 8824301) B8824301
theorem B4965401 : Blo 1742572 4965401 := bstep (se 2 (by rfl) ⟨1862025, by rfl⟩ : syracuseStep 4965401 = 3724051) B3724051
theorem B3925097 : Blo 1742572 3925097 := bstep (se 2 (by rfl) ⟨1471911, by rfl⟩ : syracuseStep 3925097 = 2943823) B2943823
theorem B2614379 : Blo 1742572 2614379 := bstep (se 1 (by rfl) ⟨1960784, by rfl⟩ : syracuseStep 2614379 = 3921569) B3921569
theorem B2483407 : Blo 1742572 2483407 := bstep (se 1 (by rfl) ⟨1862555, by rfl⟩ : syracuseStep 2483407 = 3725111) B3725111
theorem B2614619 : Blo 1742572 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B7071113 : Blo 1742572 7071113 := bstep (se 2 (by rfl) ⟨2651667, by rfl⟩ : syracuseStep 7071113 = 5303335) B5303335
theorem B19850669 : Blo 1742572 19850669 := bstep (se 3 (by rfl) ⟨3722000, by rfl⟩ : syracuseStep 19850669 = 7444001) B7444001
theorem B5883407 : Blo 1742572 5883407 := bstep (se 1 (by rfl) ⟨4412555, by rfl⟩ : syracuseStep 5883407 = 8825111) B8825111
theorem B2614895 : Blo 1742572 2614895 := bstep (se 1 (by rfl) ⟨1961171, by rfl⟩ : syracuseStep 2614895 = 3922343) B3922343
theorem B6284915 : Blo 1742572 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B2614967 : Blo 1742572 2614967 := bstep (se 1 (by rfl) ⟨1961225, by rfl⟩ : syracuseStep 2614967 = 3922451) B3922451
theorem B2615003 : Blo 1742572 2615003 := bstep (se 1 (by rfl) ⟨1961252, by rfl⟩ : syracuseStep 2615003 = 3922505) B3922505
theorem B5588833 : Blo 1742572 5588833 := bstep (se 2 (by rfl) ⟨2095812, by rfl⟩ : syracuseStep 5588833 = 4191625) B4191625
theorem B2615177 : Blo 1742572 2615177 := bstep (se 2 (by rfl) ⟨980691, by rfl⟩ : syracuseStep 2615177 = 1961383) B1961383
theorem B8947655 : Blo 1742572 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B2615279 : Blo 1742572 2615279 := bstep (se 1 (by rfl) ⟨1961459, by rfl⟩ : syracuseStep 2615279 = 3922919) B3922919
theorem B2942959 : Blo 1742572 2942959 := bstep (se 1 (by rfl) ⟨2207219, by rfl⟩ : syracuseStep 2942959 = 4414439) B4414439
theorem B5818493 : Blo 1742572 5818493 := bstep (se 3 (by rfl) ⟨1090967, by rfl⟩ : syracuseStep 5818493 = 2181935) B2181935
theorem B2943209 : Blo 1742572 2943209 := bstep (se 2 (by rfl) ⟨1103703, by rfl⟩ : syracuseStep 2943209 = 2207407) B2207407
theorem B2615531 : Blo 1742572 2615531 := bstep (se 1 (by rfl) ⟨1961648, by rfl⟩ : syracuseStep 2615531 = 3923297) B3923297
theorem B125749493 : Blo 1742572 125749493 := bstep (se 5 (by rfl) ⟨5894507, by rfl⟩ : syracuseStep 125749493 = 11789015) B11789015
theorem B2615591 : Blo 1742572 2615591 := bstep (se 1 (by rfl) ⟨1961693, by rfl⟩ : syracuseStep 2615591 = 3923387) B3923387
theorem B5884217 : Blo 1742572 5884217 := bstep (se 2 (by rfl) ⟨2206581, by rfl⟩ : syracuseStep 5884217 = 4413163) B4413163
theorem B2615675 : Blo 1742572 2615675 := bstep (se 1 (by rfl) ⟨1961756, by rfl⟩ : syracuseStep 2615675 = 3923513) B3923513
theorem B4712843 : Blo 1742572 4712843 := bstep (se 1 (by rfl) ⟨3534632, by rfl⟩ : syracuseStep 4712843 = 7069265) B7069265
theorem B9423305 : Blo 1742572 9423305 := bstep (se 2 (by rfl) ⟨3533739, by rfl⟩ : syracuseStep 9423305 = 7067479) B7067479
theorem B14133761 : Blo 1742572 14133761 := bstep (se 2 (by rfl) ⟨5300160, by rfl⟩ : syracuseStep 14133761 = 10600321) B10600321
theorem B9423391 : Blo 1742572 9423391 := bstep (se 1 (by rfl) ⟨7067543, by rfl⟩ : syracuseStep 9423391 = 14135087) B14135087
theorem B61245983 : Blo 1742572 61245983 := bstep (se 1 (by rfl) ⟨45934487, by rfl⟩ : syracuseStep 61245983 = 91868975) B91868975
theorem B5884487 : Blo 1742572 5884487 := bstep (se 1 (by rfl) ⟨4413365, by rfl⟩ : syracuseStep 5884487 = 8826731) B8826731
theorem B2615945 : Blo 1742572 2615945 := bstep (se 2 (by rfl) ⟨980979, by rfl⟩ : syracuseStep 2615945 = 1961959) B1961959
theorem B2616119 : Blo 1742572 2616119 := bstep (se 1 (by rfl) ⟨1962089, by rfl⟩ : syracuseStep 2616119 = 3924179) B3924179
theorem B2616155 : Blo 1742572 2616155 := bstep (se 1 (by rfl) ⟨1962116, by rfl⟩ : syracuseStep 2616155 = 3924233) B3924233
theorem B44706653 : Blo 1742572 44706653 := bstep (se 3 (by rfl) ⟨8382497, by rfl⟩ : syracuseStep 44706653 = 16764995) B16764995
theorem B14887799 : Blo 1742572 14887799 := bstep (se 1 (by rfl) ⟨11165849, by rfl⟩ : syracuseStep 14887799 = 22331699) B22331699
theorem B35777467 : Blo 1742572 35777467 := bstep (se 1 (by rfl) ⟨26833100, by rfl⟩ : syracuseStep 35777467 = 53666201) B53666201
theorem B2616299 : Blo 1742572 2616299 := bstep (se 1 (by rfl) ⟨1962224, by rfl⟩ : syracuseStep 2616299 = 3924449) B3924449
theorem B7072865 : Blo 1742572 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B2616503 : Blo 1742572 2616503 := bstep (se 1 (by rfl) ⟨1962377, by rfl⟩ : syracuseStep 2616503 = 3924755) B3924755
theorem B12561641 : Blo 1742572 12561641 := bstep (se 2 (by rfl) ⟨4710615, by rfl⟩ : syracuseStep 12561641 = 9421231) B9421231
theorem B9932057 : Blo 1742572 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B2616743 : Blo 1742572 2616743 := bstep (se 1 (by rfl) ⟨1962557, by rfl⟩ : syracuseStep 2616743 = 3925115) B3925115
theorem B7949819 : Blo 1742572 7949819 := bstep (se 1 (by rfl) ⟨5962364, by rfl⟩ : syracuseStep 7949819 = 11924729) B11924729
theorem B2616827 : Blo 1742572 2616827 := bstep (se 1 (by rfl) ⟨1962620, by rfl⟩ : syracuseStep 2616827 = 3925241) B3925241
theorem B5885513 : Blo 1742572 5885513 := bstep (se 2 (by rfl) ⟨2207067, by rfl⟩ : syracuseStep 5885513 = 4414135) B4414135
theorem B25464403 : Blo 1742572 25464403 := bstep (se 1 (by rfl) ⟨19098302, by rfl⟩ : syracuseStep 25464403 = 38196605) B38196605
theorem B1961563 : Blo 1742572 1961563 := bstep (se 1 (by rfl) ⟨1471172, by rfl⟩ : syracuseStep 1961563 = 2942345) B2942345
theorem B20131577 : Blo 1742572 20131577 := bstep (se 2 (by rfl) ⟨7549341, by rfl⟩ : syracuseStep 20131577 = 15098683) B15098683
theorem B22343485 : Blo 1742572 22343485 := bstep (se 3 (by rfl) ⟨4189403, by rfl⟩ : syracuseStep 22343485 = 8378807) B8378807
theorem B1961851 : Blo 1742572 1961851 := bstep (se 1 (by rfl) ⟨1471388, by rfl⟩ : syracuseStep 1961851 = 2942777) B2942777
theorem B4190395 : Blo 1742572 4190395 := bstep (se 1 (by rfl) ⟨3142796, by rfl⟩ : syracuseStep 4190395 = 6285593) B6285593
theorem B11170001 : Blo 1742572 11170001 := bstep (se 2 (by rfl) ⟨4188750, by rfl⟩ : syracuseStep 11170001 = 8377501) B8377501
theorem B16986521 : Blo 1742572 16986521 := bstep (se 2 (by rfl) ⟨6369945, by rfl⟩ : syracuseStep 16986521 = 12739891) B12739891
theorem B22352507 : Blo 1742572 22352507 := bstep (se 1 (by rfl) ⟨16764380, by rfl⟩ : syracuseStep 22352507 = 33528761) B33528761
theorem B12743315 : Blo 1742572 12743315 := bstep (se 1 (by rfl) ⟨9557486, by rfl⟩ : syracuseStep 12743315 = 19114973) B19114973
theorem B9933515 : Blo 1742572 9933515 := bstep (se 1 (by rfl) ⟨7450136, by rfl⟩ : syracuseStep 9933515 = 14900273) B14900273
theorem B5034743 : Blo 1742572 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B19862333 : Blo 1742572 19862333 := bstep (se 3 (by rfl) ⟨3724187, by rfl⟩ : syracuseStep 19862333 = 7448375) B7448375
theorem B5583745 : Blo 1742572 5583745 := bstep (se 2 (by rfl) ⟨2093904, by rfl⟩ : syracuseStep 5583745 = 4187809) B4187809
theorem B5886971 : Blo 1742572 5886971 := bstep (se 1 (by rfl) ⟨4415228, by rfl⟩ : syracuseStep 5886971 = 8830457) B8830457
theorem B13235237 : Blo 1742572 13235237 := bstep (se 4 (by rfl) ⟨1240803, by rfl⟩ : syracuseStep 13235237 = 2481607) B2481607
theorem B13243499 : Blo 1742572 13243499 := bstep (se 1 (by rfl) ⟨9932624, by rfl⟩ : syracuseStep 13243499 = 19865249) B19865249
theorem B22344821 : Blo 1742572 22344821 := bstep (se 5 (by rfl) ⟨1047413, by rfl⟩ : syracuseStep 22344821 = 2094827) B2094827
theorem B4412627 : Blo 1742572 4412627 := bstep (se 1 (by rfl) ⟨3309470, by rfl⟩ : syracuseStep 4412627 = 6618941) B6618941
theorem B5887187 : Blo 1742572 5887187 := bstep (se 1 (by rfl) ⟨4415390, by rfl⟩ : syracuseStep 5887187 = 8830781) B8830781
theorem B19871081 : Blo 1742572 19871081 := bstep (se 2 (by rfl) ⟨7451655, by rfl⟩ : syracuseStep 19871081 = 14903311) B14903311
theorem B5887457 : Blo 1742572 5887457 := bstep (se 2 (by rfl) ⟨2207796, by rfl⟩ : syracuseStep 5887457 = 4415593) B4415593
theorem B3921479 : Blo 1742572 3921479 := bstep (se 1 (by rfl) ⟨2941109, by rfl⟩ : syracuseStep 3921479 = 5882219) B5882219
theorem B3724871 : Blo 1742572 3724871 := bstep (se 1 (by rfl) ⟨2793653, by rfl⟩ : syracuseStep 3724871 = 5587307) B5587307
theorem B12564179 : Blo 1742572 12564179 := bstep (se 1 (by rfl) ⟨9423134, by rfl⟩ : syracuseStep 12564179 = 18846269) B18846269
theorem B1742587 : Blo 1742572 1742587 := bstep (se 1 (by rfl) ⟨1306940, by rfl⟩ : syracuseStep 1742587 = 2613881) B2613881
theorem B3921659 : Blo 1742572 3921659 := bstep (se 1 (by rfl) ⟨2941244, by rfl⟩ : syracuseStep 3921659 = 5882489) B5882489
theorem B1742623 : Blo 1742572 1742623 := bstep (se 1 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 1742623 = 2613935) B2613935
theorem B1742655 : Blo 1742572 1742655 := bstep (se 1 (by rfl) ⟨1306991, by rfl⟩ : syracuseStep 1742655 = 2613983) B2613983
theorem B6281023 : Blo 1742572 6281023 := bstep (se 1 (by rfl) ⟨4710767, by rfl⟩ : syracuseStep 6281023 = 9421535) B9421535
theorem B1742831 : Blo 1742572 1742831 := bstep (se 1 (by rfl) ⟨1307123, by rfl⟩ : syracuseStep 1742831 = 2614247) B2614247
theorem B2095087 : Blo 1742572 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B1743003 : Blo 1742572 1743003 := bstep (se 1 (by rfl) ⟨1307252, by rfl⟩ : syracuseStep 1743003 = 2614505) B2614505
theorem B1743039 : Blo 1742572 1743039 := bstep (se 1 (by rfl) ⟨1307279, by rfl⟩ : syracuseStep 1743039 = 2614559) B2614559
theorem B4028615 : Blo 1742572 4028615 := bstep (se 1 (by rfl) ⟨3021461, by rfl⟩ : syracuseStep 4028615 = 6042923) B6042923
theorem B8829161 : Blo 1742572 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B6281513 : Blo 1742572 6281513 := bstep (se 2 (by rfl) ⟨2355567, by rfl⟩ : syracuseStep 6281513 = 4711135) B4711135
theorem B3922217 : Blo 1742572 3922217 := bstep (se 2 (by rfl) ⟨1470831, by rfl⟩ : syracuseStep 3922217 = 2941663) B2941663
theorem B1743151 : Blo 1742572 1743151 := bstep (se 1 (by rfl) ⟨1307363, by rfl⟩ : syracuseStep 1743151 = 2614727) B2614727
theorem B8378731 : Blo 1742572 8378731 := bstep (se 1 (by rfl) ⟨6284048, by rfl⟩ : syracuseStep 8378731 = 12568097) B12568097
theorem B1743387 : Blo 1742572 1743387 := bstep (se 1 (by rfl) ⟨1307540, by rfl⟩ : syracuseStep 1743387 = 2615081) B2615081
theorem B1743391 : Blo 1742572 1743391 := bstep (se 1 (by rfl) ⟨1307543, by rfl⟩ : syracuseStep 1743391 = 2615087) B2615087
theorem B40245893 : Blo 1742572 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B1743707 : Blo 1742572 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B3922793 : Blo 1742572 3922793 := bstep (se 2 (by rfl) ⟨1471047, by rfl⟩ : syracuseStep 3922793 = 2942095) B2942095
theorem B16120711 : Blo 1742572 16120711 := bstep (se 1 (by rfl) ⟨12090533, by rfl⟩ : syracuseStep 16120711 = 24181067) B24181067
theorem B3922847 : Blo 1742572 3922847 := bstep (se 1 (by rfl) ⟨2942135, by rfl⟩ : syracuseStep 3922847 = 5884271) B5884271
theorem B1743775 : Blo 1742572 1743775 := bstep (se 1 (by rfl) ⟨1307831, by rfl⟩ : syracuseStep 1743775 = 2615663) B2615663
theorem B1743919 : Blo 1742572 1743919 := bstep (se 1 (by rfl) ⟨1307939, by rfl⟩ : syracuseStep 1743919 = 2615879) B2615879
theorem B1743943 : Blo 1742572 1743943 := bstep (se 1 (by rfl) ⟨1307957, by rfl⟩ : syracuseStep 1743943 = 2615915) B2615915
theorem B4963511 : Blo 1742572 4963511 := bstep (se 1 (by rfl) ⟨3722633, by rfl⟩ : syracuseStep 4963511 = 7445267) B7445267
theorem B1744095 : Blo 1742572 1744095 := bstep (se 1 (by rfl) ⟨1308071, by rfl⟩ : syracuseStep 1744095 = 2616143) B2616143
theorem B12573953 : Blo 1742572 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B2981129 : Blo 1742572 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B4963751 : Blo 1742572 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B1744359 : Blo 1742572 1744359 := bstep (se 1 (by rfl) ⟨1308269, by rfl⟩ : syracuseStep 1744359 = 2616539) B2616539
theorem B1744475 : Blo 1742572 1744475 := bstep (se 1 (by rfl) ⟨1308356, by rfl⟩ : syracuseStep 1744475 = 2616713) B2616713
theorem B7069427 : Blo 1742572 7069427 := bstep (se 1 (by rfl) ⟨5302070, by rfl⟩ : syracuseStep 7069427 = 10604141) B10604141
theorem B4415219 : Blo 1742572 4415219 := bstep (se 1 (by rfl) ⟨3311414, by rfl⟩ : syracuseStep 4415219 = 6622829) B6622829
theorem B37715705 : Blo 1742572 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B3923783 : Blo 1742572 3923783 := bstep (se 1 (by rfl) ⟨2942837, by rfl⟩ : syracuseStep 3923783 = 5885675) B5885675
theorem B7446667 : Blo 1742572 7446667 := bstep (se 1 (by rfl) ⟨5585000, by rfl⟩ : syracuseStep 7446667 = 11170001) B11170001
theorem B5587193 : Blo 1742572 5587193 := bstep (se 2 (by rfl) ⟨2095197, by rfl⟩ : syracuseStep 5587193 = 4190395) B4190395
theorem B15515981 : Blo 1742572 15515981 := bstep (se 3 (by rfl) ⟨2909246, by rfl⟩ : syracuseStep 15515981 = 5818493) B5818493
theorem B13238639 : Blo 1742572 13238639 := bstep (se 1 (by rfl) ⟨9928979, by rfl⟩ : syracuseStep 13238639 = 19857959) B19857959
theorem B14901671 : Blo 1742572 14901671 := bstep (se 1 (by rfl) ⟨11176253, by rfl⟩ : syracuseStep 14901671 = 22352507) B22352507
theorem B8495543 : Blo 1742572 8495543 := bstep (se 1 (by rfl) ⟨6371657, by rfl⟩ : syracuseStep 8495543 = 12743315) B12743315
theorem B3924647 : Blo 1742572 3924647 := bstep (se 1 (by rfl) ⟨2943485, by rfl⟩ : syracuseStep 3924647 = 5886971) B5886971
theorem B8823491 : Blo 1742572 8823491 := bstep (se 1 (by rfl) ⟨6617618, by rfl⟩ : syracuseStep 8823491 = 13235237) B13235237
theorem B2941751 : Blo 1742572 2941751 := bstep (se 1 (by rfl) ⟨2206313, by rfl⟩ : syracuseStep 2941751 = 4412627) B4412627
theorem B3924791 : Blo 1742572 3924791 := bstep (se 1 (by rfl) ⟨2943593, by rfl⟩ : syracuseStep 3924791 = 5887187) B5887187
theorem B13247387 : Blo 1742572 13247387 := bstep (se 1 (by rfl) ⟨9935540, by rfl⟩ : syracuseStep 13247387 = 19871081) B19871081
theorem B3924971 : Blo 1742572 3924971 := bstep (se 1 (by rfl) ⟨2943728, by rfl⟩ : syracuseStep 3924971 = 5887457) B5887457
theorem B12567581 : Blo 1742572 12567581 := bstep (se 3 (by rfl) ⟨2356421, by rfl⟩ : syracuseStep 12567581 = 4712843) B4712843
theorem B2614319 : Blo 1742572 2614319 := bstep (se 1 (by rfl) ⟨1960739, by rfl⟩ : syracuseStep 2614319 = 3921479) B3921479
theorem B2614439 : Blo 1742572 2614439 := bstep (se 1 (by rfl) ⟨1960829, by rfl⟩ : syracuseStep 2614439 = 3921659) B3921659
theorem B47703289 : Blo 1742572 47703289 := bstep (se 2 (by rfl) ⟨17888733, by rfl⟩ : syracuseStep 47703289 = 35777467) B35777467
theorem B5965103 : Blo 1742572 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B4187675 : Blo 1742572 4187675 := bstep (se 1 (by rfl) ⟨3140756, by rfl⟩ : syracuseStep 4187675 = 6281513) B6281513
theorem B2614811 : Blo 1742572 2614811 := bstep (se 1 (by rfl) ⟨1961108, by rfl⟩ : syracuseStep 2614811 = 3922217) B3922217
theorem B3311209 : Blo 1742572 3311209 := bstep (se 2 (by rfl) ⟨1241703, by rfl⟩ : syracuseStep 3311209 = 2483407) B2483407
theorem B9422507 : Blo 1742572 9422507 := bstep (se 1 (by rfl) ⟨7066880, by rfl⟩ : syracuseStep 9422507 = 14133761) B14133761
theorem B40830655 : Blo 1742572 40830655 := bstep (se 1 (by rfl) ⟨30622991, by rfl⟩ : syracuseStep 40830655 = 61245983) B61245983
theorem B26830595 : Blo 1742572 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B29804435 : Blo 1742572 29804435 := bstep (se 1 (by rfl) ⟨22353326, by rfl⟩ : syracuseStep 29804435 = 44706653) B44706653
theorem B2615195 : Blo 1742572 2615195 := bstep (se 1 (by rfl) ⟨1961396, by rfl⟩ : syracuseStep 2615195 = 3922793) B3922793
theorem B2615231 : Blo 1742572 2615231 := bstep (se 1 (by rfl) ⟨1961423, by rfl⟩ : syracuseStep 2615231 = 3922847) B3922847
theorem B2615417 : Blo 1742572 2615417 := bstep (se 2 (by rfl) ⟨980781, by rfl⟩ : syracuseStep 2615417 = 1961563) B1961563
theorem B8374427 : Blo 1742572 8374427 := bstep (se 1 (by rfl) ⟨6280820, by rfl⟩ : syracuseStep 8374427 = 12561641) B12561641
theorem B8382635 : Blo 1742572 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B6621371 : Blo 1742572 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B8374697 : Blo 1742572 8374697 := bstep (se 2 (by rfl) ⟨3140511, by rfl⟩ : syracuseStep 8374697 = 6281023) B6281023
theorem B4712951 : Blo 1742572 4712951 := bstep (se 1 (by rfl) ⟨3534713, by rfl⟩ : syracuseStep 4712951 = 7069427) B7069427
theorem B2943479 : Blo 1742572 2943479 := bstep (se 1 (by rfl) ⟨2207609, by rfl⟩ : syracuseStep 2943479 = 4415219) B4415219
theorem B2615801 : Blo 1742572 2615801 := bstep (se 2 (by rfl) ⟨980925, by rfl⟩ : syracuseStep 2615801 = 1961851) B1961851
theorem B13421051 : Blo 1742572 13421051 := bstep (se 1 (by rfl) ⟨10065788, by rfl⟩ : syracuseStep 13421051 = 20131577) B20131577
theorem B25143803 : Blo 1742572 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B2615855 : Blo 1742572 2615855 := bstep (se 1 (by rfl) ⟨1961891, by rfl⟩ : syracuseStep 2615855 = 3923783) B3923783
theorem B13241069 : Blo 1742572 13241069 := bstep (se 3 (by rfl) ⟨2482700, by rfl⟩ : syracuseStep 13241069 = 4965401) B4965401
theorem B107342779 : Blo 1742572 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B11324347 : Blo 1742572 11324347 := bstep (se 1 (by rfl) ⟨8493260, by rfl⟩ : syracuseStep 11324347 = 16986521) B16986521
theorem B2616287 : Blo 1742572 2616287 := bstep (se 1 (by rfl) ⟨1962215, by rfl⟩ : syracuseStep 2616287 = 3924431) B3924431
theorem B35793899 : Blo 1742572 35793899 := bstep (se 1 (by rfl) ⟨26845424, by rfl⟩ : syracuseStep 35793899 = 53690849) B53690849
theorem B7449641 : Blo 1742572 7449641 := bstep (se 2 (by rfl) ⟨2793615, by rfl⟩ : syracuseStep 7449641 = 5587231) B5587231
theorem B1961023 : Blo 1742572 1961023 := bstep (se 1 (by rfl) ⟨1470767, by rfl⟩ : syracuseStep 1961023 = 2941535) B2941535
theorem B6622343 : Blo 1742572 6622343 := bstep (se 1 (by rfl) ⟨4966757, by rfl⟩ : syracuseStep 6622343 = 9933515) B9933515
theorem B13241555 : Blo 1742572 13241555 := bstep (se 1 (by rfl) ⟨9931166, by rfl⟩ : syracuseStep 13241555 = 19862333) B19862333
theorem B15904019 : Blo 1742572 15904019 := bstep (se 1 (by rfl) ⟨11928014, by rfl⟩ : syracuseStep 15904019 = 23856029) B23856029
theorem B7949677 : Blo 1742572 7949677 := bstep (se 3 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 7949677 = 2981129) B2981129
theorem B2616731 : Blo 1742572 2616731 := bstep (se 1 (by rfl) ⟨1962548, by rfl⟩ : syracuseStep 2616731 = 3925097) B3925097
theorem B14896547 : Blo 1742572 14896547 := bstep (se 1 (by rfl) ⟨11172410, by rfl⟩ : syracuseStep 14896547 = 22344821) B22344821
theorem B4714075 : Blo 1742572 4714075 := bstep (se 1 (by rfl) ⟨3535556, by rfl⟩ : syracuseStep 4714075 = 7071113) B7071113
theorem B13233779 : Blo 1742572 13233779 := bstep (se 1 (by rfl) ⟨9925334, by rfl⟩ : syracuseStep 13233779 = 19850669) B19850669
theorem B4189943 : Blo 1742572 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B8376119 : Blo 1742572 8376119 := bstep (se 1 (by rfl) ⟨6282089, by rfl⟩ : syracuseStep 8376119 = 12564179) B12564179
theorem B5886107 : Blo 1742572 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B1962139 : Blo 1742572 1962139 := bstep (se 1 (by rfl) ⟨1471604, by rfl⟩ : syracuseStep 1962139 = 2943209) B2943209
theorem B83832995 : Blo 1742572 83832995 := bstep (se 1 (by rfl) ⟨62874746, by rfl⟩ : syracuseStep 83832995 = 125749493) B125749493
theorem B9932989 : Blo 1742572 9932989 := bstep (se 3 (by rfl) ⟨1862435, by rfl⟩ : syracuseStep 9932989 = 3724871) B3724871
theorem B9925199 : Blo 1742572 9925199 := bstep (se 1 (by rfl) ⟨7443899, by rfl⟩ : syracuseStep 9925199 = 14887799) B14887799
theorem B4715243 : Blo 1742572 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B33952537 : Blo 1742572 33952537 := bstep (se 2 (by rfl) ⟨12732201, by rfl⟩ : syracuseStep 33952537 = 25464403) B25464403
theorem B29791313 : Blo 1742572 29791313 := bstep (se 2 (by rfl) ⟨11171742, by rfl⟩ : syracuseStep 29791313 = 22343485) B22343485
theorem B7451777 : Blo 1742572 7451777 := bstep (se 2 (by rfl) ⟨2794416, by rfl⟩ : syracuseStep 7451777 = 5588833) B5588833
theorem B3921263 : Blo 1742572 3921263 := bstep (se 1 (by rfl) ⟨2940947, by rfl⟩ : syracuseStep 3921263 = 5881895) B5881895
theorem B1742575 : Blo 1742572 1742575 := bstep (se 1 (by rfl) ⟨1306931, by rfl⟩ : syracuseStep 1742575 = 2613863) B2613863
theorem B18847475 : Blo 1742572 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B3921695 : Blo 1742572 3921695 := bstep (se 1 (by rfl) ⟨2941271, by rfl⟩ : syracuseStep 3921695 = 5882543) B5882543
theorem B11171641 : Blo 1742572 11171641 := bstep (se 2 (by rfl) ⟨4189365, by rfl⟩ : syracuseStep 11171641 = 8378731) B8378731
theorem B1742663 : Blo 1742572 1742663 := bstep (se 1 (by rfl) ⟨1306997, by rfl⟩ : syracuseStep 1742663 = 2613995) B2613995
theorem B3356495 : Blo 1742572 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B1742683 : Blo 1742572 1742683 := bstep (se 1 (by rfl) ⟨1307012, by rfl⟩ : syracuseStep 1742683 = 2614025) B2614025
theorem B4413275 : Blo 1742572 4413275 := bstep (se 1 (by rfl) ⟨3309956, by rfl⟩ : syracuseStep 4413275 = 6619913) B6619913
theorem B5887835 : Blo 1742572 5887835 := bstep (se 1 (by rfl) ⟨4415876, by rfl⟩ : syracuseStep 5887835 = 8831753) B8831753
theorem B1742751 : Blo 1742572 1742751 := bstep (se 1 (by rfl) ⟨1307063, by rfl⟩ : syracuseStep 1742751 = 2614127) B2614127
theorem B3725281 : Blo 1742572 3725281 := bstep (se 2 (by rfl) ⟨1396980, by rfl⟩ : syracuseStep 3725281 = 2793961) B2793961
theorem B3921911 : Blo 1742572 3921911 := bstep (se 1 (by rfl) ⟨2941433, by rfl⟩ : syracuseStep 3921911 = 5882867) B5882867
theorem B7952377 : Blo 1742572 7952377 := bstep (se 2 (by rfl) ⟨2982141, by rfl⟩ : syracuseStep 7952377 = 5964283) B5964283
theorem B12564521 : Blo 1742572 12564521 := bstep (se 2 (by rfl) ⟨4711695, by rfl⟩ : syracuseStep 12564521 = 9423391) B9423391
theorem B1742919 : Blo 1742572 1742919 := bstep (se 1 (by rfl) ⟨1307189, by rfl⟩ : syracuseStep 1742919 = 2614379) B2614379
theorem B8828999 : Blo 1742572 8828999 := bstep (se 1 (by rfl) ⟨6621749, by rfl⟩ : syracuseStep 8828999 = 13243499) B13243499
theorem B1743079 : Blo 1742572 1743079 := bstep (se 1 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 1743079 = 2614619) B2614619
theorem B3922271 : Blo 1742572 3922271 := bstep (se 1 (by rfl) ⟨2941703, by rfl⟩ : syracuseStep 3922271 = 5883407) B5883407
theorem B1743263 : Blo 1742572 1743263 := bstep (se 1 (by rfl) ⟨1307447, by rfl⟩ : syracuseStep 1743263 = 2614895) B2614895
theorem B1743311 : Blo 1742572 1743311 := bstep (se 1 (by rfl) ⟨1307483, by rfl⟩ : syracuseStep 1743311 = 2614967) B2614967
theorem B1743335 : Blo 1742572 1743335 := bstep (se 1 (by rfl) ⟨1307501, by rfl⟩ : syracuseStep 1743335 = 2615003) B2615003
theorem B7444993 : Blo 1742572 7444993 := bstep (se 2 (by rfl) ⟨2791872, by rfl⟩ : syracuseStep 7444993 = 5583745) B5583745
theorem B21494281 : Blo 1742572 21494281 := bstep (se 2 (by rfl) ⟨8060355, by rfl⟩ : syracuseStep 21494281 = 16120711) B16120711
theorem B1743451 : Blo 1742572 1743451 := bstep (se 1 (by rfl) ⟨1307588, by rfl⟩ : syracuseStep 1743451 = 2615177) B2615177
theorem B1743519 : Blo 1742572 1743519 := bstep (se 1 (by rfl) ⟨1307639, by rfl⟩ : syracuseStep 1743519 = 2615279) B2615279
theorem B2685743 : Blo 1742572 2685743 := bstep (se 1 (by rfl) ⟨2014307, by rfl⟩ : syracuseStep 2685743 = 4028615) B4028615
theorem B1743687 : Blo 1742572 1743687 := bstep (se 1 (by rfl) ⟨1307765, by rfl⟩ : syracuseStep 1743687 = 2615531) B2615531
theorem B1743727 : Blo 1742572 1743727 := bstep (se 1 (by rfl) ⟨1307795, by rfl⟩ : syracuseStep 1743727 = 2615591) B2615591
theorem B3922811 : Blo 1742572 3922811 := bstep (se 1 (by rfl) ⟨2942108, by rfl⟩ : syracuseStep 3922811 = 5884217) B5884217
theorem B1743783 : Blo 1742572 1743783 := bstep (se 1 (by rfl) ⟨1307837, by rfl⟩ : syracuseStep 1743783 = 2615675) B2615675
theorem B6282203 : Blo 1742572 6282203 := bstep (se 1 (by rfl) ⟨4711652, by rfl⟩ : syracuseStep 6282203 = 9423305) B9423305
theorem B3922991 : Blo 1742572 3922991 := bstep (se 1 (by rfl) ⟨2942243, by rfl⟩ : syracuseStep 3922991 = 5884487) B5884487
theorem B1743963 : Blo 1742572 1743963 := bstep (se 1 (by rfl) ⟨1307972, by rfl⟩ : syracuseStep 1743963 = 2615945) B2615945
theorem B1744079 : Blo 1742572 1744079 := bstep (se 1 (by rfl) ⟨1308059, by rfl⟩ : syracuseStep 1744079 = 2616119) B2616119
theorem B1744103 : Blo 1742572 1744103 := bstep (se 1 (by rfl) ⟨1308077, by rfl⟩ : syracuseStep 1744103 = 2616155) B2616155
theorem B1744199 : Blo 1742572 1744199 := bstep (se 1 (by rfl) ⟨1308149, by rfl⟩ : syracuseStep 1744199 = 2616299) B2616299
theorem B3309007 : Blo 1742572 3309007 := bstep (se 1 (by rfl) ⟨2481755, by rfl⟩ : syracuseStep 3309007 = 4963511) B4963511
theorem B1744335 : Blo 1742572 1744335 := bstep (se 1 (by rfl) ⟨1308251, by rfl⟩ : syracuseStep 1744335 = 2616503) B2616503
theorem B3309167 : Blo 1742572 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1744495 : Blo 1742572 1744495 := bstep (se 1 (by rfl) ⟨1308371, by rfl⟩ : syracuseStep 1744495 = 2616743) B2616743
theorem B5299879 : Blo 1742572 5299879 := bstep (se 1 (by rfl) ⟨3974909, by rfl⟩ : syracuseStep 5299879 = 7949819) B7949819
theorem B1744551 : Blo 1742572 1744551 := bstep (se 1 (by rfl) ⟨1308413, by rfl⟩ : syracuseStep 1744551 = 2616827) B2616827
theorem B3923675 : Blo 1742572 3923675 := bstep (se 1 (by rfl) ⟨2942756, by rfl⟩ : syracuseStep 3923675 = 5885513) B5885513
theorem B2793449 : Blo 1742572 2793449 := bstep (se 2 (by rfl) ⟨1047543, by rfl⟩ : syracuseStep 2793449 = 2095087) B2095087
theorem B3923945 : Blo 1742572 3923945 := bstep (se 2 (by rfl) ⟨1471479, by rfl⟩ : syracuseStep 3923945 = 2942959) B2942959
theorem B3924071 : Blo 1742572 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B9928889 : Blo 1742572 9928889 := bstep (se 2 (by rfl) ⟨3723333, by rfl⟩ : syracuseStep 9928889 = 7446667) B7446667
theorem B5882327 : Blo 1742572 5882327 := bstep (se 1 (by rfl) ⟨4411745, by rfl⟩ : syracuseStep 5882327 = 8823491) B8823491
theorem B8831591 : Blo 1742572 8831591 := bstep (se 1 (by rfl) ⟨6623693, by rfl⟩ : syracuseStep 8831591 = 13247387) B13247387
theorem B2614175 : Blo 1742572 2614175 := bstep (se 1 (by rfl) ⟨1960631, by rfl⟩ : syracuseStep 2614175 = 3921263) B3921263
theorem B2614463 : Blo 1742572 2614463 := bstep (se 1 (by rfl) ⟨1960847, by rfl⟩ : syracuseStep 2614463 = 3921695) B3921695
theorem B2237663 : Blo 1742572 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B2942183 : Blo 1742572 2942183 := bstep (se 1 (by rfl) ⟨2206637, by rfl⟩ : syracuseStep 2942183 = 4413275) B4413275
theorem B3925223 : Blo 1742572 3925223 := bstep (se 1 (by rfl) ⟨2943917, by rfl⟩ : syracuseStep 3925223 = 5887835) B5887835
theorem B143123705 : Blo 1742572 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B12567869 : Blo 1742572 12567869 := bstep (se 3 (by rfl) ⟨2356475, by rfl⟩ : syracuseStep 12567869 = 4712951) B4712951
theorem B2614607 : Blo 1742572 2614607 := bstep (se 1 (by rfl) ⟨1960955, by rfl⟩ : syracuseStep 2614607 = 3921911) B3921911
theorem B2614697 : Blo 1742572 2614697 := bstep (se 2 (by rfl) ⟨980511, by rfl⟩ : syracuseStep 2614697 = 1961023) B1961023
theorem B5588423 : Blo 1742572 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B2614847 : Blo 1742572 2614847 := bstep (se 1 (by rfl) ⟨1961135, by rfl⟩ : syracuseStep 2614847 = 3922271) B3922271
theorem B63604385 : Blo 1742572 63604385 := bstep (se 2 (by rfl) ⟨23851644, by rfl⟩ : syracuseStep 63604385 = 47703289) B47703289
theorem B8947367 : Blo 1742572 8947367 := bstep (se 1 (by rfl) ⟨6710525, by rfl⟩ : syracuseStep 8947367 = 13421051) B13421051
theorem B16762535 : Blo 1742572 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B25126685 : Blo 1742572 25126685 := bstep (se 3 (by rfl) ⟨4711253, by rfl⟩ : syracuseStep 25126685 = 9422507) B9422507
theorem B2615207 : Blo 1742572 2615207 := bstep (se 1 (by rfl) ⟨1961405, by rfl⟩ : syracuseStep 2615207 = 3922811) B3922811
theorem B4966427 : Blo 1742572 4966427 := bstep (se 1 (by rfl) ⟨3724820, by rfl⟩ : syracuseStep 4966427 = 7449641) B7449641
theorem B2615327 : Blo 1742572 2615327 := bstep (se 1 (by rfl) ⟨1961495, by rfl⟩ : syracuseStep 2615327 = 3922991) B3922991
theorem B6285433 : Blo 1742572 6285433 := bstep (se 2 (by rfl) ⟨2357037, by rfl⟩ : syracuseStep 6285433 = 4714075) B4714075
theorem B10602679 : Blo 1742572 10602679 := bstep (se 1 (by rfl) ⟨7952009, by rfl⟩ : syracuseStep 10602679 = 15904019) B15904019
theorem B9931031 : Blo 1742572 9931031 := bstep (se 1 (by rfl) ⟨7448273, by rfl⟩ : syracuseStep 9931031 = 14896547) B14896547
theorem B2206111 : Blo 1742572 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B14895521 : Blo 1742572 14895521 := bstep (se 2 (by rfl) ⟨5585820, by rfl⟩ : syracuseStep 14895521 = 11171641) B11171641
theorem B2615783 : Blo 1742572 2615783 := bstep (se 1 (by rfl) ⟨1961837, by rfl⟩ : syracuseStep 2615783 = 3923675) B3923675
theorem B19868165 : Blo 1742572 19868165 := bstep (se 4 (by rfl) ⟨1862640, by rfl⟩ : syracuseStep 19868165 = 3725281) B3725281
theorem B1862299 : Blo 1742572 1862299 := bstep (se 1 (by rfl) ⟨1396724, by rfl⟩ : syracuseStep 1862299 = 2793449) B2793449
theorem B2615963 : Blo 1742572 2615963 := bstep (se 1 (by rfl) ⟨1961972, by rfl⟩ : syracuseStep 2615963 = 3923945) B3923945
theorem B10603169 : Blo 1742572 10603169 := bstep (se 2 (by rfl) ⟨3976188, by rfl⟩ : syracuseStep 10603169 = 7952377) B7952377
theorem B55888663 : Blo 1742572 55888663 := bstep (se 1 (by rfl) ⟨41916497, by rfl⟩ : syracuseStep 55888663 = 83832995) B83832995
theorem B2616185 : Blo 1742572 2616185 := bstep (se 2 (by rfl) ⟨981069, by rfl⟩ : syracuseStep 2616185 = 1962139) B1962139
theorem B8825759 : Blo 1742572 8825759 := bstep (se 1 (by rfl) ⟨6619319, by rfl⟩ : syracuseStep 8825759 = 13238639) B13238639
theorem B5663695 : Blo 1742572 5663695 := bstep (se 1 (by rfl) ⟨4247771, by rfl⟩ : syracuseStep 5663695 = 8495543) B8495543
theorem B2616431 : Blo 1742572 2616431 := bstep (se 1 (by rfl) ⟨1962323, by rfl⟩ : syracuseStep 2616431 = 3924647) B3924647
theorem B1961167 : Blo 1742572 1961167 := bstep (se 1 (by rfl) ⟨1470875, by rfl⟩ : syracuseStep 1961167 = 2941751) B2941751
theorem B2616527 : Blo 1742572 2616527 := bstep (se 1 (by rfl) ⟨1962395, by rfl⟩ : syracuseStep 2616527 = 3924791) B3924791
theorem B2616647 : Blo 1742572 2616647 := bstep (se 1 (by rfl) ⟨1962485, by rfl⟩ : syracuseStep 2616647 = 3924971) B3924971
theorem B28659041 : Blo 1742572 28659041 := bstep (se 2 (by rfl) ⟨10747140, by rfl⟩ : syracuseStep 28659041 = 21494281) B21494281
theorem B19860875 : Blo 1742572 19860875 := bstep (se 1 (by rfl) ⟨14895656, by rfl⟩ : syracuseStep 19860875 = 29791313) B29791313
theorem B4967851 : Blo 1742572 4967851 := bstep (se 1 (by rfl) ⟨3725888, by rfl⟩ : syracuseStep 4967851 = 7451777) B7451777
theorem B17887063 : Blo 1742572 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B19869623 : Blo 1742572 19869623 := bstep (se 1 (by rfl) ⟨14902217, by rfl⟩ : syracuseStep 19869623 = 29804435) B29804435
theorem B8376347 : Blo 1742572 8376347 := bstep (se 1 (by rfl) ⟨6282260, by rfl⟩ : syracuseStep 8376347 = 12564521) B12564521
theorem B5885999 : Blo 1742572 5885999 := bstep (se 1 (by rfl) ⟨4414499, by rfl⟩ : syracuseStep 5885999 = 8828999) B8828999
theorem B5582951 : Blo 1742572 5582951 := bstep (se 1 (by rfl) ⟨4187213, by rfl⟩ : syracuseStep 5582951 = 8374427) B8374427
theorem B181080197 : Blo 1742572 181080197 := bstep (se 4 (by rfl) ⟨16976268, by rfl⟩ : syracuseStep 181080197 = 33952537) B33952537
theorem B5583131 : Blo 1742572 5583131 := bstep (se 1 (by rfl) ⟨4187348, by rfl⟩ : syracuseStep 5583131 = 8374697) B8374697
theorem B1962319 : Blo 1742572 1962319 := bstep (se 1 (by rfl) ⟨1471739, by rfl⟩ : syracuseStep 1962319 = 2943479) B2943479
theorem B8827379 : Blo 1742572 8827379 := bstep (se 1 (by rfl) ⟨6620534, by rfl⟩ : syracuseStep 8827379 = 13241069) B13241069
theorem B1790495 : Blo 1742572 1790495 := bstep (se 1 (by rfl) ⟨1342871, by rfl⟩ : syracuseStep 1790495 = 2685743) B2685743
theorem B4412009 : Blo 1742572 4412009 := bstep (se 2 (by rfl) ⟨1654503, by rfl⟩ : syracuseStep 4412009 = 3309007) B3309007
theorem B8827703 : Blo 1742572 8827703 := bstep (se 1 (by rfl) ⟨6620777, by rfl⟩ : syracuseStep 8827703 = 13241555) B13241555
theorem B7066505 : Blo 1742572 7066505 := bstep (se 2 (by rfl) ⟨2649939, by rfl⟩ : syracuseStep 7066505 = 5299879) B5299879
theorem B54440873 : Blo 1742572 54440873 := bstep (se 2 (by rfl) ⟨20415327, by rfl⟩ : syracuseStep 54440873 = 40830655) B40830655
theorem B60396517 : Blo 1742572 60396517 := bstep (se 4 (by rfl) ⟨5662173, by rfl⟩ : syracuseStep 60396517 = 11324347) B11324347
theorem B5584079 : Blo 1742572 5584079 := bstep (se 1 (by rfl) ⟨4188059, by rfl⟩ : syracuseStep 5584079 = 8376119) B8376119
theorem B3724795 : Blo 1742572 3724795 := bstep (se 1 (by rfl) ⟨2793596, by rfl⟩ : syracuseStep 3724795 = 5587193) B5587193
theorem B10343987 : Blo 1742572 10343987 := bstep (se 1 (by rfl) ⟨7757990, by rfl⟩ : syracuseStep 10343987 = 15515981) B15515981
theorem B13243985 : Blo 1742572 13243985 := bstep (se 2 (by rfl) ⟨4966494, by rfl⟩ : syracuseStep 13243985 = 9932989) B9932989
theorem B9934447 : Blo 1742572 9934447 := bstep (se 1 (by rfl) ⟨7450835, by rfl⟩ : syracuseStep 9934447 = 14901671) B14901671
theorem B6616799 : Blo 1742572 6616799 := bstep (se 1 (by rfl) ⟨4962599, by rfl⟩ : syracuseStep 6616799 = 9925199) B9925199
theorem B3143495 : Blo 1742572 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B9926657 : Blo 1742572 9926657 := bstep (se 2 (by rfl) ⟨3722496, by rfl⟩ : syracuseStep 9926657 = 7444993) B7444993
theorem B8378387 : Blo 1742572 8378387 := bstep (se 1 (by rfl) ⟨6283790, by rfl⟩ : syracuseStep 8378387 = 12567581) B12567581
theorem B1742879 : Blo 1742572 1742879 := bstep (se 1 (by rfl) ⟨1307159, by rfl⟩ : syracuseStep 1742879 = 2614319) B2614319
theorem B1742959 : Blo 1742572 1742959 := bstep (se 1 (by rfl) ⟨1307219, by rfl⟩ : syracuseStep 1742959 = 2614439) B2614439
theorem B15906941 : Blo 1742572 15906941 := bstep (se 3 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 15906941 = 5965103) B5965103
theorem B2791783 : Blo 1742572 2791783 := bstep (se 1 (by rfl) ⟨2093837, by rfl⟩ : syracuseStep 2791783 = 4187675) B4187675
theorem B1743207 : Blo 1742572 1743207 := bstep (se 1 (by rfl) ⟨1307405, by rfl⟩ : syracuseStep 1743207 = 2614811) B2614811
theorem B12564983 : Blo 1742572 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B1743463 : Blo 1742572 1743463 := bstep (se 1 (by rfl) ⟨1307597, by rfl⟩ : syracuseStep 1743463 = 2615195) B2615195
theorem B1743487 : Blo 1742572 1743487 := bstep (se 1 (by rfl) ⟨1307615, by rfl⟩ : syracuseStep 1743487 = 2615231) B2615231
theorem B1743611 : Blo 1742572 1743611 := bstep (se 1 (by rfl) ⟨1307708, by rfl⟩ : syracuseStep 1743611 = 2615417) B2615417
theorem B4414247 : Blo 1742572 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B1743867 : Blo 1742572 1743867 := bstep (se 1 (by rfl) ⟨1307900, by rfl⟩ : syracuseStep 1743867 = 2615801) B2615801
theorem B1743903 : Blo 1742572 1743903 := bstep (se 1 (by rfl) ⟨1307927, by rfl⟩ : syracuseStep 1743903 = 2615855) B2615855
theorem B10599569 : Blo 1742572 10599569 := bstep (se 2 (by rfl) ⟨3974838, by rfl⟩ : syracuseStep 10599569 = 7949677) B7949677
theorem B1744191 : Blo 1742572 1744191 := bstep (se 1 (by rfl) ⟨1308143, by rfl⟩ : syracuseStep 1744191 = 2616287) B2616287
theorem B23862599 : Blo 1742572 23862599 := bstep (se 1 (by rfl) ⟨17896949, by rfl⟩ : syracuseStep 23862599 = 35793899) B35793899
theorem B4414895 : Blo 1742572 4414895 := bstep (se 1 (by rfl) ⟨3311171, by rfl⟩ : syracuseStep 4414895 = 6622343) B6622343
theorem B4414945 : Blo 1742572 4414945 := bstep (se 2 (by rfl) ⟨1655604, by rfl⟩ : syracuseStep 4414945 = 3311209) B3311209
theorem B1744487 : Blo 1742572 1744487 := bstep (se 1 (by rfl) ⟨1308365, by rfl⟩ : syracuseStep 1744487 = 2616731) B2616731
theorem B8822519 : Blo 1742572 8822519 := bstep (se 1 (by rfl) ⟨6616889, by rfl⟩ : syracuseStep 8822519 = 13233779) B13233779
theorem B2793295 : Blo 1742572 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B16752541 : Blo 1742572 16752541 := bstep (se 3 (by rfl) ⟨3141101, by rfl⟩ : syracuseStep 16752541 = 6282203) B6282203
theorem B3923999 : Blo 1742572 3923999 := bstep (se 1 (by rfl) ⟨2942999, by rfl⟩ : syracuseStep 3923999 = 5885999) B5885999
theorem B6619259 : Blo 1742572 6619259 := bstep (se 1 (by rfl) ⟨4964444, by rfl⟩ : syracuseStep 6619259 = 9928889) B9928889
theorem B8380577 : Blo 1742572 8380577 := bstep (se 2 (by rfl) ⟨3142716, by rfl⟩ : syracuseStep 8380577 = 6285433) B6285433
theorem B2941339 : Blo 1742572 2941339 := bstep (se 1 (by rfl) ⟨2206004, by rfl⟩ : syracuseStep 2941339 = 4412009) B4412009
theorem B2941481 : Blo 1742572 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B4711003 : Blo 1742572 4711003 := bstep (se 1 (by rfl) ⟨3533252, by rfl⟩ : syracuseStep 4711003 = 7066505) B7066505
theorem B2483065 : Blo 1742572 2483065 := bstep (se 2 (by rfl) ⟨931149, by rfl⟩ : syracuseStep 2483065 = 1862299) B1862299
theorem B42402923 : Blo 1742572 42402923 := bstep (se 1 (by rfl) ⟨31802192, by rfl⟩ : syracuseStep 42402923 = 63604385) B63604385
theorem B5964911 : Blo 1742572 5964911 := bstep (se 1 (by rfl) ⟨4473683, by rfl⟩ : syracuseStep 5964911 = 8947367) B8947367
theorem B11175023 : Blo 1742572 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B80528689 : Blo 1742572 80528689 := bstep (se 2 (by rfl) ⟨30198258, by rfl⟩ : syracuseStep 80528689 = 60396517) B60396517
theorem B3310951 : Blo 1742572 3310951 := bstep (se 1 (by rfl) ⟨2483213, by rfl⟩ : syracuseStep 3310951 = 4966427) B4966427
theorem B6620687 : Blo 1742572 6620687 := bstep (se 1 (by rfl) ⟨4965515, by rfl⟩ : syracuseStep 6620687 = 9931031) B9931031
theorem B2614889 : Blo 1742572 2614889 := bstep (se 2 (by rfl) ⟨980583, by rfl⟩ : syracuseStep 2614889 = 1961167) B1961167
theorem B9930347 : Blo 1742572 9930347 := bstep (se 1 (by rfl) ⟨7447760, by rfl⟩ : syracuseStep 9930347 = 14895521) B14895521
theorem B2942831 : Blo 1742572 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B5883839 : Blo 1742572 5883839 := bstep (se 1 (by rfl) ⟨4412879, by rfl⟩ : syracuseStep 5883839 = 8825759) B8825759
theorem B4966393 : Blo 1742572 4966393 := bstep (se 2 (by rfl) ⟨1862397, by rfl⟩ : syracuseStep 4966393 = 3724795) B3724795
theorem B8382653 : Blo 1742572 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B19106027 : Blo 1742572 19106027 := bstep (se 1 (by rfl) ⟨14329520, by rfl⟩ : syracuseStep 19106027 = 28659041) B28659041
theorem B13240583 : Blo 1742572 13240583 := bstep (se 1 (by rfl) ⟨9930437, by rfl⟩ : syracuseStep 13240583 = 19860875) B19860875
theorem B2943263 : Blo 1742572 2943263 := bstep (se 1 (by rfl) ⟨2207447, by rfl⟩ : syracuseStep 2943263 = 4414895) B4414895
theorem B23849417 : Blo 1742572 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B3721967 : Blo 1742572 3721967 := bstep (se 1 (by rfl) ⟨2791475, by rfl⟩ : syracuseStep 3721967 = 5582951) B5582951
theorem B2616047 : Blo 1742572 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B120720131 : Blo 1742572 120720131 := bstep (se 1 (by rfl) ⟨90540098, by rfl⟩ : syracuseStep 120720131 = 181080197) B181080197
theorem B3722087 : Blo 1742572 3722087 := bstep (se 1 (by rfl) ⟨2791565, by rfl⟩ : syracuseStep 3722087 = 5583131) B5583131
theorem B19098613 : Blo 1742572 19098613 := bstep (se 5 (by rfl) ⟨895247, by rfl⟩ : syracuseStep 19098613 = 1790495) B1790495
theorem B5884919 : Blo 1742572 5884919 := bstep (se 1 (by rfl) ⟨4413689, by rfl⟩ : syracuseStep 5884919 = 8827379) B8827379
theorem B2616425 : Blo 1742572 2616425 := bstep (se 2 (by rfl) ⟨981159, by rfl⟩ : syracuseStep 2616425 = 1962319) B1962319
theorem B3722377 : Blo 1742572 3722377 := bstep (se 2 (by rfl) ⟨1395891, by rfl⟩ : syracuseStep 3722377 = 2791783) B2791783
theorem B5885135 : Blo 1742572 5885135 := bstep (se 1 (by rfl) ⟨4413851, by rfl⟩ : syracuseStep 5885135 = 8827703) B8827703
theorem B5967101 : Blo 1742572 5967101 := bstep (se 3 (by rfl) ⟨1118831, by rfl⟩ : syracuseStep 5967101 = 2237663) B2237663
theorem B36293915 : Blo 1742572 36293915 := bstep (se 1 (by rfl) ⟨27220436, by rfl⟩ : syracuseStep 36293915 = 54440873) B54440873
theorem B3722719 : Blo 1742572 3722719 := bstep (se 1 (by rfl) ⟨2792039, by rfl⟩ : syracuseStep 3722719 = 5584079) B5584079
theorem B1961455 : Blo 1742572 1961455 := bstep (se 1 (by rfl) ⟨1471091, by rfl⟩ : syracuseStep 1961455 = 2942183) B2942183
theorem B2616815 : Blo 1742572 2616815 := bstep (se 1 (by rfl) ⟨1962611, by rfl⟩ : syracuseStep 2616815 = 3925223) B3925223
theorem B95415803 : Blo 1742572 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B74518217 : Blo 1742572 74518217 := bstep (se 2 (by rfl) ⟨27944331, by rfl⟩ : syracuseStep 74518217 = 55888663) B55888663
theorem B4411199 : Blo 1742572 4411199 := bstep (se 1 (by rfl) ⟨3308399, by rfl⟩ : syracuseStep 4411199 = 6616799) B6616799
theorem B10604627 : Blo 1742572 10604627 := bstep (se 1 (by rfl) ⟨7953470, by rfl⟩ : syracuseStep 10604627 = 15906941) B15906941
theorem B8376655 : Blo 1742572 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B6623801 : Blo 1742572 6623801 := bstep (se 2 (by rfl) ⟨2483925, by rfl⟩ : syracuseStep 6623801 = 4967851) B4967851
theorem B5886593 : Blo 1742572 5886593 := bstep (se 2 (by rfl) ⟨2207472, by rfl⟩ : syracuseStep 5886593 = 4414945) B4414945
theorem B7066379 : Blo 1742572 7066379 := bstep (se 1 (by rfl) ⟨5299784, by rfl⟩ : syracuseStep 7066379 = 10599569) B10599569
theorem B3724393 : Blo 1742572 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B22336721 : Blo 1742572 22336721 := bstep (se 2 (by rfl) ⟨8376270, by rfl⟩ : syracuseStep 22336721 = 16752541) B16752541
theorem B5584231 : Blo 1742572 5584231 := bstep (se 1 (by rfl) ⟨4188173, by rfl⟩ : syracuseStep 5584231 = 8376347) B8376347
theorem B14136905 : Blo 1742572 14136905 := bstep (se 2 (by rfl) ⟨5301339, by rfl⟩ : syracuseStep 14136905 = 10602679) B10602679
theorem B3921551 : Blo 1742572 3921551 := bstep (se 1 (by rfl) ⟨2941163, by rfl⟩ : syracuseStep 3921551 = 5882327) B5882327
theorem B5887727 : Blo 1742572 5887727 := bstep (se 1 (by rfl) ⟨4415795, by rfl⟩ : syracuseStep 5887727 = 8831591) B8831591
theorem B1742783 : Blo 1742572 1742783 := bstep (se 1 (by rfl) ⟨1307087, by rfl⟩ : syracuseStep 1742783 = 2614175) B2614175
theorem B1742975 : Blo 1742572 1742975 := bstep (se 1 (by rfl) ⟨1307231, by rfl⟩ : syracuseStep 1742975 = 2614463) B2614463
theorem B8378579 : Blo 1742572 8378579 := bstep (se 1 (by rfl) ⟨6283934, by rfl⟩ : syracuseStep 8378579 = 12567869) B12567869
theorem B1743071 : Blo 1742572 1743071 := bstep (se 1 (by rfl) ⟨1307303, by rfl⟩ : syracuseStep 1743071 = 2614607) B2614607
theorem B1743131 : Blo 1742572 1743131 := bstep (se 1 (by rfl) ⟨1307348, by rfl⟩ : syracuseStep 1743131 = 2614697) B2614697
theorem B3725615 : Blo 1742572 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B6895991 : Blo 1742572 6895991 := bstep (se 1 (by rfl) ⟨5171993, by rfl⟩ : syracuseStep 6895991 = 10343987) B10343987
theorem B1743231 : Blo 1742572 1743231 := bstep (se 1 (by rfl) ⟨1307423, by rfl⟩ : syracuseStep 1743231 = 2614847) B2614847
theorem B8829323 : Blo 1742572 8829323 := bstep (se 1 (by rfl) ⟨6621992, by rfl⟩ : syracuseStep 8829323 = 13243985) B13243985
theorem B16751123 : Blo 1742572 16751123 := bstep (se 1 (by rfl) ⟨12563342, by rfl⟩ : syracuseStep 16751123 = 25126685) B25126685
theorem B7551593 : Blo 1742572 7551593 := bstep (se 2 (by rfl) ⟨2831847, by rfl⟩ : syracuseStep 7551593 = 5663695) B5663695
theorem B1743471 : Blo 1742572 1743471 := bstep (se 1 (by rfl) ⟨1307603, by rfl⟩ : syracuseStep 1743471 = 2615207) B2615207
theorem B6617771 : Blo 1742572 6617771 := bstep (se 1 (by rfl) ⟨4963328, by rfl⟩ : syracuseStep 6617771 = 9926657) B9926657
theorem B5585591 : Blo 1742572 5585591 := bstep (se 1 (by rfl) ⟨4189193, by rfl⟩ : syracuseStep 5585591 = 8378387) B8378387
theorem B1743551 : Blo 1742572 1743551 := bstep (se 1 (by rfl) ⟨1307663, by rfl⟩ : syracuseStep 1743551 = 2615327) B2615327
theorem B1743855 : Blo 1742572 1743855 := bstep (se 1 (by rfl) ⟨1307891, by rfl⟩ : syracuseStep 1743855 = 2615783) B2615783
theorem B13245443 : Blo 1742572 13245443 := bstep (se 1 (by rfl) ⟨9934082, by rfl⟩ : syracuseStep 13245443 = 19868165) B19868165
theorem B1743975 : Blo 1742572 1743975 := bstep (se 1 (by rfl) ⟨1307981, by rfl⟩ : syracuseStep 1743975 = 2615963) B2615963
theorem B7068779 : Blo 1742572 7068779 := bstep (se 1 (by rfl) ⟨5301584, by rfl⟩ : syracuseStep 7068779 = 10603169) B10603169
theorem B1744123 : Blo 1742572 1744123 := bstep (se 1 (by rfl) ⟨1308092, by rfl⟩ : syracuseStep 1744123 = 2616185) B2616185
theorem B1744287 : Blo 1742572 1744287 := bstep (se 1 (by rfl) ⟨1308215, by rfl⟩ : syracuseStep 1744287 = 2616431) B2616431
theorem B1744351 : Blo 1742572 1744351 := bstep (se 1 (by rfl) ⟨1308263, by rfl⟩ : syracuseStep 1744351 = 2616527) B2616527
theorem B13245929 : Blo 1742572 13245929 := bstep (se 2 (by rfl) ⟨4967223, by rfl⟩ : syracuseStep 13245929 = 9934447) B9934447
theorem B15908399 : Blo 1742572 15908399 := bstep (se 1 (by rfl) ⟨11931299, by rfl⟩ : syracuseStep 15908399 = 23862599) B23862599
theorem B1744431 : Blo 1742572 1744431 := bstep (se 1 (by rfl) ⟨1308323, by rfl⟩ : syracuseStep 1744431 = 2616647) B2616647
theorem B5881679 : Blo 1742572 5881679 := bstep (se 1 (by rfl) ⟨4411259, by rfl⟩ : syracuseStep 5881679 = 8822519) B8822519
theorem B13246415 : Blo 1742572 13246415 := bstep (se 1 (by rfl) ⟨9934811, by rfl⟩ : syracuseStep 13246415 = 19869623) B19869623
theorem B7069751 : Blo 1742572 7069751 := bstep (se 1 (by rfl) ⟨5302313, by rfl⟩ : syracuseStep 7069751 = 10604627) B10604627
theorem B5587051 : Blo 1742572 5587051 := bstep (se 1 (by rfl) ⟨4190288, by rfl⟩ : syracuseStep 5587051 = 8380577) B8380577
theorem B4415867 : Blo 1742572 4415867 := bstep (se 1 (by rfl) ⟨3311900, by rfl⟩ : syracuseStep 4415867 = 6623801) B6623801
theorem B3924395 : Blo 1742572 3924395 := bstep (se 1 (by rfl) ⟨2943296, by rfl⟩ : syracuseStep 3924395 = 5886593) B5886593
theorem B4710919 : Blo 1742572 4710919 := bstep (se 1 (by rfl) ⟨3533189, by rfl⟩ : syracuseStep 4710919 = 7066379) B7066379
theorem B6620231 : Blo 1742572 6620231 := bstep (se 1 (by rfl) ⟨4965173, by rfl⟩ : syracuseStep 6620231 = 9930347) B9930347
theorem B2614367 : Blo 1742572 2614367 := bstep (se 1 (by rfl) ⟨1960775, by rfl⟩ : syracuseStep 2614367 = 3921551) B3921551
theorem B3925151 : Blo 1742572 3925151 := bstep (se 1 (by rfl) ⟨2943863, by rfl⟩ : syracuseStep 3925151 = 5887727) B5887727
theorem B5588435 : Blo 1742572 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B4965857 : Blo 1742572 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B4597327 : Blo 1742572 4597327 := bstep (se 1 (by rfl) ⟨3447995, by rfl⟩ : syracuseStep 4597327 = 6895991) B6895991
theorem B11167415 : Blo 1742572 11167415 := bstep (se 1 (by rfl) ⟨8375561, by rfl⟩ : syracuseStep 11167415 = 16751123) B16751123
theorem B80480087 : Blo 1742572 80480087 := bstep (se 1 (by rfl) ⟨60360065, by rfl⟩ : syracuseStep 80480087 = 120720131) B120720131
theorem B100501397 : Blo 1742572 100501397 := bstep (se 6 (by rfl) ⟨2355501, by rfl⟩ : syracuseStep 100501397 = 4711003) B4711003
theorem B2615273 : Blo 1742572 2615273 := bstep (se 2 (by rfl) ⟨980727, by rfl⟩ : syracuseStep 2615273 = 1961455) B1961455
theorem B4712519 : Blo 1742572 4712519 := bstep (se 1 (by rfl) ⟨3534389, by rfl⟩ : syracuseStep 4712519 = 7068779) B7068779
theorem B49678811 : Blo 1742572 49678811 := bstep (se 1 (by rfl) ⟨37259108, by rfl⟩ : syracuseStep 49678811 = 74518217) B74518217
theorem B6621857 : Blo 1742572 6621857 := bstep (se 2 (by rfl) ⟨2483196, by rfl⟩ : syracuseStep 6621857 = 4966393) B4966393
theorem B2615999 : Blo 1742572 2615999 := bstep (se 1 (by rfl) ⟨1961999, by rfl⟩ : syracuseStep 2615999 = 3923999) B3923999
theorem B1960987 : Blo 1742572 1960987 := bstep (se 1 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 1960987 = 2941481) B2941481
theorem B11168873 : Blo 1742572 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B3976607 : Blo 1742572 3976607 := bstep (se 1 (by rfl) ⟨2982455, by rfl⟩ : syracuseStep 3976607 = 5964911) B5964911
theorem B9424603 : Blo 1742572 9424603 := bstep (se 1 (by rfl) ⟨7068452, by rfl⟩ : syracuseStep 9424603 = 14136905) B14136905
theorem B1961887 : Blo 1742572 1961887 := bstep (se 1 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 1961887 = 2942831) B2942831
theorem B25464817 : Blo 1742572 25464817 := bstep (se 2 (by rfl) ⟨9549306, by rfl⟩ : syracuseStep 25464817 = 19098613) B19098613
theorem B8827055 : Blo 1742572 8827055 := bstep (se 1 (by rfl) ⟨6620291, by rfl⟩ : syracuseStep 8827055 = 13240583) B13240583
theorem B1962175 : Blo 1742572 1962175 := bstep (se 1 (by rfl) ⟨1471631, by rfl⟩ : syracuseStep 1962175 = 2943263) B2943263
theorem B5886215 : Blo 1742572 5886215 := bstep (se 1 (by rfl) ⟨4414661, by rfl⟩ : syracuseStep 5886215 = 8829323) B8829323
theorem B5034395 : Blo 1742572 5034395 := bstep (se 1 (by rfl) ⟨3775796, by rfl⟩ : syracuseStep 5034395 = 7551593) B7551593
theorem B4411847 : Blo 1742572 4411847 := bstep (se 1 (by rfl) ⟨3308885, by rfl⟩ : syracuseStep 4411847 = 6617771) B6617771
theorem B3723727 : Blo 1742572 3723727 := bstep (se 1 (by rfl) ⟨2792795, by rfl⟩ : syracuseStep 3723727 = 5585591) B5585591
theorem B29782565 : Blo 1742572 29782565 := bstep (se 4 (by rfl) ⟨2792115, by rfl⟩ : syracuseStep 29782565 = 5584231) B5584231
theorem B13243013 : Blo 1742572 13243013 := bstep (se 4 (by rfl) ⟨1241532, by rfl⟩ : syracuseStep 13243013 = 2483065) B2483065
theorem B3978067 : Blo 1742572 3978067 := bstep (se 1 (by rfl) ⟨2983550, by rfl⟩ : syracuseStep 3978067 = 5967101) B5967101
theorem B24195943 : Blo 1742572 24195943 := bstep (se 1 (by rfl) ⟨18146957, by rfl⟩ : syracuseStep 24195943 = 36293915) B36293915
theorem B10605599 : Blo 1742572 10605599 := bstep (se 1 (by rfl) ⟨7954199, by rfl⟩ : syracuseStep 10605599 = 15908399) B15908399
theorem B3921119 : Blo 1742572 3921119 := bstep (se 1 (by rfl) ⟨2940839, by rfl⟩ : syracuseStep 3921119 = 5881679) B5881679
theorem B4412839 : Blo 1742572 4412839 := bstep (se 1 (by rfl) ⟨3309629, by rfl⟩ : syracuseStep 4412839 = 6619259) B6619259
theorem B29800061 : Blo 1742572 29800061 := bstep (se 3 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 29800061 = 11175023) B11175023
theorem B3921785 : Blo 1742572 3921785 := bstep (se 2 (by rfl) ⟨1470669, by rfl⟩ : syracuseStep 3921785 = 2941339) B2941339
theorem B28268615 : Blo 1742572 28268615 := bstep (se 1 (by rfl) ⟨21201461, by rfl⟩ : syracuseStep 28268615 = 42402923) B42402923
theorem B9934973 : Blo 1742572 9934973 := bstep (se 3 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 9934973 = 3725615) B3725615
theorem B14891147 : Blo 1742572 14891147 := bstep (se 1 (by rfl) ⟨11168360, by rfl⟩ : syracuseStep 14891147 = 22336721) B22336721
theorem B4413791 : Blo 1742572 4413791 := bstep (se 1 (by rfl) ⟨3310343, by rfl⟩ : syracuseStep 4413791 = 6620687) B6620687
theorem B1743259 : Blo 1742572 1743259 := bstep (se 1 (by rfl) ⟨1307444, by rfl⟩ : syracuseStep 1743259 = 2614889) B2614889
theorem B3922559 : Blo 1742572 3922559 := bstep (se 1 (by rfl) ⟨2941919, by rfl⟩ : syracuseStep 3922559 = 5883839) B5883839
theorem B5585719 : Blo 1742572 5585719 := bstep (se 1 (by rfl) ⟨4189289, by rfl⟩ : syracuseStep 5585719 = 8378579) B8378579
theorem B12737351 : Blo 1742572 12737351 := bstep (se 1 (by rfl) ⟨9553013, by rfl⟩ : syracuseStep 12737351 = 19106027) B19106027
theorem B4963169 : Blo 1742572 4963169 := bstep (se 2 (by rfl) ⟨1861188, by rfl⟩ : syracuseStep 4963169 = 3722377) B3722377
theorem B15899611 : Blo 1742572 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B107371585 : Blo 1742572 107371585 := bstep (se 2 (by rfl) ⟨40264344, by rfl⟩ : syracuseStep 107371585 = 80528689) B80528689
theorem B4414601 : Blo 1742572 4414601 := bstep (se 2 (by rfl) ⟨1655475, by rfl⟩ : syracuseStep 4414601 = 3310951) B3310951
theorem B2481311 : Blo 1742572 2481311 := bstep (se 1 (by rfl) ⟨1860983, by rfl⟩ : syracuseStep 2481311 = 3721967) B3721967
theorem B1744031 : Blo 1742572 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B2481391 : Blo 1742572 2481391 := bstep (se 1 (by rfl) ⟨1861043, by rfl⟩ : syracuseStep 2481391 = 3722087) B3722087
theorem B4963625 : Blo 1742572 4963625 := bstep (se 2 (by rfl) ⟨1861359, by rfl⟩ : syracuseStep 4963625 = 3722719) B3722719
theorem B3923279 : Blo 1742572 3923279 := bstep (se 1 (by rfl) ⟨2942459, by rfl⟩ : syracuseStep 3923279 = 5884919) B5884919
theorem B8830295 : Blo 1742572 8830295 := bstep (se 1 (by rfl) ⟨6622721, by rfl⟩ : syracuseStep 8830295 = 13245443) B13245443
theorem B1744283 : Blo 1742572 1744283 := bstep (se 1 (by rfl) ⟨1308212, by rfl⟩ : syracuseStep 1744283 = 2616425) B2616425
theorem B3923423 : Blo 1742572 3923423 := bstep (se 1 (by rfl) ⟨2942567, by rfl⟩ : syracuseStep 3923423 = 5885135) B5885135
theorem B8830619 : Blo 1742572 8830619 := bstep (se 1 (by rfl) ⟨6622964, by rfl⟩ : syracuseStep 8830619 = 13245929) B13245929
theorem B1744543 : Blo 1742572 1744543 := bstep (se 1 (by rfl) ⟨1308407, by rfl⟩ : syracuseStep 1744543 = 2616815) B2616815
theorem B63610535 : Blo 1742572 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B2940799 : Blo 1742572 2940799 := bstep (se 1 (by rfl) ⟨2205599, by rfl⟩ : syracuseStep 2940799 = 4411199) B4411199
theorem B8830943 : Blo 1742572 8830943 := bstep (se 1 (by rfl) ⟨6623207, by rfl⟩ : syracuseStep 8830943 = 13246415) B13246415
theorem B3924143 : Blo 1742572 3924143 := bstep (se 1 (by rfl) ⟨2943107, by rfl⟩ : syracuseStep 3924143 = 5886215) B5886215
theorem B75382973 : Blo 1742572 75382973 := bstep (se 3 (by rfl) ⟨14134307, by rfl⟩ : syracuseStep 75382973 = 28268615) B28268615
theorem B2941231 : Blo 1742572 2941231 := bstep (se 1 (by rfl) ⟨2205923, by rfl⟩ : syracuseStep 2941231 = 4411847) B4411847
theorem B4964969 : Blo 1742572 4964969 := bstep (se 2 (by rfl) ⟨1861863, by rfl⟩ : syracuseStep 4964969 = 3723727) B3723727
theorem B7070399 : Blo 1742572 7070399 := bstep (se 1 (by rfl) ⟨5302799, by rfl⟩ : syracuseStep 7070399 = 10605599) B10605599
theorem B2614079 : Blo 1742572 2614079 := bstep (se 1 (by rfl) ⟨1960559, by rfl⟩ : syracuseStep 2614079 = 3921119) B3921119
theorem B3310571 : Blo 1742572 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B7447625 : Blo 1742572 7447625 := bstep (se 2 (by rfl) ⟨2792859, by rfl⟩ : syracuseStep 7447625 = 5585719) B5585719
theorem B19866707 : Blo 1742572 19866707 := bstep (se 1 (by rfl) ⟨14900030, by rfl⟩ : syracuseStep 19866707 = 29800061) B29800061
theorem B32261257 : Blo 1742572 32261257 := bstep (se 2 (by rfl) ⟨12097971, by rfl⟩ : syracuseStep 32261257 = 24195943) B24195943
theorem B2614523 : Blo 1742572 2614523 := bstep (se 1 (by rfl) ⟨1960892, by rfl⟩ : syracuseStep 2614523 = 3921785) B3921785
theorem B2614649 : Blo 1742572 2614649 := bstep (se 2 (by rfl) ⟨980493, by rfl⟩ : syracuseStep 2614649 = 1960987) B1960987
theorem B2942527 : Blo 1742572 2942527 := bstep (se 1 (by rfl) ⟨2206895, by rfl⟩ : syracuseStep 2942527 = 4413791) B4413791
theorem B2615039 : Blo 1742572 2615039 := bstep (se 1 (by rfl) ⟨1961279, by rfl⟩ : syracuseStep 2615039 = 3922559) B3922559
theorem B5883785 : Blo 1742572 5883785 := bstep (se 2 (by rfl) ⟨2206419, by rfl⟩ : syracuseStep 5883785 = 4412839) B4412839
theorem B2943067 : Blo 1742572 2943067 := bstep (se 1 (by rfl) ⟨2207300, by rfl⟩ : syracuseStep 2943067 = 4414601) B4414601
theorem B6129769 : Blo 1742572 6129769 := bstep (se 2 (by rfl) ⟨2298663, by rfl⟩ : syracuseStep 6129769 = 4597327) B4597327
theorem B2615519 : Blo 1742572 2615519 := bstep (se 1 (by rfl) ⟨1961639, by rfl⟩ : syracuseStep 2615519 = 3923279) B3923279
theorem B2615615 : Blo 1742572 2615615 := bstep (se 1 (by rfl) ⟨1961711, by rfl⟩ : syracuseStep 2615615 = 3923423) B3923423
theorem B2615849 : Blo 1742572 2615849 := bstep (se 2 (by rfl) ⟨980943, by rfl⟩ : syracuseStep 2615849 = 1961887) B1961887
theorem B4713167 : Blo 1742572 4713167 := bstep (se 1 (by rfl) ⟨3534875, by rfl⟩ : syracuseStep 4713167 = 7069751) B7069751
theorem B5884703 : Blo 1742572 5884703 := bstep (se 1 (by rfl) ⟨4413527, by rfl⟩ : syracuseStep 5884703 = 8827055) B8827055
theorem B7449401 : Blo 1742572 7449401 := bstep (se 2 (by rfl) ⟨2793525, by rfl⟩ : syracuseStep 7449401 = 5587051) B5587051
theorem B2943911 : Blo 1742572 2943911 := bstep (se 1 (by rfl) ⟨2207933, by rfl⟩ : syracuseStep 2943911 = 4415867) B4415867
theorem B2616233 : Blo 1742572 2616233 := bstep (se 2 (by rfl) ⟨981087, by rfl⟩ : syracuseStep 2616233 = 1962175) B1962175
theorem B2616263 : Blo 1742572 2616263 := bstep (se 1 (by rfl) ⟨1962197, by rfl⟩ : syracuseStep 2616263 = 3924395) B3924395
theorem B2616767 : Blo 1742572 2616767 := bstep (se 1 (by rfl) ⟨1962575, by rfl⟩ : syracuseStep 2616767 = 3925151) B3925151
theorem B10604285 : Blo 1742572 10604285 := bstep (se 3 (by rfl) ⟨1988303, by rfl⟩ : syracuseStep 10604285 = 3976607) B3976607
theorem B5304089 : Blo 1742572 5304089 := bstep (se 2 (by rfl) ⟨1989033, by rfl⟩ : syracuseStep 5304089 = 3978067) B3978067
theorem B53653391 : Blo 1742572 53653391 := bstep (se 1 (by rfl) ⟨40240043, by rfl⟩ : syracuseStep 53653391 = 80480087) B80480087
theorem B3141679 : Blo 1742572 3141679 := bstep (se 1 (by rfl) ⟨2356259, by rfl⟩ : syracuseStep 3141679 = 4712519) B4712519
theorem B6623315 : Blo 1742572 6623315 := bstep (se 1 (by rfl) ⟨4967486, by rfl⟩ : syracuseStep 6623315 = 9934973) B9934973
theorem B8491567 : Blo 1742572 8491567 := bstep (se 1 (by rfl) ⟨6368675, by rfl⟩ : syracuseStep 8491567 = 12737351) B12737351
theorem B5886863 : Blo 1742572 5886863 := bstep (se 1 (by rfl) ⟨4415147, by rfl⟩ : syracuseStep 5886863 = 8830295) B8830295
theorem B5887079 : Blo 1742572 5887079 := bstep (se 1 (by rfl) ⟨4415309, by rfl⟩ : syracuseStep 5887079 = 8830619) B8830619
theorem B42407023 : Blo 1742572 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B3921065 : Blo 1742572 3921065 := bstep (se 2 (by rfl) ⟨1470399, by rfl⟩ : syracuseStep 3921065 = 2940799) B2940799
theorem B5887295 : Blo 1742572 5887295 := bstep (se 1 (by rfl) ⟨4415471, by rfl⟩ : syracuseStep 5887295 = 8830943) B8830943
theorem B33953089 : Blo 1742572 33953089 := bstep (se 2 (by rfl) ⟨12732408, by rfl⟩ : syracuseStep 33953089 = 25464817) B25464817
theorem B3356263 : Blo 1742572 3356263 := bstep (se 1 (by rfl) ⟨2517197, by rfl⟩ : syracuseStep 3356263 = 5034395) B5034395
theorem B19855043 : Blo 1742572 19855043 := bstep (se 1 (by rfl) ⟨14891282, by rfl⟩ : syracuseStep 19855043 = 29782565) B29782565
theorem B6616829 : Blo 1742572 6616829 := bstep (se 3 (by rfl) ⟨1240655, by rfl⟩ : syracuseStep 6616829 = 2481311) B2481311
theorem B8828675 : Blo 1742572 8828675 := bstep (se 1 (by rfl) ⟨6621506, by rfl⟩ : syracuseStep 8828675 = 13243013) B13243013
theorem B6281225 : Blo 1742572 6281225 := bstep (se 2 (by rfl) ⟨2355459, by rfl⟩ : syracuseStep 6281225 = 4710919) B4710919
theorem B4413487 : Blo 1742572 4413487 := bstep (se 1 (by rfl) ⟨3310115, by rfl⟩ : syracuseStep 4413487 = 6620231) B6620231
theorem B1742911 : Blo 1742572 1742911 := bstep (se 1 (by rfl) ⟨1307183, by rfl⟩ : syracuseStep 1742911 = 2614367) B2614367
theorem B3725623 : Blo 1742572 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B7444943 : Blo 1742572 7444943 := bstep (se 1 (by rfl) ⟨5583707, by rfl⟩ : syracuseStep 7444943 = 11167415) B11167415
theorem B67000931 : Blo 1742572 67000931 := bstep (se 1 (by rfl) ⟨50250698, by rfl⟩ : syracuseStep 67000931 = 100501397) B100501397
theorem B21199481 : Blo 1742572 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B1743515 : Blo 1742572 1743515 := bstep (se 1 (by rfl) ⟨1307636, by rfl⟩ : syracuseStep 1743515 = 2615273) B2615273
theorem B143162113 : Blo 1742572 143162113 := bstep (se 2 (by rfl) ⟨53685792, by rfl⟩ : syracuseStep 143162113 = 107371585) B107371585
theorem B9927431 : Blo 1742572 9927431 := bstep (se 1 (by rfl) ⟨7445573, by rfl⟩ : syracuseStep 9927431 = 14891147) B14891147
theorem B33119207 : Blo 1742572 33119207 := bstep (se 1 (by rfl) ⟨24839405, by rfl⟩ : syracuseStep 33119207 = 49678811) B49678811
theorem B3308521 : Blo 1742572 3308521 := bstep (se 2 (by rfl) ⟨1240695, by rfl⟩ : syracuseStep 3308521 = 2481391) B2481391
theorem B4414571 : Blo 1742572 4414571 := bstep (se 1 (by rfl) ⟨3310928, by rfl⟩ : syracuseStep 4414571 = 6621857) B6621857
theorem B1743999 : Blo 1742572 1743999 := bstep (se 1 (by rfl) ⟨1307999, by rfl⟩ : syracuseStep 1743999 = 2615999) B2615999
theorem B3308779 : Blo 1742572 3308779 := bstep (se 1 (by rfl) ⟨2481584, by rfl⟩ : syracuseStep 3308779 = 4963169) B4963169
theorem B7445915 : Blo 1742572 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B3309083 : Blo 1742572 3309083 := bstep (se 1 (by rfl) ⟨2481812, by rfl⟩ : syracuseStep 3309083 = 4963625) B4963625
theorem B12566137 : Blo 1742572 12566137 := bstep (se 2 (by rfl) ⟨4712301, by rfl⟩ : syracuseStep 12566137 = 9424603) B9424603
theorem B4415543 : Blo 1742572 4415543 := bstep (se 1 (by rfl) ⟨3311657, by rfl⟩ : syracuseStep 4415543 = 6623315) B6623315
theorem B3924089 : Blo 1742572 3924089 := bstep (se 2 (by rfl) ⟨1471533, by rfl⟩ : syracuseStep 3924089 = 2943067) B2943067
theorem B3309979 : Blo 1742572 3309979 := bstep (se 1 (by rfl) ⟨2482484, by rfl⟩ : syracuseStep 3309979 = 4964969) B4964969
theorem B3924575 : Blo 1742572 3924575 := bstep (se 1 (by rfl) ⟨2943431, by rfl⟩ : syracuseStep 3924575 = 5886863) B5886863
theorem B4965083 : Blo 1742572 4965083 := bstep (se 1 (by rfl) ⟨3723812, by rfl⟩ : syracuseStep 4965083 = 7447625) B7447625
theorem B11322089 : Blo 1742572 11322089 := bstep (se 2 (by rfl) ⟨4245783, by rfl⟩ : syracuseStep 11322089 = 8491567) B8491567
theorem B3924719 : Blo 1742572 3924719 := bstep (se 1 (by rfl) ⟨2943539, by rfl⟩ : syracuseStep 3924719 = 5887079) B5887079
theorem B2614043 : Blo 1742572 2614043 := bstep (se 1 (by rfl) ⟨1960532, by rfl⟩ : syracuseStep 2614043 = 3921065) B3921065
theorem B3924863 : Blo 1742572 3924863 := bstep (se 1 (by rfl) ⟨2943647, by rfl⟩ : syracuseStep 3924863 = 5887295) B5887295
theorem B190882817 : Blo 1742572 190882817 := bstep (se 2 (by rfl) ⟨71581056, by rfl⟩ : syracuseStep 190882817 = 143162113) B143162113
theorem B4187483 : Blo 1742572 4187483 := bstep (se 1 (by rfl) ⟨3140612, by rfl⟩ : syracuseStep 4187483 = 6281225) B6281225
theorem B56542697 : Blo 1742572 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B14132987 : Blo 1742572 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B45270785 : Blo 1742572 45270785 := bstep (se 2 (by rfl) ⟨16976544, by rfl⟩ : syracuseStep 45270785 = 33953089) B33953089
theorem B4966267 : Blo 1742572 4966267 := bstep (se 1 (by rfl) ⟨3724700, by rfl⟩ : syracuseStep 4966267 = 7449401) B7449401
theorem B12568445 : Blo 1742572 12568445 := bstep (se 3 (by rfl) ⟨2356583, by rfl⟩ : syracuseStep 12568445 = 4713167) B4713167
theorem B22079471 : Blo 1742572 22079471 := bstep (se 1 (by rfl) ⟨16559603, by rfl⟩ : syracuseStep 22079471 = 33119207) B33119207
theorem B2943047 : Blo 1742572 2943047 := bstep (se 1 (by rfl) ⟨2207285, by rfl⟩ : syracuseStep 2943047 = 4414571) B4414571
theorem B4475017 : Blo 1742572 4475017 := bstep (se 2 (by rfl) ⟨1678131, by rfl⟩ : syracuseStep 4475017 = 3356263) B3356263
theorem B16754849 : Blo 1742572 16754849 := bstep (se 2 (by rfl) ⟨6283068, by rfl⟩ : syracuseStep 16754849 = 12566137) B12566137
theorem B2206055 : Blo 1742572 2206055 := bstep (se 1 (by rfl) ⟨1654541, by rfl⟩ : syracuseStep 2206055 = 3309083) B3309083
theorem B35768927 : Blo 1742572 35768927 := bstep (se 1 (by rfl) ⟨26826695, by rfl⟩ : syracuseStep 35768927 = 53653391) B53653391
theorem B4188905 : Blo 1742572 4188905 := bstep (se 2 (by rfl) ⟨1570839, by rfl⟩ : syracuseStep 4188905 = 3141679) B3141679
theorem B5884649 : Blo 1742572 5884649 := bstep (se 2 (by rfl) ⟨2206743, by rfl⟩ : syracuseStep 5884649 = 4413487) B4413487
theorem B2616095 : Blo 1742572 2616095 := bstep (se 1 (by rfl) ⟨1962071, by rfl⟩ : syracuseStep 2616095 = 3924143) B3924143
theorem B4967497 : Blo 1742572 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B4713599 : Blo 1742572 4713599 := bstep (se 1 (by rfl) ⟨3535199, by rfl⟩ : syracuseStep 4713599 = 7070399) B7070399
theorem B4411219 : Blo 1742572 4411219 := bstep (se 1 (by rfl) ⟨3308414, by rfl⟩ : syracuseStep 4411219 = 6616829) B6616829
theorem B5885783 : Blo 1742572 5885783 := bstep (se 1 (by rfl) ⟨4414337, by rfl⟩ : syracuseStep 5885783 = 8828675) B8828675
theorem B4411361 : Blo 1742572 4411361 := bstep (se 2 (by rfl) ⟨1654260, by rfl⟩ : syracuseStep 4411361 = 3308521) B3308521
theorem B4411705 : Blo 1742572 4411705 := bstep (se 2 (by rfl) ⟨1654389, by rfl⟩ : syracuseStep 4411705 = 3308779) B3308779
theorem B44667287 : Blo 1742572 44667287 := bstep (se 1 (by rfl) ⟨33500465, by rfl⟩ : syracuseStep 44667287 = 67000931) B67000931
theorem B1962607 : Blo 1742572 1962607 := bstep (se 1 (by rfl) ⟨1471955, by rfl⟩ : syracuseStep 1962607 = 2943911) B2943911
theorem B3536059 : Blo 1742572 3536059 := bstep (se 1 (by rfl) ⟨2652044, by rfl⟩ : syracuseStep 3536059 = 5304089) B5304089
theorem B8828189 : Blo 1742572 8828189 := bstep (se 3 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 8828189 = 3310571) B3310571
theorem B50255315 : Blo 1742572 50255315 := bstep (se 1 (by rfl) ⟨37691486, by rfl⟩ : syracuseStep 50255315 = 75382973) B75382973
theorem B8173025 : Blo 1742572 8173025 := bstep (se 2 (by rfl) ⟨3064884, by rfl⟩ : syracuseStep 8173025 = 6129769) B6129769
theorem B3921641 : Blo 1742572 3921641 := bstep (se 2 (by rfl) ⟨1470615, by rfl⟩ : syracuseStep 3921641 = 2941231) B2941231
theorem B1742719 : Blo 1742572 1742719 := bstep (se 1 (by rfl) ⟨1307039, by rfl⟩ : syracuseStep 1742719 = 2614079) B2614079
theorem B13244471 : Blo 1742572 13244471 := bstep (se 1 (by rfl) ⟨9933353, by rfl⟩ : syracuseStep 13244471 = 19866707) B19866707
theorem B1743015 : Blo 1742572 1743015 := bstep (se 1 (by rfl) ⟨1307261, by rfl⟩ : syracuseStep 1743015 = 2614523) B2614523
theorem B1743099 : Blo 1742572 1743099 := bstep (se 1 (by rfl) ⟨1307324, by rfl⟩ : syracuseStep 1743099 = 2614649) B2614649
theorem B13236695 : Blo 1742572 13236695 := bstep (se 1 (by rfl) ⟨9927521, by rfl⟩ : syracuseStep 13236695 = 19855043) B19855043
theorem B1743359 : Blo 1742572 1743359 := bstep (se 1 (by rfl) ⟨1307519, by rfl⟩ : syracuseStep 1743359 = 2615039) B2615039
theorem B3922523 : Blo 1742572 3922523 := bstep (se 1 (by rfl) ⟨2941892, by rfl⟩ : syracuseStep 3922523 = 5883785) B5883785
theorem B1743679 : Blo 1742572 1743679 := bstep (se 1 (by rfl) ⟨1307759, by rfl⟩ : syracuseStep 1743679 = 2615519) B2615519
theorem B43015009 : Blo 1742572 43015009 := bstep (se 2 (by rfl) ⟨16130628, by rfl⟩ : syracuseStep 43015009 = 32261257) B32261257
theorem B1743743 : Blo 1742572 1743743 := bstep (se 1 (by rfl) ⟨1307807, by rfl⟩ : syracuseStep 1743743 = 2615615) B2615615
theorem B4963295 : Blo 1742572 4963295 := bstep (se 1 (by rfl) ⟨3722471, by rfl⟩ : syracuseStep 4963295 = 7444943) B7444943
theorem B1743899 : Blo 1742572 1743899 := bstep (se 1 (by rfl) ⟨1307924, by rfl⟩ : syracuseStep 1743899 = 2615849) B2615849
theorem B6618287 : Blo 1742572 6618287 := bstep (se 1 (by rfl) ⟨4963715, by rfl⟩ : syracuseStep 6618287 = 9927431) B9927431
theorem B3923135 : Blo 1742572 3923135 := bstep (se 1 (by rfl) ⟨2942351, by rfl⟩ : syracuseStep 3923135 = 5884703) B5884703
theorem B1744155 : Blo 1742572 1744155 := bstep (se 1 (by rfl) ⟨1308116, by rfl⟩ : syracuseStep 1744155 = 2616233) B2616233
theorem B1744175 : Blo 1742572 1744175 := bstep (se 1 (by rfl) ⟨1308131, by rfl⟩ : syracuseStep 1744175 = 2616263) B2616263
theorem B3923369 : Blo 1742572 3923369 := bstep (se 2 (by rfl) ⟨1471263, by rfl⟩ : syracuseStep 3923369 = 2942527) B2942527
theorem B4963943 : Blo 1742572 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B1744511 : Blo 1742572 1744511 := bstep (se 1 (by rfl) ⟨1308383, by rfl⟩ : syracuseStep 1744511 = 2616767) B2616767
theorem B7069523 : Blo 1742572 7069523 := bstep (se 1 (by rfl) ⟨5302142, by rfl⟩ : syracuseStep 7069523 = 10604285) B10604285
theorem B29778191 : Blo 1742572 29778191 := bstep (se 1 (by rfl) ⟨22333643, by rfl⟩ : syracuseStep 29778191 = 44667287) B44667287
theorem B5882273 : Blo 1742572 5882273 := bstep (se 2 (by rfl) ⟨2205852, by rfl⟩ : syracuseStep 5882273 = 4411705) B4411705
theorem B3310055 : Blo 1742572 3310055 := bstep (se 1 (by rfl) ⟨2482541, by rfl⟩ : syracuseStep 3310055 = 4965083) B4965083
theorem B127255211 : Blo 1742572 127255211 := bstep (se 1 (by rfl) ⟨95441408, by rfl⟩ : syracuseStep 127255211 = 190882817) B190882817
theorem B5882813 : Blo 1742572 5882813 := bstep (se 3 (by rfl) ⟨1103027, by rfl⟩ : syracuseStep 5882813 = 2206055) B2206055
theorem B5448683 : Blo 1742572 5448683 := bstep (se 1 (by rfl) ⟨4086512, by rfl⟩ : syracuseStep 5448683 = 8173025) B8173025
theorem B57353345 : Blo 1742572 57353345 := bstep (se 2 (by rfl) ⟨21507504, by rfl⟩ : syracuseStep 57353345 = 43015009) B43015009
theorem B2614427 : Blo 1742572 2614427 := bstep (se 1 (by rfl) ⟨1960820, by rfl⟩ : syracuseStep 2614427 = 3921641) B3921641
theorem B9421991 : Blo 1742572 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B8824463 : Blo 1742572 8824463 := bstep (se 1 (by rfl) ⟨6618347, by rfl⟩ : syracuseStep 8824463 = 13236695) B13236695
theorem B2615015 : Blo 1742572 2615015 := bstep (se 1 (by rfl) ⟨1961261, by rfl⟩ : syracuseStep 2615015 = 3922523) B3922523
theorem B2615423 : Blo 1742572 2615423 := bstep (se 1 (by rfl) ⟨1961567, by rfl⟩ : syracuseStep 2615423 = 3923135) B3923135
theorem B18852061 : Blo 1742572 18852061 := bstep (se 3 (by rfl) ⟨3534761, by rfl⟩ : syracuseStep 18852061 = 7069523) B7069523
theorem B2615579 : Blo 1742572 2615579 := bstep (se 1 (by rfl) ⟨1961684, by rfl⟩ : syracuseStep 2615579 = 3923369) B3923369
theorem B235514357 : Blo 1742572 235514357 := bstep (se 5 (by rfl) ⟨11039735, by rfl⟩ : syracuseStep 235514357 = 22079471) B22079471
theorem B6621689 : Blo 1742572 6621689 := bstep (se 2 (by rfl) ⟨2483133, by rfl⟩ : syracuseStep 6621689 = 4966267) B4966267
theorem B2943695 : Blo 1742572 2943695 := bstep (se 1 (by rfl) ⟨2207771, by rfl⟩ : syracuseStep 2943695 = 4415543) B4415543
theorem B2616059 : Blo 1742572 2616059 := bstep (se 1 (by rfl) ⟨1962044, by rfl⟩ : syracuseStep 2616059 = 3924089) B3924089
theorem B5966689 : Blo 1742572 5966689 := bstep (se 2 (by rfl) ⟨2237508, by rfl⟩ : syracuseStep 5966689 = 4475017) B4475017
theorem B2616383 : Blo 1742572 2616383 := bstep (se 1 (by rfl) ⟨1962287, by rfl⟩ : syracuseStep 2616383 = 3924575) B3924575
theorem B7548059 : Blo 1742572 7548059 := bstep (se 1 (by rfl) ⟨5661044, by rfl⟩ : syracuseStep 7548059 = 11322089) B11322089
theorem B2616479 : Blo 1742572 2616479 := bstep (se 1 (by rfl) ⟨1962359, by rfl⟩ : syracuseStep 2616479 = 3924719) B3924719
theorem B2616575 : Blo 1742572 2616575 := bstep (se 1 (by rfl) ⟨1962431, by rfl⟩ : syracuseStep 2616575 = 3924863) B3924863
theorem B2616809 : Blo 1742572 2616809 := bstep (se 2 (by rfl) ⟨981303, by rfl⟩ : syracuseStep 2616809 = 1962607) B1962607
theorem B5885459 : Blo 1742572 5885459 := bstep (se 1 (by rfl) ⟨4414094, by rfl⟩ : syracuseStep 5885459 = 8828189) B8828189
theorem B37695131 : Blo 1742572 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B1962031 : Blo 1742572 1962031 := bstep (se 1 (by rfl) ⟨1471523, by rfl⟩ : syracuseStep 1962031 = 2943047) B2943047
theorem B6623329 : Blo 1742572 6623329 := bstep (se 2 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 6623329 = 4967497) B4967497
theorem B11169899 : Blo 1742572 11169899 := bstep (se 1 (by rfl) ⟨8377424, by rfl⟩ : syracuseStep 11169899 = 16754849) B16754849
theorem B4714745 : Blo 1742572 4714745 := bstep (se 2 (by rfl) ⟨1768029, by rfl⟩ : syracuseStep 4714745 = 3536059) B3536059
theorem B120722093 : Blo 1742572 120722093 := bstep (se 3 (by rfl) ⟨22635392, by rfl⟩ : syracuseStep 120722093 = 45270785) B45270785
theorem B3142399 : Blo 1742572 3142399 := bstep (se 1 (by rfl) ⟨2356799, by rfl⟩ : syracuseStep 3142399 = 4713599) B4713599
theorem B4412191 : Blo 1742572 4412191 := bstep (se 1 (by rfl) ⟨3309143, by rfl⟩ : syracuseStep 4412191 = 6618287) B6618287
theorem B1742695 : Blo 1742572 1742695 := bstep (se 1 (by rfl) ⟨1307021, by rfl⟩ : syracuseStep 1742695 = 2614043) B2614043
theorem B4413305 : Blo 1742572 4413305 := bstep (se 2 (by rfl) ⟨1654989, by rfl⟩ : syracuseStep 4413305 = 3309979) B3309979
theorem B2791655 : Blo 1742572 2791655 := bstep (se 1 (by rfl) ⟨2093741, by rfl⟩ : syracuseStep 2791655 = 4187483) B4187483
theorem B33503543 : Blo 1742572 33503543 := bstep (se 1 (by rfl) ⟨25127657, by rfl⟩ : syracuseStep 33503543 = 50255315) B50255315
theorem B8378963 : Blo 1742572 8378963 := bstep (se 1 (by rfl) ⟨6284222, by rfl⟩ : syracuseStep 8378963 = 12568445) B12568445
theorem B8829647 : Blo 1742572 8829647 := bstep (se 1 (by rfl) ⟨6622235, by rfl⟩ : syracuseStep 8829647 = 13244471) B13244471
theorem B13237181 : Blo 1742572 13237181 := bstep (se 3 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 13237181 = 4963943) B4963943
theorem B23845951 : Blo 1742572 23845951 := bstep (se 1 (by rfl) ⟨17884463, by rfl⟩ : syracuseStep 23845951 = 35768927) B35768927
theorem B2792603 : Blo 1742572 2792603 := bstep (se 1 (by rfl) ⟨2094452, by rfl⟩ : syracuseStep 2792603 = 4188905) B4188905
theorem B3923099 : Blo 1742572 3923099 := bstep (se 1 (by rfl) ⟨2942324, by rfl⟩ : syracuseStep 3923099 = 5884649) B5884649
theorem B1744063 : Blo 1742572 1744063 := bstep (se 1 (by rfl) ⟨1308047, by rfl⟩ : syracuseStep 1744063 = 2616095) B2616095
theorem B3308863 : Blo 1742572 3308863 := bstep (se 1 (by rfl) ⟨2481647, by rfl⟩ : syracuseStep 3308863 = 4963295) B4963295
theorem B5881625 : Blo 1742572 5881625 := bstep (se 2 (by rfl) ⟨2205609, by rfl⟩ : syracuseStep 5881625 = 4411219) B4411219
theorem B3923855 : Blo 1742572 3923855 := bstep (se 1 (by rfl) ⟨2942891, by rfl⟩ : syracuseStep 3923855 = 5885783) B5885783
theorem B2940907 : Blo 1742572 2940907 := bstep (se 1 (by rfl) ⟨2205680, by rfl⟩ : syracuseStep 2940907 = 4411361) B4411361
theorem B7446599 : Blo 1742572 7446599 := bstep (se 1 (by rfl) ⟨5584949, by rfl⟩ : syracuseStep 7446599 = 11169899) B11169899
theorem B8831105 : Blo 1742572 8831105 := bstep (se 2 (by rfl) ⟨3311664, by rfl⟩ : syracuseStep 8831105 = 6623329) B6623329
theorem B7446941 : Blo 1742572 7446941 := bstep (se 3 (by rfl) ⟨1396301, by rfl⟩ : syracuseStep 7446941 = 2792603) B2792603
theorem B84836807 : Blo 1742572 84836807 := bstep (se 1 (by rfl) ⟨63627605, by rfl⟩ : syracuseStep 84836807 = 127255211) B127255211
theorem B5882921 : Blo 1742572 5882921 := bstep (se 2 (by rfl) ⟨2206095, by rfl⟩ : syracuseStep 5882921 = 4412191) B4412191
theorem B5882975 : Blo 1742572 5882975 := bstep (se 1 (by rfl) ⟨4412231, by rfl⟩ : syracuseStep 5882975 = 8824463) B8824463
theorem B7955585 : Blo 1742572 7955585 := bstep (se 2 (by rfl) ⟨2983344, by rfl⟩ : syracuseStep 7955585 = 5966689) B5966689
theorem B2942203 : Blo 1742572 2942203 := bstep (se 1 (by rfl) ⟨2206652, by rfl⟩ : syracuseStep 2942203 = 4413305) B4413305
theorem B31794601 : Blo 1742572 31794601 := bstep (se 2 (by rfl) ⟨11922975, by rfl⟩ : syracuseStep 31794601 = 23845951) B23845951
theorem B1861103 : Blo 1742572 1861103 := bstep (se 1 (by rfl) ⟨1395827, by rfl⟩ : syracuseStep 1861103 = 2791655) B2791655
theorem B157009571 : Blo 1742572 157009571 := bstep (se 1 (by rfl) ⟨117757178, by rfl⟩ : syracuseStep 157009571 = 235514357) B235514357
theorem B8824787 : Blo 1742572 8824787 := bstep (se 1 (by rfl) ⟨6618590, by rfl⟩ : syracuseStep 8824787 = 13237181) B13237181
theorem B5032039 : Blo 1742572 5032039 := bstep (se 1 (by rfl) ⟨3774029, by rfl⟩ : syracuseStep 5032039 = 7548059) B7548059
theorem B2615399 : Blo 1742572 2615399 := bstep (se 1 (by rfl) ⟨1961549, by rfl⟩ : syracuseStep 2615399 = 3923099) B3923099
theorem B2615903 : Blo 1742572 2615903 := bstep (se 1 (by rfl) ⟨1961927, by rfl⟩ : syracuseStep 2615903 = 3923855) B3923855
theorem B2616041 : Blo 1742572 2616041 := bstep (se 2 (by rfl) ⟨981015, by rfl⟩ : syracuseStep 2616041 = 1962031) B1962031
theorem B19852127 : Blo 1742572 19852127 := bstep (se 1 (by rfl) ⟨14889095, by rfl⟩ : syracuseStep 19852127 = 29778191) B29778191
theorem B25136081 : Blo 1742572 25136081 := bstep (se 2 (by rfl) ⟨9426030, by rfl⟩ : syracuseStep 25136081 = 18852061) B18852061
theorem B2206703 : Blo 1742572 2206703 := bstep (se 1 (by rfl) ⟨1655027, by rfl⟩ : syracuseStep 2206703 = 3310055) B3310055
theorem B80481395 : Blo 1742572 80481395 := bstep (se 1 (by rfl) ⟨60361046, by rfl⟩ : syracuseStep 80481395 = 120722093) B120722093
theorem B3632455 : Blo 1742572 3632455 := bstep (se 1 (by rfl) ⟨2724341, by rfl⟩ : syracuseStep 3632455 = 5448683) B5448683
theorem B38235563 : Blo 1742572 38235563 := bstep (se 1 (by rfl) ⟨28676672, by rfl⟩ : syracuseStep 38235563 = 57353345) B57353345
theorem B4189865 : Blo 1742572 4189865 := bstep (se 2 (by rfl) ⟨1571199, by rfl⟩ : syracuseStep 4189865 = 3142399) B3142399
theorem B22335695 : Blo 1742572 22335695 := bstep (se 1 (by rfl) ⟨16751771, by rfl⟩ : syracuseStep 22335695 = 33503543) B33503543
theorem B4411817 : Blo 1742572 4411817 := bstep (se 2 (by rfl) ⟨1654431, by rfl⟩ : syracuseStep 4411817 = 3308863) B3308863
theorem B5886431 : Blo 1742572 5886431 := bstep (se 1 (by rfl) ⟨4414823, by rfl⟩ : syracuseStep 5886431 = 8829647) B8829647
theorem B1962463 : Blo 1742572 1962463 := bstep (se 1 (by rfl) ⟨1471847, by rfl⟩ : syracuseStep 1962463 = 2943695) B2943695
theorem B25130087 : Blo 1742572 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B3921083 : Blo 1742572 3921083 := bstep (se 1 (by rfl) ⟨2940812, by rfl⟩ : syracuseStep 3921083 = 5881625) B5881625
theorem B3921209 : Blo 1742572 3921209 := bstep (se 2 (by rfl) ⟨1470453, by rfl⟩ : syracuseStep 3921209 = 2940907) B2940907
theorem B3921515 : Blo 1742572 3921515 := bstep (se 1 (by rfl) ⟨2941136, by rfl⟩ : syracuseStep 3921515 = 5882273) B5882273
theorem B3921875 : Blo 1742572 3921875 := bstep (se 1 (by rfl) ⟨2941406, by rfl⟩ : syracuseStep 3921875 = 5882813) B5882813
theorem B12572653 : Blo 1742572 12572653 := bstep (se 3 (by rfl) ⟨2357372, by rfl⟩ : syracuseStep 12572653 = 4714745) B4714745
theorem B1742951 : Blo 1742572 1742951 := bstep (se 1 (by rfl) ⟨1307213, by rfl⟩ : syracuseStep 1742951 = 2614427) B2614427
theorem B6281327 : Blo 1742572 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B1743343 : Blo 1742572 1743343 := bstep (se 1 (by rfl) ⟨1307507, by rfl⟩ : syracuseStep 1743343 = 2615015) B2615015
theorem B1743615 : Blo 1742572 1743615 := bstep (se 1 (by rfl) ⟨1307711, by rfl⟩ : syracuseStep 1743615 = 2615423) B2615423
theorem B1743719 : Blo 1742572 1743719 := bstep (se 1 (by rfl) ⟨1307789, by rfl⟩ : syracuseStep 1743719 = 2615579) B2615579
theorem B4414459 : Blo 1742572 4414459 := bstep (se 1 (by rfl) ⟨3310844, by rfl⟩ : syracuseStep 4414459 = 6621689) B6621689
theorem B5585975 : Blo 1742572 5585975 := bstep (se 1 (by rfl) ⟨4189481, by rfl⟩ : syracuseStep 5585975 = 8378963) B8378963
theorem B1744039 : Blo 1742572 1744039 := bstep (se 1 (by rfl) ⟨1308029, by rfl⟩ : syracuseStep 1744039 = 2616059) B2616059
theorem B1744255 : Blo 1742572 1744255 := bstep (se 1 (by rfl) ⟨1308191, by rfl⟩ : syracuseStep 1744255 = 2616383) B2616383
theorem B1744319 : Blo 1742572 1744319 := bstep (se 1 (by rfl) ⟨1308239, by rfl⟩ : syracuseStep 1744319 = 2616479) B2616479
theorem B1744383 : Blo 1742572 1744383 := bstep (se 1 (by rfl) ⟨1308287, by rfl⟩ : syracuseStep 1744383 = 2616575) B2616575
theorem B1744539 : Blo 1742572 1744539 := bstep (se 1 (by rfl) ⟨1308404, by rfl⟩ : syracuseStep 1744539 = 2616809) B2616809
theorem B3923639 : Blo 1742572 3923639 := bstep (se 1 (by rfl) ⟨2942729, by rfl⟩ : syracuseStep 3923639 = 5885459) B5885459
theorem B4964399 : Blo 1742572 4964399 := bstep (se 1 (by rfl) ⟨3723299, by rfl⟩ : syracuseStep 4964399 = 7446599) B7446599
theorem B6709385 : Blo 1742572 6709385 := bstep (se 2 (by rfl) ⟨2516019, by rfl⟩ : syracuseStep 6709385 = 5032039) B5032039
theorem B4964627 : Blo 1742572 4964627 := bstep (se 1 (by rfl) ⟨3723470, by rfl⟩ : syracuseStep 4964627 = 7446941) B7446941
theorem B2941211 : Blo 1742572 2941211 := bstep (se 1 (by rfl) ⟨2205908, by rfl⟩ : syracuseStep 2941211 = 4411817) B4411817
theorem B56557871 : Blo 1742572 56557871 := bstep (se 1 (by rfl) ⟨42418403, by rfl⟩ : syracuseStep 56557871 = 84836807) B84836807
theorem B3924287 : Blo 1742572 3924287 := bstep (se 1 (by rfl) ⟨2943215, by rfl⟩ : syracuseStep 3924287 = 5886431) B5886431
theorem B16753391 : Blo 1742572 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B2614055 : Blo 1742572 2614055 := bstep (se 1 (by rfl) ⟨1960541, by rfl⟩ : syracuseStep 2614055 = 3921083) B3921083
theorem B2614139 : Blo 1742572 2614139 := bstep (se 1 (by rfl) ⟨1960604, by rfl⟩ : syracuseStep 2614139 = 3921209) B3921209
theorem B2614343 : Blo 1742572 2614343 := bstep (se 1 (by rfl) ⟨1960757, by rfl⟩ : syracuseStep 2614343 = 3921515) B3921515
theorem B2614583 : Blo 1742572 2614583 := bstep (se 1 (by rfl) ⟨1960937, by rfl⟩ : syracuseStep 2614583 = 3921875) B3921875
theorem B5883191 : Blo 1742572 5883191 := bstep (se 1 (by rfl) ⟨4412393, by rfl⟩ : syracuseStep 5883191 = 8824787) B8824787
theorem B4187551 : Blo 1742572 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B4843273 : Blo 1742572 4843273 := bstep (se 2 (by rfl) ⟨1816227, by rfl⟩ : syracuseStep 4843273 = 3632455) B3632455
theorem B2615759 : Blo 1742572 2615759 := bstep (se 1 (by rfl) ⟨1961819, by rfl⟩ : syracuseStep 2615759 = 3923639) B3923639
theorem B5884541 : Blo 1742572 5884541 := bstep (se 3 (by rfl) ⟨1103351, by rfl⟩ : syracuseStep 5884541 = 2206703) B2206703
theorem B16763537 : Blo 1742572 16763537 := bstep (se 2 (by rfl) ⟨6286326, by rfl⟩ : syracuseStep 16763537 = 12572653) B12572653
theorem B214617053 : Blo 1742572 214617053 := bstep (se 3 (by rfl) ⟨40240697, by rfl⟩ : syracuseStep 214617053 = 80481395) B80481395
theorem B2616617 : Blo 1742572 2616617 := bstep (se 2 (by rfl) ⟨981231, by rfl⟩ : syracuseStep 2616617 = 1962463) B1962463
theorem B5303723 : Blo 1742572 5303723 := bstep (se 1 (by rfl) ⟨3977792, by rfl⟩ : syracuseStep 5303723 = 7955585) B7955585
theorem B5885945 : Blo 1742572 5885945 := bstep (se 2 (by rfl) ⟨2207229, by rfl⟩ : syracuseStep 5885945 = 4414459) B4414459
theorem B1674768757 : Blo 1742572 1674768757 := bstep (se 5 (by rfl) ⟨78504785, by rfl⟩ : syracuseStep 1674768757 = 157009571) B157009571
theorem B13234751 : Blo 1742572 13234751 := bstep (se 1 (by rfl) ⟨9926063, by rfl⟩ : syracuseStep 13234751 = 19852127) B19852127
theorem B16757387 : Blo 1742572 16757387 := bstep (se 1 (by rfl) ⟨12568040, by rfl⟩ : syracuseStep 16757387 = 25136081) B25136081
theorem B3723983 : Blo 1742572 3723983 := bstep (se 1 (by rfl) ⟨2792987, by rfl⟩ : syracuseStep 3723983 = 5585975) B5585975
theorem B25490375 : Blo 1742572 25490375 := bstep (se 1 (by rfl) ⟨19117781, by rfl⟩ : syracuseStep 25490375 = 38235563) B38235563
theorem B5887403 : Blo 1742572 5887403 := bstep (se 1 (by rfl) ⟨4415552, by rfl⟩ : syracuseStep 5887403 = 8831105) B8831105
theorem B14890463 : Blo 1742572 14890463 := bstep (se 1 (by rfl) ⟨11167847, by rfl⟩ : syracuseStep 14890463 = 22335695) B22335695
theorem B3921947 : Blo 1742572 3921947 := bstep (se 1 (by rfl) ⟨2941460, by rfl⟩ : syracuseStep 3921947 = 5882921) B5882921
theorem B3921983 : Blo 1742572 3921983 := bstep (se 1 (by rfl) ⟨2941487, by rfl⟩ : syracuseStep 3921983 = 5882975) B5882975
theorem B4962941 : Blo 1742572 4962941 := bstep (se 3 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 4962941 = 1861103) B1861103
theorem B1743599 : Blo 1742572 1743599 := bstep (se 1 (by rfl) ⟨1307699, by rfl⟩ : syracuseStep 1743599 = 2615399) B2615399
theorem B3922937 : Blo 1742572 3922937 := bstep (se 2 (by rfl) ⟨1471101, by rfl⟩ : syracuseStep 3922937 = 2942203) B2942203
theorem B1743935 : Blo 1742572 1743935 := bstep (se 1 (by rfl) ⟨1307951, by rfl⟩ : syracuseStep 1743935 = 2615903) B2615903
theorem B11172973 : Blo 1742572 11172973 := bstep (se 3 (by rfl) ⟨2094932, by rfl⟩ : syracuseStep 11172973 = 4189865) B4189865
theorem B1744027 : Blo 1742572 1744027 := bstep (se 1 (by rfl) ⟨1308020, by rfl⟩ : syracuseStep 1744027 = 2616041) B2616041
theorem B42392801 : Blo 1742572 42392801 := bstep (se 2 (by rfl) ⟨15897300, by rfl⟩ : syracuseStep 42392801 = 31794601) B31794601
theorem B3309599 : Blo 1742572 3309599 := bstep (se 1 (by rfl) ⟨2482199, by rfl⟩ : syracuseStep 3309599 = 4964399) B4964399
theorem B4472923 : Blo 1742572 4472923 := bstep (se 1 (by rfl) ⟨3354692, by rfl⟩ : syracuseStep 4472923 = 6709385) B6709385
theorem B3309751 : Blo 1742572 3309751 := bstep (se 1 (by rfl) ⟨2482313, by rfl⟩ : syracuseStep 3309751 = 4964627) B4964627
theorem B8823167 : Blo 1742572 8823167 := bstep (se 1 (by rfl) ⟨6617375, by rfl⟩ : syracuseStep 8823167 = 13234751) B13234751
theorem B2482655 : Blo 1742572 2482655 := bstep (se 1 (by rfl) ⟨1861991, by rfl⟩ : syracuseStep 2482655 = 3723983) B3723983
theorem B2233025009 : Blo 1742572 2233025009 := bstep (se 2 (by rfl) ⟨837384378, by rfl⟩ : syracuseStep 2233025009 = 1674768757) B1674768757
theorem B3924935 : Blo 1742572 3924935 := bstep (se 1 (by rfl) ⟨2943701, by rfl⟩ : syracuseStep 3924935 = 5887403) B5887403
theorem B2614631 : Blo 1742572 2614631 := bstep (se 1 (by rfl) ⟨1960973, by rfl⟩ : syracuseStep 2614631 = 3921947) B3921947
theorem B2614655 : Blo 1742572 2614655 := bstep (se 1 (by rfl) ⟨1960991, by rfl⟩ : syracuseStep 2614655 = 3921983) B3921983
theorem B11175691 : Blo 1742572 11175691 := bstep (se 1 (by rfl) ⟨8381768, by rfl⟩ : syracuseStep 11175691 = 16763537) B16763537
theorem B2615291 : Blo 1742572 2615291 := bstep (se 1 (by rfl) ⟨1961468, by rfl⟩ : syracuseStep 2615291 = 3922937) B3922937
theorem B6457697 : Blo 1742572 6457697 := bstep (se 2 (by rfl) ⟨2421636, by rfl⟩ : syracuseStep 6457697 = 4843273) B4843273
theorem B1960807 : Blo 1742572 1960807 := bstep (se 1 (by rfl) ⟨1470605, by rfl⟩ : syracuseStep 1960807 = 2941211) B2941211
theorem B2616191 : Blo 1742572 2616191 := bstep (se 1 (by rfl) ⟨1962143, by rfl⟩ : syracuseStep 2616191 = 3924287) B3924287
theorem B11168927 : Blo 1742572 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B16993583 : Blo 1742572 16993583 := bstep (se 1 (by rfl) ⟨12745187, by rfl⟩ : syracuseStep 16993583 = 25490375) B25490375
theorem B14143261 : Blo 1742572 14143261 := bstep (se 3 (by rfl) ⟨2651861, by rfl⟩ : syracuseStep 14143261 = 5303723) B5303723
theorem B14897297 : Blo 1742572 14897297 := bstep (se 2 (by rfl) ⟨5586486, by rfl⟩ : syracuseStep 14897297 = 11172973) B11172973
theorem B5583401 : Blo 1742572 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B143078035 : Blo 1742572 143078035 := bstep (se 1 (by rfl) ⟨107308526, by rfl⟩ : syracuseStep 143078035 = 214617053) B214617053
theorem B37705247 : Blo 1742572 37705247 := bstep (se 1 (by rfl) ⟨28278935, by rfl⟩ : syracuseStep 37705247 = 56557871) B56557871
theorem B11171591 : Blo 1742572 11171591 := bstep (se 1 (by rfl) ⟨8378693, by rfl⟩ : syracuseStep 11171591 = 16757387) B16757387
theorem B1742703 : Blo 1742572 1742703 := bstep (se 1 (by rfl) ⟨1307027, by rfl⟩ : syracuseStep 1742703 = 2614055) B2614055
theorem B1742759 : Blo 1742572 1742759 := bstep (se 1 (by rfl) ⟨1307069, by rfl⟩ : syracuseStep 1742759 = 2614139) B2614139
theorem B1742895 : Blo 1742572 1742895 := bstep (se 1 (by rfl) ⟨1307171, by rfl⟩ : syracuseStep 1742895 = 2614343) B2614343
theorem B1743055 : Blo 1742572 1743055 := bstep (se 1 (by rfl) ⟨1307291, by rfl⟩ : syracuseStep 1743055 = 2614583) B2614583
theorem B3922127 : Blo 1742572 3922127 := bstep (se 1 (by rfl) ⟨2941595, by rfl⟩ : syracuseStep 3922127 = 5883191) B5883191
theorem B9926975 : Blo 1742572 9926975 := bstep (se 1 (by rfl) ⟨7445231, by rfl⟩ : syracuseStep 9926975 = 14890463) B14890463
theorem B1743839 : Blo 1742572 1743839 := bstep (se 1 (by rfl) ⟨1307879, by rfl⟩ : syracuseStep 1743839 = 2615759) B2615759
theorem B3308627 : Blo 1742572 3308627 := bstep (se 1 (by rfl) ⟨2481470, by rfl⟩ : syracuseStep 3308627 = 4962941) B4962941
theorem B3923027 : Blo 1742572 3923027 := bstep (se 1 (by rfl) ⟨2942270, by rfl⟩ : syracuseStep 3923027 = 5884541) B5884541
theorem B28261867 : Blo 1742572 28261867 := bstep (se 1 (by rfl) ⟨21196400, by rfl⟩ : syracuseStep 28261867 = 42392801) B42392801
theorem B1744411 : Blo 1742572 1744411 := bstep (se 1 (by rfl) ⟨1308308, by rfl⟩ : syracuseStep 1744411 = 2616617) B2616617
theorem B3923963 : Blo 1742572 3923963 := bstep (se 1 (by rfl) ⟨2942972, by rfl⟩ : syracuseStep 3923963 = 5885945) B5885945
theorem B5963897 : Blo 1742572 5963897 := bstep (se 2 (by rfl) ⟨2236461, by rfl⟩ : syracuseStep 5963897 = 4472923) B4472923
theorem B8823005 : Blo 1742572 8823005 := bstep (se 3 (by rfl) ⟨1654313, by rfl⟩ : syracuseStep 8823005 = 3308627) B3308627
theorem B5882111 : Blo 1742572 5882111 := bstep (se 1 (by rfl) ⟨4411583, by rfl⟩ : syracuseStep 5882111 = 8823167) B8823167
theorem B1488683339 : Blo 1742572 1488683339 := bstep (se 1 (by rfl) ⟨1116512504, by rfl⟩ : syracuseStep 1488683339 = 2233025009) B2233025009
theorem B2614409 : Blo 1742572 2614409 := bstep (se 2 (by rfl) ⟨980403, by rfl⟩ : syracuseStep 2614409 = 1960807) B1960807
theorem B7447727 : Blo 1742572 7447727 := bstep (se 1 (by rfl) ⟨5585795, by rfl⟩ : syracuseStep 7447727 = 11171591) B11171591
theorem B6620413 : Blo 1742572 6620413 := bstep (se 3 (by rfl) ⟨1241327, by rfl⟩ : syracuseStep 6620413 = 2482655) B2482655
theorem B2614751 : Blo 1742572 2614751 := bstep (se 1 (by rfl) ⟨1961063, by rfl⟩ : syracuseStep 2614751 = 3922127) B3922127
theorem B2615351 : Blo 1742572 2615351 := bstep (se 1 (by rfl) ⟨1961513, by rfl⟩ : syracuseStep 2615351 = 3923027) B3923027
theorem B2615975 : Blo 1742572 2615975 := bstep (se 1 (by rfl) ⟨1961981, by rfl⟩ : syracuseStep 2615975 = 3923963) B3923963
theorem B8825597 : Blo 1742572 8825597 := bstep (se 3 (by rfl) ⟨1654799, by rfl⟩ : syracuseStep 8825597 = 3309599) B3309599
theorem B9931531 : Blo 1742572 9931531 := bstep (se 1 (by rfl) ⟨7448648, by rfl⟩ : syracuseStep 9931531 = 14897297) B14897297
theorem B3722267 : Blo 1742572 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B2616623 : Blo 1742572 2616623 := bstep (se 1 (by rfl) ⟨1962467, by rfl⟩ : syracuseStep 2616623 = 3924935) B3924935
theorem B190770713 : Blo 1742572 190770713 := bstep (se 2 (by rfl) ⟨71539017, by rfl⟩ : syracuseStep 190770713 = 143078035) B143078035
theorem B25136831 : Blo 1742572 25136831 := bstep (se 1 (by rfl) ⟨18852623, by rfl⟩ : syracuseStep 25136831 = 37705247) B37705247
theorem B4305131 : Blo 1742572 4305131 := bstep (se 1 (by rfl) ⟨3228848, by rfl⟩ : syracuseStep 4305131 = 6457697) B6457697
theorem B4413001 : Blo 1742572 4413001 := bstep (se 2 (by rfl) ⟨1654875, by rfl⟩ : syracuseStep 4413001 = 3309751) B3309751
theorem B1743087 : Blo 1742572 1743087 := bstep (se 1 (by rfl) ⟨1307315, by rfl⟩ : syracuseStep 1743087 = 2614631) B2614631
theorem B1743103 : Blo 1742572 1743103 := bstep (se 1 (by rfl) ⟨1307327, by rfl⟩ : syracuseStep 1743103 = 2614655) B2614655
theorem B1743527 : Blo 1742572 1743527 := bstep (se 1 (by rfl) ⟨1307645, by rfl⟩ : syracuseStep 1743527 = 2615291) B2615291
theorem B6617983 : Blo 1742572 6617983 := bstep (se 1 (by rfl) ⟨4963487, by rfl⟩ : syracuseStep 6617983 = 9926975) B9926975
theorem B1744127 : Blo 1742572 1744127 := bstep (se 1 (by rfl) ⟨1308095, by rfl⟩ : syracuseStep 1744127 = 2616191) B2616191
theorem B37682489 : Blo 1742572 37682489 := bstep (se 2 (by rfl) ⟨14130933, by rfl⟩ : syracuseStep 37682489 = 28261867) B28261867
theorem B7445951 : Blo 1742572 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B11329055 : Blo 1742572 11329055 := bstep (se 1 (by rfl) ⟨8496791, by rfl⟩ : syracuseStep 11329055 = 16993583) B16993583
theorem B14900921 : Blo 1742572 14900921 := bstep (se 2 (by rfl) ⟨5587845, by rfl⟩ : syracuseStep 14900921 = 11175691) B11175691
theorem B18857681 : Blo 1742572 18857681 := bstep (se 2 (by rfl) ⟨7071630, by rfl⟩ : syracuseStep 18857681 = 14143261) B14143261
theorem B5882003 : Blo 1742572 5882003 := bstep (se 1 (by rfl) ⟨4411502, by rfl⟩ : syracuseStep 5882003 = 8823005) B8823005
theorem B4965151 : Blo 1742572 4965151 := bstep (se 1 (by rfl) ⟨3723863, by rfl⟩ : syracuseStep 4965151 = 7447727) B7447727
theorem B8823977 : Blo 1742572 8823977 := bstep (se 2 (by rfl) ⟨3308991, by rfl⟩ : syracuseStep 8823977 = 6617983) B6617983
theorem B5883731 : Blo 1742572 5883731 := bstep (se 1 (by rfl) ⟨4412798, by rfl⟩ : syracuseStep 5883731 = 8825597) B8825597
theorem B5884001 : Blo 1742572 5884001 := bstep (se 2 (by rfl) ⟨2206500, by rfl⟩ : syracuseStep 5884001 = 4413001) B4413001
theorem B3975931 : Blo 1742572 3975931 := bstep (se 1 (by rfl) ⟨2981948, by rfl⟩ : syracuseStep 3975931 = 5963897) B5963897
theorem B2870087 : Blo 1742572 2870087 := bstep (se 1 (by rfl) ⟨2152565, by rfl⟩ : syracuseStep 2870087 = 4305131) B4305131
theorem B992455559 : Blo 1742572 992455559 := bstep (se 1 (by rfl) ⟨744341669, by rfl⟩ : syracuseStep 992455559 = 1488683339) B1488683339
theorem B13242041 : Blo 1742572 13242041 := bstep (se 2 (by rfl) ⟨4965765, by rfl⟩ : syracuseStep 13242041 = 9931531) B9931531
theorem B8827217 : Blo 1742572 8827217 := bstep (se 2 (by rfl) ⟨3310206, by rfl⟩ : syracuseStep 8827217 = 6620413) B6620413
theorem B25121659 : Blo 1742572 25121659 := bstep (se 1 (by rfl) ⟨18841244, by rfl⟩ : syracuseStep 25121659 = 37682489) B37682489
theorem B9933947 : Blo 1742572 9933947 := bstep (se 1 (by rfl) ⟨7450460, by rfl⟩ : syracuseStep 9933947 = 14900921) B14900921
theorem B16757887 : Blo 1742572 16757887 := bstep (se 1 (by rfl) ⟨12568415, by rfl⟩ : syracuseStep 16757887 = 25136831) B25136831
theorem B12571787 : Blo 1742572 12571787 := bstep (se 1 (by rfl) ⟨9428840, by rfl⟩ : syracuseStep 12571787 = 18857681) B18857681
theorem B3921407 : Blo 1742572 3921407 := bstep (se 1 (by rfl) ⟨2941055, by rfl⟩ : syracuseStep 3921407 = 5882111) B5882111
theorem B1742939 : Blo 1742572 1742939 := bstep (se 1 (by rfl) ⟨1307204, by rfl⟩ : syracuseStep 1742939 = 2614409) B2614409
theorem B1743167 : Blo 1742572 1743167 := bstep (se 1 (by rfl) ⟨1307375, by rfl⟩ : syracuseStep 1743167 = 2614751) B2614751
theorem B1743567 : Blo 1742572 1743567 := bstep (se 1 (by rfl) ⟨1307675, by rfl⟩ : syracuseStep 1743567 = 2615351) B2615351
theorem B1743983 : Blo 1742572 1743983 := bstep (se 1 (by rfl) ⟨1307987, by rfl⟩ : syracuseStep 1743983 = 2615975) B2615975
theorem B2481511 : Blo 1742572 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B1744415 : Blo 1742572 1744415 := bstep (se 1 (by rfl) ⟨1308311, by rfl⟩ : syracuseStep 1744415 = 2616623) B2616623
theorem B4963967 : Blo 1742572 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B127180475 : Blo 1742572 127180475 := bstep (se 1 (by rfl) ⟨95385356, by rfl⟩ : syracuseStep 127180475 = 190770713) B190770713
theorem B7552703 : Blo 1742572 7552703 := bstep (se 1 (by rfl) ⟨5664527, by rfl⟩ : syracuseStep 7552703 = 11329055) B11329055
theorem B5882651 : Blo 1742572 5882651 := bstep (se 1 (by rfl) ⟨4411988, by rfl⟩ : syracuseStep 5882651 = 8823977) B8823977
theorem B2614271 : Blo 1742572 2614271 := bstep (se 1 (by rfl) ⟨1960703, by rfl⟩ : syracuseStep 2614271 = 3921407) B3921407
theorem B6620201 : Blo 1742572 6620201 := bstep (se 2 (by rfl) ⟨2482575, by rfl⟩ : syracuseStep 6620201 = 4965151) B4965151
theorem B661637039 : Blo 1742572 661637039 := bstep (se 1 (by rfl) ⟨496227779, by rfl⟩ : syracuseStep 661637039 = 992455559) B992455559
theorem B7653565 : Blo 1742572 7653565 := bstep (se 3 (by rfl) ⟨1435043, by rfl⟩ : syracuseStep 7653565 = 2870087) B2870087
theorem B5884811 : Blo 1742572 5884811 := bstep (se 1 (by rfl) ⟨4413608, by rfl⟩ : syracuseStep 5884811 = 8827217) B8827217
theorem B33524765 : Blo 1742572 33524765 := bstep (se 3 (by rfl) ⟨6285893, by rfl⟩ : syracuseStep 33524765 = 12571787) B12571787
theorem B6622631 : Blo 1742572 6622631 := bstep (se 1 (by rfl) ⟨4966973, by rfl⟩ : syracuseStep 6622631 = 9933947) B9933947
theorem B21204965 : Blo 1742572 21204965 := bstep (se 4 (by rfl) ⟨1987965, by rfl⟩ : syracuseStep 21204965 = 3975931) B3975931
theorem B22343849 : Blo 1742572 22343849 := bstep (se 2 (by rfl) ⟨8378943, by rfl⟩ : syracuseStep 22343849 = 16757887) B16757887
theorem B8828027 : Blo 1742572 8828027 := bstep (se 1 (by rfl) ⟨6621020, by rfl⟩ : syracuseStep 8828027 = 13242041) B13242041
theorem B5035135 : Blo 1742572 5035135 := bstep (se 1 (by rfl) ⟨3776351, by rfl⟩ : syracuseStep 5035135 = 7552703) B7552703
theorem B3921335 : Blo 1742572 3921335 := bstep (se 1 (by rfl) ⟨2941001, by rfl⟩ : syracuseStep 3921335 = 5882003) B5882003
theorem B33495545 : Blo 1742572 33495545 := bstep (se 2 (by rfl) ⟨12560829, by rfl⟩ : syracuseStep 33495545 = 25121659) B25121659
theorem B3922487 : Blo 1742572 3922487 := bstep (se 1 (by rfl) ⟨2941865, by rfl⟩ : syracuseStep 3922487 = 5883731) B5883731
theorem B3922667 : Blo 1742572 3922667 := bstep (se 1 (by rfl) ⟨2942000, by rfl⟩ : syracuseStep 3922667 = 5884001) B5884001
theorem B3308681 : Blo 1742572 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B3309311 : Blo 1742572 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B84786983 : Blo 1742572 84786983 := bstep (se 1 (by rfl) ⟨63590237, by rfl⟩ : syracuseStep 84786983 = 127180475) B127180475
theorem B2614223 : Blo 1742572 2614223 := bstep (se 1 (by rfl) ⟨1960667, by rfl⟩ : syracuseStep 2614223 = 3921335) B3921335
theorem B2614991 : Blo 1742572 2614991 := bstep (se 1 (by rfl) ⟨1961243, by rfl⟩ : syracuseStep 2614991 = 3922487) B3922487
theorem B2615111 : Blo 1742572 2615111 := bstep (se 1 (by rfl) ⟨1961333, by rfl⟩ : syracuseStep 2615111 = 3922667) B3922667
theorem B22349843 : Blo 1742572 22349843 := bstep (se 1 (by rfl) ⟨16762382, by rfl⟩ : syracuseStep 22349843 = 33524765) B33524765
theorem B2205787 : Blo 1742572 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B2206207 : Blo 1742572 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B14895899 : Blo 1742572 14895899 := bstep (se 1 (by rfl) ⟨11171924, by rfl⟩ : syracuseStep 14895899 = 22343849) B22343849
theorem B5885351 : Blo 1742572 5885351 := bstep (se 1 (by rfl) ⟨4414013, by rfl⟩ : syracuseStep 5885351 = 8828027) B8828027
theorem B6713513 : Blo 1742572 6713513 := bstep (se 2 (by rfl) ⟨2517567, by rfl⟩ : syracuseStep 6713513 = 5035135) B5035135
theorem B1764365437 : Blo 1742572 1764365437 := bstep (se 3 (by rfl) ⟨330818519, by rfl⟩ : syracuseStep 1764365437 = 661637039) B661637039
theorem B14136643 : Blo 1742572 14136643 := bstep (se 1 (by rfl) ⟨10602482, by rfl⟩ : syracuseStep 14136643 = 21204965) B21204965
theorem B10204753 : Blo 1742572 10204753 := bstep (se 2 (by rfl) ⟨3826782, by rfl⟩ : syracuseStep 10204753 = 7653565) B7653565
theorem B3921767 : Blo 1742572 3921767 := bstep (se 1 (by rfl) ⟨2941325, by rfl⟩ : syracuseStep 3921767 = 5882651) B5882651
theorem B1742847 : Blo 1742572 1742847 := bstep (se 1 (by rfl) ⟨1307135, by rfl⟩ : syracuseStep 1742847 = 2614271) B2614271
theorem B4413467 : Blo 1742572 4413467 := bstep (se 1 (by rfl) ⟨3310100, by rfl⟩ : syracuseStep 4413467 = 6620201) B6620201
theorem B22330363 : Blo 1742572 22330363 := bstep (se 1 (by rfl) ⟨16747772, by rfl⟩ : syracuseStep 22330363 = 33495545) B33495545
theorem B3923207 : Blo 1742572 3923207 := bstep (se 1 (by rfl) ⟨2942405, by rfl⟩ : syracuseStep 3923207 = 5884811) B5884811
theorem B4415087 : Blo 1742572 4415087 := bstep (se 1 (by rfl) ⟨3311315, by rfl⟩ : syracuseStep 4415087 = 6622631) B6622631
theorem B56524655 : Blo 1742572 56524655 := bstep (se 1 (by rfl) ⟨42393491, by rfl⟩ : syracuseStep 56524655 = 84786983) B84786983
theorem B2941049 : Blo 1742572 2941049 := bstep (se 2 (by rfl) ⟨1102893, by rfl⟩ : syracuseStep 2941049 = 2205787) B2205787
theorem B2941609 : Blo 1742572 2941609 := bstep (se 2 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 2941609 = 2206207) B2206207
theorem B2614511 : Blo 1742572 2614511 := bstep (se 1 (by rfl) ⟨1960883, by rfl⟩ : syracuseStep 2614511 = 3921767) B3921767
theorem B2942311 : Blo 1742572 2942311 := bstep (se 1 (by rfl) ⟨2206733, by rfl⟩ : syracuseStep 2942311 = 4413467) B4413467
theorem B9930599 : Blo 1742572 9930599 := bstep (se 1 (by rfl) ⟨7447949, by rfl⟩ : syracuseStep 9930599 = 14895899) B14895899
theorem B2615471 : Blo 1742572 2615471 := bstep (se 1 (by rfl) ⟨1961603, by rfl⟩ : syracuseStep 2615471 = 3923207) B3923207
theorem B2943391 : Blo 1742572 2943391 := bstep (se 1 (by rfl) ⟨2207543, by rfl⟩ : syracuseStep 2943391 = 4415087) B4415087
theorem B4475675 : Blo 1742572 4475675 := bstep (se 1 (by rfl) ⟨3356756, by rfl⟩ : syracuseStep 4475675 = 6713513) B6713513
theorem B29773817 : Blo 1742572 29773817 := bstep (se 2 (by rfl) ⟨11165181, by rfl⟩ : syracuseStep 29773817 = 22330363) B22330363
theorem B1742815 : Blo 1742572 1742815 := bstep (se 1 (by rfl) ⟨1307111, by rfl⟩ : syracuseStep 1742815 = 2614223) B2614223
theorem B1743327 : Blo 1742572 1743327 := bstep (se 1 (by rfl) ⟨1307495, by rfl⟩ : syracuseStep 1743327 = 2614991) B2614991
theorem B1743407 : Blo 1742572 1743407 := bstep (se 1 (by rfl) ⟨1307555, by rfl⟩ : syracuseStep 1743407 = 2615111) B2615111
theorem B14899895 : Blo 1742572 14899895 := bstep (se 1 (by rfl) ⟨11174921, by rfl⟩ : syracuseStep 14899895 = 22349843) B22349843
theorem B2352487249 : Blo 1742572 2352487249 := bstep (se 2 (by rfl) ⟨882182718, by rfl⟩ : syracuseStep 2352487249 = 1764365437) B1764365437
theorem B18848857 : Blo 1742572 18848857 := bstep (se 2 (by rfl) ⟨7068321, by rfl⟩ : syracuseStep 18848857 = 14136643) B14136643
theorem B13606337 : Blo 1742572 13606337 := bstep (se 2 (by rfl) ⟨5102376, by rfl⟩ : syracuseStep 13606337 = 10204753) B10204753
theorem B3923567 : Blo 1742572 3923567 := bstep (se 1 (by rfl) ⟨2942675, by rfl⟩ : syracuseStep 3923567 = 5885351) B5885351
theorem B37683103 : Blo 1742572 37683103 := bstep (se 1 (by rfl) ⟨28262327, by rfl⟩ : syracuseStep 37683103 = 56524655) B56524655
theorem B3924521 : Blo 1742572 3924521 := bstep (se 2 (by rfl) ⟨1471695, by rfl⟩ : syracuseStep 3924521 = 2943391) B2943391
theorem B36283565 : Blo 1742572 36283565 := bstep (se 3 (by rfl) ⟨6803168, by rfl⟩ : syracuseStep 36283565 = 13606337) B13606337
theorem B6620399 : Blo 1742572 6620399 := bstep (se 1 (by rfl) ⟨4965299, by rfl⟩ : syracuseStep 6620399 = 9930599) B9930599
theorem B2615711 : Blo 1742572 2615711 := bstep (se 1 (by rfl) ⟨1961783, by rfl⟩ : syracuseStep 2615711 = 3923567) B3923567
theorem B50244137 : Blo 1742572 50244137 := bstep (se 2 (by rfl) ⟨18841551, by rfl⟩ : syracuseStep 50244137 = 37683103) B37683103
theorem B1960699 : Blo 1742572 1960699 := bstep (se 1 (by rfl) ⟨1470524, by rfl⟩ : syracuseStep 1960699 = 2941049) B2941049
theorem B9933263 : Blo 1742572 9933263 := bstep (se 1 (by rfl) ⟨7449947, by rfl⟩ : syracuseStep 9933263 = 14899895) B14899895
theorem B1743007 : Blo 1742572 1743007 := bstep (se 1 (by rfl) ⟨1307255, by rfl⟩ : syracuseStep 1743007 = 2614511) B2614511
theorem B3922145 : Blo 1742572 3922145 := bstep (se 2 (by rfl) ⟨1470804, by rfl⟩ : syracuseStep 3922145 = 2941609) B2941609
theorem B3136649665 : Blo 1742572 3136649665 := bstep (se 2 (by rfl) ⟨1176243624, by rfl⟩ : syracuseStep 3136649665 = 2352487249) B2352487249
theorem B1743647 : Blo 1742572 1743647 := bstep (se 1 (by rfl) ⟨1307735, by rfl⟩ : syracuseStep 1743647 = 2615471) B2615471
theorem B25131809 : Blo 1742572 25131809 := bstep (se 2 (by rfl) ⟨9424428, by rfl⟩ : syracuseStep 25131809 = 18848857) B18848857
theorem B3923081 : Blo 1742572 3923081 := bstep (se 2 (by rfl) ⟨1471155, by rfl⟩ : syracuseStep 3923081 = 2942311) B2942311
theorem B11935133 : Blo 1742572 11935133 := bstep (se 3 (by rfl) ⟨2237837, by rfl⟩ : syracuseStep 11935133 = 4475675) B4475675
theorem B19849211 : Blo 1742572 19849211 := bstep (se 1 (by rfl) ⟨14886908, by rfl⟩ : syracuseStep 19849211 = 29773817) B29773817
theorem B2614265 : Blo 1742572 2614265 := bstep (se 2 (by rfl) ⟨980349, by rfl⟩ : syracuseStep 2614265 = 1960699) B1960699
theorem B2614763 : Blo 1742572 2614763 := bstep (se 1 (by rfl) ⟨1961072, by rfl⟩ : syracuseStep 2614763 = 3922145) B3922145
theorem B16754539 : Blo 1742572 16754539 := bstep (se 1 (by rfl) ⟨12565904, by rfl⟩ : syracuseStep 16754539 = 25131809) B25131809
theorem B2615387 : Blo 1742572 2615387 := bstep (se 1 (by rfl) ⟨1961540, by rfl⟩ : syracuseStep 2615387 = 3923081) B3923081
theorem B7956755 : Blo 1742572 7956755 := bstep (se 1 (by rfl) ⟨5967566, by rfl⟩ : syracuseStep 7956755 = 11935133) B11935133
theorem B13232807 : Blo 1742572 13232807 := bstep (se 1 (by rfl) ⟨9924605, by rfl⟩ : syracuseStep 13232807 = 19849211) B19849211
theorem B6622175 : Blo 1742572 6622175 := bstep (se 1 (by rfl) ⟨4966631, by rfl⟩ : syracuseStep 6622175 = 9933263) B9933263
theorem B2616347 : Blo 1742572 2616347 := bstep (se 1 (by rfl) ⟨1962260, by rfl⟩ : syracuseStep 2616347 = 3924521) B3924521
theorem B4182199553 : Blo 1742572 4182199553 := bstep (se 2 (by rfl) ⟨1568324832, by rfl⟩ : syracuseStep 4182199553 = 3136649665) B3136649665
theorem B24189043 : Blo 1742572 24189043 := bstep (se 1 (by rfl) ⟨18141782, by rfl⟩ : syracuseStep 24189043 = 36283565) B36283565
theorem B4413599 : Blo 1742572 4413599 := bstep (se 1 (by rfl) ⟨3310199, by rfl⟩ : syracuseStep 4413599 = 6620399) B6620399
theorem B1743807 : Blo 1742572 1743807 := bstep (se 1 (by rfl) ⟨1307855, by rfl⟩ : syracuseStep 1743807 = 2615711) B2615711
theorem B33496091 : Blo 1742572 33496091 := bstep (se 1 (by rfl) ⟨25122068, by rfl⟩ : syracuseStep 33496091 = 50244137) B50244137
theorem B32252057 : Blo 1742572 32252057 := bstep (se 2 (by rfl) ⟨12094521, by rfl⟩ : syracuseStep 32252057 = 24189043) B24189043
theorem B2942399 : Blo 1742572 2942399 := bstep (se 1 (by rfl) ⟨2206799, by rfl⟩ : syracuseStep 2942399 = 4413599) B4413599
theorem B2788133035 : Blo 1742572 2788133035 := bstep (se 1 (by rfl) ⟨2091099776, by rfl⟩ : syracuseStep 2788133035 = 4182199553) B4182199553
theorem B5304503 : Blo 1742572 5304503 := bstep (se 1 (by rfl) ⟨3978377, by rfl⟩ : syracuseStep 5304503 = 7956755) B7956755
theorem B1742843 : Blo 1742572 1742843 := bstep (se 1 (by rfl) ⟨1307132, by rfl⟩ : syracuseStep 1742843 = 2614265) B2614265
theorem B1743175 : Blo 1742572 1743175 := bstep (se 1 (by rfl) ⟨1307381, by rfl⟩ : syracuseStep 1743175 = 2614763) B2614763
theorem B1743591 : Blo 1742572 1743591 := bstep (se 1 (by rfl) ⟨1307693, by rfl⟩ : syracuseStep 1743591 = 2615387) B2615387
theorem B8821871 : Blo 1742572 8821871 := bstep (se 1 (by rfl) ⟨6616403, by rfl⟩ : syracuseStep 8821871 = 13232807) B13232807
theorem B4414783 : Blo 1742572 4414783 := bstep (se 1 (by rfl) ⟨3311087, by rfl⟩ : syracuseStep 4414783 = 6622175) B6622175
theorem B22330727 : Blo 1742572 22330727 := bstep (se 1 (by rfl) ⟨16748045, by rfl⟩ : syracuseStep 22330727 = 33496091) B33496091
theorem B1744231 : Blo 1742572 1744231 := bstep (se 1 (by rfl) ⟨1308173, by rfl⟩ : syracuseStep 1744231 = 2616347) B2616347
theorem B22339385 : Blo 1742572 22339385 := bstep (se 2 (by rfl) ⟨8377269, by rfl⟩ : syracuseStep 22339385 = 16754539) B16754539
theorem B14887151 : Blo 1742572 14887151 := bstep (se 1 (by rfl) ⟨11165363, by rfl⟩ : syracuseStep 14887151 = 22330727) B22330727
theorem B1961599 : Blo 1742572 1961599 := bstep (se 1 (by rfl) ⟨1471199, by rfl⟩ : syracuseStep 1961599 = 2942399) B2942399
theorem B5886377 : Blo 1742572 5886377 := bstep (se 2 (by rfl) ⟨2207391, by rfl⟩ : syracuseStep 5886377 = 4414783) B4414783
theorem B21501371 : Blo 1742572 21501371 := bstep (se 1 (by rfl) ⟨16126028, by rfl⟩ : syracuseStep 21501371 = 32252057) B32252057
theorem B3536335 : Blo 1742572 3536335 := bstep (se 1 (by rfl) ⟨2652251, by rfl⟩ : syracuseStep 3536335 = 5304503) B5304503
theorem B3717510713 : Blo 1742572 3717510713 := bstep (se 2 (by rfl) ⟨1394066517, by rfl⟩ : syracuseStep 3717510713 = 2788133035) B2788133035
theorem B5881247 : Blo 1742572 5881247 := bstep (se 1 (by rfl) ⟨4410935, by rfl⟩ : syracuseStep 5881247 = 8821871) B8821871
theorem B14892923 : Blo 1742572 14892923 := bstep (se 1 (by rfl) ⟨11169692, by rfl⟩ : syracuseStep 14892923 = 22339385) B22339385
theorem B3924251 : Blo 1742572 3924251 := bstep (se 1 (by rfl) ⟨2943188, by rfl⟩ : syracuseStep 3924251 = 5886377) B5886377
theorem B57336989 : Blo 1742572 57336989 := bstep (se 3 (by rfl) ⟨10750685, by rfl⟩ : syracuseStep 57336989 = 21501371) B21501371
theorem B2615465 : Blo 1742572 2615465 := bstep (se 2 (by rfl) ⟨980799, by rfl⟩ : syracuseStep 2615465 = 1961599) B1961599
theorem B9924767 : Blo 1742572 9924767 := bstep (se 1 (by rfl) ⟨7443575, by rfl⟩ : syracuseStep 9924767 = 14887151) B14887151
theorem B4715113 : Blo 1742572 4715113 := bstep (se 2 (by rfl) ⟨1768167, by rfl⟩ : syracuseStep 4715113 = 3536335) B3536335
theorem B3920831 : Blo 1742572 3920831 := bstep (se 1 (by rfl) ⟨2940623, by rfl⟩ : syracuseStep 3920831 = 5881247) B5881247
theorem B2478340475 : Blo 1742572 2478340475 := bstep (se 1 (by rfl) ⟨1858755356, by rfl⟩ : syracuseStep 2478340475 = 3717510713) B3717510713
theorem B9928615 : Blo 1742572 9928615 := bstep (se 1 (by rfl) ⟨7446461, by rfl⟩ : syracuseStep 9928615 = 14892923) B14892923
theorem B2613887 : Blo 1742572 2613887 := bstep (se 1 (by rfl) ⟨1960415, by rfl⟩ : syracuseStep 2613887 = 3920831) B3920831
theorem B2616167 : Blo 1742572 2616167 := bstep (se 1 (by rfl) ⟨1962125, by rfl⟩ : syracuseStep 2616167 = 3924251) B3924251
theorem B152898637 : Blo 1742572 152898637 := bstep (se 3 (by rfl) ⟨28668494, by rfl⟩ : syracuseStep 152898637 = 57336989) B57336989
theorem B6286817 : Blo 1742572 6286817 := bstep (se 2 (by rfl) ⟨2357556, by rfl⟩ : syracuseStep 6286817 = 4715113) B4715113
theorem B6616511 : Blo 1742572 6616511 := bstep (se 1 (by rfl) ⟨4962383, by rfl⟩ : syracuseStep 6616511 = 9924767) B9924767
theorem B1743643 : Blo 1742572 1743643 := bstep (se 1 (by rfl) ⟨1307732, by rfl⟩ : syracuseStep 1743643 = 2615465) B2615465
theorem B1652226983 : Blo 1742572 1652226983 := bstep (se 1 (by rfl) ⟨1239170237, by rfl⟩ : syracuseStep 1652226983 = 2478340475) B2478340475
theorem B13238153 : Blo 1742572 13238153 := bstep (se 2 (by rfl) ⟨4964307, by rfl⟩ : syracuseStep 13238153 = 9928615) B9928615
theorem B8825435 : Blo 1742572 8825435 := bstep (se 1 (by rfl) ⟨6619076, by rfl⟩ : syracuseStep 8825435 = 13238153) B13238153
theorem B4411007 : Blo 1742572 4411007 := bstep (se 1 (by rfl) ⟨3308255, by rfl⟩ : syracuseStep 4411007 = 6616511) B6616511
theorem B1101484655 : Blo 1742572 1101484655 := bstep (se 1 (by rfl) ⟨826113491, by rfl⟩ : syracuseStep 1101484655 = 1652226983) B1652226983
theorem B4191211 : Blo 1742572 4191211 := bstep (se 1 (by rfl) ⟨3143408, by rfl⟩ : syracuseStep 4191211 = 6286817) B6286817
theorem B1742591 : Blo 1742572 1742591 := bstep (se 1 (by rfl) ⟨1306943, by rfl⟩ : syracuseStep 1742591 = 2613887) B2613887
theorem B203864849 : Blo 1742572 203864849 := bstep (se 2 (by rfl) ⟨76449318, by rfl⟩ : syracuseStep 203864849 = 152898637) B152898637
theorem B1744111 : Blo 1742572 1744111 := bstep (se 1 (by rfl) ⟨1308083, by rfl⟩ : syracuseStep 1744111 = 2616167) B2616167
theorem B734323103 : Blo 1742572 734323103 := bstep (se 1 (by rfl) ⟨550742327, by rfl⟩ : syracuseStep 734323103 = 1101484655) B1101484655
theorem B5588281 : Blo 1742572 5588281 := bstep (se 2 (by rfl) ⟨2095605, by rfl⟩ : syracuseStep 5588281 = 4191211) B4191211
theorem B5883623 : Blo 1742572 5883623 := bstep (se 1 (by rfl) ⟨4412717, by rfl⟩ : syracuseStep 5883623 = 8825435) B8825435
theorem B135909899 : Blo 1742572 135909899 := bstep (se 1 (by rfl) ⟨101932424, by rfl⟩ : syracuseStep 135909899 = 203864849) B203864849
theorem B2940671 : Blo 1742572 2940671 := bstep (se 1 (by rfl) ⟨2205503, by rfl⟩ : syracuseStep 2940671 = 4411007) B4411007
theorem B1960447 : Blo 1742572 1960447 := bstep (se 1 (by rfl) ⟨1470335, by rfl⟩ : syracuseStep 1960447 = 2940671) B2940671
theorem B489548735 : Blo 1742572 489548735 := bstep (se 1 (by rfl) ⟨367161551, by rfl⟩ : syracuseStep 489548735 = 734323103) B734323103
theorem B90606599 : Blo 1742572 90606599 := bstep (se 1 (by rfl) ⟨67954949, by rfl⟩ : syracuseStep 90606599 = 135909899) B135909899
theorem B7451041 : Blo 1742572 7451041 := bstep (se 2 (by rfl) ⟨2794140, by rfl⟩ : syracuseStep 7451041 = 5588281) B5588281
theorem B3922415 : Blo 1742572 3922415 := bstep (se 1 (by rfl) ⟨2941811, by rfl⟩ : syracuseStep 3922415 = 5883623) B5883623
theorem B2613929 : Blo 1742572 2613929 := bstep (se 2 (by rfl) ⟨980223, by rfl⟩ : syracuseStep 2613929 = 1960447) B1960447
theorem B2614943 : Blo 1742572 2614943 := bstep (se 1 (by rfl) ⟨1961207, by rfl⟩ : syracuseStep 2614943 = 3922415) B3922415
theorem B326365823 : Blo 1742572 326365823 := bstep (se 1 (by rfl) ⟨244774367, by rfl⟩ : syracuseStep 326365823 = 489548735) B489548735
theorem B60404399 : Blo 1742572 60404399 := bstep (se 1 (by rfl) ⟨45303299, by rfl⟩ : syracuseStep 60404399 = 90606599) B90606599
theorem B9934721 : Blo 1742572 9934721 := bstep (se 2 (by rfl) ⟨3725520, by rfl⟩ : syracuseStep 9934721 = 7451041) B7451041
theorem B6623147 : Blo 1742572 6623147 := bstep (se 1 (by rfl) ⟨4967360, by rfl⟩ : syracuseStep 6623147 = 9934721) B9934721
theorem B217577215 : Blo 1742572 217577215 := bstep (se 1 (by rfl) ⟨163182911, by rfl⟩ : syracuseStep 217577215 = 326365823) B326365823
theorem B1742619 : Blo 1742572 1742619 := bstep (se 1 (by rfl) ⟨1306964, by rfl⟩ : syracuseStep 1742619 = 2613929) B2613929
theorem B40269599 : Blo 1742572 40269599 := bstep (se 1 (by rfl) ⟨30202199, by rfl⟩ : syracuseStep 40269599 = 60404399) B60404399
theorem B1743295 : Blo 1742572 1743295 := bstep (se 1 (by rfl) ⟨1307471, by rfl⟩ : syracuseStep 1743295 = 2614943) B2614943
theorem B26846399 : Blo 1742572 26846399 := bstep (se 1 (by rfl) ⟨20134799, by rfl⟩ : syracuseStep 26846399 = 40269599) B40269599
theorem B290102953 : Blo 1742572 290102953 := bstep (se 2 (by rfl) ⟨108788607, by rfl⟩ : syracuseStep 290102953 = 217577215) B217577215
theorem B4415431 : Blo 1742572 4415431 := bstep (se 1 (by rfl) ⟨3311573, by rfl⟩ : syracuseStep 4415431 = 6623147) B6623147
theorem B71590397 : Blo 1742572 71590397 := bstep (se 3 (by rfl) ⟨13423199, by rfl⟩ : syracuseStep 71590397 = 26846399) B26846399
theorem B386803937 : Blo 1742572 386803937 := bstep (se 2 (by rfl) ⟨145051476, by rfl⟩ : syracuseStep 386803937 = 290102953) B290102953
theorem B5887241 : Blo 1742572 5887241 := bstep (se 2 (by rfl) ⟨2207715, by rfl⟩ : syracuseStep 5887241 = 4415431) B4415431
theorem B3924827 : Blo 1742572 3924827 := bstep (se 1 (by rfl) ⟨2943620, by rfl⟩ : syracuseStep 3924827 = 5887241) B5887241
theorem B190907725 : Blo 1742572 190907725 := bstep (se 3 (by rfl) ⟨35795198, by rfl⟩ : syracuseStep 190907725 = 71590397) B71590397
theorem B257869291 : Blo 1742572 257869291 := bstep (se 1 (by rfl) ⟨193401968, by rfl⟩ : syracuseStep 257869291 = 386803937) B386803937
theorem B254543633 : Blo 1742572 254543633 := bstep (se 2 (by rfl) ⟨95453862, by rfl⟩ : syracuseStep 254543633 = 190907725) B190907725
theorem B2616551 : Blo 1742572 2616551 := bstep (se 1 (by rfl) ⟨1962413, by rfl⟩ : syracuseStep 2616551 = 3924827) B3924827
theorem B343825721 : Blo 1742572 343825721 := bstep (se 2 (by rfl) ⟨128934645, by rfl⟩ : syracuseStep 343825721 = 257869291) B257869291
theorem B229217147 : Blo 1742572 229217147 := bstep (se 1 (by rfl) ⟨171912860, by rfl⟩ : syracuseStep 229217147 = 343825721) B343825721
theorem B169695755 : Blo 1742572 169695755 := bstep (se 1 (by rfl) ⟨127271816, by rfl⟩ : syracuseStep 169695755 = 254543633) B254543633
theorem B1744367 : Blo 1742572 1744367 := bstep (se 1 (by rfl) ⟨1308275, by rfl⟩ : syracuseStep 1744367 = 2616551) B2616551
theorem B152811431 : Blo 1742572 152811431 := bstep (se 1 (by rfl) ⟨114608573, by rfl⟩ : syracuseStep 152811431 = 229217147) B229217147
theorem B113130503 : Blo 1742572 113130503 := bstep (se 1 (by rfl) ⟨84847877, by rfl⟩ : syracuseStep 113130503 = 169695755) B169695755
theorem B75420335 : Blo 1742572 75420335 := bstep (se 1 (by rfl) ⟨56565251, by rfl⟩ : syracuseStep 75420335 = 113130503) B113130503
theorem B101874287 : Blo 1742572 101874287 := bstep (se 1 (by rfl) ⟨76405715, by rfl⟩ : syracuseStep 101874287 = 152811431) B152811431
theorem B67916191 : Blo 1742572 67916191 := bstep (se 1 (by rfl) ⟨50937143, by rfl⟩ : syracuseStep 67916191 = 101874287) B101874287
theorem B50280223 : Blo 1742572 50280223 := bstep (se 1 (by rfl) ⟨37710167, by rfl⟩ : syracuseStep 50280223 = 75420335) B75420335
theorem B90554921 : Blo 1742572 90554921 := bstep (se 2 (by rfl) ⟨33958095, by rfl⟩ : syracuseStep 90554921 = 67916191) B67916191
theorem B67040297 : Blo 1742572 67040297 := bstep (se 2 (by rfl) ⟨25140111, by rfl⟩ : syracuseStep 67040297 = 50280223) B50280223
theorem B60369947 : Blo 1742572 60369947 := bstep (se 1 (by rfl) ⟨45277460, by rfl⟩ : syracuseStep 60369947 = 90554921) B90554921
theorem B44693531 : Blo 1742572 44693531 := bstep (se 1 (by rfl) ⟨33520148, by rfl⟩ : syracuseStep 44693531 = 67040297) B67040297
theorem B29795687 : Blo 1742572 29795687 := bstep (se 1 (by rfl) ⟨22346765, by rfl⟩ : syracuseStep 29795687 = 44693531) B44693531
theorem B40246631 : Blo 1742572 40246631 := bstep (se 1 (by rfl) ⟨30184973, by rfl⟩ : syracuseStep 40246631 = 60369947) B60369947
theorem B26831087 : Blo 1742572 26831087 := bstep (se 1 (by rfl) ⟨20123315, by rfl⟩ : syracuseStep 26831087 = 40246631) B40246631
theorem B19863791 : Blo 1742572 19863791 := bstep (se 1 (by rfl) ⟨14897843, by rfl⟩ : syracuseStep 19863791 = 29795687) B29795687
theorem B17887391 : Blo 1742572 17887391 := bstep (se 1 (by rfl) ⟨13415543, by rfl⟩ : syracuseStep 17887391 = 26831087) B26831087
theorem B13242527 : Blo 1742572 13242527 := bstep (se 1 (by rfl) ⟨9931895, by rfl⟩ : syracuseStep 13242527 = 19863791) B19863791
theorem B11924927 : Blo 1742572 11924927 := bstep (se 1 (by rfl) ⟨8943695, by rfl⟩ : syracuseStep 11924927 = 17887391) B17887391
theorem B8828351 : Blo 1742572 8828351 := bstep (se 1 (by rfl) ⟨6621263, by rfl⟩ : syracuseStep 8828351 = 13242527) B13242527
theorem B7949951 : Blo 1742572 7949951 := bstep (se 1 (by rfl) ⟨5962463, by rfl⟩ : syracuseStep 7949951 = 11924927) B11924927
theorem B5885567 : Blo 1742572 5885567 := bstep (se 1 (by rfl) ⟨4414175, by rfl⟩ : syracuseStep 5885567 = 8828351) B8828351
theorem B5299967 : Blo 1742572 5299967 := bstep (se 1 (by rfl) ⟨3974975, by rfl⟩ : syracuseStep 5299967 = 7949951) B7949951
theorem B3923711 : Blo 1742572 3923711 := bstep (se 1 (by rfl) ⟨2942783, by rfl⟩ : syracuseStep 3923711 = 5885567) B5885567
theorem B3533311 : Blo 1742572 3533311 := bstep (se 1 (by rfl) ⟨2649983, by rfl⟩ : syracuseStep 3533311 = 5299967) B5299967
theorem B2615807 : Blo 1742572 2615807 := bstep (se 1 (by rfl) ⟨1961855, by rfl⟩ : syracuseStep 2615807 = 3923711) B3923711
theorem B4711081 : Blo 1742572 4711081 := bstep (se 2 (by rfl) ⟨1766655, by rfl⟩ : syracuseStep 4711081 = 3533311) B3533311
theorem B1743871 : Blo 1742572 1743871 := bstep (se 1 (by rfl) ⟨1307903, by rfl⟩ : syracuseStep 1743871 = 2615807) B2615807
theorem B6281441 : Blo 1742572 6281441 := bstep (se 2 (by rfl) ⟨2355540, by rfl⟩ : syracuseStep 6281441 = 4711081) B4711081
theorem B4187627 : Blo 1742572 4187627 := bstep (se 1 (by rfl) ⟨3140720, by rfl⟩ : syracuseStep 4187627 = 6281441) B6281441
theorem B2791751 : Blo 1742572 2791751 := bstep (se 1 (by rfl) ⟨2093813, by rfl⟩ : syracuseStep 2791751 = 4187627) B4187627
theorem B7444669 : Blo 1742572 7444669 := bstep (se 3 (by rfl) ⟨1395875, by rfl⟩ : syracuseStep 7444669 = 2791751) B2791751
theorem B9926225 : Blo 1742572 9926225 := bstep (se 2 (by rfl) ⟨3722334, by rfl⟩ : syracuseStep 9926225 = 7444669) B7444669
theorem B6617483 : Blo 1742572 6617483 := bstep (se 1 (by rfl) ⟨4963112, by rfl⟩ : syracuseStep 6617483 = 9926225) B9926225
theorem B4411655 : Blo 1742572 4411655 := bstep (se 1 (by rfl) ⟨3308741, by rfl⟩ : syracuseStep 4411655 = 6617483) B6617483
theorem B2941103 : Blo 1742572 2941103 := bstep (se 1 (by rfl) ⟨2205827, by rfl⟩ : syracuseStep 2941103 = 4411655) B4411655
theorem B1960735 : Blo 1742572 1960735 := bstep (se 1 (by rfl) ⟨1470551, by rfl⟩ : syracuseStep 1960735 = 2941103) B2941103
theorem B2614313 : Blo 1742572 2614313 := bstep (se 2 (by rfl) ⟨980367, by rfl⟩ : syracuseStep 2614313 = 1960735) B1960735
theorem B1742875 : Blo 1742572 1742875 := bstep (se 1 (by rfl) ⟨1307156, by rfl⟩ : syracuseStep 1742875 = 2614313) B2614313

theorem C0 (j : ℕ) (h1 : 435643 ≤ j) (h2 : j ≤ 436142) : Blo 1742572 (4 * j + 3) := by
  interval_cases j
  · exact B1742575
  · exact B1742579
  · exact B1742583
  · exact B1742587
  · exact B1742591
  · exact B1742595
  · exact B1742599
  · exact B1742603
  · exact B1742607
  · exact B1742611
  · exact B1742615
  · exact B1742619
  · exact B1742623
  · exact B1742627
  · exact B1742631
  · exact B1742635
  · exact B1742639
  · exact B1742643
  · exact B1742647
  · exact B1742651
  · exact B1742655
  · exact B1742659
  · exact B1742663
  · exact B1742667
  · exact B1742671
  · exact B1742675
  · exact B1742679
  · exact B1742683
  · exact B1742687
  · exact B1742691
  · exact B1742695
  · exact B1742699
  · exact B1742703
  · exact B1742707
  · exact B1742711
  · exact B1742715
  · exact B1742719
  · exact B1742723
  · exact B1742727
  · exact B1742731
  · exact B1742735
  · exact B1742739
  · exact B1742743
  · exact B1742747
  · exact B1742751
  · exact B1742755
  · exact B1742759
  · exact B1742763
  · exact B1742767
  · exact B1742771
  · exact B1742775
  · exact B1742779
  · exact B1742783
  · exact B1742787
  · exact B1742791
  · exact B1742795
  · exact B1742799
  · exact B1742803
  · exact B1742807
  · exact B1742811
  · exact B1742815
  · exact B1742819
  · exact B1742823
  · exact B1742827
  · exact B1742831
  · exact B1742835
  · exact B1742839
  · exact B1742843
  · exact B1742847
  · exact B1742851
  · exact B1742855
  · exact B1742859
  · exact B1742863
  · exact B1742867
  · exact B1742871
  · exact B1742875
  · exact B1742879
  · exact B1742883
  · exact B1742887
  · exact B1742891
  · exact B1742895
  · exact B1742899
  · exact B1742903
  · exact B1742907
  · exact B1742911
  · exact B1742915
  · exact B1742919
  · exact B1742923
  · exact B1742927
  · exact B1742931
  · exact B1742935
  · exact B1742939
  · exact B1742943
  · exact B1742947
  · exact B1742951
  · exact B1742955
  · exact B1742959
  · exact B1742963
  · exact B1742967
  · exact B1742971
  · exact B1742975
  · exact B1742979
  · exact B1742983
  · exact B1742987
  · exact B1742991
  · exact B1742995
  · exact B1742999
  · exact B1743003
  · exact B1743007
  · exact B1743011
  · exact B1743015
  · exact B1743019
  · exact B1743023
  · exact B1743027
  · exact B1743031
  · exact B1743035
  · exact B1743039
  · exact B1743043
  · exact B1743047
  · exact B1743051
  · exact B1743055
  · exact B1743059
  · exact B1743063
  · exact B1743067
  · exact B1743071
  · exact B1743075
  · exact B1743079
  · exact B1743083
  · exact B1743087
  · exact B1743091
  · exact B1743095
  · exact B1743099
  · exact B1743103
  · exact B1743107
  · exact B1743111
  · exact B1743115
  · exact B1743119
  · exact B1743123
  · exact B1743127
  · exact B1743131
  · exact B1743135
  · exact B1743139
  · exact B1743143
  · exact B1743147
  · exact B1743151
  · exact B1743155
  · exact B1743159
  · exact B1743163
  · exact B1743167
  · exact B1743171
  · exact B1743175
  · exact B1743179
  · exact B1743183
  · exact B1743187
  · exact B1743191
  · exact B1743195
  · exact B1743199
  · exact B1743203
  · exact B1743207
  · exact B1743211
  · exact B1743215
  · exact B1743219
  · exact B1743223
  · exact B1743227
  · exact B1743231
  · exact B1743235
  · exact B1743239
  · exact B1743243
  · exact B1743247
  · exact B1743251
  · exact B1743255
  · exact B1743259
  · exact B1743263
  · exact B1743267
  · exact B1743271
  · exact B1743275
  · exact B1743279
  · exact B1743283
  · exact B1743287
  · exact B1743291
  · exact B1743295
  · exact B1743299
  · exact B1743303
  · exact B1743307
  · exact B1743311
  · exact B1743315
  · exact B1743319
  · exact B1743323
  · exact B1743327
  · exact B1743331
  · exact B1743335
  · exact B1743339
  · exact B1743343
  · exact B1743347
  · exact B1743351
  · exact B1743355
  · exact B1743359
  · exact B1743363
  · exact B1743367
  · exact B1743371
  · exact B1743375
  · exact B1743379
  · exact B1743383
  · exact B1743387
  · exact B1743391
  · exact B1743395
  · exact B1743399
  · exact B1743403
  · exact B1743407
  · exact B1743411
  · exact B1743415
  · exact B1743419
  · exact B1743423
  · exact B1743427
  · exact B1743431
  · exact B1743435
  · exact B1743439
  · exact B1743443
  · exact B1743447
  · exact B1743451
  · exact B1743455
  · exact B1743459
  · exact B1743463
  · exact B1743467
  · exact B1743471
  · exact B1743475
  · exact B1743479
  · exact B1743483
  · exact B1743487
  · exact B1743491
  · exact B1743495
  · exact B1743499
  · exact B1743503
  · exact B1743507
  · exact B1743511
  · exact B1743515
  · exact B1743519
  · exact B1743523
  · exact B1743527
  · exact B1743531
  · exact B1743535
  · exact B1743539
  · exact B1743543
  · exact B1743547
  · exact B1743551
  · exact B1743555
  · exact B1743559
  · exact B1743563
  · exact B1743567
  · exact B1743571
  · exact B1743575
  · exact B1743579
  · exact B1743583
  · exact B1743587
  · exact B1743591
  · exact B1743595
  · exact B1743599
  · exact B1743603
  · exact B1743607
  · exact B1743611
  · exact B1743615
  · exact B1743619
  · exact B1743623
  · exact B1743627
  · exact B1743631
  · exact B1743635
  · exact B1743639
  · exact B1743643
  · exact B1743647
  · exact B1743651
  · exact B1743655
  · exact B1743659
  · exact B1743663
  · exact B1743667
  · exact B1743671
  · exact B1743675
  · exact B1743679
  · exact B1743683
  · exact B1743687
  · exact B1743691
  · exact B1743695
  · exact B1743699
  · exact B1743703
  · exact B1743707
  · exact B1743711
  · exact B1743715
  · exact B1743719
  · exact B1743723
  · exact B1743727
  · exact B1743731
  · exact B1743735
  · exact B1743739
  · exact B1743743
  · exact B1743747
  · exact B1743751
  · exact B1743755
  · exact B1743759
  · exact B1743763
  · exact B1743767
  · exact B1743771
  · exact B1743775
  · exact B1743779
  · exact B1743783
  · exact B1743787
  · exact B1743791
  · exact B1743795
  · exact B1743799
  · exact B1743803
  · exact B1743807
  · exact B1743811
  · exact B1743815
  · exact B1743819
  · exact B1743823
  · exact B1743827
  · exact B1743831
  · exact B1743835
  · exact B1743839
  · exact B1743843
  · exact B1743847
  · exact B1743851
  · exact B1743855
  · exact B1743859
  · exact B1743863
  · exact B1743867
  · exact B1743871
  · exact B1743875
  · exact B1743879
  · exact B1743883
  · exact B1743887
  · exact B1743891
  · exact B1743895
  · exact B1743899
  · exact B1743903
  · exact B1743907
  · exact B1743911
  · exact B1743915
  · exact B1743919
  · exact B1743923
  · exact B1743927
  · exact B1743931
  · exact B1743935
  · exact B1743939
  · exact B1743943
  · exact B1743947
  · exact B1743951
  · exact B1743955
  · exact B1743959
  · exact B1743963
  · exact B1743967
  · exact B1743971
  · exact B1743975
  · exact B1743979
  · exact B1743983
  · exact B1743987
  · exact B1743991
  · exact B1743995
  · exact B1743999
  · exact B1744003
  · exact B1744007
  · exact B1744011
  · exact B1744015
  · exact B1744019
  · exact B1744023
  · exact B1744027
  · exact B1744031
  · exact B1744035
  · exact B1744039
  · exact B1744043
  · exact B1744047
  · exact B1744051
  · exact B1744055
  · exact B1744059
  · exact B1744063
  · exact B1744067
  · exact B1744071
  · exact B1744075
  · exact B1744079
  · exact B1744083
  · exact B1744087
  · exact B1744091
  · exact B1744095
  · exact B1744099
  · exact B1744103
  · exact B1744107
  · exact B1744111
  · exact B1744115
  · exact B1744119
  · exact B1744123
  · exact B1744127
  · exact B1744131
  · exact B1744135
  · exact B1744139
  · exact B1744143
  · exact B1744147
  · exact B1744151
  · exact B1744155
  · exact B1744159
  · exact B1744163
  · exact B1744167
  · exact B1744171
  · exact B1744175
  · exact B1744179
  · exact B1744183
  · exact B1744187
  · exact B1744191
  · exact B1744195
  · exact B1744199
  · exact B1744203
  · exact B1744207
  · exact B1744211
  · exact B1744215
  · exact B1744219
  · exact B1744223
  · exact B1744227
  · exact B1744231
  · exact B1744235
  · exact B1744239
  · exact B1744243
  · exact B1744247
  · exact B1744251
  · exact B1744255
  · exact B1744259
  · exact B1744263
  · exact B1744267
  · exact B1744271
  · exact B1744275
  · exact B1744279
  · exact B1744283
  · exact B1744287
  · exact B1744291
  · exact B1744295
  · exact B1744299
  · exact B1744303
  · exact B1744307
  · exact B1744311
  · exact B1744315
  · exact B1744319
  · exact B1744323
  · exact B1744327
  · exact B1744331
  · exact B1744335
  · exact B1744339
  · exact B1744343
  · exact B1744347
  · exact B1744351
  · exact B1744355
  · exact B1744359
  · exact B1744363
  · exact B1744367
  · exact B1744371
  · exact B1744375
  · exact B1744379
  · exact B1744383
  · exact B1744387
  · exact B1744391
  · exact B1744395
  · exact B1744399
  · exact B1744403
  · exact B1744407
  · exact B1744411
  · exact B1744415
  · exact B1744419
  · exact B1744423
  · exact B1744427
  · exact B1744431
  · exact B1744435
  · exact B1744439
  · exact B1744443
  · exact B1744447
  · exact B1744451
  · exact B1744455
  · exact B1744459
  · exact B1744463
  · exact B1744467
  · exact B1744471
  · exact B1744475
  · exact B1744479
  · exact B1744483
  · exact B1744487
  · exact B1744491
  · exact B1744495
  · exact B1744499
  · exact B1744503
  · exact B1744507
  · exact B1744511
  · exact B1744515
  · exact B1744519
  · exact B1744523
  · exact B1744527
  · exact B1744531
  · exact B1744535
  · exact B1744539
  · exact B1744543
  · exact B1744547
  · exact B1744551
  · exact B1744555
  · exact B1744559
  · exact B1744563
  · exact B1744567
  · exact B1744571

theorem solution (m : ℕ) (hlo : 1742572 ≤ m) (hhi : m ≤ 1744572) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 435643 ≤ j := by omega
    have hj2 : j ≤ 436142 := by omega
    have hb : Blo 1742572 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
