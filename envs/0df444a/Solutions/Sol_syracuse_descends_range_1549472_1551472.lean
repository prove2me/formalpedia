-- Prove2me | solution 1 for syracuse_descends_range_1549472_1551472
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:37.773667+00:00
-- url     : https://prove2.me/submissions/e9bcfa37-9137-459f-8ccc-66dc3dba0d05

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


theorem B1744897 : Blo 1549472 1744897 := bbase (se 2 (by rfl) ⟨654336, by rfl⟩ : syracuseStep 1744897 = 1308673) (by norm_num)
theorem B3309581 : Blo 1549472 3309581 := bbase (se 3 (by rfl) ⟨620546, by rfl⟩ : syracuseStep 3309581 = 1241093) (by norm_num)
theorem B2326541 : Blo 1549472 2326541 := bbase (se 3 (by rfl) ⟨436226, by rfl⟩ : syracuseStep 2326541 = 872453) (by norm_num)
theorem B3489821 : Blo 1549472 3489821 := bbase (se 3 (by rfl) ⟨654341, by rfl⟩ : syracuseStep 3489821 = 1308683) (by norm_num)
theorem B2326565 : Blo 1549472 2326565 := bbase (se 4 (by rfl) ⟨218115, by rfl⟩ : syracuseStep 2326565 = 436231) (by norm_num)
theorem B1744933 : Blo 1549472 1744933 := bbase (se 4 (by rfl) ⟨163587, by rfl⟩ : syracuseStep 1744933 = 327175) (by norm_num)
theorem B2326589 : Blo 1549472 2326589 := bbase (se 3 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 2326589 = 872471) (by norm_num)
theorem B1744969 : Blo 1549472 1744969 := bbase (se 2 (by rfl) ⟨654363, by rfl⟩ : syracuseStep 1744969 = 1308727) (by norm_num)
theorem B2326613 : Blo 1549472 2326613 := bbase (se 8 (by rfl) ⟨13632, by rfl⟩ : syracuseStep 2326613 = 27265) (by norm_num)
theorem B3489893 : Blo 1549472 3489893 := bbase (se 4 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 3489893 = 654355) (by norm_num)
theorem B2326637 : Blo 1549472 2326637 := bbase (se 3 (by rfl) ⟨436244, by rfl⟩ : syracuseStep 2326637 = 872489) (by norm_num)
theorem B1745005 : Blo 1549472 1745005 := bbase (se 3 (by rfl) ⟨327188, by rfl⟩ : syracuseStep 1745005 = 654377) (by norm_num)
theorem B3924085 : Blo 1549472 3924085 := bbase (se 5 (by rfl) ⟨183941, by rfl⟩ : syracuseStep 3924085 = 367883) (by norm_num)
theorem B2326661 : Blo 1549472 2326661 := bbase (se 4 (by rfl) ⟨218124, by rfl⟩ : syracuseStep 2326661 = 436249) (by norm_num)
theorem B1745041 : Blo 1549472 1745041 := bbase (se 2 (by rfl) ⟨654390, by rfl⟩ : syracuseStep 1745041 = 1308781) (by norm_num)
theorem B2326685 : Blo 1549472 2326685 := bbase (se 3 (by rfl) ⟨436253, by rfl⟩ : syracuseStep 2326685 = 872507) (by norm_num)
theorem B3489965 : Blo 1549472 3489965 := bbase (se 3 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 3489965 = 1308737) (by norm_num)
theorem B2326709 : Blo 1549472 2326709 := bbase (se 5 (by rfl) ⟨109064, by rfl⟩ : syracuseStep 2326709 = 218129) (by norm_num)
theorem B4538549 : Blo 1549472 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1745077 : Blo 1549472 1745077 := bbase (se 5 (by rfl) ⟨81800, by rfl⟩ : syracuseStep 1745077 = 163601) (by norm_num)
theorem B5890229 : Blo 1549472 5890229 := bbase (se 5 (by rfl) ⟨276104, by rfl⟩ : syracuseStep 5890229 = 552209) (by norm_num)
theorem B2326733 : Blo 1549472 2326733 := bbase (se 3 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 2326733 = 872525) (by norm_num)
theorem B1745113 : Blo 1549472 1745113 := bbase (se 2 (by rfl) ⟨654417, by rfl⟩ : syracuseStep 1745113 = 1308835) (by norm_num)
theorem B3924197 : Blo 1549472 3924197 := bbase (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) (by norm_num)
theorem B2326757 : Blo 1549472 2326757 := bbase (se 4 (by rfl) ⟨218133, by rfl⟩ : syracuseStep 2326757 = 436267) (by norm_num)
theorem B3490037 : Blo 1549472 3490037 := bbase (se 5 (by rfl) ⟨163595, by rfl⟩ : syracuseStep 3490037 = 327191) (by norm_num)
theorem B2326781 : Blo 1549472 2326781 := bbase (se 3 (by rfl) ⟨436271, by rfl⟩ : syracuseStep 2326781 = 872543) (by norm_num)
theorem B1745149 : Blo 1549472 1745149 := bbase (se 3 (by rfl) ⟨327215, by rfl⟩ : syracuseStep 1745149 = 654431) (by norm_num)
theorem B2326805 : Blo 1549472 2326805 := bbase (se 6 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 2326805 = 109069) (by norm_num)
theorem B1745185 : Blo 1549472 1745185 := bbase (se 2 (by rfl) ⟨654444, by rfl⟩ : syracuseStep 1745185 = 1308889) (by norm_num)
theorem B2326829 : Blo 1549472 2326829 := bbase (se 3 (by rfl) ⟨436280, by rfl⟩ : syracuseStep 2326829 = 872561) (by norm_num)
theorem B2482493 : Blo 1549472 2482493 := bbase (se 3 (by rfl) ⟨465467, by rfl⟩ : syracuseStep 2482493 = 930935) (by norm_num)
theorem B3490109 : Blo 1549472 3490109 := bbase (se 3 (by rfl) ⟨654395, by rfl⟩ : syracuseStep 3490109 = 1308791) (by norm_num)
theorem B2326853 : Blo 1549472 2326853 := bbase (se 4 (by rfl) ⟨218142, by rfl⟩ : syracuseStep 2326853 = 436285) (by norm_num)
theorem B1745221 : Blo 1549472 1745221 := bbase (se 4 (by rfl) ⟨163614, by rfl⟩ : syracuseStep 1745221 = 327229) (by norm_num)
theorem B5235029 : Blo 1549472 5235029 := bbase (se 10 (by rfl) ⟨7668, by rfl⟩ : syracuseStep 5235029 = 15337) (by norm_num)
theorem B2326877 : Blo 1549472 2326877 := bbase (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) (by norm_num)
theorem B1745257 : Blo 1549472 1745257 := bbase (se 2 (by rfl) ⟨654471, by rfl⟩ : syracuseStep 1745257 = 1308943) (by norm_num)
theorem B2326901 : Blo 1549472 2326901 := bbase (se 5 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 2326901 = 218147) (by norm_num)
theorem B3490181 : Blo 1549472 3490181 := bbase (se 4 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 3490181 = 654409) (by norm_num)
theorem B2326925 : Blo 1549472 2326925 := bbase (se 3 (by rfl) ⟨436298, by rfl⟩ : syracuseStep 2326925 = 872597) (by norm_num)
theorem B1745293 : Blo 1549472 1745293 := bbase (se 3 (by rfl) ⟨327242, by rfl⟩ : syracuseStep 1745293 = 654485) (by norm_num)
theorem B3924389 : Blo 1549472 3924389 := bbase (se 4 (by rfl) ⟨367911, by rfl⟩ : syracuseStep 3924389 = 735823) (by norm_num)
theorem B2326949 : Blo 1549472 2326949 := bbase (se 4 (by rfl) ⟨218151, by rfl⟩ : syracuseStep 2326949 = 436303) (by norm_num)
theorem B1745329 : Blo 1549472 1745329 := bbase (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) (by norm_num)
theorem B13246901 : Blo 1549472 13246901 := bbase (se 5 (by rfl) ⟨620948, by rfl⟩ : syracuseStep 13246901 = 1241897) (by norm_num)
theorem B2326973 : Blo 1549472 2326973 := bbase (se 3 (by rfl) ⟨436307, by rfl⟩ : syracuseStep 2326973 = 872615) (by norm_num)
theorem B3490253 : Blo 1549472 3490253 := bbase (se 3 (by rfl) ⟨654422, by rfl⟩ : syracuseStep 3490253 = 1308845) (by norm_num)
theorem B2326997 : Blo 1549472 2326997 := bbase (se 7 (by rfl) ⟨27269, by rfl⟩ : syracuseStep 2326997 = 54539) (by norm_num)
theorem B1745365 : Blo 1549472 1745365 := bbase (se 7 (by rfl) ⟨20453, by rfl⟩ : syracuseStep 1745365 = 40907) (by norm_num)
theorem B2327021 : Blo 1549472 2327021 := bbase (se 3 (by rfl) ⟨436316, by rfl⟩ : syracuseStep 2327021 = 872633) (by norm_num)
theorem B1745401 : Blo 1549472 1745401 := bbase (se 2 (by rfl) ⟨654525, by rfl⟩ : syracuseStep 1745401 = 1309051) (by norm_num)
theorem B3310085 : Blo 1549472 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B7168517 : Blo 1549472 7168517 := bbase (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) (by norm_num)
theorem B2327045 : Blo 1549472 2327045 := bbase (se 4 (by rfl) ⟨218160, by rfl⟩ : syracuseStep 2327045 = 436321) (by norm_num)
theorem B3310093 : Blo 1549472 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B4964885 : Blo 1549472 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B3490325 : Blo 1549472 3490325 := bbase (se 6 (by rfl) ⟨81804, by rfl⟩ : syracuseStep 3490325 = 163609) (by norm_num)
theorem B2327069 : Blo 1549472 2327069 := bbase (se 3 (by rfl) ⟨436325, by rfl⟩ : syracuseStep 2327069 = 872651) (by norm_num)
theorem B2327093 : Blo 1549472 2327093 := bbase (se 5 (by rfl) ⟨109082, by rfl⟩ : syracuseStep 2327093 = 218165) (by norm_num)
theorem B2327117 : Blo 1549472 2327117 := bbase (se 3 (by rfl) ⟨436334, by rfl⟩ : syracuseStep 2327117 = 872669) (by norm_num)
theorem B3490397 : Blo 1549472 3490397 := bbase (se 3 (by rfl) ⟨654449, by rfl⟩ : syracuseStep 3490397 = 1308899) (by norm_num)
theorem B2327141 : Blo 1549472 2327141 := bbase (se 4 (by rfl) ⟨218169, by rfl⟩ : syracuseStep 2327141 = 436339) (by norm_num)
theorem B2327165 : Blo 1549472 2327165 := bbase (se 3 (by rfl) ⟨436343, by rfl⟩ : syracuseStep 2327165 = 872687) (by norm_num)
theorem B2327189 : Blo 1549472 2327189 := bbase (se 6 (by rfl) ⟨54543, by rfl⟩ : syracuseStep 2327189 = 109087) (by norm_num)
theorem B3490469 : Blo 1549472 3490469 := bbase (se 4 (by rfl) ⟨327231, by rfl⟩ : syracuseStep 3490469 = 654463) (by norm_num)
theorem B3023581 : Blo 1549472 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B1655525 : Blo 1549472 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B7660261 : Blo 1549472 7660261 := bbase (se 4 (by rfl) ⟨718149, by rfl⟩ : syracuseStep 7660261 = 1436299) (by norm_num)
theorem B3490541 : Blo 1549472 3490541 := bbase (se 3 (by rfl) ⟨654476, by rfl⟩ : syracuseStep 3490541 = 1308953) (by norm_num)
theorem B3924733 : Blo 1549472 3924733 := bbase (se 3 (by rfl) ⟨735887, by rfl⟩ : syracuseStep 3924733 = 1471775) (by norm_num)
theorem B5235461 : Blo 1549472 5235461 := bbase (se 4 (by rfl) ⟨490824, by rfl⟩ : syracuseStep 5235461 = 981649) (by norm_num)
theorem B3490613 : Blo 1549472 3490613 := bbase (se 5 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 3490613 = 327245) (by norm_num)
theorem B2794333 : Blo 1549472 2794333 := bbase (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) (by norm_num)
theorem B2483045 : Blo 1549472 2483045 := bbase (se 4 (by rfl) ⟨232785, by rfl⟩ : syracuseStep 2483045 = 465571) (by norm_num)
theorem B3924845 : Blo 1549472 3924845 := bbase (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) (by norm_num)
theorem B4416373 : Blo 1549472 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B3490685 : Blo 1549472 3490685 := bbase (se 3 (by rfl) ⟨654503, by rfl⟩ : syracuseStep 3490685 = 1309007) (by norm_num)
theorem B2483077 : Blo 1549472 2483077 := bbase (se 4 (by rfl) ⟨232788, by rfl⟩ : syracuseStep 2483077 = 465577) (by norm_num)
theorem B3490757 : Blo 1549472 3490757 := bbase (se 4 (by rfl) ⟨327258, by rfl⟩ : syracuseStep 3490757 = 654517) (by norm_num)
theorem B2941933 : Blo 1549472 2941933 := bbase (se 3 (by rfl) ⟨551612, by rfl⟩ : syracuseStep 2941933 = 1103225) (by norm_num)
theorem B3925037 : Blo 1549472 3925037 := bbase (se 3 (by rfl) ⟨735944, by rfl⟩ : syracuseStep 3925037 = 1471889) (by norm_num)
theorem B5104709 : Blo 1549472 5104709 := bbase (se 4 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 5104709 = 957133) (by norm_num)
theorem B7849061 : Blo 1549472 7849061 := bbase (se 4 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 7849061 = 1471699) (by norm_num)
theorem B2516093 : Blo 1549472 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B2942077 : Blo 1549472 2942077 := bbase (se 3 (by rfl) ⟨551639, by rfl⟩ : syracuseStep 2942077 = 1103279) (by norm_num)
theorem B2794637 : Blo 1549472 2794637 := bbase (se 3 (by rfl) ⟨523994, by rfl⟩ : syracuseStep 2794637 = 1047989) (by norm_num)
theorem B1655969 : Blo 1549472 1655969 := bbase (se 2 (by rfl) ⟨620988, by rfl⟩ : syracuseStep 1655969 = 1241977) (by norm_num)
theorem B5235893 : Blo 1549472 5235893 := bbase (se 5 (by rfl) ⟨245432, by rfl⟩ : syracuseStep 5235893 = 490865) (by norm_num)
theorem B2123029 : Blo 1549472 2123029 := bbase (se 6 (by rfl) ⟨49758, by rfl⟩ : syracuseStep 2123029 = 99517) (by norm_num)
theorem B2942237 : Blo 1549472 2942237 := bbase (se 3 (by rfl) ⟨551669, by rfl⟩ : syracuseStep 2942237 = 1103339) (by norm_num)
theorem B3925381 : Blo 1549472 3925381 := bbase (se 4 (by rfl) ⟨368004, by rfl⟩ : syracuseStep 3925381 = 736009) (by norm_num)
theorem B4965781 : Blo 1549472 4965781 := bbase (se 6 (by rfl) ⟨116385, by rfl⟩ : syracuseStep 4965781 = 232771) (by norm_num)
theorem B1656217 : Blo 1549472 1656217 := bbase (se 2 (by rfl) ⟨621081, by rfl⟩ : syracuseStep 1656217 = 1242163) (by norm_num)
theorem B2942381 : Blo 1549472 2942381 := bbase (se 3 (by rfl) ⟨551696, by rfl⟩ : syracuseStep 2942381 = 1103393) (by norm_num)
theorem B3925493 : Blo 1549472 3925493 := bbase (se 5 (by rfl) ⟨184007, by rfl⟩ : syracuseStep 3925493 = 368015) (by norm_num)
theorem B2614781 : Blo 1549472 2614781 := bbase (se 3 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 2614781 = 980543) (by norm_num)
theorem B3311221 : Blo 1549472 3311221 := bbase (se 5 (by rfl) ⟨155213, by rfl⟩ : syracuseStep 3311221 = 310427) (by norm_num)
theorem B2614909 : Blo 1549472 2614909 := bbase (se 3 (by rfl) ⟨490295, by rfl⟩ : syracuseStep 2614909 = 980591) (by norm_num)
theorem B8382133 : Blo 1549472 8382133 := bbase (se 5 (by rfl) ⟨392912, by rfl⟩ : syracuseStep 8382133 = 785825) (by norm_num)
theorem B3925685 : Blo 1549472 3925685 := bbase (se 5 (by rfl) ⟨184016, by rfl⟩ : syracuseStep 3925685 = 368033) (by norm_num)
theorem B6620869 : Blo 1549472 6620869 := bbase (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) (by norm_num)
theorem B2942669 : Blo 1549472 2942669 := bbase (se 3 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 2942669 = 1103501) (by norm_num)
theorem B2614997 : Blo 1549472 2614997 := bbase (se 7 (by rfl) ⟨30644, by rfl⟩ : syracuseStep 2614997 = 61289) (by norm_num)
theorem B8832725 : Blo 1549472 8832725 := bbase (se 7 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 8832725 = 207017) (by norm_num)
theorem B5883637 : Blo 1549472 5883637 := bbase (se 5 (by rfl) ⟨275795, by rfl⟩ : syracuseStep 5883637 = 551591) (by norm_num)
theorem B2017045 : Blo 1549472 2017045 := bbase (se 6 (by rfl) ⟨47274, by rfl⟩ : syracuseStep 2017045 = 94549) (by norm_num)
theorem B2484005 : Blo 1549472 2484005 := bbase (se 4 (by rfl) ⟨232875, by rfl⟩ : syracuseStep 2484005 = 465751) (by norm_num)
theorem B1656649 : Blo 1549472 1656649 := bbase (se 2 (by rfl) ⟨621243, by rfl⟩ : syracuseStep 1656649 = 1242487) (by norm_num)
theorem B2615125 : Blo 1549472 2615125 := bbase (se 9 (by rfl) ⟨7661, by rfl⟩ : syracuseStep 2615125 = 15323) (by norm_num)
theorem B2942821 : Blo 1549472 2942821 := bbase (se 4 (by rfl) ⟨275889, by rfl⟩ : syracuseStep 2942821 = 551779) (by norm_num)
theorem B1656721 : Blo 1549472 1656721 := bbase (se 2 (by rfl) ⟨621270, by rfl⟩ : syracuseStep 1656721 = 1242541) (by norm_num)
theorem B2869141 : Blo 1549472 2869141 := bbase (se 6 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 2869141 = 134491) (by norm_num)
theorem B14903189 : Blo 1549472 14903189 := bbase (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) (by norm_num)
theorem B14149525 : Blo 1549472 14149525 := bbase (se 6 (by rfl) ⟨331629, by rfl⟩ : syracuseStep 14149525 = 663259) (by norm_num)
theorem B2615213 : Blo 1549472 2615213 := bbase (se 3 (by rfl) ⟨490352, by rfl⟩ : syracuseStep 2615213 = 980705) (by norm_num)
theorem B1861553 : Blo 1549472 1861553 := bbase (se 2 (by rfl) ⟨698082, by rfl⟩ : syracuseStep 1861553 = 1396165) (by norm_num)
theorem B5105605 : Blo 1549472 5105605 := bbase (se 4 (by rfl) ⟨478650, by rfl⟩ : syracuseStep 5105605 = 957301) (by norm_num)
theorem B3311597 : Blo 1549472 3311597 := bbase (se 3 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 3311597 = 1241849) (by norm_num)
theorem B3926029 : Blo 1549472 3926029 := bbase (se 3 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 3926029 = 1472261) (by norm_num)
theorem B2517013 : Blo 1549472 2517013 := bbase (se 6 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 2517013 = 117985) (by norm_num)
theorem B5883941 : Blo 1549472 5883941 := bbase (se 4 (by rfl) ⟨551619, by rfl⟩ : syracuseStep 5883941 = 1103239) (by norm_num)
theorem B2615341 : Blo 1549472 2615341 := bbase (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) (by norm_num)
theorem B2795573 : Blo 1549472 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B3926141 : Blo 1549472 3926141 := bbase (se 3 (by rfl) ⟨736151, by rfl⟩ : syracuseStep 3926141 = 1472303) (by norm_num)
theorem B2615429 : Blo 1549472 2615429 := bbase (se 4 (by rfl) ⟨245196, by rfl⟩ : syracuseStep 2615429 = 490393) (by norm_num)
theorem B2943125 : Blo 1549472 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B1861861 : Blo 1549472 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B2615557 : Blo 1549472 2615557 := bbase (se 4 (by rfl) ⟨245208, by rfl⟩ : syracuseStep 2615557 = 490417) (by norm_num)
theorem B3926333 : Blo 1549472 3926333 := bbase (se 3 (by rfl) ⟨736187, by rfl⟩ : syracuseStep 3926333 = 1472375) (by norm_num)
theorem B4417877 : Blo 1549472 4417877 := bbase (se 10 (by rfl) ⟨6471, by rfl⟩ : syracuseStep 4417877 = 12943) (by norm_num)
theorem B2615645 : Blo 1549472 2615645 := bbase (se 3 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 2615645 = 980867) (by norm_num)
theorem B7850357 : Blo 1549472 7850357 := bbase (se 5 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 7850357 = 735971) (by norm_num)
theorem B1862077 : Blo 1549472 1862077 := bbase (se 3 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 1862077 = 698279) (by norm_num)
theorem B2484685 : Blo 1549472 2484685 := bbase (se 3 (by rfl) ⟨465878, by rfl⟩ : syracuseStep 2484685 = 931757) (by norm_num)
theorem B2615773 : Blo 1549472 2615773 := bbase (se 3 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 2615773 = 980915) (by norm_num)
theorem B6375925 : Blo 1549472 6375925 := bbase (se 5 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 6375925 = 597743) (by norm_num)
theorem B2484749 : Blo 1549472 2484749 := bbase (se 3 (by rfl) ⟨465890, by rfl⟩ : syracuseStep 2484749 = 931781) (by norm_num)
theorem B2615861 : Blo 1549472 2615861 := bbase (se 5 (by rfl) ⟨122618, by rfl⟩ : syracuseStep 2615861 = 245237) (by norm_num)
theorem B2517637 : Blo 1549472 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B3926677 : Blo 1549472 3926677 := bbase (se 6 (by rfl) ⟨92031, by rfl⟩ : syracuseStep 3926677 = 184063) (by norm_num)
theorem B2615989 : Blo 1549472 2615989 := bbase (se 5 (by rfl) ⟨122624, by rfl⟩ : syracuseStep 2615989 = 245249) (by norm_num)
theorem B5663429 : Blo 1549472 5663429 := bbase (se 4 (by rfl) ⟨530946, by rfl⟩ : syracuseStep 5663429 = 1061893) (by norm_num)
theorem B1862389 : Blo 1549472 1862389 := bbase (se 5 (by rfl) ⟨87299, by rfl⟩ : syracuseStep 1862389 = 174599) (by norm_num)
theorem B3926789 : Blo 1549472 3926789 := bbase (se 4 (by rfl) ⟨368136, by rfl⟩ : syracuseStep 3926789 = 736273) (by norm_num)
theorem B2616077 : Blo 1549472 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B2206541 : Blo 1549472 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B2943877 : Blo 1549472 2943877 := bbase (se 4 (by rfl) ⟨275988, by rfl⟩ : syracuseStep 2943877 = 551977) (by norm_num)
theorem B2616205 : Blo 1549472 2616205 := bbase (se 3 (by rfl) ⟨490538, by rfl⟩ : syracuseStep 2616205 = 981077) (by norm_num)
theorem B15944597 : Blo 1549472 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B3926981 : Blo 1549472 3926981 := bbase (se 4 (by rfl) ⟨368154, by rfl⟩ : syracuseStep 3926981 = 736309) (by norm_num)
theorem B2616293 : Blo 1549472 2616293 := bbase (se 4 (by rfl) ⟨245277, by rfl⟩ : syracuseStep 2616293 = 490555) (by norm_num)
theorem B2944021 : Blo 1549472 2944021 := bbase (se 6 (by rfl) ⟨69000, by rfl⟩ : syracuseStep 2944021 = 138001) (by norm_num)
theorem B2616421 : Blo 1549472 2616421 := bbase (se 4 (by rfl) ⟨245289, by rfl⟩ : syracuseStep 2616421 = 490579) (by norm_num)
theorem B1961101 : Blo 1549472 1961101 := bbase (se 3 (by rfl) ⟨367706, by rfl⟩ : syracuseStep 1961101 = 735413) (by norm_num)
theorem B6622357 : Blo 1549472 6622357 := bbase (se 6 (by rfl) ⟨155211, by rfl⟩ : syracuseStep 6622357 = 310423) (by norm_num)
theorem B6622373 : Blo 1549472 6622373 := bbase (se 4 (by rfl) ⟨620847, by rfl⟩ : syracuseStep 6622373 = 1241695) (by norm_num)
theorem B2944181 : Blo 1549472 2944181 := bbase (se 5 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 2944181 = 276017) (by norm_num)
theorem B2616509 : Blo 1549472 2616509 := bbase (se 3 (by rfl) ⟨490595, by rfl⟩ : syracuseStep 2616509 = 981191) (by norm_num)
theorem B4246757 : Blo 1549472 4246757 := bbase (se 4 (by rfl) ⟨398133, by rfl⟩ : syracuseStep 4246757 = 796267) (by norm_num)
theorem B5229845 : Blo 1549472 5229845 := bbase (se 6 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 5229845 = 245149) (by norm_num)
theorem B25849109 : Blo 1549472 25849109 := bbase (se 6 (by rfl) ⟨605838, by rfl⟩ : syracuseStep 25849109 = 1211677) (by norm_num)
theorem B1961273 : Blo 1549472 1961273 := bbase (se 2 (by rfl) ⟨735477, by rfl⟩ : syracuseStep 1961273 = 1470955) (by norm_num)
theorem B2616637 : Blo 1549472 2616637 := bbase (se 3 (by rfl) ⟨490619, by rfl⟩ : syracuseStep 2616637 = 981239) (by norm_num)
theorem B2944325 : Blo 1549472 2944325 := bbase (se 4 (by rfl) ⟨276030, by rfl⟩ : syracuseStep 2944325 = 552061) (by norm_num)
theorem B22646101 : Blo 1549472 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B1961329 : Blo 1549472 1961329 := bbase (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) (by norm_num)
theorem B2207093 : Blo 1549472 2207093 := bbase (se 5 (by rfl) ⟨103457, by rfl⟩ : syracuseStep 2207093 = 206915) (by norm_num)
theorem B2616725 : Blo 1549472 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B1961425 : Blo 1549472 1961425 := bbase (se 2 (by rfl) ⟨735534, by rfl⟩ : syracuseStep 1961425 = 1471069) (by norm_num)
theorem B2616853 : Blo 1549472 2616853 := bbase (se 6 (by rfl) ⟨61332, by rfl⟩ : syracuseStep 2616853 = 122665) (by norm_num)
theorem B3313237 : Blo 1549472 3313237 := bbase (se 8 (by rfl) ⟨19413, by rfl⟩ : syracuseStep 3313237 = 38827) (by norm_num)
theorem B2944613 : Blo 1549472 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B2616941 : Blo 1549472 2616941 := bbase (se 3 (by rfl) ⟨490676, by rfl⟩ : syracuseStep 2616941 = 981353) (by norm_num)
theorem B1961597 : Blo 1549472 1961597 := bbase (se 3 (by rfl) ⟨367799, by rfl⟩ : syracuseStep 1961597 = 735599) (by norm_num)
theorem B7851653 : Blo 1549472 7851653 := bbase (se 4 (by rfl) ⟨736092, by rfl⟩ : syracuseStep 7851653 = 1472185) (by norm_num)
theorem B11177621 : Blo 1549472 11177621 := bbase (se 6 (by rfl) ⟨261975, by rfl⟩ : syracuseStep 11177621 = 523951) (by norm_num)
theorem B8171189 : Blo 1549472 8171189 := bbase (se 5 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 8171189 = 766049) (by norm_num)
theorem B1961653 : Blo 1549472 1961653 := bbase (se 5 (by rfl) ⟨91952, by rfl⟩ : syracuseStep 1961653 = 183905) (by norm_num)
theorem B5230277 : Blo 1549472 5230277 := bbase (se 4 (by rfl) ⟨490338, by rfl⟩ : syracuseStep 5230277 = 980677) (by norm_num)
theorem B7450325 : Blo 1549472 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B2617069 : Blo 1549472 2617069 := bbase (se 3 (by rfl) ⟨490700, by rfl⟩ : syracuseStep 2617069 = 981401) (by norm_num)
theorem B2944765 : Blo 1549472 2944765 := bbase (se 3 (by rfl) ⟨552143, by rfl⟩ : syracuseStep 2944765 = 1104287) (by norm_num)
theorem B1961749 : Blo 1549472 1961749 := bbase (se 6 (by rfl) ⟨45978, by rfl⟩ : syracuseStep 1961749 = 91957) (by norm_num)
theorem B3141413 : Blo 1549472 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B2617157 : Blo 1549472 2617157 := bbase (se 4 (by rfl) ⟨245358, by rfl⟩ : syracuseStep 2617157 = 490717) (by norm_num)
theorem B8834933 : Blo 1549472 8834933 := bbase (se 5 (by rfl) ⟨414137, by rfl⟩ : syracuseStep 8834933 = 828275) (by norm_num)
theorem B7450517 : Blo 1549472 7450517 := bbase (se 6 (by rfl) ⟨174621, by rfl⟩ : syracuseStep 7450517 = 349243) (by norm_num)
theorem B1961921 : Blo 1549472 1961921 := bbase (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) (by norm_num)
theorem B2617285 : Blo 1549472 2617285 := bbase (se 4 (by rfl) ⟨245370, by rfl⟩ : syracuseStep 2617285 = 490741) (by norm_num)
theorem B1961977 : Blo 1549472 1961977 := bbase (se 2 (by rfl) ⟨735741, by rfl⟩ : syracuseStep 1961977 = 1471483) (by norm_num)
theorem B2617373 : Blo 1549472 2617373 := bbase (se 3 (by rfl) ⟨490757, by rfl⟩ : syracuseStep 2617373 = 981515) (by norm_num)
theorem B2945069 : Blo 1549472 2945069 := bbase (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) (by norm_num)
theorem B3723317 : Blo 1549472 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B1962073 : Blo 1549472 1962073 := bbase (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) (by norm_num)
theorem B5886053 : Blo 1549472 5886053 := bbase (se 4 (by rfl) ⟨551817, by rfl⟩ : syracuseStep 5886053 = 1103635) (by norm_num)
theorem B2207845 : Blo 1549472 2207845 := bbase (se 4 (by rfl) ⟨206985, by rfl⟩ : syracuseStep 2207845 = 413971) (by norm_num)
theorem B5230709 : Blo 1549472 5230709 := bbase (se 5 (by rfl) ⟨245189, by rfl⟩ : syracuseStep 5230709 = 490379) (by norm_num)
theorem B3723413 : Blo 1549472 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B2617501 : Blo 1549472 2617501 := bbase (se 3 (by rfl) ⟨490781, by rfl⟩ : syracuseStep 2617501 = 981563) (by norm_num)
theorem B1863869 : Blo 1549472 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B3535045 : Blo 1549472 3535045 := bbase (se 4 (by rfl) ⟨331410, by rfl⟩ : syracuseStep 3535045 = 662821) (by norm_num)
theorem B4968677 : Blo 1549472 4968677 := bbase (se 4 (by rfl) ⟨465813, by rfl⟩ : syracuseStep 4968677 = 931627) (by norm_num)
theorem B2617589 : Blo 1549472 2617589 := bbase (se 5 (by rfl) ⟨122699, by rfl⟩ : syracuseStep 2617589 = 245399) (by norm_num)
theorem B1962245 : Blo 1549472 1962245 := bbase (se 4 (by rfl) ⟨183960, by rfl⟩ : syracuseStep 1962245 = 367921) (by norm_num)
theorem B1913101 : Blo 1549472 1913101 := bbase (se 3 (by rfl) ⟨358706, by rfl⟩ : syracuseStep 1913101 = 717413) (by norm_num)
theorem B3535157 : Blo 1549472 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B4714805 : Blo 1549472 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B1962301 : Blo 1549472 1962301 := bbase (se 3 (by rfl) ⟨367931, by rfl⟩ : syracuseStep 1962301 = 735863) (by norm_num)
theorem B4714853 : Blo 1549472 4714853 := bbase (se 4 (by rfl) ⟨442017, by rfl⟩ : syracuseStep 4714853 = 884035) (by norm_num)
theorem B2617717 : Blo 1549472 2617717 := bbase (se 5 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 2617717 = 245411) (by norm_num)
theorem B5886341 : Blo 1549472 5886341 := bbase (se 4 (by rfl) ⟨551844, by rfl⟩ : syracuseStep 5886341 = 1103689) (by norm_num)
theorem B1962397 : Blo 1549472 1962397 := bbase (se 3 (by rfl) ⟨367949, by rfl⟩ : syracuseStep 1962397 = 735899) (by norm_num)
theorem B2617805 : Blo 1549472 2617805 := bbase (se 3 (by rfl) ⟨490838, by rfl⟩ : syracuseStep 2617805 = 981677) (by norm_num)
theorem B5231141 : Blo 1549472 5231141 := bbase (se 4 (by rfl) ⟨490419, by rfl⟩ : syracuseStep 5231141 = 980839) (by norm_num)
theorem B1962569 : Blo 1549472 1962569 := bbase (se 2 (by rfl) ⟨735963, by rfl⟩ : syracuseStep 1962569 = 1471927) (by norm_num)
theorem B2617933 : Blo 1549472 2617933 := bbase (se 3 (by rfl) ⟨490862, by rfl⟩ : syracuseStep 2617933 = 981725) (by norm_num)
theorem B1962625 : Blo 1549472 1962625 := bbase (se 2 (by rfl) ⟨735984, by rfl⟩ : syracuseStep 1962625 = 1471969) (by norm_num)
theorem B3486365 : Blo 1549472 3486365 := bbase (se 3 (by rfl) ⟨653693, by rfl⟩ : syracuseStep 3486365 = 1307387) (by norm_num)
theorem B2618021 : Blo 1549472 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B9425621 : Blo 1549472 9425621 := bbase (se 7 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 9425621 = 220913) (by norm_num)
theorem B1962721 : Blo 1549472 1962721 := bbase (se 2 (by rfl) ⟨736020, by rfl⟩ : syracuseStep 1962721 = 1472041) (by norm_num)
theorem B3486437 : Blo 1549472 3486437 := bbase (se 4 (by rfl) ⟨326853, by rfl⟩ : syracuseStep 3486437 = 653707) (by norm_num)
theorem B3486509 : Blo 1549472 3486509 := bbase (se 3 (by rfl) ⟨653720, by rfl⟩ : syracuseStep 3486509 = 1307441) (by norm_num)
theorem B3486581 : Blo 1549472 3486581 := bbase (se 5 (by rfl) ⟨163433, by rfl⟩ : syracuseStep 3486581 = 326867) (by norm_num)
theorem B2208637 : Blo 1549472 2208637 := bbase (se 3 (by rfl) ⟨414119, by rfl⟩ : syracuseStep 2208637 = 828239) (by norm_num)
theorem B1962893 : Blo 1549472 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B7852949 : Blo 1549472 7852949 := bbase (se 6 (by rfl) ⟨184053, by rfl⟩ : syracuseStep 7852949 = 368107) (by norm_num)
theorem B3486653 : Blo 1549472 3486653 := bbase (se 3 (by rfl) ⟨653747, by rfl⟩ : syracuseStep 3486653 = 1307495) (by norm_num)
theorem B1962949 : Blo 1549472 1962949 := bbase (se 4 (by rfl) ⟨184026, by rfl⟩ : syracuseStep 1962949 = 368053) (by norm_num)
theorem B5231573 : Blo 1549472 5231573 := bbase (se 7 (by rfl) ⟨61307, by rfl⟩ : syracuseStep 5231573 = 122615) (by norm_num)
theorem B33993685 : Blo 1549472 33993685 := bbase (se 7 (by rfl) ⟨398363, by rfl⟩ : syracuseStep 33993685 = 796727) (by norm_num)
theorem B3486725 : Blo 1549472 3486725 := bbase (se 4 (by rfl) ⟨326880, by rfl⟩ : syracuseStep 3486725 = 653761) (by norm_num)
theorem B3142685 : Blo 1549472 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B1963045 : Blo 1549472 1963045 := bbase (se 4 (by rfl) ⟨184035, by rfl⟩ : syracuseStep 1963045 = 368071) (by norm_num)
theorem B2651189 : Blo 1549472 2651189 := bbase (se 5 (by rfl) ⟨124274, by rfl⟩ : syracuseStep 2651189 = 248549) (by norm_num)
theorem B2241605 : Blo 1549472 2241605 := bbase (se 4 (by rfl) ⟨210150, by rfl⟩ : syracuseStep 2241605 = 420301) (by norm_num)
theorem B3486797 : Blo 1549472 3486797 := bbase (se 3 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 3486797 = 1307549) (by norm_num)
theorem B4412501 : Blo 1549472 4412501 := bbase (se 8 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 4412501 = 51709) (by norm_num)
theorem B3486869 : Blo 1549472 3486869 := bbase (se 6 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 3486869 = 163447) (by norm_num)
theorem B2208973 : Blo 1549472 2208973 := bbase (se 3 (by rfl) ⟨414182, by rfl⟩ : syracuseStep 2208973 = 828365) (by norm_num)
theorem B1963217 : Blo 1549472 1963217 := bbase (se 2 (by rfl) ⟨736206, by rfl⟩ : syracuseStep 1963217 = 1472413) (by norm_num)
theorem B11777237 : Blo 1549472 11777237 := bbase (se 7 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 11777237 = 276029) (by norm_num)
theorem B3486941 : Blo 1549472 3486941 := bbase (se 3 (by rfl) ⟨653801, by rfl⟩ : syracuseStep 3486941 = 1307603) (by norm_num)
theorem B1963273 : Blo 1549472 1963273 := bbase (se 2 (by rfl) ⟨736227, by rfl⟩ : syracuseStep 1963273 = 1472455) (by norm_num)
theorem B3487013 : Blo 1549472 3487013 := bbase (se 4 (by rfl) ⟨326907, by rfl⟩ : syracuseStep 3487013 = 653815) (by norm_num)
theorem B7845173 : Blo 1549472 7845173 := bbase (se 5 (by rfl) ⟨367742, by rfl⟩ : syracuseStep 7845173 = 735485) (by norm_num)
theorem B1963369 : Blo 1549472 1963369 := bbase (se 2 (by rfl) ⟨736263, by rfl⟩ : syracuseStep 1963369 = 1472527) (by norm_num)
theorem B3487085 : Blo 1549472 3487085 := bbase (se 3 (by rfl) ⟨653828, by rfl⟩ : syracuseStep 3487085 = 1307657) (by norm_num)
theorem B6624629 : Blo 1549472 6624629 := bbase (se 5 (by rfl) ⟨310529, by rfl⟩ : syracuseStep 6624629 = 621059) (by norm_num)
theorem B5232005 : Blo 1549472 5232005 := bbase (se 4 (by rfl) ⟨490500, by rfl⟩ : syracuseStep 5232005 = 981001) (by norm_num)
theorem B3487157 : Blo 1549472 3487157 := bbase (se 5 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 3487157 = 326921) (by norm_num)
theorem B3487229 : Blo 1549472 3487229 := bbase (se 3 (by rfl) ⟨653855, by rfl⟩ : syracuseStep 3487229 = 1307711) (by norm_num)
theorem B13243925 : Blo 1549472 13243925 := bbase (se 6 (by rfl) ⟨310404, by rfl⟩ : syracuseStep 13243925 = 620809) (by norm_num)
theorem B7075349 : Blo 1549472 7075349 := bbase (se 6 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 7075349 = 331657) (by norm_num)
theorem B1963541 : Blo 1549472 1963541 := bbase (se 6 (by rfl) ⟨46020, by rfl⟩ : syracuseStep 1963541 = 92041) (by norm_num)
theorem B5887525 : Blo 1549472 5887525 := bbase (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) (by norm_num)
theorem B3487301 : Blo 1549472 3487301 := bbase (se 4 (by rfl) ⟨326934, by rfl⟩ : syracuseStep 3487301 = 653869) (by norm_num)
theorem B4191845 : Blo 1549472 4191845 := bbase (se 4 (by rfl) ⟨392985, by rfl⟩ : syracuseStep 4191845 = 785971) (by norm_num)
theorem B11769461 : Blo 1549472 11769461 := bbase (se 5 (by rfl) ⟨551693, by rfl⟩ : syracuseStep 11769461 = 1103387) (by norm_num)
theorem B11179637 : Blo 1549472 11179637 := bbase (se 5 (by rfl) ⟨524045, by rfl⟩ : syracuseStep 11179637 = 1048091) (by norm_num)
theorem B3487373 : Blo 1549472 3487373 := bbase (se 3 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 3487373 = 1307765) (by norm_num)
theorem B3487445 : Blo 1549472 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B2324213 : Blo 1549472 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B2324237 : Blo 1549472 2324237 := bbase (se 3 (by rfl) ⟨435794, by rfl⟩ : syracuseStep 2324237 = 871589) (by norm_num)
theorem B3487517 : Blo 1549472 3487517 := bbase (se 3 (by rfl) ⟨653909, by rfl⟩ : syracuseStep 3487517 = 1307819) (by norm_num)
theorem B2324261 : Blo 1549472 2324261 := bbase (se 4 (by rfl) ⟨217899, by rfl⟩ : syracuseStep 2324261 = 435799) (by norm_num)
theorem B5232437 : Blo 1549472 5232437 := bbase (se 5 (by rfl) ⟨245270, by rfl⟩ : syracuseStep 5232437 = 490541) (by norm_num)
theorem B2324285 : Blo 1549472 2324285 := bbase (se 3 (by rfl) ⟨435803, by rfl⟩ : syracuseStep 2324285 = 871607) (by norm_num)
theorem B2324309 : Blo 1549472 2324309 := bbase (se 9 (by rfl) ⟨6809, by rfl⟩ : syracuseStep 2324309 = 13619) (by norm_num)
theorem B5887829 : Blo 1549472 5887829 := bbase (se 9 (by rfl) ⟨17249, by rfl⟩ : syracuseStep 5887829 = 34499) (by norm_num)
theorem B3487589 : Blo 1549472 3487589 := bbase (se 4 (by rfl) ⟨326961, by rfl⟩ : syracuseStep 3487589 = 653923) (by norm_num)
theorem B2324333 : Blo 1549472 2324333 := bbase (se 3 (by rfl) ⟨435812, by rfl⟩ : syracuseStep 2324333 = 871625) (by norm_num)
theorem B2324357 : Blo 1549472 2324357 := bbase (se 4 (by rfl) ⟨217908, by rfl⟩ : syracuseStep 2324357 = 435817) (by norm_num)
theorem B3536789 : Blo 1549472 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B2324381 : Blo 1549472 2324381 := bbase (se 3 (by rfl) ⟨435821, by rfl⟩ : syracuseStep 2324381 = 871643) (by norm_num)
theorem B3487661 : Blo 1549472 3487661 := bbase (se 3 (by rfl) ⟨653936, by rfl⟩ : syracuseStep 3487661 = 1307873) (by norm_num)
theorem B2324405 : Blo 1549472 2324405 := bbase (se 5 (by rfl) ⟨108956, by rfl⟩ : syracuseStep 2324405 = 217913) (by norm_num)
theorem B2324429 : Blo 1549472 2324429 := bbase (se 3 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 2324429 = 871661) (by norm_num)
theorem B2324453 : Blo 1549472 2324453 := bbase (se 4 (by rfl) ⟨217917, by rfl⟩ : syracuseStep 2324453 = 435835) (by norm_num)
theorem B3487733 : Blo 1549472 3487733 := bbase (se 5 (by rfl) ⟨163487, by rfl⟩ : syracuseStep 3487733 = 326975) (by norm_num)
theorem B2324477 : Blo 1549472 2324477 := bbase (se 3 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 2324477 = 871679) (by norm_num)
theorem B2324501 : Blo 1549472 2324501 := bbase (se 6 (by rfl) ⟨54480, by rfl⟩ : syracuseStep 2324501 = 108961) (by norm_num)
theorem B2324525 : Blo 1549472 2324525 := bbase (se 3 (by rfl) ⟨435848, by rfl⟩ : syracuseStep 2324525 = 871697) (by norm_num)
theorem B3487805 : Blo 1549472 3487805 := bbase (se 3 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 3487805 = 1307927) (by norm_num)
theorem B2324549 : Blo 1549472 2324549 := bbase (se 4 (by rfl) ⟨217926, by rfl⟩ : syracuseStep 2324549 = 435853) (by norm_num)
theorem B2324573 : Blo 1549472 2324573 := bbase (se 3 (by rfl) ⟨435857, by rfl⟩ : syracuseStep 2324573 = 871715) (by norm_num)
theorem B2324597 : Blo 1549472 2324597 := bbase (se 5 (by rfl) ⟨108965, by rfl⟩ : syracuseStep 2324597 = 217931) (by norm_num)
theorem B3487877 : Blo 1549472 3487877 := bbase (se 4 (by rfl) ⟨326988, by rfl⟩ : syracuseStep 3487877 = 653977) (by norm_num)
theorem B2324621 : Blo 1549472 2324621 := bbase (se 3 (by rfl) ⟨435866, by rfl⟩ : syracuseStep 2324621 = 871733) (by norm_num)
theorem B1570969 : Blo 1549472 1570969 := bbase (se 2 (by rfl) ⟨589113, by rfl⟩ : syracuseStep 1570969 = 1178227) (by norm_num)
theorem B1792153 : Blo 1549472 1792153 := bbase (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) (by norm_num)
theorem B2324645 : Blo 1549472 2324645 := bbase (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) (by norm_num)
theorem B7854245 : Blo 1549472 7854245 := bbase (se 4 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 7854245 = 1472671) (by norm_num)
theorem B2324669 : Blo 1549472 2324669 := bbase (se 3 (by rfl) ⟨435875, by rfl⟩ : syracuseStep 2324669 = 871751) (by norm_num)
theorem B3725509 : Blo 1549472 3725509 := bbase (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) (by norm_num)
theorem B3487949 : Blo 1549472 3487949 := bbase (se 3 (by rfl) ⟨653990, by rfl⟩ : syracuseStep 3487949 = 1307981) (by norm_num)
theorem B2324693 : Blo 1549472 2324693 := bbase (se 7 (by rfl) ⟨27242, by rfl⟩ : syracuseStep 2324693 = 54485) (by norm_num)
theorem B3922141 : Blo 1549472 3922141 := bbase (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) (by norm_num)
theorem B5232869 : Blo 1549472 5232869 := bbase (se 4 (by rfl) ⟨490581, by rfl⟩ : syracuseStep 5232869 = 981163) (by norm_num)
theorem B2324717 : Blo 1549472 2324717 := bbase (se 3 (by rfl) ⟨435884, by rfl⟩ : syracuseStep 2324717 = 871769) (by norm_num)
theorem B4413685 : Blo 1549472 4413685 := bbase (se 5 (by rfl) ⟨206891, by rfl⟩ : syracuseStep 4413685 = 413783) (by norm_num)
theorem B2324741 : Blo 1549472 2324741 := bbase (se 4 (by rfl) ⟨217944, by rfl⟩ : syracuseStep 2324741 = 435889) (by norm_num)
theorem B3488021 : Blo 1549472 3488021 := bbase (se 6 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 3488021 = 163501) (by norm_num)
theorem B2324765 : Blo 1549472 2324765 := bbase (se 3 (by rfl) ⟨435893, by rfl⟩ : syracuseStep 2324765 = 871787) (by norm_num)
theorem B2324789 : Blo 1549472 2324789 := bbase (se 5 (by rfl) ⟨108974, by rfl⟩ : syracuseStep 2324789 = 217949) (by norm_num)
theorem B1743169 : Blo 1549472 1743169 := bbase (se 2 (by rfl) ⟨653688, by rfl⟩ : syracuseStep 1743169 = 1307377) (by norm_num)
theorem B3922253 : Blo 1549472 3922253 := bbase (se 3 (by rfl) ⟨735422, by rfl⟩ : syracuseStep 3922253 = 1470845) (by norm_num)
theorem B2324813 : Blo 1549472 2324813 := bbase (se 3 (by rfl) ⟨435902, by rfl⟩ : syracuseStep 2324813 = 871805) (by norm_num)
theorem B3488093 : Blo 1549472 3488093 := bbase (se 3 (by rfl) ⟨654017, by rfl⟩ : syracuseStep 3488093 = 1308035) (by norm_num)
theorem B2357597 : Blo 1549472 2357597 := bbase (se 3 (by rfl) ⟨442049, by rfl⟩ : syracuseStep 2357597 = 884099) (by norm_num)
theorem B1743205 : Blo 1549472 1743205 := bbase (se 4 (by rfl) ⟨163425, by rfl⟩ : syracuseStep 1743205 = 326851) (by norm_num)
theorem B2324837 : Blo 1549472 2324837 := bbase (se 4 (by rfl) ⟨217953, by rfl⟩ : syracuseStep 2324837 = 435907) (by norm_num)
theorem B3979637 : Blo 1549472 3979637 := bbase (se 5 (by rfl) ⟨186545, by rfl⟩ : syracuseStep 3979637 = 373091) (by norm_num)
theorem B2324861 : Blo 1549472 2324861 := bbase (se 3 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 2324861 = 871823) (by norm_num)
theorem B1743241 : Blo 1549472 1743241 := bbase (se 2 (by rfl) ⟨653715, by rfl⟩ : syracuseStep 1743241 = 1307431) (by norm_num)
theorem B2324885 : Blo 1549472 2324885 := bbase (se 6 (by rfl) ⟨54489, by rfl⟩ : syracuseStep 2324885 = 108979) (by norm_num)
theorem B4413845 : Blo 1549472 4413845 := bbase (se 6 (by rfl) ⟨103449, by rfl⟩ : syracuseStep 4413845 = 206899) (by norm_num)
theorem B3488165 : Blo 1549472 3488165 := bbase (se 4 (by rfl) ⟨327015, by rfl⟩ : syracuseStep 3488165 = 654031) (by norm_num)
theorem B1743277 : Blo 1549472 1743277 := bbase (se 3 (by rfl) ⟨326864, by rfl⟩ : syracuseStep 1743277 = 653729) (by norm_num)
theorem B2324909 : Blo 1549472 2324909 := bbase (se 3 (by rfl) ⟨435920, by rfl⟩ : syracuseStep 2324909 = 871841) (by norm_num)
theorem B2324933 : Blo 1549472 2324933 := bbase (se 4 (by rfl) ⟨217962, by rfl⟩ : syracuseStep 2324933 = 435925) (by norm_num)
theorem B1743313 : Blo 1549472 1743313 := bbase (se 2 (by rfl) ⟨653742, by rfl⟩ : syracuseStep 1743313 = 1307485) (by norm_num)
theorem B2324957 : Blo 1549472 2324957 := bbase (se 3 (by rfl) ⟨435929, by rfl⟩ : syracuseStep 2324957 = 871859) (by norm_num)
theorem B3488237 : Blo 1549472 3488237 := bbase (se 3 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 3488237 = 1308089) (by norm_num)
theorem B1743349 : Blo 1549472 1743349 := bbase (se 5 (by rfl) ⟨81719, by rfl⟩ : syracuseStep 1743349 = 163439) (by norm_num)
theorem B2324981 : Blo 1549472 2324981 := bbase (se 5 (by rfl) ⟨108983, by rfl⟩ : syracuseStep 2324981 = 217967) (by norm_num)
theorem B3922445 : Blo 1549472 3922445 := bbase (se 3 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 3922445 = 1470917) (by norm_num)
theorem B2325005 : Blo 1549472 2325005 := bbase (se 3 (by rfl) ⟨435938, by rfl⟩ : syracuseStep 2325005 = 871877) (by norm_num)
theorem B1743385 : Blo 1549472 1743385 := bbase (se 2 (by rfl) ⟨653769, by rfl⟩ : syracuseStep 1743385 = 1307539) (by norm_num)
theorem B2325029 : Blo 1549472 2325029 := bbase (se 4 (by rfl) ⟨217971, by rfl⟩ : syracuseStep 2325029 = 435943) (by norm_num)
theorem B3488309 : Blo 1549472 3488309 := bbase (se 5 (by rfl) ⟨163514, by rfl⟩ : syracuseStep 3488309 = 327029) (by norm_num)
theorem B1743421 : Blo 1549472 1743421 := bbase (se 3 (by rfl) ⟨326891, by rfl⟩ : syracuseStep 1743421 = 653783) (by norm_num)
theorem B2325053 : Blo 1549472 2325053 := bbase (se 3 (by rfl) ⟨435947, by rfl⟩ : syracuseStep 2325053 = 871895) (by norm_num)
theorem B7846469 : Blo 1549472 7846469 := bbase (se 4 (by rfl) ⟨735606, by rfl⟩ : syracuseStep 7846469 = 1471213) (by norm_num)
theorem B2325077 : Blo 1549472 2325077 := bbase (se 8 (by rfl) ⟨13623, by rfl⟩ : syracuseStep 2325077 = 27247) (by norm_num)
theorem B12573269 : Blo 1549472 12573269 := bbase (se 8 (by rfl) ⟨73671, by rfl⟩ : syracuseStep 12573269 = 147343) (by norm_num)
theorem B1743457 : Blo 1549472 1743457 := bbase (se 2 (by rfl) ⟨653796, by rfl⟩ : syracuseStep 1743457 = 1307593) (by norm_num)
theorem B2325101 : Blo 1549472 2325101 := bbase (se 3 (by rfl) ⟨435956, by rfl⟩ : syracuseStep 2325101 = 871913) (by norm_num)
theorem B8829557 : Blo 1549472 8829557 := bbase (se 5 (by rfl) ⟨413885, by rfl⟩ : syracuseStep 8829557 = 827771) (by norm_num)
theorem B3488381 : Blo 1549472 3488381 := bbase (se 3 (by rfl) ⟨654071, by rfl⟩ : syracuseStep 3488381 = 1308143) (by norm_num)
theorem B1743493 : Blo 1549472 1743493 := bbase (se 4 (by rfl) ⟨163452, by rfl⟩ : syracuseStep 1743493 = 326905) (by norm_num)
theorem B4414085 : Blo 1549472 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B2325125 : Blo 1549472 2325125 := bbase (se 4 (by rfl) ⟨217980, by rfl⟩ : syracuseStep 2325125 = 435961) (by norm_num)
theorem B5233301 : Blo 1549472 5233301 := bbase (se 6 (by rfl) ⟨122655, by rfl⟩ : syracuseStep 5233301 = 245311) (by norm_num)
theorem B2325149 : Blo 1549472 2325149 := bbase (se 3 (by rfl) ⟨435965, by rfl⟩ : syracuseStep 2325149 = 871931) (by norm_num)
theorem B1571485 : Blo 1549472 1571485 := bbase (se 3 (by rfl) ⟨294653, by rfl⟩ : syracuseStep 1571485 = 589307) (by norm_num)
theorem B1743529 : Blo 1549472 1743529 := bbase (se 2 (by rfl) ⟨653823, by rfl⟩ : syracuseStep 1743529 = 1307647) (by norm_num)
theorem B2325173 : Blo 1549472 2325173 := bbase (se 5 (by rfl) ⟨108992, by rfl⟩ : syracuseStep 2325173 = 217985) (by norm_num)
theorem B3488453 : Blo 1549472 3488453 := bbase (se 4 (by rfl) ⟨327042, by rfl⟩ : syracuseStep 3488453 = 654085) (by norm_num)
theorem B1743565 : Blo 1549472 1743565 := bbase (se 3 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 1743565 = 653837) (by norm_num)
theorem B2325197 : Blo 1549472 2325197 := bbase (se 3 (by rfl) ⟨435974, by rfl⟩ : syracuseStep 2325197 = 871949) (by norm_num)
theorem B2325221 : Blo 1549472 2325221 := bbase (se 4 (by rfl) ⟨217989, by rfl⟩ : syracuseStep 2325221 = 435979) (by norm_num)
theorem B1743601 : Blo 1549472 1743601 := bbase (se 2 (by rfl) ⟨653850, by rfl⟩ : syracuseStep 1743601 = 1307701) (by norm_num)
theorem B3144437 : Blo 1549472 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B2325245 : Blo 1549472 2325245 := bbase (se 3 (by rfl) ⟨435983, by rfl⟩ : syracuseStep 2325245 = 871967) (by norm_num)
theorem B3488525 : Blo 1549472 3488525 := bbase (se 3 (by rfl) ⟨654098, by rfl⟩ : syracuseStep 3488525 = 1308197) (by norm_num)
theorem B1743637 : Blo 1549472 1743637 := bbase (se 6 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 1743637 = 81733) (by norm_num)
theorem B2325269 : Blo 1549472 2325269 := bbase (se 6 (by rfl) ⟨54498, by rfl⟩ : syracuseStep 2325269 = 108997) (by norm_num)
theorem B3144485 : Blo 1549472 3144485 := bbase (se 4 (by rfl) ⟨294795, by rfl⟩ : syracuseStep 3144485 = 589591) (by norm_num)
theorem B2325293 : Blo 1549472 2325293 := bbase (se 3 (by rfl) ⟨435992, by rfl⟩ : syracuseStep 2325293 = 871985) (by norm_num)
theorem B3726125 : Blo 1549472 3726125 := bbase (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) (by norm_num)
theorem B1743673 : Blo 1549472 1743673 := bbase (se 2 (by rfl) ⟨653877, by rfl⟩ : syracuseStep 1743673 = 1307755) (by norm_num)
theorem B4414277 : Blo 1549472 4414277 := bbase (se 4 (by rfl) ⟨413838, by rfl⟩ : syracuseStep 4414277 = 827677) (by norm_num)
theorem B2325317 : Blo 1549472 2325317 := bbase (se 4 (by rfl) ⟨217998, by rfl⟩ : syracuseStep 2325317 = 435997) (by norm_num)
theorem B3488597 : Blo 1549472 3488597 := bbase (se 9 (by rfl) ⟨10220, by rfl⟩ : syracuseStep 3488597 = 20441) (by norm_num)
theorem B22362965 : Blo 1549472 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B1743709 : Blo 1549472 1743709 := bbase (se 3 (by rfl) ⟨326945, by rfl⟩ : syracuseStep 1743709 = 653891) (by norm_num)
theorem B2325341 : Blo 1549472 2325341 := bbase (se 3 (by rfl) ⟨436001, by rfl⟩ : syracuseStep 2325341 = 872003) (by norm_num)
theorem B3922789 : Blo 1549472 3922789 := bbase (se 4 (by rfl) ⟨367761, by rfl⟩ : syracuseStep 3922789 = 735523) (by norm_num)
theorem B2325365 : Blo 1549472 2325365 := bbase (se 5 (by rfl) ⟨109001, by rfl⟩ : syracuseStep 2325365 = 218003) (by norm_num)
theorem B1743745 : Blo 1549472 1743745 := bbase (se 2 (by rfl) ⟨653904, by rfl⟩ : syracuseStep 1743745 = 1307809) (by norm_num)
theorem B2325389 : Blo 1549472 2325389 := bbase (se 3 (by rfl) ⟨436010, by rfl⟩ : syracuseStep 2325389 = 872021) (by norm_num)
theorem B3488669 : Blo 1549472 3488669 := bbase (se 3 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 3488669 = 1308251) (by norm_num)
theorem B1743781 : Blo 1549472 1743781 := bbase (se 4 (by rfl) ⟨163479, by rfl⟩ : syracuseStep 1743781 = 326959) (by norm_num)
theorem B2325413 : Blo 1549472 2325413 := bbase (se 4 (by rfl) ⟨218007, by rfl⟩ : syracuseStep 2325413 = 436015) (by norm_num)
theorem B2325437 : Blo 1549472 2325437 := bbase (se 3 (by rfl) ⟨436019, by rfl⟩ : syracuseStep 2325437 = 872039) (by norm_num)
theorem B1743817 : Blo 1549472 1743817 := bbase (se 2 (by rfl) ⟨653931, by rfl⟩ : syracuseStep 1743817 = 1307863) (by norm_num)
theorem B3922901 : Blo 1549472 3922901 := bbase (se 7 (by rfl) ⟨45971, by rfl⟩ : syracuseStep 3922901 = 91943) (by norm_num)
theorem B2325461 : Blo 1549472 2325461 := bbase (se 7 (by rfl) ⟨27251, by rfl⟩ : syracuseStep 2325461 = 54503) (by norm_num)
theorem B3488741 : Blo 1549472 3488741 := bbase (se 4 (by rfl) ⟨327069, by rfl⟩ : syracuseStep 3488741 = 654139) (by norm_num)
theorem B1743853 : Blo 1549472 1743853 := bbase (se 3 (by rfl) ⟨326972, by rfl⟩ : syracuseStep 1743853 = 653945) (by norm_num)
theorem B2325485 : Blo 1549472 2325485 := bbase (se 3 (by rfl) ⟨436028, by rfl⟩ : syracuseStep 2325485 = 872057) (by norm_num)
theorem B2325509 : Blo 1549472 2325509 := bbase (se 4 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 2325509 = 436033) (by norm_num)
theorem B1743889 : Blo 1549472 1743889 := bbase (se 2 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 1743889 = 1307917) (by norm_num)
theorem B2325533 : Blo 1549472 2325533 := bbase (se 3 (by rfl) ⟨436037, by rfl⟩ : syracuseStep 2325533 = 872075) (by norm_num)
theorem B3488813 : Blo 1549472 3488813 := bbase (se 3 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 3488813 = 1308305) (by norm_num)
theorem B1743925 : Blo 1549472 1743925 := bbase (se 5 (by rfl) ⟨81746, by rfl⟩ : syracuseStep 1743925 = 163493) (by norm_num)
theorem B2325557 : Blo 1549472 2325557 := bbase (se 5 (by rfl) ⟨109010, by rfl⟩ : syracuseStep 2325557 = 218021) (by norm_num)
theorem B5233733 : Blo 1549472 5233733 := bbase (se 4 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 5233733 = 981325) (by norm_num)
theorem B2325581 : Blo 1549472 2325581 := bbase (se 3 (by rfl) ⟨436046, by rfl⟩ : syracuseStep 2325581 = 872093) (by norm_num)
theorem B1678421 : Blo 1549472 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B1743961 : Blo 1549472 1743961 := bbase (se 2 (by rfl) ⟨653985, by rfl⟩ : syracuseStep 1743961 = 1307971) (by norm_num)
theorem B2096221 : Blo 1549472 2096221 := bbase (se 3 (by rfl) ⟨393041, by rfl⟩ : syracuseStep 2096221 = 786083) (by norm_num)
theorem B2325605 : Blo 1549472 2325605 := bbase (se 4 (by rfl) ⟨218025, by rfl⟩ : syracuseStep 2325605 = 436051) (by norm_num)
theorem B2096237 : Blo 1549472 2096237 := bbase (se 3 (by rfl) ⟨393044, by rfl⟩ : syracuseStep 2096237 = 786089) (by norm_num)
theorem B3488885 : Blo 1549472 3488885 := bbase (se 5 (by rfl) ⟨163541, by rfl⟩ : syracuseStep 3488885 = 327083) (by norm_num)
theorem B1743997 : Blo 1549472 1743997 := bbase (se 3 (by rfl) ⟨326999, by rfl⟩ : syracuseStep 1743997 = 653999) (by norm_num)
theorem B2325629 : Blo 1549472 2325629 := bbase (se 3 (by rfl) ⟨436055, by rfl⟩ : syracuseStep 2325629 = 872111) (by norm_num)
theorem B3726461 : Blo 1549472 3726461 := bbase (se 3 (by rfl) ⟨698711, by rfl⟩ : syracuseStep 3726461 = 1397423) (by norm_num)
theorem B3923093 : Blo 1549472 3923093 := bbase (se 6 (by rfl) ⟨91947, by rfl⟩ : syracuseStep 3923093 = 183895) (by norm_num)
theorem B2325653 : Blo 1549472 2325653 := bbase (se 6 (by rfl) ⟨54507, by rfl⟩ : syracuseStep 2325653 = 109015) (by norm_num)
theorem B1744033 : Blo 1549472 1744033 := bbase (se 2 (by rfl) ⟨654012, by rfl⟩ : syracuseStep 1744033 = 1308025) (by norm_num)
theorem B2325677 : Blo 1549472 2325677 := bbase (se 3 (by rfl) ⟨436064, by rfl⟩ : syracuseStep 2325677 = 872129) (by norm_num)
theorem B3488957 : Blo 1549472 3488957 := bbase (se 3 (by rfl) ⟨654179, by rfl⟩ : syracuseStep 3488957 = 1308359) (by norm_num)
theorem B1744069 : Blo 1549472 1744069 := bbase (se 4 (by rfl) ⟨163506, by rfl⟩ : syracuseStep 1744069 = 327013) (by norm_num)
theorem B2325701 : Blo 1549472 2325701 := bbase (se 4 (by rfl) ⟨218034, by rfl⟩ : syracuseStep 2325701 = 436069) (by norm_num)
theorem B2325725 : Blo 1549472 2325725 := bbase (se 3 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 2325725 = 872147) (by norm_num)
theorem B1744105 : Blo 1549472 1744105 := bbase (se 2 (by rfl) ⟨654039, by rfl⟩ : syracuseStep 1744105 = 1308079) (by norm_num)
theorem B2268397 : Blo 1549472 2268397 := bbase (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) (by norm_num)
theorem B2325749 : Blo 1549472 2325749 := bbase (se 5 (by rfl) ⟨109019, by rfl⟩ : syracuseStep 2325749 = 218039) (by norm_num)
theorem B3489029 : Blo 1549472 3489029 := bbase (se 4 (by rfl) ⟨327096, by rfl⟩ : syracuseStep 3489029 = 654193) (by norm_num)
theorem B1744141 : Blo 1549472 1744141 := bbase (se 3 (by rfl) ⟨327026, by rfl⟩ : syracuseStep 1744141 = 654053) (by norm_num)
theorem B2325773 : Blo 1549472 2325773 := bbase (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) (by norm_num)
theorem B2325797 : Blo 1549472 2325797 := bbase (se 4 (by rfl) ⟨218043, by rfl⟩ : syracuseStep 2325797 = 436087) (by norm_num)
theorem B1744177 : Blo 1549472 1744177 := bbase (se 2 (by rfl) ⟨654066, by rfl⟩ : syracuseStep 1744177 = 1308133) (by norm_num)
theorem B1989937 : Blo 1549472 1989937 := bbase (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) (by norm_num)
theorem B2325821 : Blo 1549472 2325821 := bbase (se 3 (by rfl) ⟨436091, by rfl⟩ : syracuseStep 2325821 = 872183) (by norm_num)
theorem B3489101 : Blo 1549472 3489101 := bbase (se 3 (by rfl) ⟨654206, by rfl⟩ : syracuseStep 3489101 = 1308413) (by norm_num)
theorem B1744213 : Blo 1549472 1744213 := bbase (se 11 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 1744213 = 2555) (by norm_num)
theorem B2325845 : Blo 1549472 2325845 := bbase (se 11 (by rfl) ⟨1703, by rfl⟩ : syracuseStep 2325845 = 3407) (by norm_num)
theorem B2325869 : Blo 1549472 2325869 := bbase (se 3 (by rfl) ⟨436100, by rfl⟩ : syracuseStep 2325869 = 872201) (by norm_num)
theorem B4193653 : Blo 1549472 4193653 := bbase (se 5 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 4193653 = 393155) (by norm_num)
theorem B1744249 : Blo 1549472 1744249 := bbase (se 2 (by rfl) ⟨654093, by rfl⟩ : syracuseStep 1744249 = 1308187) (by norm_num)
theorem B2325893 : Blo 1549472 2325893 := bbase (se 4 (by rfl) ⟨218052, by rfl⟩ : syracuseStep 2325893 = 436105) (by norm_num)
theorem B3489173 : Blo 1549472 3489173 := bbase (se 6 (by rfl) ⟨81777, by rfl⟩ : syracuseStep 3489173 = 163555) (by norm_num)
theorem B1744285 : Blo 1549472 1744285 := bbase (se 3 (by rfl) ⟨327053, by rfl⟩ : syracuseStep 1744285 = 654107) (by norm_num)
theorem B2325917 : Blo 1549472 2325917 := bbase (se 3 (by rfl) ⟨436109, by rfl⟩ : syracuseStep 2325917 = 872219) (by norm_num)
theorem B3145117 : Blo 1549472 3145117 := bbase (se 3 (by rfl) ⟨589709, by rfl⟩ : syracuseStep 3145117 = 1179419) (by norm_num)
theorem B2325941 : Blo 1549472 2325941 := bbase (se 5 (by rfl) ⟨109028, by rfl⟩ : syracuseStep 2325941 = 218057) (by norm_num)
theorem B1744321 : Blo 1549472 1744321 := bbase (se 2 (by rfl) ⟨654120, by rfl⟩ : syracuseStep 1744321 = 1308241) (by norm_num)
theorem B2325965 : Blo 1549472 2325965 := bbase (se 3 (by rfl) ⟨436118, by rfl⟩ : syracuseStep 2325965 = 872237) (by norm_num)
theorem B6618581 : Blo 1549472 6618581 := bbase (se 7 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 6618581 = 155123) (by norm_num)
theorem B3489245 : Blo 1549472 3489245 := bbase (se 3 (by rfl) ⟨654233, by rfl⟩ : syracuseStep 3489245 = 1308467) (by norm_num)
theorem B1744357 : Blo 1549472 1744357 := bbase (se 4 (by rfl) ⟨163533, by rfl⟩ : syracuseStep 1744357 = 327067) (by norm_num)
theorem B2325989 : Blo 1549472 2325989 := bbase (se 4 (by rfl) ⟨218061, by rfl⟩ : syracuseStep 2325989 = 436123) (by norm_num)
theorem B1990117 : Blo 1549472 1990117 := bbase (se 4 (by rfl) ⟨186573, by rfl⟩ : syracuseStep 1990117 = 373147) (by norm_num)
theorem B3923437 : Blo 1549472 3923437 := bbase (se 3 (by rfl) ⟨735644, by rfl⟩ : syracuseStep 3923437 = 1471289) (by norm_num)
theorem B5234165 : Blo 1549472 5234165 := bbase (se 5 (by rfl) ⟨245351, by rfl⟩ : syracuseStep 5234165 = 490703) (by norm_num)
theorem B2326013 : Blo 1549472 2326013 := bbase (se 3 (by rfl) ⟨436127, by rfl⟩ : syracuseStep 2326013 = 872255) (by norm_num)
theorem B3726853 : Blo 1549472 3726853 := bbase (se 4 (by rfl) ⟨349392, by rfl⟩ : syracuseStep 3726853 = 698785) (by norm_num)
theorem B1744393 : Blo 1549472 1744393 := bbase (se 2 (by rfl) ⟨654147, by rfl⟩ : syracuseStep 1744393 = 1308295) (by norm_num)
theorem B6282773 : Blo 1549472 6282773 := bbase (se 6 (by rfl) ⟨147252, by rfl⟩ : syracuseStep 6282773 = 294505) (by norm_num)
theorem B2326037 : Blo 1549472 2326037 := bbase (se 6 (by rfl) ⟨54516, by rfl⟩ : syracuseStep 2326037 = 109033) (by norm_num)
theorem B3489317 : Blo 1549472 3489317 := bbase (se 4 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 3489317 = 654247) (by norm_num)
theorem B1744429 : Blo 1549472 1744429 := bbase (se 3 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 1744429 = 654161) (by norm_num)
theorem B2326061 : Blo 1549472 2326061 := bbase (se 3 (by rfl) ⟨436136, by rfl⟩ : syracuseStep 2326061 = 872273) (by norm_num)
theorem B2326085 : Blo 1549472 2326085 := bbase (se 4 (by rfl) ⟨218070, by rfl⟩ : syracuseStep 2326085 = 436141) (by norm_num)
theorem B1744465 : Blo 1549472 1744465 := bbase (se 2 (by rfl) ⟨654174, by rfl⟩ : syracuseStep 1744465 = 1308349) (by norm_num)
theorem B3923549 : Blo 1549472 3923549 := bbase (se 3 (by rfl) ⟨735665, by rfl⟩ : syracuseStep 3923549 = 1471331) (by norm_num)
theorem B2326109 : Blo 1549472 2326109 := bbase (se 3 (by rfl) ⟨436145, by rfl⟩ : syracuseStep 2326109 = 872291) (by norm_num)
theorem B5586533 : Blo 1549472 5586533 := bbase (se 4 (by rfl) ⟨523737, by rfl⟩ : syracuseStep 5586533 = 1047475) (by norm_num)
theorem B3489389 : Blo 1549472 3489389 := bbase (se 3 (by rfl) ⟨654260, by rfl⟩ : syracuseStep 3489389 = 1308521) (by norm_num)
theorem B1744501 : Blo 1549472 1744501 := bbase (se 5 (by rfl) ⟨81773, by rfl⟩ : syracuseStep 1744501 = 163547) (by norm_num)
theorem B2326133 : Blo 1549472 2326133 := bbase (se 5 (by rfl) ⟨109037, by rfl⟩ : syracuseStep 2326133 = 218075) (by norm_num)
theorem B1990265 : Blo 1549472 1990265 := bbase (se 2 (by rfl) ⟨746349, by rfl⟩ : syracuseStep 1990265 = 1492699) (by norm_num)
theorem B2326157 : Blo 1549472 2326157 := bbase (se 3 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 2326157 = 872309) (by norm_num)
theorem B9936533 : Blo 1549472 9936533 := bbase (se 6 (by rfl) ⟨232887, by rfl⟩ : syracuseStep 9936533 = 465775) (by norm_num)
theorem B1744537 : Blo 1549472 1744537 := bbase (se 2 (by rfl) ⟨654201, by rfl⟩ : syracuseStep 1744537 = 1308403) (by norm_num)
theorem B2326181 : Blo 1549472 2326181 := bbase (se 4 (by rfl) ⟨218079, by rfl⟩ : syracuseStep 2326181 = 436159) (by norm_num)
theorem B3489461 : Blo 1549472 3489461 := bbase (se 5 (by rfl) ⟨163568, by rfl⟩ : syracuseStep 3489461 = 327137) (by norm_num)
theorem B1744573 : Blo 1549472 1744573 := bbase (se 3 (by rfl) ⟨327107, by rfl⟩ : syracuseStep 1744573 = 654215) (by norm_num)
theorem B2326205 : Blo 1549472 2326205 := bbase (se 3 (by rfl) ⟨436163, by rfl⟩ : syracuseStep 2326205 = 872327) (by norm_num)
theorem B40271573 : Blo 1549472 40271573 := bbase (se 7 (by rfl) ⟨471932, by rfl⟩ : syracuseStep 40271573 = 943865) (by norm_num)
theorem B2326229 : Blo 1549472 2326229 := bbase (se 7 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 2326229 = 54521) (by norm_num)
theorem B1744609 : Blo 1549472 1744609 := bbase (se 2 (by rfl) ⟨654228, by rfl⟩ : syracuseStep 1744609 = 1308457) (by norm_num)
theorem B2326253 : Blo 1549472 2326253 := bbase (se 3 (by rfl) ⟨436172, by rfl⟩ : syracuseStep 2326253 = 872345) (by norm_num)
theorem B3489533 : Blo 1549472 3489533 := bbase (se 3 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 3489533 = 1308575) (by norm_num)
theorem B1744645 : Blo 1549472 1744645 := bbase (se 4 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 1744645 = 327121) (by norm_num)
theorem B2326277 : Blo 1549472 2326277 := bbase (se 4 (by rfl) ⟨218088, by rfl⟩ : syracuseStep 2326277 = 436177) (by norm_num)
theorem B8830741 : Blo 1549472 8830741 := bbase (se 6 (by rfl) ⟨206970, by rfl⟩ : syracuseStep 8830741 = 413941) (by norm_num)
theorem B3923741 : Blo 1549472 3923741 := bbase (se 3 (by rfl) ⟨735701, by rfl⟩ : syracuseStep 3923741 = 1471403) (by norm_num)
theorem B3309341 : Blo 1549472 3309341 := bbase (se 3 (by rfl) ⟨620501, by rfl⟩ : syracuseStep 3309341 = 1241003) (by norm_num)
theorem B2326301 : Blo 1549472 2326301 := bbase (se 3 (by rfl) ⟨436181, by rfl⟩ : syracuseStep 2326301 = 872363) (by norm_num)
theorem B4415269 : Blo 1549472 4415269 := bbase (se 4 (by rfl) ⟨413931, by rfl⟩ : syracuseStep 4415269 = 827863) (by norm_num)
theorem B1744681 : Blo 1549472 1744681 := bbase (se 2 (by rfl) ⟨654255, by rfl⟩ : syracuseStep 1744681 = 1308511) (by norm_num)
theorem B7446325 : Blo 1549472 7446325 := bbase (se 5 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 7446325 = 698093) (by norm_num)
theorem B2326325 : Blo 1549472 2326325 := bbase (se 5 (by rfl) ⟨109046, by rfl⟩ : syracuseStep 2326325 = 218093) (by norm_num)
theorem B3489605 : Blo 1549472 3489605 := bbase (se 4 (by rfl) ⟨327150, by rfl⟩ : syracuseStep 3489605 = 654301) (by norm_num)
theorem B1744717 : Blo 1549472 1744717 := bbase (se 3 (by rfl) ⟨327134, by rfl⟩ : syracuseStep 1744717 = 654269) (by norm_num)
theorem B2326349 : Blo 1549472 2326349 := bbase (se 3 (by rfl) ⟨436190, by rfl⟩ : syracuseStep 2326349 = 872381) (by norm_num)
theorem B7847765 : Blo 1549472 7847765 := bbase (se 9 (by rfl) ⟨22991, by rfl⟩ : syracuseStep 7847765 = 45983) (by norm_num)
theorem B2326373 : Blo 1549472 2326373 := bbase (se 4 (by rfl) ⟨218097, by rfl⟩ : syracuseStep 2326373 = 436195) (by norm_num)
theorem B1744753 : Blo 1549472 1744753 := bbase (se 2 (by rfl) ⟨654282, by rfl⟩ : syracuseStep 1744753 = 1308565) (by norm_num)
theorem B2326397 : Blo 1549472 2326397 := bbase (se 3 (by rfl) ⟨436199, by rfl⟩ : syracuseStep 2326397 = 872399) (by norm_num)
theorem B1965961 : Blo 1549472 1965961 := bbase (se 2 (by rfl) ⟨737235, by rfl⟩ : syracuseStep 1965961 = 1474471) (by norm_num)
theorem B3489677 : Blo 1549472 3489677 := bbase (se 3 (by rfl) ⟨654314, by rfl⟩ : syracuseStep 3489677 = 1308629) (by norm_num)
theorem B1744789 : Blo 1549472 1744789 := bbase (se 6 (by rfl) ⟨40893, by rfl⟩ : syracuseStep 1744789 = 81787) (by norm_num)
theorem B2326421 : Blo 1549472 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B5889941 : Blo 1549472 5889941 := bbase (se 6 (by rfl) ⟨138045, by rfl⟩ : syracuseStep 5889941 = 276091) (by norm_num)
theorem B5234597 : Blo 1549472 5234597 := bbase (se 4 (by rfl) ⟨490743, by rfl⟩ : syracuseStep 5234597 = 981487) (by norm_num)
theorem B7454629 : Blo 1549472 7454629 := bbase (se 4 (by rfl) ⟨698871, by rfl⟩ : syracuseStep 7454629 = 1397743) (by norm_num)
theorem B2326445 : Blo 1549472 2326445 := bbase (se 3 (by rfl) ⟨436208, by rfl⟩ : syracuseStep 2326445 = 872417) (by norm_num)
theorem B1654705 : Blo 1549472 1654705 := bbase (se 2 (by rfl) ⟨620514, by rfl⟩ : syracuseStep 1654705 = 1241029) (by norm_num)
theorem B1744825 : Blo 1549472 1744825 := bbase (se 2 (by rfl) ⟨654309, by rfl⟩ : syracuseStep 1744825 = 1308619) (by norm_num)
theorem B2326469 : Blo 1549472 2326469 := bbase (se 4 (by rfl) ⟨218106, by rfl⟩ : syracuseStep 2326469 = 436213) (by norm_num)
theorem B3489749 : Blo 1549472 3489749 := bbase (se 7 (by rfl) ⟨40895, by rfl⟩ : syracuseStep 3489749 = 81791) (by norm_num)
theorem B1744861 : Blo 1549472 1744861 := bbase (se 3 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 1744861 = 654323) (by norm_num)
theorem B2326493 : Blo 1549472 2326493 := bbase (se 3 (by rfl) ⟨436217, by rfl⟩ : syracuseStep 2326493 = 872435) (by norm_num)
theorem B2326517 : Blo 1549472 2326517 := bbase (se 5 (by rfl) ⟨109055, by rfl⟩ : syracuseStep 2326517 = 218111) (by norm_num)
theorem B2326529 : Blo 1549472 2326529 := bstep (se 2 (by rfl) ⟨872448, by rfl⟩ : syracuseStep 2326529 = 1744897) B1744897
theorem B5234705 : Blo 1549472 5234705 := bstep (se 2 (by rfl) ⟨1963014, by rfl⟩ : syracuseStep 5234705 = 3926029) B3926029
theorem B2326547 : Blo 1549472 2326547 := bstep (se 1 (by rfl) ⟨1744910, by rfl⟩ : syracuseStep 2326547 = 3489821) B3489821
theorem B1744915 : Blo 1549472 1744915 := bstep (se 1 (by rfl) ⟨1308686, by rfl⟩ : syracuseStep 1744915 = 2617373) B2617373
theorem B2482211 : Blo 1549472 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B2326577 : Blo 1549472 2326577 := bstep (se 2 (by rfl) ⟨872466, by rfl⟩ : syracuseStep 2326577 = 1744933) B1744933
theorem B3924035 : Blo 1549472 3924035 := bstep (se 1 (by rfl) ⟨2943026, by rfl⟩ : syracuseStep 3924035 = 5886053) B5886053
theorem B2326595 : Blo 1549472 2326595 := bstep (se 1 (by rfl) ⟨1744946, by rfl⟩ : syracuseStep 2326595 = 3489893) B3489893
theorem B8380493 : Blo 1549472 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B2326625 : Blo 1549472 2326625 := bstep (se 2 (by rfl) ⟨872484, by rfl⟩ : syracuseStep 2326625 = 1744969) B1744969
theorem B2326643 : Blo 1549472 2326643 := bstep (se 1 (by rfl) ⟨1744982, by rfl⟩ : syracuseStep 2326643 = 3489965) B3489965
theorem B7069837 : Blo 1549472 7069837 := bstep (se 3 (by rfl) ⟨1325594, by rfl⟩ : syracuseStep 7069837 = 2651189) B2651189
theorem B7454861 : Blo 1549472 7454861 := bstep (se 3 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 7454861 = 2795573) B2795573
theorem B2326673 : Blo 1549472 2326673 := bstep (se 2 (by rfl) ⟨872502, by rfl⟩ : syracuseStep 2326673 = 1745005) B1745005
theorem B2326691 : Blo 1549472 2326691 := bstep (se 1 (by rfl) ⟨1745018, by rfl⟩ : syracuseStep 2326691 = 3490037) B3490037
theorem B1745059 : Blo 1549472 1745059 := bstep (se 1 (by rfl) ⟨1308794, by rfl⟩ : syracuseStep 1745059 = 2617589) B2617589
theorem B2326721 : Blo 1549472 2326721 := bstep (se 2 (by rfl) ⟨872520, by rfl⟩ : syracuseStep 2326721 = 1745041) B1745041
theorem B3490001 : Blo 1549472 3490001 := bstep (se 2 (by rfl) ⟨1308750, by rfl⟩ : syracuseStep 3490001 = 2617501) B2617501
theorem B2326739 : Blo 1549472 2326739 := bstep (se 1 (by rfl) ⟨1745054, by rfl⟩ : syracuseStep 2326739 = 3490109) B3490109
theorem B3490019 : Blo 1549472 3490019 := bstep (se 1 (by rfl) ⟨2617514, by rfl⟩ : syracuseStep 3490019 = 5235029) B5235029
theorem B2326769 : Blo 1549472 2326769 := bstep (se 2 (by rfl) ⟨872538, by rfl⟩ : syracuseStep 2326769 = 1745077) B1745077
theorem B3924227 : Blo 1549472 3924227 := bstep (se 1 (by rfl) ⟨2943170, by rfl⟩ : syracuseStep 3924227 = 5886341) B5886341
theorem B2326787 : Blo 1549472 2326787 := bstep (se 1 (by rfl) ⟨1745090, by rfl⟩ : syracuseStep 2326787 = 3490181) B3490181
theorem B2326817 : Blo 1549472 2326817 := bstep (se 2 (by rfl) ⟨872556, by rfl⟩ : syracuseStep 2326817 = 1745113) B1745113
theorem B8831267 : Blo 1549472 8831267 := bstep (se 1 (by rfl) ⟨6623450, by rfl⟩ : syracuseStep 8831267 = 13246901) B13246901
theorem B2482481 : Blo 1549472 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B2326835 : Blo 1549472 2326835 := bstep (se 1 (by rfl) ⟨1745126, by rfl⟩ : syracuseStep 2326835 = 3490253) B3490253
theorem B1745203 : Blo 1549472 1745203 := bstep (se 1 (by rfl) ⟨1308902, by rfl⟩ : syracuseStep 1745203 = 2617805) B2617805
theorem B2326865 : Blo 1549472 2326865 := bstep (se 2 (by rfl) ⟨872574, by rfl⟩ : syracuseStep 2326865 = 1745149) B1745149
theorem B3309923 : Blo 1549472 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B2326883 : Blo 1549472 2326883 := bstep (se 1 (by rfl) ⟨1745162, by rfl⟩ : syracuseStep 2326883 = 3490325) B3490325
theorem B2326913 : Blo 1549472 2326913 := bstep (se 2 (by rfl) ⟨872592, by rfl⟩ : syracuseStep 2326913 = 1745185) B1745185
theorem B9929101 : Blo 1549472 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B2326931 : Blo 1549472 2326931 := bstep (se 1 (by rfl) ⟨1745198, by rfl⟩ : syracuseStep 2326931 = 3490397) B3490397
theorem B2326961 : Blo 1549472 2326961 := bstep (se 2 (by rfl) ⟨872610, by rfl⟩ : syracuseStep 2326961 = 1745221) B1745221
theorem B2326979 : Blo 1549472 2326979 := bstep (se 1 (by rfl) ⟨1745234, by rfl⟩ : syracuseStep 2326979 = 3490469) B3490469
theorem B1745347 : Blo 1549472 1745347 := bstep (se 1 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 1745347 = 2618021) B2618021
theorem B2327009 : Blo 1549472 2327009 := bstep (se 2 (by rfl) ⟨872628, by rfl⟩ : syracuseStep 2327009 = 1745257) B1745257
theorem B6283747 : Blo 1549472 6283747 := bstep (se 1 (by rfl) ⟨4712810, by rfl⟩ : syracuseStep 6283747 = 9425621) B9425621
theorem B3490289 : Blo 1549472 3490289 := bstep (se 2 (by rfl) ⟨1308858, by rfl⟩ : syracuseStep 3490289 = 2617717) B2617717
theorem B2327027 : Blo 1549472 2327027 := bstep (se 1 (by rfl) ⟨1745270, by rfl⟩ : syracuseStep 2327027 = 3490541) B3490541
theorem B3490307 : Blo 1549472 3490307 := bstep (se 1 (by rfl) ⟨2617730, by rfl⟩ : syracuseStep 3490307 = 5235461) B5235461
theorem B2327057 : Blo 1549472 2327057 := bstep (se 2 (by rfl) ⟨872646, by rfl⟩ : syracuseStep 2327057 = 1745293) B1745293
theorem B2327075 : Blo 1549472 2327075 := bstep (se 1 (by rfl) ⟨1745306, by rfl⟩ : syracuseStep 2327075 = 3490613) B3490613
theorem B5235245 : Blo 1549472 5235245 := bstep (se 3 (by rfl) ⟨981608, by rfl⟩ : syracuseStep 5235245 = 1963217) B1963217
theorem B2327105 : Blo 1549472 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B1655363 : Blo 1549472 1655363 := bstep (se 1 (by rfl) ⟨1241522, by rfl⟩ : syracuseStep 1655363 = 2483045) B2483045
theorem B2482769 : Blo 1549472 2482769 := bstep (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) B1862077
theorem B2327123 : Blo 1549472 2327123 := bstep (se 1 (by rfl) ⟨1745342, by rfl⟩ : syracuseStep 2327123 = 3490685) B3490685
theorem B5235299 : Blo 1549472 5235299 := bstep (se 1 (by rfl) ⟨3926474, by rfl⟩ : syracuseStep 5235299 = 7852949) B7852949
theorem B2327153 : Blo 1549472 2327153 := bstep (se 2 (by rfl) ⟨872682, by rfl⟩ : syracuseStep 2327153 = 1745365) B1745365
theorem B2327171 : Blo 1549472 2327171 := bstep (se 1 (by rfl) ⟨1745378, by rfl⟩ : syracuseStep 2327171 = 3490757) B3490757
theorem B2327201 : Blo 1549472 2327201 := bstep (se 2 (by rfl) ⟨872700, by rfl⟩ : syracuseStep 2327201 = 1745401) B1745401
theorem B2941667 : Blo 1549472 2941667 := bstep (se 1 (by rfl) ⟨2206250, by rfl⟩ : syracuseStep 2941667 = 4412501) B4412501
theorem B3490577 : Blo 1549472 3490577 := bstep (se 2 (by rfl) ⟨1308966, by rfl⟩ : syracuseStep 3490577 = 2617933) B2617933
theorem B3490595 : Blo 1549472 3490595 := bstep (se 1 (by rfl) ⟨2617946, by rfl⟩ : syracuseStep 3490595 = 5235893) B5235893
theorem B6619981 : Blo 1549472 6619981 := bstep (se 3 (by rfl) ⟨1241246, by rfl⟩ : syracuseStep 6619981 = 2482493) B2482493
theorem B5235569 : Blo 1549472 5235569 := bstep (se 2 (by rfl) ⟨1963338, by rfl⟩ : syracuseStep 5235569 = 3926677) B3926677
theorem B4416419 : Blo 1549472 4416419 := bstep (se 1 (by rfl) ⟨3312314, by rfl⟩ : syracuseStep 4416419 = 6624629) B6624629
theorem B44704709 : Blo 1549472 44704709 := bstep (se 4 (by rfl) ⟨4191066, by rfl⟩ : syracuseStep 44704709 = 8382133) B8382133
theorem B4031441 : Blo 1549472 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B2483185 : Blo 1549472 2483185 := bstep (se 2 (by rfl) ⟨931194, by rfl⟩ : syracuseStep 2483185 = 1862389) B1862389
theorem B1549475 : Blo 1549472 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B3310769 : Blo 1549472 3310769 := bstep (se 2 (by rfl) ⟨1241538, by rfl⟩ : syracuseStep 3310769 = 2483077) B2483077
theorem B3925169 : Blo 1549472 3925169 := bstep (se 2 (by rfl) ⟨1471938, by rfl⟩ : syracuseStep 3925169 = 2943877) B2943877
theorem B1549491 : Blo 1549472 1549491 := bstep (se 1 (by rfl) ⟨1162118, by rfl⟩ : syracuseStep 1549491 = 2324237) B2324237
theorem B1549507 : Blo 1549472 1549507 := bstep (se 1 (by rfl) ⟨1162130, by rfl⟩ : syracuseStep 1549507 = 2324261) B2324261
theorem B40854725 : Blo 1549472 40854725 := bstep (se 4 (by rfl) ⟨3830130, by rfl⟩ : syracuseStep 40854725 = 7660261) B7660261
theorem B1549523 : Blo 1549472 1549523 := bstep (se 1 (by rfl) ⟨1162142, by rfl⟩ : syracuseStep 1549523 = 2324285) B2324285
theorem B1549539 : Blo 1549472 1549539 := bstep (se 1 (by rfl) ⟨1162154, by rfl⟩ : syracuseStep 1549539 = 2324309) B2324309
theorem B3925219 : Blo 1549472 3925219 := bstep (se 1 (by rfl) ⟨2943914, by rfl⟩ : syracuseStep 3925219 = 5887829) B5887829
theorem B1549555 : Blo 1549472 1549555 := bstep (se 1 (by rfl) ⟨1162166, by rfl⟩ : syracuseStep 1549555 = 2324333) B2324333
theorem B1549571 : Blo 1549472 1549571 := bstep (se 1 (by rfl) ⟨1162178, by rfl⟩ : syracuseStep 1549571 = 2324357) B2324357
theorem B1549587 : Blo 1549472 1549587 := bstep (se 1 (by rfl) ⟨1162190, by rfl⟩ : syracuseStep 1549587 = 2324381) B2324381
theorem B1549603 : Blo 1549472 1549603 := bstep (se 1 (by rfl) ⟨1162202, by rfl⟩ : syracuseStep 1549603 = 2324405) B2324405
theorem B1549619 : Blo 1549472 1549619 := bstep (se 1 (by rfl) ⟨1162214, by rfl⟩ : syracuseStep 1549619 = 2324429) B2324429
theorem B1549635 : Blo 1549472 1549635 := bstep (se 1 (by rfl) ⟨1162226, by rfl⟩ : syracuseStep 1549635 = 2324453) B2324453
theorem B1549651 : Blo 1549472 1549651 := bstep (se 1 (by rfl) ⟨1162238, by rfl⟩ : syracuseStep 1549651 = 2324477) B2324477
theorem B1549667 : Blo 1549472 1549667 := bstep (se 1 (by rfl) ⟨1162250, by rfl⟩ : syracuseStep 1549667 = 2324501) B2324501
theorem B3925361 : Blo 1549472 3925361 := bstep (se 2 (by rfl) ⟨1472010, by rfl⟩ : syracuseStep 3925361 = 2944021) B2944021
theorem B1549683 : Blo 1549472 1549683 := bstep (se 1 (by rfl) ⟨1162262, by rfl⟩ : syracuseStep 1549683 = 2324525) B2324525
theorem B1549699 : Blo 1549472 1549699 := bstep (se 1 (by rfl) ⟨1162274, by rfl⟩ : syracuseStep 1549699 = 2324549) B2324549
theorem B5236109 : Blo 1549472 5236109 := bstep (se 3 (by rfl) ⟨981770, by rfl⟩ : syracuseStep 5236109 = 1963541) B1963541
theorem B1549715 : Blo 1549472 1549715 := bstep (se 1 (by rfl) ⟨1162286, by rfl⟩ : syracuseStep 1549715 = 2324573) B2324573
theorem B1549731 : Blo 1549472 1549731 := bstep (se 1 (by rfl) ⟨1162298, by rfl⟩ : syracuseStep 1549731 = 2324597) B2324597
theorem B1549747 : Blo 1549472 1549747 := bstep (se 1 (by rfl) ⟨1162310, by rfl⟩ : syracuseStep 1549747 = 2324621) B2324621
theorem B1549763 : Blo 1549472 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B5236163 : Blo 1549472 5236163 := bstep (se 1 (by rfl) ⟨3927122, by rfl⟩ : syracuseStep 5236163 = 7854245) B7854245
theorem B11322821 : Blo 1549472 11322821 := bstep (se 4 (by rfl) ⟨1061514, by rfl⟩ : syracuseStep 11322821 = 2123029) B2123029
theorem B2794961 : Blo 1549472 2794961 := bstep (se 2 (by rfl) ⟨1048110, by rfl⟩ : syracuseStep 2794961 = 2096221) B2096221
theorem B1549779 : Blo 1549472 1549779 := bstep (se 1 (by rfl) ⟨1162334, by rfl⟩ : syracuseStep 1549779 = 2324669) B2324669
theorem B1549795 : Blo 1549472 1549795 := bstep (se 1 (by rfl) ⟨1162346, by rfl⟩ : syracuseStep 1549795 = 2324693) B2324693
theorem B1549811 : Blo 1549472 1549811 := bstep (se 1 (by rfl) ⟨1162358, by rfl⟩ : syracuseStep 1549811 = 2324717) B2324717
theorem B1549827 : Blo 1549472 1549827 := bstep (se 1 (by rfl) ⟨1162370, by rfl⟩ : syracuseStep 1549827 = 2324741) B2324741
theorem B2614801 : Blo 1549472 2614801 := bstep (se 2 (by rfl) ⟨980550, by rfl⟩ : syracuseStep 2614801 = 1961101) B1961101
theorem B1549843 : Blo 1549472 1549843 := bstep (se 1 (by rfl) ⟨1162382, by rfl⟩ : syracuseStep 1549843 = 2324765) B2324765
theorem B1549859 : Blo 1549472 1549859 := bstep (se 1 (by rfl) ⟨1162394, by rfl⟩ : syracuseStep 1549859 = 2324789) B2324789
theorem B2614835 : Blo 1549472 2614835 := bstep (se 1 (by rfl) ⟨1961126, by rfl⟩ : syracuseStep 2614835 = 3922253) B3922253
theorem B1549875 : Blo 1549472 1549875 := bstep (se 1 (by rfl) ⟨1162406, by rfl⟩ : syracuseStep 1549875 = 2324813) B2324813
theorem B37725749 : Blo 1549472 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B1549891 : Blo 1549472 1549891 := bstep (se 1 (by rfl) ⟨1162418, by rfl⟩ : syracuseStep 1549891 = 2324837) B2324837
theorem B1549907 : Blo 1549472 1549907 := bstep (se 1 (by rfl) ⟨1162430, by rfl⟩ : syracuseStep 1549907 = 2324861) B2324861
theorem B1549923 : Blo 1549472 1549923 := bstep (se 1 (by rfl) ⟨1162442, by rfl⟩ : syracuseStep 1549923 = 2324885) B2324885
theorem B2942563 : Blo 1549472 2942563 := bstep (se 1 (by rfl) ⟨2206922, by rfl⟩ : syracuseStep 2942563 = 4413845) B4413845
theorem B1549939 : Blo 1549472 1549939 := bstep (se 1 (by rfl) ⟨1162454, by rfl⟩ : syracuseStep 1549939 = 2324909) B2324909
theorem B1549955 : Blo 1549472 1549955 := bstep (se 1 (by rfl) ⟨1162466, by rfl⟩ : syracuseStep 1549955 = 2324933) B2324933
theorem B1549971 : Blo 1549472 1549971 := bstep (se 1 (by rfl) ⟨1162478, by rfl⟩ : syracuseStep 1549971 = 2324957) B2324957
theorem B1549987 : Blo 1549472 1549987 := bstep (se 1 (by rfl) ⟨1162490, by rfl⟩ : syracuseStep 1549987 = 2324981) B2324981
theorem B2614963 : Blo 1549472 2614963 := bstep (se 1 (by rfl) ⟨1961222, by rfl⟩ : syracuseStep 2614963 = 3922445) B3922445
theorem B1550003 : Blo 1549472 1550003 := bstep (se 1 (by rfl) ⟨1162502, by rfl⟩ : syracuseStep 1550003 = 2325005) B2325005
theorem B17663669 : Blo 1549472 17663669 := bstep (se 5 (by rfl) ⟨827984, by rfl⟩ : syracuseStep 17663669 = 1655969) B1655969
theorem B1656499 : Blo 1549472 1656499 := bstep (se 1 (by rfl) ⟨1242374, by rfl⟩ : syracuseStep 1656499 = 2484749) B2484749
theorem B1550019 : Blo 1549472 1550019 := bstep (se 1 (by rfl) ⟨1162514, by rfl⟩ : syracuseStep 1550019 = 2325029) B2325029
theorem B1550035 : Blo 1549472 1550035 := bstep (se 1 (by rfl) ⟨1162526, by rfl⟩ : syracuseStep 1550035 = 2325053) B2325053
theorem B1550051 : Blo 1549472 1550051 := bstep (se 1 (by rfl) ⟨1162538, by rfl⟩ : syracuseStep 1550051 = 2325077) B2325077
theorem B8382179 : Blo 1549472 8382179 := bstep (se 1 (by rfl) ⟨6286634, by rfl⟩ : syracuseStep 8382179 = 12573269) B12573269
theorem B1550067 : Blo 1549472 1550067 := bstep (se 1 (by rfl) ⟨1162550, by rfl⟩ : syracuseStep 1550067 = 2325101) B2325101
theorem B2942723 : Blo 1549472 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B1550083 : Blo 1549472 1550083 := bstep (se 1 (by rfl) ⟨1162562, by rfl⟩ : syracuseStep 1550083 = 2325125) B2325125
theorem B1550099 : Blo 1549472 1550099 := bstep (se 1 (by rfl) ⟨1162574, by rfl⟩ : syracuseStep 1550099 = 2325149) B2325149
theorem B1550115 : Blo 1549472 1550115 := bstep (se 1 (by rfl) ⟨1162586, by rfl⟩ : syracuseStep 1550115 = 2325173) B2325173
theorem B1550131 : Blo 1549472 1550131 := bstep (se 1 (by rfl) ⟨1162598, by rfl⟩ : syracuseStep 1550131 = 2325197) B2325197
theorem B2615105 : Blo 1549472 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B1550147 : Blo 1549472 1550147 := bstep (se 1 (by rfl) ⟨1162610, by rfl⟩ : syracuseStep 1550147 = 2325221) B2325221
theorem B1550163 : Blo 1549472 1550163 := bstep (se 1 (by rfl) ⟨1162622, by rfl⟩ : syracuseStep 1550163 = 2325245) B2325245
theorem B1550179 : Blo 1549472 1550179 := bstep (se 1 (by rfl) ⟨1162634, by rfl⟩ : syracuseStep 1550179 = 2325269) B2325269
theorem B6621041 : Blo 1549472 6621041 := bstep (se 2 (by rfl) ⟨2482890, by rfl⟩ : syracuseStep 6621041 = 4965781) B4965781
theorem B1550195 : Blo 1549472 1550195 := bstep (se 1 (by rfl) ⟨1162646, by rfl⟩ : syracuseStep 1550195 = 2325293) B2325293
theorem B2484083 : Blo 1549472 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B1550211 : Blo 1549472 1550211 := bstep (se 1 (by rfl) ⟨1162658, by rfl⟩ : syracuseStep 1550211 = 2325317) B2325317
theorem B1550227 : Blo 1549472 1550227 := bstep (se 1 (by rfl) ⟨1162670, by rfl⟩ : syracuseStep 1550227 = 2325341) B2325341
theorem B1550243 : Blo 1549472 1550243 := bstep (se 1 (by rfl) ⟨1162682, by rfl⟩ : syracuseStep 1550243 = 2325365) B2325365
theorem B1550259 : Blo 1549472 1550259 := bstep (se 1 (by rfl) ⟨1162694, by rfl⟩ : syracuseStep 1550259 = 2325389) B2325389
theorem B2615233 : Blo 1549472 2615233 := bstep (se 2 (by rfl) ⟨980712, by rfl⟩ : syracuseStep 2615233 = 1961425) B1961425
theorem B1550275 : Blo 1549472 1550275 := bstep (se 1 (by rfl) ⟨1162706, by rfl⟩ : syracuseStep 1550275 = 2325413) B2325413
theorem B1550291 : Blo 1549472 1550291 := bstep (se 1 (by rfl) ⟨1162718, by rfl⟩ : syracuseStep 1550291 = 2325437) B2325437
theorem B2615267 : Blo 1549472 2615267 := bstep (se 1 (by rfl) ⟨1961450, by rfl⟩ : syracuseStep 2615267 = 3922901) B3922901
theorem B1550307 : Blo 1549472 1550307 := bstep (se 1 (by rfl) ⟨1162730, by rfl⟩ : syracuseStep 1550307 = 2325461) B2325461
theorem B1550323 : Blo 1549472 1550323 := bstep (se 1 (by rfl) ⟨1162742, by rfl⟩ : syracuseStep 1550323 = 2325485) B2325485
theorem B1550339 : Blo 1549472 1550339 := bstep (se 1 (by rfl) ⟨1162754, by rfl⟩ : syracuseStep 1550339 = 2325509) B2325509
theorem B1550355 : Blo 1549472 1550355 := bstep (se 1 (by rfl) ⟨1162766, by rfl⟩ : syracuseStep 1550355 = 2325533) B2325533
theorem B1550371 : Blo 1549472 1550371 := bstep (se 1 (by rfl) ⟨1162778, by rfl⟩ : syracuseStep 1550371 = 2325557) B2325557
theorem B7850033 : Blo 1549472 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B1550387 : Blo 1549472 1550387 := bstep (se 1 (by rfl) ⟨1162790, by rfl⟩ : syracuseStep 1550387 = 2325581) B2325581
theorem B1550403 : Blo 1549472 1550403 := bstep (se 1 (by rfl) ⟨1162802, by rfl⟩ : syracuseStep 1550403 = 2325605) B2325605
theorem B8824909 : Blo 1549472 8824909 := bstep (se 3 (by rfl) ⟨1654670, by rfl⟩ : syracuseStep 8824909 = 3309341) B3309341
theorem B1550419 : Blo 1549472 1550419 := bstep (se 1 (by rfl) ⟨1162814, by rfl⟩ : syracuseStep 1550419 = 2325629) B2325629
theorem B2484307 : Blo 1549472 2484307 := bstep (se 1 (by rfl) ⟨1863230, by rfl⟩ : syracuseStep 2484307 = 3726461) B3726461
theorem B2615395 : Blo 1549472 2615395 := bstep (se 1 (by rfl) ⟨1961546, by rfl⟩ : syracuseStep 2615395 = 3923093) B3923093
theorem B1550435 : Blo 1549472 1550435 := bstep (se 1 (by rfl) ⟨1162826, by rfl⟩ : syracuseStep 1550435 = 2325653) B2325653
theorem B4417649 : Blo 1549472 4417649 := bstep (se 2 (by rfl) ⟨1656618, by rfl⟩ : syracuseStep 4417649 = 3313237) B3313237
theorem B1550451 : Blo 1549472 1550451 := bstep (se 1 (by rfl) ⟨1162838, by rfl⟩ : syracuseStep 1550451 = 2325677) B2325677
theorem B1550467 : Blo 1549472 1550467 := bstep (se 1 (by rfl) ⟨1162850, by rfl⟩ : syracuseStep 1550467 = 2325701) B2325701
theorem B8833157 : Blo 1549472 8833157 := bstep (se 4 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 8833157 = 1656217) B1656217
theorem B1550483 : Blo 1549472 1550483 := bstep (se 1 (by rfl) ⟨1162862, by rfl⟩ : syracuseStep 1550483 = 2325725) B2325725
theorem B1550499 : Blo 1549472 1550499 := bstep (se 1 (by rfl) ⟨1162874, by rfl⟩ : syracuseStep 1550499 = 2325749) B2325749
theorem B1550515 : Blo 1549472 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B1550531 : Blo 1549472 1550531 := bstep (se 1 (by rfl) ⟨1162898, by rfl⟩ : syracuseStep 1550531 = 2325797) B2325797
theorem B5884109 : Blo 1549472 5884109 := bstep (se 3 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 5884109 = 2206541) B2206541
theorem B1550547 : Blo 1549472 1550547 := bstep (se 1 (by rfl) ⟨1162910, by rfl⟩ : syracuseStep 1550547 = 2325821) B2325821
theorem B1550563 : Blo 1549472 1550563 := bstep (se 1 (by rfl) ⟨1162922, by rfl⟩ : syracuseStep 1550563 = 2325845) B2325845
theorem B2615537 : Blo 1549472 2615537 := bstep (se 2 (by rfl) ⟨980826, by rfl⟩ : syracuseStep 2615537 = 1961653) B1961653
theorem B1550579 : Blo 1549472 1550579 := bstep (se 1 (by rfl) ⟨1162934, by rfl⟩ : syracuseStep 1550579 = 2325869) B2325869
theorem B1550595 : Blo 1549472 1550595 := bstep (se 1 (by rfl) ⟨1162946, by rfl⟩ : syracuseStep 1550595 = 2325893) B2325893
theorem B1550611 : Blo 1549472 1550611 := bstep (se 1 (by rfl) ⟨1162958, by rfl⟩ : syracuseStep 1550611 = 2325917) B2325917
theorem B1550627 : Blo 1549472 1550627 := bstep (se 1 (by rfl) ⟨1162970, by rfl⟩ : syracuseStep 1550627 = 2325941) B2325941
theorem B1550643 : Blo 1549472 1550643 := bstep (se 1 (by rfl) ⟨1162982, by rfl⟩ : syracuseStep 1550643 = 2325965) B2325965
theorem B1550659 : Blo 1549472 1550659 := bstep (se 1 (by rfl) ⟨1162994, by rfl⟩ : syracuseStep 1550659 = 2325989) B2325989
theorem B3926353 : Blo 1549472 3926353 := bstep (se 2 (by rfl) ⟨1472382, by rfl⟩ : syracuseStep 3926353 = 2944765) B2944765
theorem B1550675 : Blo 1549472 1550675 := bstep (se 1 (by rfl) ⟨1163006, by rfl⟩ : syracuseStep 1550675 = 2326013) B2326013
theorem B4188515 : Blo 1549472 4188515 := bstep (se 1 (by rfl) ⟨3141386, by rfl⟩ : syracuseStep 4188515 = 6282773) B6282773
theorem B1550691 : Blo 1549472 1550691 := bstep (se 1 (by rfl) ⟨1163018, by rfl⟩ : syracuseStep 1550691 = 2326037) B2326037
theorem B2615665 : Blo 1549472 2615665 := bstep (se 2 (by rfl) ⟨980874, by rfl⟩ : syracuseStep 2615665 = 1961749) B1961749
theorem B11774321 : Blo 1549472 11774321 := bstep (se 2 (by rfl) ⟨4415370, by rfl⟩ : syracuseStep 11774321 = 8830741) B8830741
theorem B1550707 : Blo 1549472 1550707 := bstep (se 1 (by rfl) ⟨1163030, by rfl⟩ : syracuseStep 1550707 = 2326061) B2326061
theorem B2689393 : Blo 1549472 2689393 := bstep (se 2 (by rfl) ⟨1008522, by rfl⟩ : syracuseStep 2689393 = 2017045) B2017045
theorem B1550723 : Blo 1549472 1550723 := bstep (se 1 (by rfl) ⟨1163042, by rfl⟩ : syracuseStep 1550723 = 2326085) B2326085
theorem B2615699 : Blo 1549472 2615699 := bstep (se 1 (by rfl) ⟨1961774, by rfl⟩ : syracuseStep 2615699 = 3923549) B3923549
theorem B1550739 : Blo 1549472 1550739 := bstep (se 1 (by rfl) ⟨1163054, by rfl⟩ : syracuseStep 1550739 = 2326109) B2326109
theorem B1550755 : Blo 1549472 1550755 := bstep (se 1 (by rfl) ⟨1163066, by rfl⟩ : syracuseStep 1550755 = 2326133) B2326133
theorem B1550771 : Blo 1549472 1550771 := bstep (se 1 (by rfl) ⟨1163078, by rfl⟩ : syracuseStep 1550771 = 2326157) B2326157
theorem B1550787 : Blo 1549472 1550787 := bstep (se 1 (by rfl) ⟨1163090, by rfl⟩ : syracuseStep 1550787 = 2326181) B2326181
theorem B181299653 : Blo 1549472 181299653 := bstep (se 4 (by rfl) ⟨16996842, by rfl⟩ : syracuseStep 181299653 = 33993685) B33993685
theorem B1550803 : Blo 1549472 1550803 := bstep (se 1 (by rfl) ⟨1163102, by rfl⟩ : syracuseStep 1550803 = 2326205) B2326205
theorem B26847715 : Blo 1549472 26847715 := bstep (se 1 (by rfl) ⟨20135786, by rfl⟩ : syracuseStep 26847715 = 40271573) B40271573
theorem B4966883 : Blo 1549472 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B1550819 : Blo 1549472 1550819 := bstep (se 1 (by rfl) ⟨1163114, by rfl⟩ : syracuseStep 1550819 = 2326229) B2326229
theorem B1550835 : Blo 1549472 1550835 := bstep (se 1 (by rfl) ⟨1163126, by rfl⟩ : syracuseStep 1550835 = 2326253) B2326253
theorem B1550851 : Blo 1549472 1550851 := bstep (se 1 (by rfl) ⟨1163138, by rfl⟩ : syracuseStep 1550851 = 2326277) B2326277
theorem B2615827 : Blo 1549472 2615827 := bstep (se 1 (by rfl) ⟨1961870, by rfl⟩ : syracuseStep 2615827 = 3923741) B3923741
theorem B1550867 : Blo 1549472 1550867 := bstep (se 1 (by rfl) ⟨1163150, by rfl⟩ : syracuseStep 1550867 = 2326301) B2326301
theorem B1550883 : Blo 1549472 1550883 := bstep (se 1 (by rfl) ⟨1163162, by rfl⟩ : syracuseStep 1550883 = 2326325) B2326325
theorem B9939505 : Blo 1549472 9939505 := bstep (se 2 (by rfl) ⟨3727314, by rfl⟩ : syracuseStep 9939505 = 7454629) B7454629
theorem B1550899 : Blo 1549472 1550899 := bstep (se 1 (by rfl) ⟨1163174, by rfl⟩ : syracuseStep 1550899 = 2326349) B2326349
theorem B2206273 : Blo 1549472 2206273 := bstep (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) B1654705
theorem B1550915 : Blo 1549472 1550915 := bstep (se 1 (by rfl) ⟨1163186, by rfl⟩ : syracuseStep 1550915 = 2326373) B2326373
theorem B1550931 : Blo 1549472 1550931 := bstep (se 1 (by rfl) ⟨1163198, by rfl⟩ : syracuseStep 1550931 = 2326397) B2326397
theorem B4967011 : Blo 1549472 4967011 := bstep (se 1 (by rfl) ⟨3725258, by rfl⟩ : syracuseStep 4967011 = 7450517) B7450517
theorem B1550947 : Blo 1549472 1550947 := bstep (se 1 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 1550947 = 2326421) B2326421
theorem B3926627 : Blo 1549472 3926627 := bstep (se 1 (by rfl) ⟨2944970, by rfl⟩ : syracuseStep 3926627 = 5889941) B5889941
theorem B1550963 : Blo 1549472 1550963 := bstep (se 1 (by rfl) ⟨1163222, by rfl⟩ : syracuseStep 1550963 = 2326445) B2326445
theorem B1550979 : Blo 1549472 1550979 := bstep (se 1 (by rfl) ⟨1163234, by rfl⟩ : syracuseStep 1550979 = 2326469) B2326469
theorem B1550995 : Blo 1549472 1550995 := bstep (se 1 (by rfl) ⟨1163246, by rfl⟩ : syracuseStep 1550995 = 2326493) B2326493
theorem B2615969 : Blo 1549472 2615969 := bstep (se 2 (by rfl) ⟨980988, by rfl⟩ : syracuseStep 2615969 = 1961977) B1961977
theorem B1551011 : Blo 1549472 1551011 := bstep (se 1 (by rfl) ⟨1163258, by rfl⟩ : syracuseStep 1551011 = 2326517) B2326517
theorem B2206387 : Blo 1549472 2206387 := bstep (se 1 (by rfl) ⟨1654790, by rfl⟩ : syracuseStep 2206387 = 3309581) B3309581
theorem B1551027 : Blo 1549472 1551027 := bstep (se 1 (by rfl) ⟨1163270, by rfl⟩ : syracuseStep 1551027 = 2326541) B2326541
theorem B1551043 : Blo 1549472 1551043 := bstep (se 1 (by rfl) ⟨1163282, by rfl⟩ : syracuseStep 1551043 = 2326565) B2326565
theorem B19876549 : Blo 1549472 19876549 := bstep (se 4 (by rfl) ⟨1863426, by rfl⟩ : syracuseStep 19876549 = 3726853) B3726853
theorem B1551059 : Blo 1549472 1551059 := bstep (se 1 (by rfl) ⟨1163294, by rfl⟩ : syracuseStep 1551059 = 2326589) B2326589
theorem B1551075 : Blo 1549472 1551075 := bstep (se 1 (by rfl) ⟨1163306, by rfl⟩ : syracuseStep 1551075 = 2326613) B2326613
theorem B1551091 : Blo 1549472 1551091 := bstep (se 1 (by rfl) ⟨1163318, by rfl⟩ : syracuseStep 1551091 = 2326637) B2326637
theorem B1551107 : Blo 1549472 1551107 := bstep (se 1 (by rfl) ⟨1163330, by rfl⟩ : syracuseStep 1551107 = 2326661) B2326661
theorem B1551123 : Blo 1549472 1551123 := bstep (se 1 (by rfl) ⟨1163342, by rfl⟩ : syracuseStep 1551123 = 2326685) B2326685
theorem B2616097 : Blo 1549472 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B1551139 : Blo 1549472 1551139 := bstep (se 1 (by rfl) ⟨1163354, by rfl⟩ : syracuseStep 1551139 = 2326709) B2326709
theorem B3926819 : Blo 1549472 3926819 := bstep (se 1 (by rfl) ⟨2945114, by rfl⟩ : syracuseStep 3926819 = 5890229) B5890229
theorem B2943793 : Blo 1549472 2943793 := bstep (se 2 (by rfl) ⟨1103922, by rfl⟩ : syracuseStep 2943793 = 2207845) B2207845
theorem B1551155 : Blo 1549472 1551155 := bstep (se 1 (by rfl) ⟨1163366, by rfl⟩ : syracuseStep 1551155 = 2326733) B2326733
theorem B2616131 : Blo 1549472 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B3312451 : Blo 1549472 3312451 := bstep (se 1 (by rfl) ⟨2484338, by rfl⟩ : syracuseStep 3312451 = 4968677) B4968677
theorem B1551171 : Blo 1549472 1551171 := bstep (se 1 (by rfl) ⟨1163378, by rfl⟩ : syracuseStep 1551171 = 2326757) B2326757
theorem B1551187 : Blo 1549472 1551187 := bstep (se 1 (by rfl) ⟨1163390, by rfl⟩ : syracuseStep 1551187 = 2326781) B2326781
theorem B1551203 : Blo 1549472 1551203 := bstep (se 1 (by rfl) ⟨1163402, by rfl⟩ : syracuseStep 1551203 = 2326805) B2326805
theorem B1551219 : Blo 1549472 1551219 := bstep (se 1 (by rfl) ⟨1163414, by rfl⟩ : syracuseStep 1551219 = 2326829) B2326829
theorem B1551235 : Blo 1549472 1551235 := bstep (se 1 (by rfl) ⟨1163426, by rfl⟩ : syracuseStep 1551235 = 2326853) B2326853
theorem B4475789 : Blo 1549472 4475789 := bstep (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) B1678421
theorem B1551251 : Blo 1549472 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1551267 : Blo 1549472 1551267 := bstep (se 1 (by rfl) ⟨1163450, by rfl⟩ : syracuseStep 1551267 = 2326901) B2326901
theorem B4967345 : Blo 1549472 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B1551283 : Blo 1549472 1551283 := bstep (se 1 (by rfl) ⟨1163462, by rfl⟩ : syracuseStep 1551283 = 2326925) B2326925
theorem B2616259 : Blo 1549472 2616259 := bstep (se 1 (by rfl) ⟨1962194, by rfl⟩ : syracuseStep 2616259 = 3924389) B3924389
theorem B1551299 : Blo 1549472 1551299 := bstep (se 1 (by rfl) ⟨1163474, by rfl⟩ : syracuseStep 1551299 = 2326949) B2326949
theorem B5589965 : Blo 1549472 5589965 := bstep (se 3 (by rfl) ⟨1048118, by rfl⟩ : syracuseStep 5589965 = 2096237) B2096237
theorem B5229521 : Blo 1549472 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B1551315 : Blo 1549472 1551315 := bstep (se 1 (by rfl) ⟨1163486, by rfl⟩ : syracuseStep 1551315 = 2326973) B2326973
theorem B1551331 : Blo 1549472 1551331 := bstep (se 1 (by rfl) ⟨1163498, by rfl⟩ : syracuseStep 1551331 = 2326997) B2326997
theorem B5884913 : Blo 1549472 5884913 := bstep (se 2 (by rfl) ⟨2206842, by rfl⟩ : syracuseStep 5884913 = 4413685) B4413685
theorem B1551347 : Blo 1549472 1551347 := bstep (se 1 (by rfl) ⟨1163510, by rfl⟩ : syracuseStep 1551347 = 2327021) B2327021
theorem B4779011 : Blo 1549472 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B1551363 : Blo 1549472 1551363 := bstep (se 1 (by rfl) ⟨1163522, by rfl⟩ : syracuseStep 1551363 = 2327045) B2327045
theorem B1551379 : Blo 1549472 1551379 := bstep (se 1 (by rfl) ⟨1163534, by rfl⟩ : syracuseStep 1551379 = 2327069) B2327069
theorem B1551395 : Blo 1549472 1551395 := bstep (se 1 (by rfl) ⟨1163546, by rfl⟩ : syracuseStep 1551395 = 2327093) B2327093
theorem B1551411 : Blo 1549472 1551411 := bstep (se 1 (by rfl) ⟨1163558, by rfl⟩ : syracuseStep 1551411 = 2327117) B2327117
theorem B1551427 : Blo 1549472 1551427 := bstep (se 1 (by rfl) ⟨1163570, by rfl⟩ : syracuseStep 1551427 = 2327141) B2327141
theorem B2616401 : Blo 1549472 2616401 := bstep (se 2 (by rfl) ⟨981150, by rfl⟩ : syracuseStep 2616401 = 1962301) B1962301
theorem B1551443 : Blo 1549472 1551443 := bstep (se 1 (by rfl) ⟨1163582, by rfl⟩ : syracuseStep 1551443 = 2327165) B2327165
theorem B1551459 : Blo 1549472 1551459 := bstep (se 1 (by rfl) ⟨1163594, by rfl⟩ : syracuseStep 1551459 = 2327189) B2327189
theorem B12102797 : Blo 1549472 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B2616529 : Blo 1549472 2616529 := bstep (se 2 (by rfl) ⟨981198, by rfl⟩ : syracuseStep 2616529 = 1962397) B1962397
theorem B2616563 : Blo 1549472 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B3312913 : Blo 1549472 3312913 := bstep (se 2 (by rfl) ⟨1242342, by rfl⟩ : syracuseStep 3312913 = 2484685) B2484685
theorem B2616691 : Blo 1549472 2616691 := bstep (se 1 (by rfl) ⟨1962518, by rfl⟩ : syracuseStep 2616691 = 3925037) B3925037
theorem B3403139 : Blo 1549472 3403139 := bstep (se 1 (by rfl) ⟨2552354, by rfl⟩ : syracuseStep 3403139 = 5104709) B5104709
theorem B68930957 : Blo 1549472 68930957 := bstep (se 3 (by rfl) ⟨12924554, by rfl⟩ : syracuseStep 68930957 = 25849109) B25849109
theorem B1863091 : Blo 1549472 1863091 := bstep (se 1 (by rfl) ⟨1397318, by rfl⟩ : syracuseStep 1863091 = 2794637) B2794637
theorem B7851491 : Blo 1549472 7851491 := bstep (se 1 (by rfl) ⟨5888618, by rfl⟩ : syracuseStep 7851491 = 11777237) B11777237
theorem B5230061 : Blo 1549472 5230061 := bstep (se 3 (by rfl) ⟨980636, by rfl⟩ : syracuseStep 5230061 = 1961273) B1961273
theorem B2616833 : Blo 1549472 2616833 := bstep (se 2 (by rfl) ⟨981312, by rfl⟩ : syracuseStep 2616833 = 1962625) B1962625
theorem B1961491 : Blo 1549472 1961491 := bstep (se 1 (by rfl) ⟨1471118, by rfl⟩ : syracuseStep 1961491 = 2942237) B2942237
theorem B5230115 : Blo 1549472 5230115 := bstep (se 1 (by rfl) ⟨3922586, by rfl⟩ : syracuseStep 5230115 = 7845173) B7845173
theorem B6286925 : Blo 1549472 6286925 := bstep (se 3 (by rfl) ⟨1178798, by rfl⟩ : syracuseStep 6286925 = 2357597) B2357597
theorem B1961587 : Blo 1549472 1961587 := bstep (se 1 (by rfl) ⟨1471190, by rfl⟩ : syracuseStep 1961587 = 2942381) B2942381
theorem B2616961 : Blo 1549472 2616961 := bstep (se 2 (by rfl) ⟨981360, by rfl⟩ : syracuseStep 2616961 = 1962721) B1962721
theorem B5885581 : Blo 1549472 5885581 := bstep (se 3 (by rfl) ⟨1103546, by rfl⟩ : syracuseStep 5885581 = 2207093) B2207093
theorem B2616995 : Blo 1549472 2616995 := bstep (se 1 (by rfl) ⟨1962746, by rfl⟩ : syracuseStep 2616995 = 3925493) B3925493
theorem B18853573 : Blo 1549472 18853573 := bstep (se 4 (by rfl) ⟨1767522, by rfl⟩ : syracuseStep 18853573 = 3535045) B3535045
theorem B2617123 : Blo 1549472 2617123 := bstep (se 1 (by rfl) ⟨1962842, by rfl⟩ : syracuseStep 2617123 = 3925685) B3925685
theorem B5230385 : Blo 1549472 5230385 := bstep (se 2 (by rfl) ⟨1961394, by rfl⟩ : syracuseStep 5230385 = 3922789) B3922789
theorem B2944849 : Blo 1549472 2944849 := bstep (se 2 (by rfl) ⟨1104318, by rfl⟩ : syracuseStep 2944849 = 2208637) B2208637
theorem B2617265 : Blo 1549472 2617265 := bstep (se 2 (by rfl) ⟨981474, by rfl⟩ : syracuseStep 2617265 = 1962949) B1962949
theorem B2207731 : Blo 1549472 2207731 := bstep (se 1 (by rfl) ⟨1655798, by rfl⟩ : syracuseStep 2207731 = 3311597) B3311597
theorem B8826893 : Blo 1549472 8826893 := bstep (se 3 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 8826893 = 3310085) B3310085
theorem B2617393 : Blo 1549472 2617393 := bstep (se 2 (by rfl) ⟨981522, by rfl⟩ : syracuseStep 2617393 = 1963045) B1963045
theorem B10203205 : Blo 1549472 10203205 := bstep (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) B1913101
theorem B2617427 : Blo 1549472 2617427 := bstep (se 1 (by rfl) ⟨1963070, by rfl⟩ : syracuseStep 2617427 = 3926141) B3926141
theorem B1962083 : Blo 1549472 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B2617555 : Blo 1549472 2617555 := bstep (se 1 (by rfl) ⟨1963166, by rfl⟩ : syracuseStep 2617555 = 3926333) B3926333
theorem B2945251 : Blo 1549472 2945251 := bstep (se 1 (by rfl) ⟨2208938, by rfl⟩ : syracuseStep 2945251 = 4417877) B4417877
theorem B11178253 : Blo 1549472 11178253 := bstep (se 3 (by rfl) ⟨2095922, by rfl⟩ : syracuseStep 11178253 = 4191845) B4191845
theorem B7852301 : Blo 1549472 7852301 := bstep (se 3 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 7852301 = 2944613) B2944613
theorem B2945297 : Blo 1549472 2945297 := bstep (se 2 (by rfl) ⟨1104486, by rfl⟩ : syracuseStep 2945297 = 2208973) B2208973
theorem B5230925 : Blo 1549472 5230925 := bstep (se 3 (by rfl) ⟨980798, by rfl⟩ : syracuseStep 5230925 = 1961597) B1961597
theorem B2617697 : Blo 1549472 2617697 := bstep (se 2 (by rfl) ⟨981636, by rfl⟩ : syracuseStep 2617697 = 1963273) B1963273
theorem B5230979 : Blo 1549472 5230979 := bstep (se 1 (by rfl) ⟨3923234, by rfl⟩ : syracuseStep 5230979 = 7846469) B7846469
theorem B5886371 : Blo 1549472 5886371 := bstep (se 1 (by rfl) ⟨4414778, by rfl⟩ : syracuseStep 5886371 = 8829557) B8829557
theorem B2617825 : Blo 1549472 2617825 := bstep (se 2 (by rfl) ⟨981684, by rfl⟩ : syracuseStep 2617825 = 1963369) B1963369
theorem B5591537 : Blo 1549472 5591537 := bstep (se 2 (by rfl) ⟨2096826, by rfl⟩ : syracuseStep 5591537 = 4193653) B4193653
theorem B2617859 : Blo 1549472 2617859 := bstep (se 1 (by rfl) ⟨1963394, by rfl⟩ : syracuseStep 2617859 = 3926789) B3926789
theorem B10629731 : Blo 1549472 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B2617987 : Blo 1549472 2617987 := bstep (se 1 (by rfl) ⟨1963490, by rfl⟩ : syracuseStep 2617987 = 3926981) B3926981
theorem B5231249 : Blo 1549472 5231249 := bstep (se 2 (by rfl) ⟨1961718, by rfl⟩ : syracuseStep 5231249 = 3923437) B3923437
theorem B6624013 : Blo 1549472 6624013 := bstep (se 3 (by rfl) ⟨1242002, by rfl⟩ : syracuseStep 6624013 = 2484005) B2484005
theorem B1962787 : Blo 1549472 1962787 := bstep (se 1 (by rfl) ⟨1472090, by rfl⟩ : syracuseStep 1962787 = 2944181) B2944181
theorem B2831171 : Blo 1549472 2831171 := bstep (se 1 (by rfl) ⟨2123378, by rfl⟩ : syracuseStep 2831171 = 4246757) B4246757
theorem B3486545 : Blo 1549472 3486545 := bstep (se 2 (by rfl) ⟨1307454, by rfl⟩ : syracuseStep 3486545 = 2614909) B2614909
theorem B3486563 : Blo 1549472 3486563 := bstep (se 1 (by rfl) ⟨2614922, by rfl⟩ : syracuseStep 3486563 = 5229845) B5229845
theorem B1962883 : Blo 1549472 1962883 := bstep (se 1 (by rfl) ⟨1472162, by rfl⟩ : syracuseStep 1962883 = 2944325) B2944325
theorem B8827825 : Blo 1549472 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B4412387 : Blo 1549472 4412387 := bstep (se 1 (by rfl) ⟨3309290, by rfl⟩ : syracuseStep 4412387 = 6618581) B6618581
theorem B7844849 : Blo 1549472 7844849 := bstep (se 2 (by rfl) ⟨2941818, by rfl⟩ : syracuseStep 7844849 = 5883637) B5883637
theorem B5887025 : Blo 1549472 5887025 := bstep (se 2 (by rfl) ⟨2207634, by rfl⟩ : syracuseStep 5887025 = 4415269) B4415269
theorem B3724355 : Blo 1549472 3724355 := bstep (se 1 (by rfl) ⟨2793266, by rfl⟩ : syracuseStep 3724355 = 5586533) B5586533
theorem B2208865 : Blo 1549472 2208865 := bstep (se 2 (by rfl) ⟨828324, by rfl⟩ : syracuseStep 2208865 = 1656649) B1656649
theorem B7451747 : Blo 1549472 7451747 := bstep (se 1 (by rfl) ⟨5588810, by rfl⟩ : syracuseStep 7451747 = 11177621) B11177621
theorem B6624355 : Blo 1549472 6624355 := bstep (se 1 (by rfl) ⟨4968266, by rfl⟩ : syracuseStep 6624355 = 9936533) B9936533
theorem B3486833 : Blo 1549472 3486833 := bstep (se 2 (by rfl) ⟨1307562, by rfl⟩ : syracuseStep 3486833 = 2615125) B2615125
theorem B3486851 : Blo 1549472 3486851 := bstep (se 1 (by rfl) ⟨2615138, by rfl⟩ : syracuseStep 3486851 = 5230277) B5230277
theorem B5231789 : Blo 1549472 5231789 := bstep (se 3 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 5231789 = 1961921) B1961921
theorem B2208961 : Blo 1549472 2208961 := bstep (se 2 (by rfl) ⟨828360, by rfl⟩ : syracuseStep 2208961 = 1656721) B1656721
theorem B2094275 : Blo 1549472 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B5231843 : Blo 1549472 5231843 := bstep (se 1 (by rfl) ⟨3923882, by rfl⟩ : syracuseStep 5231843 = 7847765) B7847765
theorem B1963379 : Blo 1549472 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B3487121 : Blo 1549472 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B3487139 : Blo 1549472 3487139 := bstep (se 1 (by rfl) ⟨2615354, by rfl⟩ : syracuseStep 3487139 = 5230709) B5230709
theorem B13424069 : Blo 1549472 13424069 := bstep (se 4 (by rfl) ⟨1258506, by rfl⟩ : syracuseStep 13424069 = 2517013) B2517013
theorem B5232113 : Blo 1549472 5232113 := bstep (se 2 (by rfl) ⟨1962042, by rfl⟩ : syracuseStep 5232113 = 3924085) B3924085
theorem B5977613 : Blo 1549472 5977613 := bstep (se 3 (by rfl) ⟨1120802, by rfl⟩ : syracuseStep 5977613 = 2241605) B2241605
theorem B2094625 : Blo 1549472 2094625 := bstep (se 2 (by rfl) ⟨785484, by rfl⟩ : syracuseStep 2094625 = 1570969) B1570969
theorem B2356771 : Blo 1549472 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B2389537 : Blo 1549472 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B3487409 : Blo 1549472 3487409 := bstep (se 2 (by rfl) ⟨1307778, by rfl⟩ : syracuseStep 3487409 = 2615557) B2615557
theorem B3487427 : Blo 1549472 3487427 := bstep (se 1 (by rfl) ⟨2615570, by rfl⟩ : syracuseStep 3487427 = 5231141) B5231141
theorem B2324225 : Blo 1549472 2324225 := bstep (se 2 (by rfl) ⟨871584, by rfl⟩ : syracuseStep 2324225 = 1743169) B1743169
theorem B2324243 : Blo 1549472 2324243 := bstep (se 1 (by rfl) ⟨1743182, by rfl⟩ : syracuseStep 2324243 = 3486365) B3486365
theorem B2324273 : Blo 1549472 2324273 := bstep (se 2 (by rfl) ⟨871602, by rfl⟩ : syracuseStep 2324273 = 1743205) B1743205
theorem B2324291 : Blo 1549472 2324291 := bstep (se 1 (by rfl) ⟨1743218, by rfl⟩ : syracuseStep 2324291 = 3486437) B3486437
theorem B4970317 : Blo 1549472 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B2324321 : Blo 1549472 2324321 := bstep (se 2 (by rfl) ⟨871620, by rfl⟩ : syracuseStep 2324321 = 1743241) B1743241
theorem B2324339 : Blo 1549472 2324339 := bstep (se 1 (by rfl) ⟨1743254, by rfl⟩ : syracuseStep 2324339 = 3486509) B3486509
theorem B2324369 : Blo 1549472 2324369 := bstep (se 2 (by rfl) ⟨871638, by rfl⟩ : syracuseStep 2324369 = 1743277) B1743277
theorem B2324387 : Blo 1549472 2324387 := bstep (se 1 (by rfl) ⟨1743290, by rfl⟩ : syracuseStep 2324387 = 3486581) B3486581
theorem B2324417 : Blo 1549472 2324417 := bstep (se 2 (by rfl) ⟨871656, by rfl⟩ : syracuseStep 2324417 = 1743313) B1743313
theorem B3487697 : Blo 1549472 3487697 := bstep (se 2 (by rfl) ⟨1307886, by rfl⟩ : syracuseStep 3487697 = 2615773) B2615773
theorem B2324435 : Blo 1549472 2324435 := bstep (se 1 (by rfl) ⟨1743326, by rfl⟩ : syracuseStep 2324435 = 3486653) B3486653
theorem B3487715 : Blo 1549472 3487715 := bstep (se 1 (by rfl) ⟨2615786, by rfl⟩ : syracuseStep 3487715 = 5231573) B5231573
theorem B2324465 : Blo 1549472 2324465 := bstep (se 2 (by rfl) ⟨871674, by rfl⟩ : syracuseStep 2324465 = 1743349) B1743349
theorem B8501233 : Blo 1549472 8501233 := bstep (se 2 (by rfl) ⟨3187962, by rfl⟩ : syracuseStep 8501233 = 6375925) B6375925
theorem B2324483 : Blo 1549472 2324483 := bstep (se 1 (by rfl) ⟨1743362, by rfl⟩ : syracuseStep 2324483 = 3486725) B3486725
theorem B5232653 : Blo 1549472 5232653 := bstep (se 3 (by rfl) ⟨981122, by rfl⟩ : syracuseStep 5232653 = 1962245) B1962245
theorem B4413457 : Blo 1549472 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B2324513 : Blo 1549472 2324513 := bstep (se 2 (by rfl) ⟨871692, by rfl⟩ : syracuseStep 2324513 = 1743385) B1743385
theorem B2324531 : Blo 1549472 2324531 := bstep (se 1 (by rfl) ⟨1743398, by rfl⟩ : syracuseStep 2324531 = 3486797) B3486797
theorem B5232707 : Blo 1549472 5232707 := bstep (se 1 (by rfl) ⟨3924530, by rfl⟩ : syracuseStep 5232707 = 7849061) B7849061
theorem B2324561 : Blo 1549472 2324561 := bstep (se 2 (by rfl) ⟨871710, by rfl⟩ : syracuseStep 2324561 = 1743421) B1743421
theorem B1677395 : Blo 1549472 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B2324579 : Blo 1549472 2324579 := bstep (se 1 (by rfl) ⟨1743434, by rfl⟩ : syracuseStep 2324579 = 3486869) B3486869
theorem B2324609 : Blo 1549472 2324609 := bstep (se 2 (by rfl) ⟨871728, by rfl⟩ : syracuseStep 2324609 = 1743457) B1743457
theorem B12572813 : Blo 1549472 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B2324627 : Blo 1549472 2324627 := bstep (se 1 (by rfl) ⟨1743470, by rfl⟩ : syracuseStep 2324627 = 3486941) B3486941
theorem B2324657 : Blo 1549472 2324657 := bstep (se 2 (by rfl) ⟨871746, by rfl⟩ : syracuseStep 2324657 = 1743493) B1743493
theorem B3356849 : Blo 1549472 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B2324675 : Blo 1549472 2324675 := bstep (se 1 (by rfl) ⟨1743506, by rfl⟩ : syracuseStep 2324675 = 3487013) B3487013
theorem B2095313 : Blo 1549472 2095313 := bstep (se 2 (by rfl) ⟨785742, by rfl⟩ : syracuseStep 2095313 = 1571485) B1571485
theorem B2324705 : Blo 1549472 2324705 := bstep (se 2 (by rfl) ⟨871764, by rfl⟩ : syracuseStep 2324705 = 1743529) B1743529
theorem B3487985 : Blo 1549472 3487985 := bstep (se 2 (by rfl) ⟨1307994, by rfl⟩ : syracuseStep 3487985 = 2615989) B2615989
theorem B2324723 : Blo 1549472 2324723 := bstep (se 1 (by rfl) ⟨1743542, by rfl⟩ : syracuseStep 2324723 = 3487085) B3487085
theorem B3488003 : Blo 1549472 3488003 := bstep (se 1 (by rfl) ⟨2616002, by rfl⟩ : syracuseStep 3488003 = 5232005) B5232005
theorem B12572941 : Blo 1549472 12572941 := bstep (se 3 (by rfl) ⟨2357426, by rfl⟩ : syracuseStep 12572941 = 4714853) B4714853
theorem B2324753 : Blo 1549472 2324753 := bstep (se 2 (by rfl) ⟨871782, by rfl⟩ : syracuseStep 2324753 = 1743565) B1743565
theorem B2324771 : Blo 1549472 2324771 := bstep (se 1 (by rfl) ⟨1743578, by rfl⟩ : syracuseStep 2324771 = 3487157) B3487157
theorem B2324801 : Blo 1549472 2324801 := bstep (se 2 (by rfl) ⟨871800, by rfl⟩ : syracuseStep 2324801 = 1743601) B1743601
theorem B5232977 : Blo 1549472 5232977 := bstep (se 2 (by rfl) ⟨1962366, by rfl⟩ : syracuseStep 5232977 = 3924733) B3924733
theorem B1743187 : Blo 1549472 1743187 := bstep (se 1 (by rfl) ⟨1307390, by rfl⟩ : syracuseStep 1743187 = 2614781) B2614781
theorem B2324819 : Blo 1549472 2324819 := bstep (se 1 (by rfl) ⟨1743614, by rfl⟩ : syracuseStep 2324819 = 3487229) B3487229
theorem B8829283 : Blo 1549472 8829283 := bstep (se 1 (by rfl) ⟨6621962, by rfl⟩ : syracuseStep 8829283 = 13243925) B13243925
theorem B4716899 : Blo 1549472 4716899 := bstep (se 1 (by rfl) ⟨3537674, by rfl⟩ : syracuseStep 4716899 = 7075349) B7075349
theorem B2324849 : Blo 1549472 2324849 := bstep (se 2 (by rfl) ⟨871818, by rfl⟩ : syracuseStep 2324849 = 1743637) B1743637
theorem B2324867 : Blo 1549472 2324867 := bstep (se 1 (by rfl) ⟨1743650, by rfl⟩ : syracuseStep 2324867 = 3487301) B3487301
theorem B2324897 : Blo 1549472 2324897 := bstep (se 2 (by rfl) ⟨871836, by rfl⟩ : syracuseStep 2324897 = 1743673) B1743673
theorem B7846307 : Blo 1549472 7846307 := bstep (se 1 (by rfl) ⟨5884730, by rfl⟩ : syracuseStep 7846307 = 11769461) B11769461
theorem B7453091 : Blo 1549472 7453091 := bstep (se 1 (by rfl) ⟨5589818, by rfl⟩ : syracuseStep 7453091 = 11179637) B11179637
theorem B2324915 : Blo 1549472 2324915 := bstep (se 1 (by rfl) ⟨1743686, by rfl⟩ : syracuseStep 2324915 = 3487373) B3487373
theorem B2324945 : Blo 1549472 2324945 := bstep (se 2 (by rfl) ⟨871854, by rfl⟩ : syracuseStep 2324945 = 1743709) B1743709
theorem B3725777 : Blo 1549472 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B1743331 : Blo 1549472 1743331 := bstep (se 1 (by rfl) ⟨1307498, by rfl⟩ : syracuseStep 1743331 = 2614997) B2614997
theorem B2324963 : Blo 1549472 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B5888483 : Blo 1549472 5888483 := bstep (se 1 (by rfl) ⟨4416362, by rfl⟩ : syracuseStep 5888483 = 8832725) B8832725
theorem B5888497 : Blo 1549472 5888497 := bstep (se 2 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 5888497 = 4416373) B4416373
theorem B2324993 : Blo 1549472 2324993 := bstep (se 2 (by rfl) ⟨871872, by rfl⟩ : syracuseStep 2324993 = 1743745) B1743745
theorem B3488273 : Blo 1549472 3488273 := bstep (se 2 (by rfl) ⟨1308102, by rfl⟩ : syracuseStep 3488273 = 2616205) B2616205
theorem B2325011 : Blo 1549472 2325011 := bstep (se 1 (by rfl) ⟨1743758, by rfl⟩ : syracuseStep 2325011 = 3487517) B3487517
theorem B3488291 : Blo 1549472 3488291 := bstep (se 1 (by rfl) ⟨2616218, by rfl⟩ : syracuseStep 3488291 = 5232437) B5232437
theorem B2325041 : Blo 1549472 2325041 := bstep (se 2 (by rfl) ⟨871890, by rfl⟩ : syracuseStep 2325041 = 1743781) B1743781
theorem B2325059 : Blo 1549472 2325059 := bstep (se 1 (by rfl) ⟨1743794, by rfl⟩ : syracuseStep 2325059 = 3487589) B3487589
theorem B12098117 : Blo 1549472 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B2325089 : Blo 1549472 2325089 := bstep (se 2 (by rfl) ⟨871908, by rfl⟩ : syracuseStep 2325089 = 1743817) B1743817
theorem B9935459 : Blo 1549472 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B1743475 : Blo 1549472 1743475 := bstep (se 1 (by rfl) ⟨1307606, by rfl⟩ : syracuseStep 1743475 = 2615213) B2615213
theorem B2325107 : Blo 1549472 2325107 := bstep (se 1 (by rfl) ⟨1743830, by rfl⟩ : syracuseStep 2325107 = 3487661) B3487661
theorem B3922577 : Blo 1549472 3922577 := bstep (se 2 (by rfl) ⟨1470966, by rfl⟩ : syracuseStep 3922577 = 2941933) B2941933
theorem B2325137 : Blo 1549472 2325137 := bstep (se 2 (by rfl) ⟨871926, by rfl⟩ : syracuseStep 2325137 = 1743853) B1743853
theorem B2325155 : Blo 1549472 2325155 := bstep (se 1 (by rfl) ⟨1743866, by rfl⟩ : syracuseStep 2325155 = 3487733) B3487733
theorem B2325185 : Blo 1549472 2325185 := bstep (se 2 (by rfl) ⟨871944, by rfl⟩ : syracuseStep 2325185 = 1743889) B1743889
theorem B3922627 : Blo 1549472 3922627 := bstep (se 1 (by rfl) ⟨2941970, by rfl⟩ : syracuseStep 3922627 = 5883941) B5883941
theorem B2325203 : Blo 1549472 2325203 := bstep (se 1 (by rfl) ⟨1743902, by rfl⟩ : syracuseStep 2325203 = 3487805) B3487805
theorem B2325233 : Blo 1549472 2325233 := bstep (se 2 (by rfl) ⟨871962, by rfl⟩ : syracuseStep 2325233 = 1743925) B1743925
theorem B1743619 : Blo 1549472 1743619 := bstep (se 1 (by rfl) ⟨1307714, by rfl⟩ : syracuseStep 1743619 = 2615429) B2615429
theorem B2325251 : Blo 1549472 2325251 := bstep (se 1 (by rfl) ⟨1743938, by rfl⟩ : syracuseStep 2325251 = 3487877) B3487877
theorem B2325281 : Blo 1549472 2325281 := bstep (se 2 (by rfl) ⟨871980, by rfl⟩ : syracuseStep 2325281 = 1743961) B1743961
theorem B3488561 : Blo 1549472 3488561 := bstep (se 2 (by rfl) ⟨1308210, by rfl⟩ : syracuseStep 3488561 = 2616421) B2616421
theorem B2325299 : Blo 1549472 2325299 := bstep (se 1 (by rfl) ⟨1743974, by rfl⟩ : syracuseStep 2325299 = 3487949) B3487949
theorem B3488579 : Blo 1549472 3488579 := bstep (se 1 (by rfl) ⟨2616434, by rfl⟩ : syracuseStep 3488579 = 5232869) B5232869
theorem B3922769 : Blo 1549472 3922769 := bstep (se 2 (by rfl) ⟨1471038, by rfl⟩ : syracuseStep 3922769 = 2942077) B2942077
theorem B2325329 : Blo 1549472 2325329 := bstep (se 2 (by rfl) ⟨871998, by rfl⟩ : syracuseStep 2325329 = 1743997) B1743997
theorem B2325347 : Blo 1549472 2325347 := bstep (se 1 (by rfl) ⟨1744010, by rfl⟩ : syracuseStep 2325347 = 3488021) B3488021
theorem B5233517 : Blo 1549472 5233517 := bstep (se 3 (by rfl) ⟨981284, by rfl⟩ : syracuseStep 5233517 = 1962569) B1962569
theorem B8829809 : Blo 1549472 8829809 := bstep (se 2 (by rfl) ⟨3311178, by rfl⟩ : syracuseStep 8829809 = 6622357) B6622357
theorem B2325377 : Blo 1549472 2325377 := bstep (se 2 (by rfl) ⟨872016, by rfl⟩ : syracuseStep 2325377 = 1744033) B1744033
theorem B1743763 : Blo 1549472 1743763 := bstep (se 1 (by rfl) ⟨1307822, by rfl⟩ : syracuseStep 1743763 = 2615645) B2615645
theorem B2325395 : Blo 1549472 2325395 := bstep (se 1 (by rfl) ⟨1744046, by rfl⟩ : syracuseStep 2325395 = 3488093) B3488093
theorem B5233571 : Blo 1549472 5233571 := bstep (se 1 (by rfl) ⟨3925178, by rfl⟩ : syracuseStep 5233571 = 7850357) B7850357
theorem B2653091 : Blo 1549472 2653091 := bstep (se 1 (by rfl) ⟨1989818, by rfl⟩ : syracuseStep 2653091 = 3979637) B3979637
theorem B2325425 : Blo 1549472 2325425 := bstep (se 2 (by rfl) ⟨872034, by rfl⟩ : syracuseStep 2325425 = 1744069) B1744069
theorem B2325443 : Blo 1549472 2325443 := bstep (se 1 (by rfl) ⟨1744082, by rfl⟩ : syracuseStep 2325443 = 3488165) B3488165
theorem B2325473 : Blo 1549472 2325473 := bstep (se 2 (by rfl) ⟨872052, by rfl⟩ : syracuseStep 2325473 = 1744105) B1744105
theorem B5307373 : Blo 1549472 5307373 := bstep (se 3 (by rfl) ⟨995132, by rfl⟩ : syracuseStep 5307373 = 1990265) B1990265
theorem B2325491 : Blo 1549472 2325491 := bstep (se 1 (by rfl) ⟨1744118, by rfl⟩ : syracuseStep 2325491 = 3488237) B3488237
theorem B2325521 : Blo 1549472 2325521 := bstep (se 2 (by rfl) ⟨872070, by rfl⟩ : syracuseStep 2325521 = 1744141) B1744141
theorem B1743907 : Blo 1549472 1743907 := bstep (se 1 (by rfl) ⟨1307930, by rfl⟩ : syracuseStep 1743907 = 2615861) B2615861
theorem B2325539 : Blo 1549472 2325539 := bstep (se 1 (by rfl) ⟨1744154, by rfl⟩ : syracuseStep 2325539 = 3488309) B3488309
theorem B2325569 : Blo 1549472 2325569 := bstep (se 2 (by rfl) ⟨872088, by rfl⟩ : syracuseStep 2325569 = 1744177) B1744177
theorem B2653249 : Blo 1549472 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B3488849 : Blo 1549472 3488849 := bstep (se 2 (by rfl) ⟨1308318, by rfl⟩ : syracuseStep 3488849 = 2616637) B2616637
theorem B2325587 : Blo 1549472 2325587 := bstep (se 1 (by rfl) ⟨1744190, by rfl⟩ : syracuseStep 2325587 = 3488381) B3488381
theorem B3488867 : Blo 1549472 3488867 := bstep (se 1 (by rfl) ⟨2616650, by rfl⟩ : syracuseStep 3488867 = 5233301) B5233301
theorem B30194801 : Blo 1549472 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B2325617 : Blo 1549472 2325617 := bstep (se 2 (by rfl) ⟨872106, by rfl⟩ : syracuseStep 2325617 = 1744213) B1744213
theorem B3775619 : Blo 1549472 3775619 := bstep (se 1 (by rfl) ⟨2831714, by rfl⟩ : syracuseStep 3775619 = 5663429) B5663429
theorem B2325635 : Blo 1549472 2325635 := bstep (se 1 (by rfl) ⟨1744226, by rfl⟩ : syracuseStep 2325635 = 3488453) B3488453
theorem B2325665 : Blo 1549472 2325665 := bstep (se 2 (by rfl) ⟨872124, by rfl⟩ : syracuseStep 2325665 = 1744249) B1744249
theorem B2096291 : Blo 1549472 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B5233841 : Blo 1549472 5233841 := bstep (se 2 (by rfl) ⟨1962690, by rfl⟩ : syracuseStep 5233841 = 3925381) B3925381
theorem B1744051 : Blo 1549472 1744051 := bstep (se 1 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 1744051 = 2616077) B2616077
theorem B2325683 : Blo 1549472 2325683 := bstep (se 1 (by rfl) ⟨1744262, by rfl⟩ : syracuseStep 2325683 = 3488525) B3488525
theorem B2096323 : Blo 1549472 2096323 := bstep (se 1 (by rfl) ⟨1572242, by rfl⟩ : syracuseStep 2096323 = 3144485) B3144485
theorem B7847117 : Blo 1549472 7847117 := bstep (se 3 (by rfl) ⟨1471334, by rfl⟩ : syracuseStep 7847117 = 2942669) B2942669
theorem B2325713 : Blo 1549472 2325713 := bstep (se 2 (by rfl) ⟨872142, by rfl⟩ : syracuseStep 2325713 = 1744285) B1744285
theorem B4193489 : Blo 1549472 4193489 := bstep (se 2 (by rfl) ⟨1572558, by rfl⟩ : syracuseStep 4193489 = 3145117) B3145117
theorem B2325731 : Blo 1549472 2325731 := bstep (se 1 (by rfl) ⟨1744298, by rfl⟩ : syracuseStep 2325731 = 3488597) B3488597
theorem B14908643 : Blo 1549472 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B2325761 : Blo 1549472 2325761 := bstep (se 2 (by rfl) ⟨872160, by rfl⟩ : syracuseStep 2325761 = 1744321) B1744321
theorem B4414733 : Blo 1549472 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B2325779 : Blo 1549472 2325779 := bstep (se 1 (by rfl) ⟨1744334, by rfl⟩ : syracuseStep 2325779 = 3488669) B3488669
theorem B2325809 : Blo 1549472 2325809 := bstep (se 2 (by rfl) ⟨872178, by rfl⟩ : syracuseStep 2325809 = 1744357) B1744357
theorem B2653489 : Blo 1549472 2653489 := bstep (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) B1990117
theorem B1744195 : Blo 1549472 1744195 := bstep (se 1 (by rfl) ⟨1308146, by rfl⟩ : syracuseStep 1744195 = 2616293) B2616293
theorem B2325827 : Blo 1549472 2325827 := bstep (se 1 (by rfl) ⟨1744370, by rfl⟩ : syracuseStep 2325827 = 3488741) B3488741
theorem B2325857 : Blo 1549472 2325857 := bstep (se 2 (by rfl) ⟨872196, by rfl⟩ : syracuseStep 2325857 = 1744393) B1744393
theorem B3489137 : Blo 1549472 3489137 := bstep (se 2 (by rfl) ⟨1308426, by rfl⟩ : syracuseStep 3489137 = 2616853) B2616853
theorem B2325875 : Blo 1549472 2325875 := bstep (se 1 (by rfl) ⟨1744406, by rfl⟩ : syracuseStep 2325875 = 3488813) B3488813
theorem B3489155 : Blo 1549472 3489155 := bstep (se 1 (by rfl) ⟨2616866, by rfl⟩ : syracuseStep 3489155 = 5233733) B5233733
theorem B2325905 : Blo 1549472 2325905 := bstep (se 2 (by rfl) ⟨872214, by rfl⟩ : syracuseStep 2325905 = 1744429) B1744429
theorem B2325923 : Blo 1549472 2325923 := bstep (se 1 (by rfl) ⟨1744442, by rfl⟩ : syracuseStep 2325923 = 3488885) B3488885
theorem B4414915 : Blo 1549472 4414915 := bstep (se 1 (by rfl) ⟨3311186, by rfl⟩ : syracuseStep 4414915 = 6622373) B6622373
theorem B2325953 : Blo 1549472 2325953 := bstep (se 2 (by rfl) ⟨872232, by rfl⟩ : syracuseStep 2325953 = 1744465) B1744465
theorem B1744339 : Blo 1549472 1744339 := bstep (se 1 (by rfl) ⟨1308254, by rfl⟩ : syracuseStep 1744339 = 2616509) B2616509
theorem B2325971 : Blo 1549472 2325971 := bstep (se 1 (by rfl) ⟨1744478, by rfl⟩ : syracuseStep 2325971 = 3488957) B3488957
theorem B4414961 : Blo 1549472 4414961 := bstep (se 2 (by rfl) ⟨1655610, by rfl⟩ : syracuseStep 4414961 = 3311221) B3311221
theorem B2326001 : Blo 1549472 2326001 := bstep (se 2 (by rfl) ⟨872250, by rfl⟩ : syracuseStep 2326001 = 1744501) B1744501
theorem B2326019 : Blo 1549472 2326019 := bstep (se 1 (by rfl) ⟨1744514, by rfl⟩ : syracuseStep 2326019 = 3489029) B3489029
theorem B11771405 : Blo 1549472 11771405 := bstep (se 3 (by rfl) ⟨2207138, by rfl⟩ : syracuseStep 11771405 = 4414277) B4414277
theorem B2326049 : Blo 1549472 2326049 := bstep (se 2 (by rfl) ⟨872268, by rfl⟩ : syracuseStep 2326049 = 1744537) B1744537
theorem B2326067 : Blo 1549472 2326067 := bstep (se 1 (by rfl) ⟨1744550, by rfl⟩ : syracuseStep 2326067 = 3489101) B3489101
theorem B2326097 : Blo 1549472 2326097 := bstep (se 2 (by rfl) ⟨872286, by rfl⟩ : syracuseStep 2326097 = 1744573) B1744573
theorem B1744483 : Blo 1549472 1744483 := bstep (se 1 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 1744483 = 2616725) B2616725
theorem B2326115 : Blo 1549472 2326115 := bstep (se 1 (by rfl) ⟨1744586, by rfl⟩ : syracuseStep 2326115 = 3489173) B3489173
theorem B2326145 : Blo 1549472 2326145 := bstep (se 2 (by rfl) ⟨872304, by rfl⟩ : syracuseStep 2326145 = 1744609) B1744609
theorem B3489425 : Blo 1549472 3489425 := bstep (se 2 (by rfl) ⟨1308534, by rfl⟩ : syracuseStep 3489425 = 2617069) B2617069
theorem B2326163 : Blo 1549472 2326163 := bstep (se 1 (by rfl) ⟨1744622, by rfl⟩ : syracuseStep 2326163 = 3489245) B3489245
theorem B3489443 : Blo 1549472 3489443 := bstep (se 1 (by rfl) ⟨2617082, by rfl⟩ : syracuseStep 3489443 = 5234165) B5234165
theorem B2326193 : Blo 1549472 2326193 := bstep (se 2 (by rfl) ⟨872322, by rfl⟩ : syracuseStep 2326193 = 1744645) B1744645
theorem B2326211 : Blo 1549472 2326211 := bstep (se 1 (by rfl) ⟨1744658, by rfl⟩ : syracuseStep 2326211 = 3489317) B3489317
theorem B5234381 : Blo 1549472 5234381 := bstep (se 3 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 5234381 = 1962893) B1962893
theorem B2326241 : Blo 1549472 2326241 := bstep (se 2 (by rfl) ⟨872340, by rfl⟩ : syracuseStep 2326241 = 1744681) B1744681
theorem B9928433 : Blo 1549472 9928433 := bstep (se 2 (by rfl) ⟨3723162, by rfl⟩ : syracuseStep 9928433 = 7446325) B7446325
theorem B1744627 : Blo 1549472 1744627 := bstep (se 1 (by rfl) ⟨1308470, by rfl⟩ : syracuseStep 1744627 = 2616941) B2616941
theorem B2326259 : Blo 1549472 2326259 := bstep (se 1 (by rfl) ⟨1744694, by rfl⟩ : syracuseStep 2326259 = 3489389) B3489389
theorem B5234435 : Blo 1549472 5234435 := bstep (se 1 (by rfl) ⟨3925826, by rfl⟩ : syracuseStep 5234435 = 7851653) B7851653
theorem B2326289 : Blo 1549472 2326289 := bstep (se 2 (by rfl) ⟨872358, by rfl⟩ : syracuseStep 2326289 = 1744717) B1744717
theorem B5447459 : Blo 1549472 5447459 := bstep (se 1 (by rfl) ⟨4085594, by rfl⟩ : syracuseStep 5447459 = 8171189) B8171189
theorem B2326307 : Blo 1549472 2326307 := bstep (se 1 (by rfl) ⟨1744730, by rfl⟩ : syracuseStep 2326307 = 3489461) B3489461
theorem B4964141 : Blo 1549472 4964141 := bstep (se 3 (by rfl) ⟨930776, by rfl⟩ : syracuseStep 4964141 = 1861553) B1861553
theorem B3923761 : Blo 1549472 3923761 := bstep (se 2 (by rfl) ⟨1471410, by rfl⟩ : syracuseStep 3923761 = 2942821) B2942821
theorem B2326337 : Blo 1549472 2326337 := bstep (se 2 (by rfl) ⟨872376, by rfl⟩ : syracuseStep 2326337 = 1744753) B1744753
theorem B2326355 : Blo 1549472 2326355 := bstep (se 1 (by rfl) ⟨1744766, by rfl⟩ : syracuseStep 2326355 = 3489533) B3489533
theorem B2621281 : Blo 1549472 2621281 := bstep (se 2 (by rfl) ⟨982980, by rfl⟩ : syracuseStep 2621281 = 1965961) B1965961
theorem B3825521 : Blo 1549472 3825521 := bstep (se 2 (by rfl) ⟨1434570, by rfl⟩ : syracuseStep 3825521 = 2869141) B2869141
theorem B2326385 : Blo 1549472 2326385 := bstep (se 2 (by rfl) ⟨872394, by rfl⟩ : syracuseStep 2326385 = 1744789) B1744789
theorem B18866033 : Blo 1549472 18866033 := bstep (se 2 (by rfl) ⟨7074762, by rfl⟩ : syracuseStep 18866033 = 14149525) B14149525
theorem B1744771 : Blo 1549472 1744771 := bstep (se 1 (by rfl) ⟨1308578, by rfl⟩ : syracuseStep 1744771 = 2617157) B2617157
theorem B2326403 : Blo 1549472 2326403 := bstep (se 1 (by rfl) ⟨1744802, by rfl⟩ : syracuseStep 2326403 = 3489605) B3489605
theorem B2326433 : Blo 1549472 2326433 := bstep (se 2 (by rfl) ⟨872412, by rfl⟩ : syracuseStep 2326433 = 1744825) B1744825
theorem B5889955 : Blo 1549472 5889955 := bstep (se 1 (by rfl) ⟨4417466, by rfl⟩ : syracuseStep 5889955 = 8834933) B8834933
theorem B3489713 : Blo 1549472 3489713 := bstep (se 2 (by rfl) ⟨1308642, by rfl⟩ : syracuseStep 3489713 = 2617285) B2617285
theorem B2326451 : Blo 1549472 2326451 := bstep (se 1 (by rfl) ⟨1744838, by rfl⟩ : syracuseStep 2326451 = 3489677) B3489677
theorem B6807473 : Blo 1549472 6807473 := bstep (se 2 (by rfl) ⟨2552802, by rfl⟩ : syracuseStep 6807473 = 5105605) B5105605
theorem B3489731 : Blo 1549472 3489731 := bstep (se 1 (by rfl) ⟨2617298, by rfl⟩ : syracuseStep 3489731 = 5234597) B5234597
theorem B2326481 : Blo 1549472 2326481 := bstep (se 2 (by rfl) ⟨872430, by rfl⟩ : syracuseStep 2326481 = 1744861) B1744861
theorem B2326499 : Blo 1549472 2326499 := bstep (se 1 (by rfl) ⟨1744874, by rfl⟩ : syracuseStep 2326499 = 3489749) B3489749
theorem B3489803 : Blo 1549472 3489803 := bstep (se 1 (by rfl) ⟨2617352, by rfl⟩ : syracuseStep 3489803 = 5234705) B5234705
theorem B2326553 : Blo 1549472 2326553 := bstep (se 2 (by rfl) ⟨872457, by rfl⟩ : syracuseStep 2326553 = 1744915) B1744915
theorem B5586995 : Blo 1549472 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B1744951 : Blo 1549472 1744951 := bstep (se 1 (by rfl) ⟨1308713, by rfl⟩ : syracuseStep 1744951 = 2617427) B2617427
theorem B3489857 : Blo 1549472 3489857 := bstep (se 2 (by rfl) ⟨1308696, by rfl⟩ : syracuseStep 3489857 = 2617393) B2617393
theorem B6619229 : Blo 1549472 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B2326667 : Blo 1549472 2326667 := bstep (se 1 (by rfl) ⟨1745000, by rfl⟩ : syracuseStep 2326667 = 3490001) B3490001
theorem B2326679 : Blo 1549472 2326679 := bstep (se 1 (by rfl) ⟨1745009, by rfl⟩ : syracuseStep 2326679 = 3490019) B3490019
theorem B5234867 : Blo 1549472 5234867 := bstep (se 1 (by rfl) ⟨3926150, by rfl⟩ : syracuseStep 5234867 = 7852301) B7852301
theorem B1654987 : Blo 1549472 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B2326745 : Blo 1549472 2326745 := bstep (se 2 (by rfl) ⟨872529, by rfl⟩ : syracuseStep 2326745 = 1745059) B1745059
theorem B4473053 : Blo 1549472 4473053 := bstep (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) B1677395
theorem B1745131 : Blo 1549472 1745131 := bstep (se 1 (by rfl) ⟨1308848, by rfl⟩ : syracuseStep 1745131 = 2617697) B2617697
theorem B3924247 : Blo 1549472 3924247 := bstep (se 1 (by rfl) ⟨2943185, by rfl⟩ : syracuseStep 3924247 = 5886371) B5886371
theorem B3490073 : Blo 1549472 3490073 := bstep (se 2 (by rfl) ⟨1308777, by rfl⟩ : syracuseStep 3490073 = 2617555) B2617555
theorem B2326859 : Blo 1549472 2326859 := bstep (se 1 (by rfl) ⟨1745144, by rfl⟩ : syracuseStep 2326859 = 3490289) B3490289
theorem B3727691 : Blo 1549472 3727691 := bstep (se 1 (by rfl) ⟨2795768, by rfl⟩ : syracuseStep 3727691 = 5591537) B5591537
theorem B2326871 : Blo 1549472 2326871 := bstep (se 1 (by rfl) ⟨1745153, by rfl⟩ : syracuseStep 2326871 = 3490307) B3490307
theorem B1745239 : Blo 1549472 1745239 := bstep (se 1 (by rfl) ⟨1308929, by rfl⟩ : syracuseStep 1745239 = 2617859) B2617859
theorem B10068317 : Blo 1549472 10068317 := bstep (se 3 (by rfl) ⟨1887809, by rfl⟩ : syracuseStep 10068317 = 3775619) B3775619
theorem B3490163 : Blo 1549472 3490163 := bstep (se 1 (by rfl) ⟨2617622, by rfl⟩ : syracuseStep 3490163 = 5235245) B5235245
theorem B3490199 : Blo 1549472 3490199 := bstep (se 1 (by rfl) ⟨2617649, by rfl⟩ : syracuseStep 3490199 = 5235299) B5235299
theorem B2326937 : Blo 1549472 2326937 := bstep (se 2 (by rfl) ⟨872601, by rfl⟩ : syracuseStep 2326937 = 1745203) B1745203
theorem B5235137 : Blo 1549472 5235137 := bstep (se 2 (by rfl) ⟨1963176, by rfl⟩ : syracuseStep 5235137 = 3926353) B3926353
theorem B11772377 : Blo 1549472 11772377 := bstep (se 2 (by rfl) ⟨4414641, by rfl⟩ : syracuseStep 11772377 = 8829283) B8829283
theorem B2327051 : Blo 1549472 2327051 := bstep (se 1 (by rfl) ⟨1745288, by rfl⟩ : syracuseStep 2327051 = 3490577) B3490577
theorem B13238801 : Blo 1549472 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B2327063 : Blo 1549472 2327063 := bstep (se 1 (by rfl) ⟨1745297, by rfl⟩ : syracuseStep 2327063 = 3490595) B3490595
theorem B5587501 : Blo 1549472 5587501 := bstep (se 3 (by rfl) ⟨1047656, by rfl⟩ : syracuseStep 5587501 = 2095313) B2095313
theorem B11182637 : Blo 1549472 11182637 := bstep (se 3 (by rfl) ⟨2096744, by rfl⟩ : syracuseStep 11182637 = 4193489) B4193489
theorem B3490379 : Blo 1549472 3490379 := bstep (se 1 (by rfl) ⟨2617784, by rfl⟩ : syracuseStep 3490379 = 5235569) B5235569
theorem B2327129 : Blo 1549472 2327129 := bstep (se 2 (by rfl) ⟨872673, by rfl⟩ : syracuseStep 2327129 = 1745347) B1745347
theorem B3490433 : Blo 1549472 3490433 := bstep (se 2 (by rfl) ⟨1308912, by rfl⟩ : syracuseStep 3490433 = 2617825) B2617825
theorem B29803139 : Blo 1549472 29803139 := bstep (se 1 (by rfl) ⟨22352354, by rfl⟩ : syracuseStep 29803139 = 44704709) B44704709
theorem B2687627 : Blo 1549472 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B2941591 : Blo 1549472 2941591 := bstep (se 1 (by rfl) ⟨2206193, by rfl⟩ : syracuseStep 2941591 = 4412387) B4412387
theorem B3924683 : Blo 1549472 3924683 := bstep (se 1 (by rfl) ⟨2943512, by rfl⟩ : syracuseStep 3924683 = 5887025) B5887025
theorem B2482903 : Blo 1549472 2482903 := bstep (se 1 (by rfl) ⟨1862177, by rfl⟩ : syracuseStep 2482903 = 3724355) B3724355
theorem B2941697 : Blo 1549472 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B3490649 : Blo 1549472 3490649 := bstep (se 2 (by rfl) ⟨1308993, by rfl⟩ : syracuseStep 3490649 = 2617987) B2617987
theorem B2941849 : Blo 1549472 2941849 := bstep (se 2 (by rfl) ⟨1103193, by rfl⟩ : syracuseStep 2941849 = 2206387) B2206387
theorem B26502065 : Blo 1549472 26502065 := bstep (se 2 (by rfl) ⟨9938274, by rfl⟩ : syracuseStep 26502065 = 19876549) B19876549
theorem B3490739 : Blo 1549472 3490739 := bstep (se 1 (by rfl) ⟨2618054, by rfl⟩ : syracuseStep 3490739 = 5236109) B5236109
theorem B3490775 : Blo 1549472 3490775 := bstep (se 1 (by rfl) ⟨2618081, by rfl⟩ : syracuseStep 3490775 = 5236163) B5236163
theorem B5235677 : Blo 1549472 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B11781125 : Blo 1549472 11781125 := bstep (se 4 (by rfl) ⟨1104480, by rfl⟩ : syracuseStep 11781125 = 2208961) B2208961
theorem B8832017 : Blo 1549472 8832017 := bstep (se 2 (by rfl) ⟨3312006, by rfl⟩ : syracuseStep 8832017 = 6624013) B6624013
theorem B25150499 : Blo 1549472 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B3925057 : Blo 1549472 3925057 := bstep (se 2 (by rfl) ⟨1471896, by rfl⟩ : syracuseStep 3925057 = 2943793) B2943793
theorem B4416601 : Blo 1549472 4416601 := bstep (se 2 (by rfl) ⟨1656225, by rfl⟩ : syracuseStep 4416601 = 3312451) B3312451
theorem B19874909 : Blo 1549472 19874909 := bstep (se 3 (by rfl) ⟨3726545, by rfl⟩ : syracuseStep 19874909 = 7453091) B7453091
theorem B5588119 : Blo 1549472 5588119 := bstep (se 1 (by rfl) ⟨4191089, by rfl⟩ : syracuseStep 5588119 = 8382179) B8382179
theorem B1549483 : Blo 1549472 1549483 := bstep (se 1 (by rfl) ⟨1162112, by rfl⟩ : syracuseStep 1549483 = 2324225) B2324225
theorem B1549495 : Blo 1549472 1549495 := bstep (se 1 (by rfl) ⟨1162121, by rfl⟩ : syracuseStep 1549495 = 2324243) B2324243
theorem B1549515 : Blo 1549472 1549515 := bstep (se 1 (by rfl) ⟨1162136, by rfl⟩ : syracuseStep 1549515 = 2324273) B2324273
theorem B1549527 : Blo 1549472 1549527 := bstep (se 1 (by rfl) ⟨1162145, by rfl⟩ : syracuseStep 1549527 = 2324291) B2324291
theorem B1549547 : Blo 1549472 1549547 := bstep (se 1 (by rfl) ⟨1162160, by rfl⟩ : syracuseStep 1549547 = 2324321) B2324321
theorem B1549559 : Blo 1549472 1549559 := bstep (se 1 (by rfl) ⟨1162169, by rfl⟩ : syracuseStep 1549559 = 2324339) B2324339
theorem B1656055 : Blo 1549472 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1549579 : Blo 1549472 1549579 := bstep (se 1 (by rfl) ⟨1162184, by rfl⟩ : syracuseStep 1549579 = 2324369) B2324369
theorem B1549591 : Blo 1549472 1549591 := bstep (se 1 (by rfl) ⟨1162193, by rfl⟩ : syracuseStep 1549591 = 2324387) B2324387
theorem B1549611 : Blo 1549472 1549611 := bstep (se 1 (by rfl) ⟨1162208, by rfl⟩ : syracuseStep 1549611 = 2324417) B2324417
theorem B1549623 : Blo 1549472 1549623 := bstep (se 1 (by rfl) ⟨1162217, by rfl⟩ : syracuseStep 1549623 = 2324435) B2324435
theorem B3310913 : Blo 1549472 3310913 := bstep (se 2 (by rfl) ⟨1241592, by rfl⟩ : syracuseStep 3310913 = 2483185) B2483185
theorem B1549643 : Blo 1549472 1549643 := bstep (se 1 (by rfl) ⟨1162232, by rfl⟩ : syracuseStep 1549643 = 2324465) B2324465
theorem B1549655 : Blo 1549472 1549655 := bstep (se 1 (by rfl) ⟨1162241, by rfl⟩ : syracuseStep 1549655 = 2324483) B2324483
theorem B1549675 : Blo 1549472 1549675 := bstep (se 1 (by rfl) ⟨1162256, by rfl⟩ : syracuseStep 1549675 = 2324513) B2324513
theorem B1549687 : Blo 1549472 1549687 := bstep (se 1 (by rfl) ⟨1162265, by rfl⟩ : syracuseStep 1549687 = 2324531) B2324531
theorem B1549707 : Blo 1549472 1549707 := bstep (se 1 (by rfl) ⟨1162280, by rfl⟩ : syracuseStep 1549707 = 2324561) B2324561
theorem B1549719 : Blo 1549472 1549719 := bstep (se 1 (by rfl) ⟨1162289, by rfl⟩ : syracuseStep 1549719 = 2324579) B2324579
theorem B1549739 : Blo 1549472 1549739 := bstep (se 1 (by rfl) ⟨1162304, by rfl⟩ : syracuseStep 1549739 = 2324609) B2324609
theorem B8381875 : Blo 1549472 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B1549751 : Blo 1549472 1549751 := bstep (se 1 (by rfl) ⟨1162313, by rfl⟩ : syracuseStep 1549751 = 2324627) B2324627
theorem B1549771 : Blo 1549472 1549771 := bstep (se 1 (by rfl) ⟨1162328, by rfl⟩ : syracuseStep 1549771 = 2324657) B2324657
theorem B1549783 : Blo 1549472 1549783 := bstep (se 1 (by rfl) ⟨1162337, by rfl⟩ : syracuseStep 1549783 = 2324675) B2324675
theorem B8832473 : Blo 1549472 8832473 := bstep (se 2 (by rfl) ⟨3312177, by rfl⟩ : syracuseStep 8832473 = 6624355) B6624355
theorem B1549803 : Blo 1549472 1549803 := bstep (se 1 (by rfl) ⟨1162352, by rfl⟩ : syracuseStep 1549803 = 2324705) B2324705
theorem B1549815 : Blo 1549472 1549815 := bstep (se 1 (by rfl) ⟨1162361, by rfl⟩ : syracuseStep 1549815 = 2324723) B2324723
theorem B1549835 : Blo 1549472 1549835 := bstep (se 1 (by rfl) ⟨1162376, by rfl⟩ : syracuseStep 1549835 = 2324753) B2324753
theorem B32261645 : Blo 1549472 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B1549847 : Blo 1549472 1549847 := bstep (se 1 (by rfl) ⟨1162385, by rfl⟩ : syracuseStep 1549847 = 2324771) B2324771
theorem B1549867 : Blo 1549472 1549867 := bstep (se 1 (by rfl) ⟨1162400, by rfl⟩ : syracuseStep 1549867 = 2324801) B2324801
theorem B6620717 : Blo 1549472 6620717 := bstep (se 3 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 6620717 = 2482769) B2482769
theorem B1549879 : Blo 1549472 1549879 := bstep (se 1 (by rfl) ⟨1162409, by rfl⟩ : syracuseStep 1549879 = 2324819) B2324819
theorem B1549899 : Blo 1549472 1549899 := bstep (se 1 (by rfl) ⟨1162424, by rfl⟩ : syracuseStep 1549899 = 2324849) B2324849
theorem B7849547 : Blo 1549472 7849547 := bstep (se 1 (by rfl) ⟨5887160, by rfl⟩ : syracuseStep 7849547 = 11774321) B11774321
theorem B1549911 : Blo 1549472 1549911 := bstep (se 1 (by rfl) ⟨1162433, by rfl⟩ : syracuseStep 1549911 = 2324867) B2324867
theorem B28345949 : Blo 1549472 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B1549931 : Blo 1549472 1549931 := bstep (se 1 (by rfl) ⟨1162448, by rfl⟩ : syracuseStep 1549931 = 2324897) B2324897
theorem B1549943 : Blo 1549472 1549943 := bstep (se 1 (by rfl) ⟨1162457, by rfl⟩ : syracuseStep 1549943 = 2324915) B2324915
theorem B120866435 : Blo 1549472 120866435 := bstep (se 1 (by rfl) ⟨90649826, by rfl⟩ : syracuseStep 120866435 = 181299653) B181299653
theorem B1549963 : Blo 1549472 1549963 := bstep (se 1 (by rfl) ⟨1162472, by rfl⟩ : syracuseStep 1549963 = 2324945) B2324945
theorem B1549975 : Blo 1549472 1549975 := bstep (se 1 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 1549975 = 2324963) B2324963
theorem B3311255 : Blo 1549472 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B3925655 : Blo 1549472 3925655 := bstep (se 1 (by rfl) ⟨2944241, by rfl⟩ : syracuseStep 3925655 = 5888483) B5888483
theorem B1549995 : Blo 1549472 1549995 := bstep (se 1 (by rfl) ⟨1162496, by rfl⟩ : syracuseStep 1549995 = 2324993) B2324993
theorem B1550007 : Blo 1549472 1550007 := bstep (se 1 (by rfl) ⟨1162505, by rfl⟩ : syracuseStep 1550007 = 2325011) B2325011
theorem B4417217 : Blo 1549472 4417217 := bstep (se 2 (by rfl) ⟨1656456, by rfl⟩ : syracuseStep 4417217 = 3312913) B3312913
theorem B1550027 : Blo 1549472 1550027 := bstep (se 1 (by rfl) ⟨1162520, by rfl⟩ : syracuseStep 1550027 = 2325041) B2325041
theorem B1550039 : Blo 1549472 1550039 := bstep (se 1 (by rfl) ⟨1162529, by rfl⟩ : syracuseStep 1550039 = 2325059) B2325059
theorem B1550059 : Blo 1549472 1550059 := bstep (se 1 (by rfl) ⟨1162544, by rfl⟩ : syracuseStep 1550059 = 2325089) B2325089
theorem B1550071 : Blo 1549472 1550071 := bstep (se 1 (by rfl) ⟨1162553, by rfl⟩ : syracuseStep 1550071 = 2325107) B2325107
theorem B2615051 : Blo 1549472 2615051 := bstep (se 1 (by rfl) ⟨1961288, by rfl⟩ : syracuseStep 2615051 = 3922577) B3922577
theorem B1550091 : Blo 1549472 1550091 := bstep (se 1 (by rfl) ⟨1162568, by rfl⟩ : syracuseStep 1550091 = 2325137) B2325137
theorem B1550103 : Blo 1549472 1550103 := bstep (se 1 (by rfl) ⟨1162577, by rfl⟩ : syracuseStep 1550103 = 2325155) B2325155
theorem B1550123 : Blo 1549472 1550123 := bstep (se 1 (by rfl) ⟨1162592, by rfl⟩ : syracuseStep 1550123 = 2325185) B2325185
theorem B1550135 : Blo 1549472 1550135 := bstep (se 1 (by rfl) ⟨1162601, by rfl⟩ : syracuseStep 1550135 = 2325203) B2325203
theorem B1550155 : Blo 1549472 1550155 := bstep (se 1 (by rfl) ⟨1162616, by rfl⟩ : syracuseStep 1550155 = 2325233) B2325233
theorem B1550167 : Blo 1549472 1550167 := bstep (se 1 (by rfl) ⟨1162625, by rfl⟩ : syracuseStep 1550167 = 2325251) B2325251
theorem B1550187 : Blo 1549472 1550187 := bstep (se 1 (by rfl) ⟨1162640, by rfl⟩ : syracuseStep 1550187 = 2325281) B2325281
theorem B1550199 : Blo 1549472 1550199 := bstep (se 1 (by rfl) ⟨1162649, by rfl⟩ : syracuseStep 1550199 = 2325299) B2325299
theorem B2615179 : Blo 1549472 2615179 := bstep (se 1 (by rfl) ⟨1961384, by rfl⟩ : syracuseStep 2615179 = 3922769) B3922769
theorem B1550219 : Blo 1549472 1550219 := bstep (se 1 (by rfl) ⟨1162664, by rfl⟩ : syracuseStep 1550219 = 2325329) B2325329
theorem B1550231 : Blo 1549472 1550231 := bstep (se 1 (by rfl) ⟨1162673, by rfl⟩ : syracuseStep 1550231 = 2325347) B2325347
theorem B2484121 : Blo 1549472 2484121 := bstep (se 2 (by rfl) ⟨931545, by rfl⟩ : syracuseStep 2484121 = 1863091) B1863091
theorem B1550251 : Blo 1549472 1550251 := bstep (se 1 (by rfl) ⟨1162688, by rfl⟩ : syracuseStep 1550251 = 2325377) B2325377
theorem B2983859 : Blo 1549472 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B1550263 : Blo 1549472 1550263 := bstep (se 1 (by rfl) ⟨1162697, by rfl⟩ : syracuseStep 1550263 = 2325395) B2325395
theorem B1550283 : Blo 1549472 1550283 := bstep (se 1 (by rfl) ⟨1162712, by rfl⟩ : syracuseStep 1550283 = 2325425) B2325425
theorem B3311563 : Blo 1549472 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B1550295 : Blo 1549472 1550295 := bstep (se 1 (by rfl) ⟨1162721, by rfl⟩ : syracuseStep 1550295 = 2325443) B2325443
theorem B1550315 : Blo 1549472 1550315 := bstep (se 1 (by rfl) ⟨1162736, by rfl⟩ : syracuseStep 1550315 = 2325473) B2325473
theorem B1550327 : Blo 1549472 1550327 := bstep (se 1 (by rfl) ⟨1162745, by rfl⟩ : syracuseStep 1550327 = 2325491) B2325491
theorem B1550347 : Blo 1549472 1550347 := bstep (se 1 (by rfl) ⟨1162760, by rfl⟩ : syracuseStep 1550347 = 2325521) B2325521
theorem B1550359 : Blo 1549472 1550359 := bstep (se 1 (by rfl) ⟨1162769, by rfl⟩ : syracuseStep 1550359 = 2325539) B2325539
theorem B2615321 : Blo 1549472 2615321 := bstep (se 2 (by rfl) ⟨980745, by rfl⟩ : syracuseStep 2615321 = 1961491) B1961491
theorem B1550379 : Blo 1549472 1550379 := bstep (se 1 (by rfl) ⟨1162784, by rfl⟩ : syracuseStep 1550379 = 2325569) B2325569
theorem B1550391 : Blo 1549472 1550391 := bstep (se 1 (by rfl) ⟨1162793, by rfl⟩ : syracuseStep 1550391 = 2325587) B2325587
theorem B20129867 : Blo 1549472 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B1550411 : Blo 1549472 1550411 := bstep (se 1 (by rfl) ⟨1162808, by rfl⟩ : syracuseStep 1550411 = 2325617) B2325617
theorem B1550423 : Blo 1549472 1550423 := bstep (se 1 (by rfl) ⟨1162817, by rfl⟩ : syracuseStep 1550423 = 2325635) B2325635
theorem B1550443 : Blo 1549472 1550443 := bstep (se 1 (by rfl) ⟨1162832, by rfl⟩ : syracuseStep 1550443 = 2325665) B2325665
theorem B1550455 : Blo 1549472 1550455 := bstep (se 1 (by rfl) ⟨1162841, by rfl⟩ : syracuseStep 1550455 = 2325683) B2325683
theorem B1550475 : Blo 1549472 1550475 := bstep (se 1 (by rfl) ⟨1162856, by rfl⟩ : syracuseStep 1550475 = 2325713) B2325713
theorem B1550487 : Blo 1549472 1550487 := bstep (se 1 (by rfl) ⟨1162865, by rfl⟩ : syracuseStep 1550487 = 2325731) B2325731
theorem B9939095 : Blo 1549472 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B2615449 : Blo 1549472 2615449 := bstep (se 2 (by rfl) ⟨980793, by rfl⟩ : syracuseStep 2615449 = 1961587) B1961587
theorem B1550507 : Blo 1549472 1550507 := bstep (se 1 (by rfl) ⟨1162880, by rfl⟩ : syracuseStep 1550507 = 2325761) B2325761
theorem B2943155 : Blo 1549472 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B1550519 : Blo 1549472 1550519 := bstep (se 1 (by rfl) ⟨1162889, by rfl⟩ : syracuseStep 1550519 = 2325779) B2325779
theorem B1550539 : Blo 1549472 1550539 := bstep (se 1 (by rfl) ⟨1162904, by rfl⟩ : syracuseStep 1550539 = 2325809) B2325809
theorem B1550551 : Blo 1549472 1550551 := bstep (se 1 (by rfl) ⟨1162913, by rfl⟩ : syracuseStep 1550551 = 2325827) B2325827
theorem B1550571 : Blo 1549472 1550571 := bstep (se 1 (by rfl) ⟨1162928, by rfl⟩ : syracuseStep 1550571 = 2325857) B2325857
theorem B1550583 : Blo 1549472 1550583 := bstep (se 1 (by rfl) ⟨1162937, by rfl⟩ : syracuseStep 1550583 = 2325875) B2325875
theorem B1550603 : Blo 1549472 1550603 := bstep (se 1 (by rfl) ⟨1162952, by rfl⟩ : syracuseStep 1550603 = 2325905) B2325905
theorem B1550615 : Blo 1549472 1550615 := bstep (se 1 (by rfl) ⟨1162961, by rfl⟩ : syracuseStep 1550615 = 2325923) B2325923
theorem B1550635 : Blo 1549472 1550635 := bstep (se 1 (by rfl) ⟨1162976, by rfl⟩ : syracuseStep 1550635 = 2325953) B2325953
theorem B1550647 : Blo 1549472 1550647 := bstep (se 1 (by rfl) ⟨1162985, by rfl⟩ : syracuseStep 1550647 = 2325971) B2325971
theorem B2943307 : Blo 1549472 2943307 := bstep (se 1 (by rfl) ⟨2207480, by rfl⟩ : syracuseStep 2943307 = 4414961) B4414961
theorem B1550667 : Blo 1549472 1550667 := bstep (se 1 (by rfl) ⟨1163000, by rfl⟩ : syracuseStep 1550667 = 2326001) B2326001
theorem B1550679 : Blo 1549472 1550679 := bstep (se 1 (by rfl) ⟨1163009, by rfl⟩ : syracuseStep 1550679 = 2326019) B2326019
theorem B1550699 : Blo 1549472 1550699 := bstep (se 1 (by rfl) ⟨1163024, by rfl⟩ : syracuseStep 1550699 = 2326049) B2326049
theorem B1550711 : Blo 1549472 1550711 := bstep (se 1 (by rfl) ⟨1163033, by rfl⟩ : syracuseStep 1550711 = 2326067) B2326067
theorem B1550731 : Blo 1549472 1550731 := bstep (se 1 (by rfl) ⟨1163048, by rfl⟩ : syracuseStep 1550731 = 2326097) B2326097
theorem B1550743 : Blo 1549472 1550743 := bstep (se 1 (by rfl) ⟨1163057, by rfl⟩ : syracuseStep 1550743 = 2326115) B2326115
theorem B1550763 : Blo 1549472 1550763 := bstep (se 1 (by rfl) ⟨1163072, by rfl⟩ : syracuseStep 1550763 = 2326145) B2326145
theorem B1550775 : Blo 1549472 1550775 := bstep (se 1 (by rfl) ⟨1163081, by rfl⟩ : syracuseStep 1550775 = 2326163) B2326163
theorem B3926465 : Blo 1549472 3926465 := bstep (se 2 (by rfl) ⟨1472424, by rfl⟩ : syracuseStep 3926465 = 2944849) B2944849
theorem B1550795 : Blo 1549472 1550795 := bstep (se 1 (by rfl) ⟨1163096, by rfl⟩ : syracuseStep 1550795 = 2326193) B2326193
theorem B1550807 : Blo 1549472 1550807 := bstep (se 1 (by rfl) ⟨1163105, by rfl⟩ : syracuseStep 1550807 = 2326211) B2326211
theorem B1550827 : Blo 1549472 1550827 := bstep (se 1 (by rfl) ⟨1163120, by rfl⟩ : syracuseStep 1550827 = 2326241) B2326241
theorem B1550839 : Blo 1549472 1550839 := bstep (se 1 (by rfl) ⟨1163129, by rfl⟩ : syracuseStep 1550839 = 2326259) B2326259
theorem B1550859 : Blo 1549472 1550859 := bstep (se 1 (by rfl) ⟨1163144, by rfl⟩ : syracuseStep 1550859 = 2326289) B2326289
theorem B3631639 : Blo 1549472 3631639 := bstep (se 1 (by rfl) ⟨2723729, by rfl⟩ : syracuseStep 3631639 = 5447459) B5447459
theorem B1550871 : Blo 1549472 1550871 := bstep (se 1 (by rfl) ⟨1163153, by rfl⟩ : syracuseStep 1550871 = 2326307) B2326307
theorem B1550891 : Blo 1549472 1550891 := bstep (se 1 (by rfl) ⟨1163168, by rfl⟩ : syracuseStep 1550891 = 2326337) B2326337
theorem B1550903 : Blo 1549472 1550903 := bstep (se 1 (by rfl) ⟨1163177, by rfl⟩ : syracuseStep 1550903 = 2326355) B2326355
theorem B2550347 : Blo 1549472 2550347 := bstep (se 1 (by rfl) ⟨1912760, by rfl⟩ : syracuseStep 2550347 = 3825521) B3825521
theorem B1550923 : Blo 1549472 1550923 := bstep (se 1 (by rfl) ⟨1163192, by rfl⟩ : syracuseStep 1550923 = 2326385) B2326385
theorem B12577355 : Blo 1549472 12577355 := bstep (se 1 (by rfl) ⟨9433016, by rfl⟩ : syracuseStep 12577355 = 18866033) B18866033
theorem B1550935 : Blo 1549472 1550935 := bstep (se 1 (by rfl) ⟨1163201, by rfl⟩ : syracuseStep 1550935 = 2326403) B2326403
theorem B1550955 : Blo 1549472 1550955 := bstep (se 1 (by rfl) ⟨1163216, by rfl⟩ : syracuseStep 1550955 = 2326433) B2326433
theorem B1550967 : Blo 1549472 1550967 := bstep (se 1 (by rfl) ⟨1163225, by rfl⟩ : syracuseStep 1550967 = 2326451) B2326451
theorem B1550987 : Blo 1549472 1550987 := bstep (se 1 (by rfl) ⟨1163240, by rfl⟩ : syracuseStep 1550987 = 2326481) B2326481
theorem B1550999 : Blo 1549472 1550999 := bstep (se 1 (by rfl) ⟨1163249, by rfl⟩ : syracuseStep 1550999 = 2326499) B2326499
theorem B2943641 : Blo 1549472 2943641 := bstep (se 2 (by rfl) ⟨1103865, by rfl⟩ : syracuseStep 2943641 = 2207731) B2207731
theorem B1551019 : Blo 1549472 1551019 := bstep (se 1 (by rfl) ⟨1163264, by rfl⟩ : syracuseStep 1551019 = 2326529) B2326529
theorem B5884595 : Blo 1549472 5884595 := bstep (se 1 (by rfl) ⟨4413446, by rfl⟩ : syracuseStep 5884595 = 8826893) B8826893
theorem B1551031 : Blo 1549472 1551031 := bstep (se 1 (by rfl) ⟨1163273, by rfl⟩ : syracuseStep 1551031 = 2326547) B2326547
theorem B5884609 : Blo 1549472 5884609 := bstep (se 2 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 5884609 = 4413457) B4413457
theorem B1551051 : Blo 1549472 1551051 := bstep (se 1 (by rfl) ⟨1163288, by rfl⟩ : syracuseStep 1551051 = 2326577) B2326577
theorem B2616023 : Blo 1549472 2616023 := bstep (se 1 (by rfl) ⟨1962017, by rfl⟩ : syracuseStep 2616023 = 3924035) B3924035
theorem B1551063 : Blo 1549472 1551063 := bstep (se 1 (by rfl) ⟨1163297, by rfl⟩ : syracuseStep 1551063 = 2326595) B2326595
theorem B1551083 : Blo 1549472 1551083 := bstep (se 1 (by rfl) ⟨1163312, by rfl⟩ : syracuseStep 1551083 = 2326625) B2326625
theorem B1551095 : Blo 1549472 1551095 := bstep (se 1 (by rfl) ⟨1163321, by rfl⟩ : syracuseStep 1551095 = 2326643) B2326643
theorem B1551115 : Blo 1549472 1551115 := bstep (se 1 (by rfl) ⟨1163336, by rfl⟩ : syracuseStep 1551115 = 2326673) B2326673
theorem B11766545 : Blo 1549472 11766545 := bstep (se 2 (by rfl) ⟨4412454, by rfl⟩ : syracuseStep 11766545 = 8824909) B8824909
theorem B1551127 : Blo 1549472 1551127 := bstep (se 1 (by rfl) ⟨1163345, by rfl⟩ : syracuseStep 1551127 = 2326691) B2326691
theorem B3312409 : Blo 1549472 3312409 := bstep (se 2 (by rfl) ⟨1242153, by rfl⟩ : syracuseStep 3312409 = 2484307) B2484307
theorem B1551147 : Blo 1549472 1551147 := bstep (se 1 (by rfl) ⟨1163360, by rfl⟩ : syracuseStep 1551147 = 2326721) B2326721
theorem B1551159 : Blo 1549472 1551159 := bstep (se 1 (by rfl) ⟨1163369, by rfl⟩ : syracuseStep 1551159 = 2326739) B2326739
theorem B1551179 : Blo 1549472 1551179 := bstep (se 1 (by rfl) ⟨1163384, by rfl⟩ : syracuseStep 1551179 = 2326769) B2326769
theorem B2616151 : Blo 1549472 2616151 := bstep (se 1 (by rfl) ⟨1962113, by rfl⟩ : syracuseStep 2616151 = 3924227) B3924227
theorem B1551191 : Blo 1549472 1551191 := bstep (se 1 (by rfl) ⟨1163393, by rfl⟩ : syracuseStep 1551191 = 2326787) B2326787
theorem B1551211 : Blo 1549472 1551211 := bstep (se 1 (by rfl) ⟨1163408, by rfl⟩ : syracuseStep 1551211 = 2326817) B2326817
theorem B1551223 : Blo 1549472 1551223 := bstep (se 1 (by rfl) ⟨1163417, by rfl⟩ : syracuseStep 1551223 = 2326835) B2326835
theorem B1551243 : Blo 1549472 1551243 := bstep (se 1 (by rfl) ⟨1163432, by rfl⟩ : syracuseStep 1551243 = 2326865) B2326865
theorem B2206615 : Blo 1549472 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B1551255 : Blo 1549472 1551255 := bstep (se 1 (by rfl) ⟨1163441, by rfl⟩ : syracuseStep 1551255 = 2326883) B2326883
theorem B1551275 : Blo 1549472 1551275 := bstep (se 1 (by rfl) ⟨1163456, by rfl⟩ : syracuseStep 1551275 = 2326913) B2326913
theorem B1551287 : Blo 1549472 1551287 := bstep (se 1 (by rfl) ⟨1163465, by rfl⟩ : syracuseStep 1551287 = 2326931) B2326931
theorem B1551307 : Blo 1549472 1551307 := bstep (se 1 (by rfl) ⟨1163480, by rfl⟩ : syracuseStep 1551307 = 2326961) B2326961
theorem B1551319 : Blo 1549472 1551319 := bstep (se 1 (by rfl) ⟨1163489, by rfl⟩ : syracuseStep 1551319 = 2326979) B2326979
theorem B3927001 : Blo 1549472 3927001 := bstep (se 2 (by rfl) ⟨1472625, by rfl⟩ : syracuseStep 3927001 = 2945251) B2945251
theorem B1551339 : Blo 1549472 1551339 := bstep (se 1 (by rfl) ⟨1163504, by rfl⟩ : syracuseStep 1551339 = 2327009) B2327009
theorem B1551351 : Blo 1549472 1551351 := bstep (se 1 (by rfl) ⟨1163513, by rfl⟩ : syracuseStep 1551351 = 2327027) B2327027
theorem B1551371 : Blo 1549472 1551371 := bstep (se 1 (by rfl) ⟨1163528, by rfl⟩ : syracuseStep 1551371 = 2327057) B2327057
theorem B16763921 : Blo 1549472 16763921 := bstep (se 2 (by rfl) ⟨6286470, by rfl⟩ : syracuseStep 16763921 = 12572941) B12572941
theorem B14904337 : Blo 1549472 14904337 := bstep (se 2 (by rfl) ⟨5589126, by rfl⟩ : syracuseStep 14904337 = 11178253) B11178253
theorem B1551383 : Blo 1549472 1551383 := bstep (se 1 (by rfl) ⟨1163537, by rfl⟩ : syracuseStep 1551383 = 2327075) B2327075
theorem B1551403 : Blo 1549472 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B1551415 : Blo 1549472 1551415 := bstep (se 1 (by rfl) ⟨1163561, by rfl⟩ : syracuseStep 1551415 = 2327123) B2327123
theorem B1551435 : Blo 1549472 1551435 := bstep (se 1 (by rfl) ⟨1163576, by rfl⟩ : syracuseStep 1551435 = 2327153) B2327153
theorem B1551447 : Blo 1549472 1551447 := bstep (se 1 (by rfl) ⟨1163585, by rfl⟩ : syracuseStep 1551447 = 2327171) B2327171
theorem B5590109 : Blo 1549472 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B1551467 : Blo 1549472 1551467 := bstep (se 1 (by rfl) ⟨1163600, by rfl⟩ : syracuseStep 1551467 = 2327201) B2327201
theorem B1961111 : Blo 1549472 1961111 := bstep (se 1 (by rfl) ⟨1470833, by rfl⟩ : syracuseStep 1961111 = 2941667) B2941667
theorem B2944279 : Blo 1549472 2944279 := bstep (se 1 (by rfl) ⟨2208209, by rfl⟩ : syracuseStep 2944279 = 4416419) B4416419
theorem B7851329 : Blo 1549472 7851329 := bstep (se 2 (by rfl) ⟨2944248, by rfl⟩ : syracuseStep 7851329 = 5888497) B5888497
theorem B5229899 : Blo 1549472 5229899 := bstep (se 1 (by rfl) ⟨3922424, by rfl⟩ : syracuseStep 5229899 = 7844849) B7844849
theorem B4967831 : Blo 1549472 4967831 := bstep (se 1 (by rfl) ⟨3725873, by rfl⟩ : syracuseStep 4967831 = 7451747) B7451747
theorem B2207179 : Blo 1549472 2207179 := bstep (se 1 (by rfl) ⟨1655384, by rfl⟩ : syracuseStep 2207179 = 3310769) B3310769
theorem B2616779 : Blo 1549472 2616779 := bstep (se 1 (by rfl) ⟨1962584, by rfl⟩ : syracuseStep 2616779 = 3925169) B3925169
theorem B6622681 : Blo 1549472 6622681 := bstep (se 2 (by rfl) ⟨2483505, by rfl⟩ : syracuseStep 6622681 = 4967011) B4967011
theorem B2616907 : Blo 1549472 2616907 := bstep (se 1 (by rfl) ⟨1962680, by rfl⟩ : syracuseStep 2616907 = 3925361) B3925361
theorem B5230169 : Blo 1549472 5230169 := bstep (se 2 (by rfl) ⟨1961313, by rfl⟩ : syracuseStep 5230169 = 3922627) B3922627
theorem B7548547 : Blo 1549472 7548547 := bstep (se 1 (by rfl) ⟨5661410, by rfl⟩ : syracuseStep 7548547 = 11322821) B11322821
theorem B8949379 : Blo 1549472 8949379 := bstep (se 1 (by rfl) ⟨6712034, by rfl⟩ : syracuseStep 8949379 = 13424069) B13424069
theorem B1863307 : Blo 1549472 1863307 := bstep (se 1 (by rfl) ⟨1397480, by rfl⟩ : syracuseStep 1863307 = 2794961) B2794961
theorem B3985075 : Blo 1549472 3985075 := bstep (se 1 (by rfl) ⟨2988806, by rfl⟩ : syracuseStep 3985075 = 5977613) B5977613
theorem B183815885 : Blo 1549472 183815885 := bstep (se 3 (by rfl) ⟨34465478, by rfl⟩ : syracuseStep 183815885 = 68930957) B68930957
theorem B2617049 : Blo 1549472 2617049 := bstep (se 2 (by rfl) ⟨981393, by rfl⟩ : syracuseStep 2617049 = 1962787) B1962787
theorem B8826641 : Blo 1549472 8826641 := bstep (se 2 (by rfl) ⟨3309990, by rfl⟩ : syracuseStep 8826641 = 6619981) B6619981
theorem B11775779 : Blo 1549472 11775779 := bstep (se 1 (by rfl) ⟨8831834, by rfl⟩ : syracuseStep 11775779 = 17663669) B17663669
theorem B1961815 : Blo 1549472 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B2617177 : Blo 1549472 2617177 := bstep (se 2 (by rfl) ⟨981441, by rfl⟩ : syracuseStep 2617177 = 1962883) B1962883
theorem B2945099 : Blo 1549472 2945099 := bstep (se 1 (by rfl) ⟨2208824, by rfl⟩ : syracuseStep 2945099 = 4417649) B4417649
theorem B2945153 : Blo 1549472 2945153 := bstep (se 2 (by rfl) ⟨1104432, by rfl⟩ : syracuseStep 2945153 = 2208865) B2208865
theorem B14151941 : Blo 1549472 14151941 := bstep (se 4 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 14151941 = 2653489) B2653489
theorem B5230871 : Blo 1549472 5230871 := bstep (se 1 (by rfl) ⟨3923153, by rfl⟩ : syracuseStep 5230871 = 7846307) B7846307
theorem B6623639 : Blo 1549472 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B2617751 : Blo 1549472 2617751 := bstep (se 1 (by rfl) ⟨1963313, by rfl⟩ : syracuseStep 2617751 = 3926627) B3926627
theorem B2617879 : Blo 1549472 2617879 := bstep (se 1 (by rfl) ⟨1963409, by rfl⟩ : syracuseStep 2617879 = 3926819) B3926819
theorem B5886539 : Blo 1549472 5886539 := bstep (se 1 (by rfl) ⟨4414904, by rfl⟩ : syracuseStep 5886539 = 8829809) B8829809
theorem B5886553 : Blo 1549472 5886553 := bstep (se 2 (by rfl) ⟨2207457, by rfl⟩ : syracuseStep 5886553 = 4414915) B4414915
theorem B3486347 : Blo 1549472 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B3486401 : Blo 1549472 3486401 := bstep (se 2 (by rfl) ⟨1307400, by rfl⟩ : syracuseStep 3486401 = 2614801) B2614801
theorem B3142361 : Blo 1549472 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B5231411 : Blo 1549472 5231411 := bstep (se 1 (by rfl) ⟨3923558, by rfl⟩ : syracuseStep 5231411 = 7847117) B7847117
theorem B7549789 : Blo 1549472 7549789 := bstep (se 3 (by rfl) ⟨1415585, by rfl⟩ : syracuseStep 7549789 = 2831171) B2831171
theorem B3486617 : Blo 1549472 3486617 := bstep (se 2 (by rfl) ⟨1307481, by rfl⟩ : syracuseStep 3486617 = 2614963) B2614963
theorem B2208665 : Blo 1549472 2208665 := bstep (se 2 (by rfl) ⟨828249, by rfl⟩ : syracuseStep 2208665 = 1656499) B1656499
theorem B25138097 : Blo 1549472 25138097 := bstep (se 2 (by rfl) ⟨9426786, by rfl⟩ : syracuseStep 25138097 = 18853573) B18853573
theorem B3486707 : Blo 1549472 3486707 := bstep (se 1 (by rfl) ⟨2615030, by rfl⟩ : syracuseStep 3486707 = 5230061) B5230061
theorem B57373717 : Blo 1549472 57373717 := bstep (se 6 (by rfl) ⟨1344696, by rfl⟩ : syracuseStep 57373717 = 2689393) B2689393
theorem B3486743 : Blo 1549472 3486743 := bstep (se 1 (by rfl) ⟨2615057, by rfl⟩ : syracuseStep 3486743 = 5230115) B5230115
theorem B4191283 : Blo 1549472 4191283 := bstep (se 1 (by rfl) ⟨3143462, by rfl⟩ : syracuseStep 4191283 = 6286925) B6286925
theorem B5231681 : Blo 1549472 5231681 := bstep (se 2 (by rfl) ⟨1961880, by rfl⟩ : syracuseStep 5231681 = 3923761) B3923761
theorem B3495041 : Blo 1549472 3495041 := bstep (se 2 (by rfl) ⟨1310640, by rfl⟩ : syracuseStep 3495041 = 2621281) B2621281
theorem B3486923 : Blo 1549472 3486923 := bstep (se 1 (by rfl) ⟨2615192, by rfl⟩ : syracuseStep 3486923 = 5230385) B5230385
theorem B7853273 : Blo 1549472 7853273 := bstep (se 2 (by rfl) ⟨2944977, by rfl⟩ : syracuseStep 7853273 = 5889955) B5889955
theorem B3486977 : Blo 1549472 3486977 := bstep (se 2 (by rfl) ⟨1307616, by rfl⟩ : syracuseStep 3486977 = 2615233) B2615233
theorem B11334977 : Blo 1549472 11334977 := bstep (se 2 (by rfl) ⟨4250616, by rfl⟩ : syracuseStep 11334977 = 8501233) B8501233
theorem B12744029 : Blo 1549472 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B13604273 : Blo 1549472 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B4969907 : Blo 1549472 4969907 := bstep (se 1 (by rfl) ⟨3727430, by rfl⟩ : syracuseStep 4969907 = 7454861) B7454861
theorem B3487193 : Blo 1549472 3487193 := bstep (se 2 (by rfl) ⟨1307697, by rfl⟩ : syracuseStep 3487193 = 2615395) B2615395
theorem B11171333 : Blo 1549472 11171333 := bstep (se 4 (by rfl) ⟨1047312, by rfl⟩ : syracuseStep 11171333 = 2094625) B2094625
theorem B1963531 : Blo 1549472 1963531 := bstep (se 1 (by rfl) ⟨1472648, by rfl⟩ : syracuseStep 1963531 = 2945297) B2945297
theorem B9426449 : Blo 1549472 9426449 := bstep (se 2 (by rfl) ⟨3534918, by rfl⟩ : syracuseStep 9426449 = 7069837) B7069837
theorem B5887511 : Blo 1549472 5887511 := bstep (se 1 (by rfl) ⟨4415633, by rfl⟩ : syracuseStep 5887511 = 8831267) B8831267
theorem B3487283 : Blo 1549472 3487283 := bstep (se 1 (by rfl) ⟨2615462, by rfl⟩ : syracuseStep 3487283 = 5230925) B5230925
theorem B3487319 : Blo 1549472 3487319 := bstep (se 1 (by rfl) ⟨2615489, by rfl⟩ : syracuseStep 3487319 = 5230979) B5230979
theorem B5232221 : Blo 1549472 5232221 := bstep (se 3 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 5232221 = 1962083) B1962083
theorem B3487499 : Blo 1549472 3487499 := bstep (se 1 (by rfl) ⟨2615624, by rfl⟩ : syracuseStep 3487499 = 5231249) B5231249
theorem B2324249 : Blo 1549472 2324249 := bstep (se 2 (by rfl) ⟨871593, by rfl⟩ : syracuseStep 2324249 = 1743187) B1743187
theorem B8951597 : Blo 1549472 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B3487553 : Blo 1549472 3487553 := bstep (se 2 (by rfl) ⟨1307832, by rfl⟩ : syracuseStep 3487553 = 2615665) B2615665
theorem B5584733 : Blo 1549472 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B2324363 : Blo 1549472 2324363 := bstep (se 1 (by rfl) ⟨1743272, by rfl⟩ : syracuseStep 2324363 = 3486545) B3486545
theorem B2324375 : Blo 1549472 2324375 := bstep (se 1 (by rfl) ⟨1743281, by rfl⟩ : syracuseStep 2324375 = 3486563) B3486563
theorem B2324441 : Blo 1549472 2324441 := bstep (se 2 (by rfl) ⟨871665, by rfl⟩ : syracuseStep 2324441 = 1743331) B1743331
theorem B8378329 : Blo 1549472 8378329 := bstep (se 2 (by rfl) ⟨3141873, by rfl⟩ : syracuseStep 8378329 = 6283747) B6283747
theorem B35796953 : Blo 1549472 35796953 := bstep (se 2 (by rfl) ⟨13423857, by rfl⟩ : syracuseStep 35796953 = 26847715) B26847715
theorem B3487769 : Blo 1549472 3487769 := bstep (se 2 (by rfl) ⟨1307913, by rfl⟩ : syracuseStep 3487769 = 2615827) B2615827
theorem B13252673 : Blo 1549472 13252673 := bstep (se 2 (by rfl) ⟨4969752, by rfl⟩ : syracuseStep 13252673 = 9939505) B9939505
theorem B2324555 : Blo 1549472 2324555 := bstep (se 1 (by rfl) ⟨1743416, by rfl⟩ : syracuseStep 2324555 = 3486833) B3486833
theorem B2324567 : Blo 1549472 2324567 := bstep (se 1 (by rfl) ⟨1743425, by rfl⟩ : syracuseStep 2324567 = 3486851) B3486851
theorem B3487859 : Blo 1549472 3487859 := bstep (se 1 (by rfl) ⟨2615894, by rfl⟩ : syracuseStep 3487859 = 5231789) B5231789
theorem B27236483 : Blo 1549472 27236483 := bstep (se 1 (by rfl) ⟨20427362, by rfl⟩ : syracuseStep 27236483 = 40854725) B40854725
theorem B3487895 : Blo 1549472 3487895 := bstep (se 1 (by rfl) ⟨2615921, by rfl⟩ : syracuseStep 3487895 = 5231843) B5231843
theorem B2324633 : Blo 1549472 2324633 := bstep (se 2 (by rfl) ⟨871737, by rfl⟩ : syracuseStep 2324633 = 1743475) B1743475
theorem B2324747 : Blo 1549472 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B2324759 : Blo 1549472 2324759 := bstep (se 1 (by rfl) ⟨1743569, by rfl⟩ : syracuseStep 2324759 = 3487139) B3487139
theorem B3488075 : Blo 1549472 3488075 := bstep (se 1 (by rfl) ⟨2616056, by rfl⟩ : syracuseStep 3488075 = 5232113) B5232113
theorem B2324825 : Blo 1549472 2324825 := bstep (se 2 (by rfl) ⟨871809, by rfl⟩ : syracuseStep 2324825 = 1743619) B1743619
theorem B9075037 : Blo 1549472 9075037 := bstep (se 3 (by rfl) ⟨1701569, by rfl⟩ : syracuseStep 9075037 = 3403139) B3403139
theorem B11180389 : Blo 1549472 11180389 := bstep (se 4 (by rfl) ⟨1048161, by rfl⟩ : syracuseStep 11180389 = 2096323) B2096323
theorem B44677493 : Blo 1549472 44677493 := bstep (se 5 (by rfl) ⟨2094257, by rfl⟩ : syracuseStep 44677493 = 4188515) B4188515
theorem B1743223 : Blo 1549472 1743223 := bstep (se 1 (by rfl) ⟨1307417, by rfl⟩ : syracuseStep 1743223 = 2614835) B2614835
theorem B3488129 : Blo 1549472 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B2324939 : Blo 1549472 2324939 := bstep (se 1 (by rfl) ⟨1743704, by rfl⟩ : syracuseStep 2324939 = 3487409) B3487409
theorem B2324951 : Blo 1549472 2324951 := bstep (se 1 (by rfl) ⟨1743713, by rfl⟩ : syracuseStep 2324951 = 3487427) B3487427
theorem B2325017 : Blo 1549472 2325017 := bstep (se 2 (by rfl) ⟨871881, by rfl⟩ : syracuseStep 2325017 = 1743763) B1743763
theorem B1743403 : Blo 1549472 1743403 := bstep (se 1 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 1743403 = 2615105) B2615105
theorem B9935405 : Blo 1549472 9935405 := bstep (se 3 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 9935405 = 3725777) B3725777
theorem B11770433 : Blo 1549472 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B4414027 : Blo 1549472 4414027 := bstep (se 1 (by rfl) ⟨3310520, by rfl⟩ : syracuseStep 4414027 = 6621041) B6621041
theorem B3488345 : Blo 1549472 3488345 := bstep (se 2 (by rfl) ⟨1308129, by rfl⟩ : syracuseStep 3488345 = 2616259) B2616259
theorem B2325131 : Blo 1549472 2325131 := bstep (se 1 (by rfl) ⟨1743848, by rfl⟩ : syracuseStep 2325131 = 3487697) B3487697
theorem B7076497 : Blo 1549472 7076497 := bstep (se 2 (by rfl) ⟨2653686, by rfl⟩ : syracuseStep 7076497 = 5307373) B5307373
theorem B1743511 : Blo 1549472 1743511 := bstep (se 1 (by rfl) ⟨1307633, by rfl⟩ : syracuseStep 1743511 = 2615267) B2615267
theorem B2325143 : Blo 1549472 2325143 := bstep (se 1 (by rfl) ⟨1743857, by rfl⟩ : syracuseStep 2325143 = 3487715) B3487715
theorem B3488435 : Blo 1549472 3488435 := bstep (se 1 (by rfl) ⟨2616326, by rfl⟩ : syracuseStep 3488435 = 5232653) B5232653
theorem B5233355 : Blo 1549472 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B3488471 : Blo 1549472 3488471 := bstep (se 1 (by rfl) ⟨2616353, by rfl⟩ : syracuseStep 3488471 = 5232707) B5232707
theorem B2325209 : Blo 1549472 2325209 := bstep (se 2 (by rfl) ⟨871953, by rfl⟩ : syracuseStep 2325209 = 1743907) B1743907
theorem B3537665 : Blo 1549472 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B5888771 : Blo 1549472 5888771 := bstep (se 1 (by rfl) ⟨4416578, by rfl⟩ : syracuseStep 5888771 = 8833157) B8833157
theorem B3922739 : Blo 1549472 3922739 := bstep (se 1 (by rfl) ⟨2942054, by rfl⟩ : syracuseStep 3922739 = 5884109) B5884109
theorem B1743691 : Blo 1549472 1743691 := bstep (se 1 (by rfl) ⟨1307768, by rfl⟩ : syracuseStep 1743691 = 2615537) B2615537
theorem B2325323 : Blo 1549472 2325323 := bstep (se 1 (by rfl) ⟨1743992, by rfl⟩ : syracuseStep 2325323 = 3487985) B3487985
theorem B2325335 : Blo 1549472 2325335 := bstep (se 1 (by rfl) ⟨1744001, by rfl⟩ : syracuseStep 2325335 = 3488003) B3488003
theorem B4414301 : Blo 1549472 4414301 := bstep (se 3 (by rfl) ⟨827681, by rfl⟩ : syracuseStep 4414301 = 1655363) B1655363
theorem B3488651 : Blo 1549472 3488651 := bstep (se 1 (by rfl) ⟨2616488, by rfl⟩ : syracuseStep 3488651 = 5232977) B5232977
theorem B3144599 : Blo 1549472 3144599 := bstep (se 1 (by rfl) ⟨2358449, by rfl⟩ : syracuseStep 3144599 = 4716899) B4716899
theorem B2325401 : Blo 1549472 2325401 := bstep (se 2 (by rfl) ⟨872025, by rfl⟩ : syracuseStep 2325401 = 1744051) B1744051
theorem B1743799 : Blo 1549472 1743799 := bstep (se 1 (by rfl) ⟨1307849, by rfl⟩ : syracuseStep 1743799 = 2615699) B2615699
theorem B3488705 : Blo 1549472 3488705 := bstep (se 2 (by rfl) ⟨1308264, by rfl⟩ : syracuseStep 3488705 = 2616529) B2616529
theorem B5233625 : Blo 1549472 5233625 := bstep (se 2 (by rfl) ⟨1962609, by rfl⟩ : syracuseStep 5233625 = 3925219) B3925219
theorem B2325515 : Blo 1549472 2325515 := bstep (se 1 (by rfl) ⟨1744136, by rfl⟩ : syracuseStep 2325515 = 3488273) B3488273
theorem B2325527 : Blo 1549472 2325527 := bstep (se 1 (by rfl) ⟨1744145, by rfl⟩ : syracuseStep 2325527 = 3488291) B3488291
theorem B2325593 : Blo 1549472 2325593 := bstep (se 2 (by rfl) ⟨872097, by rfl⟩ : syracuseStep 2325593 = 1744195) B1744195
theorem B1743979 : Blo 1549472 1743979 := bstep (se 1 (by rfl) ⟨1307984, by rfl⟩ : syracuseStep 1743979 = 2615969) B2615969
theorem B3488921 : Blo 1549472 3488921 := bstep (se 2 (by rfl) ⟨1308345, by rfl⟩ : syracuseStep 3488921 = 2616691) B2616691
theorem B2325707 : Blo 1549472 2325707 := bstep (se 1 (by rfl) ⟨1744280, by rfl⟩ : syracuseStep 2325707 = 3488561) B3488561
theorem B1744087 : Blo 1549472 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B2325719 : Blo 1549472 2325719 := bstep (se 1 (by rfl) ⟨1744289, by rfl⟩ : syracuseStep 2325719 = 3488579) B3488579
theorem B3489011 : Blo 1549472 3489011 := bstep (se 1 (by rfl) ⟨2616758, by rfl⟩ : syracuseStep 3489011 = 5233517) B5233517
theorem B3489047 : Blo 1549472 3489047 := bstep (se 1 (by rfl) ⟨2616785, by rfl⟩ : syracuseStep 3489047 = 5233571) B5233571
theorem B2325785 : Blo 1549472 2325785 := bstep (se 2 (by rfl) ⟨872169, by rfl⟩ : syracuseStep 2325785 = 1744339) B1744339
theorem B1768727 : Blo 1549472 1768727 := bstep (se 1 (by rfl) ⟨1326545, by rfl⟩ : syracuseStep 1768727 = 2653091) B2653091
theorem B26475821 : Blo 1549472 26475821 := bstep (se 3 (by rfl) ⟨4964216, by rfl⟩ : syracuseStep 26475821 = 9928433) B9928433
theorem B3726643 : Blo 1549472 3726643 := bstep (se 1 (by rfl) ⟨2794982, by rfl⟩ : syracuseStep 3726643 = 5589965) B5589965
theorem B3923275 : Blo 1549472 3923275 := bstep (se 1 (by rfl) ⟨2942456, by rfl⟩ : syracuseStep 3923275 = 5884913) B5884913
theorem B3186049 : Blo 1549472 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B1744267 : Blo 1549472 1744267 := bstep (se 1 (by rfl) ⟨1308200, by rfl⟩ : syracuseStep 1744267 = 2616401) B2616401
theorem B2325899 : Blo 1549472 2325899 := bstep (se 1 (by rfl) ⟨1744424, by rfl⟩ : syracuseStep 2325899 = 3488849) B3488849
theorem B2325911 : Blo 1549472 2325911 := bstep (se 1 (by rfl) ⟨1744433, by rfl⟩ : syracuseStep 2325911 = 3488867) B3488867
theorem B8068531 : Blo 1549472 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B3489227 : Blo 1549472 3489227 := bstep (se 1 (by rfl) ⟨2616920, by rfl⟩ : syracuseStep 3489227 = 5233841) B5233841
theorem B3923417 : Blo 1549472 3923417 := bstep (se 2 (by rfl) ⟨1471281, by rfl⟩ : syracuseStep 3923417 = 2942563) B2942563
theorem B2325977 : Blo 1549472 2325977 := bstep (se 2 (by rfl) ⟨872241, by rfl⟩ : syracuseStep 2325977 = 1744483) B1744483
theorem B1744375 : Blo 1549472 1744375 := bstep (se 1 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 1744375 = 2616563) B2616563
theorem B3489281 : Blo 1549472 3489281 := bstep (se 2 (by rfl) ⟨1308480, by rfl⟩ : syracuseStep 3489281 = 2616961) B2616961
theorem B7847441 : Blo 1549472 7847441 := bstep (se 2 (by rfl) ⟨2942790, by rfl⟩ : syracuseStep 7847441 = 5885581) B5885581
theorem B2326091 : Blo 1549472 2326091 := bstep (se 1 (by rfl) ⟨1744568, by rfl⟩ : syracuseStep 2326091 = 3489137) B3489137
theorem B2326103 : Blo 1549472 2326103 := bstep (se 1 (by rfl) ⟨1744577, by rfl⟩ : syracuseStep 2326103 = 3489155) B3489155
theorem B5234327 : Blo 1549472 5234327 := bstep (se 1 (by rfl) ⟨3925745, by rfl⟩ : syracuseStep 5234327 = 7851491) B7851491
theorem B2326169 : Blo 1549472 2326169 := bstep (se 2 (by rfl) ⟨872313, by rfl⟩ : syracuseStep 2326169 = 1744627) B1744627
theorem B1744555 : Blo 1549472 1744555 := bstep (se 1 (by rfl) ⟨1308416, by rfl⟩ : syracuseStep 1744555 = 2616833) B2616833
theorem B7847603 : Blo 1549472 7847603 := bstep (se 1 (by rfl) ⟨5885702, by rfl⟩ : syracuseStep 7847603 = 11771405) B11771405
theorem B3489497 : Blo 1549472 3489497 := bstep (se 2 (by rfl) ⟨1308561, by rfl⟩ : syracuseStep 3489497 = 2617123) B2617123
theorem B2326283 : Blo 1549472 2326283 := bstep (se 1 (by rfl) ⟨1744712, by rfl⟩ : syracuseStep 2326283 = 3489425) B3489425
theorem B6627089 : Blo 1549472 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B1744663 : Blo 1549472 1744663 := bstep (se 1 (by rfl) ⟨1308497, by rfl⟩ : syracuseStep 1744663 = 2616995) B2616995
theorem B2326295 : Blo 1549472 2326295 := bstep (se 1 (by rfl) ⟨1744721, by rfl⟩ : syracuseStep 2326295 = 3489443) B3489443
theorem B3489587 : Blo 1549472 3489587 := bstep (se 1 (by rfl) ⟨2617190, by rfl⟩ : syracuseStep 3489587 = 5234381) B5234381
theorem B3489623 : Blo 1549472 3489623 := bstep (se 1 (by rfl) ⟨2617217, by rfl⟩ : syracuseStep 3489623 = 5234435) B5234435
theorem B2326361 : Blo 1549472 2326361 := bstep (se 2 (by rfl) ⟨872385, by rfl⟩ : syracuseStep 2326361 = 1744771) B1744771
theorem B3309427 : Blo 1549472 3309427 := bstep (se 1 (by rfl) ⟨2482070, by rfl⟩ : syracuseStep 3309427 = 4964141) B4964141
theorem B1744843 : Blo 1549472 1744843 := bstep (se 1 (by rfl) ⟨1308632, by rfl⟩ : syracuseStep 1744843 = 2617265) B2617265
theorem B2326475 : Blo 1549472 2326475 := bstep (se 1 (by rfl) ⟨1744856, by rfl⟩ : syracuseStep 2326475 = 3489713) B3489713
theorem B4538315 : Blo 1549472 4538315 := bstep (se 1 (by rfl) ⟨3403736, by rfl⟩ : syracuseStep 4538315 = 6807473) B6807473
theorem B2326487 : Blo 1549472 2326487 := bstep (se 1 (by rfl) ⟨1744865, by rfl⟩ : syracuseStep 2326487 = 3489731) B3489731
theorem B2326535 : Blo 1549472 2326535 := bstep (se 1 (by rfl) ⟨1744901, by rfl⟩ : syracuseStep 2326535 = 3489803) B3489803
theorem B2326571 : Blo 1549472 2326571 := bstep (se 1 (by rfl) ⟨1744928, by rfl⟩ : syracuseStep 2326571 = 3489857) B3489857
theorem B2326601 : Blo 1549472 2326601 := bstep (se 2 (by rfl) ⟨872475, by rfl⟩ : syracuseStep 2326601 = 1744951) B1744951
theorem B3489911 : Blo 1549472 3489911 := bstep (se 1 (by rfl) ⟨2617433, by rfl⟩ : syracuseStep 3489911 = 5234867) B5234867
theorem B2982035 : Blo 1549472 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B2326715 : Blo 1549472 2326715 := bstep (se 1 (by rfl) ⟨1745036, by rfl⟩ : syracuseStep 2326715 = 3490073) B3490073
theorem B2326775 : Blo 1549472 2326775 := bstep (se 1 (by rfl) ⟨1745081, by rfl⟩ : syracuseStep 2326775 = 3490163) B3490163
theorem B4415759 : Blo 1549472 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B2326799 : Blo 1549472 2326799 := bstep (se 1 (by rfl) ⟨1745099, by rfl⟩ : syracuseStep 2326799 = 3490199) B3490199
theorem B1745167 : Blo 1549472 1745167 := bstep (se 1 (by rfl) ⟨1308875, by rfl⟩ : syracuseStep 1745167 = 2617751) B2617751
theorem B3490091 : Blo 1549472 3490091 := bstep (se 1 (by rfl) ⟨2617568, by rfl⟩ : syracuseStep 3490091 = 5235137) B5235137
theorem B2326841 : Blo 1549472 2326841 := bstep (se 2 (by rfl) ⟨872565, by rfl⟩ : syracuseStep 2326841 = 1745131) B1745131
theorem B7848251 : Blo 1549472 7848251 := bstep (se 1 (by rfl) ⟨5886188, by rfl⟩ : syracuseStep 7848251 = 11772377) B11772377
theorem B7455091 : Blo 1549472 7455091 := bstep (se 1 (by rfl) ⟨5591318, by rfl⟩ : syracuseStep 7455091 = 11182637) B11182637
theorem B3924359 : Blo 1549472 3924359 := bstep (se 1 (by rfl) ⟨2943269, by rfl⟩ : syracuseStep 3924359 = 5886539) B5886539
theorem B2326919 : Blo 1549472 2326919 := bstep (se 1 (by rfl) ⟨1745189, by rfl⟩ : syracuseStep 2326919 = 3490379) B3490379
theorem B2326955 : Blo 1549472 2326955 := bstep (se 1 (by rfl) ⟨1745216, by rfl⟩ : syracuseStep 2326955 = 3490433) B3490433
theorem B3924409 : Blo 1549472 3924409 := bstep (se 2 (by rfl) ⟨1471653, by rfl⟩ : syracuseStep 3924409 = 2943307) B2943307
theorem B2326985 : Blo 1549472 2326985 := bstep (se 2 (by rfl) ⟨872619, by rfl⟩ : syracuseStep 2326985 = 1745239) B1745239
theorem B12100049 : Blo 1549472 12100049 := bstep (se 2 (by rfl) ⟨4537518, by rfl⟩ : syracuseStep 12100049 = 9075037) B9075037
theorem B7848413 : Blo 1549472 7848413 := bstep (se 3 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 7848413 = 2943155) B2943155
theorem B2327099 : Blo 1549472 2327099 := bstep (se 1 (by rfl) ⟨1745324, by rfl⟩ : syracuseStep 2327099 = 3490649) B3490649
theorem B2327159 : Blo 1549472 2327159 := bstep (se 1 (by rfl) ⟨1745369, by rfl⟩ : syracuseStep 2327159 = 3490739) B3490739
theorem B2327183 : Blo 1549472 2327183 := bstep (se 1 (by rfl) ⟨1745387, by rfl⟩ : syracuseStep 2327183 = 3490775) B3490775
theorem B3490451 : Blo 1549472 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B4842185 : Blo 1549472 4842185 := bstep (se 2 (by rfl) ⟨1815819, by rfl⟩ : syracuseStep 4842185 = 3631639) B3631639
theorem B3490505 : Blo 1549472 3490505 := bstep (se 2 (by rfl) ⟨1308939, by rfl⟩ : syracuseStep 3490505 = 2617879) B2617879
theorem B9937637 : Blo 1549472 9937637 := bstep (se 4 (by rfl) ⟨931653, by rfl⟩ : syracuseStep 9937637 = 1863307) B1863307
theorem B7848737 : Blo 1549472 7848737 := bstep (se 2 (by rfl) ⟨2943276, by rfl⟩ : syracuseStep 7848737 = 5886553) B5886553
theorem B5235515 : Blo 1549472 5235515 := bstep (se 1 (by rfl) ⟨3926636, by rfl⟩ : syracuseStep 5235515 = 7853273) B7853273
theorem B8496019 : Blo 1549472 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B9069515 : Blo 1549472 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B7447555 : Blo 1549472 7447555 := bstep (se 1 (by rfl) ⟨5585666, by rfl⟩ : syracuseStep 7447555 = 11171333) B11171333
theorem B6284299 : Blo 1549472 6284299 := bstep (se 1 (by rfl) ⟨4713224, by rfl⟩ : syracuseStep 6284299 = 9426449) B9426449
theorem B3925007 : Blo 1549472 3925007 := bstep (se 1 (by rfl) ⟨2943755, by rfl⟩ : syracuseStep 3925007 = 5887511) B5887511
theorem B4416545 : Blo 1549472 4416545 := bstep (se 2 (by rfl) ⟨1656204, by rfl⟩ : syracuseStep 4416545 = 3312409) B3312409
theorem B13247549 : Blo 1549472 13247549 := bstep (se 3 (by rfl) ⟨2483915, by rfl⟩ : syracuseStep 13247549 = 4967831) B4967831
theorem B80577623 : Blo 1549472 80577623 := bstep (se 1 (by rfl) ⟨60433217, by rfl⟩ : syracuseStep 80577623 = 120866435) B120866435
theorem B1549499 : Blo 1549472 1549499 := bstep (se 1 (by rfl) ⟨1162124, by rfl⟩ : syracuseStep 1549499 = 2324249) B2324249
theorem B2942153 : Blo 1549472 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B1549575 : Blo 1549472 1549575 := bstep (se 1 (by rfl) ⟨1162181, by rfl⟩ : syracuseStep 1549575 = 2324363) B2324363
theorem B1549583 : Blo 1549472 1549583 := bstep (se 1 (by rfl) ⟨1162187, by rfl⟩ : syracuseStep 1549583 = 2324375) B2324375
theorem B5236001 : Blo 1549472 5236001 := bstep (se 2 (by rfl) ⟨1963500, by rfl⟩ : syracuseStep 5236001 = 3927001) B3927001
theorem B1549627 : Blo 1549472 1549627 := bstep (se 1 (by rfl) ⟨1162220, by rfl⟩ : syracuseStep 1549627 = 2324441) B2324441
theorem B23864635 : Blo 1549472 23864635 := bstep (se 1 (by rfl) ⟨17898476, by rfl⟩ : syracuseStep 23864635 = 35796953) B35796953
theorem B76498289 : Blo 1549472 76498289 := bstep (se 2 (by rfl) ⟨28686858, by rfl⟩ : syracuseStep 76498289 = 57373717) B57373717
theorem B1549703 : Blo 1549472 1549703 := bstep (se 1 (by rfl) ⟨1162277, by rfl⟩ : syracuseStep 1549703 = 2324555) B2324555
theorem B13419911 : Blo 1549472 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B1549711 : Blo 1549472 1549711 := bstep (se 1 (by rfl) ⟨1162283, by rfl⟩ : syracuseStep 1549711 = 2324567) B2324567
theorem B1549755 : Blo 1549472 1549755 := bstep (se 1 (by rfl) ⟨1162316, by rfl⟩ : syracuseStep 1549755 = 2324633) B2324633
theorem B1549831 : Blo 1549472 1549831 := bstep (se 1 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 1549831 = 2324747) B2324747
theorem B1549839 : Blo 1549472 1549839 := bstep (se 1 (by rfl) ⟨1162379, by rfl⟩ : syracuseStep 1549839 = 2324759) B2324759
theorem B1549883 : Blo 1549472 1549883 := bstep (se 1 (by rfl) ⟨1162412, by rfl⟩ : syracuseStep 1549883 = 2324825) B2324825
theorem B1549959 : Blo 1549472 1549959 := bstep (se 1 (by rfl) ⟨1162469, by rfl⟩ : syracuseStep 1549959 = 2324939) B2324939
theorem B1549967 : Blo 1549472 1549967 := bstep (se 1 (by rfl) ⟨1162475, by rfl⟩ : syracuseStep 1549967 = 2324951) B2324951
theorem B1550011 : Blo 1549472 1550011 := bstep (se 1 (by rfl) ⟨1162508, by rfl⟩ : syracuseStep 1550011 = 2325017) B2325017
theorem B3925705 : Blo 1549472 3925705 := bstep (se 2 (by rfl) ⟨1472139, by rfl⟩ : syracuseStep 3925705 = 2944279) B2944279
theorem B7849709 : Blo 1549472 7849709 := bstep (se 3 (by rfl) ⟨1471820, by rfl⟩ : syracuseStep 7849709 = 2943641) B2943641
theorem B1550087 : Blo 1549472 1550087 := bstep (se 1 (by rfl) ⟨1162565, by rfl⟩ : syracuseStep 1550087 = 2325131) B2325131
theorem B1550095 : Blo 1549472 1550095 := bstep (se 1 (by rfl) ⟨1162571, by rfl⟩ : syracuseStep 1550095 = 2325143) B2325143
theorem B1550139 : Blo 1549472 1550139 := bstep (se 1 (by rfl) ⟨1162604, by rfl⟩ : syracuseStep 1550139 = 2325209) B2325209
theorem B3925847 : Blo 1549472 3925847 := bstep (se 1 (by rfl) ⟨2944385, by rfl⟩ : syracuseStep 3925847 = 5888771) B5888771
theorem B2615159 : Blo 1549472 2615159 := bstep (se 1 (by rfl) ⟨1961369, by rfl⟩ : syracuseStep 2615159 = 3922739) B3922739
theorem B1550215 : Blo 1549472 1550215 := bstep (se 1 (by rfl) ⟨1162661, by rfl⟩ : syracuseStep 1550215 = 2325323) B2325323
theorem B1550223 : Blo 1549472 1550223 := bstep (se 1 (by rfl) ⟨1162667, by rfl⟩ : syracuseStep 1550223 = 2325335) B2325335
theorem B2942867 : Blo 1549472 2942867 := bstep (se 1 (by rfl) ⟨2207150, by rfl⟩ : syracuseStep 2942867 = 4414301) B4414301
theorem B11175833 : Blo 1549472 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B10758041 : Blo 1549472 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B2942905 : Blo 1549472 2942905 := bstep (se 2 (by rfl) ⟨1103589, by rfl⟩ : syracuseStep 2942905 = 2207179) B2207179
theorem B1550267 : Blo 1549472 1550267 := bstep (se 1 (by rfl) ⟨1162700, by rfl⟩ : syracuseStep 1550267 = 2325401) B2325401
theorem B1550343 : Blo 1549472 1550343 := bstep (se 1 (by rfl) ⟨1162757, by rfl⟩ : syracuseStep 1550343 = 2325515) B2325515
theorem B11175947 : Blo 1549472 11175947 := bstep (se 1 (by rfl) ⟨8381960, by rfl⟩ : syracuseStep 11175947 = 16763921) B16763921
theorem B1550351 : Blo 1549472 1550351 := bstep (se 1 (by rfl) ⟨1162763, by rfl⟩ : syracuseStep 1550351 = 2325527) B2325527
theorem B1550395 : Blo 1549472 1550395 := bstep (se 1 (by rfl) ⟨1162796, by rfl⟩ : syracuseStep 1550395 = 2325593) B2325593
theorem B1550471 : Blo 1549472 1550471 := bstep (se 1 (by rfl) ⟨1162853, by rfl⟩ : syracuseStep 1550471 = 2325707) B2325707
theorem B1550479 : Blo 1549472 1550479 := bstep (se 1 (by rfl) ⟨1162859, by rfl⟩ : syracuseStep 1550479 = 2325719) B2325719
theorem B1550523 : Blo 1549472 1550523 := bstep (se 1 (by rfl) ⟨1162892, by rfl⟩ : syracuseStep 1550523 = 2325785) B2325785
theorem B1550599 : Blo 1549472 1550599 := bstep (se 1 (by rfl) ⟨1162949, by rfl⟩ : syracuseStep 1550599 = 2325899) B2325899
theorem B1550607 : Blo 1549472 1550607 := bstep (se 1 (by rfl) ⟨1162955, by rfl⟩ : syracuseStep 1550607 = 2325911) B2325911
theorem B2615611 : Blo 1549472 2615611 := bstep (se 1 (by rfl) ⟨1961708, by rfl⟩ : syracuseStep 2615611 = 3923417) B3923417
theorem B1550651 : Blo 1549472 1550651 := bstep (se 1 (by rfl) ⟨1162988, by rfl⟩ : syracuseStep 1550651 = 2325977) B2325977
theorem B1550727 : Blo 1549472 1550727 := bstep (se 1 (by rfl) ⟨1163045, by rfl⟩ : syracuseStep 1550727 = 2326091) B2326091
theorem B1550735 : Blo 1549472 1550735 := bstep (se 1 (by rfl) ⟨1163051, by rfl⟩ : syracuseStep 1550735 = 2326103) B2326103
theorem B1550779 : Blo 1549472 1550779 := bstep (se 1 (by rfl) ⟨1163084, by rfl⟩ : syracuseStep 1550779 = 2326169) B2326169
theorem B2615753 : Blo 1549472 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B1550855 : Blo 1549472 1550855 := bstep (se 1 (by rfl) ⟨1163141, by rfl⟩ : syracuseStep 1550855 = 2326283) B2326283
theorem B5884427 : Blo 1549472 5884427 := bstep (se 1 (by rfl) ⟨4413320, by rfl⟩ : syracuseStep 5884427 = 8826641) B8826641
theorem B4418059 : Blo 1549472 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B1550863 : Blo 1549472 1550863 := bstep (se 1 (by rfl) ⟨1163147, by rfl⟩ : syracuseStep 1550863 = 2326295) B2326295
theorem B7850519 : Blo 1549472 7850519 := bstep (se 1 (by rfl) ⟨5887889, by rfl⟩ : syracuseStep 7850519 = 11775779) B11775779
theorem B12102173 : Blo 1549472 12102173 := bstep (se 3 (by rfl) ⟨2269157, by rfl⟩ : syracuseStep 12102173 = 4538315) B4538315
theorem B3312161 : Blo 1549472 3312161 := bstep (se 2 (by rfl) ⟨1242060, by rfl⟩ : syracuseStep 3312161 = 2484121) B2484121
theorem B1550907 : Blo 1549472 1550907 := bstep (se 1 (by rfl) ⟨1163180, by rfl⟩ : syracuseStep 1550907 = 2326361) B2326361
theorem B1550983 : Blo 1549472 1550983 := bstep (se 1 (by rfl) ⟨1163237, by rfl⟩ : syracuseStep 1550983 = 2326475) B2326475
theorem B1550991 : Blo 1549472 1550991 := bstep (se 1 (by rfl) ⟨1163243, by rfl⟩ : syracuseStep 1550991 = 2326487) B2326487
theorem B1551035 : Blo 1549472 1551035 := bstep (se 1 (by rfl) ⟨1163276, by rfl⟩ : syracuseStep 1551035 = 2326553) B2326553
theorem B1551111 : Blo 1549472 1551111 := bstep (se 1 (by rfl) ⟨1163333, by rfl⟩ : syracuseStep 1551111 = 2326667) B2326667
theorem B1551119 : Blo 1549472 1551119 := bstep (se 1 (by rfl) ⟨1163339, by rfl⟩ : syracuseStep 1551119 = 2326679) B2326679
theorem B1551163 : Blo 1549472 1551163 := bstep (se 1 (by rfl) ⟨1163372, by rfl⟩ : syracuseStep 1551163 = 2326745) B2326745
theorem B1551239 : Blo 1549472 1551239 := bstep (se 1 (by rfl) ⟨1163429, by rfl⟩ : syracuseStep 1551239 = 2326859) B2326859
theorem B2485127 : Blo 1549472 2485127 := bstep (se 1 (by rfl) ⟨1863845, by rfl⟩ : syracuseStep 2485127 = 3727691) B3727691
theorem B1551247 : Blo 1549472 1551247 := bstep (se 1 (by rfl) ⟨1163435, by rfl⟩ : syracuseStep 1551247 = 2326871) B2326871
theorem B6712211 : Blo 1549472 6712211 := bstep (se 1 (by rfl) ⟨5034158, by rfl⟩ : syracuseStep 6712211 = 10068317) B10068317
theorem B2206649 : Blo 1549472 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B1551291 : Blo 1549472 1551291 := bstep (se 1 (by rfl) ⟨1163468, by rfl⟩ : syracuseStep 1551291 = 2326937) B2326937
theorem B1551367 : Blo 1549472 1551367 := bstep (se 1 (by rfl) ⟨1163525, by rfl⟩ : syracuseStep 1551367 = 2327051) B2327051
theorem B8825867 : Blo 1549472 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B1551375 : Blo 1549472 1551375 := bstep (se 1 (by rfl) ⟨1163531, by rfl⟩ : syracuseStep 1551375 = 2327063) B2327063
theorem B1551419 : Blo 1549472 1551419 := bstep (se 1 (by rfl) ⟨1163564, by rfl⟩ : syracuseStep 1551419 = 2327129) B2327129
theorem B5229629 : Blo 1549472 5229629 := bstep (se 3 (by rfl) ⟨980555, by rfl⟩ : syracuseStep 5229629 = 1961111) B1961111
theorem B19868759 : Blo 1549472 19868759 := bstep (se 1 (by rfl) ⟨14901569, by rfl⟩ : syracuseStep 19868759 = 29803139) B29803139
theorem B2616455 : Blo 1549472 2616455 := bstep (se 1 (by rfl) ⟨1962341, by rfl⟩ : syracuseStep 2616455 = 3924683) B3924683
theorem B7450001 : Blo 1549472 7450001 := bstep (se 2 (by rfl) ⟨2793750, by rfl⟩ : syracuseStep 7450001 = 5587501) B5587501
theorem B13249939 : Blo 1549472 13249939 := bstep (se 1 (by rfl) ⟨9937454, by rfl⟩ : syracuseStep 13249939 = 19874909) B19874909
theorem B2330027 : Blo 1549472 2330027 := bstep (se 1 (by rfl) ⟨1747520, by rfl⟩ : syracuseStep 2330027 = 3495041) B3495041
theorem B5885369 : Blo 1549472 5885369 := bstep (se 2 (by rfl) ⟨2207013, by rfl⟩ : syracuseStep 5885369 = 4414027) B4414027
theorem B7556651 : Blo 1549472 7556651 := bstep (se 1 (by rfl) ⟨5667488, by rfl⟩ : syracuseStep 7556651 = 11334977) B11334977
theorem B3313271 : Blo 1549472 3313271 := bstep (se 1 (by rfl) ⟨2484953, by rfl⟩ : syracuseStep 3313271 = 4969907) B4969907
theorem B21507763 : Blo 1549472 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B2207503 : Blo 1549472 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B2617103 : Blo 1549472 2617103 := bstep (se 1 (by rfl) ⟨1962827, by rfl⟩ : syracuseStep 2617103 = 3925655) B3925655
theorem B13242149 : Blo 1549472 13242149 := bstep (se 4 (by rfl) ⟨1241451, by rfl⟩ : syracuseStep 13242149 = 2482903) B2482903
theorem B2944811 : Blo 1549472 2944811 := bstep (se 1 (by rfl) ⟨2208608, by rfl⟩ : syracuseStep 2944811 = 4417217) B4417217
theorem B5967731 : Blo 1549472 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B3723155 : Blo 1549472 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B8835115 : Blo 1549472 8835115 := bstep (se 1 (by rfl) ⟨6626336, by rfl⟩ : syracuseStep 8835115 = 13252673) B13252673
theorem B18157655 : Blo 1549472 18157655 := bstep (se 1 (by rfl) ⟨13618241, by rfl⟩ : syracuseStep 18157655 = 27236483) B27236483
theorem B7450825 : Blo 1549472 7450825 := bstep (se 2 (by rfl) ⟨2794059, by rfl⟩ : syracuseStep 7450825 = 5588119) B5588119
theorem B2617643 : Blo 1549472 2617643 := bstep (se 1 (by rfl) ⟨1963232, by rfl⟩ : syracuseStep 2617643 = 3926465) B3926465
theorem B2208073 : Blo 1549472 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B6623603 : Blo 1549472 6623603 := bstep (se 1 (by rfl) ⟨4967702, by rfl⟩ : syracuseStep 6623603 = 9935405) B9935405
theorem B8384903 : Blo 1549472 8384903 := bstep (se 1 (by rfl) ⟨6288677, by rfl⟩ : syracuseStep 8384903 = 12577355) B12577355
theorem B4968857 : Blo 1549472 4968857 := bstep (se 2 (by rfl) ⟨1863321, by rfl⟩ : syracuseStep 4968857 = 3726643) B3726643
theorem B5231033 : Blo 1549472 5231033 := bstep (se 2 (by rfl) ⟨1961637, by rfl⟩ : syracuseStep 5231033 = 3923275) B3923275
theorem B4248065 : Blo 1549472 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B7844363 : Blo 1549472 7844363 := bstep (se 1 (by rfl) ⟨5883272, by rfl⟩ : syracuseStep 7844363 = 11766545) B11766545
theorem B7844525 : Blo 1549472 7844525 := bstep (se 3 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 7844525 = 2941697) B2941697
theorem B2618041 : Blo 1549472 2618041 := bstep (se 2 (by rfl) ⟨981765, by rfl⟩ : syracuseStep 2618041 = 1963531) B1963531
theorem B10064729 : Blo 1549472 10064729 := bstep (se 2 (by rfl) ⟨3774273, by rfl⟩ : syracuseStep 10064729 = 7548547) B7548547
theorem B11932505 : Blo 1549472 11932505 := bstep (se 2 (by rfl) ⟨4474689, by rfl⟩ : syracuseStep 11932505 = 8949379) B8949379
theorem B17650547 : Blo 1549472 17650547 := bstep (se 1 (by rfl) ⟨13237910, by rfl⟩ : syracuseStep 17650547 = 26475821) B26475821
theorem B3486599 : Blo 1549472 3486599 := bstep (se 1 (by rfl) ⟨2614949, by rfl⟩ : syracuseStep 3486599 = 5229899) B5229899
theorem B5313433 : Blo 1549472 5313433 := bstep (se 2 (by rfl) ⟨1992537, by rfl⟩ : syracuseStep 5313433 = 3985075) B3985075
theorem B5231627 : Blo 1549472 5231627 := bstep (se 1 (by rfl) ⟨3923720, by rfl⟩ : syracuseStep 5231627 = 7847441) B7847441
theorem B3486779 : Blo 1549472 3486779 := bstep (se 1 (by rfl) ⟨2615084, by rfl⟩ : syracuseStep 3486779 = 5230169) B5230169
theorem B5231735 : Blo 1549472 5231735 := bstep (se 1 (by rfl) ⟨3923801, by rfl⟩ : syracuseStep 5231735 = 7847603) B7847603
theorem B4412569 : Blo 1549472 4412569 := bstep (se 2 (by rfl) ⟨1654713, by rfl⟩ : syracuseStep 4412569 = 3309427) B3309427
theorem B3486905 : Blo 1549472 3486905 := bstep (se 2 (by rfl) ⟨1307589, by rfl⟩ : syracuseStep 3486905 = 2615179) B2615179
theorem B11171105 : Blo 1549472 11171105 := bstep (se 2 (by rfl) ⟨4189164, by rfl⟩ : syracuseStep 11171105 = 8378329) B8378329
theorem B3724663 : Blo 1549472 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B4412819 : Blo 1549472 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B1963435 : Blo 1549472 1963435 := bstep (se 1 (by rfl) ⟨1472576, by rfl⟩ : syracuseStep 1963435 = 2945153) B2945153
theorem B9434627 : Blo 1549472 9434627 := bstep (se 1 (by rfl) ⟨7075970, by rfl⟩ : syracuseStep 9434627 = 14151941) B14151941
theorem B3487247 : Blo 1549472 3487247 := bstep (se 1 (by rfl) ⟨2615435, by rfl⟩ : syracuseStep 3487247 = 5230871) B5230871
theorem B7853597 : Blo 1549472 7853597 := bstep (se 3 (by rfl) ⟨1472549, by rfl⟩ : syracuseStep 7853597 = 2945099) B2945099
theorem B3487265 : Blo 1549472 3487265 := bstep (se 2 (by rfl) ⟨1307724, by rfl⟩ : syracuseStep 3487265 = 2615449) B2615449
theorem B22353509 : Blo 1549472 22353509 := bstep (se 4 (by rfl) ⟨2095641, by rfl⟩ : syracuseStep 22353509 = 4191283) B4191283
theorem B5232329 : Blo 1549472 5232329 := bstep (se 2 (by rfl) ⟨1962123, by rfl⟩ : syracuseStep 5232329 = 3924247) B3924247
theorem B2324231 : Blo 1549472 2324231 := bstep (se 1 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 2324231 = 3486347) B3486347
theorem B2324267 : Blo 1549472 2324267 := bstep (se 1 (by rfl) ⟨1743200, by rfl⟩ : syracuseStep 2324267 = 3486401) B3486401
theorem B14907185 : Blo 1549472 14907185 := bstep (se 2 (by rfl) ⟨5590194, by rfl⟩ : syracuseStep 14907185 = 11180389) B11180389
theorem B2094907 : Blo 1549472 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B2324297 : Blo 1549472 2324297 := bstep (se 2 (by rfl) ⟨871611, by rfl⟩ : syracuseStep 2324297 = 1743223) B1743223
theorem B3487607 : Blo 1549472 3487607 := bstep (se 1 (by rfl) ⟨2615705, by rfl⟩ : syracuseStep 3487607 = 5231411) B5231411
theorem B2324411 : Blo 1549472 2324411 := bstep (se 1 (by rfl) ⟨1743308, by rfl⟩ : syracuseStep 2324411 = 3486617) B3486617
theorem B16758731 : Blo 1549472 16758731 := bstep (se 1 (by rfl) ⟨12569048, by rfl⟩ : syracuseStep 16758731 = 25138097) B25138097
theorem B17668043 : Blo 1549472 17668043 := bstep (se 1 (by rfl) ⟨13251032, by rfl⟩ : syracuseStep 17668043 = 26502065) B26502065
theorem B2324471 : Blo 1549472 2324471 := bstep (se 1 (by rfl) ⟨1743353, by rfl⟩ : syracuseStep 2324471 = 3486707) B3486707
theorem B7854083 : Blo 1549472 7854083 := bstep (se 1 (by rfl) ⟨5890562, by rfl⟩ : syracuseStep 7854083 = 11781125) B11781125
theorem B5888011 : Blo 1549472 5888011 := bstep (se 1 (by rfl) ⟨4416008, by rfl⟩ : syracuseStep 5888011 = 8832017) B8832017
theorem B2324495 : Blo 1549472 2324495 := bstep (se 1 (by rfl) ⟨1743371, by rfl⟩ : syracuseStep 2324495 = 3486743) B3486743
theorem B16766999 : Blo 1549472 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B3487787 : Blo 1549472 3487787 := bstep (se 1 (by rfl) ⟨2615840, by rfl⟩ : syracuseStep 3487787 = 5231681) B5231681
theorem B2324537 : Blo 1549472 2324537 := bstep (se 2 (by rfl) ⟨871701, by rfl⟩ : syracuseStep 2324537 = 1743403) B1743403
theorem B4716605 : Blo 1549472 4716605 := bstep (se 3 (by rfl) ⟨884363, by rfl⟩ : syracuseStep 4716605 = 1768727) B1768727
theorem B27203701 : Blo 1549472 27203701 := bstep (se 5 (by rfl) ⟨1275173, by rfl⟩ : syracuseStep 27203701 = 2550347) B2550347
theorem B2324615 : Blo 1549472 2324615 := bstep (se 1 (by rfl) ⟨1743461, by rfl⟩ : syracuseStep 2324615 = 3486923) B3486923
theorem B2324651 : Blo 1549472 2324651 := bstep (se 1 (by rfl) ⟨1743488, by rfl⟩ : syracuseStep 2324651 = 3486977) B3486977
theorem B8829101 : Blo 1549472 8829101 := bstep (se 3 (by rfl) ⟨1655456, by rfl⟩ : syracuseStep 8829101 = 3310913) B3310913
theorem B9435329 : Blo 1549472 9435329 := bstep (se 2 (by rfl) ⟨3538248, by rfl⟩ : syracuseStep 9435329 = 7076497) B7076497
theorem B3922121 : Blo 1549472 3922121 := bstep (se 2 (by rfl) ⟨1470795, by rfl⟩ : syracuseStep 3922121 = 2941591) B2941591
theorem B2324681 : Blo 1549472 2324681 := bstep (se 2 (by rfl) ⟨871755, by rfl⟩ : syracuseStep 2324681 = 1743511) B1743511
theorem B7846145 : Blo 1549472 7846145 := bstep (se 2 (by rfl) ⟨2942304, by rfl⟩ : syracuseStep 7846145 = 5884609) B5884609
theorem B2324795 : Blo 1549472 2324795 := bstep (se 1 (by rfl) ⟨1743596, by rfl⟩ : syracuseStep 2324795 = 3487193) B3487193
theorem B5888315 : Blo 1549472 5888315 := bstep (se 1 (by rfl) ⟨4416236, by rfl⟩ : syracuseStep 5888315 = 8832473) B8832473
theorem B4413811 : Blo 1549472 4413811 := bstep (se 1 (by rfl) ⟨3310358, by rfl⟩ : syracuseStep 4413811 = 6620717) B6620717
theorem B2324855 : Blo 1549472 2324855 := bstep (se 1 (by rfl) ⟨1743641, by rfl⟩ : syracuseStep 2324855 = 3487283) B3487283
theorem B5233031 : Blo 1549472 5233031 := bstep (se 1 (by rfl) ⟨3924773, by rfl⟩ : syracuseStep 5233031 = 7849547) B7849547
theorem B2324879 : Blo 1549472 2324879 := bstep (se 1 (by rfl) ⟨1743659, by rfl⟩ : syracuseStep 2324879 = 3487319) B3487319
theorem B3488147 : Blo 1549472 3488147 := bstep (se 1 (by rfl) ⟨2616110, by rfl⟩ : syracuseStep 3488147 = 5232221) B5232221
theorem B18897299 : Blo 1549472 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B2324921 : Blo 1549472 2324921 := bstep (se 2 (by rfl) ⟨871845, by rfl⟩ : syracuseStep 2324921 = 1743691) B1743691
theorem B3488201 : Blo 1549472 3488201 := bstep (se 2 (by rfl) ⟨1308075, by rfl⟩ : syracuseStep 3488201 = 2616151) B2616151
theorem B10066385 : Blo 1549472 10066385 := bstep (se 2 (by rfl) ⟨3774894, by rfl⟩ : syracuseStep 10066385 = 7549789) B7549789
theorem B1743367 : Blo 1549472 1743367 := bstep (se 1 (by rfl) ⟨1307525, by rfl⟩ : syracuseStep 1743367 = 2615051) B2615051
theorem B2324999 : Blo 1549472 2324999 := bstep (se 1 (by rfl) ⟨1743749, by rfl⟩ : syracuseStep 2324999 = 3487499) B3487499
theorem B3922465 : Blo 1549472 3922465 := bstep (se 2 (by rfl) ⟨1470924, by rfl⟩ : syracuseStep 3922465 = 2941849) B2941849
theorem B2325035 : Blo 1549472 2325035 := bstep (se 1 (by rfl) ⟨1743776, by rfl⟩ : syracuseStep 2325035 = 3487553) B3487553
theorem B2325065 : Blo 1549472 2325065 := bstep (se 2 (by rfl) ⟨871899, by rfl⟩ : syracuseStep 2325065 = 1743799) B1743799
theorem B1989239 : Blo 1549472 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B1743547 : Blo 1549472 1743547 := bstep (se 1 (by rfl) ⟨1307660, by rfl⟩ : syracuseStep 1743547 = 2615321) B2615321
theorem B2325179 : Blo 1549472 2325179 := bstep (se 1 (by rfl) ⟨1743884, by rfl⟩ : syracuseStep 2325179 = 3487769) B3487769
theorem B19872449 : Blo 1549472 19872449 := bstep (se 2 (by rfl) ⟨7452168, by rfl⟩ : syracuseStep 19872449 = 14904337) B14904337
theorem B2325239 : Blo 1549472 2325239 := bstep (se 1 (by rfl) ⟨1743929, by rfl⟩ : syracuseStep 2325239 = 3487859) B3487859
theorem B5233409 : Blo 1549472 5233409 := bstep (se 2 (by rfl) ⟨1962528, by rfl⟩ : syracuseStep 5233409 = 3925057) B3925057
theorem B2325263 : Blo 1549472 2325263 := bstep (se 1 (by rfl) ⟨1743947, by rfl⟩ : syracuseStep 2325263 = 3487895) B3487895
theorem B6626063 : Blo 1549472 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B5888801 : Blo 1549472 5888801 := bstep (se 2 (by rfl) ⟨2208300, by rfl⟩ : syracuseStep 5888801 = 4416601) B4416601
theorem B2325305 : Blo 1549472 2325305 := bstep (se 2 (by rfl) ⟨871989, by rfl⟩ : syracuseStep 2325305 = 1743979) B1743979
theorem B2325383 : Blo 1549472 2325383 := bstep (se 1 (by rfl) ⟨1744037, by rfl⟩ : syracuseStep 2325383 = 3488075) B3488075
theorem B29784995 : Blo 1549472 29784995 := bstep (se 1 (by rfl) ⟨22338746, by rfl⟩ : syracuseStep 29784995 = 44677493) B44677493
theorem B2325419 : Blo 1549472 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B2325449 : Blo 1549472 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B7167005 : Blo 1549472 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B7846955 : Blo 1549472 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B2325563 : Blo 1549472 2325563 := bstep (se 1 (by rfl) ⟨1744172, by rfl⟩ : syracuseStep 2325563 = 3488345) B3488345
theorem B3923063 : Blo 1549472 3923063 := bstep (se 1 (by rfl) ⟨2942297, by rfl⟩ : syracuseStep 3923063 = 5884595) B5884595
theorem B2325623 : Blo 1549472 2325623 := bstep (se 1 (by rfl) ⟨1744217, by rfl⟩ : syracuseStep 2325623 = 3488435) B3488435
theorem B3488903 : Blo 1549472 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B1744015 : Blo 1549472 1744015 := bstep (se 1 (by rfl) ⟨1308011, by rfl⟩ : syracuseStep 1744015 = 2616023) B2616023
theorem B2325647 : Blo 1549472 2325647 := bstep (se 1 (by rfl) ⟨1744235, by rfl⟩ : syracuseStep 2325647 = 3488471) B3488471
theorem B2358443 : Blo 1549472 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B2325689 : Blo 1549472 2325689 := bstep (se 2 (by rfl) ⟨872133, by rfl⟩ : syracuseStep 2325689 = 1744267) B1744267
theorem B2325767 : Blo 1549472 2325767 := bstep (se 1 (by rfl) ⟨1744325, by rfl⟩ : syracuseStep 2325767 = 3488651) B3488651
theorem B2096399 : Blo 1549472 2096399 := bstep (se 1 (by rfl) ⟨1572299, by rfl⟩ : syracuseStep 2096399 = 3144599) B3144599
theorem B8830241 : Blo 1549472 8830241 := bstep (se 2 (by rfl) ⟨3311340, by rfl⟩ : syracuseStep 8830241 = 6622681) B6622681
theorem B2325803 : Blo 1549472 2325803 := bstep (se 1 (by rfl) ⟨1744352, by rfl⟩ : syracuseStep 2325803 = 3488705) B3488705
theorem B3489083 : Blo 1549472 3489083 := bstep (se 1 (by rfl) ⟨2616812, by rfl⟩ : syracuseStep 3489083 = 5233625) B5233625
theorem B2325833 : Blo 1549472 2325833 := bstep (se 2 (by rfl) ⟨872187, by rfl⟩ : syracuseStep 2325833 = 1744375) B1744375
theorem B3726739 : Blo 1549472 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B3489209 : Blo 1549472 3489209 := bstep (se 2 (by rfl) ⟨1308453, by rfl⟩ : syracuseStep 3489209 = 2616907) B2616907
theorem B2325947 : Blo 1549472 2325947 := bstep (se 1 (by rfl) ⟨1744460, by rfl⟩ : syracuseStep 2325947 = 3488921) B3488921
theorem B2326007 : Blo 1549472 2326007 := bstep (se 1 (by rfl) ⟨1744505, by rfl⟩ : syracuseStep 2326007 = 3489011) B3489011
theorem B2326031 : Blo 1549472 2326031 := bstep (se 1 (by rfl) ⟨1744523, by rfl⟩ : syracuseStep 2326031 = 3489047) B3489047
theorem B5234219 : Blo 1549472 5234219 := bstep (se 1 (by rfl) ⟨3925664, by rfl⟩ : syracuseStep 5234219 = 7851329) B7851329
theorem B2326073 : Blo 1549472 2326073 := bstep (se 2 (by rfl) ⟨872277, by rfl⟩ : syracuseStep 2326073 = 1744555) B1744555
theorem B1744519 : Blo 1549472 1744519 := bstep (se 1 (by rfl) ⟨1308389, by rfl⟩ : syracuseStep 1744519 = 2616779) B2616779
theorem B2326151 : Blo 1549472 2326151 := bstep (se 1 (by rfl) ⟨1744613, by rfl⟩ : syracuseStep 2326151 = 3489227) B3489227
theorem B2326187 : Blo 1549472 2326187 := bstep (se 1 (by rfl) ⟨1744640, by rfl⟩ : syracuseStep 2326187 = 3489281) B3489281
theorem B2326217 : Blo 1549472 2326217 := bstep (se 2 (by rfl) ⟨872331, by rfl⟩ : syracuseStep 2326217 = 1744663) B1744663
theorem B5889773 : Blo 1549472 5889773 := bstep (se 3 (by rfl) ⟨1104332, by rfl⟩ : syracuseStep 5889773 = 2208665) B2208665
theorem B3489551 : Blo 1549472 3489551 := bstep (se 1 (by rfl) ⟨2617163, by rfl⟩ : syracuseStep 3489551 = 5234327) B5234327
theorem B3489569 : Blo 1549472 3489569 := bstep (se 2 (by rfl) ⟨1308588, by rfl⟩ : syracuseStep 3489569 = 2617177) B2617177
theorem B122543923 : Blo 1549472 122543923 := bstep (se 1 (by rfl) ⟨91907942, by rfl⟩ : syracuseStep 122543923 = 183815885) B183815885
theorem B1744699 : Blo 1549472 1744699 := bstep (se 1 (by rfl) ⟨1308524, by rfl⟩ : syracuseStep 1744699 = 2617049) B2617049
theorem B2326331 : Blo 1549472 2326331 := bstep (se 1 (by rfl) ⟨1744748, by rfl⟩ : syracuseStep 2326331 = 3489497) B3489497
theorem B2326391 : Blo 1549472 2326391 := bstep (se 1 (by rfl) ⟨1744793, by rfl⟩ : syracuseStep 2326391 = 3489587) B3489587
theorem B2326415 : Blo 1549472 2326415 := bstep (se 1 (by rfl) ⟨1744811, by rfl⟩ : syracuseStep 2326415 = 3489623) B3489623
theorem B4415417 : Blo 1549472 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B2326457 : Blo 1549472 2326457 := bstep (se 2 (by rfl) ⟨872421, by rfl⟩ : syracuseStep 2326457 = 1744843) B1744843
theorem B11780153 : Blo 1549472 11780153 := bstep (se 2 (by rfl) ⟨4417557, by rfl⟩ : syracuseStep 11780153 = 8835115) B8835115
theorem B2326607 : Blo 1549472 2326607 := bstep (se 1 (by rfl) ⟨1744955, by rfl⟩ : syracuseStep 2326607 = 3489911) B3489911
theorem B2326727 : Blo 1549472 2326727 := bstep (se 1 (by rfl) ⟨1745045, by rfl⟩ : syracuseStep 2326727 = 3490091) B3490091
theorem B1745095 : Blo 1549472 1745095 := bstep (se 1 (by rfl) ⟨1308821, by rfl⟩ : syracuseStep 1745095 = 2617643) B2617643
theorem B4415735 : Blo 1549472 4415735 := bstep (se 1 (by rfl) ⟨3311801, by rfl⟩ : syracuseStep 4415735 = 6623603) B6623603
theorem B2326889 : Blo 1549472 2326889 := bstep (se 2 (by rfl) ⟨872583, by rfl⟩ : syracuseStep 2326889 = 1745167) B1745167
theorem B2326967 : Blo 1549472 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B2327003 : Blo 1549472 2327003 := bstep (se 1 (by rfl) ⟨1745252, by rfl⟩ : syracuseStep 2327003 = 3490505) B3490505
theorem B3490343 : Blo 1549472 3490343 := bstep (se 1 (by rfl) ⟨2617757, by rfl⟩ : syracuseStep 3490343 = 5235515) B5235515
theorem B6709819 : Blo 1549472 6709819 := bstep (se 1 (by rfl) ⟨5032364, by rfl⟩ : syracuseStep 6709819 = 10064729) B10064729
theorem B7955003 : Blo 1549472 7955003 := bstep (se 1 (by rfl) ⟨5966252, by rfl⟩ : syracuseStep 7955003 = 11932505) B11932505
theorem B6046343 : Blo 1549472 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B5890745 : Blo 1549472 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B8831699 : Blo 1549472 8831699 := bstep (se 1 (by rfl) ⟨6623774, by rfl⟩ : syracuseStep 8831699 = 13247549) B13247549
theorem B7447403 : Blo 1549472 7447403 := bstep (se 1 (by rfl) ⟨5585552, by rfl⟩ : syracuseStep 7447403 = 11171105) B11171105
theorem B3490667 : Blo 1549472 3490667 := bstep (se 1 (by rfl) ⟨2618000, by rfl⟩ : syracuseStep 3490667 = 5236001) B5236001
theorem B3490721 : Blo 1549472 3490721 := bstep (se 2 (by rfl) ⟨1309020, by rfl⟩ : syracuseStep 3490721 = 2618041) B2618041
theorem B8946607 : Blo 1549472 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B5235731 : Blo 1549472 5235731 := bstep (se 1 (by rfl) ⟨3926798, by rfl⟩ : syracuseStep 5235731 = 7853597) B7853597
theorem B14902339 : Blo 1549472 14902339 := bstep (se 1 (by rfl) ⟨11176754, by rfl⟩ : syracuseStep 14902339 = 22353509) B22353509
theorem B1549487 : Blo 1549472 1549487 := bstep (se 1 (by rfl) ⟨1162115, by rfl⟩ : syracuseStep 1549487 = 2324231) B2324231
theorem B1549511 : Blo 1549472 1549511 := bstep (se 1 (by rfl) ⟨1162133, by rfl⟩ : syracuseStep 1549511 = 2324267) B2324267
theorem B9938123 : Blo 1549472 9938123 := bstep (se 1 (by rfl) ⟨7453592, by rfl⟩ : syracuseStep 9938123 = 14907185) B14907185
theorem B1549531 : Blo 1549472 1549531 := bstep (se 1 (by rfl) ⟨1162148, by rfl⟩ : syracuseStep 1549531 = 2324297) B2324297
theorem B1549607 : Blo 1549472 1549607 := bstep (se 1 (by rfl) ⟨1162205, by rfl⟩ : syracuseStep 1549607 = 2324411) B2324411
theorem B1549647 : Blo 1549472 1549647 := bstep (se 1 (by rfl) ⟨1162235, by rfl⟩ : syracuseStep 1549647 = 2324471) B2324471
theorem B5236055 : Blo 1549472 5236055 := bstep (se 1 (by rfl) ⟨3927041, by rfl⟩ : syracuseStep 5236055 = 7854083) B7854083
theorem B1549663 : Blo 1549472 1549663 := bstep (se 1 (by rfl) ⟨1162247, by rfl⟩ : syracuseStep 1549663 = 2324495) B2324495
theorem B1549691 : Blo 1549472 1549691 := bstep (se 1 (by rfl) ⟨1162268, by rfl⟩ : syracuseStep 1549691 = 2324537) B2324537
theorem B11773349 : Blo 1549472 11773349 := bstep (se 4 (by rfl) ⟨1103751, by rfl⟩ : syracuseStep 11773349 = 2207503) B2207503
theorem B1549743 : Blo 1549472 1549743 := bstep (se 1 (by rfl) ⟨1162307, by rfl⟩ : syracuseStep 1549743 = 2324615) B2324615
theorem B1549767 : Blo 1549472 1549767 := bstep (se 1 (by rfl) ⟨1162325, by rfl⟩ : syracuseStep 1549767 = 2324651) B2324651
theorem B2614747 : Blo 1549472 2614747 := bstep (se 1 (by rfl) ⟨1961060, by rfl⟩ : syracuseStep 2614747 = 3922121) B3922121
theorem B1549787 : Blo 1549472 1549787 := bstep (se 1 (by rfl) ⟨1162340, by rfl⟩ : syracuseStep 1549787 = 2324681) B2324681
theorem B5883425 : Blo 1549472 5883425 := bstep (se 2 (by rfl) ⟨2206284, by rfl⟩ : syracuseStep 5883425 = 4412569) B4412569
theorem B1549863 : Blo 1549472 1549863 := bstep (se 1 (by rfl) ⟨1162397, by rfl⟩ : syracuseStep 1549863 = 2324795) B2324795
theorem B3925543 : Blo 1549472 3925543 := bstep (se 1 (by rfl) ⟨2944157, by rfl⟩ : syracuseStep 3925543 = 5888315) B5888315
theorem B1549903 : Blo 1549472 1549903 := bstep (se 1 (by rfl) ⟨1162427, by rfl⟩ : syracuseStep 1549903 = 2324855) B2324855
theorem B1549919 : Blo 1549472 1549919 := bstep (se 1 (by rfl) ⟨1162439, by rfl⟩ : syracuseStep 1549919 = 2324879) B2324879
theorem B1549947 : Blo 1549472 1549947 := bstep (se 1 (by rfl) ⟨1162460, by rfl⟩ : syracuseStep 1549947 = 2324921) B2324921
theorem B6710923 : Blo 1549472 6710923 := bstep (se 1 (by rfl) ⟨5033192, by rfl⟩ : syracuseStep 6710923 = 10066385) B10066385
theorem B1549999 : Blo 1549472 1549999 := bstep (se 1 (by rfl) ⟨1162499, by rfl⟩ : syracuseStep 1549999 = 2324999) B2324999
theorem B1550023 : Blo 1549472 1550023 := bstep (se 1 (by rfl) ⟨1162517, by rfl⟩ : syracuseStep 1550023 = 2325035) B2325035
theorem B1550043 : Blo 1549472 1550043 := bstep (se 1 (by rfl) ⟨1162532, by rfl⟩ : syracuseStep 1550043 = 2325065) B2325065
theorem B31819513 : Blo 1549472 31819513 := bstep (se 2 (by rfl) ⟨11932317, by rfl⟩ : syracuseStep 31819513 = 23864635) B23864635
theorem B1550119 : Blo 1549472 1550119 := bstep (se 1 (by rfl) ⟨1162589, by rfl⟩ : syracuseStep 1550119 = 2325179) B2325179
theorem B13248299 : Blo 1549472 13248299 := bstep (se 1 (by rfl) ⟨9936224, by rfl⟩ : syracuseStep 13248299 = 19872449) B19872449
theorem B4966217 : Blo 1549472 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B1550159 : Blo 1549472 1550159 := bstep (se 1 (by rfl) ⟨1162619, by rfl⟩ : syracuseStep 1550159 = 2325239) B2325239
theorem B1550175 : Blo 1549472 1550175 := bstep (se 1 (by rfl) ⟨1162631, by rfl⟩ : syracuseStep 1550175 = 2325263) B2325263
theorem B12912493 : Blo 1549472 12912493 := bstep (se 3 (by rfl) ⟨2421092, by rfl⟩ : syracuseStep 12912493 = 4842185) B4842185
theorem B3925867 : Blo 1549472 3925867 := bstep (se 1 (by rfl) ⟨2944400, by rfl⟩ : syracuseStep 3925867 = 5888801) B5888801
theorem B1550203 : Blo 1549472 1550203 := bstep (se 1 (by rfl) ⟨1162652, by rfl⟩ : syracuseStep 1550203 = 2325305) B2325305
theorem B1550255 : Blo 1549472 1550255 := bstep (se 1 (by rfl) ⟨1162691, by rfl⟩ : syracuseStep 1550255 = 2325383) B2325383
theorem B4474807 : Blo 1549472 4474807 := bstep (se 1 (by rfl) ⟨3356105, by rfl⟩ : syracuseStep 4474807 = 6712211) B6712211
theorem B1550279 : Blo 1549472 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B1550299 : Blo 1549472 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B5883911 : Blo 1549472 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B4778003 : Blo 1549472 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B1550375 : Blo 1549472 1550375 := bstep (se 1 (by rfl) ⟨1162781, by rfl⟩ : syracuseStep 1550375 = 2325563) B2325563
theorem B2615375 : Blo 1549472 2615375 := bstep (se 1 (by rfl) ⟨1961531, by rfl⟩ : syracuseStep 2615375 = 3923063) B3923063
theorem B1550415 : Blo 1549472 1550415 := bstep (se 1 (by rfl) ⟨1162811, by rfl⟩ : syracuseStep 1550415 = 2325623) B2325623
theorem B1550431 : Blo 1549472 1550431 := bstep (se 1 (by rfl) ⟨1162823, by rfl⟩ : syracuseStep 1550431 = 2325647) B2325647
theorem B1550459 : Blo 1549472 1550459 := bstep (se 1 (by rfl) ⟨1162844, by rfl⟩ : syracuseStep 1550459 = 2325689) B2325689
theorem B1550511 : Blo 1549472 1550511 := bstep (se 1 (by rfl) ⟨1162883, by rfl⟩ : syracuseStep 1550511 = 2325767) B2325767
theorem B1550535 : Blo 1549472 1550535 := bstep (se 1 (by rfl) ⟨1162901, by rfl⟩ : syracuseStep 1550535 = 2325803) B2325803
theorem B1550555 : Blo 1549472 1550555 := bstep (se 1 (by rfl) ⟨1162916, by rfl⟩ : syracuseStep 1550555 = 2325833) B2325833
theorem B4966667 : Blo 1549472 4966667 := bstep (se 1 (by rfl) ⟨3725000, by rfl⟩ : syracuseStep 4966667 = 7450001) B7450001
theorem B1550631 : Blo 1549472 1550631 := bstep (se 1 (by rfl) ⟨1162973, by rfl⟩ : syracuseStep 1550631 = 2325947) B2325947
theorem B1550671 : Blo 1549472 1550671 := bstep (se 1 (by rfl) ⟨1163003, by rfl⟩ : syracuseStep 1550671 = 2326007) B2326007
theorem B1550687 : Blo 1549472 1550687 := bstep (se 1 (by rfl) ⟨1163015, by rfl⟩ : syracuseStep 1550687 = 2326031) B2326031
theorem B1550715 : Blo 1549472 1550715 := bstep (se 1 (by rfl) ⟨1163036, by rfl⟩ : syracuseStep 1550715 = 2326073) B2326073
theorem B163391897 : Blo 1549472 163391897 := bstep (se 2 (by rfl) ⟨61271961, by rfl⟩ : syracuseStep 163391897 = 122543923) B122543923
theorem B1550767 : Blo 1549472 1550767 := bstep (se 1 (by rfl) ⟨1163075, by rfl⟩ : syracuseStep 1550767 = 2326151) B2326151
theorem B1550791 : Blo 1549472 1550791 := bstep (se 1 (by rfl) ⟨1163093, by rfl⟩ : syracuseStep 1550791 = 2326187) B2326187
theorem B1550811 : Blo 1549472 1550811 := bstep (se 1 (by rfl) ⟨1163108, by rfl⟩ : syracuseStep 1550811 = 2326217) B2326217
theorem B5884397 : Blo 1549472 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B3926515 : Blo 1549472 3926515 := bstep (se 1 (by rfl) ⟨2944886, by rfl⟩ : syracuseStep 3926515 = 5889773) B5889773
theorem B1550887 : Blo 1549472 1550887 := bstep (se 1 (by rfl) ⟨1163165, by rfl⟩ : syracuseStep 1550887 = 2326331) B2326331
theorem B1550927 : Blo 1549472 1550927 := bstep (se 1 (by rfl) ⟨1163195, by rfl⟩ : syracuseStep 1550927 = 2326391) B2326391
theorem B1550943 : Blo 1549472 1550943 := bstep (se 1 (by rfl) ⟨1163207, by rfl⟩ : syracuseStep 1550943 = 2326415) B2326415
theorem B2943611 : Blo 1549472 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B1550971 : Blo 1549472 1550971 := bstep (se 1 (by rfl) ⟨1163228, by rfl⟩ : syracuseStep 1550971 = 2326457) B2326457
theorem B1551023 : Blo 1549472 1551023 := bstep (se 1 (by rfl) ⟨1163267, by rfl⟩ : syracuseStep 1551023 = 2326535) B2326535
theorem B7850681 : Blo 1549472 7850681 := bstep (se 2 (by rfl) ⟨2944005, by rfl⟩ : syracuseStep 7850681 = 5888011) B5888011
theorem B1551047 : Blo 1549472 1551047 := bstep (se 1 (by rfl) ⟨1163285, by rfl⟩ : syracuseStep 1551047 = 2326571) B2326571
theorem B1551067 : Blo 1549472 1551067 := bstep (se 1 (by rfl) ⟨1163300, by rfl⟩ : syracuseStep 1551067 = 2326601) B2326601
theorem B1551143 : Blo 1549472 1551143 := bstep (se 1 (by rfl) ⟨1163357, by rfl⟩ : syracuseStep 1551143 = 2326715) B2326715
theorem B1551183 : Blo 1549472 1551183 := bstep (se 1 (by rfl) ⟨1163387, by rfl⟩ : syracuseStep 1551183 = 2326775) B2326775
theorem B2943839 : Blo 1549472 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B1551199 : Blo 1549472 1551199 := bstep (se 1 (by rfl) ⟨1163399, by rfl⟩ : syracuseStep 1551199 = 2326799) B2326799
theorem B1551227 : Blo 1549472 1551227 := bstep (se 1 (by rfl) ⟨1163420, by rfl⟩ : syracuseStep 1551227 = 2326841) B2326841
theorem B2616239 : Blo 1549472 2616239 := bstep (se 1 (by rfl) ⟨1962179, by rfl⟩ : syracuseStep 2616239 = 3924359) B3924359
theorem B5589935 : Blo 1549472 5589935 := bstep (se 1 (by rfl) ⟨4192451, by rfl⟩ : syracuseStep 5589935 = 8384903) B8384903
theorem B1551279 : Blo 1549472 1551279 := bstep (se 1 (by rfl) ⟨1163459, by rfl⟩ : syracuseStep 1551279 = 2326919) B2326919
theorem B3312571 : Blo 1549472 3312571 := bstep (se 1 (by rfl) ⟨2484428, by rfl⟩ : syracuseStep 3312571 = 4968857) B4968857
theorem B1551303 : Blo 1549472 1551303 := bstep (se 1 (by rfl) ⟨1163477, by rfl⟩ : syracuseStep 1551303 = 2326955) B2326955
theorem B1551323 : Blo 1549472 1551323 := bstep (se 1 (by rfl) ⟨1163492, by rfl⟩ : syracuseStep 1551323 = 2326985) B2326985
theorem B5229575 : Blo 1549472 5229575 := bstep (se 1 (by rfl) ⟨3922181, by rfl⟩ : syracuseStep 5229575 = 7844363) B7844363
theorem B1551399 : Blo 1549472 1551399 := bstep (se 1 (by rfl) ⟨1163549, by rfl⟩ : syracuseStep 1551399 = 2327099) B2327099
theorem B1551439 : Blo 1549472 1551439 := bstep (se 1 (by rfl) ⟨1163579, by rfl⟩ : syracuseStep 1551439 = 2327159) B2327159
theorem B1551455 : Blo 1549472 1551455 := bstep (se 1 (by rfl) ⟨1163591, by rfl⟩ : syracuseStep 1551455 = 2327183) B2327183
theorem B2944097 : Blo 1549472 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B5229683 : Blo 1549472 5229683 := bstep (se 1 (by rfl) ⟨3922262, by rfl⟩ : syracuseStep 5229683 = 7844525) B7844525
theorem B5885081 : Blo 1549472 5885081 := bstep (se 2 (by rfl) ⟨2206905, by rfl⟩ : syracuseStep 5885081 = 4413811) B4413811
theorem B9940121 : Blo 1549472 9940121 := bstep (se 2 (by rfl) ⟨3727545, by rfl⟩ : syracuseStep 9940121 = 7455091) B7455091
theorem B11767031 : Blo 1549472 11767031 := bstep (se 1 (by rfl) ⟨8825273, by rfl⟩ : syracuseStep 11767031 = 17650547) B17650547
theorem B2616671 : Blo 1549472 2616671 := bstep (se 1 (by rfl) ⟨1962503, by rfl⟩ : syracuseStep 2616671 = 3925007) B3925007
theorem B2944363 : Blo 1549472 2944363 := bstep (se 1 (by rfl) ⟨2208272, by rfl⟩ : syracuseStep 2944363 = 4416545) B4416545
theorem B5590397 : Blo 1549472 5590397 := bstep (se 3 (by rfl) ⟨1048199, by rfl⟩ : syracuseStep 5590397 = 2096399) B2096399
theorem B5229953 : Blo 1549472 5229953 := bstep (se 2 (by rfl) ⟨1961232, by rfl⟩ : syracuseStep 5229953 = 3922465) B3922465
theorem B1961435 : Blo 1549472 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B50998859 : Blo 1549472 50998859 := bstep (se 1 (by rfl) ⟨38249144, by rfl⟩ : syracuseStep 50998859 = 76498289) B76498289
theorem B11767517 : Blo 1549472 11767517 := bstep (se 3 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 11767517 = 4412819) B4412819
theorem B2617231 : Blo 1549472 2617231 := bstep (se 1 (by rfl) ⟨1962923, by rfl⟩ : syracuseStep 2617231 = 3925847) B3925847
theorem B1961911 : Blo 1549472 1961911 := bstep (se 1 (by rfl) ⟨1471433, by rfl⟩ : syracuseStep 1961911 = 2942867) B2942867
theorem B7450555 : Blo 1549472 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B7172027 : Blo 1549472 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B7450631 : Blo 1549472 7450631 := bstep (se 1 (by rfl) ⟨5587973, by rfl⟩ : syracuseStep 7450631 = 11175947) B11175947
theorem B11177999 : Blo 1549472 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B5886067 : Blo 1549472 5886067 := bstep (se 1 (by rfl) ⟨4414550, by rfl⟩ : syracuseStep 5886067 = 8829101) B8829101
theorem B5230763 : Blo 1549472 5230763 := bstep (se 1 (by rfl) ⟨3923072, by rfl⟩ : syracuseStep 5230763 = 7846145) B7846145
theorem B5304637 : Blo 1549472 5304637 := bstep (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) B1989239
theorem B8835389 : Blo 1549472 8835389 := bstep (se 3 (by rfl) ⟨1656635, by rfl⟩ : syracuseStep 8835389 = 3313271) B3313271
theorem B2208107 : Blo 1549472 2208107 := bstep (se 1 (by rfl) ⟨1656080, by rfl⟩ : syracuseStep 2208107 = 3312161) B3312161
theorem B17666585 : Blo 1549472 17666585 := bstep (se 2 (by rfl) ⟨6624969, by rfl⟩ : syracuseStep 17666585 = 13249939) B13249939
theorem B4968985 : Blo 1549472 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B2617913 : Blo 1549472 2617913 := bstep (se 2 (by rfl) ⟨981717, by rfl⟩ : syracuseStep 2617913 = 1963435) B1963435
theorem B5231303 : Blo 1549472 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B3486419 : Blo 1549472 3486419 := bstep (se 1 (by rfl) ⟨2614814, by rfl⟩ : syracuseStep 3486419 = 5229629) B5229629
theorem B5886827 : Blo 1549472 5886827 := bstep (se 1 (by rfl) ⟨4415120, by rfl⟩ : syracuseStep 5886827 = 8830241) B8830241
theorem B28677017 : Blo 1549472 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B1553351 : Blo 1549472 1553351 := bstep (se 1 (by rfl) ⟨1165013, by rfl⟩ : syracuseStep 1553351 = 2330027) B2330027
theorem B8828099 : Blo 1549472 8828099 := bstep (se 1 (by rfl) ⟨6621074, by rfl⟩ : syracuseStep 8828099 = 13242149) B13242149
theorem B1963207 : Blo 1549472 1963207 := bstep (se 1 (by rfl) ⟨1472405, by rfl⟩ : syracuseStep 1963207 = 2944811) B2944811
theorem B3978487 : Blo 1549472 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B39720293 : Blo 1549472 39720293 := bstep (se 4 (by rfl) ⟨3723777, by rfl⟩ : syracuseStep 39720293 = 7447555) B7447555
theorem B36271601 : Blo 1549472 36271601 := bstep (se 2 (by rfl) ⟨13601850, by rfl⟩ : syracuseStep 36271601 = 27203701) B27203701
theorem B5232167 : Blo 1549472 5232167 := bstep (se 1 (by rfl) ⟨3924125, by rfl⟩ : syracuseStep 5232167 = 7848251) B7848251
theorem B214873661 : Blo 1549472 214873661 := bstep (se 3 (by rfl) ⟨40288811, by rfl⟩ : syracuseStep 214873661 = 80577623) B80577623
theorem B48420413 : Blo 1549472 48420413 := bstep (se 3 (by rfl) ⟨9078827, by rfl⟩ : syracuseStep 48420413 = 18157655) B18157655
theorem B9934433 : Blo 1549472 9934433 := bstep (se 2 (by rfl) ⟨3725412, by rfl⟩ : syracuseStep 9934433 = 7450825) B7450825
theorem B3487355 : Blo 1549472 3487355 := bstep (se 1 (by rfl) ⟨2615516, by rfl⟩ : syracuseStep 3487355 = 5231033) B5231033
theorem B8066699 : Blo 1549472 8066699 := bstep (se 1 (by rfl) ⟨6050024, by rfl⟩ : syracuseStep 8066699 = 12100049) B12100049
theorem B5232275 : Blo 1549472 5232275 := bstep (se 1 (by rfl) ⟨3924206, by rfl⟩ : syracuseStep 5232275 = 7848413) B7848413
theorem B7952093 : Blo 1549472 7952093 := bstep (se 3 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 7952093 = 2982035) B2982035
theorem B3487481 : Blo 1549472 3487481 := bstep (se 2 (by rfl) ⟨1307805, by rfl⟩ : syracuseStep 3487481 = 2615611) B2615611
theorem B6289181 : Blo 1549472 6289181 := bstep (se 3 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 6289181 = 2358443) B2358443
theorem B6625091 : Blo 1549472 6625091 := bstep (se 1 (by rfl) ⟨4968818, by rfl⟩ : syracuseStep 6625091 = 9937637) B9937637
theorem B5232491 : Blo 1549472 5232491 := bstep (se 1 (by rfl) ⟨3924368, by rfl⟩ : syracuseStep 5232491 = 7848737) B7848737
theorem B5232545 : Blo 1549472 5232545 := bstep (se 2 (by rfl) ⟨1962204, by rfl⟩ : syracuseStep 5232545 = 3924409) B3924409
theorem B2324399 : Blo 1549472 2324399 := bstep (se 1 (by rfl) ⟨1743299, by rfl⟩ : syracuseStep 2324399 = 3486599) B3486599
theorem B3487751 : Blo 1549472 3487751 := bstep (se 1 (by rfl) ⟨2615813, by rfl⟩ : syracuseStep 3487751 = 5231627) B5231627
theorem B2324489 : Blo 1549472 2324489 := bstep (se 2 (by rfl) ⟨871683, by rfl⟩ : syracuseStep 2324489 = 1743367) B1743367
theorem B2324519 : Blo 1549472 2324519 := bstep (se 1 (by rfl) ⟨1743389, by rfl⟩ : syracuseStep 2324519 = 3486779) B3486779
theorem B3487823 : Blo 1549472 3487823 := bstep (se 1 (by rfl) ⟨2615867, by rfl⟩ : syracuseStep 3487823 = 5231735) B5231735
theorem B2324603 : Blo 1549472 2324603 := bstep (se 1 (by rfl) ⟨1743452, by rfl⟩ : syracuseStep 2324603 = 3486905) B3486905
theorem B2324729 : Blo 1549472 2324729 := bstep (se 2 (by rfl) ⟨871773, by rfl⟩ : syracuseStep 2324729 = 1743547) B1743547
theorem B6289751 : Blo 1549472 6289751 := bstep (se 1 (by rfl) ⟨4717313, by rfl⟩ : syracuseStep 6289751 = 9434627) B9434627
theorem B2324831 : Blo 1549472 2324831 := bstep (se 1 (by rfl) ⟨1743623, by rfl⟩ : syracuseStep 2324831 = 3487247) B3487247
theorem B2324843 : Blo 1549472 2324843 := bstep (se 1 (by rfl) ⟨1743632, by rfl⟩ : syracuseStep 2324843 = 3487265) B3487265
theorem B3488219 : Blo 1549472 3488219 := bstep (se 1 (by rfl) ⟨2616164, by rfl⟩ : syracuseStep 3488219 = 5232329) B5232329
theorem B5233139 : Blo 1549472 5233139 := bstep (se 1 (by rfl) ⟨3924854, by rfl⟩ : syracuseStep 5233139 = 7849709) B7849709
theorem B11328025 : Blo 1549472 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B7084577 : Blo 1549472 7084577 := bstep (se 2 (by rfl) ⟨2656716, by rfl⟩ : syracuseStep 7084577 = 5313433) B5313433
theorem B1743439 : Blo 1549472 1743439 := bstep (se 1 (by rfl) ⟨1307579, by rfl⟩ : syracuseStep 1743439 = 2615159) B2615159
theorem B2325071 : Blo 1549472 2325071 := bstep (se 1 (by rfl) ⟨1743803, by rfl⟩ : syracuseStep 2325071 = 3487607) B3487607
theorem B11172487 : Blo 1549472 11172487 := bstep (se 1 (by rfl) ⟨8379365, by rfl⟩ : syracuseStep 11172487 = 16758731) B16758731
theorem B11778695 : Blo 1549472 11778695 := bstep (se 1 (by rfl) ⟨8834021, by rfl⟩ : syracuseStep 11778695 = 17668043) B17668043
theorem B11328173 : Blo 1549472 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B8379065 : Blo 1549472 8379065 := bstep (se 2 (by rfl) ⟨3142149, by rfl⟩ : syracuseStep 8379065 = 6284299) B6284299
theorem B2325191 : Blo 1549472 2325191 := bstep (se 1 (by rfl) ⟨1743893, by rfl⟩ : syracuseStep 2325191 = 3487787) B3487787
theorem B3144403 : Blo 1549472 3144403 := bstep (se 1 (by rfl) ⟨2358302, by rfl⟩ : syracuseStep 3144403 = 4716605) B4716605
theorem B6290219 : Blo 1549472 6290219 := bstep (se 1 (by rfl) ⟨4717664, by rfl⟩ : syracuseStep 6290219 = 9435329) B9435329
theorem B2325353 : Blo 1549472 2325353 := bstep (se 2 (by rfl) ⟨872007, by rfl⟩ : syracuseStep 2325353 = 1744015) B1744015
theorem B3488687 : Blo 1549472 3488687 := bstep (se 1 (by rfl) ⟨2616515, by rfl⟩ : syracuseStep 3488687 = 5233031) B5233031
theorem B2325431 : Blo 1549472 2325431 := bstep (se 1 (by rfl) ⟨1744073, by rfl⟩ : syracuseStep 2325431 = 3488147) B3488147
theorem B12598199 : Blo 1549472 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B1743835 : Blo 1549472 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B2325467 : Blo 1549472 2325467 := bstep (se 1 (by rfl) ⟨1744100, by rfl⟩ : syracuseStep 2325467 = 3488201) B3488201
theorem B3922951 : Blo 1549472 3922951 := bstep (se 1 (by rfl) ⟨2942213, by rfl⟩ : syracuseStep 3922951 = 5884427) B5884427
theorem B5233679 : Blo 1549472 5233679 := bstep (se 1 (by rfl) ⟨3925259, by rfl⟩ : syracuseStep 5233679 = 7850519) B7850519
theorem B8068115 : Blo 1549472 8068115 := bstep (se 1 (by rfl) ⟨6051086, by rfl⟩ : syracuseStep 8068115 = 12102173) B12102173
theorem B3488939 : Blo 1549472 3488939 := bstep (se 1 (by rfl) ⟨2616704, by rfl⟩ : syracuseStep 3488939 = 5233409) B5233409
theorem B19856663 : Blo 1549472 19856663 := bstep (se 1 (by rfl) ⟨14892497, by rfl⟩ : syracuseStep 19856663 = 29784995) B29784995
theorem B17669501 : Blo 1549472 17669501 := bstep (se 3 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 17669501 = 6626063) B6626063
theorem B13245839 : Blo 1549472 13245839 := bstep (se 1 (by rfl) ⟨9934379, by rfl⟩ : syracuseStep 13245839 = 19868759) B19868759
theorem B1744303 : Blo 1549472 1744303 := bstep (se 1 (by rfl) ⟨1308227, by rfl⟩ : syracuseStep 1744303 = 2616455) B2616455
theorem B2325935 : Blo 1549472 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B2326025 : Blo 1549472 2326025 := bstep (se 2 (by rfl) ⟨872259, by rfl⟩ : syracuseStep 2326025 = 1744519) B1744519
theorem B2326055 : Blo 1549472 2326055 := bstep (se 1 (by rfl) ⟨1744541, by rfl⟩ : syracuseStep 2326055 = 3489083) B3489083
theorem B5234273 : Blo 1549472 5234273 := bstep (se 2 (by rfl) ⟨1962852, by rfl⟩ : syracuseStep 5234273 = 3925705) B3925705
theorem B3923579 : Blo 1549472 3923579 := bstep (se 1 (by rfl) ⟨2942684, by rfl⟩ : syracuseStep 3923579 = 5885369) B5885369
theorem B2326139 : Blo 1549472 2326139 := bstep (se 1 (by rfl) ⟨1744604, by rfl⟩ : syracuseStep 2326139 = 3489209) B3489209
theorem B6627005 : Blo 1549472 6627005 := bstep (se 3 (by rfl) ⟨1242563, by rfl⟩ : syracuseStep 6627005 = 2485127) B2485127
theorem B3489479 : Blo 1549472 3489479 := bstep (se 1 (by rfl) ⟨2617109, by rfl⟩ : syracuseStep 3489479 = 5234219) B5234219
theorem B5037767 : Blo 1549472 5037767 := bstep (se 1 (by rfl) ⟨3778325, by rfl⟩ : syracuseStep 5037767 = 7556651) B7556651
theorem B2793209 : Blo 1549472 2793209 := bstep (se 2 (by rfl) ⟨1047453, by rfl⟩ : syracuseStep 2793209 = 2094907) B2094907
theorem B2326265 : Blo 1549472 2326265 := bstep (se 2 (by rfl) ⟨872349, by rfl⟩ : syracuseStep 2326265 = 1744699) B1744699
theorem B1744735 : Blo 1549472 1744735 := bstep (se 1 (by rfl) ⟨1308551, by rfl⟩ : syracuseStep 1744735 = 2617103) B2617103
theorem B2326367 : Blo 1549472 2326367 := bstep (se 1 (by rfl) ⟨1744775, by rfl⟩ : syracuseStep 2326367 = 3489551) B3489551
theorem B2326379 : Blo 1549472 2326379 := bstep (se 1 (by rfl) ⟨1744784, by rfl⟩ : syracuseStep 2326379 = 3489569) B3489569
theorem B3923873 : Blo 1549472 3923873 := bstep (se 2 (by rfl) ⟨1471452, by rfl⟩ : syracuseStep 3923873 = 2942905) B2942905
theorem B2482103 : Blo 1549472 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B7848089 : Blo 1549472 7848089 := bstep (se 2 (by rfl) ⟨2943033, by rfl⟩ : syracuseStep 7848089 = 5886067) B5886067
theorem B5890259 : Blo 1549472 5890259 := bstep (se 1 (by rfl) ⟨4417694, by rfl⟩ : syracuseStep 5890259 = 8835389) B8835389
theorem B2326793 : Blo 1549472 2326793 := bstep (se 2 (by rfl) ⟨872547, by rfl⟩ : syracuseStep 2326793 = 1745095) B1745095
theorem B2326895 : Blo 1549472 2326895 := bstep (se 1 (by rfl) ⟨1745171, by rfl⟩ : syracuseStep 2326895 = 3490343) B3490343
theorem B1745275 : Blo 1549472 1745275 := bstep (se 1 (by rfl) ⟨1308956, by rfl⟩ : syracuseStep 1745275 = 2617913) B2617913
theorem B4030895 : Blo 1549472 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B4964935 : Blo 1549472 4964935 := bstep (se 1 (by rfl) ⟨3723701, by rfl⟩ : syracuseStep 4964935 = 7447403) B7447403
theorem B3924551 : Blo 1549472 3924551 := bstep (se 1 (by rfl) ⟨2943413, by rfl⟩ : syracuseStep 3924551 = 5886827) B5886827
theorem B2327111 : Blo 1549472 2327111 := bstep (se 1 (by rfl) ⟨1745333, by rfl⟩ : syracuseStep 2327111 = 3490667) B3490667
theorem B2327147 : Blo 1549472 2327147 := bstep (se 1 (by rfl) ⟨1745360, by rfl⟩ : syracuseStep 2327147 = 3490721) B3490721
theorem B5235353 : Blo 1549472 5235353 := bstep (se 2 (by rfl) ⟨1963257, by rfl⟩ : syracuseStep 5235353 = 3926515) B3926515
theorem B3490487 : Blo 1549472 3490487 := bstep (se 1 (by rfl) ⟨2617865, by rfl⟩ : syracuseStep 3490487 = 5235731) B5235731
theorem B8946425 : Blo 1549472 8946425 := bstep (se 2 (by rfl) ⟨3354909, by rfl⟩ : syracuseStep 8946425 = 6709819) B6709819
theorem B3490703 : Blo 1549472 3490703 := bstep (se 1 (by rfl) ⟨2618027, by rfl⟩ : syracuseStep 3490703 = 5236055) B5236055
theorem B7848899 : Blo 1549472 7848899 := bstep (se 1 (by rfl) ⟨5886674, by rfl⟩ : syracuseStep 7848899 = 11773349) B11773349
theorem B16770149 : Blo 1549472 16770149 := bstep (se 4 (by rfl) ⟨1572201, by rfl⟩ : syracuseStep 16770149 = 3144403) B3144403
theorem B5301395 : Blo 1549472 5301395 := bstep (se 1 (by rfl) ⟨3976046, by rfl⟩ : syracuseStep 5301395 = 7952093) B7952093
theorem B8832199 : Blo 1549472 8832199 := bstep (se 1 (by rfl) ⟨6624149, by rfl⟩ : syracuseStep 8832199 = 13248299) B13248299
theorem B4416727 : Blo 1549472 4416727 := bstep (se 1 (by rfl) ⟨3312545, by rfl⟩ : syracuseStep 4416727 = 6625091) B6625091
theorem B3310811 : Blo 1549472 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B11928809 : Blo 1549472 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B4416761 : Blo 1549472 4416761 := bstep (se 2 (by rfl) ⟨1656285, by rfl⟩ : syracuseStep 4416761 = 3312571) B3312571
theorem B1549599 : Blo 1549472 1549599 := bstep (se 1 (by rfl) ⟨1162199, by rfl⟩ : syracuseStep 1549599 = 2324399) B2324399
theorem B1549659 : Blo 1549472 1549659 := bstep (se 1 (by rfl) ⟨1162244, by rfl⟩ : syracuseStep 1549659 = 2324489) B2324489
theorem B1549679 : Blo 1549472 1549679 := bstep (se 1 (by rfl) ⟨1162259, by rfl⟩ : syracuseStep 1549679 = 2324519) B2324519
theorem B1549735 : Blo 1549472 1549735 := bstep (se 1 (by rfl) ⟨1162301, by rfl⟩ : syracuseStep 1549735 = 2324603) B2324603
theorem B1549819 : Blo 1549472 1549819 := bstep (se 1 (by rfl) ⟨1162364, by rfl⟩ : syracuseStep 1549819 = 2324729) B2324729
theorem B3311111 : Blo 1549472 3311111 := bstep (se 1 (by rfl) ⟨2483333, by rfl⟩ : syracuseStep 3311111 = 4966667) B4966667
theorem B1549887 : Blo 1549472 1549887 := bstep (se 1 (by rfl) ⟨1162415, by rfl⟩ : syracuseStep 1549887 = 2324831) B2324831
theorem B1549895 : Blo 1549472 1549895 := bstep (se 1 (by rfl) ⟨1162421, by rfl⟩ : syracuseStep 1549895 = 2324843) B2324843
theorem B1550047 : Blo 1549472 1550047 := bstep (se 1 (by rfl) ⟨1162535, by rfl⟩ : syracuseStep 1550047 = 2325071) B2325071
theorem B1550127 : Blo 1549472 1550127 := bstep (se 1 (by rfl) ⟨1162595, by rfl⟩ : syracuseStep 1550127 = 2325191) B2325191
theorem B3925817 : Blo 1549472 3925817 := bstep (se 2 (by rfl) ⟨1472181, by rfl⟩ : syracuseStep 3925817 = 2944363) B2944363
theorem B1550235 : Blo 1549472 1550235 := bstep (se 1 (by rfl) ⟨1162676, by rfl⟩ : syracuseStep 1550235 = 2325353) B2325353
theorem B1550287 : Blo 1549472 1550287 := bstep (se 1 (by rfl) ⟨1162715, by rfl⟩ : syracuseStep 1550287 = 2325431) B2325431
theorem B8398799 : Blo 1549472 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B1550311 : Blo 1549472 1550311 := bstep (se 1 (by rfl) ⟨1162733, by rfl⟩ : syracuseStep 1550311 = 2325467) B2325467
theorem B7448557 : Blo 1549472 7448557 := bstep (se 3 (by rfl) ⟨1396604, by rfl⟩ : syracuseStep 7448557 = 2793209) B2793209
theorem B8947897 : Blo 1549472 8947897 := bstep (se 2 (by rfl) ⟨3355461, by rfl⟩ : syracuseStep 8947897 = 6710923) B6710923
theorem B1550623 : Blo 1549472 1550623 := bstep (se 1 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 1550623 = 2325935) B2325935
theorem B23865637 : Blo 1549472 23865637 := bstep (se 4 (by rfl) ⟨2237403, by rfl⟩ : syracuseStep 23865637 = 4474807) B4474807
theorem B1550683 : Blo 1549472 1550683 := bstep (se 1 (by rfl) ⟨1163012, by rfl⟩ : syracuseStep 1550683 = 2326025) B2326025
theorem B1550703 : Blo 1549472 1550703 := bstep (se 1 (by rfl) ⟨1163027, by rfl⟩ : syracuseStep 1550703 = 2326055) B2326055
theorem B33999239 : Blo 1549472 33999239 := bstep (se 1 (by rfl) ⟨25499429, by rfl⟩ : syracuseStep 33999239 = 50998859) B50998859
theorem B2615719 : Blo 1549472 2615719 := bstep (se 1 (by rfl) ⟨1961789, by rfl⟩ : syracuseStep 2615719 = 3923579) B3923579
theorem B1550759 : Blo 1549472 1550759 := bstep (se 1 (by rfl) ⟨1163069, by rfl⟩ : syracuseStep 1550759 = 2326139) B2326139
theorem B4418003 : Blo 1549472 4418003 := bstep (se 1 (by rfl) ⟨3313502, by rfl⟩ : syracuseStep 4418003 = 6627005) B6627005
theorem B1550843 : Blo 1549472 1550843 := bstep (se 1 (by rfl) ⟨1163132, by rfl⟩ : syracuseStep 1550843 = 2326265) B2326265
theorem B1550911 : Blo 1549472 1550911 := bstep (se 1 (by rfl) ⟨1163183, by rfl⟩ : syracuseStep 1550911 = 2326367) B2326367
theorem B1550919 : Blo 1549472 1550919 := bstep (se 1 (by rfl) ⟨1163189, by rfl⟩ : syracuseStep 1550919 = 2326379) B2326379
theorem B2615881 : Blo 1549472 2615881 := bstep (se 2 (by rfl) ⟨980955, by rfl⟩ : syracuseStep 2615881 = 1961911) B1961911
theorem B2615915 : Blo 1549472 2615915 := bstep (se 1 (by rfl) ⟨1961936, by rfl⟩ : syracuseStep 2615915 = 3923873) B3923873
theorem B4967087 : Blo 1549472 4967087 := bstep (se 1 (by rfl) ⟨3725315, by rfl⟩ : syracuseStep 4967087 = 7450631) B7450631
theorem B1551071 : Blo 1549472 1551071 := bstep (se 1 (by rfl) ⟨1163303, by rfl⟩ : syracuseStep 1551071 = 2326607) B2326607
theorem B1551151 : Blo 1549472 1551151 := bstep (se 1 (by rfl) ⟨1163363, by rfl⟩ : syracuseStep 1551151 = 2326727) B2326727
theorem B1551259 : Blo 1549472 1551259 := bstep (se 1 (by rfl) ⟨1163444, by rfl⟩ : syracuseStep 1551259 = 2326889) B2326889
theorem B1551311 : Blo 1549472 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B1551335 : Blo 1549472 1551335 := bstep (se 1 (by rfl) ⟨1163501, by rfl⟩ : syracuseStep 1551335 = 2327003) B2327003
theorem B5303335 : Blo 1549472 5303335 := bstep (se 1 (by rfl) ⟨3977501, by rfl⟩ : syracuseStep 5303335 = 7955003) B7955003
theorem B7072849 : Blo 1549472 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B3927163 : Blo 1549472 3927163 := bstep (se 1 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 3927163 = 5890745) B5890745
theorem B11775293 : Blo 1549472 11775293 := bstep (se 3 (by rfl) ⟨2207867, by rfl⟩ : syracuseStep 11775293 = 4415735) B4415735
theorem B5885399 : Blo 1549472 5885399 := bstep (se 1 (by rfl) ⟨4414049, by rfl⟩ : syracuseStep 5885399 = 8828099) B8828099
theorem B14896649 : Blo 1549472 14896649 := bstep (se 2 (by rfl) ⟨5586243, by rfl⟩ : syracuseStep 14896649 = 11172487) B11172487
theorem B26480195 : Blo 1549472 26480195 := bstep (se 1 (by rfl) ⟨19860146, by rfl⟩ : syracuseStep 26480195 = 39720293) B39720293
theorem B32280275 : Blo 1549472 32280275 := bstep (se 1 (by rfl) ⟨24210206, by rfl⟩ : syracuseStep 32280275 = 48420413) B48420413
theorem B6622955 : Blo 1549472 6622955 := bstep (se 1 (by rfl) ⟨4967216, by rfl⟩ : syracuseStep 6622955 = 9934433) B9934433
theorem B5377799 : Blo 1549472 5377799 := bstep (se 1 (by rfl) ⟨4033349, by rfl⟩ : syracuseStep 5377799 = 8066699) B8066699
theorem B5230493 : Blo 1549472 5230493 := bstep (se 3 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 5230493 = 1961435) B1961435
theorem B5230601 : Blo 1549472 5230601 := bstep (se 2 (by rfl) ⟨1961475, by rfl⟩ : syracuseStep 5230601 = 3922951) B3922951
theorem B19869785 : Blo 1549472 19869785 := bstep (se 2 (by rfl) ⟨7451169, by rfl⟩ : syracuseStep 19869785 = 14902339) B14902339
theorem B2617609 : Blo 1549472 2617609 := bstep (se 2 (by rfl) ⟨981603, by rfl⟩ : syracuseStep 2617609 = 1963207) B1963207
theorem B5304649 : Blo 1549472 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B4723051 : Blo 1549472 4723051 := bstep (se 1 (by rfl) ⟨3542288, by rfl⟩ : syracuseStep 4723051 = 7084577) B7084577
theorem B1962407 : Blo 1549472 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B7852463 : Blo 1549472 7852463 := bstep (se 1 (by rfl) ⟨5889347, by rfl⟩ : syracuseStep 7852463 = 11778695) B11778695
theorem B1962559 : Blo 1549472 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B3486329 : Blo 1549472 3486329 := bstep (se 2 (by rfl) ⟨1307373, by rfl⟩ : syracuseStep 3486329 = 2614747) B2614747
theorem B3486383 : Blo 1549472 3486383 := bstep (se 1 (by rfl) ⟨2614787, by rfl⟩ : syracuseStep 3486383 = 5229575) B5229575
theorem B5378743 : Blo 1549472 5378743 := bstep (se 1 (by rfl) ⟨4034057, by rfl⟩ : syracuseStep 5378743 = 8068115) B8068115
theorem B1962731 : Blo 1549472 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B3486455 : Blo 1549472 3486455 := bstep (se 1 (by rfl) ⟨2614841, by rfl⟩ : syracuseStep 3486455 = 5229683) B5229683
theorem B7844687 : Blo 1549472 7844687 := bstep (se 1 (by rfl) ⟨5883515, by rfl⟩ : syracuseStep 7844687 = 11767031) B11767031
theorem B3486635 : Blo 1549472 3486635 := bstep (se 1 (by rfl) ⟨2614976, by rfl⟩ : syracuseStep 3486635 = 5229953) B5229953
theorem B17216657 : Blo 1549472 17216657 := bstep (se 2 (by rfl) ⟨6456246, by rfl⟩ : syracuseStep 17216657 = 12912493) B12912493
theorem B7845011 : Blo 1549472 7845011 := bstep (se 1 (by rfl) ⟨5883758, by rfl⟩ : syracuseStep 7845011 = 11767517) B11767517
theorem B4142269 : Blo 1549472 4142269 := bstep (se 3 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 4142269 = 1553351) B1553351
theorem B9934073 : Blo 1549472 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B4781351 : Blo 1549472 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B7451999 : Blo 1549472 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B7853435 : Blo 1549472 7853435 := bstep (se 1 (by rfl) ⟨5890076, by rfl⟩ : syracuseStep 7853435 = 11780153) B11780153
theorem B3487175 : Blo 1549472 3487175 := bstep (se 1 (by rfl) ⟨2615381, by rfl⟩ : syracuseStep 3487175 = 5230763) B5230763
theorem B11777723 : Blo 1549472 11777723 := bstep (se 1 (by rfl) ⟨8833292, by rfl⟩ : syracuseStep 11777723 = 17666585) B17666585
theorem B3487535 : Blo 1549472 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B2324279 : Blo 1549472 2324279 := bstep (se 1 (by rfl) ⟨1743209, by rfl⟩ : syracuseStep 2324279 = 3486419) B3486419
theorem B5887799 : Blo 1549472 5887799 := bstep (se 1 (by rfl) ⟨4415849, by rfl⟩ : syracuseStep 5887799 = 8831699) B8831699
theorem B15104033 : Blo 1549472 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B6625313 : Blo 1549472 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B2324585 : Blo 1549472 2324585 := bstep (se 2 (by rfl) ⟨871719, by rfl⟩ : syracuseStep 2324585 = 1743439) B1743439
theorem B6625415 : Blo 1549472 6625415 := bstep (se 1 (by rfl) ⟨4969061, by rfl⟩ : syracuseStep 6625415 = 9938123) B9938123
theorem B5888285 : Blo 1549472 5888285 := bstep (se 3 (by rfl) ⟨1104053, by rfl⟩ : syracuseStep 5888285 = 2208107) B2208107
theorem B24181067 : Blo 1549472 24181067 := bstep (se 1 (by rfl) ⟨18135800, by rfl⟩ : syracuseStep 24181067 = 36271601) B36271601
theorem B3922283 : Blo 1549472 3922283 := bstep (se 1 (by rfl) ⟨2941712, by rfl⟩ : syracuseStep 3922283 = 5883425) B5883425
theorem B3488111 : Blo 1549472 3488111 := bstep (se 1 (by rfl) ⟨2616083, by rfl⟩ : syracuseStep 3488111 = 5232167) B5232167
theorem B2324903 : Blo 1549472 2324903 := bstep (se 1 (by rfl) ⟨1743677, by rfl⟩ : syracuseStep 2324903 = 3487355) B3487355
theorem B3488183 : Blo 1549472 3488183 := bstep (se 1 (by rfl) ⟨2616137, by rfl⟩ : syracuseStep 3488183 = 5232275) B5232275
theorem B2324987 : Blo 1549472 2324987 := bstep (se 1 (by rfl) ⟨1743740, by rfl⟩ : syracuseStep 2324987 = 3487481) B3487481
theorem B4192787 : Blo 1549472 4192787 := bstep (se 1 (by rfl) ⟨3144590, by rfl⟩ : syracuseStep 4192787 = 6289181) B6289181
theorem B3488327 : Blo 1549472 3488327 := bstep (se 1 (by rfl) ⟨2616245, by rfl⟩ : syracuseStep 3488327 = 5232491) B5232491
theorem B3488363 : Blo 1549472 3488363 := bstep (se 1 (by rfl) ⟨2616272, by rfl⟩ : syracuseStep 3488363 = 5232545) B5232545
theorem B2325113 : Blo 1549472 2325113 := bstep (se 2 (by rfl) ⟨871917, by rfl⟩ : syracuseStep 2325113 = 1743835) B1743835
theorem B3922607 : Blo 1549472 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B2325167 : Blo 1549472 2325167 := bstep (se 1 (by rfl) ⟨1743875, by rfl⟩ : syracuseStep 2325167 = 3487751) B3487751
theorem B3185335 : Blo 1549472 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B1743583 : Blo 1549472 1743583 := bstep (se 1 (by rfl) ⟨1307687, by rfl⟩ : syracuseStep 1743583 = 2615375) B2615375
theorem B2325215 : Blo 1549472 2325215 := bstep (se 1 (by rfl) ⟨1743911, by rfl⟩ : syracuseStep 2325215 = 3487823) B3487823
theorem B572996429 : Blo 1549472 572996429 := bstep (se 3 (by rfl) ⟨107436830, by rfl⟩ : syracuseStep 572996429 = 214873661) B214873661
theorem B4193167 : Blo 1549472 4193167 := bstep (se 1 (by rfl) ⟨3144875, by rfl⟩ : syracuseStep 4193167 = 6289751) B6289751
theorem B108927931 : Blo 1549472 108927931 := bstep (se 1 (by rfl) ⟨81695948, by rfl⟩ : syracuseStep 108927931 = 163391897) B163391897
theorem B2325479 : Blo 1549472 2325479 := bstep (se 1 (by rfl) ⟨1744109, by rfl⟩ : syracuseStep 2325479 = 3488219) B3488219
theorem B3922931 : Blo 1549472 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B3488759 : Blo 1549472 3488759 := bstep (se 1 (by rfl) ⟨2616569, by rfl⟩ : syracuseStep 3488759 = 5233139) B5233139
theorem B7552115 : Blo 1549472 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B5586043 : Blo 1549472 5586043 := bstep (se 1 (by rfl) ⟨4189532, by rfl⟩ : syracuseStep 5586043 = 8379065) B8379065
theorem B5233787 : Blo 1549472 5233787 := bstep (se 1 (by rfl) ⟨3925340, by rfl⟩ : syracuseStep 5233787 = 7850681) B7850681
theorem B4193479 : Blo 1549472 4193479 := bstep (se 1 (by rfl) ⟨3145109, by rfl⟩ : syracuseStep 4193479 = 6290219) B6290219
theorem B2325737 : Blo 1549472 2325737 := bstep (se 2 (by rfl) ⟨872151, by rfl⟩ : syracuseStep 2325737 = 1744303) B1744303
theorem B1744159 : Blo 1549472 1744159 := bstep (se 1 (by rfl) ⟨1308119, by rfl⟩ : syracuseStep 1744159 = 2616239) B2616239
theorem B2325791 : Blo 1549472 2325791 := bstep (se 1 (by rfl) ⟨1744343, by rfl⟩ : syracuseStep 2325791 = 3488687) B3488687
theorem B3726623 : Blo 1549472 3726623 := bstep (se 1 (by rfl) ⟨2794967, by rfl⟩ : syracuseStep 3726623 = 5589935) B5589935
theorem B3489119 : Blo 1549472 3489119 := bstep (se 1 (by rfl) ⟨2616839, by rfl⟩ : syracuseStep 3489119 = 5233679) B5233679
theorem B5234057 : Blo 1549472 5234057 := bstep (se 2 (by rfl) ⟨1962771, by rfl⟩ : syracuseStep 5234057 = 3925543) B3925543
theorem B3923387 : Blo 1549472 3923387 := bstep (se 1 (by rfl) ⟨2942540, by rfl⟩ : syracuseStep 3923387 = 5885081) B5885081
theorem B6626747 : Blo 1549472 6626747 := bstep (se 1 (by rfl) ⟨4970060, by rfl⟩ : syracuseStep 6626747 = 9940121) B9940121
theorem B2325959 : Blo 1549472 2325959 := bstep (se 1 (by rfl) ⟨1744469, by rfl⟩ : syracuseStep 2325959 = 3488939) B3488939
theorem B13237775 : Blo 1549472 13237775 := bstep (se 1 (by rfl) ⟨9928331, by rfl⟩ : syracuseStep 13237775 = 19856663) B19856663
theorem B1744447 : Blo 1549472 1744447 := bstep (se 1 (by rfl) ⟨1308335, by rfl⟩ : syracuseStep 1744447 = 2616671) B2616671
theorem B3726931 : Blo 1549472 3726931 := bstep (se 1 (by rfl) ⟨2795198, by rfl⟩ : syracuseStep 3726931 = 5590397) B5590397
theorem B11779667 : Blo 1549472 11779667 := bstep (se 1 (by rfl) ⟨8834750, by rfl⟩ : syracuseStep 11779667 = 17669501) B17669501
theorem B8830559 : Blo 1549472 8830559 := bstep (se 1 (by rfl) ⟨6622919, by rfl⟩ : syracuseStep 8830559 = 13245839) B13245839
theorem B42426017 : Blo 1549472 42426017 := bstep (se 2 (by rfl) ⟨15909756, by rfl⟩ : syracuseStep 42426017 = 31819513) B31819513
theorem B3489515 : Blo 1549472 3489515 := bstep (se 1 (by rfl) ⟨2617136, by rfl⟩ : syracuseStep 3489515 = 5234273) B5234273
theorem B76472045 : Blo 1549472 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B2326313 : Blo 1549472 2326313 := bstep (se 2 (by rfl) ⟨872367, by rfl⟩ : syracuseStep 2326313 = 1744735) B1744735
theorem B2326319 : Blo 1549472 2326319 := bstep (se 1 (by rfl) ⟨1744739, by rfl⟩ : syracuseStep 2326319 = 3489479) B3489479
theorem B3358511 : Blo 1549472 3358511 := bstep (se 1 (by rfl) ⟨2518883, by rfl⟩ : syracuseStep 3358511 = 5037767) B5037767
theorem B5234489 : Blo 1549472 5234489 := bstep (se 2 (by rfl) ⟨1962933, by rfl⟩ : syracuseStep 5234489 = 3925867) B3925867
theorem B6618941 : Blo 1549472 6618941 := bstep (se 3 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 6618941 = 2482103) B2482103
theorem B3489641 : Blo 1549472 3489641 := bstep (se 2 (by rfl) ⟨1308615, by rfl⟩ : syracuseStep 3489641 = 2617231) B2617231
theorem B13246523 : Blo 1549472 13246523 := bstep (se 1 (by rfl) ⟨9934892, by rfl⟩ : syracuseStep 13246523 = 19869785) B19869785
theorem B2687263 : Blo 1549472 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B5234975 : Blo 1549472 5234975 := bstep (se 1 (by rfl) ⟨3926231, by rfl⟩ : syracuseStep 5234975 = 7852463) B7852463
theorem B3490145 : Blo 1549472 3490145 := bstep (se 2 (by rfl) ⟨1308804, by rfl⟩ : syracuseStep 3490145 = 2617609) B2617609
theorem B3490235 : Blo 1549472 3490235 := bstep (se 1 (by rfl) ⟨2617676, by rfl⟩ : syracuseStep 3490235 = 5235353) B5235353
theorem B2326991 : Blo 1549472 2326991 := bstep (se 1 (by rfl) ⟨1745243, by rfl⟩ : syracuseStep 2326991 = 3490487) B3490487
theorem B2327033 : Blo 1549472 2327033 := bstep (se 2 (by rfl) ⟨872637, by rfl⟩ : syracuseStep 2327033 = 1745275) B1745275
theorem B5964283 : Blo 1549472 5964283 := bstep (se 1 (by rfl) ⟨4473212, by rfl⟩ : syracuseStep 5964283 = 8946425) B8946425
theorem B2327135 : Blo 1549472 2327135 := bstep (se 1 (by rfl) ⟨1745351, by rfl⟩ : syracuseStep 2327135 = 3490703) B3490703
theorem B31810157 : Blo 1549472 31810157 := bstep (se 3 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 31810157 = 11928809) B11928809
theorem B6619913 : Blo 1549472 6619913 := bstep (se 2 (by rfl) ⟨2482467, by rfl⟩ : syracuseStep 6619913 = 4964935) B4964935
theorem B11477771 : Blo 1549472 11477771 := bstep (se 1 (by rfl) ⟨8608328, by rfl⟩ : syracuseStep 11477771 = 17216657) B17216657
theorem B3187567 : Blo 1549472 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B5235623 : Blo 1549472 5235623 := bstep (se 1 (by rfl) ⟨3926717, by rfl⟩ : syracuseStep 5235623 = 7853435) B7853435
theorem B1549519 : Blo 1549472 1549519 := bstep (se 1 (by rfl) ⟨1162139, by rfl⟩ : syracuseStep 1549519 = 2324279) B2324279
theorem B3925199 : Blo 1549472 3925199 := bstep (se 1 (by rfl) ⟨2943899, by rfl⟩ : syracuseStep 3925199 = 5887799) B5887799
theorem B145237241 : Blo 1549472 145237241 := bstep (se 2 (by rfl) ⟨54463965, by rfl⟩ : syracuseStep 145237241 = 108927931) B108927931
theorem B10069355 : Blo 1549472 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B4416875 : Blo 1549472 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B7071113 : Blo 1549472 7071113 := bstep (se 2 (by rfl) ⟨2651667, by rfl⟩ : syracuseStep 7071113 = 5303335) B5303335
theorem B1549723 : Blo 1549472 1549723 := bstep (se 1 (by rfl) ⟨1162292, by rfl⟩ : syracuseStep 1549723 = 2324585) B2324585
theorem B4416943 : Blo 1549472 4416943 := bstep (se 1 (by rfl) ⟨3312707, by rfl⟩ : syracuseStep 4416943 = 6625415) B6625415
theorem B9430465 : Blo 1549472 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B7448057 : Blo 1549472 7448057 := bstep (se 2 (by rfl) ⟨2793021, by rfl⟩ : syracuseStep 7448057 = 5586043) B5586043
theorem B5236217 : Blo 1549472 5236217 := bstep (se 2 (by rfl) ⟨1963581, by rfl⟩ : syracuseStep 5236217 = 3927163) B3927163
theorem B3925523 : Blo 1549472 3925523 := bstep (se 1 (by rfl) ⟨2944142, by rfl⟩ : syracuseStep 3925523 = 5888285) B5888285
theorem B2614855 : Blo 1549472 2614855 := bstep (se 1 (by rfl) ⟨1961141, by rfl⟩ : syracuseStep 2614855 = 3922283) B3922283
theorem B5523025 : Blo 1549472 5523025 := bstep (se 2 (by rfl) ⟨2071134, by rfl⟩ : syracuseStep 5523025 = 4142269) B4142269
theorem B1549935 : Blo 1549472 1549935 := bstep (se 1 (by rfl) ⟨1162451, by rfl⟩ : syracuseStep 1549935 = 2324903) B2324903
theorem B1549991 : Blo 1549472 1549991 := bstep (se 1 (by rfl) ⟨1162493, by rfl⟩ : syracuseStep 1549991 = 2324987) B2324987
theorem B2795191 : Blo 1549472 2795191 := bstep (se 1 (by rfl) ⟨2096393, by rfl⟩ : syracuseStep 2795191 = 4192787) B4192787
theorem B1550075 : Blo 1549472 1550075 := bstep (se 1 (by rfl) ⟨1162556, by rfl⟩ : syracuseStep 1550075 = 2325113) B2325113
theorem B1550111 : Blo 1549472 1550111 := bstep (se 1 (by rfl) ⟨1162583, by rfl⟩ : syracuseStep 1550111 = 2325167) B2325167
theorem B2615071 : Blo 1549472 2615071 := bstep (se 1 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 2615071 = 3922607) B3922607
theorem B1550143 : Blo 1549472 1550143 := bstep (se 1 (by rfl) ⟨1162607, by rfl⟩ : syracuseStep 1550143 = 2325215) B2325215
theorem B1550319 : Blo 1549472 1550319 := bstep (se 1 (by rfl) ⟨1162739, by rfl⟩ : syracuseStep 1550319 = 2325479) B2325479
theorem B2615287 : Blo 1549472 2615287 := bstep (se 1 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 2615287 = 3922931) B3922931
theorem B1550491 : Blo 1549472 1550491 := bstep (se 1 (by rfl) ⟨1162868, by rfl⟩ : syracuseStep 1550491 = 2325737) B2325737
theorem B1550527 : Blo 1549472 1550527 := bstep (se 1 (by rfl) ⟨1162895, by rfl⟩ : syracuseStep 1550527 = 2325791) B2325791
theorem B2484415 : Blo 1549472 2484415 := bstep (se 1 (by rfl) ⟨1863311, by rfl⟩ : syracuseStep 2484415 = 3726623) B3726623
theorem B7850195 : Blo 1549472 7850195 := bstep (se 1 (by rfl) ⟨5887646, by rfl⟩ : syracuseStep 7850195 = 11775293) B11775293
theorem B2615591 : Blo 1549472 2615591 := bstep (se 1 (by rfl) ⟨1961693, by rfl⟩ : syracuseStep 2615591 = 3923387) B3923387
theorem B4417831 : Blo 1549472 4417831 := bstep (se 1 (by rfl) ⟨3313373, by rfl⟩ : syracuseStep 4417831 = 6626747) B6626747
theorem B1550639 : Blo 1549472 1550639 := bstep (se 1 (by rfl) ⟨1162979, by rfl⟩ : syracuseStep 1550639 = 2325959) B2325959
theorem B9931099 : Blo 1549472 9931099 := bstep (se 1 (by rfl) ⟨7448324, by rfl⟩ : syracuseStep 9931099 = 14896649) B14896649
theorem B8825183 : Blo 1549472 8825183 := bstep (se 1 (by rfl) ⟨6618887, by rfl⟩ : syracuseStep 8825183 = 13237775) B13237775
theorem B50981363 : Blo 1549472 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B1550875 : Blo 1549472 1550875 := bstep (se 1 (by rfl) ⟨1163156, by rfl⟩ : syracuseStep 1550875 = 2326313) B2326313
theorem B1550879 : Blo 1549472 1550879 := bstep (se 1 (by rfl) ⟨1163159, by rfl⟩ : syracuseStep 1550879 = 2326319) B2326319
theorem B2239007 : Blo 1549472 2239007 := bstep (se 1 (by rfl) ⟨1679255, by rfl⟩ : syracuseStep 2239007 = 3358511) B3358511
theorem B9931409 : Blo 1549472 9931409 := bstep (se 2 (by rfl) ⟨3724278, by rfl⟩ : syracuseStep 9931409 = 7448557) B7448557
theorem B3926839 : Blo 1549472 3926839 := bstep (se 1 (by rfl) ⟨2945129, by rfl⟩ : syracuseStep 3926839 = 5890259) B5890259
theorem B1551195 : Blo 1549472 1551195 := bstep (se 1 (by rfl) ⟨1163396, by rfl⟩ : syracuseStep 1551195 = 2326793) B2326793
theorem B1551263 : Blo 1549472 1551263 := bstep (se 1 (by rfl) ⟨1163447, by rfl⟩ : syracuseStep 1551263 = 2326895) B2326895
theorem B2616367 : Blo 1549472 2616367 := bstep (se 1 (by rfl) ⟨1962275, by rfl⟩ : syracuseStep 2616367 = 3924551) B3924551
theorem B1551407 : Blo 1549472 1551407 := bstep (se 1 (by rfl) ⟨1163555, by rfl⟩ : syracuseStep 1551407 = 2327111) B2327111
theorem B31820849 : Blo 1549472 31820849 := bstep (se 2 (by rfl) ⟨11932818, by rfl⟩ : syracuseStep 31820849 = 23865637) B23865637
theorem B1551431 : Blo 1549472 1551431 := bstep (se 1 (by rfl) ⟨1163573, by rfl⟩ : syracuseStep 1551431 = 2327147) B2327147
theorem B7072865 : Blo 1549472 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B5229791 : Blo 1549472 5229791 := bstep (se 1 (by rfl) ⟨3922343, by rfl⟩ : syracuseStep 5229791 = 7844687) B7844687
theorem B2616745 : Blo 1549472 2616745 := bstep (se 2 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 2616745 = 1962559) B1962559
theorem B5230007 : Blo 1549472 5230007 := bstep (se 1 (by rfl) ⟨3922505, by rfl⟩ : syracuseStep 5230007 = 7845011) B7845011
theorem B3534263 : Blo 1549472 3534263 := bstep (se 1 (by rfl) ⟨2650697, by rfl⟩ : syracuseStep 3534263 = 5301395) B5301395
theorem B2207207 : Blo 1549472 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B6622715 : Blo 1549472 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B2944507 : Blo 1549472 2944507 := bstep (se 1 (by rfl) ⟨2208380, by rfl⟩ : syracuseStep 2944507 = 4416761) B4416761
theorem B4967999 : Blo 1549472 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B4247113 : Blo 1549472 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B47722117 : Blo 1549472 47722117 := bstep (se 4 (by rfl) ⟨4473948, by rfl⟩ : syracuseStep 47722117 = 8947897) B8947897
theorem B2207407 : Blo 1549472 2207407 := bstep (se 1 (by rfl) ⟨1655555, by rfl⟩ : syracuseStep 2207407 = 3311111) B3311111
theorem B7851815 : Blo 1549472 7851815 := bstep (se 1 (by rfl) ⟨5888861, by rfl⟩ : syracuseStep 7851815 = 11777723) B11777723
theorem B5590889 : Blo 1549472 5590889 := bstep (se 2 (by rfl) ⟨2096583, by rfl⟩ : syracuseStep 5590889 = 4193167) B4193167
theorem B2617211 : Blo 1549472 2617211 := bstep (se 1 (by rfl) ⟨1962908, by rfl⟩ : syracuseStep 2617211 = 3925817) B3925817
theorem B5599199 : Blo 1549472 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B11776265 : Blo 1549472 11776265 := bstep (se 2 (by rfl) ⟨4416099, by rfl⟩ : syracuseStep 11776265 = 8832199) B8832199
theorem B5591305 : Blo 1549472 5591305 := bstep (se 2 (by rfl) ⟨2096739, by rfl⟩ : syracuseStep 5591305 = 4193479) B4193479
theorem B2945335 : Blo 1549472 2945335 := bstep (se 1 (by rfl) ⟨2209001, by rfl⟩ : syracuseStep 2945335 = 4418003) B4418003
theorem B381997619 : Blo 1549472 381997619 := bstep (se 1 (by rfl) ⟨286498214, by rfl⟩ : syracuseStep 381997619 = 572996429) B572996429
theorem B14340797 : Blo 1549472 14340797 := bstep (se 3 (by rfl) ⟨2688899, by rfl⟩ : syracuseStep 14340797 = 5377799) B5377799
theorem B5034743 : Blo 1549472 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B4969241 : Blo 1549472 4969241 := bstep (se 2 (by rfl) ⟨1863465, by rfl⟩ : syracuseStep 4969241 = 3726931) B3726931
theorem B7853111 : Blo 1549472 7853111 := bstep (se 1 (by rfl) ⟨5889833, by rfl⟩ : syracuseStep 7853111 = 11779667) B11779667
theorem B5887039 : Blo 1549472 5887039 := bstep (se 1 (by rfl) ⟨4415279, by rfl⟩ : syracuseStep 5887039 = 8830559) B8830559
theorem B28284011 : Blo 1549472 28284011 := bstep (se 1 (by rfl) ⟨21213008, by rfl⟩ : syracuseStep 28284011 = 42426017) B42426017
theorem B4412627 : Blo 1549472 4412627 := bstep (se 1 (by rfl) ⟨3309470, by rfl⟩ : syracuseStep 4412627 = 6618941) B6618941
theorem B3486995 : Blo 1549472 3486995 := bstep (se 1 (by rfl) ⟨2615246, by rfl⟩ : syracuseStep 3486995 = 5230493) B5230493
theorem B3487067 : Blo 1549472 3487067 := bstep (se 1 (by rfl) ⟨2615300, by rfl⟩ : syracuseStep 3487067 = 5230601) B5230601
theorem B5232059 : Blo 1549472 5232059 := bstep (se 1 (by rfl) ⟨3924044, by rfl⟩ : syracuseStep 5232059 = 7848089) B7848089
theorem B2324219 : Blo 1549472 2324219 := bstep (se 1 (by rfl) ⟨1743164, by rfl⟩ : syracuseStep 2324219 = 3486329) B3486329
theorem B2324255 : Blo 1549472 2324255 := bstep (se 1 (by rfl) ⟨1743191, by rfl⟩ : syracuseStep 2324255 = 3486383) B3486383
theorem B6297401 : Blo 1549472 6297401 := bstep (se 2 (by rfl) ⟨2361525, by rfl⟩ : syracuseStep 6297401 = 4723051) B4723051
theorem B2324303 : Blo 1549472 2324303 := bstep (se 1 (by rfl) ⟨1743227, by rfl⟩ : syracuseStep 2324303 = 3486455) B3486455
theorem B3487625 : Blo 1549472 3487625 := bstep (se 2 (by rfl) ⟨1307859, by rfl⟩ : syracuseStep 3487625 = 2615719) B2615719
theorem B2324423 : Blo 1549472 2324423 := bstep (se 1 (by rfl) ⟨1743317, by rfl⟩ : syracuseStep 2324423 = 3486635) B3486635
theorem B5232599 : Blo 1549472 5232599 := bstep (se 1 (by rfl) ⟨3924449, by rfl⟩ : syracuseStep 5232599 = 7848899) B7848899
theorem B11180099 : Blo 1549472 11180099 := bstep (se 1 (by rfl) ⟨8385074, by rfl⟩ : syracuseStep 11180099 = 16770149) B16770149
theorem B3487841 : Blo 1549472 3487841 := bstep (se 2 (by rfl) ⟨1307940, by rfl⟩ : syracuseStep 3487841 = 2615881) B2615881
theorem B28686629 : Blo 1549472 28686629 := bstep (se 4 (by rfl) ⟨2689371, by rfl⟩ : syracuseStep 28686629 = 5378743) B5378743
theorem B2324777 : Blo 1549472 2324777 := bstep (se 2 (by rfl) ⟨871791, by rfl⟩ : syracuseStep 2324777 = 1743583) B1743583
theorem B2324783 : Blo 1549472 2324783 := bstep (se 1 (by rfl) ⟨1743587, by rfl⟩ : syracuseStep 2324783 = 3487175) B3487175
theorem B5233085 : Blo 1549472 5233085 := bstep (se 3 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 5233085 = 1962407) B1962407
theorem B2325023 : Blo 1549472 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B16120711 : Blo 1549472 16120711 := bstep (se 1 (by rfl) ⟨12090533, by rfl⟩ : syracuseStep 16120711 = 24181067) B24181067
theorem B2325407 : Blo 1549472 2325407 := bstep (se 1 (by rfl) ⟨1744055, by rfl⟩ : syracuseStep 2325407 = 3488111) B3488111
theorem B22666159 : Blo 1549472 22666159 := bstep (se 1 (by rfl) ⟨16999619, by rfl⟩ : syracuseStep 22666159 = 33999239) B33999239
theorem B5888969 : Blo 1549472 5888969 := bstep (se 2 (by rfl) ⟨2208363, by rfl⟩ : syracuseStep 5888969 = 4416727) B4416727
theorem B2325455 : Blo 1549472 2325455 := bstep (se 1 (by rfl) ⟨1744091, by rfl⟩ : syracuseStep 2325455 = 3488183) B3488183
theorem B2325545 : Blo 1549472 2325545 := bstep (se 2 (by rfl) ⟨872079, by rfl⟩ : syracuseStep 2325545 = 1744159) B1744159
theorem B2325551 : Blo 1549472 2325551 := bstep (se 1 (by rfl) ⟨1744163, by rfl⟩ : syracuseStep 2325551 = 3488327) B3488327
theorem B1743943 : Blo 1549472 1743943 := bstep (se 1 (by rfl) ⟨1307957, by rfl⟩ : syracuseStep 1743943 = 2615915) B2615915
theorem B2325575 : Blo 1549472 2325575 := bstep (se 1 (by rfl) ⟨1744181, by rfl⟩ : syracuseStep 2325575 = 3488363) B3488363
theorem B13245565 : Blo 1549472 13245565 := bstep (se 3 (by rfl) ⟨2483543, by rfl⟩ : syracuseStep 13245565 = 4967087) B4967087
theorem B5233949 : Blo 1549472 5233949 := bstep (se 3 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 5233949 = 1962731) B1962731
theorem B2325839 : Blo 1549472 2325839 := bstep (se 1 (by rfl) ⟨1744379, by rfl⟩ : syracuseStep 2325839 = 3488759) B3488759
theorem B3489191 : Blo 1549472 3489191 := bstep (se 1 (by rfl) ⟨2616893, by rfl⟩ : syracuseStep 3489191 = 5233787) B5233787
theorem B2325929 : Blo 1549472 2325929 := bstep (se 2 (by rfl) ⟨872223, by rfl⟩ : syracuseStep 2325929 = 1744447) B1744447
theorem B2326079 : Blo 1549472 2326079 := bstep (se 1 (by rfl) ⟨1744559, by rfl⟩ : syracuseStep 2326079 = 3489119) B3489119
theorem B3489371 : Blo 1549472 3489371 := bstep (se 1 (by rfl) ⟨2617028, by rfl⟩ : syracuseStep 3489371 = 5234057) B5234057
theorem B3923599 : Blo 1549472 3923599 := bstep (se 1 (by rfl) ⟨2942699, by rfl⟩ : syracuseStep 3923599 = 5885399) B5885399
theorem B17653463 : Blo 1549472 17653463 := bstep (se 1 (by rfl) ⟨13240097, by rfl⟩ : syracuseStep 17653463 = 26480195) B26480195
theorem B21520183 : Blo 1549472 21520183 := bstep (se 1 (by rfl) ⟨16140137, by rfl⟩ : syracuseStep 21520183 = 32280275) B32280275
theorem B4415303 : Blo 1549472 4415303 := bstep (se 1 (by rfl) ⟨3311477, by rfl⟩ : syracuseStep 4415303 = 6622955) B6622955
theorem B2326343 : Blo 1549472 2326343 := bstep (se 1 (by rfl) ⟨1744757, by rfl⟩ : syracuseStep 2326343 = 3489515) B3489515
theorem B3489659 : Blo 1549472 3489659 := bstep (se 1 (by rfl) ⟨2617244, by rfl⟩ : syracuseStep 3489659 = 5234489) B5234489
theorem B2326427 : Blo 1549472 2326427 := bstep (se 1 (by rfl) ⟨1744820, by rfl⟩ : syracuseStep 2326427 = 3489641) B3489641
theorem B8831015 : Blo 1549472 8831015 := bstep (se 1 (by rfl) ⟨6623261, by rfl⟩ : syracuseStep 8831015 = 13246523) B13246523
theorem B3489983 : Blo 1549472 3489983 := bstep (se 1 (by rfl) ⟨2617487, by rfl⟩ : syracuseStep 3489983 = 5234975) B5234975
theorem B2326763 : Blo 1549472 2326763 := bstep (se 1 (by rfl) ⟨1745072, by rfl⟩ : syracuseStep 2326763 = 3490145) B3490145
theorem B2326823 : Blo 1549472 2326823 := bstep (se 1 (by rfl) ⟨1745117, by rfl⟩ : syracuseStep 2326823 = 3490235) B3490235
theorem B7455073 : Blo 1549472 7455073 := bstep (se 2 (by rfl) ⟨2795652, by rfl⟩ : syracuseStep 7455073 = 5591305) B5591305
theorem B254665079 : Blo 1549472 254665079 := bstep (se 1 (by rfl) ⟨190998809, by rfl⟩ : syracuseStep 254665079 = 381997619) B381997619
theorem B5890441 : Blo 1549472 5890441 := bstep (se 2 (by rfl) ⟨2208915, by rfl⟩ : syracuseStep 5890441 = 4417831) B4417831
theorem B9560531 : Blo 1549472 9560531 := bstep (se 1 (by rfl) ⟨7170398, by rfl⟩ : syracuseStep 9560531 = 14340797) B14340797
theorem B7651847 : Blo 1549472 7651847 := bstep (se 1 (by rfl) ⟨5738885, by rfl⟩ : syracuseStep 7651847 = 11477771) B11477771
theorem B3490415 : Blo 1549472 3490415 := bstep (se 1 (by rfl) ⟨2617811, by rfl⟩ : syracuseStep 3490415 = 5235623) B5235623
theorem B5235407 : Blo 1549472 5235407 := bstep (se 1 (by rfl) ⟨3926555, by rfl⟩ : syracuseStep 5235407 = 7853111) B7853111
theorem B2941751 : Blo 1549472 2941751 := bstep (se 1 (by rfl) ⟨2206313, by rfl⟩ : syracuseStep 2941751 = 4412627) B4412627
theorem B4965371 : Blo 1549472 4965371 := bstep (se 1 (by rfl) ⟨3724028, by rfl⟩ : syracuseStep 4965371 = 7448057) B7448057
theorem B3490811 : Blo 1549472 3490811 := bstep (se 1 (by rfl) ⟨2618108, by rfl⟩ : syracuseStep 3490811 = 5236217) B5236217
theorem B5235785 : Blo 1549472 5235785 := bstep (se 2 (by rfl) ⟨1963419, by rfl⟩ : syracuseStep 5235785 = 3926839) B3926839
theorem B1549479 : Blo 1549472 1549479 := bstep (se 1 (by rfl) ⟨1162109, by rfl⟩ : syracuseStep 1549479 = 2324219) B2324219
theorem B1549503 : Blo 1549472 1549503 := bstep (se 1 (by rfl) ⟨1162127, by rfl⟩ : syracuseStep 1549503 = 2324255) B2324255
theorem B1549535 : Blo 1549472 1549535 := bstep (se 1 (by rfl) ⟨1162151, by rfl⟩ : syracuseStep 1549535 = 2324303) B2324303
theorem B30221545 : Blo 1549472 30221545 := bstep (se 2 (by rfl) ⟨11333079, by rfl⟩ : syracuseStep 30221545 = 22666159) B22666159
theorem B1549615 : Blo 1549472 1549615 := bstep (se 1 (by rfl) ⟨1162211, by rfl⟩ : syracuseStep 1549615 = 2324423) B2324423
theorem B7849385 : Blo 1549472 7849385 := bstep (se 2 (by rfl) ⟨2943519, by rfl⟩ : syracuseStep 7849385 = 5887039) B5887039
theorem B1549851 : Blo 1549472 1549851 := bstep (se 1 (by rfl) ⟨1162388, by rfl⟩ : syracuseStep 1549851 = 2324777) B2324777
theorem B1549855 : Blo 1549472 1549855 := bstep (se 1 (by rfl) ⟨1162391, by rfl⟩ : syracuseStep 1549855 = 2324783) B2324783
theorem B5883455 : Blo 1549472 5883455 := bstep (se 1 (by rfl) ⟨4412591, by rfl⟩ : syracuseStep 5883455 = 8825183) B8825183
theorem B1550015 : Blo 1549472 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B6620939 : Blo 1549472 6620939 := bstep (se 1 (by rfl) ⟨4965704, by rfl⟩ : syracuseStep 6620939 = 9931409) B9931409
theorem B1550271 : Blo 1549472 1550271 := bstep (se 1 (by rfl) ⟨1162703, by rfl⟩ : syracuseStep 1550271 = 2325407) B2325407
theorem B3925979 : Blo 1549472 3925979 := bstep (se 1 (by rfl) ⟨2944484, by rfl⟩ : syracuseStep 3925979 = 5888969) B5888969
theorem B1550303 : Blo 1549472 1550303 := bstep (se 1 (by rfl) ⟨1162727, by rfl⟩ : syracuseStep 1550303 = 2325455) B2325455
theorem B3926009 : Blo 1549472 3926009 := bstep (se 2 (by rfl) ⟨1472253, by rfl⟩ : syracuseStep 3926009 = 2944507) B2944507
theorem B1550363 : Blo 1549472 1550363 := bstep (se 1 (by rfl) ⟨1162772, by rfl⟩ : syracuseStep 1550363 = 2325545) B2325545
theorem B1550367 : Blo 1549472 1550367 := bstep (se 1 (by rfl) ⟨1162775, by rfl⟩ : syracuseStep 1550367 = 2325551) B2325551
theorem B1550383 : Blo 1549472 1550383 := bstep (se 1 (by rfl) ⟨1162787, by rfl⟩ : syracuseStep 1550383 = 2325575) B2325575
theorem B5662817 : Blo 1549472 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B63629489 : Blo 1549472 63629489 := bstep (se 2 (by rfl) ⟨23861058, by rfl⟩ : syracuseStep 63629489 = 47722117) B47722117
theorem B1550559 : Blo 1549472 1550559 := bstep (se 1 (by rfl) ⟨1162919, by rfl⟩ : syracuseStep 1550559 = 2325839) B2325839
theorem B2943209 : Blo 1549472 2943209 := bstep (se 2 (by rfl) ⟨1103703, by rfl⟩ : syracuseStep 2943209 = 2207407) B2207407
theorem B1550619 : Blo 1549472 1550619 := bstep (se 1 (by rfl) ⟨1162964, by rfl⟩ : syracuseStep 1550619 = 2325929) B2325929
theorem B1550719 : Blo 1549472 1550719 := bstep (se 1 (by rfl) ⟨1163039, by rfl⟩ : syracuseStep 1550719 = 2326079) B2326079
theorem B3311999 : Blo 1549472 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B2943535 : Blo 1549472 2943535 := bstep (se 1 (by rfl) ⟨2207651, by rfl⟩ : syracuseStep 2943535 = 4415303) B4415303
theorem B1550895 : Blo 1549472 1550895 := bstep (se 1 (by rfl) ⟨1163171, by rfl⟩ : syracuseStep 1550895 = 2326343) B2326343
theorem B1550951 : Blo 1549472 1550951 := bstep (se 1 (by rfl) ⟨1163213, by rfl⟩ : syracuseStep 1550951 = 2326427) B2326427
theorem B7850843 : Blo 1549472 7850843 := bstep (se 1 (by rfl) ⟨5888132, by rfl⟩ : syracuseStep 7850843 = 11776265) B11776265
theorem B1551327 : Blo 1549472 1551327 := bstep (se 1 (by rfl) ⟨1163495, by rfl⟩ : syracuseStep 1551327 = 2326991) B2326991
theorem B1551355 : Blo 1549472 1551355 := bstep (se 1 (by rfl) ⟨1163516, by rfl⟩ : syracuseStep 1551355 = 2327033) B2327033
theorem B1551423 : Blo 1549472 1551423 := bstep (se 1 (by rfl) ⟨1163567, by rfl⟩ : syracuseStep 1551423 = 2327135) B2327135
theorem B3927113 : Blo 1549472 3927113 := bstep (se 2 (by rfl) ⟨1472667, by rfl⟩ : syracuseStep 3927113 = 2945335) B2945335
theorem B13241465 : Blo 1549472 13241465 := bstep (se 2 (by rfl) ⟨4965549, by rfl⟩ : syracuseStep 13241465 = 9931099) B9931099
theorem B3312827 : Blo 1549472 3312827 := bstep (se 1 (by rfl) ⟨2484620, by rfl⟩ : syracuseStep 3312827 = 4969241) B4969241
theorem B2616799 : Blo 1549472 2616799 := bstep (se 1 (by rfl) ⟨1962599, by rfl⟩ : syracuseStep 2616799 = 3925199) B3925199
theorem B96824827 : Blo 1549472 96824827 := bstep (se 1 (by rfl) ⟨72618620, by rfl⟩ : syracuseStep 96824827 = 145237241) B145237241
theorem B6712903 : Blo 1549472 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B2944583 : Blo 1549472 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B4714075 : Blo 1549472 4714075 := bstep (se 1 (by rfl) ⟨3535556, by rfl⟩ : syracuseStep 4714075 = 7071113) B7071113
theorem B13250213 : Blo 1549472 13250213 := bstep (se 4 (by rfl) ⟨1242207, by rfl⟩ : syracuseStep 13250213 = 2484415) B2484415
theorem B2617015 : Blo 1549472 2617015 := bstep (se 1 (by rfl) ⟨1962761, by rfl⟩ : syracuseStep 2617015 = 3925523) B3925523
theorem B4198267 : Blo 1549472 4198267 := bstep (se 1 (by rfl) ⟨3148700, by rfl⟩ : syracuseStep 4198267 = 6297401) B6297401
theorem B5885885 : Blo 1549472 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B14332069 : Blo 1549472 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B19124419 : Blo 1549472 19124419 := bstep (se 1 (by rfl) ⟨14343314, by rfl⟩ : syracuseStep 19124419 = 28686629) B28686629
theorem B21213899 : Blo 1549472 21213899 := bstep (se 1 (by rfl) ⟨15910424, by rfl⟩ : syracuseStep 21213899 = 31820849) B31820849
theorem B4715243 : Blo 1549472 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B3486473 : Blo 1549472 3486473 := bstep (se 2 (by rfl) ⟨1307427, by rfl⟩ : syracuseStep 3486473 = 2614855) B2614855
theorem B3486527 : Blo 1549472 3486527 := bstep (se 1 (by rfl) ⟨2614895, by rfl⟩ : syracuseStep 3486527 = 5229791) B5229791
theorem B5231465 : Blo 1549472 5231465 := bstep (se 2 (by rfl) ⟨1961799, by rfl⟩ : syracuseStep 5231465 = 3923599) B3923599
theorem B3486671 : Blo 1549472 3486671 := bstep (se 1 (by rfl) ⟨2615003, by rfl⟩ : syracuseStep 3486671 = 5230007) B5230007
theorem B2356175 : Blo 1549472 2356175 := bstep (se 1 (by rfl) ⟨1767131, by rfl⟩ : syracuseStep 2356175 = 3534263) B3534263
theorem B3486761 : Blo 1549472 3486761 := bstep (se 2 (by rfl) ⟨1307535, by rfl⟩ : syracuseStep 3486761 = 2615071) B2615071
theorem B28693577 : Blo 1549472 28693577 := bstep (se 2 (by rfl) ⟨10760091, by rfl⟩ : syracuseStep 28693577 = 21520183) B21520183
theorem B11768975 : Blo 1549472 11768975 := bstep (se 1 (by rfl) ⟨8826731, by rfl⟩ : syracuseStep 11768975 = 17653463) B17653463
theorem B3732799 : Blo 1549472 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B3487049 : Blo 1549472 3487049 := bstep (se 2 (by rfl) ⟨1307643, by rfl⟩ : syracuseStep 3487049 = 2615287) B2615287
theorem B21206771 : Blo 1549472 21206771 := bstep (se 1 (by rfl) ⟨15905078, by rfl⟩ : syracuseStep 21206771 = 31810157) B31810157
theorem B3356495 : Blo 1549472 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B4413275 : Blo 1549472 4413275 := bstep (se 1 (by rfl) ⟨3309956, by rfl⟩ : syracuseStep 4413275 = 6619913) B6619913
theorem B7952377 : Blo 1549472 7952377 := bstep (se 2 (by rfl) ⟨2982141, by rfl⟩ : syracuseStep 7952377 = 5964283) B5964283
theorem B18856007 : Blo 1549472 18856007 := bstep (se 1 (by rfl) ⟨14142005, by rfl⟩ : syracuseStep 18856007 = 28284011) B28284011
theorem B2324663 : Blo 1549472 2324663 := bstep (se 1 (by rfl) ⟨1743497, by rfl⟩ : syracuseStep 2324663 = 3486995) B3486995
theorem B2324711 : Blo 1549472 2324711 := bstep (se 1 (by rfl) ⟨1743533, by rfl⟩ : syracuseStep 2324711 = 3487067) B3487067
theorem B3488039 : Blo 1549472 3488039 := bstep (se 1 (by rfl) ⟨2616029, by rfl⟩ : syracuseStep 3488039 = 5232059) B5232059
theorem B14907685 : Blo 1549472 14907685 := bstep (se 4 (by rfl) ⟨1397595, by rfl⟩ : syracuseStep 14907685 = 2795191) B2795191
theorem B4250089 : Blo 1549472 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B21494281 : Blo 1549472 21494281 := bstep (se 2 (by rfl) ⟨8060355, by rfl⟩ : syracuseStep 21494281 = 16120711) B16120711
theorem B2325083 : Blo 1549472 2325083 := bstep (se 1 (by rfl) ⟨1743812, by rfl⟩ : syracuseStep 2325083 = 3487625) B3487625
theorem B3488399 : Blo 1549472 3488399 := bstep (se 1 (by rfl) ⟨2616299, by rfl⟩ : syracuseStep 3488399 = 5232599) B5232599
theorem B7453399 : Blo 1549472 7453399 := bstep (se 1 (by rfl) ⟨5590049, by rfl⟩ : syracuseStep 7453399 = 11180099) B11180099
theorem B3488489 : Blo 1549472 3488489 := bstep (se 2 (by rfl) ⟨1308183, by rfl⟩ : syracuseStep 3488489 = 2616367) B2616367
theorem B2325227 : Blo 1549472 2325227 := bstep (se 1 (by rfl) ⟨1743920, by rfl⟩ : syracuseStep 2325227 = 3487841) B3487841
theorem B5970685 : Blo 1549472 5970685 := bstep (se 3 (by rfl) ⟨1119503, by rfl⟩ : syracuseStep 5970685 = 2239007) B2239007
theorem B2325257 : Blo 1549472 2325257 := bstep (se 2 (by rfl) ⟨871971, by rfl⟩ : syracuseStep 2325257 = 1743943) B1743943
theorem B5233463 : Blo 1549472 5233463 := bstep (se 1 (by rfl) ⟨3925097, by rfl⟩ : syracuseStep 5233463 = 7850195) B7850195
theorem B17660753 : Blo 1549472 17660753 := bstep (se 2 (by rfl) ⟨6622782, by rfl⟩ : syracuseStep 17660753 = 13245565) B13245565
theorem B1743727 : Blo 1549472 1743727 := bstep (se 1 (by rfl) ⟨1307795, by rfl⟩ : syracuseStep 1743727 = 2615591) B2615591
theorem B3488723 : Blo 1549472 3488723 := bstep (se 1 (by rfl) ⟨2616542, by rfl⟩ : syracuseStep 3488723 = 5233085) B5233085
theorem B33987575 : Blo 1549472 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B3488993 : Blo 1549472 3488993 := bstep (se 2 (by rfl) ⟨1308372, by rfl⟩ : syracuseStep 3488993 = 2616745) B2616745
theorem B5889257 : Blo 1549472 5889257 := bstep (se 2 (by rfl) ⟨2208471, by rfl⟩ : syracuseStep 5889257 = 4416943) B4416943
theorem B12573953 : Blo 1549472 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B7364033 : Blo 1549472 7364033 := bstep (se 2 (by rfl) ⟨2761512, by rfl⟩ : syracuseStep 7364033 = 5523025) B5523025
theorem B3489299 : Blo 1549472 3489299 := bstep (se 1 (by rfl) ⟨2616974, by rfl⟩ : syracuseStep 3489299 = 5233949) B5233949
theorem B2326127 : Blo 1549472 2326127 := bstep (se 1 (by rfl) ⟨1744595, by rfl⟩ : syracuseStep 2326127 = 3489191) B3489191
theorem B4415143 : Blo 1549472 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B2326247 : Blo 1549472 2326247 := bstep (se 1 (by rfl) ⟨1744685, by rfl⟩ : syracuseStep 2326247 = 3489371) B3489371
theorem B5234543 : Blo 1549472 5234543 := bstep (se 1 (by rfl) ⟨3925907, by rfl⟩ : syracuseStep 5234543 = 7851815) B7851815
theorem B3727259 : Blo 1549472 3727259 := bstep (se 1 (by rfl) ⟨2795444, by rfl⟩ : syracuseStep 3727259 = 5590889) B5590889
theorem B1744807 : Blo 1549472 1744807 := bstep (se 1 (by rfl) ⟨1308605, by rfl⟩ : syracuseStep 1744807 = 2617211) B2617211
theorem B2326439 : Blo 1549472 2326439 := bstep (se 1 (by rfl) ⟨1744829, by rfl⟩ : syracuseStep 2326439 = 3489659) B3489659
theorem B2326655 : Blo 1549472 2326655 := bstep (se 1 (by rfl) ⟨1744991, by rfl⟩ : syracuseStep 2326655 = 3489983) B3489983
theorem B2326943 : Blo 1549472 2326943 := bstep (se 1 (by rfl) ⟨1745207, by rfl⟩ : syracuseStep 2326943 = 3490415) B3490415
theorem B3490271 : Blo 1549472 3490271 := bstep (se 1 (by rfl) ⟨2617703, by rfl⟩ : syracuseStep 3490271 = 5235407) B5235407
theorem B3310247 : Blo 1549472 3310247 := bstep (se 1 (by rfl) ⟨2482685, by rfl⟩ : syracuseStep 3310247 = 4965371) B4965371
theorem B2327207 : Blo 1549472 2327207 := bstep (se 1 (by rfl) ⟨1745405, by rfl⟩ : syracuseStep 2327207 = 3490811) B3490811
theorem B3490523 : Blo 1549472 3490523 := bstep (se 1 (by rfl) ⟨2617892, by rfl⟩ : syracuseStep 3490523 = 5235785) B5235785
theorem B19129051 : Blo 1549472 19129051 := bstep (se 1 (by rfl) ⟨14346788, by rfl⟩ : syracuseStep 19129051 = 28693577) B28693577
theorem B3924713 : Blo 1549472 3924713 := bstep (se 2 (by rfl) ⟨1471767, by rfl⟩ : syracuseStep 3924713 = 2943535) B2943535
theorem B9937865 : Blo 1549472 9937865 := bstep (se 2 (by rfl) ⟨3726699, by rfl⟩ : syracuseStep 9937865 = 7453399) B7453399
theorem B25494749 : Blo 1549472 25494749 := bstep (se 3 (by rfl) ⟨4780265, by rfl⟩ : syracuseStep 25494749 = 9560531) B9560531
theorem B2237663 : Blo 1549472 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B2942183 : Blo 1549472 2942183 := bstep (se 1 (by rfl) ⟨2206637, by rfl⟩ : syracuseStep 2942183 = 4413275) B4413275
theorem B1549775 : Blo 1549472 1549775 := bstep (se 1 (by rfl) ⟨1162331, by rfl⟩ : syracuseStep 1549775 = 2324663) B2324663
theorem B1549807 : Blo 1549472 1549807 := bstep (se 1 (by rfl) ⟨1162355, by rfl⟩ : syracuseStep 1549807 = 2324711) B2324711
theorem B1550055 : Blo 1549472 1550055 := bstep (se 1 (by rfl) ⟨1162541, by rfl⟩ : syracuseStep 1550055 = 2325083) B2325083
theorem B1550151 : Blo 1549472 1550151 := bstep (se 1 (by rfl) ⟨1162613, by rfl⟩ : syracuseStep 1550151 = 2325227) B2325227
theorem B1550171 : Blo 1549472 1550171 := bstep (se 1 (by rfl) ⟨1162628, by rfl⟩ : syracuseStep 1550171 = 2325257) B2325257
theorem B11773835 : Blo 1549472 11773835 := bstep (se 1 (by rfl) ⟨8830376, by rfl⟩ : syracuseStep 11773835 = 17660753) B17660753
theorem B22390757 : Blo 1549472 22390757 := bstep (se 4 (by rfl) ⟨2099133, by rfl⟩ : syracuseStep 22390757 = 4198267) B4198267
theorem B6285433 : Blo 1549472 6285433 := bstep (se 2 (by rfl) ⟨2357037, by rfl⟩ : syracuseStep 6285433 = 4714075) B4714075
theorem B3926171 : Blo 1549472 3926171 := bstep (se 1 (by rfl) ⟨2944628, by rfl⟩ : syracuseStep 3926171 = 5889257) B5889257
theorem B8382635 : Blo 1549472 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B4909355 : Blo 1549472 4909355 := bstep (se 1 (by rfl) ⟨3682016, by rfl⟩ : syracuseStep 4909355 = 7364033) B7364033
theorem B1550751 : Blo 1549472 1550751 := bstep (se 1 (by rfl) ⟨1163063, by rfl⟩ : syracuseStep 1550751 = 2326127) B2326127
theorem B8833475 : Blo 1549472 8833475 := bstep (se 1 (by rfl) ⟨6625106, by rfl⟩ : syracuseStep 8833475 = 13250213) B13250213
theorem B1550831 : Blo 1549472 1550831 := bstep (se 1 (by rfl) ⟨1163123, by rfl⟩ : syracuseStep 1550831 = 2326247) B2326247
theorem B2484839 : Blo 1549472 2484839 := bstep (se 1 (by rfl) ⟨1863629, by rfl⟩ : syracuseStep 2484839 = 3727259) B3727259
theorem B1550959 : Blo 1549472 1550959 := bstep (se 1 (by rfl) ⟨1163219, by rfl⟩ : syracuseStep 1550959 = 2326439) B2326439
theorem B10603169 : Blo 1549472 10603169 := bstep (se 2 (by rfl) ⟨3976188, by rfl⟩ : syracuseStep 10603169 = 7952377) B7952377
theorem B1551175 : Blo 1549472 1551175 := bstep (se 1 (by rfl) ⟨1163381, by rfl⟩ : syracuseStep 1551175 = 2326763) B2326763
theorem B1551215 : Blo 1549472 1551215 := bstep (se 1 (by rfl) ⟨1163411, by rfl⟩ : syracuseStep 1551215 = 2326823) B2326823
theorem B19876913 : Blo 1549472 19876913 := bstep (se 2 (by rfl) ⟨7453842, by rfl⟩ : syracuseStep 19876913 = 14907685) B14907685
theorem B9940097 : Blo 1549472 9940097 := bstep (se 2 (by rfl) ⟨3727536, by rfl⟩ : syracuseStep 9940097 = 7455073) B7455073
theorem B14142599 : Blo 1549472 14142599 := bstep (se 1 (by rfl) ⟨10606949, by rfl⟩ : syracuseStep 14142599 = 21213899) B21213899
theorem B1961167 : Blo 1549472 1961167 := bstep (se 1 (by rfl) ⟨1470875, by rfl⟩ : syracuseStep 1961167 = 2941751) B2941751
theorem B28659041 : Blo 1549472 28659041 := bstep (se 2 (by rfl) ⟨10747140, by rfl⟩ : syracuseStep 28659041 = 21494281) B21494281
theorem B2617319 : Blo 1549472 2617319 := bstep (se 1 (by rfl) ⟨1962989, by rfl⟩ : syracuseStep 2617319 = 3925979) B3925979
theorem B2617339 : Blo 1549472 2617339 := bstep (se 1 (by rfl) ⟨1963004, by rfl⟩ : syracuseStep 2617339 = 3926009) B3926009
theorem B12570671 : Blo 1549472 12570671 := bstep (se 1 (by rfl) ⟨9428003, by rfl⟩ : syracuseStep 12570671 = 18856007) B18856007
theorem B1962139 : Blo 1549472 1962139 := bstep (se 1 (by rfl) ⟨1471604, by rfl⟩ : syracuseStep 1962139 = 2943209) B2943209
theorem B2207999 : Blo 1549472 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B4977065 : Blo 1549472 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B2618075 : Blo 1549472 2618075 := bstep (se 1 (by rfl) ⟨1963556, by rfl⟩ : syracuseStep 2618075 = 3927113) B3927113
theorem B8827643 : Blo 1549472 8827643 := bstep (se 1 (by rfl) ⟨6620732, by rfl⟩ : syracuseStep 8827643 = 13241465) B13241465
theorem B8950537 : Blo 1549472 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B2208551 : Blo 1549472 2208551 := bstep (se 1 (by rfl) ⟨1656413, by rfl⟩ : syracuseStep 2208551 = 3312827) B3312827
theorem B5886857 : Blo 1549472 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B1963055 : Blo 1549472 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B5887343 : Blo 1549472 5887343 := bstep (se 1 (by rfl) ⟨4415507, by rfl⟩ : syracuseStep 5887343 = 8831015) B8831015
theorem B169776719 : Blo 1549472 169776719 := bstep (se 1 (by rfl) ⟨127332539, by rfl⟩ : syracuseStep 169776719 = 254665079) B254665079
theorem B25499225 : Blo 1549472 25499225 := bstep (se 2 (by rfl) ⟨9562209, by rfl⟩ : syracuseStep 25499225 = 19124419) B19124419
theorem B5101231 : Blo 1549472 5101231 := bstep (se 1 (by rfl) ⟨3825923, by rfl⟩ : syracuseStep 5101231 = 7651847) B7651847
theorem B169678637 : Blo 1549472 169678637 := bstep (se 3 (by rfl) ⟨31814744, by rfl⟩ : syracuseStep 169678637 = 63629489) B63629489
theorem B3143495 : Blo 1549472 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B2324315 : Blo 1549472 2324315 := bstep (se 1 (by rfl) ⟨1743236, by rfl⟩ : syracuseStep 2324315 = 3486473) B3486473
theorem B7853921 : Blo 1549472 7853921 := bstep (se 2 (by rfl) ⟨2945220, by rfl⟩ : syracuseStep 7853921 = 5890441) B5890441
theorem B2324351 : Blo 1549472 2324351 := bstep (se 1 (by rfl) ⟨1743263, by rfl⟩ : syracuseStep 2324351 = 3486527) B3486527
theorem B3487643 : Blo 1549472 3487643 := bstep (se 1 (by rfl) ⟨2615732, by rfl⟩ : syracuseStep 3487643 = 5231465) B5231465
theorem B2324447 : Blo 1549472 2324447 := bstep (se 1 (by rfl) ⟨1743335, by rfl⟩ : syracuseStep 2324447 = 3486671) B3486671
theorem B2324507 : Blo 1549472 2324507 := bstep (se 1 (by rfl) ⟨1743380, by rfl⟩ : syracuseStep 2324507 = 3486761) B3486761
theorem B7845983 : Blo 1549472 7845983 := bstep (se 1 (by rfl) ⟨5884487, by rfl⟩ : syracuseStep 7845983 = 11768975) B11768975
theorem B76437701 : Blo 1549472 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B2324699 : Blo 1549472 2324699 := bstep (se 1 (by rfl) ⟨1743524, by rfl⟩ : syracuseStep 2324699 = 3487049) B3487049
theorem B5232923 : Blo 1549472 5232923 := bstep (se 1 (by rfl) ⟨3924692, by rfl⟩ : syracuseStep 5232923 = 7849385) B7849385
theorem B7960913 : Blo 1549472 7960913 := bstep (se 2 (by rfl) ⟨2985342, by rfl⟩ : syracuseStep 7960913 = 5970685) B5970685
theorem B3922303 : Blo 1549472 3922303 := bstep (se 1 (by rfl) ⟨2941727, by rfl⟩ : syracuseStep 3922303 = 5883455) B5883455
theorem B2324969 : Blo 1549472 2324969 := bstep (se 2 (by rfl) ⟨871863, by rfl⟩ : syracuseStep 2324969 = 1743727) B1743727
theorem B14137847 : Blo 1549472 14137847 := bstep (se 1 (by rfl) ⟨10603385, by rfl⟩ : syracuseStep 14137847 = 21206771) B21206771
theorem B4413959 : Blo 1549472 4413959 := bstep (se 1 (by rfl) ⟨3310469, by rfl⟩ : syracuseStep 4413959 = 6620939) B6620939
theorem B3775211 : Blo 1549472 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B2325359 : Blo 1549472 2325359 := bstep (se 1 (by rfl) ⟨1744019, by rfl⟩ : syracuseStep 2325359 = 3488039) B3488039
theorem B40295393 : Blo 1549472 40295393 := bstep (se 2 (by rfl) ⟨15110772, by rfl⟩ : syracuseStep 40295393 = 30221545) B30221545
theorem B2325599 : Blo 1549472 2325599 := bstep (se 1 (by rfl) ⟨1744199, by rfl⟩ : syracuseStep 2325599 = 3488399) B3488399
theorem B2325659 : Blo 1549472 2325659 := bstep (se 1 (by rfl) ⟨1744244, by rfl⟩ : syracuseStep 2325659 = 3488489) B3488489
theorem B3488975 : Blo 1549472 3488975 := bstep (se 1 (by rfl) ⟨2616731, by rfl⟩ : syracuseStep 3488975 = 5233463) B5233463
theorem B5233895 : Blo 1549472 5233895 := bstep (se 1 (by rfl) ⟨3925421, by rfl⟩ : syracuseStep 5233895 = 7850843) B7850843
theorem B3489065 : Blo 1549472 3489065 := bstep (se 2 (by rfl) ⟨1308399, by rfl⟩ : syracuseStep 3489065 = 2616799) B2616799
theorem B2325815 : Blo 1549472 2325815 := bstep (se 1 (by rfl) ⟨1744361, by rfl⟩ : syracuseStep 2325815 = 3488723) B3488723
theorem B22658383 : Blo 1549472 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B2325995 : Blo 1549472 2325995 := bstep (se 1 (by rfl) ⟨1744496, by rfl⟩ : syracuseStep 2325995 = 3488993) B3488993
theorem B3489353 : Blo 1549472 3489353 := bstep (se 2 (by rfl) ⟨1308507, by rfl⟩ : syracuseStep 3489353 = 2617015) B2617015
theorem B2326199 : Blo 1549472 2326199 := bstep (se 1 (by rfl) ⟨1744649, by rfl⟩ : syracuseStep 2326199 = 3489299) B3489299
theorem B6283133 : Blo 1549472 6283133 := bstep (se 3 (by rfl) ⟨1178087, by rfl⟩ : syracuseStep 6283133 = 2356175) B2356175
theorem B22667141 : Blo 1549472 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B2326409 : Blo 1549472 2326409 := bstep (se 2 (by rfl) ⟨872403, by rfl⟩ : syracuseStep 2326409 = 1744807) B1744807
theorem B3489695 : Blo 1549472 3489695 := bstep (se 1 (by rfl) ⟨2617271, by rfl⟩ : syracuseStep 3489695 = 5234543) B5234543
theorem B3923923 : Blo 1549472 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B516399077 : Blo 1549472 516399077 := bstep (se 4 (by rfl) ⟨48412413, by rfl⟩ : syracuseStep 516399077 = 96824827) B96824827
theorem B33521789 : Blo 1549472 33521789 := bstep (se 3 (by rfl) ⟨6285335, by rfl⟩ : syracuseStep 33521789 = 12570671) B12570671
theorem B5234813 : Blo 1549472 5234813 := bstep (se 3 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 5234813 = 1963055) B1963055
theorem B8380577 : Blo 1549472 8380577 := bstep (se 2 (by rfl) ⟨3142716, by rfl⟩ : syracuseStep 8380577 = 6285433) B6285433
theorem B2326847 : Blo 1549472 2326847 := bstep (se 1 (by rfl) ⟨1745135, by rfl⟩ : syracuseStep 2326847 = 3490271) B3490271
theorem B2327015 : Blo 1549472 2327015 := bstep (se 1 (by rfl) ⟨1745261, by rfl⟩ : syracuseStep 2327015 = 3490523) B3490523
theorem B1745383 : Blo 1549472 1745383 := bstep (se 1 (by rfl) ⟨1309037, by rfl⟩ : syracuseStep 1745383 = 2618075) B2618075
theorem B3924571 : Blo 1549472 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B3924895 : Blo 1549472 3924895 := bstep (se 1 (by rfl) ⟨2943671, by rfl⟩ : syracuseStep 3924895 = 5887343) B5887343
theorem B16999483 : Blo 1549472 16999483 := bstep (se 1 (by rfl) ⟨12749612, by rfl⟩ : syracuseStep 16999483 = 25499225) B25499225
theorem B13272173 : Blo 1549472 13272173 := bstep (se 3 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 13272173 = 4977065) B4977065
theorem B1549543 : Blo 1549472 1549543 := bstep (se 1 (by rfl) ⟨1162157, by rfl⟩ : syracuseStep 1549543 = 2324315) B2324315
theorem B5235947 : Blo 1549472 5235947 := bstep (se 1 (by rfl) ⟨3926960, by rfl⟩ : syracuseStep 5235947 = 7853921) B7853921
theorem B1549567 : Blo 1549472 1549567 := bstep (se 1 (by rfl) ⟨1162175, by rfl⟩ : syracuseStep 1549567 = 2324351) B2324351
theorem B7849223 : Blo 1549472 7849223 := bstep (se 1 (by rfl) ⟨5886917, by rfl⟩ : syracuseStep 7849223 = 11773835) B11773835
theorem B1549631 : Blo 1549472 1549631 := bstep (se 1 (by rfl) ⟨1162223, by rfl⟩ : syracuseStep 1549631 = 2324447) B2324447
theorem B14927171 : Blo 1549472 14927171 := bstep (se 1 (by rfl) ⟨11195378, by rfl⟩ : syracuseStep 14927171 = 22390757) B22390757
theorem B1549671 : Blo 1549472 1549671 := bstep (se 1 (by rfl) ⟨1162253, by rfl⟩ : syracuseStep 1549671 = 2324507) B2324507
theorem B5588423 : Blo 1549472 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B1549799 : Blo 1549472 1549799 := bstep (se 1 (by rfl) ⟨1162349, by rfl⟩ : syracuseStep 1549799 = 2324699) B2324699
theorem B2614889 : Blo 1549472 2614889 := bstep (se 2 (by rfl) ⟨980583, by rfl⟩ : syracuseStep 2614889 = 1961167) B1961167
theorem B1549979 : Blo 1549472 1549979 := bstep (se 1 (by rfl) ⟨1162484, by rfl⟩ : syracuseStep 1549979 = 2324969) B2324969
theorem B2942639 : Blo 1549472 2942639 := bstep (se 1 (by rfl) ⟨2206979, by rfl⟩ : syracuseStep 2942639 = 4413959) B4413959
theorem B1656559 : Blo 1549472 1656559 := bstep (se 1 (by rfl) ⟨1242419, by rfl⟩ : syracuseStep 1656559 = 2484839) B2484839
theorem B2516807 : Blo 1549472 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B1550239 : Blo 1549472 1550239 := bstep (se 1 (by rfl) ⟨1162679, by rfl⟩ : syracuseStep 1550239 = 2325359) B2325359
theorem B26863595 : Blo 1549472 26863595 := bstep (se 1 (by rfl) ⟨20147696, by rfl⟩ : syracuseStep 26863595 = 40295393) B40295393
theorem B1550399 : Blo 1549472 1550399 := bstep (se 1 (by rfl) ⟨1162799, by rfl⟩ : syracuseStep 1550399 = 2325599) B2325599
theorem B1550439 : Blo 1549472 1550439 := bstep (se 1 (by rfl) ⟨1162829, by rfl⟩ : syracuseStep 1550439 = 2325659) B2325659
theorem B8382653 : Blo 1549472 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B1550543 : Blo 1549472 1550543 := bstep (se 1 (by rfl) ⟨1162907, by rfl⟩ : syracuseStep 1550543 = 2325815) B2325815
theorem B6801641 : Blo 1549472 6801641 := bstep (se 2 (by rfl) ⟨2550615, by rfl⟩ : syracuseStep 6801641 = 5101231) B5101231
theorem B19106027 : Blo 1549472 19106027 := bstep (se 1 (by rfl) ⟨14329520, by rfl⟩ : syracuseStep 19106027 = 28659041) B28659041
theorem B1550663 : Blo 1549472 1550663 := bstep (se 1 (by rfl) ⟨1162997, by rfl⟩ : syracuseStep 1550663 = 2325995) B2325995
theorem B1550799 : Blo 1549472 1550799 := bstep (se 1 (by rfl) ⟨1163099, by rfl⟩ : syracuseStep 1550799 = 2326199) B2326199
theorem B4188755 : Blo 1549472 4188755 := bstep (se 1 (by rfl) ⟨3141566, by rfl⟩ : syracuseStep 4188755 = 6283133) B6283133
theorem B1550939 : Blo 1549472 1550939 := bstep (se 1 (by rfl) ⟨1163204, by rfl⟩ : syracuseStep 1550939 = 2326409) B2326409
theorem B1551103 : Blo 1549472 1551103 := bstep (se 1 (by rfl) ⟨1163327, by rfl⟩ : syracuseStep 1551103 = 2326655) B2326655
theorem B2616185 : Blo 1549472 2616185 := bstep (se 2 (by rfl) ⟨981069, by rfl⟩ : syracuseStep 2616185 = 1962139) B1962139
theorem B1551295 : Blo 1549472 1551295 := bstep (se 1 (by rfl) ⟨1163471, by rfl⟩ : syracuseStep 1551295 = 2326943) B2326943
theorem B1551471 : Blo 1549472 1551471 := bstep (se 1 (by rfl) ⟨1163603, by rfl⟩ : syracuseStep 1551471 = 2327207) B2327207
theorem B2616475 : Blo 1549472 2616475 := bstep (se 1 (by rfl) ⟨1962356, by rfl⟩ : syracuseStep 2616475 = 3924713) B3924713
theorem B5885095 : Blo 1549472 5885095 := bstep (se 1 (by rfl) ⟨4413821, by rfl⟩ : syracuseStep 5885095 = 8827643) B8827643
theorem B5229737 : Blo 1549472 5229737 := bstep (se 2 (by rfl) ⟨1961151, by rfl⟩ : syracuseStep 5229737 = 3922303) B3922303
theorem B5967101 : Blo 1549472 5967101 := bstep (se 3 (by rfl) ⟨1118831, by rfl⟩ : syracuseStep 5967101 = 2237663) B2237663
theorem B113184479 : Blo 1549472 113184479 := bstep (se 1 (by rfl) ⟨84888359, by rfl⟩ : syracuseStep 113184479 = 169776719) B169776719
theorem B113119091 : Blo 1549472 113119091 := bstep (se 1 (by rfl) ⟨84839318, by rfl⟩ : syracuseStep 113119091 = 169678637) B169678637
theorem B5230655 : Blo 1549472 5230655 := bstep (se 1 (by rfl) ⟨3922991, by rfl⟩ : syracuseStep 5230655 = 7845983) B7845983
theorem B2617447 : Blo 1549472 2617447 := bstep (se 1 (by rfl) ⟨1963085, by rfl⟩ : syracuseStep 2617447 = 3926171) B3926171
theorem B50958467 : Blo 1549472 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B3272903 : Blo 1549472 3272903 := bstep (se 1 (by rfl) ⟨2454677, by rfl⟩ : syracuseStep 3272903 = 4909355) B4909355
theorem B9425231 : Blo 1549472 9425231 := bstep (se 1 (by rfl) ⟨7068923, by rfl⟩ : syracuseStep 9425231 = 14137847) B14137847
theorem B8827325 : Blo 1549472 8827325 := bstep (se 3 (by rfl) ⟨1655123, by rfl⟩ : syracuseStep 8827325 = 3310247) B3310247
theorem B13251275 : Blo 1549472 13251275 := bstep (se 1 (by rfl) ⟨9938456, by rfl⟩ : syracuseStep 13251275 = 19876913) B19876913
theorem B60445709 : Blo 1549472 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B5231897 : Blo 1549472 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B344266051 : Blo 1549472 344266051 := bstep (se 1 (by rfl) ⟨258199538, by rfl⟩ : syracuseStep 344266051 = 516399077) B516399077
theorem B7845821 : Blo 1549472 7845821 := bstep (se 3 (by rfl) ⟨1471091, by rfl⟩ : syracuseStep 7845821 = 2942183) B2942183
theorem B6625243 : Blo 1549472 6625243 := bstep (se 1 (by rfl) ⟨4968932, by rfl⟩ : syracuseStep 6625243 = 9937865) B9937865
theorem B5887997 : Blo 1549472 5887997 := bstep (se 3 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 5887997 = 2207999) B2207999
theorem B16996499 : Blo 1549472 16996499 := bstep (se 1 (by rfl) ⟨12747374, by rfl⟩ : syracuseStep 16996499 = 25494749) B25494749
theorem B11934049 : Blo 1549472 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B102021605 : Blo 1549472 102021605 := bstep (se 4 (by rfl) ⟨9564525, by rfl⟩ : syracuseStep 102021605 = 19129051) B19129051
theorem B2325095 : Blo 1549472 2325095 := bstep (se 1 (by rfl) ⟨1743821, by rfl⟩ : syracuseStep 2325095 = 3487643) B3487643
theorem B3488615 : Blo 1549472 3488615 := bstep (se 1 (by rfl) ⟨2616461, by rfl⟩ : syracuseStep 3488615 = 5232923) B5232923
theorem B5307275 : Blo 1549472 5307275 := bstep (se 1 (by rfl) ⟨3980456, by rfl⟩ : syracuseStep 5307275 = 7960913) B7960913
theorem B5888983 : Blo 1549472 5888983 := bstep (se 1 (by rfl) ⟨4416737, by rfl⟩ : syracuseStep 5888983 = 8833475) B8833475
theorem B30211177 : Blo 1549472 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B7068779 : Blo 1549472 7068779 := bstep (se 1 (by rfl) ⟨5301584, by rfl⟩ : syracuseStep 7068779 = 10603169) B10603169
theorem B6626731 : Blo 1549472 6626731 := bstep (se 1 (by rfl) ⟨4970048, by rfl⟩ : syracuseStep 6626731 = 9940097) B9940097
theorem B9428399 : Blo 1549472 9428399 := bstep (se 1 (by rfl) ⟨7071299, by rfl⟩ : syracuseStep 9428399 = 14142599) B14142599
theorem B5889469 : Blo 1549472 5889469 := bstep (se 3 (by rfl) ⟨1104275, by rfl⟩ : syracuseStep 5889469 = 2208551) B2208551
theorem B2325983 : Blo 1549472 2325983 := bstep (se 1 (by rfl) ⟨1744487, by rfl⟩ : syracuseStep 2325983 = 3488975) B3488975
theorem B3489263 : Blo 1549472 3489263 := bstep (se 1 (by rfl) ⟨2616947, by rfl⟩ : syracuseStep 3489263 = 5233895) B5233895
theorem B2326043 : Blo 1549472 2326043 := bstep (se 1 (by rfl) ⟨1744532, by rfl⟩ : syracuseStep 2326043 = 3489065) B3489065
theorem B2326235 : Blo 1549472 2326235 := bstep (se 1 (by rfl) ⟨1744676, by rfl⟩ : syracuseStep 2326235 = 3489353) B3489353
theorem B2326463 : Blo 1549472 2326463 := bstep (se 1 (by rfl) ⟨1744847, by rfl⟩ : syracuseStep 2326463 = 3489695) B3489695
theorem B1744879 : Blo 1549472 1744879 := bstep (se 1 (by rfl) ⟨1308659, by rfl⟩ : syracuseStep 1744879 = 2617319) B2617319
theorem B3489785 : Blo 1549472 3489785 := bstep (se 2 (by rfl) ⟨1308669, by rfl⟩ : syracuseStep 3489785 = 2617339) B2617339
theorem B22347859 : Blo 1549472 22347859 := bstep (se 1 (by rfl) ⟨16760894, by rfl⟩ : syracuseStep 22347859 = 33521789) B33521789
theorem B3489875 : Blo 1549472 3489875 := bstep (se 1 (by rfl) ⟨2617406, by rfl⟩ : syracuseStep 3489875 = 5234813) B5234813
theorem B33972311 : Blo 1549472 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B5587051 : Blo 1549472 5587051 := bstep (se 1 (by rfl) ⟨4190288, by rfl⟩ : syracuseStep 5587051 = 8380577) B8380577
theorem B3489929 : Blo 1549472 3489929 := bstep (se 2 (by rfl) ⟨1308723, by rfl⟩ : syracuseStep 3489929 = 2617447) B2617447
theorem B6283487 : Blo 1549472 6283487 := bstep (se 1 (by rfl) ⟨4712615, by rfl⟩ : syracuseStep 6283487 = 9425231) B9425231
theorem B2327177 : Blo 1549472 2327177 := bstep (se 2 (by rfl) ⟨872691, by rfl⟩ : syracuseStep 2327177 = 1745383) B1745383
theorem B40297139 : Blo 1549472 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B8848115 : Blo 1549472 8848115 := bstep (se 1 (by rfl) ⟨6636086, by rfl⟩ : syracuseStep 8848115 = 13272173) B13272173
theorem B3490631 : Blo 1549472 3490631 := bstep (se 1 (by rfl) ⟨2617973, by rfl⟩ : syracuseStep 3490631 = 5235947) B5235947
theorem B39805789 : Blo 1549472 39805789 := bstep (se 3 (by rfl) ⟨7463585, by rfl⟩ : syracuseStep 39805789 = 14927171) B14927171
theorem B17909063 : Blo 1549472 17909063 := bstep (se 1 (by rfl) ⟨13431797, by rfl⟩ : syracuseStep 17909063 = 26863595) B26863595
theorem B3925331 : Blo 1549472 3925331 := bstep (se 1 (by rfl) ⟨2943998, by rfl⟩ : syracuseStep 3925331 = 5887997) B5887997
theorem B11330999 : Blo 1549472 11330999 := bstep (se 1 (by rfl) ⟨8498249, by rfl⟩ : syracuseStep 11330999 = 16996499) B16996499
theorem B5588435 : Blo 1549472 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B40281569 : Blo 1549472 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B1550063 : Blo 1549472 1550063 := bstep (se 1 (by rfl) ⟨1162547, by rfl⟩ : syracuseStep 1550063 = 2325095) B2325095
theorem B4712519 : Blo 1549472 4712519 := bstep (se 1 (by rfl) ⟨3534389, by rfl⟩ : syracuseStep 4712519 = 7068779) B7068779
theorem B6285599 : Blo 1549472 6285599 := bstep (se 1 (by rfl) ⟨4714199, by rfl⟩ : syracuseStep 6285599 = 9428399) B9428399
theorem B1550655 : Blo 1549472 1550655 := bstep (se 1 (by rfl) ⟨1162991, by rfl⟩ : syracuseStep 1550655 = 2325983) B2325983
theorem B1550695 : Blo 1549472 1550695 := bstep (se 1 (by rfl) ⟨1163021, by rfl⟩ : syracuseStep 1550695 = 2326043) B2326043
theorem B1550823 : Blo 1549472 1550823 := bstep (se 1 (by rfl) ⟨1163117, by rfl⟩ : syracuseStep 1550823 = 2326235) B2326235
theorem B8833657 : Blo 1549472 8833657 := bstep (se 2 (by rfl) ⟨3312621, by rfl⟩ : syracuseStep 8833657 = 6625243) B6625243
theorem B1550975 : Blo 1549472 1550975 := bstep (se 1 (by rfl) ⟨1163231, by rfl⟩ : syracuseStep 1550975 = 2326463) B2326463
theorem B2181935 : Blo 1549472 2181935 := bstep (se 1 (by rfl) ⟨1636451, by rfl⟩ : syracuseStep 2181935 = 3272903) B3272903
theorem B1551231 : Blo 1549472 1551231 := bstep (se 1 (by rfl) ⟨1163423, by rfl⟩ : syracuseStep 1551231 = 2326847) B2326847
theorem B5884883 : Blo 1549472 5884883 := bstep (se 1 (by rfl) ⟨4413662, by rfl⟩ : syracuseStep 5884883 = 8827325) B8827325
theorem B1551343 : Blo 1549472 1551343 := bstep (se 1 (by rfl) ⟨1163507, by rfl⟩ : syracuseStep 1551343 = 2327015) B2327015
theorem B15912065 : Blo 1549472 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B8834183 : Blo 1549472 8834183 := bstep (se 1 (by rfl) ⟨6625637, by rfl⟩ : syracuseStep 8834183 = 13251275) B13251275
theorem B1961759 : Blo 1549472 1961759 := bstep (se 1 (by rfl) ⟨1471319, by rfl⟩ : syracuseStep 1961759 = 2942639) B2942639
theorem B7851977 : Blo 1549472 7851977 := bstep (se 2 (by rfl) ⟨2944491, by rfl⟩ : syracuseStep 7851977 = 5888983) B5888983
theorem B5230547 : Blo 1549472 5230547 := bstep (se 1 (by rfl) ⟨3922910, by rfl⟩ : syracuseStep 5230547 = 7845821) B7845821
theorem B4534427 : Blo 1549472 4534427 := bstep (se 1 (by rfl) ⟨3400820, by rfl⟩ : syracuseStep 4534427 = 6801641) B6801641
theorem B68014403 : Blo 1549472 68014403 := bstep (se 1 (by rfl) ⟨51010802, by rfl⟩ : syracuseStep 68014403 = 102021605) B102021605
theorem B8835641 : Blo 1549472 8835641 := bstep (se 2 (by rfl) ⟨3313365, by rfl⟩ : syracuseStep 8835641 = 6626731) B6626731
theorem B7852625 : Blo 1549472 7852625 := bstep (se 2 (by rfl) ⟨2944734, by rfl⟩ : syracuseStep 7852625 = 5889469) B5889469
theorem B3486491 : Blo 1549472 3486491 := bstep (se 1 (by rfl) ⟨2614868, by rfl⟩ : syracuseStep 3486491 = 5229737) B5229737
theorem B3978067 : Blo 1549472 3978067 := bstep (se 1 (by rfl) ⟨2983550, by rfl⟩ : syracuseStep 3978067 = 5967101) B5967101
theorem B2208745 : Blo 1549472 2208745 := bstep (se 2 (by rfl) ⟨828279, by rfl⟩ : syracuseStep 2208745 = 1656559) B1656559
theorem B75412727 : Blo 1549472 75412727 := bstep (se 1 (by rfl) ⟨56559545, by rfl⟩ : syracuseStep 75412727 = 113119091) B113119091
theorem B3487103 : Blo 1549472 3487103 := bstep (se 1 (by rfl) ⟨2615327, by rfl⟩ : syracuseStep 3487103 = 5230655) B5230655
theorem B5232761 : Blo 1549472 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B5232815 : Blo 1549472 5232815 := bstep (se 1 (by rfl) ⟨3924611, by rfl⟩ : syracuseStep 5232815 = 7849223) B7849223
theorem B3487931 : Blo 1549472 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B3725615 : Blo 1549472 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B1743259 : Blo 1549472 1743259 := bstep (se 1 (by rfl) ⟨1307444, by rfl⟩ : syracuseStep 1743259 = 2614889) B2614889
theorem B5233193 : Blo 1549472 5233193 := bstep (se 2 (by rfl) ⟨1962447, by rfl⟩ : syracuseStep 5233193 = 3924895) B3924895
theorem B1677871 : Blo 1549472 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B22665977 : Blo 1549472 22665977 := bstep (se 2 (by rfl) ⟨8499741, by rfl⟩ : syracuseStep 22665977 = 16999483) B16999483
theorem B12737351 : Blo 1549472 12737351 := bstep (se 1 (by rfl) ⟨9553013, by rfl⟩ : syracuseStep 12737351 = 19106027) B19106027
theorem B3488633 : Blo 1549472 3488633 := bstep (se 2 (by rfl) ⟨1308237, by rfl⟩ : syracuseStep 3488633 = 2616475) B2616475
theorem B7846793 : Blo 1549472 7846793 := bstep (se 2 (by rfl) ⟨2942547, by rfl⟩ : syracuseStep 7846793 = 5885095) B5885095
theorem B2792503 : Blo 1549472 2792503 := bstep (se 1 (by rfl) ⟨2094377, by rfl⟩ : syracuseStep 2792503 = 4188755) B4188755
theorem B459021401 : Blo 1549472 459021401 := bstep (se 2 (by rfl) ⟨172133025, by rfl⟩ : syracuseStep 459021401 = 344266051) B344266051
theorem B2325743 : Blo 1549472 2325743 := bstep (se 1 (by rfl) ⟨1744307, by rfl⟩ : syracuseStep 2325743 = 3488615) B3488615
theorem B1744123 : Blo 1549472 1744123 := bstep (se 1 (by rfl) ⟨1308092, by rfl⟩ : syracuseStep 1744123 = 2616185) B2616185
theorem B3538183 : Blo 1549472 3538183 := bstep (se 1 (by rfl) ⟨2653637, by rfl⟩ : syracuseStep 3538183 = 5307275) B5307275
theorem B2326175 : Blo 1549472 2326175 := bstep (se 1 (by rfl) ⟨1744631, by rfl⟩ : syracuseStep 2326175 = 3489263) B3489263
theorem B75456319 : Blo 1549472 75456319 := bstep (se 1 (by rfl) ⟨56592239, by rfl⟩ : syracuseStep 75456319 = 113184479) B113184479
theorem B2326505 : Blo 1549472 2326505 := bstep (se 2 (by rfl) ⟨872439, by rfl⟩ : syracuseStep 2326505 = 1744879) B1744879
theorem B2326523 : Blo 1549472 2326523 := bstep (se 1 (by rfl) ⟨1744892, by rfl⟩ : syracuseStep 2326523 = 3489785) B3489785
theorem B2326583 : Blo 1549472 2326583 := bstep (se 1 (by rfl) ⟨1744937, by rfl⟩ : syracuseStep 2326583 = 3489875) B3489875
theorem B2326619 : Blo 1549472 2326619 := bstep (se 1 (by rfl) ⟨1744964, by rfl⟩ : syracuseStep 2326619 = 3489929) B3489929
theorem B3022951 : Blo 1549472 3022951 := bstep (se 1 (by rfl) ⟨2267213, by rfl⟩ : syracuseStep 3022951 = 4534427) B4534427
theorem B45342935 : Blo 1549472 45342935 := bstep (se 1 (by rfl) ⟨34007201, by rfl⟩ : syracuseStep 45342935 = 68014403) B68014403
theorem B5890427 : Blo 1549472 5890427 := bstep (se 1 (by rfl) ⟨4417820, by rfl⟩ : syracuseStep 5890427 = 8835641) B8835641
theorem B5235083 : Blo 1549472 5235083 := bstep (se 1 (by rfl) ⟨3926312, by rfl⟩ : syracuseStep 5235083 = 7852625) B7852625
theorem B5898743 : Blo 1549472 5898743 := bstep (se 1 (by rfl) ⟨4424057, by rfl⟩ : syracuseStep 5898743 = 8848115) B8848115
theorem B2327087 : Blo 1549472 2327087 := bstep (se 1 (by rfl) ⟨1745315, by rfl⟩ : syracuseStep 2327087 = 3490631) B3490631
theorem B2237161 : Blo 1549472 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B50275151 : Blo 1549472 50275151 := bstep (se 1 (by rfl) ⟨37706363, by rfl⟩ : syracuseStep 50275151 = 75412727) B75412727
theorem B7553999 : Blo 1549472 7553999 := bstep (se 1 (by rfl) ⟨5665499, by rfl⟩ : syracuseStep 7553999 = 11330999) B11330999
theorem B26854379 : Blo 1549472 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B306014267 : Blo 1549472 306014267 := bstep (se 1 (by rfl) ⟨229510700, by rfl⟩ : syracuseStep 306014267 = 459021401) B459021401
theorem B5818493 : Blo 1549472 5818493 := bstep (se 3 (by rfl) ⟨1090967, by rfl⟩ : syracuseStep 5818493 = 2181935) B2181935
theorem B1550495 : Blo 1549472 1550495 := bstep (se 1 (by rfl) ⟨1162871, by rfl⟩ : syracuseStep 1550495 = 2325743) B2325743
theorem B100608425 : Blo 1549472 100608425 := bstep (se 2 (by rfl) ⟨37728159, by rfl⟩ : syracuseStep 100608425 = 75456319) B75456319
theorem B1550783 : Blo 1549472 1550783 := bstep (se 1 (by rfl) ⟨1163087, by rfl⟩ : syracuseStep 1550783 = 2326175) B2326175
theorem B1551003 : Blo 1549472 1551003 := bstep (se 1 (by rfl) ⟨1163252, by rfl⟩ : syracuseStep 1551003 = 2326505) B2326505
theorem B1551015 : Blo 1549472 1551015 := bstep (se 1 (by rfl) ⟨1163261, by rfl⟩ : syracuseStep 1551015 = 2326523) B2326523
theorem B29797145 : Blo 1549472 29797145 := bstep (se 2 (by rfl) ⟨11173929, by rfl⟩ : syracuseStep 29797145 = 22347859) B22347859
theorem B7449401 : Blo 1549472 7449401 := bstep (se 2 (by rfl) ⟨2793525, by rfl⟩ : syracuseStep 7449401 = 5587051) B5587051
theorem B4188991 : Blo 1549472 4188991 := bstep (se 1 (by rfl) ⟨3141743, by rfl⟩ : syracuseStep 4188991 = 6283487) B6283487
theorem B1551451 : Blo 1549472 1551451 := bstep (se 1 (by rfl) ⟨1163588, by rfl⟩ : syracuseStep 1551451 = 2327177) B2327177
theorem B26864759 : Blo 1549472 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B11939375 : Blo 1549472 11939375 := bstep (se 1 (by rfl) ⟨8954531, by rfl⟩ : syracuseStep 11939375 = 17909063) B17909063
theorem B2616887 : Blo 1549472 2616887 := bstep (se 1 (by rfl) ⟨1962665, by rfl⟩ : syracuseStep 2616887 = 3925331) B3925331
theorem B5304089 : Blo 1549472 5304089 := bstep (se 2 (by rfl) ⟨1989033, by rfl⟩ : syracuseStep 5304089 = 3978067) B3978067
theorem B2944993 : Blo 1549472 2944993 := bstep (se 2 (by rfl) ⟨1104372, by rfl⟩ : syracuseStep 2944993 = 2208745) B2208745
theorem B3141679 : Blo 1549472 3141679 := bstep (se 1 (by rfl) ⟨2356259, by rfl⟩ : syracuseStep 3141679 = 4712519) B4712519
theorem B3723337 : Blo 1549472 3723337 := bstep (se 2 (by rfl) ⟨1396251, by rfl⟩ : syracuseStep 3723337 = 2792503) B2792503
theorem B4190399 : Blo 1549472 4190399 := bstep (se 1 (by rfl) ⟨3142799, by rfl⟩ : syracuseStep 4190399 = 6285599) B6285599
theorem B15110651 : Blo 1549472 15110651 := bstep (se 1 (by rfl) ⟨11332988, by rfl⟩ : syracuseStep 15110651 = 22665977) B22665977
theorem B8491567 : Blo 1549472 8491567 := bstep (se 1 (by rfl) ⟨6368675, by rfl⟩ : syracuseStep 8491567 = 12737351) B12737351
theorem B5231195 : Blo 1549472 5231195 := bstep (se 1 (by rfl) ⟨3923396, by rfl⟩ : syracuseStep 5231195 = 7846793) B7846793
theorem B5231357 : Blo 1549472 5231357 := bstep (se 3 (by rfl) ⟨980879, by rfl⟩ : syracuseStep 5231357 = 1961759) B1961759
theorem B3487031 : Blo 1549472 3487031 := bstep (se 1 (by rfl) ⟨2615273, by rfl⟩ : syracuseStep 3487031 = 5230547) B5230547
theorem B22648207 : Blo 1549472 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B42432173 : Blo 1549472 42432173 := bstep (se 3 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 42432173 = 15912065) B15912065
theorem B2324327 : Blo 1549472 2324327 := bstep (se 1 (by rfl) ⟨1743245, by rfl⟩ : syracuseStep 2324327 = 3486491) B3486491
theorem B2324345 : Blo 1549472 2324345 := bstep (se 2 (by rfl) ⟨871629, by rfl⟩ : syracuseStep 2324345 = 1743259) B1743259
theorem B9934973 : Blo 1549472 9934973 := bstep (se 3 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 9934973 = 3725615) B3725615
theorem B11778209 : Blo 1549472 11778209 := bstep (se 2 (by rfl) ⟨4416828, by rfl⟩ : syracuseStep 11778209 = 8833657) B8833657
theorem B2324735 : Blo 1549472 2324735 := bstep (se 1 (by rfl) ⟨1743551, by rfl⟩ : syracuseStep 2324735 = 3487103) B3487103
theorem B3725623 : Blo 1549472 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B53074385 : Blo 1549472 53074385 := bstep (se 2 (by rfl) ⟨19902894, by rfl⟩ : syracuseStep 53074385 = 39805789) B39805789
theorem B3488507 : Blo 1549472 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B3488543 : Blo 1549472 3488543 := bstep (se 1 (by rfl) ⟨2616407, by rfl⟩ : syracuseStep 3488543 = 5232815) B5232815
theorem B2325287 : Blo 1549472 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B2325497 : Blo 1549472 2325497 := bstep (se 2 (by rfl) ⟨872061, by rfl⟩ : syracuseStep 2325497 = 1744123) B1744123
theorem B4717577 : Blo 1549472 4717577 := bstep (se 2 (by rfl) ⟨1769091, by rfl⟩ : syracuseStep 4717577 = 3538183) B3538183
theorem B3488795 : Blo 1549472 3488795 := bstep (se 1 (by rfl) ⟨2616596, by rfl⟩ : syracuseStep 3488795 = 5233193) B5233193
theorem B2325755 : Blo 1549472 2325755 := bstep (se 1 (by rfl) ⟨1744316, by rfl⟩ : syracuseStep 2325755 = 3488633) B3488633
theorem B3923255 : Blo 1549472 3923255 := bstep (se 1 (by rfl) ⟨2942441, by rfl⟩ : syracuseStep 3923255 = 5884883) B5884883
theorem B5889455 : Blo 1549472 5889455 := bstep (se 1 (by rfl) ⟨4417091, by rfl⟩ : syracuseStep 5889455 = 8834183) B8834183
theorem B5234651 : Blo 1549472 5234651 := bstep (se 1 (by rfl) ⟨3925988, by rfl⟩ : syracuseStep 5234651 = 7851977) B7851977
theorem B4964449 : Blo 1549472 4964449 := bstep (se 2 (by rfl) ⟨1861668, by rfl⟩ : syracuseStep 4964449 = 3723337) B3723337
theorem B2793599 : Blo 1549472 2793599 := bstep (se 1 (by rfl) ⟨2095199, by rfl⟩ : syracuseStep 2793599 = 4190399) B4190399
theorem B4030601 : Blo 1549472 4030601 := bstep (se 2 (by rfl) ⟨1511475, by rfl⟩ : syracuseStep 4030601 = 3022951) B3022951
theorem B30228623 : Blo 1549472 30228623 := bstep (se 1 (by rfl) ⟨22671467, by rfl⟩ : syracuseStep 30228623 = 45342935) B45342935
theorem B3490055 : Blo 1549472 3490055 := bstep (se 1 (by rfl) ⟨2617541, by rfl⟩ : syracuseStep 3490055 = 5235083) B5235083
theorem B15515981 : Blo 1549472 15515981 := bstep (se 3 (by rfl) ⟨2909246, by rfl⟩ : syracuseStep 15515981 = 5818493) B5818493
theorem B3932495 : Blo 1549472 3932495 := bstep (se 1 (by rfl) ⟨2949371, by rfl⟩ : syracuseStep 3932495 = 5898743) B5898743
theorem B11322089 : Blo 1549472 11322089 := bstep (se 2 (by rfl) ⟨4245783, by rfl⟩ : syracuseStep 11322089 = 8491567) B8491567
theorem B2982881 : Blo 1549472 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B28288115 : Blo 1549472 28288115 := bstep (se 1 (by rfl) ⟨21216086, by rfl⟩ : syracuseStep 28288115 = 42432173) B42432173
theorem B1549551 : Blo 1549472 1549551 := bstep (se 1 (by rfl) ⟨1162163, by rfl⟩ : syracuseStep 1549551 = 2324327) B2324327
theorem B1549563 : Blo 1549472 1549563 := bstep (se 1 (by rfl) ⟨1162172, by rfl⟩ : syracuseStep 1549563 = 2324345) B2324345
theorem B1549823 : Blo 1549472 1549823 := bstep (se 1 (by rfl) ⟨1162367, by rfl⟩ : syracuseStep 1549823 = 2324735) B2324735
theorem B35382923 : Blo 1549472 35382923 := bstep (se 1 (by rfl) ⟨26537192, by rfl⟩ : syracuseStep 35382923 = 53074385) B53074385
theorem B30197609 : Blo 1549472 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B1550191 : Blo 1549472 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B4966267 : Blo 1549472 4966267 := bstep (se 1 (by rfl) ⟨3724700, by rfl⟩ : syracuseStep 4966267 = 7449401) B7449401
theorem B1550331 : Blo 1549472 1550331 := bstep (se 1 (by rfl) ⟨1162748, by rfl⟩ : syracuseStep 1550331 = 2325497) B2325497
theorem B17909839 : Blo 1549472 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B1550503 : Blo 1549472 1550503 := bstep (se 1 (by rfl) ⟨1162877, by rfl⟩ : syracuseStep 1550503 = 2325755) B2325755
theorem B2615503 : Blo 1549472 2615503 := bstep (se 1 (by rfl) ⟨1961627, by rfl⟩ : syracuseStep 2615503 = 3923255) B3923255
theorem B3926303 : Blo 1549472 3926303 := bstep (se 1 (by rfl) ⟨2944727, by rfl⟩ : syracuseStep 3926303 = 5889455) B5889455
theorem B3926657 : Blo 1549472 3926657 := bstep (se 2 (by rfl) ⟨1472496, by rfl⟩ : syracuseStep 3926657 = 2944993) B2944993
theorem B1551055 : Blo 1549472 1551055 := bstep (se 1 (by rfl) ⟨1163291, by rfl⟩ : syracuseStep 1551055 = 2326583) B2326583
theorem B1551079 : Blo 1549472 1551079 := bstep (se 1 (by rfl) ⟨1163309, by rfl⟩ : syracuseStep 1551079 = 2326619) B2326619
theorem B4188905 : Blo 1549472 4188905 := bstep (se 2 (by rfl) ⟨1570839, by rfl⟩ : syracuseStep 4188905 = 3141679) B3141679
theorem B3926951 : Blo 1549472 3926951 := bstep (se 1 (by rfl) ⟨2945213, by rfl⟩ : syracuseStep 3926951 = 5890427) B5890427
theorem B1551391 : Blo 1549472 1551391 := bstep (se 1 (by rfl) ⟨1163543, by rfl⟩ : syracuseStep 1551391 = 2327087) B2327087
theorem B4967497 : Blo 1549472 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B33516767 : Blo 1549472 33516767 := bstep (se 1 (by rfl) ⟨25137575, by rfl⟩ : syracuseStep 33516767 = 50275151) B50275151
theorem B17902919 : Blo 1549472 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B204009511 : Blo 1549472 204009511 := bstep (se 1 (by rfl) ⟨153007133, by rfl⟩ : syracuseStep 204009511 = 306014267) B306014267
theorem B6623315 : Blo 1549472 6623315 := bstep (se 1 (by rfl) ⟨4967486, by rfl⟩ : syracuseStep 6623315 = 9934973) B9934973
theorem B7852139 : Blo 1549472 7852139 := bstep (se 1 (by rfl) ⟨5889104, by rfl⟩ : syracuseStep 7852139 = 11778209) B11778209
theorem B67072283 : Blo 1549472 67072283 := bstep (se 1 (by rfl) ⟨50304212, by rfl⟩ : syracuseStep 67072283 = 100608425) B100608425
theorem B7959583 : Blo 1549472 7959583 := bstep (se 1 (by rfl) ⟨5969687, by rfl⟩ : syracuseStep 7959583 = 11939375) B11939375
theorem B3536059 : Blo 1549472 3536059 := bstep (se 1 (by rfl) ⟨2652044, by rfl⟩ : syracuseStep 3536059 = 5304089) B5304089
theorem B12580205 : Blo 1549472 12580205 := bstep (se 3 (by rfl) ⟨2358788, by rfl⟩ : syracuseStep 12580205 = 4717577) B4717577
theorem B10073767 : Blo 1549472 10073767 := bstep (se 1 (by rfl) ⟨7555325, by rfl⟩ : syracuseStep 10073767 = 15110651) B15110651
theorem B3487463 : Blo 1549472 3487463 := bstep (se 1 (by rfl) ⟨2615597, by rfl⟩ : syracuseStep 3487463 = 5231195) B5231195
theorem B3487571 : Blo 1549472 3487571 := bstep (se 1 (by rfl) ⟨2615678, by rfl⟩ : syracuseStep 3487571 = 5231357) B5231357
theorem B2324687 : Blo 1549472 2324687 := bstep (se 1 (by rfl) ⟨1743515, by rfl⟩ : syracuseStep 2324687 = 3487031) B3487031
theorem B5585321 : Blo 1549472 5585321 := bstep (se 2 (by rfl) ⟨2094495, by rfl⟩ : syracuseStep 5585321 = 4188991) B4188991
theorem B2325671 : Blo 1549472 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B19864763 : Blo 1549472 19864763 := bstep (se 1 (by rfl) ⟨14898572, by rfl⟩ : syracuseStep 19864763 = 29797145) B29797145
theorem B2325695 : Blo 1549472 2325695 := bstep (se 1 (by rfl) ⟨1744271, by rfl⟩ : syracuseStep 2325695 = 3488543) B3488543
theorem B2325863 : Blo 1549472 2325863 := bstep (se 1 (by rfl) ⟨1744397, by rfl⟩ : syracuseStep 2325863 = 3488795) B3488795
theorem B1744591 : Blo 1549472 1744591 := bstep (se 1 (by rfl) ⟨1308443, by rfl⟩ : syracuseStep 1744591 = 2616887) B2616887
theorem B20143997 : Blo 1549472 20143997 := bstep (se 3 (by rfl) ⟨3776999, by rfl⟩ : syracuseStep 20143997 = 7553999) B7553999
theorem B3489767 : Blo 1549472 3489767 := bstep (se 1 (by rfl) ⟨2617325, by rfl⟩ : syracuseStep 3489767 = 5234651) B5234651
theorem B4415543 : Blo 1549472 4415543 := bstep (se 1 (by rfl) ⟨3311657, by rfl⟩ : syracuseStep 4415543 = 6623315) B6623315
theorem B5234759 : Blo 1549472 5234759 := bstep (se 1 (by rfl) ⟨3926069, by rfl⟩ : syracuseStep 5234759 = 7852139) B7852139
theorem B20152415 : Blo 1549472 20152415 := bstep (se 1 (by rfl) ⟨15114311, by rfl⟩ : syracuseStep 20152415 = 30228623) B30228623
theorem B23879785 : Blo 1549472 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B6619265 : Blo 1549472 6619265 := bstep (se 2 (by rfl) ⟨2482224, by rfl⟩ : syracuseStep 6619265 = 4964449) B4964449
theorem B2326703 : Blo 1549472 2326703 := bstep (se 1 (by rfl) ⟨1745027, by rfl⟩ : syracuseStep 2326703 = 3490055) B3490055
theorem B2621663 : Blo 1549472 2621663 := bstep (se 1 (by rfl) ⟨1966247, by rfl⟩ : syracuseStep 2621663 = 3932495) B3932495
theorem B26493317 : Blo 1549472 26493317 := bstep (se 4 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 26493317 = 4967497) B4967497
theorem B18858743 : Blo 1549472 18858743 := bstep (se 1 (by rfl) ⟨14144057, by rfl⟩ : syracuseStep 18858743 = 28288115) B28288115
theorem B33547213 : Blo 1549472 33547213 := bstep (se 3 (by rfl) ⟨6290102, by rfl⟩ : syracuseStep 33547213 = 12580205) B12580205
theorem B14894189 : Blo 1549472 14894189 := bstep (se 3 (by rfl) ⟨2792660, by rfl⟩ : syracuseStep 14894189 = 5585321) B5585321
theorem B42993077 : Blo 1549472 42993077 := bstep (se 5 (by rfl) ⟨2015300, by rfl⟩ : syracuseStep 42993077 = 4030601) B4030601
theorem B1549791 : Blo 1549472 1549791 := bstep (se 1 (by rfl) ⟨1162343, by rfl⟩ : syracuseStep 1549791 = 2324687) B2324687
theorem B1550447 : Blo 1549472 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B1550463 : Blo 1549472 1550463 := bstep (se 1 (by rfl) ⟨1162847, by rfl⟩ : syracuseStep 1550463 = 2325695) B2325695
theorem B1550575 : Blo 1549472 1550575 := bstep (se 1 (by rfl) ⟨1162931, by rfl⟩ : syracuseStep 1550575 = 2325863) B2325863
theorem B6621689 : Blo 1549472 6621689 := bstep (se 2 (by rfl) ⟨2483133, by rfl⟩ : syracuseStep 6621689 = 4966267) B4966267
theorem B13429331 : Blo 1549472 13429331 := bstep (se 1 (by rfl) ⟨10071998, by rfl⟩ : syracuseStep 13429331 = 20143997) B20143997
theorem B1862399 : Blo 1549472 1862399 := bstep (se 1 (by rfl) ⟨1396799, by rfl⟩ : syracuseStep 1862399 = 2793599) B2793599
theorem B44714855 : Blo 1549472 44714855 := bstep (se 1 (by rfl) ⟨33536141, by rfl⟩ : syracuseStep 44714855 = 67072283) B67072283
theorem B7548059 : Blo 1549472 7548059 := bstep (se 1 (by rfl) ⟨5661044, by rfl⟩ : syracuseStep 7548059 = 11322089) B11322089
theorem B23588615 : Blo 1549472 23588615 := bstep (se 1 (by rfl) ⟨17691461, by rfl⟩ : syracuseStep 23588615 = 35382923) B35382923
theorem B20131739 : Blo 1549472 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B10612777 : Blo 1549472 10612777 := bstep (se 2 (by rfl) ⟨3979791, by rfl⟩ : syracuseStep 10612777 = 7959583) B7959583
theorem B2617535 : Blo 1549472 2617535 := bstep (se 1 (by rfl) ⟨1963151, by rfl⟩ : syracuseStep 2617535 = 3926303) B3926303
theorem B4714745 : Blo 1549472 4714745 := bstep (se 2 (by rfl) ⟨1768029, by rfl⟩ : syracuseStep 4714745 = 3536059) B3536059
theorem B2617771 : Blo 1549472 2617771 := bstep (se 1 (by rfl) ⟨1963328, by rfl⟩ : syracuseStep 2617771 = 3926657) B3926657
theorem B2617967 : Blo 1549472 2617967 := bstep (se 1 (by rfl) ⟨1963475, by rfl⟩ : syracuseStep 2617967 = 3926951) B3926951
theorem B13243175 : Blo 1549472 13243175 := bstep (se 1 (by rfl) ⟨9932381, by rfl⟩ : syracuseStep 13243175 = 19864763) B19864763
theorem B22344511 : Blo 1549472 22344511 := bstep (se 1 (by rfl) ⟨16758383, by rfl⟩ : syracuseStep 22344511 = 33516767) B33516767
theorem B13431689 : Blo 1549472 13431689 := bstep (se 2 (by rfl) ⟨5036883, by rfl⟩ : syracuseStep 13431689 = 10073767) B10073767
theorem B272012681 : Blo 1549472 272012681 := bstep (se 2 (by rfl) ⟨102004755, by rfl⟩ : syracuseStep 272012681 = 204009511) B204009511
theorem B10343987 : Blo 1549472 10343987 := bstep (se 1 (by rfl) ⟨7757990, by rfl⟩ : syracuseStep 10343987 = 15515981) B15515981
theorem B3487337 : Blo 1549472 3487337 := bstep (se 2 (by rfl) ⟨1307751, by rfl⟩ : syracuseStep 3487337 = 2615503) B2615503
theorem B1988587 : Blo 1549472 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B2324975 : Blo 1549472 2324975 := bstep (se 1 (by rfl) ⟨1743731, by rfl⟩ : syracuseStep 2324975 = 3487463) B3487463
theorem B2325047 : Blo 1549472 2325047 := bstep (se 1 (by rfl) ⟨1743785, by rfl⟩ : syracuseStep 2325047 = 3487571) B3487571
theorem B2792603 : Blo 1549472 2792603 := bstep (se 1 (by rfl) ⟨2094452, by rfl⟩ : syracuseStep 2792603 = 4188905) B4188905
theorem B11935279 : Blo 1549472 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B2326121 : Blo 1549472 2326121 := bstep (se 2 (by rfl) ⟨872295, by rfl⟩ : syracuseStep 2326121 = 1744591) B1744591
theorem B2326511 : Blo 1549472 2326511 := bstep (se 1 (by rfl) ⟨1744883, by rfl⟩ : syracuseStep 2326511 = 3489767) B3489767
theorem B3489839 : Blo 1549472 3489839 := bstep (se 1 (by rfl) ⟨2617379, by rfl⟩ : syracuseStep 3489839 = 5234759) B5234759
theorem B13434943 : Blo 1549472 13434943 := bstep (se 1 (by rfl) ⟨10076207, by rfl⟩ : syracuseStep 13434943 = 20152415) B20152415
theorem B1745023 : Blo 1549472 1745023 := bstep (se 1 (by rfl) ⟨1308767, by rfl⟩ : syracuseStep 1745023 = 2617535) B2617535
theorem B17662211 : Blo 1549472 17662211 := bstep (se 1 (by rfl) ⟨13246658, by rfl⟩ : syracuseStep 17662211 = 26493317) B26493317
theorem B7446941 : Blo 1549472 7446941 := bstep (se 3 (by rfl) ⟨1396301, by rfl⟩ : syracuseStep 7446941 = 2792603) B2792603
theorem B1745311 : Blo 1549472 1745311 := bstep (se 1 (by rfl) ⟨1308983, by rfl⟩ : syracuseStep 1745311 = 2617967) B2617967
theorem B3490361 : Blo 1549472 3490361 := bstep (se 2 (by rfl) ⟨1308885, by rfl⟩ : syracuseStep 3490361 = 2617771) B2617771
theorem B8954459 : Blo 1549472 8954459 := bstep (se 1 (by rfl) ⟨6715844, by rfl⟩ : syracuseStep 8954459 = 13431689) B13431689
theorem B9929459 : Blo 1549472 9929459 := bstep (se 1 (by rfl) ⟨7447094, by rfl⟩ : syracuseStep 9929459 = 14894189) B14894189
theorem B114648205 : Blo 1549472 114648205 := bstep (se 3 (by rfl) ⟨21496538, by rfl⟩ : syracuseStep 114648205 = 42993077) B42993077
theorem B44729617 : Blo 1549472 44729617 := bstep (se 2 (by rfl) ⟨16773606, by rfl⟩ : syracuseStep 44729617 = 33547213) B33547213
theorem B1549983 : Blo 1549472 1549983 := bstep (se 1 (by rfl) ⟨1162487, by rfl⟩ : syracuseStep 1549983 = 2324975) B2324975
theorem B1550031 : Blo 1549472 1550031 := bstep (se 1 (by rfl) ⟨1162523, by rfl⟩ : syracuseStep 1550031 = 2325047) B2325047
theorem B4966397 : Blo 1549472 4966397 := bstep (se 3 (by rfl) ⟨931199, by rfl⟩ : syracuseStep 4966397 = 1862399) B1862399
theorem B5032039 : Blo 1549472 5032039 := bstep (se 1 (by rfl) ⟨3774029, by rfl⟩ : syracuseStep 5032039 = 7548059) B7548059
theorem B1550747 : Blo 1549472 1550747 := bstep (se 1 (by rfl) ⟨1163060, by rfl⟩ : syracuseStep 1550747 = 2326121) B2326121
theorem B13421159 : Blo 1549472 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B1551007 : Blo 1549472 1551007 := bstep (se 1 (by rfl) ⟨1163255, by rfl⟩ : syracuseStep 1551007 = 2326511) B2326511
theorem B2943695 : Blo 1549472 2943695 := bstep (se 1 (by rfl) ⟨2207771, by rfl⟩ : syracuseStep 2943695 = 4415543) B4415543
theorem B14150369 : Blo 1549472 14150369 := bstep (se 2 (by rfl) ⟨5306388, by rfl⟩ : syracuseStep 14150369 = 10612777) B10612777
theorem B1551135 : Blo 1549472 1551135 := bstep (se 1 (by rfl) ⟨1163351, by rfl⟩ : syracuseStep 1551135 = 2326703) B2326703
theorem B1747775 : Blo 1549472 1747775 := bstep (se 1 (by rfl) ⟨1310831, by rfl⟩ : syracuseStep 1747775 = 2621663) B2621663
theorem B63654821 : Blo 1549472 63654821 := bstep (se 4 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 63654821 = 11935279) B11935279
theorem B181341787 : Blo 1549472 181341787 := bstep (se 1 (by rfl) ⟨136006340, by rfl⟩ : syracuseStep 181341787 = 272012681) B272012681
theorem B17657837 : Blo 1549472 17657837 := bstep (se 3 (by rfl) ⟨3310844, by rfl⟩ : syracuseStep 17657837 = 6621689) B6621689
theorem B62902973 : Blo 1549472 62902973 := bstep (se 3 (by rfl) ⟨11794307, by rfl⟩ : syracuseStep 62902973 = 23588615) B23588615
theorem B2651449 : Blo 1549472 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B4412843 : Blo 1549472 4412843 := bstep (se 1 (by rfl) ⟨3309632, by rfl⟩ : syracuseStep 4412843 = 6619265) B6619265
theorem B31839713 : Blo 1549472 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B12572495 : Blo 1549472 12572495 := bstep (se 1 (by rfl) ⟨9429371, by rfl⟩ : syracuseStep 12572495 = 18858743) B18858743
theorem B8828783 : Blo 1549472 8828783 := bstep (se 1 (by rfl) ⟨6621587, by rfl⟩ : syracuseStep 8828783 = 13243175) B13243175
theorem B12572653 : Blo 1549472 12572653 := bstep (se 3 (by rfl) ⟨2357372, by rfl⟩ : syracuseStep 12572653 = 4714745) B4714745
theorem B6895991 : Blo 1549472 6895991 := bstep (se 1 (by rfl) ⟨5171993, by rfl⟩ : syracuseStep 6895991 = 10343987) B10343987
theorem B2324891 : Blo 1549472 2324891 := bstep (se 1 (by rfl) ⟨1743668, by rfl⟩ : syracuseStep 2324891 = 3487337) B3487337
theorem B29792681 : Blo 1549472 29792681 := bstep (se 2 (by rfl) ⟨11172255, by rfl⟩ : syracuseStep 29792681 = 22344511) B22344511
theorem B8952887 : Blo 1549472 8952887 := bstep (se 1 (by rfl) ⟨6714665, by rfl⟩ : syracuseStep 8952887 = 13429331) B13429331
theorem B29809903 : Blo 1549472 29809903 := bstep (se 1 (by rfl) ⟨22357427, by rfl⟩ : syracuseStep 29809903 = 44714855) B44714855
theorem B2326559 : Blo 1549472 2326559 := bstep (se 1 (by rfl) ⟨1744919, by rfl⟩ : syracuseStep 2326559 = 3489839) B3489839
theorem B6709385 : Blo 1549472 6709385 := bstep (se 2 (by rfl) ⟨2516019, by rfl⟩ : syracuseStep 6709385 = 5032039) B5032039
theorem B2326697 : Blo 1549472 2326697 := bstep (se 2 (by rfl) ⟨872511, by rfl⟩ : syracuseStep 2326697 = 1745023) B1745023
theorem B4964627 : Blo 1549472 4964627 := bstep (se 1 (by rfl) ⟨3723470, by rfl⟩ : syracuseStep 4964627 = 7446941) B7446941
theorem B2326907 : Blo 1549472 2326907 := bstep (se 1 (by rfl) ⟨1745180, by rfl⟩ : syracuseStep 2326907 = 3490361) B3490361
theorem B41935315 : Blo 1549472 41935315 := bstep (se 1 (by rfl) ⟨31451486, by rfl⟩ : syracuseStep 41935315 = 62902973) B62902973
theorem B6619639 : Blo 1549472 6619639 := bstep (se 1 (by rfl) ⟨4964729, by rfl⟩ : syracuseStep 6619639 = 9929459) B9929459
theorem B2327081 : Blo 1549472 2327081 := bstep (se 2 (by rfl) ⟨872655, by rfl⟩ : syracuseStep 2327081 = 1745311) B1745311
theorem B2941895 : Blo 1549472 2941895 := bstep (se 1 (by rfl) ⟨2206421, by rfl⟩ : syracuseStep 2941895 = 4412843) B4412843
theorem B21226475 : Blo 1549472 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B8381663 : Blo 1549472 8381663 := bstep (se 1 (by rfl) ⟨6286247, by rfl⟩ : syracuseStep 8381663 = 12572495) B12572495
theorem B3310931 : Blo 1549472 3310931 := bstep (se 1 (by rfl) ⟨2483198, by rfl⟩ : syracuseStep 3310931 = 4966397) B4966397
theorem B152864273 : Blo 1549472 152864273 := bstep (se 2 (by rfl) ⟨57324102, by rfl⟩ : syracuseStep 152864273 = 114648205) B114648205
theorem B4597327 : Blo 1549472 4597327 := bstep (se 1 (by rfl) ⟨3447995, by rfl⟩ : syracuseStep 4597327 = 6895991) B6895991
theorem B1549927 : Blo 1549472 1549927 := bstep (se 1 (by rfl) ⟨1162445, by rfl⟩ : syracuseStep 1549927 = 2324891) B2324891
theorem B59639489 : Blo 1549472 59639489 := bstep (se 2 (by rfl) ⟨22364808, by rfl⟩ : syracuseStep 59639489 = 44729617) B44729617
theorem B8947439 : Blo 1549472 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B42436547 : Blo 1549472 42436547 := bstep (se 1 (by rfl) ⟨31827410, by rfl⟩ : syracuseStep 42436547 = 63654821) B63654821
theorem B241789049 : Blo 1549472 241789049 := bstep (se 2 (by rfl) ⟨90670893, by rfl⟩ : syracuseStep 241789049 = 181341787) B181341787
theorem B16763537 : Blo 1549472 16763537 := bstep (se 2 (by rfl) ⟨6286326, by rfl⟩ : syracuseStep 16763537 = 12572653) B12572653
theorem B23874365 : Blo 1549472 23874365 := bstep (se 3 (by rfl) ⟨4476443, by rfl⟩ : syracuseStep 23874365 = 8952887) B8952887
theorem B11774807 : Blo 1549472 11774807 := bstep (se 1 (by rfl) ⟨8831105, by rfl⟩ : syracuseStep 11774807 = 17662211) B17662211
theorem B5885855 : Blo 1549472 5885855 := bstep (se 1 (by rfl) ⟨4414391, by rfl⟩ : syracuseStep 5885855 = 8828783) B8828783
theorem B19861787 : Blo 1549472 19861787 := bstep (se 1 (by rfl) ⟨14896340, by rfl⟩ : syracuseStep 19861787 = 29792681) B29792681
theorem B3535265 : Blo 1549472 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B1962463 : Blo 1549472 1962463 := bstep (se 1 (by rfl) ⟨1471847, by rfl⟩ : syracuseStep 1962463 = 2943695) B2943695
theorem B9433579 : Blo 1549472 9433579 := bstep (se 1 (by rfl) ⟨7075184, by rfl⟩ : syracuseStep 9433579 = 14150369) B14150369
theorem B17913257 : Blo 1549472 17913257 := bstep (se 2 (by rfl) ⟨6717471, by rfl⟩ : syracuseStep 17913257 = 13434943) B13434943
theorem B5969639 : Blo 1549472 5969639 := bstep (se 1 (by rfl) ⟨4477229, by rfl⟩ : syracuseStep 5969639 = 8954459) B8954459
theorem B39746537 : Blo 1549472 39746537 := bstep (se 2 (by rfl) ⟨14904951, by rfl⟩ : syracuseStep 39746537 = 29809903) B29809903
theorem B4660733 : Blo 1549472 4660733 := bstep (se 3 (by rfl) ⟨873887, by rfl⟩ : syracuseStep 4660733 = 1747775) B1747775
theorem B11771891 : Blo 1549472 11771891 := bstep (se 1 (by rfl) ⟨8828918, by rfl⟩ : syracuseStep 11771891 = 17657837) B17657837
theorem B4472923 : Blo 1549472 4472923 := bstep (se 1 (by rfl) ⟨3354692, by rfl⟩ : syracuseStep 4472923 = 6709385) B6709385
theorem B3309751 : Blo 1549472 3309751 := bstep (se 1 (by rfl) ⟨2482313, by rfl⟩ : syracuseStep 3309751 = 4964627) B4964627
theorem B5587775 : Blo 1549472 5587775 := bstep (se 1 (by rfl) ⟨4190831, by rfl⟩ : syracuseStep 5587775 = 8381663) B8381663
theorem B101909515 : Blo 1549472 101909515 := bstep (se 1 (by rfl) ⟨76432136, by rfl⟩ : syracuseStep 101909515 = 152864273) B152864273
theorem B5964959 : Blo 1549472 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B11175691 : Blo 1549472 11175691 := bstep (se 1 (by rfl) ⟨8381768, by rfl⟩ : syracuseStep 11175691 = 16763537) B16763537
theorem B7849871 : Blo 1549472 7849871 := bstep (se 1 (by rfl) ⟨5887403, by rfl⟩ : syracuseStep 7849871 = 11774807) B11774807
theorem B15919037 : Blo 1549472 15919037 := bstep (se 3 (by rfl) ⟨2984819, by rfl⟩ : syracuseStep 15919037 = 5969639) B5969639
theorem B6129769 : Blo 1549472 6129769 := bstep (se 2 (by rfl) ⟨2298663, by rfl⟩ : syracuseStep 6129769 = 4597327) B4597327
theorem B3107155 : Blo 1549472 3107155 := bstep (se 1 (by rfl) ⟨2330366, by rfl⟩ : syracuseStep 3107155 = 4660733) B4660733
theorem B1551039 : Blo 1549472 1551039 := bstep (se 1 (by rfl) ⟨1163279, by rfl⟩ : syracuseStep 1551039 = 2326559) B2326559
theorem B1551131 : Blo 1549472 1551131 := bstep (se 1 (by rfl) ⟨1163348, by rfl⟩ : syracuseStep 1551131 = 2326697) B2326697
theorem B13241191 : Blo 1549472 13241191 := bstep (se 1 (by rfl) ⟨9930893, by rfl⟩ : syracuseStep 13241191 = 19861787) B19861787
theorem B1551271 : Blo 1549472 1551271 := bstep (se 1 (by rfl) ⟨1163453, by rfl⟩ : syracuseStep 1551271 = 2326907) B2326907
theorem B1551387 : Blo 1549472 1551387 := bstep (se 1 (by rfl) ⟨1163540, by rfl⟩ : syracuseStep 1551387 = 2327081) B2327081
theorem B55913753 : Blo 1549472 55913753 := bstep (se 2 (by rfl) ⟨20967657, by rfl⟩ : syracuseStep 55913753 = 41935315) B41935315
theorem B2616617 : Blo 1549472 2616617 := bstep (se 2 (by rfl) ⟨981231, by rfl⟩ : syracuseStep 2616617 = 1962463) B1962463
theorem B1961263 : Blo 1549472 1961263 := bstep (se 1 (by rfl) ⟨1470947, by rfl⟩ : syracuseStep 1961263 = 2941895) B2941895
theorem B12578105 : Blo 1549472 12578105 := bstep (se 2 (by rfl) ⟨4716789, by rfl⟩ : syracuseStep 12578105 = 9433579) B9433579
theorem B8826185 : Blo 1549472 8826185 := bstep (se 2 (by rfl) ⟨3309819, by rfl⟩ : syracuseStep 8826185 = 6619639) B6619639
theorem B2207287 : Blo 1549472 2207287 := bstep (se 1 (by rfl) ⟨1655465, by rfl⟩ : syracuseStep 2207287 = 3310931) B3310931
theorem B39759659 : Blo 1549472 39759659 := bstep (se 1 (by rfl) ⟨29819744, by rfl⟩ : syracuseStep 39759659 = 59639489) B59639489
theorem B28291031 : Blo 1549472 28291031 := bstep (se 1 (by rfl) ⟨21218273, by rfl⟩ : syracuseStep 28291031 = 42436547) B42436547
theorem B26497691 : Blo 1549472 26497691 := bstep (se 1 (by rfl) ⟨19873268, by rfl⟩ : syracuseStep 26497691 = 39746537) B39746537
theorem B63664973 : Blo 1549472 63664973 := bstep (se 3 (by rfl) ⟨11937182, by rfl⟩ : syracuseStep 63664973 = 23874365) B23874365
theorem B56603933 : Blo 1549472 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B2356843 : Blo 1549472 2356843 := bstep (se 1 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 2356843 = 3535265) B3535265
theorem B11942171 : Blo 1549472 11942171 := bstep (se 1 (by rfl) ⟨8956628, by rfl⟩ : syracuseStep 11942171 = 17913257) B17913257
theorem B161192699 : Blo 1549472 161192699 := bstep (se 1 (by rfl) ⟨120894524, by rfl⟩ : syracuseStep 161192699 = 241789049) B241789049
theorem B3923903 : Blo 1549472 3923903 := bstep (se 1 (by rfl) ⟨2942927, by rfl⟩ : syracuseStep 3923903 = 5885855) B5885855
theorem B7847927 : Blo 1549472 7847927 := bstep (se 1 (by rfl) ⟨5885945, by rfl⟩ : syracuseStep 7847927 = 11771891) B11771891
theorem B5963897 : Blo 1549472 5963897 := bstep (se 2 (by rfl) ⟨2236461, by rfl⟩ : syracuseStep 5963897 = 4472923) B4472923
theorem B42443315 : Blo 1549472 42443315 := bstep (se 1 (by rfl) ⟨31832486, by rfl⟩ : syracuseStep 42443315 = 63664973) B63664973
theorem B149103341 : Blo 1549472 149103341 := bstep (se 3 (by rfl) ⟨27956876, by rfl⟩ : syracuseStep 149103341 = 55913753) B55913753
theorem B17654921 : Blo 1549472 17654921 := bstep (se 2 (by rfl) ⟨6620595, by rfl⟩ : syracuseStep 17654921 = 13241191) B13241191
theorem B2615017 : Blo 1549472 2615017 := bstep (se 2 (by rfl) ⟨980631, by rfl⟩ : syracuseStep 2615017 = 1961263) B1961263
theorem B2943049 : Blo 1549472 2943049 := bstep (se 2 (by rfl) ⟨1103643, by rfl⟩ : syracuseStep 2943049 = 2207287) B2207287
theorem B5884123 : Blo 1549472 5884123 := bstep (se 1 (by rfl) ⟨4413092, by rfl⟩ : syracuseStep 5884123 = 8826185) B8826185
theorem B2615935 : Blo 1549472 2615935 := bstep (se 1 (by rfl) ⟨1961951, by rfl⟩ : syracuseStep 2615935 = 3923903) B3923903
theorem B18860687 : Blo 1549472 18860687 := bstep (se 1 (by rfl) ⟨14145515, by rfl⟩ : syracuseStep 18860687 = 28291031) B28291031
theorem B17665127 : Blo 1549472 17665127 := bstep (se 1 (by rfl) ⟨13248845, by rfl⟩ : syracuseStep 17665127 = 26497691) B26497691
theorem B37735955 : Blo 1549472 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B10612691 : Blo 1549472 10612691 := bstep (se 1 (by rfl) ⟨7959518, by rfl⟩ : syracuseStep 10612691 = 15919037) B15919037
theorem B3142457 : Blo 1549472 3142457 := bstep (se 2 (by rfl) ⟨1178421, by rfl⟩ : syracuseStep 3142457 = 2356843) B2356843
theorem B8385403 : Blo 1549472 8385403 := bstep (se 1 (by rfl) ⟨6289052, by rfl⟩ : syracuseStep 8385403 = 12578105) B12578105
theorem B26506439 : Blo 1549472 26506439 := bstep (se 1 (by rfl) ⟨19879829, by rfl⟩ : syracuseStep 26506439 = 39759659) B39759659
theorem B5231951 : Blo 1549472 5231951 := bstep (se 1 (by rfl) ⟨3923963, by rfl⟩ : syracuseStep 5231951 = 7847927) B7847927
theorem B8173025 : Blo 1549472 8173025 := bstep (se 2 (by rfl) ⟨3064884, by rfl⟩ : syracuseStep 8173025 = 6129769) B6129769
theorem B15906557 : Blo 1549472 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B4142873 : Blo 1549472 4142873 := bstep (se 2 (by rfl) ⟨1553577, by rfl⟩ : syracuseStep 4142873 = 3107155) B3107155
theorem B3725183 : Blo 1549472 3725183 := bstep (se 1 (by rfl) ⟨2793887, by rfl⟩ : syracuseStep 3725183 = 5587775) B5587775
theorem B17652005 : Blo 1549472 17652005 := bstep (se 4 (by rfl) ⟨1654875, by rfl⟩ : syracuseStep 17652005 = 3309751) B3309751
theorem B5233247 : Blo 1549472 5233247 := bstep (se 1 (by rfl) ⟨3924935, by rfl⟩ : syracuseStep 5233247 = 7849871) B7849871
theorem B135879353 : Blo 1549472 135879353 := bstep (se 2 (by rfl) ⟨50954757, by rfl⟩ : syracuseStep 135879353 = 101909515) B101909515
theorem B7961447 : Blo 1549472 7961447 := bstep (se 1 (by rfl) ⟨5971085, by rfl⟩ : syracuseStep 7961447 = 11942171) B11942171
theorem B107461799 : Blo 1549472 107461799 := bstep (se 1 (by rfl) ⟨80596349, by rfl⟩ : syracuseStep 107461799 = 161192699) B161192699
theorem B1744411 : Blo 1549472 1744411 := bstep (se 1 (by rfl) ⟨1308308, by rfl⟩ : syracuseStep 1744411 = 2616617) B2616617
theorem B14900921 : Blo 1549472 14900921 := bstep (se 2 (by rfl) ⟨5587845, by rfl⟩ : syracuseStep 14900921 = 11175691) B11175691
theorem B3924065 : Blo 1549472 3924065 := bstep (se 2 (by rfl) ⟨1471524, by rfl⟩ : syracuseStep 3924065 = 2943049) B2943049
theorem B28295543 : Blo 1549472 28295543 := bstep (se 1 (by rfl) ⟨21221657, by rfl⟩ : syracuseStep 28295543 = 42443315) B42443315
theorem B99402227 : Blo 1549472 99402227 := bstep (se 1 (by rfl) ⟨74551670, by rfl⟩ : syracuseStep 99402227 = 149103341) B149103341
theorem B17670959 : Blo 1549472 17670959 := bstep (se 1 (by rfl) ⟨13253219, by rfl⟩ : syracuseStep 17670959 = 26506439) B26506439
theorem B5448683 : Blo 1549472 5448683 := bstep (se 1 (by rfl) ⟨4086512, by rfl⟩ : syracuseStep 5448683 = 8173025) B8173025
theorem B2483455 : Blo 1549472 2483455 := bstep (se 1 (by rfl) ⟨1862591, by rfl⟩ : syracuseStep 2483455 = 3725183) B3725183
theorem B71641199 : Blo 1549472 71641199 := bstep (se 1 (by rfl) ⟨53730899, by rfl⟩ : syracuseStep 71641199 = 107461799) B107461799
theorem B3975931 : Blo 1549472 3975931 := bstep (se 1 (by rfl) ⟨2981948, by rfl⟩ : syracuseStep 3975931 = 5963897) B5963897
theorem B10604371 : Blo 1549472 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B11768003 : Blo 1549472 11768003 := bstep (se 1 (by rfl) ⟨8826002, by rfl⟩ : syracuseStep 11768003 = 17652005) B17652005
theorem B11047661 : Blo 1549472 11047661 := bstep (se 3 (by rfl) ⟨2071436, by rfl⟩ : syracuseStep 11047661 = 4142873) B4142873
theorem B11776751 : Blo 1549472 11776751 := bstep (se 1 (by rfl) ⟨8832563, by rfl⟩ : syracuseStep 11776751 = 17665127) B17665127
theorem B21230525 : Blo 1549472 21230525 := bstep (se 3 (by rfl) ⟨3980723, by rfl⟩ : syracuseStep 21230525 = 7961447) B7961447
theorem B3486689 : Blo 1549472 3486689 := bstep (se 2 (by rfl) ⟨1307508, by rfl⟩ : syracuseStep 3486689 = 2615017) B2615017
theorem B9933947 : Blo 1549472 9933947 := bstep (se 1 (by rfl) ⟨7450460, by rfl⟩ : syracuseStep 9933947 = 14900921) B14900921
theorem B7075127 : Blo 1549472 7075127 := bstep (se 1 (by rfl) ⟨5306345, by rfl⟩ : syracuseStep 7075127 = 10612691) B10612691
theorem B7845497 : Blo 1549472 7845497 := bstep (se 2 (by rfl) ⟨2942061, by rfl⟩ : syracuseStep 7845497 = 5884123) B5884123
theorem B2094971 : Blo 1549472 2094971 := bstep (se 1 (by rfl) ⟨1571228, by rfl⟩ : syracuseStep 2094971 = 3142457) B3142457
theorem B11769947 : Blo 1549472 11769947 := bstep (se 1 (by rfl) ⟨8827460, by rfl⟩ : syracuseStep 11769947 = 17654921) B17654921
theorem B3487913 : Blo 1549472 3487913 := bstep (se 2 (by rfl) ⟨1307967, by rfl⟩ : syracuseStep 3487913 = 2615935) B2615935
theorem B3487967 : Blo 1549472 3487967 := bstep (se 1 (by rfl) ⟨2615975, by rfl⟩ : syracuseStep 3487967 = 5231951) B5231951
theorem B11180537 : Blo 1549472 11180537 := bstep (se 2 (by rfl) ⟨4192701, by rfl⟩ : syracuseStep 11180537 = 8385403) B8385403
theorem B3488831 : Blo 1549472 3488831 := bstep (se 1 (by rfl) ⟨2616623, by rfl⟩ : syracuseStep 3488831 = 5233247) B5233247
theorem B12573791 : Blo 1549472 12573791 := bstep (se 1 (by rfl) ⟨9430343, by rfl⟩ : syracuseStep 12573791 = 18860687) B18860687
theorem B90586235 : Blo 1549472 90586235 := bstep (se 1 (by rfl) ⟨67939676, by rfl⟩ : syracuseStep 90586235 = 135879353) B135879353
theorem B2325881 : Blo 1549472 2325881 := bstep (se 2 (by rfl) ⟨872205, by rfl⟩ : syracuseStep 2325881 = 1744411) B1744411
theorem B25157303 : Blo 1549472 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B7365107 : Blo 1549472 7365107 := bstep (se 1 (by rfl) ⟨5523830, by rfl⟩ : syracuseStep 7365107 = 11047661) B11047661
theorem B11780639 : Blo 1549472 11780639 := bstep (se 1 (by rfl) ⟨8835479, by rfl⟩ : syracuseStep 11780639 = 17670959) B17670959
theorem B18867005 : Blo 1549472 18867005 := bstep (se 3 (by rfl) ⟨3537563, by rfl⟩ : syracuseStep 18867005 = 7075127) B7075127
theorem B3311273 : Blo 1549472 3311273 := bstep (se 2 (by rfl) ⟨1241727, by rfl⟩ : syracuseStep 3311273 = 2483455) B2483455
theorem B8382527 : Blo 1549472 8382527 := bstep (se 1 (by rfl) ⟨6286895, by rfl⟩ : syracuseStep 8382527 = 12573791) B12573791
theorem B1550587 : Blo 1549472 1550587 := bstep (se 1 (by rfl) ⟨1162940, by rfl⟩ : syracuseStep 1550587 = 2325881) B2325881
theorem B16771535 : Blo 1549472 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B2616043 : Blo 1549472 2616043 := bstep (se 1 (by rfl) ⟨1962032, by rfl⟩ : syracuseStep 2616043 = 3924065) B3924065
theorem B66268151 : Blo 1549472 66268151 := bstep (se 1 (by rfl) ⟨49701113, by rfl⟩ : syracuseStep 66268151 = 99402227) B99402227
theorem B7851167 : Blo 1549472 7851167 := bstep (se 1 (by rfl) ⟨5888375, by rfl⟩ : syracuseStep 7851167 = 11776751) B11776751
theorem B3632455 : Blo 1549472 3632455 := bstep (se 1 (by rfl) ⟨2724341, by rfl⟩ : syracuseStep 3632455 = 5448683) B5448683
theorem B6622631 : Blo 1549472 6622631 := bstep (se 1 (by rfl) ⟨4966973, by rfl⟩ : syracuseStep 6622631 = 9933947) B9933947
theorem B5230331 : Blo 1549472 5230331 := bstep (se 1 (by rfl) ⟨3922748, by rfl⟩ : syracuseStep 5230331 = 7845497) B7845497
theorem B21204965 : Blo 1549472 21204965 := bstep (se 4 (by rfl) ⟨1987965, by rfl⟩ : syracuseStep 21204965 = 3975931) B3975931
theorem B7845335 : Blo 1549472 7845335 := bstep (se 1 (by rfl) ⟨5884001, by rfl⟩ : syracuseStep 7845335 = 11768003) B11768003
theorem B18863695 : Blo 1549472 18863695 := bstep (se 1 (by rfl) ⟨14147771, by rfl⟩ : syracuseStep 18863695 = 28295543) B28295543
theorem B191043197 : Blo 1549472 191043197 := bstep (se 3 (by rfl) ⟨35820599, by rfl⟩ : syracuseStep 191043197 = 71641199) B71641199
theorem B241563293 : Blo 1549472 241563293 := bstep (se 3 (by rfl) ⟨45293117, by rfl⟩ : syracuseStep 241563293 = 90586235) B90586235
theorem B2324459 : Blo 1549472 2324459 := bstep (se 1 (by rfl) ⟨1743344, by rfl⟩ : syracuseStep 2324459 = 3486689) B3486689
theorem B7846631 : Blo 1549472 7846631 := bstep (se 1 (by rfl) ⟨5884973, by rfl⟩ : syracuseStep 7846631 = 11769947) B11769947
theorem B2325275 : Blo 1549472 2325275 := bstep (se 1 (by rfl) ⟨1743956, by rfl⟩ : syracuseStep 2325275 = 3487913) B3487913
theorem B2325311 : Blo 1549472 2325311 := bstep (se 1 (by rfl) ⟨1743983, by rfl⟩ : syracuseStep 2325311 = 3487967) B3487967
theorem B7453691 : Blo 1549472 7453691 := bstep (se 1 (by rfl) ⟨5590268, by rfl⟩ : syracuseStep 7453691 = 11180537) B11180537
theorem B2325887 : Blo 1549472 2325887 := bstep (se 1 (by rfl) ⟨1744415, by rfl⟩ : syracuseStep 2325887 = 3488831) B3488831
theorem B5586589 : Blo 1549472 5586589 := bstep (se 3 (by rfl) ⟨1047485, by rfl⟩ : syracuseStep 5586589 = 2094971) B2094971
theorem B14139161 : Blo 1549472 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B56614733 : Blo 1549472 56614733 := bstep (se 3 (by rfl) ⟨10615262, by rfl⟩ : syracuseStep 56614733 = 21230525) B21230525
theorem B29795141 : Blo 1549472 29795141 := bstep (se 4 (by rfl) ⟨2793294, by rfl⟩ : syracuseStep 29795141 = 5586589) B5586589
theorem B127362131 : Blo 1549472 127362131 := bstep (se 1 (by rfl) ⟨95521598, by rfl⟩ : syracuseStep 127362131 = 191043197) B191043197
theorem B1549639 : Blo 1549472 1549639 := bstep (se 1 (by rfl) ⟨1162229, by rfl⟩ : syracuseStep 1549639 = 2324459) B2324459
theorem B5588351 : Blo 1549472 5588351 := bstep (se 1 (by rfl) ⟨4191263, by rfl⟩ : syracuseStep 5588351 = 8382527) B8382527
theorem B4843273 : Blo 1549472 4843273 := bstep (se 2 (by rfl) ⟨1816227, by rfl⟩ : syracuseStep 4843273 = 3632455) B3632455
theorem B1550183 : Blo 1549472 1550183 := bstep (se 1 (by rfl) ⟨1162637, by rfl⟩ : syracuseStep 1550183 = 2325275) B2325275
theorem B1550207 : Blo 1549472 1550207 := bstep (se 1 (by rfl) ⟨1162655, by rfl⟩ : syracuseStep 1550207 = 2325311) B2325311
theorem B25151593 : Blo 1549472 25151593 := bstep (se 2 (by rfl) ⟨9431847, by rfl⟩ : syracuseStep 25151593 = 18863695) B18863695
theorem B1550591 : Blo 1549472 1550591 := bstep (se 1 (by rfl) ⟨1162943, by rfl⟩ : syracuseStep 1550591 = 2325887) B2325887
theorem B37743155 : Blo 1549472 37743155 := bstep (se 1 (by rfl) ⟨28307366, by rfl⟩ : syracuseStep 37743155 = 56614733) B56614733
theorem B4910071 : Blo 1549472 4910071 := bstep (se 1 (by rfl) ⟨3682553, by rfl⟩ : syracuseStep 4910071 = 7365107) B7365107
theorem B12578003 : Blo 1549472 12578003 := bstep (se 1 (by rfl) ⟨9433502, by rfl⟩ : syracuseStep 12578003 = 18867005) B18867005
theorem B5230223 : Blo 1549472 5230223 := bstep (se 1 (by rfl) ⟨3922667, by rfl⟩ : syracuseStep 5230223 = 7845335) B7845335
theorem B161042195 : Blo 1549472 161042195 := bstep (se 1 (by rfl) ⟨120781646, by rfl⟩ : syracuseStep 161042195 = 241563293) B241563293
theorem B2207515 : Blo 1549472 2207515 := bstep (se 1 (by rfl) ⟨1655636, by rfl⟩ : syracuseStep 2207515 = 3311273) B3311273
theorem B5231087 : Blo 1549472 5231087 := bstep (se 1 (by rfl) ⟨3923315, by rfl⟩ : syracuseStep 5231087 = 7846631) B7846631
theorem B4969127 : Blo 1549472 4969127 := bstep (se 1 (by rfl) ⟨3726845, by rfl⟩ : syracuseStep 4969127 = 7453691) B7453691
theorem B3486887 : Blo 1549472 3486887 := bstep (se 1 (by rfl) ⟨2615165, by rfl⟩ : syracuseStep 3486887 = 5230331) B5230331
theorem B9426107 : Blo 1549472 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B14136643 : Blo 1549472 14136643 := bstep (se 1 (by rfl) ⟨10602482, by rfl⟩ : syracuseStep 14136643 = 21204965) B21204965
theorem B7853759 : Blo 1549472 7853759 := bstep (se 1 (by rfl) ⟨5890319, by rfl⟩ : syracuseStep 7853759 = 11780639) B11780639
theorem B3488057 : Blo 1549472 3488057 := bstep (se 2 (by rfl) ⟨1308021, by rfl⟩ : syracuseStep 3488057 = 2616043) B2616043
theorem B11181023 : Blo 1549472 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B44178767 : Blo 1549472 44178767 := bstep (se 1 (by rfl) ⟨33134075, by rfl⟩ : syracuseStep 44178767 = 66268151) B66268151
theorem B5234111 : Blo 1549472 5234111 := bstep (se 1 (by rfl) ⟨3925583, by rfl⟩ : syracuseStep 5234111 = 7851167) B7851167
theorem B4415087 : Blo 1549472 4415087 := bstep (se 1 (by rfl) ⟨3311315, by rfl⟩ : syracuseStep 4415087 = 6622631) B6622631
theorem B6284071 : Blo 1549472 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B5235839 : Blo 1549472 5235839 := bstep (se 1 (by rfl) ⟨3926879, by rfl⟩ : syracuseStep 5235839 = 7853759) B7853759
theorem B6546761 : Blo 1549472 6546761 := bstep (se 2 (by rfl) ⟨2455035, by rfl⟩ : syracuseStep 6546761 = 4910071) B4910071
theorem B29452511 : Blo 1549472 29452511 := bstep (se 1 (by rfl) ⟨22089383, by rfl⟩ : syracuseStep 29452511 = 44178767) B44178767
theorem B6457697 : Blo 1549472 6457697 := bstep (se 2 (by rfl) ⟨2421636, by rfl⟩ : syracuseStep 6457697 = 4843273) B4843273
theorem B2943353 : Blo 1549472 2943353 := bstep (se 2 (by rfl) ⟨1103757, by rfl⟩ : syracuseStep 2943353 = 2207515) B2207515
theorem B2943391 : Blo 1549472 2943391 := bstep (se 1 (by rfl) ⟨2207543, by rfl⟩ : syracuseStep 2943391 = 4415087) B4415087
theorem B3312751 : Blo 1549472 3312751 := bstep (se 1 (by rfl) ⟨2484563, by rfl⟩ : syracuseStep 3312751 = 4969127) B4969127
theorem B25162103 : Blo 1549472 25162103 := bstep (se 1 (by rfl) ⟨18871577, by rfl⟩ : syracuseStep 25162103 = 37743155) B37743155
theorem B8385335 : Blo 1549472 8385335 := bstep (se 1 (by rfl) ⟨6289001, by rfl⟩ : syracuseStep 8385335 = 12578003) B12578003
theorem B3486815 : Blo 1549472 3486815 := bstep (se 1 (by rfl) ⟨2615111, by rfl⟩ : syracuseStep 3486815 = 5230223) B5230223
theorem B107361463 : Blo 1549472 107361463 := bstep (se 1 (by rfl) ⟨80521097, by rfl⟩ : syracuseStep 107361463 = 161042195) B161042195
theorem B33535457 : Blo 1549472 33535457 := bstep (se 2 (by rfl) ⟨12575796, by rfl⟩ : syracuseStep 33535457 = 25151593) B25151593
theorem B3487391 : Blo 1549472 3487391 := bstep (se 1 (by rfl) ⟨2615543, by rfl⟩ : syracuseStep 3487391 = 5231087) B5231087
theorem B19863427 : Blo 1549472 19863427 := bstep (se 1 (by rfl) ⟨14897570, by rfl⟩ : syracuseStep 19863427 = 29795141) B29795141
theorem B84908087 : Blo 1549472 84908087 := bstep (se 1 (by rfl) ⟨63681065, by rfl⟩ : syracuseStep 84908087 = 127362131) B127362131
theorem B2324591 : Blo 1549472 2324591 := bstep (se 1 (by rfl) ⟨1743443, by rfl⟩ : syracuseStep 2324591 = 3486887) B3486887
theorem B3725567 : Blo 1549472 3725567 := bstep (se 1 (by rfl) ⟨2794175, by rfl⟩ : syracuseStep 3725567 = 5588351) B5588351
theorem B2325371 : Blo 1549472 2325371 := bstep (se 1 (by rfl) ⟨1744028, by rfl⟩ : syracuseStep 2325371 = 3488057) B3488057
theorem B18848857 : Blo 1549472 18848857 := bstep (se 2 (by rfl) ⟨7068321, by rfl⟩ : syracuseStep 18848857 = 14136643) B14136643
theorem B7454015 : Blo 1549472 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B3489407 : Blo 1549472 3489407 := bstep (se 1 (by rfl) ⟨2617055, by rfl⟩ : syracuseStep 3489407 = 5234111) B5234111
theorem B3924521 : Blo 1549472 3924521 := bstep (se 2 (by rfl) ⟨1471695, by rfl⟩ : syracuseStep 3924521 = 2943391) B2943391
theorem B3490559 : Blo 1549472 3490559 := bstep (se 1 (by rfl) ⟨2617919, by rfl⟩ : syracuseStep 3490559 = 5235839) B5235839
theorem B22356971 : Blo 1549472 22356971 := bstep (se 1 (by rfl) ⟨16767728, by rfl⟩ : syracuseStep 22356971 = 33535457) B33535457
theorem B1549727 : Blo 1549472 1549727 := bstep (se 1 (by rfl) ⟨1162295, by rfl⟩ : syracuseStep 1549727 = 2324591) B2324591
theorem B4417001 : Blo 1549472 4417001 := bstep (se 2 (by rfl) ⟨1656375, by rfl⟩ : syracuseStep 4417001 = 3312751) B3312751
theorem B2483711 : Blo 1549472 2483711 := bstep (se 1 (by rfl) ⟨1862783, by rfl⟩ : syracuseStep 2483711 = 3725567) B3725567
theorem B33515045 : Blo 1549472 33515045 := bstep (se 4 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 33515045 = 6284071) B6284071
theorem B143148617 : Blo 1549472 143148617 := bstep (se 2 (by rfl) ⟨53680731, by rfl⟩ : syracuseStep 143148617 = 107361463) B107361463
theorem B1550247 : Blo 1549472 1550247 := bstep (se 1 (by rfl) ⟨1162685, by rfl⟩ : syracuseStep 1550247 = 2325371) B2325371
theorem B5590223 : Blo 1549472 5590223 := bstep (se 1 (by rfl) ⟨4192667, by rfl⟩ : syracuseStep 5590223 = 8385335) B8385335
theorem B4305131 : Blo 1549472 4305131 := bstep (se 1 (by rfl) ⟨3228848, by rfl⟩ : syracuseStep 4305131 = 6457697) B6457697
theorem B1962235 : Blo 1549472 1962235 := bstep (se 1 (by rfl) ⟨1471676, by rfl⟩ : syracuseStep 1962235 = 2943353) B2943353
theorem B4969343 : Blo 1549472 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B16774735 : Blo 1549472 16774735 := bstep (se 1 (by rfl) ⟨12581051, by rfl⟩ : syracuseStep 16774735 = 25162103) B25162103
theorem B2324543 : Blo 1549472 2324543 := bstep (se 1 (by rfl) ⟨1743407, by rfl⟩ : syracuseStep 2324543 = 3486815) B3486815
theorem B4364507 : Blo 1549472 4364507 := bstep (se 1 (by rfl) ⟨3273380, by rfl⟩ : syracuseStep 4364507 = 6546761) B6546761
theorem B2324927 : Blo 1549472 2324927 := bstep (se 1 (by rfl) ⟨1743695, by rfl⟩ : syracuseStep 2324927 = 3487391) B3487391
theorem B56605391 : Blo 1549472 56605391 := bstep (se 1 (by rfl) ⟨42454043, by rfl⟩ : syracuseStep 56605391 = 84908087) B84908087
theorem B25131809 : Blo 1549472 25131809 := bstep (se 2 (by rfl) ⟨9424428, by rfl⟩ : syracuseStep 25131809 = 18848857) B18848857
theorem B19635007 : Blo 1549472 19635007 := bstep (se 1 (by rfl) ⟨14726255, by rfl⟩ : syracuseStep 19635007 = 29452511) B29452511
theorem B2326271 : Blo 1549472 2326271 := bstep (se 1 (by rfl) ⟨1744703, by rfl⟩ : syracuseStep 2326271 = 3489407) B3489407
theorem B26484569 : Blo 1549472 26484569 := bstep (se 2 (by rfl) ⟨9931713, by rfl⟩ : syracuseStep 26484569 = 19863427) B19863427
theorem B2327039 : Blo 1549472 2327039 := bstep (se 1 (by rfl) ⟨1745279, by rfl⟩ : syracuseStep 2327039 = 3490559) B3490559
theorem B1655807 : Blo 1549472 1655807 := bstep (se 1 (by rfl) ⟨1241855, by rfl⟩ : syracuseStep 1655807 = 2483711) B2483711
theorem B1549695 : Blo 1549472 1549695 := bstep (se 1 (by rfl) ⟨1162271, by rfl⟩ : syracuseStep 1549695 = 2324543) B2324543
theorem B1549951 : Blo 1549472 1549951 := bstep (se 1 (by rfl) ⟨1162463, by rfl⟩ : syracuseStep 1549951 = 2324927) B2324927
theorem B16754539 : Blo 1549472 16754539 := bstep (se 1 (by rfl) ⟨12565904, by rfl⟩ : syracuseStep 16754539 = 25131809) B25131809
theorem B22366313 : Blo 1549472 22366313 := bstep (se 2 (by rfl) ⟨8387367, by rfl⟩ : syracuseStep 22366313 = 16774735) B16774735
theorem B1550847 : Blo 1549472 1550847 := bstep (se 1 (by rfl) ⟨1163135, by rfl⟩ : syracuseStep 1550847 = 2326271) B2326271
theorem B17656379 : Blo 1549472 17656379 := bstep (se 1 (by rfl) ⟨13242284, by rfl⟩ : syracuseStep 17656379 = 26484569) B26484569
theorem B2870087 : Blo 1549472 2870087 := bstep (se 1 (by rfl) ⟨2152565, by rfl⟩ : syracuseStep 2870087 = 4305131) B4305131
theorem B2616313 : Blo 1549472 2616313 := bstep (se 2 (by rfl) ⟨981117, by rfl⟩ : syracuseStep 2616313 = 1962235) B1962235
theorem B2616347 : Blo 1549472 2616347 := bstep (se 1 (by rfl) ⟨1962260, by rfl⟩ : syracuseStep 2616347 = 3924521) B3924521
theorem B3312895 : Blo 1549472 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B14904647 : Blo 1549472 14904647 := bstep (se 1 (by rfl) ⟨11178485, by rfl⟩ : syracuseStep 14904647 = 22356971) B22356971
theorem B2944667 : Blo 1549472 2944667 := bstep (se 1 (by rfl) ⟨2208500, by rfl⟩ : syracuseStep 2944667 = 4417001) B4417001
theorem B22343363 : Blo 1549472 22343363 := bstep (se 1 (by rfl) ⟨16757522, by rfl⟩ : syracuseStep 22343363 = 33515045) B33515045
theorem B95432411 : Blo 1549472 95432411 := bstep (se 1 (by rfl) ⟨71574308, by rfl⟩ : syracuseStep 95432411 = 143148617) B143148617
theorem B37736927 : Blo 1549472 37736927 := bstep (se 1 (by rfl) ⟨28302695, by rfl⟩ : syracuseStep 37736927 = 56605391) B56605391
theorem B11638685 : Blo 1549472 11638685 := bstep (se 3 (by rfl) ⟨2182253, by rfl⟩ : syracuseStep 11638685 = 4364507) B4364507
theorem B26180009 : Blo 1549472 26180009 := bstep (se 2 (by rfl) ⟨9817503, by rfl⟩ : syracuseStep 26180009 = 19635007) B19635007
theorem B3726815 : Blo 1549472 3726815 := bstep (se 1 (by rfl) ⟨2795111, by rfl⟩ : syracuseStep 3726815 = 5590223) B5590223
theorem B25157951 : Blo 1549472 25157951 := bstep (se 1 (by rfl) ⟨18868463, by rfl⟩ : syracuseStep 25157951 = 37736927) B37736927
theorem B9938173 : Blo 1549472 9938173 := bstep (se 3 (by rfl) ⟨1863407, by rfl⟩ : syracuseStep 9938173 = 3726815) B3726815
theorem B7759123 : Blo 1549472 7759123 := bstep (se 1 (by rfl) ⟨5819342, by rfl⟩ : syracuseStep 7759123 = 11638685) B11638685
theorem B14910875 : Blo 1549472 14910875 := bstep (se 1 (by rfl) ⟨11183156, by rfl⟩ : syracuseStep 14910875 = 22366313) B22366313
theorem B4417193 : Blo 1549472 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B7653565 : Blo 1549472 7653565 := bstep (se 3 (by rfl) ⟨1435043, by rfl⟩ : syracuseStep 7653565 = 2870087) B2870087
theorem B14895575 : Blo 1549472 14895575 := bstep (se 1 (by rfl) ⟨11171681, by rfl⟩ : syracuseStep 14895575 = 22343363) B22343363
theorem B63621607 : Blo 1549472 63621607 := bstep (se 1 (by rfl) ⟨47716205, by rfl⟩ : syracuseStep 63621607 = 95432411) B95432411
theorem B1551359 : Blo 1549472 1551359 := bstep (se 1 (by rfl) ⟨1163519, by rfl⟩ : syracuseStep 1551359 = 2327039) B2327039
theorem B17453339 : Blo 1549472 17453339 := bstep (se 1 (by rfl) ⟨13090004, by rfl⟩ : syracuseStep 17453339 = 26180009) B26180009
theorem B1963111 : Blo 1549472 1963111 := bstep (se 1 (by rfl) ⟨1472333, by rfl⟩ : syracuseStep 1963111 = 2944667) B2944667
theorem B3488417 : Blo 1549472 3488417 := bstep (se 2 (by rfl) ⟨1308156, by rfl⟩ : syracuseStep 3488417 = 2616313) B2616313
theorem B4415485 : Blo 1549472 4415485 := bstep (se 3 (by rfl) ⟨827903, by rfl⟩ : syracuseStep 4415485 = 1655807) B1655807
theorem B11770919 : Blo 1549472 11770919 := bstep (se 1 (by rfl) ⟨8828189, by rfl⟩ : syracuseStep 11770919 = 17656379) B17656379
theorem B1744231 : Blo 1549472 1744231 := bstep (se 1 (by rfl) ⟨1308173, by rfl⟩ : syracuseStep 1744231 = 2616347) B2616347
theorem B9936431 : Blo 1549472 9936431 := bstep (se 1 (by rfl) ⟨7452323, by rfl⟩ : syracuseStep 9936431 = 14904647) B14904647
theorem B22339385 : Blo 1549472 22339385 := bstep (se 2 (by rfl) ⟨8377269, by rfl⟩ : syracuseStep 22339385 = 16754539) B16754539
theorem B84828809 : Blo 1549472 84828809 := bstep (se 2 (by rfl) ⟨31810803, by rfl⟩ : syracuseStep 84828809 = 63621607) B63621607
theorem B9930383 : Blo 1549472 9930383 := bstep (se 1 (by rfl) ⟨7447787, by rfl⟩ : syracuseStep 9930383 = 14895575) B14895575
theorem B11635559 : Blo 1549472 11635559 := bstep (se 1 (by rfl) ⟨8726669, by rfl⟩ : syracuseStep 11635559 = 17453339) B17453339
theorem B16771967 : Blo 1549472 16771967 := bstep (se 1 (by rfl) ⟨12578975, by rfl⟩ : syracuseStep 16771967 = 25157951) B25157951
theorem B9940583 : Blo 1549472 9940583 := bstep (se 1 (by rfl) ⟨7455437, by rfl⟩ : syracuseStep 9940583 = 14910875) B14910875
theorem B41381989 : Blo 1549472 41381989 := bstep (se 4 (by rfl) ⟨3879561, by rfl⟩ : syracuseStep 41381989 = 7759123) B7759123
theorem B2617481 : Blo 1549472 2617481 := bstep (se 2 (by rfl) ⟨981555, by rfl⟩ : syracuseStep 2617481 = 1963111) B1963111
theorem B13250897 : Blo 1549472 13250897 := bstep (se 2 (by rfl) ⟨4969086, by rfl⟩ : syracuseStep 13250897 = 9938173) B9938173
theorem B6624287 : Blo 1549472 6624287 := bstep (se 1 (by rfl) ⟨4968215, by rfl⟩ : syracuseStep 6624287 = 9936431) B9936431
theorem B5887313 : Blo 1549472 5887313 := bstep (se 2 (by rfl) ⟨2207742, by rfl⟩ : syracuseStep 5887313 = 4415485) B4415485
theorem B10204753 : Blo 1549472 10204753 := bstep (se 2 (by rfl) ⟨3826782, by rfl⟩ : syracuseStep 10204753 = 7653565) B7653565
theorem B2325611 : Blo 1549472 2325611 := bstep (se 1 (by rfl) ⟨1744208, by rfl⟩ : syracuseStep 2325611 = 3488417) B3488417
theorem B11779181 : Blo 1549472 11779181 := bstep (se 3 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 11779181 = 4417193) B4417193
theorem B2325641 : Blo 1549472 2325641 := bstep (se 2 (by rfl) ⟨872115, by rfl⟩ : syracuseStep 2325641 = 1744231) B1744231
theorem B7847279 : Blo 1549472 7847279 := bstep (se 1 (by rfl) ⟨5885459, by rfl⟩ : syracuseStep 7847279 = 11770919) B11770919
theorem B14892923 : Blo 1549472 14892923 := bstep (se 1 (by rfl) ⟨11169692, by rfl⟩ : syracuseStep 14892923 = 22339385) B22339385
theorem B1744987 : Blo 1549472 1744987 := bstep (se 1 (by rfl) ⟨1308740, by rfl⟩ : syracuseStep 1744987 = 2617481) B2617481
theorem B4416191 : Blo 1549472 4416191 := bstep (se 1 (by rfl) ⟨3312143, by rfl⟩ : syracuseStep 4416191 = 6624287) B6624287
theorem B3924875 : Blo 1549472 3924875 := bstep (se 1 (by rfl) ⟨2943656, by rfl⟩ : syracuseStep 3924875 = 5887313) B5887313
theorem B6620255 : Blo 1549472 6620255 := bstep (se 1 (by rfl) ⟨4965191, by rfl⟩ : syracuseStep 6620255 = 9930383) B9930383
theorem B1550407 : Blo 1549472 1550407 := bstep (se 1 (by rfl) ⟨1162805, by rfl⟩ : syracuseStep 1550407 = 2325611) B2325611
theorem B1550427 : Blo 1549472 1550427 := bstep (se 1 (by rfl) ⟨1162820, by rfl⟩ : syracuseStep 1550427 = 2325641) B2325641
theorem B8833931 : Blo 1549472 8833931 := bstep (se 1 (by rfl) ⟨6625448, by rfl⟩ : syracuseStep 8833931 = 13250897) B13250897
theorem B226210157 : Blo 1549472 226210157 := bstep (se 3 (by rfl) ⟨42414404, by rfl⟩ : syracuseStep 226210157 = 84828809) B84828809
theorem B7852787 : Blo 1549472 7852787 := bstep (se 1 (by rfl) ⟨5889590, by rfl⟩ : syracuseStep 7852787 = 11779181) B11779181
theorem B882815765 : Blo 1549472 882815765 := bstep (se 6 (by rfl) ⟨20690994, by rfl⟩ : syracuseStep 882815765 = 41381989) B41381989
theorem B5231519 : Blo 1549472 5231519 := bstep (se 1 (by rfl) ⟨3923639, by rfl⟩ : syracuseStep 5231519 = 7847279) B7847279
theorem B7757039 : Blo 1549472 7757039 := bstep (se 1 (by rfl) ⟨5817779, by rfl⟩ : syracuseStep 7757039 = 11635559) B11635559
theorem B11181311 : Blo 1549472 11181311 := bstep (se 1 (by rfl) ⟨8385983, by rfl⟩ : syracuseStep 11181311 = 16771967) B16771967
theorem B13606337 : Blo 1549472 13606337 := bstep (se 2 (by rfl) ⟨5102376, by rfl⟩ : syracuseStep 13606337 = 10204753) B10204753
theorem B6627055 : Blo 1549472 6627055 := bstep (se 1 (by rfl) ⟨4970291, by rfl⟩ : syracuseStep 6627055 = 9940583) B9940583
theorem B9928615 : Blo 1549472 9928615 := bstep (se 1 (by rfl) ⟨7446461, by rfl⟩ : syracuseStep 9928615 = 14892923) B14892923
theorem B2326649 : Blo 1549472 2326649 := bstep (se 2 (by rfl) ⟨872493, by rfl⟩ : syracuseStep 2326649 = 1744987) B1744987
theorem B150806771 : Blo 1549472 150806771 := bstep (se 1 (by rfl) ⟨113105078, by rfl⟩ : syracuseStep 150806771 = 226210157) B226210157
theorem B5235191 : Blo 1549472 5235191 := bstep (se 1 (by rfl) ⟨3926393, by rfl⟩ : syracuseStep 5235191 = 7852787) B7852787
theorem B36283565 : Blo 1549472 36283565 := bstep (se 3 (by rfl) ⟨6803168, by rfl⟩ : syracuseStep 36283565 = 13606337) B13606337
theorem B5171359 : Blo 1549472 5171359 := bstep (se 1 (by rfl) ⟨3878519, by rfl⟩ : syracuseStep 5171359 = 7757039) B7757039
theorem B2944127 : Blo 1549472 2944127 := bstep (se 1 (by rfl) ⟨2208095, by rfl⟩ : syracuseStep 2944127 = 4416191) B4416191
theorem B2616583 : Blo 1549472 2616583 := bstep (se 1 (by rfl) ⟨1962437, by rfl⟩ : syracuseStep 2616583 = 3924875) B3924875
theorem B8836073 : Blo 1549472 8836073 := bstep (se 2 (by rfl) ⟨3313527, by rfl⟩ : syracuseStep 8836073 = 6627055) B6627055
theorem B3487679 : Blo 1549472 3487679 := bstep (se 1 (by rfl) ⟨2615759, by rfl⟩ : syracuseStep 3487679 = 5231519) B5231519
theorem B4413503 : Blo 1549472 4413503 := bstep (se 1 (by rfl) ⟨3310127, by rfl⟩ : syracuseStep 4413503 = 6620255) B6620255
theorem B5889287 : Blo 1549472 5889287 := bstep (se 1 (by rfl) ⟨4416965, by rfl⟩ : syracuseStep 5889287 = 8833931) B8833931
theorem B2354175373 : Blo 1549472 2354175373 := bstep (se 3 (by rfl) ⟨441407882, by rfl⟩ : syracuseStep 2354175373 = 882815765) B882815765
theorem B7454207 : Blo 1549472 7454207 := bstep (se 1 (by rfl) ⟨5590655, by rfl⟩ : syracuseStep 7454207 = 11181311) B11181311
theorem B13238153 : Blo 1549472 13238153 := bstep (se 2 (by rfl) ⟨4964307, by rfl⟩ : syracuseStep 13238153 = 9928615) B9928615
theorem B3490127 : Blo 1549472 3490127 := bstep (se 1 (by rfl) ⟨2617595, by rfl⟩ : syracuseStep 3490127 = 5235191) B5235191
theorem B5890715 : Blo 1549472 5890715 := bstep (se 1 (by rfl) ⟨4418036, by rfl⟩ : syracuseStep 5890715 = 8836073) B8836073
theorem B2942335 : Blo 1549472 2942335 := bstep (se 1 (by rfl) ⟨2206751, by rfl⟩ : syracuseStep 2942335 = 4413503) B4413503
theorem B3926191 : Blo 1549472 3926191 := bstep (se 1 (by rfl) ⟨2944643, by rfl⟩ : syracuseStep 3926191 = 5889287) B5889287
theorem B8825435 : Blo 1549472 8825435 := bstep (se 1 (by rfl) ⟨6619076, by rfl⟩ : syracuseStep 8825435 = 13238153) B13238153
theorem B1551099 : Blo 1549472 1551099 := bstep (se 1 (by rfl) ⟨1163324, by rfl⟩ : syracuseStep 1551099 = 2326649) B2326649
theorem B7851005 : Blo 1549472 7851005 := bstep (se 3 (by rfl) ⟨1472063, by rfl⟩ : syracuseStep 7851005 = 2944127) B2944127
theorem B19877885 : Blo 1549472 19877885 := bstep (se 3 (by rfl) ⟨3727103, by rfl⟩ : syracuseStep 19877885 = 7454207) B7454207
theorem B3138900497 : Blo 1549472 3138900497 := bstep (se 2 (by rfl) ⟨1177087686, by rfl⟩ : syracuseStep 3138900497 = 2354175373) B2354175373
theorem B100537847 : Blo 1549472 100537847 := bstep (se 1 (by rfl) ⟨75403385, by rfl⟩ : syracuseStep 100537847 = 150806771) B150806771
theorem B6895145 : Blo 1549472 6895145 := bstep (se 2 (by rfl) ⟨2585679, by rfl⟩ : syracuseStep 6895145 = 5171359) B5171359
theorem B24189043 : Blo 1549472 24189043 := bstep (se 1 (by rfl) ⟨18141782, by rfl⟩ : syracuseStep 24189043 = 36283565) B36283565
theorem B2325119 : Blo 1549472 2325119 := bstep (se 1 (by rfl) ⟨1743839, by rfl⟩ : syracuseStep 2325119 = 3487679) B3487679
theorem B3488777 : Blo 1549472 3488777 := bstep (se 2 (by rfl) ⟨1308291, by rfl⟩ : syracuseStep 3488777 = 2616583) B2616583
theorem B32252057 : Blo 1549472 32252057 := bstep (se 2 (by rfl) ⟨12094521, by rfl⟩ : syracuseStep 32252057 = 24189043) B24189043
theorem B2326751 : Blo 1549472 2326751 := bstep (se 1 (by rfl) ⟨1745063, by rfl⟩ : syracuseStep 2326751 = 3490127) B3490127
theorem B5234921 : Blo 1549472 5234921 := bstep (se 2 (by rfl) ⟨1963095, by rfl⟩ : syracuseStep 5234921 = 3926191) B3926191
theorem B4596763 : Blo 1549472 4596763 := bstep (se 1 (by rfl) ⟨3447572, by rfl⟩ : syracuseStep 4596763 = 6895145) B6895145
theorem B5883623 : Blo 1549472 5883623 := bstep (se 1 (by rfl) ⟨4412717, by rfl⟩ : syracuseStep 5883623 = 8825435) B8825435
theorem B1550079 : Blo 1549472 1550079 := bstep (se 1 (by rfl) ⟨1162559, by rfl⟩ : syracuseStep 1550079 = 2325119) B2325119
theorem B2092600331 : Blo 1549472 2092600331 := bstep (se 1 (by rfl) ⟨1569450248, by rfl⟩ : syracuseStep 2092600331 = 3138900497) B3138900497
theorem B3927143 : Blo 1549472 3927143 := bstep (se 1 (by rfl) ⟨2945357, by rfl⟩ : syracuseStep 3927143 = 5890715) B5890715
theorem B13251923 : Blo 1549472 13251923 := bstep (se 1 (by rfl) ⟨9938942, by rfl⟩ : syracuseStep 13251923 = 19877885) B19877885
theorem B67025231 : Blo 1549472 67025231 := bstep (se 1 (by rfl) ⟨50268923, by rfl⟩ : syracuseStep 67025231 = 100537847) B100537847
theorem B3923113 : Blo 1549472 3923113 := bstep (se 2 (by rfl) ⟨1471167, by rfl⟩ : syracuseStep 3923113 = 2942335) B2942335
theorem B5234003 : Blo 1549472 5234003 := bstep (se 1 (by rfl) ⟨3925502, by rfl⟩ : syracuseStep 5234003 = 7851005) B7851005
theorem B2325851 : Blo 1549472 2325851 := bstep (se 1 (by rfl) ⟨1744388, by rfl⟩ : syracuseStep 2325851 = 3488777) B3488777
theorem B3489947 : Blo 1549472 3489947 := bstep (se 1 (by rfl) ⟨2617460, by rfl⟩ : syracuseStep 3489947 = 5234921) B5234921
theorem B6129017 : Blo 1549472 6129017 := bstep (se 2 (by rfl) ⟨2298381, by rfl⟩ : syracuseStep 6129017 = 4596763) B4596763
theorem B1395066887 : Blo 1549472 1395066887 := bstep (se 1 (by rfl) ⟨1046300165, by rfl⟩ : syracuseStep 1395066887 = 2092600331) B2092600331
theorem B1550567 : Blo 1549472 1550567 := bstep (se 1 (by rfl) ⟨1162925, by rfl⟩ : syracuseStep 1550567 = 2325851) B2325851
theorem B1551167 : Blo 1549472 1551167 := bstep (se 1 (by rfl) ⟨1163375, by rfl⟩ : syracuseStep 1551167 = 2326751) B2326751
theorem B8834615 : Blo 1549472 8834615 := bstep (se 1 (by rfl) ⟨6625961, by rfl⟩ : syracuseStep 8834615 = 13251923) B13251923
theorem B44683487 : Blo 1549472 44683487 := bstep (se 1 (by rfl) ⟨33512615, by rfl⟩ : syracuseStep 44683487 = 67025231) B67025231
theorem B5230817 : Blo 1549472 5230817 := bstep (se 2 (by rfl) ⟨1961556, by rfl⟩ : syracuseStep 5230817 = 3923113) B3923113
theorem B2618095 : Blo 1549472 2618095 := bstep (se 1 (by rfl) ⟨1963571, by rfl⟩ : syracuseStep 2618095 = 3927143) B3927143
theorem B21501371 : Blo 1549472 21501371 := bstep (se 1 (by rfl) ⟨16126028, by rfl⟩ : syracuseStep 21501371 = 32252057) B32252057
theorem B3922415 : Blo 1549472 3922415 := bstep (se 1 (by rfl) ⟨2941811, by rfl⟩ : syracuseStep 3922415 = 5883623) B5883623
theorem B3489335 : Blo 1549472 3489335 := bstep (se 1 (by rfl) ⟨2617001, by rfl⟩ : syracuseStep 3489335 = 5234003) B5234003
theorem B2326631 : Blo 1549472 2326631 := bstep (se 1 (by rfl) ⟨1744973, by rfl⟩ : syracuseStep 2326631 = 3489947) B3489947
theorem B3490793 : Blo 1549472 3490793 := bstep (se 2 (by rfl) ⟨1309047, by rfl⟩ : syracuseStep 3490793 = 2618095) B2618095
theorem B57336989 : Blo 1549472 57336989 := bstep (se 3 (by rfl) ⟨10750685, by rfl⟩ : syracuseStep 57336989 = 21501371) B21501371
theorem B2614943 : Blo 1549472 2614943 := bstep (se 1 (by rfl) ⟨1961207, by rfl⟩ : syracuseStep 2614943 = 3922415) B3922415
theorem B29788991 : Blo 1549472 29788991 := bstep (se 1 (by rfl) ⟨22341743, by rfl⟩ : syracuseStep 29788991 = 44683487) B44683487
theorem B3487211 : Blo 1549472 3487211 := bstep (se 1 (by rfl) ⟨2615408, by rfl⟩ : syracuseStep 3487211 = 5230817) B5230817
theorem B4086011 : Blo 1549472 4086011 := bstep (se 1 (by rfl) ⟨3064508, by rfl⟩ : syracuseStep 4086011 = 6129017) B6129017
theorem B930044591 : Blo 1549472 930044591 := bstep (se 1 (by rfl) ⟨697533443, by rfl⟩ : syracuseStep 930044591 = 1395066887) B1395066887
theorem B2326223 : Blo 1549472 2326223 := bstep (se 1 (by rfl) ⟨1744667, by rfl⟩ : syracuseStep 2326223 = 3489335) B3489335
theorem B5889743 : Blo 1549472 5889743 := bstep (se 1 (by rfl) ⟨4417307, by rfl⟩ : syracuseStep 5889743 = 8834615) B8834615
theorem B2327195 : Blo 1549472 2327195 := bstep (se 1 (by rfl) ⟨1745396, by rfl⟩ : syracuseStep 2327195 = 3490793) B3490793
theorem B10896029 : Blo 1549472 10896029 := bstep (se 3 (by rfl) ⟨2043005, by rfl⟩ : syracuseStep 10896029 = 4086011) B4086011
theorem B620029727 : Blo 1549472 620029727 := bstep (se 1 (by rfl) ⟨465022295, by rfl⟩ : syracuseStep 620029727 = 930044591) B930044591
theorem B19859327 : Blo 1549472 19859327 := bstep (se 1 (by rfl) ⟨14894495, by rfl⟩ : syracuseStep 19859327 = 29788991) B29788991
theorem B1550815 : Blo 1549472 1550815 := bstep (se 1 (by rfl) ⟨1163111, by rfl⟩ : syracuseStep 1550815 = 2326223) B2326223
theorem B3926495 : Blo 1549472 3926495 := bstep (se 1 (by rfl) ⟨2944871, by rfl⟩ : syracuseStep 3926495 = 5889743) B5889743
theorem B1551087 : Blo 1549472 1551087 := bstep (se 1 (by rfl) ⟨1163315, by rfl⟩ : syracuseStep 1551087 = 2326631) B2326631
theorem B152898637 : Blo 1549472 152898637 := bstep (se 3 (by rfl) ⟨28668494, by rfl⟩ : syracuseStep 152898637 = 57336989) B57336989
theorem B2324807 : Blo 1549472 2324807 := bstep (se 1 (by rfl) ⟨1743605, by rfl⟩ : syracuseStep 2324807 = 3487211) B3487211
theorem B1743295 : Blo 1549472 1743295 := bstep (se 1 (by rfl) ⟨1307471, by rfl⟩ : syracuseStep 1743295 = 2614943) B2614943
theorem B413353151 : Blo 1549472 413353151 := bstep (se 1 (by rfl) ⟨310014863, by rfl⟩ : syracuseStep 413353151 = 620029727) B620029727
theorem B13239551 : Blo 1549472 13239551 := bstep (se 1 (by rfl) ⟨9929663, by rfl⟩ : syracuseStep 13239551 = 19859327) B19859327
theorem B1549871 : Blo 1549472 1549871 := bstep (se 1 (by rfl) ⟨1162403, by rfl⟩ : syracuseStep 1549871 = 2324807) B2324807
theorem B1551463 : Blo 1549472 1551463 := bstep (se 1 (by rfl) ⟨1163597, by rfl⟩ : syracuseStep 1551463 = 2327195) B2327195
theorem B2617663 : Blo 1549472 2617663 := bstep (se 1 (by rfl) ⟨1963247, by rfl⟩ : syracuseStep 2617663 = 3926495) B3926495
theorem B7264019 : Blo 1549472 7264019 := bstep (se 1 (by rfl) ⟨5448014, by rfl⟩ : syracuseStep 7264019 = 10896029) B10896029
theorem B2324393 : Blo 1549472 2324393 := bstep (se 2 (by rfl) ⟨871647, by rfl⟩ : syracuseStep 2324393 = 1743295) B1743295
theorem B203864849 : Blo 1549472 203864849 := bstep (se 2 (by rfl) ⟨76449318, by rfl⟩ : syracuseStep 203864849 = 152898637) B152898637
theorem B3490217 : Blo 1549472 3490217 := bstep (se 2 (by rfl) ⟨1308831, by rfl⟩ : syracuseStep 3490217 = 2617663) B2617663
theorem B4842679 : Blo 1549472 4842679 := bstep (se 1 (by rfl) ⟨3632009, by rfl⟩ : syracuseStep 4842679 = 7264019) B7264019
theorem B1549595 : Blo 1549472 1549595 := bstep (se 1 (by rfl) ⟨1162196, by rfl⟩ : syracuseStep 1549595 = 2324393) B2324393
theorem B8826367 : Blo 1549472 8826367 := bstep (se 1 (by rfl) ⟨6619775, by rfl⟩ : syracuseStep 8826367 = 13239551) B13239551
theorem B135909899 : Blo 1549472 135909899 := bstep (se 1 (by rfl) ⟨101932424, by rfl⟩ : syracuseStep 135909899 = 203864849) B203864849
theorem B275568767 : Blo 1549472 275568767 := bstep (se 1 (by rfl) ⟨206676575, by rfl⟩ : syracuseStep 275568767 = 413353151) B413353151
theorem B2326811 : Blo 1549472 2326811 := bstep (se 1 (by rfl) ⟨1745108, by rfl⟩ : syracuseStep 2326811 = 3490217) B3490217
theorem B6456905 : Blo 1549472 6456905 := bstep (se 2 (by rfl) ⟨2421339, by rfl⟩ : syracuseStep 6456905 = 4842679) B4842679
theorem B90606599 : Blo 1549472 90606599 := bstep (se 1 (by rfl) ⟨67954949, by rfl⟩ : syracuseStep 90606599 = 135909899) B135909899
theorem B11768489 : Blo 1549472 11768489 := bstep (se 2 (by rfl) ⟨4413183, by rfl⟩ : syracuseStep 11768489 = 8826367) B8826367
theorem B183712511 : Blo 1549472 183712511 := bstep (se 1 (by rfl) ⟨137784383, by rfl⟩ : syracuseStep 183712511 = 275568767) B275568767
theorem B1551207 : Blo 1549472 1551207 := bstep (se 1 (by rfl) ⟨1163405, by rfl⟩ : syracuseStep 1551207 = 2326811) B2326811
theorem B4304603 : Blo 1549472 4304603 := bstep (se 1 (by rfl) ⟨3228452, by rfl⟩ : syracuseStep 4304603 = 6456905) B6456905
theorem B122475007 : Blo 1549472 122475007 := bstep (se 1 (by rfl) ⟨91856255, by rfl⟩ : syracuseStep 122475007 = 183712511) B183712511
theorem B60404399 : Blo 1549472 60404399 := bstep (se 1 (by rfl) ⟨45303299, by rfl⟩ : syracuseStep 60404399 = 90606599) B90606599
theorem B7845659 : Blo 1549472 7845659 := bstep (se 1 (by rfl) ⟨5884244, by rfl⟩ : syracuseStep 7845659 = 11768489) B11768489
theorem B2869735 : Blo 1549472 2869735 := bstep (se 1 (by rfl) ⟨2152301, by rfl⟩ : syracuseStep 2869735 = 4304603) B4304603
theorem B653200037 : Blo 1549472 653200037 := bstep (se 4 (by rfl) ⟨61237503, by rfl⟩ : syracuseStep 653200037 = 122475007) B122475007
theorem B5230439 : Blo 1549472 5230439 := bstep (se 1 (by rfl) ⟨3922829, by rfl⟩ : syracuseStep 5230439 = 7845659) B7845659
theorem B40269599 : Blo 1549472 40269599 := bstep (se 1 (by rfl) ⟨30202199, by rfl⟩ : syracuseStep 40269599 = 60404399) B60404399
theorem B3826313 : Blo 1549472 3826313 := bstep (se 2 (by rfl) ⟨1434867, by rfl⟩ : syracuseStep 3826313 = 2869735) B2869735
theorem B26846399 : Blo 1549472 26846399 := bstep (se 1 (by rfl) ⟨20134799, by rfl⟩ : syracuseStep 26846399 = 40269599) B40269599
theorem B435466691 : Blo 1549472 435466691 := bstep (se 1 (by rfl) ⟨326600018, by rfl⟩ : syracuseStep 435466691 = 653200037) B653200037
theorem B3486959 : Blo 1549472 3486959 := bstep (se 1 (by rfl) ⟨2615219, by rfl⟩ : syracuseStep 3486959 = 5230439) B5230439
theorem B71590397 : Blo 1549472 71590397 := bstep (se 3 (by rfl) ⟨13423199, by rfl⟩ : syracuseStep 71590397 = 26846399) B26846399
theorem B290311127 : Blo 1549472 290311127 := bstep (se 1 (by rfl) ⟨217733345, by rfl⟩ : syracuseStep 290311127 = 435466691) B435466691
theorem B2550875 : Blo 1549472 2550875 := bstep (se 1 (by rfl) ⟨1913156, by rfl⟩ : syracuseStep 2550875 = 3826313) B3826313
theorem B2324639 : Blo 1549472 2324639 := bstep (se 1 (by rfl) ⟨1743479, by rfl⟩ : syracuseStep 2324639 = 3486959) B3486959
theorem B190907725 : Blo 1549472 190907725 := bstep (se 3 (by rfl) ⟨35795198, by rfl⟩ : syracuseStep 190907725 = 71590397) B71590397
theorem B1549759 : Blo 1549472 1549759 := bstep (se 1 (by rfl) ⟨1162319, by rfl⟩ : syracuseStep 1549759 = 2324639) B2324639
theorem B27209333 : Blo 1549472 27209333 := bstep (se 5 (by rfl) ⟨1275437, by rfl⟩ : syracuseStep 27209333 = 2550875) B2550875
theorem B193540751 : Blo 1549472 193540751 := bstep (se 1 (by rfl) ⟨145155563, by rfl⟩ : syracuseStep 193540751 = 290311127) B290311127
theorem B254543633 : Blo 1549472 254543633 := bstep (se 2 (by rfl) ⟨95453862, by rfl⟩ : syracuseStep 254543633 = 190907725) B190907725
theorem B18139555 : Blo 1549472 18139555 := bstep (se 1 (by rfl) ⟨13604666, by rfl⟩ : syracuseStep 18139555 = 27209333) B27209333
theorem B129027167 : Blo 1549472 129027167 := bstep (se 1 (by rfl) ⟨96770375, by rfl⟩ : syracuseStep 129027167 = 193540751) B193540751
theorem B86018111 : Blo 1549472 86018111 := bstep (se 1 (by rfl) ⟨64513583, by rfl⟩ : syracuseStep 86018111 = 129027167) B129027167
theorem B96744293 : Blo 1549472 96744293 := bstep (se 4 (by rfl) ⟨9069777, by rfl⟩ : syracuseStep 96744293 = 18139555) B18139555
theorem B169695755 : Blo 1549472 169695755 := bstep (se 1 (by rfl) ⟨127271816, by rfl⟩ : syracuseStep 169695755 = 254543633) B254543633
theorem B64496195 : Blo 1549472 64496195 := bstep (se 1 (by rfl) ⟨48372146, by rfl⟩ : syracuseStep 64496195 = 96744293) B96744293
theorem B57345407 : Blo 1549472 57345407 := bstep (se 1 (by rfl) ⟨43009055, by rfl⟩ : syracuseStep 57345407 = 86018111) B86018111
theorem B113130503 : Blo 1549472 113130503 := bstep (se 1 (by rfl) ⟨84847877, by rfl⟩ : syracuseStep 113130503 = 169695755) B169695755
theorem B75420335 : Blo 1549472 75420335 := bstep (se 1 (by rfl) ⟨56565251, by rfl⟩ : syracuseStep 75420335 = 113130503) B113130503
theorem B42997463 : Blo 1549472 42997463 := bstep (se 1 (by rfl) ⟨32248097, by rfl⟩ : syracuseStep 42997463 = 64496195) B64496195
theorem B38230271 : Blo 1549472 38230271 := bstep (se 1 (by rfl) ⟨28672703, by rfl⟩ : syracuseStep 38230271 = 57345407) B57345407
theorem B28664975 : Blo 1549472 28664975 := bstep (se 1 (by rfl) ⟨21498731, by rfl⟩ : syracuseStep 28664975 = 42997463) B42997463
theorem B25486847 : Blo 1549472 25486847 := bstep (se 1 (by rfl) ⟨19115135, by rfl⟩ : syracuseStep 25486847 = 38230271) B38230271
theorem B50280223 : Blo 1549472 50280223 := bstep (se 1 (by rfl) ⟨37710167, by rfl⟩ : syracuseStep 50280223 = 75420335) B75420335
theorem B76439933 : Blo 1549472 76439933 := bstep (se 3 (by rfl) ⟨14332487, by rfl⟩ : syracuseStep 76439933 = 28664975) B28664975
theorem B16991231 : Blo 1549472 16991231 := bstep (se 1 (by rfl) ⟨12743423, by rfl⟩ : syracuseStep 16991231 = 25486847) B25486847
theorem B67040297 : Blo 1549472 67040297 := bstep (se 2 (by rfl) ⟨25140111, by rfl⟩ : syracuseStep 67040297 = 50280223) B50280223
theorem B50959955 : Blo 1549472 50959955 := bstep (se 1 (by rfl) ⟨38219966, by rfl⟩ : syracuseStep 50959955 = 76439933) B76439933
theorem B44693531 : Blo 1549472 44693531 := bstep (se 1 (by rfl) ⟨33520148, by rfl⟩ : syracuseStep 44693531 = 67040297) B67040297
theorem B45309949 : Blo 1549472 45309949 := bstep (se 3 (by rfl) ⟨8495615, by rfl⟩ : syracuseStep 45309949 = 16991231) B16991231
theorem B33973303 : Blo 1549472 33973303 := bstep (se 1 (by rfl) ⟨25479977, by rfl⟩ : syracuseStep 33973303 = 50959955) B50959955
theorem B29795687 : Blo 1549472 29795687 := bstep (se 1 (by rfl) ⟨22346765, by rfl⟩ : syracuseStep 29795687 = 44693531) B44693531
theorem B241653061 : Blo 1549472 241653061 := bstep (se 4 (by rfl) ⟨22654974, by rfl⟩ : syracuseStep 241653061 = 45309949) B45309949
theorem B45297737 : Blo 1549472 45297737 := bstep (se 2 (by rfl) ⟨16986651, by rfl⟩ : syracuseStep 45297737 = 33973303) B33973303
theorem B322204081 : Blo 1549472 322204081 := bstep (se 2 (by rfl) ⟨120826530, by rfl⟩ : syracuseStep 322204081 = 241653061) B241653061
theorem B19863791 : Blo 1549472 19863791 := bstep (se 1 (by rfl) ⟨14897843, by rfl⟩ : syracuseStep 19863791 = 29795687) B29795687
theorem B429605441 : Blo 1549472 429605441 := bstep (se 2 (by rfl) ⟨161102040, by rfl⟩ : syracuseStep 429605441 = 322204081) B322204081
theorem B30198491 : Blo 1549472 30198491 := bstep (se 1 (by rfl) ⟨22648868, by rfl⟩ : syracuseStep 30198491 = 45297737) B45297737
theorem B13242527 : Blo 1549472 13242527 := bstep (se 1 (by rfl) ⟨9931895, by rfl⟩ : syracuseStep 13242527 = 19863791) B19863791
theorem B286403627 : Blo 1549472 286403627 := bstep (se 1 (by rfl) ⟨214802720, by rfl⟩ : syracuseStep 286403627 = 429605441) B429605441
theorem B20132327 : Blo 1549472 20132327 := bstep (se 1 (by rfl) ⟨15099245, by rfl⟩ : syracuseStep 20132327 = 30198491) B30198491
theorem B8828351 : Blo 1549472 8828351 := bstep (se 1 (by rfl) ⟨6621263, by rfl⟩ : syracuseStep 8828351 = 13242527) B13242527
theorem B13421551 : Blo 1549472 13421551 := bstep (se 1 (by rfl) ⟨10066163, by rfl⟩ : syracuseStep 13421551 = 20132327) B20132327
theorem B5885567 : Blo 1549472 5885567 := bstep (se 1 (by rfl) ⟨4414175, by rfl⟩ : syracuseStep 5885567 = 8828351) B8828351
theorem B190935751 : Blo 1549472 190935751 := bstep (se 1 (by rfl) ⟨143201813, by rfl⟩ : syracuseStep 190935751 = 286403627) B286403627
theorem B17895401 : Blo 1549472 17895401 := bstep (se 2 (by rfl) ⟨6710775, by rfl⟩ : syracuseStep 17895401 = 13421551) B13421551
theorem B254581001 : Blo 1549472 254581001 := bstep (se 2 (by rfl) ⟨95467875, by rfl⟩ : syracuseStep 254581001 = 190935751) B190935751
theorem B3923711 : Blo 1549472 3923711 := bstep (se 1 (by rfl) ⟨2942783, by rfl⟩ : syracuseStep 3923711 = 5885567) B5885567
theorem B2615807 : Blo 1549472 2615807 := bstep (se 1 (by rfl) ⟨1961855, by rfl⟩ : syracuseStep 2615807 = 3923711) B3923711
theorem B11930267 : Blo 1549472 11930267 := bstep (se 1 (by rfl) ⟨8947700, by rfl⟩ : syracuseStep 11930267 = 17895401) B17895401
theorem B169720667 : Blo 1549472 169720667 := bstep (se 1 (by rfl) ⟨127290500, by rfl⟩ : syracuseStep 169720667 = 254581001) B254581001
theorem B1743871 : Blo 1549472 1743871 := bstep (se 1 (by rfl) ⟨1307903, by rfl⟩ : syracuseStep 1743871 = 2615807) B2615807
theorem B7953511 : Blo 1549472 7953511 := bstep (se 1 (by rfl) ⟨5965133, by rfl⟩ : syracuseStep 7953511 = 11930267) B11930267
theorem B113147111 : Blo 1549472 113147111 := bstep (se 1 (by rfl) ⟨84860333, by rfl⟩ : syracuseStep 113147111 = 169720667) B169720667
theorem B10604681 : Blo 1549472 10604681 := bstep (se 2 (by rfl) ⟨3976755, by rfl⟩ : syracuseStep 10604681 = 7953511) B7953511
theorem B2325161 : Blo 1549472 2325161 := bstep (se 2 (by rfl) ⟨871935, by rfl⟩ : syracuseStep 2325161 = 1743871) B1743871
theorem B75431407 : Blo 1549472 75431407 := bstep (se 1 (by rfl) ⟨56573555, by rfl⟩ : syracuseStep 75431407 = 113147111) B113147111
theorem B7069787 : Blo 1549472 7069787 := bstep (se 1 (by rfl) ⟨5302340, by rfl⟩ : syracuseStep 7069787 = 10604681) B10604681
theorem B1550107 : Blo 1549472 1550107 := bstep (se 1 (by rfl) ⟨1162580, by rfl⟩ : syracuseStep 1550107 = 2325161) B2325161
theorem B100575209 : Blo 1549472 100575209 := bstep (se 2 (by rfl) ⟨37715703, by rfl⟩ : syracuseStep 100575209 = 75431407) B75431407
theorem B4713191 : Blo 1549472 4713191 := bstep (se 1 (by rfl) ⟨3534893, by rfl⟩ : syracuseStep 4713191 = 7069787) B7069787
theorem B67050139 : Blo 1549472 67050139 := bstep (se 1 (by rfl) ⟨50287604, by rfl⟩ : syracuseStep 67050139 = 100575209) B100575209
theorem B89400185 : Blo 1549472 89400185 := bstep (se 2 (by rfl) ⟨33525069, by rfl⟩ : syracuseStep 89400185 = 67050139) B67050139
theorem B3142127 : Blo 1549472 3142127 := bstep (se 1 (by rfl) ⟨2356595, by rfl⟩ : syracuseStep 3142127 = 4713191) B4713191
theorem B59600123 : Blo 1549472 59600123 := bstep (se 1 (by rfl) ⟨44700092, by rfl⟩ : syracuseStep 59600123 = 89400185) B89400185
theorem B2094751 : Blo 1549472 2094751 := bstep (se 1 (by rfl) ⟨1571063, by rfl⟩ : syracuseStep 2094751 = 3142127) B3142127
theorem B39733415 : Blo 1549472 39733415 := bstep (se 1 (by rfl) ⟨29800061, by rfl⟩ : syracuseStep 39733415 = 59600123) B59600123
theorem B2793001 : Blo 1549472 2793001 := bstep (se 2 (by rfl) ⟨1047375, by rfl⟩ : syracuseStep 2793001 = 2094751) B2094751
theorem B26488943 : Blo 1549472 26488943 := bstep (se 1 (by rfl) ⟨19866707, by rfl⟩ : syracuseStep 26488943 = 39733415) B39733415
theorem B3724001 : Blo 1549472 3724001 := bstep (se 2 (by rfl) ⟨1396500, by rfl⟩ : syracuseStep 3724001 = 2793001) B2793001
theorem B2482667 : Blo 1549472 2482667 := bstep (se 1 (by rfl) ⟨1862000, by rfl⟩ : syracuseStep 2482667 = 3724001) B3724001
theorem B17659295 : Blo 1549472 17659295 := bstep (se 1 (by rfl) ⟨13244471, by rfl⟩ : syracuseStep 17659295 = 26488943) B26488943
theorem B1655111 : Blo 1549472 1655111 := bstep (se 1 (by rfl) ⟨1241333, by rfl⟩ : syracuseStep 1655111 = 2482667) B2482667
theorem B11772863 : Blo 1549472 11772863 := bstep (se 1 (by rfl) ⟨8829647, by rfl⟩ : syracuseStep 11772863 = 17659295) B17659295
theorem B7848575 : Blo 1549472 7848575 := bstep (se 1 (by rfl) ⟨5886431, by rfl⟩ : syracuseStep 7848575 = 11772863) B11772863
theorem B4413629 : Blo 1549472 4413629 := bstep (se 3 (by rfl) ⟨827555, by rfl⟩ : syracuseStep 4413629 = 1655111) B1655111
theorem B2942419 : Blo 1549472 2942419 := bstep (se 1 (by rfl) ⟨2206814, by rfl⟩ : syracuseStep 2942419 = 4413629) B4413629
theorem B5232383 : Blo 1549472 5232383 := bstep (se 1 (by rfl) ⟨3924287, by rfl⟩ : syracuseStep 5232383 = 7848575) B7848575
theorem B3488255 : Blo 1549472 3488255 := bstep (se 1 (by rfl) ⟨2616191, by rfl⟩ : syracuseStep 3488255 = 5232383) B5232383
theorem B3923225 : Blo 1549472 3923225 := bstep (se 2 (by rfl) ⟨1471209, by rfl⟩ : syracuseStep 3923225 = 2942419) B2942419
theorem B2615483 : Blo 1549472 2615483 := bstep (se 1 (by rfl) ⟨1961612, by rfl⟩ : syracuseStep 2615483 = 3923225) B3923225
theorem B2325503 : Blo 1549472 2325503 := bstep (se 1 (by rfl) ⟨1744127, by rfl⟩ : syracuseStep 2325503 = 3488255) B3488255
theorem B1550335 : Blo 1549472 1550335 := bstep (se 1 (by rfl) ⟨1162751, by rfl⟩ : syracuseStep 1550335 = 2325503) B2325503
theorem B1743655 : Blo 1549472 1743655 := bstep (se 1 (by rfl) ⟨1307741, by rfl⟩ : syracuseStep 1743655 = 2615483) B2615483
theorem B2324873 : Blo 1549472 2324873 := bstep (se 2 (by rfl) ⟨871827, by rfl⟩ : syracuseStep 2324873 = 1743655) B1743655
theorem B1549915 : Blo 1549472 1549915 := bstep (se 1 (by rfl) ⟨1162436, by rfl⟩ : syracuseStep 1549915 = 2324873) B2324873

theorem C0 (j : ℕ) (h1 : 387368 ≤ j) (h2 : j ≤ 387867) : Blo 1549472 (4 * j + 3) := by
  interval_cases j
  · exact B1549475
  · exact B1549479
  · exact B1549483
  · exact B1549487
  · exact B1549491
  · exact B1549495
  · exact B1549499
  · exact B1549503
  · exact B1549507
  · exact B1549511
  · exact B1549515
  · exact B1549519
  · exact B1549523
  · exact B1549527
  · exact B1549531
  · exact B1549535
  · exact B1549539
  · exact B1549543
  · exact B1549547
  · exact B1549551
  · exact B1549555
  · exact B1549559
  · exact B1549563
  · exact B1549567
  · exact B1549571
  · exact B1549575
  · exact B1549579
  · exact B1549583
  · exact B1549587
  · exact B1549591
  · exact B1549595
  · exact B1549599
  · exact B1549603
  · exact B1549607
  · exact B1549611
  · exact B1549615
  · exact B1549619
  · exact B1549623
  · exact B1549627
  · exact B1549631
  · exact B1549635
  · exact B1549639
  · exact B1549643
  · exact B1549647
  · exact B1549651
  · exact B1549655
  · exact B1549659
  · exact B1549663
  · exact B1549667
  · exact B1549671
  · exact B1549675
  · exact B1549679
  · exact B1549683
  · exact B1549687
  · exact B1549691
  · exact B1549695
  · exact B1549699
  · exact B1549703
  · exact B1549707
  · exact B1549711
  · exact B1549715
  · exact B1549719
  · exact B1549723
  · exact B1549727
  · exact B1549731
  · exact B1549735
  · exact B1549739
  · exact B1549743
  · exact B1549747
  · exact B1549751
  · exact B1549755
  · exact B1549759
  · exact B1549763
  · exact B1549767
  · exact B1549771
  · exact B1549775
  · exact B1549779
  · exact B1549783
  · exact B1549787
  · exact B1549791
  · exact B1549795
  · exact B1549799
  · exact B1549803
  · exact B1549807
  · exact B1549811
  · exact B1549815
  · exact B1549819
  · exact B1549823
  · exact B1549827
  · exact B1549831
  · exact B1549835
  · exact B1549839
  · exact B1549843
  · exact B1549847
  · exact B1549851
  · exact B1549855
  · exact B1549859
  · exact B1549863
  · exact B1549867
  · exact B1549871
  · exact B1549875
  · exact B1549879
  · exact B1549883
  · exact B1549887
  · exact B1549891
  · exact B1549895
  · exact B1549899
  · exact B1549903
  · exact B1549907
  · exact B1549911
  · exact B1549915
  · exact B1549919
  · exact B1549923
  · exact B1549927
  · exact B1549931
  · exact B1549935
  · exact B1549939
  · exact B1549943
  · exact B1549947
  · exact B1549951
  · exact B1549955
  · exact B1549959
  · exact B1549963
  · exact B1549967
  · exact B1549971
  · exact B1549975
  · exact B1549979
  · exact B1549983
  · exact B1549987
  · exact B1549991
  · exact B1549995
  · exact B1549999
  · exact B1550003
  · exact B1550007
  · exact B1550011
  · exact B1550015
  · exact B1550019
  · exact B1550023
  · exact B1550027
  · exact B1550031
  · exact B1550035
  · exact B1550039
  · exact B1550043
  · exact B1550047
  · exact B1550051
  · exact B1550055
  · exact B1550059
  · exact B1550063
  · exact B1550067
  · exact B1550071
  · exact B1550075
  · exact B1550079
  · exact B1550083
  · exact B1550087
  · exact B1550091
  · exact B1550095
  · exact B1550099
  · exact B1550103
  · exact B1550107
  · exact B1550111
  · exact B1550115
  · exact B1550119
  · exact B1550123
  · exact B1550127
  · exact B1550131
  · exact B1550135
  · exact B1550139
  · exact B1550143
  · exact B1550147
  · exact B1550151
  · exact B1550155
  · exact B1550159
  · exact B1550163
  · exact B1550167
  · exact B1550171
  · exact B1550175
  · exact B1550179
  · exact B1550183
  · exact B1550187
  · exact B1550191
  · exact B1550195
  · exact B1550199
  · exact B1550203
  · exact B1550207
  · exact B1550211
  · exact B1550215
  · exact B1550219
  · exact B1550223
  · exact B1550227
  · exact B1550231
  · exact B1550235
  · exact B1550239
  · exact B1550243
  · exact B1550247
  · exact B1550251
  · exact B1550255
  · exact B1550259
  · exact B1550263
  · exact B1550267
  · exact B1550271
  · exact B1550275
  · exact B1550279
  · exact B1550283
  · exact B1550287
  · exact B1550291
  · exact B1550295
  · exact B1550299
  · exact B1550303
  · exact B1550307
  · exact B1550311
  · exact B1550315
  · exact B1550319
  · exact B1550323
  · exact B1550327
  · exact B1550331
  · exact B1550335
  · exact B1550339
  · exact B1550343
  · exact B1550347
  · exact B1550351
  · exact B1550355
  · exact B1550359
  · exact B1550363
  · exact B1550367
  · exact B1550371
  · exact B1550375
  · exact B1550379
  · exact B1550383
  · exact B1550387
  · exact B1550391
  · exact B1550395
  · exact B1550399
  · exact B1550403
  · exact B1550407
  · exact B1550411
  · exact B1550415
  · exact B1550419
  · exact B1550423
  · exact B1550427
  · exact B1550431
  · exact B1550435
  · exact B1550439
  · exact B1550443
  · exact B1550447
  · exact B1550451
  · exact B1550455
  · exact B1550459
  · exact B1550463
  · exact B1550467
  · exact B1550471
  · exact B1550475
  · exact B1550479
  · exact B1550483
  · exact B1550487
  · exact B1550491
  · exact B1550495
  · exact B1550499
  · exact B1550503
  · exact B1550507
  · exact B1550511
  · exact B1550515
  · exact B1550519
  · exact B1550523
  · exact B1550527
  · exact B1550531
  · exact B1550535
  · exact B1550539
  · exact B1550543
  · exact B1550547
  · exact B1550551
  · exact B1550555
  · exact B1550559
  · exact B1550563
  · exact B1550567
  · exact B1550571
  · exact B1550575
  · exact B1550579
  · exact B1550583
  · exact B1550587
  · exact B1550591
  · exact B1550595
  · exact B1550599
  · exact B1550603
  · exact B1550607
  · exact B1550611
  · exact B1550615
  · exact B1550619
  · exact B1550623
  · exact B1550627
  · exact B1550631
  · exact B1550635
  · exact B1550639
  · exact B1550643
  · exact B1550647
  · exact B1550651
  · exact B1550655
  · exact B1550659
  · exact B1550663
  · exact B1550667
  · exact B1550671
  · exact B1550675
  · exact B1550679
  · exact B1550683
  · exact B1550687
  · exact B1550691
  · exact B1550695
  · exact B1550699
  · exact B1550703
  · exact B1550707
  · exact B1550711
  · exact B1550715
  · exact B1550719
  · exact B1550723
  · exact B1550727
  · exact B1550731
  · exact B1550735
  · exact B1550739
  · exact B1550743
  · exact B1550747
  · exact B1550751
  · exact B1550755
  · exact B1550759
  · exact B1550763
  · exact B1550767
  · exact B1550771
  · exact B1550775
  · exact B1550779
  · exact B1550783
  · exact B1550787
  · exact B1550791
  · exact B1550795
  · exact B1550799
  · exact B1550803
  · exact B1550807
  · exact B1550811
  · exact B1550815
  · exact B1550819
  · exact B1550823
  · exact B1550827
  · exact B1550831
  · exact B1550835
  · exact B1550839
  · exact B1550843
  · exact B1550847
  · exact B1550851
  · exact B1550855
  · exact B1550859
  · exact B1550863
  · exact B1550867
  · exact B1550871
  · exact B1550875
  · exact B1550879
  · exact B1550883
  · exact B1550887
  · exact B1550891
  · exact B1550895
  · exact B1550899
  · exact B1550903
  · exact B1550907
  · exact B1550911
  · exact B1550915
  · exact B1550919
  · exact B1550923
  · exact B1550927
  · exact B1550931
  · exact B1550935
  · exact B1550939
  · exact B1550943
  · exact B1550947
  · exact B1550951
  · exact B1550955
  · exact B1550959
  · exact B1550963
  · exact B1550967
  · exact B1550971
  · exact B1550975
  · exact B1550979
  · exact B1550983
  · exact B1550987
  · exact B1550991
  · exact B1550995
  · exact B1550999
  · exact B1551003
  · exact B1551007
  · exact B1551011
  · exact B1551015
  · exact B1551019
  · exact B1551023
  · exact B1551027
  · exact B1551031
  · exact B1551035
  · exact B1551039
  · exact B1551043
  · exact B1551047
  · exact B1551051
  · exact B1551055
  · exact B1551059
  · exact B1551063
  · exact B1551067
  · exact B1551071
  · exact B1551075
  · exact B1551079
  · exact B1551083
  · exact B1551087
  · exact B1551091
  · exact B1551095
  · exact B1551099
  · exact B1551103
  · exact B1551107
  · exact B1551111
  · exact B1551115
  · exact B1551119
  · exact B1551123
  · exact B1551127
  · exact B1551131
  · exact B1551135
  · exact B1551139
  · exact B1551143
  · exact B1551147
  · exact B1551151
  · exact B1551155
  · exact B1551159
  · exact B1551163
  · exact B1551167
  · exact B1551171
  · exact B1551175
  · exact B1551179
  · exact B1551183
  · exact B1551187
  · exact B1551191
  · exact B1551195
  · exact B1551199
  · exact B1551203
  · exact B1551207
  · exact B1551211
  · exact B1551215
  · exact B1551219
  · exact B1551223
  · exact B1551227
  · exact B1551231
  · exact B1551235
  · exact B1551239
  · exact B1551243
  · exact B1551247
  · exact B1551251
  · exact B1551255
  · exact B1551259
  · exact B1551263
  · exact B1551267
  · exact B1551271
  · exact B1551275
  · exact B1551279
  · exact B1551283
  · exact B1551287
  · exact B1551291
  · exact B1551295
  · exact B1551299
  · exact B1551303
  · exact B1551307
  · exact B1551311
  · exact B1551315
  · exact B1551319
  · exact B1551323
  · exact B1551327
  · exact B1551331
  · exact B1551335
  · exact B1551339
  · exact B1551343
  · exact B1551347
  · exact B1551351
  · exact B1551355
  · exact B1551359
  · exact B1551363
  · exact B1551367
  · exact B1551371
  · exact B1551375
  · exact B1551379
  · exact B1551383
  · exact B1551387
  · exact B1551391
  · exact B1551395
  · exact B1551399
  · exact B1551403
  · exact B1551407
  · exact B1551411
  · exact B1551415
  · exact B1551419
  · exact B1551423
  · exact B1551427
  · exact B1551431
  · exact B1551435
  · exact B1551439
  · exact B1551443
  · exact B1551447
  · exact B1551451
  · exact B1551455
  · exact B1551459
  · exact B1551463
  · exact B1551467
  · exact B1551471

theorem solution (m : ℕ) (hlo : 1549472 ≤ m) (hhi : m ≤ 1551472) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 387368 ≤ j := by omega
    have hj2 : j ≤ 387867 := by omega
    have hb : Blo 1549472 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
