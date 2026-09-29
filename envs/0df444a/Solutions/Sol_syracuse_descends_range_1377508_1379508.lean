-- Prove2me | solution 1 for syracuse_descends_range_1377508_1379508
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:17.920599+00:00
-- url     : https://prove2.me/submissions/1285013b-169d-4693-ac15-de05e16d0196

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


theorem B1744897 : Blo 1377508 1744897 := bbase (se 2 (by rfl) ⟨654336, by rfl⟩ : syracuseStep 1744897 = 1308673) (by norm_num)
theorem B2326549 : Blo 1377508 2326549 := bbase (se 6 (by rfl) ⟨54528, by rfl⟩ : syracuseStep 2326549 = 109057) (by norm_num)
theorem B4653125 : Blo 1377508 4653125 := bbase (se 4 (by rfl) ⟨436230, by rfl⟩ : syracuseStep 4653125 = 872461) (by norm_num)
theorem B1744993 : Blo 1377508 1744993 := bbase (se 2 (by rfl) ⟨654372, by rfl⟩ : syracuseStep 1744993 = 1308745) (by norm_num)
theorem B2326637 : Blo 1377508 2326637 := bbase (se 3 (by rfl) ⟨436244, by rfl⟩ : syracuseStep 2326637 = 872489) (by norm_num)
theorem B3489925 : Blo 1377508 3489925 := bbase (se 4 (by rfl) ⟨327180, by rfl⟩ : syracuseStep 3489925 = 654361) (by norm_num)
theorem B6291589 : Blo 1377508 6291589 := bbase (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) (by norm_num)
theorem B1654997 : Blo 1377508 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B3924197 : Blo 1377508 3924197 := bbase (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) (by norm_num)
theorem B2326765 : Blo 1377508 2326765 := bbase (se 3 (by rfl) ⟨436268, by rfl⟩ : syracuseStep 2326765 = 872537) (by norm_num)
theorem B3490037 : Blo 1377508 3490037 := bbase (se 5 (by rfl) ⟨163595, by rfl⟩ : syracuseStep 3490037 = 327191) (by norm_num)
theorem B2834677 : Blo 1377508 2834677 := bbase (se 5 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 2834677 = 265751) (by norm_num)
theorem B1745165 : Blo 1377508 1745165 := bbase (se 3 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 1745165 = 654437) (by norm_num)
theorem B4964645 : Blo 1377508 4964645 := bbase (se 4 (by rfl) ⟨465435, by rfl⟩ : syracuseStep 4964645 = 930871) (by norm_num)
theorem B2326853 : Blo 1377508 2326853 := bbase (se 4 (by rfl) ⟨218142, by rfl⟩ : syracuseStep 2326853 = 436285) (by norm_num)
theorem B1745221 : Blo 1377508 1745221 := bbase (se 4 (by rfl) ⟨163614, by rfl⟩ : syracuseStep 1745221 = 327229) (by norm_num)
theorem B4251989 : Blo 1377508 4251989 := bbase (se 10 (by rfl) ⟨6228, by rfl⟩ : syracuseStep 4251989 = 12457) (by norm_num)
theorem B3924389 : Blo 1377508 3924389 := bbase (se 4 (by rfl) ⟨367911, by rfl⟩ : syracuseStep 3924389 = 735823) (by norm_num)
theorem B1745317 : Blo 1377508 1745317 := bbase (se 4 (by rfl) ⟨163623, by rfl⟩ : syracuseStep 1745317 = 327247) (by norm_num)
theorem B3490229 : Blo 1377508 3490229 := bbase (se 5 (by rfl) ⟨163604, by rfl⟩ : syracuseStep 3490229 = 327209) (by norm_num)
theorem B3539389 : Blo 1377508 3539389 := bbase (se 3 (by rfl) ⟨663635, by rfl⟩ : syracuseStep 3539389 = 1327271) (by norm_num)
theorem B5587397 : Blo 1377508 5587397 := bbase (se 4 (by rfl) ⟨523818, by rfl⟩ : syracuseStep 5587397 = 1047637) (by norm_num)
theorem B2326981 : Blo 1377508 2326981 := bbase (se 4 (by rfl) ⟨218154, by rfl⟩ : syracuseStep 2326981 = 436309) (by norm_num)
theorem B4653557 : Blo 1377508 4653557 := bbase (se 5 (by rfl) ⟨218135, by rfl⟩ : syracuseStep 4653557 = 436271) (by norm_num)
theorem B7168517 : Blo 1377508 7168517 := bbase (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) (by norm_num)
theorem B2327069 : Blo 1377508 2327069 := bbase (se 3 (by rfl) ⟨436325, by rfl⟩ : syracuseStep 2327069 = 872651) (by norm_num)
theorem B1655329 : Blo 1377508 1655329 := bbase (se 2 (by rfl) ⟨620748, by rfl⟩ : syracuseStep 1655329 = 1241497) (by norm_num)
theorem B2482741 : Blo 1377508 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B1491517 : Blo 1377508 1491517 := bbase (se 3 (by rfl) ⟨279659, by rfl⟩ : syracuseStep 1491517 = 559319) (by norm_num)
theorem B1745489 : Blo 1377508 1745489 := bbase (se 2 (by rfl) ⟨654558, by rfl⟩ : syracuseStep 1745489 = 1309117) (by norm_num)
theorem B4194917 : Blo 1377508 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B3359341 : Blo 1377508 3359341 := bbase (se 3 (by rfl) ⟨629876, by rfl⟩ : syracuseStep 3359341 = 1259753) (by norm_num)
theorem B1745545 : Blo 1377508 1745545 := bbase (se 2 (by rfl) ⟨654579, by rfl⟩ : syracuseStep 1745545 = 1309159) (by norm_num)
theorem B2327197 : Blo 1377508 2327197 := bbase (se 3 (by rfl) ⟨436349, by rfl⟩ : syracuseStep 2327197 = 872699) (by norm_num)
theorem B1745641 : Blo 1377508 1745641 := bbase (se 2 (by rfl) ⟨654615, by rfl⟩ : syracuseStep 1745641 = 1309231) (by norm_num)
theorem B2327285 : Blo 1377508 2327285 := bbase (se 5 (by rfl) ⟨109091, by rfl⟩ : syracuseStep 2327285 = 218183) (by norm_num)
theorem B3490573 : Blo 1377508 3490573 := bbase (se 3 (by rfl) ⟨654482, by rfl⟩ : syracuseStep 3490573 = 1308965) (by norm_num)
theorem B3310397 : Blo 1377508 3310397 := bbase (se 3 (by rfl) ⟨620699, by rfl⟩ : syracuseStep 3310397 = 1241399) (by norm_num)
theorem B53715797 : Blo 1377508 53715797 := bbase (se 9 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 53715797 = 314741) (by norm_num)
theorem B4416373 : Blo 1377508 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B2327413 : Blo 1377508 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B3490685 : Blo 1377508 3490685 := bbase (se 3 (by rfl) ⟨654503, by rfl⟩ : syracuseStep 3490685 = 1309007) (by norm_num)
theorem B1745813 : Blo 1377508 1745813 := bbase (se 6 (by rfl) ⟨40917, by rfl⟩ : syracuseStep 1745813 = 81835) (by norm_num)
theorem B4653989 : Blo 1377508 4653989 := bbase (se 4 (by rfl) ⟨436311, by rfl⟩ : syracuseStep 4653989 = 872623) (by norm_num)
theorem B6718373 : Blo 1377508 6718373 := bbase (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) (by norm_num)
theorem B2794429 : Blo 1377508 2794429 := bbase (se 3 (by rfl) ⟨523955, by rfl⟩ : syracuseStep 2794429 = 1047911) (by norm_num)
theorem B2327501 : Blo 1377508 2327501 := bbase (se 3 (by rfl) ⟨436406, by rfl⟩ : syracuseStep 2327501 = 872813) (by norm_num)
theorem B1745869 : Blo 1377508 1745869 := bbase (se 3 (by rfl) ⟨327350, by rfl⟩ : syracuseStep 1745869 = 654701) (by norm_num)
theorem B2483245 : Blo 1377508 2483245 := bbase (se 3 (by rfl) ⟨465608, by rfl⟩ : syracuseStep 2483245 = 931217) (by norm_num)
theorem B7070773 : Blo 1377508 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B6628405 : Blo 1377508 6628405 := bbase (se 5 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 6628405 = 621413) (by norm_num)
theorem B3490877 : Blo 1377508 3490877 := bbase (se 3 (by rfl) ⟨654539, by rfl⟩ : syracuseStep 3490877 = 1309079) (by norm_num)
theorem B2327629 : Blo 1377508 2327629 := bbase (se 3 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 2327629 = 872861) (by norm_num)
theorem B6980741 : Blo 1377508 6980741 := bbase (se 4 (by rfl) ⟨654444, by rfl⟩ : syracuseStep 6980741 = 1308889) (by norm_num)
theorem B2327717 : Blo 1377508 2327717 := bbase (se 4 (by rfl) ⟨218223, by rfl⟩ : syracuseStep 2327717 = 436447) (by norm_num)
theorem B2942165 : Blo 1377508 2942165 := bbase (se 7 (by rfl) ⟨34478, by rfl⟩ : syracuseStep 2942165 = 68957) (by norm_num)
theorem B2327845 : Blo 1377508 2327845 := bbase (se 4 (by rfl) ⟨218235, by rfl⟩ : syracuseStep 2327845 = 436471) (by norm_num)
theorem B4654421 : Blo 1377508 4654421 := bbase (se 12 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 4654421 = 3409) (by norm_num)
theorem B3925381 : Blo 1377508 3925381 := bbase (se 4 (by rfl) ⟨368004, by rfl⟩ : syracuseStep 3925381 = 736009) (by norm_num)
theorem B1549705 : Blo 1377508 1549705 := bbase (se 2 (by rfl) ⟨581139, by rfl⟩ : syracuseStep 1549705 = 1162279) (by norm_num)
theorem B3491221 : Blo 1377508 3491221 := bbase (se 6 (by rfl) ⟨81825, by rfl⟩ : syracuseStep 3491221 = 163651) (by norm_num)
theorem B1656217 : Blo 1377508 1656217 := bbase (se 2 (by rfl) ⟨621081, by rfl⟩ : syracuseStep 1656217 = 1242163) (by norm_num)
theorem B1549741 : Blo 1377508 1549741 := bbase (se 3 (by rfl) ⟨290576, by rfl⟩ : syracuseStep 1549741 = 581153) (by norm_num)
theorem B1549777 : Blo 1377508 1549777 := bbase (se 2 (by rfl) ⟨581166, by rfl⟩ : syracuseStep 1549777 = 1162333) (by norm_num)
theorem B10470869 : Blo 1377508 10470869 := bbase (se 7 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 10470869 = 245411) (by norm_num)
theorem B1492453 : Blo 1377508 1492453 := bbase (se 4 (by rfl) ⟨139917, by rfl⟩ : syracuseStep 1492453 = 279835) (by norm_num)
theorem B1549813 : Blo 1377508 1549813 := bbase (se 5 (by rfl) ⟨72647, by rfl⟩ : syracuseStep 1549813 = 145295) (by norm_num)
theorem B3491333 : Blo 1377508 3491333 := bbase (se 4 (by rfl) ⟨327312, by rfl⟩ : syracuseStep 3491333 = 654625) (by norm_num)
theorem B1549849 : Blo 1377508 1549849 := bbase (se 2 (by rfl) ⟨581193, by rfl⟩ : syracuseStep 1549849 = 1162387) (by norm_num)
theorem B1549885 : Blo 1377508 1549885 := bbase (se 3 (by rfl) ⟨290603, by rfl⟩ : syracuseStep 1549885 = 581207) (by norm_num)
theorem B1549921 : Blo 1377508 1549921 := bbase (se 2 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 1549921 = 1162441) (by norm_num)
theorem B1549957 : Blo 1377508 1549957 := bbase (se 4 (by rfl) ⟨145308, by rfl⟩ : syracuseStep 1549957 = 290617) (by norm_num)
theorem B1549993 : Blo 1377508 1549993 := bbase (se 2 (by rfl) ⟨581247, by rfl⟩ : syracuseStep 1549993 = 1162495) (by norm_num)
theorem B6620869 : Blo 1377508 6620869 := bbase (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) (by norm_num)
theorem B3491525 : Blo 1377508 3491525 := bbase (se 4 (by rfl) ⟨327330, by rfl⟩ : syracuseStep 3491525 = 654661) (by norm_num)
theorem B1550029 : Blo 1377508 1550029 := bbase (se 3 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 1550029 = 581261) (by norm_num)
theorem B2942669 : Blo 1377508 2942669 := bbase (se 3 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 2942669 = 1103501) (by norm_num)
theorem B2942677 : Blo 1377508 2942677 := bbase (se 7 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 2942677 = 68969) (by norm_num)
theorem B8832725 : Blo 1377508 8832725 := bbase (se 7 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 8832725 = 207017) (by norm_num)
theorem B2238173 : Blo 1377508 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B1550065 : Blo 1377508 1550065 := bbase (se 2 (by rfl) ⟨581274, by rfl⟩ : syracuseStep 1550065 = 1162549) (by norm_num)
theorem B4654853 : Blo 1377508 4654853 := bbase (se 4 (by rfl) ⟨436392, by rfl⟩ : syracuseStep 4654853 = 872785) (by norm_num)
theorem B1550101 : Blo 1377508 1550101 := bbase (se 6 (by rfl) ⟨36330, by rfl⟩ : syracuseStep 1550101 = 72661) (by norm_num)
theorem B2516789 : Blo 1377508 2516789 := bbase (se 5 (by rfl) ⟨117974, by rfl⟩ : syracuseStep 2516789 = 235949) (by norm_num)
theorem B7849781 : Blo 1377508 7849781 := bbase (se 5 (by rfl) ⟨367958, by rfl⟩ : syracuseStep 7849781 = 735917) (by norm_num)
theorem B1550137 : Blo 1377508 1550137 := bbase (se 2 (by rfl) ⟨581301, by rfl⟩ : syracuseStep 1550137 = 1162603) (by norm_num)
theorem B4966229 : Blo 1377508 4966229 := bbase (se 9 (by rfl) ⟨14549, by rfl⟩ : syracuseStep 4966229 = 29099) (by norm_num)
theorem B1550173 : Blo 1377508 1550173 := bbase (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) (by norm_num)
theorem B2066285 : Blo 1377508 2066285 := bbase (se 3 (by rfl) ⟨387428, by rfl⟩ : syracuseStep 2066285 = 774857) (by norm_num)
theorem B9930613 : Blo 1377508 9930613 := bbase (se 5 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 9930613 = 930995) (by norm_num)
theorem B10463093 : Blo 1377508 10463093 := bbase (se 5 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 10463093 = 980915) (by norm_num)
theorem B1550209 : Blo 1377508 1550209 := bbase (se 2 (by rfl) ⟨581328, by rfl⟩ : syracuseStep 1550209 = 1162657) (by norm_num)
theorem B2066309 : Blo 1377508 2066309 := bbase (se 4 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 2066309 = 387433) (by norm_num)
theorem B14903189 : Blo 1377508 14903189 := bbase (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) (by norm_num)
theorem B2066333 : Blo 1377508 2066333 := bbase (se 3 (by rfl) ⟨387437, by rfl⟩ : syracuseStep 2066333 = 774875) (by norm_num)
theorem B2484125 : Blo 1377508 2484125 := bbase (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) (by norm_num)
theorem B1550245 : Blo 1377508 1550245 := bbase (se 4 (by rfl) ⟨145335, by rfl⟩ : syracuseStep 1550245 = 290671) (by norm_num)
theorem B2066357 : Blo 1377508 2066357 := bbase (se 5 (by rfl) ⟨96860, by rfl⟩ : syracuseStep 2066357 = 193721) (by norm_num)
theorem B1550281 : Blo 1377508 1550281 := bbase (se 2 (by rfl) ⟨581355, by rfl⟩ : syracuseStep 1550281 = 1162711) (by norm_num)
theorem B2066381 : Blo 1377508 2066381 := bbase (se 3 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 2066381 = 774893) (by norm_num)
theorem B2066405 : Blo 1377508 2066405 := bbase (se 4 (by rfl) ⟨193725, by rfl⟩ : syracuseStep 2066405 = 387451) (by norm_num)
theorem B1550317 : Blo 1377508 1550317 := bbase (se 3 (by rfl) ⟨290684, by rfl⟩ : syracuseStep 1550317 = 581369) (by norm_num)
theorem B2066429 : Blo 1377508 2066429 := bbase (se 3 (by rfl) ⟨387455, by rfl⟩ : syracuseStep 2066429 = 774911) (by norm_num)
theorem B1550353 : Blo 1377508 1550353 := bbase (se 2 (by rfl) ⟨581382, by rfl⟩ : syracuseStep 1550353 = 1162765) (by norm_num)
theorem B2066453 : Blo 1377508 2066453 := bbase (se 6 (by rfl) ⟨48432, by rfl⟩ : syracuseStep 2066453 = 96865) (by norm_num)
theorem B5236757 : Blo 1377508 5236757 := bbase (se 6 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 5236757 = 245473) (by norm_num)
theorem B3491869 : Blo 1377508 3491869 := bbase (se 3 (by rfl) ⟨654725, by rfl⟩ : syracuseStep 3491869 = 1309451) (by norm_num)
theorem B2615341 : Blo 1377508 2615341 := bbase (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) (by norm_num)
theorem B2066477 : Blo 1377508 2066477 := bbase (se 3 (by rfl) ⟨387464, by rfl⟩ : syracuseStep 2066477 = 774929) (by norm_num)
theorem B1550389 : Blo 1377508 1550389 := bbase (se 5 (by rfl) ⟨72674, by rfl⟩ : syracuseStep 1550389 = 145349) (by norm_num)
theorem B2795573 : Blo 1377508 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B2066501 : Blo 1377508 2066501 := bbase (se 4 (by rfl) ⟨193734, by rfl⟩ : syracuseStep 2066501 = 387469) (by norm_num)
theorem B1550425 : Blo 1377508 1550425 := bbase (se 2 (by rfl) ⟨581409, by rfl⟩ : syracuseStep 1550425 = 1162819) (by norm_num)
theorem B2066525 : Blo 1377508 2066525 := bbase (se 3 (by rfl) ⟨387473, by rfl⟩ : syracuseStep 2066525 = 774947) (by norm_num)
theorem B2066549 : Blo 1377508 2066549 := bbase (se 5 (by rfl) ⟨96869, by rfl⟩ : syracuseStep 2066549 = 193739) (by norm_num)
theorem B1550461 : Blo 1377508 1550461 := bbase (se 3 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 1550461 = 581423) (by norm_num)
theorem B2795645 : Blo 1377508 2795645 := bbase (se 3 (by rfl) ⟨524183, by rfl⟩ : syracuseStep 2795645 = 1048367) (by norm_num)
theorem B2066573 : Blo 1377508 2066573 := bbase (se 3 (by rfl) ⟨387482, by rfl⟩ : syracuseStep 2066573 = 774965) (by norm_num)
theorem B1550497 : Blo 1377508 1550497 := bbase (se 2 (by rfl) ⟨581436, by rfl⟩ : syracuseStep 1550497 = 1162873) (by norm_num)
theorem B2066597 : Blo 1377508 2066597 := bbase (se 4 (by rfl) ⟨193743, by rfl⟩ : syracuseStep 2066597 = 387487) (by norm_num)
theorem B4655285 : Blo 1377508 4655285 := bbase (se 5 (by rfl) ⟨218216, by rfl⟩ : syracuseStep 4655285 = 436433) (by norm_num)
theorem B2615485 : Blo 1377508 2615485 := bbase (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) (by norm_num)
theorem B2066621 : Blo 1377508 2066621 := bbase (se 3 (by rfl) ⟨387491, by rfl⟩ : syracuseStep 2066621 = 774983) (by norm_num)
theorem B1550533 : Blo 1377508 1550533 := bbase (se 4 (by rfl) ⟨145362, by rfl⟩ : syracuseStep 1550533 = 290725) (by norm_num)
theorem B4417733 : Blo 1377508 4417733 := bbase (se 4 (by rfl) ⟨414162, by rfl⟩ : syracuseStep 4417733 = 828325) (by norm_num)
theorem B2066645 : Blo 1377508 2066645 := bbase (se 7 (by rfl) ⟨24218, by rfl⟩ : syracuseStep 2066645 = 48437) (by norm_num)
theorem B1861861 : Blo 1377508 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B1550569 : Blo 1377508 1550569 := bbase (se 2 (by rfl) ⟨581463, by rfl⟩ : syracuseStep 1550569 = 1162927) (by norm_num)
theorem B2066669 : Blo 1377508 2066669 := bbase (se 3 (by rfl) ⟨387500, by rfl⟩ : syracuseStep 2066669 = 775001) (by norm_num)
theorem B2066693 : Blo 1377508 2066693 := bbase (se 4 (by rfl) ⟨193752, by rfl⟩ : syracuseStep 2066693 = 387505) (by norm_num)
theorem B1550605 : Blo 1377508 1550605 := bbase (se 3 (by rfl) ⟨290738, by rfl⟩ : syracuseStep 1550605 = 581477) (by norm_num)
theorem B2066717 : Blo 1377508 2066717 := bbase (se 3 (by rfl) ⟨387509, by rfl⟩ : syracuseStep 2066717 = 775019) (by norm_num)
theorem B6285605 : Blo 1377508 6285605 := bbase (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) (by norm_num)
theorem B1550641 : Blo 1377508 1550641 := bbase (se 2 (by rfl) ⟨581490, by rfl⟩ : syracuseStep 1550641 = 1162981) (by norm_num)
theorem B2066741 : Blo 1377508 2066741 := bbase (se 5 (by rfl) ⟨96878, by rfl⟩ : syracuseStep 2066741 = 193757) (by norm_num)
theorem B11774261 : Blo 1377508 11774261 := bbase (se 5 (by rfl) ⟨551918, by rfl⟩ : syracuseStep 11774261 = 1103837) (by norm_num)
theorem B5237045 : Blo 1377508 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B4417861 : Blo 1377508 4417861 := bbase (se 4 (by rfl) ⟨414174, by rfl⟩ : syracuseStep 4417861 = 828349) (by norm_num)
theorem B2066765 : Blo 1377508 2066765 := bbase (se 3 (by rfl) ⟨387518, by rfl⟩ : syracuseStep 2066765 = 775037) (by norm_num)
theorem B7072085 : Blo 1377508 7072085 := bbase (se 10 (by rfl) ⟨10359, by rfl⟩ : syracuseStep 7072085 = 20719) (by norm_num)
theorem B1550677 : Blo 1377508 1550677 := bbase (se 10 (by rfl) ⟨2271, by rfl⟩ : syracuseStep 1550677 = 4543) (by norm_num)
theorem B2615645 : Blo 1377508 2615645 := bbase (se 3 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 2615645 = 980867) (by norm_num)
theorem B2066789 : Blo 1377508 2066789 := bbase (se 4 (by rfl) ⟨193761, by rfl⟩ : syracuseStep 2066789 = 387523) (by norm_num)
theorem B1550713 : Blo 1377508 1550713 := bbase (se 2 (by rfl) ⟨581517, by rfl⟩ : syracuseStep 1550713 = 1163035) (by norm_num)
theorem B2066813 : Blo 1377508 2066813 := bbase (se 3 (by rfl) ⟨387527, by rfl⟩ : syracuseStep 2066813 = 775055) (by norm_num)
theorem B2066837 : Blo 1377508 2066837 := bbase (se 6 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 2066837 = 96883) (by norm_num)
theorem B6982037 : Blo 1377508 6982037 := bbase (se 6 (by rfl) ⟨163641, by rfl⟩ : syracuseStep 6982037 = 327283) (by norm_num)
theorem B1550749 : Blo 1377508 1550749 := bbase (se 3 (by rfl) ⟨290765, by rfl⟩ : syracuseStep 1550749 = 581531) (by norm_num)
theorem B2066861 : Blo 1377508 2066861 := bbase (se 3 (by rfl) ⟨387536, by rfl⟩ : syracuseStep 2066861 = 775073) (by norm_num)
theorem B1657265 : Blo 1377508 1657265 := bbase (se 2 (by rfl) ⟨621474, by rfl⟩ : syracuseStep 1657265 = 1242949) (by norm_num)
theorem B1862077 : Blo 1377508 1862077 := bbase (se 3 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 1862077 = 698279) (by norm_num)
theorem B1550785 : Blo 1377508 1550785 := bbase (se 2 (by rfl) ⟨581544, by rfl⟩ : syracuseStep 1550785 = 1163089) (by norm_num)
theorem B2066885 : Blo 1377508 2066885 := bbase (se 4 (by rfl) ⟨193770, by rfl⟩ : syracuseStep 2066885 = 387541) (by norm_num)
theorem B3926485 : Blo 1377508 3926485 := bbase (se 7 (by rfl) ⟨46013, by rfl⟩ : syracuseStep 3926485 = 92027) (by norm_num)
theorem B2066909 : Blo 1377508 2066909 := bbase (se 3 (by rfl) ⟨387545, by rfl⟩ : syracuseStep 2066909 = 775091) (by norm_num)
theorem B1550821 : Blo 1377508 1550821 := bbase (se 4 (by rfl) ⟨145389, by rfl⟩ : syracuseStep 1550821 = 290779) (by norm_num)
theorem B2615789 : Blo 1377508 2615789 := bbase (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) (by norm_num)
theorem B2066933 : Blo 1377508 2066933 := bbase (se 5 (by rfl) ⟨96887, by rfl⟩ : syracuseStep 2066933 = 193775) (by norm_num)
theorem B1550857 : Blo 1377508 1550857 := bbase (se 2 (by rfl) ⟨581571, by rfl⟩ : syracuseStep 1550857 = 1163143) (by norm_num)
theorem B2066957 : Blo 1377508 2066957 := bbase (se 3 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 2066957 = 775109) (by norm_num)
theorem B2066981 : Blo 1377508 2066981 := bbase (se 4 (by rfl) ⟨193779, by rfl⟩ : syracuseStep 2066981 = 387559) (by norm_num)
theorem B1550893 : Blo 1377508 1550893 := bbase (se 3 (by rfl) ⟨290792, by rfl⟩ : syracuseStep 1550893 = 581585) (by norm_num)
theorem B2067005 : Blo 1377508 2067005 := bbase (se 3 (by rfl) ⟨387563, by rfl⟩ : syracuseStep 2067005 = 775127) (by norm_num)
theorem B4418117 : Blo 1377508 4418117 := bbase (se 4 (by rfl) ⟨414198, by rfl⟩ : syracuseStep 4418117 = 828397) (by norm_num)
theorem B1550929 : Blo 1377508 1550929 := bbase (se 2 (by rfl) ⟨581598, by rfl⟩ : syracuseStep 1550929 = 1163197) (by norm_num)
theorem B2067029 : Blo 1377508 2067029 := bbase (se 8 (by rfl) ⟨12111, by rfl⟩ : syracuseStep 2067029 = 24223) (by norm_num)
theorem B3025493 : Blo 1377508 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B4655717 : Blo 1377508 4655717 := bbase (se 4 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 4655717 = 872947) (by norm_num)
theorem B2067053 : Blo 1377508 2067053 := bbase (se 3 (by rfl) ⟨387572, by rfl⟩ : syracuseStep 2067053 = 775145) (by norm_num)
theorem B1550965 : Blo 1377508 1550965 := bbase (se 5 (by rfl) ⟨72701, by rfl⟩ : syracuseStep 1550965 = 145403) (by norm_num)
theorem B2067077 : Blo 1377508 2067077 := bbase (se 4 (by rfl) ⟨193788, by rfl⟩ : syracuseStep 2067077 = 387577) (by norm_num)
theorem B1551001 : Blo 1377508 1551001 := bbase (se 2 (by rfl) ⟨581625, by rfl⟩ : syracuseStep 1551001 = 1163251) (by norm_num)
theorem B2067101 : Blo 1377508 2067101 := bbase (se 3 (by rfl) ⟨387581, by rfl⟩ : syracuseStep 2067101 = 775163) (by norm_num)
theorem B2067125 : Blo 1377508 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B1551037 : Blo 1377508 1551037 := bbase (se 3 (by rfl) ⟨290819, by rfl⟩ : syracuseStep 1551037 = 581639) (by norm_num)
theorem B2067149 : Blo 1377508 2067149 := bbase (se 3 (by rfl) ⟨387590, by rfl⟩ : syracuseStep 2067149 = 775181) (by norm_num)
theorem B1551073 : Blo 1377508 1551073 := bbase (se 2 (by rfl) ⟨581652, by rfl⟩ : syracuseStep 1551073 = 1163305) (by norm_num)
theorem B2067173 : Blo 1377508 2067173 := bbase (se 4 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 2067173 = 387595) (by norm_num)
theorem B2067197 : Blo 1377508 2067197 := bbase (se 3 (by rfl) ⟨387599, by rfl⟩ : syracuseStep 2067197 = 775199) (by norm_num)
theorem B1551109 : Blo 1377508 1551109 := bbase (se 4 (by rfl) ⟨145416, by rfl⟩ : syracuseStep 1551109 = 290833) (by norm_num)
theorem B2616077 : Blo 1377508 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B2067221 : Blo 1377508 2067221 := bbase (se 6 (by rfl) ⟨48450, by rfl⟩ : syracuseStep 2067221 = 96901) (by norm_num)
theorem B1551145 : Blo 1377508 1551145 := bbase (se 2 (by rfl) ⟨581679, by rfl⟩ : syracuseStep 1551145 = 1163359) (by norm_num)
theorem B3099437 : Blo 1377508 3099437 := bbase (se 3 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 3099437 = 1162289) (by norm_num)
theorem B2067245 : Blo 1377508 2067245 := bbase (se 3 (by rfl) ⟨387608, by rfl⟩ : syracuseStep 2067245 = 775217) (by norm_num)
theorem B6974261 : Blo 1377508 6974261 := bbase (se 5 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 6974261 = 653837) (by norm_num)
theorem B2943805 : Blo 1377508 2943805 := bbase (se 3 (by rfl) ⟨551963, by rfl⟩ : syracuseStep 2943805 = 1103927) (by norm_num)
theorem B2067269 : Blo 1377508 2067269 := bbase (se 4 (by rfl) ⟨193806, by rfl⟩ : syracuseStep 2067269 = 387613) (by norm_num)
theorem B2206541 : Blo 1377508 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B1551181 : Blo 1377508 1551181 := bbase (se 3 (by rfl) ⟨290846, by rfl⟩ : syracuseStep 1551181 = 581693) (by norm_num)
theorem B2067293 : Blo 1377508 2067293 := bbase (se 3 (by rfl) ⟨387617, by rfl⟩ : syracuseStep 2067293 = 775235) (by norm_num)
theorem B1551217 : Blo 1377508 1551217 := bbase (se 2 (by rfl) ⟨581706, by rfl⟩ : syracuseStep 1551217 = 1163413) (by norm_num)
theorem B3099509 : Blo 1377508 3099509 := bbase (se 5 (by rfl) ⟨145289, by rfl⟩ : syracuseStep 3099509 = 290579) (by norm_num)
theorem B2067317 : Blo 1377508 2067317 := bbase (se 5 (by rfl) ⟨96905, by rfl⟩ : syracuseStep 2067317 = 193811) (by norm_num)
theorem B2067341 : Blo 1377508 2067341 := bbase (se 3 (by rfl) ⟨387626, by rfl⟩ : syracuseStep 2067341 = 775253) (by norm_num)
theorem B2485133 : Blo 1377508 2485133 := bbase (se 3 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 2485133 = 931925) (by norm_num)
theorem B5032853 : Blo 1377508 5032853 := bbase (se 6 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 5032853 = 235915) (by norm_num)
theorem B15944597 : Blo 1377508 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B1551253 : Blo 1377508 1551253 := bbase (se 6 (by rfl) ⟨36357, by rfl⟩ : syracuseStep 1551253 = 72715) (by norm_num)
theorem B2616229 : Blo 1377508 2616229 := bbase (se 4 (by rfl) ⟨245271, by rfl⟩ : syracuseStep 2616229 = 490543) (by norm_num)
theorem B2067365 : Blo 1377508 2067365 := bbase (se 4 (by rfl) ⟨193815, by rfl⟩ : syracuseStep 2067365 = 387631) (by norm_num)
theorem B1551289 : Blo 1377508 1551289 := bbase (se 2 (by rfl) ⟨581733, by rfl⟩ : syracuseStep 1551289 = 1163467) (by norm_num)
theorem B3099581 : Blo 1377508 3099581 := bbase (se 3 (by rfl) ⟨581171, by rfl⟩ : syracuseStep 3099581 = 1162343) (by norm_num)
theorem B2067389 : Blo 1377508 2067389 := bbase (se 3 (by rfl) ⟨387635, by rfl⟩ : syracuseStep 2067389 = 775271) (by norm_num)
theorem B2067413 : Blo 1377508 2067413 := bbase (se 7 (by rfl) ⟨24227, by rfl⟩ : syracuseStep 2067413 = 48455) (by norm_num)
theorem B7850965 : Blo 1377508 7850965 := bbase (se 7 (by rfl) ⟨92003, by rfl⟩ : syracuseStep 7850965 = 184007) (by norm_num)
theorem B1551325 : Blo 1377508 1551325 := bbase (se 3 (by rfl) ⟨290873, by rfl⟩ : syracuseStep 1551325 = 581747) (by norm_num)
theorem B2067437 : Blo 1377508 2067437 := bbase (se 3 (by rfl) ⟨387644, by rfl⟩ : syracuseStep 2067437 = 775289) (by norm_num)
theorem B1551361 : Blo 1377508 1551361 := bbase (se 2 (by rfl) ⟨581760, by rfl⟩ : syracuseStep 1551361 = 1163521) (by norm_num)
theorem B3099653 : Blo 1377508 3099653 := bbase (se 4 (by rfl) ⟨290592, by rfl⟩ : syracuseStep 3099653 = 581185) (by norm_num)
theorem B2067461 : Blo 1377508 2067461 := bbase (se 4 (by rfl) ⟨193824, by rfl⟩ : syracuseStep 2067461 = 387649) (by norm_num)
theorem B2067485 : Blo 1377508 2067485 := bbase (se 3 (by rfl) ⟨387653, by rfl⟩ : syracuseStep 2067485 = 775307) (by norm_num)
theorem B1551397 : Blo 1377508 1551397 := bbase (se 4 (by rfl) ⟨145443, by rfl⟩ : syracuseStep 1551397 = 290887) (by norm_num)
theorem B2067509 : Blo 1377508 2067509 := bbase (se 5 (by rfl) ⟨96914, by rfl⟩ : syracuseStep 2067509 = 193829) (by norm_num)
theorem B1551433 : Blo 1377508 1551433 := bbase (se 2 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 1551433 = 1163575) (by norm_num)
theorem B3099725 : Blo 1377508 3099725 := bbase (se 3 (by rfl) ⟨581198, by rfl⟩ : syracuseStep 3099725 = 1162397) (by norm_num)
theorem B2067533 : Blo 1377508 2067533 := bbase (se 3 (by rfl) ⟨387662, by rfl⟩ : syracuseStep 2067533 = 775325) (by norm_num)
theorem B2067557 : Blo 1377508 2067557 := bbase (se 4 (by rfl) ⟨193833, by rfl⟩ : syracuseStep 2067557 = 387667) (by norm_num)
theorem B1551469 : Blo 1377508 1551469 := bbase (se 3 (by rfl) ⟨290900, by rfl⟩ : syracuseStep 1551469 = 581801) (by norm_num)
theorem B2067581 : Blo 1377508 2067581 := bbase (se 3 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 2067581 = 775343) (by norm_num)
theorem B1551505 : Blo 1377508 1551505 := bbase (se 2 (by rfl) ⟨581814, by rfl⟩ : syracuseStep 1551505 = 1163629) (by norm_num)
theorem B3099797 : Blo 1377508 3099797 := bbase (se 6 (by rfl) ⟨72651, by rfl⟩ : syracuseStep 3099797 = 145303) (by norm_num)
theorem B2067605 : Blo 1377508 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B2067629 : Blo 1377508 2067629 := bbase (se 3 (by rfl) ⟨387680, by rfl⟩ : syracuseStep 2067629 = 775361) (by norm_num)
theorem B2944181 : Blo 1377508 2944181 := bbase (se 5 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 2944181 = 276017) (by norm_num)
theorem B1551541 : Blo 1377508 1551541 := bbase (se 5 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 1551541 = 145457) (by norm_num)
theorem B2067653 : Blo 1377508 2067653 := bbase (se 4 (by rfl) ⟨193842, by rfl⟩ : syracuseStep 2067653 = 387685) (by norm_num)
theorem B2616533 : Blo 1377508 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B1551577 : Blo 1377508 1551577 := bbase (se 2 (by rfl) ⟨581841, by rfl⟩ : syracuseStep 1551577 = 1163683) (by norm_num)
theorem B3099869 : Blo 1377508 3099869 := bbase (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) (by norm_num)
theorem B2067677 : Blo 1377508 2067677 := bbase (se 3 (by rfl) ⟨387689, by rfl⟩ : syracuseStep 2067677 = 775379) (by norm_num)
theorem B2518237 : Blo 1377508 2518237 := bbase (se 3 (by rfl) ⟨472169, by rfl⟩ : syracuseStep 2518237 = 944339) (by norm_num)
theorem B2067701 : Blo 1377508 2067701 := bbase (se 5 (by rfl) ⟨96923, by rfl⟩ : syracuseStep 2067701 = 193847) (by norm_num)
theorem B1551613 : Blo 1377508 1551613 := bbase (se 3 (by rfl) ⟨290927, by rfl⟩ : syracuseStep 1551613 = 581855) (by norm_num)
theorem B2067725 : Blo 1377508 2067725 := bbase (se 3 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 2067725 = 775397) (by norm_num)
theorem B1551649 : Blo 1377508 1551649 := bbase (se 2 (by rfl) ⟨581868, by rfl⟩ : syracuseStep 1551649 = 1163737) (by norm_num)
theorem B3099941 : Blo 1377508 3099941 := bbase (se 4 (by rfl) ⟨290619, by rfl⟩ : syracuseStep 3099941 = 581239) (by norm_num)
theorem B2067749 : Blo 1377508 2067749 := bbase (se 4 (by rfl) ⟨193851, by rfl⟩ : syracuseStep 2067749 = 387703) (by norm_num)
theorem B2067773 : Blo 1377508 2067773 := bbase (se 3 (by rfl) ⟨387707, by rfl⟩ : syracuseStep 2067773 = 775415) (by norm_num)
theorem B1551685 : Blo 1377508 1551685 := bbase (se 4 (by rfl) ⟨145470, by rfl⟩ : syracuseStep 1551685 = 290941) (by norm_num)
theorem B22646101 : Blo 1377508 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B16764245 : Blo 1377508 16764245 := bbase (se 11 (by rfl) ⟨12278, by rfl⟩ : syracuseStep 16764245 = 24557) (by norm_num)
theorem B2067797 : Blo 1377508 2067797 := bbase (se 11 (by rfl) ⟨1514, by rfl⟩ : syracuseStep 2067797 = 3029) (by norm_num)
theorem B1551721 : Blo 1377508 1551721 := bbase (se 2 (by rfl) ⟨581895, by rfl⟩ : syracuseStep 1551721 = 1163791) (by norm_num)
theorem B3100013 : Blo 1377508 3100013 := bbase (se 3 (by rfl) ⟨581252, by rfl⟩ : syracuseStep 3100013 = 1162505) (by norm_num)
theorem B2067821 : Blo 1377508 2067821 := bbase (se 3 (by rfl) ⟨387716, by rfl⟩ : syracuseStep 2067821 = 775433) (by norm_num)
theorem B2067845 : Blo 1377508 2067845 := bbase (se 4 (by rfl) ⟨193860, by rfl⟩ : syracuseStep 2067845 = 387721) (by norm_num)
theorem B1551757 : Blo 1377508 1551757 := bbase (se 3 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 1551757 = 581909) (by norm_num)
theorem B2067869 : Blo 1377508 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B1551793 : Blo 1377508 1551793 := bbase (se 2 (by rfl) ⟨581922, by rfl⟩ : syracuseStep 1551793 = 1163845) (by norm_num)
theorem B3100085 : Blo 1377508 3100085 := bbase (se 5 (by rfl) ⟨145316, by rfl⟩ : syracuseStep 3100085 = 290633) (by norm_num)
theorem B2067893 : Blo 1377508 2067893 := bbase (se 5 (by rfl) ⟨96932, by rfl⟩ : syracuseStep 2067893 = 193865) (by norm_num)
theorem B2067917 : Blo 1377508 2067917 := bbase (se 3 (by rfl) ⟨387734, by rfl⟩ : syracuseStep 2067917 = 775469) (by norm_num)
theorem B1551829 : Blo 1377508 1551829 := bbase (se 7 (by rfl) ⟨18185, by rfl⟩ : syracuseStep 1551829 = 36371) (by norm_num)
theorem B2067941 : Blo 1377508 2067941 := bbase (se 4 (by rfl) ⟨193869, by rfl⟩ : syracuseStep 2067941 = 387739) (by norm_num)
theorem B1551865 : Blo 1377508 1551865 := bbase (se 2 (by rfl) ⟨581949, by rfl⟩ : syracuseStep 1551865 = 1163899) (by norm_num)
theorem B3100157 : Blo 1377508 3100157 := bbase (se 3 (by rfl) ⟨581279, by rfl⟩ : syracuseStep 3100157 = 1162559) (by norm_num)
theorem B2067965 : Blo 1377508 2067965 := bbase (se 3 (by rfl) ⟨387743, by rfl⟩ : syracuseStep 2067965 = 775487) (by norm_num)
theorem B3313165 : Blo 1377508 3313165 := bbase (se 3 (by rfl) ⟨621218, by rfl⟩ : syracuseStep 3313165 = 1242437) (by norm_num)
theorem B2067989 : Blo 1377508 2067989 := bbase (se 6 (by rfl) ⟨48468, by rfl⟩ : syracuseStep 2067989 = 96937) (by norm_num)
theorem B1551901 : Blo 1377508 1551901 := bbase (se 3 (by rfl) ⟨290981, by rfl⟩ : syracuseStep 1551901 = 581963) (by norm_num)
theorem B2068013 : Blo 1377508 2068013 := bbase (se 3 (by rfl) ⟨387752, by rfl⟩ : syracuseStep 2068013 = 775505) (by norm_num)
theorem B1551937 : Blo 1377508 1551937 := bbase (se 2 (by rfl) ⟨581976, by rfl⟩ : syracuseStep 1551937 = 1163953) (by norm_num)
theorem B3100229 : Blo 1377508 3100229 := bbase (se 4 (by rfl) ⟨290646, by rfl⟩ : syracuseStep 3100229 = 581293) (by norm_num)
theorem B2068037 : Blo 1377508 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B2068061 : Blo 1377508 2068061 := bbase (se 3 (by rfl) ⟨387761, by rfl⟩ : syracuseStep 2068061 = 775523) (by norm_num)
theorem B2207341 : Blo 1377508 2207341 := bbase (se 3 (by rfl) ⟨413876, by rfl⟩ : syracuseStep 2207341 = 827753) (by norm_num)
theorem B2068085 : Blo 1377508 2068085 := bbase (se 5 (by rfl) ⟨96941, by rfl⟩ : syracuseStep 2068085 = 193883) (by norm_num)
theorem B1961597 : Blo 1377508 1961597 := bbase (se 3 (by rfl) ⟨367799, by rfl⟩ : syracuseStep 1961597 = 735599) (by norm_num)
theorem B3100301 : Blo 1377508 3100301 := bbase (se 3 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 3100301 = 1162613) (by norm_num)
theorem B2068109 : Blo 1377508 2068109 := bbase (se 3 (by rfl) ⟨387770, by rfl⟩ : syracuseStep 2068109 = 775541) (by norm_num)
theorem B11177621 : Blo 1377508 11177621 := bbase (se 6 (by rfl) ⟨261975, by rfl⟩ : syracuseStep 11177621 = 523951) (by norm_num)
theorem B2068133 : Blo 1377508 2068133 := bbase (se 4 (by rfl) ⟨193887, by rfl⟩ : syracuseStep 2068133 = 387775) (by norm_num)
theorem B6983333 : Blo 1377508 6983333 := bbase (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) (by norm_num)
theorem B8171189 : Blo 1377508 8171189 := bbase (se 5 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 8171189 = 766049) (by norm_num)
theorem B2068157 : Blo 1377508 2068157 := bbase (se 3 (by rfl) ⟨387779, by rfl⟩ : syracuseStep 2068157 = 775559) (by norm_num)
theorem B3100373 : Blo 1377508 3100373 := bbase (se 7 (by rfl) ⟨36332, by rfl⟩ : syracuseStep 3100373 = 72665) (by norm_num)
theorem B2068181 : Blo 1377508 2068181 := bbase (se 7 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 2068181 = 48473) (by norm_num)
theorem B2068205 : Blo 1377508 2068205 := bbase (se 3 (by rfl) ⟨387788, by rfl⟩ : syracuseStep 2068205 = 775577) (by norm_num)
theorem B2068229 : Blo 1377508 2068229 := bbase (se 4 (by rfl) ⟨193896, by rfl⟩ : syracuseStep 2068229 = 387793) (by norm_num)
theorem B3100445 : Blo 1377508 3100445 := bbase (se 3 (by rfl) ⟨581333, by rfl⟩ : syracuseStep 3100445 = 1162667) (by norm_num)
theorem B2068253 : Blo 1377508 2068253 := bbase (se 3 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 2068253 = 775595) (by norm_num)
theorem B2068277 : Blo 1377508 2068277 := bbase (se 5 (by rfl) ⟨96950, by rfl⟩ : syracuseStep 2068277 = 193901) (by norm_num)
theorem B2068301 : Blo 1377508 2068301 := bbase (se 3 (by rfl) ⟨387806, by rfl⟩ : syracuseStep 2068301 = 775613) (by norm_num)
theorem B3100517 : Blo 1377508 3100517 := bbase (se 4 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 3100517 = 581347) (by norm_num)
theorem B2068325 : Blo 1377508 2068325 := bbase (se 4 (by rfl) ⟨193905, by rfl⟩ : syracuseStep 2068325 = 387811) (by norm_num)
theorem B5230453 : Blo 1377508 5230453 := bbase (se 5 (by rfl) ⟨245177, by rfl⟩ : syracuseStep 5230453 = 490355) (by norm_num)
theorem B2068349 : Blo 1377508 2068349 := bbase (se 3 (by rfl) ⟨387815, by rfl⟩ : syracuseStep 2068349 = 775631) (by norm_num)
theorem B2068373 : Blo 1377508 2068373 := bbase (se 6 (by rfl) ⟨48477, by rfl⟩ : syracuseStep 2068373 = 96955) (by norm_num)
theorem B3100589 : Blo 1377508 3100589 := bbase (se 3 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 3100589 = 1162721) (by norm_num)
theorem B2068397 : Blo 1377508 2068397 := bbase (se 3 (by rfl) ⟨387824, by rfl⟩ : syracuseStep 2068397 = 775649) (by norm_num)
theorem B11177909 : Blo 1377508 11177909 := bbase (se 5 (by rfl) ⟨523964, by rfl⟩ : syracuseStep 11177909 = 1047929) (by norm_num)
theorem B3927989 : Blo 1377508 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B2617285 : Blo 1377508 2617285 := bbase (se 4 (by rfl) ⟨245370, by rfl⟩ : syracuseStep 2617285 = 490741) (by norm_num)
theorem B2068421 : Blo 1377508 2068421 := bbase (se 4 (by rfl) ⟨193914, by rfl⟩ : syracuseStep 2068421 = 387829) (by norm_num)
theorem B2068445 : Blo 1377508 2068445 := bbase (se 3 (by rfl) ⟨387833, by rfl⟩ : syracuseStep 2068445 = 775667) (by norm_num)
theorem B3100661 : Blo 1377508 3100661 := bbase (se 5 (by rfl) ⟨145343, by rfl⟩ : syracuseStep 3100661 = 290687) (by norm_num)
theorem B2068469 : Blo 1377508 2068469 := bbase (se 5 (by rfl) ⟨96959, by rfl⟩ : syracuseStep 2068469 = 193919) (by norm_num)
theorem B2068493 : Blo 1377508 2068493 := bbase (se 3 (by rfl) ⟨387842, by rfl⟩ : syracuseStep 2068493 = 775685) (by norm_num)
theorem B3313685 : Blo 1377508 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B2068517 : Blo 1377508 2068517 := bbase (se 4 (by rfl) ⟨193923, by rfl⟩ : syracuseStep 2068517 = 387847) (by norm_num)
theorem B3100733 : Blo 1377508 3100733 := bbase (se 3 (by rfl) ⟨581387, by rfl⟩ : syracuseStep 3100733 = 1162775) (by norm_num)
theorem B2068541 : Blo 1377508 2068541 := bbase (se 3 (by rfl) ⟨387851, by rfl⟩ : syracuseStep 2068541 = 775703) (by norm_num)
theorem B6975557 : Blo 1377508 6975557 := bbase (se 4 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 6975557 = 1307917) (by norm_num)
theorem B5886037 : Blo 1377508 5886037 := bbase (se 8 (by rfl) ⟨34488, by rfl⟩ : syracuseStep 5886037 = 68977) (by norm_num)
theorem B2617429 : Blo 1377508 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B2068565 : Blo 1377508 2068565 := bbase (se 8 (by rfl) ⟨12120, by rfl⟩ : syracuseStep 2068565 = 24241) (by norm_num)
theorem B2068589 : Blo 1377508 2068589 := bbase (se 3 (by rfl) ⟨387860, by rfl⟩ : syracuseStep 2068589 = 775721) (by norm_num)
theorem B3313781 : Blo 1377508 3313781 := bbase (se 5 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 3313781 = 310667) (by norm_num)
theorem B1724537 : Blo 1377508 1724537 := bbase (se 2 (by rfl) ⟨646701, by rfl⟩ : syracuseStep 1724537 = 1293403) (by norm_num)
theorem B3100805 : Blo 1377508 3100805 := bbase (se 4 (by rfl) ⟨290700, by rfl⟩ : syracuseStep 3100805 = 581401) (by norm_num)
theorem B2068613 : Blo 1377508 2068613 := bbase (se 4 (by rfl) ⟨193932, by rfl⟩ : syracuseStep 2068613 = 387865) (by norm_num)
theorem B2207893 : Blo 1377508 2207893 := bbase (se 6 (by rfl) ⟨51747, by rfl⟩ : syracuseStep 2207893 = 103495) (by norm_num)
theorem B2068637 : Blo 1377508 2068637 := bbase (se 3 (by rfl) ⟨387869, by rfl⟩ : syracuseStep 2068637 = 775739) (by norm_num)
theorem B5230757 : Blo 1377508 5230757 := bbase (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) (by norm_num)
theorem B1962149 : Blo 1377508 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B2068661 : Blo 1377508 2068661 := bbase (se 5 (by rfl) ⟨96968, by rfl⟩ : syracuseStep 2068661 = 193937) (by norm_num)
theorem B3100877 : Blo 1377508 3100877 := bbase (se 3 (by rfl) ⟨581414, by rfl⟩ : syracuseStep 3100877 = 1162829) (by norm_num)
theorem B2068685 : Blo 1377508 2068685 := bbase (se 3 (by rfl) ⟨387878, by rfl⟩ : syracuseStep 2068685 = 775757) (by norm_num)
theorem B2068709 : Blo 1377508 2068709 := bbase (se 4 (by rfl) ⟨193941, by rfl⟩ : syracuseStep 2068709 = 387883) (by norm_num)
theorem B3027173 : Blo 1377508 3027173 := bbase (se 4 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 3027173 = 567595) (by norm_num)
theorem B2617589 : Blo 1377508 2617589 := bbase (se 5 (by rfl) ⟨122699, by rfl⟩ : syracuseStep 2617589 = 245399) (by norm_num)
theorem B2068733 : Blo 1377508 2068733 := bbase (se 3 (by rfl) ⟨387887, by rfl⟩ : syracuseStep 2068733 = 775775) (by norm_num)
theorem B1913101 : Blo 1377508 1913101 := bbase (se 3 (by rfl) ⟨358706, by rfl⟩ : syracuseStep 1913101 = 717413) (by norm_num)
theorem B4649237 : Blo 1377508 4649237 := bbase (se 6 (by rfl) ⟨108966, by rfl⟩ : syracuseStep 4649237 = 217933) (by norm_num)
theorem B3100949 : Blo 1377508 3100949 := bbase (se 6 (by rfl) ⟨72678, by rfl⟩ : syracuseStep 3100949 = 145357) (by norm_num)
theorem B2068757 : Blo 1377508 2068757 := bbase (se 6 (by rfl) ⟨48486, by rfl⟩ : syracuseStep 2068757 = 96973) (by norm_num)
theorem B2068781 : Blo 1377508 2068781 := bbase (se 3 (by rfl) ⟨387896, by rfl⟩ : syracuseStep 2068781 = 775793) (by norm_num)
theorem B4714805 : Blo 1377508 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B2068805 : Blo 1377508 2068805 := bbase (se 4 (by rfl) ⟨193950, by rfl⟩ : syracuseStep 2068805 = 387901) (by norm_num)
theorem B3101021 : Blo 1377508 3101021 := bbase (se 3 (by rfl) ⟨581441, by rfl⟩ : syracuseStep 3101021 = 1162883) (by norm_num)
theorem B2068829 : Blo 1377508 2068829 := bbase (se 3 (by rfl) ⟨387905, by rfl⟩ : syracuseStep 2068829 = 775811) (by norm_num)
theorem B2068853 : Blo 1377508 2068853 := bbase (se 5 (by rfl) ⟨96977, by rfl⟩ : syracuseStep 2068853 = 193955) (by norm_num)
theorem B2617733 : Blo 1377508 2617733 := bbase (se 4 (by rfl) ⟨245412, by rfl⟩ : syracuseStep 2617733 = 490825) (by norm_num)
theorem B2068877 : Blo 1377508 2068877 := bbase (se 3 (by rfl) ⟨387914, by rfl⟩ : syracuseStep 2068877 = 775829) (by norm_num)
theorem B2208149 : Blo 1377508 2208149 := bbase (se 6 (by rfl) ⟨51753, by rfl⟩ : syracuseStep 2208149 = 103507) (by norm_num)
theorem B13250965 : Blo 1377508 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B3101093 : Blo 1377508 3101093 := bbase (se 4 (by rfl) ⟨290727, by rfl⟩ : syracuseStep 3101093 = 581455) (by norm_num)
theorem B2068901 : Blo 1377508 2068901 := bbase (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) (by norm_num)
theorem B2068925 : Blo 1377508 2068925 := bbase (se 3 (by rfl) ⟨387923, by rfl⟩ : syracuseStep 2068925 = 775847) (by norm_num)
theorem B2068949 : Blo 1377508 2068949 := bbase (se 7 (by rfl) ⟨24245, by rfl⟩ : syracuseStep 2068949 = 48491) (by norm_num)
theorem B3101165 : Blo 1377508 3101165 := bbase (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) (by norm_num)
theorem B2068973 : Blo 1377508 2068973 := bbase (se 3 (by rfl) ⟨387932, by rfl⟩ : syracuseStep 2068973 = 775865) (by norm_num)
theorem B2068997 : Blo 1377508 2068997 := bbase (se 4 (by rfl) ⟨193968, by rfl⟩ : syracuseStep 2068997 = 387937) (by norm_num)
theorem B2069021 : Blo 1377508 2069021 := bbase (se 3 (by rfl) ⟨387941, by rfl⟩ : syracuseStep 2069021 = 775883) (by norm_num)
theorem B3101237 : Blo 1377508 3101237 := bbase (se 5 (by rfl) ⟨145370, by rfl⟩ : syracuseStep 3101237 = 290741) (by norm_num)
theorem B2069045 : Blo 1377508 2069045 := bbase (se 5 (by rfl) ⟨96986, by rfl⟩ : syracuseStep 2069045 = 193973) (by norm_num)
theorem B2069069 : Blo 1377508 2069069 := bbase (se 3 (by rfl) ⟨387950, by rfl⟩ : syracuseStep 2069069 = 775901) (by norm_num)
theorem B2069093 : Blo 1377508 2069093 := bbase (se 4 (by rfl) ⟨193977, by rfl⟩ : syracuseStep 2069093 = 387955) (by norm_num)
theorem B3101309 : Blo 1377508 3101309 := bbase (se 3 (by rfl) ⟨581495, by rfl⟩ : syracuseStep 3101309 = 1162991) (by norm_num)
theorem B2069117 : Blo 1377508 2069117 := bbase (se 3 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 2069117 = 775919) (by norm_num)
theorem B2069141 : Blo 1377508 2069141 := bbase (se 6 (by rfl) ⟨48495, by rfl⟩ : syracuseStep 2069141 = 96991) (by norm_num)
theorem B2618021 : Blo 1377508 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B2069165 : Blo 1377508 2069165 := bbase (se 3 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 2069165 = 775937) (by norm_num)
theorem B4649669 : Blo 1377508 4649669 := bbase (se 4 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 4649669 = 871813) (by norm_num)
theorem B3101381 : Blo 1377508 3101381 := bbase (se 4 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 3101381 = 581509) (by norm_num)
theorem B2069189 : Blo 1377508 2069189 := bbase (se 4 (by rfl) ⟨193986, by rfl⟩ : syracuseStep 2069189 = 387973) (by norm_num)
theorem B2069213 : Blo 1377508 2069213 := bbase (se 3 (by rfl) ⟨387977, by rfl⟩ : syracuseStep 2069213 = 775955) (by norm_num)
theorem B2069237 : Blo 1377508 2069237 := bbase (se 5 (by rfl) ⟨96995, by rfl⟩ : syracuseStep 2069237 = 193991) (by norm_num)
theorem B3101453 : Blo 1377508 3101453 := bbase (se 3 (by rfl) ⟨581522, by rfl⟩ : syracuseStep 3101453 = 1163045) (by norm_num)
theorem B2069261 : Blo 1377508 2069261 := bbase (se 3 (by rfl) ⟨387986, by rfl⟩ : syracuseStep 2069261 = 775973) (by norm_num)
theorem B2945821 : Blo 1377508 2945821 := bbase (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) (by norm_num)
theorem B3355445 : Blo 1377508 3355445 := bbase (se 5 (by rfl) ⟨157286, by rfl⟩ : syracuseStep 3355445 = 314573) (by norm_num)
theorem B2618173 : Blo 1377508 2618173 := bbase (se 3 (by rfl) ⟨490907, by rfl⟩ : syracuseStep 2618173 = 981815) (by norm_num)
theorem B3101525 : Blo 1377508 3101525 := bbase (se 9 (by rfl) ⟨9086, by rfl⟩ : syracuseStep 3101525 = 18173) (by norm_num)
theorem B8835925 : Blo 1377508 8835925 := bbase (se 9 (by rfl) ⟨25886, by rfl⟩ : syracuseStep 8835925 = 51773) (by norm_num)
theorem B6714245 : Blo 1377508 6714245 := bbase (se 4 (by rfl) ⟨629460, by rfl⟩ : syracuseStep 6714245 = 1258921) (by norm_num)
theorem B1962901 : Blo 1377508 1962901 := bbase (se 6 (by rfl) ⟨46005, by rfl⟩ : syracuseStep 1962901 = 92011) (by norm_num)
theorem B7852949 : Blo 1377508 7852949 := bbase (se 6 (by rfl) ⟨184053, by rfl⟩ : syracuseStep 7852949 = 368107) (by norm_num)
theorem B3101597 : Blo 1377508 3101597 := bbase (se 3 (by rfl) ⟨581549, by rfl⟩ : syracuseStep 3101597 = 1163099) (by norm_num)
theorem B3101669 : Blo 1377508 3101669 := bbase (se 4 (by rfl) ⟨290781, by rfl⟩ : syracuseStep 3101669 = 581563) (by norm_num)
theorem B3142685 : Blo 1377508 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B3101741 : Blo 1377508 3101741 := bbase (se 3 (by rfl) ⟨581576, by rfl⟩ : syracuseStep 3101741 = 1163153) (by norm_num)
theorem B2208853 : Blo 1377508 2208853 := bbase (se 8 (by rfl) ⟨12942, by rfl⟩ : syracuseStep 2208853 = 25885) (by norm_num)
theorem B2618477 : Blo 1377508 2618477 := bbase (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) (by norm_num)
theorem B4650101 : Blo 1377508 4650101 := bbase (se 5 (by rfl) ⟨217973, by rfl⟩ : syracuseStep 4650101 = 435947) (by norm_num)
theorem B3101813 : Blo 1377508 3101813 := bbase (se 5 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 3101813 = 290795) (by norm_num)
theorem B3101885 : Blo 1377508 3101885 := bbase (se 3 (by rfl) ⟨581603, by rfl⟩ : syracuseStep 3101885 = 1163207) (by norm_num)
theorem B11777237 : Blo 1377508 11777237 := bbase (se 7 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 11777237 = 276029) (by norm_num)
theorem B1397993 : Blo 1377508 1397993 := bbase (se 2 (by rfl) ⟨524247, by rfl⟩ : syracuseStep 1397993 = 1048495) (by norm_num)
theorem B3101957 : Blo 1377508 3101957 := bbase (se 4 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 3101957 = 581617) (by norm_num)
theorem B3486989 : Blo 1377508 3486989 := bbase (se 3 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 3486989 = 1307621) (by norm_num)
theorem B1471817 : Blo 1377508 1471817 := bbase (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) (by norm_num)
theorem B3102029 : Blo 1377508 3102029 := bbase (se 3 (by rfl) ⟨581630, by rfl⟩ : syracuseStep 3102029 = 1163261) (by norm_num)
theorem B6976853 : Blo 1377508 6976853 := bbase (se 13 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 6976853 = 2555) (by norm_num)
theorem B28661141 : Blo 1377508 28661141 := bbase (se 6 (by rfl) ⟨671745, by rfl⟩ : syracuseStep 28661141 = 1343491) (by norm_num)
theorem B3102101 : Blo 1377508 3102101 := bbase (se 6 (by rfl) ⟨72705, by rfl⟩ : syracuseStep 3102101 = 145411) (by norm_num)
theorem B3102173 : Blo 1377508 3102173 := bbase (se 3 (by rfl) ⟨581657, by rfl⟩ : syracuseStep 3102173 = 1163315) (by norm_num)
theorem B2209277 : Blo 1377508 2209277 := bbase (se 3 (by rfl) ⟨414239, by rfl⟩ : syracuseStep 2209277 = 828479) (by norm_num)
theorem B4650533 : Blo 1377508 4650533 := bbase (se 4 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 4650533 = 871975) (by norm_num)
theorem B5887525 : Blo 1377508 5887525 := bbase (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) (by norm_num)
theorem B3102245 : Blo 1377508 3102245 := bbase (se 4 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 3102245 = 581671) (by norm_num)
theorem B5887541 : Blo 1377508 5887541 := bbase (se 5 (by rfl) ⟨275978, by rfl⟩ : syracuseStep 5887541 = 551957) (by norm_num)
theorem B9942581 : Blo 1377508 9942581 := bbase (se 5 (by rfl) ⟨466058, by rfl⟩ : syracuseStep 9942581 = 932117) (by norm_num)
theorem B3487333 : Blo 1377508 3487333 := bbase (se 4 (by rfl) ⟨326937, by rfl⟩ : syracuseStep 3487333 = 653875) (by norm_num)
theorem B3102317 : Blo 1377508 3102317 := bbase (se 3 (by rfl) ⟨581684, by rfl⟩ : syracuseStep 3102317 = 1163369) (by norm_num)
theorem B1963693 : Blo 1377508 1963693 := bbase (se 3 (by rfl) ⟨368192, by rfl⟩ : syracuseStep 1963693 = 736385) (by norm_num)
theorem B3102389 : Blo 1377508 3102389 := bbase (se 5 (by rfl) ⟨145424, by rfl⟩ : syracuseStep 3102389 = 290849) (by norm_num)
theorem B3487445 : Blo 1377508 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B3102461 : Blo 1377508 3102461 := bbase (se 3 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 3102461 = 1163423) (by norm_num)
theorem B1472261 : Blo 1377508 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B2209565 : Blo 1377508 2209565 := bbase (se 3 (by rfl) ⟨414293, by rfl⟩ : syracuseStep 2209565 = 828587) (by norm_num)
theorem B6625061 : Blo 1377508 6625061 := bbase (se 4 (by rfl) ⟨621099, by rfl⟩ : syracuseStep 6625061 = 1242199) (by norm_num)
theorem B3102533 : Blo 1377508 3102533 := bbase (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) (by norm_num)
theorem B3102605 : Blo 1377508 3102605 := bbase (se 3 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 3102605 = 1163477) (by norm_num)
theorem B3487637 : Blo 1377508 3487637 := bbase (se 6 (by rfl) ⟨81741, by rfl⟩ : syracuseStep 3487637 = 163483) (by norm_num)
theorem B3880885 : Blo 1377508 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B4650965 : Blo 1377508 4650965 := bbase (se 7 (by rfl) ⟨54503, by rfl⟩ : syracuseStep 4650965 = 109007) (by norm_num)
theorem B3102677 : Blo 1377508 3102677 := bbase (se 7 (by rfl) ⟨36359, by rfl⟩ : syracuseStep 3102677 = 72719) (by norm_num)
theorem B1472509 : Blo 1377508 1472509 := bbase (se 3 (by rfl) ⟨276095, by rfl⟩ : syracuseStep 1472509 = 552191) (by norm_num)
theorem B1964029 : Blo 1377508 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B3102749 : Blo 1377508 3102749 := bbase (se 3 (by rfl) ⟨581765, by rfl⟩ : syracuseStep 3102749 = 1163531) (by norm_num)
theorem B3725365 : Blo 1377508 3725365 := bbase (se 5 (by rfl) ⟨174626, by rfl⟩ : syracuseStep 3725365 = 349253) (by norm_num)
theorem B2357309 : Blo 1377508 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B3102821 : Blo 1377508 3102821 := bbase (se 4 (by rfl) ⟨290889, by rfl⟩ : syracuseStep 3102821 = 581779) (by norm_num)
theorem B2324605 : Blo 1377508 2324605 := bbase (se 3 (by rfl) ⟨435863, by rfl⟩ : syracuseStep 2324605 = 871727) (by norm_num)
theorem B3102893 : Blo 1377508 3102893 := bbase (se 3 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 3102893 = 1163585) (by norm_num)
theorem B2324693 : Blo 1377508 2324693 := bbase (se 7 (by rfl) ⟨27242, by rfl⟩ : syracuseStep 2324693 = 54485) (by norm_num)
theorem B5232869 : Blo 1377508 5232869 := bbase (se 4 (by rfl) ⟨490581, by rfl⟩ : syracuseStep 5232869 = 981163) (by norm_num)
theorem B3487981 : Blo 1377508 3487981 := bbase (se 3 (by rfl) ⟨653996, by rfl⟩ : syracuseStep 3487981 = 1307993) (by norm_num)
theorem B3102965 : Blo 1377508 3102965 := bbase (se 5 (by rfl) ⟨145451, by rfl⟩ : syracuseStep 3102965 = 290903) (by norm_num)
theorem B1554733 : Blo 1377508 1554733 := bbase (se 3 (by rfl) ⟨291512, by rfl⟩ : syracuseStep 1554733 = 583025) (by norm_num)
theorem B3103037 : Blo 1377508 3103037 := bbase (se 3 (by rfl) ⟨581819, by rfl⟩ : syracuseStep 3103037 = 1163639) (by norm_num)
theorem B2324821 : Blo 1377508 2324821 := bbase (se 10 (by rfl) ⟨3405, by rfl⟩ : syracuseStep 2324821 = 6811) (by norm_num)
theorem B3488093 : Blo 1377508 3488093 := bbase (se 3 (by rfl) ⟨654017, by rfl⟩ : syracuseStep 3488093 = 1308035) (by norm_num)
theorem B4651397 : Blo 1377508 4651397 := bbase (se 4 (by rfl) ⟨436068, by rfl⟩ : syracuseStep 4651397 = 872137) (by norm_num)
theorem B3103109 : Blo 1377508 3103109 := bbase (se 4 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 3103109 = 581833) (by norm_num)
theorem B2324909 : Blo 1377508 2324909 := bbase (se 3 (by rfl) ⟨435920, by rfl⟩ : syracuseStep 2324909 = 871841) (by norm_num)
theorem B1472941 : Blo 1377508 1472941 := bbase (se 3 (by rfl) ⟨276176, by rfl⟩ : syracuseStep 1472941 = 552353) (by norm_num)
theorem B3103181 : Blo 1377508 3103181 := bbase (se 3 (by rfl) ⟨581846, by rfl⟩ : syracuseStep 3103181 = 1163693) (by norm_num)
theorem B1473013 : Blo 1377508 1473013 := bbase (se 5 (by rfl) ⟨69047, by rfl⟩ : syracuseStep 1473013 = 138095) (by norm_num)
theorem B5233157 : Blo 1377508 5233157 := bbase (se 4 (by rfl) ⟨490608, by rfl⟩ : syracuseStep 5233157 = 981217) (by norm_num)
theorem B3103253 : Blo 1377508 3103253 := bbase (se 6 (by rfl) ⟨72732, by rfl⟩ : syracuseStep 3103253 = 145465) (by norm_num)
theorem B3488285 : Blo 1377508 3488285 := bbase (se 3 (by rfl) ⟨654053, by rfl⟩ : syracuseStep 3488285 = 1308107) (by norm_num)
theorem B2325037 : Blo 1377508 2325037 := bbase (se 3 (by rfl) ⟨435944, by rfl⟩ : syracuseStep 2325037 = 871889) (by norm_num)
theorem B3103325 : Blo 1377508 3103325 := bbase (se 3 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 3103325 = 1163747) (by norm_num)
theorem B6978149 : Blo 1377508 6978149 := bbase (se 4 (by rfl) ⟨654201, by rfl⟩ : syracuseStep 6978149 = 1308403) (by norm_num)
theorem B2325125 : Blo 1377508 2325125 := bbase (se 4 (by rfl) ⟨217980, by rfl⟩ : syracuseStep 2325125 = 435961) (by norm_num)
theorem B3103397 : Blo 1377508 3103397 := bbase (se 4 (by rfl) ⟨290943, by rfl⟩ : syracuseStep 3103397 = 581887) (by norm_num)
theorem B1743545 : Blo 1377508 1743545 := bbase (se 2 (by rfl) ⟨653829, by rfl⟩ : syracuseStep 1743545 = 1307659) (by norm_num)
theorem B3103469 : Blo 1377508 3103469 := bbase (se 3 (by rfl) ⟨581900, by rfl⟩ : syracuseStep 3103469 = 1163801) (by norm_num)
theorem B1743601 : Blo 1377508 1743601 := bbase (se 2 (by rfl) ⟨653850, by rfl⟩ : syracuseStep 1743601 = 1307701) (by norm_num)
theorem B3144437 : Blo 1377508 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B2325253 : Blo 1377508 2325253 := bbase (se 4 (by rfl) ⟨217992, by rfl⟩ : syracuseStep 2325253 = 435985) (by norm_num)
theorem B4651829 : Blo 1377508 4651829 := bbase (se 5 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 4651829 = 436109) (by norm_num)
theorem B3103541 : Blo 1377508 3103541 := bbase (se 5 (by rfl) ⟨145478, by rfl⟩ : syracuseStep 3103541 = 290957) (by norm_num)
theorem B1743697 : Blo 1377508 1743697 := bbase (se 2 (by rfl) ⟨653886, by rfl⟩ : syracuseStep 1743697 = 1307773) (by norm_num)
theorem B2325341 : Blo 1377508 2325341 := bbase (se 3 (by rfl) ⟨436001, by rfl⟩ : syracuseStep 2325341 = 872003) (by norm_num)
theorem B3144557 : Blo 1377508 3144557 := bbase (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) (by norm_num)
theorem B3488629 : Blo 1377508 3488629 := bbase (se 5 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 3488629 = 327059) (by norm_num)
theorem B3103613 : Blo 1377508 3103613 := bbase (se 3 (by rfl) ⟨581927, by rfl⟩ : syracuseStep 3103613 = 1163855) (by norm_num)
theorem B3103685 : Blo 1377508 3103685 := bbase (se 4 (by rfl) ⟨290970, by rfl⟩ : syracuseStep 3103685 = 581941) (by norm_num)
theorem B2325469 : Blo 1377508 2325469 := bbase (se 3 (by rfl) ⟨436025, by rfl⟩ : syracuseStep 2325469 = 872051) (by norm_num)
theorem B3488741 : Blo 1377508 3488741 := bbase (se 4 (by rfl) ⟨327069, by rfl⟩ : syracuseStep 3488741 = 654139) (by norm_num)
theorem B1743869 : Blo 1377508 1743869 := bbase (se 3 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 1743869 = 653951) (by norm_num)
theorem B3103757 : Blo 1377508 3103757 := bbase (se 3 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 3103757 = 1163909) (by norm_num)
theorem B1743925 : Blo 1377508 1743925 := bbase (se 5 (by rfl) ⟨81746, by rfl⟩ : syracuseStep 1743925 = 163493) (by norm_num)
theorem B2325557 : Blo 1377508 2325557 := bbase (se 5 (by rfl) ⟨109010, by rfl⟩ : syracuseStep 2325557 = 218021) (by norm_num)
theorem B7855157 : Blo 1377508 7855157 := bbase (se 5 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 7855157 = 736421) (by norm_num)
theorem B1678421 : Blo 1377508 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B3103829 : Blo 1377508 3103829 := bbase (se 8 (by rfl) ⟨18186, by rfl⟩ : syracuseStep 3103829 = 36373) (by norm_num)
theorem B6626405 : Blo 1377508 6626405 := bbase (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) (by norm_num)
theorem B2653309 : Blo 1377508 2653309 := bbase (se 3 (by rfl) ⟨497495, by rfl⟩ : syracuseStep 2653309 = 994991) (by norm_num)
theorem B1744021 : Blo 1377508 1744021 := bbase (se 6 (by rfl) ⟨40875, by rfl⟩ : syracuseStep 1744021 = 81751) (by norm_num)
theorem B3488933 : Blo 1377508 3488933 := bbase (se 4 (by rfl) ⟨327087, by rfl⟩ : syracuseStep 3488933 = 654175) (by norm_num)
theorem B2325685 : Blo 1377508 2325685 := bbase (se 5 (by rfl) ⟨109016, by rfl⟩ : syracuseStep 2325685 = 218033) (by norm_num)
theorem B13253813 : Blo 1377508 13253813 := bbase (se 5 (by rfl) ⟨621272, by rfl⟩ : syracuseStep 13253813 = 1242545) (by norm_num)
theorem B4652261 : Blo 1377508 4652261 := bbase (se 4 (by rfl) ⟨436149, by rfl⟩ : syracuseStep 4652261 = 872299) (by norm_num)
theorem B2325773 : Blo 1377508 2325773 := bbase (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) (by norm_num)
theorem B1744193 : Blo 1377508 1744193 := bbase (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) (by norm_num)
theorem B4193653 : Blo 1377508 4193653 := bbase (se 5 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 4193653 = 393155) (by norm_num)
theorem B1744249 : Blo 1377508 1744249 := bbase (se 2 (by rfl) ⟨654093, by rfl⟩ : syracuseStep 1744249 = 1308187) (by norm_num)
theorem B2325901 : Blo 1377508 2325901 := bbase (se 3 (by rfl) ⟨436106, by rfl⟩ : syracuseStep 2325901 = 872213) (by norm_num)
theorem B1572305 : Blo 1377508 1572305 := bbase (se 2 (by rfl) ⟨589614, by rfl⟩ : syracuseStep 1572305 = 1179229) (by norm_num)
theorem B1744345 : Blo 1377508 1744345 := bbase (se 2 (by rfl) ⟨654129, by rfl⟩ : syracuseStep 1744345 = 1308259) (by norm_num)
theorem B2325989 : Blo 1377508 2325989 := bbase (se 4 (by rfl) ⟨218061, by rfl⟩ : syracuseStep 2325989 = 436123) (by norm_num)
theorem B1990117 : Blo 1377508 1990117 := bbase (se 4 (by rfl) ⟨186573, by rfl⟩ : syracuseStep 1990117 = 373147) (by norm_num)
theorem B3489277 : Blo 1377508 3489277 := bbase (se 3 (by rfl) ⟨654239, by rfl⟩ : syracuseStep 3489277 = 1308479) (by norm_num)
theorem B7077461 : Blo 1377508 7077461 := bbase (se 8 (by rfl) ⟨41469, by rfl⟩ : syracuseStep 7077461 = 82939) (by norm_num)
theorem B2326117 : Blo 1377508 2326117 := bbase (se 4 (by rfl) ⟨218073, by rfl⟩ : syracuseStep 2326117 = 436147) (by norm_num)
theorem B3489389 : Blo 1377508 3489389 := bbase (se 3 (by rfl) ⟨654260, by rfl⟩ : syracuseStep 3489389 = 1308521) (by norm_num)
theorem B4415093 : Blo 1377508 4415093 := bbase (se 5 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 4415093 = 413915) (by norm_num)
theorem B3726965 : Blo 1377508 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B1744517 : Blo 1377508 1744517 := bbase (se 4 (by rfl) ⟨163548, by rfl⟩ : syracuseStep 1744517 = 327097) (by norm_num)
theorem B4652693 : Blo 1377508 4652693 := bbase (se 6 (by rfl) ⟨109047, by rfl⟩ : syracuseStep 4652693 = 218095) (by norm_num)
theorem B5234341 : Blo 1377508 5234341 := bbase (se 4 (by rfl) ⟨490719, by rfl⟩ : syracuseStep 5234341 = 981439) (by norm_num)
theorem B2793133 : Blo 1377508 2793133 := bbase (se 3 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 2793133 = 1047425) (by norm_num)
theorem B1744573 : Blo 1377508 1744573 := bbase (se 3 (by rfl) ⟨327107, by rfl⟩ : syracuseStep 1744573 = 654215) (by norm_num)
theorem B2326205 : Blo 1377508 2326205 := bbase (se 3 (by rfl) ⟨436163, by rfl⟩ : syracuseStep 2326205 = 872327) (by norm_num)
theorem B5889797 : Blo 1377508 5889797 := bbase (se 4 (by rfl) ⟨552168, by rfl⟩ : syracuseStep 5889797 = 1104337) (by norm_num)
theorem B1744669 : Blo 1377508 1744669 := bbase (se 3 (by rfl) ⟨327125, by rfl⟩ : syracuseStep 1744669 = 654251) (by norm_num)
theorem B3489581 : Blo 1377508 3489581 := bbase (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) (by norm_num)
theorem B2326333 : Blo 1377508 2326333 := bbase (se 3 (by rfl) ⟨436187, by rfl⟩ : syracuseStep 2326333 = 872375) (by norm_num)
theorem B3923797 : Blo 1377508 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B1572697 : Blo 1377508 1572697 := bbase (se 2 (by rfl) ⟨589761, by rfl⟩ : syracuseStep 1572697 = 1179523) (by norm_num)
theorem B6979445 : Blo 1377508 6979445 := bbase (se 5 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 6979445 = 654323) (by norm_num)
theorem B2326421 : Blo 1377508 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B1744841 : Blo 1377508 1744841 := bbase (se 2 (by rfl) ⟨654315, by rfl⟩ : syracuseStep 1744841 = 1308631) (by norm_num)
theorem B5234645 : Blo 1377508 5234645 := bbase (se 7 (by rfl) ⟨61343, by rfl⟩ : syracuseStep 5234645 = 122687) (by norm_num)
theorem B3923957 : Blo 1377508 3923957 := bbase (se 5 (by rfl) ⟨183935, by rfl⟩ : syracuseStep 3923957 = 367871) (by norm_num)
theorem B2326529 : Blo 1377508 2326529 := bstep (se 2 (by rfl) ⟨872448, by rfl⟩ : syracuseStep 2326529 = 1744897) B1744897
theorem B15704117 : Blo 1377508 15704117 := bstep (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) B1472261
theorem B8380493 : Blo 1377508 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B7848049 : Blo 1377508 7848049 := bstep (se 2 (by rfl) ⟨2943018, by rfl⟩ : syracuseStep 7848049 = 5886037) B5886037
theorem B3489905 : Blo 1377508 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B2326657 : Blo 1377508 2326657 := bstep (se 2 (by rfl) ⟨872496, by rfl⟩ : syracuseStep 2326657 = 1744993) B1744993
theorem B7454861 : Blo 1377508 7454861 := bstep (se 3 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 7454861 = 2795573) B2795573
theorem B2326691 : Blo 1377508 2326691 := bstep (se 1 (by rfl) ⟨1745018, by rfl⟩ : syracuseStep 2326691 = 3490037) B3490037
theorem B1745059 : Blo 1377508 1745059 := bstep (se 1 (by rfl) ⟨1308794, by rfl⟩ : syracuseStep 1745059 = 2617589) B2617589
theorem B4653233 : Blo 1377508 4653233 := bstep (se 2 (by rfl) ⟨1744962, by rfl⟩ : syracuseStep 4653233 = 3489925) B3489925
theorem B8388785 : Blo 1377508 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B3309763 : Blo 1377508 3309763 := bstep (se 1 (by rfl) ⟨2482322, by rfl⟩ : syracuseStep 3309763 = 4964645) B4964645
theorem B2834659 : Blo 1377508 2834659 := bstep (se 1 (by rfl) ⟨2125994, by rfl⟩ : syracuseStep 2834659 = 4251989) B4251989
theorem B1745155 : Blo 1377508 1745155 := bstep (se 1 (by rfl) ⟨1308866, by rfl⟩ : syracuseStep 1745155 = 2617733) B2617733
theorem B17670413 : Blo 1377508 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B2326819 : Blo 1377508 2326819 := bstep (se 1 (by rfl) ⟨1745114, by rfl⟩ : syracuseStep 2326819 = 3490229) B3490229
theorem B2482481 : Blo 1377508 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B7954757 : Blo 1377508 7954757 := bstep (se 4 (by rfl) ⟨745758, by rfl⟩ : syracuseStep 7954757 = 1491517) B1491517
theorem B7455053 : Blo 1377508 7455053 := bstep (se 3 (by rfl) ⟨1397822, by rfl⟩ : syracuseStep 7455053 = 2795645) B2795645
theorem B2326961 : Blo 1377508 2326961 := bstep (se 2 (by rfl) ⟨872610, by rfl⟩ : syracuseStep 2326961 = 1745221) B1745221
theorem B5890481 : Blo 1377508 5890481 := bstep (se 2 (by rfl) ⟨2208930, by rfl⟩ : syracuseStep 5890481 = 4417861) B4417861
theorem B11780549 : Blo 1377508 11780549 := bstep (se 4 (by rfl) ⟨1104426, by rfl⟩ : syracuseStep 11780549 = 2208853) B2208853
theorem B2327089 : Blo 1377508 2327089 := bstep (se 2 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 2327089 = 1745317) B1745317
theorem B11772485 : Blo 1377508 11772485 := bstep (se 4 (by rfl) ⟨1103670, by rfl⟩ : syracuseStep 11772485 = 2207341) B2207341
theorem B17916485 : Blo 1377508 17916485 := bstep (se 4 (by rfl) ⟨1679670, by rfl⟩ : syracuseStep 17916485 = 3359341) B3359341
theorem B2482769 : Blo 1377508 2482769 := bstep (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) B1862077
theorem B2327123 : Blo 1377508 2327123 := bstep (se 1 (by rfl) ⟨1745342, by rfl⟩ : syracuseStep 2327123 = 3490685) B3490685
theorem B4719185 : Blo 1377508 4719185 := bstep (se 2 (by rfl) ⟨1769694, by rfl⟩ : syracuseStep 4719185 = 3539389) B3539389
theorem B5235299 : Blo 1377508 5235299 := bstep (se 1 (by rfl) ⟨3926474, by rfl⟩ : syracuseStep 5235299 = 7852949) B7852949
theorem B3727981 : Blo 1377508 3727981 := bstep (se 3 (by rfl) ⟨698996, by rfl⟩ : syracuseStep 3727981 = 1397993) B1397993
theorem B5235313 : Blo 1377508 5235313 := bstep (se 2 (by rfl) ⟨1963242, by rfl⟩ : syracuseStep 5235313 = 3926485) B3926485
theorem B4653773 : Blo 1377508 4653773 := bstep (se 3 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 4653773 = 1745165) B1745165
theorem B2327251 : Blo 1377508 2327251 := bstep (se 1 (by rfl) ⟨1745438, by rfl⟩ : syracuseStep 2327251 = 3490877) B3490877
theorem B3310321 : Blo 1377508 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B1745651 : Blo 1377508 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B4653827 : Blo 1377508 4653827 := bstep (se 1 (by rfl) ⟨3490370, by rfl⟩ : syracuseStep 4653827 = 6980741) B6980741
theorem B16761613 : Blo 1377508 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B2327393 : Blo 1377508 2327393 := bstep (se 2 (by rfl) ⟨872772, by rfl⟩ : syracuseStep 2327393 = 1745545) B1745545
theorem B3924845 : Blo 1377508 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B2327521 : Blo 1377508 2327521 := bstep (se 2 (by rfl) ⟨872820, by rfl⟩ : syracuseStep 2327521 = 1745641) B1745641
theorem B6980579 : Blo 1377508 6980579 := bstep (se 1 (by rfl) ⟨5235434, by rfl⟩ : syracuseStep 6980579 = 10470869) B10470869
theorem B2327555 : Blo 1377508 2327555 := bstep (se 1 (by rfl) ⟨1745666, by rfl⟩ : syracuseStep 2327555 = 3491333) B3491333
theorem B4654097 : Blo 1377508 4654097 := bstep (se 2 (by rfl) ⟨1745286, by rfl⟩ : syracuseStep 4654097 = 3490573) B3490573
theorem B3925027 : Blo 1377508 3925027 := bstep (se 1 (by rfl) ⟨2943770, by rfl⟩ : syracuseStep 3925027 = 5887541) B5887541
theorem B6628387 : Blo 1377508 6628387 := bstep (se 1 (by rfl) ⟨4971290, by rfl⟩ : syracuseStep 6628387 = 9942581) B9942581
theorem B3925073 : Blo 1377508 3925073 := bstep (se 2 (by rfl) ⟨1471902, by rfl⟩ : syracuseStep 3925073 = 2943805) B2943805
theorem B3490897 : Blo 1377508 3490897 := bstep (se 2 (by rfl) ⟨1309086, by rfl⟩ : syracuseStep 3490897 = 2618173) B2618173
theorem B11781233 : Blo 1377508 11781233 := bstep (se 2 (by rfl) ⟨4417962, by rfl⟩ : syracuseStep 11781233 = 8835925) B8835925
theorem B2327683 : Blo 1377508 2327683 := bstep (se 1 (by rfl) ⟨1745762, by rfl⟩ : syracuseStep 2327683 = 3491525) B3491525
theorem B1492115 : Blo 1377508 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B4416707 : Blo 1377508 4416707 := bstep (se 1 (by rfl) ⟨3312530, by rfl⟩ : syracuseStep 4416707 = 6625061) B6625061
theorem B1377523 : Blo 1377508 1377523 := bstep (se 1 (by rfl) ⟨1033142, by rfl⟩ : syracuseStep 1377523 = 2066285) B2066285
theorem B1377539 : Blo 1377508 1377539 := bstep (se 1 (by rfl) ⟨1033154, by rfl⟩ : syracuseStep 1377539 = 2066309) B2066309
theorem B2327825 : Blo 1377508 2327825 := bstep (se 2 (by rfl) ⟨872934, by rfl⟩ : syracuseStep 2327825 = 1745869) B1745869
theorem B1377555 : Blo 1377508 1377555 := bstep (se 1 (by rfl) ⟨1033166, by rfl⟩ : syracuseStep 1377555 = 2066333) B2066333
theorem B1656083 : Blo 1377508 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B1377571 : Blo 1377508 1377571 := bstep (se 1 (by rfl) ⟨1033178, by rfl⟩ : syracuseStep 1377571 = 2066357) B2066357
theorem B1377587 : Blo 1377508 1377587 := bstep (se 1 (by rfl) ⟨1033190, by rfl⟩ : syracuseStep 1377587 = 2066381) B2066381
theorem B1377603 : Blo 1377508 1377603 := bstep (se 1 (by rfl) ⟨1033202, by rfl⟩ : syracuseStep 1377603 = 2066405) B2066405
theorem B1377619 : Blo 1377508 1377619 := bstep (se 1 (by rfl) ⟨1033214, by rfl⟩ : syracuseStep 1377619 = 2066429) B2066429
theorem B1377635 : Blo 1377508 1377635 := bstep (se 1 (by rfl) ⟨1033226, by rfl⟩ : syracuseStep 1377635 = 2066453) B2066453
theorem B3491171 : Blo 1377508 3491171 := bstep (se 1 (by rfl) ⟨2618378, by rfl⟩ : syracuseStep 3491171 = 5236757) B5236757
theorem B1377651 : Blo 1377508 1377651 := bstep (se 1 (by rfl) ⟨1033238, by rfl⟩ : syracuseStep 1377651 = 2066477) B2066477
theorem B1377667 : Blo 1377508 1377667 := bstep (se 1 (by rfl) ⟨1033250, by rfl⟩ : syracuseStep 1377667 = 2066501) B2066501
theorem B3310993 : Blo 1377508 3310993 := bstep (se 2 (by rfl) ⟨1241622, by rfl⟩ : syracuseStep 3310993 = 2483245) B2483245
theorem B1377683 : Blo 1377508 1377683 := bstep (se 1 (by rfl) ⟨1033262, by rfl⟩ : syracuseStep 1377683 = 2066525) B2066525
theorem B1377699 : Blo 1377508 1377699 := bstep (se 1 (by rfl) ⟨1033274, by rfl⟩ : syracuseStep 1377699 = 2066549) B2066549
theorem B1377715 : Blo 1377508 1377715 := bstep (se 1 (by rfl) ⟨1033286, by rfl⟩ : syracuseStep 1377715 = 2066573) B2066573
theorem B1377731 : Blo 1377508 1377731 := bstep (se 1 (by rfl) ⟨1033298, by rfl⟩ : syracuseStep 1377731 = 2066597) B2066597
theorem B1377747 : Blo 1377508 1377747 := bstep (se 1 (by rfl) ⟨1033310, by rfl⟩ : syracuseStep 1377747 = 2066621) B2066621
theorem B1549795 : Blo 1377508 1549795 := bstep (se 1 (by rfl) ⟨1162346, by rfl⟩ : syracuseStep 1549795 = 2324693) B2324693
theorem B1377763 : Blo 1377508 1377763 := bstep (se 1 (by rfl) ⟨1033322, by rfl⟩ : syracuseStep 1377763 = 2066645) B2066645
theorem B1377779 : Blo 1377508 1377779 := bstep (se 1 (by rfl) ⟨1033334, by rfl⟩ : syracuseStep 1377779 = 2066669) B2066669
theorem B1377795 : Blo 1377508 1377795 := bstep (se 1 (by rfl) ⟨1033346, by rfl⟩ : syracuseStep 1377795 = 2066693) B2066693
theorem B1377811 : Blo 1377508 1377811 := bstep (se 1 (by rfl) ⟨1033358, by rfl⟩ : syracuseStep 1377811 = 2066717) B2066717
theorem B1377827 : Blo 1377508 1377827 := bstep (se 1 (by rfl) ⟨1033370, by rfl⟩ : syracuseStep 1377827 = 2066741) B2066741
theorem B7849507 : Blo 1377508 7849507 := bstep (se 1 (by rfl) ⟨5887130, by rfl⟩ : syracuseStep 7849507 = 11774261) B11774261
theorem B3491363 : Blo 1377508 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B4654637 : Blo 1377508 4654637 := bstep (se 3 (by rfl) ⟨872744, by rfl⟩ : syracuseStep 4654637 = 1745489) B1745489
theorem B1377843 : Blo 1377508 1377843 := bstep (se 1 (by rfl) ⟨1033382, by rfl⟩ : syracuseStep 1377843 = 2066765) B2066765
theorem B1377859 : Blo 1377508 1377859 := bstep (se 1 (by rfl) ⟨1033394, by rfl⟩ : syracuseStep 1377859 = 2066789) B2066789
theorem B8291909 : Blo 1377508 8291909 := bstep (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) B1554733
theorem B1377875 : Blo 1377508 1377875 := bstep (se 1 (by rfl) ⟨1033406, by rfl⟩ : syracuseStep 1377875 = 2066813) B2066813
theorem B1377891 : Blo 1377508 1377891 := bstep (se 1 (by rfl) ⟨1033418, by rfl⟩ : syracuseStep 1377891 = 2066837) B2066837
theorem B4654691 : Blo 1377508 4654691 := bstep (se 1 (by rfl) ⟨3491018, by rfl⟩ : syracuseStep 4654691 = 6982037) B6982037
theorem B1549939 : Blo 1377508 1549939 := bstep (se 1 (by rfl) ⟨1162454, by rfl⟩ : syracuseStep 1549939 = 2324909) B2324909
theorem B1377907 : Blo 1377508 1377907 := bstep (se 1 (by rfl) ⟨1033430, by rfl⟩ : syracuseStep 1377907 = 2066861) B2066861
theorem B1377923 : Blo 1377508 1377923 := bstep (se 1 (by rfl) ⟨1033442, by rfl⟩ : syracuseStep 1377923 = 2066885) B2066885
theorem B1377939 : Blo 1377508 1377939 := bstep (se 1 (by rfl) ⟨1033454, by rfl⟩ : syracuseStep 1377939 = 2066909) B2066909
theorem B1377955 : Blo 1377508 1377955 := bstep (se 1 (by rfl) ⟨1033466, by rfl⟩ : syracuseStep 1377955 = 2066933) B2066933
theorem B1377971 : Blo 1377508 1377971 := bstep (se 1 (by rfl) ⟨1033478, by rfl⟩ : syracuseStep 1377971 = 2066957) B2066957
theorem B1377987 : Blo 1377508 1377987 := bstep (se 1 (by rfl) ⟨1033490, by rfl⟩ : syracuseStep 1377987 = 2066981) B2066981
theorem B1378003 : Blo 1377508 1378003 := bstep (se 1 (by rfl) ⟨1033502, by rfl⟩ : syracuseStep 1378003 = 2067005) B2067005
theorem B1378019 : Blo 1377508 1378019 := bstep (se 1 (by rfl) ⟨1033514, by rfl⟩ : syracuseStep 1378019 = 2067029) B2067029
theorem B2016995 : Blo 1377508 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B1378035 : Blo 1377508 1378035 := bstep (se 1 (by rfl) ⟨1033526, by rfl⟩ : syracuseStep 1378035 = 2067053) B2067053
theorem B1550083 : Blo 1377508 1550083 := bstep (se 1 (by rfl) ⟨1162562, by rfl⟩ : syracuseStep 1550083 = 2325125) B2325125
theorem B1378051 : Blo 1377508 1378051 := bstep (se 1 (by rfl) ⟨1033538, by rfl⟩ : syracuseStep 1378051 = 2067077) B2067077
theorem B6981389 : Blo 1377508 6981389 := bstep (se 3 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 6981389 = 2618021) B2618021
theorem B1378067 : Blo 1377508 1378067 := bstep (se 1 (by rfl) ⟨1033550, by rfl⟩ : syracuseStep 1378067 = 2067101) B2067101
theorem B1378083 : Blo 1377508 1378083 := bstep (se 1 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 1378083 = 2067125) B2067125
theorem B1378099 : Blo 1377508 1378099 := bstep (se 1 (by rfl) ⟨1033574, by rfl⟩ : syracuseStep 1378099 = 2067149) B2067149
theorem B1378115 : Blo 1377508 1378115 := bstep (se 1 (by rfl) ⟨1033586, by rfl⟩ : syracuseStep 1378115 = 2067173) B2067173
theorem B1378131 : Blo 1377508 1378131 := bstep (se 1 (by rfl) ⟨1033598, by rfl⟩ : syracuseStep 1378131 = 2067197) B2067197
theorem B2066273 : Blo 1377508 2066273 := bstep (se 2 (by rfl) ⟨774852, by rfl⟩ : syracuseStep 2066273 = 1549705) B1549705
theorem B1378147 : Blo 1377508 1378147 := bstep (se 1 (by rfl) ⟨1033610, by rfl⟩ : syracuseStep 1378147 = 2067221) B2067221
theorem B2066291 : Blo 1377508 2066291 := bstep (se 1 (by rfl) ⟨1549718, by rfl⟩ : syracuseStep 2066291 = 3099437) B3099437
theorem B1378163 : Blo 1377508 1378163 := bstep (se 1 (by rfl) ⟨1033622, by rfl⟩ : syracuseStep 1378163 = 2067245) B2067245
theorem B1378179 : Blo 1377508 1378179 := bstep (se 1 (by rfl) ⟨1033634, by rfl⟩ : syracuseStep 1378179 = 2067269) B2067269
theorem B2066321 : Blo 1377508 2066321 := bstep (se 2 (by rfl) ⟨774870, by rfl⟩ : syracuseStep 2066321 = 1549741) B1549741
theorem B1550227 : Blo 1377508 1550227 := bstep (se 1 (by rfl) ⟨1162670, by rfl⟩ : syracuseStep 1550227 = 2325341) B2325341
theorem B1378195 : Blo 1377508 1378195 := bstep (se 1 (by rfl) ⟨1033646, by rfl⟩ : syracuseStep 1378195 = 2067293) B2067293
theorem B2066339 : Blo 1377508 2066339 := bstep (se 1 (by rfl) ⟨1549754, by rfl⟩ : syracuseStep 2066339 = 3099509) B3099509
theorem B1378211 : Blo 1377508 1378211 := bstep (se 1 (by rfl) ⟨1033658, by rfl⟩ : syracuseStep 1378211 = 2067317) B2067317
theorem B1378227 : Blo 1377508 1378227 := bstep (se 1 (by rfl) ⟨1033670, by rfl⟩ : syracuseStep 1378227 = 2067341) B2067341
theorem B1656755 : Blo 1377508 1656755 := bstep (se 1 (by rfl) ⟨1242566, by rfl⟩ : syracuseStep 1656755 = 2485133) B2485133
theorem B2066369 : Blo 1377508 2066369 := bstep (se 2 (by rfl) ⟨774888, by rfl⟩ : syracuseStep 2066369 = 1549777) B1549777
theorem B1378243 : Blo 1377508 1378243 := bstep (se 1 (by rfl) ⟨1033682, by rfl⟩ : syracuseStep 1378243 = 2067365) B2067365
theorem B23553989 : Blo 1377508 23553989 := bstep (se 4 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 23553989 = 4416373) B4416373
theorem B2066387 : Blo 1377508 2066387 := bstep (se 1 (by rfl) ⟨1549790, by rfl⟩ : syracuseStep 2066387 = 3099581) B3099581
theorem B1378259 : Blo 1377508 1378259 := bstep (se 1 (by rfl) ⟨1033694, by rfl⟩ : syracuseStep 1378259 = 2067389) B2067389
theorem B1378275 : Blo 1377508 1378275 := bstep (se 1 (by rfl) ⟨1033706, by rfl⟩ : syracuseStep 1378275 = 2067413) B2067413
theorem B2066417 : Blo 1377508 2066417 := bstep (se 2 (by rfl) ⟨774906, by rfl⟩ : syracuseStep 2066417 = 1549813) B1549813
theorem B1378291 : Blo 1377508 1378291 := bstep (se 1 (by rfl) ⟨1033718, by rfl⟩ : syracuseStep 1378291 = 2067437) B2067437
theorem B2066435 : Blo 1377508 2066435 := bstep (se 1 (by rfl) ⟨1549826, by rfl⟩ : syracuseStep 2066435 = 3099653) B3099653
theorem B1378307 : Blo 1377508 1378307 := bstep (se 1 (by rfl) ⟨1033730, by rfl⟩ : syracuseStep 1378307 = 2067461) B2067461
theorem B4417553 : Blo 1377508 4417553 := bstep (se 2 (by rfl) ⟨1656582, by rfl⟩ : syracuseStep 4417553 = 3313165) B3313165
theorem B1378323 : Blo 1377508 1378323 := bstep (se 1 (by rfl) ⟨1033742, by rfl⟩ : syracuseStep 1378323 = 2067485) B2067485
theorem B2066465 : Blo 1377508 2066465 := bstep (se 2 (by rfl) ⟨774924, by rfl⟩ : syracuseStep 2066465 = 1549849) B1549849
theorem B1550371 : Blo 1377508 1550371 := bstep (se 1 (by rfl) ⟨1162778, by rfl⟩ : syracuseStep 1550371 = 2325557) B2325557
theorem B1378339 : Blo 1377508 1378339 := bstep (se 1 (by rfl) ⟨1033754, by rfl⟩ : syracuseStep 1378339 = 2067509) B2067509
theorem B5236771 : Blo 1377508 5236771 := bstep (se 1 (by rfl) ⟨3927578, by rfl⟩ : syracuseStep 5236771 = 7855157) B7855157
theorem B7850033 : Blo 1377508 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B2066483 : Blo 1377508 2066483 := bstep (se 1 (by rfl) ⟨1549862, by rfl⟩ : syracuseStep 2066483 = 3099725) B3099725
theorem B1378355 : Blo 1377508 1378355 := bstep (se 1 (by rfl) ⟨1033766, by rfl⟩ : syracuseStep 1378355 = 2067533) B2067533
theorem B1378371 : Blo 1377508 1378371 := bstep (se 1 (by rfl) ⟨1033778, by rfl⟩ : syracuseStep 1378371 = 2067557) B2067557
theorem B5892173 : Blo 1377508 5892173 := bstep (se 3 (by rfl) ⟨1104782, by rfl⟩ : syracuseStep 5892173 = 2209565) B2209565
theorem B2066513 : Blo 1377508 2066513 := bstep (se 2 (by rfl) ⟨774942, by rfl⟩ : syracuseStep 2066513 = 1549885) B1549885
theorem B1378387 : Blo 1377508 1378387 := bstep (se 1 (by rfl) ⟨1033790, by rfl⟩ : syracuseStep 1378387 = 2067581) B2067581
theorem B2066531 : Blo 1377508 2066531 := bstep (se 1 (by rfl) ⟨1549898, by rfl⟩ : syracuseStep 2066531 = 3099797) B3099797
theorem B1378403 : Blo 1377508 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B1378419 : Blo 1377508 1378419 := bstep (se 1 (by rfl) ⟨1033814, by rfl⟩ : syracuseStep 1378419 = 2067629) B2067629
theorem B2066561 : Blo 1377508 2066561 := bstep (se 2 (by rfl) ⟨774960, by rfl⟩ : syracuseStep 2066561 = 1549921) B1549921
theorem B1378435 : Blo 1377508 1378435 := bstep (se 1 (by rfl) ⟨1033826, by rfl⟩ : syracuseStep 1378435 = 2067653) B2067653
theorem B8833157 : Blo 1377508 8833157 := bstep (se 4 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 8833157 = 1656217) B1656217
theorem B8947853 : Blo 1377508 8947853 := bstep (se 3 (by rfl) ⟨1677722, by rfl⟩ : syracuseStep 8947853 = 3355445) B3355445
theorem B2066579 : Blo 1377508 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B1378451 : Blo 1377508 1378451 := bstep (se 1 (by rfl) ⟨1033838, by rfl⟩ : syracuseStep 1378451 = 2067677) B2067677
theorem B1378467 : Blo 1377508 1378467 := bstep (se 1 (by rfl) ⟨1033850, by rfl⟩ : syracuseStep 1378467 = 2067701) B2067701
theorem B2066609 : Blo 1377508 2066609 := bstep (se 2 (by rfl) ⟨774978, by rfl⟩ : syracuseStep 2066609 = 1549957) B1549957
theorem B1550515 : Blo 1377508 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B1378483 : Blo 1377508 1378483 := bstep (se 1 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 1378483 = 2067725) B2067725
theorem B2066627 : Blo 1377508 2066627 := bstep (se 1 (by rfl) ⟨1549970, by rfl⟩ : syracuseStep 2066627 = 3099941) B3099941
theorem B1378499 : Blo 1377508 1378499 := bstep (se 1 (by rfl) ⟨1033874, by rfl⟩ : syracuseStep 1378499 = 2067749) B2067749
theorem B5884109 : Blo 1377508 5884109 := bstep (se 3 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 5884109 = 2206541) B2206541
theorem B1378515 : Blo 1377508 1378515 := bstep (se 1 (by rfl) ⟨1033886, by rfl⟩ : syracuseStep 1378515 = 2067773) B2067773
theorem B2066657 : Blo 1377508 2066657 := bstep (se 2 (by rfl) ⟨774996, by rfl⟩ : syracuseStep 2066657 = 1549993) B1549993
theorem B11176163 : Blo 1377508 11176163 := bstep (se 1 (by rfl) ⟨8382122, by rfl⟩ : syracuseStep 11176163 = 16764245) B16764245
theorem B1378531 : Blo 1377508 1378531 := bstep (se 1 (by rfl) ⟨1033898, by rfl⟩ : syracuseStep 1378531 = 2067797) B2067797
theorem B2066675 : Blo 1377508 2066675 := bstep (se 1 (by rfl) ⟨1550006, by rfl⟩ : syracuseStep 2066675 = 3100013) B3100013
theorem B1378547 : Blo 1377508 1378547 := bstep (se 1 (by rfl) ⟨1033910, by rfl⟩ : syracuseStep 1378547 = 2067821) B2067821
theorem B1378563 : Blo 1377508 1378563 := bstep (se 1 (by rfl) ⟨1033922, by rfl⟩ : syracuseStep 1378563 = 2067845) B2067845
theorem B2066705 : Blo 1377508 2066705 := bstep (se 2 (by rfl) ⟨775014, by rfl⟩ : syracuseStep 2066705 = 1550029) B1550029
theorem B1378579 : Blo 1377508 1378579 := bstep (se 1 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 1378579 = 2067869) B2067869
theorem B2066723 : Blo 1377508 2066723 := bstep (se 1 (by rfl) ⟨1550042, by rfl⟩ : syracuseStep 2066723 = 3100085) B3100085
theorem B1378595 : Blo 1377508 1378595 := bstep (se 1 (by rfl) ⟨1033946, by rfl⟩ : syracuseStep 1378595 = 2067893) B2067893
theorem B1378611 : Blo 1377508 1378611 := bstep (se 1 (by rfl) ⟨1033958, by rfl⟩ : syracuseStep 1378611 = 2067917) B2067917
theorem B2066753 : Blo 1377508 2066753 := bstep (se 2 (by rfl) ⟨775032, by rfl⟩ : syracuseStep 2066753 = 1550065) B1550065
theorem B1550659 : Blo 1377508 1550659 := bstep (se 1 (by rfl) ⟨1162994, by rfl⟩ : syracuseStep 1550659 = 2325989) B2325989
theorem B1378627 : Blo 1377508 1378627 := bstep (se 1 (by rfl) ⟨1033970, by rfl⟩ : syracuseStep 1378627 = 2067941) B2067941
theorem B14903621 : Blo 1377508 14903621 := bstep (se 4 (by rfl) ⟨1397214, by rfl⟩ : syracuseStep 14903621 = 2794429) B2794429
theorem B2066771 : Blo 1377508 2066771 := bstep (se 1 (by rfl) ⟨1550078, by rfl⟩ : syracuseStep 2066771 = 3100157) B3100157
theorem B1378643 : Blo 1377508 1378643 := bstep (se 1 (by rfl) ⟨1033982, by rfl⟩ : syracuseStep 1378643 = 2067965) B2067965
theorem B1378659 : Blo 1377508 1378659 := bstep (se 1 (by rfl) ⟨1033994, by rfl⟩ : syracuseStep 1378659 = 2067989) B2067989
theorem B2066801 : Blo 1377508 2066801 := bstep (se 2 (by rfl) ⟨775050, by rfl⟩ : syracuseStep 2066801 = 1550101) B1550101
theorem B1378675 : Blo 1377508 1378675 := bstep (se 1 (by rfl) ⟨1034006, by rfl⟩ : syracuseStep 1378675 = 2068013) B2068013
theorem B2066819 : Blo 1377508 2066819 := bstep (se 1 (by rfl) ⟨1550114, by rfl⟩ : syracuseStep 2066819 = 3100229) B3100229
theorem B1378691 : Blo 1377508 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B4655501 : Blo 1377508 4655501 := bstep (se 3 (by rfl) ⟨872906, by rfl⟩ : syracuseStep 4655501 = 1745813) B1745813
theorem B1378707 : Blo 1377508 1378707 := bstep (se 1 (by rfl) ⟨1034030, by rfl⟩ : syracuseStep 1378707 = 2068061) B2068061
theorem B2066849 : Blo 1377508 2066849 := bstep (se 2 (by rfl) ⟨775068, by rfl⟩ : syracuseStep 2066849 = 1550137) B1550137
theorem B2943395 : Blo 1377508 2943395 := bstep (se 1 (by rfl) ⟨2207546, by rfl⟩ : syracuseStep 2943395 = 4415093) B4415093
theorem B1378723 : Blo 1377508 1378723 := bstep (se 1 (by rfl) ⟨1034042, by rfl⟩ : syracuseStep 1378723 = 2068085) B2068085
theorem B2484643 : Blo 1377508 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B2066867 : Blo 1377508 2066867 := bstep (se 1 (by rfl) ⟨1550150, by rfl⟩ : syracuseStep 2066867 = 3100301) B3100301
theorem B1378739 : Blo 1377508 1378739 := bstep (se 1 (by rfl) ⟨1034054, by rfl⟩ : syracuseStep 1378739 = 2068109) B2068109
theorem B1378755 : Blo 1377508 1378755 := bstep (se 1 (by rfl) ⟨1034066, by rfl⟩ : syracuseStep 1378755 = 2068133) B2068133
theorem B4655555 : Blo 1377508 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B2066897 : Blo 1377508 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B1550803 : Blo 1377508 1550803 := bstep (se 1 (by rfl) ⟨1163102, by rfl⟩ : syracuseStep 1550803 = 2326205) B2326205
theorem B1378771 : Blo 1377508 1378771 := bstep (se 1 (by rfl) ⟨1034078, by rfl⟩ : syracuseStep 1378771 = 2068157) B2068157
theorem B2066915 : Blo 1377508 2066915 := bstep (se 1 (by rfl) ⟨1550186, by rfl⟩ : syracuseStep 2066915 = 3100373) B3100373
theorem B1378787 : Blo 1377508 1378787 := bstep (se 1 (by rfl) ⟨1034090, by rfl⟩ : syracuseStep 1378787 = 2068181) B2068181
theorem B6973937 : Blo 1377508 6973937 := bstep (se 2 (by rfl) ⟨2615226, by rfl⟩ : syracuseStep 6973937 = 5230453) B5230453
theorem B13240817 : Blo 1377508 13240817 := bstep (se 2 (by rfl) ⟨4965306, by rfl⟩ : syracuseStep 13240817 = 9930613) B9930613
theorem B1378803 : Blo 1377508 1378803 := bstep (se 1 (by rfl) ⟨1034102, by rfl⟩ : syracuseStep 1378803 = 2068205) B2068205
theorem B2066945 : Blo 1377508 2066945 := bstep (se 2 (by rfl) ⟨775104, by rfl⟩ : syracuseStep 2066945 = 1550209) B1550209
theorem B1378819 : Blo 1377508 1378819 := bstep (se 1 (by rfl) ⟨1034114, by rfl⟩ : syracuseStep 1378819 = 2068229) B2068229
theorem B3926531 : Blo 1377508 3926531 := bstep (se 1 (by rfl) ⟨2944898, by rfl⟩ : syracuseStep 3926531 = 5889797) B5889797
theorem B2066963 : Blo 1377508 2066963 := bstep (se 1 (by rfl) ⟨1550222, by rfl⟩ : syracuseStep 2066963 = 3100445) B3100445
theorem B1378835 : Blo 1377508 1378835 := bstep (se 1 (by rfl) ⟨1034126, by rfl⟩ : syracuseStep 1378835 = 2068253) B2068253
theorem B1378851 : Blo 1377508 1378851 := bstep (se 1 (by rfl) ⟨1034138, by rfl⟩ : syracuseStep 1378851 = 2068277) B2068277
theorem B2066993 : Blo 1377508 2066993 := bstep (se 2 (by rfl) ⟨775122, by rfl⟩ : syracuseStep 2066993 = 1550245) B1550245
theorem B1378867 : Blo 1377508 1378867 := bstep (se 1 (by rfl) ⟨1034150, by rfl⟩ : syracuseStep 1378867 = 2068301) B2068301
theorem B2067011 : Blo 1377508 2067011 := bstep (se 1 (by rfl) ⟨1550258, by rfl⟩ : syracuseStep 2067011 = 3100517) B3100517
theorem B1378883 : Blo 1377508 1378883 := bstep (se 1 (by rfl) ⟨1034162, by rfl⟩ : syracuseStep 1378883 = 2068325) B2068325
theorem B1378899 : Blo 1377508 1378899 := bstep (se 1 (by rfl) ⟨1034174, by rfl⟩ : syracuseStep 1378899 = 2068349) B2068349
theorem B2067041 : Blo 1377508 2067041 := bstep (se 2 (by rfl) ⟨775140, by rfl⟩ : syracuseStep 2067041 = 1550281) B1550281
theorem B1550947 : Blo 1377508 1550947 := bstep (se 1 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 1550947 = 2326421) B2326421
theorem B1378915 : Blo 1377508 1378915 := bstep (se 1 (by rfl) ⟨1034186, by rfl⟩ : syracuseStep 1378915 = 2068373) B2068373
theorem B2067059 : Blo 1377508 2067059 := bstep (se 1 (by rfl) ⟨1550294, by rfl⟩ : syracuseStep 2067059 = 3100589) B3100589
theorem B1378931 : Blo 1377508 1378931 := bstep (se 1 (by rfl) ⟨1034198, by rfl⟩ : syracuseStep 1378931 = 2068397) B2068397
theorem B1378947 : Blo 1377508 1378947 := bstep (se 1 (by rfl) ⟨1034210, by rfl⟩ : syracuseStep 1378947 = 2068421) B2068421
theorem B2067089 : Blo 1377508 2067089 := bstep (se 2 (by rfl) ⟨775158, by rfl⟩ : syracuseStep 2067089 = 1550317) B1550317
theorem B1378963 : Blo 1377508 1378963 := bstep (se 1 (by rfl) ⟨1034222, by rfl⟩ : syracuseStep 1378963 = 2068445) B2068445
theorem B2615971 : Blo 1377508 2615971 := bstep (se 1 (by rfl) ⟨1961978, by rfl⟩ : syracuseStep 2615971 = 3923957) B3923957
theorem B2067107 : Blo 1377508 2067107 := bstep (se 1 (by rfl) ⟨1550330, by rfl⟩ : syracuseStep 2067107 = 3100661) B3100661
theorem B1378979 : Blo 1377508 1378979 := bstep (se 1 (by rfl) ⟨1034234, by rfl⟩ : syracuseStep 1378979 = 2068469) B2068469
theorem B1378995 : Blo 1377508 1378995 := bstep (se 1 (by rfl) ⟨1034246, by rfl⟩ : syracuseStep 1378995 = 2068493) B2068493
theorem B2067137 : Blo 1377508 2067137 := bstep (se 2 (by rfl) ⟨775176, by rfl⟩ : syracuseStep 2067137 = 1550353) B1550353
theorem B1379011 : Blo 1377508 1379011 := bstep (se 1 (by rfl) ⟨1034258, by rfl⟩ : syracuseStep 1379011 = 2068517) B2068517
theorem B4655825 : Blo 1377508 4655825 := bstep (se 2 (by rfl) ⟨1745934, by rfl⟩ : syracuseStep 4655825 = 3491869) B3491869
theorem B2067155 : Blo 1377508 2067155 := bstep (se 1 (by rfl) ⟨1550366, by rfl⟩ : syracuseStep 2067155 = 3100733) B3100733
theorem B1379027 : Blo 1377508 1379027 := bstep (se 1 (by rfl) ⟨1034270, by rfl⟩ : syracuseStep 1379027 = 2068541) B2068541
theorem B1379043 : Blo 1377508 1379043 := bstep (se 1 (by rfl) ⟨1034282, by rfl⟩ : syracuseStep 1379043 = 2068565) B2068565
theorem B2067185 : Blo 1377508 2067185 := bstep (se 2 (by rfl) ⟨775194, by rfl⟩ : syracuseStep 2067185 = 1550389) B1550389
theorem B4967153 : Blo 1377508 4967153 := bstep (se 2 (by rfl) ⟨1862682, by rfl⟩ : syracuseStep 4967153 = 3725365) B3725365
theorem B1551091 : Blo 1377508 1551091 := bstep (se 1 (by rfl) ⟨1163318, by rfl⟩ : syracuseStep 1551091 = 2326637) B2326637
theorem B1379059 : Blo 1377508 1379059 := bstep (se 1 (by rfl) ⟨1034294, by rfl⟩ : syracuseStep 1379059 = 2068589) B2068589
theorem B2067203 : Blo 1377508 2067203 := bstep (se 1 (by rfl) ⟨1550402, by rfl⟩ : syracuseStep 2067203 = 3100805) B3100805
theorem B1379075 : Blo 1377508 1379075 := bstep (se 1 (by rfl) ⟨1034306, by rfl⟩ : syracuseStep 1379075 = 2068613) B2068613
theorem B1379091 : Blo 1377508 1379091 := bstep (se 1 (by rfl) ⟨1034318, by rfl⟩ : syracuseStep 1379091 = 2068637) B2068637
theorem B2067233 : Blo 1377508 2067233 := bstep (se 2 (by rfl) ⟨775212, by rfl⟩ : syracuseStep 2067233 = 1550425) B1550425
theorem B1379107 : Blo 1377508 1379107 := bstep (se 1 (by rfl) ⟨1034330, by rfl⟩ : syracuseStep 1379107 = 2068661) B2068661
theorem B2067251 : Blo 1377508 2067251 := bstep (se 1 (by rfl) ⟨1550438, by rfl⟩ : syracuseStep 2067251 = 3100877) B3100877
theorem B1379123 : Blo 1377508 1379123 := bstep (se 1 (by rfl) ⟨1034342, by rfl⟩ : syracuseStep 1379123 = 2068685) B2068685
theorem B2616131 : Blo 1377508 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B1379139 : Blo 1377508 1379139 := bstep (se 1 (by rfl) ⟨1034354, by rfl⟩ : syracuseStep 1379139 = 2068709) B2068709
theorem B6286157 : Blo 1377508 6286157 := bstep (se 3 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 6286157 = 2357309) B2357309
theorem B3099473 : Blo 1377508 3099473 := bstep (se 2 (by rfl) ⟨1162302, by rfl⟩ : syracuseStep 3099473 = 2324605) B2324605
theorem B2067281 : Blo 1377508 2067281 := bstep (se 2 (by rfl) ⟨775230, by rfl⟩ : syracuseStep 2067281 = 1550461) B1550461
theorem B1379155 : Blo 1377508 1379155 := bstep (se 1 (by rfl) ⟨1034366, by rfl⟩ : syracuseStep 1379155 = 2068733) B2068733
theorem B3099491 : Blo 1377508 3099491 := bstep (se 1 (by rfl) ⟨2324618, by rfl⟩ : syracuseStep 3099491 = 4649237) B4649237
theorem B2067299 : Blo 1377508 2067299 := bstep (se 1 (by rfl) ⟨1550474, by rfl⟩ : syracuseStep 2067299 = 3100949) B3100949
theorem B1379171 : Blo 1377508 1379171 := bstep (se 1 (by rfl) ⟨1034378, by rfl⟩ : syracuseStep 1379171 = 2068757) B2068757
theorem B2943857 : Blo 1377508 2943857 := bstep (se 2 (by rfl) ⟨1103946, by rfl⟩ : syracuseStep 2943857 = 2207893) B2207893
theorem B1379187 : Blo 1377508 1379187 := bstep (se 1 (by rfl) ⟨1034390, by rfl⟩ : syracuseStep 1379187 = 2068781) B2068781
theorem B2067329 : Blo 1377508 2067329 := bstep (se 2 (by rfl) ⟨775248, by rfl⟩ : syracuseStep 2067329 = 1550497) B1550497
theorem B1551235 : Blo 1377508 1551235 := bstep (se 1 (by rfl) ⟨1163426, by rfl⟩ : syracuseStep 1551235 = 2326853) B2326853
theorem B1379203 : Blo 1377508 1379203 := bstep (se 1 (by rfl) ⟨1034402, by rfl⟩ : syracuseStep 1379203 = 2068805) B2068805
theorem B4475789 : Blo 1377508 4475789 := bstep (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) B1678421
theorem B2067347 : Blo 1377508 2067347 := bstep (se 1 (by rfl) ⟨1550510, by rfl⟩ : syracuseStep 2067347 = 3101021) B3101021
theorem B1379219 : Blo 1377508 1379219 := bstep (se 1 (by rfl) ⟨1034414, by rfl⟩ : syracuseStep 1379219 = 2068829) B2068829
theorem B1379235 : Blo 1377508 1379235 := bstep (se 1 (by rfl) ⟨1034426, by rfl⟩ : syracuseStep 1379235 = 2068853) B2068853
theorem B2067377 : Blo 1377508 2067377 := bstep (se 2 (by rfl) ⟨775266, by rfl⟩ : syracuseStep 2067377 = 1550533) B1550533
theorem B1379251 : Blo 1377508 1379251 := bstep (se 1 (by rfl) ⟨1034438, by rfl⟩ : syracuseStep 1379251 = 2068877) B2068877
theorem B2067395 : Blo 1377508 2067395 := bstep (se 1 (by rfl) ⟨1550546, by rfl⟩ : syracuseStep 2067395 = 3101093) B3101093
theorem B1379267 : Blo 1377508 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B1379283 : Blo 1377508 1379283 := bstep (se 1 (by rfl) ⟨1034462, by rfl⟩ : syracuseStep 1379283 = 2068925) B2068925
theorem B2067425 : Blo 1377508 2067425 := bstep (se 2 (by rfl) ⟨775284, by rfl⟩ : syracuseStep 2067425 = 1550569) B1550569
theorem B1379299 : Blo 1377508 1379299 := bstep (se 1 (by rfl) ⟨1034474, by rfl⟩ : syracuseStep 1379299 = 2068949) B2068949
theorem B4598765 : Blo 1377508 4598765 := bstep (se 3 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 4598765 = 1724537) B1724537
theorem B3779569 : Blo 1377508 3779569 := bstep (se 2 (by rfl) ⟨1417338, by rfl⟩ : syracuseStep 3779569 = 2834677) B2834677
theorem B2067443 : Blo 1377508 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B1379315 : Blo 1377508 1379315 := bstep (se 1 (by rfl) ⟨1034486, by rfl⟩ : syracuseStep 1379315 = 2068973) B2068973
theorem B4779011 : Blo 1377508 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B1379331 : Blo 1377508 1379331 := bstep (se 1 (by rfl) ⟨1034498, by rfl⟩ : syracuseStep 1379331 = 2068997) B2068997
theorem B2067473 : Blo 1377508 2067473 := bstep (se 2 (by rfl) ⟨775302, by rfl⟩ : syracuseStep 2067473 = 1550605) B1550605
theorem B1551379 : Blo 1377508 1551379 := bstep (se 1 (by rfl) ⟨1163534, by rfl⟩ : syracuseStep 1551379 = 2327069) B2327069
theorem B1379347 : Blo 1377508 1379347 := bstep (se 1 (by rfl) ⟨1034510, by rfl⟩ : syracuseStep 1379347 = 2069021) B2069021
theorem B2067491 : Blo 1377508 2067491 := bstep (se 1 (by rfl) ⟨1550618, by rfl⟩ : syracuseStep 2067491 = 3101237) B3101237
theorem B1379363 : Blo 1377508 1379363 := bstep (se 1 (by rfl) ⟨1034522, by rfl⟩ : syracuseStep 1379363 = 2069045) B2069045
theorem B1379379 : Blo 1377508 1379379 := bstep (se 1 (by rfl) ⟨1034534, by rfl⟩ : syracuseStep 1379379 = 2069069) B2069069
theorem B2067521 : Blo 1377508 2067521 := bstep (se 2 (by rfl) ⟨775320, by rfl⟩ : syracuseStep 2067521 = 1550641) B1550641
theorem B1379395 : Blo 1377508 1379395 := bstep (se 1 (by rfl) ⟨1034546, by rfl⟩ : syracuseStep 1379395 = 2069093) B2069093
theorem B2796611 : Blo 1377508 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B2067539 : Blo 1377508 2067539 := bstep (se 1 (by rfl) ⟨1550654, by rfl⟩ : syracuseStep 2067539 = 3101309) B3101309
theorem B1379411 : Blo 1377508 1379411 := bstep (se 1 (by rfl) ⟨1034558, by rfl⟩ : syracuseStep 1379411 = 2069117) B2069117
theorem B1379427 : Blo 1377508 1379427 := bstep (se 1 (by rfl) ⟨1034570, by rfl⟩ : syracuseStep 1379427 = 2069141) B2069141
theorem B3099761 : Blo 1377508 3099761 := bstep (se 2 (by rfl) ⟨1162410, by rfl⟩ : syracuseStep 3099761 = 2324821) B2324821
theorem B2067569 : Blo 1377508 2067569 := bstep (se 2 (by rfl) ⟨775338, by rfl⟩ : syracuseStep 2067569 = 1550677) B1550677
theorem B1379443 : Blo 1377508 1379443 := bstep (se 1 (by rfl) ⟨1034582, by rfl⟩ : syracuseStep 1379443 = 2069165) B2069165
theorem B3099779 : Blo 1377508 3099779 := bstep (se 1 (by rfl) ⟨2324834, by rfl⟩ : syracuseStep 3099779 = 4649669) B4649669
theorem B2067587 : Blo 1377508 2067587 := bstep (se 1 (by rfl) ⟨1550690, by rfl⟩ : syracuseStep 2067587 = 3101381) B3101381
theorem B1379459 : Blo 1377508 1379459 := bstep (se 1 (by rfl) ⟨1034594, by rfl⟩ : syracuseStep 1379459 = 2069189) B2069189
theorem B1379475 : Blo 1377508 1379475 := bstep (se 1 (by rfl) ⟨1034606, by rfl⟩ : syracuseStep 1379475 = 2069213) B2069213
theorem B2067617 : Blo 1377508 2067617 := bstep (se 2 (by rfl) ⟨775356, by rfl⟩ : syracuseStep 2067617 = 1550713) B1550713
theorem B1551523 : Blo 1377508 1551523 := bstep (se 1 (by rfl) ⟨1163642, by rfl⟩ : syracuseStep 1551523 = 2327285) B2327285
theorem B1379491 : Blo 1377508 1379491 := bstep (se 1 (by rfl) ⟨1034618, by rfl⟩ : syracuseStep 1379491 = 2069237) B2069237
theorem B2067635 : Blo 1377508 2067635 := bstep (se 1 (by rfl) ⟨1550726, by rfl⟩ : syracuseStep 2067635 = 3101453) B3101453
theorem B1379507 : Blo 1377508 1379507 := bstep (se 1 (by rfl) ⟨1034630, by rfl⟩ : syracuseStep 1379507 = 2069261) B2069261
theorem B2067665 : Blo 1377508 2067665 := bstep (se 2 (by rfl) ⟨775374, by rfl⟩ : syracuseStep 2067665 = 1550749) B1550749
theorem B2206931 : Blo 1377508 2206931 := bstep (se 1 (by rfl) ⟨1655198, by rfl⟩ : syracuseStep 2206931 = 3310397) B3310397
theorem B2067683 : Blo 1377508 2067683 := bstep (se 1 (by rfl) ⟨1550762, by rfl⟩ : syracuseStep 2067683 = 3101525) B3101525
theorem B35810531 : Blo 1377508 35810531 := bstep (se 1 (by rfl) ⟨26857898, by rfl⟩ : syracuseStep 35810531 = 53715797) B53715797
theorem B2067713 : Blo 1377508 2067713 := bstep (se 2 (by rfl) ⟨775392, by rfl⟩ : syracuseStep 2067713 = 1550785) B1550785
theorem B4476163 : Blo 1377508 4476163 := bstep (se 1 (by rfl) ⟨3357122, by rfl⟩ : syracuseStep 4476163 = 6714245) B6714245
theorem B8072461 : Blo 1377508 8072461 := bstep (se 3 (by rfl) ⟨1513586, by rfl⟩ : syracuseStep 8072461 = 3027173) B3027173
theorem B2067731 : Blo 1377508 2067731 := bstep (se 1 (by rfl) ⟨1550798, by rfl⟩ : syracuseStep 2067731 = 3101597) B3101597
theorem B2067761 : Blo 1377508 2067761 := bstep (se 2 (by rfl) ⟨775410, by rfl⟩ : syracuseStep 2067761 = 1550821) B1550821
theorem B1551667 : Blo 1377508 1551667 := bstep (se 1 (by rfl) ⟨1163750, by rfl⟩ : syracuseStep 1551667 = 2327501) B2327501
theorem B2067779 : Blo 1377508 2067779 := bstep (se 1 (by rfl) ⟨1550834, by rfl⟩ : syracuseStep 2067779 = 3101669) B3101669
theorem B2067809 : Blo 1377508 2067809 := bstep (se 2 (by rfl) ⟨775428, by rfl⟩ : syracuseStep 2067809 = 1550857) B1550857
theorem B2067827 : Blo 1377508 2067827 := bstep (se 1 (by rfl) ⟨1550870, by rfl⟩ : syracuseStep 2067827 = 3101741) B3101741
theorem B2207105 : Blo 1377508 2207105 := bstep (se 2 (by rfl) ⟨827664, by rfl⟩ : syracuseStep 2207105 = 1655329) B1655329
theorem B3100049 : Blo 1377508 3100049 := bstep (se 2 (by rfl) ⟨1162518, by rfl⟩ : syracuseStep 3100049 = 2325037) B2325037
theorem B2067857 : Blo 1377508 2067857 := bstep (se 2 (by rfl) ⟨775446, by rfl⟩ : syracuseStep 2067857 = 1550893) B1550893
theorem B3100067 : Blo 1377508 3100067 := bstep (se 1 (by rfl) ⟨2325050, by rfl⟩ : syracuseStep 3100067 = 4650101) B4650101
theorem B2067875 : Blo 1377508 2067875 := bstep (se 1 (by rfl) ⟨1550906, by rfl⟩ : syracuseStep 2067875 = 3101813) B3101813
theorem B2067905 : Blo 1377508 2067905 := bstep (se 2 (by rfl) ⟨775464, by rfl⟩ : syracuseStep 2067905 = 1550929) B1550929
theorem B1551811 : Blo 1377508 1551811 := bstep (se 1 (by rfl) ⟨1163858, by rfl⟩ : syracuseStep 1551811 = 2327717) B2327717
theorem B2067923 : Blo 1377508 2067923 := bstep (se 1 (by rfl) ⟨1550942, by rfl⟩ : syracuseStep 2067923 = 3101885) B3101885
theorem B1961443 : Blo 1377508 1961443 := bstep (se 1 (by rfl) ⟨1471082, by rfl⟩ : syracuseStep 1961443 = 2942165) B2942165
theorem B7851491 : Blo 1377508 7851491 := bstep (se 1 (by rfl) ⟨5888618, by rfl⟩ : syracuseStep 7851491 = 11777237) B11777237
theorem B2067953 : Blo 1377508 2067953 := bstep (se 2 (by rfl) ⟨775482, by rfl⟩ : syracuseStep 2067953 = 1550965) B1550965
theorem B2067971 : Blo 1377508 2067971 := bstep (se 1 (by rfl) ⟨1550978, by rfl⟩ : syracuseStep 2067971 = 3101957) B3101957
theorem B2068001 : Blo 1377508 2068001 := bstep (se 2 (by rfl) ⟨775500, by rfl⟩ : syracuseStep 2068001 = 1551001) B1551001
theorem B2068019 : Blo 1377508 2068019 := bstep (se 1 (by rfl) ⟨1551014, by rfl⟩ : syracuseStep 2068019 = 3102029) B3102029
theorem B75492917 : Blo 1377508 75492917 := bstep (se 5 (by rfl) ⟨3538730, by rfl⟩ : syracuseStep 75492917 = 7077461) B7077461
theorem B2068049 : Blo 1377508 2068049 := bstep (se 2 (by rfl) ⟨775518, by rfl⟩ : syracuseStep 2068049 = 1551037) B1551037
theorem B19107427 : Blo 1377508 19107427 := bstep (se 1 (by rfl) ⟨14330570, by rfl⟩ : syracuseStep 19107427 = 28661141) B28661141
theorem B2068067 : Blo 1377508 2068067 := bstep (se 1 (by rfl) ⟨1551050, by rfl⟩ : syracuseStep 2068067 = 3102101) B3102101
theorem B2068097 : Blo 1377508 2068097 := bstep (se 2 (by rfl) ⟨775536, by rfl⟩ : syracuseStep 2068097 = 1551073) B1551073
theorem B2068115 : Blo 1377508 2068115 := bstep (se 1 (by rfl) ⟨1551086, by rfl⟩ : syracuseStep 2068115 = 3102173) B3102173
theorem B3100337 : Blo 1377508 3100337 := bstep (se 2 (by rfl) ⟨1162626, by rfl⟩ : syracuseStep 3100337 = 2325253) B2325253
theorem B2068145 : Blo 1377508 2068145 := bstep (se 2 (by rfl) ⟨775554, by rfl⟩ : syracuseStep 2068145 = 1551109) B1551109
theorem B3100355 : Blo 1377508 3100355 := bstep (se 1 (by rfl) ⟨2325266, by rfl⟩ : syracuseStep 3100355 = 4650533) B4650533
theorem B35311301 : Blo 1377508 35311301 := bstep (se 4 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 35311301 = 6620869) B6620869
theorem B2068163 : Blo 1377508 2068163 := bstep (se 1 (by rfl) ⟨1551122, by rfl⟩ : syracuseStep 2068163 = 3102245) B3102245
theorem B3927761 : Blo 1377508 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B2068193 : Blo 1377508 2068193 := bstep (se 2 (by rfl) ⟨775572, by rfl⟩ : syracuseStep 2068193 = 1551145) B1551145
theorem B2068211 : Blo 1377508 2068211 := bstep (se 1 (by rfl) ⟨1551158, by rfl⟩ : syracuseStep 2068211 = 3102317) B3102317
theorem B10465037 : Blo 1377508 10465037 := bstep (se 3 (by rfl) ⟨1962194, by rfl⟩ : syracuseStep 10465037 = 3924389) B3924389
theorem B2068241 : Blo 1377508 2068241 := bstep (se 2 (by rfl) ⟨775590, by rfl⟩ : syracuseStep 2068241 = 1551181) B1551181
theorem B2068259 : Blo 1377508 2068259 := bstep (se 1 (by rfl) ⟨1551194, by rfl⟩ : syracuseStep 2068259 = 3102389) B3102389
theorem B4419373 : Blo 1377508 4419373 := bstep (se 3 (by rfl) ⟨828632, by rfl⟩ : syracuseStep 4419373 = 1657265) B1657265
theorem B2068289 : Blo 1377508 2068289 := bstep (se 2 (by rfl) ⟨775608, by rfl⟩ : syracuseStep 2068289 = 1551217) B1551217
theorem B2068307 : Blo 1377508 2068307 := bstep (se 1 (by rfl) ⟨1551230, by rfl⟩ : syracuseStep 2068307 = 3102461) B3102461
theorem B2617201 : Blo 1377508 2617201 := bstep (se 2 (by rfl) ⟨981450, by rfl⟩ : syracuseStep 2617201 = 1962901) B1962901
theorem B2068337 : Blo 1377508 2068337 := bstep (se 2 (by rfl) ⟨775626, by rfl⟩ : syracuseStep 2068337 = 1551253) B1551253
theorem B2068355 : Blo 1377508 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B2068385 : Blo 1377508 2068385 := bstep (se 2 (by rfl) ⟨775644, by rfl⟩ : syracuseStep 2068385 = 1551289) B1551289
theorem B6975395 : Blo 1377508 6975395 := bstep (se 1 (by rfl) ⟨5231546, by rfl⟩ : syracuseStep 6975395 = 10463093) B10463093
theorem B2068403 : Blo 1377508 2068403 := bstep (se 1 (by rfl) ⟨1551302, by rfl⟩ : syracuseStep 2068403 = 3102605) B3102605
theorem B3100625 : Blo 1377508 3100625 := bstep (se 2 (by rfl) ⟨1162734, by rfl⟩ : syracuseStep 3100625 = 2325469) B2325469
theorem B2068433 : Blo 1377508 2068433 := bstep (se 2 (by rfl) ⟨775662, by rfl⟩ : syracuseStep 2068433 = 1551325) B1551325
theorem B3100643 : Blo 1377508 3100643 := bstep (se 1 (by rfl) ⟨2325482, by rfl⟩ : syracuseStep 3100643 = 4650965) B4650965
theorem B2068451 : Blo 1377508 2068451 := bstep (se 1 (by rfl) ⟨1551338, by rfl⟩ : syracuseStep 2068451 = 3102677) B3102677
theorem B2068481 : Blo 1377508 2068481 := bstep (se 2 (by rfl) ⟨775680, by rfl⟩ : syracuseStep 2068481 = 1551361) B1551361
theorem B2068499 : Blo 1377508 2068499 := bstep (se 1 (by rfl) ⟨1551374, by rfl⟩ : syracuseStep 2068499 = 3102749) B3102749
theorem B2068529 : Blo 1377508 2068529 := bstep (se 2 (by rfl) ⟨775698, by rfl⟩ : syracuseStep 2068529 = 1551397) B1551397
theorem B2068547 : Blo 1377508 2068547 := bstep (se 1 (by rfl) ⟨1551410, by rfl⟩ : syracuseStep 2068547 = 3102821) B3102821
theorem B10203205 : Blo 1377508 10203205 := bstep (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) B1913101
theorem B2068577 : Blo 1377508 2068577 := bstep (se 2 (by rfl) ⟨775716, by rfl⟩ : syracuseStep 2068577 = 1551433) B1551433
theorem B2068595 : Blo 1377508 2068595 := bstep (se 1 (by rfl) ⟨1551446, by rfl⟩ : syracuseStep 2068595 = 3102893) B3102893
theorem B2945155 : Blo 1377508 2945155 := bstep (se 1 (by rfl) ⟨2208866, by rfl⟩ : syracuseStep 2945155 = 4417733) B4417733
theorem B2068625 : Blo 1377508 2068625 := bstep (se 2 (by rfl) ⟨775734, by rfl⟩ : syracuseStep 2068625 = 1551469) B1551469
theorem B2068643 : Blo 1377508 2068643 := bstep (se 1 (by rfl) ⟨1551482, by rfl⟩ : syracuseStep 2068643 = 3102965) B3102965
theorem B2068673 : Blo 1377508 2068673 := bstep (se 2 (by rfl) ⟨775752, by rfl⟩ : syracuseStep 2068673 = 1551505) B1551505
theorem B2068691 : Blo 1377508 2068691 := bstep (se 1 (by rfl) ⟨1551518, by rfl⟩ : syracuseStep 2068691 = 3103037) B3103037
theorem B4714723 : Blo 1377508 4714723 := bstep (se 1 (by rfl) ⟨3536042, by rfl⟩ : syracuseStep 4714723 = 7072085) B7072085
theorem B3100913 : Blo 1377508 3100913 := bstep (se 2 (by rfl) ⟨1162842, by rfl⟩ : syracuseStep 3100913 = 2325685) B2325685
theorem B2068721 : Blo 1377508 2068721 := bstep (se 2 (by rfl) ⟨775770, by rfl⟩ : syracuseStep 2068721 = 1551541) B1551541
theorem B3100931 : Blo 1377508 3100931 := bstep (se 1 (by rfl) ⟨2325698, by rfl⟩ : syracuseStep 3100931 = 4651397) B4651397
theorem B2068739 : Blo 1377508 2068739 := bstep (se 1 (by rfl) ⟨1551554, by rfl⟩ : syracuseStep 2068739 = 3103109) B3103109
theorem B2068769 : Blo 1377508 2068769 := bstep (se 2 (by rfl) ⟨775788, by rfl⟩ : syracuseStep 2068769 = 1551577) B1551577
theorem B2068787 : Blo 1377508 2068787 := bstep (se 1 (by rfl) ⟨1551590, by rfl⟩ : syracuseStep 2068787 = 3103181) B3103181
theorem B5230925 : Blo 1377508 5230925 := bstep (se 3 (by rfl) ⟨980798, by rfl⟩ : syracuseStep 5230925 = 1961597) B1961597
theorem B2068817 : Blo 1377508 2068817 := bstep (se 2 (by rfl) ⟨775806, by rfl⟩ : syracuseStep 2068817 = 1551613) B1551613
theorem B2068835 : Blo 1377508 2068835 := bstep (se 1 (by rfl) ⟨1551626, by rfl⟩ : syracuseStep 2068835 = 3103253) B3103253
theorem B2945411 : Blo 1377508 2945411 := bstep (se 1 (by rfl) ⟨2209058, by rfl⟩ : syracuseStep 2945411 = 4418117) B4418117
theorem B2068865 : Blo 1377508 2068865 := bstep (se 2 (by rfl) ⟨775824, by rfl⟩ : syracuseStep 2068865 = 1551649) B1551649
theorem B2068883 : Blo 1377508 2068883 := bstep (se 1 (by rfl) ⟨1551662, by rfl⟩ : syracuseStep 2068883 = 3103325) B3103325
theorem B2068913 : Blo 1377508 2068913 := bstep (se 2 (by rfl) ⟨775842, by rfl⟩ : syracuseStep 2068913 = 1551685) B1551685
theorem B2068931 : Blo 1377508 2068931 := bstep (se 1 (by rfl) ⟨1551698, by rfl⟩ : syracuseStep 2068931 = 3103397) B3103397
theorem B2068961 : Blo 1377508 2068961 := bstep (se 2 (by rfl) ⟨775860, by rfl⟩ : syracuseStep 2068961 = 1551721) B1551721
theorem B4649453 : Blo 1377508 4649453 := bstep (se 3 (by rfl) ⟨871772, by rfl⟩ : syracuseStep 4649453 = 1743545) B1743545
theorem B5591537 : Blo 1377508 5591537 := bstep (se 2 (by rfl) ⟨2096826, by rfl⟩ : syracuseStep 5591537 = 4193653) B4193653
theorem B2068979 : Blo 1377508 2068979 := bstep (se 1 (by rfl) ⟨1551734, by rfl⟩ : syracuseStep 2068979 = 3103469) B3103469
theorem B3101201 : Blo 1377508 3101201 := bstep (se 2 (by rfl) ⟨1162950, by rfl⟩ : syracuseStep 3101201 = 2325901) B2325901
theorem B2069009 : Blo 1377508 2069009 := bstep (se 2 (by rfl) ⟨775878, by rfl⟩ : syracuseStep 2069009 = 1551757) B1551757
theorem B4649507 : Blo 1377508 4649507 := bstep (se 1 (by rfl) ⟨3487130, by rfl⟩ : syracuseStep 4649507 = 6974261) B6974261
theorem B3101219 : Blo 1377508 3101219 := bstep (se 1 (by rfl) ⟨2325914, by rfl⟩ : syracuseStep 3101219 = 4651829) B4651829
theorem B2069027 : Blo 1377508 2069027 := bstep (se 1 (by rfl) ⟨1551770, by rfl⟩ : syracuseStep 2069027 = 3103541) B3103541
theorem B2069057 : Blo 1377508 2069057 := bstep (se 2 (by rfl) ⟨775896, by rfl⟩ : syracuseStep 2069057 = 1551793) B1551793
theorem B2069075 : Blo 1377508 2069075 := bstep (se 1 (by rfl) ⟨1551806, by rfl⟩ : syracuseStep 2069075 = 3103613) B3103613
theorem B3355235 : Blo 1377508 3355235 := bstep (se 1 (by rfl) ⟨2516426, by rfl⟩ : syracuseStep 3355235 = 5032853) B5032853
theorem B10629731 : Blo 1377508 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B2069105 : Blo 1377508 2069105 := bstep (se 2 (by rfl) ⟨775914, by rfl⟩ : syracuseStep 2069105 = 1551829) B1551829
theorem B2069123 : Blo 1377508 2069123 := bstep (se 1 (by rfl) ⟨1551842, by rfl⟩ : syracuseStep 2069123 = 3103685) B3103685
theorem B2069153 : Blo 1377508 2069153 := bstep (se 2 (by rfl) ⟨775932, by rfl⟩ : syracuseStep 2069153 = 1551865) B1551865
theorem B2069171 : Blo 1377508 2069171 := bstep (se 1 (by rfl) ⟨1551878, by rfl⟩ : syracuseStep 2069171 = 3103757) B3103757
theorem B6976205 : Blo 1377508 6976205 := bstep (se 3 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 6976205 = 2616077) B2616077
theorem B2069201 : Blo 1377508 2069201 := bstep (se 2 (by rfl) ⟨775950, by rfl⟩ : syracuseStep 2069201 = 1551901) B1551901
theorem B2069219 : Blo 1377508 2069219 := bstep (se 1 (by rfl) ⟨1551914, by rfl⟩ : syracuseStep 2069219 = 3103829) B3103829
theorem B2069249 : Blo 1377508 2069249 := bstep (se 2 (by rfl) ⟨775968, by rfl⟩ : syracuseStep 2069249 = 1551937) B1551937
theorem B1962787 : Blo 1377508 1962787 := bstep (se 1 (by rfl) ⟨1472090, by rfl⟩ : syracuseStep 1962787 = 2944181) B2944181
theorem B8835875 : Blo 1377508 8835875 := bstep (se 1 (by rfl) ⟨6626906, by rfl⟩ : syracuseStep 8835875 = 13253813) B13253813
theorem B4649777 : Blo 1377508 4649777 := bstep (se 2 (by rfl) ⟨1743666, by rfl⟩ : syracuseStep 4649777 = 3487333) B3487333
theorem B3101489 : Blo 1377508 3101489 := bstep (se 2 (by rfl) ⟨1163058, by rfl⟩ : syracuseStep 3101489 = 2326117) B2326117
theorem B3101507 : Blo 1377508 3101507 := bstep (se 1 (by rfl) ⟨2326130, by rfl⟩ : syracuseStep 3101507 = 4652261) B4652261
theorem B13243277 : Blo 1377508 13243277 := bstep (se 3 (by rfl) ⟨2483114, by rfl⟩ : syracuseStep 13243277 = 4966229) B4966229
theorem B3724177 : Blo 1377508 3724177 := bstep (se 2 (by rfl) ⟨1396566, by rfl⟩ : syracuseStep 3724177 = 2793133) B2793133
theorem B2618257 : Blo 1377508 2618257 := bstep (se 2 (by rfl) ⟨981846, by rfl⟩ : syracuseStep 2618257 = 1963693) B1963693
theorem B3101777 : Blo 1377508 3101777 := bstep (se 2 (by rfl) ⟨1163166, by rfl⟩ : syracuseStep 3101777 = 2326333) B2326333
theorem B7451747 : Blo 1377508 7451747 := bstep (se 1 (by rfl) ⟨5588810, by rfl⟩ : syracuseStep 7451747 = 11177621) B11177621
theorem B3101795 : Blo 1377508 3101795 := bstep (se 1 (by rfl) ⟨2326346, by rfl⟩ : syracuseStep 3101795 = 4652693) B4652693
theorem B5231729 : Blo 1377508 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B5174513 : Blo 1377508 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B7451939 : Blo 1377508 7451939 := bstep (se 1 (by rfl) ⟨5588954, by rfl⟩ : syracuseStep 7451939 = 11177909) B11177909
theorem B2618659 : Blo 1377508 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B7853381 : Blo 1377508 7853381 := bstep (se 4 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 7853381 = 1472509) B1472509
theorem B4650317 : Blo 1377508 4650317 := bstep (se 3 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 4650317 = 1743869) B1743869
theorem B2618705 : Blo 1377508 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B2209123 : Blo 1377508 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B3102065 : Blo 1377508 3102065 := bstep (se 2 (by rfl) ⟨1163274, by rfl⟩ : syracuseStep 3102065 = 2326549) B2326549
theorem B4650371 : Blo 1377508 4650371 := bstep (se 1 (by rfl) ⟨3487778, by rfl⟩ : syracuseStep 4650371 = 6975557) B6975557
theorem B3102083 : Blo 1377508 3102083 := bstep (se 1 (by rfl) ⟨2326562, by rfl⟩ : syracuseStep 3102083 = 4653125) B4653125
theorem B3487121 : Blo 1377508 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B2209187 : Blo 1377508 2209187 := bstep (se 1 (by rfl) ⟨1656890, by rfl⟩ : syracuseStep 2209187 = 3313781) B3313781
theorem B3487171 : Blo 1377508 3487171 := bstep (se 1 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 3487171 = 5230757) B5230757
theorem B3487313 : Blo 1377508 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B1472099 : Blo 1377508 1472099 := bstep (se 1 (by rfl) ⟨1104074, by rfl⟩ : syracuseStep 1472099 = 2208149) B2208149
theorem B3724931 : Blo 1377508 3724931 := bstep (se 1 (by rfl) ⟨2793698, by rfl⟩ : syracuseStep 3724931 = 5587397) B5587397
theorem B4650641 : Blo 1377508 4650641 := bstep (se 2 (by rfl) ⟨1743990, by rfl⟩ : syracuseStep 4650641 = 3487981) B3487981
theorem B3102353 : Blo 1377508 3102353 := bstep (se 2 (by rfl) ⟨1163382, by rfl⟩ : syracuseStep 3102353 = 2326765) B2326765
theorem B3102371 : Blo 1377508 3102371 := bstep (se 1 (by rfl) ⟨2326778, by rfl⟩ : syracuseStep 3102371 = 4653557) B4653557
theorem B5232397 : Blo 1377508 5232397 := bstep (se 3 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 5232397 = 1962149) B1962149
theorem B17667953 : Blo 1377508 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B4413325 : Blo 1377508 4413325 := bstep (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) B1654997
theorem B1963921 : Blo 1377508 1963921 := bstep (se 2 (by rfl) ⟨736470, by rfl⟩ : syracuseStep 1963921 = 1472941) B1472941
theorem B3102641 : Blo 1377508 3102641 := bstep (se 2 (by rfl) ⟨1163490, by rfl⟩ : syracuseStep 3102641 = 2326981) B2326981
theorem B3102659 : Blo 1377508 3102659 := bstep (se 1 (by rfl) ⟨2326994, by rfl⟩ : syracuseStep 3102659 = 4653989) B4653989
theorem B4478915 : Blo 1377508 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B1964017 : Blo 1377508 1964017 := bstep (se 2 (by rfl) ⟨736506, by rfl⟩ : syracuseStep 1964017 = 1473013) B1473013
theorem B12572813 : Blo 1377508 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B4651181 : Blo 1377508 4651181 := bstep (se 3 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 4651181 = 1744193) B1744193
theorem B2324659 : Blo 1377508 2324659 := bstep (se 1 (by rfl) ⟨1743494, by rfl⟩ : syracuseStep 2324659 = 3486989) B3486989
theorem B3102929 : Blo 1377508 3102929 := bstep (se 2 (by rfl) ⟨1163598, by rfl⟩ : syracuseStep 3102929 = 2327197) B2327197
theorem B4651235 : Blo 1377508 4651235 := bstep (se 1 (by rfl) ⟨3488426, by rfl⟩ : syracuseStep 4651235 = 6976853) B6976853
theorem B3102947 : Blo 1377508 3102947 := bstep (se 1 (by rfl) ⟨2327210, by rfl⟩ : syracuseStep 3102947 = 4654421) B4654421
theorem B2324801 : Blo 1377508 2324801 := bstep (se 2 (by rfl) ⟨871800, by rfl⟩ : syracuseStep 2324801 = 1743601) B1743601
theorem B1472851 : Blo 1377508 1472851 := bstep (se 1 (by rfl) ⟨1104638, by rfl⟩ : syracuseStep 1472851 = 2209277) B2209277
theorem B2324929 : Blo 1377508 2324929 := bstep (se 2 (by rfl) ⟨871848, by rfl⟩ : syracuseStep 2324929 = 1743697) B1743697
theorem B2324963 : Blo 1377508 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B5888483 : Blo 1377508 5888483 := bstep (se 1 (by rfl) ⟨4416362, by rfl⟩ : syracuseStep 5888483 = 8832725) B8832725
theorem B4651505 : Blo 1377508 4651505 := bstep (se 2 (by rfl) ⟨1744314, by rfl⟩ : syracuseStep 4651505 = 3488629) B3488629
theorem B3103217 : Blo 1377508 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B3103235 : Blo 1377508 3103235 := bstep (se 1 (by rfl) ⟨2327426, by rfl⟩ : syracuseStep 3103235 = 4654853) B4654853
theorem B1677859 : Blo 1377508 1677859 := bstep (se 1 (by rfl) ⟨1258394, by rfl⟩ : syracuseStep 1677859 = 2516789) B2516789
theorem B5233187 : Blo 1377508 5233187 := bstep (se 1 (by rfl) ⟨3924890, by rfl⟩ : syracuseStep 5233187 = 7849781) B7849781
theorem B4192813 : Blo 1377508 4192813 := bstep (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) B1572305
theorem B3488305 : Blo 1377508 3488305 := bstep (se 2 (by rfl) ⟨1308114, by rfl⟩ : syracuseStep 3488305 = 2616229) B2616229
theorem B2325091 : Blo 1377508 2325091 := bstep (se 1 (by rfl) ⟨1743818, by rfl⟩ : syracuseStep 2325091 = 3487637) B3487637
theorem B9935459 : Blo 1377508 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B10467953 : Blo 1377508 10467953 := bstep (se 2 (by rfl) ⟨3925482, by rfl⟩ : syracuseStep 10467953 = 7850965) B7850965
theorem B9427697 : Blo 1377508 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B2325233 : Blo 1377508 2325233 := bstep (se 2 (by rfl) ⟨871962, by rfl⟩ : syracuseStep 2325233 = 1743925) B1743925
theorem B8837873 : Blo 1377508 8837873 := bstep (se 2 (by rfl) ⟨3314202, by rfl⟩ : syracuseStep 8837873 = 6628405) B6628405
theorem B3103505 : Blo 1377508 3103505 := bstep (se 2 (by rfl) ⟨1163814, by rfl⟩ : syracuseStep 3103505 = 2327629) B2327629
theorem B3103523 : Blo 1377508 3103523 := bstep (se 1 (by rfl) ⟨2327642, by rfl⟩ : syracuseStep 3103523 = 4655285) B4655285
theorem B3488579 : Blo 1377508 3488579 := bstep (se 1 (by rfl) ⟨2616434, by rfl⟩ : syracuseStep 3488579 = 5232869) B5232869
theorem B3537745 : Blo 1377508 3537745 := bstep (se 2 (by rfl) ⟨1326654, by rfl⟩ : syracuseStep 3537745 = 2653309) B2653309
theorem B2325361 : Blo 1377508 2325361 := bstep (se 2 (by rfl) ⟨872010, by rfl⟩ : syracuseStep 2325361 = 1744021) B1744021
theorem B1743763 : Blo 1377508 1743763 := bstep (se 1 (by rfl) ⟨1307822, by rfl⟩ : syracuseStep 1743763 = 2615645) B2615645
theorem B2325395 : Blo 1377508 2325395 := bstep (se 1 (by rfl) ⟨1744046, by rfl⟩ : syracuseStep 2325395 = 3488093) B3488093
theorem B3357649 : Blo 1377508 3357649 := bstep (se 2 (by rfl) ⟨1259118, by rfl⟩ : syracuseStep 3357649 = 2518237) B2518237
theorem B1743859 : Blo 1377508 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B3488771 : Blo 1377508 3488771 := bstep (se 1 (by rfl) ⟨2616578, by rfl⟩ : syracuseStep 3488771 = 5233157) B5233157
theorem B4652045 : Blo 1377508 4652045 := bstep (se 3 (by rfl) ⟨872258, by rfl⟩ : syracuseStep 4652045 = 1744517) B1744517
theorem B2325523 : Blo 1377508 2325523 := bstep (se 1 (by rfl) ⟨1744142, by rfl⟩ : syracuseStep 2325523 = 3488285) B3488285
theorem B3103793 : Blo 1377508 3103793 := bstep (se 2 (by rfl) ⟨1163922, by rfl⟩ : syracuseStep 3103793 = 2327845) B2327845
theorem B4652099 : Blo 1377508 4652099 := bstep (se 1 (by rfl) ⟨3489074, by rfl⟩ : syracuseStep 4652099 = 6978149) B6978149
theorem B3103811 : Blo 1377508 3103811 := bstep (se 1 (by rfl) ⟨2327858, by rfl⟩ : syracuseStep 3103811 = 4655717) B4655717
theorem B30194801 : Blo 1377508 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B2325665 : Blo 1377508 2325665 := bstep (se 2 (by rfl) ⟨872124, by rfl⟩ : syracuseStep 2325665 = 1744249) B1744249
theorem B2096291 : Blo 1377508 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B5233841 : Blo 1377508 5233841 := bstep (se 2 (by rfl) ⟨1962690, by rfl⟩ : syracuseStep 5233841 = 3925381) B3925381
theorem B7847117 : Blo 1377508 7847117 := bstep (se 3 (by rfl) ⟨1471334, by rfl⟩ : syracuseStep 7847117 = 2942669) B2942669
theorem B2096371 : Blo 1377508 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B2325793 : Blo 1377508 2325793 := bstep (se 2 (by rfl) ⟨872172, by rfl⟩ : syracuseStep 2325793 = 1744345) B1744345
theorem B1989937 : Blo 1377508 1989937 := bstep (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) B1492453
theorem B2653489 : Blo 1377508 2653489 := bstep (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) B1990117
theorem B2325827 : Blo 1377508 2325827 := bstep (se 1 (by rfl) ⟨1744370, by rfl⟩ : syracuseStep 2325827 = 3488741) B3488741
theorem B4652369 : Blo 1377508 4652369 := bstep (se 2 (by rfl) ⟨1744638, by rfl⟩ : syracuseStep 4652369 = 3489277) B3489277
theorem B4654961 : Blo 1377508 4654961 := bstep (se 2 (by rfl) ⟨1745610, by rfl⟩ : syracuseStep 4654961 = 3491221) B3491221
theorem B2325955 : Blo 1377508 2325955 := bstep (se 1 (by rfl) ⟨1744466, by rfl⟩ : syracuseStep 2325955 = 3488933) B3488933
theorem B1744355 : Blo 1377508 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B6979121 : Blo 1377508 6979121 := bstep (se 2 (by rfl) ⟨2617170, by rfl⟩ : syracuseStep 6979121 = 5234341) B5234341
theorem B2326097 : Blo 1377508 2326097 := bstep (se 2 (by rfl) ⟨872286, by rfl⟩ : syracuseStep 2326097 = 1744573) B1744573
theorem B3923569 : Blo 1377508 3923569 := bstep (se 2 (by rfl) ⟨1471338, by rfl⟩ : syracuseStep 3923569 = 2942677) B2942677
theorem B2326225 : Blo 1377508 2326225 := bstep (se 2 (by rfl) ⟨872334, by rfl⟩ : syracuseStep 2326225 = 1744669) B1744669
theorem B2326259 : Blo 1377508 2326259 := bstep (se 1 (by rfl) ⟨1744694, by rfl⟩ : syracuseStep 2326259 = 3489389) B3489389
theorem B2096929 : Blo 1377508 2096929 := bstep (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) B1572697
theorem B5447459 : Blo 1377508 5447459 := bstep (se 1 (by rfl) ⟨4085594, by rfl⟩ : syracuseStep 5447459 = 8171189) B8171189
theorem B4652909 : Blo 1377508 4652909 := bstep (se 3 (by rfl) ⟨872420, by rfl⟩ : syracuseStep 4652909 = 1744841) B1744841
theorem B2326387 : Blo 1377508 2326387 := bstep (se 1 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 2326387 = 3489581) B3489581
theorem B4652963 : Blo 1377508 4652963 := bstep (se 1 (by rfl) ⟨3489722, by rfl⟩ : syracuseStep 4652963 = 6979445) B6979445
theorem B3489713 : Blo 1377508 3489713 := bstep (se 2 (by rfl) ⟨1308642, by rfl⟩ : syracuseStep 3489713 = 2617285) B2617285
theorem B3489763 : Blo 1377508 3489763 := bstep (se 1 (by rfl) ⟨2617322, by rfl⟩ : syracuseStep 3489763 = 5234645) B5234645
theorem B10469411 : Blo 1377508 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B5586995 : Blo 1377508 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B2326603 : Blo 1377508 2326603 := bstep (se 1 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 2326603 = 3489905) B3489905
theorem B11780275 : Blo 1377508 11780275 := bstep (se 1 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 11780275 = 17670413) B17670413
theorem B1654987 : Blo 1377508 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B2326745 : Blo 1377508 2326745 := bstep (se 2 (by rfl) ⟨872529, by rfl⟩ : syracuseStep 2326745 = 1745059) B1745059
theorem B3727691 : Blo 1377508 3727691 := bstep (se 1 (by rfl) ⟨2795768, by rfl⟩ : syracuseStep 3727691 = 5591537) B5591537
theorem B2326873 : Blo 1377508 2326873 := bstep (se 2 (by rfl) ⟨872577, by rfl⟩ : syracuseStep 2326873 = 1745155) B1745155
theorem B7848323 : Blo 1377508 7848323 := bstep (se 1 (by rfl) ⟨5886242, by rfl⟩ : syracuseStep 7848323 = 11772485) B11772485
theorem B3146123 : Blo 1377508 3146123 := bstep (se 1 (by rfl) ⟨2359592, by rfl⟩ : syracuseStep 3146123 = 4719185) B4719185
theorem B2236823 : Blo 1377508 2236823 := bstep (se 1 (by rfl) ⟨1677617, by rfl⟩ : syracuseStep 2236823 = 3355235) B3355235
theorem B3490199 : Blo 1377508 3490199 := bstep (se 1 (by rfl) ⟨2617649, by rfl⟩ : syracuseStep 3490199 = 5235299) B5235299
theorem B5890583 : Blo 1377508 5890583 := bstep (se 1 (by rfl) ⟨4417937, by rfl⟩ : syracuseStep 5890583 = 8835875) B8835875
theorem B4653719 : Blo 1377508 4653719 := bstep (se 1 (by rfl) ⟨3490289, by rfl⟩ : syracuseStep 4653719 = 6980579) B6980579
theorem B4416221 : Blo 1377508 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B6980417 : Blo 1377508 6980417 := bstep (se 2 (by rfl) ⟨2617656, by rfl⟩ : syracuseStep 6980417 = 5235313) B5235313
theorem B3449675 : Blo 1377508 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B5235587 : Blo 1377508 5235587 := bstep (se 1 (by rfl) ⟨3926690, by rfl⟩ : syracuseStep 5235587 = 7853381) B7853381
theorem B1745803 : Blo 1377508 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B2327447 : Blo 1377508 2327447 := bstep (se 1 (by rfl) ⟨1745585, by rfl⟩ : syracuseStep 2327447 = 3491171) B3491171
theorem B22348817 : Blo 1377508 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B2327575 : Blo 1377508 2327575 := bstep (se 1 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 2327575 = 3491363) B3491363
theorem B4654259 : Blo 1377508 4654259 := bstep (se 1 (by rfl) ⟨3490694, by rfl⟩ : syracuseStep 4654259 = 6981389) B6981389
theorem B4965569 : Blo 1377508 4965569 := bstep (se 2 (by rfl) ⟨1862088, by rfl⟩ : syracuseStep 4965569 = 3724177) B3724177
theorem B3491009 : Blo 1377508 3491009 := bstep (se 2 (by rfl) ⟨1309128, by rfl⟩ : syracuseStep 3491009 = 2618257) B2618257
theorem B1377515 : Blo 1377508 1377515 := bstep (se 1 (by rfl) ⟨1033136, by rfl⟩ : syracuseStep 1377515 = 2066273) B2066273
theorem B1377527 : Blo 1377508 1377527 := bstep (se 1 (by rfl) ⟨1033145, by rfl⟩ : syracuseStep 1377527 = 2066291) B2066291
theorem B1377547 : Blo 1377508 1377547 := bstep (se 1 (by rfl) ⟨1033160, by rfl⟩ : syracuseStep 1377547 = 2066321) B2066321
theorem B1377559 : Blo 1377508 1377559 := bstep (se 1 (by rfl) ⟨1033169, by rfl⟩ : syracuseStep 1377559 = 2066339) B2066339
theorem B1377579 : Blo 1377508 1377579 := bstep (se 1 (by rfl) ⟨1033184, by rfl⟩ : syracuseStep 1377579 = 2066369) B2066369
theorem B1377591 : Blo 1377508 1377591 := bstep (se 1 (by rfl) ⟨1033193, by rfl⟩ : syracuseStep 1377591 = 2066387) B2066387
theorem B5039425 : Blo 1377508 5039425 := bstep (se 2 (by rfl) ⟨1889784, by rfl⟩ : syracuseStep 5039425 = 3779569) B3779569
theorem B1377611 : Blo 1377508 1377611 := bstep (se 1 (by rfl) ⟨1033208, by rfl⟩ : syracuseStep 1377611 = 2066417) B2066417
theorem B1377623 : Blo 1377508 1377623 := bstep (se 1 (by rfl) ⟨1033217, by rfl⟩ : syracuseStep 1377623 = 2066435) B2066435
theorem B1377643 : Blo 1377508 1377643 := bstep (se 1 (by rfl) ⟨1033232, by rfl⟩ : syracuseStep 1377643 = 2066465) B2066465
theorem B1377655 : Blo 1377508 1377655 := bstep (se 1 (by rfl) ⟨1033241, by rfl⟩ : syracuseStep 1377655 = 2066483) B2066483
theorem B1377675 : Blo 1377508 1377675 := bstep (se 1 (by rfl) ⟨1033256, by rfl⟩ : syracuseStep 1377675 = 2066513) B2066513
theorem B1377687 : Blo 1377508 1377687 := bstep (se 1 (by rfl) ⟨1033265, by rfl⟩ : syracuseStep 1377687 = 2066531) B2066531
theorem B1377707 : Blo 1377508 1377707 := bstep (se 1 (by rfl) ⟨1033280, by rfl⟩ : syracuseStep 1377707 = 2066561) B2066561
theorem B5965235 : Blo 1377508 5965235 := bstep (se 1 (by rfl) ⟨4473926, by rfl⟩ : syracuseStep 5965235 = 8947853) B8947853
theorem B8381875 : Blo 1377508 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B1377719 : Blo 1377508 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B4654529 : Blo 1377508 4654529 := bstep (se 2 (by rfl) ⟨1745448, by rfl⟩ : syracuseStep 4654529 = 3490897) B3490897
theorem B1377739 : Blo 1377508 1377739 := bstep (se 1 (by rfl) ⟨1033304, by rfl⟩ : syracuseStep 1377739 = 2066609) B2066609
theorem B1377751 : Blo 1377508 1377751 := bstep (se 1 (by rfl) ⟨1033313, by rfl⟩ : syracuseStep 1377751 = 2066627) B2066627
theorem B1377771 : Blo 1377508 1377771 := bstep (se 1 (by rfl) ⟨1033328, by rfl⟩ : syracuseStep 1377771 = 2066657) B2066657
theorem B1377783 : Blo 1377508 1377783 := bstep (se 1 (by rfl) ⟨1033337, by rfl⟩ : syracuseStep 1377783 = 2066675) B2066675
theorem B1377803 : Blo 1377508 1377803 := bstep (se 1 (by rfl) ⟨1033352, by rfl⟩ : syracuseStep 1377803 = 2066705) B2066705
theorem B47777293 : Blo 1377508 47777293 := bstep (se 3 (by rfl) ⟨8958242, by rfl⟩ : syracuseStep 47777293 = 17916485) B17916485
theorem B1377815 : Blo 1377508 1377815 := bstep (se 1 (by rfl) ⟨1033361, by rfl⟩ : syracuseStep 1377815 = 2066723) B2066723
theorem B1549867 : Blo 1377508 1549867 := bstep (se 1 (by rfl) ⟨1162400, by rfl⟩ : syracuseStep 1549867 = 2324801) B2324801
theorem B6620717 : Blo 1377508 6620717 := bstep (se 3 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 6620717 = 2482769) B2482769
theorem B1377835 : Blo 1377508 1377835 := bstep (se 1 (by rfl) ⟨1033376, by rfl⟩ : syracuseStep 1377835 = 2066753) B2066753
theorem B1377847 : Blo 1377508 1377847 := bstep (se 1 (by rfl) ⟨1033385, by rfl⟩ : syracuseStep 1377847 = 2066771) B2066771
theorem B1377867 : Blo 1377508 1377867 := bstep (se 1 (by rfl) ⟨1033400, by rfl⟩ : syracuseStep 1377867 = 2066801) B2066801
theorem B1377879 : Blo 1377508 1377879 := bstep (se 1 (by rfl) ⟨1033409, by rfl⟩ : syracuseStep 1377879 = 2066819) B2066819
theorem B28345949 : Blo 1377508 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B3925597 : Blo 1377508 3925597 := bstep (se 3 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 3925597 = 1472099) B1472099
theorem B1377899 : Blo 1377508 1377899 := bstep (se 1 (by rfl) ⟨1033424, by rfl⟩ : syracuseStep 1377899 = 2066849) B2066849
theorem B1377911 : Blo 1377508 1377911 := bstep (se 1 (by rfl) ⟨1033433, by rfl⟩ : syracuseStep 1377911 = 2066867) B2066867
theorem B1377931 : Blo 1377508 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B1549975 : Blo 1377508 1549975 := bstep (se 1 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 1549975 = 2324963) B2324963
theorem B1377943 : Blo 1377508 1377943 := bstep (se 1 (by rfl) ⟨1033457, by rfl⟩ : syracuseStep 1377943 = 2066915) B2066915
theorem B3925655 : Blo 1377508 3925655 := bstep (se 1 (by rfl) ⟨2944241, by rfl⟩ : syracuseStep 3925655 = 5888483) B5888483
theorem B2795161 : Blo 1377508 2795161 := bstep (se 2 (by rfl) ⟨1048185, by rfl⟩ : syracuseStep 2795161 = 2096371) B2096371
theorem B1377963 : Blo 1377508 1377963 := bstep (se 1 (by rfl) ⟨1033472, by rfl⟩ : syracuseStep 1377963 = 2066945) B2066945
theorem B1377975 : Blo 1377508 1377975 := bstep (se 1 (by rfl) ⟨1033481, by rfl⟩ : syracuseStep 1377975 = 2066963) B2066963
theorem B1377995 : Blo 1377508 1377995 := bstep (se 1 (by rfl) ⟨1033496, by rfl⟩ : syracuseStep 1377995 = 2066993) B2066993
theorem B1378007 : Blo 1377508 1378007 := bstep (se 1 (by rfl) ⟨1033505, by rfl⟩ : syracuseStep 1378007 = 2067011) B2067011
theorem B3491545 : Blo 1377508 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B1378027 : Blo 1377508 1378027 := bstep (se 1 (by rfl) ⟨1033520, by rfl⟩ : syracuseStep 1378027 = 2067041) B2067041
theorem B1378039 : Blo 1377508 1378039 := bstep (se 1 (by rfl) ⟨1033529, by rfl⟩ : syracuseStep 1378039 = 2067059) B2067059
theorem B18867973 : Blo 1377508 18867973 := bstep (se 4 (by rfl) ⟨1768872, by rfl⟩ : syracuseStep 18867973 = 3537745) B3537745
theorem B1378059 : Blo 1377508 1378059 := bstep (se 1 (by rfl) ⟨1033544, by rfl⟩ : syracuseStep 1378059 = 2067089) B2067089
theorem B1378071 : Blo 1377508 1378071 := bstep (se 1 (by rfl) ⟨1033553, by rfl⟩ : syracuseStep 1378071 = 2067107) B2067107
theorem B1378091 : Blo 1377508 1378091 := bstep (se 1 (by rfl) ⟨1033568, by rfl⟩ : syracuseStep 1378091 = 2067137) B2067137
theorem B1378103 : Blo 1377508 1378103 := bstep (se 1 (by rfl) ⟨1033577, by rfl⟩ : syracuseStep 1378103 = 2067155) B2067155
theorem B6285131 : Blo 1377508 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B1550155 : Blo 1377508 1550155 := bstep (se 1 (by rfl) ⟨1162616, by rfl⟩ : syracuseStep 1550155 = 2325233) B2325233
theorem B1378123 : Blo 1377508 1378123 := bstep (se 1 (by rfl) ⟨1033592, by rfl⟩ : syracuseStep 1378123 = 2067185) B2067185
theorem B3311435 : Blo 1377508 3311435 := bstep (se 1 (by rfl) ⟨2483576, by rfl⟩ : syracuseStep 3311435 = 4967153) B4967153
theorem B5891915 : Blo 1377508 5891915 := bstep (se 1 (by rfl) ⟨4418936, by rfl⟩ : syracuseStep 5891915 = 8837873) B8837873
theorem B1378135 : Blo 1377508 1378135 := bstep (se 1 (by rfl) ⟨1033601, by rfl⟩ : syracuseStep 1378135 = 2067203) B2067203
theorem B1378155 : Blo 1377508 1378155 := bstep (se 1 (by rfl) ⟨1033616, by rfl⟩ : syracuseStep 1378155 = 2067233) B2067233
theorem B1378167 : Blo 1377508 1378167 := bstep (se 1 (by rfl) ⟨1033625, by rfl⟩ : syracuseStep 1378167 = 2067251) B2067251
theorem B17672053 : Blo 1377508 17672053 := bstep (se 5 (by rfl) ⟨828377, by rfl⟩ : syracuseStep 17672053 = 1656755) B1656755
theorem B2066315 : Blo 1377508 2066315 := bstep (se 1 (by rfl) ⟨1549736, by rfl⟩ : syracuseStep 2066315 = 3099473) B3099473
theorem B1378187 : Blo 1377508 1378187 := bstep (se 1 (by rfl) ⟨1033640, by rfl⟩ : syracuseStep 1378187 = 2067281) B2067281
theorem B2066327 : Blo 1377508 2066327 := bstep (se 1 (by rfl) ⟨1549745, by rfl⟩ : syracuseStep 2066327 = 3099491) B3099491
theorem B1378199 : Blo 1377508 1378199 := bstep (se 1 (by rfl) ⟨1033649, by rfl⟩ : syracuseStep 1378199 = 2067299) B2067299
theorem B1378219 : Blo 1377508 1378219 := bstep (se 1 (by rfl) ⟨1033664, by rfl⟩ : syracuseStep 1378219 = 2067329) B2067329
theorem B2983859 : Blo 1377508 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B1550263 : Blo 1377508 1550263 := bstep (se 1 (by rfl) ⟨1162697, by rfl⟩ : syracuseStep 1550263 = 2325395) B2325395
theorem B1378231 : Blo 1377508 1378231 := bstep (se 1 (by rfl) ⟨1033673, by rfl⟩ : syracuseStep 1378231 = 2067347) B2067347
theorem B1378251 : Blo 1377508 1378251 := bstep (se 1 (by rfl) ⟨1033688, by rfl⟩ : syracuseStep 1378251 = 2067377) B2067377
theorem B1378263 : Blo 1377508 1378263 := bstep (se 1 (by rfl) ⟨1033697, by rfl⟩ : syracuseStep 1378263 = 2067395) B2067395
theorem B2615257 : Blo 1377508 2615257 := bstep (se 2 (by rfl) ⟨980721, by rfl⟩ : syracuseStep 2615257 = 1961443) B1961443
theorem B2066393 : Blo 1377508 2066393 := bstep (se 2 (by rfl) ⟨774897, by rfl⟩ : syracuseStep 2066393 = 1549795) B1549795
theorem B4655069 : Blo 1377508 4655069 := bstep (se 3 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 4655069 = 1745651) B1745651
theorem B1378283 : Blo 1377508 1378283 := bstep (se 1 (by rfl) ⟨1033712, by rfl⟩ : syracuseStep 1378283 = 2067425) B2067425
theorem B3065843 : Blo 1377508 3065843 := bstep (se 1 (by rfl) ⟨2299382, by rfl⟩ : syracuseStep 3065843 = 4598765) B4598765
theorem B1378295 : Blo 1377508 1378295 := bstep (se 1 (by rfl) ⟨1033721, by rfl⟩ : syracuseStep 1378295 = 2067443) B2067443
theorem B1378315 : Blo 1377508 1378315 := bstep (se 1 (by rfl) ⟨1033736, by rfl⟩ : syracuseStep 1378315 = 2067473) B2067473
theorem B1378327 : Blo 1377508 1378327 := bstep (se 1 (by rfl) ⟨1033745, by rfl⟩ : syracuseStep 1378327 = 2067491) B2067491
theorem B1378347 : Blo 1377508 1378347 := bstep (se 1 (by rfl) ⟨1033760, by rfl⟩ : syracuseStep 1378347 = 2067521) B2067521
theorem B1378359 : Blo 1377508 1378359 := bstep (se 1 (by rfl) ⟨1033769, by rfl⟩ : syracuseStep 1378359 = 2067539) B2067539
theorem B20129867 : Blo 1377508 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B2066507 : Blo 1377508 2066507 := bstep (se 1 (by rfl) ⟨1549880, by rfl⟩ : syracuseStep 2066507 = 3099761) B3099761
theorem B1378379 : Blo 1377508 1378379 := bstep (se 1 (by rfl) ⟨1033784, by rfl⟩ : syracuseStep 1378379 = 2067569) B2067569
theorem B2066519 : Blo 1377508 2066519 := bstep (se 1 (by rfl) ⟨1549889, by rfl⟩ : syracuseStep 2066519 = 3099779) B3099779
theorem B1378391 : Blo 1377508 1378391 := bstep (se 1 (by rfl) ⟨1033793, by rfl⟩ : syracuseStep 1378391 = 2067587) B2067587
theorem B1550443 : Blo 1377508 1550443 := bstep (se 1 (by rfl) ⟨1162832, by rfl⟩ : syracuseStep 1550443 = 2325665) B2325665
theorem B1378411 : Blo 1377508 1378411 := bstep (se 1 (by rfl) ⟨1033808, by rfl⟩ : syracuseStep 1378411 = 2067617) B2067617
theorem B1378423 : Blo 1377508 1378423 := bstep (se 1 (by rfl) ⟨1033817, by rfl⟩ : syracuseStep 1378423 = 2067635) B2067635
theorem B1378443 : Blo 1377508 1378443 := bstep (se 1 (by rfl) ⟨1033832, by rfl⟩ : syracuseStep 1378443 = 2067665) B2067665
theorem B1378455 : Blo 1377508 1378455 := bstep (se 1 (by rfl) ⟨1033841, by rfl⟩ : syracuseStep 1378455 = 2067683) B2067683
theorem B23873687 : Blo 1377508 23873687 := bstep (se 1 (by rfl) ⟨17905265, by rfl⟩ : syracuseStep 23873687 = 35810531) B35810531
theorem B2066585 : Blo 1377508 2066585 := bstep (se 2 (by rfl) ⟨774969, by rfl⟩ : syracuseStep 2066585 = 1549939) B1549939
theorem B1378475 : Blo 1377508 1378475 := bstep (se 1 (by rfl) ⟨1033856, by rfl⟩ : syracuseStep 1378475 = 2067713) B2067713
theorem B1378487 : Blo 1377508 1378487 := bstep (se 1 (by rfl) ⟨1033865, by rfl⟩ : syracuseStep 1378487 = 2067731) B2067731
theorem B1378507 : Blo 1377508 1378507 := bstep (se 1 (by rfl) ⟨1033880, by rfl⟩ : syracuseStep 1378507 = 2067761) B2067761
theorem B1550551 : Blo 1377508 1550551 := bstep (se 1 (by rfl) ⟨1162913, by rfl⟩ : syracuseStep 1550551 = 2325827) B2325827
theorem B1378519 : Blo 1377508 1378519 := bstep (se 1 (by rfl) ⟨1033889, by rfl⟩ : syracuseStep 1378519 = 2067779) B2067779
theorem B1378539 : Blo 1377508 1378539 := bstep (se 1 (by rfl) ⟨1033904, by rfl⟩ : syracuseStep 1378539 = 2067809) B2067809
theorem B1378551 : Blo 1377508 1378551 := bstep (se 1 (by rfl) ⟨1033913, by rfl⟩ : syracuseStep 1378551 = 2067827) B2067827
theorem B2066699 : Blo 1377508 2066699 := bstep (se 1 (by rfl) ⟨1550024, by rfl⟩ : syracuseStep 2066699 = 3100049) B3100049
theorem B1378571 : Blo 1377508 1378571 := bstep (se 1 (by rfl) ⟨1033928, by rfl⟩ : syracuseStep 1378571 = 2067857) B2067857
theorem B2066711 : Blo 1377508 2066711 := bstep (se 1 (by rfl) ⟨1550033, by rfl⟩ : syracuseStep 2066711 = 3100067) B3100067
theorem B1378583 : Blo 1377508 1378583 := bstep (se 1 (by rfl) ⟨1033937, by rfl⟩ : syracuseStep 1378583 = 2067875) B2067875
theorem B1378603 : Blo 1377508 1378603 := bstep (se 1 (by rfl) ⟨1033952, by rfl⟩ : syracuseStep 1378603 = 2067905) B2067905
theorem B1378615 : Blo 1377508 1378615 := bstep (se 1 (by rfl) ⟨1033961, by rfl⟩ : syracuseStep 1378615 = 2067923) B2067923
theorem B1378635 : Blo 1377508 1378635 := bstep (se 1 (by rfl) ⟨1033976, by rfl⟩ : syracuseStep 1378635 = 2067953) B2067953
theorem B1378647 : Blo 1377508 1378647 := bstep (se 1 (by rfl) ⟨1033985, by rfl⟩ : syracuseStep 1378647 = 2067971) B2067971
theorem B2066777 : Blo 1377508 2066777 := bstep (se 2 (by rfl) ⟨775041, by rfl⟩ : syracuseStep 2066777 = 1550083) B1550083
theorem B1378667 : Blo 1377508 1378667 := bstep (se 1 (by rfl) ⟨1034000, by rfl⟩ : syracuseStep 1378667 = 2068001) B2068001
theorem B1378679 : Blo 1377508 1378679 := bstep (se 1 (by rfl) ⟨1034009, by rfl⟩ : syracuseStep 1378679 = 2068019) B2068019
theorem B2795905 : Blo 1377508 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B1550731 : Blo 1377508 1550731 := bstep (se 1 (by rfl) ⟨1163048, by rfl⟩ : syracuseStep 1550731 = 2326097) B2326097
theorem B1378699 : Blo 1377508 1378699 := bstep (se 1 (by rfl) ⟨1034024, by rfl⟩ : syracuseStep 1378699 = 2068049) B2068049
theorem B5892497 : Blo 1377508 5892497 := bstep (se 2 (by rfl) ⟨2209686, by rfl⟩ : syracuseStep 5892497 = 4419373) B4419373
theorem B1378711 : Blo 1377508 1378711 := bstep (se 1 (by rfl) ⟨1034033, by rfl⟩ : syracuseStep 1378711 = 2068067) B2068067
theorem B1378731 : Blo 1377508 1378731 := bstep (se 1 (by rfl) ⟨1034048, by rfl⟩ : syracuseStep 1378731 = 2068097) B2068097
theorem B1378743 : Blo 1377508 1378743 := bstep (se 1 (by rfl) ⟨1034057, by rfl⟩ : syracuseStep 1378743 = 2068115) B2068115
theorem B2066891 : Blo 1377508 2066891 := bstep (se 1 (by rfl) ⟨1550168, by rfl⟩ : syracuseStep 2066891 = 3100337) B3100337
theorem B1378763 : Blo 1377508 1378763 := bstep (se 1 (by rfl) ⟨1034072, by rfl⟩ : syracuseStep 1378763 = 2068145) B2068145
theorem B2066903 : Blo 1377508 2066903 := bstep (se 1 (by rfl) ⟨1550177, by rfl⟩ : syracuseStep 2066903 = 3100355) B3100355
theorem B1378775 : Blo 1377508 1378775 := bstep (se 1 (by rfl) ⟨1034081, by rfl⟩ : syracuseStep 1378775 = 2068163) B2068163
theorem B1378795 : Blo 1377508 1378795 := bstep (se 1 (by rfl) ⟨1034096, by rfl⟩ : syracuseStep 1378795 = 2068193) B2068193
theorem B1550839 : Blo 1377508 1550839 := bstep (se 1 (by rfl) ⟨1163129, by rfl⟩ : syracuseStep 1550839 = 2326259) B2326259
theorem B1378807 : Blo 1377508 1378807 := bstep (se 1 (by rfl) ⟨1034105, by rfl⟩ : syracuseStep 1378807 = 2068211) B2068211
theorem B1378827 : Blo 1377508 1378827 := bstep (se 1 (by rfl) ⟨1034120, by rfl⟩ : syracuseStep 1378827 = 2068241) B2068241
theorem B5884433 : Blo 1377508 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B3631639 : Blo 1377508 3631639 := bstep (se 1 (by rfl) ⟨2723729, by rfl⟩ : syracuseStep 3631639 = 5447459) B5447459
theorem B1378839 : Blo 1377508 1378839 := bstep (se 1 (by rfl) ⟨1034129, by rfl⟩ : syracuseStep 1378839 = 2068259) B2068259
theorem B2066969 : Blo 1377508 2066969 := bstep (se 2 (by rfl) ⟨775113, by rfl⟩ : syracuseStep 2066969 = 1550227) B1550227
theorem B1378859 : Blo 1377508 1378859 := bstep (se 1 (by rfl) ⟨1034144, by rfl⟩ : syracuseStep 1378859 = 2068289) B2068289
theorem B1378871 : Blo 1377508 1378871 := bstep (se 1 (by rfl) ⟨1034153, by rfl⟩ : syracuseStep 1378871 = 2068307) B2068307
theorem B1378891 : Blo 1377508 1378891 := bstep (se 1 (by rfl) ⟨1034168, by rfl⟩ : syracuseStep 1378891 = 2068337) B2068337
theorem B1378903 : Blo 1377508 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B1378923 : Blo 1377508 1378923 := bstep (se 1 (by rfl) ⟨1034192, by rfl⟩ : syracuseStep 1378923 = 2068385) B2068385
theorem B1378935 : Blo 1377508 1378935 := bstep (se 1 (by rfl) ⟨1034201, by rfl⟩ : syracuseStep 1378935 = 2068403) B2068403
theorem B2067083 : Blo 1377508 2067083 := bstep (se 1 (by rfl) ⟨1550312, by rfl⟩ : syracuseStep 2067083 = 3100625) B3100625
theorem B1378955 : Blo 1377508 1378955 := bstep (se 1 (by rfl) ⟨1034216, by rfl⟩ : syracuseStep 1378955 = 2068433) B2068433
theorem B2067095 : Blo 1377508 2067095 := bstep (se 1 (by rfl) ⟨1550321, by rfl⟩ : syracuseStep 2067095 = 3100643) B3100643
theorem B1378967 : Blo 1377508 1378967 := bstep (se 1 (by rfl) ⟨1034225, by rfl⟩ : syracuseStep 1378967 = 2068451) B2068451
theorem B1551019 : Blo 1377508 1551019 := bstep (se 1 (by rfl) ⟨1163264, by rfl⟩ : syracuseStep 1551019 = 2326529) B2326529
theorem B1378987 : Blo 1377508 1378987 := bstep (se 1 (by rfl) ⟨1034240, by rfl⟩ : syracuseStep 1378987 = 2068481) B2068481
theorem B1378999 : Blo 1377508 1378999 := bstep (se 1 (by rfl) ⟨1034249, by rfl⟩ : syracuseStep 1378999 = 2068499) B2068499
theorem B1379019 : Blo 1377508 1379019 := bstep (se 1 (by rfl) ⟨1034264, by rfl⟩ : syracuseStep 1379019 = 2068529) B2068529
theorem B1379031 : Blo 1377508 1379031 := bstep (se 1 (by rfl) ⟨1034273, by rfl⟩ : syracuseStep 1379031 = 2068547) B2068547
theorem B2067161 : Blo 1377508 2067161 := bstep (se 2 (by rfl) ⟨775185, by rfl⟩ : syracuseStep 2067161 = 1550371) B1550371
theorem B6982361 : Blo 1377508 6982361 := bstep (se 2 (by rfl) ⟨2618385, by rfl⟩ : syracuseStep 6982361 = 5236771) B5236771
theorem B1379051 : Blo 1377508 1379051 := bstep (se 1 (by rfl) ⟨1034288, by rfl⟩ : syracuseStep 1379051 = 2068577) B2068577
theorem B1379063 : Blo 1377508 1379063 := bstep (se 1 (by rfl) ⟨1034297, by rfl⟩ : syracuseStep 1379063 = 2068595) B2068595
theorem B1379083 : Blo 1377508 1379083 := bstep (se 1 (by rfl) ⟨1034312, by rfl⟩ : syracuseStep 1379083 = 2068625) B2068625
theorem B1551127 : Blo 1377508 1551127 := bstep (se 1 (by rfl) ⟨1163345, by rfl⟩ : syracuseStep 1551127 = 2326691) B2326691
theorem B1379095 : Blo 1377508 1379095 := bstep (se 1 (by rfl) ⟨1034321, by rfl⟩ : syracuseStep 1379095 = 2068643) B2068643
theorem B1379115 : Blo 1377508 1379115 := bstep (se 1 (by rfl) ⟨1034336, by rfl⟩ : syracuseStep 1379115 = 2068673) B2068673
theorem B1379127 : Blo 1377508 1379127 := bstep (se 1 (by rfl) ⟨1034345, by rfl⟩ : syracuseStep 1379127 = 2068691) B2068691
theorem B10464065 : Blo 1377508 10464065 := bstep (se 2 (by rfl) ⟨3924024, by rfl⟩ : syracuseStep 10464065 = 7848049) B7848049
theorem B2067275 : Blo 1377508 2067275 := bstep (se 1 (by rfl) ⟨1550456, by rfl⟩ : syracuseStep 2067275 = 3100913) B3100913
theorem B1379147 : Blo 1377508 1379147 := bstep (se 1 (by rfl) ⟨1034360, by rfl⟩ : syracuseStep 1379147 = 2068721) B2068721
theorem B2067287 : Blo 1377508 2067287 := bstep (se 1 (by rfl) ⟨1550465, by rfl⟩ : syracuseStep 2067287 = 3100931) B3100931
theorem B1379159 : Blo 1377508 1379159 := bstep (se 1 (by rfl) ⟨1034369, by rfl⟩ : syracuseStep 1379159 = 2068739) B2068739
theorem B3926873 : Blo 1377508 3926873 := bstep (se 2 (by rfl) ⟨1472577, by rfl⟩ : syracuseStep 3926873 = 2945155) B2945155
theorem B7457629 : Blo 1377508 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B1379179 : Blo 1377508 1379179 := bstep (se 1 (by rfl) ⟨1034384, by rfl⟩ : syracuseStep 1379179 = 2068769) B2068769
theorem B1379191 : Blo 1377508 1379191 := bstep (se 1 (by rfl) ⟨1034393, by rfl⟩ : syracuseStep 1379191 = 2068787) B2068787
theorem B5303171 : Blo 1377508 5303171 := bstep (se 1 (by rfl) ⟨3977378, by rfl⟩ : syracuseStep 5303171 = 7954757) B7954757
theorem B1379211 : Blo 1377508 1379211 := bstep (se 1 (by rfl) ⟨1034408, by rfl⟩ : syracuseStep 1379211 = 2068817) B2068817
theorem B1379223 : Blo 1377508 1379223 := bstep (se 1 (by rfl) ⟨1034417, by rfl⟩ : syracuseStep 1379223 = 2068835) B2068835
theorem B3099545 : Blo 1377508 3099545 := bstep (se 2 (by rfl) ⟨1162329, by rfl⟩ : syracuseStep 3099545 = 2324659) B2324659
theorem B2067353 : Blo 1377508 2067353 := bstep (se 2 (by rfl) ⟨775257, by rfl⟩ : syracuseStep 2067353 = 1550515) B1550515
theorem B1379243 : Blo 1377508 1379243 := bstep (se 1 (by rfl) ⟨1034432, by rfl⟩ : syracuseStep 1379243 = 2068865) B2068865
theorem B1379255 : Blo 1377508 1379255 := bstep (se 1 (by rfl) ⟨1034441, by rfl⟩ : syracuseStep 1379255 = 2068883) B2068883
theorem B1551307 : Blo 1377508 1551307 := bstep (se 1 (by rfl) ⟨1163480, by rfl⟩ : syracuseStep 1551307 = 2326961) B2326961
theorem B3926987 : Blo 1377508 3926987 := bstep (se 1 (by rfl) ⟨2945240, by rfl⟩ : syracuseStep 3926987 = 5890481) B5890481
theorem B1379275 : Blo 1377508 1379275 := bstep (se 1 (by rfl) ⟨1034456, by rfl⟩ : syracuseStep 1379275 = 2068913) B2068913
theorem B6286297 : Blo 1377508 6286297 := bstep (se 2 (by rfl) ⟨2357361, by rfl⟩ : syracuseStep 6286297 = 4714723) B4714723
theorem B1379287 : Blo 1377508 1379287 := bstep (se 1 (by rfl) ⟨1034465, by rfl⟩ : syracuseStep 1379287 = 2068931) B2068931
theorem B3779545 : Blo 1377508 3779545 := bstep (se 2 (by rfl) ⟨1417329, by rfl⟩ : syracuseStep 3779545 = 2834659) B2834659
theorem B1379307 : Blo 1377508 1379307 := bstep (se 1 (by rfl) ⟨1034480, by rfl⟩ : syracuseStep 1379307 = 2068961) B2068961
theorem B3099635 : Blo 1377508 3099635 := bstep (se 1 (by rfl) ⟨2324726, by rfl⟩ : syracuseStep 3099635 = 4649453) B4649453
theorem B1379319 : Blo 1377508 1379319 := bstep (se 1 (by rfl) ⟨1034489, by rfl⟩ : syracuseStep 1379319 = 2068979) B2068979
theorem B2067467 : Blo 1377508 2067467 := bstep (se 1 (by rfl) ⟨1550600, by rfl⟩ : syracuseStep 2067467 = 3101201) B3101201
theorem B1379339 : Blo 1377508 1379339 := bstep (se 1 (by rfl) ⟨1034504, by rfl⟩ : syracuseStep 1379339 = 2069009) B2069009
theorem B3099671 : Blo 1377508 3099671 := bstep (se 1 (by rfl) ⟨2324753, by rfl⟩ : syracuseStep 3099671 = 4649507) B4649507
theorem B2067479 : Blo 1377508 2067479 := bstep (se 1 (by rfl) ⟨1550609, by rfl⟩ : syracuseStep 2067479 = 3101219) B3101219
theorem B1379351 : Blo 1377508 1379351 := bstep (se 1 (by rfl) ⟨1034513, by rfl⟩ : syracuseStep 1379351 = 2069027) B2069027
theorem B1379371 : Blo 1377508 1379371 := bstep (se 1 (by rfl) ⟨1034528, by rfl⟩ : syracuseStep 1379371 = 2069057) B2069057
theorem B1551415 : Blo 1377508 1551415 := bstep (se 1 (by rfl) ⟨1163561, by rfl⟩ : syracuseStep 1551415 = 2327123) B2327123
theorem B1379383 : Blo 1377508 1379383 := bstep (se 1 (by rfl) ⟨1034537, by rfl⟩ : syracuseStep 1379383 = 2069075) B2069075
theorem B1379403 : Blo 1377508 1379403 := bstep (se 1 (by rfl) ⟨1034552, by rfl⟩ : syracuseStep 1379403 = 2069105) B2069105
theorem B1379415 : Blo 1377508 1379415 := bstep (se 1 (by rfl) ⟨1034561, by rfl⟩ : syracuseStep 1379415 = 2069123) B2069123
theorem B2067545 : Blo 1377508 2067545 := bstep (se 2 (by rfl) ⟨775329, by rfl⟩ : syracuseStep 2067545 = 1550659) B1550659
theorem B5590109 : Blo 1377508 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B1379435 : Blo 1377508 1379435 := bstep (se 1 (by rfl) ⟨1034576, by rfl⟩ : syracuseStep 1379435 = 2069153) B2069153
theorem B1379447 : Blo 1377508 1379447 := bstep (se 1 (by rfl) ⟨1034585, by rfl⟩ : syracuseStep 1379447 = 2069171) B2069171
theorem B1379467 : Blo 1377508 1379467 := bstep (se 1 (by rfl) ⟨1034600, by rfl⟩ : syracuseStep 1379467 = 2069201) B2069201
theorem B1379479 : Blo 1377508 1379479 := bstep (se 1 (by rfl) ⟨1034609, by rfl⟩ : syracuseStep 1379479 = 2069219) B2069219
theorem B1379499 : Blo 1377508 1379499 := bstep (se 1 (by rfl) ⟨1034624, by rfl⟩ : syracuseStep 1379499 = 2069249) B2069249
theorem B3099851 : Blo 1377508 3099851 := bstep (se 1 (by rfl) ⟨2324888, by rfl⟩ : syracuseStep 3099851 = 4649777) B4649777
theorem B2067659 : Blo 1377508 2067659 := bstep (se 1 (by rfl) ⟨1550744, by rfl⟩ : syracuseStep 2067659 = 3101489) B3101489
theorem B2067671 : Blo 1377508 2067671 := bstep (se 1 (by rfl) ⟨1550753, by rfl⟩ : syracuseStep 2067671 = 3101507) B3101507
theorem B3312857 : Blo 1377508 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B5885149 : Blo 1377508 5885149 := bstep (se 3 (by rfl) ⟨1103465, by rfl⟩ : syracuseStep 5885149 = 2206931) B2206931
theorem B1551595 : Blo 1377508 1551595 := bstep (se 1 (by rfl) ⟨1163696, by rfl⟩ : syracuseStep 1551595 = 2327393) B2327393
theorem B2616563 : Blo 1377508 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B3099905 : Blo 1377508 3099905 := bstep (se 2 (by rfl) ⟨1162464, by rfl⟩ : syracuseStep 3099905 = 2324929) B2324929
theorem B2067737 : Blo 1377508 2067737 := bstep (se 2 (by rfl) ⟨775401, by rfl⟩ : syracuseStep 2067737 = 1550803) B1550803
theorem B1551703 : Blo 1377508 1551703 := bstep (se 1 (by rfl) ⟨1163777, by rfl⟩ : syracuseStep 1551703 = 2327555) B2327555
theorem B2616715 : Blo 1377508 2616715 := bstep (se 1 (by rfl) ⟨1962536, by rfl⟩ : syracuseStep 2616715 = 3925073) B3925073
theorem B2067851 : Blo 1377508 2067851 := bstep (se 1 (by rfl) ⟨1550888, by rfl⟩ : syracuseStep 2067851 = 3101777) B3101777
theorem B5590417 : Blo 1377508 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B35794325 : Blo 1377508 35794325 := bstep (se 6 (by rfl) ⟨838929, by rfl⟩ : syracuseStep 35794325 = 1677859) B1677859
theorem B4967831 : Blo 1377508 4967831 := bstep (se 1 (by rfl) ⟨3725873, by rfl⟩ : syracuseStep 4967831 = 7451747) B7451747
theorem B2067863 : Blo 1377508 2067863 := bstep (se 1 (by rfl) ⟨1550897, by rfl⟩ : syracuseStep 2067863 = 3101795) B3101795
theorem B3100121 : Blo 1377508 3100121 := bstep (se 2 (by rfl) ⟨1162545, by rfl⟩ : syracuseStep 3100121 = 2325091) B2325091
theorem B2067929 : Blo 1377508 2067929 := bstep (se 2 (by rfl) ⟨775473, by rfl⟩ : syracuseStep 2067929 = 1550947) B1550947
theorem B1551883 : Blo 1377508 1551883 := bstep (se 1 (by rfl) ⟨1163912, by rfl⟩ : syracuseStep 1551883 = 2327825) B2327825
theorem B4967959 : Blo 1377508 4967959 := bstep (se 1 (by rfl) ⟨3725969, by rfl⟩ : syracuseStep 4967959 = 7451939) B7451939
theorem B3100211 : Blo 1377508 3100211 := bstep (se 1 (by rfl) ⟨2325158, by rfl⟩ : syracuseStep 3100211 = 4650317) B4650317
theorem B2068043 : Blo 1377508 2068043 := bstep (se 1 (by rfl) ⟨1551032, by rfl⟩ : syracuseStep 2068043 = 3102065) B3102065
theorem B3100247 : Blo 1377508 3100247 := bstep (se 1 (by rfl) ⟨2325185, by rfl⟩ : syracuseStep 3100247 = 4650371) B4650371
theorem B2068055 : Blo 1377508 2068055 := bstep (se 1 (by rfl) ⟨1551041, by rfl⟩ : syracuseStep 2068055 = 3102083) B3102083
theorem B2068121 : Blo 1377508 2068121 := bstep (se 2 (by rfl) ⟨775545, by rfl⟩ : syracuseStep 2068121 = 1551091) B1551091
theorem B2617049 : Blo 1377508 2617049 := bstep (se 2 (by rfl) ⟨981393, by rfl⟩ : syracuseStep 2617049 = 1962787) B1962787
theorem B3100427 : Blo 1377508 3100427 := bstep (se 1 (by rfl) ⟨2325320, by rfl⟩ : syracuseStep 3100427 = 4650641) B4650641
theorem B2068235 : Blo 1377508 2068235 := bstep (se 1 (by rfl) ⟨1551176, by rfl⟩ : syracuseStep 2068235 = 3102353) B3102353
theorem B2068247 : Blo 1377508 2068247 := bstep (se 1 (by rfl) ⟨1551185, by rfl⟩ : syracuseStep 2068247 = 3102371) B3102371
theorem B3100481 : Blo 1377508 3100481 := bstep (se 2 (by rfl) ⟨1162680, by rfl⟩ : syracuseStep 3100481 = 2325361) B2325361
theorem B2068313 : Blo 1377508 2068313 := bstep (se 2 (by rfl) ⟨775617, by rfl⟩ : syracuseStep 2068313 = 1551235) B1551235
theorem B4476865 : Blo 1377508 4476865 := bstep (se 2 (by rfl) ⟨1678824, by rfl⟩ : syracuseStep 4476865 = 3357649) B3357649
theorem B2068427 : Blo 1377508 2068427 := bstep (se 1 (by rfl) ⟨1551320, by rfl⟩ : syracuseStep 2068427 = 3102641) B3102641
theorem B2068439 : Blo 1377508 2068439 := bstep (se 1 (by rfl) ⟨1551329, by rfl⟩ : syracuseStep 2068439 = 3102659) B3102659
theorem B2945035 : Blo 1377508 2945035 := bstep (se 1 (by rfl) ⟨2208776, by rfl⟩ : syracuseStep 2945035 = 4417553) B4417553
theorem B3100697 : Blo 1377508 3100697 := bstep (se 2 (by rfl) ⟨1162761, by rfl⟩ : syracuseStep 3100697 = 2325523) B2325523
theorem B2068505 : Blo 1377508 2068505 := bstep (se 2 (by rfl) ⟨775689, by rfl⟩ : syracuseStep 2068505 = 1551379) B1551379
theorem B3928115 : Blo 1377508 3928115 := bstep (se 1 (by rfl) ⟨2946086, by rfl⟩ : syracuseStep 3928115 = 5892173) B5892173
theorem B3100787 : Blo 1377508 3100787 := bstep (se 1 (by rfl) ⟨2325590, by rfl⟩ : syracuseStep 3100787 = 4651181) B4651181
theorem B2068619 : Blo 1377508 2068619 := bstep (se 1 (by rfl) ⟨1551464, by rfl⟩ : syracuseStep 2068619 = 3102929) B3102929
theorem B3100823 : Blo 1377508 3100823 := bstep (se 1 (by rfl) ⟨2325617, by rfl⟩ : syracuseStep 3100823 = 4651235) B4651235
theorem B7450775 : Blo 1377508 7450775 := bstep (se 1 (by rfl) ⟨5588081, by rfl⟩ : syracuseStep 7450775 = 11176163) B11176163
theorem B2068631 : Blo 1377508 2068631 := bstep (se 1 (by rfl) ⟨1551473, by rfl⟩ : syracuseStep 2068631 = 3102947) B3102947
theorem B2068697 : Blo 1377508 2068697 := bstep (se 2 (by rfl) ⟨775761, by rfl⟩ : syracuseStep 2068697 = 1551523) B1551523
theorem B14151941 : Blo 1377508 14151941 := bstep (se 4 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 14151941 = 2653489) B2653489
theorem B1962263 : Blo 1377508 1962263 := bstep (se 1 (by rfl) ⟨1471697, by rfl⟩ : syracuseStep 1962263 = 2943395) B2943395
theorem B3101003 : Blo 1377508 3101003 := bstep (se 1 (by rfl) ⟨2325752, by rfl⟩ : syracuseStep 3101003 = 4651505) B4651505
theorem B4649291 : Blo 1377508 4649291 := bstep (se 1 (by rfl) ⟨3486968, by rfl⟩ : syracuseStep 4649291 = 6973937) B6973937
theorem B8827211 : Blo 1377508 8827211 := bstep (se 1 (by rfl) ⟨6620408, by rfl⟩ : syracuseStep 8827211 = 13240817) B13240817
theorem B2068811 : Blo 1377508 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B2617687 : Blo 1377508 2617687 := bstep (se 1 (by rfl) ⟨1963265, by rfl⟩ : syracuseStep 2617687 = 3926531) B3926531
theorem B2068823 : Blo 1377508 2068823 := bstep (se 1 (by rfl) ⟨1551617, by rfl⟩ : syracuseStep 2068823 = 3103235) B3103235
theorem B5968217 : Blo 1377508 5968217 := bstep (se 2 (by rfl) ⟨2238081, by rfl⟩ : syracuseStep 5968217 = 4476163) B4476163
theorem B9933149 : Blo 1377508 9933149 := bstep (se 3 (by rfl) ⟨1862465, by rfl⟩ : syracuseStep 9933149 = 3724931) B3724931
theorem B3101057 : Blo 1377508 3101057 := bstep (se 2 (by rfl) ⟨1162896, by rfl⟩ : syracuseStep 3101057 = 2325793) B2325793
theorem B6623639 : Blo 1377508 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B2068889 : Blo 1377508 2068889 := bstep (se 2 (by rfl) ⟨775833, by rfl⟩ : syracuseStep 2068889 = 1551667) B1551667
theorem B2945497 : Blo 1377508 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B2069003 : Blo 1377508 2069003 := bstep (se 1 (by rfl) ⟨1551752, by rfl⟩ : syracuseStep 2069003 = 3103505) B3103505
theorem B2069015 : Blo 1377508 2069015 := bstep (se 1 (by rfl) ⟨1551761, by rfl⟩ : syracuseStep 2069015 = 3103523) B3103523
theorem B4190771 : Blo 1377508 4190771 := bstep (se 1 (by rfl) ⟨3143078, by rfl⟩ : syracuseStep 4190771 = 6286157) B6286157
theorem B1962571 : Blo 1377508 1962571 := bstep (se 1 (by rfl) ⟨1471928, by rfl⟩ : syracuseStep 1962571 = 2943857) B2943857
theorem B4649561 : Blo 1377508 4649561 := bstep (se 2 (by rfl) ⟨1743585, by rfl⟩ : syracuseStep 4649561 = 3487171) B3487171
theorem B3101273 : Blo 1377508 3101273 := bstep (se 2 (by rfl) ⟨1162977, by rfl⟩ : syracuseStep 3101273 = 2325955) B2325955
theorem B2069081 : Blo 1377508 2069081 := bstep (se 2 (by rfl) ⟨775905, by rfl⟩ : syracuseStep 2069081 = 1551811) B1551811
theorem B5378653 : Blo 1377508 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B3101363 : Blo 1377508 3101363 := bstep (se 1 (by rfl) ⟨2326022, by rfl⟩ : syracuseStep 3101363 = 4652045) B4652045
theorem B2069195 : Blo 1377508 2069195 := bstep (se 1 (by rfl) ⟨1551896, by rfl⟩ : syracuseStep 2069195 = 3103793) B3103793
theorem B3101399 : Blo 1377508 3101399 := bstep (se 1 (by rfl) ⟨2326049, by rfl⟩ : syracuseStep 3101399 = 4652099) B4652099
theorem B2069207 : Blo 1377508 2069207 := bstep (se 1 (by rfl) ⟨1551905, by rfl⟩ : syracuseStep 2069207 = 3103811) B3103811
theorem B10466009 : Blo 1377508 10466009 := bstep (se 2 (by rfl) ⟨3924753, by rfl⟩ : syracuseStep 10466009 = 7849507) B7849507
theorem B5231411 : Blo 1377508 5231411 := bstep (se 1 (by rfl) ⟨3923558, by rfl⟩ : syracuseStep 5231411 = 7847117) B7847117
theorem B5231425 : Blo 1377508 5231425 := bstep (se 2 (by rfl) ⟨1961784, by rfl⟩ : syracuseStep 5231425 = 3923569) B3923569
theorem B3101579 : Blo 1377508 3101579 := bstep (se 1 (by rfl) ⟨2326184, by rfl⟩ : syracuseStep 3101579 = 4652369) B4652369
theorem B1471403 : Blo 1377508 1471403 := bstep (se 1 (by rfl) ⟨1103552, by rfl⟩ : syracuseStep 1471403 = 2207105) B2207105
theorem B3101633 : Blo 1377508 3101633 := bstep (se 2 (by rfl) ⟨1163112, by rfl⟩ : syracuseStep 3101633 = 2326225) B2326225
theorem B6976529 : Blo 1377508 6976529 := bstep (se 2 (by rfl) ⟨2616198, by rfl⟩ : syracuseStep 6976529 = 5232397) B5232397
theorem B50328611 : Blo 1377508 50328611 := bstep (se 1 (by rfl) ⟨37746458, by rfl⟩ : syracuseStep 50328611 = 75492917) B75492917
theorem B23540867 : Blo 1377508 23540867 := bstep (se 1 (by rfl) ⟨17655650, by rfl⟩ : syracuseStep 23540867 = 35311301) B35311301
theorem B2618507 : Blo 1377508 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B3101849 : Blo 1377508 3101849 := bstep (se 2 (by rfl) ⟨1163193, by rfl⟩ : syracuseStep 3101849 = 2326387) B2326387
theorem B6976691 : Blo 1377508 6976691 := bstep (se 1 (by rfl) ⟨5232518, by rfl⟩ : syracuseStep 6976691 = 10465037) B10465037
theorem B2618561 : Blo 1377508 2618561 := bstep (se 2 (by rfl) ⟨981960, by rfl⟩ : syracuseStep 2618561 = 1963921) B1963921
theorem B3101939 : Blo 1377508 3101939 := bstep (se 1 (by rfl) ⟨2326454, by rfl⟩ : syracuseStep 3101939 = 4652909) B4652909
theorem B10474757 : Blo 1377508 10474757 := bstep (se 4 (by rfl) ⟨982008, by rfl⟩ : syracuseStep 10474757 = 1964017) B1964017
theorem B4650263 : Blo 1377508 4650263 := bstep (se 1 (by rfl) ⟨3487697, by rfl⟩ : syracuseStep 4650263 = 6975395) B6975395
theorem B3101975 : Blo 1377508 3101975 := bstep (se 1 (by rfl) ⟨2326481, by rfl⟩ : syracuseStep 3101975 = 4652963) B4652963
theorem B12744029 : Blo 1377508 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B13604273 : Blo 1377508 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B4969907 : Blo 1377508 4969907 := bstep (se 1 (by rfl) ⟨3727430, by rfl⟩ : syracuseStep 4969907 = 7454861) B7454861
theorem B3102155 : Blo 1377508 3102155 := bstep (se 1 (by rfl) ⟨2326616, by rfl⟩ : syracuseStep 3102155 = 4653233) B4653233
theorem B3102209 : Blo 1377508 3102209 := bstep (se 2 (by rfl) ⟨1163328, by rfl⟩ : syracuseStep 3102209 = 2326657) B2326657
theorem B3487283 : Blo 1377508 3487283 := bstep (se 1 (by rfl) ⟨2615462, by rfl⟩ : syracuseStep 3487283 = 5230925) B5230925
theorem B4970035 : Blo 1377508 4970035 := bstep (se 1 (by rfl) ⟨3727526, by rfl⟩ : syracuseStep 4970035 = 7455053) B7455053
theorem B1963607 : Blo 1377508 1963607 := bstep (se 1 (by rfl) ⟨1472705, by rfl⟩ : syracuseStep 1963607 = 2945411) B2945411
theorem B4413017 : Blo 1377508 4413017 := bstep (se 2 (by rfl) ⟨1654881, by rfl⟩ : syracuseStep 4413017 = 3309763) B3309763
theorem B7853699 : Blo 1377508 7853699 := bstep (se 1 (by rfl) ⟨5890274, by rfl⟩ : syracuseStep 7853699 = 11780549) B11780549
theorem B3102425 : Blo 1377508 3102425 := bstep (se 2 (by rfl) ⟨1163409, by rfl⟩ : syracuseStep 3102425 = 2326819) B2326819
theorem B3978973 : Blo 1377508 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B1963801 : Blo 1377508 1963801 := bstep (se 2 (by rfl) ⟨736425, by rfl⟩ : syracuseStep 1963801 = 1472851) B1472851
theorem B22370093 : Blo 1377508 22370093 := bstep (se 3 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 22370093 = 8388785) B8388785
theorem B4650803 : Blo 1377508 4650803 := bstep (se 1 (by rfl) ⟨3488102, by rfl⟩ : syracuseStep 4650803 = 6976205) B6976205
theorem B3102515 : Blo 1377508 3102515 := bstep (se 1 (by rfl) ⟨2326886, by rfl⟩ : syracuseStep 3102515 = 4653773) B4653773
theorem B3102551 : Blo 1377508 3102551 := bstep (se 1 (by rfl) ⟨2326913, by rfl⟩ : syracuseStep 3102551 = 4653827) B4653827
theorem B11777885 : Blo 1377508 11777885 := bstep (se 3 (by rfl) ⟨2208353, by rfl⟩ : syracuseStep 11777885 = 4416707) B4416707
theorem B8828851 : Blo 1377508 8828851 := bstep (se 1 (by rfl) ⟨6621638, by rfl⟩ : syracuseStep 8828851 = 13243277) B13243277
theorem B3102731 : Blo 1377508 3102731 := bstep (se 1 (by rfl) ⟨2327048, by rfl⟩ : syracuseStep 3102731 = 4654097) B4654097
theorem B4651073 : Blo 1377508 4651073 := bstep (se 2 (by rfl) ⟨1744152, by rfl⟩ : syracuseStep 4651073 = 3488305) B3488305
theorem B3102785 : Blo 1377508 3102785 := bstep (se 2 (by rfl) ⟨1163544, by rfl⟩ : syracuseStep 3102785 = 2327089) B2327089
theorem B3487819 : Blo 1377508 3487819 := bstep (se 1 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 3487819 = 5231729) B5231729
theorem B7854155 : Blo 1377508 7854155 := bstep (se 1 (by rfl) ⟨5890616, by rfl⟩ : syracuseStep 7854155 = 11781233) B11781233
theorem B4970641 : Blo 1377508 4970641 := bstep (se 2 (by rfl) ⟨1863990, by rfl⟩ : syracuseStep 4970641 = 3727981) B3727981
theorem B3487961 : Blo 1377508 3487961 := bstep (se 2 (by rfl) ⟨1307985, by rfl⟩ : syracuseStep 3487961 = 2615971) B2615971
theorem B2324747 : Blo 1377508 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B1472791 : Blo 1377508 1472791 := bstep (se 1 (by rfl) ⟨1104593, by rfl⟩ : syracuseStep 1472791 = 2209187) B2209187
theorem B3103001 : Blo 1377508 3103001 := bstep (se 2 (by rfl) ⟨1163625, by rfl⟩ : syracuseStep 3103001 = 2327251) B2327251
theorem B4413761 : Blo 1377508 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B3103091 : Blo 1377508 3103091 := bstep (se 1 (by rfl) ⟨2327318, by rfl⟩ : syracuseStep 3103091 = 4654637) B4654637
theorem B5527939 : Blo 1377508 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B2324875 : Blo 1377508 2324875 := bstep (se 1 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 2324875 = 3487313) B3487313
theorem B3103127 : Blo 1377508 3103127 := bstep (se 1 (by rfl) ⟨2327345, by rfl⟩ : syracuseStep 3103127 = 4654691) B4654691
theorem B2325017 : Blo 1377508 2325017 := bstep (se 2 (by rfl) ⟨871881, by rfl⟩ : syracuseStep 2325017 = 1743763) B1743763
theorem B11778635 : Blo 1377508 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B3103307 : Blo 1377508 3103307 := bstep (se 1 (by rfl) ⟨2327480, by rfl⟩ : syracuseStep 3103307 = 4654961) B4654961
theorem B4651613 : Blo 1377508 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B3103361 : Blo 1377508 3103361 := bstep (se 2 (by rfl) ⟨1163760, by rfl⟩ : syracuseStep 3103361 = 2327521) B2327521
theorem B15702659 : Blo 1377508 15702659 := bstep (se 1 (by rfl) ⟨11776994, by rfl⟩ : syracuseStep 15702659 = 23553989) B23553989
theorem B2325145 : Blo 1377508 2325145 := bstep (se 2 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 2325145 = 1743859) B1743859
theorem B5233355 : Blo 1377508 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B5233369 : Blo 1377508 5233369 := bstep (se 2 (by rfl) ⟨1962513, by rfl⟩ : syracuseStep 5233369 = 3925027) B3925027
theorem B8837849 : Blo 1377508 8837849 := bstep (se 2 (by rfl) ⟨3314193, by rfl⟩ : syracuseStep 8837849 = 6628387) B6628387
theorem B5888771 : Blo 1377508 5888771 := bstep (se 1 (by rfl) ⟨4416578, by rfl⟩ : syracuseStep 5888771 = 8833157) B8833157
theorem B3922739 : Blo 1377508 3922739 := bstep (se 1 (by rfl) ⟨2942054, by rfl⟩ : syracuseStep 3922739 = 5884109) B5884109
theorem B3103577 : Blo 1377508 3103577 := bstep (se 2 (by rfl) ⟨1163841, by rfl⟩ : syracuseStep 3103577 = 2327683) B2327683
theorem B9935747 : Blo 1377508 9935747 := bstep (se 1 (by rfl) ⟨7451810, by rfl⟩ : syracuseStep 9935747 = 14903621) B14903621
theorem B3103667 : Blo 1377508 3103667 := bstep (se 1 (by rfl) ⟨2327750, by rfl⟩ : syracuseStep 3103667 = 4655501) B4655501
theorem B3103703 : Blo 1377508 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B10763281 : Blo 1377508 10763281 := bstep (se 2 (by rfl) ⟨4036230, by rfl⟩ : syracuseStep 10763281 = 8072461) B8072461
theorem B3488791 : Blo 1377508 3488791 := bstep (se 1 (by rfl) ⟨2616593, by rfl⟩ : syracuseStep 3488791 = 5233187) B5233187
theorem B2653249 : Blo 1377508 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B6978635 : Blo 1377508 6978635 := bstep (se 1 (by rfl) ⟨5233976, by rfl⟩ : syracuseStep 6978635 = 10467953) B10467953
theorem B3103883 : Blo 1377508 3103883 := bstep (se 1 (by rfl) ⟨2327912, by rfl⟩ : syracuseStep 3103883 = 4655825) B4655825
theorem B4414657 : Blo 1377508 4414657 := bstep (se 2 (by rfl) ⟨1655496, by rfl⟩ : syracuseStep 4414657 = 3310993) B3310993
theorem B1744087 : Blo 1377508 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B2325719 : Blo 1377508 2325719 := bstep (se 1 (by rfl) ⟨1744289, by rfl⟩ : syracuseStep 2325719 = 3488579) B3488579
theorem B2325847 : Blo 1377508 2325847 := bstep (se 1 (by rfl) ⟨1744385, by rfl⟩ : syracuseStep 2325847 = 3488771) B3488771
theorem B3489227 : Blo 1377508 3489227 := bstep (se 1 (by rfl) ⟨2616920, by rfl⟩ : syracuseStep 3489227 = 5233841) B5233841
theorem B25476569 : Blo 1377508 25476569 := bstep (se 2 (by rfl) ⟨9553713, by rfl⟩ : syracuseStep 25476569 = 19107427) B19107427
theorem B5234327 : Blo 1377508 5234327 := bstep (se 1 (by rfl) ⟨3925745, by rfl⟩ : syracuseStep 5234327 = 7851491) B7851491
theorem B4652747 : Blo 1377508 4652747 := bstep (se 1 (by rfl) ⟨3489560, by rfl⟩ : syracuseStep 4652747 = 6979121) B6979121
theorem B3489601 : Blo 1377508 3489601 := bstep (se 2 (by rfl) ⟨1308600, by rfl⟩ : syracuseStep 3489601 = 2617201) B2617201
theorem B11943773 : Blo 1377508 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B2326475 : Blo 1377508 2326475 := bstep (se 1 (by rfl) ⟨1744856, by rfl⟩ : syracuseStep 2326475 = 3489713) B3489713
theorem B4653017 : Blo 1377508 4653017 := bstep (se 2 (by rfl) ⟨1744881, by rfl⟩ : syracuseStep 4653017 = 3489763) B3489763
theorem B6979607 : Blo 1377508 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B6627521 : Blo 1377508 6627521 := bstep (se 2 (by rfl) ⟨2485320, by rfl⟩ : syracuseStep 6627521 = 4970641) B4970641
theorem B2097415 : Blo 1377508 2097415 := bstep (se 1 (by rfl) ⟨1573061, by rfl⟩ : syracuseStep 2097415 = 3146123) B3146123
theorem B1491215 : Blo 1377508 1491215 := bstep (se 1 (by rfl) ⟨1118411, by rfl⟩ : syracuseStep 1491215 = 2236823) B2236823
theorem B4415759 : Blo 1377508 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B2326799 : Blo 1377508 2326799 := bstep (se 1 (by rfl) ⟨1745099, by rfl⟩ : syracuseStep 2326799 = 3490199) B3490199
theorem B2793847 : Blo 1377508 2793847 := bstep (se 1 (by rfl) ⟨2095385, by rfl⟩ : syracuseStep 2793847 = 4190771) B4190771
theorem B3490249 : Blo 1377508 3490249 := bstep (se 2 (by rfl) ⟨1308843, by rfl⟩ : syracuseStep 3490249 = 2617687) B2617687
theorem B3727873 : Blo 1377508 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B4653611 : Blo 1377508 4653611 := bstep (se 1 (by rfl) ⟨3490208, by rfl⟩ : syracuseStep 4653611 = 6980417) B6980417
theorem B3490391 : Blo 1377508 3490391 := bstep (se 1 (by rfl) ⟨2617793, by rfl⟩ : syracuseStep 3490391 = 5235587) B5235587
theorem B4842185 : Blo 1377508 4842185 := bstep (se 2 (by rfl) ⟨1815819, by rfl⟩ : syracuseStep 4842185 = 3631639) B3631639
theorem B3310379 : Blo 1377508 3310379 := bstep (se 1 (by rfl) ⟨2482784, by rfl⟩ : syracuseStep 3310379 = 4965569) B4965569
theorem B2327339 : Blo 1377508 2327339 := bstep (se 1 (by rfl) ⟨1745504, by rfl⟩ : syracuseStep 2327339 = 3491009) B3491009
theorem B1745707 : Blo 1377508 1745707 := bstep (se 1 (by rfl) ⟨1309280, by rfl⟩ : syracuseStep 1745707 = 2618561) B2618561
theorem B8496019 : Blo 1377508 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B9069515 : Blo 1377508 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B2942011 : Blo 1377508 2942011 := bstep (se 1 (by rfl) ⟨2206508, by rfl⟩ : syracuseStep 2942011 = 4413017) B4413017
theorem B13247549 : Blo 1377508 13247549 := bstep (se 3 (by rfl) ⟨2483915, by rfl⟩ : syracuseStep 13247549 = 4967831) B4967831
theorem B5235799 : Blo 1377508 5235799 := bstep (se 1 (by rfl) ⟨3926849, by rfl⟩ : syracuseStep 5235799 = 7853699) B7853699
theorem B2327737 : Blo 1377508 2327737 := bstep (se 2 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 2327737 = 1745803) B1745803
theorem B1377543 : Blo 1377508 1377543 := bstep (se 1 (by rfl) ⟨1033157, by rfl⟩ : syracuseStep 1377543 = 2066315) B2066315
theorem B1377551 : Blo 1377508 1377551 := bstep (se 1 (by rfl) ⟨1033163, by rfl⟩ : syracuseStep 1377551 = 2066327) B2066327
theorem B8381729 : Blo 1377508 8381729 := bstep (se 2 (by rfl) ⟨3143148, by rfl⟩ : syracuseStep 8381729 = 6286297) B6286297
theorem B5039393 : Blo 1377508 5039393 := bstep (se 2 (by rfl) ⟨1889772, by rfl⟩ : syracuseStep 5039393 = 3779545) B3779545
theorem B1377595 : Blo 1377508 1377595 := bstep (se 1 (by rfl) ⟨1033196, by rfl⟩ : syracuseStep 1377595 = 2066393) B2066393
theorem B13419911 : Blo 1377508 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B1377671 : Blo 1377508 1377671 := bstep (se 1 (by rfl) ⟨1033253, by rfl⟩ : syracuseStep 1377671 = 2066507) B2066507
theorem B5236103 : Blo 1377508 5236103 := bstep (se 1 (by rfl) ⟨3927077, by rfl⟩ : syracuseStep 5236103 = 7854155) B7854155
theorem B1377679 : Blo 1377508 1377679 := bstep (se 1 (by rfl) ⟨1033259, by rfl⟩ : syracuseStep 1377679 = 2066519) B2066519
theorem B1377723 : Blo 1377508 1377723 := bstep (se 1 (by rfl) ⟨1033292, by rfl⟩ : syracuseStep 1377723 = 2066585) B2066585
theorem B1549831 : Blo 1377508 1549831 := bstep (se 1 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 1549831 = 2324747) B2324747
theorem B1377799 : Blo 1377508 1377799 := bstep (se 1 (by rfl) ⟨1033349, by rfl⟩ : syracuseStep 1377799 = 2066699) B2066699
theorem B1377807 : Blo 1377508 1377807 := bstep (se 1 (by rfl) ⟨1033355, by rfl⟩ : syracuseStep 1377807 = 2066711) B2066711
theorem B2942507 : Blo 1377508 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B1377851 : Blo 1377508 1377851 := bstep (se 1 (by rfl) ⟨1033388, by rfl⟩ : syracuseStep 1377851 = 2066777) B2066777
theorem B5236285 : Blo 1377508 5236285 := bstep (se 3 (by rfl) ⟨981803, by rfl⟩ : syracuseStep 5236285 = 1963607) B1963607
theorem B1377927 : Blo 1377508 1377927 := bstep (se 1 (by rfl) ⟨1033445, by rfl⟩ : syracuseStep 1377927 = 2066891) B2066891
theorem B1377935 : Blo 1377508 1377935 := bstep (se 1 (by rfl) ⟨1033451, by rfl⟩ : syracuseStep 1377935 = 2066903) B2066903
theorem B1550011 : Blo 1377508 1550011 := bstep (se 1 (by rfl) ⟨1162508, by rfl⟩ : syracuseStep 1550011 = 2325017) B2325017
theorem B1377979 : Blo 1377508 1377979 := bstep (se 1 (by rfl) ⟨1033484, by rfl⟩ : syracuseStep 1377979 = 2066969) B2066969
theorem B1378055 : Blo 1377508 1378055 := bstep (se 1 (by rfl) ⟨1033541, by rfl⟩ : syracuseStep 1378055 = 2067083) B2067083
theorem B1378063 : Blo 1377508 1378063 := bstep (se 1 (by rfl) ⟨1033547, by rfl⟩ : syracuseStep 1378063 = 2067095) B2067095
theorem B1378107 : Blo 1377508 1378107 := bstep (se 1 (by rfl) ⟨1033580, by rfl⟩ : syracuseStep 1378107 = 2067161) B2067161
theorem B4654907 : Blo 1377508 4654907 := bstep (se 1 (by rfl) ⟨3491180, by rfl⟩ : syracuseStep 4654907 = 6982361) B6982361
theorem B5891899 : Blo 1377508 5891899 := bstep (se 1 (by rfl) ⟨4418924, by rfl⟩ : syracuseStep 5891899 = 8837849) B8837849
theorem B3925847 : Blo 1377508 3925847 := bstep (se 1 (by rfl) ⟨2944385, by rfl⟩ : syracuseStep 3925847 = 5888771) B5888771
theorem B2615159 : Blo 1377508 2615159 := bstep (se 1 (by rfl) ⟨1961369, by rfl⟩ : syracuseStep 2615159 = 3922739) B3922739
theorem B1378183 : Blo 1377508 1378183 := bstep (se 1 (by rfl) ⟨1033637, by rfl⟩ : syracuseStep 1378183 = 2067275) B2067275
theorem B1378191 : Blo 1377508 1378191 := bstep (se 1 (by rfl) ⟨1033643, by rfl⟩ : syracuseStep 1378191 = 2067287) B2067287
theorem B11175833 : Blo 1377508 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B2066363 : Blo 1377508 2066363 := bstep (se 1 (by rfl) ⟨1549772, by rfl⟩ : syracuseStep 2066363 = 3099545) B3099545
theorem B1378235 : Blo 1377508 1378235 := bstep (se 1 (by rfl) ⟨1033676, by rfl⟩ : syracuseStep 1378235 = 2067353) B2067353
theorem B2066423 : Blo 1377508 2066423 := bstep (se 1 (by rfl) ⟨1549817, by rfl⟩ : syracuseStep 2066423 = 3099635) B3099635
theorem B1378311 : Blo 1377508 1378311 := bstep (se 1 (by rfl) ⟨1033733, by rfl⟩ : syracuseStep 1378311 = 2067467) B2067467
theorem B2066447 : Blo 1377508 2066447 := bstep (se 1 (by rfl) ⟨1549835, by rfl⟩ : syracuseStep 2066447 = 3099671) B3099671
theorem B1378319 : Blo 1377508 1378319 := bstep (se 1 (by rfl) ⟨1033739, by rfl⟩ : syracuseStep 1378319 = 2067479) B2067479
theorem B63703057 : Blo 1377508 63703057 := bstep (se 2 (by rfl) ⟨23888646, by rfl⟩ : syracuseStep 63703057 = 47777293) B47777293
theorem B2066489 : Blo 1377508 2066489 := bstep (se 2 (by rfl) ⟨774933, by rfl⟩ : syracuseStep 2066489 = 1549867) B1549867
theorem B1378363 : Blo 1377508 1378363 := bstep (se 1 (by rfl) ⟨1033772, by rfl⟩ : syracuseStep 1378363 = 2067545) B2067545
theorem B2066567 : Blo 1377508 2066567 := bstep (se 1 (by rfl) ⟨1549925, by rfl⟩ : syracuseStep 2066567 = 3099851) B3099851
theorem B1378439 : Blo 1377508 1378439 := bstep (se 1 (by rfl) ⟨1033829, by rfl⟩ : syracuseStep 1378439 = 2067659) B2067659
theorem B1550479 : Blo 1377508 1550479 := bstep (se 1 (by rfl) ⟨1162859, by rfl⟩ : syracuseStep 1550479 = 2325719) B2325719
theorem B1378447 : Blo 1377508 1378447 := bstep (se 1 (by rfl) ⟨1033835, by rfl⟩ : syracuseStep 1378447 = 2067671) B2067671
theorem B2066603 : Blo 1377508 2066603 := bstep (se 1 (by rfl) ⟨1549952, by rfl⟩ : syracuseStep 2066603 = 3099905) B3099905
theorem B1378491 : Blo 1377508 1378491 := bstep (se 1 (by rfl) ⟨1033868, by rfl⟩ : syracuseStep 1378491 = 2067737) B2067737
theorem B2066633 : Blo 1377508 2066633 := bstep (se 2 (by rfl) ⟨774987, by rfl⟩ : syracuseStep 2066633 = 1549975) B1549975
theorem B1378567 : Blo 1377508 1378567 := bstep (se 1 (by rfl) ⟨1033925, by rfl⟩ : syracuseStep 1378567 = 2067851) B2067851
theorem B1378575 : Blo 1377508 1378575 := bstep (se 1 (by rfl) ⟨1033931, by rfl⟩ : syracuseStep 1378575 = 2067863) B2067863
theorem B4655393 : Blo 1377508 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B16984379 : Blo 1377508 16984379 := bstep (se 1 (by rfl) ⟨12738284, by rfl⟩ : syracuseStep 16984379 = 25476569) B25476569
theorem B2066747 : Blo 1377508 2066747 := bstep (se 1 (by rfl) ⟨1550060, by rfl⟩ : syracuseStep 2066747 = 3100121) B3100121
theorem B1378619 : Blo 1377508 1378619 := bstep (se 1 (by rfl) ⟨1033964, by rfl⟩ : syracuseStep 1378619 = 2067929) B2067929
theorem B14141789 : Blo 1377508 14141789 := bstep (se 3 (by rfl) ⟨2651585, by rfl⟩ : syracuseStep 14141789 = 5303171) B5303171
theorem B2066807 : Blo 1377508 2066807 := bstep (se 1 (by rfl) ⟨1550105, by rfl⟩ : syracuseStep 2066807 = 3100211) B3100211
theorem B1378695 : Blo 1377508 1378695 := bstep (se 1 (by rfl) ⟨1034021, by rfl⟩ : syracuseStep 1378695 = 2068043) B2068043
theorem B2066831 : Blo 1377508 2066831 := bstep (se 1 (by rfl) ⟨1550123, by rfl⟩ : syracuseStep 2066831 = 3100247) B3100247
theorem B1378703 : Blo 1377508 1378703 := bstep (se 1 (by rfl) ⟨1034027, by rfl⟩ : syracuseStep 1378703 = 2068055) B2068055
theorem B2066873 : Blo 1377508 2066873 := bstep (se 2 (by rfl) ⟨775077, by rfl⟩ : syracuseStep 2066873 = 1550155) B1550155
theorem B1378747 : Blo 1377508 1378747 := bstep (se 1 (by rfl) ⟨1034060, by rfl⟩ : syracuseStep 1378747 = 2068121) B2068121
theorem B23562737 : Blo 1377508 23562737 := bstep (se 2 (by rfl) ⟨8836026, by rfl⟩ : syracuseStep 23562737 = 17672053) B17672053
theorem B2066951 : Blo 1377508 2066951 := bstep (se 1 (by rfl) ⟨1550213, by rfl⟩ : syracuseStep 2066951 = 3100427) B3100427
theorem B1378823 : Blo 1377508 1378823 := bstep (se 1 (by rfl) ⟨1034117, by rfl⟩ : syracuseStep 1378823 = 2068235) B2068235
theorem B1378831 : Blo 1377508 1378831 := bstep (se 1 (by rfl) ⟨1034123, by rfl⟩ : syracuseStep 1378831 = 2068247) B2068247
theorem B2066987 : Blo 1377508 2066987 := bstep (se 1 (by rfl) ⟨1550240, by rfl⟩ : syracuseStep 2066987 = 3100481) B3100481
theorem B1378875 : Blo 1377508 1378875 := bstep (se 1 (by rfl) ⟨1034156, by rfl⟩ : syracuseStep 1378875 = 2068313) B2068313
theorem B2067017 : Blo 1377508 2067017 := bstep (se 2 (by rfl) ⟨775131, by rfl⟩ : syracuseStep 2067017 = 1550263) B1550263
theorem B1550983 : Blo 1377508 1550983 := bstep (se 1 (by rfl) ⟨1163237, by rfl⟩ : syracuseStep 1550983 = 2326475) B2326475
theorem B1378951 : Blo 1377508 1378951 := bstep (se 1 (by rfl) ⟨1034213, by rfl⟩ : syracuseStep 1378951 = 2068427) B2068427
theorem B1378959 : Blo 1377508 1378959 := bstep (se 1 (by rfl) ⟨1034219, by rfl⟩ : syracuseStep 1378959 = 2068439) B2068439
theorem B3926713 : Blo 1377508 3926713 := bstep (se 2 (by rfl) ⟨1472517, by rfl⟩ : syracuseStep 3926713 = 2945035) B2945035
theorem B2067131 : Blo 1377508 2067131 := bstep (se 1 (by rfl) ⟨1550348, by rfl⟩ : syracuseStep 2067131 = 3100697) B3100697
theorem B1379003 : Blo 1377508 1379003 := bstep (se 1 (by rfl) ⟨1034252, by rfl⟩ : syracuseStep 1379003 = 2068505) B2068505
theorem B2067191 : Blo 1377508 2067191 := bstep (se 1 (by rfl) ⟨1550393, by rfl⟩ : syracuseStep 2067191 = 3100787) B3100787
theorem B1379079 : Blo 1377508 1379079 := bstep (se 1 (by rfl) ⟨1034309, by rfl⟩ : syracuseStep 1379079 = 2068619) B2068619
theorem B2067215 : Blo 1377508 2067215 := bstep (se 1 (by rfl) ⟨1550411, by rfl⟩ : syracuseStep 2067215 = 3100823) B3100823
theorem B4967183 : Blo 1377508 4967183 := bstep (se 1 (by rfl) ⟨3725387, by rfl⟩ : syracuseStep 4967183 = 7450775) B7450775
theorem B1379087 : Blo 1377508 1379087 := bstep (se 1 (by rfl) ⟨1034315, by rfl⟩ : syracuseStep 1379087 = 2068631) B2068631
theorem B2067257 : Blo 1377508 2067257 := bstep (se 2 (by rfl) ⟨775221, by rfl⟩ : syracuseStep 2067257 = 1550443) B1550443
theorem B1551163 : Blo 1377508 1551163 := bstep (se 1 (by rfl) ⟨1163372, by rfl⟩ : syracuseStep 1551163 = 2326745) B2326745
theorem B1379131 : Blo 1377508 1379131 := bstep (se 1 (by rfl) ⟨1034348, by rfl⟩ : syracuseStep 1379131 = 2068697) B2068697
theorem B3099527 : Blo 1377508 3099527 := bstep (se 1 (by rfl) ⟨2324645, by rfl⟩ : syracuseStep 3099527 = 4649291) B4649291
theorem B5884807 : Blo 1377508 5884807 := bstep (se 1 (by rfl) ⟨4413605, by rfl⟩ : syracuseStep 5884807 = 8827211) B8827211
theorem B2067335 : Blo 1377508 2067335 := bstep (se 1 (by rfl) ⟨1550501, by rfl⟩ : syracuseStep 2067335 = 3101003) B3101003
theorem B2485127 : Blo 1377508 2485127 := bstep (se 1 (by rfl) ⟨1863845, by rfl⟩ : syracuseStep 2485127 = 3727691) B3727691
theorem B1379207 : Blo 1377508 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B1379215 : Blo 1377508 1379215 := bstep (se 1 (by rfl) ⟨1034411, by rfl⟩ : syracuseStep 1379215 = 2068823) B2068823
theorem B15707033 : Blo 1377508 15707033 := bstep (se 2 (by rfl) ⟨5890137, by rfl⟩ : syracuseStep 15707033 = 11780275) B11780275
theorem B2067371 : Blo 1377508 2067371 := bstep (se 1 (by rfl) ⟨1550528, by rfl⟩ : syracuseStep 2067371 = 3101057) B3101057
theorem B2206649 : Blo 1377508 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B1379259 : Blo 1377508 1379259 := bstep (se 1 (by rfl) ⟨1034444, by rfl⟩ : syracuseStep 1379259 = 2068889) B2068889
theorem B2067401 : Blo 1377508 2067401 := bstep (se 2 (by rfl) ⟨775275, by rfl⟩ : syracuseStep 2067401 = 1550551) B1550551
theorem B1379335 : Blo 1377508 1379335 := bstep (se 1 (by rfl) ⟨1034501, by rfl⟩ : syracuseStep 1379335 = 2069003) B2069003
theorem B3927055 : Blo 1377508 3927055 := bstep (se 1 (by rfl) ⟨2945291, by rfl⟩ : syracuseStep 3927055 = 5890583) B5890583
theorem B1379343 : Blo 1377508 1379343 := bstep (se 1 (by rfl) ⟨1034507, by rfl⟩ : syracuseStep 1379343 = 2069015) B2069015
theorem B6982685 : Blo 1377508 6982685 := bstep (se 3 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 6982685 = 2618507) B2618507
theorem B3099707 : Blo 1377508 3099707 := bstep (se 1 (by rfl) ⟨2324780, by rfl⟩ : syracuseStep 3099707 = 4649561) B4649561
theorem B2067515 : Blo 1377508 2067515 := bstep (se 1 (by rfl) ⟨1550636, by rfl⟩ : syracuseStep 2067515 = 3101273) B3101273
theorem B1379387 : Blo 1377508 1379387 := bstep (se 1 (by rfl) ⟨1034540, by rfl⟩ : syracuseStep 1379387 = 2069081) B2069081
theorem B2067575 : Blo 1377508 2067575 := bstep (se 1 (by rfl) ⟨1550681, by rfl⟩ : syracuseStep 2067575 = 3101363) B3101363
theorem B1379463 : Blo 1377508 1379463 := bstep (se 1 (by rfl) ⟨1034597, by rfl⟩ : syracuseStep 1379463 = 2069195) B2069195
theorem B2067599 : Blo 1377508 2067599 := bstep (se 1 (by rfl) ⟨1550699, by rfl⟩ : syracuseStep 2067599 = 3101399) B3101399
theorem B1379471 : Blo 1377508 1379471 := bstep (se 1 (by rfl) ⟨1034603, by rfl⟩ : syracuseStep 1379471 = 2069207) B2069207
theorem B2944147 : Blo 1377508 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B3099833 : Blo 1377508 3099833 := bstep (se 2 (by rfl) ⟨1162437, by rfl⟩ : syracuseStep 3099833 = 2324875) B2324875
theorem B2067641 : Blo 1377508 2067641 := bstep (se 2 (by rfl) ⟨775365, by rfl⟩ : syracuseStep 2067641 = 1550731) B1550731
theorem B8834285 : Blo 1377508 8834285 := bstep (se 3 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 8834285 = 3312857) B3312857
theorem B2067719 : Blo 1377508 2067719 := bstep (se 1 (by rfl) ⟨1550789, by rfl⟩ : syracuseStep 2067719 = 3101579) B3101579
theorem B1551631 : Blo 1377508 1551631 := bstep (se 1 (by rfl) ⟨1163723, by rfl⟩ : syracuseStep 1551631 = 2327447) B2327447
theorem B3927329 : Blo 1377508 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B2067755 : Blo 1377508 2067755 := bstep (se 1 (by rfl) ⟨1550816, by rfl⟩ : syracuseStep 2067755 = 3101633) B3101633
theorem B2067785 : Blo 1377508 2067785 := bstep (se 2 (by rfl) ⟨775419, by rfl⟩ : syracuseStep 2067785 = 1550839) B1550839
theorem B2616761 : Blo 1377508 2616761 := bstep (se 2 (by rfl) ⟨981285, by rfl⟩ : syracuseStep 2616761 = 1962571) B1962571
theorem B2067899 : Blo 1377508 2067899 := bstep (se 1 (by rfl) ⟨1550924, by rfl⟩ : syracuseStep 2067899 = 3101849) B3101849
theorem B2067959 : Blo 1377508 2067959 := bstep (se 1 (by rfl) ⟨1550969, by rfl⟩ : syracuseStep 2067959 = 3101939) B3101939
theorem B6983171 : Blo 1377508 6983171 := bstep (se 1 (by rfl) ⟨5237378, by rfl⟩ : syracuseStep 6983171 = 10474757) B10474757
theorem B3100175 : Blo 1377508 3100175 := bstep (se 1 (by rfl) ⟨2325131, by rfl⟩ : syracuseStep 3100175 = 4650263) B4650263
theorem B2067983 : Blo 1377508 2067983 := bstep (se 1 (by rfl) ⟨1550987, by rfl⟩ : syracuseStep 2067983 = 3101975) B3101975
theorem B3100193 : Blo 1377508 3100193 := bstep (se 2 (by rfl) ⟨1162572, by rfl⟩ : syracuseStep 3100193 = 2325145) B2325145
theorem B2068025 : Blo 1377508 2068025 := bstep (se 2 (by rfl) ⟨775509, by rfl⟩ : syracuseStep 2068025 = 1551019) B1551019
theorem B26488397 : Blo 1377508 26488397 := bstep (se 3 (by rfl) ⟨4966574, by rfl⟩ : syracuseStep 26488397 = 9933149) B9933149
theorem B3976823 : Blo 1377508 3976823 := bstep (se 1 (by rfl) ⟨2982617, by rfl⟩ : syracuseStep 3976823 = 5965235) B5965235
theorem B3313271 : Blo 1377508 3313271 := bstep (se 1 (by rfl) ⟨2484953, by rfl⟩ : syracuseStep 3313271 = 4969907) B4969907
theorem B2068103 : Blo 1377508 2068103 := bstep (se 1 (by rfl) ⟨1551077, by rfl⟩ : syracuseStep 2068103 = 3102155) B3102155
theorem B2068139 : Blo 1377508 2068139 := bstep (se 1 (by rfl) ⟨1551104, by rfl⟩ : syracuseStep 2068139 = 3102209) B3102209
theorem B2068169 : Blo 1377508 2068169 := bstep (se 2 (by rfl) ⟨775563, by rfl⟩ : syracuseStep 2068169 = 1551127) B1551127
theorem B6975233 : Blo 1377508 6975233 := bstep (se 2 (by rfl) ⟨2615712, by rfl⟩ : syracuseStep 6975233 = 5231425) B5231425
theorem B2617103 : Blo 1377508 2617103 := bstep (se 1 (by rfl) ⟨1962827, by rfl⟩ : syracuseStep 2617103 = 3925655) B3925655
theorem B2068283 : Blo 1377508 2068283 := bstep (se 1 (by rfl) ⟨1551212, by rfl⟩ : syracuseStep 2068283 = 3102425) B3102425
theorem B21221189 : Blo 1377508 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B14913395 : Blo 1377508 14913395 := bstep (se 1 (by rfl) ⟨11185046, by rfl⟩ : syracuseStep 14913395 = 22370093) B22370093
theorem B3100535 : Blo 1377508 3100535 := bstep (se 1 (by rfl) ⟨2325401, by rfl⟩ : syracuseStep 3100535 = 4650803) B4650803
theorem B2068343 : Blo 1377508 2068343 := bstep (se 1 (by rfl) ⟨1551257, by rfl⟩ : syracuseStep 2068343 = 3102515) B3102515
theorem B4190087 : Blo 1377508 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B2207623 : Blo 1377508 2207623 := bstep (se 1 (by rfl) ⟨1655717, by rfl⟩ : syracuseStep 2207623 = 3311435) B3311435
theorem B3927943 : Blo 1377508 3927943 := bstep (se 1 (by rfl) ⟨2945957, by rfl⟩ : syracuseStep 3927943 = 5891915) B5891915
theorem B2068367 : Blo 1377508 2068367 := bstep (se 1 (by rfl) ⟨1551275, by rfl⟩ : syracuseStep 2068367 = 3102551) B3102551
theorem B7851923 : Blo 1377508 7851923 := bstep (se 1 (by rfl) ⟨5888942, by rfl⟩ : syracuseStep 7851923 = 11777885) B11777885
theorem B2068409 : Blo 1377508 2068409 := bstep (se 2 (by rfl) ⟨775653, by rfl⟩ : syracuseStep 2068409 = 1551307) B1551307
theorem B2043895 : Blo 1377508 2043895 := bstep (se 1 (by rfl) ⟨1532921, by rfl⟩ : syracuseStep 2043895 = 3065843) B3065843
theorem B2068487 : Blo 1377508 2068487 := bstep (se 1 (by rfl) ⟨1551365, by rfl⟩ : syracuseStep 2068487 = 3102731) B3102731
theorem B3100715 : Blo 1377508 3100715 := bstep (se 1 (by rfl) ⟨2325536, by rfl⟩ : syracuseStep 3100715 = 4651073) B4651073
theorem B2068523 : Blo 1377508 2068523 := bstep (se 1 (by rfl) ⟨1551392, by rfl⟩ : syracuseStep 2068523 = 3102785) B3102785
theorem B2068553 : Blo 1377508 2068553 := bstep (se 2 (by rfl) ⟨775707, by rfl⟩ : syracuseStep 2068553 = 1551415) B1551415
theorem B2068667 : Blo 1377508 2068667 := bstep (se 1 (by rfl) ⟨1551500, by rfl⟩ : syracuseStep 2068667 = 3103001) B3103001
theorem B2068727 : Blo 1377508 2068727 := bstep (se 1 (by rfl) ⟨1551545, by rfl⟩ : syracuseStep 2068727 = 3103091) B3103091
theorem B5886209 : Blo 1377508 5886209 := bstep (se 2 (by rfl) ⟨2207328, by rfl⟩ : syracuseStep 5886209 = 4414657) B4414657
theorem B3928331 : Blo 1377508 3928331 := bstep (se 1 (by rfl) ⟨2946248, by rfl⟩ : syracuseStep 3928331 = 5892497) B5892497
theorem B2068751 : Blo 1377508 2068751 := bstep (se 1 (by rfl) ⟨1551563, by rfl⟩ : syracuseStep 2068751 = 3103127) B3103127
theorem B2068793 : Blo 1377508 2068793 := bstep (se 2 (by rfl) ⟨775797, by rfl⟩ : syracuseStep 2068793 = 1551595) B1551595
theorem B7852423 : Blo 1377508 7852423 := bstep (se 1 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 7852423 = 11778635) B11778635
theorem B2068871 : Blo 1377508 2068871 := bstep (se 1 (by rfl) ⟨1551653, by rfl⟩ : syracuseStep 2068871 = 3103307) B3103307
theorem B3101075 : Blo 1377508 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B2068907 : Blo 1377508 2068907 := bstep (se 1 (by rfl) ⟨1551680, by rfl⟩ : syracuseStep 2068907 = 3103361) B3103361
theorem B3101129 : Blo 1377508 3101129 := bstep (se 2 (by rfl) ⟨1162923, by rfl⟩ : syracuseStep 3101129 = 2325847) B2325847
theorem B2068937 : Blo 1377508 2068937 := bstep (se 2 (by rfl) ⟨775851, by rfl⟩ : syracuseStep 2068937 = 1551703) B1551703
theorem B6976043 : Blo 1377508 6976043 := bstep (se 1 (by rfl) ⟨5232032, by rfl⟩ : syracuseStep 6976043 = 10464065) B10464065
theorem B2617915 : Blo 1377508 2617915 := bstep (se 1 (by rfl) ⟨1963436, by rfl⟩ : syracuseStep 2617915 = 3926873) B3926873
theorem B2069051 : Blo 1377508 2069051 := bstep (se 1 (by rfl) ⟨1551788, by rfl⟩ : syracuseStep 2069051 = 3103577) B3103577
theorem B6623831 : Blo 1377508 6623831 := bstep (se 1 (by rfl) ⟨4967873, by rfl⟩ : syracuseStep 6623831 = 9935747) B9935747
theorem B2069111 : Blo 1377508 2069111 := bstep (se 1 (by rfl) ⟨1551833, by rfl⟩ : syracuseStep 2069111 = 3103667) B3103667
theorem B2617991 : Blo 1377508 2617991 := bstep (se 1 (by rfl) ⟨1963493, by rfl⟩ : syracuseStep 2617991 = 3926987) B3926987
theorem B2069135 : Blo 1377508 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B2069177 : Blo 1377508 2069177 := bstep (se 2 (by rfl) ⟨775941, by rfl⟩ : syracuseStep 2069177 = 1551883) B1551883
theorem B6623945 : Blo 1377508 6623945 := bstep (se 2 (by rfl) ⟨2483979, by rfl⟩ : syracuseStep 6623945 = 4967959) B4967959
theorem B2069255 : Blo 1377508 2069255 := bstep (se 1 (by rfl) ⟨1551941, by rfl⟩ : syracuseStep 2069255 = 3103883) B3103883
theorem B2618401 : Blo 1377508 2618401 := bstep (se 2 (by rfl) ⟨981900, by rfl⟩ : syracuseStep 2618401 = 1963801) B1963801
theorem B3101831 : Blo 1377508 3101831 := bstep (se 1 (by rfl) ⟨2326373, by rfl⟩ : syracuseStep 3101831 = 4652747) B4652747
theorem B5969153 : Blo 1377508 5969153 := bstep (se 2 (by rfl) ⟨2238432, by rfl⟩ : syracuseStep 5969153 = 4476865) B4476865
theorem B3487009 : Blo 1377508 3487009 := bstep (se 2 (by rfl) ⟨1307628, by rfl⟩ : syracuseStep 3487009 = 2615257) B2615257
theorem B3102011 : Blo 1377508 3102011 := bstep (se 1 (by rfl) ⟨2326508, by rfl⟩ : syracuseStep 3102011 = 4653017) B4653017
theorem B3724663 : Blo 1377508 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B2618743 : Blo 1377508 2618743 := bstep (se 1 (by rfl) ⟨1964057, by rfl⟩ : syracuseStep 2618743 = 3928115) B3928115
theorem B4650425 : Blo 1377508 4650425 := bstep (se 2 (by rfl) ⟨1743909, by rfl⟩ : syracuseStep 4650425 = 3487819) B3487819
theorem B3102137 : Blo 1377508 3102137 := bstep (se 2 (by rfl) ⟨1163301, by rfl⟩ : syracuseStep 3102137 = 2326603) B2326603
theorem B9434627 : Blo 1377508 9434627 := bstep (se 1 (by rfl) ⟨7075970, by rfl⟩ : syracuseStep 9434627 = 14151941) B14151941
theorem B3978811 : Blo 1377508 3978811 := bstep (se 1 (by rfl) ⟨2984108, by rfl⟩ : syracuseStep 3978811 = 5968217) B5968217
theorem B5232215 : Blo 1377508 5232215 := bstep (se 1 (by rfl) ⟨3924161, by rfl⟩ : syracuseStep 5232215 = 7848323) B7848323
theorem B1963721 : Blo 1377508 1963721 := bstep (se 2 (by rfl) ⟨736395, by rfl⟩ : syracuseStep 1963721 = 1472791) B1472791
theorem B3102479 : Blo 1377508 3102479 := bstep (se 1 (by rfl) ⟨2326859, by rfl⟩ : syracuseStep 3102479 = 4653719) B4653719
theorem B3102497 : Blo 1377508 3102497 := bstep (se 2 (by rfl) ⟨1163436, by rfl⟩ : syracuseStep 3102497 = 2326873) B2326873
theorem B6977339 : Blo 1377508 6977339 := bstep (se 1 (by rfl) ⟨5233004, by rfl⟩ : syracuseStep 6977339 = 10466009) B10466009
theorem B28686149 : Blo 1377508 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B7370585 : Blo 1377508 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B3487607 : Blo 1377508 3487607 := bstep (se 1 (by rfl) ⟨2615705, by rfl⟩ : syracuseStep 3487607 = 5231411) B5231411
theorem B6977501 : Blo 1377508 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B14899211 : Blo 1377508 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B4651019 : Blo 1377508 4651019 := bstep (se 1 (by rfl) ⟨3488264, by rfl⟩ : syracuseStep 4651019 = 6976529) B6976529
theorem B33552407 : Blo 1377508 33552407 := bstep (se 1 (by rfl) ⟨25164305, by rfl⟩ : syracuseStep 33552407 = 50328611) B50328611
theorem B5232701 : Blo 1377508 5232701 := bstep (se 3 (by rfl) ⟨981131, by rfl⟩ : syracuseStep 5232701 = 1962263) B1962263
theorem B15693911 : Blo 1377508 15693911 := bstep (se 1 (by rfl) ⟨11770433, by rfl⟩ : syracuseStep 15693911 = 23540867) B23540867
theorem B4651127 : Blo 1377508 4651127 := bstep (se 1 (by rfl) ⟨3488345, by rfl⟩ : syracuseStep 4651127 = 6976691) B6976691
theorem B3102839 : Blo 1377508 3102839 := bstep (se 1 (by rfl) ⟨2327129, by rfl⟩ : syracuseStep 3102839 = 4654259) B4654259
theorem B6977825 : Blo 1377508 6977825 := bstep (se 2 (by rfl) ⟨2616684, by rfl⟩ : syracuseStep 6977825 = 5233369) B5233369
theorem B3103019 : Blo 1377508 3103019 := bstep (se 1 (by rfl) ⟨2327264, by rfl⟩ : syracuseStep 3103019 = 4654529) B4654529
theorem B4413811 : Blo 1377508 4413811 := bstep (se 1 (by rfl) ⟨3310358, by rfl⟩ : syracuseStep 4413811 = 6620717) B6620717
theorem B2324855 : Blo 1377508 2324855 := bstep (se 1 (by rfl) ⟨1743641, by rfl⟩ : syracuseStep 2324855 = 3487283) B3487283
theorem B95451533 : Blo 1377508 95451533 := bstep (se 3 (by rfl) ⟨17897162, by rfl⟩ : syracuseStep 95451533 = 35794325) B35794325
theorem B18897299 : Blo 1377508 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B9943505 : Blo 1377508 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B1989239 : Blo 1377508 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B3103379 : Blo 1377508 3103379 := bstep (se 1 (by rfl) ⟨2327534, by rfl⟩ : syracuseStep 3103379 = 4655069) B4655069
theorem B14351041 : Blo 1377508 14351041 := bstep (se 2 (by rfl) ⟨5381640, by rfl⟩ : syracuseStep 14351041 = 10763281) B10763281
theorem B4651721 : Blo 1377508 4651721 := bstep (se 2 (by rfl) ⟨1744395, by rfl⟩ : syracuseStep 4651721 = 3488791) B3488791
theorem B3103433 : Blo 1377508 3103433 := bstep (se 2 (by rfl) ⟨1163787, by rfl⟩ : syracuseStep 3103433 = 2327575) B2327575
theorem B3537665 : Blo 1377508 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B15915791 : Blo 1377508 15915791 := bstep (se 1 (by rfl) ⟨11936843, by rfl⟩ : syracuseStep 15915791 = 23873687) B23873687
theorem B2325307 : Blo 1377508 2325307 := bstep (se 1 (by rfl) ⟨1743980, by rfl⟩ : syracuseStep 2325307 = 3487961) B3487961
theorem B2325449 : Blo 1377508 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B7846865 : Blo 1377508 7846865 := bstep (se 2 (by rfl) ⟨2942574, by rfl⟩ : syracuseStep 7846865 = 5885149) B5885149
theorem B26876933 : Blo 1377508 26876933 := bstep (se 4 (by rfl) ⟨2519712, by rfl⟩ : syracuseStep 26876933 = 5039425) B5039425
theorem B3922955 : Blo 1377508 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B10468439 : Blo 1377508 10468439 := bstep (se 1 (by rfl) ⟨7851329, by rfl⟩ : syracuseStep 10468439 = 15702659) B15702659
theorem B3488903 : Blo 1377508 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B3488953 : Blo 1377508 3488953 := bstep (se 2 (by rfl) ⟨1308357, by rfl⟩ : syracuseStep 3488953 = 2616715) B2616715
theorem B7453889 : Blo 1377508 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B6978797 : Blo 1377508 6978797 := bstep (se 3 (by rfl) ⟨1308524, by rfl⟩ : syracuseStep 6978797 = 2617049) B2617049
theorem B4652423 : Blo 1377508 4652423 := bstep (se 1 (by rfl) ⟨3489317, by rfl⟩ : syracuseStep 4652423 = 6978635) B6978635
theorem B3726739 : Blo 1377508 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B6626713 : Blo 1377508 6626713 := bstep (se 2 (by rfl) ⟨2485017, by rfl⟩ : syracuseStep 6626713 = 4970035) B4970035
theorem B5234129 : Blo 1377508 5234129 := bstep (se 2 (by rfl) ⟨1962798, by rfl⟩ : syracuseStep 5234129 = 3925597) B3925597
theorem B9199133 : Blo 1377508 9199133 := bstep (se 3 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 9199133 = 3449675) B3449675
theorem B3726881 : Blo 1377508 3726881 := bstep (se 2 (by rfl) ⟨1397580, by rfl⟩ : syracuseStep 3726881 = 2795161) B2795161
theorem B2326151 : Blo 1377508 2326151 := bstep (se 1 (by rfl) ⟨1744613, by rfl⟩ : syracuseStep 2326151 = 3489227) B3489227
theorem B25157297 : Blo 1377508 25157297 := bstep (se 2 (by rfl) ⟨9433986, by rfl⟩ : syracuseStep 25157297 = 18867973) B18867973
theorem B4652801 : Blo 1377508 4652801 := bstep (se 2 (by rfl) ⟨1744800, by rfl⟩ : syracuseStep 4652801 = 3489601) B3489601
theorem B3489551 : Blo 1377508 3489551 := bstep (se 1 (by rfl) ⟨2617163, by rfl⟩ : syracuseStep 3489551 = 5234327) B5234327
theorem B3923741 : Blo 1377508 3923741 := bstep (se 3 (by rfl) ⟨735701, by rfl⟩ : syracuseStep 3923741 = 1471403) B1471403
theorem B7962515 : Blo 1377508 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B11771801 : Blo 1377508 11771801 := bstep (se 2 (by rfl) ⟨4414425, by rfl⟩ : syracuseStep 11771801 = 8828851) B8828851
theorem B4653071 : Blo 1377508 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B3924139 : Blo 1377508 3924139 := bstep (se 1 (by rfl) ⟨2943104, by rfl⟩ : syracuseStep 3924139 = 5886209) B5886209
theorem B4415887 : Blo 1377508 4415887 := bstep (se 1 (by rfl) ⟨3311915, by rfl⟩ : syracuseStep 4415887 = 6623831) B6623831
theorem B2326927 : Blo 1377508 2326927 := bstep (se 1 (by rfl) ⟨1745195, by rfl⟩ : syracuseStep 2326927 = 3490391) B3490391
theorem B1745327 : Blo 1377508 1745327 := bstep (se 1 (by rfl) ⟨1308995, by rfl⟩ : syracuseStep 1745327 = 2617991) B2617991
theorem B4415963 : Blo 1377508 4415963 := bstep (se 1 (by rfl) ⟨3311972, by rfl⟩ : syracuseStep 4415963 = 6623945) B6623945
theorem B10469897 : Blo 1377508 10469897 := bstep (se 2 (by rfl) ⟨3926211, by rfl⟩ : syracuseStep 10469897 = 7852423) B7852423
theorem B4653665 : Blo 1377508 4653665 := bstep (se 2 (by rfl) ⟨1745124, by rfl⟩ : syracuseStep 4653665 = 3490249) B3490249
theorem B6046343 : Blo 1377508 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B8831699 : Blo 1377508 8831699 := bstep (se 1 (by rfl) ⟨6623774, by rfl⟩ : syracuseStep 8831699 = 13247549) B13247549
theorem B3490553 : Blo 1377508 3490553 := bstep (se 2 (by rfl) ⟨1308957, by rfl⟩ : syracuseStep 3490553 = 2617915) B2617915
theorem B5235617 : Blo 1377508 5235617 := bstep (se 2 (by rfl) ⟨1963356, by rfl⟩ : syracuseStep 5235617 = 3926713) B3926713
theorem B8946607 : Blo 1377508 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B3490735 : Blo 1377508 3490735 := bstep (se 1 (by rfl) ⟨2618051, by rfl⟩ : syracuseStep 3490735 = 5236103) B5236103
theorem B2327609 : Blo 1377508 2327609 := bstep (se 2 (by rfl) ⟨872853, by rfl⟩ : syracuseStep 2327609 = 1745707) B1745707
theorem B5236589 : Blo 1377508 5236589 := bstep (se 3 (by rfl) ⟨981860, by rfl⟩ : syracuseStep 5236589 = 1963721) B1963721
theorem B1377575 : Blo 1377508 1377575 := bstep (se 1 (by rfl) ⟨1033181, by rfl⟩ : syracuseStep 1377575 = 2066363) B2066363
theorem B1377615 : Blo 1377508 1377615 := bstep (se 1 (by rfl) ⟨1033211, by rfl⟩ : syracuseStep 1377615 = 2066423) B2066423
theorem B1377631 : Blo 1377508 1377631 := bstep (se 1 (by rfl) ⟨1033223, by rfl⟩ : syracuseStep 1377631 = 2066447) B2066447
theorem B5236073 : Blo 1377508 5236073 := bstep (se 2 (by rfl) ⟨1963527, by rfl⟩ : syracuseStep 5236073 = 3927055) B3927055
theorem B1377659 : Blo 1377508 1377659 := bstep (se 1 (by rfl) ⟨1033244, by rfl⟩ : syracuseStep 1377659 = 2066489) B2066489
theorem B3491201 : Blo 1377508 3491201 := bstep (se 2 (by rfl) ⟨1309200, by rfl⟩ : syracuseStep 3491201 = 2618401) B2618401
theorem B10462607 : Blo 1377508 10462607 := bstep (se 1 (by rfl) ⟨7846955, by rfl⟩ : syracuseStep 10462607 = 15693911) B15693911
theorem B1377711 : Blo 1377508 1377711 := bstep (se 1 (by rfl) ⟨1033283, by rfl⟩ : syracuseStep 1377711 = 2066567) B2066567
theorem B1377735 : Blo 1377508 1377735 := bstep (se 1 (by rfl) ⟨1033301, by rfl⟩ : syracuseStep 1377735 = 2066603) B2066603
theorem B6981065 : Blo 1377508 6981065 := bstep (se 2 (by rfl) ⟨2617899, by rfl⟩ : syracuseStep 6981065 = 5235799) B5235799
theorem B1377755 : Blo 1377508 1377755 := bstep (se 1 (by rfl) ⟨1033316, by rfl⟩ : syracuseStep 1377755 = 2066633) B2066633
theorem B3925529 : Blo 1377508 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B11322919 : Blo 1377508 11322919 := bstep (se 1 (by rfl) ⟨8492189, by rfl⟩ : syracuseStep 11322919 = 16984379) B16984379
theorem B1377831 : Blo 1377508 1377831 := bstep (se 1 (by rfl) ⟨1033373, by rfl⟩ : syracuseStep 1377831 = 2066747) B2066747
theorem B1549903 : Blo 1377508 1549903 := bstep (se 1 (by rfl) ⟨1162427, by rfl⟩ : syracuseStep 1549903 = 2324855) B2324855
theorem B1377871 : Blo 1377508 1377871 := bstep (se 1 (by rfl) ⟨1033403, by rfl⟩ : syracuseStep 1377871 = 2066807) B2066807
theorem B1377887 : Blo 1377508 1377887 := bstep (se 1 (by rfl) ⟨1033415, by rfl⟩ : syracuseStep 1377887 = 2066831) B2066831
theorem B1377915 : Blo 1377508 1377915 := bstep (se 1 (by rfl) ⟨1033436, by rfl⟩ : syracuseStep 1377915 = 2066873) B2066873
theorem B6629003 : Blo 1377508 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B1377967 : Blo 1377508 1377967 := bstep (se 1 (by rfl) ⟨1033475, by rfl⟩ : syracuseStep 1377967 = 2066951) B2066951
theorem B1377991 : Blo 1377508 1377991 := bstep (se 1 (by rfl) ⟨1033493, by rfl⟩ : syracuseStep 1377991 = 2066987) B2066987
theorem B1378011 : Blo 1377508 1378011 := bstep (se 1 (by rfl) ⟨1033508, by rfl⟩ : syracuseStep 1378011 = 2067017) B2067017
theorem B4655447 : Blo 1377508 4655447 := bstep (se 1 (by rfl) ⟨3491585, by rfl⟩ : syracuseStep 4655447 = 6983171) B6983171
theorem B1378087 : Blo 1377508 1378087 := bstep (se 1 (by rfl) ⟨1033565, by rfl⟩ : syracuseStep 1378087 = 2067131) B2067131
theorem B4966217 : Blo 1377508 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B3491657 : Blo 1377508 3491657 := bstep (se 2 (by rfl) ⟨1309371, by rfl⟩ : syracuseStep 3491657 = 2618743) B2618743
theorem B1378127 : Blo 1377508 1378127 := bstep (se 1 (by rfl) ⟨1033595, by rfl⟩ : syracuseStep 1378127 = 2067191) B2067191
theorem B1378143 : Blo 1377508 1378143 := bstep (se 1 (by rfl) ⟨1033607, by rfl⟩ : syracuseStep 1378143 = 2067215) B2067215
theorem B3311455 : Blo 1377508 3311455 := bstep (se 1 (by rfl) ⟨2483591, by rfl⟩ : syracuseStep 3311455 = 4967183) B4967183
theorem B10610527 : Blo 1377508 10610527 := bstep (se 1 (by rfl) ⟨7957895, by rfl⟩ : syracuseStep 10610527 = 15915791) B15915791
theorem B12912493 : Blo 1377508 12912493 := bstep (se 3 (by rfl) ⟨2421092, by rfl⟩ : syracuseStep 12912493 = 4842185) B4842185
theorem B1378171 : Blo 1377508 1378171 := bstep (se 1 (by rfl) ⟨1033628, by rfl⟩ : syracuseStep 1378171 = 2067257) B2067257
theorem B2066351 : Blo 1377508 2066351 := bstep (se 1 (by rfl) ⟨1549763, by rfl⟩ : syracuseStep 2066351 = 3099527) B3099527
theorem B1378223 : Blo 1377508 1378223 := bstep (se 1 (by rfl) ⟨1033667, by rfl⟩ : syracuseStep 1378223 = 2067335) B2067335
theorem B10471355 : Blo 1377508 10471355 := bstep (se 1 (by rfl) ⟨7853516, by rfl⟩ : syracuseStep 10471355 = 15707033) B15707033
theorem B1378247 : Blo 1377508 1378247 := bstep (se 1 (by rfl) ⟨1033685, by rfl⟩ : syracuseStep 1378247 = 2067371) B2067371
theorem B1550299 : Blo 1377508 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B1378267 : Blo 1377508 1378267 := bstep (se 1 (by rfl) ⟨1033700, by rfl⟩ : syracuseStep 1378267 = 2067401) B2067401
theorem B17917955 : Blo 1377508 17917955 := bstep (se 1 (by rfl) ⟨13438466, by rfl⟩ : syracuseStep 17917955 = 26876933) B26876933
theorem B2615303 : Blo 1377508 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B2066441 : Blo 1377508 2066441 := bstep (se 2 (by rfl) ⟨774915, by rfl⟩ : syracuseStep 2066441 = 1549831) B1549831
theorem B4655123 : Blo 1377508 4655123 := bstep (se 1 (by rfl) ⟨3491342, by rfl⟩ : syracuseStep 4655123 = 6982685) B6982685
theorem B2066471 : Blo 1377508 2066471 := bstep (se 1 (by rfl) ⟨1549853, by rfl⟩ : syracuseStep 2066471 = 3099707) B3099707
theorem B1378343 : Blo 1377508 1378343 := bstep (se 1 (by rfl) ⟨1033757, by rfl⟩ : syracuseStep 1378343 = 2067515) B2067515
theorem B1378383 : Blo 1377508 1378383 := bstep (se 1 (by rfl) ⟨1033787, by rfl⟩ : syracuseStep 1378383 = 2067575) B2067575
theorem B6981713 : Blo 1377508 6981713 := bstep (se 2 (by rfl) ⟨2618142, by rfl⟩ : syracuseStep 6981713 = 5236285) B5236285
theorem B1378399 : Blo 1377508 1378399 := bstep (se 1 (by rfl) ⟨1033799, by rfl⟩ : syracuseStep 1378399 = 2067599) B2067599
theorem B2066555 : Blo 1377508 2066555 := bstep (se 1 (by rfl) ⟨1549916, by rfl⟩ : syracuseStep 2066555 = 3099833) B3099833
theorem B1378427 : Blo 1377508 1378427 := bstep (se 1 (by rfl) ⟨1033820, by rfl⟩ : syracuseStep 1378427 = 2067641) B2067641
theorem B1378479 : Blo 1377508 1378479 := bstep (se 1 (by rfl) ⟨1033859, by rfl⟩ : syracuseStep 1378479 = 2067719) B2067719
theorem B1378503 : Blo 1377508 1378503 := bstep (se 1 (by rfl) ⟨1033877, by rfl⟩ : syracuseStep 1378503 = 2067755) B2067755
theorem B1378523 : Blo 1377508 1378523 := bstep (se 1 (by rfl) ⟨1033892, by rfl⟩ : syracuseStep 1378523 = 2067785) B2067785
theorem B2066681 : Blo 1377508 2066681 := bstep (se 2 (by rfl) ⟨775005, by rfl⟩ : syracuseStep 2066681 = 1550011) B1550011
theorem B1378599 : Blo 1377508 1378599 := bstep (se 1 (by rfl) ⟨1033949, by rfl⟩ : syracuseStep 1378599 = 2067899) B2067899
theorem B1378639 : Blo 1377508 1378639 := bstep (se 1 (by rfl) ⟨1033979, by rfl⟩ : syracuseStep 1378639 = 2067959) B2067959
theorem B2066783 : Blo 1377508 2066783 := bstep (se 1 (by rfl) ⟨1550087, by rfl⟩ : syracuseStep 2066783 = 3100175) B3100175
theorem B1378655 : Blo 1377508 1378655 := bstep (se 1 (by rfl) ⟨1033991, by rfl⟩ : syracuseStep 1378655 = 2067983) B2067983
theorem B2066795 : Blo 1377508 2066795 := bstep (se 1 (by rfl) ⟨1550096, by rfl⟩ : syracuseStep 2066795 = 3100193) B3100193
theorem B2484587 : Blo 1377508 2484587 := bstep (se 1 (by rfl) ⟨1863440, by rfl⟩ : syracuseStep 2484587 = 3726881) B3726881
theorem B1378683 : Blo 1377508 1378683 := bstep (se 1 (by rfl) ⟨1034012, by rfl⟩ : syracuseStep 1378683 = 2068025) B2068025
theorem B1550767 : Blo 1377508 1550767 := bstep (se 1 (by rfl) ⟨1163075, by rfl⟩ : syracuseStep 1550767 = 2326151) B2326151
theorem B1378735 : Blo 1377508 1378735 := bstep (se 1 (by rfl) ⟨1034051, by rfl⟩ : syracuseStep 1378735 = 2068103) B2068103
theorem B1378759 : Blo 1377508 1378759 := bstep (se 1 (by rfl) ⟨1034069, by rfl⟩ : syracuseStep 1378759 = 2068139) B2068139
theorem B16771531 : Blo 1377508 16771531 := bstep (se 1 (by rfl) ⟨12578648, by rfl⟩ : syracuseStep 16771531 = 25157297) B25157297
theorem B1378779 : Blo 1377508 1378779 := bstep (se 1 (by rfl) ⟨1034084, by rfl⟩ : syracuseStep 1378779 = 2068169) B2068169
theorem B5884397 : Blo 1377508 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B2943497 : Blo 1377508 2943497 := bstep (se 2 (by rfl) ⟨1103811, by rfl⟩ : syracuseStep 2943497 = 2207623) B2207623
theorem B5237257 : Blo 1377508 5237257 := bstep (se 2 (by rfl) ⟨1963971, by rfl⟩ : syracuseStep 5237257 = 3927943) B3927943
theorem B2615827 : Blo 1377508 2615827 := bstep (se 1 (by rfl) ⟨1961870, by rfl⟩ : syracuseStep 2615827 = 3923741) B3923741
theorem B1378855 : Blo 1377508 1378855 := bstep (se 1 (by rfl) ⟨1034141, by rfl⟩ : syracuseStep 1378855 = 2068283) B2068283
theorem B2067023 : Blo 1377508 2067023 := bstep (se 1 (by rfl) ⟨1550267, by rfl⟩ : syracuseStep 2067023 = 3100535) B3100535
theorem B1378895 : Blo 1377508 1378895 := bstep (se 1 (by rfl) ⟨1034171, by rfl⟩ : syracuseStep 1378895 = 2068343) B2068343
theorem B1378911 : Blo 1377508 1378911 := bstep (se 1 (by rfl) ⟨1034183, by rfl⟩ : syracuseStep 1378911 = 2068367) B2068367
theorem B1378939 : Blo 1377508 1378939 := bstep (se 1 (by rfl) ⟨1034204, by rfl⟩ : syracuseStep 1378939 = 2068409) B2068409
theorem B1378991 : Blo 1377508 1378991 := bstep (se 1 (by rfl) ⟨1034243, by rfl⟩ : syracuseStep 1378991 = 2068487) B2068487
theorem B84937409 : Blo 1377508 84937409 := bstep (se 2 (by rfl) ⟨31851528, by rfl⟩ : syracuseStep 84937409 = 63703057) B63703057
theorem B2067143 : Blo 1377508 2067143 := bstep (se 1 (by rfl) ⟨1550357, by rfl⟩ : syracuseStep 2067143 = 3100715) B3100715
theorem B1379015 : Blo 1377508 1379015 := bstep (se 1 (by rfl) ⟨1034261, by rfl⟩ : syracuseStep 1379015 = 2068523) B2068523
theorem B1379035 : Blo 1377508 1379035 := bstep (se 1 (by rfl) ⟨1034276, by rfl⟩ : syracuseStep 1379035 = 2068553) B2068553
theorem B1379111 : Blo 1377508 1379111 := bstep (se 1 (by rfl) ⟨1034333, by rfl⟩ : syracuseStep 1379111 = 2068667) B2068667
theorem B1379151 : Blo 1377508 1379151 := bstep (se 1 (by rfl) ⟨1034363, by rfl⟩ : syracuseStep 1379151 = 2068727) B2068727
theorem B2943839 : Blo 1377508 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B1551199 : Blo 1377508 1551199 := bstep (se 1 (by rfl) ⟨1163399, by rfl⟩ : syracuseStep 1551199 = 2326799) B2326799
theorem B1379167 : Blo 1377508 1379167 := bstep (se 1 (by rfl) ⟨1034375, by rfl⟩ : syracuseStep 1379167 = 2068751) B2068751
theorem B2067305 : Blo 1377508 2067305 := bstep (se 2 (by rfl) ⟨775239, by rfl⟩ : syracuseStep 2067305 = 1550479) B1550479
theorem B1379195 : Blo 1377508 1379195 := bstep (se 1 (by rfl) ⟨1034396, by rfl⟩ : syracuseStep 1379195 = 2068793) B2068793
theorem B1379247 : Blo 1377508 1379247 := bstep (se 1 (by rfl) ⟨1034435, by rfl⟩ : syracuseStep 1379247 = 2068871) B2068871
theorem B2067383 : Blo 1377508 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1379271 : Blo 1377508 1379271 := bstep (se 1 (by rfl) ⟨1034453, by rfl⟩ : syracuseStep 1379271 = 2068907) B2068907
theorem B2067419 : Blo 1377508 2067419 := bstep (se 1 (by rfl) ⟨1550564, by rfl⟩ : syracuseStep 2067419 = 3101129) B3101129
theorem B1379291 : Blo 1377508 1379291 := bstep (se 1 (by rfl) ⟨1034468, by rfl⟩ : syracuseStep 1379291 = 2068937) B2068937
theorem B21220325 : Blo 1377508 21220325 := bstep (se 4 (by rfl) ⟨1989405, by rfl⟩ : syracuseStep 21220325 = 3978811) B3978811
theorem B2796553 : Blo 1377508 2796553 := bstep (se 2 (by rfl) ⟨1048707, by rfl⟩ : syracuseStep 2796553 = 2097415) B2097415
theorem B1379367 : Blo 1377508 1379367 := bstep (se 1 (by rfl) ⟨1034525, by rfl⟩ : syracuseStep 1379367 = 2069051) B2069051
theorem B1379407 : Blo 1377508 1379407 := bstep (se 1 (by rfl) ⟨1034555, by rfl⟩ : syracuseStep 1379407 = 2069111) B2069111
theorem B1379423 : Blo 1377508 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B1379451 : Blo 1377508 1379451 := bstep (se 1 (by rfl) ⟨1034588, by rfl⟩ : syracuseStep 1379451 = 2069177) B2069177
theorem B5885081 : Blo 1377508 5885081 := bstep (se 2 (by rfl) ⟨2206905, by rfl⟩ : syracuseStep 5885081 = 4413811) B4413811
theorem B17673389 : Blo 1377508 17673389 := bstep (se 3 (by rfl) ⟨3313760, by rfl⟩ : syracuseStep 17673389 = 6627521) B6627521
theorem B1379503 : Blo 1377508 1379503 := bstep (se 1 (by rfl) ⟨1034627, by rfl⟩ : syracuseStep 1379503 = 2069255) B2069255
theorem B2206919 : Blo 1377508 2206919 := bstep (se 1 (by rfl) ⟨1655189, by rfl⟩ : syracuseStep 2206919 = 3310379) B3310379
theorem B1551559 : Blo 1377508 1551559 := bstep (se 1 (by rfl) ⟨1163669, by rfl⟩ : syracuseStep 1551559 = 2327339) B2327339
theorem B22351277 : Blo 1377508 22351277 := bstep (se 3 (by rfl) ⟨4190864, by rfl⟩ : syracuseStep 22351277 = 8381729) B8381729
theorem B13438381 : Blo 1377508 13438381 := bstep (se 3 (by rfl) ⟨2519696, by rfl⟩ : syracuseStep 13438381 = 5039393) B5039393
theorem B2067887 : Blo 1377508 2067887 := bstep (se 1 (by rfl) ⟨1550915, by rfl⟩ : syracuseStep 2067887 = 3101831) B3101831
theorem B2067977 : Blo 1377508 2067977 := bstep (se 2 (by rfl) ⟨775491, by rfl⟩ : syracuseStep 2067977 = 1550983) B1550983
theorem B2068007 : Blo 1377508 2068007 := bstep (se 1 (by rfl) ⟨1551005, by rfl⟩ : syracuseStep 2068007 = 3102011) B3102011
theorem B3100283 : Blo 1377508 3100283 := bstep (se 1 (by rfl) ⟨2325212, by rfl⟩ : syracuseStep 3100283 = 4650425) B4650425
theorem B2068091 : Blo 1377508 2068091 := bstep (se 1 (by rfl) ⟨1551068, by rfl⟩ : syracuseStep 2068091 = 3102137) B3102137
theorem B1961671 : Blo 1377508 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B3100409 : Blo 1377508 3100409 := bstep (se 2 (by rfl) ⟨1162653, by rfl⟩ : syracuseStep 3100409 = 2325307) B2325307
theorem B2068217 : Blo 1377508 2068217 := bstep (se 2 (by rfl) ⟨775581, by rfl⟩ : syracuseStep 2068217 = 1551163) B1551163
theorem B2068319 : Blo 1377508 2068319 := bstep (se 1 (by rfl) ⟨1551239, by rfl⟩ : syracuseStep 2068319 = 3102479) B3102479
theorem B2068331 : Blo 1377508 2068331 := bstep (se 1 (by rfl) ⟨1551248, by rfl⟩ : syracuseStep 2068331 = 3102497) B3102497
theorem B19124099 : Blo 1377508 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B7450555 : Blo 1377508 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B9932807 : Blo 1377508 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B3100679 : Blo 1377508 3100679 := bstep (se 1 (by rfl) ⟨2325509, by rfl⟩ : syracuseStep 3100679 = 4651019) B4651019
theorem B22368271 : Blo 1377508 22368271 := bstep (se 1 (by rfl) ⟨16776203, by rfl⟩ : syracuseStep 22368271 = 33552407) B33552407
theorem B3100751 : Blo 1377508 3100751 := bstep (se 1 (by rfl) ⟨2325563, by rfl⟩ : syracuseStep 3100751 = 4651127) B4651127
theorem B2068559 : Blo 1377508 2068559 := bstep (se 1 (by rfl) ⟨1551419, by rfl⟩ : syracuseStep 2068559 = 3102839) B3102839
theorem B2068679 : Blo 1377508 2068679 := bstep (se 1 (by rfl) ⟨1551509, by rfl⟩ : syracuseStep 2068679 = 3103019) B3103019
theorem B10604861 : Blo 1377508 10604861 := bstep (se 3 (by rfl) ⟨1988411, by rfl⟩ : syracuseStep 10604861 = 3976823) B3976823
theorem B5304637 : Blo 1377508 5304637 := bstep (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) B1989239
theorem B8835389 : Blo 1377508 8835389 := bstep (se 3 (by rfl) ⟨1656635, by rfl⟩ : syracuseStep 8835389 = 3313271) B3313271
theorem B15708491 : Blo 1377508 15708491 := bstep (se 1 (by rfl) ⟨11781368, by rfl⟩ : syracuseStep 15708491 = 23562737) B23562737
theorem B2068841 : Blo 1377508 2068841 := bstep (se 2 (by rfl) ⟨775815, by rfl⟩ : syracuseStep 2068841 = 1551631) B1551631
theorem B4649345 : Blo 1377508 4649345 := bstep (se 2 (by rfl) ⟨1743504, by rfl⟩ : syracuseStep 4649345 = 3487009) B3487009
theorem B2068919 : Blo 1377508 2068919 := bstep (se 1 (by rfl) ⟨1551689, by rfl⟩ : syracuseStep 2068919 = 3103379) B3103379
theorem B3101147 : Blo 1377508 3101147 := bstep (se 1 (by rfl) ⟨2325860, by rfl⟩ : syracuseStep 3101147 = 4651721) B4651721
theorem B2068955 : Blo 1377508 2068955 := bstep (se 1 (by rfl) ⟨1551716, by rfl⟩ : syracuseStep 2068955 = 3103433) B3103433
theorem B4968985 : Blo 1377508 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B8835617 : Blo 1377508 8835617 := bstep (se 2 (by rfl) ⟨3313356, by rfl⟩ : syracuseStep 8835617 = 6626713) B6626713
theorem B5231243 : Blo 1377508 5231243 := bstep (se 1 (by rfl) ⟨3923432, by rfl⟩ : syracuseStep 5231243 = 7846865) B7846865
theorem B4969259 : Blo 1377508 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B2618219 : Blo 1377508 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B3101615 : Blo 1377508 3101615 := bstep (se 1 (by rfl) ⟨2326211, by rfl⟩ : syracuseStep 3101615 = 4652423) B4652423
theorem B6132755 : Blo 1377508 6132755 := bstep (se 1 (by rfl) ⟨4599566, by rfl⟩ : syracuseStep 6132755 = 9199133) B9199133
theorem B17658931 : Blo 1377508 17658931 := bstep (se 1 (by rfl) ⟨13244198, by rfl⟩ : syracuseStep 17658931 = 26488397) B26488397
theorem B4650155 : Blo 1377508 4650155 := bstep (se 1 (by rfl) ⟨3487616, by rfl⟩ : syracuseStep 4650155 = 6975233) B6975233
theorem B3101867 : Blo 1377508 3101867 := bstep (se 1 (by rfl) ⟨2326400, by rfl⟩ : syracuseStep 3101867 = 4652801) B4652801
theorem B9942263 : Blo 1377508 9942263 := bstep (se 1 (by rfl) ⟨7456697, by rfl⟩ : syracuseStep 9942263 = 14913395) B14913395
theorem B2725193 : Blo 1377508 2725193 := bstep (se 2 (by rfl) ⟨1021947, by rfl⟩ : syracuseStep 2725193 = 2043895) B2043895
theorem B15906293 : Blo 1377508 15906293 := bstep (se 5 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 15906293 = 1491215) B1491215
theorem B2618887 : Blo 1377508 2618887 := bstep (se 1 (by rfl) ⟨1964165, by rfl⟩ : syracuseStep 2618887 = 3928331) B3928331
theorem B4650695 : Blo 1377508 4650695 := bstep (se 1 (by rfl) ⟨3488021, by rfl⟩ : syracuseStep 4650695 = 6976043) B6976043
theorem B3102407 : Blo 1377508 3102407 := bstep (se 1 (by rfl) ⟨2326805, by rfl⟩ : syracuseStep 3102407 = 4653611) B4653611
theorem B3725129 : Blo 1377508 3725129 := bstep (se 2 (by rfl) ⟨1396923, by rfl⟩ : syracuseStep 3725129 = 2793847) B2793847
theorem B4970497 : Blo 1377508 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B3979435 : Blo 1377508 3979435 := bstep (se 1 (by rfl) ⟨2984576, by rfl⟩ : syracuseStep 3979435 = 5969153) B5969153
theorem B19134721 : Blo 1377508 19134721 := bstep (se 2 (by rfl) ⟨7175520, by rfl⟩ : syracuseStep 19134721 = 14351041) B14351041
theorem B6289751 : Blo 1377508 6289751 := bstep (se 1 (by rfl) ⟨4717313, by rfl⟩ : syracuseStep 6289751 = 9434627) B9434627
theorem B3488143 : Blo 1377508 3488143 := bstep (se 1 (by rfl) ⟨2616107, by rfl⟩ : syracuseStep 3488143 = 5232215) B5232215
theorem B7846409 : Blo 1377508 7846409 := bstep (se 2 (by rfl) ⟨2942403, by rfl⟩ : syracuseStep 7846409 = 5884807) B5884807
theorem B11328025 : Blo 1377508 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B4651559 : Blo 1377508 4651559 := bstep (se 1 (by rfl) ⟨3488669, by rfl⟩ : syracuseStep 4651559 = 6977339) B6977339
theorem B3103271 : Blo 1377508 3103271 := bstep (se 1 (by rfl) ⟨2327453, by rfl⟩ : syracuseStep 3103271 = 4654907) B4654907
theorem B4913723 : Blo 1377508 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B1743439 : Blo 1377508 1743439 := bstep (se 1 (by rfl) ⟨1307579, by rfl⟩ : syracuseStep 1743439 = 2615159) B2615159
theorem B2325071 : Blo 1377508 2325071 := bstep (se 1 (by rfl) ⟨1743803, by rfl⟩ : syracuseStep 2325071 = 3487607) B3487607
theorem B4651667 : Blo 1377508 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B3488467 : Blo 1377508 3488467 := bstep (se 1 (by rfl) ⟨2616350, by rfl⟩ : syracuseStep 3488467 = 5232701) B5232701
theorem B3922681 : Blo 1377508 3922681 := bstep (se 2 (by rfl) ⟨1471005, by rfl⟩ : syracuseStep 3922681 = 2942011) B2942011
theorem B4651883 : Blo 1377508 4651883 := bstep (se 1 (by rfl) ⟨3488912, by rfl⟩ : syracuseStep 4651883 = 6977825) B6977825
theorem B3103595 : Blo 1377508 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B9427859 : Blo 1377508 9427859 := bstep (se 1 (by rfl) ⟨7070894, by rfl⟩ : syracuseStep 9427859 = 14141789) B14141789
theorem B4651937 : Blo 1377508 4651937 := bstep (se 2 (by rfl) ⟨1744476, by rfl⟩ : syracuseStep 4651937 = 3488953) B3488953
theorem B3103649 : Blo 1377508 3103649 := bstep (se 2 (by rfl) ⟨1163868, by rfl⟩ : syracuseStep 3103649 = 2327737) B2327737
theorem B63634355 : Blo 1377508 63634355 := bstep (se 1 (by rfl) ⟨47725766, by rfl⟩ : syracuseStep 63634355 = 95451533) B95451533
theorem B12598199 : Blo 1377508 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B2358443 : Blo 1377508 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B6978959 : Blo 1377508 6978959 := bstep (se 1 (by rfl) ⟨5234219, by rfl⟩ : syracuseStep 6978959 = 10468439) B10468439
theorem B2325935 : Blo 1377508 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B4652531 : Blo 1377508 4652531 := bstep (se 1 (by rfl) ⟨3489398, by rfl⟩ : syracuseStep 4652531 = 6978797) B6978797
theorem B5889523 : Blo 1377508 5889523 := bstep (se 1 (by rfl) ⟨4417142, by rfl⟩ : syracuseStep 5889523 = 8834285) B8834285
theorem B10468925 : Blo 1377508 10468925 := bstep (se 3 (by rfl) ⟨1962923, by rfl⟩ : syracuseStep 10468925 = 3925847) B3925847
theorem B1744507 : Blo 1377508 1744507 := bstep (se 1 (by rfl) ⟨1308380, by rfl⟩ : syracuseStep 1744507 = 2616761) B2616761
theorem B3489419 : Blo 1377508 3489419 := bstep (se 1 (by rfl) ⟨2617064, by rfl⟩ : syracuseStep 3489419 = 5234129) B5234129
theorem B11173565 : Blo 1377508 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B6627005 : Blo 1377508 6627005 := bstep (se 3 (by rfl) ⟨1242563, by rfl⟩ : syracuseStep 6627005 = 2485127) B2485127
theorem B7855865 : Blo 1377508 7855865 := bstep (se 2 (by rfl) ⟨2945949, by rfl⟩ : syracuseStep 7855865 = 5891899) B5891899
theorem B1744735 : Blo 1377508 1744735 := bstep (se 1 (by rfl) ⟨1308551, by rfl⟩ : syracuseStep 1744735 = 2617103) B2617103
theorem B2326367 : Blo 1377508 2326367 := bstep (se 1 (by rfl) ⟨1744775, by rfl⟩ : syracuseStep 2326367 = 3489551) B3489551
theorem B14147459 : Blo 1377508 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B5234615 : Blo 1377508 5234615 := bstep (se 1 (by rfl) ⟨3925961, by rfl⟩ : syracuseStep 5234615 = 7851923) B7851923
theorem B5308343 : Blo 1377508 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B7847867 : Blo 1377508 7847867 := bstep (se 1 (by rfl) ⟨5885900, by rfl⟩ : syracuseStep 7847867 = 11771801) B11771801
theorem B6627329 : Blo 1377508 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B7069907 : Blo 1377508 7069907 := bstep (se 1 (by rfl) ⟨5302430, by rfl⟩ : syracuseStep 7069907 = 10604861) B10604861
theorem B5890259 : Blo 1377508 5890259 := bstep (se 1 (by rfl) ⟨4417694, by rfl⟩ : syracuseStep 5890259 = 8835389) B8835389
theorem B6979931 : Blo 1377508 6979931 := bstep (se 1 (by rfl) ⟨5234948, by rfl⟩ : syracuseStep 6979931 = 10469897) B10469897
theorem B5890411 : Blo 1377508 5890411 := bstep (se 1 (by rfl) ⟨4417808, by rfl⟩ : syracuseStep 5890411 = 8835617) B8835617
theorem B4030895 : Blo 1377508 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B2327035 : Blo 1377508 2327035 := bstep (se 1 (by rfl) ⟨1745276, by rfl⟩ : syracuseStep 2327035 = 3490553) B3490553
theorem B1745479 : Blo 1377508 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B3490411 : Blo 1377508 3490411 := bstep (se 1 (by rfl) ⟨2617808, by rfl⟩ : syracuseStep 3490411 = 5235617) B5235617
theorem B4088503 : Blo 1377508 4088503 := bstep (se 1 (by rfl) ⟨3066377, by rfl⟩ : syracuseStep 4088503 = 6132755) B6132755
theorem B6628175 : Blo 1377508 6628175 := bstep (se 1 (by rfl) ⟨4971131, by rfl⟩ : syracuseStep 6628175 = 9942263) B9942263
theorem B3490715 : Blo 1377508 3490715 := bstep (se 1 (by rfl) ⟨2618036, by rfl⟩ : syracuseStep 3490715 = 5236073) B5236073
theorem B2327467 : Blo 1377508 2327467 := bstep (se 1 (by rfl) ⟨1745600, by rfl⟩ : syracuseStep 2327467 = 3491201) B3491201
theorem B4654043 : Blo 1377508 4654043 := bstep (se 1 (by rfl) ⟨3490532, by rfl⟩ : syracuseStep 4654043 = 6981065) B6981065
theorem B4654205 : Blo 1377508 4654205 := bstep (se 3 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 4654205 = 1745327) B1745327
theorem B3310811 : Blo 1377508 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B2483419 : Blo 1377508 2483419 := bstep (se 1 (by rfl) ⟨1862564, by rfl⟩ : syracuseStep 2483419 = 3725129) B3725129
theorem B2327771 : Blo 1377508 2327771 := bstep (se 1 (by rfl) ⟨1745828, by rfl⟩ : syracuseStep 2327771 = 3491657) B3491657
theorem B11928809 : Blo 1377508 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B4654313 : Blo 1377508 4654313 := bstep (se 2 (by rfl) ⟨1745367, by rfl⟩ : syracuseStep 4654313 = 3490735) B3490735
theorem B3491059 : Blo 1377508 3491059 := bstep (se 1 (by rfl) ⟨2618294, by rfl⟩ : syracuseStep 3491059 = 5236589) B5236589
theorem B1377567 : Blo 1377508 1377567 := bstep (se 1 (by rfl) ⟨1033175, by rfl⟩ : syracuseStep 1377567 = 2066351) B2066351
theorem B6980903 : Blo 1377508 6980903 := bstep (se 1 (by rfl) ⟨5235677, by rfl⟩ : syracuseStep 6980903 = 10471355) B10471355
theorem B11945303 : Blo 1377508 11945303 := bstep (se 1 (by rfl) ⟨8958977, by rfl⟩ : syracuseStep 11945303 = 17917955) B17917955
theorem B1377627 : Blo 1377508 1377627 := bstep (se 1 (by rfl) ⟨1033220, by rfl⟩ : syracuseStep 1377627 = 2066441) B2066441
theorem B3728737 : Blo 1377508 3728737 := bstep (se 2 (by rfl) ⟨1398276, by rfl⟩ : syracuseStep 3728737 = 2796553) B2796553
theorem B7849325 : Blo 1377508 7849325 := bstep (se 3 (by rfl) ⟨1471748, by rfl⟩ : syracuseStep 7849325 = 2943497) B2943497
theorem B1377647 : Blo 1377508 1377647 := bstep (se 1 (by rfl) ⟨1033235, by rfl⟩ : syracuseStep 1377647 = 2066471) B2066471
theorem B4654475 : Blo 1377508 4654475 := bstep (se 1 (by rfl) ⟨3490856, by rfl⟩ : syracuseStep 4654475 = 6981713) B6981713
theorem B23545241 : Blo 1377508 23545241 := bstep (se 2 (by rfl) ⟨8829465, by rfl⟩ : syracuseStep 23545241 = 17658931) B17658931
theorem B1377703 : Blo 1377508 1377703 := bstep (se 1 (by rfl) ⟨1033277, by rfl⟩ : syracuseStep 1377703 = 2066555) B2066555
theorem B1377787 : Blo 1377508 1377787 := bstep (se 1 (by rfl) ⟨1033340, by rfl⟩ : syracuseStep 1377787 = 2066681) B2066681
theorem B1377855 : Blo 1377508 1377855 := bstep (se 1 (by rfl) ⟨1033391, by rfl⟩ : syracuseStep 1377855 = 2066783) B2066783
theorem B1377863 : Blo 1377508 1377863 := bstep (se 1 (by rfl) ⟨1033397, by rfl⟩ : syracuseStep 1377863 = 2066795) B2066795
theorem B1656391 : Blo 1377508 1656391 := bstep (se 1 (by rfl) ⟨1242293, by rfl⟩ : syracuseStep 1656391 = 2484587) B2484587
theorem B1550047 : Blo 1377508 1550047 := bstep (se 1 (by rfl) ⟨1162535, by rfl⟩ : syracuseStep 1550047 = 2325071) B2325071
theorem B1378015 : Blo 1377508 1378015 := bstep (se 1 (by rfl) ⟨1033511, by rfl⟩ : syracuseStep 1378015 = 2067023) B2067023
theorem B56624939 : Blo 1377508 56624939 := bstep (se 1 (by rfl) ⟨42468704, by rfl⟩ : syracuseStep 56624939 = 84937409) B84937409
theorem B1378095 : Blo 1377508 1378095 := bstep (se 1 (by rfl) ⟨1033571, by rfl⟩ : syracuseStep 1378095 = 2067143) B2067143
theorem B17917841 : Blo 1377508 17917841 := bstep (se 2 (by rfl) ⟨6719190, by rfl⟩ : syracuseStep 17917841 = 13438381) B13438381
theorem B1378203 : Blo 1377508 1378203 := bstep (se 1 (by rfl) ⟨1033652, by rfl⟩ : syracuseStep 1378203 = 2067305) B2067305
theorem B6285239 : Blo 1377508 6285239 := bstep (se 1 (by rfl) ⟨4713929, by rfl⟩ : syracuseStep 6285239 = 9427859) B9427859
theorem B8398799 : Blo 1377508 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B1378255 : Blo 1377508 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1378279 : Blo 1377508 1378279 := bstep (se 1 (by rfl) ⟨1033709, by rfl⟩ : syracuseStep 1378279 = 2067419) B2067419
theorem B3491849 : Blo 1377508 3491849 := bstep (se 2 (by rfl) ⟨1309443, by rfl⟩ : syracuseStep 3491849 = 2618887) B2618887
theorem B2066537 : Blo 1377508 2066537 := bstep (se 2 (by rfl) ⟨774951, by rfl⟩ : syracuseStep 2066537 = 1549903) B1549903
theorem B11782259 : Blo 1377508 11782259 := bstep (se 1 (by rfl) ⟨8836694, by rfl⟩ : syracuseStep 11782259 = 17673389) B17673389
theorem B2615561 : Blo 1377508 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B1550623 : Blo 1377508 1550623 := bstep (se 1 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 1550623 = 2325935) B2325935
theorem B1378591 : Blo 1377508 1378591 := bstep (se 1 (by rfl) ⟨1033943, by rfl⟩ : syracuseStep 1378591 = 2067887) B2067887
theorem B1378651 : Blo 1377508 1378651 := bstep (se 1 (by rfl) ⟨1033988, by rfl⟩ : syracuseStep 1378651 = 2067977) B2067977
theorem B1378671 : Blo 1377508 1378671 := bstep (se 1 (by rfl) ⟨1034003, by rfl⟩ : syracuseStep 1378671 = 2068007) B2068007
theorem B2066855 : Blo 1377508 2066855 := bstep (se 1 (by rfl) ⟨1550141, by rfl⟩ : syracuseStep 2066855 = 3100283) B3100283
theorem B1378727 : Blo 1377508 1378727 := bstep (se 1 (by rfl) ⟨1034045, by rfl⟩ : syracuseStep 1378727 = 2068091) B2068091
theorem B7449043 : Blo 1377508 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B4418003 : Blo 1377508 4418003 := bstep (se 1 (by rfl) ⟨3313502, by rfl⟩ : syracuseStep 4418003 = 6627005) B6627005
theorem B2066939 : Blo 1377508 2066939 := bstep (se 1 (by rfl) ⟨1550204, by rfl⟩ : syracuseStep 2066939 = 3100409) B3100409
theorem B1378811 : Blo 1377508 1378811 := bstep (se 1 (by rfl) ⟨1034108, by rfl⟩ : syracuseStep 1378811 = 2068217) B2068217
theorem B5237243 : Blo 1377508 5237243 := bstep (se 1 (by rfl) ⟨3927932, by rfl⟩ : syracuseStep 5237243 = 7855865) B7855865
theorem B1550911 : Blo 1377508 1550911 := bstep (se 1 (by rfl) ⟨1163183, by rfl⟩ : syracuseStep 1550911 = 2326367) B2326367
theorem B1378879 : Blo 1377508 1378879 := bstep (se 1 (by rfl) ⟨1034159, by rfl⟩ : syracuseStep 1378879 = 2068319) B2068319
theorem B1378887 : Blo 1377508 1378887 := bstep (se 1 (by rfl) ⟨1034165, by rfl⟩ : syracuseStep 1378887 = 2068331) B2068331
theorem B9431639 : Blo 1377508 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B12749399 : Blo 1377508 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B2067065 : Blo 1377508 2067065 := bstep (se 2 (by rfl) ⟨775149, by rfl⟩ : syracuseStep 2067065 = 1550299) B1550299
theorem B6621871 : Blo 1377508 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B2067119 : Blo 1377508 2067119 := bstep (se 1 (by rfl) ⟨1550339, by rfl⟩ : syracuseStep 2067119 = 3100679) B3100679
theorem B2067167 : Blo 1377508 2067167 := bstep (se 1 (by rfl) ⟨1550375, by rfl⟩ : syracuseStep 2067167 = 3100751) B3100751
theorem B1379039 : Blo 1377508 1379039 := bstep (se 1 (by rfl) ⟨1034279, by rfl⟩ : syracuseStep 1379039 = 2068559) B2068559
theorem B1379119 : Blo 1377508 1379119 := bstep (se 1 (by rfl) ⟨1034339, by rfl⟩ : syracuseStep 1379119 = 2068679) B2068679
theorem B10472327 : Blo 1377508 10472327 := bstep (se 1 (by rfl) ⟨7854245, by rfl⟩ : syracuseStep 10472327 = 15708491) B15708491
theorem B1379227 : Blo 1377508 1379227 := bstep (se 1 (by rfl) ⟨1034420, by rfl⟩ : syracuseStep 1379227 = 2068841) B2068841
theorem B3099563 : Blo 1377508 3099563 := bstep (se 1 (by rfl) ⟨2324672, by rfl⟩ : syracuseStep 3099563 = 4649345) B4649345
theorem B1379279 : Blo 1377508 1379279 := bstep (se 1 (by rfl) ⟨1034459, by rfl⟩ : syracuseStep 1379279 = 2068919) B2068919
theorem B2067431 : Blo 1377508 2067431 := bstep (se 1 (by rfl) ⟨1550573, by rfl⟩ : syracuseStep 2067431 = 3101147) B3101147
theorem B1379303 : Blo 1377508 1379303 := bstep (se 1 (by rfl) ⟨1034477, by rfl⟩ : syracuseStep 1379303 = 2068955) B2068955
theorem B7072849 : Blo 1377508 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B3312839 : Blo 1377508 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B2067689 : Blo 1377508 2067689 := bstep (se 2 (by rfl) ⟨775383, by rfl⟩ : syracuseStep 2067689 = 1550767) B1550767
theorem B2067743 : Blo 1377508 2067743 := bstep (se 1 (by rfl) ⟨1550807, by rfl⟩ : syracuseStep 2067743 = 3101615) B3101615
theorem B6983009 : Blo 1377508 6983009 := bstep (se 2 (by rfl) ⟨2618628, by rfl⟩ : syracuseStep 6983009 = 5237257) B5237257
theorem B1551739 : Blo 1377508 1551739 := bstep (se 1 (by rfl) ⟨1163804, by rfl⟩ : syracuseStep 1551739 = 2327609) B2327609
theorem B3100103 : Blo 1377508 3100103 := bstep (se 1 (by rfl) ⟨2325077, by rfl⟩ : syracuseStep 3100103 = 4650155) B4650155
theorem B2067911 : Blo 1377508 2067911 := bstep (se 1 (by rfl) ⟨1550933, by rfl⟩ : syracuseStep 2067911 = 3101867) B3101867
theorem B6975071 : Blo 1377508 6975071 := bstep (se 1 (by rfl) ⟨5231303, by rfl⟩ : syracuseStep 6975071 = 10462607) B10462607
theorem B5230241 : Blo 1377508 5230241 := bstep (se 2 (by rfl) ⟨1961340, by rfl⟩ : syracuseStep 5230241 = 3922681) B3922681
theorem B10604195 : Blo 1377508 10604195 := bstep (se 1 (by rfl) ⟨7953146, by rfl⟩ : syracuseStep 10604195 = 15906293) B15906293
theorem B2617019 : Blo 1377508 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B4419335 : Blo 1377508 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B2068265 : Blo 1377508 2068265 := bstep (se 2 (by rfl) ⟨775599, by rfl⟩ : syracuseStep 2068265 = 1551199) B1551199
theorem B3100463 : Blo 1377508 3100463 := bstep (se 1 (by rfl) ⟨2325347, by rfl⟩ : syracuseStep 3100463 = 4650695) B4650695
theorem B2068271 : Blo 1377508 2068271 := bstep (se 1 (by rfl) ⟨1551203, by rfl⟩ : syracuseStep 2068271 = 3102407) B3102407
theorem B11775901 : Blo 1377508 11775901 := bstep (se 3 (by rfl) ⟨2207981, by rfl⟩ : syracuseStep 11775901 = 4415963) B4415963
theorem B102051845 : Blo 1377508 102051845 := bstep (se 4 (by rfl) ⟨9567360, by rfl⟩ : syracuseStep 102051845 = 19134721) B19134721
theorem B2068745 : Blo 1377508 2068745 := bstep (se 2 (by rfl) ⟨775779, by rfl⟩ : syracuseStep 2068745 = 1551559) B1551559
theorem B5230939 : Blo 1377508 5230939 := bstep (se 1 (by rfl) ⟨3923204, by rfl⟩ : syracuseStep 5230939 = 7846409) B7846409
theorem B3101039 : Blo 1377508 3101039 := bstep (se 1 (by rfl) ⟨2325779, by rfl⟩ : syracuseStep 3101039 = 4651559) B4651559
theorem B2068847 : Blo 1377508 2068847 := bstep (se 1 (by rfl) ⟨1551635, by rfl⟩ : syracuseStep 2068847 = 3103271) B3103271
theorem B3101111 : Blo 1377508 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B1962559 : Blo 1377508 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B3101255 : Blo 1377508 3101255 := bstep (se 1 (by rfl) ⟨2325941, by rfl⟩ : syracuseStep 3101255 = 4651883) B4651883
theorem B2069063 : Blo 1377508 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B3101291 : Blo 1377508 3101291 := bstep (se 1 (by rfl) ⟨2325968, by rfl⟩ : syracuseStep 3101291 = 4651937) B4651937
theorem B2069099 : Blo 1377508 2069099 := bstep (se 1 (by rfl) ⟨1551824, by rfl⟩ : syracuseStep 2069099 = 3103649) B3103649
theorem B42422903 : Blo 1377508 42422903 := bstep (se 1 (by rfl) ⟨31817177, by rfl⟩ : syracuseStep 42422903 = 63634355) B63634355
theorem B7852697 : Blo 1377508 7852697 := bstep (se 2 (by rfl) ⟨2944761, by rfl⟩ : syracuseStep 7852697 = 5889523) B5889523
theorem B1471279 : Blo 1377508 1471279 := bstep (se 1 (by rfl) ⟨1103459, by rfl⟩ : syracuseStep 1471279 = 2206919) B2206919
theorem B3101687 : Blo 1377508 3101687 := bstep (se 1 (by rfl) ⟨2326265, by rfl⟩ : syracuseStep 3101687 = 4652531) B4652531
theorem B17216657 : Blo 1377508 17216657 := bstep (se 2 (by rfl) ⟨6456246, by rfl⟩ : syracuseStep 17216657 = 12912493) B12912493
theorem B9934073 : Blo 1377508 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B5231911 : Blo 1377508 5231911 := bstep (se 1 (by rfl) ⟨3923933, by rfl⟩ : syracuseStep 5231911 = 7847867) B7847867
theorem B3102047 : Blo 1377508 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B29824361 : Blo 1377508 29824361 := bstep (se 2 (by rfl) ⟨11184135, by rfl⟩ : syracuseStep 29824361 = 22368271) B22368271
theorem B5232185 : Blo 1377508 5232185 := bstep (se 2 (by rfl) ⟨1962069, by rfl⟩ : syracuseStep 5232185 = 3924139) B3924139
theorem B5305913 : Blo 1377508 5305913 := bstep (se 2 (by rfl) ⟨1989717, by rfl⟩ : syracuseStep 5305913 = 3979435) B3979435
theorem B3102443 : Blo 1377508 3102443 := bstep (se 1 (by rfl) ⟨2326832, by rfl⟩ : syracuseStep 3102443 = 4653665) B4653665
theorem B3487495 : Blo 1377508 3487495 := bstep (se 1 (by rfl) ⟨2615621, by rfl⟩ : syracuseStep 3487495 = 5231243) B5231243
theorem B6289181 : Blo 1377508 6289181 := bstep (se 3 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 6289181 = 2358443) B2358443
theorem B5887799 : Blo 1377508 5887799 := bstep (se 1 (by rfl) ⟨4415849, by rfl⟩ : syracuseStep 5887799 = 8831699) B8831699
theorem B4650857 : Blo 1377508 4650857 := bstep (se 2 (by rfl) ⟨1744071, by rfl⟩ : syracuseStep 4650857 = 3488143) B3488143
theorem B5887849 : Blo 1377508 5887849 := bstep (se 2 (by rfl) ⟨2207943, by rfl⟩ : syracuseStep 5887849 = 4415887) B4415887
theorem B3102569 : Blo 1377508 3102569 := bstep (se 2 (by rfl) ⟨1163463, by rfl⟩ : syracuseStep 3102569 = 2326927) B2326927
theorem B22362041 : Blo 1377508 22362041 := bstep (se 2 (by rfl) ⟨8385765, by rfl⟩ : syracuseStep 22362041 = 16771531) B16771531
theorem B3487769 : Blo 1377508 3487769 := bstep (se 2 (by rfl) ⟨1307913, by rfl⟩ : syracuseStep 3487769 = 2615827) B2615827
theorem B15104033 : Blo 1377508 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B6625313 : Blo 1377508 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B2324585 : Blo 1377508 2324585 := bstep (se 2 (by rfl) ⟨871719, by rfl⟩ : syracuseStep 2324585 = 1743439) B1743439
theorem B1816795 : Blo 1377508 1816795 := bstep (se 1 (by rfl) ⟨1362596, by rfl⟩ : syracuseStep 1816795 = 2725193) B2725193
theorem B4651289 : Blo 1377508 4651289 := bstep (se 2 (by rfl) ⟨1744233, by rfl⟩ : syracuseStep 4651289 = 3488467) B3488467
theorem B1743535 : Blo 1377508 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B3103415 : Blo 1377508 3103415 := bstep (se 1 (by rfl) ⟨2327561, by rfl⟩ : syracuseStep 3103415 = 4655123) B4655123
theorem B4193167 : Blo 1377508 4193167 := bstep (se 1 (by rfl) ⟨3144875, by rfl⟩ : syracuseStep 4193167 = 6289751) B6289751
theorem B3103631 : Blo 1377508 3103631 := bstep (se 1 (by rfl) ⟨2327723, by rfl⟩ : syracuseStep 3103631 = 4655447) B4655447
theorem B3922931 : Blo 1377508 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B3275815 : Blo 1377508 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B14146883 : Blo 1377508 14146883 := bstep (se 1 (by rfl) ⟨10610162, by rfl⟩ : syracuseStep 14146883 = 21220325) B21220325
theorem B15097225 : Blo 1377508 15097225 := bstep (se 2 (by rfl) ⟨5661459, by rfl⟩ : syracuseStep 15097225 = 11322919) B11322919
theorem B3923387 : Blo 1377508 3923387 := bstep (se 1 (by rfl) ⟨2942540, by rfl⟩ : syracuseStep 3923387 = 5885081) B5885081
theorem B2326009 : Blo 1377508 2326009 := bstep (se 2 (by rfl) ⟨872253, by rfl⟩ : syracuseStep 2326009 = 1744507) B1744507
theorem B4652639 : Blo 1377508 4652639 := bstep (se 1 (by rfl) ⟨3489479, by rfl⟩ : syracuseStep 4652639 = 6978959) B6978959
theorem B14900851 : Blo 1377508 14900851 := bstep (se 1 (by rfl) ⟨11175638, by rfl⟩ : syracuseStep 14900851 = 22351277) B22351277
theorem B6979283 : Blo 1377508 6979283 := bstep (se 1 (by rfl) ⟨5234462, by rfl⟩ : syracuseStep 6979283 = 10468925) B10468925
theorem B2326279 : Blo 1377508 2326279 := bstep (se 1 (by rfl) ⟨1744709, by rfl⟩ : syracuseStep 2326279 = 3489419) B3489419
theorem B4415273 : Blo 1377508 4415273 := bstep (se 2 (by rfl) ⟨1655727, by rfl⟩ : syracuseStep 4415273 = 3311455) B3311455
theorem B14147369 : Blo 1377508 14147369 := bstep (se 2 (by rfl) ⟨5305263, by rfl⟩ : syracuseStep 14147369 = 10610527) B10610527
theorem B2326313 : Blo 1377508 2326313 := bstep (se 2 (by rfl) ⟨872367, by rfl⟩ : syracuseStep 2326313 = 1744735) B1744735
theorem B3489743 : Blo 1377508 3489743 := bstep (se 1 (by rfl) ⟨2617307, by rfl⟩ : syracuseStep 3489743 = 5234615) B5234615
theorem B3538895 : Blo 1377508 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B68034563 : Blo 1377508 68034563 := bstep (se 1 (by rfl) ⟨51025922, by rfl⟩ : syracuseStep 68034563 = 102051845) B102051845
theorem B4653287 : Blo 1377508 4653287 := bstep (se 1 (by rfl) ⟨3489965, by rfl⟩ : syracuseStep 4653287 = 6979931) B6979931
theorem B2687263 : Blo 1377508 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B5235131 : Blo 1377508 5235131 := bstep (se 1 (by rfl) ⟨3926348, by rfl⟩ : syracuseStep 5235131 = 7852697) B7852697
theorem B2327143 : Blo 1377508 2327143 := bstep (se 1 (by rfl) ⟨1745357, by rfl⟩ : syracuseStep 2327143 = 3490715) B3490715
theorem B31810157 : Blo 1377508 31810157 := bstep (se 3 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 31810157 = 11928809) B11928809
theorem B2327305 : Blo 1377508 2327305 := bstep (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) B1745479
theorem B11477771 : Blo 1377508 11477771 := bstep (se 1 (by rfl) ⟨8608328, by rfl⟩ : syracuseStep 11477771 = 17216657) B17216657
theorem B4653881 : Blo 1377508 4653881 := bstep (se 2 (by rfl) ⟨1745205, by rfl⟩ : syracuseStep 4653881 = 3490411) B3490411
theorem B4653935 : Blo 1377508 4653935 := bstep (se 1 (by rfl) ⟨3490451, by rfl⟩ : syracuseStep 4653935 = 6980903) B6980903
theorem B7963535 : Blo 1377508 7963535 := bstep (se 1 (by rfl) ⟨5972651, by rfl⟩ : syracuseStep 7963535 = 11945303) B11945303
theorem B19882907 : Blo 1377508 19882907 := bstep (se 1 (by rfl) ⟨14912180, by rfl⟩ : syracuseStep 19882907 = 29824361) B29824361
theorem B15696827 : Blo 1377508 15696827 := bstep (se 1 (by rfl) ⟨11772620, by rfl⟩ : syracuseStep 15696827 = 23545241) B23545241
theorem B37749959 : Blo 1377508 37749959 := bstep (se 1 (by rfl) ⟨28312469, by rfl⟩ : syracuseStep 37749959 = 56624939) B56624939
theorem B3925199 : Blo 1377508 3925199 := bstep (se 1 (by rfl) ⟨2943899, by rfl⟩ : syracuseStep 3925199 = 5887799) B5887799
theorem B11945227 : Blo 1377508 11945227 := bstep (se 1 (by rfl) ⟨8958920, by rfl⟩ : syracuseStep 11945227 = 17917841) B17917841
theorem B2327899 : Blo 1377508 2327899 := bstep (se 1 (by rfl) ⟨1745924, by rfl⟩ : syracuseStep 2327899 = 3491849) B3491849
theorem B10069355 : Blo 1377508 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B4416875 : Blo 1377508 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B4367753 : Blo 1377508 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B1549723 : Blo 1377508 1549723 := bstep (se 1 (by rfl) ⟨1162292, by rfl⟩ : syracuseStep 1549723 = 2324585) B2324585
theorem B1377691 : Blo 1377508 1377691 := bstep (se 1 (by rfl) ⟨1033268, by rfl⟩ : syracuseStep 1377691 = 2066537) B2066537
theorem B9430465 : Blo 1377508 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B1377903 : Blo 1377508 1377903 := bstep (se 1 (by rfl) ⟨1033427, by rfl⟩ : syracuseStep 1377903 = 2066855) B2066855
theorem B3311225 : Blo 1377508 3311225 := bstep (se 2 (by rfl) ⟨1241709, by rfl⟩ : syracuseStep 3311225 = 2483419) B2483419
theorem B4654745 : Blo 1377508 4654745 := bstep (se 2 (by rfl) ⟨1745529, by rfl⟩ : syracuseStep 4654745 = 3491059) B3491059
theorem B1377959 : Blo 1377508 1377959 := bstep (se 1 (by rfl) ⟨1033469, by rfl⟩ : syracuseStep 1377959 = 2066939) B2066939
theorem B3491495 : Blo 1377508 3491495 := bstep (se 1 (by rfl) ⟨2618621, by rfl⟩ : syracuseStep 3491495 = 5237243) B5237243
theorem B1378043 : Blo 1377508 1378043 := bstep (se 1 (by rfl) ⟨1033532, by rfl⟩ : syracuseStep 1378043 = 2067065) B2067065
theorem B1378079 : Blo 1377508 1378079 := bstep (se 1 (by rfl) ⟨1033559, by rfl⟩ : syracuseStep 1378079 = 2067119) B2067119
theorem B1378111 : Blo 1377508 1378111 := bstep (se 1 (by rfl) ⟨1033583, by rfl⟩ : syracuseStep 1378111 = 2067167) B2067167
theorem B20129633 : Blo 1377508 20129633 := bstep (se 2 (by rfl) ⟨7548612, by rfl⟩ : syracuseStep 20129633 = 15097225) B15097225
theorem B6981551 : Blo 1377508 6981551 := bstep (se 1 (by rfl) ⟨5236163, by rfl⟩ : syracuseStep 6981551 = 10472327) B10472327
theorem B2066375 : Blo 1377508 2066375 := bstep (se 1 (by rfl) ⟨1549781, by rfl⟩ : syracuseStep 2066375 = 3099563) B3099563
theorem B1378287 : Blo 1377508 1378287 := bstep (se 1 (by rfl) ⟨1033715, by rfl⟩ : syracuseStep 1378287 = 2067431) B2067431
theorem B19867801 : Blo 1377508 19867801 := bstep (se 2 (by rfl) ⟨7450425, by rfl⟩ : syracuseStep 19867801 = 14900851) B14900851
theorem B1378459 : Blo 1377508 1378459 := bstep (se 1 (by rfl) ⟨1033844, by rfl⟩ : syracuseStep 1378459 = 2067689) B2067689
theorem B1378495 : Blo 1377508 1378495 := bstep (se 1 (by rfl) ⟨1033871, by rfl⟩ : syracuseStep 1378495 = 2067743) B2067743
theorem B9431255 : Blo 1377508 9431255 := bstep (se 1 (by rfl) ⟨7073441, by rfl⟩ : syracuseStep 9431255 = 14146883) B14146883
theorem B4655339 : Blo 1377508 4655339 := bstep (se 1 (by rfl) ⟨3491504, by rfl⟩ : syracuseStep 4655339 = 6983009) B6983009
theorem B2615591 : Blo 1377508 2615591 := bstep (se 1 (by rfl) ⟨1961693, by rfl⟩ : syracuseStep 2615591 = 3923387) B3923387
theorem B2066729 : Blo 1377508 2066729 := bstep (se 2 (by rfl) ⟨775023, by rfl⟩ : syracuseStep 2066729 = 1550047) B1550047
theorem B2066735 : Blo 1377508 2066735 := bstep (se 1 (by rfl) ⟨1550051, by rfl⟩ : syracuseStep 2066735 = 3100103) B3100103
theorem B1378607 : Blo 1377508 1378607 := bstep (se 1 (by rfl) ⟨1033955, by rfl⟩ : syracuseStep 1378607 = 2067911) B2067911
theorem B7850465 : Blo 1377508 7850465 := bstep (se 2 (by rfl) ⟨2943924, by rfl⟩ : syracuseStep 7850465 = 5887849) B5887849
theorem B59632109 : Blo 1377508 59632109 := bstep (se 3 (by rfl) ⟨11181020, by rfl⟩ : syracuseStep 59632109 = 22362041) B22362041
theorem B2943515 : Blo 1377508 2943515 := bstep (se 1 (by rfl) ⟨2207636, by rfl⟩ : syracuseStep 2943515 = 4415273) B4415273
theorem B9431579 : Blo 1377508 9431579 := bstep (se 1 (by rfl) ⟨7073684, by rfl⟩ : syracuseStep 9431579 = 14147369) B14147369
theorem B1550875 : Blo 1377508 1550875 := bstep (se 1 (by rfl) ⟨1163156, by rfl⟩ : syracuseStep 1550875 = 2326313) B2326313
theorem B1378843 : Blo 1377508 1378843 := bstep (se 1 (by rfl) ⟨1034132, by rfl⟩ : syracuseStep 1378843 = 2068265) B2068265
theorem B2066975 : Blo 1377508 2066975 := bstep (se 1 (by rfl) ⟨1550231, by rfl⟩ : syracuseStep 2066975 = 3100463) B3100463
theorem B1378847 : Blo 1377508 1378847 := bstep (se 1 (by rfl) ⟨1034135, by rfl⟩ : syracuseStep 1378847 = 2068271) B2068271
theorem B4418219 : Blo 1377508 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B3926839 : Blo 1377508 3926839 := bstep (se 1 (by rfl) ⟨2945129, by rfl⟩ : syracuseStep 3926839 = 5890259) B5890259
theorem B1379163 : Blo 1377508 1379163 := bstep (se 1 (by rfl) ⟨1034372, by rfl⟩ : syracuseStep 1379163 = 2068745) B2068745
theorem B2067359 : Blo 1377508 2067359 := bstep (se 1 (by rfl) ⟨1550519, by rfl⟩ : syracuseStep 2067359 = 3101039) B3101039
theorem B1379231 : Blo 1377508 1379231 := bstep (se 1 (by rfl) ⟨1034423, by rfl⟩ : syracuseStep 1379231 = 2068847) B2068847
theorem B2067407 : Blo 1377508 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B2067497 : Blo 1377508 2067497 := bstep (se 2 (by rfl) ⟨775311, by rfl⟩ : syracuseStep 2067497 = 1550623) B1550623
theorem B2067503 : Blo 1377508 2067503 := bstep (se 1 (by rfl) ⟨1550627, by rfl⟩ : syracuseStep 2067503 = 3101255) B3101255
theorem B1379375 : Blo 1377508 1379375 := bstep (se 1 (by rfl) ⟨1034531, by rfl⟩ : syracuseStep 1379375 = 2069063) B2069063
theorem B2067527 : Blo 1377508 2067527 := bstep (se 1 (by rfl) ⟨1550645, by rfl⟩ : syracuseStep 2067527 = 3101291) B3101291
theorem B1379399 : Blo 1377508 1379399 := bstep (se 1 (by rfl) ⟨1034549, by rfl⟩ : syracuseStep 1379399 = 2069099) B2069099
theorem B28281935 : Blo 1377508 28281935 := bstep (se 1 (by rfl) ⟨21211451, by rfl⟩ : syracuseStep 28281935 = 42422903) B42422903
theorem B6974585 : Blo 1377508 6974585 := bstep (se 2 (by rfl) ⟨2615469, by rfl⟩ : syracuseStep 6974585 = 5230939) B5230939
theorem B18853085 : Blo 1377508 18853085 := bstep (se 3 (by rfl) ⟨3534953, by rfl⟩ : syracuseStep 18853085 = 7069907) B7069907
theorem B4418783 : Blo 1377508 4418783 := bstep (se 1 (by rfl) ⟨3314087, by rfl⟩ : syracuseStep 4418783 = 6628175) B6628175
theorem B9932057 : Blo 1377508 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B2067791 : Blo 1377508 2067791 := bstep (se 1 (by rfl) ⟨1550843, by rfl⟩ : syracuseStep 2067791 = 3101687) B3101687
theorem B2067881 : Blo 1377508 2067881 := bstep (se 2 (by rfl) ⟨775455, by rfl⟩ : syracuseStep 2067881 = 1550911) B1550911
theorem B2207207 : Blo 1377508 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B1551847 : Blo 1377508 1551847 := bstep (se 1 (by rfl) ⟨1163885, by rfl⟩ : syracuseStep 1551847 = 2327771) B2327771
theorem B6622715 : Blo 1377508 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B2068031 : Blo 1377508 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B5451337 : Blo 1377508 5451337 := bstep (se 2 (by rfl) ⟨2044251, by rfl⟩ : syracuseStep 5451337 = 4088503) B4088503
theorem B1961705 : Blo 1377508 1961705 := bstep (se 2 (by rfl) ⟨735639, by rfl⟩ : syracuseStep 1961705 = 1471279) B1471279
theorem B2068295 : Blo 1377508 2068295 := bstep (se 1 (by rfl) ⟨1551221, by rfl⟩ : syracuseStep 2068295 = 3102443) B3102443
theorem B5590889 : Blo 1377508 5590889 := bstep (se 2 (by rfl) ⟨2096583, by rfl⟩ : syracuseStep 5590889 = 4193167) B4193167
theorem B3100571 : Blo 1377508 3100571 := bstep (se 1 (by rfl) ⟨2325428, by rfl⟩ : syracuseStep 3100571 = 4650857) B4650857
theorem B2068379 : Blo 1377508 2068379 := bstep (se 1 (by rfl) ⟨1551284, by rfl⟩ : syracuseStep 2068379 = 3102569) B3102569
theorem B4190159 : Blo 1377508 4190159 := bstep (se 1 (by rfl) ⟨3142619, by rfl⟩ : syracuseStep 4190159 = 6285239) B6285239
theorem B5599199 : Blo 1377508 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B3100859 : Blo 1377508 3100859 := bstep (se 1 (by rfl) ⟨2325644, by rfl⟩ : syracuseStep 3100859 = 4651289) B4651289
theorem B2945335 : Blo 1377508 2945335 := bstep (se 1 (by rfl) ⟨2209001, by rfl⟩ : syracuseStep 2945335 = 4418003) B4418003
theorem B6975881 : Blo 1377508 6975881 := bstep (se 2 (by rfl) ⟨2615955, by rfl⟩ : syracuseStep 6975881 = 5231911) B5231911
theorem B6287759 : Blo 1377508 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B8499599 : Blo 1377508 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B2068943 : Blo 1377508 2068943 := bstep (se 1 (by rfl) ⟨1551707, by rfl⟩ : syracuseStep 2068943 = 3103415) B3103415
theorem B2068985 : Blo 1377508 2068985 := bstep (se 2 (by rfl) ⟨775869, by rfl⟩ : syracuseStep 2068985 = 1551739) B1551739
theorem B19886597 : Blo 1377508 19886597 := bstep (se 4 (by rfl) ⟨1864368, by rfl⟩ : syracuseStep 19886597 = 3728737) B3728737
theorem B2069087 : Blo 1377508 2069087 := bstep (se 1 (by rfl) ⟨1551815, by rfl⟩ : syracuseStep 2069087 = 3103631) B3103631
theorem B3101345 : Blo 1377508 3101345 := bstep (se 2 (by rfl) ⟨1163004, by rfl⟩ : syracuseStep 3101345 = 2326009) B2326009
theorem B2208521 : Blo 1377508 2208521 := bstep (se 2 (by rfl) ⟨828195, by rfl⟩ : syracuseStep 2208521 = 1656391) B1656391
theorem B2208559 : Blo 1377508 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B4649993 : Blo 1377508 4649993 := bstep (se 2 (by rfl) ⟨1743747, by rfl⟩ : syracuseStep 4649993 = 3487495) B3487495
theorem B3101705 : Blo 1377508 3101705 := bstep (se 2 (by rfl) ⟨1163139, by rfl⟩ : syracuseStep 3101705 = 2326279) B2326279
theorem B4650047 : Blo 1377508 4650047 := bstep (se 1 (by rfl) ⟨3487535, by rfl⟩ : syracuseStep 4650047 = 6975071) B6975071
theorem B3101759 : Blo 1377508 3101759 := bstep (se 1 (by rfl) ⟨2326319, by rfl⟩ : syracuseStep 3101759 = 4652639) B4652639
theorem B3486827 : Blo 1377508 3486827 := bstep (se 1 (by rfl) ⟨2615120, by rfl⟩ : syracuseStep 3486827 = 5230241) B5230241
theorem B2946223 : Blo 1377508 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B15701201 : Blo 1377508 15701201 := bstep (se 2 (by rfl) ⟨5887950, by rfl⟩ : syracuseStep 15701201 = 11775901) B11775901
theorem B2422393 : Blo 1377508 2422393 := bstep (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) B1816795
theorem B10466981 : Blo 1377508 10466981 := bstep (se 4 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 10466981 = 1962559) B1962559
theorem B7853881 : Blo 1377508 7853881 := bstep (se 2 (by rfl) ⟨2945205, by rfl⟩ : syracuseStep 7853881 = 5890411) B5890411
theorem B3102695 : Blo 1377508 3102695 := bstep (se 1 (by rfl) ⟨2327021, by rfl⟩ : syracuseStep 3102695 = 4654043) B4654043
theorem B3102713 : Blo 1377508 3102713 := bstep (se 2 (by rfl) ⟨1163517, by rfl⟩ : syracuseStep 3102713 = 2327035) B2327035
theorem B3102803 : Blo 1377508 3102803 := bstep (se 1 (by rfl) ⟨2327102, by rfl⟩ : syracuseStep 3102803 = 4654205) B4654205
theorem B3102875 : Blo 1377508 3102875 := bstep (se 1 (by rfl) ⟨2327156, by rfl⟩ : syracuseStep 3102875 = 4654313) B4654313
theorem B2324713 : Blo 1377508 2324713 := bstep (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) B1743535
theorem B8829161 : Blo 1377508 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B5232883 : Blo 1377508 5232883 := bstep (se 1 (by rfl) ⟨3924662, by rfl⟩ : syracuseStep 5232883 = 7849325) B7849325
theorem B3102983 : Blo 1377508 3102983 := bstep (se 1 (by rfl) ⟨2327237, by rfl⟩ : syracuseStep 3102983 = 4654475) B4654475
theorem B3488123 : Blo 1377508 3488123 := bstep (se 1 (by rfl) ⟨2616092, by rfl⟩ : syracuseStep 3488123 = 5232185) B5232185
theorem B3537275 : Blo 1377508 3537275 := bstep (se 1 (by rfl) ⟨2652956, by rfl⟩ : syracuseStep 3537275 = 5305913) B5305913
theorem B4192787 : Blo 1377508 4192787 := bstep (se 1 (by rfl) ⟨3144590, by rfl⟩ : syracuseStep 4192787 = 6289181) B6289181
theorem B3103289 : Blo 1377508 3103289 := bstep (se 2 (by rfl) ⟨1163733, by rfl⟩ : syracuseStep 3103289 = 2327467) B2327467
theorem B2325179 : Blo 1377508 2325179 := bstep (se 1 (by rfl) ⟨1743884, by rfl⟩ : syracuseStep 2325179 = 3487769) B3487769
theorem B7854839 : Blo 1377508 7854839 := bstep (se 1 (by rfl) ⟨5891129, by rfl⟩ : syracuseStep 7854839 = 11782259) B11782259
theorem B1743707 : Blo 1377508 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B37748213 : Blo 1377508 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B7069463 : Blo 1377508 7069463 := bstep (se 1 (by rfl) ⟨5302097, by rfl⟩ : syracuseStep 7069463 = 10604195) B10604195
theorem B1744679 : Blo 1377508 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B4652855 : Blo 1377508 4652855 := bstep (se 1 (by rfl) ⟨3489641, by rfl⟩ : syracuseStep 4652855 = 6979283) B6979283
theorem B10461149 : Blo 1377508 10461149 := bstep (se 3 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 10461149 = 3922931) B3922931
theorem B2326495 : Blo 1377508 2326495 := bstep (se 1 (by rfl) ⟨1744871, by rfl⟩ : syracuseStep 2326495 = 3489743) B3489743
theorem B3490087 : Blo 1377508 3490087 := bstep (se 1 (by rfl) ⟨2617565, by rfl⟩ : syracuseStep 3490087 = 5235131) B5235131
theorem B7651847 : Blo 1377508 7651847 := bstep (se 1 (by rfl) ⟨5738885, by rfl⟩ : syracuseStep 7651847 = 11477771) B11477771
theorem B50274893 : Blo 1377508 50274893 := bstep (se 3 (by rfl) ⟨9426542, by rfl⟩ : syracuseStep 50274893 = 18853085) B18853085
theorem B5309023 : Blo 1377508 5309023 := bstep (se 1 (by rfl) ⟨3981767, by rfl⟩ : syracuseStep 5309023 = 7963535) B7963535
theorem B13255271 : Blo 1377508 13255271 := bstep (se 1 (by rfl) ⟨9941453, by rfl⟩ : syracuseStep 13255271 = 19882907) B19882907
theorem B12919429 : Blo 1377508 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B25166639 : Blo 1377508 25166639 := bstep (se 1 (by rfl) ⟨18874979, by rfl⟩ : syracuseStep 25166639 = 37749959) B37749959
theorem B5235785 : Blo 1377508 5235785 := bstep (se 2 (by rfl) ⟨1963419, by rfl⟩ : syracuseStep 5235785 = 3926839) B3926839
theorem B2327663 : Blo 1377508 2327663 := bstep (se 1 (by rfl) ⟨1745747, by rfl⟩ : syracuseStep 2327663 = 3491495) B3491495
theorem B13419755 : Blo 1377508 13419755 := bstep (se 1 (by rfl) ⟨10064816, by rfl⟩ : syracuseStep 13419755 = 20129633) B20129633
theorem B4654367 : Blo 1377508 4654367 := bstep (se 1 (by rfl) ⟨3490775, by rfl⟩ : syracuseStep 4654367 = 6981551) B6981551
theorem B1377583 : Blo 1377508 1377583 := bstep (se 1 (by rfl) ⟨1033187, by rfl⟩ : syracuseStep 1377583 = 2066375) B2066375
theorem B25150877 : Blo 1377508 25150877 := bstep (se 3 (by rfl) ⟨4715789, by rfl⟩ : syracuseStep 25150877 = 9431579) B9431579
theorem B1377819 : Blo 1377508 1377819 := bstep (se 1 (by rfl) ⟨1033364, by rfl⟩ : syracuseStep 1377819 = 2066729) B2066729
theorem B1377823 : Blo 1377508 1377823 := bstep (se 1 (by rfl) ⟨1033367, by rfl⟩ : syracuseStep 1377823 = 2066735) B2066735
theorem B2795191 : Blo 1377508 2795191 := bstep (se 1 (by rfl) ⟨2096393, by rfl⟩ : syracuseStep 2795191 = 4192787) B4192787
theorem B15926969 : Blo 1377508 15926969 := bstep (se 2 (by rfl) ⟨5972613, by rfl⟩ : syracuseStep 15926969 = 11945227) B11945227
theorem B1377983 : Blo 1377508 1377983 := bstep (se 1 (by rfl) ⟨1033487, by rfl⟩ : syracuseStep 1377983 = 2066975) B2066975
theorem B1550119 : Blo 1377508 1550119 := bstep (se 1 (by rfl) ⟨1162589, by rfl⟩ : syracuseStep 1550119 = 2325179) B2325179
theorem B5236559 : Blo 1377508 5236559 := bstep (se 1 (by rfl) ⟨3927419, by rfl⟩ : syracuseStep 5236559 = 7854839) B7854839
theorem B2066297 : Blo 1377508 2066297 := bstep (se 2 (by rfl) ⟨774861, by rfl⟩ : syracuseStep 2066297 = 1549723) B1549723
theorem B1378239 : Blo 1377508 1378239 := bstep (se 1 (by rfl) ⟨1033679, by rfl⟩ : syracuseStep 1378239 = 2067359) B2067359
theorem B1378271 : Blo 1377508 1378271 := bstep (se 1 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 1378271 = 2067407) B2067407
theorem B1378331 : Blo 1377508 1378331 := bstep (se 1 (by rfl) ⟨1033748, by rfl⟩ : syracuseStep 1378331 = 2067497) B2067497
theorem B1378335 : Blo 1377508 1378335 := bstep (se 1 (by rfl) ⟨1033751, by rfl⟩ : syracuseStep 1378335 = 2067503) B2067503
theorem B1378351 : Blo 1377508 1378351 := bstep (se 1 (by rfl) ⟨1033763, by rfl⟩ : syracuseStep 1378351 = 2067527) B2067527
theorem B7268449 : Blo 1377508 7268449 := bstep (se 2 (by rfl) ⟨2725668, by rfl⟩ : syracuseStep 7268449 = 5451337) B5451337
theorem B6621371 : Blo 1377508 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B1378527 : Blo 1377508 1378527 := bstep (se 1 (by rfl) ⟨1033895, by rfl⟩ : syracuseStep 1378527 = 2067791) B2067791
theorem B1378587 : Blo 1377508 1378587 := bstep (se 1 (by rfl) ⟨1033940, by rfl⟩ : syracuseStep 1378587 = 2067881) B2067881
theorem B1378687 : Blo 1377508 1378687 := bstep (se 1 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 1378687 = 2068031) B2068031
theorem B10471841 : Blo 1377508 10471841 := bstep (se 2 (by rfl) ⟨3926940, by rfl⟩ : syracuseStep 10471841 = 7853881) B7853881
theorem B4712975 : Blo 1377508 4712975 := bstep (se 1 (by rfl) ⟨3534731, by rfl⟩ : syracuseStep 4712975 = 7069463) B7069463
theorem B1378863 : Blo 1377508 1378863 := bstep (se 1 (by rfl) ⟨1034147, by rfl⟩ : syracuseStep 1378863 = 2068295) B2068295
theorem B2067047 : Blo 1377508 2067047 := bstep (se 1 (by rfl) ⟨1550285, by rfl⟩ : syracuseStep 2067047 = 3100571) B3100571
theorem B1378919 : Blo 1377508 1378919 := bstep (se 1 (by rfl) ⟨1034189, by rfl⟩ : syracuseStep 1378919 = 2068379) B2068379
theorem B6974099 : Blo 1377508 6974099 := bstep (se 1 (by rfl) ⟨5230574, by rfl⟩ : syracuseStep 6974099 = 10461149) B10461149
theorem B2067239 : Blo 1377508 2067239 := bstep (se 1 (by rfl) ⟨1550429, by rfl⟩ : syracuseStep 2067239 = 3100859) B3100859
theorem B1379295 : Blo 1377508 1379295 := bstep (se 1 (by rfl) ⟨1034471, by rfl⟩ : syracuseStep 1379295 = 2068943) B2068943
theorem B3099617 : Blo 1377508 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B1379323 : Blo 1377508 1379323 := bstep (se 1 (by rfl) ⟨1034492, by rfl⟩ : syracuseStep 1379323 = 2068985) B2068985
theorem B13257731 : Blo 1377508 13257731 := bstep (se 1 (by rfl) ⟨9943298, by rfl⟩ : syracuseStep 13257731 = 19886597) B19886597
theorem B1379391 : Blo 1377508 1379391 := bstep (se 1 (by rfl) ⟨1034543, by rfl⟩ : syracuseStep 1379391 = 2069087) B2069087
theorem B3927113 : Blo 1377508 3927113 := bstep (se 2 (by rfl) ⟨1472667, by rfl⟩ : syracuseStep 3927113 = 2945335) B2945335
theorem B2067563 : Blo 1377508 2067563 := bstep (se 1 (by rfl) ⟨1550672, by rfl⟩ : syracuseStep 2067563 = 3101345) B3101345
theorem B10464551 : Blo 1377508 10464551 := bstep (se 1 (by rfl) ⟨7848413, by rfl⟩ : syracuseStep 10464551 = 15696827) B15696827
theorem B3099995 : Blo 1377508 3099995 := bstep (se 1 (by rfl) ⟨2324996, by rfl⟩ : syracuseStep 3099995 = 4649993) B4649993
theorem B2067803 : Blo 1377508 2067803 := bstep (se 1 (by rfl) ⟨1550852, by rfl⟩ : syracuseStep 2067803 = 3101705) B3101705
theorem B2067833 : Blo 1377508 2067833 := bstep (se 2 (by rfl) ⟨775437, by rfl⟩ : syracuseStep 2067833 = 1550875) B1550875
theorem B3100031 : Blo 1377508 3100031 := bstep (se 1 (by rfl) ⟨2325023, by rfl⟩ : syracuseStep 3100031 = 4650047) B4650047
theorem B2067839 : Blo 1377508 2067839 := bstep (se 1 (by rfl) ⟨1550879, by rfl⟩ : syracuseStep 2067839 = 3101759) B3101759
theorem B6974909 : Blo 1377508 6974909 := bstep (se 3 (by rfl) ⟨1307795, by rfl⟩ : syracuseStep 6974909 = 2615591) B2615591
theorem B2616799 : Blo 1377508 2616799 := bstep (se 1 (by rfl) ⟨1962599, by rfl⟩ : syracuseStep 2616799 = 3925199) B3925199
theorem B6712903 : Blo 1377508 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B2944583 : Blo 1377508 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B2911835 : Blo 1377508 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B9432733 : Blo 1377508 9432733 := bstep (se 3 (by rfl) ⟨1768637, by rfl⟩ : syracuseStep 9432733 = 3537275) B3537275
theorem B2944745 : Blo 1377508 2944745 := bstep (se 2 (by rfl) ⟨1104279, by rfl⟩ : syracuseStep 2944745 = 2208559) B2208559
theorem B2207483 : Blo 1377508 2207483 := bstep (se 1 (by rfl) ⟨1655612, by rfl⟩ : syracuseStep 2207483 = 3311225) B3311225
theorem B5885885 : Blo 1377508 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B2068463 : Blo 1377508 2068463 := bstep (se 1 (by rfl) ⟨1551347, by rfl⟩ : syracuseStep 2068463 = 3102695) B3102695
theorem B2068475 : Blo 1377508 2068475 := bstep (se 1 (by rfl) ⟨1551356, by rfl⟩ : syracuseStep 2068475 = 3102713) B3102713
theorem B2068535 : Blo 1377508 2068535 := bstep (se 1 (by rfl) ⟨1551401, by rfl⟩ : syracuseStep 2068535 = 3102803) B3102803
theorem B2068583 : Blo 1377508 2068583 := bstep (se 1 (by rfl) ⟨1551437, by rfl⟩ : syracuseStep 2068583 = 3102875) B3102875
theorem B6287503 : Blo 1377508 6287503 := bstep (se 1 (by rfl) ⟨4715627, by rfl⟩ : syracuseStep 6287503 = 9431255) B9431255
theorem B5886107 : Blo 1377508 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B14332069 : Blo 1377508 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B2068655 : Blo 1377508 2068655 := bstep (se 1 (by rfl) ⟨1551491, by rfl⟩ : syracuseStep 2068655 = 3102983) B3102983
theorem B3928297 : Blo 1377508 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B1962343 : Blo 1377508 1962343 := bstep (se 1 (by rfl) ⟨1471757, by rfl⟩ : syracuseStep 1962343 = 2943515) B2943515
theorem B2068859 : Blo 1377508 2068859 := bstep (se 1 (by rfl) ⟨1551644, by rfl⟩ : syracuseStep 2068859 = 3103289) B3103289
theorem B2945479 : Blo 1377508 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B5231213 : Blo 1377508 5231213 := bstep (se 3 (by rfl) ⟨980852, by rfl⟩ : syracuseStep 5231213 = 1961705) B1961705
theorem B2069129 : Blo 1377508 2069129 := bstep (se 2 (by rfl) ⟨775923, by rfl⟩ : syracuseStep 2069129 = 1551847) B1551847
theorem B18854623 : Blo 1377508 18854623 := bstep (se 1 (by rfl) ⟨14140967, by rfl⟩ : syracuseStep 18854623 = 28281935) B28281935
theorem B4649723 : Blo 1377508 4649723 := bstep (se 1 (by rfl) ⟨3487292, by rfl⟩ : syracuseStep 4649723 = 6974585) B6974585
theorem B2945855 : Blo 1377508 2945855 := bstep (se 1 (by rfl) ⟨2209391, by rfl⟩ : syracuseStep 2945855 = 4418783) B4418783
theorem B4649885 : Blo 1377508 4649885 := bstep (se 3 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 4649885 = 1743707) B1743707
theorem B3101903 : Blo 1377508 3101903 := bstep (se 1 (by rfl) ⟨2326427, by rfl⟩ : syracuseStep 3101903 = 4652855) B4652855
theorem B3101993 : Blo 1377508 3101993 := bstep (se 2 (by rfl) ⟨1163247, by rfl⟩ : syracuseStep 3101993 = 2326495) B2326495
theorem B3732799 : Blo 1377508 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B45356375 : Blo 1377508 45356375 := bstep (se 1 (by rfl) ⟨34017281, by rfl⟩ : syracuseStep 45356375 = 68034563) B68034563
theorem B3102191 : Blo 1377508 3102191 := bstep (se 1 (by rfl) ⟨2326643, by rfl⟩ : syracuseStep 3102191 = 4653287) B4653287
theorem B26490401 : Blo 1377508 26490401 := bstep (se 2 (by rfl) ⟨9933900, by rfl⟩ : syracuseStep 26490401 = 19867801) B19867801
theorem B4650587 : Blo 1377508 4650587 := bstep (se 1 (by rfl) ⟨3487940, by rfl⟩ : syracuseStep 4650587 = 6975881) B6975881
theorem B4191839 : Blo 1377508 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B5666399 : Blo 1377508 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B6977177 : Blo 1377508 6977177 := bstep (se 2 (by rfl) ⟨2616441, by rfl⟩ : syracuseStep 6977177 = 5232883) B5232883
theorem B21206771 : Blo 1377508 21206771 := bstep (se 1 (by rfl) ⟨15905078, by rfl⟩ : syracuseStep 21206771 = 31810157) B31810157
theorem B1472347 : Blo 1377508 1472347 := bstep (se 1 (by rfl) ⟨1104260, by rfl⟩ : syracuseStep 1472347 = 2208521) B2208521
theorem B3102587 : Blo 1377508 3102587 := bstep (se 1 (by rfl) ⟨2326940, by rfl⟩ : syracuseStep 3102587 = 4653881) B4653881
theorem B3102623 : Blo 1377508 3102623 := bstep (se 1 (by rfl) ⟨2326967, by rfl⟩ : syracuseStep 3102623 = 4653935) B4653935
theorem B2324551 : Blo 1377508 2324551 := bstep (se 1 (by rfl) ⟨1743413, by rfl⟩ : syracuseStep 2324551 = 3486827) B3486827
theorem B3102857 : Blo 1377508 3102857 := bstep (se 2 (by rfl) ⟨1163571, by rfl⟩ : syracuseStep 3102857 = 2327143) B2327143
theorem B10467467 : Blo 1377508 10467467 := bstep (se 1 (by rfl) ⟨7850600, by rfl⟩ : syracuseStep 10467467 = 15701201) B15701201
theorem B3103073 : Blo 1377508 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B3103163 : Blo 1377508 3103163 := bstep (se 1 (by rfl) ⟨2327372, by rfl⟩ : syracuseStep 3103163 = 4654745) B4654745
theorem B6977987 : Blo 1377508 6977987 := bstep (se 1 (by rfl) ⟨5233490, by rfl⟩ : syracuseStep 6977987 = 10466981) B10466981
theorem B3103559 : Blo 1377508 3103559 := bstep (se 1 (by rfl) ⟨2327669, by rfl⟩ : syracuseStep 3103559 = 4655339) B4655339
theorem B2325415 : Blo 1377508 2325415 := bstep (se 1 (by rfl) ⟨1744061, by rfl⟩ : syracuseStep 2325415 = 3488123) B3488123
theorem B5233643 : Blo 1377508 5233643 := bstep (se 1 (by rfl) ⟨3925232, by rfl⟩ : syracuseStep 5233643 = 7850465) B7850465
theorem B39754739 : Blo 1377508 39754739 := bstep (se 1 (by rfl) ⟨29816054, by rfl⟩ : syracuseStep 39754739 = 59632109) B59632109
theorem B3103865 : Blo 1377508 3103865 := bstep (se 2 (by rfl) ⟨1163949, by rfl⟩ : syracuseStep 3103865 = 2327899) B2327899
theorem B12573953 : Blo 1377508 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B4652477 : Blo 1377508 4652477 := bstep (se 3 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 4652477 = 1744679) B1744679
theorem B25165475 : Blo 1377508 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B4415143 : Blo 1377508 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B3727259 : Blo 1377508 3727259 := bstep (se 1 (by rfl) ⟨2795444, by rfl⟩ : syracuseStep 3727259 = 5590889) B5590889
theorem B2793439 : Blo 1377508 2793439 := bstep (se 1 (by rfl) ⟨2095079, by rfl⟩ : syracuseStep 2793439 = 4190159) B4190159
theorem B3924071 : Blo 1377508 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B9691265 : Blo 1377508 9691265 := bstep (se 2 (by rfl) ⟨3634224, by rfl⟩ : syracuseStep 9691265 = 7268449) B7268449
theorem B4653449 : Blo 1377508 4653449 := bstep (se 2 (by rfl) ⟨1745043, by rfl⟩ : syracuseStep 4653449 = 3490087) B3490087
theorem B16777759 : Blo 1377508 16777759 := bstep (se 1 (by rfl) ⟨12583319, by rfl⟩ : syracuseStep 16777759 = 25166639) B25166639
theorem B68903621 : Blo 1377508 68903621 := bstep (se 4 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 68903621 = 12919429) B12919429
theorem B3490523 : Blo 1377508 3490523 := bstep (se 1 (by rfl) ⟨2617892, by rfl⟩ : syracuseStep 3490523 = 5235785) B5235785
theorem B7078697 : Blo 1377508 7078697 := bstep (se 2 (by rfl) ⟨2654511, by rfl⟩ : syracuseStep 7078697 = 5309023) B5309023
theorem B8946503 : Blo 1377508 8946503 := bstep (se 1 (by rfl) ⟨6709877, by rfl⟩ : syracuseStep 8946503 = 13419755) B13419755
theorem B30237583 : Blo 1377508 30237583 := bstep (se 1 (by rfl) ⟨22678187, by rfl⟩ : syracuseStep 30237583 = 45356375) B45356375
theorem B2794559 : Blo 1377508 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B3777599 : Blo 1377508 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B3491039 : Blo 1377508 3491039 := bstep (se 1 (by rfl) ⟨2618279, by rfl⟩ : syracuseStep 3491039 = 5236559) B5236559
theorem B1377531 : Blo 1377508 1377531 := bstep (se 1 (by rfl) ⟨1033148, by rfl⟩ : syracuseStep 1377531 = 2066297) B2066297
theorem B6981227 : Blo 1377508 6981227 := bstep (se 1 (by rfl) ⟨5235920, by rfl⟩ : syracuseStep 6981227 = 10471841) B10471841
theorem B1378031 : Blo 1377508 1378031 := bstep (se 1 (by rfl) ⟨1033523, by rfl⟩ : syracuseStep 1378031 = 2067047) B2067047
theorem B1378159 : Blo 1377508 1378159 := bstep (se 1 (by rfl) ⟨1033619, by rfl⟩ : syracuseStep 1378159 = 2067239) B2067239
theorem B2066411 : Blo 1377508 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B26503159 : Blo 1377508 26503159 := bstep (se 1 (by rfl) ⟨19877369, by rfl⟩ : syracuseStep 26503159 = 39754739) B39754739
theorem B1378375 : Blo 1377508 1378375 := bstep (se 1 (by rfl) ⟨1033781, by rfl⟩ : syracuseStep 1378375 = 2067563) B2067563
theorem B8382635 : Blo 1377508 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B12576977 : Blo 1377508 12576977 := bstep (se 2 (by rfl) ⟨4716366, by rfl⟩ : syracuseStep 12576977 = 9432733) B9432733
theorem B2066663 : Blo 1377508 2066663 := bstep (se 1 (by rfl) ⟨1549997, by rfl⟩ : syracuseStep 2066663 = 3099995) B3099995
theorem B1378535 : Blo 1377508 1378535 := bstep (se 1 (by rfl) ⟨1033901, by rfl⟩ : syracuseStep 1378535 = 2067803) B2067803
theorem B1378555 : Blo 1377508 1378555 := bstep (se 1 (by rfl) ⟨1033916, by rfl⟩ : syracuseStep 1378555 = 2067833) B2067833
theorem B2066687 : Blo 1377508 2066687 := bstep (se 1 (by rfl) ⟨1550015, by rfl⟩ : syracuseStep 2066687 = 3100031) B3100031
theorem B1378559 : Blo 1377508 1378559 := bstep (se 1 (by rfl) ⟨1033919, by rfl⟩ : syracuseStep 1378559 = 2067839) B2067839
theorem B2066825 : Blo 1377508 2066825 := bstep (se 2 (by rfl) ⟨775059, by rfl⟩ : syracuseStep 2066825 = 1550119) B1550119
theorem B2484839 : Blo 1377508 2484839 := bstep (se 1 (by rfl) ⟨1863629, by rfl⟩ : syracuseStep 2484839 = 3727259) B3727259
theorem B1378975 : Blo 1377508 1378975 := bstep (se 1 (by rfl) ⟨1034231, by rfl⟩ : syracuseStep 1378975 = 2068463) B2068463
theorem B1378983 : Blo 1377508 1378983 := bstep (se 1 (by rfl) ⟨1034237, by rfl⟩ : syracuseStep 1378983 = 2068475) B2068475
theorem B1379023 : Blo 1377508 1379023 := bstep (se 1 (by rfl) ⟨1034267, by rfl⟩ : syracuseStep 1379023 = 2068535) B2068535
theorem B1379055 : Blo 1377508 1379055 := bstep (se 1 (by rfl) ⟨1034291, by rfl⟩ : syracuseStep 1379055 = 2068583) B2068583
theorem B3099401 : Blo 1377508 3099401 := bstep (se 2 (by rfl) ⟨1162275, by rfl⟩ : syracuseStep 3099401 = 2324551) B2324551
theorem B1379103 : Blo 1377508 1379103 := bstep (se 1 (by rfl) ⟨1034327, by rfl⟩ : syracuseStep 1379103 = 2068655) B2068655
theorem B8383337 : Blo 1377508 8383337 := bstep (se 2 (by rfl) ⟨3143751, by rfl⟩ : syracuseStep 8383337 = 6287503) B6287503
theorem B1379239 : Blo 1377508 1379239 := bstep (se 1 (by rfl) ⟨1034429, by rfl⟩ : syracuseStep 1379239 = 2068859) B2068859
theorem B5237729 : Blo 1377508 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B33516595 : Blo 1377508 33516595 := bstep (se 1 (by rfl) ⟨25137446, by rfl⟩ : syracuseStep 33516595 = 50274893) B50274893
theorem B1379419 : Blo 1377508 1379419 := bstep (se 1 (by rfl) ⟨1034564, by rfl⟩ : syracuseStep 1379419 = 2069129) B2069129
theorem B2616457 : Blo 1377508 2616457 := bstep (se 2 (by rfl) ⟨981171, by rfl⟩ : syracuseStep 2616457 = 1962343) B1962343
theorem B3099815 : Blo 1377508 3099815 := bstep (se 1 (by rfl) ⟨2324861, by rfl⟩ : syracuseStep 3099815 = 4649723) B4649723
theorem B3927305 : Blo 1377508 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B3099923 : Blo 1377508 3099923 := bstep (se 1 (by rfl) ⟨2324942, by rfl⟩ : syracuseStep 3099923 = 4649885) B4649885
theorem B1551775 : Blo 1377508 1551775 := bstep (se 1 (by rfl) ⟨1163831, by rfl⟩ : syracuseStep 1551775 = 2327663) B2327663
theorem B2067935 : Blo 1377508 2067935 := bstep (se 1 (by rfl) ⟨1550951, by rfl⟩ : syracuseStep 2067935 = 3101903) B3101903
theorem B2067995 : Blo 1377508 2067995 := bstep (se 1 (by rfl) ⟨1550996, by rfl⟩ : syracuseStep 2067995 = 3101993) B3101993
theorem B2068127 : Blo 1377508 2068127 := bstep (se 1 (by rfl) ⟨1551095, by rfl⟩ : syracuseStep 2068127 = 3102191) B3102191
theorem B3100391 : Blo 1377508 3100391 := bstep (se 1 (by rfl) ⟨2325293, by rfl⟩ : syracuseStep 3100391 = 4650587) B4650587
theorem B3100553 : Blo 1377508 3100553 := bstep (se 2 (by rfl) ⟨1162707, by rfl⟩ : syracuseStep 3100553 = 2325415) B2325415
theorem B2068391 : Blo 1377508 2068391 := bstep (se 1 (by rfl) ⟨1551293, by rfl⟩ : syracuseStep 2068391 = 3102587) B3102587
theorem B2068415 : Blo 1377508 2068415 := bstep (se 1 (by rfl) ⟨1551311, by rfl⟩ : syracuseStep 2068415 = 3102623) B3102623
theorem B2068571 : Blo 1377508 2068571 := bstep (se 1 (by rfl) ⟨1551428, by rfl⟩ : syracuseStep 2068571 = 3102857) B3102857
theorem B2068715 : Blo 1377508 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B2068775 : Blo 1377508 2068775 := bstep (se 1 (by rfl) ⟨1551581, by rfl⟩ : syracuseStep 2068775 = 3103163) B3103163
theorem B3141983 : Blo 1377508 3141983 := bstep (se 1 (by rfl) ⟨2356487, by rfl⟩ : syracuseStep 3141983 = 4712975) B4712975
theorem B4977065 : Blo 1377508 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B4649399 : Blo 1377508 4649399 := bstep (se 1 (by rfl) ⟨3487049, by rfl⟩ : syracuseStep 4649399 = 6974099) B6974099
theorem B42471917 : Blo 1377508 42471917 := bstep (se 3 (by rfl) ⟨7963484, by rfl⟩ : syracuseStep 42471917 = 15926969) B15926969
theorem B2069039 : Blo 1377508 2069039 := bstep (se 1 (by rfl) ⟨1551779, by rfl⟩ : syracuseStep 2069039 = 3103559) B3103559
theorem B2618075 : Blo 1377508 2618075 := bstep (se 1 (by rfl) ⟨1963556, by rfl⟩ : syracuseStep 2618075 = 3927113) B3927113
theorem B2069243 : Blo 1377508 2069243 := bstep (se 1 (by rfl) ⟨1551932, by rfl⟩ : syracuseStep 2069243 = 3103865) B3103865
theorem B8950537 : Blo 1377508 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B6976367 : Blo 1377508 6976367 := bstep (se 1 (by rfl) ⟨5232275, by rfl⟩ : syracuseStep 6976367 = 10464551) B10464551
theorem B5886857 : Blo 1377508 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B4649939 : Blo 1377508 4649939 := bstep (se 1 (by rfl) ⟨3487454, by rfl⟩ : syracuseStep 4649939 = 6974909) B6974909
theorem B3101651 : Blo 1377508 3101651 := bstep (se 1 (by rfl) ⟨2326238, by rfl⟩ : syracuseStep 3101651 = 4652477) B4652477
theorem B1963055 : Blo 1377508 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B1963129 : Blo 1377508 1963129 := bstep (se 2 (by rfl) ⟨736173, by rfl⟩ : syracuseStep 1963129 = 1472347) B1472347
theorem B1963163 : Blo 1377508 1963163 := bstep (se 1 (by rfl) ⟨1472372, by rfl⟩ : syracuseStep 1963163 = 2944745) B2944745
theorem B1471655 : Blo 1377508 1471655 := bstep (se 1 (by rfl) ⟨1103741, by rfl⟩ : syracuseStep 1471655 = 2207483) B2207483
theorem B3724585 : Blo 1377508 3724585 := bstep (se 2 (by rfl) ⟨1396719, by rfl⟩ : syracuseStep 3724585 = 2793439) B2793439
theorem B5101231 : Blo 1377508 5101231 := bstep (se 1 (by rfl) ⟨3825923, by rfl⟩ : syracuseStep 5101231 = 7651847) B7651847
theorem B8836847 : Blo 1377508 8836847 := bstep (se 1 (by rfl) ⟨6627635, by rfl⟩ : syracuseStep 8836847 = 13255271) B13255271
theorem B3487475 : Blo 1377508 3487475 := bstep (se 1 (by rfl) ⟨2615606, by rfl⟩ : syracuseStep 3487475 = 5231213) B5231213
theorem B3102911 : Blo 1377508 3102911 := bstep (se 1 (by rfl) ⟨2327183, by rfl⟩ : syracuseStep 3102911 = 4654367) B4654367
theorem B76437701 : Blo 1377508 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B16767251 : Blo 1377508 16767251 := bstep (se 1 (by rfl) ⟨12575438, by rfl⟩ : syracuseStep 16767251 = 25150877) B25150877
theorem B14907685 : Blo 1377508 14907685 := bstep (se 4 (by rfl) ⟨1397595, by rfl⟩ : syracuseStep 14907685 = 2795191) B2795191
theorem B25139497 : Blo 1377508 25139497 := bstep (se 2 (by rfl) ⟨9427311, by rfl⟩ : syracuseStep 25139497 = 18854623) B18854623
theorem B17660267 : Blo 1377508 17660267 := bstep (se 1 (by rfl) ⟨13245200, by rfl⟩ : syracuseStep 17660267 = 26490401) B26490401
theorem B4651451 : Blo 1377508 4651451 := bstep (se 1 (by rfl) ⟨3488588, by rfl⟩ : syracuseStep 4651451 = 6977177) B6977177
theorem B14137847 : Blo 1377508 14137847 := bstep (se 1 (by rfl) ⟨10603385, by rfl⟩ : syracuseStep 14137847 = 21206771) B21206771
theorem B6978311 : Blo 1377508 6978311 := bstep (se 1 (by rfl) ⟨5233733, by rfl⟩ : syracuseStep 6978311 = 10467467) B10467467
theorem B4414247 : Blo 1377508 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B4651991 : Blo 1377508 4651991 := bstep (se 1 (by rfl) ⟨3488993, by rfl⟩ : syracuseStep 4651991 = 6977987) B6977987
theorem B3489065 : Blo 1377508 3489065 := bstep (se 2 (by rfl) ⟨1308399, by rfl⟩ : syracuseStep 3489065 = 2616799) B2616799
theorem B3489095 : Blo 1377508 3489095 := bstep (se 1 (by rfl) ⟨2616821, by rfl⟩ : syracuseStep 3489095 = 5233643) B5233643
theorem B8838487 : Blo 1377508 8838487 := bstep (se 1 (by rfl) ⟨6628865, by rfl⟩ : syracuseStep 8838487 = 13257731) B13257731
theorem B7855613 : Blo 1377508 7855613 := bstep (se 3 (by rfl) ⟨1472927, by rfl⟩ : syracuseStep 7855613 = 2945855) B2945855
theorem B1941223 : Blo 1377508 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B16776983 : Blo 1377508 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B3923923 : Blo 1377508 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B5234813 : Blo 1377508 5234813 := bstep (se 3 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 5234813 = 1963055) B1963055
theorem B5235101 : Blo 1377508 5235101 := bstep (se 3 (by rfl) ⟨981581, by rfl⟩ : syracuseStep 5235101 = 1963163) B1963163
theorem B3924413 : Blo 1377508 3924413 := bstep (se 3 (by rfl) ⟨735827, by rfl⟩ : syracuseStep 3924413 = 1471655) B1471655
theorem B2327015 : Blo 1377508 2327015 := bstep (se 1 (by rfl) ⟨1745261, by rfl⟩ : syracuseStep 2327015 = 3490523) B3490523
theorem B1745383 : Blo 1377508 1745383 := bstep (se 1 (by rfl) ⟨1309037, by rfl⟩ : syracuseStep 1745383 = 2618075) B2618075
theorem B4719131 : Blo 1377508 4719131 := bstep (se 1 (by rfl) ⟨3539348, by rfl⟩ : syracuseStep 4719131 = 7078697) B7078697
theorem B5964335 : Blo 1377508 5964335 := bstep (se 1 (by rfl) ⟨4473251, by rfl⟩ : syracuseStep 5964335 = 8946503) B8946503
theorem B2327359 : Blo 1377508 2327359 := bstep (se 1 (by rfl) ⟨1745519, by rfl⟩ : syracuseStep 2327359 = 3491039) B3491039
theorem B4654151 : Blo 1377508 4654151 := bstep (se 1 (by rfl) ⟨3490613, by rfl⟩ : syracuseStep 4654151 = 6981227) B6981227
theorem B13272173 : Blo 1377508 13272173 := bstep (se 3 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 13272173 = 4977065) B4977065
theorem B5891231 : Blo 1377508 5891231 := bstep (se 1 (by rfl) ⟨4418423, by rfl⟩ : syracuseStep 5891231 = 8836847) B8836847
theorem B1377607 : Blo 1377508 1377607 := bstep (se 1 (by rfl) ⟨1033205, by rfl⟩ : syracuseStep 1377607 = 2066411) B2066411
theorem B44688793 : Blo 1377508 44688793 := bstep (se 2 (by rfl) ⟨16758297, by rfl⟩ : syracuseStep 44688793 = 33516595) B33516595
theorem B5588423 : Blo 1377508 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B1377775 : Blo 1377508 1377775 := bstep (se 1 (by rfl) ⟨1033331, by rfl⟩ : syracuseStep 1377775 = 2066663) B2066663
theorem B1377791 : Blo 1377508 1377791 := bstep (se 1 (by rfl) ⟨1033343, by rfl⟩ : syracuseStep 1377791 = 2066687) B2066687
theorem B11773511 : Blo 1377508 11773511 := bstep (se 1 (by rfl) ⟨8830133, by rfl⟩ : syracuseStep 11773511 = 17660267) B17660267
theorem B1377883 : Blo 1377508 1377883 := bstep (se 1 (by rfl) ⟨1033412, by rfl⟩ : syracuseStep 1377883 = 2066825) B2066825
theorem B1656559 : Blo 1377508 1656559 := bstep (se 1 (by rfl) ⟨1242419, by rfl⟩ : syracuseStep 1656559 = 2484839) B2484839
theorem B2066267 : Blo 1377508 2066267 := bstep (se 1 (by rfl) ⟨1549700, by rfl⟩ : syracuseStep 2066267 = 3099401) B3099401
theorem B2942831 : Blo 1377508 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B5588891 : Blo 1377508 5588891 := bstep (se 1 (by rfl) ⟨4191668, by rfl⟩ : syracuseStep 5588891 = 8383337) B8383337
theorem B3491819 : Blo 1377508 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B2066543 : Blo 1377508 2066543 := bstep (se 1 (by rfl) ⟨1549907, by rfl⟩ : syracuseStep 2066543 = 3099815) B3099815
theorem B2066615 : Blo 1377508 2066615 := bstep (se 1 (by rfl) ⟨1549961, by rfl⟩ : syracuseStep 2066615 = 3099923) B3099923
theorem B6801641 : Blo 1377508 6801641 := bstep (se 2 (by rfl) ⟨2550615, by rfl⟩ : syracuseStep 6801641 = 5101231) B5101231
theorem B1378623 : Blo 1377508 1378623 := bstep (se 1 (by rfl) ⟨1033967, by rfl⟩ : syracuseStep 1378623 = 2067935) B2067935
theorem B5237075 : Blo 1377508 5237075 := bstep (se 1 (by rfl) ⟨3927806, by rfl⟩ : syracuseStep 5237075 = 7855613) B7855613
theorem B1378663 : Blo 1377508 1378663 := bstep (se 1 (by rfl) ⟨1033997, by rfl⟩ : syracuseStep 1378663 = 2067995) B2067995
theorem B15698285 : Blo 1377508 15698285 := bstep (se 3 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 15698285 = 5886857) B5886857
theorem B1378751 : Blo 1377508 1378751 := bstep (se 1 (by rfl) ⟨1034063, by rfl⟩ : syracuseStep 1378751 = 2068127) B2068127
theorem B2066927 : Blo 1377508 2066927 := bstep (se 1 (by rfl) ⟨1550195, by rfl⟩ : syracuseStep 2066927 = 3100391) B3100391
theorem B11184655 : Blo 1377508 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B2067035 : Blo 1377508 2067035 := bstep (se 1 (by rfl) ⟨1550276, by rfl⟩ : syracuseStep 2067035 = 3100553) B3100553
theorem B1378927 : Blo 1377508 1378927 := bstep (se 1 (by rfl) ⟨1034195, by rfl⟩ : syracuseStep 1378927 = 2068391) B2068391
theorem B1378943 : Blo 1377508 1378943 := bstep (se 1 (by rfl) ⟨1034207, by rfl⟩ : syracuseStep 1378943 = 2068415) B2068415
theorem B1379047 : Blo 1377508 1379047 := bstep (se 1 (by rfl) ⟨1034285, by rfl⟩ : syracuseStep 1379047 = 2068571) B2068571
theorem B2616047 : Blo 1377508 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B1379143 : Blo 1377508 1379143 := bstep (se 1 (by rfl) ⟨1034357, by rfl⟩ : syracuseStep 1379143 = 2068715) B2068715
theorem B1379183 : Blo 1377508 1379183 := bstep (se 1 (by rfl) ⟨1034387, by rfl⟩ : syracuseStep 1379183 = 2068775) B2068775
theorem B3099599 : Blo 1377508 3099599 := bstep (se 1 (by rfl) ⟨2324699, by rfl⟩ : syracuseStep 3099599 = 4649399) B4649399
theorem B28314611 : Blo 1377508 28314611 := bstep (se 1 (by rfl) ⟨21235958, by rfl⟩ : syracuseStep 28314611 = 42471917) B42471917
theorem B1379359 : Blo 1377508 1379359 := bstep (se 1 (by rfl) ⟨1034519, by rfl⟩ : syracuseStep 1379359 = 2069039) B2069039
theorem B19876913 : Blo 1377508 19876913 := bstep (se 2 (by rfl) ⟨7453842, by rfl⟩ : syracuseStep 19876913 = 14907685) B14907685
theorem B45935747 : Blo 1377508 45935747 := bstep (se 1 (by rfl) ⟨34451810, by rfl⟩ : syracuseStep 45935747 = 68903621) B68903621
theorem B1379495 : Blo 1377508 1379495 := bstep (se 1 (by rfl) ⟨1034621, by rfl⟩ : syracuseStep 1379495 = 2069243) B2069243
theorem B3099959 : Blo 1377508 3099959 := bstep (se 1 (by rfl) ⟨2324969, by rfl⟩ : syracuseStep 3099959 = 4649939) B4649939
theorem B2067767 : Blo 1377508 2067767 := bstep (se 1 (by rfl) ⟨1550825, by rfl⟩ : syracuseStep 2067767 = 3101651) B3101651
theorem B10472813 : Blo 1377508 10472813 := bstep (se 3 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 10472813 = 3927305) B3927305
theorem B2518399 : Blo 1377508 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B40316777 : Blo 1377508 40316777 := bstep (se 2 (by rfl) ⟨15118791, by rfl⟩ : syracuseStep 40316777 = 30237583) B30237583
theorem B2068607 : Blo 1377508 2068607 := bstep (se 1 (by rfl) ⟨1551455, by rfl⟩ : syracuseStep 2068607 = 3102911) B3102911
theorem B50958467 : Blo 1377508 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B8384651 : Blo 1377508 8384651 := bstep (se 1 (by rfl) ⟨6288488, by rfl⟩ : syracuseStep 8384651 = 12576977) B12576977
theorem B2617505 : Blo 1377508 2617505 := bstep (se 2 (by rfl) ⟨981564, by rfl⟩ : syracuseStep 2617505 = 1963129) B1963129
theorem B11178167 : Blo 1377508 11178167 := bstep (se 1 (by rfl) ⟨8383625, by rfl⟩ : syracuseStep 11178167 = 16767251) B16767251
theorem B3100967 : Blo 1377508 3100967 := bstep (se 1 (by rfl) ⟨2325725, by rfl⟩ : syracuseStep 3100967 = 4651451) B4651451
theorem B9425231 : Blo 1377508 9425231 := bstep (se 1 (by rfl) ⟨7068923, by rfl⟩ : syracuseStep 9425231 = 14137847) B14137847
theorem B11784649 : Blo 1377508 11784649 := bstep (se 2 (by rfl) ⟨4419243, by rfl⟩ : syracuseStep 11784649 = 8838487) B8838487
theorem B2069033 : Blo 1377508 2069033 := bstep (se 2 (by rfl) ⟨775887, by rfl⟩ : syracuseStep 2069033 = 1551775) B1551775
theorem B3101327 : Blo 1377508 3101327 := bstep (se 1 (by rfl) ⟨2325995, by rfl⟩ : syracuseStep 3101327 = 4651991) B4651991
theorem B5231897 : Blo 1377508 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B35337545 : Blo 1377508 35337545 := bstep (se 2 (by rfl) ⟨13251579, by rfl⟩ : syracuseStep 35337545 = 26503159) B26503159
theorem B6460843 : Blo 1377508 6460843 := bstep (se 1 (by rfl) ⟨4845632, by rfl⟩ : syracuseStep 6460843 = 9691265) B9691265
theorem B7452157 : Blo 1377508 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B2094655 : Blo 1377508 2094655 := bstep (se 1 (by rfl) ⟨1570991, by rfl⟩ : syracuseStep 2094655 = 3141983) B3141983
theorem B3102299 : Blo 1377508 3102299 := bstep (se 1 (by rfl) ⟨2326724, by rfl⟩ : syracuseStep 3102299 = 4653449) B4653449
theorem B33519329 : Blo 1377508 33519329 := bstep (se 2 (by rfl) ⟨12569748, by rfl⟩ : syracuseStep 33519329 = 25139497) B25139497
theorem B4650911 : Blo 1377508 4650911 := bstep (se 1 (by rfl) ⟨3488183, by rfl⟩ : syracuseStep 4650911 = 6976367) B6976367
theorem B22370345 : Blo 1377508 22370345 := bstep (se 2 (by rfl) ⟨8388879, by rfl⟩ : syracuseStep 22370345 = 16777759) B16777759
theorem B11934049 : Blo 1377508 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B2324983 : Blo 1377508 2324983 := bstep (se 1 (by rfl) ⟨1743737, by rfl⟩ : syracuseStep 2324983 = 3487475) B3487475
theorem B3488609 : Blo 1377508 3488609 := bstep (se 2 (by rfl) ⟨1308228, by rfl⟩ : syracuseStep 3488609 = 2616457) B2616457
theorem B19864453 : Blo 1377508 19864453 := bstep (se 4 (by rfl) ⟨1862292, by rfl⟩ : syracuseStep 19864453 = 3724585) B3724585
theorem B4652207 : Blo 1377508 4652207 := bstep (se 1 (by rfl) ⟨3489155, by rfl⟩ : syracuseStep 4652207 = 6978311) B6978311
theorem B2326043 : Blo 1377508 2326043 := bstep (se 1 (by rfl) ⟨1744532, by rfl⟩ : syracuseStep 2326043 = 3489065) B3489065
theorem B2326063 : Blo 1377508 2326063 := bstep (se 1 (by rfl) ⟨1744547, by rfl⟩ : syracuseStep 2326063 = 3489095) B3489095
theorem B2588297 : Blo 1377508 2588297 := bstep (se 2 (by rfl) ⟨970611, by rfl⟩ : syracuseStep 2588297 = 1941223) B1941223
theorem B3489875 : Blo 1377508 3489875 := bstep (se 1 (by rfl) ⟨2617406, by rfl⟩ : syracuseStep 3489875 = 5234813) B5234813
theorem B33972311 : Blo 1377508 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B1745003 : Blo 1377508 1745003 := bstep (se 1 (by rfl) ⟨1308752, by rfl⟩ : syracuseStep 1745003 = 2617505) B2617505
theorem B6283487 : Blo 1377508 6283487 := bstep (se 1 (by rfl) ⟨4712615, by rfl⟩ : syracuseStep 6283487 = 9425231) B9425231
theorem B3490067 : Blo 1377508 3490067 := bstep (se 1 (by rfl) ⟨2617550, by rfl⟩ : syracuseStep 3490067 = 5235101) B5235101
theorem B3146087 : Blo 1377508 3146087 := bstep (se 1 (by rfl) ⟨2359565, by rfl⟩ : syracuseStep 3146087 = 4719131) B4719131
theorem B15712865 : Blo 1377508 15712865 := bstep (se 2 (by rfl) ⟨5892324, by rfl⟩ : syracuseStep 15712865 = 11784649) B11784649
theorem B2327177 : Blo 1377508 2327177 := bstep (se 2 (by rfl) ⟨872691, by rfl⟩ : syracuseStep 2327177 = 1745383) B1745383
theorem B8848115 : Blo 1377508 8848115 := bstep (se 1 (by rfl) ⟨6636086, by rfl⟩ : syracuseStep 8848115 = 13272173) B13272173
theorem B7849007 : Blo 1377508 7849007 := bstep (se 1 (by rfl) ⟨5886755, by rfl⟩ : syracuseStep 7849007 = 11773511) B11773511
theorem B26485937 : Blo 1377508 26485937 := bstep (se 2 (by rfl) ⟨9932226, by rfl⟩ : syracuseStep 26485937 = 19864453) B19864453
theorem B1377511 : Blo 1377508 1377511 := bstep (se 1 (by rfl) ⟨1033133, by rfl⟩ : syracuseStep 1377511 = 2066267) B2066267
theorem B2327879 : Blo 1377508 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1377695 : Blo 1377508 1377695 := bstep (se 1 (by rfl) ⟨1033271, by rfl⟩ : syracuseStep 1377695 = 2066543) B2066543
theorem B27608501 : Blo 1377508 27608501 := bstep (se 5 (by rfl) ⟨1294148, by rfl⟩ : syracuseStep 27608501 = 2588297) B2588297
theorem B1377743 : Blo 1377508 1377743 := bstep (se 1 (by rfl) ⟨1033307, by rfl⟩ : syracuseStep 1377743 = 2066615) B2066615
theorem B3491383 : Blo 1377508 3491383 := bstep (se 1 (by rfl) ⟨2618537, by rfl⟩ : syracuseStep 3491383 = 5237075) B5237075
theorem B1377951 : Blo 1377508 1377951 := bstep (se 1 (by rfl) ⟨1033463, by rfl⟩ : syracuseStep 1377951 = 2066927) B2066927
theorem B1378023 : Blo 1377508 1378023 := bstep (se 1 (by rfl) ⟨1033517, by rfl⟩ : syracuseStep 1378023 = 2067035) B2067035
theorem B2066399 : Blo 1377508 2066399 := bstep (se 1 (by rfl) ⟨1549799, by rfl⟩ : syracuseStep 2066399 = 3099599) B3099599
theorem B18876407 : Blo 1377508 18876407 := bstep (se 1 (by rfl) ⟨14157305, by rfl⟩ : syracuseStep 18876407 = 28314611) B28314611
theorem B30623831 : Blo 1377508 30623831 := bstep (se 1 (by rfl) ⟨22967873, by rfl⟩ : syracuseStep 30623831 = 45935747) B45935747
theorem B2066639 : Blo 1377508 2066639 := bstep (se 1 (by rfl) ⟨1549979, by rfl⟩ : syracuseStep 2066639 = 3099959) B3099959
theorem B1378511 : Blo 1377508 1378511 := bstep (se 1 (by rfl) ⟨1033883, by rfl⟩ : syracuseStep 1378511 = 2067767) B2067767
theorem B6981875 : Blo 1377508 6981875 := bstep (se 1 (by rfl) ⟨5236406, by rfl⟩ : syracuseStep 6981875 = 10472813) B10472813
theorem B1550695 : Blo 1377508 1550695 := bstep (se 1 (by rfl) ⟨1163021, by rfl⟩ : syracuseStep 1550695 = 2326043) B2326043
theorem B1379071 : Blo 1377508 1379071 := bstep (se 1 (by rfl) ⟨1034303, by rfl⟩ : syracuseStep 1379071 = 2068607) B2068607
theorem B5589767 : Blo 1377508 5589767 := bstep (se 1 (by rfl) ⟨4192325, by rfl⟩ : syracuseStep 5589767 = 8384651) B8384651
theorem B2067311 : Blo 1377508 2067311 := bstep (se 1 (by rfl) ⟨1550483, by rfl⟩ : syracuseStep 2067311 = 3100967) B3100967
theorem B2616275 : Blo 1377508 2616275 := bstep (se 1 (by rfl) ⟨1962206, by rfl⟩ : syracuseStep 2616275 = 3924413) B3924413
theorem B1551343 : Blo 1377508 1551343 := bstep (se 1 (by rfl) ⟨1163507, by rfl⟩ : syracuseStep 1551343 = 2327015) B2327015
theorem B1379355 : Blo 1377508 1379355 := bstep (se 1 (by rfl) ⟨1034516, by rfl⟩ : syracuseStep 1379355 = 2069033) B2069033
theorem B3976223 : Blo 1377508 3976223 := bstep (se 1 (by rfl) ⟨2982167, by rfl⟩ : syracuseStep 3976223 = 5964335) B5964335
theorem B2067551 : Blo 1377508 2067551 := bstep (se 1 (by rfl) ⟨1550663, by rfl⟩ : syracuseStep 2067551 = 3101327) B3101327
theorem B15912065 : Blo 1377508 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B3099977 : Blo 1377508 3099977 := bstep (se 2 (by rfl) ⟨1162491, by rfl⟩ : syracuseStep 3099977 = 2324983) B2324983
theorem B14912873 : Blo 1377508 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B2068199 : Blo 1377508 2068199 := bstep (se 1 (by rfl) ⟨1551149, by rfl⟩ : syracuseStep 2068199 = 3102299) B3102299
theorem B3100607 : Blo 1377508 3100607 := bstep (se 1 (by rfl) ⟨2325455, by rfl⟩ : syracuseStep 3100607 = 4650911) B4650911
theorem B14913563 : Blo 1377508 14913563 := bstep (se 1 (by rfl) ⟨11185172, by rfl⟩ : syracuseStep 14913563 = 22370345) B22370345
theorem B4534427 : Blo 1377508 4534427 := bstep (se 1 (by rfl) ⟨3400820, by rfl⟩ : syracuseStep 4534427 = 6801641) B6801641
theorem B10465523 : Blo 1377508 10465523 := bstep (se 1 (by rfl) ⟨7849142, by rfl⟩ : syracuseStep 10465523 = 15698285) B15698285
theorem B59585057 : Blo 1377508 59585057 := bstep (se 2 (by rfl) ⟨22344396, by rfl⟩ : syracuseStep 59585057 = 44688793) B44688793
theorem B8614457 : Blo 1377508 8614457 := bstep (se 2 (by rfl) ⟨3230421, by rfl⟩ : syracuseStep 8614457 = 6460843) B6460843
theorem B13251275 : Blo 1377508 13251275 := bstep (se 1 (by rfl) ⟨9938456, by rfl⟩ : syracuseStep 13251275 = 19876913) B19876913
theorem B3101417 : Blo 1377508 3101417 := bstep (se 2 (by rfl) ⟨1163031, by rfl⟩ : syracuseStep 3101417 = 2326063) B2326063
theorem B3101471 : Blo 1377508 3101471 := bstep (se 1 (by rfl) ⟨2326103, by rfl⟩ : syracuseStep 3101471 = 4652207) B4652207
theorem B2208745 : Blo 1377508 2208745 := bstep (se 2 (by rfl) ⟨828279, by rfl⟩ : syracuseStep 2208745 = 1656559) B1656559
theorem B15709949 : Blo 1377508 15709949 := bstep (se 3 (by rfl) ⟨2945615, by rfl⟩ : syracuseStep 15709949 = 5891231) B5891231
theorem B29808445 : Blo 1377508 29808445 := bstep (se 3 (by rfl) ⟨5589083, by rfl⟩ : syracuseStep 29808445 = 11178167) B11178167
theorem B3102767 : Blo 1377508 3102767 := bstep (se 1 (by rfl) ⟨2327075, by rfl⟩ : syracuseStep 3102767 = 4654151) B4654151
theorem B3487931 : Blo 1377508 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B23558363 : Blo 1377508 23558363 := bstep (se 1 (by rfl) ⟨17668772, by rfl⟩ : syracuseStep 23558363 = 35337545) B35337545
theorem B3725615 : Blo 1377508 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B3103145 : Blo 1377508 3103145 := bstep (se 2 (by rfl) ⟨1163679, by rfl⟩ : syracuseStep 3103145 = 2327359) B2327359
theorem B22346219 : Blo 1377508 22346219 := bstep (se 1 (by rfl) ⟨16759664, by rfl⟩ : syracuseStep 22346219 = 33519329) B33519329
theorem B3725927 : Blo 1377508 3725927 := bstep (se 1 (by rfl) ⟨2794445, by rfl⟩ : syracuseStep 3725927 = 5588891) B5588891
theorem B1744031 : Blo 1377508 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B3357865 : Blo 1377508 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B2325739 : Blo 1377508 2325739 := bstep (se 1 (by rfl) ⟨1744304, by rfl⟩ : syracuseStep 2325739 = 3488609) B3488609
theorem B9936209 : Blo 1377508 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B2792873 : Blo 1377508 2792873 := bstep (se 2 (by rfl) ⟨1047327, by rfl⟩ : syracuseStep 2792873 = 2094655) B2094655
theorem B7847549 : Blo 1377508 7847549 := bstep (se 3 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 7847549 = 2942831) B2942831
theorem B26877851 : Blo 1377508 26877851 := bstep (se 1 (by rfl) ⟨20158388, by rfl⟩ : syracuseStep 26877851 = 40316777) B40316777
theorem B2326583 : Blo 1377508 2326583 := bstep (se 1 (by rfl) ⟨1744937, by rfl⟩ : syracuseStep 2326583 = 3489875) B3489875
theorem B3022951 : Blo 1377508 3022951 := bstep (se 1 (by rfl) ⟨2267213, by rfl⟩ : syracuseStep 3022951 = 4534427) B4534427
theorem B2326711 : Blo 1377508 2326711 := bstep (se 1 (by rfl) ⟨1745033, by rfl⟩ : syracuseStep 2326711 = 3490067) B3490067
theorem B4653341 : Blo 1377508 4653341 := bstep (se 3 (by rfl) ⟨872501, by rfl⟩ : syracuseStep 4653341 = 1745003) B1745003
theorem B39723371 : Blo 1377508 39723371 := bstep (se 1 (by rfl) ⟨29792528, by rfl⟩ : syracuseStep 39723371 = 59585057) B59585057
theorem B5742971 : Blo 1377508 5742971 := bstep (se 1 (by rfl) ⟨4307228, by rfl⟩ : syracuseStep 5742971 = 8614457) B8614457
theorem B5898743 : Blo 1377508 5898743 := bstep (se 1 (by rfl) ⟨4424057, by rfl⟩ : syracuseStep 5898743 = 8848115) B8848115
theorem B17908613 : Blo 1377508 17908613 := bstep (se 4 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 17908613 = 3357865) B3357865
theorem B8389565 : Blo 1377508 8389565 := bstep (se 3 (by rfl) ⟨1573043, by rfl⟩ : syracuseStep 8389565 = 3146087) B3146087
theorem B1377599 : Blo 1377508 1377599 := bstep (se 1 (by rfl) ⟨1033199, by rfl⟩ : syracuseStep 1377599 = 2066399) B2066399
theorem B20415887 : Blo 1377508 20415887 := bstep (se 1 (by rfl) ⟨15311915, by rfl⟩ : syracuseStep 20415887 = 30623831) B30623831
theorem B1377759 : Blo 1377508 1377759 := bstep (se 1 (by rfl) ⟨1033319, by rfl⟩ : syracuseStep 1377759 = 2066639) B2066639
theorem B15705575 : Blo 1377508 15705575 := bstep (se 1 (by rfl) ⟨11779181, by rfl⟩ : syracuseStep 15705575 = 23558363) B23558363
theorem B4654583 : Blo 1377508 4654583 := bstep (se 1 (by rfl) ⟨3490937, by rfl⟩ : syracuseStep 4654583 = 6981875) B6981875
theorem B2483951 : Blo 1377508 2483951 := bstep (se 1 (by rfl) ⟨1862963, by rfl⟩ : syracuseStep 2483951 = 3725927) B3725927
theorem B1378207 : Blo 1377508 1378207 := bstep (se 1 (by rfl) ⟨1033655, by rfl⟩ : syracuseStep 1378207 = 2067311) B2067311
theorem B1378367 : Blo 1377508 1378367 := bstep (se 1 (by rfl) ⟨1033775, by rfl⟩ : syracuseStep 1378367 = 2067551) B2067551
theorem B4655177 : Blo 1377508 4655177 := bstep (se 2 (by rfl) ⟨1745691, by rfl⟩ : syracuseStep 4655177 = 3491383) B3491383
theorem B2066651 : Blo 1377508 2066651 := bstep (se 1 (by rfl) ⟨1549988, by rfl⟩ : syracuseStep 2066651 = 3099977) B3099977
theorem B1861915 : Blo 1377508 1861915 := bstep (se 1 (by rfl) ⟨1396436, by rfl⟩ : syracuseStep 1861915 = 2792873) B2792873
theorem B1378799 : Blo 1377508 1378799 := bstep (se 1 (by rfl) ⟨1034099, by rfl⟩ : syracuseStep 1378799 = 2068199) B2068199
theorem B17918567 : Blo 1377508 17918567 := bstep (se 1 (by rfl) ⟨13438925, by rfl⟩ : syracuseStep 17918567 = 26877851) B26877851
theorem B2067071 : Blo 1377508 2067071 := bstep (se 1 (by rfl) ⟨1550303, by rfl⟩ : syracuseStep 2067071 = 3100607) B3100607
theorem B10603261 : Blo 1377508 10603261 := bstep (se 3 (by rfl) ⟨1988111, by rfl⟩ : syracuseStep 10603261 = 3976223) B3976223
theorem B4188991 : Blo 1377508 4188991 := bstep (se 1 (by rfl) ⟨3141743, by rfl⟩ : syracuseStep 4188991 = 6283487) B6283487
theorem B1551451 : Blo 1377508 1551451 := bstep (se 1 (by rfl) ⟨1163588, by rfl⟩ : syracuseStep 1551451 = 2327177) B2327177
theorem B8834183 : Blo 1377508 8834183 := bstep (se 1 (by rfl) ⟨6625637, by rfl⟩ : syracuseStep 8834183 = 13251275) B13251275
theorem B2067593 : Blo 1377508 2067593 := bstep (se 2 (by rfl) ⟨775347, by rfl⟩ : syracuseStep 2067593 = 1550695) B1550695
theorem B2067611 : Blo 1377508 2067611 := bstep (se 1 (by rfl) ⟨1550708, by rfl⟩ : syracuseStep 2067611 = 3101417) B3101417
theorem B2067647 : Blo 1377508 2067647 := bstep (se 1 (by rfl) ⟨1550735, by rfl⟩ : syracuseStep 2067647 = 3101471) B3101471
theorem B17657291 : Blo 1377508 17657291 := bstep (se 1 (by rfl) ⟨13242968, by rfl⟩ : syracuseStep 17657291 = 26485937) B26485937
theorem B1551919 : Blo 1377508 1551919 := bstep (se 1 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 1551919 = 2327879) B2327879
theorem B10473299 : Blo 1377508 10473299 := bstep (se 1 (by rfl) ⟨7854974, by rfl⟩ : syracuseStep 10473299 = 15709949) B15709949
theorem B2944993 : Blo 1377508 2944993 := bstep (se 2 (by rfl) ⟨1104372, by rfl⟩ : syracuseStep 2944993 = 2208745) B2208745
theorem B2068457 : Blo 1377508 2068457 := bstep (se 2 (by rfl) ⟨775671, by rfl⟩ : syracuseStep 2068457 = 1551343) B1551343
theorem B2068511 : Blo 1377508 2068511 := bstep (se 1 (by rfl) ⟨1551383, by rfl⟩ : syracuseStep 2068511 = 3102767) B3102767
theorem B2068763 : Blo 1377508 2068763 := bstep (se 1 (by rfl) ⟨1551572, by rfl⟩ : syracuseStep 2068763 = 3103145) B3103145
theorem B3100985 : Blo 1377508 3100985 := bstep (se 2 (by rfl) ⟨1162869, by rfl⟩ : syracuseStep 3100985 = 2325739) B2325739
theorem B14897479 : Blo 1377508 14897479 := bstep (se 1 (by rfl) ⟨11173109, by rfl⟩ : syracuseStep 14897479 = 22346219) B22346219
theorem B14906045 : Blo 1377508 14906045 := bstep (se 3 (by rfl) ⟨2794883, by rfl⟩ : syracuseStep 14906045 = 5589767) B5589767
theorem B6624139 : Blo 1377508 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B9941915 : Blo 1377508 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B39744593 : Blo 1377508 39744593 := bstep (se 2 (by rfl) ⟨14904222, by rfl⟩ : syracuseStep 39744593 = 29808445) B29808445
theorem B5231699 : Blo 1377508 5231699 := bstep (se 1 (by rfl) ⟨3923774, by rfl⟩ : syracuseStep 5231699 = 7847549) B7847549
theorem B50337085 : Blo 1377508 50337085 := bstep (se 3 (by rfl) ⟨9438203, by rfl⟩ : syracuseStep 50337085 = 18876407) B18876407
theorem B22648207 : Blo 1377508 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B39769501 : Blo 1377508 39769501 := bstep (se 3 (by rfl) ⟨7456781, by rfl⟩ : syracuseStep 39769501 = 14913563) B14913563
theorem B6977015 : Blo 1377508 6977015 := bstep (se 1 (by rfl) ⟨5232761, by rfl⟩ : syracuseStep 6977015 = 10465523) B10465523
theorem B42432173 : Blo 1377508 42432173 := bstep (se 3 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 42432173 = 15912065) B15912065
theorem B10475243 : Blo 1377508 10475243 := bstep (se 1 (by rfl) ⟨7856432, by rfl⟩ : syracuseStep 10475243 = 15712865) B15712865
theorem B4650749 : Blo 1377508 4650749 := bstep (se 3 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 4650749 = 1744031) B1744031
theorem B5232671 : Blo 1377508 5232671 := bstep (se 1 (by rfl) ⟨3924503, by rfl⟩ : syracuseStep 5232671 = 7849007) B7849007
theorem B9934973 : Blo 1377508 9934973 := bstep (se 3 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 9934973 = 3725615) B3725615
theorem B18405667 : Blo 1377508 18405667 := bstep (se 1 (by rfl) ⟨13804250, by rfl⟩ : syracuseStep 18405667 = 27608501) B27608501
theorem B2325287 : Blo 1377508 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B1744183 : Blo 1377508 1744183 := bstep (se 1 (by rfl) ⟨1308137, by rfl⟩ : syracuseStep 1744183 = 2616275) B2616275
theorem B4030601 : Blo 1377508 4030601 := bstep (se 2 (by rfl) ⟨1511475, by rfl⟩ : syracuseStep 4030601 = 3022951) B3022951
theorem B3932495 : Blo 1377508 3932495 := bstep (se 1 (by rfl) ⟨2949371, by rfl⟩ : syracuseStep 3932495 = 5898743) B5898743
theorem B2482553 : Blo 1377508 2482553 := bstep (se 2 (by rfl) ⟨930957, by rfl⟩ : syracuseStep 2482553 = 1861915) B1861915
theorem B9937363 : Blo 1377508 9937363 := bstep (se 1 (by rfl) ⟨7453022, by rfl⟩ : syracuseStep 9937363 = 14906045) B14906045
theorem B6627943 : Blo 1377508 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B10470383 : Blo 1377508 10470383 := bstep (se 1 (by rfl) ⟨7852787, by rfl⟩ : syracuseStep 10470383 = 15705575) B15705575
theorem B28288115 : Blo 1377508 28288115 := bstep (se 1 (by rfl) ⟨21216086, by rfl⟩ : syracuseStep 28288115 = 42432173) B42432173
theorem B8832185 : Blo 1377508 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B1377767 : Blo 1377508 1377767 := bstep (se 1 (by rfl) ⟨1033325, by rfl⟩ : syracuseStep 1377767 = 2066651) B2066651
theorem B11945711 : Blo 1377508 11945711 := bstep (se 1 (by rfl) ⟨8959283, by rfl⟩ : syracuseStep 11945711 = 17918567) B17918567
theorem B1378047 : Blo 1377508 1378047 := bstep (se 1 (by rfl) ⟨1033535, by rfl⟩ : syracuseStep 1378047 = 2067071) B2067071
theorem B30197609 : Blo 1377508 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B1550191 : Blo 1377508 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B1378395 : Blo 1377508 1378395 := bstep (se 1 (by rfl) ⟨1033796, by rfl⟩ : syracuseStep 1378395 = 2067593) B2067593
theorem B1378407 : Blo 1377508 1378407 := bstep (se 1 (by rfl) ⟨1033805, by rfl⟩ : syracuseStep 1378407 = 2067611) B2067611
theorem B1378431 : Blo 1377508 1378431 := bstep (se 1 (by rfl) ⟨1033823, by rfl⟩ : syracuseStep 1378431 = 2067647) B2067647
theorem B6982199 : Blo 1377508 6982199 := bstep (se 1 (by rfl) ⟨5236649, by rfl⟩ : syracuseStep 6982199 = 10473299) B10473299
theorem B3926657 : Blo 1377508 3926657 := bstep (se 2 (by rfl) ⟨1472496, by rfl⟩ : syracuseStep 3926657 = 2944993) B2944993
theorem B1378971 : Blo 1377508 1378971 := bstep (se 1 (by rfl) ⟨1034228, by rfl⟩ : syracuseStep 1378971 = 2068457) B2068457
theorem B1379007 : Blo 1377508 1379007 := bstep (se 1 (by rfl) ⟨1034255, by rfl⟩ : syracuseStep 1379007 = 2068511) B2068511
theorem B1551055 : Blo 1377508 1551055 := bstep (se 1 (by rfl) ⟨1163291, by rfl⟩ : syracuseStep 1551055 = 2326583) B2326583
theorem B1379175 : Blo 1377508 1379175 := bstep (se 1 (by rfl) ⟨1034381, by rfl⟩ : syracuseStep 1379175 = 2068763) B2068763
theorem B2067323 : Blo 1377508 2067323 := bstep (se 1 (by rfl) ⟨1550492, by rfl⟩ : syracuseStep 2067323 = 3100985) B3100985
theorem B3828647 : Blo 1377508 3828647 := bstep (se 1 (by rfl) ⟨2871485, by rfl⟩ : syracuseStep 3828647 = 5742971) B5742971
theorem B11939075 : Blo 1377508 11939075 := bstep (se 1 (by rfl) ⟨8954306, by rfl⟩ : syracuseStep 11939075 = 17908613) B17908613
theorem B26496395 : Blo 1377508 26496395 := bstep (se 1 (by rfl) ⟨19872296, by rfl⟩ : syracuseStep 26496395 = 39744593) B39744593
theorem B13610591 : Blo 1377508 13610591 := bstep (se 1 (by rfl) ⟨10207943, by rfl⟩ : syracuseStep 13610591 = 20415887) B20415887
theorem B6983495 : Blo 1377508 6983495 := bstep (se 1 (by rfl) ⟨5237621, by rfl⟩ : syracuseStep 6983495 = 10475243) B10475243
theorem B3100499 : Blo 1377508 3100499 := bstep (se 1 (by rfl) ⟨2325374, by rfl⟩ : syracuseStep 3100499 = 4650749) B4650749
theorem B6623315 : Blo 1377508 6623315 := bstep (se 1 (by rfl) ⟨4967486, by rfl⟩ : syracuseStep 6623315 = 9934973) B9934973
theorem B2068601 : Blo 1377508 2068601 := bstep (se 2 (by rfl) ⟨775725, by rfl⟩ : syracuseStep 2068601 = 1551451) B1551451
theorem B6623869 : Blo 1377508 6623869 := bstep (se 3 (by rfl) ⟨1241975, by rfl⟩ : syracuseStep 6623869 = 2483951) B2483951
theorem B2069225 : Blo 1377508 2069225 := bstep (se 2 (by rfl) ⟨775959, by rfl⟩ : syracuseStep 2069225 = 1551919) B1551919
theorem B3102227 : Blo 1377508 3102227 := bstep (se 1 (by rfl) ⟨2326670, by rfl⟩ : syracuseStep 3102227 = 4653341) B4653341
theorem B26482247 : Blo 1377508 26482247 := bstep (se 1 (by rfl) ⟨19861685, by rfl⟩ : syracuseStep 26482247 = 39723371) B39723371
theorem B3102281 : Blo 1377508 3102281 := bstep (se 2 (by rfl) ⟨1163355, by rfl⟩ : syracuseStep 3102281 = 2326711) B2326711
theorem B24540889 : Blo 1377508 24540889 := bstep (se 2 (by rfl) ⟨9202833, by rfl⟩ : syracuseStep 24540889 = 18405667) B18405667
theorem B19863305 : Blo 1377508 19863305 := bstep (se 2 (by rfl) ⟨7448739, by rfl⟩ : syracuseStep 19863305 = 14897479) B14897479
theorem B5593043 : Blo 1377508 5593043 := bstep (se 1 (by rfl) ⟨4194782, by rfl⟩ : syracuseStep 5593043 = 8389565) B8389565
theorem B3487799 : Blo 1377508 3487799 := bstep (se 1 (by rfl) ⟨2615849, by rfl⟩ : syracuseStep 3487799 = 5231699) B5231699
theorem B4651343 : Blo 1377508 4651343 := bstep (se 1 (by rfl) ⟨3488507, by rfl⟩ : syracuseStep 4651343 = 6977015) B6977015
theorem B14137681 : Blo 1377508 14137681 := bstep (se 2 (by rfl) ⟨5301630, by rfl⟩ : syracuseStep 14137681 = 10603261) B10603261
theorem B3103055 : Blo 1377508 3103055 := bstep (se 1 (by rfl) ⟨2327291, by rfl⟩ : syracuseStep 3103055 = 4654583) B4654583
theorem B5585321 : Blo 1377508 5585321 := bstep (se 2 (by rfl) ⟨2094495, by rfl⟩ : syracuseStep 5585321 = 4188991) B4188991
theorem B3488447 : Blo 1377508 3488447 := bstep (se 1 (by rfl) ⟨2616335, by rfl⟩ : syracuseStep 3488447 = 5232671) B5232671
theorem B3103451 : Blo 1377508 3103451 := bstep (se 1 (by rfl) ⟨2327588, by rfl⟩ : syracuseStep 3103451 = 4655177) B4655177
theorem B2325577 : Blo 1377508 2325577 := bstep (se 2 (by rfl) ⟨872091, by rfl⟩ : syracuseStep 2325577 = 1744183) B1744183
theorem B67116113 : Blo 1377508 67116113 := bstep (se 2 (by rfl) ⟨25168542, by rfl⟩ : syracuseStep 67116113 = 50337085) B50337085
theorem B53026001 : Blo 1377508 53026001 := bstep (se 2 (by rfl) ⟨19884750, by rfl⟩ : syracuseStep 53026001 = 39769501) B39769501
theorem B5889455 : Blo 1377508 5889455 := bstep (se 1 (by rfl) ⟨4417091, by rfl⟩ : syracuseStep 5889455 = 8834183) B8834183
theorem B11771527 : Blo 1377508 11771527 := bstep (se 1 (by rfl) ⟨8828645, by rfl⟩ : syracuseStep 11771527 = 17657291) B17657291
theorem B4415543 : Blo 1377508 4415543 := bstep (se 1 (by rfl) ⟨3311657, by rfl⟩ : syracuseStep 4415543 = 6623315) B6623315
theorem B2621663 : Blo 1377508 2621663 := bstep (se 1 (by rfl) ⟨1966247, by rfl⟩ : syracuseStep 2621663 = 3932495) B3932495
theorem B1655035 : Blo 1377508 1655035 := bstep (se 1 (by rfl) ⟨1241276, by rfl⟩ : syracuseStep 1655035 = 2482553) B2482553
theorem B18850241 : Blo 1377508 18850241 := bstep (se 2 (by rfl) ⟨7068840, by rfl⟩ : syracuseStep 18850241 = 14137681) B14137681
theorem B6980255 : Blo 1377508 6980255 := bstep (se 1 (by rfl) ⟨5235191, by rfl⟩ : syracuseStep 6980255 = 10470383) B10470383
theorem B18858743 : Blo 1377508 18858743 := bstep (se 1 (by rfl) ⟨14144057, by rfl⟩ : syracuseStep 18858743 = 28288115) B28288115
theorem B8831825 : Blo 1377508 8831825 := bstep (se 2 (by rfl) ⟨3311934, by rfl⟩ : syracuseStep 8831825 = 6623869) B6623869
theorem B17654831 : Blo 1377508 17654831 := bstep (se 1 (by rfl) ⟨13241123, by rfl⟩ : syracuseStep 17654831 = 26482247) B26482247
theorem B14894189 : Blo 1377508 14894189 := bstep (se 3 (by rfl) ⟨2792660, by rfl⟩ : syracuseStep 14894189 = 5585321) B5585321
theorem B7963807 : Blo 1377508 7963807 := bstep (se 1 (by rfl) ⟨5972855, by rfl⟩ : syracuseStep 7963807 = 11945711) B11945711
theorem B3728695 : Blo 1377508 3728695 := bstep (se 1 (by rfl) ⟨2796521, by rfl⟩ : syracuseStep 3728695 = 5593043) B5593043
theorem B42993077 : Blo 1377508 42993077 := bstep (se 5 (by rfl) ⟨2015300, by rfl⟩ : syracuseStep 42993077 = 4030601) B4030601
theorem B4654799 : Blo 1377508 4654799 := bstep (se 1 (by rfl) ⟨3491099, by rfl⟩ : syracuseStep 4654799 = 6982199) B6982199
theorem B1378215 : Blo 1377508 1378215 := bstep (se 1 (by rfl) ⟨1033661, by rfl⟩ : syracuseStep 1378215 = 2067323) B2067323
theorem B35350667 : Blo 1377508 35350667 := bstep (se 1 (by rfl) ⟨26513000, by rfl⟩ : syracuseStep 35350667 = 53026001) B53026001
theorem B17664263 : Blo 1377508 17664263 := bstep (se 1 (by rfl) ⟨13248197, by rfl⟩ : syracuseStep 17664263 = 26496395) B26496395
theorem B3926303 : Blo 1377508 3926303 := bstep (se 1 (by rfl) ⟨2944727, by rfl⟩ : syracuseStep 3926303 = 5889455) B5889455
theorem B32721185 : Blo 1377508 32721185 := bstep (se 2 (by rfl) ⟨12270444, by rfl⟩ : syracuseStep 32721185 = 24540889) B24540889
theorem B2066921 : Blo 1377508 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B4655663 : Blo 1377508 4655663 := bstep (se 1 (by rfl) ⟨3491747, by rfl⟩ : syracuseStep 4655663 = 6983495) B6983495
theorem B2066999 : Blo 1377508 2066999 := bstep (se 1 (by rfl) ⟨1550249, by rfl⟩ : syracuseStep 2066999 = 3100499) B3100499
theorem B1379067 : Blo 1377508 1379067 := bstep (se 1 (by rfl) ⟨1034300, by rfl⟩ : syracuseStep 1379067 = 2068601) B2068601
theorem B1379483 : Blo 1377508 1379483 := bstep (se 1 (by rfl) ⟨1034612, by rfl⟩ : syracuseStep 1379483 = 2069225) B2069225
theorem B13249817 : Blo 1377508 13249817 := bstep (se 2 (by rfl) ⟨4968681, by rfl⟩ : syracuseStep 13249817 = 9937363) B9937363
theorem B2068073 : Blo 1377508 2068073 := bstep (se 2 (by rfl) ⟨775527, by rfl⟩ : syracuseStep 2068073 = 1551055) B1551055
theorem B2068151 : Blo 1377508 2068151 := bstep (se 1 (by rfl) ⟨1551113, by rfl⟩ : syracuseStep 2068151 = 3102227) B3102227
theorem B2068187 : Blo 1377508 2068187 := bstep (se 1 (by rfl) ⟨1551140, by rfl⟩ : syracuseStep 2068187 = 3102281) B3102281
theorem B13242203 : Blo 1377508 13242203 := bstep (se 1 (by rfl) ⟨9931652, by rfl⟩ : syracuseStep 13242203 = 19863305) B19863305
theorem B20131739 : Blo 1377508 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B3100769 : Blo 1377508 3100769 := bstep (se 2 (by rfl) ⟨1162788, by rfl⟩ : syracuseStep 3100769 = 2325577) B2325577
theorem B3100895 : Blo 1377508 3100895 := bstep (se 1 (by rfl) ⟨2325671, by rfl⟩ : syracuseStep 3100895 = 4651343) B4651343
theorem B2068703 : Blo 1377508 2068703 := bstep (se 1 (by rfl) ⟨1551527, by rfl⟩ : syracuseStep 2068703 = 3103055) B3103055
theorem B2617771 : Blo 1377508 2617771 := bstep (se 1 (by rfl) ⟨1963328, by rfl⟩ : syracuseStep 2617771 = 3926657) B3926657
theorem B2068967 : Blo 1377508 2068967 := bstep (se 1 (by rfl) ⟨1551725, by rfl⟩ : syracuseStep 2068967 = 3103451) B3103451
theorem B2552431 : Blo 1377508 2552431 := bstep (se 1 (by rfl) ⟨1914323, by rfl⟩ : syracuseStep 2552431 = 3828647) B3828647
theorem B7959383 : Blo 1377508 7959383 := bstep (se 1 (by rfl) ⟨5969537, by rfl⟩ : syracuseStep 7959383 = 11939075) B11939075
theorem B9073727 : Blo 1377508 9073727 := bstep (se 1 (by rfl) ⟨6805295, by rfl⟩ : syracuseStep 9073727 = 13610591) B13610591
theorem B5888123 : Blo 1377508 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B8837257 : Blo 1377508 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B2325199 : Blo 1377508 2325199 := bstep (se 1 (by rfl) ⟨1743899, by rfl⟩ : syracuseStep 2325199 = 3487799) B3487799
theorem B2325631 : Blo 1377508 2325631 := bstep (se 1 (by rfl) ⟨1744223, by rfl⟩ : syracuseStep 2325631 = 3488447) B3488447
theorem B44744075 : Blo 1377508 44744075 := bstep (se 1 (by rfl) ⟨33558056, by rfl⟩ : syracuseStep 44744075 = 67116113) B67116113
theorem B15695369 : Blo 1377508 15695369 := bstep (se 2 (by rfl) ⟨5885763, by rfl⟩ : syracuseStep 15695369 = 11771527) B11771527
theorem B12566827 : Blo 1377508 12566827 := bstep (se 1 (by rfl) ⟨9425120, by rfl⟩ : syracuseStep 12566827 = 18850241) B18850241
theorem B4653503 : Blo 1377508 4653503 := bstep (se 1 (by rfl) ⟨3490127, by rfl⟩ : syracuseStep 4653503 = 6980255) B6980255
theorem B3490361 : Blo 1377508 3490361 := bstep (se 2 (by rfl) ⟨1308885, by rfl⟩ : syracuseStep 3490361 = 2617771) B2617771
theorem B9929459 : Blo 1377508 9929459 := bstep (se 1 (by rfl) ⟨7447094, by rfl⟩ : syracuseStep 9929459 = 14894189) B14894189
theorem B114648205 : Blo 1377508 114648205 := bstep (se 3 (by rfl) ⟨21496538, by rfl⟩ : syracuseStep 114648205 = 42993077) B42993077
theorem B3925415 : Blo 1377508 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B10618409 : Blo 1377508 10618409 := bstep (se 2 (by rfl) ⟨3981903, by rfl⟩ : syracuseStep 10618409 = 7963807) B7963807
theorem B1377947 : Blo 1377508 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B1377999 : Blo 1377508 1377999 := bstep (se 1 (by rfl) ⟨1033499, by rfl⟩ : syracuseStep 1377999 = 2066999) B2066999
theorem B8833211 : Blo 1377508 8833211 := bstep (se 1 (by rfl) ⟨6624908, by rfl⟩ : syracuseStep 8833211 = 13249817) B13249817
theorem B29829383 : Blo 1377508 29829383 := bstep (se 1 (by rfl) ⟨22372037, by rfl⟩ : syracuseStep 29829383 = 44744075) B44744075
theorem B10463579 : Blo 1377508 10463579 := bstep (se 1 (by rfl) ⟨7847684, by rfl⟩ : syracuseStep 10463579 = 15695369) B15695369
theorem B1378715 : Blo 1377508 1378715 := bstep (se 1 (by rfl) ⟨1034036, by rfl⟩ : syracuseStep 1378715 = 2068073) B2068073
theorem B1378767 : Blo 1377508 1378767 := bstep (se 1 (by rfl) ⟨1034075, by rfl⟩ : syracuseStep 1378767 = 2068151) B2068151
theorem B1378791 : Blo 1377508 1378791 := bstep (se 1 (by rfl) ⟨1034093, by rfl⟩ : syracuseStep 1378791 = 2068187) B2068187
theorem B13421159 : Blo 1377508 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B2943695 : Blo 1377508 2943695 := bstep (se 1 (by rfl) ⟨2207771, by rfl⟩ : syracuseStep 2943695 = 4415543) B4415543
theorem B2067179 : Blo 1377508 2067179 := bstep (se 1 (by rfl) ⟨1550384, by rfl⟩ : syracuseStep 2067179 = 3100769) B3100769
theorem B1747775 : Blo 1377508 1747775 := bstep (se 1 (by rfl) ⟨1310831, by rfl⟩ : syracuseStep 1747775 = 2621663) B2621663
theorem B2067263 : Blo 1377508 2067263 := bstep (se 1 (by rfl) ⟨1550447, by rfl⟩ : syracuseStep 2067263 = 3100895) B3100895
theorem B1379135 : Blo 1377508 1379135 := bstep (se 1 (by rfl) ⟨1034351, by rfl⟩ : syracuseStep 1379135 = 2068703) B2068703
theorem B11783009 : Blo 1377508 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B1379311 : Blo 1377508 1379311 := bstep (se 1 (by rfl) ⟨1034483, by rfl⟩ : syracuseStep 1379311 = 2068967) B2068967
theorem B6049151 : Blo 1377508 6049151 := bstep (se 1 (by rfl) ⟨4536863, by rfl⟩ : syracuseStep 6049151 = 9073727) B9073727
theorem B3403241 : Blo 1377508 3403241 := bstep (se 2 (by rfl) ⟨1276215, by rfl⟩ : syracuseStep 3403241 = 2552431) B2552431
theorem B3100265 : Blo 1377508 3100265 := bstep (se 2 (by rfl) ⟨1162599, by rfl⟩ : syracuseStep 3100265 = 2325199) B2325199
theorem B8826853 : Blo 1377508 8826853 := bstep (se 4 (by rfl) ⟨827517, by rfl⟩ : syracuseStep 8826853 = 1655035) B1655035
theorem B3100841 : Blo 1377508 3100841 := bstep (se 2 (by rfl) ⟨1162815, by rfl⟩ : syracuseStep 3100841 = 2325631) B2325631
theorem B11776175 : Blo 1377508 11776175 := bstep (se 1 (by rfl) ⟨8832131, by rfl⟩ : syracuseStep 11776175 = 17664263) B17664263
theorem B2617535 : Blo 1377508 2617535 := bstep (se 1 (by rfl) ⟨1963151, by rfl⟩ : syracuseStep 2617535 = 3926303) B3926303
theorem B8828135 : Blo 1377508 8828135 := bstep (se 1 (by rfl) ⟨6621101, by rfl⟩ : syracuseStep 8828135 = 13242203) B13242203
theorem B12572495 : Blo 1377508 12572495 := bstep (se 1 (by rfl) ⟨9429371, by rfl⟩ : syracuseStep 12572495 = 18858743) B18858743
theorem B5887883 : Blo 1377508 5887883 := bstep (se 1 (by rfl) ⟨4415912, by rfl⟩ : syracuseStep 5887883 = 8831825) B8831825
theorem B5306255 : Blo 1377508 5306255 := bstep (se 1 (by rfl) ⟨3979691, by rfl⟩ : syracuseStep 5306255 = 7959383) B7959383
theorem B11769887 : Blo 1377508 11769887 := bstep (se 1 (by rfl) ⟨8827415, by rfl⟩ : syracuseStep 11769887 = 17654831) B17654831
theorem B3103199 : Blo 1377508 3103199 := bstep (se 1 (by rfl) ⟨2327399, by rfl⟩ : syracuseStep 3103199 = 4654799) B4654799
theorem B23567111 : Blo 1377508 23567111 := bstep (se 1 (by rfl) ⟨17675333, by rfl⟩ : syracuseStep 23567111 = 35350667) B35350667
theorem B21814123 : Blo 1377508 21814123 := bstep (se 1 (by rfl) ⟨16360592, by rfl⟩ : syracuseStep 21814123 = 32721185) B32721185
theorem B3103775 : Blo 1377508 3103775 := bstep (se 1 (by rfl) ⟨2327831, by rfl⟩ : syracuseStep 3103775 = 4655663) B4655663
theorem B4971593 : Blo 1377508 4971593 := bstep (se 2 (by rfl) ⟨1864347, by rfl⟩ : syracuseStep 4971593 = 3728695) B3728695
theorem B2326907 : Blo 1377508 2326907 := bstep (se 1 (by rfl) ⟨1745180, by rfl⟩ : syracuseStep 2326907 = 3490361) B3490361
theorem B6619639 : Blo 1377508 6619639 := bstep (se 1 (by rfl) ⟨4964729, by rfl⟩ : syracuseStep 6619639 = 9929459) B9929459
theorem B6980093 : Blo 1377508 6980093 := bstep (se 3 (by rfl) ⟨1308767, by rfl⟩ : syracuseStep 6980093 = 2617535) B2617535
theorem B8381663 : Blo 1377508 8381663 := bstep (se 1 (by rfl) ⟨6286247, by rfl⟩ : syracuseStep 8381663 = 12572495) B12572495
theorem B3925255 : Blo 1377508 3925255 := bstep (se 1 (by rfl) ⟨2943941, by rfl⟩ : syracuseStep 3925255 = 5887883) B5887883
theorem B152864273 : Blo 1377508 152864273 := bstep (se 2 (by rfl) ⟨57324102, by rfl⟩ : syracuseStep 152864273 = 114648205) B114648205
theorem B8947439 : Blo 1377508 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B1378119 : Blo 1377508 1378119 := bstep (se 1 (by rfl) ⟨1033589, by rfl⟩ : syracuseStep 1378119 = 2067179) B2067179
theorem B1378175 : Blo 1377508 1378175 := bstep (se 1 (by rfl) ⟨1033631, by rfl⟩ : syracuseStep 1378175 = 2067263) B2067263
theorem B4032767 : Blo 1377508 4032767 := bstep (se 1 (by rfl) ⟨3024575, by rfl⟩ : syracuseStep 4032767 = 6049151) B6049151
theorem B2066843 : Blo 1377508 2066843 := bstep (se 1 (by rfl) ⟨1550132, by rfl⟩ : syracuseStep 2066843 = 3100265) B3100265
theorem B2067227 : Blo 1377508 2067227 := bstep (se 1 (by rfl) ⟨1550420, by rfl⟩ : syracuseStep 2067227 = 3100841) B3100841
theorem B7850783 : Blo 1377508 7850783 := bstep (se 1 (by rfl) ⟨5888087, by rfl⟩ : syracuseStep 7850783 = 11776175) B11776175
theorem B16755769 : Blo 1377508 16755769 := bstep (se 2 (by rfl) ⟨6283413, by rfl⟩ : syracuseStep 16755769 = 12566827) B12566827
theorem B5885423 : Blo 1377508 5885423 := bstep (se 1 (by rfl) ⟨4414067, by rfl⟩ : syracuseStep 5885423 = 8828135) B8828135
theorem B2616943 : Blo 1377508 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B29085497 : Blo 1377508 29085497 := bstep (se 2 (by rfl) ⟨10907061, by rfl⟩ : syracuseStep 29085497 = 21814123) B21814123
theorem B28315757 : Blo 1377508 28315757 := bstep (se 3 (by rfl) ⟨5309204, by rfl⟩ : syracuseStep 28315757 = 10618409) B10618409
theorem B19886255 : Blo 1377508 19886255 := bstep (se 1 (by rfl) ⟨14914691, by rfl⟩ : syracuseStep 19886255 = 29829383) B29829383
theorem B6975719 : Blo 1377508 6975719 := bstep (se 1 (by rfl) ⟨5231789, by rfl⟩ : syracuseStep 6975719 = 10463579) B10463579
theorem B2068799 : Blo 1377508 2068799 := bstep (se 1 (by rfl) ⟨1551599, by rfl⟩ : syracuseStep 2068799 = 3103199) B3103199
theorem B1962463 : Blo 1377508 1962463 := bstep (se 1 (by rfl) ⟨1471847, by rfl⟩ : syracuseStep 1962463 = 2943695) B2943695
theorem B2069183 : Blo 1377508 2069183 := bstep (se 1 (by rfl) ⟨1551887, by rfl⟩ : syracuseStep 2069183 = 3103775) B3103775
theorem B3314395 : Blo 1377508 3314395 := bstep (se 1 (by rfl) ⟨2485796, by rfl⟩ : syracuseStep 3314395 = 4971593) B4971593
theorem B11769137 : Blo 1377508 11769137 := bstep (se 2 (by rfl) ⟨4413426, by rfl⟩ : syracuseStep 11769137 = 8826853) B8826853
theorem B3102335 : Blo 1377508 3102335 := bstep (se 1 (by rfl) ⟨2326751, by rfl⟩ : syracuseStep 3102335 = 4653503) B4653503
theorem B3537503 : Blo 1377508 3537503 := bstep (se 1 (by rfl) ⟨2653127, by rfl⟩ : syracuseStep 3537503 = 5306255) B5306255
theorem B7846591 : Blo 1377508 7846591 := bstep (se 1 (by rfl) ⟨5884943, by rfl⟩ : syracuseStep 7846591 = 11769887) B11769887
theorem B5888807 : Blo 1377508 5888807 := bstep (se 1 (by rfl) ⟨4416605, by rfl⟩ : syracuseStep 5888807 = 8833211) B8833211
theorem B15711407 : Blo 1377508 15711407 := bstep (se 1 (by rfl) ⟨11783555, by rfl⟩ : syracuseStep 15711407 = 23567111) B23567111
theorem B7855339 : Blo 1377508 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B4660733 : Blo 1377508 4660733 := bstep (se 3 (by rfl) ⟨873887, by rfl⟩ : syracuseStep 4660733 = 1747775) B1747775
theorem B2268827 : Blo 1377508 2268827 := bstep (se 1 (by rfl) ⟨1701620, by rfl⟩ : syracuseStep 2268827 = 3403241) B3403241
theorem B4653395 : Blo 1377508 4653395 := bstep (se 1 (by rfl) ⟨3490046, by rfl⟩ : syracuseStep 4653395 = 6980093) B6980093
theorem B5587775 : Blo 1377508 5587775 := bstep (se 1 (by rfl) ⟨4190831, by rfl⟩ : syracuseStep 5587775 = 8381663) B8381663
theorem B10462121 : Blo 1377508 10462121 := bstep (se 2 (by rfl) ⟨3923295, by rfl⟩ : syracuseStep 10462121 = 7846591) B7846591
theorem B101909515 : Blo 1377508 101909515 := bstep (se 1 (by rfl) ⟨76432136, by rfl⟩ : syracuseStep 101909515 = 152864273) B152864273
theorem B5964959 : Blo 1377508 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B22341025 : Blo 1377508 22341025 := bstep (se 2 (by rfl) ⟨8377884, by rfl⟩ : syracuseStep 22341025 = 16755769) B16755769
theorem B1377895 : Blo 1377508 1377895 := bstep (se 1 (by rfl) ⟨1033421, by rfl⟩ : syracuseStep 1377895 = 2066843) B2066843
theorem B1378151 : Blo 1377508 1378151 := bstep (se 1 (by rfl) ⟨1033613, by rfl⟩ : syracuseStep 1378151 = 2067227) B2067227
theorem B3925871 : Blo 1377508 3925871 := bstep (se 1 (by rfl) ⟨2944403, by rfl⟩ : syracuseStep 3925871 = 5888807) B5888807
theorem B3107155 : Blo 1377508 3107155 := bstep (se 1 (by rfl) ⟨2330366, by rfl⟩ : syracuseStep 3107155 = 4660733) B4660733
theorem B18877171 : Blo 1377508 18877171 := bstep (se 1 (by rfl) ⟨14157878, by rfl⟩ : syracuseStep 18877171 = 28315757) B28315757
theorem B13257503 : Blo 1377508 13257503 := bstep (se 1 (by rfl) ⟨9943127, by rfl⟩ : syracuseStep 13257503 = 19886255) B19886255
theorem B1379199 : Blo 1377508 1379199 := bstep (se 1 (by rfl) ⟨1034399, by rfl⟩ : syracuseStep 1379199 = 2068799) B2068799
theorem B1551271 : Blo 1377508 1551271 := bstep (se 1 (by rfl) ⟨1163453, by rfl⟩ : syracuseStep 1551271 = 2326907) B2326907
theorem B1379455 : Blo 1377508 1379455 := bstep (se 1 (by rfl) ⟨1034591, by rfl⟩ : syracuseStep 1379455 = 2069183) B2069183
theorem B2616617 : Blo 1377508 2616617 := bstep (se 2 (by rfl) ⟨981231, by rfl⟩ : syracuseStep 2616617 = 1962463) B1962463
theorem B8826185 : Blo 1377508 8826185 := bstep (se 2 (by rfl) ⟨3309819, by rfl⟩ : syracuseStep 8826185 = 6619639) B6619639
theorem B4419193 : Blo 1377508 4419193 := bstep (se 2 (by rfl) ⟨1657197, by rfl⟩ : syracuseStep 4419193 = 3314395) B3314395
theorem B2068223 : Blo 1377508 2068223 := bstep (se 1 (by rfl) ⟨1551167, by rfl⟩ : syracuseStep 2068223 = 3102335) B3102335
theorem B10473785 : Blo 1377508 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B10474271 : Blo 1377508 10474271 := bstep (se 1 (by rfl) ⟨7855703, by rfl⟩ : syracuseStep 10474271 = 15711407) B15711407
theorem B1512551 : Blo 1377508 1512551 := bstep (se 1 (by rfl) ⟨1134413, by rfl⟩ : syracuseStep 1512551 = 2268827) B2268827
theorem B4650479 : Blo 1377508 4650479 := bstep (se 1 (by rfl) ⟨3487859, by rfl⟩ : syracuseStep 4650479 = 6975719) B6975719
theorem B10754045 : Blo 1377508 10754045 := bstep (se 3 (by rfl) ⟨2016383, by rfl⟩ : syracuseStep 10754045 = 4032767) B4032767
theorem B7846091 : Blo 1377508 7846091 := bstep (se 1 (by rfl) ⟨5884568, by rfl⟩ : syracuseStep 7846091 = 11769137) B11769137
theorem B5233673 : Blo 1377508 5233673 := bstep (se 2 (by rfl) ⟨1962627, by rfl⟩ : syracuseStep 5233673 = 3925255) B3925255
theorem B2358335 : Blo 1377508 2358335 := bstep (se 1 (by rfl) ⟨1768751, by rfl⟩ : syracuseStep 2358335 = 3537503) B3537503
theorem B5233855 : Blo 1377508 5233855 := bstep (se 1 (by rfl) ⟨3925391, by rfl⟩ : syracuseStep 5233855 = 7850783) B7850783
theorem B3489257 : Blo 1377508 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B3923615 : Blo 1377508 3923615 := bstep (se 1 (by rfl) ⟨2942711, by rfl⟩ : syracuseStep 3923615 = 5885423) B5885423
theorem B19390331 : Blo 1377508 19390331 := bstep (se 1 (by rfl) ⟨14542748, by rfl⟩ : syracuseStep 19390331 = 29085497) B29085497
theorem B23536493 : Blo 1377508 23536493 := bstep (se 3 (by rfl) ⟨4413092, by rfl⟩ : syracuseStep 23536493 = 8826185) B8826185
theorem B7169363 : Blo 1377508 7169363 := bstep (se 1 (by rfl) ⟨5377022, by rfl⟩ : syracuseStep 7169363 = 10754045) B10754045
theorem B29788033 : Blo 1377508 29788033 := bstep (se 2 (by rfl) ⟨11170512, by rfl⟩ : syracuseStep 29788033 = 22341025) B22341025
theorem B5892257 : Blo 1377508 5892257 := bstep (se 2 (by rfl) ⟨2209596, by rfl⟩ : syracuseStep 5892257 = 4419193) B4419193
theorem B2615743 : Blo 1377508 2615743 := bstep (se 1 (by rfl) ⟨1961807, by rfl⟩ : syracuseStep 2615743 = 3923615) B3923615
theorem B1378815 : Blo 1377508 1378815 := bstep (se 1 (by rfl) ⟨1034111, by rfl⟩ : syracuseStep 1378815 = 2068223) B2068223
theorem B6982523 : Blo 1377508 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B4033469 : Blo 1377508 4033469 := bstep (se 3 (by rfl) ⟨756275, by rfl⟩ : syracuseStep 4033469 = 1512551) B1512551
theorem B6982847 : Blo 1377508 6982847 := bstep (se 1 (by rfl) ⟨5237135, by rfl⟩ : syracuseStep 6982847 = 10474271) B10474271
theorem B6974747 : Blo 1377508 6974747 := bstep (se 1 (by rfl) ⟨5231060, by rfl⟩ : syracuseStep 6974747 = 10462121) B10462121
theorem B25169561 : Blo 1377508 25169561 := bstep (se 2 (by rfl) ⟨9438585, by rfl⟩ : syracuseStep 25169561 = 18877171) B18877171
theorem B3100319 : Blo 1377508 3100319 := bstep (se 1 (by rfl) ⟨2325239, by rfl⟩ : syracuseStep 3100319 = 4650479) B4650479
theorem B2068361 : Blo 1377508 2068361 := bstep (se 2 (by rfl) ⟨775635, by rfl⟩ : syracuseStep 2068361 = 1551271) B1551271
theorem B2617247 : Blo 1377508 2617247 := bstep (se 1 (by rfl) ⟨1962935, by rfl⟩ : syracuseStep 2617247 = 3925871) B3925871
theorem B5230727 : Blo 1377508 5230727 := bstep (se 1 (by rfl) ⟨3923045, by rfl⟩ : syracuseStep 5230727 = 7846091) B7846091
theorem B3102263 : Blo 1377508 3102263 := bstep (se 1 (by rfl) ⟨2326697, by rfl⟩ : syracuseStep 3102263 = 4653395) B4653395
theorem B15906557 : Blo 1377508 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B4142873 : Blo 1377508 4142873 := bstep (se 2 (by rfl) ⟨1553577, by rfl⟩ : syracuseStep 4142873 = 3107155) B3107155
theorem B3725183 : Blo 1377508 3725183 := bstep (se 1 (by rfl) ⟨2793887, by rfl⟩ : syracuseStep 3725183 = 5587775) B5587775
theorem B135879353 : Blo 1377508 135879353 := bstep (se 2 (by rfl) ⟨50954757, by rfl⟩ : syracuseStep 135879353 = 101909515) B101909515
theorem B6978473 : Blo 1377508 6978473 := bstep (se 2 (by rfl) ⟨2616927, by rfl⟩ : syracuseStep 6978473 = 5233855) B5233855
theorem B8838335 : Blo 1377508 8838335 := bstep (se 1 (by rfl) ⟨6628751, by rfl⟩ : syracuseStep 8838335 = 13257503) B13257503
theorem B3489115 : Blo 1377508 3489115 := bstep (se 1 (by rfl) ⟨2616836, by rfl⟩ : syracuseStep 3489115 = 5233673) B5233673
theorem B1572223 : Blo 1377508 1572223 := bstep (se 1 (by rfl) ⟨1179167, by rfl⟩ : syracuseStep 1572223 = 2358335) B2358335
theorem B1744411 : Blo 1377508 1744411 := bstep (se 1 (by rfl) ⟨1308308, by rfl⟩ : syracuseStep 1744411 = 2616617) B2616617
theorem B2326171 : Blo 1377508 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B51707549 : Blo 1377508 51707549 := bstep (se 3 (by rfl) ⟨9695165, by rfl⟩ : syracuseStep 51707549 = 19390331) B19390331
theorem B2483455 : Blo 1377508 2483455 := bstep (se 1 (by rfl) ⟨1862591, by rfl⟩ : syracuseStep 2483455 = 3725183) B3725183
theorem B4655015 : Blo 1377508 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B4655231 : Blo 1377508 4655231 := bstep (se 1 (by rfl) ⟨3491423, by rfl⟩ : syracuseStep 4655231 = 6982847) B6982847
theorem B5892223 : Blo 1377508 5892223 := bstep (se 1 (by rfl) ⟨4419167, by rfl⟩ : syracuseStep 5892223 = 8838335) B8838335
theorem B16779707 : Blo 1377508 16779707 := bstep (se 1 (by rfl) ⟨12584780, by rfl⟩ : syracuseStep 16779707 = 25169561) B25169561
theorem B2066879 : Blo 1377508 2066879 := bstep (se 1 (by rfl) ⟨1550159, by rfl⟩ : syracuseStep 2066879 = 3100319) B3100319
theorem B39717377 : Blo 1377508 39717377 := bstep (se 2 (by rfl) ⟨14894016, by rfl⟩ : syracuseStep 39717377 = 29788033) B29788033
theorem B1378907 : Blo 1377508 1378907 := bstep (se 1 (by rfl) ⟨1034180, by rfl⟩ : syracuseStep 1378907 = 2068361) B2068361
theorem B15690995 : Blo 1377508 15690995 := bstep (se 1 (by rfl) ⟨11768246, by rfl⟩ : syracuseStep 15690995 = 23536493) B23536493
theorem B4779575 : Blo 1377508 4779575 := bstep (se 1 (by rfl) ⟨3584681, by rfl⟩ : syracuseStep 4779575 = 7169363) B7169363
theorem B2068175 : Blo 1377508 2068175 := bstep (se 1 (by rfl) ⟨1551131, by rfl⟩ : syracuseStep 2068175 = 3102263) B3102263
theorem B10604371 : Blo 1377508 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B3928171 : Blo 1377508 3928171 := bstep (se 1 (by rfl) ⟨2946128, by rfl⟩ : syracuseStep 3928171 = 5892257) B5892257
theorem B11047661 : Blo 1377508 11047661 := bstep (se 3 (by rfl) ⟨2071436, by rfl⟩ : syracuseStep 11047661 = 4142873) B4142873
theorem B4649831 : Blo 1377508 4649831 := bstep (se 1 (by rfl) ⟨3487373, by rfl⟩ : syracuseStep 4649831 = 6974747) B6974747
theorem B3101561 : Blo 1377508 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B3487151 : Blo 1377508 3487151 := bstep (se 1 (by rfl) ⟨2615363, by rfl⟩ : syracuseStep 3487151 = 5230727) B5230727
theorem B3487657 : Blo 1377508 3487657 := bstep (se 2 (by rfl) ⟨1307871, by rfl⟩ : syracuseStep 3487657 = 2615743) B2615743
theorem B4652153 : Blo 1377508 4652153 := bstep (se 2 (by rfl) ⟨1744557, by rfl⟩ : syracuseStep 4652153 = 3489115) B3489115
theorem B90586235 : Blo 1377508 90586235 := bstep (se 1 (by rfl) ⟨67939676, by rfl⟩ : syracuseStep 90586235 = 135879353) B135879353
theorem B2096297 : Blo 1377508 2096297 := bstep (se 2 (by rfl) ⟨786111, by rfl⟩ : syracuseStep 2096297 = 1572223) B1572223
theorem B4652315 : Blo 1377508 4652315 := bstep (se 1 (by rfl) ⟨3489236, by rfl⟩ : syracuseStep 4652315 = 6978473) B6978473
theorem B2325881 : Blo 1377508 2325881 := bstep (se 2 (by rfl) ⟨872205, by rfl⟩ : syracuseStep 2325881 = 1744411) B1744411
theorem B34471699 : Blo 1377508 34471699 := bstep (se 1 (by rfl) ⟨25853774, by rfl⟩ : syracuseStep 34471699 = 51707549) B51707549
theorem B10755917 : Blo 1377508 10755917 := bstep (se 3 (by rfl) ⟨2016734, by rfl⟩ : syracuseStep 10755917 = 4033469) B4033469
theorem B1744831 : Blo 1377508 1744831 := bstep (se 1 (by rfl) ⟨1308623, by rfl⟩ : syracuseStep 1744831 = 2617247) B2617247
theorem B7856297 : Blo 1377508 7856297 := bstep (se 2 (by rfl) ⟨2946111, by rfl⟩ : syracuseStep 7856297 = 5892223) B5892223
theorem B7365107 : Blo 1377508 7365107 := bstep (se 1 (by rfl) ⟨5523830, by rfl⟩ : syracuseStep 7365107 = 11047661) B11047661
theorem B1377919 : Blo 1377508 1377919 := bstep (se 1 (by rfl) ⟨1033439, by rfl⟩ : syracuseStep 1377919 = 2066879) B2066879
theorem B3311273 : Blo 1377508 3311273 := bstep (se 2 (by rfl) ⟨1241727, by rfl⟩ : syracuseStep 3311273 = 2483455) B2483455
theorem B26478251 : Blo 1377508 26478251 := bstep (se 1 (by rfl) ⟨19858688, by rfl⟩ : syracuseStep 26478251 = 39717377) B39717377
theorem B1550587 : Blo 1377508 1550587 := bstep (se 1 (by rfl) ⟨1162940, by rfl⟩ : syracuseStep 1550587 = 2325881) B2325881
theorem B1378783 : Blo 1377508 1378783 := bstep (se 1 (by rfl) ⟨1034087, by rfl⟩ : syracuseStep 1378783 = 2068175) B2068175
theorem B7170611 : Blo 1377508 7170611 := bstep (se 1 (by rfl) ⟨5377958, by rfl⟩ : syracuseStep 7170611 = 10755917) B10755917
theorem B5237561 : Blo 1377508 5237561 := bstep (se 2 (by rfl) ⟨1964085, by rfl⟩ : syracuseStep 5237561 = 3928171) B3928171
theorem B3099887 : Blo 1377508 3099887 := bstep (se 1 (by rfl) ⟨2324915, by rfl⟩ : syracuseStep 3099887 = 4649831) B4649831
theorem B2067707 : Blo 1377508 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B183849061 : Blo 1377508 183849061 := bstep (se 4 (by rfl) ⟨17235849, by rfl⟩ : syracuseStep 183849061 = 34471699) B34471699
theorem B11186471 : Blo 1377508 11186471 := bstep (se 1 (by rfl) ⟨8389853, by rfl⟩ : syracuseStep 11186471 = 16779707) B16779707
theorem B3101435 : Blo 1377508 3101435 := bstep (se 1 (by rfl) ⟨2326076, by rfl⟩ : syracuseStep 3101435 = 4652153) B4652153
theorem B1397531 : Blo 1377508 1397531 := bstep (se 1 (by rfl) ⟨1048148, by rfl⟩ : syracuseStep 1397531 = 2096297) B2096297
theorem B3101543 : Blo 1377508 3101543 := bstep (se 1 (by rfl) ⟨2326157, by rfl⟩ : syracuseStep 3101543 = 4652315) B4652315
theorem B4650209 : Blo 1377508 4650209 := bstep (se 2 (by rfl) ⟨1743828, by rfl⟩ : syracuseStep 4650209 = 3487657) B3487657
theorem B241563293 : Blo 1377508 241563293 := bstep (se 3 (by rfl) ⟨45293117, by rfl⟩ : syracuseStep 241563293 = 90586235) B90586235
theorem B2324767 : Blo 1377508 2324767 := bstep (se 1 (by rfl) ⟨1743575, by rfl⟩ : syracuseStep 2324767 = 3487151) B3487151
theorem B3103343 : Blo 1377508 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B3103487 : Blo 1377508 3103487 := bstep (se 1 (by rfl) ⟨2327615, by rfl⟩ : syracuseStep 3103487 = 4655231) B4655231
theorem B10460663 : Blo 1377508 10460663 := bstep (se 1 (by rfl) ⟨7845497, by rfl⟩ : syracuseStep 10460663 = 15690995) B15690995
theorem B3186383 : Blo 1377508 3186383 := bstep (se 1 (by rfl) ⟨2389787, by rfl⟩ : syracuseStep 3186383 = 4779575) B4779575
theorem B14139161 : Blo 1377508 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B2326441 : Blo 1377508 2326441 := bstep (se 2 (by rfl) ⟨872415, by rfl⟩ : syracuseStep 2326441 = 1744831) B1744831
theorem B19121629 : Blo 1377508 19121629 := bstep (se 3 (by rfl) ⟨3585305, by rfl⟩ : syracuseStep 19121629 = 7170611) B7170611
theorem B3491707 : Blo 1377508 3491707 := bstep (se 1 (by rfl) ⟨2618780, by rfl⟩ : syracuseStep 3491707 = 5237561) B5237561
theorem B2066591 : Blo 1377508 2066591 := bstep (se 1 (by rfl) ⟨1549943, by rfl⟩ : syracuseStep 2066591 = 3099887) B3099887
theorem B1378471 : Blo 1377508 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B6973775 : Blo 1377508 6973775 := bstep (se 1 (by rfl) ⟨5230331, by rfl⟩ : syracuseStep 6973775 = 10460663) B10460663
theorem B5237531 : Blo 1377508 5237531 := bstep (se 1 (by rfl) ⟨3928148, by rfl⟩ : syracuseStep 5237531 = 7856297) B7856297
theorem B245132081 : Blo 1377508 245132081 := bstep (se 2 (by rfl) ⟨91924530, by rfl⟩ : syracuseStep 245132081 = 183849061) B183849061
theorem B4910071 : Blo 1377508 4910071 := bstep (se 1 (by rfl) ⟨3682553, by rfl⟩ : syracuseStep 4910071 = 7365107) B7365107
theorem B2067449 : Blo 1377508 2067449 := bstep (se 2 (by rfl) ⟨775293, by rfl⟩ : syracuseStep 2067449 = 1550587) B1550587
theorem B3099689 : Blo 1377508 3099689 := bstep (se 2 (by rfl) ⟨1162383, by rfl⟩ : syracuseStep 3099689 = 2324767) B2324767
theorem B2067623 : Blo 1377508 2067623 := bstep (se 1 (by rfl) ⟨1550717, by rfl⟩ : syracuseStep 2067623 = 3101435) B3101435
theorem B2067695 : Blo 1377508 2067695 := bstep (se 1 (by rfl) ⟨1550771, by rfl⟩ : syracuseStep 2067695 = 3101543) B3101543
theorem B29830589 : Blo 1377508 29830589 := bstep (se 3 (by rfl) ⟨5593235, by rfl⟩ : syracuseStep 29830589 = 11186471) B11186471
theorem B3100139 : Blo 1377508 3100139 := bstep (se 1 (by rfl) ⟨2325104, by rfl⟩ : syracuseStep 3100139 = 4650209) B4650209
theorem B161042195 : Blo 1377508 161042195 := bstep (se 1 (by rfl) ⟨120781646, by rfl⟩ : syracuseStep 161042195 = 241563293) B241563293
theorem B2207515 : Blo 1377508 2207515 := bstep (se 1 (by rfl) ⟨1655636, by rfl⟩ : syracuseStep 2207515 = 3311273) B3311273
theorem B2068895 : Blo 1377508 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B2068991 : Blo 1377508 2068991 := bstep (se 1 (by rfl) ⟨1551743, by rfl⟩ : syracuseStep 2068991 = 3103487) B3103487
theorem B9426107 : Blo 1377508 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B3101921 : Blo 1377508 3101921 := bstep (se 2 (by rfl) ⟨1163220, by rfl⟩ : syracuseStep 3101921 = 2326441) B2326441
theorem B17652167 : Blo 1377508 17652167 := bstep (se 1 (by rfl) ⟨13239125, by rfl⟩ : syracuseStep 17652167 = 26478251) B26478251
theorem B3726749 : Blo 1377508 3726749 := bstep (se 3 (by rfl) ⟨698765, by rfl⟩ : syracuseStep 3726749 = 1397531) B1397531
theorem B33988085 : Blo 1377508 33988085 := bstep (se 5 (by rfl) ⟨1593191, by rfl⟩ : syracuseStep 33988085 = 3186383) B3186383
theorem B6284071 : Blo 1377508 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B6546761 : Blo 1377508 6546761 := bstep (se 2 (by rfl) ⟨2455035, by rfl⟩ : syracuseStep 6546761 = 4910071) B4910071
theorem B1377727 : Blo 1377508 1377727 := bstep (se 1 (by rfl) ⟨1033295, by rfl⟩ : syracuseStep 1377727 = 2066591) B2066591
theorem B3491687 : Blo 1377508 3491687 := bstep (se 1 (by rfl) ⟨2618765, by rfl⟩ : syracuseStep 3491687 = 5237531) B5237531
theorem B25495505 : Blo 1377508 25495505 := bstep (se 2 (by rfl) ⟨9560814, by rfl⟩ : syracuseStep 25495505 = 19121629) B19121629
theorem B1378299 : Blo 1377508 1378299 := bstep (se 1 (by rfl) ⟨1033724, by rfl⟩ : syracuseStep 1378299 = 2067449) B2067449
theorem B2066459 : Blo 1377508 2066459 := bstep (se 1 (by rfl) ⟨1549844, by rfl⟩ : syracuseStep 2066459 = 3099689) B3099689
theorem B1378415 : Blo 1377508 1378415 := bstep (se 1 (by rfl) ⟨1033811, by rfl⟩ : syracuseStep 1378415 = 2067623) B2067623
theorem B1378463 : Blo 1377508 1378463 := bstep (se 1 (by rfl) ⟨1033847, by rfl⟩ : syracuseStep 1378463 = 2067695) B2067695
theorem B2484499 : Blo 1377508 2484499 := bstep (se 1 (by rfl) ⟨1863374, by rfl⟩ : syracuseStep 2484499 = 3726749) B3726749
theorem B2066759 : Blo 1377508 2066759 := bstep (se 1 (by rfl) ⟨1550069, by rfl⟩ : syracuseStep 2066759 = 3100139) B3100139
theorem B2943353 : Blo 1377508 2943353 := bstep (se 2 (by rfl) ⟨1103757, by rfl⟩ : syracuseStep 2943353 = 2207515) B2207515
theorem B4655609 : Blo 1377508 4655609 := bstep (se 2 (by rfl) ⟨1745853, by rfl⟩ : syracuseStep 4655609 = 3491707) B3491707
theorem B1379263 : Blo 1377508 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B1379327 : Blo 1377508 1379327 := bstep (se 1 (by rfl) ⟨1034495, by rfl⟩ : syracuseStep 1379327 = 2068991) B2068991
theorem B2067947 : Blo 1377508 2067947 := bstep (se 1 (by rfl) ⟨1550960, by rfl⟩ : syracuseStep 2067947 = 3101921) B3101921
theorem B4649183 : Blo 1377508 4649183 := bstep (se 1 (by rfl) ⟨3486887, by rfl⟩ : syracuseStep 4649183 = 6973775) B6973775
theorem B11768111 : Blo 1377508 11768111 := bstep (se 1 (by rfl) ⟨8826083, by rfl⟩ : syracuseStep 11768111 = 17652167) B17652167
theorem B19887059 : Blo 1377508 19887059 := bstep (se 1 (by rfl) ⟨14915294, by rfl⟩ : syracuseStep 19887059 = 29830589) B29830589
theorem B107361463 : Blo 1377508 107361463 := bstep (se 1 (by rfl) ⟨80521097, by rfl⟩ : syracuseStep 107361463 = 161042195) B161042195
theorem B163421387 : Blo 1377508 163421387 := bstep (se 1 (by rfl) ⟨122566040, by rfl⟩ : syracuseStep 163421387 = 245132081) B245132081
theorem B22658723 : Blo 1377508 22658723 := bstep (se 1 (by rfl) ⟨16994042, by rfl⟩ : syracuseStep 22658723 = 33988085) B33988085
theorem B2327791 : Blo 1377508 2327791 := bstep (se 1 (by rfl) ⟨1745843, by rfl⟩ : syracuseStep 2327791 = 3491687) B3491687
theorem B1377639 : Blo 1377508 1377639 := bstep (se 1 (by rfl) ⟨1033229, by rfl⟩ : syracuseStep 1377639 = 2066459) B2066459
theorem B33515045 : Blo 1377508 33515045 := bstep (se 4 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 33515045 = 6284071) B6284071
theorem B1377839 : Blo 1377508 1377839 := bstep (se 1 (by rfl) ⟨1033379, by rfl⟩ : syracuseStep 1377839 = 2066759) B2066759
theorem B143148617 : Blo 1377508 143148617 := bstep (se 2 (by rfl) ⟨53680731, by rfl⟩ : syracuseStep 143148617 = 107361463) B107361463
theorem B108947591 : Blo 1377508 108947591 := bstep (se 1 (by rfl) ⟨81710693, by rfl⟩ : syracuseStep 108947591 = 163421387) B163421387
theorem B1378631 : Blo 1377508 1378631 := bstep (se 1 (by rfl) ⟨1033973, by rfl⟩ : syracuseStep 1378631 = 2067947) B2067947
theorem B3099455 : Blo 1377508 3099455 := bstep (se 1 (by rfl) ⟨2324591, by rfl⟩ : syracuseStep 3099455 = 4649183) B4649183
theorem B3312665 : Blo 1377508 3312665 := bstep (se 2 (by rfl) ⟨1242249, by rfl⟩ : syracuseStep 3312665 = 2484499) B2484499
theorem B13258039 : Blo 1377508 13258039 := bstep (se 1 (by rfl) ⟨9943529, by rfl⟩ : syracuseStep 13258039 = 19887059) B19887059
theorem B1962235 : Blo 1377508 1962235 := bstep (se 1 (by rfl) ⟨1471676, by rfl⟩ : syracuseStep 1962235 = 2943353) B2943353
theorem B7845407 : Blo 1377508 7845407 := bstep (se 1 (by rfl) ⟨5884055, by rfl⟩ : syracuseStep 7845407 = 11768111) B11768111
theorem B4364507 : Blo 1377508 4364507 := bstep (se 1 (by rfl) ⟨3273380, by rfl⟩ : syracuseStep 4364507 = 6546761) B6546761
theorem B16997003 : Blo 1377508 16997003 := bstep (se 1 (by rfl) ⟨12747752, by rfl⟩ : syracuseStep 16997003 = 25495505) B25495505
theorem B3103739 : Blo 1377508 3103739 := bstep (se 1 (by rfl) ⟨2327804, by rfl⟩ : syracuseStep 3103739 = 4655609) B4655609
theorem B15105815 : Blo 1377508 15105815 := bstep (se 1 (by rfl) ⟨11329361, by rfl⟩ : syracuseStep 15105815 = 22658723) B22658723
theorem B72631727 : Blo 1377508 72631727 := bstep (se 1 (by rfl) ⟨54473795, by rfl⟩ : syracuseStep 72631727 = 108947591) B108947591
theorem B11331335 : Blo 1377508 11331335 := bstep (se 1 (by rfl) ⟨8498501, by rfl⟩ : syracuseStep 11331335 = 16997003) B16997003
theorem B2066303 : Blo 1377508 2066303 := bstep (se 1 (by rfl) ⟨1549727, by rfl⟩ : syracuseStep 2066303 = 3099455) B3099455
theorem B10070543 : Blo 1377508 10070543 := bstep (se 1 (by rfl) ⟨7552907, by rfl⟩ : syracuseStep 10070543 = 15105815) B15105815
theorem B2616313 : Blo 1377508 2616313 := bstep (se 2 (by rfl) ⟨981117, by rfl⟩ : syracuseStep 2616313 = 1962235) B1962235
theorem B5230271 : Blo 1377508 5230271 := bstep (se 1 (by rfl) ⟨3922703, by rfl⟩ : syracuseStep 5230271 = 7845407) B7845407
theorem B22343363 : Blo 1377508 22343363 := bstep (se 1 (by rfl) ⟨16757522, by rfl⟩ : syracuseStep 22343363 = 33515045) B33515045
theorem B95432411 : Blo 1377508 95432411 := bstep (se 1 (by rfl) ⟨71574308, by rfl⟩ : syracuseStep 95432411 = 143148617) B143148617
theorem B2069159 : Blo 1377508 2069159 := bstep (se 1 (by rfl) ⟨1551869, by rfl⟩ : syracuseStep 2069159 = 3103739) B3103739
theorem B2208443 : Blo 1377508 2208443 := bstep (se 1 (by rfl) ⟨1656332, by rfl⟩ : syracuseStep 2208443 = 3312665) B3312665
theorem B11638685 : Blo 1377508 11638685 := bstep (se 3 (by rfl) ⟨2182253, by rfl⟩ : syracuseStep 11638685 = 4364507) B4364507
theorem B3103721 : Blo 1377508 3103721 := bstep (se 2 (by rfl) ⟨1163895, by rfl⟩ : syracuseStep 3103721 = 2327791) B2327791
theorem B17677385 : Blo 1377508 17677385 := bstep (se 2 (by rfl) ⟨6629019, by rfl⟩ : syracuseStep 17677385 = 13258039) B13258039
theorem B7554223 : Blo 1377508 7554223 := bstep (se 1 (by rfl) ⟨5665667, by rfl⟩ : syracuseStep 7554223 = 11331335) B11331335
theorem B1377535 : Blo 1377508 1377535 := bstep (se 1 (by rfl) ⟨1033151, by rfl⟩ : syracuseStep 1377535 = 2066303) B2066303
theorem B7759123 : Blo 1377508 7759123 := bstep (se 1 (by rfl) ⟨5819342, by rfl⟩ : syracuseStep 7759123 = 11638685) B11638685
theorem B14895575 : Blo 1377508 14895575 := bstep (se 1 (by rfl) ⟨11171681, by rfl⟩ : syracuseStep 14895575 = 22343363) B22343363
theorem B63621607 : Blo 1377508 63621607 := bstep (se 1 (by rfl) ⟨47716205, by rfl⟩ : syracuseStep 63621607 = 95432411) B95432411
theorem B1379439 : Blo 1377508 1379439 := bstep (se 1 (by rfl) ⟨1034579, by rfl⟩ : syracuseStep 1379439 = 2069159) B2069159
theorem B6713695 : Blo 1377508 6713695 := bstep (se 1 (by rfl) ⟨5035271, by rfl⟩ : syracuseStep 6713695 = 10070543) B10070543
theorem B2069147 : Blo 1377508 2069147 := bstep (se 1 (by rfl) ⟨1551860, by rfl⟩ : syracuseStep 2069147 = 3103721) B3103721
theorem B11784923 : Blo 1377508 11784923 := bstep (se 1 (by rfl) ⟨8838692, by rfl⟩ : syracuseStep 11784923 = 17677385) B17677385
theorem B3486847 : Blo 1377508 3486847 := bstep (se 1 (by rfl) ⟨2615135, by rfl⟩ : syracuseStep 3486847 = 5230271) B5230271
theorem B48421151 : Blo 1377508 48421151 := bstep (se 1 (by rfl) ⟨36315863, by rfl⟩ : syracuseStep 48421151 = 72631727) B72631727
theorem B3488417 : Blo 1377508 3488417 := bstep (se 2 (by rfl) ⟨1308156, by rfl⟩ : syracuseStep 3488417 = 2616313) B2616313
theorem B5889181 : Blo 1377508 5889181 := bstep (se 3 (by rfl) ⟨1104221, by rfl⟩ : syracuseStep 5889181 = 2208443) B2208443
theorem B7856615 : Blo 1377508 7856615 := bstep (se 1 (by rfl) ⟨5892461, by rfl⟩ : syracuseStep 7856615 = 11784923) B11784923
theorem B84828809 : Blo 1377508 84828809 := bstep (se 2 (by rfl) ⟨31810803, by rfl⟩ : syracuseStep 84828809 = 63621607) B63621607
theorem B9930383 : Blo 1377508 9930383 := bstep (se 1 (by rfl) ⟨7447787, by rfl⟩ : syracuseStep 9930383 = 14895575) B14895575
theorem B1379431 : Blo 1377508 1379431 := bstep (se 1 (by rfl) ⟨1034573, by rfl⟩ : syracuseStep 1379431 = 2069147) B2069147
theorem B41381989 : Blo 1377508 41381989 := bstep (se 4 (by rfl) ⟨3879561, by rfl⟩ : syracuseStep 41381989 = 7759123) B7759123
theorem B4649129 : Blo 1377508 4649129 := bstep (se 2 (by rfl) ⟨1743423, by rfl⟩ : syracuseStep 4649129 = 3486847) B3486847
theorem B32280767 : Blo 1377508 32280767 := bstep (se 1 (by rfl) ⟨24210575, by rfl⟩ : syracuseStep 32280767 = 48421151) B48421151
theorem B7852241 : Blo 1377508 7852241 := bstep (se 2 (by rfl) ⟨2944590, by rfl⟩ : syracuseStep 7852241 = 5889181) B5889181
theorem B10072297 : Blo 1377508 10072297 := bstep (se 2 (by rfl) ⟨3777111, by rfl⟩ : syracuseStep 10072297 = 7554223) B7554223
theorem B8951593 : Blo 1377508 8951593 := bstep (se 2 (by rfl) ⟨3356847, by rfl⟩ : syracuseStep 8951593 = 6713695) B6713695
theorem B2325611 : Blo 1377508 2325611 := bstep (se 1 (by rfl) ⟨1744208, by rfl⟩ : syracuseStep 2325611 = 3488417) B3488417
theorem B21520511 : Blo 1377508 21520511 := bstep (se 1 (by rfl) ⟨16140383, by rfl⟩ : syracuseStep 21520511 = 32280767) B32280767
theorem B5234827 : Blo 1377508 5234827 := bstep (se 1 (by rfl) ⟨3926120, by rfl⟩ : syracuseStep 5234827 = 7852241) B7852241
theorem B6620255 : Blo 1377508 6620255 := bstep (se 1 (by rfl) ⟨4965191, by rfl⟩ : syracuseStep 6620255 = 9930383) B9930383
theorem B1550407 : Blo 1377508 1550407 := bstep (se 1 (by rfl) ⟨1162805, by rfl⟩ : syracuseStep 1550407 = 2325611) B2325611
theorem B3099419 : Blo 1377508 3099419 := bstep (se 1 (by rfl) ⟨2324564, by rfl⟩ : syracuseStep 3099419 = 4649129) B4649129
theorem B13429729 : Blo 1377508 13429729 := bstep (se 2 (by rfl) ⟨5036148, by rfl⟩ : syracuseStep 13429729 = 10072297) B10072297
theorem B5237743 : Blo 1377508 5237743 := bstep (se 1 (by rfl) ⟨3928307, by rfl⟩ : syracuseStep 5237743 = 7856615) B7856615
theorem B226210157 : Blo 1377508 226210157 := bstep (se 3 (by rfl) ⟨42414404, by rfl⟩ : syracuseStep 226210157 = 84828809) B84828809
theorem B882815765 : Blo 1377508 882815765 := bstep (se 6 (by rfl) ⟨20690994, by rfl⟩ : syracuseStep 882815765 = 41381989) B41381989
theorem B11935457 : Blo 1377508 11935457 := bstep (se 2 (by rfl) ⟨4475796, by rfl⟩ : syracuseStep 11935457 = 8951593) B8951593
theorem B6979769 : Blo 1377508 6979769 := bstep (se 2 (by rfl) ⟨2617413, by rfl⟩ : syracuseStep 6979769 = 5234827) B5234827
theorem B150806771 : Blo 1377508 150806771 := bstep (se 1 (by rfl) ⟨113105078, by rfl⟩ : syracuseStep 150806771 = 226210157) B226210157
theorem B2066279 : Blo 1377508 2066279 := bstep (se 1 (by rfl) ⟨1549709, by rfl⟩ : syracuseStep 2066279 = 3099419) B3099419
theorem B7956971 : Blo 1377508 7956971 := bstep (se 1 (by rfl) ⟨5967728, by rfl⟩ : syracuseStep 7956971 = 11935457) B11935457
theorem B71625221 : Blo 1377508 71625221 := bstep (se 4 (by rfl) ⟨6714864, by rfl⟩ : syracuseStep 71625221 = 13429729) B13429729
theorem B14347007 : Blo 1377508 14347007 := bstep (se 1 (by rfl) ⟨10760255, by rfl⟩ : syracuseStep 14347007 = 21520511) B21520511
theorem B2067209 : Blo 1377508 2067209 := bstep (se 2 (by rfl) ⟨775203, by rfl⟩ : syracuseStep 2067209 = 1550407) B1550407
theorem B6983657 : Blo 1377508 6983657 := bstep (se 2 (by rfl) ⟨2618871, by rfl⟩ : syracuseStep 6983657 = 5237743) B5237743
theorem B4413503 : Blo 1377508 4413503 := bstep (se 1 (by rfl) ⟨3310127, by rfl⟩ : syracuseStep 4413503 = 6620255) B6620255
theorem B2354175373 : Blo 1377508 2354175373 := bstep (se 3 (by rfl) ⟨441407882, by rfl⟩ : syracuseStep 2354175373 = 882815765) B882815765
theorem B4653179 : Blo 1377508 4653179 := bstep (se 1 (by rfl) ⟨3489884, by rfl⟩ : syracuseStep 4653179 = 6979769) B6979769
theorem B1377519 : Blo 1377508 1377519 := bstep (se 1 (by rfl) ⟨1033139, by rfl⟩ : syracuseStep 1377519 = 2066279) B2066279
theorem B2942335 : Blo 1377508 2942335 := bstep (se 1 (by rfl) ⟨2206751, by rfl⟩ : syracuseStep 2942335 = 4413503) B4413503
theorem B1378139 : Blo 1377508 1378139 := bstep (se 1 (by rfl) ⟨1033604, by rfl⟩ : syracuseStep 1378139 = 2067209) B2067209
theorem B4655771 : Blo 1377508 4655771 := bstep (se 1 (by rfl) ⟨3491828, by rfl⟩ : syracuseStep 4655771 = 6983657) B6983657
theorem B5304647 : Blo 1377508 5304647 := bstep (se 1 (by rfl) ⟨3978485, by rfl⟩ : syracuseStep 5304647 = 7956971) B7956971
theorem B9564671 : Blo 1377508 9564671 := bstep (se 1 (by rfl) ⟨7173503, by rfl⟩ : syracuseStep 9564671 = 14347007) B14347007
theorem B3138900497 : Blo 1377508 3138900497 := bstep (se 2 (by rfl) ⟨1177087686, by rfl⟩ : syracuseStep 3138900497 = 2354175373) B2354175373
theorem B100537847 : Blo 1377508 100537847 := bstep (se 1 (by rfl) ⟨75403385, by rfl⟩ : syracuseStep 100537847 = 150806771) B150806771
theorem B47750147 : Blo 1377508 47750147 := bstep (se 1 (by rfl) ⟨35812610, by rfl⟩ : syracuseStep 47750147 = 71625221) B71625221
theorem B6376447 : Blo 1377508 6376447 := bstep (se 1 (by rfl) ⟨4782335, by rfl⟩ : syracuseStep 6376447 = 9564671) B9564671
theorem B2092600331 : Blo 1377508 2092600331 := bstep (se 1 (by rfl) ⟨1569450248, by rfl⟩ : syracuseStep 2092600331 = 3138900497) B3138900497
theorem B15692453 : Blo 1377508 15692453 := bstep (se 4 (by rfl) ⟨1471167, by rfl⟩ : syracuseStep 15692453 = 2942335) B2942335
theorem B3102119 : Blo 1377508 3102119 := bstep (se 1 (by rfl) ⟨2326589, by rfl⟩ : syracuseStep 3102119 = 4653179) B4653179
theorem B14145725 : Blo 1377508 14145725 := bstep (se 3 (by rfl) ⟨2652323, by rfl⟩ : syracuseStep 14145725 = 5304647) B5304647
theorem B67025231 : Blo 1377508 67025231 := bstep (se 1 (by rfl) ⟨50268923, by rfl⟩ : syracuseStep 67025231 = 100537847) B100537847
theorem B3103847 : Blo 1377508 3103847 := bstep (se 1 (by rfl) ⟨2327885, by rfl⟩ : syracuseStep 3103847 = 4655771) B4655771
theorem B31833431 : Blo 1377508 31833431 := bstep (se 1 (by rfl) ⟨23875073, by rfl⟩ : syracuseStep 31833431 = 47750147) B47750147
theorem B10461635 : Blo 1377508 10461635 := bstep (se 1 (by rfl) ⟨7846226, by rfl⟩ : syracuseStep 10461635 = 15692453) B15692453
theorem B1395066887 : Blo 1377508 1395066887 := bstep (se 1 (by rfl) ⟨1046300165, by rfl⟩ : syracuseStep 1395066887 = 2092600331) B2092600331
theorem B2068079 : Blo 1377508 2068079 := bstep (se 1 (by rfl) ⟨1551059, by rfl⟩ : syracuseStep 2068079 = 3102119) B3102119
theorem B44683487 : Blo 1377508 44683487 := bstep (se 1 (by rfl) ⟨33512615, by rfl⟩ : syracuseStep 44683487 = 67025231) B67025231
theorem B2069231 : Blo 1377508 2069231 := bstep (se 1 (by rfl) ⟨1551923, by rfl⟩ : syracuseStep 2069231 = 3103847) B3103847
theorem B21222287 : Blo 1377508 21222287 := bstep (se 1 (by rfl) ⟨15916715, by rfl⟩ : syracuseStep 21222287 = 31833431) B31833431
theorem B37721933 : Blo 1377508 37721933 := bstep (se 3 (by rfl) ⟨7072862, by rfl⟩ : syracuseStep 37721933 = 14145725) B14145725
theorem B8501929 : Blo 1377508 8501929 := bstep (se 2 (by rfl) ⟨3188223, by rfl⟩ : syracuseStep 8501929 = 6376447) B6376447
theorem B14148191 : Blo 1377508 14148191 := bstep (se 1 (by rfl) ⟨10611143, by rfl⟩ : syracuseStep 14148191 = 21222287) B21222287
theorem B45343621 : Blo 1377508 45343621 := bstep (se 4 (by rfl) ⟨4250964, by rfl⟩ : syracuseStep 45343621 = 8501929) B8501929
theorem B1378719 : Blo 1377508 1378719 := bstep (se 1 (by rfl) ⟨1034039, by rfl⟩ : syracuseStep 1378719 = 2068079) B2068079
theorem B29788991 : Blo 1377508 29788991 := bstep (se 1 (by rfl) ⟨22341743, by rfl⟩ : syracuseStep 29788991 = 44683487) B44683487
theorem B6974423 : Blo 1377508 6974423 := bstep (se 1 (by rfl) ⟨5230817, by rfl⟩ : syracuseStep 6974423 = 10461635) B10461635
theorem B1379487 : Blo 1377508 1379487 := bstep (se 1 (by rfl) ⟨1034615, by rfl⟩ : syracuseStep 1379487 = 2069231) B2069231
theorem B25147955 : Blo 1377508 25147955 := bstep (se 1 (by rfl) ⟨18860966, by rfl⟩ : syracuseStep 25147955 = 37721933) B37721933
theorem B930044591 : Blo 1377508 930044591 := bstep (se 1 (by rfl) ⟨697533443, by rfl⟩ : syracuseStep 930044591 = 1395066887) B1395066887
theorem B60458161 : Blo 1377508 60458161 := bstep (se 2 (by rfl) ⟨22671810, by rfl⟩ : syracuseStep 60458161 = 45343621) B45343621
theorem B620029727 : Blo 1377508 620029727 := bstep (se 1 (by rfl) ⟨465022295, by rfl⟩ : syracuseStep 620029727 = 930044591) B930044591
theorem B19859327 : Blo 1377508 19859327 := bstep (se 1 (by rfl) ⟨14894495, by rfl⟩ : syracuseStep 19859327 = 29788991) B29788991
theorem B9432127 : Blo 1377508 9432127 := bstep (se 1 (by rfl) ⟨7074095, by rfl⟩ : syracuseStep 9432127 = 14148191) B14148191
theorem B16765303 : Blo 1377508 16765303 := bstep (se 1 (by rfl) ⟨12573977, by rfl⟩ : syracuseStep 16765303 = 25147955) B25147955
theorem B4649615 : Blo 1377508 4649615 := bstep (se 1 (by rfl) ⟨3487211, by rfl⟩ : syracuseStep 4649615 = 6974423) B6974423
theorem B413353151 : Blo 1377508 413353151 := bstep (se 1 (by rfl) ⟨310014863, by rfl⟩ : syracuseStep 413353151 = 620029727) B620029727
theorem B13239551 : Blo 1377508 13239551 := bstep (se 1 (by rfl) ⟨9929663, by rfl⟩ : syracuseStep 13239551 = 19859327) B19859327
theorem B12576169 : Blo 1377508 12576169 := bstep (se 2 (by rfl) ⟨4716063, by rfl⟩ : syracuseStep 12576169 = 9432127) B9432127
theorem B80610881 : Blo 1377508 80610881 := bstep (se 2 (by rfl) ⟨30229080, by rfl⟩ : syracuseStep 80610881 = 60458161) B60458161
theorem B3099743 : Blo 1377508 3099743 := bstep (se 1 (by rfl) ⟨2324807, by rfl⟩ : syracuseStep 3099743 = 4649615) B4649615
theorem B22353737 : Blo 1377508 22353737 := bstep (se 2 (by rfl) ⟨8382651, by rfl⟩ : syracuseStep 22353737 = 16765303) B16765303
theorem B2066495 : Blo 1377508 2066495 := bstep (se 1 (by rfl) ⟨1549871, by rfl⟩ : syracuseStep 2066495 = 3099743) B3099743
theorem B8826367 : Blo 1377508 8826367 := bstep (se 1 (by rfl) ⟨6619775, by rfl⟩ : syracuseStep 8826367 = 13239551) B13239551
theorem B214962349 : Blo 1377508 214962349 := bstep (se 3 (by rfl) ⟨40305440, by rfl⟩ : syracuseStep 214962349 = 80610881) B80610881
theorem B59609965 : Blo 1377508 59609965 := bstep (se 3 (by rfl) ⟨11176868, by rfl⟩ : syracuseStep 59609965 = 22353737) B22353737
theorem B275568767 : Blo 1377508 275568767 := bstep (se 1 (by rfl) ⟨206676575, by rfl⟩ : syracuseStep 275568767 = 413353151) B413353151
theorem B16768225 : Blo 1377508 16768225 := bstep (se 2 (by rfl) ⟨6288084, by rfl⟩ : syracuseStep 16768225 = 12576169) B12576169
theorem B79479953 : Blo 1377508 79479953 := bstep (se 2 (by rfl) ⟨29804982, by rfl⟩ : syracuseStep 79479953 = 59609965) B59609965
theorem B1377663 : Blo 1377508 1377663 := bstep (se 1 (by rfl) ⟨1033247, by rfl⟩ : syracuseStep 1377663 = 2066495) B2066495
theorem B22357633 : Blo 1377508 22357633 := bstep (se 2 (by rfl) ⟨8384112, by rfl⟩ : syracuseStep 22357633 = 16768225) B16768225
theorem B286616465 : Blo 1377508 286616465 := bstep (se 2 (by rfl) ⟨107481174, by rfl⟩ : syracuseStep 286616465 = 214962349) B214962349
theorem B11768489 : Blo 1377508 11768489 := bstep (se 2 (by rfl) ⟨4413183, by rfl⟩ : syracuseStep 11768489 = 8826367) B8826367
theorem B183712511 : Blo 1377508 183712511 := bstep (se 1 (by rfl) ⟨137784383, by rfl⟩ : syracuseStep 183712511 = 275568767) B275568767
theorem B52986635 : Blo 1377508 52986635 := bstep (se 1 (by rfl) ⟨39739976, by rfl⟩ : syracuseStep 52986635 = 79479953) B79479953
theorem B122475007 : Blo 1377508 122475007 := bstep (se 1 (by rfl) ⟨91856255, by rfl⟩ : syracuseStep 122475007 = 183712511) B183712511
theorem B7845659 : Blo 1377508 7845659 := bstep (se 1 (by rfl) ⟨5884244, by rfl⟩ : syracuseStep 7845659 = 11768489) B11768489
theorem B191077643 : Blo 1377508 191077643 := bstep (se 1 (by rfl) ⟨143308232, by rfl⟩ : syracuseStep 191077643 = 286616465) B286616465
theorem B29810177 : Blo 1377508 29810177 := bstep (se 2 (by rfl) ⟨11178816, by rfl⟩ : syracuseStep 29810177 = 22357633) B22357633
theorem B35324423 : Blo 1377508 35324423 := bstep (se 1 (by rfl) ⟨26493317, by rfl⟩ : syracuseStep 35324423 = 52986635) B52986635
theorem B653200037 : Blo 1377508 653200037 := bstep (se 4 (by rfl) ⟨61237503, by rfl⟩ : syracuseStep 653200037 = 122475007) B122475007
theorem B5230439 : Blo 1377508 5230439 := bstep (se 1 (by rfl) ⟨3922829, by rfl⟩ : syracuseStep 5230439 = 7845659) B7845659
theorem B127385095 : Blo 1377508 127385095 := bstep (se 1 (by rfl) ⟨95538821, by rfl⟩ : syracuseStep 127385095 = 191077643) B191077643
theorem B19873451 : Blo 1377508 19873451 := bstep (se 1 (by rfl) ⟨14905088, by rfl⟩ : syracuseStep 19873451 = 29810177) B29810177
theorem B169846793 : Blo 1377508 169846793 := bstep (se 2 (by rfl) ⟨63692547, by rfl⟩ : syracuseStep 169846793 = 127385095) B127385095
theorem B13248967 : Blo 1377508 13248967 := bstep (se 1 (by rfl) ⟨9936725, by rfl⟩ : syracuseStep 13248967 = 19873451) B19873451
theorem B435466691 : Blo 1377508 435466691 := bstep (se 1 (by rfl) ⟨326600018, by rfl⟩ : syracuseStep 435466691 = 653200037) B653200037
theorem B3486959 : Blo 1377508 3486959 := bstep (se 1 (by rfl) ⟨2615219, by rfl⟩ : syracuseStep 3486959 = 5230439) B5230439
theorem B23549615 : Blo 1377508 23549615 := bstep (se 1 (by rfl) ⟨17662211, by rfl⟩ : syracuseStep 23549615 = 35324423) B35324423
theorem B113231195 : Blo 1377508 113231195 := bstep (se 1 (by rfl) ⟨84923396, by rfl⟩ : syracuseStep 113231195 = 169846793) B169846793
theorem B290311127 : Blo 1377508 290311127 := bstep (se 1 (by rfl) ⟨217733345, by rfl⟩ : syracuseStep 290311127 = 435466691) B435466691
theorem B17665289 : Blo 1377508 17665289 := bstep (se 2 (by rfl) ⟨6624483, by rfl⟩ : syracuseStep 17665289 = 13248967) B13248967
theorem B15699743 : Blo 1377508 15699743 := bstep (se 1 (by rfl) ⟨11774807, by rfl⟩ : syracuseStep 15699743 = 23549615) B23549615
theorem B2324639 : Blo 1377508 2324639 := bstep (se 1 (by rfl) ⟨1743479, by rfl⟩ : syracuseStep 2324639 = 3486959) B3486959
theorem B1549759 : Blo 1377508 1549759 := bstep (se 1 (by rfl) ⟨1162319, by rfl⟩ : syracuseStep 1549759 = 2324639) B2324639
theorem B193540751 : Blo 1377508 193540751 := bstep (se 1 (by rfl) ⟨145155563, by rfl⟩ : syracuseStep 193540751 = 290311127) B290311127
theorem B11776859 : Blo 1377508 11776859 := bstep (se 1 (by rfl) ⟨8832644, by rfl⟩ : syracuseStep 11776859 = 17665289) B17665289
theorem B10466495 : Blo 1377508 10466495 := bstep (se 1 (by rfl) ⟨7849871, by rfl⟩ : syracuseStep 10466495 = 15699743) B15699743
theorem B75487463 : Blo 1377508 75487463 := bstep (se 1 (by rfl) ⟨56615597, by rfl⟩ : syracuseStep 75487463 = 113231195) B113231195
theorem B50324975 : Blo 1377508 50324975 := bstep (se 1 (by rfl) ⟨37743731, by rfl⟩ : syracuseStep 50324975 = 75487463) B75487463
theorem B2066345 : Blo 1377508 2066345 := bstep (se 2 (by rfl) ⟨774879, by rfl⟩ : syracuseStep 2066345 = 1549759) B1549759
theorem B129027167 : Blo 1377508 129027167 := bstep (se 1 (by rfl) ⟨96770375, by rfl⟩ : syracuseStep 129027167 = 193540751) B193540751
theorem B7851239 : Blo 1377508 7851239 := bstep (se 1 (by rfl) ⟨5888429, by rfl⟩ : syracuseStep 7851239 = 11776859) B11776859
theorem B6977663 : Blo 1377508 6977663 := bstep (se 1 (by rfl) ⟨5233247, by rfl⟩ : syracuseStep 6977663 = 10466495) B10466495
theorem B1377563 : Blo 1377508 1377563 := bstep (se 1 (by rfl) ⟨1033172, by rfl⟩ : syracuseStep 1377563 = 2066345) B2066345
theorem B86018111 : Blo 1377508 86018111 := bstep (se 1 (by rfl) ⟨64513583, by rfl⟩ : syracuseStep 86018111 = 129027167) B129027167
theorem B33549983 : Blo 1377508 33549983 := bstep (se 1 (by rfl) ⟨25162487, by rfl⟩ : syracuseStep 33549983 = 50324975) B50324975
theorem B4651775 : Blo 1377508 4651775 := bstep (se 1 (by rfl) ⟨3488831, by rfl⟩ : syracuseStep 4651775 = 6977663) B6977663
theorem B5234159 : Blo 1377508 5234159 := bstep (se 1 (by rfl) ⟨3925619, by rfl⟩ : syracuseStep 5234159 = 7851239) B7851239
theorem B57345407 : Blo 1377508 57345407 := bstep (se 1 (by rfl) ⟨43009055, by rfl⟩ : syracuseStep 57345407 = 86018111) B86018111
theorem B22366655 : Blo 1377508 22366655 := bstep (se 1 (by rfl) ⟨16774991, by rfl⟩ : syracuseStep 22366655 = 33549983) B33549983
theorem B3101183 : Blo 1377508 3101183 := bstep (se 1 (by rfl) ⟨2325887, by rfl⟩ : syracuseStep 3101183 = 4651775) B4651775
theorem B3489439 : Blo 1377508 3489439 := bstep (se 1 (by rfl) ⟨2617079, by rfl⟩ : syracuseStep 3489439 = 5234159) B5234159
theorem B14911103 : Blo 1377508 14911103 := bstep (se 1 (by rfl) ⟨11183327, by rfl⟩ : syracuseStep 14911103 = 22366655) B22366655
theorem B2067455 : Blo 1377508 2067455 := bstep (se 1 (by rfl) ⟨1550591, by rfl⟩ : syracuseStep 2067455 = 3101183) B3101183
theorem B38230271 : Blo 1377508 38230271 := bstep (se 1 (by rfl) ⟨28672703, by rfl⟩ : syracuseStep 38230271 = 57345407) B57345407
theorem B4652585 : Blo 1377508 4652585 := bstep (se 2 (by rfl) ⟨1744719, by rfl⟩ : syracuseStep 4652585 = 3489439) B3489439
theorem B25486847 : Blo 1377508 25486847 := bstep (se 1 (by rfl) ⟨19115135, by rfl⟩ : syracuseStep 25486847 = 38230271) B38230271
theorem B1378303 : Blo 1377508 1378303 := bstep (se 1 (by rfl) ⟨1033727, by rfl⟩ : syracuseStep 1378303 = 2067455) B2067455
theorem B9940735 : Blo 1377508 9940735 := bstep (se 1 (by rfl) ⟨7455551, by rfl⟩ : syracuseStep 9940735 = 14911103) B14911103
theorem B3101723 : Blo 1377508 3101723 := bstep (se 1 (by rfl) ⟨2326292, by rfl⟩ : syracuseStep 3101723 = 4652585) B4652585
theorem B16991231 : Blo 1377508 16991231 := bstep (se 1 (by rfl) ⟨12743423, by rfl⟩ : syracuseStep 16991231 = 25486847) B25486847
theorem B2067815 : Blo 1377508 2067815 := bstep (se 1 (by rfl) ⟨1550861, by rfl⟩ : syracuseStep 2067815 = 3101723) B3101723
theorem B13254313 : Blo 1377508 13254313 := bstep (se 2 (by rfl) ⟨4970367, by rfl⟩ : syracuseStep 13254313 = 9940735) B9940735
theorem B17672417 : Blo 1377508 17672417 := bstep (se 2 (by rfl) ⟨6627156, by rfl⟩ : syracuseStep 17672417 = 13254313) B13254313
theorem B1378543 : Blo 1377508 1378543 := bstep (se 1 (by rfl) ⟨1033907, by rfl⟩ : syracuseStep 1378543 = 2067815) B2067815
theorem B45309949 : Blo 1377508 45309949 := bstep (se 3 (by rfl) ⟨8495615, by rfl⟩ : syracuseStep 45309949 = 16991231) B16991231
theorem B11781611 : Blo 1377508 11781611 := bstep (se 1 (by rfl) ⟨8836208, by rfl⟩ : syracuseStep 11781611 = 17672417) B17672417
theorem B241653061 : Blo 1377508 241653061 := bstep (se 4 (by rfl) ⟨22654974, by rfl⟩ : syracuseStep 241653061 = 45309949) B45309949
theorem B322204081 : Blo 1377508 322204081 := bstep (se 2 (by rfl) ⟨120826530, by rfl⟩ : syracuseStep 322204081 = 241653061) B241653061
theorem B7854407 : Blo 1377508 7854407 := bstep (se 1 (by rfl) ⟨5890805, by rfl⟩ : syracuseStep 7854407 = 11781611) B11781611
theorem B429605441 : Blo 1377508 429605441 := bstep (se 2 (by rfl) ⟨161102040, by rfl⟩ : syracuseStep 429605441 = 322204081) B322204081
theorem B5236271 : Blo 1377508 5236271 := bstep (se 1 (by rfl) ⟨3927203, by rfl⟩ : syracuseStep 5236271 = 7854407) B7854407
theorem B3490847 : Blo 1377508 3490847 := bstep (se 1 (by rfl) ⟨2618135, by rfl⟩ : syracuseStep 3490847 = 5236271) B5236271
theorem B286403627 : Blo 1377508 286403627 := bstep (se 1 (by rfl) ⟨214802720, by rfl⟩ : syracuseStep 286403627 = 429605441) B429605441
theorem B2327231 : Blo 1377508 2327231 := bstep (se 1 (by rfl) ⟨1745423, by rfl⟩ : syracuseStep 2327231 = 3490847) B3490847
theorem B190935751 : Blo 1377508 190935751 := bstep (se 1 (by rfl) ⟨143201813, by rfl⟩ : syracuseStep 190935751 = 286403627) B286403627
theorem B1551487 : Blo 1377508 1551487 := bstep (se 1 (by rfl) ⟨1163615, by rfl⟩ : syracuseStep 1551487 = 2327231) B2327231
theorem B254581001 : Blo 1377508 254581001 := bstep (se 2 (by rfl) ⟨95467875, by rfl⟩ : syracuseStep 254581001 = 190935751) B190935751
theorem B2068649 : Blo 1377508 2068649 := bstep (se 2 (by rfl) ⟨775743, by rfl⟩ : syracuseStep 2068649 = 1551487) B1551487
theorem B169720667 : Blo 1377508 169720667 := bstep (se 1 (by rfl) ⟨127290500, by rfl⟩ : syracuseStep 169720667 = 254581001) B254581001
theorem B1379099 : Blo 1377508 1379099 := bstep (se 1 (by rfl) ⟨1034324, by rfl⟩ : syracuseStep 1379099 = 2068649) B2068649
theorem B113147111 : Blo 1377508 113147111 := bstep (se 1 (by rfl) ⟨84860333, by rfl⟩ : syracuseStep 113147111 = 169720667) B169720667
theorem B75431407 : Blo 1377508 75431407 := bstep (se 1 (by rfl) ⟨56573555, by rfl⟩ : syracuseStep 75431407 = 113147111) B113147111
theorem B100575209 : Blo 1377508 100575209 := bstep (se 2 (by rfl) ⟨37715703, by rfl⟩ : syracuseStep 100575209 = 75431407) B75431407
theorem B67050139 : Blo 1377508 67050139 := bstep (se 1 (by rfl) ⟨50287604, by rfl⟩ : syracuseStep 67050139 = 100575209) B100575209
theorem B89400185 : Blo 1377508 89400185 := bstep (se 2 (by rfl) ⟨33525069, by rfl⟩ : syracuseStep 89400185 = 67050139) B67050139
theorem B59600123 : Blo 1377508 59600123 := bstep (se 1 (by rfl) ⟨44700092, by rfl⟩ : syracuseStep 59600123 = 89400185) B89400185
theorem B39733415 : Blo 1377508 39733415 := bstep (se 1 (by rfl) ⟨29800061, by rfl⟩ : syracuseStep 39733415 = 59600123) B59600123
theorem B26488943 : Blo 1377508 26488943 := bstep (se 1 (by rfl) ⟨19866707, by rfl⟩ : syracuseStep 26488943 = 39733415) B39733415
theorem B17659295 : Blo 1377508 17659295 := bstep (se 1 (by rfl) ⟨13244471, by rfl⟩ : syracuseStep 17659295 = 26488943) B26488943
theorem B11772863 : Blo 1377508 11772863 := bstep (se 1 (by rfl) ⟨8829647, by rfl⟩ : syracuseStep 11772863 = 17659295) B17659295
theorem B7848575 : Blo 1377508 7848575 := bstep (se 1 (by rfl) ⟨5886431, by rfl⟩ : syracuseStep 7848575 = 11772863) B11772863
theorem B5232383 : Blo 1377508 5232383 := bstep (se 1 (by rfl) ⟨3924287, by rfl⟩ : syracuseStep 5232383 = 7848575) B7848575
theorem B3488255 : Blo 1377508 3488255 := bstep (se 1 (by rfl) ⟨2616191, by rfl⟩ : syracuseStep 3488255 = 5232383) B5232383
theorem B2325503 : Blo 1377508 2325503 := bstep (se 1 (by rfl) ⟨1744127, by rfl⟩ : syracuseStep 2325503 = 3488255) B3488255
theorem B1550335 : Blo 1377508 1550335 := bstep (se 1 (by rfl) ⟨1162751, by rfl⟩ : syracuseStep 1550335 = 2325503) B2325503
theorem B2067113 : Blo 1377508 2067113 := bstep (se 2 (by rfl) ⟨775167, by rfl⟩ : syracuseStep 2067113 = 1550335) B1550335
theorem B1378075 : Blo 1377508 1378075 := bstep (se 1 (by rfl) ⟨1033556, by rfl⟩ : syracuseStep 1378075 = 2067113) B2067113

theorem C0 (j : ℕ) (h1 : 344377 ≤ j) (h2 : j ≤ 344876) : Blo 1377508 (4 * j + 3) := by
  interval_cases j
  · exact B1377511
  · exact B1377515
  · exact B1377519
  · exact B1377523
  · exact B1377527
  · exact B1377531
  · exact B1377535
  · exact B1377539
  · exact B1377543
  · exact B1377547
  · exact B1377551
  · exact B1377555
  · exact B1377559
  · exact B1377563
  · exact B1377567
  · exact B1377571
  · exact B1377575
  · exact B1377579
  · exact B1377583
  · exact B1377587
  · exact B1377591
  · exact B1377595
  · exact B1377599
  · exact B1377603
  · exact B1377607
  · exact B1377611
  · exact B1377615
  · exact B1377619
  · exact B1377623
  · exact B1377627
  · exact B1377631
  · exact B1377635
  · exact B1377639
  · exact B1377643
  · exact B1377647
  · exact B1377651
  · exact B1377655
  · exact B1377659
  · exact B1377663
  · exact B1377667
  · exact B1377671
  · exact B1377675
  · exact B1377679
  · exact B1377683
  · exact B1377687
  · exact B1377691
  · exact B1377695
  · exact B1377699
  · exact B1377703
  · exact B1377707
  · exact B1377711
  · exact B1377715
  · exact B1377719
  · exact B1377723
  · exact B1377727
  · exact B1377731
  · exact B1377735
  · exact B1377739
  · exact B1377743
  · exact B1377747
  · exact B1377751
  · exact B1377755
  · exact B1377759
  · exact B1377763
  · exact B1377767
  · exact B1377771
  · exact B1377775
  · exact B1377779
  · exact B1377783
  · exact B1377787
  · exact B1377791
  · exact B1377795
  · exact B1377799
  · exact B1377803
  · exact B1377807
  · exact B1377811
  · exact B1377815
  · exact B1377819
  · exact B1377823
  · exact B1377827
  · exact B1377831
  · exact B1377835
  · exact B1377839
  · exact B1377843
  · exact B1377847
  · exact B1377851
  · exact B1377855
  · exact B1377859
  · exact B1377863
  · exact B1377867
  · exact B1377871
  · exact B1377875
  · exact B1377879
  · exact B1377883
  · exact B1377887
  · exact B1377891
  · exact B1377895
  · exact B1377899
  · exact B1377903
  · exact B1377907
  · exact B1377911
  · exact B1377915
  · exact B1377919
  · exact B1377923
  · exact B1377927
  · exact B1377931
  · exact B1377935
  · exact B1377939
  · exact B1377943
  · exact B1377947
  · exact B1377951
  · exact B1377955
  · exact B1377959
  · exact B1377963
  · exact B1377967
  · exact B1377971
  · exact B1377975
  · exact B1377979
  · exact B1377983
  · exact B1377987
  · exact B1377991
  · exact B1377995
  · exact B1377999
  · exact B1378003
  · exact B1378007
  · exact B1378011
  · exact B1378015
  · exact B1378019
  · exact B1378023
  · exact B1378027
  · exact B1378031
  · exact B1378035
  · exact B1378039
  · exact B1378043
  · exact B1378047
  · exact B1378051
  · exact B1378055
  · exact B1378059
  · exact B1378063
  · exact B1378067
  · exact B1378071
  · exact B1378075
  · exact B1378079
  · exact B1378083
  · exact B1378087
  · exact B1378091
  · exact B1378095
  · exact B1378099
  · exact B1378103
  · exact B1378107
  · exact B1378111
  · exact B1378115
  · exact B1378119
  · exact B1378123
  · exact B1378127
  · exact B1378131
  · exact B1378135
  · exact B1378139
  · exact B1378143
  · exact B1378147
  · exact B1378151
  · exact B1378155
  · exact B1378159
  · exact B1378163
  · exact B1378167
  · exact B1378171
  · exact B1378175
  · exact B1378179
  · exact B1378183
  · exact B1378187
  · exact B1378191
  · exact B1378195
  · exact B1378199
  · exact B1378203
  · exact B1378207
  · exact B1378211
  · exact B1378215
  · exact B1378219
  · exact B1378223
  · exact B1378227
  · exact B1378231
  · exact B1378235
  · exact B1378239
  · exact B1378243
  · exact B1378247
  · exact B1378251
  · exact B1378255
  · exact B1378259
  · exact B1378263
  · exact B1378267
  · exact B1378271
  · exact B1378275
  · exact B1378279
  · exact B1378283
  · exact B1378287
  · exact B1378291
  · exact B1378295
  · exact B1378299
  · exact B1378303
  · exact B1378307
  · exact B1378311
  · exact B1378315
  · exact B1378319
  · exact B1378323
  · exact B1378327
  · exact B1378331
  · exact B1378335
  · exact B1378339
  · exact B1378343
  · exact B1378347
  · exact B1378351
  · exact B1378355
  · exact B1378359
  · exact B1378363
  · exact B1378367
  · exact B1378371
  · exact B1378375
  · exact B1378379
  · exact B1378383
  · exact B1378387
  · exact B1378391
  · exact B1378395
  · exact B1378399
  · exact B1378403
  · exact B1378407
  · exact B1378411
  · exact B1378415
  · exact B1378419
  · exact B1378423
  · exact B1378427
  · exact B1378431
  · exact B1378435
  · exact B1378439
  · exact B1378443
  · exact B1378447
  · exact B1378451
  · exact B1378455
  · exact B1378459
  · exact B1378463
  · exact B1378467
  · exact B1378471
  · exact B1378475
  · exact B1378479
  · exact B1378483
  · exact B1378487
  · exact B1378491
  · exact B1378495
  · exact B1378499
  · exact B1378503
  · exact B1378507
  · exact B1378511
  · exact B1378515
  · exact B1378519
  · exact B1378523
  · exact B1378527
  · exact B1378531
  · exact B1378535
  · exact B1378539
  · exact B1378543
  · exact B1378547
  · exact B1378551
  · exact B1378555
  · exact B1378559
  · exact B1378563
  · exact B1378567
  · exact B1378571
  · exact B1378575
  · exact B1378579
  · exact B1378583
  · exact B1378587
  · exact B1378591
  · exact B1378595
  · exact B1378599
  · exact B1378603
  · exact B1378607
  · exact B1378611
  · exact B1378615
  · exact B1378619
  · exact B1378623
  · exact B1378627
  · exact B1378631
  · exact B1378635
  · exact B1378639
  · exact B1378643
  · exact B1378647
  · exact B1378651
  · exact B1378655
  · exact B1378659
  · exact B1378663
  · exact B1378667
  · exact B1378671
  · exact B1378675
  · exact B1378679
  · exact B1378683
  · exact B1378687
  · exact B1378691
  · exact B1378695
  · exact B1378699
  · exact B1378703
  · exact B1378707
  · exact B1378711
  · exact B1378715
  · exact B1378719
  · exact B1378723
  · exact B1378727
  · exact B1378731
  · exact B1378735
  · exact B1378739
  · exact B1378743
  · exact B1378747
  · exact B1378751
  · exact B1378755
  · exact B1378759
  · exact B1378763
  · exact B1378767
  · exact B1378771
  · exact B1378775
  · exact B1378779
  · exact B1378783
  · exact B1378787
  · exact B1378791
  · exact B1378795
  · exact B1378799
  · exact B1378803
  · exact B1378807
  · exact B1378811
  · exact B1378815
  · exact B1378819
  · exact B1378823
  · exact B1378827
  · exact B1378831
  · exact B1378835
  · exact B1378839
  · exact B1378843
  · exact B1378847
  · exact B1378851
  · exact B1378855
  · exact B1378859
  · exact B1378863
  · exact B1378867
  · exact B1378871
  · exact B1378875
  · exact B1378879
  · exact B1378883
  · exact B1378887
  · exact B1378891
  · exact B1378895
  · exact B1378899
  · exact B1378903
  · exact B1378907
  · exact B1378911
  · exact B1378915
  · exact B1378919
  · exact B1378923
  · exact B1378927
  · exact B1378931
  · exact B1378935
  · exact B1378939
  · exact B1378943
  · exact B1378947
  · exact B1378951
  · exact B1378955
  · exact B1378959
  · exact B1378963
  · exact B1378967
  · exact B1378971
  · exact B1378975
  · exact B1378979
  · exact B1378983
  · exact B1378987
  · exact B1378991
  · exact B1378995
  · exact B1378999
  · exact B1379003
  · exact B1379007
  · exact B1379011
  · exact B1379015
  · exact B1379019
  · exact B1379023
  · exact B1379027
  · exact B1379031
  · exact B1379035
  · exact B1379039
  · exact B1379043
  · exact B1379047
  · exact B1379051
  · exact B1379055
  · exact B1379059
  · exact B1379063
  · exact B1379067
  · exact B1379071
  · exact B1379075
  · exact B1379079
  · exact B1379083
  · exact B1379087
  · exact B1379091
  · exact B1379095
  · exact B1379099
  · exact B1379103
  · exact B1379107
  · exact B1379111
  · exact B1379115
  · exact B1379119
  · exact B1379123
  · exact B1379127
  · exact B1379131
  · exact B1379135
  · exact B1379139
  · exact B1379143
  · exact B1379147
  · exact B1379151
  · exact B1379155
  · exact B1379159
  · exact B1379163
  · exact B1379167
  · exact B1379171
  · exact B1379175
  · exact B1379179
  · exact B1379183
  · exact B1379187
  · exact B1379191
  · exact B1379195
  · exact B1379199
  · exact B1379203
  · exact B1379207
  · exact B1379211
  · exact B1379215
  · exact B1379219
  · exact B1379223
  · exact B1379227
  · exact B1379231
  · exact B1379235
  · exact B1379239
  · exact B1379243
  · exact B1379247
  · exact B1379251
  · exact B1379255
  · exact B1379259
  · exact B1379263
  · exact B1379267
  · exact B1379271
  · exact B1379275
  · exact B1379279
  · exact B1379283
  · exact B1379287
  · exact B1379291
  · exact B1379295
  · exact B1379299
  · exact B1379303
  · exact B1379307
  · exact B1379311
  · exact B1379315
  · exact B1379319
  · exact B1379323
  · exact B1379327
  · exact B1379331
  · exact B1379335
  · exact B1379339
  · exact B1379343
  · exact B1379347
  · exact B1379351
  · exact B1379355
  · exact B1379359
  · exact B1379363
  · exact B1379367
  · exact B1379371
  · exact B1379375
  · exact B1379379
  · exact B1379383
  · exact B1379387
  · exact B1379391
  · exact B1379395
  · exact B1379399
  · exact B1379403
  · exact B1379407
  · exact B1379411
  · exact B1379415
  · exact B1379419
  · exact B1379423
  · exact B1379427
  · exact B1379431
  · exact B1379435
  · exact B1379439
  · exact B1379443
  · exact B1379447
  · exact B1379451
  · exact B1379455
  · exact B1379459
  · exact B1379463
  · exact B1379467
  · exact B1379471
  · exact B1379475
  · exact B1379479
  · exact B1379483
  · exact B1379487
  · exact B1379491
  · exact B1379495
  · exact B1379499
  · exact B1379503
  · exact B1379507

theorem solution (m : ℕ) (hlo : 1377508 ≤ m) (hhi : m ≤ 1379508) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 344377 ≤ j := by omega
    have hj2 : j ≤ 344876 := by omega
    have hb : Blo 1377508 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
