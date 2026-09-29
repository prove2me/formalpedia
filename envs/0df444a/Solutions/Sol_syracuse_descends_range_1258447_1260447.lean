-- Prove2me | solution 1 for syracuse_descends_range_1258447_1260447
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:21.948355+00:00
-- url     : https://prove2.me/submissions/722cdff7-ff1d-4ee2-936e-98002eb2bdeb

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


theorem B1417225 : Blo 1258447 1417225 := bbase (se 2 (by rfl) ⟨531459, by rfl⟩ : syracuseStep 1417225 = 1062919) (by norm_num)
theorem B2392085 : Blo 1258447 2392085 := bbase (se 6 (by rfl) ⟨56064, by rfl⟩ : syracuseStep 2392085 = 112129) (by norm_num)
theorem B2834477 : Blo 1258447 2834477 := bbase (se 3 (by rfl) ⟨531464, by rfl⟩ : syracuseStep 2834477 = 1062929) (by norm_num)
theorem B1417261 : Blo 1258447 1417261 := bbase (se 3 (by rfl) ⟨265736, by rfl⟩ : syracuseStep 1417261 = 531473) (by norm_num)
theorem B1417297 : Blo 1258447 1417297 := bbase (se 2 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 1417297 = 1062973) (by norm_num)
theorem B3186773 : Blo 1258447 3186773 := bbase (se 8 (by rfl) ⟨18672, by rfl⟩ : syracuseStep 3186773 = 37345) (by norm_num)
theorem B2834549 : Blo 1258447 2834549 := bbase (se 5 (by rfl) ⟨132869, by rfl⟩ : syracuseStep 2834549 = 265739) (by norm_num)
theorem B1417333 : Blo 1258447 1417333 := bbase (se 5 (by rfl) ⟨66437, by rfl⟩ : syracuseStep 1417333 = 132875) (by norm_num)
theorem B3588229 : Blo 1258447 3588229 := bbase (se 4 (by rfl) ⟨336396, by rfl⟩ : syracuseStep 3588229 = 672793) (by norm_num)
theorem B4251797 : Blo 1258447 4251797 := bbase (se 6 (by rfl) ⟨99651, by rfl⟩ : syracuseStep 4251797 = 199303) (by norm_num)
theorem B1417369 : Blo 1258447 1417369 := bbase (se 2 (by rfl) ⟨531513, by rfl⟩ : syracuseStep 1417369 = 1063027) (by norm_num)
theorem B2392229 : Blo 1258447 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B2834621 : Blo 1258447 2834621 := bbase (se 3 (by rfl) ⟨531491, by rfl⟩ : syracuseStep 2834621 = 1062983) (by norm_num)
theorem B1417405 : Blo 1258447 1417405 := bbase (se 3 (by rfl) ⟨265763, by rfl⟩ : syracuseStep 1417405 = 531527) (by norm_num)
theorem B4849861 : Blo 1258447 4849861 := bbase (se 4 (by rfl) ⟨454674, by rfl⟩ : syracuseStep 4849861 = 909349) (by norm_num)
theorem B1417441 : Blo 1258447 1417441 := bbase (se 2 (by rfl) ⟨531540, by rfl⟩ : syracuseStep 1417441 = 1063081) (by norm_num)
theorem B7176437 : Blo 1258447 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B2834693 : Blo 1258447 2834693 := bbase (se 4 (by rfl) ⟨265752, by rfl⟩ : syracuseStep 2834693 = 531505) (by norm_num)
theorem B1417477 : Blo 1258447 1417477 := bbase (se 4 (by rfl) ⟨132888, by rfl⟩ : syracuseStep 1417477 = 265777) (by norm_num)
theorem B3186965 : Blo 1258447 3186965 := bbase (se 6 (by rfl) ⟨74694, by rfl⟩ : syracuseStep 3186965 = 149389) (by norm_num)
theorem B1417513 : Blo 1258447 1417513 := bbase (se 2 (by rfl) ⟨531567, by rfl⟩ : syracuseStep 1417513 = 1063135) (by norm_num)
theorem B2834765 : Blo 1258447 2834765 := bbase (se 3 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 2834765 = 1063037) (by norm_num)
theorem B1417549 : Blo 1258447 1417549 := bbase (se 3 (by rfl) ⟨265790, by rfl⟩ : syracuseStep 1417549 = 531581) (by norm_num)
theorem B1417585 : Blo 1258447 1417585 := bbase (se 2 (by rfl) ⟨531594, by rfl⟩ : syracuseStep 1417585 = 1063189) (by norm_num)
theorem B18153877 : Blo 1258447 18153877 := bbase (se 6 (by rfl) ⟨425481, by rfl⟩ : syracuseStep 18153877 = 850963) (by norm_num)
theorem B2834837 : Blo 1258447 2834837 := bbase (se 6 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 2834837 = 132883) (by norm_num)
theorem B1417621 : Blo 1258447 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B1417657 : Blo 1258447 1417657 := bbase (se 2 (by rfl) ⟨531621, by rfl⟩ : syracuseStep 1417657 = 1063243) (by norm_num)
theorem B2425277 : Blo 1258447 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B2392517 : Blo 1258447 2392517 := bbase (se 4 (by rfl) ⟨224298, by rfl⟩ : syracuseStep 2392517 = 448597) (by norm_num)
theorem B2834909 : Blo 1258447 2834909 := bbase (se 3 (by rfl) ⟨531545, by rfl⟩ : syracuseStep 2834909 = 1063091) (by norm_num)
theorem B1417693 : Blo 1258447 1417693 := bbase (se 3 (by rfl) ⟨265817, by rfl⟩ : syracuseStep 1417693 = 531635) (by norm_num)
theorem B1343989 : Blo 1258447 1343989 := bbase (se 5 (by rfl) ⟨62999, by rfl⟩ : syracuseStep 1343989 = 125999) (by norm_num)
theorem B1417729 : Blo 1258447 1417729 := bbase (se 2 (by rfl) ⟨531648, by rfl⟩ : syracuseStep 1417729 = 1063297) (by norm_num)
theorem B1794565 : Blo 1258447 1794565 := bbase (se 4 (by rfl) ⟨168240, by rfl⟩ : syracuseStep 1794565 = 336481) (by norm_num)
theorem B2834981 : Blo 1258447 2834981 := bbase (se 4 (by rfl) ⟨265779, by rfl⟩ : syracuseStep 2834981 = 531559) (by norm_num)
theorem B1417765 : Blo 1258447 1417765 := bbase (se 4 (by rfl) ⟨132915, by rfl⟩ : syracuseStep 1417765 = 265831) (by norm_num)
theorem B4252229 : Blo 1258447 4252229 := bbase (se 4 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 4252229 = 797293) (by norm_num)
theorem B1417801 : Blo 1258447 1417801 := bbase (se 2 (by rfl) ⟨531675, by rfl⟩ : syracuseStep 1417801 = 1063351) (by norm_num)
theorem B9568853 : Blo 1258447 9568853 := bbase (se 8 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 9568853 = 112135) (by norm_num)
theorem B2392669 : Blo 1258447 2392669 := bbase (se 3 (by rfl) ⟨448625, by rfl⟩ : syracuseStep 2392669 = 897251) (by norm_num)
theorem B3187309 : Blo 1258447 3187309 := bbase (se 3 (by rfl) ⟨597620, by rfl⟩ : syracuseStep 3187309 = 1195241) (by norm_num)
theorem B2835053 : Blo 1258447 2835053 := bbase (se 3 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 2835053 = 1063145) (by norm_num)
theorem B1417837 : Blo 1258447 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B1417873 : Blo 1258447 1417873 := bbase (se 2 (by rfl) ⟨531702, by rfl⟩ : syracuseStep 1417873 = 1063405) (by norm_num)
theorem B2835125 : Blo 1258447 2835125 := bbase (se 5 (by rfl) ⟨132896, by rfl⟩ : syracuseStep 2835125 = 265793) (by norm_num)
theorem B1417909 : Blo 1258447 1417909 := bbase (se 5 (by rfl) ⟨66464, by rfl⟩ : syracuseStep 1417909 = 132929) (by norm_num)
theorem B2155205 : Blo 1258447 2155205 := bbase (se 4 (by rfl) ⟨202050, by rfl⟩ : syracuseStep 2155205 = 404101) (by norm_num)
theorem B1417945 : Blo 1258447 1417945 := bbase (se 2 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 1417945 = 1063459) (by norm_num)
theorem B3187421 : Blo 1258447 3187421 := bbase (se 3 (by rfl) ⟨597641, by rfl⟩ : syracuseStep 3187421 = 1195283) (by norm_num)
theorem B2155261 : Blo 1258447 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B2835197 : Blo 1258447 2835197 := bbase (se 3 (by rfl) ⟨531599, by rfl⟩ : syracuseStep 2835197 = 1063199) (by norm_num)
theorem B1417981 : Blo 1258447 1417981 := bbase (se 3 (by rfl) ⟨265871, by rfl⟩ : syracuseStep 1417981 = 531743) (by norm_num)
theorem B2687789 : Blo 1258447 2687789 := bbase (se 3 (by rfl) ⟨503960, by rfl⟩ : syracuseStep 2687789 = 1007921) (by norm_num)
theorem B6374213 : Blo 1258447 6374213 := bbase (se 4 (by rfl) ⟨597582, by rfl⟩ : syracuseStep 6374213 = 1195165) (by norm_num)
theorem B2835269 : Blo 1258447 2835269 := bbase (se 4 (by rfl) ⟨265806, by rfl⟩ : syracuseStep 2835269 = 531613) (by norm_num)
theorem B73630549 : Blo 1258447 73630549 := bbase (se 9 (by rfl) ⟨215714, by rfl⟩ : syracuseStep 73630549 = 431429) (by norm_num)
theorem B3023725 : Blo 1258447 3023725 := bbase (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) (by norm_num)
theorem B3277685 : Blo 1258447 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B2835341 : Blo 1258447 2835341 := bbase (se 3 (by rfl) ⟨531626, by rfl⟩ : syracuseStep 2835341 = 1063253) (by norm_num)
theorem B11797397 : Blo 1258447 11797397 := bbase (se 6 (by rfl) ⟨276501, by rfl⟩ : syracuseStep 11797397 = 553003) (by norm_num)
theorem B20423573 : Blo 1258447 20423573 := bbase (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) (by norm_num)
theorem B2270101 : Blo 1258447 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B3187613 : Blo 1258447 3187613 := bbase (se 3 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 3187613 = 1195355) (by norm_num)
theorem B5104549 : Blo 1258447 5104549 := bbase (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) (by norm_num)
theorem B1344433 : Blo 1258447 1344433 := bbase (se 2 (by rfl) ⟨504162, by rfl⟩ : syracuseStep 1344433 = 1008325) (by norm_num)
theorem B2835413 : Blo 1258447 2835413 := bbase (se 7 (by rfl) ⟨33227, by rfl⟩ : syracuseStep 2835413 = 66455) (by norm_num)
theorem B5104613 : Blo 1258447 5104613 := bbase (se 4 (by rfl) ⟨478557, by rfl⟩ : syracuseStep 5104613 = 957115) (by norm_num)
theorem B9561077 : Blo 1258447 9561077 := bbase (se 5 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 9561077 = 896351) (by norm_num)
theorem B4252661 : Blo 1258447 4252661 := bbase (se 5 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 4252661 = 398687) (by norm_num)
theorem B2835485 : Blo 1258447 2835485 := bbase (se 3 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 2835485 = 1063307) (by norm_num)
theorem B6464549 : Blo 1258447 6464549 := bbase (se 4 (by rfl) ⟨606051, by rfl⟩ : syracuseStep 6464549 = 1212103) (by norm_num)
theorem B1344557 : Blo 1258447 1344557 := bbase (se 3 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 1344557 = 504209) (by norm_num)
theorem B41976917 : Blo 1258447 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B5104741 : Blo 1258447 5104741 := bbase (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) (by norm_num)
theorem B2835557 : Blo 1258447 2835557 := bbase (se 4 (by rfl) ⟨265833, by rfl⟩ : syracuseStep 2835557 = 531667) (by norm_num)
theorem B4539509 : Blo 1258447 4539509 := bbase (se 5 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 4539509 = 425579) (by norm_num)
theorem B22103189 : Blo 1258447 22103189 := bbase (se 6 (by rfl) ⟨518043, by rfl⟩ : syracuseStep 22103189 = 1036087) (by norm_num)
theorem B2688157 : Blo 1258447 2688157 := bbase (se 3 (by rfl) ⟨504029, by rfl⟩ : syracuseStep 2688157 = 1008059) (by norm_num)
theorem B2835629 : Blo 1258447 2835629 := bbase (se 3 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 2835629 = 1063361) (by norm_num)
theorem B2270389 : Blo 1258447 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B3187957 : Blo 1258447 3187957 := bbase (se 5 (by rfl) ⟨149435, by rfl⟩ : syracuseStep 3187957 = 298871) (by norm_num)
theorem B2835701 : Blo 1258447 2835701 := bbase (se 5 (by rfl) ⟨132923, by rfl⟩ : syracuseStep 2835701 = 265847) (by norm_num)
theorem B1344809 : Blo 1258447 1344809 := bbase (se 2 (by rfl) ⟨504303, by rfl⟩ : syracuseStep 1344809 = 1008607) (by norm_num)
theorem B2835773 : Blo 1258447 2835773 := bbase (se 3 (by rfl) ⟨531707, by rfl⟩ : syracuseStep 2835773 = 1063415) (by norm_num)
theorem B3188069 : Blo 1258447 3188069 := bbase (se 4 (by rfl) ⟨298881, by rfl⟩ : syracuseStep 3188069 = 597763) (by norm_num)
theorem B2835845 : Blo 1258447 2835845 := bbase (se 4 (by rfl) ⟨265860, by rfl⟩ : syracuseStep 2835845 = 531721) (by norm_num)
theorem B4539797 : Blo 1258447 4539797 := bbase (se 6 (by rfl) ⟨106401, by rfl⟩ : syracuseStep 4539797 = 212803) (by norm_num)
theorem B4253093 : Blo 1258447 4253093 := bbase (se 4 (by rfl) ⟨398727, by rfl⟩ : syracuseStep 4253093 = 797455) (by norm_num)
theorem B2835917 : Blo 1258447 2835917 := bbase (se 3 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 2835917 = 1063469) (by norm_num)
theorem B3024341 : Blo 1258447 3024341 := bbase (se 7 (by rfl) ⟨35441, by rfl⟩ : syracuseStep 3024341 = 70883) (by norm_num)
theorem B10765781 : Blo 1258447 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B2016733 : Blo 1258447 2016733 := bbase (se 3 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 2016733 = 756275) (by norm_num)
theorem B2835989 : Blo 1258447 2835989 := bbase (se 6 (by rfl) ⟨66468, by rfl⟩ : syracuseStep 2835989 = 132937) (by norm_num)
theorem B3188261 : Blo 1258447 3188261 := bbase (se 4 (by rfl) ⟨298899, by rfl⟩ : syracuseStep 3188261 = 597799) (by norm_num)
theorem B8611381 : Blo 1258447 8611381 := bbase (se 5 (by rfl) ⟨403658, by rfl⟩ : syracuseStep 8611381 = 807317) (by norm_num)
theorem B10757717 : Blo 1258447 10757717 := bbase (se 8 (by rfl) ⟨63033, by rfl⟩ : syracuseStep 10757717 = 126067) (by norm_num)
theorem B4785749 : Blo 1258447 4785749 := bbase (se 8 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 4785749 = 56083) (by norm_num)
theorem B1435253 : Blo 1258447 1435253 := bbase (se 5 (by rfl) ⟨67277, by rfl⟩ : syracuseStep 1435253 = 134555) (by norm_num)
theorem B3024533 : Blo 1258447 3024533 := bbase (se 6 (by rfl) ⟨70887, by rfl⟩ : syracuseStep 3024533 = 141775) (by norm_num)
theorem B1345253 : Blo 1258447 1345253 := bbase (se 4 (by rfl) ⟨126117, by rfl⟩ : syracuseStep 1345253 = 252235) (by norm_num)
theorem B2270965 : Blo 1258447 2270965 := bbase (se 5 (by rfl) ⟨106451, by rfl⟩ : syracuseStep 2270965 = 212903) (by norm_num)
theorem B1615645 : Blo 1258447 1615645 := bbase (se 3 (by rfl) ⟨302933, by rfl⟩ : syracuseStep 1615645 = 605867) (by norm_num)
theorem B7767893 : Blo 1258447 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B4253525 : Blo 1258447 4253525 := bbase (se 9 (by rfl) ⟨12461, by rfl⟩ : syracuseStep 4253525 = 24923) (by norm_num)
theorem B1615717 : Blo 1258447 1615717 := bbase (se 4 (by rfl) ⟨151473, by rfl⟩ : syracuseStep 1615717 = 302947) (by norm_num)
theorem B3188605 : Blo 1258447 3188605 := bbase (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) (by norm_num)
theorem B1574845 : Blo 1258447 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B2123725 : Blo 1258447 2123725 := bbase (se 3 (by rfl) ⟨398198, by rfl⟩ : syracuseStep 2123725 = 796397) (by norm_num)
theorem B1345501 : Blo 1258447 1345501 := bbase (se 3 (by rfl) ⟨252281, by rfl⟩ : syracuseStep 1345501 = 504563) (by norm_num)
theorem B3188717 : Blo 1258447 3188717 := bbase (se 3 (by rfl) ⟨597884, by rfl⟩ : syracuseStep 3188717 = 1195769) (by norm_num)
theorem B2123813 : Blo 1258447 2123813 := bbase (se 4 (by rfl) ⟨199107, by rfl⟩ : syracuseStep 2123813 = 398215) (by norm_num)
theorem B6375509 : Blo 1258447 6375509 := bbase (se 8 (by rfl) ⟨37356, by rfl⟩ : syracuseStep 6375509 = 74713) (by norm_num)
theorem B2017405 : Blo 1258447 2017405 := bbase (se 3 (by rfl) ⟨378263, by rfl⟩ : syracuseStep 2017405 = 756527) (by norm_num)
theorem B2123941 : Blo 1258447 2123941 := bbase (se 4 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 2123941 = 398239) (by norm_num)
theorem B3188909 : Blo 1258447 3188909 := bbase (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) (by norm_num)
theorem B3401909 : Blo 1258447 3401909 := bbase (se 5 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 3401909 = 318929) (by norm_num)
theorem B3025109 : Blo 1258447 3025109 := bbase (se 7 (by rfl) ⟨35450, by rfl⟩ : syracuseStep 3025109 = 70901) (by norm_num)
theorem B2124029 : Blo 1258447 2124029 := bbase (se 3 (by rfl) ⟨398255, by rfl⟩ : syracuseStep 2124029 = 796511) (by norm_num)
theorem B4253957 : Blo 1258447 4253957 := bbase (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) (by norm_num)
theorem B4778261 : Blo 1258447 4778261 := bbase (se 6 (by rfl) ⟨111990, by rfl⟩ : syracuseStep 4778261 = 223981) (by norm_num)
theorem B6056213 : Blo 1258447 6056213 := bbase (se 6 (by rfl) ⟨141942, by rfl⟩ : syracuseStep 6056213 = 283885) (by norm_num)
theorem B2124157 : Blo 1258447 2124157 := bbase (se 3 (by rfl) ⟨398279, by rfl⟩ : syracuseStep 2124157 = 796559) (by norm_num)
theorem B7178645 : Blo 1258447 7178645 := bbase (se 6 (by rfl) ⟨168249, by rfl⟩ : syracuseStep 7178645 = 336499) (by norm_num)
theorem B1345945 : Blo 1258447 1345945 := bbase (se 2 (by rfl) ⟨504729, by rfl⟩ : syracuseStep 1345945 = 1009459) (by norm_num)
theorem B4032965 : Blo 1258447 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B2124245 : Blo 1258447 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B3189253 : Blo 1258447 3189253 := bbase (se 4 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 3189253 = 597985) (by norm_num)
theorem B2124373 : Blo 1258447 2124373 := bbase (se 8 (by rfl) ⟨12447, by rfl⟩ : syracuseStep 2124373 = 24895) (by norm_num)
theorem B3025493 : Blo 1258447 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B3189365 : Blo 1258447 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B2689661 : Blo 1258447 2689661 := bbase (se 3 (by rfl) ⟨504311, by rfl⟩ : syracuseStep 2689661 = 1008623) (by norm_num)
theorem B2124461 : Blo 1258447 2124461 := bbase (se 3 (by rfl) ⟨398336, by rfl⟩ : syracuseStep 2124461 = 796673) (by norm_num)
theorem B5376725 : Blo 1258447 5376725 := bbase (se 7 (by rfl) ⟨63008, by rfl⟩ : syracuseStep 5376725 = 126017) (by norm_num)
theorem B2689805 : Blo 1258447 2689805 := bbase (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) (by norm_num)
theorem B2124589 : Blo 1258447 2124589 := bbase (se 3 (by rfl) ⟨398360, by rfl⟩ : syracuseStep 2124589 = 796721) (by norm_num)
theorem B3189557 : Blo 1258447 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2124677 : Blo 1258447 2124677 := bbase (se 4 (by rfl) ⟨199188, by rfl⟩ : syracuseStep 2124677 = 398377) (by norm_num)
theorem B5377013 : Blo 1258447 5377013 := bbase (se 5 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 5377013 = 504095) (by norm_num)
theorem B11496437 : Blo 1258447 11496437 := bbase (se 5 (by rfl) ⟨538895, by rfl⟩ : syracuseStep 11496437 = 1077791) (by norm_num)
theorem B2124805 : Blo 1258447 2124805 := bbase (se 4 (by rfl) ⟨199200, by rfl⟩ : syracuseStep 2124805 = 398401) (by norm_num)
theorem B2124893 : Blo 1258447 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B2018405 : Blo 1258447 2018405 := bbase (se 4 (by rfl) ⟨189225, by rfl⟩ : syracuseStep 2018405 = 378451) (by norm_num)
theorem B2690165 : Blo 1258447 2690165 := bbase (se 5 (by rfl) ⟨126101, by rfl⟩ : syracuseStep 2690165 = 252203) (by norm_num)
theorem B3189901 : Blo 1258447 3189901 := bbase (se 3 (by rfl) ⟨598106, by rfl⟩ : syracuseStep 3189901 = 1196213) (by norm_num)
theorem B3402901 : Blo 1258447 3402901 := bbase (se 6 (by rfl) ⟨79755, by rfl⟩ : syracuseStep 3402901 = 159511) (by norm_num)
theorem B3230941 : Blo 1258447 3230941 := bbase (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) (by norm_num)
theorem B2125021 : Blo 1258447 2125021 := bbase (se 3 (by rfl) ⟨398441, by rfl⟩ : syracuseStep 2125021 = 796883) (by norm_num)
theorem B3190013 : Blo 1258447 3190013 := bbase (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) (by norm_num)
theorem B2125109 : Blo 1258447 2125109 := bbase (se 5 (by rfl) ⟨99614, by rfl⟩ : syracuseStep 2125109 = 199229) (by norm_num)
theorem B6376805 : Blo 1258447 6376805 := bbase (se 4 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 6376805 = 1195651) (by norm_num)
theorem B4541845 : Blo 1258447 4541845 := bbase (se 6 (by rfl) ⟨106449, by rfl⟩ : syracuseStep 4541845 = 212899) (by norm_num)
theorem B4779445 : Blo 1258447 4779445 := bbase (se 5 (by rfl) ⟨224036, by rfl⟩ : syracuseStep 4779445 = 448073) (by norm_num)
theorem B2125237 : Blo 1258447 2125237 := bbase (se 5 (by rfl) ⟨99620, by rfl⟩ : syracuseStep 2125237 = 199241) (by norm_num)
theorem B1887677 : Blo 1258447 1887677 := bbase (se 3 (by rfl) ⟨353939, by rfl⟩ : syracuseStep 1887677 = 707879) (by norm_num)
theorem B3190205 : Blo 1258447 3190205 := bbase (se 3 (by rfl) ⟨598163, by rfl⟩ : syracuseStep 3190205 = 1196327) (by norm_num)
theorem B1887701 : Blo 1258447 1887701 := bbase (se 7 (by rfl) ⟨22121, by rfl⟩ : syracuseStep 1887701 = 44243) (by norm_num)
theorem B24202709 : Blo 1258447 24202709 := bbase (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) (by norm_num)
theorem B1887725 : Blo 1258447 1887725 := bbase (se 3 (by rfl) ⟨353948, by rfl⟩ : syracuseStep 1887725 = 707897) (by norm_num)
theorem B1887749 : Blo 1258447 1887749 := bbase (se 4 (by rfl) ⟨176976, by rfl⟩ : syracuseStep 1887749 = 353953) (by norm_num)
theorem B6458885 : Blo 1258447 6458885 := bbase (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) (by norm_num)
theorem B2125325 : Blo 1258447 2125325 := bbase (se 3 (by rfl) ⟨398498, by rfl⟩ : syracuseStep 2125325 = 796997) (by norm_num)
theorem B1887773 : Blo 1258447 1887773 := bbase (se 3 (by rfl) ⟨353957, by rfl⟩ : syracuseStep 1887773 = 707915) (by norm_num)
theorem B4541989 : Blo 1258447 4541989 := bbase (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) (by norm_num)
theorem B1887797 : Blo 1258447 1887797 := bbase (se 5 (by rfl) ⟨88490, by rfl⟩ : syracuseStep 1887797 = 176981) (by norm_num)
theorem B1592885 : Blo 1258447 1592885 := bbase (se 5 (by rfl) ⟨74666, by rfl⟩ : syracuseStep 1592885 = 149333) (by norm_num)
theorem B6049333 : Blo 1258447 6049333 := bbase (se 5 (by rfl) ⟨283562, by rfl⟩ : syracuseStep 6049333 = 567125) (by norm_num)
theorem B1887821 : Blo 1258447 1887821 := bbase (se 3 (by rfl) ⟨353966, by rfl⟩ : syracuseStep 1887821 = 707933) (by norm_num)
theorem B6131285 : Blo 1258447 6131285 := bbase (se 8 (by rfl) ⟨35925, by rfl⟩ : syracuseStep 6131285 = 71851) (by norm_num)
theorem B1887845 : Blo 1258447 1887845 := bbase (se 4 (by rfl) ⟨176985, by rfl⟩ : syracuseStep 1887845 = 353971) (by norm_num)
theorem B1592941 : Blo 1258447 1592941 := bbase (se 3 (by rfl) ⟨298676, by rfl⟩ : syracuseStep 1592941 = 597353) (by norm_num)
theorem B1887869 : Blo 1258447 1887869 := bbase (se 3 (by rfl) ⟨353975, by rfl⟩ : syracuseStep 1887869 = 707951) (by norm_num)
theorem B2125453 : Blo 1258447 2125453 := bbase (se 3 (by rfl) ⟨398522, by rfl⟩ : syracuseStep 2125453 = 797045) (by norm_num)
theorem B1887893 : Blo 1258447 1887893 := bbase (se 6 (by rfl) ⟨44247, by rfl⟩ : syracuseStep 1887893 = 88495) (by norm_num)
theorem B1887917 : Blo 1258447 1887917 := bbase (se 3 (by rfl) ⟨353984, by rfl⟩ : syracuseStep 1887917 = 707969) (by norm_num)
theorem B1887941 : Blo 1258447 1887941 := bbase (se 4 (by rfl) ⟨176994, by rfl⟩ : syracuseStep 1887941 = 353989) (by norm_num)
theorem B4542149 : Blo 1258447 4542149 := bbase (se 4 (by rfl) ⟨425826, by rfl⟩ : syracuseStep 4542149 = 851653) (by norm_num)
theorem B1593037 : Blo 1258447 1593037 := bbase (se 3 (by rfl) ⟨298694, by rfl⟩ : syracuseStep 1593037 = 597389) (by norm_num)
theorem B1887965 : Blo 1258447 1887965 := bbase (se 3 (by rfl) ⟨353993, by rfl⟩ : syracuseStep 1887965 = 707987) (by norm_num)
theorem B4779749 : Blo 1258447 4779749 := bbase (se 4 (by rfl) ⟨448101, by rfl⟩ : syracuseStep 4779749 = 896203) (by norm_num)
theorem B5377765 : Blo 1258447 5377765 := bbase (se 4 (by rfl) ⟨504165, by rfl⟩ : syracuseStep 5377765 = 1008331) (by norm_num)
theorem B2125541 : Blo 1258447 2125541 := bbase (se 4 (by rfl) ⟨199269, by rfl⟩ : syracuseStep 2125541 = 398539) (by norm_num)
theorem B1887989 : Blo 1258447 1887989 := bbase (se 5 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 1887989 = 176999) (by norm_num)
theorem B1888013 : Blo 1258447 1888013 := bbase (se 3 (by rfl) ⟨354002, by rfl⟩ : syracuseStep 1888013 = 708005) (by norm_num)
theorem B1888037 : Blo 1258447 1888037 := bbase (se 4 (by rfl) ⟨177003, by rfl⟩ : syracuseStep 1888037 = 354007) (by norm_num)
theorem B1888061 : Blo 1258447 1888061 := bbase (se 3 (by rfl) ⟨354011, by rfl⟩ : syracuseStep 1888061 = 708023) (by norm_num)
theorem B4542277 : Blo 1258447 4542277 := bbase (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) (by norm_num)
theorem B1888085 : Blo 1258447 1888085 := bbase (se 9 (by rfl) ⟨5531, by rfl⟩ : syracuseStep 1888085 = 11063) (by norm_num)
theorem B2043749 : Blo 1258447 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B2125669 : Blo 1258447 2125669 := bbase (se 4 (by rfl) ⟨199281, by rfl⟩ : syracuseStep 2125669 = 398563) (by norm_num)
theorem B1888109 : Blo 1258447 1888109 := bbase (se 3 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 1888109 = 708041) (by norm_num)
theorem B1593209 : Blo 1258447 1593209 := bbase (se 2 (by rfl) ⟨597453, by rfl⟩ : syracuseStep 1593209 = 1194907) (by norm_num)
theorem B1888133 : Blo 1258447 1888133 := bbase (se 4 (by rfl) ⟨177012, by rfl⟩ : syracuseStep 1888133 = 354025) (by norm_num)
theorem B1888157 : Blo 1258447 1888157 := bbase (se 3 (by rfl) ⟨354029, by rfl⟩ : syracuseStep 1888157 = 708059) (by norm_num)
theorem B1593265 : Blo 1258447 1593265 := bbase (se 2 (by rfl) ⟨597474, by rfl⟩ : syracuseStep 1593265 = 1194949) (by norm_num)
theorem B4247477 : Blo 1258447 4247477 := bbase (se 5 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 4247477 = 398201) (by norm_num)
theorem B1888181 : Blo 1258447 1888181 := bbase (se 5 (by rfl) ⟨88508, by rfl⟩ : syracuseStep 1888181 = 177017) (by norm_num)
theorem B2125757 : Blo 1258447 2125757 := bbase (se 3 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 2125757 = 797159) (by norm_num)
theorem B1888205 : Blo 1258447 1888205 := bbase (se 3 (by rfl) ⟨354038, by rfl⟩ : syracuseStep 1888205 = 708077) (by norm_num)
theorem B1888229 : Blo 1258447 1888229 := bbase (se 4 (by rfl) ⟨177021, by rfl⟩ : syracuseStep 1888229 = 354043) (by norm_num)
theorem B2691053 : Blo 1258447 2691053 := bbase (se 3 (by rfl) ⟨504572, by rfl⟩ : syracuseStep 2691053 = 1009145) (by norm_num)
theorem B12095477 : Blo 1258447 12095477 := bbase (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) (by norm_num)
theorem B1888253 : Blo 1258447 1888253 := bbase (se 3 (by rfl) ⟨354047, by rfl⟩ : syracuseStep 1888253 = 708095) (by norm_num)
theorem B6131717 : Blo 1258447 6131717 := bbase (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) (by norm_num)
theorem B1593361 : Blo 1258447 1593361 := bbase (se 2 (by rfl) ⟨597510, by rfl⟩ : syracuseStep 1593361 = 1195021) (by norm_num)
theorem B1888277 : Blo 1258447 1888277 := bbase (se 6 (by rfl) ⟨44256, by rfl⟩ : syracuseStep 1888277 = 88513) (by norm_num)
theorem B15331349 : Blo 1258447 15331349 := bbase (se 6 (by rfl) ⟨359328, by rfl⟩ : syracuseStep 15331349 = 718657) (by norm_num)
theorem B1888301 : Blo 1258447 1888301 := bbase (se 3 (by rfl) ⟨354056, by rfl⟩ : syracuseStep 1888301 = 708113) (by norm_num)
theorem B2125885 : Blo 1258447 2125885 := bbase (se 3 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 2125885 = 797207) (by norm_num)
theorem B1888325 : Blo 1258447 1888325 := bbase (se 4 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 1888325 = 354061) (by norm_num)
theorem B8065109 : Blo 1258447 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B1888349 : Blo 1258447 1888349 := bbase (se 3 (by rfl) ⟨354065, by rfl⟩ : syracuseStep 1888349 = 708131) (by norm_num)
theorem B2551909 : Blo 1258447 2551909 := bbase (se 4 (by rfl) ⟨239241, by rfl⟩ : syracuseStep 2551909 = 478483) (by norm_num)
theorem B1888373 : Blo 1258447 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B2101373 : Blo 1258447 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B1888397 : Blo 1258447 1888397 := bbase (se 3 (by rfl) ⟨354074, by rfl⟩ : syracuseStep 1888397 = 708149) (by norm_num)
theorem B2125973 : Blo 1258447 2125973 := bbase (se 6 (by rfl) ⟨49827, by rfl⟩ : syracuseStep 2125973 = 99655) (by norm_num)
theorem B1888421 : Blo 1258447 1888421 := bbase (se 4 (by rfl) ⟨177039, by rfl⟩ : syracuseStep 1888421 = 354079) (by norm_num)
theorem B1888445 : Blo 1258447 1888445 := bbase (se 3 (by rfl) ⟨354083, by rfl⟩ : syracuseStep 1888445 = 708167) (by norm_num)
theorem B1593533 : Blo 1258447 1593533 := bbase (se 3 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 1593533 = 597575) (by norm_num)
theorem B1888469 : Blo 1258447 1888469 := bbase (se 7 (by rfl) ⟨22130, by rfl⟩ : syracuseStep 1888469 = 44261) (by norm_num)
theorem B10219733 : Blo 1258447 10219733 := bbase (se 7 (by rfl) ⟨119762, by rfl⟩ : syracuseStep 10219733 = 239525) (by norm_num)
theorem B2691301 : Blo 1258447 2691301 := bbase (se 4 (by rfl) ⟨252309, by rfl⟩ : syracuseStep 2691301 = 504619) (by norm_num)
theorem B1888493 : Blo 1258447 1888493 := bbase (se 3 (by rfl) ⟨354092, by rfl⟩ : syracuseStep 1888493 = 708185) (by norm_num)
theorem B1593589 : Blo 1258447 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1888517 : Blo 1258447 1888517 := bbase (se 4 (by rfl) ⟨177048, by rfl⟩ : syracuseStep 1888517 = 354097) (by norm_num)
theorem B2126101 : Blo 1258447 2126101 := bbase (se 6 (by rfl) ⟨49830, by rfl⟩ : syracuseStep 2126101 = 99661) (by norm_num)
theorem B1888541 : Blo 1258447 1888541 := bbase (se 3 (by rfl) ⟨354101, by rfl⟩ : syracuseStep 1888541 = 708203) (by norm_num)
theorem B1888565 : Blo 1258447 1888565 := bbase (se 5 (by rfl) ⟨88526, by rfl⟩ : syracuseStep 1888565 = 177053) (by norm_num)
theorem B3027253 : Blo 1258447 3027253 := bbase (se 5 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 3027253 = 283805) (by norm_num)
theorem B1888589 : Blo 1258447 1888589 := bbase (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) (by norm_num)
theorem B1593685 : Blo 1258447 1593685 := bbase (se 10 (by rfl) ⟨2334, by rfl⟩ : syracuseStep 1593685 = 4669) (by norm_num)
theorem B4247909 : Blo 1258447 4247909 := bbase (se 4 (by rfl) ⟨398241, by rfl⟩ : syracuseStep 4247909 = 796483) (by norm_num)
theorem B3584357 : Blo 1258447 3584357 := bbase (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) (by norm_num)
theorem B1888613 : Blo 1258447 1888613 := bbase (se 4 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 1888613 = 354115) (by norm_num)
theorem B2126189 : Blo 1258447 2126189 := bbase (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) (by norm_num)
theorem B1888637 : Blo 1258447 1888637 := bbase (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) (by norm_num)
theorem B1888661 : Blo 1258447 1888661 := bbase (se 6 (by rfl) ⟨44265, by rfl⟩ : syracuseStep 1888661 = 88531) (by norm_num)
theorem B1888685 : Blo 1258447 1888685 := bbase (se 3 (by rfl) ⟨354128, by rfl⟩ : syracuseStep 1888685 = 708257) (by norm_num)
theorem B1888709 : Blo 1258447 1888709 := bbase (se 4 (by rfl) ⟨177066, by rfl⟩ : syracuseStep 1888709 = 354133) (by norm_num)
theorem B5378501 : Blo 1258447 5378501 := bbase (se 4 (by rfl) ⟨504234, by rfl⟩ : syracuseStep 5378501 = 1008469) (by norm_num)
theorem B1888733 : Blo 1258447 1888733 := bbase (se 3 (by rfl) ⟨354137, by rfl⟩ : syracuseStep 1888733 = 708275) (by norm_num)
theorem B2126317 : Blo 1258447 2126317 := bbase (se 3 (by rfl) ⟨398684, by rfl⟩ : syracuseStep 2126317 = 797369) (by norm_num)
theorem B1888757 : Blo 1258447 1888757 := bbase (se 5 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 1888757 = 177071) (by norm_num)
theorem B1593857 : Blo 1258447 1593857 := bbase (se 2 (by rfl) ⟨597696, by rfl⟩ : syracuseStep 1593857 = 1195393) (by norm_num)
theorem B1888781 : Blo 1258447 1888781 := bbase (se 3 (by rfl) ⟨354146, by rfl⟩ : syracuseStep 1888781 = 708293) (by norm_num)
theorem B1888805 : Blo 1258447 1888805 := bbase (se 4 (by rfl) ⟨177075, by rfl⟩ : syracuseStep 1888805 = 354151) (by norm_num)
theorem B1593913 : Blo 1258447 1593913 := bbase (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) (by norm_num)
theorem B1888829 : Blo 1258447 1888829 := bbase (se 3 (by rfl) ⟨354155, by rfl⟩ : syracuseStep 1888829 = 708311) (by norm_num)
theorem B2126405 : Blo 1258447 2126405 := bbase (se 4 (by rfl) ⟨199350, by rfl⟩ : syracuseStep 2126405 = 398701) (by norm_num)
theorem B1888853 : Blo 1258447 1888853 := bbase (se 8 (by rfl) ⟨11067, by rfl⟩ : syracuseStep 1888853 = 22135) (by norm_num)
theorem B1888877 : Blo 1258447 1888877 := bbase (se 3 (by rfl) ⟨354164, by rfl⟩ : syracuseStep 1888877 = 708329) (by norm_num)
theorem B6378101 : Blo 1258447 6378101 := bbase (se 5 (by rfl) ⟨298973, by rfl⟩ : syracuseStep 6378101 = 597947) (by norm_num)
theorem B1888901 : Blo 1258447 1888901 := bbase (se 4 (by rfl) ⟨177084, by rfl⟩ : syracuseStep 1888901 = 354169) (by norm_num)
theorem B4035221 : Blo 1258447 4035221 := bbase (se 6 (by rfl) ⟨94575, by rfl⟩ : syracuseStep 4035221 = 189151) (by norm_num)
theorem B1594009 : Blo 1258447 1594009 := bbase (se 2 (by rfl) ⟨597753, by rfl⟩ : syracuseStep 1594009 = 1195507) (by norm_num)
theorem B1888925 : Blo 1258447 1888925 := bbase (se 3 (by rfl) ⟨354173, by rfl⟩ : syracuseStep 1888925 = 708347) (by norm_num)
theorem B1888949 : Blo 1258447 1888949 := bbase (se 5 (by rfl) ⟨88544, by rfl⟩ : syracuseStep 1888949 = 177089) (by norm_num)
theorem B2126533 : Blo 1258447 2126533 := bbase (se 4 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 2126533 = 398725) (by norm_num)
theorem B1888973 : Blo 1258447 1888973 := bbase (se 3 (by rfl) ⟨354182, by rfl⟩ : syracuseStep 1888973 = 708365) (by norm_num)
theorem B2691805 : Blo 1258447 2691805 := bbase (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) (by norm_num)
theorem B1888997 : Blo 1258447 1888997 := bbase (se 4 (by rfl) ⟨177093, by rfl⟩ : syracuseStep 1888997 = 354187) (by norm_num)
theorem B1889021 : Blo 1258447 1889021 := bbase (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) (by norm_num)
theorem B6804245 : Blo 1258447 6804245 := bbase (se 6 (by rfl) ⟨159474, by rfl⟩ : syracuseStep 6804245 = 318949) (by norm_num)
theorem B4248341 : Blo 1258447 4248341 := bbase (se 6 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 4248341 = 199141) (by norm_num)
theorem B1889045 : Blo 1258447 1889045 := bbase (se 6 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 1889045 = 88549) (by norm_num)
theorem B4035349 : Blo 1258447 4035349 := bbase (se 6 (by rfl) ⟨94578, by rfl⟩ : syracuseStep 4035349 = 189157) (by norm_num)
theorem B2126621 : Blo 1258447 2126621 := bbase (se 3 (by rfl) ⟨398741, by rfl⟩ : syracuseStep 2126621 = 797483) (by norm_num)
theorem B1889069 : Blo 1258447 1889069 := bbase (se 3 (by rfl) ⟨354200, by rfl⟩ : syracuseStep 1889069 = 708401) (by norm_num)
theorem B1889093 : Blo 1258447 1889093 := bbase (se 4 (by rfl) ⟨177102, by rfl⟩ : syracuseStep 1889093 = 354205) (by norm_num)
theorem B1594181 : Blo 1258447 1594181 := bbase (se 4 (by rfl) ⟨149454, by rfl⟩ : syracuseStep 1594181 = 298909) (by norm_num)
theorem B1889117 : Blo 1258447 1889117 := bbase (se 3 (by rfl) ⟨354209, by rfl⟩ : syracuseStep 1889117 = 708419) (by norm_num)
theorem B1889141 : Blo 1258447 1889141 := bbase (se 5 (by rfl) ⟨88553, by rfl⟩ : syracuseStep 1889141 = 177107) (by norm_num)
theorem B1594237 : Blo 1258447 1594237 := bbase (se 3 (by rfl) ⟨298919, by rfl⟩ : syracuseStep 1594237 = 597839) (by norm_num)
theorem B1889165 : Blo 1258447 1889165 := bbase (se 3 (by rfl) ⟨354218, by rfl⟩ : syracuseStep 1889165 = 708437) (by norm_num)
theorem B2126749 : Blo 1258447 2126749 := bbase (se 3 (by rfl) ⟨398765, by rfl⟩ : syracuseStep 2126749 = 797531) (by norm_num)
theorem B1889189 : Blo 1258447 1889189 := bbase (se 4 (by rfl) ⟨177111, by rfl⟩ : syracuseStep 1889189 = 354223) (by norm_num)
theorem B1889213 : Blo 1258447 1889213 := bbase (se 3 (by rfl) ⟨354227, by rfl⟩ : syracuseStep 1889213 = 708455) (by norm_num)
theorem B1889237 : Blo 1258447 1889237 := bbase (se 7 (by rfl) ⟨22139, by rfl⟩ : syracuseStep 1889237 = 44279) (by norm_num)
theorem B1594333 : Blo 1258447 1594333 := bbase (se 3 (by rfl) ⟨298937, by rfl⟩ : syracuseStep 1594333 = 597875) (by norm_num)
theorem B1889261 : Blo 1258447 1889261 := bbase (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) (by norm_num)
theorem B2126837 : Blo 1258447 2126837 := bbase (se 5 (by rfl) ⟨99695, by rfl⟩ : syracuseStep 2126837 = 199391) (by norm_num)
theorem B1889285 : Blo 1258447 1889285 := bbase (se 4 (by rfl) ⟨177120, by rfl⟩ : syracuseStep 1889285 = 354241) (by norm_num)
theorem B1889309 : Blo 1258447 1889309 := bbase (se 3 (by rfl) ⟨354245, by rfl⟩ : syracuseStep 1889309 = 708491) (by norm_num)
theorem B1889333 : Blo 1258447 1889333 := bbase (se 5 (by rfl) ⟨88562, by rfl⟩ : syracuseStep 1889333 = 177125) (by norm_num)
theorem B1889357 : Blo 1258447 1889357 := bbase (se 3 (by rfl) ⟨354254, by rfl⟩ : syracuseStep 1889357 = 708509) (by norm_num)
theorem B2389085 : Blo 1258447 2389085 := bbase (se 3 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 2389085 = 895907) (by norm_num)
theorem B1889381 : Blo 1258447 1889381 := bbase (se 4 (by rfl) ⟨177129, by rfl⟩ : syracuseStep 1889381 = 354259) (by norm_num)
theorem B2126965 : Blo 1258447 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B1889405 : Blo 1258447 1889405 := bbase (se 3 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 1889405 = 708527) (by norm_num)
theorem B1594505 : Blo 1258447 1594505 := bbase (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) (by norm_num)
theorem B7173269 : Blo 1258447 7173269 := bbase (se 6 (by rfl) ⟨168123, by rfl⟩ : syracuseStep 7173269 = 336247) (by norm_num)
theorem B1889429 : Blo 1258447 1889429 := bbase (se 6 (by rfl) ⟨44283, by rfl⟩ : syracuseStep 1889429 = 88567) (by norm_num)
theorem B2831525 : Blo 1258447 2831525 := bbase (se 4 (by rfl) ⟨265455, by rfl⟩ : syracuseStep 2831525 = 530911) (by norm_num)
theorem B1889453 : Blo 1258447 1889453 := bbase (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) (by norm_num)
theorem B1512641 : Blo 1258447 1512641 := bbase (se 2 (by rfl) ⟨567240, by rfl⟩ : syracuseStep 1512641 = 1134481) (by norm_num)
theorem B1594561 : Blo 1258447 1594561 := bbase (se 2 (by rfl) ⟨597960, by rfl⟩ : syracuseStep 1594561 = 1195921) (by norm_num)
theorem B4248773 : Blo 1258447 4248773 := bbase (se 4 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 4248773 = 796645) (by norm_num)
theorem B1889477 : Blo 1258447 1889477 := bbase (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) (by norm_num)
theorem B1889501 : Blo 1258447 1889501 := bbase (se 3 (by rfl) ⟨354281, by rfl⟩ : syracuseStep 1889501 = 708563) (by norm_num)
theorem B2831597 : Blo 1258447 2831597 := bbase (se 3 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 2831597 = 1061849) (by norm_num)
theorem B1889525 : Blo 1258447 1889525 := bbase (se 5 (by rfl) ⟨88571, by rfl⟩ : syracuseStep 1889525 = 177143) (by norm_num)
theorem B2553101 : Blo 1258447 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B1889549 : Blo 1258447 1889549 := bbase (se 3 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 1889549 = 708581) (by norm_num)
theorem B1594657 : Blo 1258447 1594657 := bbase (se 2 (by rfl) ⟨597996, by rfl⟩ : syracuseStep 1594657 = 1195993) (by norm_num)
theorem B1889573 : Blo 1258447 1889573 := bbase (se 4 (by rfl) ⟨177147, by rfl⟩ : syracuseStep 1889573 = 354295) (by norm_num)
theorem B3028261 : Blo 1258447 3028261 := bbase (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) (by norm_num)
theorem B2831669 : Blo 1258447 2831669 := bbase (se 5 (by rfl) ⟨132734, by rfl⟩ : syracuseStep 2831669 = 265469) (by norm_num)
theorem B1889597 : Blo 1258447 1889597 := bbase (se 3 (by rfl) ⟨354299, by rfl⟩ : syracuseStep 1889597 = 708599) (by norm_num)
theorem B1889621 : Blo 1258447 1889621 := bbase (se 15 (by rfl) ⟨86, by rfl⟩ : syracuseStep 1889621 = 173) (by norm_num)
theorem B1889645 : Blo 1258447 1889645 := bbase (se 3 (by rfl) ⟨354308, by rfl⟩ : syracuseStep 1889645 = 708617) (by norm_num)
theorem B2831741 : Blo 1258447 2831741 := bbase (se 3 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 2831741 = 1061903) (by norm_num)
theorem B1889669 : Blo 1258447 1889669 := bbase (se 4 (by rfl) ⟨177156, by rfl⟩ : syracuseStep 1889669 = 354313) (by norm_num)
theorem B3028357 : Blo 1258447 3028357 := bbase (se 4 (by rfl) ⟨283908, by rfl⟩ : syracuseStep 3028357 = 567817) (by norm_num)
theorem B1889693 : Blo 1258447 1889693 := bbase (se 3 (by rfl) ⟨354317, by rfl⟩ : syracuseStep 1889693 = 708635) (by norm_num)
theorem B1889717 : Blo 1258447 1889717 := bbase (se 5 (by rfl) ⟨88580, by rfl⟩ : syracuseStep 1889717 = 177161) (by norm_num)
theorem B2831813 : Blo 1258447 2831813 := bbase (se 4 (by rfl) ⟨265482, by rfl⟩ : syracuseStep 2831813 = 530965) (by norm_num)
theorem B1889741 : Blo 1258447 1889741 := bbase (se 3 (by rfl) ⟨354326, by rfl⟩ : syracuseStep 1889741 = 708653) (by norm_num)
theorem B1594829 : Blo 1258447 1594829 := bbase (se 3 (by rfl) ⟨299030, by rfl⟩ : syracuseStep 1594829 = 598061) (by norm_num)
theorem B5821925 : Blo 1258447 5821925 := bbase (se 4 (by rfl) ⟨545805, by rfl⟩ : syracuseStep 5821925 = 1091611) (by norm_num)
theorem B1889765 : Blo 1258447 1889765 := bbase (se 4 (by rfl) ⟨177165, by rfl⟩ : syracuseStep 1889765 = 354331) (by norm_num)
theorem B1889789 : Blo 1258447 1889789 := bbase (se 3 (by rfl) ⟨354335, by rfl⟩ : syracuseStep 1889789 = 708671) (by norm_num)
theorem B3585541 : Blo 1258447 3585541 := bbase (se 4 (by rfl) ⟨336144, by rfl⟩ : syracuseStep 3585541 = 672289) (by norm_num)
theorem B1594885 : Blo 1258447 1594885 := bbase (se 4 (by rfl) ⟨149520, by rfl⟩ : syracuseStep 1594885 = 299041) (by norm_num)
theorem B2831885 : Blo 1258447 2831885 := bbase (se 3 (by rfl) ⟨530978, by rfl⟩ : syracuseStep 2831885 = 1061957) (by norm_num)
theorem B1512977 : Blo 1258447 1512977 := bbase (se 2 (by rfl) ⟨567366, by rfl⟩ : syracuseStep 1512977 = 1134733) (by norm_num)
theorem B1889813 : Blo 1258447 1889813 := bbase (se 6 (by rfl) ⟨44292, by rfl⟩ : syracuseStep 1889813 = 88585) (by norm_num)
theorem B1889837 : Blo 1258447 1889837 := bbase (se 3 (by rfl) ⟨354344, by rfl⟩ : syracuseStep 1889837 = 708689) (by norm_num)
theorem B1889861 : Blo 1258447 1889861 := bbase (se 4 (by rfl) ⟨177174, by rfl⟩ : syracuseStep 1889861 = 354349) (by norm_num)
theorem B18142805 : Blo 1258447 18142805 := bbase (se 8 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 18142805 = 212611) (by norm_num)
theorem B2831957 : Blo 1258447 2831957 := bbase (se 8 (by rfl) ⟨16593, by rfl⟩ : syracuseStep 2831957 = 33187) (by norm_num)
theorem B1889885 : Blo 1258447 1889885 := bbase (se 3 (by rfl) ⟨354353, by rfl⟩ : syracuseStep 1889885 = 708707) (by norm_num)
theorem B1594981 : Blo 1258447 1594981 := bbase (se 4 (by rfl) ⟨149529, by rfl⟩ : syracuseStep 1594981 = 299059) (by norm_num)
theorem B4249205 : Blo 1258447 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B1889909 : Blo 1258447 1889909 := bbase (se 5 (by rfl) ⟨88589, by rfl⟩ : syracuseStep 1889909 = 177179) (by norm_num)
theorem B1513093 : Blo 1258447 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B1889933 : Blo 1258447 1889933 := bbase (se 3 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 1889933 = 708725) (by norm_num)
theorem B2832029 : Blo 1258447 2832029 := bbase (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) (by norm_num)
theorem B3585701 : Blo 1258447 3585701 := bbase (se 4 (by rfl) ⟨336159, by rfl⟩ : syracuseStep 3585701 = 672319) (by norm_num)
theorem B1889957 : Blo 1258447 1889957 := bbase (se 4 (by rfl) ⟨177183, by rfl⟩ : syracuseStep 1889957 = 354367) (by norm_num)
theorem B1889981 : Blo 1258447 1889981 := bbase (se 3 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 1889981 = 708743) (by norm_num)
theorem B1513165 : Blo 1258447 1513165 := bbase (se 3 (by rfl) ⟨283718, by rfl⟩ : syracuseStep 1513165 = 567437) (by norm_num)
theorem B1890005 : Blo 1258447 1890005 := bbase (se 7 (by rfl) ⟨22148, by rfl⟩ : syracuseStep 1890005 = 44297) (by norm_num)
theorem B2832101 : Blo 1258447 2832101 := bbase (se 4 (by rfl) ⟨265509, by rfl⟩ : syracuseStep 2832101 = 531019) (by norm_num)
theorem B1513189 : Blo 1258447 1513189 := bbase (se 4 (by rfl) ⟨141861, by rfl⟩ : syracuseStep 1513189 = 283723) (by norm_num)
theorem B1890029 : Blo 1258447 1890029 := bbase (se 3 (by rfl) ⟨354380, by rfl⟩ : syracuseStep 1890029 = 708761) (by norm_num)
theorem B1890053 : Blo 1258447 1890053 := bbase (se 4 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 1890053 = 354385) (by norm_num)
theorem B1595153 : Blo 1258447 1595153 := bbase (se 2 (by rfl) ⟨598182, by rfl⟩ : syracuseStep 1595153 = 1196365) (by norm_num)
theorem B1890077 : Blo 1258447 1890077 := bbase (se 3 (by rfl) ⟨354389, by rfl⟩ : syracuseStep 1890077 = 708779) (by norm_num)
theorem B4781861 : Blo 1258447 4781861 := bbase (se 4 (by rfl) ⟨448299, by rfl⟩ : syracuseStep 4781861 = 896599) (by norm_num)
theorem B2832173 : Blo 1258447 2832173 := bbase (se 3 (by rfl) ⟨531032, by rfl⟩ : syracuseStep 2832173 = 1062065) (by norm_num)
theorem B1890101 : Blo 1258447 1890101 := bbase (se 5 (by rfl) ⟨88598, by rfl⟩ : syracuseStep 1890101 = 177197) (by norm_num)
theorem B1595209 : Blo 1258447 1595209 := bbase (se 2 (by rfl) ⟨598203, by rfl⟩ : syracuseStep 1595209 = 1196407) (by norm_num)
theorem B2389837 : Blo 1258447 2389837 := bbase (se 3 (by rfl) ⟨448094, by rfl⟩ : syracuseStep 2389837 = 896189) (by norm_num)
theorem B1890125 : Blo 1258447 1890125 := bbase (se 3 (by rfl) ⟨354398, by rfl⟩ : syracuseStep 1890125 = 708797) (by norm_num)
theorem B1890149 : Blo 1258447 1890149 := bbase (se 4 (by rfl) ⟨177201, by rfl⟩ : syracuseStep 1890149 = 354403) (by norm_num)
theorem B2832245 : Blo 1258447 2832245 := bbase (se 5 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 2832245 = 265523) (by norm_num)
theorem B1513333 : Blo 1258447 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B1890173 : Blo 1258447 1890173 := bbase (se 3 (by rfl) ⟨354407, by rfl⟩ : syracuseStep 1890173 = 708815) (by norm_num)
theorem B1791877 : Blo 1258447 1791877 := bbase (se 4 (by rfl) ⟨167988, by rfl⟩ : syracuseStep 1791877 = 335977) (by norm_num)
theorem B6379397 : Blo 1258447 6379397 := bbase (se 4 (by rfl) ⟨598068, by rfl⟩ : syracuseStep 6379397 = 1196137) (by norm_num)
theorem B3585941 : Blo 1258447 3585941 := bbase (se 6 (by rfl) ⟨84045, by rfl⟩ : syracuseStep 3585941 = 168091) (by norm_num)
theorem B1890197 : Blo 1258447 1890197 := bbase (se 6 (by rfl) ⟨44301, by rfl⟩ : syracuseStep 1890197 = 88603) (by norm_num)
theorem B1456037 : Blo 1258447 1456037 := bbase (se 4 (by rfl) ⟨136503, by rfl⟩ : syracuseStep 1456037 = 273007) (by norm_num)
theorem B1890221 : Blo 1258447 1890221 := bbase (se 3 (by rfl) ⟨354416, by rfl⟩ : syracuseStep 1890221 = 708833) (by norm_num)
theorem B2832317 : Blo 1258447 2832317 := bbase (se 3 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 2832317 = 1062119) (by norm_num)
theorem B1890245 : Blo 1258447 1890245 := bbase (se 4 (by rfl) ⟨177210, by rfl⟩ : syracuseStep 1890245 = 354421) (by norm_num)
theorem B2389981 : Blo 1258447 2389981 := bbase (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) (by norm_num)
theorem B1890269 : Blo 1258447 1890269 := bbase (se 3 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 1890269 = 708851) (by norm_num)
theorem B1791973 : Blo 1258447 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B1890293 : Blo 1258447 1890293 := bbase (se 5 (by rfl) ⟨88607, by rfl⟩ : syracuseStep 1890293 = 177215) (by norm_num)
theorem B2832389 : Blo 1258447 2832389 := bbase (se 4 (by rfl) ⟨265536, by rfl⟩ : syracuseStep 2832389 = 531073) (by norm_num)
theorem B1890317 : Blo 1258447 1890317 := bbase (se 3 (by rfl) ⟨354434, by rfl⟩ : syracuseStep 1890317 = 708869) (by norm_num)
theorem B4249637 : Blo 1258447 4249637 := bbase (se 4 (by rfl) ⟨398403, by rfl⟩ : syracuseStep 4249637 = 796807) (by norm_num)
theorem B1890341 : Blo 1258447 1890341 := bbase (se 4 (by rfl) ⟨177219, by rfl⟩ : syracuseStep 1890341 = 354439) (by norm_num)
theorem B1890365 : Blo 1258447 1890365 := bbase (se 3 (by rfl) ⟨354443, by rfl⟩ : syracuseStep 1890365 = 708887) (by norm_num)
theorem B4782149 : Blo 1258447 4782149 := bbase (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) (by norm_num)
theorem B2832461 : Blo 1258447 2832461 := bbase (se 3 (by rfl) ⟨531086, by rfl⟩ : syracuseStep 2832461 = 1062173) (by norm_num)
theorem B3586133 : Blo 1258447 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B1890389 : Blo 1258447 1890389 := bbase (se 8 (by rfl) ⟨11076, by rfl⟩ : syracuseStep 1890389 = 22153) (by norm_num)
theorem B5740645 : Blo 1258447 5740645 := bbase (se 4 (by rfl) ⟨538185, by rfl⟩ : syracuseStep 5740645 = 1076371) (by norm_num)
theorem B1890413 : Blo 1258447 1890413 := bbase (se 3 (by rfl) ⟨354452, by rfl⟩ : syracuseStep 1890413 = 708905) (by norm_num)
theorem B2390141 : Blo 1258447 2390141 := bbase (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) (by norm_num)
theorem B1890437 : Blo 1258447 1890437 := bbase (se 4 (by rfl) ⟨177228, by rfl⟩ : syracuseStep 1890437 = 354457) (by norm_num)
theorem B2832533 : Blo 1258447 2832533 := bbase (se 6 (by rfl) ⟨66387, by rfl⟩ : syracuseStep 2832533 = 132775) (by norm_num)
theorem B1890461 : Blo 1258447 1890461 := bbase (se 3 (by rfl) ⟨354461, by rfl⟩ : syracuseStep 1890461 = 708923) (by norm_num)
theorem B1890485 : Blo 1258447 1890485 := bbase (se 5 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 1890485 = 177233) (by norm_num)
theorem B1890509 : Blo 1258447 1890509 := bbase (se 3 (by rfl) ⟨354470, by rfl⟩ : syracuseStep 1890509 = 708941) (by norm_num)
theorem B2832605 : Blo 1258447 2832605 := bbase (se 3 (by rfl) ⟨531113, by rfl⟩ : syracuseStep 2832605 = 1062227) (by norm_num)
theorem B1890533 : Blo 1258447 1890533 := bbase (se 4 (by rfl) ⟨177237, by rfl⟩ : syracuseStep 1890533 = 354475) (by norm_num)
theorem B1890557 : Blo 1258447 1890557 := bbase (se 3 (by rfl) ⟨354479, by rfl⟩ : syracuseStep 1890557 = 708959) (by norm_num)
theorem B2390285 : Blo 1258447 2390285 := bbase (se 3 (by rfl) ⟨448178, by rfl⟩ : syracuseStep 2390285 = 896357) (by norm_num)
theorem B1890581 : Blo 1258447 1890581 := bbase (se 6 (by rfl) ⟨44310, by rfl⟩ : syracuseStep 1890581 = 88621) (by norm_num)
theorem B6371621 : Blo 1258447 6371621 := bbase (se 4 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 6371621 = 1194679) (by norm_num)
theorem B2832677 : Blo 1258447 2832677 := bbase (se 4 (by rfl) ⟨265563, by rfl⟩ : syracuseStep 2832677 = 531127) (by norm_num)
theorem B1890605 : Blo 1258447 1890605 := bbase (se 3 (by rfl) ⟨354488, by rfl⟩ : syracuseStep 1890605 = 708977) (by norm_num)
theorem B7174453 : Blo 1258447 7174453 := bbase (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) (by norm_num)
theorem B1890629 : Blo 1258447 1890629 := bbase (se 4 (by rfl) ⟨177246, by rfl⟩ : syracuseStep 1890629 = 354493) (by norm_num)
theorem B1890653 : Blo 1258447 1890653 := bbase (se 3 (by rfl) ⟨354497, by rfl⟩ : syracuseStep 1890653 = 708995) (by norm_num)
theorem B2832749 : Blo 1258447 2832749 := bbase (se 3 (by rfl) ⟨531140, by rfl⟩ : syracuseStep 2832749 = 1062281) (by norm_num)
theorem B9083285 : Blo 1258447 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B2832821 : Blo 1258447 2832821 := bbase (se 5 (by rfl) ⟨132788, by rfl⟩ : syracuseStep 2832821 = 265577) (by norm_num)
theorem B1792469 : Blo 1258447 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B4250069 : Blo 1258447 4250069 := bbase (se 7 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 4250069 = 99611) (by norm_num)
theorem B2832893 : Blo 1258447 2832893 := bbase (se 3 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 2832893 = 1062335) (by norm_num)
theorem B2390573 : Blo 1258447 2390573 := bbase (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) (by norm_num)
theorem B2832965 : Blo 1258447 2832965 := bbase (se 4 (by rfl) ⟨265590, by rfl⟩ : syracuseStep 2832965 = 531181) (by norm_num)
theorem B1415785 : Blo 1258447 1415785 := bbase (se 2 (by rfl) ⟨530919, by rfl⟩ : syracuseStep 1415785 = 1061839) (by norm_num)
theorem B1415821 : Blo 1258447 1415821 := bbase (se 3 (by rfl) ⟨265466, by rfl⟩ : syracuseStep 1415821 = 530933) (by norm_num)
theorem B2833037 : Blo 1258447 2833037 := bbase (se 3 (by rfl) ⟨531194, by rfl⟩ : syracuseStep 2833037 = 1062389) (by norm_num)
theorem B1415857 : Blo 1258447 1415857 := bbase (se 2 (by rfl) ⟨530946, by rfl⟩ : syracuseStep 1415857 = 1061893) (by norm_num)
theorem B2390725 : Blo 1258447 2390725 := bbase (se 4 (by rfl) ⟨224130, by rfl⟩ : syracuseStep 2390725 = 448261) (by norm_num)
theorem B5454533 : Blo 1258447 5454533 := bbase (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) (by norm_num)
theorem B1415893 : Blo 1258447 1415893 := bbase (se 7 (by rfl) ⟨16592, by rfl⟩ : syracuseStep 1415893 = 33185) (by norm_num)
theorem B2833109 : Blo 1258447 2833109 := bbase (se 7 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 2833109 = 66401) (by norm_num)
theorem B1415929 : Blo 1258447 1415929 := bbase (se 2 (by rfl) ⟨530973, by rfl⟩ : syracuseStep 1415929 = 1061947) (by norm_num)
theorem B1415965 : Blo 1258447 1415965 := bbase (se 3 (by rfl) ⟨265493, by rfl⟩ : syracuseStep 1415965 = 530987) (by norm_num)
theorem B2833181 : Blo 1258447 2833181 := bbase (se 3 (by rfl) ⟨531221, by rfl⟩ : syracuseStep 2833181 = 1062443) (by norm_num)
theorem B1416001 : Blo 1258447 1416001 := bbase (se 2 (by rfl) ⟨531000, by rfl⟩ : syracuseStep 1416001 = 1062001) (by norm_num)
theorem B3185477 : Blo 1258447 3185477 := bbase (se 4 (by rfl) ⟨298638, by rfl⟩ : syracuseStep 3185477 = 597277) (by norm_num)
theorem B1416037 : Blo 1258447 1416037 := bbase (se 4 (by rfl) ⟨132753, by rfl⟩ : syracuseStep 1416037 = 265507) (by norm_num)
theorem B2833253 : Blo 1258447 2833253 := bbase (se 4 (by rfl) ⟨265617, by rfl⟩ : syracuseStep 2833253 = 531235) (by norm_num)
theorem B4250501 : Blo 1258447 4250501 := bbase (se 4 (by rfl) ⟨398484, by rfl⟩ : syracuseStep 4250501 = 796969) (by norm_num)
theorem B1416073 : Blo 1258447 1416073 := bbase (se 2 (by rfl) ⟨531027, by rfl⟩ : syracuseStep 1416073 = 1062055) (by norm_num)
theorem B1416109 : Blo 1258447 1416109 := bbase (se 3 (by rfl) ⟨265520, by rfl⟩ : syracuseStep 1416109 = 531041) (by norm_num)
theorem B2833325 : Blo 1258447 2833325 := bbase (se 3 (by rfl) ⟨531248, by rfl⟩ : syracuseStep 2833325 = 1062497) (by norm_num)
theorem B1416145 : Blo 1258447 1416145 := bbase (se 2 (by rfl) ⟨531054, by rfl⟩ : syracuseStep 1416145 = 1062109) (by norm_num)
theorem B2153453 : Blo 1258447 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B1416181 : Blo 1258447 1416181 := bbase (se 5 (by rfl) ⟨66383, by rfl⟩ : syracuseStep 1416181 = 132767) (by norm_num)
theorem B8068085 : Blo 1258447 8068085 := bbase (se 5 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 8068085 = 756383) (by norm_num)
theorem B2833397 : Blo 1258447 2833397 := bbase (se 5 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 2833397 = 265631) (by norm_num)
theorem B2391029 : Blo 1258447 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B1793021 : Blo 1258447 1793021 := bbase (se 3 (by rfl) ⟨336191, by rfl⟩ : syracuseStep 1793021 = 672383) (by norm_num)
theorem B3185669 : Blo 1258447 3185669 := bbase (se 4 (by rfl) ⟨298656, by rfl⟩ : syracuseStep 3185669 = 597313) (by norm_num)
theorem B1416217 : Blo 1258447 1416217 := bbase (se 2 (by rfl) ⟨531081, by rfl⟩ : syracuseStep 1416217 = 1062163) (by norm_num)
theorem B3587125 : Blo 1258447 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B1416253 : Blo 1258447 1416253 := bbase (se 3 (by rfl) ⟨265547, by rfl⟩ : syracuseStep 1416253 = 531095) (by norm_num)
theorem B2833469 : Blo 1258447 2833469 := bbase (se 3 (by rfl) ⟨531275, by rfl⟩ : syracuseStep 2833469 = 1062551) (by norm_num)
theorem B1276993 : Blo 1258447 1276993 := bbase (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) (by norm_num)
theorem B1416289 : Blo 1258447 1416289 := bbase (se 2 (by rfl) ⟨531108, by rfl⟩ : syracuseStep 1416289 = 1062217) (by norm_num)
theorem B1277029 : Blo 1258447 1277029 := bbase (se 4 (by rfl) ⟨119721, by rfl⟩ : syracuseStep 1277029 = 239443) (by norm_num)
theorem B1416325 : Blo 1258447 1416325 := bbase (se 4 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 1416325 = 265561) (by norm_num)
theorem B2833541 : Blo 1258447 2833541 := bbase (se 4 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 2833541 = 531289) (by norm_num)
theorem B6380693 : Blo 1258447 6380693 := bbase (se 6 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 6380693 = 299095) (by norm_num)
theorem B1416361 : Blo 1258447 1416361 := bbase (se 2 (by rfl) ⟨531135, by rfl⟩ : syracuseStep 1416361 = 1062271) (by norm_num)
theorem B1416397 : Blo 1258447 1416397 := bbase (se 3 (by rfl) ⟨265574, by rfl⟩ : syracuseStep 1416397 = 531149) (by norm_num)
theorem B2833613 : Blo 1258447 2833613 := bbase (se 3 (by rfl) ⟨531302, by rfl⟩ : syracuseStep 2833613 = 1062605) (by norm_num)
theorem B4783333 : Blo 1258447 4783333 := bbase (se 4 (by rfl) ⟨448437, by rfl⟩ : syracuseStep 4783333 = 896875) (by norm_num)
theorem B1416433 : Blo 1258447 1416433 := bbase (se 2 (by rfl) ⟨531162, by rfl⟩ : syracuseStep 1416433 = 1062325) (by norm_num)
theorem B1416469 : Blo 1258447 1416469 := bbase (se 6 (by rfl) ⟨33198, by rfl⟩ : syracuseStep 1416469 = 66397) (by norm_num)
theorem B2833685 : Blo 1258447 2833685 := bbase (se 6 (by rfl) ⟨66414, by rfl⟩ : syracuseStep 2833685 = 132829) (by norm_num)
theorem B4250933 : Blo 1258447 4250933 := bbase (se 5 (by rfl) ⟨199262, by rfl⟩ : syracuseStep 4250933 = 398525) (by norm_num)
theorem B1416505 : Blo 1258447 1416505 := bbase (se 2 (by rfl) ⟨531189, by rfl⟩ : syracuseStep 1416505 = 1062379) (by norm_num)
theorem B3186013 : Blo 1258447 3186013 := bbase (se 3 (by rfl) ⟨597377, by rfl⟩ : syracuseStep 3186013 = 1194755) (by norm_num)
theorem B1416541 : Blo 1258447 1416541 := bbase (se 3 (by rfl) ⟨265601, by rfl⟩ : syracuseStep 1416541 = 531203) (by norm_num)
theorem B2833757 : Blo 1258447 2833757 := bbase (se 3 (by rfl) ⟨531329, by rfl⟩ : syracuseStep 2833757 = 1062659) (by norm_num)
theorem B1416577 : Blo 1258447 1416577 := bbase (se 2 (by rfl) ⟨531216, by rfl⟩ : syracuseStep 1416577 = 1062433) (by norm_num)
theorem B1416613 : Blo 1258447 1416613 := bbase (se 4 (by rfl) ⟨132807, by rfl⟩ : syracuseStep 1416613 = 265615) (by norm_num)
theorem B2833829 : Blo 1258447 2833829 := bbase (se 4 (by rfl) ⟨265671, by rfl⟩ : syracuseStep 2833829 = 531343) (by norm_num)
theorem B1277353 : Blo 1258447 1277353 := bbase (se 2 (by rfl) ⟨479007, by rfl⟩ : syracuseStep 1277353 = 958015) (by norm_num)
theorem B1416649 : Blo 1258447 1416649 := bbase (se 2 (by rfl) ⟨531243, by rfl⟩ : syracuseStep 1416649 = 1062487) (by norm_num)
theorem B3186125 : Blo 1258447 3186125 := bbase (se 3 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 3186125 = 1194797) (by norm_num)
theorem B1416685 : Blo 1258447 1416685 := bbase (se 3 (by rfl) ⟨265628, by rfl⟩ : syracuseStep 1416685 = 531257) (by norm_num)
theorem B2833901 : Blo 1258447 2833901 := bbase (se 3 (by rfl) ⟨531356, by rfl⟩ : syracuseStep 2833901 = 1062713) (by norm_num)
theorem B1416721 : Blo 1258447 1416721 := bbase (se 2 (by rfl) ⟨531270, by rfl⟩ : syracuseStep 1416721 = 1062541) (by norm_num)
theorem B4783637 : Blo 1258447 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B6372917 : Blo 1258447 6372917 := bbase (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) (by norm_num)
theorem B1416757 : Blo 1258447 1416757 := bbase (se 5 (by rfl) ⟨66410, by rfl⟩ : syracuseStep 1416757 = 132821) (by norm_num)
theorem B2833973 : Blo 1258447 2833973 := bbase (se 5 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 2833973 = 265685) (by norm_num)
theorem B1818173 : Blo 1258447 1818173 := bbase (se 3 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 1818173 = 681815) (by norm_num)
theorem B1416793 : Blo 1258447 1416793 := bbase (se 2 (by rfl) ⟨531297, by rfl⟩ : syracuseStep 1416793 = 1062595) (by norm_num)
theorem B1416829 : Blo 1258447 1416829 := bbase (se 3 (by rfl) ⟨265655, by rfl⟩ : syracuseStep 1416829 = 531311) (by norm_num)
theorem B2834045 : Blo 1258447 2834045 := bbase (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) (by norm_num)
theorem B3186317 : Blo 1258447 3186317 := bbase (se 3 (by rfl) ⟨597434, by rfl⟩ : syracuseStep 3186317 = 1194869) (by norm_num)
theorem B6053525 : Blo 1258447 6053525 := bbase (se 6 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 6053525 = 283759) (by norm_num)
theorem B1416865 : Blo 1258447 1416865 := bbase (se 2 (by rfl) ⟨531324, by rfl⟩ : syracuseStep 1416865 = 1062649) (by norm_num)
theorem B5381797 : Blo 1258447 5381797 := bbase (se 4 (by rfl) ⟨504543, by rfl⟩ : syracuseStep 5381797 = 1009087) (by norm_num)
theorem B5529269 : Blo 1258447 5529269 := bbase (se 5 (by rfl) ⟨259184, by rfl⟩ : syracuseStep 5529269 = 518369) (by norm_num)
theorem B1416901 : Blo 1258447 1416901 := bbase (se 4 (by rfl) ⟨132834, by rfl⟩ : syracuseStep 1416901 = 265669) (by norm_num)
theorem B2834117 : Blo 1258447 2834117 := bbase (se 4 (by rfl) ⟨265698, by rfl⟩ : syracuseStep 2834117 = 531397) (by norm_num)
theorem B3546821 : Blo 1258447 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B4251365 : Blo 1258447 4251365 := bbase (se 4 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 4251365 = 797131) (by norm_num)
theorem B2391781 : Blo 1258447 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B1416937 : Blo 1258447 1416937 := bbase (se 2 (by rfl) ⟨531351, by rfl⟩ : syracuseStep 1416937 = 1062703) (by norm_num)
theorem B1793773 : Blo 1258447 1793773 := bbase (se 3 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 1793773 = 672665) (by norm_num)
theorem B4849397 : Blo 1258447 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B1416973 : Blo 1258447 1416973 := bbase (se 3 (by rfl) ⟨265682, by rfl⟩ : syracuseStep 1416973 = 531365) (by norm_num)
theorem B2834189 : Blo 1258447 2834189 := bbase (se 3 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 2834189 = 1062821) (by norm_num)
theorem B1417009 : Blo 1258447 1417009 := bbase (se 2 (by rfl) ⟨531378, by rfl⟩ : syracuseStep 1417009 = 1062757) (by norm_num)
theorem B5103445 : Blo 1258447 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B1417045 : Blo 1258447 1417045 := bbase (se 9 (by rfl) ⟨4151, by rfl⟩ : syracuseStep 1417045 = 8303) (by norm_num)
theorem B2834261 : Blo 1258447 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B2391925 : Blo 1258447 2391925 := bbase (se 5 (by rfl) ⟨112121, by rfl⟩ : syracuseStep 2391925 = 224243) (by norm_num)
theorem B1417081 : Blo 1258447 1417081 := bbase (se 2 (by rfl) ⟨531405, by rfl⟩ : syracuseStep 1417081 = 1062811) (by norm_num)
theorem B4308869 : Blo 1258447 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B1417117 : Blo 1258447 1417117 := bbase (se 3 (by rfl) ⟨265709, by rfl⟩ : syracuseStep 1417117 = 531419) (by norm_num)
theorem B2834333 : Blo 1258447 2834333 := bbase (se 3 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 2834333 = 1062875) (by norm_num)
theorem B1417153 : Blo 1258447 1417153 := bbase (se 2 (by rfl) ⟨531432, by rfl⟩ : syracuseStep 1417153 = 1062865) (by norm_num)
theorem B3186661 : Blo 1258447 3186661 := bbase (se 4 (by rfl) ⟨298749, by rfl⟩ : syracuseStep 3186661 = 597499) (by norm_num)
theorem B1417189 : Blo 1258447 1417189 := bbase (se 4 (by rfl) ⟨132861, by rfl⟩ : syracuseStep 1417189 = 265723) (by norm_num)
theorem B2834405 : Blo 1258447 2834405 := bbase (se 4 (by rfl) ⟨265725, by rfl⟩ : syracuseStep 2834405 = 531451) (by norm_num)
theorem B4087811 : Blo 1258447 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B2834513 : Blo 1258447 2834513 := bstep (se 2 (by rfl) ⟨1062942, by rfl⟩ : syracuseStep 2834513 = 2125885) B2125885
theorem B1400915 : Blo 1258447 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B2834531 : Blo 1258447 2834531 := bstep (se 1 (by rfl) ⟨2125898, by rfl⟩ : syracuseStep 2834531 = 4251797) B4251797
theorem B1417315 : Blo 1258447 1417315 := bstep (se 1 (by rfl) ⟨1062986, by rfl⟩ : syracuseStep 1417315 = 2125973) B2125973
theorem B4784291 : Blo 1258447 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B4784305 : Blo 1258447 4784305 := bstep (se 2 (by rfl) ⟨1794114, by rfl⟩ : syracuseStep 4784305 = 3588229) B3588229
theorem B1417459 : Blo 1258447 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B5382413 : Blo 1258447 5382413 := bstep (se 3 (by rfl) ⟨1009202, by rfl⟩ : syracuseStep 5382413 = 2018405) B2018405
theorem B3588401 : Blo 1258447 3588401 := bstep (se 2 (by rfl) ⟨1345650, by rfl⟩ : syracuseStep 3588401 = 2691301) B2691301
theorem B4252013 : Blo 1258447 4252013 := bstep (se 3 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 4252013 = 1594505) B1594505
theorem B2834801 : Blo 1258447 2834801 := bstep (se 2 (by rfl) ⟨1063050, by rfl⟩ : syracuseStep 2834801 = 2126101) B2126101
theorem B2834819 : Blo 1258447 2834819 := bstep (se 1 (by rfl) ⟨2126114, by rfl⟩ : syracuseStep 2834819 = 4252229) B4252229
theorem B1417603 : Blo 1258447 1417603 := bstep (se 1 (by rfl) ⟨1063202, by rfl⟩ : syracuseStep 1417603 = 2126405) B2126405
theorem B4252067 : Blo 1258447 4252067 := bstep (se 1 (by rfl) ⟨3189050, by rfl⟩ : syracuseStep 4252067 = 6378101) B6378101
theorem B1417747 : Blo 1258447 1417747 := bstep (se 1 (by rfl) ⟨1063310, by rfl⟩ : syracuseStep 1417747 = 2126621) B2126621
theorem B1794593 : Blo 1258447 1794593 := bstep (se 2 (by rfl) ⟨672972, by rfl⟩ : syracuseStep 1794593 = 1345945) B1345945
theorem B7864931 : Blo 1258447 7864931 := bstep (se 1 (by rfl) ⟨5898698, by rfl⟩ : syracuseStep 7864931 = 11797397) B11797397
theorem B13615715 : Blo 1258447 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B2835089 : Blo 1258447 2835089 := bstep (se 2 (by rfl) ⟨1063158, by rfl⟩ : syracuseStep 2835089 = 2126317) B2126317
theorem B6374051 : Blo 1258447 6374051 := bstep (se 1 (by rfl) ⟨4780538, by rfl⟩ : syracuseStep 6374051 = 9561077) B9561077
theorem B2835107 : Blo 1258447 2835107 := bstep (se 1 (by rfl) ⟨2126330, by rfl⟩ : syracuseStep 2835107 = 4252661) B4252661
theorem B1417891 : Blo 1258447 1417891 := bstep (se 1 (by rfl) ⟨1063418, by rfl⟩ : syracuseStep 1417891 = 2126837) B2126837
theorem B4252337 : Blo 1258447 4252337 := bstep (se 2 (by rfl) ⟨1594626, by rfl⟩ : syracuseStep 4252337 = 3189253) B3189253
theorem B2392753 : Blo 1258447 2392753 := bstep (se 2 (by rfl) ⟨897282, by rfl⟩ : syracuseStep 2392753 = 1794565) B1794565
theorem B4309699 : Blo 1258447 4309699 := bstep (se 1 (by rfl) ⟨3232274, by rfl⟩ : syracuseStep 4309699 = 6464549) B6464549
theorem B27984611 : Blo 1258447 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B3187633 : Blo 1258447 3187633 := bstep (se 2 (by rfl) ⟨1195362, by rfl⟩ : syracuseStep 3187633 = 2390725) B2390725
theorem B2835377 : Blo 1258447 2835377 := bstep (se 2 (by rfl) ⟨1063266, by rfl⟩ : syracuseStep 2835377 = 2126533) B2126533
theorem B2835395 : Blo 1258447 2835395 := bstep (se 1 (by rfl) ⟨2126546, by rfl⟩ : syracuseStep 2835395 = 4253093) B4253093
theorem B3589073 : Blo 1258447 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B2016227 : Blo 1258447 2016227 := bstep (se 1 (by rfl) ⟨1512170, by rfl⟩ : syracuseStep 2016227 = 3024341) B3024341
theorem B7177187 : Blo 1258447 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B2016355 : Blo 1258447 2016355 := bstep (se 1 (by rfl) ⟨1512266, by rfl⟩ : syracuseStep 2016355 = 3024533) B3024533
theorem B98174065 : Blo 1258447 98174065 := bstep (se 2 (by rfl) ⟨36815274, by rfl⟩ : syracuseStep 98174065 = 73630549) B73630549
theorem B4031633 : Blo 1258447 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B3187907 : Blo 1258447 3187907 := bstep (se 1 (by rfl) ⟨2390930, by rfl⟩ : syracuseStep 3187907 = 4781861) B4781861
theorem B4252877 : Blo 1258447 4252877 := bstep (se 3 (by rfl) ⟨797414, by rfl⟩ : syracuseStep 4252877 = 1594829) B1594829
theorem B2835665 : Blo 1258447 2835665 := bstep (se 2 (by rfl) ⟨1063374, by rfl⟩ : syracuseStep 2835665 = 2126749) B2126749
theorem B5178595 : Blo 1258447 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B2835683 : Blo 1258447 2835683 := bstep (se 1 (by rfl) ⟨2126762, by rfl⟩ : syracuseStep 2835683 = 4253525) B4253525
theorem B4252931 : Blo 1258447 4252931 := bstep (se 1 (by rfl) ⟨3189698, by rfl⟩ : syracuseStep 4252931 = 6379397) B6379397
theorem B33596693 : Blo 1258447 33596693 := bstep (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) B1574845
theorem B3188099 : Blo 1258447 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B6374861 : Blo 1258447 6374861 := bstep (se 3 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 6374861 = 2390573) B2390573
theorem B2016739 : Blo 1258447 2016739 := bstep (se 1 (by rfl) ⟨1512554, by rfl⟩ : syracuseStep 2016739 = 3025109) B3025109
theorem B2835953 : Blo 1258447 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B2835971 : Blo 1258447 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B4253201 : Blo 1258447 4253201 := bstep (se 2 (by rfl) ⟨1594950, by rfl⟩ : syracuseStep 4253201 = 3189901) B3189901
theorem B6055523 : Blo 1258447 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B4785763 : Blo 1258447 4785763 := bstep (se 1 (by rfl) ⟨3589322, by rfl⟩ : syracuseStep 4785763 = 7178645) B7178645
theorem B2688643 : Blo 1258447 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B3827341 : Blo 1258447 3827341 := bstep (se 3 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 3827341 = 1435253) B1435253
theorem B2016995 : Blo 1258447 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B6055793 : Blo 1258447 6055793 := bstep (se 2 (by rfl) ⟨2270922, by rfl⟩ : syracuseStep 6055793 = 4541845) B4541845
theorem B2123651 : Blo 1258447 2123651 := bstep (se 1 (by rfl) ⟨1592738, by rfl⟩ : syracuseStep 2123651 = 3185477) B3185477
theorem B8071109 : Blo 1258447 8071109 := bstep (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) B1513333
theorem B2688977 : Blo 1258447 2688977 := bstep (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) B2016733
theorem B2123779 : Blo 1258447 2123779 := bstep (se 1 (by rfl) ⟨1592834, by rfl⟩ : syracuseStep 2123779 = 3185669) B3185669
theorem B4253741 : Blo 1258447 4253741 := bstep (se 3 (by rfl) ⟨797576, by rfl⟩ : syracuseStep 4253741 = 1595153) B1595153
theorem B6055985 : Blo 1258447 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B4253795 : Blo 1258447 4253795 := bstep (se 1 (by rfl) ⟨3190346, by rfl⟩ : syracuseStep 4253795 = 6380693) B6380693
theorem B2123921 : Blo 1258447 2123921 := bstep (se 2 (by rfl) ⟨796470, by rfl⟩ : syracuseStep 2123921 = 1592941) B1592941
theorem B2017457 : Blo 1258447 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B5449997 : Blo 1258447 5449997 := bstep (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) B2043749
theorem B2124049 : Blo 1258447 2124049 := bstep (se 2 (by rfl) ⟨796518, by rfl⟩ : syracuseStep 2124049 = 1593037) B1593037
theorem B2017553 : Blo 1258447 2017553 := bstep (se 2 (by rfl) ⟨756582, by rfl⟩ : syracuseStep 2017553 = 1513165) B1513165
theorem B7170353 : Blo 1258447 7170353 := bstep (se 2 (by rfl) ⟨2688882, by rfl⟩ : syracuseStep 7170353 = 5377765) B5377765
theorem B2017585 : Blo 1258447 2017585 := bstep (se 2 (by rfl) ⟨756594, by rfl⟩ : syracuseStep 2017585 = 1513189) B1513189
theorem B2124083 : Blo 1258447 2124083 := bstep (se 1 (by rfl) ⟨1593062, by rfl⟩ : syracuseStep 2124083 = 3186125) B3186125
theorem B3189041 : Blo 1258447 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B3189091 : Blo 1258447 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B6056369 : Blo 1258447 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B2124211 : Blo 1258447 2124211 := bstep (se 1 (by rfl) ⟨1593158, by rfl⟩ : syracuseStep 2124211 = 3186317) B3186317
theorem B3189233 : Blo 1258447 3189233 := bstep (se 2 (by rfl) ⟨1195962, by rfl⟩ : syracuseStep 3189233 = 2391925) B2391925
theorem B2124353 : Blo 1258447 2124353 := bstep (se 2 (by rfl) ⟨796632, by rfl⟩ : syracuseStep 2124353 = 1593265) B1593265
theorem B8063651 : Blo 1258447 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B2124481 : Blo 1258447 2124481 := bstep (se 2 (by rfl) ⟨796680, by rfl⟩ : syracuseStep 2124481 = 1593361) B1593361
theorem B2124515 : Blo 1258447 2124515 := bstep (se 1 (by rfl) ⟨1593386, by rfl⟩ : syracuseStep 2124515 = 3186773) B3186773
theorem B7654193 : Blo 1258447 7654193 := bstep (se 2 (by rfl) ⟨2870322, by rfl⟩ : syracuseStep 7654193 = 5740645) B5740645
theorem B3402545 : Blo 1258447 3402545 := bstep (se 2 (by rfl) ⟨1275954, by rfl⟩ : syracuseStep 3402545 = 2551909) B2551909
theorem B2124643 : Blo 1258447 2124643 := bstep (se 1 (by rfl) ⟨1593482, by rfl⟩ : syracuseStep 2124643 = 3186965) B3186965
theorem B21506957 : Blo 1258447 21506957 := bstep (se 3 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 21506957 = 8065109) B8065109
theorem B9563021 : Blo 1258447 9563021 := bstep (se 3 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 9563021 = 3586133) B3586133
theorem B6466481 : Blo 1258447 6466481 := bstep (se 2 (by rfl) ⟨2424930, by rfl⟩ : syracuseStep 6466481 = 4849861) B4849861
theorem B1616851 : Blo 1258447 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B2124785 : Blo 1258447 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2690147 : Blo 1258447 2690147 := bstep (se 1 (by rfl) ⟨2017610, by rfl⟩ : syracuseStep 2690147 = 4035221) B4035221
theorem B2124913 : Blo 1258447 2124913 := bstep (se 2 (by rfl) ⟨796842, by rfl⟩ : syracuseStep 2124913 = 1593685) B1593685
theorem B1436803 : Blo 1258447 1436803 := bstep (se 1 (by rfl) ⟨1077602, by rfl⟩ : syracuseStep 1436803 = 2155205) B2155205
theorem B2124947 : Blo 1258447 2124947 := bstep (se 1 (by rfl) ⟨1593710, by rfl⟩ : syracuseStep 2124947 = 3187421) B3187421
theorem B4033709 : Blo 1258447 4033709 := bstep (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) B1512641
theorem B2125075 : Blo 1258447 2125075 := bstep (se 1 (by rfl) ⟨1593806, by rfl⟩ : syracuseStep 2125075 = 3187613) B3187613
theorem B3403075 : Blo 1258447 3403075 := bstep (se 1 (by rfl) ⟨2552306, by rfl⟩ : syracuseStep 3403075 = 5104613) B5104613
theorem B10759493 : Blo 1258447 10759493 := bstep (se 4 (by rfl) ⟨1008702, by rfl⟩ : syracuseStep 10759493 = 2017405) B2017405
theorem B16149901 : Blo 1258447 16149901 := bstep (se 3 (by rfl) ⟨3028106, by rfl⟩ : syracuseStep 16149901 = 6056213) B6056213
theorem B1592723 : Blo 1258447 1592723 := bstep (se 1 (by rfl) ⟨1194542, by rfl⟩ : syracuseStep 1592723 = 2389085) B2389085
theorem B2125217 : Blo 1258447 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B3026339 : Blo 1258447 3026339 := bstep (se 1 (by rfl) ⟨2269754, by rfl⟩ : syracuseStep 3026339 = 4539509) B4539509
theorem B1887683 : Blo 1258447 1887683 := bstep (se 1 (by rfl) ⟨1415762, by rfl⟩ : syracuseStep 1887683 = 2831525) B2831525
theorem B18148805 : Blo 1258447 18148805 := bstep (se 4 (by rfl) ⟨1701450, by rfl⟩ : syracuseStep 18148805 = 3402901) B3402901
theorem B3190225 : Blo 1258447 3190225 := bstep (se 2 (by rfl) ⟨1196334, by rfl⟩ : syracuseStep 3190225 = 2392669) B2392669
theorem B1887713 : Blo 1258447 1887713 := bstep (se 2 (by rfl) ⟨707892, by rfl⟩ : syracuseStep 1887713 = 1415785) B1415785
theorem B1887731 : Blo 1258447 1887731 := bstep (se 1 (by rfl) ⟨1415798, by rfl⟩ : syracuseStep 1887731 = 2831597) B2831597
theorem B1887761 : Blo 1258447 1887761 := bstep (se 2 (by rfl) ⟨707910, by rfl⟩ : syracuseStep 1887761 = 1415821) B1415821
theorem B2125345 : Blo 1258447 2125345 := bstep (se 2 (by rfl) ⟨797004, by rfl⟩ : syracuseStep 2125345 = 1594009) B1594009
theorem B1887779 : Blo 1258447 1887779 := bstep (se 1 (by rfl) ⟨1415834, by rfl⟩ : syracuseStep 1887779 = 2831669) B2831669
theorem B1887809 : Blo 1258447 1887809 := bstep (se 2 (by rfl) ⟨707928, by rfl⟩ : syracuseStep 1887809 = 1415857) B1415857
theorem B2125379 : Blo 1258447 2125379 := bstep (se 1 (by rfl) ⟨1594034, by rfl⟩ : syracuseStep 2125379 = 3188069) B3188069
theorem B1887827 : Blo 1258447 1887827 := bstep (se 1 (by rfl) ⟨1415870, by rfl⟩ : syracuseStep 1887827 = 2831741) B2831741
theorem B3026531 : Blo 1258447 3026531 := bstep (se 1 (by rfl) ⟨2269898, by rfl⟩ : syracuseStep 3026531 = 4539797) B4539797
theorem B1887857 : Blo 1258447 1887857 := bstep (se 2 (by rfl) ⟨707946, by rfl⟩ : syracuseStep 1887857 = 1415893) B1415893
theorem B1887875 : Blo 1258447 1887875 := bstep (se 1 (by rfl) ⟨1415906, by rfl⟩ : syracuseStep 1887875 = 2831813) B2831813
theorem B1887905 : Blo 1258447 1887905 := bstep (se 2 (by rfl) ⟨707964, by rfl⟩ : syracuseStep 1887905 = 1415929) B1415929
theorem B1887923 : Blo 1258447 1887923 := bstep (se 1 (by rfl) ⟨1415942, by rfl⟩ : syracuseStep 1887923 = 2831885) B2831885
theorem B2125507 : Blo 1258447 2125507 := bstep (se 1 (by rfl) ⟨1594130, by rfl⟩ : syracuseStep 2125507 = 3188261) B3188261
theorem B1887953 : Blo 1258447 1887953 := bstep (se 2 (by rfl) ⟨707982, by rfl⟩ : syracuseStep 1887953 = 1415965) B1415965
theorem B7171811 : Blo 1258447 7171811 := bstep (se 1 (by rfl) ⟨5378858, by rfl⟩ : syracuseStep 7171811 = 10757717) B10757717
theorem B1887971 : Blo 1258447 1887971 := bstep (se 1 (by rfl) ⟨1415978, by rfl⟩ : syracuseStep 1887971 = 2831957) B2831957
theorem B3190499 : Blo 1258447 3190499 := bstep (se 1 (by rfl) ⟨2392874, by rfl⟩ : syracuseStep 3190499 = 4785749) B4785749
theorem B1888001 : Blo 1258447 1888001 := bstep (se 2 (by rfl) ⟨708000, by rfl⟩ : syracuseStep 1888001 = 1416001) B1416001
theorem B1888019 : Blo 1258447 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B1888049 : Blo 1258447 1888049 := bstep (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) B1416037
theorem B1888067 : Blo 1258447 1888067 := bstep (se 1 (by rfl) ⟨1416050, by rfl⟩ : syracuseStep 1888067 = 2832101) B2832101
theorem B2125649 : Blo 1258447 2125649 := bstep (se 2 (by rfl) ⟨797118, by rfl⟩ : syracuseStep 2125649 = 1594237) B1594237
theorem B1888097 : Blo 1258447 1888097 := bstep (se 2 (by rfl) ⟨708036, by rfl⟩ : syracuseStep 1888097 = 1416073) B1416073
theorem B3026801 : Blo 1258447 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B1888115 : Blo 1258447 1888115 := bstep (se 1 (by rfl) ⟨1416086, by rfl⟩ : syracuseStep 1888115 = 2832173) B2832173
theorem B4779917 : Blo 1258447 4779917 := bstep (se 3 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 4779917 = 1792469) B1792469
theorem B1888145 : Blo 1258447 1888145 := bstep (se 2 (by rfl) ⟨708054, by rfl⟩ : syracuseStep 1888145 = 1416109) B1416109
theorem B1888163 : Blo 1258447 1888163 := bstep (se 1 (by rfl) ⟨1416122, by rfl⟩ : syracuseStep 1888163 = 2832245) B2832245
theorem B1888193 : Blo 1258447 1888193 := bstep (se 2 (by rfl) ⟨708072, by rfl⟩ : syracuseStep 1888193 = 1416145) B1416145
theorem B2125777 : Blo 1258447 2125777 := bstep (se 2 (by rfl) ⟨797166, by rfl⟩ : syracuseStep 2125777 = 1594333) B1594333
theorem B1888211 : Blo 1258447 1888211 := bstep (se 1 (by rfl) ⟨1416158, by rfl⟩ : syracuseStep 1888211 = 2832317) B2832317
theorem B1888241 : Blo 1258447 1888241 := bstep (se 2 (by rfl) ⟨708090, by rfl⟩ : syracuseStep 1888241 = 1416181) B1416181
theorem B2125811 : Blo 1258447 2125811 := bstep (se 1 (by rfl) ⟨1594358, by rfl⟩ : syracuseStep 2125811 = 3188717) B3188717
theorem B1888259 : Blo 1258447 1888259 := bstep (se 1 (by rfl) ⟨1416194, by rfl⟩ : syracuseStep 1888259 = 2832389) B2832389
theorem B1888289 : Blo 1258447 1888289 := bstep (se 2 (by rfl) ⟨708108, by rfl⟩ : syracuseStep 1888289 = 1416217) B1416217
theorem B4034605 : Blo 1258447 4034605 := bstep (se 3 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 4034605 = 1512977) B1512977
theorem B1888307 : Blo 1258447 1888307 := bstep (se 1 (by rfl) ⟨1416230, by rfl⟩ : syracuseStep 1888307 = 2832461) B2832461
theorem B1888337 : Blo 1258447 1888337 := bstep (se 2 (by rfl) ⟨708126, by rfl⟩ : syracuseStep 1888337 = 1416253) B1416253
theorem B1593427 : Blo 1258447 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B1888355 : Blo 1258447 1888355 := bstep (se 1 (by rfl) ⟨1416266, by rfl⟩ : syracuseStep 1888355 = 2832533) B2832533
theorem B2125939 : Blo 1258447 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B1888385 : Blo 1258447 1888385 := bstep (se 2 (by rfl) ⟨708144, by rfl⟩ : syracuseStep 1888385 = 1416289) B1416289
theorem B4247693 : Blo 1258447 4247693 := bstep (se 3 (by rfl) ⟨796442, by rfl⟩ : syracuseStep 4247693 = 1592885) B1592885
theorem B1888403 : Blo 1258447 1888403 := bstep (se 1 (by rfl) ⟨1416302, by rfl⟩ : syracuseStep 1888403 = 2832605) B2832605
theorem B1888433 : Blo 1258447 1888433 := bstep (se 2 (by rfl) ⟨708162, by rfl⟩ : syracuseStep 1888433 = 1416325) B1416325
theorem B1593523 : Blo 1258447 1593523 := bstep (se 1 (by rfl) ⟨1195142, by rfl⟩ : syracuseStep 1593523 = 2390285) B2390285
theorem B4247747 : Blo 1258447 4247747 := bstep (se 1 (by rfl) ⟨3185810, by rfl⟩ : syracuseStep 4247747 = 6371621) B6371621
theorem B1888451 : Blo 1258447 1888451 := bstep (se 1 (by rfl) ⟨1416338, by rfl⟩ : syracuseStep 1888451 = 2832677) B2832677
theorem B3584209 : Blo 1258447 3584209 := bstep (se 2 (by rfl) ⟨1344078, by rfl⟩ : syracuseStep 3584209 = 2688157) B2688157
theorem B1888481 : Blo 1258447 1888481 := bstep (se 2 (by rfl) ⟨708180, by rfl⟩ : syracuseStep 1888481 = 1416361) B1416361
theorem B3027185 : Blo 1258447 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B1888499 : Blo 1258447 1888499 := bstep (se 1 (by rfl) ⟨1416374, by rfl⟩ : syracuseStep 1888499 = 2832749) B2832749
theorem B2126081 : Blo 1258447 2126081 := bstep (se 2 (by rfl) ⟨797280, by rfl⟩ : syracuseStep 2126081 = 1594561) B1594561
theorem B1888529 : Blo 1258447 1888529 := bstep (se 2 (by rfl) ⟨708198, by rfl⟩ : syracuseStep 1888529 = 1416397) B1416397
theorem B1888547 : Blo 1258447 1888547 := bstep (se 1 (by rfl) ⟨1416410, by rfl⟩ : syracuseStep 1888547 = 2832821) B2832821
theorem B6377777 : Blo 1258447 6377777 := bstep (se 2 (by rfl) ⟨2391666, by rfl⟩ : syracuseStep 6377777 = 4783333) B4783333
theorem B1888577 : Blo 1258447 1888577 := bstep (se 2 (by rfl) ⟨708216, by rfl⟩ : syracuseStep 1888577 = 1416433) B1416433
theorem B1888595 : Blo 1258447 1888595 := bstep (se 1 (by rfl) ⟨1416446, by rfl⟩ : syracuseStep 1888595 = 2832893) B2832893
theorem B1888625 : Blo 1258447 1888625 := bstep (se 2 (by rfl) ⟨708234, by rfl⟩ : syracuseStep 1888625 = 1416469) B1416469
theorem B1888643 : Blo 1258447 1888643 := bstep (se 1 (by rfl) ⟨1416482, by rfl⟩ : syracuseStep 1888643 = 2832965) B2832965
theorem B2126209 : Blo 1258447 2126209 := bstep (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) B1594657
theorem B1888673 : Blo 1258447 1888673 := bstep (se 2 (by rfl) ⟨708252, by rfl⟩ : syracuseStep 1888673 = 1416505) B1416505
theorem B2126243 : Blo 1258447 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B1888691 : Blo 1258447 1888691 := bstep (se 1 (by rfl) ⟨1416518, by rfl⟩ : syracuseStep 1888691 = 2833037) B2833037
theorem B4248017 : Blo 1258447 4248017 := bstep (se 2 (by rfl) ⟨1593006, by rfl⟩ : syracuseStep 4248017 = 3186013) B3186013
theorem B1888721 : Blo 1258447 1888721 := bstep (se 2 (by rfl) ⟨708270, by rfl⟩ : syracuseStep 1888721 = 1416541) B1416541
theorem B3584483 : Blo 1258447 3584483 := bstep (se 1 (by rfl) ⟨2688362, by rfl⟩ : syracuseStep 3584483 = 5376725) B5376725
theorem B1888739 : Blo 1258447 1888739 := bstep (se 1 (by rfl) ⟨1416554, by rfl⟩ : syracuseStep 1888739 = 2833109) B2833109
theorem B1888769 : Blo 1258447 1888769 := bstep (se 2 (by rfl) ⟨708288, by rfl⟩ : syracuseStep 1888769 = 1416577) B1416577
theorem B1888787 : Blo 1258447 1888787 := bstep (se 1 (by rfl) ⟨1416590, by rfl⟩ : syracuseStep 1888787 = 2833181) B2833181
theorem B2126371 : Blo 1258447 2126371 := bstep (se 1 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 2126371 = 3189557) B3189557
theorem B1888817 : Blo 1258447 1888817 := bstep (se 2 (by rfl) ⟨708306, by rfl⟩ : syracuseStep 1888817 = 1416613) B1416613
theorem B1888835 : Blo 1258447 1888835 := bstep (se 1 (by rfl) ⟨1416626, by rfl⟩ : syracuseStep 1888835 = 2833253) B2833253
theorem B1888865 : Blo 1258447 1888865 := bstep (se 2 (by rfl) ⟨708324, by rfl⟩ : syracuseStep 1888865 = 1416649) B1416649
theorem B1888883 : Blo 1258447 1888883 := bstep (se 1 (by rfl) ⟨1416662, by rfl⟩ : syracuseStep 1888883 = 2833325) B2833325
theorem B1888913 : Blo 1258447 1888913 := bstep (se 2 (by rfl) ⟨708342, by rfl⟩ : syracuseStep 1888913 = 1416685) B1416685
theorem B3584675 : Blo 1258447 3584675 := bstep (se 1 (by rfl) ⟨2688506, by rfl⟩ : syracuseStep 3584675 = 5377013) B5377013
theorem B5378723 : Blo 1258447 5378723 := bstep (se 1 (by rfl) ⟨4034042, by rfl⟩ : syracuseStep 5378723 = 8068085) B8068085
theorem B1888931 : Blo 1258447 1888931 := bstep (se 1 (by rfl) ⟨1416698, by rfl⟩ : syracuseStep 1888931 = 2833397) B2833397
theorem B1594019 : Blo 1258447 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B7664291 : Blo 1258447 7664291 := bstep (se 1 (by rfl) ⟨5748218, by rfl⟩ : syracuseStep 7664291 = 11496437) B11496437
theorem B4780721 : Blo 1258447 4780721 := bstep (se 2 (by rfl) ⟨1792770, by rfl⟩ : syracuseStep 4780721 = 3585541) B3585541
theorem B2126513 : Blo 1258447 2126513 := bstep (se 2 (by rfl) ⟨797442, by rfl⟩ : syracuseStep 2126513 = 1594885) B1594885
theorem B1888961 : Blo 1258447 1888961 := bstep (se 2 (by rfl) ⟨708360, by rfl⟩ : syracuseStep 1888961 = 1416721) B1416721
theorem B16151237 : Blo 1258447 16151237 := bstep (se 4 (by rfl) ⟨1514178, by rfl⟩ : syracuseStep 16151237 = 3028357) B3028357
theorem B7172813 : Blo 1258447 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B1888979 : Blo 1258447 1888979 := bstep (se 1 (by rfl) ⟨1416734, by rfl⟩ : syracuseStep 1888979 = 2833469) B2833469
theorem B11481841 : Blo 1258447 11481841 := bstep (se 2 (by rfl) ⟨4305690, by rfl⟩ : syracuseStep 11481841 = 8611381) B8611381
theorem B8065777 : Blo 1258447 8065777 := bstep (se 2 (by rfl) ⟨3024666, by rfl⟩ : syracuseStep 8065777 = 6049333) B6049333
theorem B1889009 : Blo 1258447 1889009 := bstep (se 2 (by rfl) ⟨708378, by rfl⟩ : syracuseStep 1889009 = 1416757) B1416757
theorem B1889027 : Blo 1258447 1889027 := bstep (se 1 (by rfl) ⟨1416770, by rfl⟩ : syracuseStep 1889027 = 2833541) B2833541
theorem B1889057 : Blo 1258447 1889057 := bstep (se 2 (by rfl) ⟨708396, by rfl⟩ : syracuseStep 1889057 = 1416793) B1416793
theorem B2126641 : Blo 1258447 2126641 := bstep (se 2 (by rfl) ⟨797490, by rfl⟩ : syracuseStep 2126641 = 1594981) B1594981
theorem B1889075 : Blo 1258447 1889075 := bstep (se 1 (by rfl) ⟨1416806, by rfl⟩ : syracuseStep 1889075 = 2833613) B2833613
theorem B1889105 : Blo 1258447 1889105 := bstep (se 2 (by rfl) ⟨708414, by rfl⟩ : syracuseStep 1889105 = 1416829) B1416829
theorem B2126675 : Blo 1258447 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B1889123 : Blo 1258447 1889123 := bstep (se 1 (by rfl) ⟨1416842, by rfl⟩ : syracuseStep 1889123 = 2833685) B2833685
theorem B1889153 : Blo 1258447 1889153 := bstep (se 2 (by rfl) ⟨708432, by rfl⟩ : syracuseStep 1889153 = 1416865) B1416865
theorem B6812549 : Blo 1258447 6812549 := bstep (se 4 (by rfl) ⟨638676, by rfl⟩ : syracuseStep 6812549 = 1277353) B1277353
theorem B1889171 : Blo 1258447 1889171 := bstep (se 1 (by rfl) ⟨1416878, by rfl⟩ : syracuseStep 1889171 = 2833757) B2833757
theorem B1889201 : Blo 1258447 1889201 := bstep (se 2 (by rfl) ⟨708450, by rfl⟩ : syracuseStep 1889201 = 1416901) B1416901
theorem B1889219 : Blo 1258447 1889219 := bstep (se 1 (by rfl) ⟨1416914, by rfl⟩ : syracuseStep 1889219 = 2833829) B2833829
theorem B1258451 : Blo 1258447 1258451 := bstep (se 1 (by rfl) ⟨943838, by rfl⟩ : syracuseStep 1258451 = 1887677) B1887677
theorem B2126803 : Blo 1258447 2126803 := bstep (se 1 (by rfl) ⟨1595102, by rfl⟩ : syracuseStep 2126803 = 3190205) B3190205
theorem B1889249 : Blo 1258447 1889249 := bstep (se 2 (by rfl) ⟨708468, by rfl⟩ : syracuseStep 1889249 = 1416937) B1416937
theorem B1258467 : Blo 1258447 1258467 := bstep (se 1 (by rfl) ⟨943850, by rfl⟩ : syracuseStep 1258467 = 1887701) B1887701
theorem B16135139 : Blo 1258447 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B4248557 : Blo 1258447 4248557 := bstep (se 3 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 4248557 = 1593209) B1593209
theorem B3027953 : Blo 1258447 3027953 := bstep (se 2 (by rfl) ⟨1135482, by rfl⟩ : syracuseStep 3027953 = 2270965) B2270965
theorem B1258483 : Blo 1258447 1258483 := bstep (se 1 (by rfl) ⟨943862, by rfl⟩ : syracuseStep 1258483 = 1887725) B1887725
theorem B1889267 : Blo 1258447 1889267 := bstep (se 1 (by rfl) ⟨1416950, by rfl⟩ : syracuseStep 1889267 = 2833901) B2833901
theorem B1258499 : Blo 1258447 1258499 := bstep (se 1 (by rfl) ⟨943874, by rfl⟩ : syracuseStep 1258499 = 1887749) B1887749
theorem B4305923 : Blo 1258447 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B1889297 : Blo 1258447 1889297 := bstep (se 2 (by rfl) ⟨708486, by rfl⟩ : syracuseStep 1889297 = 1416973) B1416973
theorem B1258515 : Blo 1258447 1258515 := bstep (se 1 (by rfl) ⟨943886, by rfl⟩ : syracuseStep 1258515 = 1887773) B1887773
theorem B1258531 : Blo 1258447 1258531 := bstep (se 1 (by rfl) ⟨943898, by rfl⟩ : syracuseStep 1258531 = 1887797) B1887797
theorem B4248611 : Blo 1258447 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B1889315 : Blo 1258447 1889315 := bstep (se 1 (by rfl) ⟨1416986, by rfl⟩ : syracuseStep 1889315 = 2833973) B2833973
theorem B1258547 : Blo 1258447 1258547 := bstep (se 1 (by rfl) ⟨943910, by rfl⟩ : syracuseStep 1258547 = 1887821) B1887821
theorem B62100533 : Blo 1258447 62100533 := bstep (se 5 (by rfl) ⟨2910962, by rfl⟩ : syracuseStep 62100533 = 5821925) B5821925
theorem B1889345 : Blo 1258447 1889345 := bstep (se 2 (by rfl) ⟨708504, by rfl⟩ : syracuseStep 1889345 = 1417009) B1417009
theorem B1258563 : Blo 1258447 1258563 := bstep (se 1 (by rfl) ⟨943922, by rfl⟩ : syracuseStep 1258563 = 1887845) B1887845
theorem B1258579 : Blo 1258447 1258579 := bstep (se 1 (by rfl) ⟨943934, by rfl⟩ : syracuseStep 1258579 = 1887869) B1887869
theorem B1889363 : Blo 1258447 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B2126945 : Blo 1258447 2126945 := bstep (se 2 (by rfl) ⟨797604, by rfl⟩ : syracuseStep 2126945 = 1595209) B1595209
theorem B1258595 : Blo 1258447 1258595 := bstep (se 1 (by rfl) ⟨943946, by rfl⟩ : syracuseStep 1258595 = 1887893) B1887893
theorem B4035683 : Blo 1258447 4035683 := bstep (se 1 (by rfl) ⟨3026762, by rfl⟩ : syracuseStep 4035683 = 6053525) B6053525
theorem B6804593 : Blo 1258447 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B1889393 : Blo 1258447 1889393 := bstep (se 2 (by rfl) ⟨708522, by rfl⟩ : syracuseStep 1889393 = 1417045) B1417045
theorem B1258611 : Blo 1258447 1258611 := bstep (se 1 (by rfl) ⟨943958, by rfl⟩ : syracuseStep 1258611 = 1887917) B1887917
theorem B1258627 : Blo 1258447 1258627 := bstep (se 1 (by rfl) ⟨943970, by rfl⟩ : syracuseStep 1258627 = 1887941) B1887941
theorem B1889411 : Blo 1258447 1889411 := bstep (se 1 (by rfl) ⟨1417058, by rfl⟩ : syracuseStep 1889411 = 2834117) B2834117
theorem B2364547 : Blo 1258447 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3028099 : Blo 1258447 3028099 := bstep (se 1 (by rfl) ⟨2271074, by rfl⟩ : syracuseStep 3028099 = 4542149) B4542149
theorem B1258643 : Blo 1258447 1258643 := bstep (se 1 (by rfl) ⟨943982, by rfl⟩ : syracuseStep 1258643 = 1887965) B1887965
theorem B1889441 : Blo 1258447 1889441 := bstep (se 2 (by rfl) ⟨708540, by rfl⟩ : syracuseStep 1889441 = 1417081) B1417081
theorem B1258659 : Blo 1258447 1258659 := bstep (se 1 (by rfl) ⟨943994, by rfl⟩ : syracuseStep 1258659 = 1887989) B1887989
theorem B3232931 : Blo 1258447 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B2389169 : Blo 1258447 2389169 := bstep (se 2 (by rfl) ⟨895938, by rfl⟩ : syracuseStep 2389169 = 1791877) B1791877
theorem B1258675 : Blo 1258447 1258675 := bstep (se 1 (by rfl) ⟨944006, by rfl⟩ : syracuseStep 1258675 = 1888013) B1888013
theorem B1889459 : Blo 1258447 1889459 := bstep (se 1 (by rfl) ⟨1417094, by rfl⟩ : syracuseStep 1889459 = 2834189) B2834189
theorem B1258691 : Blo 1258447 1258691 := bstep (se 1 (by rfl) ⟨944018, by rfl⟩ : syracuseStep 1258691 = 1888037) B1888037
theorem B9557189 : Blo 1258447 9557189 := bstep (se 4 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 9557189 = 1791973) B1791973
theorem B1889489 : Blo 1258447 1889489 := bstep (se 2 (by rfl) ⟨708558, by rfl⟩ : syracuseStep 1889489 = 1417117) B1417117
theorem B1258707 : Blo 1258447 1258707 := bstep (se 1 (by rfl) ⟨944030, by rfl⟩ : syracuseStep 1258707 = 1888061) B1888061
theorem B1258723 : Blo 1258447 1258723 := bstep (se 1 (by rfl) ⟨944042, by rfl⟩ : syracuseStep 1258723 = 1888085) B1888085
theorem B1889507 : Blo 1258447 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B1258739 : Blo 1258447 1258739 := bstep (se 1 (by rfl) ⟨944054, by rfl⟩ : syracuseStep 1258739 = 1888109) B1888109
theorem B1889537 : Blo 1258447 1889537 := bstep (se 2 (by rfl) ⟨708576, by rfl⟩ : syracuseStep 1889537 = 1417153) B1417153
theorem B1258755 : Blo 1258447 1258755 := bstep (se 1 (by rfl) ⟨944066, by rfl⟩ : syracuseStep 1258755 = 1888133) B1888133
theorem B2872579 : Blo 1258447 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B2831633 : Blo 1258447 2831633 := bstep (se 2 (by rfl) ⟨1061862, by rfl⟩ : syracuseStep 2831633 = 2123725) B2123725
theorem B1258771 : Blo 1258447 1258771 := bstep (se 1 (by rfl) ⟨944078, by rfl⟩ : syracuseStep 1258771 = 1888157) B1888157
theorem B1889555 : Blo 1258447 1889555 := bstep (se 1 (by rfl) ⟨1417166, by rfl⟩ : syracuseStep 1889555 = 2834333) B2834333
theorem B2831651 : Blo 1258447 2831651 := bstep (se 1 (by rfl) ⟨2123738, by rfl⟩ : syracuseStep 2831651 = 4247477) B4247477
theorem B1258787 : Blo 1258447 1258787 := bstep (se 1 (by rfl) ⟨944090, by rfl⟩ : syracuseStep 1258787 = 1888181) B1888181
theorem B4248881 : Blo 1258447 4248881 := bstep (se 2 (by rfl) ⟨1593330, by rfl⟩ : syracuseStep 4248881 = 3186661) B3186661
theorem B1889585 : Blo 1258447 1889585 := bstep (se 2 (by rfl) ⟨708594, by rfl⟩ : syracuseStep 1889585 = 1417189) B1417189
theorem B1258803 : Blo 1258447 1258803 := bstep (se 1 (by rfl) ⟨944102, by rfl⟩ : syracuseStep 1258803 = 1888205) B1888205
theorem B1258819 : Blo 1258447 1258819 := bstep (se 1 (by rfl) ⟨944114, by rfl⟩ : syracuseStep 1258819 = 1888229) B1888229
theorem B1889603 : Blo 1258447 1889603 := bstep (se 1 (by rfl) ⟨1417202, by rfl⟩ : syracuseStep 1889603 = 2834405) B2834405
theorem B4781389 : Blo 1258447 4781389 := bstep (se 3 (by rfl) ⟨896510, by rfl⟩ : syracuseStep 4781389 = 1793021) B1793021
theorem B1258835 : Blo 1258447 1258835 := bstep (se 1 (by rfl) ⟨944126, by rfl⟩ : syracuseStep 1258835 = 1888253) B1888253
theorem B1889633 : Blo 1258447 1889633 := bstep (se 2 (by rfl) ⟨708612, by rfl⟩ : syracuseStep 1889633 = 1417225) B1417225
theorem B1258851 : Blo 1258447 1258851 := bstep (se 1 (by rfl) ⟨944138, by rfl⟩ : syracuseStep 1258851 = 1888277) B1888277
theorem B1594723 : Blo 1258447 1594723 := bstep (se 1 (by rfl) ⟨1196042, by rfl⟩ : syracuseStep 1594723 = 2392085) B2392085
theorem B10220899 : Blo 1258447 10220899 := bstep (se 1 (by rfl) ⟨7665674, by rfl⟩ : syracuseStep 10220899 = 15331349) B15331349
theorem B1258867 : Blo 1258447 1258867 := bstep (se 1 (by rfl) ⟨944150, by rfl⟩ : syracuseStep 1258867 = 1888301) B1888301
theorem B1889651 : Blo 1258447 1889651 := bstep (se 1 (by rfl) ⟨1417238, by rfl⟩ : syracuseStep 1889651 = 2834477) B2834477
theorem B1258883 : Blo 1258447 1258883 := bstep (se 1 (by rfl) ⟨944162, by rfl⟩ : syracuseStep 1258883 = 1888325) B1888325
theorem B1258899 : Blo 1258447 1258899 := bstep (se 1 (by rfl) ⟨944174, by rfl⟩ : syracuseStep 1258899 = 1888349) B1888349
theorem B1889681 : Blo 1258447 1889681 := bstep (se 2 (by rfl) ⟨708630, by rfl⟩ : syracuseStep 1889681 = 1417261) B1417261
theorem B1258915 : Blo 1258447 1258915 := bstep (se 1 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 1258915 = 1888373) B1888373
theorem B1889699 : Blo 1258447 1889699 := bstep (se 1 (by rfl) ⟨1417274, by rfl⟩ : syracuseStep 1889699 = 2834549) B2834549
theorem B1258931 : Blo 1258447 1258931 := bstep (se 1 (by rfl) ⟨944198, by rfl⟩ : syracuseStep 1258931 = 1888397) B1888397
theorem B1889729 : Blo 1258447 1889729 := bstep (se 2 (by rfl) ⟨708648, by rfl⟩ : syracuseStep 1889729 = 1417297) B1417297
theorem B1258947 : Blo 1258447 1258947 := bstep (se 1 (by rfl) ⟨944210, by rfl⟩ : syracuseStep 1258947 = 1888421) B1888421
theorem B1594819 : Blo 1258447 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B3585485 : Blo 1258447 3585485 := bstep (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) B1344557
theorem B1258963 : Blo 1258447 1258963 := bstep (se 1 (by rfl) ⟨944222, by rfl⟩ : syracuseStep 1258963 = 1888445) B1888445
theorem B1889747 : Blo 1258447 1889747 := bstep (se 1 (by rfl) ⟨1417310, by rfl⟩ : syracuseStep 1889747 = 2834621) B2834621
theorem B1258979 : Blo 1258447 1258979 := bstep (se 1 (by rfl) ⟨944234, by rfl⟩ : syracuseStep 1258979 = 1888469) B1888469
theorem B6813155 : Blo 1258447 6813155 := bstep (se 1 (by rfl) ⟨5109866, by rfl⟩ : syracuseStep 6813155 = 10219733) B10219733
theorem B1889777 : Blo 1258447 1889777 := bstep (se 2 (by rfl) ⟨708666, by rfl⟩ : syracuseStep 1889777 = 1417333) B1417333
theorem B1258995 : Blo 1258447 1258995 := bstep (se 1 (by rfl) ⟨944246, by rfl⟩ : syracuseStep 1258995 = 1888493) B1888493
theorem B1259011 : Blo 1258447 1259011 := bstep (se 1 (by rfl) ⟨944258, by rfl⟩ : syracuseStep 1259011 = 1888517) B1888517
theorem B1889795 : Blo 1258447 1889795 := bstep (se 1 (by rfl) ⟨1417346, by rfl⟩ : syracuseStep 1889795 = 2834693) B2834693
theorem B1259027 : Blo 1258447 1259027 := bstep (se 1 (by rfl) ⟨944270, by rfl⟩ : syracuseStep 1259027 = 1888541) B1888541
theorem B1889825 : Blo 1258447 1889825 := bstep (se 2 (by rfl) ⟨708684, by rfl⟩ : syracuseStep 1889825 = 1417369) B1417369
theorem B1259043 : Blo 1258447 1259043 := bstep (se 1 (by rfl) ⟨944282, by rfl⟩ : syracuseStep 1259043 = 1888565) B1888565
theorem B2831921 : Blo 1258447 2831921 := bstep (se 2 (by rfl) ⟨1061970, by rfl⟩ : syracuseStep 2831921 = 2123941) B2123941
theorem B1259059 : Blo 1258447 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B1889843 : Blo 1258447 1889843 := bstep (se 1 (by rfl) ⟨1417382, by rfl⟩ : syracuseStep 1889843 = 2834765) B2834765
theorem B2831939 : Blo 1258447 2831939 := bstep (se 1 (by rfl) ⟨2123954, by rfl⟩ : syracuseStep 2831939 = 4247909) B4247909
theorem B2389571 : Blo 1258447 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B1259075 : Blo 1258447 1259075 := bstep (se 1 (by rfl) ⟨944306, by rfl⟩ : syracuseStep 1259075 = 1888613) B1888613
theorem B1889873 : Blo 1258447 1889873 := bstep (se 2 (by rfl) ⟨708702, by rfl⟩ : syracuseStep 1889873 = 1417405) B1417405
theorem B1259091 : Blo 1258447 1259091 := bstep (se 1 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 1259091 = 1888637) B1888637
theorem B1259107 : Blo 1258447 1259107 := bstep (se 1 (by rfl) ⟨944330, by rfl⟩ : syracuseStep 1259107 = 1888661) B1888661
theorem B1889891 : Blo 1258447 1889891 := bstep (se 1 (by rfl) ⟨1417418, by rfl⟩ : syracuseStep 1889891 = 2834837) B2834837
theorem B1259123 : Blo 1258447 1259123 := bstep (se 1 (by rfl) ⟨944342, by rfl⟩ : syracuseStep 1259123 = 1888685) B1888685
theorem B1889921 : Blo 1258447 1889921 := bstep (se 2 (by rfl) ⟨708720, by rfl⟩ : syracuseStep 1889921 = 1417441) B1417441
theorem B1259139 : Blo 1258447 1259139 := bstep (se 1 (by rfl) ⟨944354, by rfl⟩ : syracuseStep 1259139 = 1888709) B1888709
theorem B3585667 : Blo 1258447 3585667 := bstep (se 1 (by rfl) ⟨2689250, by rfl⟩ : syracuseStep 3585667 = 5378501) B5378501
theorem B1259155 : Blo 1258447 1259155 := bstep (se 1 (by rfl) ⟨944366, by rfl⟩ : syracuseStep 1259155 = 1888733) B1888733
theorem B1889939 : Blo 1258447 1889939 := bstep (se 1 (by rfl) ⟨1417454, by rfl⟩ : syracuseStep 1889939 = 2834909) B2834909
theorem B1259171 : Blo 1258447 1259171 := bstep (se 1 (by rfl) ⟨944378, by rfl⟩ : syracuseStep 1259171 = 1888757) B1888757
theorem B1889969 : Blo 1258447 1889969 := bstep (se 2 (by rfl) ⟨708738, by rfl⟩ : syracuseStep 1889969 = 1417477) B1417477
theorem B1259187 : Blo 1258447 1259187 := bstep (se 1 (by rfl) ⟨944390, by rfl⟩ : syracuseStep 1259187 = 1888781) B1888781
theorem B1259203 : Blo 1258447 1259203 := bstep (se 1 (by rfl) ⟨944402, by rfl⟩ : syracuseStep 1259203 = 1888805) B1888805
theorem B1889987 : Blo 1258447 1889987 := bstep (se 1 (by rfl) ⟨1417490, by rfl⟩ : syracuseStep 1889987 = 2834981) B2834981
theorem B1259219 : Blo 1258447 1259219 := bstep (se 1 (by rfl) ⟨944414, by rfl⟩ : syracuseStep 1259219 = 1888829) B1888829
theorem B1890017 : Blo 1258447 1890017 := bstep (se 2 (by rfl) ⟨708756, by rfl⟩ : syracuseStep 1890017 = 1417513) B1417513
theorem B1259235 : Blo 1258447 1259235 := bstep (se 1 (by rfl) ⟨944426, by rfl⟩ : syracuseStep 1259235 = 1888853) B1888853
theorem B6379235 : Blo 1258447 6379235 := bstep (se 1 (by rfl) ⟨4784426, by rfl⟩ : syracuseStep 6379235 = 9568853) B9568853
theorem B9565937 : Blo 1258447 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B4036337 : Blo 1258447 4036337 := bstep (se 2 (by rfl) ⟨1513626, by rfl⟩ : syracuseStep 4036337 = 3027253) B3027253
theorem B1259251 : Blo 1258447 1259251 := bstep (se 1 (by rfl) ⟨944438, by rfl⟩ : syracuseStep 1259251 = 1888877) B1888877
theorem B1890035 : Blo 1258447 1890035 := bstep (se 1 (by rfl) ⟨1417526, by rfl⟩ : syracuseStep 1890035 = 2835053) B2835053
theorem B1259267 : Blo 1258447 1259267 := bstep (se 1 (by rfl) ⟨944450, by rfl⟩ : syracuseStep 1259267 = 1888901) B1888901
theorem B1890065 : Blo 1258447 1890065 := bstep (se 2 (by rfl) ⟨708774, by rfl⟩ : syracuseStep 1890065 = 1417549) B1417549
theorem B1259283 : Blo 1258447 1259283 := bstep (se 1 (by rfl) ⟨944462, by rfl⟩ : syracuseStep 1259283 = 1888925) B1888925
theorem B1259299 : Blo 1258447 1259299 := bstep (se 1 (by rfl) ⟨944474, by rfl⟩ : syracuseStep 1259299 = 1888949) B1888949
theorem B1890083 : Blo 1258447 1890083 := bstep (se 1 (by rfl) ⟨1417562, by rfl⟩ : syracuseStep 1890083 = 2835125) B2835125
theorem B1259315 : Blo 1258447 1259315 := bstep (se 1 (by rfl) ⟨944486, by rfl⟩ : syracuseStep 1259315 = 1888973) B1888973
theorem B1259331 : Blo 1258447 1259331 := bstep (se 1 (by rfl) ⟨944498, by rfl⟩ : syracuseStep 1259331 = 1888997) B1888997
theorem B1890113 : Blo 1258447 1890113 := bstep (se 2 (by rfl) ⟨708792, by rfl⟩ : syracuseStep 1890113 = 1417585) B1417585
theorem B4249421 : Blo 1258447 4249421 := bstep (se 3 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 4249421 = 1593533) B1593533
theorem B2832209 : Blo 1258447 2832209 := bstep (se 2 (by rfl) ⟨1062078, by rfl⟩ : syracuseStep 2832209 = 2124157) B2124157
theorem B1259347 : Blo 1258447 1259347 := bstep (se 1 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 1259347 = 1889021) B1889021
theorem B1890131 : Blo 1258447 1890131 := bstep (se 1 (by rfl) ⟨1417598, by rfl⟩ : syracuseStep 1890131 = 2835197) B2835197
theorem B4536163 : Blo 1258447 4536163 := bstep (se 1 (by rfl) ⟨3402122, by rfl⟩ : syracuseStep 4536163 = 6804245) B6804245
theorem B2832227 : Blo 1258447 2832227 := bstep (se 1 (by rfl) ⟨2124170, by rfl⟩ : syracuseStep 2832227 = 4248341) B4248341
theorem B1259363 : Blo 1258447 1259363 := bstep (se 1 (by rfl) ⟨944522, by rfl⟩ : syracuseStep 1259363 = 1889045) B1889045
theorem B24205169 : Blo 1258447 24205169 := bstep (se 2 (by rfl) ⟨9076938, by rfl⟩ : syracuseStep 24205169 = 18153877) B18153877
theorem B1890161 : Blo 1258447 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B1259379 : Blo 1258447 1259379 := bstep (se 1 (by rfl) ⟨944534, by rfl⟩ : syracuseStep 1259379 = 1889069) B1889069
theorem B4249475 : Blo 1258447 4249475 := bstep (se 1 (by rfl) ⟨3187106, by rfl⟩ : syracuseStep 4249475 = 6374213) B6374213
theorem B1259395 : Blo 1258447 1259395 := bstep (se 1 (by rfl) ⟨944546, by rfl⟩ : syracuseStep 1259395 = 1889093) B1889093
theorem B1890179 : Blo 1258447 1890179 := bstep (se 1 (by rfl) ⟨1417634, by rfl⟩ : syracuseStep 1890179 = 2835269) B2835269
theorem B1259411 : Blo 1258447 1259411 := bstep (se 1 (by rfl) ⟨944558, by rfl⟩ : syracuseStep 1259411 = 1889117) B1889117
theorem B1890209 : Blo 1258447 1890209 := bstep (se 2 (by rfl) ⟨708828, by rfl⟩ : syracuseStep 1890209 = 1417657) B1417657
theorem B1259427 : Blo 1258447 1259427 := bstep (se 1 (by rfl) ⟨944570, by rfl⟩ : syracuseStep 1259427 = 1889141) B1889141
theorem B1259443 : Blo 1258447 1259443 := bstep (se 1 (by rfl) ⟨944582, by rfl⟩ : syracuseStep 1259443 = 1889165) B1889165
theorem B1890227 : Blo 1258447 1890227 := bstep (se 1 (by rfl) ⟨1417670, by rfl⟩ : syracuseStep 1890227 = 2835341) B2835341
theorem B1259459 : Blo 1258447 1259459 := bstep (se 1 (by rfl) ⟨944594, by rfl⟩ : syracuseStep 1259459 = 1889189) B1889189
theorem B1890257 : Blo 1258447 1890257 := bstep (se 2 (by rfl) ⟨708846, by rfl⟩ : syracuseStep 1890257 = 1417693) B1417693
theorem B1259475 : Blo 1258447 1259475 := bstep (se 1 (by rfl) ⟨944606, by rfl⟩ : syracuseStep 1259475 = 1889213) B1889213
theorem B1259491 : Blo 1258447 1259491 := bstep (se 1 (by rfl) ⟨944618, by rfl⟩ : syracuseStep 1259491 = 1889237) B1889237
theorem B1890275 : Blo 1258447 1890275 := bstep (se 1 (by rfl) ⟨1417706, by rfl⟩ : syracuseStep 1890275 = 2835413) B2835413
theorem B1791985 : Blo 1258447 1791985 := bstep (se 2 (by rfl) ⟨671994, by rfl⟩ : syracuseStep 1791985 = 1343989) B1343989
theorem B1259507 : Blo 1258447 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B1890305 : Blo 1258447 1890305 := bstep (se 2 (by rfl) ⟨708864, by rfl⟩ : syracuseStep 1890305 = 1417729) B1417729
theorem B1259523 : Blo 1258447 1259523 := bstep (se 1 (by rfl) ⟨944642, by rfl⟩ : syracuseStep 1259523 = 1889285) B1889285
theorem B1259539 : Blo 1258447 1259539 := bstep (se 1 (by rfl) ⟨944654, by rfl⟩ : syracuseStep 1259539 = 1889309) B1889309
theorem B1890323 : Blo 1258447 1890323 := bstep (se 1 (by rfl) ⟨1417742, by rfl⟩ : syracuseStep 1890323 = 2835485) B2835485
theorem B1259555 : Blo 1258447 1259555 := bstep (se 1 (by rfl) ⟨944666, by rfl⟩ : syracuseStep 1259555 = 1889333) B1889333
theorem B1890353 : Blo 1258447 1890353 := bstep (se 2 (by rfl) ⟨708882, by rfl⟩ : syracuseStep 1890353 = 1417765) B1417765
theorem B1259571 : Blo 1258447 1259571 := bstep (se 1 (by rfl) ⟨944678, by rfl⟩ : syracuseStep 1259571 = 1889357) B1889357
theorem B1259587 : Blo 1258447 1259587 := bstep (se 1 (by rfl) ⟨944690, by rfl⟩ : syracuseStep 1259587 = 1889381) B1889381
theorem B1890371 : Blo 1258447 1890371 := bstep (se 1 (by rfl) ⟨1417778, by rfl⟩ : syracuseStep 1890371 = 2835557) B2835557
theorem B1259603 : Blo 1258447 1259603 := bstep (se 1 (by rfl) ⟨944702, by rfl⟩ : syracuseStep 1259603 = 1889405) B1889405
theorem B1890401 : Blo 1258447 1890401 := bstep (se 2 (by rfl) ⟨708900, by rfl⟩ : syracuseStep 1890401 = 1417801) B1417801
theorem B14735459 : Blo 1258447 14735459 := bstep (se 1 (by rfl) ⟨11051594, by rfl⟩ : syracuseStep 14735459 = 22103189) B22103189
theorem B4782179 : Blo 1258447 4782179 := bstep (se 1 (by rfl) ⟨3586634, by rfl⟩ : syracuseStep 4782179 = 7173269) B7173269
theorem B1259619 : Blo 1258447 1259619 := bstep (se 1 (by rfl) ⟨944714, by rfl⟩ : syracuseStep 1259619 = 1889429) B1889429
theorem B3586157 : Blo 1258447 3586157 := bstep (se 3 (by rfl) ⟨672404, by rfl⟩ : syracuseStep 3586157 = 1344809) B1344809
theorem B2832497 : Blo 1258447 2832497 := bstep (se 2 (by rfl) ⟨1062186, by rfl⟩ : syracuseStep 2832497 = 2124373) B2124373
theorem B1259635 : Blo 1258447 1259635 := bstep (se 1 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 1259635 = 1889453) B1889453
theorem B1890419 : Blo 1258447 1890419 := bstep (se 1 (by rfl) ⟨1417814, by rfl⟩ : syracuseStep 1890419 = 2835629) B2835629
theorem B2832515 : Blo 1258447 2832515 := bstep (se 1 (by rfl) ⟨2124386, by rfl⟩ : syracuseStep 2832515 = 4248773) B4248773
theorem B1259651 : Blo 1258447 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B4249745 : Blo 1258447 4249745 := bstep (se 2 (by rfl) ⟨1593654, by rfl⟩ : syracuseStep 4249745 = 3187309) B3187309
theorem B1259667 : Blo 1258447 1259667 := bstep (se 1 (by rfl) ⟨944750, by rfl⟩ : syracuseStep 1259667 = 1889501) B1889501
theorem B1890449 : Blo 1258447 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B1259683 : Blo 1258447 1259683 := bstep (se 1 (by rfl) ⟨944762, by rfl⟩ : syracuseStep 1259683 = 1889525) B1889525
theorem B1890467 : Blo 1258447 1890467 := bstep (se 1 (by rfl) ⟨1417850, by rfl⟩ : syracuseStep 1890467 = 2835701) B2835701
theorem B1702067 : Blo 1258447 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B1259699 : Blo 1258447 1259699 := bstep (se 1 (by rfl) ⟨944774, by rfl⟩ : syracuseStep 1259699 = 1889549) B1889549
theorem B1890497 : Blo 1258447 1890497 := bstep (se 2 (by rfl) ⟨708936, by rfl⟩ : syracuseStep 1890497 = 1417873) B1417873
theorem B1259715 : Blo 1258447 1259715 := bstep (se 1 (by rfl) ⟨944786, by rfl⟩ : syracuseStep 1259715 = 1889573) B1889573
theorem B1259731 : Blo 1258447 1259731 := bstep (se 1 (by rfl) ⟨944798, by rfl⟩ : syracuseStep 1259731 = 1889597) B1889597
theorem B1890515 : Blo 1258447 1890515 := bstep (se 1 (by rfl) ⟨1417886, by rfl⟩ : syracuseStep 1890515 = 2835773) B2835773
theorem B1259747 : Blo 1258447 1259747 := bstep (se 1 (by rfl) ⟨944810, by rfl⟩ : syracuseStep 1259747 = 1889621) B1889621
theorem B1890545 : Blo 1258447 1890545 := bstep (se 2 (by rfl) ⟨708954, by rfl⟩ : syracuseStep 1890545 = 1417909) B1417909
theorem B1259763 : Blo 1258447 1259763 := bstep (se 1 (by rfl) ⟨944822, by rfl⟩ : syracuseStep 1259763 = 1889645) B1889645
theorem B1259779 : Blo 1258447 1259779 := bstep (se 1 (by rfl) ⟨944834, by rfl⟩ : syracuseStep 1259779 = 1889669) B1889669
theorem B1890563 : Blo 1258447 1890563 := bstep (se 1 (by rfl) ⟨1417922, by rfl⟩ : syracuseStep 1890563 = 2835845) B2835845
theorem B1259795 : Blo 1258447 1259795 := bstep (se 1 (by rfl) ⟨944846, by rfl⟩ : syracuseStep 1259795 = 1889693) B1889693
theorem B1890593 : Blo 1258447 1890593 := bstep (se 2 (by rfl) ⟨708972, by rfl⟩ : syracuseStep 1890593 = 1417945) B1417945
theorem B1259811 : Blo 1258447 1259811 := bstep (se 1 (by rfl) ⟨944858, by rfl⟩ : syracuseStep 1259811 = 1889717) B1889717
theorem B1259827 : Blo 1258447 1259827 := bstep (se 1 (by rfl) ⟨944870, by rfl⟩ : syracuseStep 1259827 = 1889741) B1889741
theorem B1890611 : Blo 1258447 1890611 := bstep (se 1 (by rfl) ⟨1417958, by rfl⟩ : syracuseStep 1890611 = 2835917) B2835917
theorem B1259843 : Blo 1258447 1259843 := bstep (se 1 (by rfl) ⟨944882, by rfl⟩ : syracuseStep 1259843 = 1889765) B1889765
theorem B2873681 : Blo 1258447 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B1890641 : Blo 1258447 1890641 := bstep (se 2 (by rfl) ⟨708990, by rfl⟩ : syracuseStep 1890641 = 1417981) B1417981
theorem B1259859 : Blo 1258447 1259859 := bstep (se 1 (by rfl) ⟨944894, by rfl⟩ : syracuseStep 1259859 = 1889789) B1889789
theorem B1259875 : Blo 1258447 1259875 := bstep (se 1 (by rfl) ⟨944906, by rfl⟩ : syracuseStep 1259875 = 1889813) B1889813
theorem B1890659 : Blo 1258447 1890659 := bstep (se 1 (by rfl) ⟨1417994, by rfl⟩ : syracuseStep 1890659 = 2835989) B2835989
theorem B5380465 : Blo 1258447 5380465 := bstep (se 2 (by rfl) ⟨2017674, by rfl⟩ : syracuseStep 5380465 = 4035349) B4035349
theorem B1259891 : Blo 1258447 1259891 := bstep (se 1 (by rfl) ⟨944918, by rfl⟩ : syracuseStep 1259891 = 1889837) B1889837
theorem B1259907 : Blo 1258447 1259907 := bstep (se 1 (by rfl) ⟨944930, by rfl⟩ : syracuseStep 1259907 = 1889861) B1889861
theorem B2832785 : Blo 1258447 2832785 := bstep (se 2 (by rfl) ⟨1062294, by rfl⟩ : syracuseStep 2832785 = 2124589) B2124589
theorem B1259923 : Blo 1258447 1259923 := bstep (se 1 (by rfl) ⟨944942, by rfl⟩ : syracuseStep 1259923 = 1889885) B1889885
theorem B2832803 : Blo 1258447 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B1259939 : Blo 1258447 1259939 := bstep (se 1 (by rfl) ⟨944954, by rfl⟩ : syracuseStep 1259939 = 1889909) B1889909
theorem B1259955 : Blo 1258447 1259955 := bstep (se 1 (by rfl) ⟨944966, by rfl⟩ : syracuseStep 1259955 = 1889933) B1889933
theorem B2390467 : Blo 1258447 2390467 := bstep (se 1 (by rfl) ⟨1792850, by rfl⟩ : syracuseStep 2390467 = 3585701) B3585701
theorem B1259971 : Blo 1258447 1259971 := bstep (se 1 (by rfl) ⟨944978, by rfl⟩ : syracuseStep 1259971 = 1889957) B1889957
theorem B1259987 : Blo 1258447 1259987 := bstep (se 1 (by rfl) ⟨944990, by rfl⟩ : syracuseStep 1259987 = 1889981) B1889981
theorem B1260003 : Blo 1258447 1260003 := bstep (se 1 (by rfl) ⟨945002, by rfl⟩ : syracuseStep 1260003 = 1890005) B1890005
theorem B1260019 : Blo 1258447 1260019 := bstep (se 1 (by rfl) ⟨945014, by rfl⟩ : syracuseStep 1260019 = 1890029) B1890029
theorem B1260035 : Blo 1258447 1260035 := bstep (se 1 (by rfl) ⟨945026, by rfl⟩ : syracuseStep 1260035 = 1890053) B1890053
theorem B6380045 : Blo 1258447 6380045 := bstep (se 3 (by rfl) ⟨1196258, by rfl⟩ : syracuseStep 6380045 = 2392517) B2392517
theorem B1260051 : Blo 1258447 1260051 := bstep (se 1 (by rfl) ⟨945038, by rfl⟩ : syracuseStep 1260051 = 1890077) B1890077
theorem B1260067 : Blo 1258447 1260067 := bstep (se 1 (by rfl) ⟨945050, by rfl⟩ : syracuseStep 1260067 = 1890101) B1890101
theorem B6806065 : Blo 1258447 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B1260083 : Blo 1258447 1260083 := bstep (se 1 (by rfl) ⟨945062, by rfl⟩ : syracuseStep 1260083 = 1890125) B1890125
theorem B1792577 : Blo 1258447 1792577 := bstep (se 2 (by rfl) ⟨672216, by rfl⟩ : syracuseStep 1792577 = 1344433) B1344433
theorem B1260099 : Blo 1258447 1260099 := bstep (se 1 (by rfl) ⟨945074, by rfl⟩ : syracuseStep 1260099 = 1890149) B1890149
theorem B1260115 : Blo 1258447 1260115 := bstep (se 1 (by rfl) ⟨945086, by rfl⟩ : syracuseStep 1260115 = 1890173) B1890173
theorem B2390627 : Blo 1258447 2390627 := bstep (se 1 (by rfl) ⟨1792970, by rfl⟩ : syracuseStep 2390627 = 3585941) B3585941
theorem B1260131 : Blo 1258447 1260131 := bstep (se 1 (by rfl) ⟨945098, by rfl⟩ : syracuseStep 1260131 = 1890197) B1890197
theorem B1260147 : Blo 1258447 1260147 := bstep (se 1 (by rfl) ⟨945110, by rfl⟩ : syracuseStep 1260147 = 1890221) B1890221
theorem B1260163 : Blo 1258447 1260163 := bstep (se 1 (by rfl) ⟨945122, by rfl⟩ : syracuseStep 1260163 = 1890245) B1890245
theorem B1260179 : Blo 1258447 1260179 := bstep (se 1 (by rfl) ⟨945134, by rfl⟩ : syracuseStep 1260179 = 1890269) B1890269
theorem B1260195 : Blo 1258447 1260195 := bstep (se 1 (by rfl) ⟨945146, by rfl⟩ : syracuseStep 1260195 = 1890293) B1890293
theorem B4250285 : Blo 1258447 4250285 := bstep (se 3 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 4250285 = 1593857) B1593857
theorem B2833073 : Blo 1258447 2833073 := bstep (se 2 (by rfl) ⟨1062402, by rfl⟩ : syracuseStep 2833073 = 2124805) B2124805
theorem B1260211 : Blo 1258447 1260211 := bstep (se 1 (by rfl) ⟨945158, by rfl⟩ : syracuseStep 1260211 = 1890317) B1890317
theorem B1415875 : Blo 1258447 1415875 := bstep (se 1 (by rfl) ⟨1061906, by rfl⟩ : syracuseStep 1415875 = 2123813) B2123813
theorem B2833091 : Blo 1258447 2833091 := bstep (se 1 (by rfl) ⟨2124818, by rfl⟩ : syracuseStep 2833091 = 4249637) B4249637
theorem B1260227 : Blo 1258447 1260227 := bstep (se 1 (by rfl) ⟨945170, by rfl⟩ : syracuseStep 1260227 = 1890341) B1890341
theorem B1260243 : Blo 1258447 1260243 := bstep (se 1 (by rfl) ⟨945182, by rfl⟩ : syracuseStep 1260243 = 1890365) B1890365
theorem B4250339 : Blo 1258447 4250339 := bstep (se 1 (by rfl) ⟨3187754, by rfl⟩ : syracuseStep 4250339 = 6375509) B6375509
theorem B1260259 : Blo 1258447 1260259 := bstep (se 1 (by rfl) ⟨945194, by rfl⟩ : syracuseStep 1260259 = 1890389) B1890389
theorem B4782833 : Blo 1258447 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B1260275 : Blo 1258447 1260275 := bstep (se 1 (by rfl) ⟨945206, by rfl⟩ : syracuseStep 1260275 = 1890413) B1890413
theorem B1702657 : Blo 1258447 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B1260291 : Blo 1258447 1260291 := bstep (se 1 (by rfl) ⟨945218, by rfl⟩ : syracuseStep 1260291 = 1890437) B1890437
theorem B1260307 : Blo 1258447 1260307 := bstep (se 1 (by rfl) ⟨945230, by rfl⟩ : syracuseStep 1260307 = 1890461) B1890461
theorem B2267939 : Blo 1258447 2267939 := bstep (se 1 (by rfl) ⟨1700954, by rfl⟩ : syracuseStep 2267939 = 3401909) B3401909
theorem B1260323 : Blo 1258447 1260323 := bstep (se 1 (by rfl) ⟨945242, by rfl⟩ : syracuseStep 1260323 = 1890485) B1890485
theorem B6806321 : Blo 1258447 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B1702705 : Blo 1258447 1702705 := bstep (se 2 (by rfl) ⟨638514, by rfl⟩ : syracuseStep 1702705 = 1277029) B1277029
theorem B1260339 : Blo 1258447 1260339 := bstep (se 1 (by rfl) ⟨945254, by rfl⟩ : syracuseStep 1260339 = 1890509) B1890509
theorem B8616773 : Blo 1258447 8616773 := bstep (se 4 (by rfl) ⟨807822, by rfl⟩ : syracuseStep 8616773 = 1615645) B1615645
theorem B1260355 : Blo 1258447 1260355 := bstep (se 1 (by rfl) ⟨945266, by rfl⟩ : syracuseStep 1260355 = 1890533) B1890533
theorem B4848461 : Blo 1258447 4848461 := bstep (se 3 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 4848461 = 1818173) B1818173
theorem B1416019 : Blo 1258447 1416019 := bstep (se 1 (by rfl) ⟨1062014, by rfl⟩ : syracuseStep 1416019 = 2124029) B2124029
theorem B1260371 : Blo 1258447 1260371 := bstep (se 1 (by rfl) ⟨945278, by rfl⟩ : syracuseStep 1260371 = 1890557) B1890557
theorem B3185507 : Blo 1258447 3185507 := bstep (se 1 (by rfl) ⟨2389130, by rfl⟩ : syracuseStep 3185507 = 4778261) B4778261
theorem B1260387 : Blo 1258447 1260387 := bstep (se 1 (by rfl) ⟨945290, by rfl⟩ : syracuseStep 1260387 = 1890581) B1890581
theorem B1260403 : Blo 1258447 1260403 := bstep (se 1 (by rfl) ⟨945302, by rfl⟩ : syracuseStep 1260403 = 1890605) B1890605
theorem B1260419 : Blo 1258447 1260419 := bstep (se 1 (by rfl) ⟨945314, by rfl⟩ : syracuseStep 1260419 = 1890629) B1890629
theorem B48380813 : Blo 1258447 48380813 := bstep (se 3 (by rfl) ⟨9071402, by rfl⟩ : syracuseStep 48380813 = 18142805) B18142805
theorem B1260435 : Blo 1258447 1260435 := bstep (se 1 (by rfl) ⟨945326, by rfl⟩ : syracuseStep 1260435 = 1890653) B1890653
theorem B4307921 : Blo 1258447 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B2833361 : Blo 1258447 2833361 := bstep (se 2 (by rfl) ⟨1062510, by rfl⟩ : syracuseStep 2833361 = 2125021) B2125021
theorem B1416163 : Blo 1258447 1416163 := bstep (se 1 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 1416163 = 2124245) B2124245
theorem B2833379 : Blo 1258447 2833379 := bstep (se 1 (by rfl) ⟨2125034, by rfl⟩ : syracuseStep 2833379 = 4250069) B4250069
theorem B4250609 : Blo 1258447 4250609 := bstep (se 2 (by rfl) ⟨1593978, by rfl⟩ : syracuseStep 4250609 = 3187957) B3187957
theorem B4037681 : Blo 1258447 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B15531061 : Blo 1258447 15531061 := bstep (se 5 (by rfl) ⟨728018, by rfl⟩ : syracuseStep 15531061 = 1456037) B1456037
theorem B1793107 : Blo 1258447 1793107 := bstep (se 1 (by rfl) ⟨1344830, by rfl⟩ : syracuseStep 1793107 = 2689661) B2689661
theorem B1416307 : Blo 1258447 1416307 := bstep (se 1 (by rfl) ⟨1062230, by rfl⟩ : syracuseStep 1416307 = 2124461) B2124461
theorem B3636355 : Blo 1258447 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B14744717 : Blo 1258447 14744717 := bstep (se 3 (by rfl) ⟨2764634, by rfl⟩ : syracuseStep 14744717 = 5529269) B5529269
theorem B8617157 : Blo 1258447 8617157 := bstep (se 4 (by rfl) ⟨807858, by rfl⟩ : syracuseStep 8617157 = 1615717) B1615717
theorem B6372593 : Blo 1258447 6372593 := bstep (se 2 (by rfl) ⟨2389722, by rfl⟩ : syracuseStep 6372593 = 4779445) B4779445
theorem B2833649 : Blo 1258447 2833649 := bstep (se 2 (by rfl) ⟨1062618, by rfl⟩ : syracuseStep 2833649 = 2125237) B2125237
theorem B1416451 : Blo 1258447 1416451 := bstep (se 1 (by rfl) ⟨1062338, by rfl⟩ : syracuseStep 1416451 = 2124677) B2124677
theorem B2833667 : Blo 1258447 2833667 := bstep (se 1 (by rfl) ⟨2125250, by rfl⟩ : syracuseStep 2833667 = 4250501) B4250501
theorem B3587341 : Blo 1258447 3587341 := bstep (se 3 (by rfl) ⟨672626, by rfl⟩ : syracuseStep 3587341 = 1345253) B1345253
theorem B1416595 : Blo 1258447 1416595 := bstep (se 1 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 1416595 = 2124893) B2124893
theorem B1793443 : Blo 1258447 1793443 := bstep (se 1 (by rfl) ⟨1345082, by rfl⟩ : syracuseStep 1793443 = 2690165) B2690165
theorem B7167437 : Blo 1258447 7167437 := bstep (se 3 (by rfl) ⟨1343894, by rfl⟩ : syracuseStep 7167437 = 2687789) B2687789
theorem B4251149 : Blo 1258447 4251149 := bstep (se 3 (by rfl) ⟨797090, by rfl⟩ : syracuseStep 4251149 = 1594181) B1594181
theorem B2833937 : Blo 1258447 2833937 := bstep (se 2 (by rfl) ⟨1062726, by rfl⟩ : syracuseStep 2833937 = 2125453) B2125453
theorem B1416739 : Blo 1258447 1416739 := bstep (se 1 (by rfl) ⟨1062554, by rfl⟩ : syracuseStep 1416739 = 2125109) B2125109
theorem B2833955 : Blo 1258447 2833955 := bstep (se 1 (by rfl) ⟨2125466, by rfl⟩ : syracuseStep 2833955 = 4250933) B4250933
theorem B7175729 : Blo 1258447 7175729 := bstep (se 2 (by rfl) ⟨2690898, by rfl⟩ : syracuseStep 7175729 = 5381797) B5381797
theorem B4251203 : Blo 1258447 4251203 := bstep (se 1 (by rfl) ⟨3188402, by rfl⟩ : syracuseStep 4251203 = 6376805) B6376805
theorem B8740493 : Blo 1258447 8740493 := bstep (se 3 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 8740493 = 3277685) B3277685
theorem B2391697 : Blo 1258447 2391697 := bstep (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) B1793773
theorem B1416883 : Blo 1258447 1416883 := bstep (se 1 (by rfl) ⟨1062662, by rfl⟩ : syracuseStep 1416883 = 2125325) B2125325
theorem B4087523 : Blo 1258447 4087523 := bstep (se 1 (by rfl) ⟨3065642, by rfl⟩ : syracuseStep 4087523 = 6131285) B6131285
theorem B3186449 : Blo 1258447 3186449 := bstep (se 2 (by rfl) ⟨1194918, by rfl⟩ : syracuseStep 3186449 = 2389837) B2389837
theorem B2834225 : Blo 1258447 2834225 := bstep (se 2 (by rfl) ⟨1062834, by rfl⟩ : syracuseStep 2834225 = 2125669) B2125669
theorem B3186499 : Blo 1258447 3186499 := bstep (se 1 (by rfl) ⟨2389874, by rfl⟩ : syracuseStep 3186499 = 4779749) B4779749
theorem B1417027 : Blo 1258447 1417027 := bstep (se 1 (by rfl) ⟨1062770, by rfl⟩ : syracuseStep 1417027 = 2125541) B2125541
theorem B2834243 : Blo 1258447 2834243 := bstep (se 1 (by rfl) ⟨2125682, by rfl⟩ : syracuseStep 2834243 = 4251365) B4251365
theorem B4251473 : Blo 1258447 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B5742541 : Blo 1258447 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B3186641 : Blo 1258447 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B1794001 : Blo 1258447 1794001 := bstep (se 2 (by rfl) ⟨672750, by rfl⟩ : syracuseStep 1794001 = 1345501) B1345501
theorem B1417171 : Blo 1258447 1417171 := bstep (se 1 (by rfl) ⟨1062878, by rfl⟩ : syracuseStep 1417171 = 2125757) B2125757
theorem B1794035 : Blo 1258447 1794035 := bstep (se 1 (by rfl) ⟨1345526, by rfl⟩ : syracuseStep 1794035 = 2691053) B2691053
theorem B2834585 : Blo 1258447 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B1417387 : Blo 1258447 1417387 := bstep (se 1 (by rfl) ⟨1063040, by rfl⟩ : syracuseStep 1417387 = 2126081) B2126081
theorem B3588275 : Blo 1258447 3588275 := bstep (se 1 (by rfl) ⟨2691206, by rfl⟩ : syracuseStep 3588275 = 5382413) B5382413
theorem B4251851 : Blo 1258447 4251851 := bstep (se 1 (by rfl) ⟨3188888, by rfl⟩ : syracuseStep 4251851 = 6377777) B6377777
theorem B2392267 : Blo 1258447 2392267 := bstep (se 1 (by rfl) ⟨1794200, by rfl⟩ : syracuseStep 2392267 = 3588401) B3588401
theorem B3735773 : Blo 1258447 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B2834675 : Blo 1258447 2834675 := bstep (se 1 (by rfl) ⟨2126006, by rfl⟩ : syracuseStep 2834675 = 4252013) B4252013
theorem B2834711 : Blo 1258447 2834711 := bstep (se 1 (by rfl) ⟨2126033, by rfl⟩ : syracuseStep 2834711 = 4252067) B4252067
theorem B1417495 : Blo 1258447 1417495 := bstep (se 1 (by rfl) ⟨1063121, by rfl⟩ : syracuseStep 1417495 = 2126243) B2126243
theorem B5243287 : Blo 1258447 5243287 := bstep (se 1 (by rfl) ⟨3932465, by rfl⟩ : syracuseStep 5243287 = 7864931) B7864931
theorem B3187147 : Blo 1258447 3187147 := bstep (se 1 (by rfl) ⟨2390360, by rfl⟩ : syracuseStep 3187147 = 4780721) B4780721
theorem B2834891 : Blo 1258447 2834891 := bstep (se 1 (by rfl) ⟨2126168, by rfl⟩ : syracuseStep 2834891 = 4252337) B4252337
theorem B1417675 : Blo 1258447 1417675 := bstep (se 1 (by rfl) ⟨1063256, by rfl⟩ : syracuseStep 1417675 = 2126513) B2126513
theorem B4252121 : Blo 1258447 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B4538845 : Blo 1258447 4538845 := bstep (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) B1702067
theorem B2834945 : Blo 1258447 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B1417783 : Blo 1258447 1417783 := bstep (se 1 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 1417783 = 2126675) B2126675
theorem B3187289 : Blo 1258447 3187289 := bstep (se 2 (by rfl) ⟨1195233, by rfl⟩ : syracuseStep 3187289 = 2390467) B2390467
theorem B2392715 : Blo 1258447 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B1344151 : Blo 1258447 1344151 := bstep (se 1 (by rfl) ⟨1008113, by rfl⟩ : syracuseStep 1344151 = 2016227) B2016227
theorem B10756759 : Blo 1258447 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B4784791 : Blo 1258447 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B2835161 : Blo 1258447 2835161 := bstep (se 2 (by rfl) ⟨1063185, by rfl⟩ : syracuseStep 2835161 = 2126371) B2126371
theorem B1417963 : Blo 1258447 1417963 := bstep (se 1 (by rfl) ⟨1063472, by rfl⟩ : syracuseStep 1417963 = 2126945) B2126945
theorem B2687755 : Blo 1258447 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B2835251 : Blo 1258447 2835251 := bstep (se 1 (by rfl) ⟨2126438, by rfl⟩ : syracuseStep 2835251 = 4252877) B4252877
theorem B2835287 : Blo 1258447 2835287 := bstep (se 1 (by rfl) ⟨2126465, by rfl⟩ : syracuseStep 2835287 = 4252931) B4252931
theorem B22397795 : Blo 1258447 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B2270209 : Blo 1258447 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B2835467 : Blo 1258447 2835467 := bstep (se 1 (by rfl) ⟨2126600, by rfl⟩ : syracuseStep 2835467 = 4253201) B4253201
theorem B2270273 : Blo 1258447 2270273 := bstep (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) B1702705
theorem B2835521 : Blo 1258447 2835521 := bstep (se 2 (by rfl) ⟨1063320, by rfl⟩ : syracuseStep 2835521 = 2126641) B2126641
theorem B4252823 : Blo 1258447 4252823 := bstep (se 1 (by rfl) ⟨3189617, by rfl⟩ : syracuseStep 4252823 = 6379235) B6379235
theorem B2155801 : Blo 1258447 2155801 := bstep (se 2 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 2155801 = 1616851) B1616851
theorem B2835737 : Blo 1258447 2835737 := bstep (se 2 (by rfl) ⟨1063401, by rfl⟩ : syracuseStep 2835737 = 2126803) B2126803
theorem B2835827 : Blo 1258447 2835827 := bstep (se 1 (by rfl) ⟨2126870, by rfl⟩ : syracuseStep 2835827 = 4253741) B4253741
theorem B9823639 : Blo 1258447 9823639 := bstep (se 1 (by rfl) ⟨7367729, by rfl⟩ : syracuseStep 9823639 = 14735459) B14735459
theorem B3188119 : Blo 1258447 3188119 := bstep (se 1 (by rfl) ⟨2391089, by rfl⟩ : syracuseStep 3188119 = 4782179) B4782179
theorem B2835863 : Blo 1258447 2835863 := bstep (se 1 (by rfl) ⟨2126897, by rfl⟩ : syracuseStep 2835863 = 4253795) B4253795
theorem B4785581 : Blo 1258447 4785581 := bstep (se 3 (by rfl) ⟨897296, by rfl⟩ : syracuseStep 4785581 = 1794593) B1794593
theorem B1344971 : Blo 1258447 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B2688473 : Blo 1258447 2688473 := bstep (se 2 (by rfl) ⟨1008177, by rfl⟩ : syracuseStep 2688473 = 2016355) B2016355
theorem B36308573 : Blo 1258447 36308573 := bstep (se 3 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 36308573 = 13615715) B13615715
theorem B8070749 : Blo 1258447 8070749 := bstep (se 3 (by rfl) ⟨1513265, by rfl⟩ : syracuseStep 8070749 = 3026531) B3026531
theorem B4253363 : Blo 1258447 4253363 := bstep (se 1 (by rfl) ⟨3190022, by rfl⟩ : syracuseStep 4253363 = 6380045) B6380045
theorem B6375185 : Blo 1258447 6375185 := bstep (se 2 (by rfl) ⟨2390694, by rfl⟩ : syracuseStep 6375185 = 4781389) B4781389
theorem B5375767 : Blo 1258447 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B3188555 : Blo 1258447 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B5744515 : Blo 1258447 5744515 := bstep (se 1 (by rfl) ⟨4308386, by rfl⟩ : syracuseStep 5744515 = 8616773) B8616773
theorem B2123671 : Blo 1258447 2123671 := bstep (se 1 (by rfl) ⟨1592753, by rfl⟩ : syracuseStep 2123671 = 3185507) B3185507
theorem B32253875 : Blo 1258447 32253875 := bstep (se 1 (by rfl) ⟨24190406, by rfl⟩ : syracuseStep 32253875 = 48380813) B48380813
theorem B14337971 : Blo 1258447 14337971 := bstep (se 1 (by rfl) ⟨10753478, by rfl⟩ : syracuseStep 14337971 = 21506957) B21506957
theorem B6375347 : Blo 1258447 6375347 := bstep (se 1 (by rfl) ⟨4781510, by rfl⟩ : syracuseStep 6375347 = 9563021) B9563021
theorem B4253633 : Blo 1258447 4253633 := bstep (se 2 (by rfl) ⟨1595112, by rfl⟩ : syracuseStep 4253633 = 3190225) B3190225
theorem B4310987 : Blo 1258447 4310987 := bstep (se 1 (by rfl) ⟨3233240, by rfl⟩ : syracuseStep 4310987 = 6466481) B6466481
theorem B2688985 : Blo 1258447 2688985 := bstep (se 2 (by rfl) ⟨1008369, by rfl⟩ : syracuseStep 2688985 = 2016739) B2016739
theorem B2689139 : Blo 1258447 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B5744771 : Blo 1258447 5744771 := bstep (se 1 (by rfl) ⟨4308578, by rfl⟩ : syracuseStep 5744771 = 8617157) B8617157
theorem B3188929 : Blo 1258447 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B2017559 : Blo 1258447 2017559 := bstep (se 1 (by rfl) ⟨1513169, by rfl⟩ : syracuseStep 2017559 = 3026339) B3026339
theorem B4778291 : Blo 1258447 4778291 := bstep (se 1 (by rfl) ⟨3583718, by rfl⟩ : syracuseStep 4778291 = 7167437) B7167437
theorem B5826995 : Blo 1258447 5826995 := bstep (se 1 (by rfl) ⟨4370246, by rfl⟩ : syracuseStep 5826995 = 8740493) B8740493
theorem B6048217 : Blo 1258447 6048217 := bstep (se 2 (by rfl) ⟨2268081, by rfl⟩ : syracuseStep 6048217 = 4536163) B4536163
theorem B2124299 : Blo 1258447 2124299 := bstep (se 1 (by rfl) ⟨1593224, by rfl⟩ : syracuseStep 2124299 = 3186449) B3186449
theorem B7170605 : Blo 1258447 7170605 := bstep (se 3 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 7170605 = 2688977) B2688977
theorem B2017867 : Blo 1258447 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B2124427 : Blo 1258447 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B3189527 : Blo 1258447 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B2124569 : Blo 1258447 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B2018123 : Blo 1258447 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B2124697 : Blo 1258447 2124697 := bstep (se 2 (by rfl) ⟨796761, by rfl⟩ : syracuseStep 2124697 = 1593523) B1593523
theorem B4778945 : Blo 1258447 4778945 := bstep (se 2 (by rfl) ⟨1792104, by rfl⟩ : syracuseStep 4778945 = 3584209) B3584209
theorem B2690113 : Blo 1258447 2690113 := bstep (se 2 (by rfl) ⟨1008792, by rfl⟩ : syracuseStep 2690113 = 2017585) B2017585
theorem B8621149 : Blo 1258447 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B10767491 : Blo 1258447 10767491 := bstep (se 1 (by rfl) ⟨8075618, by rfl⟩ : syracuseStep 10767491 = 16151237) B16151237
theorem B18656407 : Blo 1258447 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B4541699 : Blo 1258447 4541699 := bstep (se 1 (by rfl) ⟨3406274, by rfl⟩ : syracuseStep 4541699 = 6812549) B6812549
theorem B2870615 : Blo 1258447 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B14339429 : Blo 1258447 14339429 := bstep (se 4 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 14339429 = 2688643) B2688643
theorem B2690455 : Blo 1258447 2690455 := bstep (se 1 (by rfl) ⟨2017841, by rfl⟩ : syracuseStep 2690455 = 4035683) B4035683
theorem B1592779 : Blo 1258447 1592779 := bstep (se 1 (by rfl) ⟨1194584, by rfl⟩ : syracuseStep 1592779 = 2389169) B2389169
theorem B2125271 : Blo 1258447 2125271 := bstep (se 1 (by rfl) ⟨1593953, by rfl⟩ : syracuseStep 2125271 = 3187907) B3187907
theorem B1887755 : Blo 1258447 1887755 := bstep (se 1 (by rfl) ⟨1415816, by rfl⟩ : syracuseStep 1887755 = 2831633) B2831633
theorem B1887767 : Blo 1258447 1887767 := bstep (se 1 (by rfl) ⟨1415825, by rfl⟩ : syracuseStep 1887767 = 2831651) B2831651
theorem B3190337 : Blo 1258447 3190337 := bstep (se 2 (by rfl) ⟨1196376, by rfl⟩ : syracuseStep 3190337 = 2392753) B2392753
theorem B2125399 : Blo 1258447 2125399 := bstep (se 1 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 2125399 = 3188099) B3188099
theorem B1887833 : Blo 1258447 1887833 := bstep (se 2 (by rfl) ⟨707937, by rfl⟩ : syracuseStep 1887833 = 1415875) B1415875
theorem B5746265 : Blo 1258447 5746265 := bstep (se 2 (by rfl) ⟨2154849, by rfl⟩ : syracuseStep 5746265 = 4309699) B4309699
theorem B4542103 : Blo 1258447 4542103 := bstep (se 1 (by rfl) ⟨3406577, by rfl⟩ : syracuseStep 4542103 = 6813155) B6813155
theorem B1887947 : Blo 1258447 1887947 := bstep (se 1 (by rfl) ⟨1415960, by rfl⟩ : syracuseStep 1887947 = 2831921) B2831921
theorem B1887959 : Blo 1258447 1887959 := bstep (se 1 (by rfl) ⟨1415969, by rfl⟩ : syracuseStep 1887959 = 2831939) B2831939
theorem B1593047 : Blo 1258447 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B4247261 : Blo 1258447 4247261 := bstep (se 3 (by rfl) ⟨796361, by rfl⟩ : syracuseStep 4247261 = 1592723) B1592723
theorem B1888025 : Blo 1258447 1888025 := bstep (se 2 (by rfl) ⟨708009, by rfl⟩ : syracuseStep 1888025 = 1416019) B1416019
theorem B6377291 : Blo 1258447 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B2690891 : Blo 1258447 2690891 := bstep (se 1 (by rfl) ⟨2018168, by rfl⟩ : syracuseStep 2690891 = 4036337) B4036337
theorem B1888139 : Blo 1258447 1888139 := bstep (se 1 (by rfl) ⟨1416104, by rfl⟩ : syracuseStep 1888139 = 2832209) B2832209
theorem B1888151 : Blo 1258447 1888151 := bstep (se 1 (by rfl) ⟨1416113, by rfl⟩ : syracuseStep 1888151 = 2832227) B2832227
theorem B1888217 : Blo 1258447 1888217 := bstep (se 2 (by rfl) ⟨708081, by rfl⟩ : syracuseStep 1888217 = 1416163) B1416163
theorem B1888331 : Blo 1258447 1888331 := bstep (se 1 (by rfl) ⟨1416248, by rfl⟩ : syracuseStep 1888331 = 2832497) B2832497
theorem B1888343 : Blo 1258447 1888343 := bstep (se 1 (by rfl) ⟨1416257, by rfl⟩ : syracuseStep 1888343 = 2832515) B2832515
theorem B1888409 : Blo 1258447 1888409 := bstep (se 2 (by rfl) ⟨708153, by rfl⟩ : syracuseStep 1888409 = 1416307) B1416307
theorem B4780205 : Blo 1258447 4780205 := bstep (se 3 (by rfl) ⟨896288, by rfl⟩ : syracuseStep 4780205 = 1792577) B1792577
theorem B3633331 : Blo 1258447 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B4780235 : Blo 1258447 4780235 := bstep (se 1 (by rfl) ⟨3585176, by rfl⟩ : syracuseStep 4780235 = 7170353) B7170353
theorem B2126027 : Blo 1258447 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B1888523 : Blo 1258447 1888523 := bstep (se 1 (by rfl) ⟨1416392, by rfl⟩ : syracuseStep 1888523 = 2832785) B2832785
theorem B1888535 : Blo 1258447 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B2126155 : Blo 1258447 2126155 := bstep (se 1 (by rfl) ⟨1594616, by rfl⟩ : syracuseStep 2126155 = 3189233) B3189233
theorem B1888601 : Blo 1258447 1888601 := bstep (se 2 (by rfl) ⟨708225, by rfl⟩ : syracuseStep 1888601 = 1416451) B1416451
theorem B3830105 : Blo 1258447 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B1593751 : Blo 1258447 1593751 := bstep (se 1 (by rfl) ⟨1195313, by rfl⟩ : syracuseStep 1593751 = 2390627) B2390627
theorem B1888715 : Blo 1258447 1888715 := bstep (se 1 (by rfl) ⟨1416536, by rfl⟩ : syracuseStep 1888715 = 2833073) B2833073
theorem B1888727 : Blo 1258447 1888727 := bstep (se 1 (by rfl) ⟨1416545, by rfl⟩ : syracuseStep 1888727 = 2833091) B2833091
theorem B2126297 : Blo 1258447 2126297 := bstep (se 2 (by rfl) ⟨797361, by rfl⟩ : syracuseStep 2126297 = 1594723) B1594723
theorem B13627865 : Blo 1258447 13627865 := bstep (se 2 (by rfl) ⟨5110449, by rfl⟩ : syracuseStep 13627865 = 10220899) B10220899
theorem B21533201 : Blo 1258447 21533201 := bstep (se 2 (by rfl) ⟨8074950, by rfl⟩ : syracuseStep 21533201 = 16149901) B16149901
theorem B1511959 : Blo 1258447 1511959 := bstep (se 1 (by rfl) ⟨1133969, by rfl⟩ : syracuseStep 1511959 = 2267939) B2267939
theorem B1888793 : Blo 1258447 1888793 := bstep (se 2 (by rfl) ⟨708297, by rfl⟩ : syracuseStep 1888793 = 1416595) B1416595
theorem B3232307 : Blo 1258447 3232307 := bstep (se 1 (by rfl) ⟨2424230, by rfl⟩ : syracuseStep 3232307 = 4848461) B4848461
theorem B2126425 : Blo 1258447 2126425 := bstep (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) B1594819
theorem B5378653 : Blo 1258447 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B2871947 : Blo 1258447 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B1888907 : Blo 1258447 1888907 := bstep (se 1 (by rfl) ⟨1416680, by rfl⟩ : syracuseStep 1888907 = 2833361) B2833361
theorem B1888919 : Blo 1258447 1888919 := bstep (se 1 (by rfl) ⟨1416689, by rfl⟩ : syracuseStep 1888919 = 2833379) B2833379
theorem B2691787 : Blo 1258447 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B1888985 : Blo 1258447 1888985 := bstep (se 2 (by rfl) ⟨708369, by rfl⟩ : syracuseStep 1888985 = 1416739) B1416739
theorem B9073453 : Blo 1258447 9073453 := bstep (se 3 (by rfl) ⟨1701272, by rfl⟩ : syracuseStep 9073453 = 3402545) B3402545
theorem B4248395 : Blo 1258447 4248395 := bstep (se 1 (by rfl) ⟨3186296, by rfl⟩ : syracuseStep 4248395 = 6372593) B6372593
theorem B1889099 : Blo 1258447 1889099 := bstep (se 1 (by rfl) ⟨1416824, by rfl⟩ : syracuseStep 1889099 = 2833649) B2833649
theorem B1889111 : Blo 1258447 1889111 := bstep (se 1 (by rfl) ⟨1416833, by rfl⟩ : syracuseStep 1889111 = 2833667) B2833667
theorem B4780889 : Blo 1258447 4780889 := bstep (se 2 (by rfl) ⟨1792833, by rfl⟩ : syracuseStep 4780889 = 3585667) B3585667
theorem B7172995 : Blo 1258447 7172995 := bstep (se 1 (by rfl) ⟨5379746, by rfl⟩ : syracuseStep 7172995 = 10759493) B10759493
theorem B1889177 : Blo 1258447 1889177 := bstep (se 2 (by rfl) ⟨708441, by rfl⟩ : syracuseStep 1889177 = 1416883) B1416883
theorem B1258455 : Blo 1258447 1258455 := bstep (se 1 (by rfl) ⟨943841, by rfl⟩ : syracuseStep 1258455 = 1887683) B1887683
theorem B1258475 : Blo 1258447 1258475 := bstep (se 1 (by rfl) ⟨943856, by rfl⟩ : syracuseStep 1258475 = 1887713) B1887713
theorem B1258487 : Blo 1258447 1258487 := bstep (se 1 (by rfl) ⟨943865, by rfl⟩ : syracuseStep 1258487 = 1887731) B1887731
theorem B1258507 : Blo 1258447 1258507 := bstep (se 1 (by rfl) ⟨943880, by rfl⟩ : syracuseStep 1258507 = 1887761) B1887761
theorem B1889291 : Blo 1258447 1889291 := bstep (se 1 (by rfl) ⟨1416968, by rfl⟩ : syracuseStep 1889291 = 2833937) B2833937
theorem B1258519 : Blo 1258447 1258519 := bstep (se 1 (by rfl) ⟨943889, by rfl⟩ : syracuseStep 1258519 = 1887779) B1887779
theorem B1889303 : Blo 1258447 1889303 := bstep (se 1 (by rfl) ⟨1416977, by rfl⟩ : syracuseStep 1889303 = 2833955) B2833955
theorem B1258539 : Blo 1258447 1258539 := bstep (se 1 (by rfl) ⟨943904, by rfl⟩ : syracuseStep 1258539 = 1887809) B1887809
theorem B1258551 : Blo 1258447 1258551 := bstep (se 1 (by rfl) ⟨943913, by rfl⟩ : syracuseStep 1258551 = 1887827) B1887827
theorem B30626885 : Blo 1258447 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B1258571 : Blo 1258447 1258571 := bstep (se 1 (by rfl) ⟨943928, by rfl⟩ : syracuseStep 1258571 = 1887857) B1887857
theorem B1258583 : Blo 1258447 1258583 := bstep (se 1 (by rfl) ⟨943937, by rfl⟩ : syracuseStep 1258583 = 1887875) B1887875
theorem B4248665 : Blo 1258447 4248665 := bstep (se 2 (by rfl) ⟨1593249, by rfl⟩ : syracuseStep 4248665 = 3186499) B3186499
theorem B1889369 : Blo 1258447 1889369 := bstep (se 2 (by rfl) ⟨708513, by rfl⟩ : syracuseStep 1889369 = 1417027) B1417027
theorem B1258603 : Blo 1258447 1258603 := bstep (se 1 (by rfl) ⟨943952, by rfl⟩ : syracuseStep 1258603 = 1887905) B1887905
theorem B1258615 : Blo 1258447 1258615 := bstep (se 1 (by rfl) ⟨943961, by rfl⟩ : syracuseStep 1258615 = 1887923) B1887923
theorem B1258635 : Blo 1258447 1258635 := bstep (se 1 (by rfl) ⟨943976, by rfl⟩ : syracuseStep 1258635 = 1887953) B1887953
theorem B1258647 : Blo 1258447 1258647 := bstep (se 1 (by rfl) ⟨943985, by rfl⟩ : syracuseStep 1258647 = 1887971) B1887971
theorem B2725015 : Blo 1258447 2725015 := bstep (se 1 (by rfl) ⟨2043761, by rfl⟩ : syracuseStep 2725015 = 4087523) B4087523
theorem B4781207 : Blo 1258447 4781207 := bstep (se 1 (by rfl) ⟨3585905, by rfl⟩ : syracuseStep 4781207 = 7171811) B7171811
theorem B2126999 : Blo 1258447 2126999 := bstep (se 1 (by rfl) ⟨1595249, by rfl⟩ : syracuseStep 2126999 = 3190499) B3190499
theorem B1258667 : Blo 1258447 1258667 := bstep (se 1 (by rfl) ⟨944000, by rfl⟩ : syracuseStep 1258667 = 1888001) B1888001
theorem B1258679 : Blo 1258447 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B1258699 : Blo 1258447 1258699 := bstep (se 1 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 1258699 = 1888049) B1888049
theorem B1889483 : Blo 1258447 1889483 := bstep (se 1 (by rfl) ⟨1417112, by rfl⟩ : syracuseStep 1889483 = 2834225) B2834225
theorem B1258711 : Blo 1258447 1258711 := bstep (se 1 (by rfl) ⟨944033, by rfl⟩ : syracuseStep 1258711 = 1888067) B1888067
theorem B1889495 : Blo 1258447 1889495 := bstep (se 1 (by rfl) ⟨1417121, by rfl⟩ : syracuseStep 1889495 = 2834243) B2834243
theorem B1258731 : Blo 1258447 1258731 := bstep (se 1 (by rfl) ⟨944048, by rfl⟩ : syracuseStep 1258731 = 1888097) B1888097
theorem B1258743 : Blo 1258447 1258743 := bstep (se 1 (by rfl) ⟨944057, by rfl⟩ : syracuseStep 1258743 = 1888115) B1888115
theorem B1258763 : Blo 1258447 1258763 := bstep (se 1 (by rfl) ⟨944072, by rfl⟩ : syracuseStep 1258763 = 1888145) B1888145
theorem B1258775 : Blo 1258447 1258775 := bstep (se 1 (by rfl) ⟨944081, by rfl⟩ : syracuseStep 1258775 = 1888163) B1888163
theorem B1889561 : Blo 1258447 1889561 := bstep (se 2 (by rfl) ⟨708585, by rfl⟩ : syracuseStep 1889561 = 1417171) B1417171
theorem B1258795 : Blo 1258447 1258795 := bstep (se 1 (by rfl) ⟨944096, by rfl⟩ : syracuseStep 1258795 = 1888193) B1888193
theorem B8074541 : Blo 1258447 8074541 := bstep (se 3 (by rfl) ⟨1513976, by rfl⟩ : syracuseStep 8074541 = 3027953) B3027953
theorem B1258807 : Blo 1258447 1258807 := bstep (se 1 (by rfl) ⟨944105, by rfl⟩ : syracuseStep 1258807 = 1888211) B1888211
theorem B2389313 : Blo 1258447 2389313 := bstep (se 2 (by rfl) ⟨895992, by rfl⟩ : syracuseStep 2389313 = 1791985) B1791985
theorem B1258827 : Blo 1258447 1258827 := bstep (se 1 (by rfl) ⟨944120, by rfl⟩ : syracuseStep 1258827 = 1888241) B1888241
theorem B2725207 : Blo 1258447 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B1258839 : Blo 1258447 1258839 := bstep (se 1 (by rfl) ⟨944129, by rfl⟩ : syracuseStep 1258839 = 1888259) B1888259
theorem B2831705 : Blo 1258447 2831705 := bstep (se 2 (by rfl) ⟨1061889, by rfl⟩ : syracuseStep 2831705 = 2123779) B2123779
theorem B1258859 : Blo 1258447 1258859 := bstep (se 1 (by rfl) ⟨944144, by rfl⟩ : syracuseStep 1258859 = 1888289) B1888289
theorem B1258871 : Blo 1258447 1258871 := bstep (se 1 (by rfl) ⟨944153, by rfl⟩ : syracuseStep 1258871 = 1888307) B1888307
theorem B1258891 : Blo 1258447 1258891 := bstep (se 1 (by rfl) ⟨944168, by rfl⟩ : syracuseStep 1258891 = 1888337) B1888337
theorem B1889675 : Blo 1258447 1889675 := bstep (se 1 (by rfl) ⟨1417256, by rfl⟩ : syracuseStep 1889675 = 2834513) B2834513
theorem B5379473 : Blo 1258447 5379473 := bstep (se 2 (by rfl) ⟨2017302, by rfl⟩ : syracuseStep 5379473 = 4034605) B4034605
theorem B30651797 : Blo 1258447 30651797 := bstep (se 6 (by rfl) ⟨718401, by rfl⟩ : syracuseStep 30651797 = 1436803) B1436803
theorem B1258903 : Blo 1258447 1258903 := bstep (se 1 (by rfl) ⟨944177, by rfl⟩ : syracuseStep 1258903 = 1888355) B1888355
theorem B1889687 : Blo 1258447 1889687 := bstep (se 1 (by rfl) ⟨1417265, by rfl⟩ : syracuseStep 1889687 = 2834531) B2834531
theorem B1258923 : Blo 1258447 1258923 := bstep (se 1 (by rfl) ⟨944192, by rfl⟩ : syracuseStep 1258923 = 1888385) B1888385
theorem B2831795 : Blo 1258447 2831795 := bstep (se 1 (by rfl) ⟨2123846, by rfl⟩ : syracuseStep 2831795 = 4247693) B4247693
theorem B1258935 : Blo 1258447 1258935 := bstep (se 1 (by rfl) ⟨944201, by rfl⟩ : syracuseStep 1258935 = 1888403) B1888403
theorem B1258955 : Blo 1258447 1258955 := bstep (se 1 (by rfl) ⟨944216, by rfl⟩ : syracuseStep 1258955 = 1888433) B1888433
theorem B2831831 : Blo 1258447 2831831 := bstep (se 1 (by rfl) ⟨2123873, by rfl⟩ : syracuseStep 2831831 = 4247747) B4247747
theorem B1258967 : Blo 1258447 1258967 := bstep (se 1 (by rfl) ⟨944225, by rfl⟩ : syracuseStep 1258967 = 1888451) B1888451
theorem B1889753 : Blo 1258447 1889753 := bstep (se 2 (by rfl) ⟨708657, by rfl⟩ : syracuseStep 1889753 = 1417315) B1417315
theorem B1258987 : Blo 1258447 1258987 := bstep (se 1 (by rfl) ⟨944240, by rfl⟩ : syracuseStep 1258987 = 1888481) B1888481
theorem B1258999 : Blo 1258447 1258999 := bstep (se 1 (by rfl) ⟨944249, by rfl⟩ : syracuseStep 1258999 = 1888499) B1888499
theorem B1259019 : Blo 1258447 1259019 := bstep (se 1 (by rfl) ⟨944264, by rfl⟩ : syracuseStep 1259019 = 1888529) B1888529
theorem B1259031 : Blo 1258447 1259031 := bstep (se 1 (by rfl) ⟨944273, by rfl⟩ : syracuseStep 1259031 = 1888547) B1888547
theorem B1259051 : Blo 1258447 1259051 := bstep (se 1 (by rfl) ⟨944288, by rfl⟩ : syracuseStep 1259051 = 1888577) B1888577
theorem B1259063 : Blo 1258447 1259063 := bstep (se 1 (by rfl) ⟨944297, by rfl⟩ : syracuseStep 1259063 = 1888595) B1888595
theorem B6379073 : Blo 1258447 6379073 := bstep (se 2 (by rfl) ⟨2392152, by rfl⟩ : syracuseStep 6379073 = 4784305) B4784305
theorem B1259083 : Blo 1258447 1259083 := bstep (se 1 (by rfl) ⟨944312, by rfl⟩ : syracuseStep 1259083 = 1888625) B1888625
theorem B1889867 : Blo 1258447 1889867 := bstep (se 1 (by rfl) ⟨1417400, by rfl⟩ : syracuseStep 1889867 = 2834801) B2834801
theorem B1259095 : Blo 1258447 1259095 := bstep (se 1 (by rfl) ⟨944321, by rfl⟩ : syracuseStep 1259095 = 1888643) B1888643
theorem B1889879 : Blo 1258447 1889879 := bstep (se 1 (by rfl) ⟨1417409, by rfl⟩ : syracuseStep 1889879 = 2834819) B2834819
theorem B1259115 : Blo 1258447 1259115 := bstep (se 1 (by rfl) ⟨944336, by rfl⟩ : syracuseStep 1259115 = 1888673) B1888673
theorem B1259127 : Blo 1258447 1259127 := bstep (se 1 (by rfl) ⟨944345, by rfl⟩ : syracuseStep 1259127 = 1888691) B1888691
theorem B2832011 : Blo 1258447 2832011 := bstep (se 1 (by rfl) ⟨2124008, by rfl⟩ : syracuseStep 2832011 = 4248017) B4248017
theorem B1259147 : Blo 1258447 1259147 := bstep (se 1 (by rfl) ⟨944360, by rfl⟩ : syracuseStep 1259147 = 1888721) B1888721
theorem B2389655 : Blo 1258447 2389655 := bstep (se 1 (by rfl) ⟨1792241, by rfl⟩ : syracuseStep 2389655 = 3584483) B3584483
theorem B1259159 : Blo 1258447 1259159 := bstep (se 1 (by rfl) ⟨944369, by rfl⟩ : syracuseStep 1259159 = 1888739) B1888739
theorem B1889945 : Blo 1258447 1889945 := bstep (se 2 (by rfl) ⟨708729, by rfl⟩ : syracuseStep 1889945 = 1417459) B1417459
theorem B1259179 : Blo 1258447 1259179 := bstep (se 1 (by rfl) ⟨944384, by rfl⟩ : syracuseStep 1259179 = 1888769) B1888769
theorem B1259191 : Blo 1258447 1259191 := bstep (se 1 (by rfl) ⟨944393, by rfl⟩ : syracuseStep 1259191 = 1888787) B1888787
theorem B2832065 : Blo 1258447 2832065 := bstep (se 2 (by rfl) ⟨1062024, by rfl⟩ : syracuseStep 2832065 = 2124049) B2124049
theorem B1259211 : Blo 1258447 1259211 := bstep (se 1 (by rfl) ⟨944408, by rfl⟩ : syracuseStep 1259211 = 1888817) B1888817
theorem B1259223 : Blo 1258447 1259223 := bstep (se 1 (by rfl) ⟨944417, by rfl⟩ : syracuseStep 1259223 = 1888835) B1888835
theorem B1259243 : Blo 1258447 1259243 := bstep (se 1 (by rfl) ⟨944432, by rfl⟩ : syracuseStep 1259243 = 1888865) B1888865
theorem B1259255 : Blo 1258447 1259255 := bstep (se 1 (by rfl) ⟨944441, by rfl⟩ : syracuseStep 1259255 = 1888883) B1888883
theorem B1259275 : Blo 1258447 1259275 := bstep (se 1 (by rfl) ⟨944456, by rfl⟩ : syracuseStep 1259275 = 1888913) B1888913
theorem B1890059 : Blo 1258447 1890059 := bstep (se 1 (by rfl) ⟨1417544, by rfl⟩ : syracuseStep 1890059 = 2835089) B2835089
theorem B4249367 : Blo 1258447 4249367 := bstep (se 1 (by rfl) ⟨3187025, by rfl⟩ : syracuseStep 4249367 = 6374051) B6374051
theorem B3585815 : Blo 1258447 3585815 := bstep (se 1 (by rfl) ⟨2689361, by rfl⟩ : syracuseStep 3585815 = 5378723) B5378723
theorem B1259287 : Blo 1258447 1259287 := bstep (se 1 (by rfl) ⟨944465, by rfl⟩ : syracuseStep 1259287 = 1888931) B1888931
theorem B1890071 : Blo 1258447 1890071 := bstep (se 1 (by rfl) ⟨1417553, by rfl⟩ : syracuseStep 1890071 = 2835107) B2835107
theorem B5109527 : Blo 1258447 5109527 := bstep (se 1 (by rfl) ⟨3832145, by rfl⟩ : syracuseStep 5109527 = 7664291) B7664291
theorem B1259307 : Blo 1258447 1259307 := bstep (se 1 (by rfl) ⟨944480, by rfl⟩ : syracuseStep 1259307 = 1888961) B1888961
theorem B4781875 : Blo 1258447 4781875 := bstep (se 1 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 4781875 = 7172813) B7172813
theorem B1259319 : Blo 1258447 1259319 := bstep (se 1 (by rfl) ⟨944489, by rfl⟩ : syracuseStep 1259319 = 1888979) B1888979
theorem B7173953 : Blo 1258447 7173953 := bstep (se 2 (by rfl) ⟨2690232, by rfl⟩ : syracuseStep 7173953 = 5380465) B5380465
theorem B1259339 : Blo 1258447 1259339 := bstep (se 1 (by rfl) ⟨944504, by rfl⟩ : syracuseStep 1259339 = 1889009) B1889009
theorem B1259351 : Blo 1258447 1259351 := bstep (se 1 (by rfl) ⟨944513, by rfl⟩ : syracuseStep 1259351 = 1889027) B1889027
theorem B1890137 : Blo 1258447 1890137 := bstep (se 2 (by rfl) ⟨708801, by rfl⟩ : syracuseStep 1890137 = 1417603) B1417603
theorem B1259371 : Blo 1258447 1259371 := bstep (se 1 (by rfl) ⟨944528, by rfl⟩ : syracuseStep 1259371 = 1889057) B1889057
theorem B1259383 : Blo 1258447 1259383 := bstep (se 1 (by rfl) ⟨944537, by rfl⟩ : syracuseStep 1259383 = 1889075) B1889075
theorem B1259403 : Blo 1258447 1259403 := bstep (se 1 (by rfl) ⟨944552, by rfl⟩ : syracuseStep 1259403 = 1889105) B1889105
theorem B1259415 : Blo 1258447 1259415 := bstep (se 1 (by rfl) ⟨944561, by rfl⟩ : syracuseStep 1259415 = 1889123) B1889123
theorem B2832281 : Blo 1258447 2832281 := bstep (se 2 (by rfl) ⟨1062105, by rfl⟩ : syracuseStep 2832281 = 2124211) B2124211
theorem B1259435 : Blo 1258447 1259435 := bstep (se 1 (by rfl) ⟨944576, by rfl⟩ : syracuseStep 1259435 = 1889153) B1889153
theorem B1259447 : Blo 1258447 1259447 := bstep (se 1 (by rfl) ⟨944585, by rfl⟩ : syracuseStep 1259447 = 1889171) B1889171
theorem B1259467 : Blo 1258447 1259467 := bstep (se 1 (by rfl) ⟨944600, by rfl⟩ : syracuseStep 1259467 = 1889201) B1889201
theorem B1890251 : Blo 1258447 1890251 := bstep (se 1 (by rfl) ⟨1417688, by rfl⟩ : syracuseStep 1890251 = 2835377) B2835377
theorem B1259479 : Blo 1258447 1259479 := bstep (se 1 (by rfl) ⟨944609, by rfl⟩ : syracuseStep 1259479 = 1889219) B1889219
theorem B1890263 : Blo 1258447 1890263 := bstep (se 1 (by rfl) ⟨1417697, by rfl⟩ : syracuseStep 1890263 = 2835395) B2835395
theorem B1259499 : Blo 1258447 1259499 := bstep (se 1 (by rfl) ⟨944624, by rfl⟩ : syracuseStep 1259499 = 1889249) B1889249
theorem B2832371 : Blo 1258447 2832371 := bstep (se 1 (by rfl) ⟨2124278, by rfl⟩ : syracuseStep 2832371 = 4248557) B4248557
theorem B1259511 : Blo 1258447 1259511 := bstep (se 1 (by rfl) ⟨944633, by rfl⟩ : syracuseStep 1259511 = 1889267) B1889267
theorem B1259531 : Blo 1258447 1259531 := bstep (se 1 (by rfl) ⟨944648, by rfl⟩ : syracuseStep 1259531 = 1889297) B1889297
theorem B2832407 : Blo 1258447 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B1259543 : Blo 1258447 1259543 := bstep (se 1 (by rfl) ⟨944657, by rfl⟩ : syracuseStep 1259543 = 1889315) B1889315
theorem B1890329 : Blo 1258447 1890329 := bstep (se 2 (by rfl) ⟨708873, by rfl⟩ : syracuseStep 1890329 = 1417747) B1417747
theorem B41400355 : Blo 1258447 41400355 := bstep (se 1 (by rfl) ⟨31050266, by rfl⟩ : syracuseStep 41400355 = 62100533) B62100533
theorem B1259563 : Blo 1258447 1259563 := bstep (se 1 (by rfl) ⟨944672, by rfl⟩ : syracuseStep 1259563 = 1889345) B1889345
theorem B5380141 : Blo 1258447 5380141 := bstep (se 3 (by rfl) ⟨1008776, by rfl⟩ : syracuseStep 5380141 = 2017553) B2017553
theorem B1259575 : Blo 1258447 1259575 := bstep (se 1 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 1259575 = 1889363) B1889363
theorem B9074753 : Blo 1258447 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B4536395 : Blo 1258447 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B1259595 : Blo 1258447 1259595 := bstep (se 1 (by rfl) ⟨944696, by rfl⟩ : syracuseStep 1259595 = 1889393) B1889393
theorem B1259607 : Blo 1258447 1259607 := bstep (se 1 (by rfl) ⟨944705, by rfl⟩ : syracuseStep 1259607 = 1889411) B1889411
theorem B1259627 : Blo 1258447 1259627 := bstep (se 1 (by rfl) ⟨944720, by rfl⟩ : syracuseStep 1259627 = 1889441) B1889441
theorem B1259639 : Blo 1258447 1259639 := bstep (se 1 (by rfl) ⟨944729, by rfl⟩ : syracuseStep 1259639 = 1889459) B1889459
theorem B6371459 : Blo 1258447 6371459 := bstep (se 1 (by rfl) ⟨4778594, by rfl⟩ : syracuseStep 6371459 = 9557189) B9557189
theorem B1259659 : Blo 1258447 1259659 := bstep (se 1 (by rfl) ⟨944744, by rfl⟩ : syracuseStep 1259659 = 1889489) B1889489
theorem B1890443 : Blo 1258447 1890443 := bstep (se 1 (by rfl) ⟨1417832, by rfl⟩ : syracuseStep 1890443 = 2835665) B2835665
theorem B1259671 : Blo 1258447 1259671 := bstep (se 1 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 1259671 = 1889507) B1889507
theorem B1890455 : Blo 1258447 1890455 := bstep (se 1 (by rfl) ⟨1417841, by rfl⟩ : syracuseStep 1890455 = 2835683) B2835683
theorem B1259691 : Blo 1258447 1259691 := bstep (se 1 (by rfl) ⟨944768, by rfl⟩ : syracuseStep 1259691 = 1889537) B1889537
theorem B1259703 : Blo 1258447 1259703 := bstep (se 1 (by rfl) ⟨944777, by rfl⟩ : syracuseStep 1259703 = 1889555) B1889555
theorem B2832587 : Blo 1258447 2832587 := bstep (se 1 (by rfl) ⟨2124440, by rfl⟩ : syracuseStep 2832587 = 4248881) B4248881
theorem B1259723 : Blo 1258447 1259723 := bstep (se 1 (by rfl) ⟨944792, by rfl⟩ : syracuseStep 1259723 = 1889585) B1889585
theorem B1259735 : Blo 1258447 1259735 := bstep (se 1 (by rfl) ⟨944801, by rfl⟩ : syracuseStep 1259735 = 1889603) B1889603
theorem B1890521 : Blo 1258447 1890521 := bstep (se 2 (by rfl) ⟨708945, by rfl⟩ : syracuseStep 1890521 = 1417891) B1417891
theorem B1259755 : Blo 1258447 1259755 := bstep (se 1 (by rfl) ⟨944816, by rfl⟩ : syracuseStep 1259755 = 1889633) B1889633
theorem B1259767 : Blo 1258447 1259767 := bstep (se 1 (by rfl) ⟨944825, by rfl⟩ : syracuseStep 1259767 = 1889651) B1889651
theorem B2832641 : Blo 1258447 2832641 := bstep (se 2 (by rfl) ⟨1062240, by rfl⟩ : syracuseStep 2832641 = 2124481) B2124481
theorem B1259787 : Blo 1258447 1259787 := bstep (se 1 (by rfl) ⟨944840, by rfl⟩ : syracuseStep 1259787 = 1889681) B1889681
theorem B1259799 : Blo 1258447 1259799 := bstep (se 1 (by rfl) ⟨944849, by rfl⟩ : syracuseStep 1259799 = 1889699) B1889699
theorem B1259819 : Blo 1258447 1259819 := bstep (se 1 (by rfl) ⟨944864, by rfl⟩ : syracuseStep 1259819 = 1889729) B1889729
theorem B2390323 : Blo 1258447 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B4249907 : Blo 1258447 4249907 := bstep (se 1 (by rfl) ⟨3187430, by rfl⟩ : syracuseStep 4249907 = 6374861) B6374861
theorem B1259831 : Blo 1258447 1259831 := bstep (se 1 (by rfl) ⟨944873, by rfl⟩ : syracuseStep 1259831 = 1889747) B1889747
theorem B15309121 : Blo 1258447 15309121 := bstep (se 2 (by rfl) ⟨5740920, by rfl⟩ : syracuseStep 15309121 = 11481841) B11481841
theorem B10754369 : Blo 1258447 10754369 := bstep (se 2 (by rfl) ⟨4032888, by rfl⟩ : syracuseStep 10754369 = 8065777) B8065777
theorem B1259851 : Blo 1258447 1259851 := bstep (se 1 (by rfl) ⟨944888, by rfl⟩ : syracuseStep 1259851 = 1889777) B1889777
theorem B1890635 : Blo 1258447 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B1259863 : Blo 1258447 1259863 := bstep (se 1 (by rfl) ⟨944897, by rfl⟩ : syracuseStep 1259863 = 1889795) B1889795
theorem B1890647 : Blo 1258447 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B1259883 : Blo 1258447 1259883 := bstep (se 1 (by rfl) ⟨944912, by rfl⟩ : syracuseStep 1259883 = 1889825) B1889825
theorem B1259895 : Blo 1258447 1259895 := bstep (se 1 (by rfl) ⟨944921, by rfl⟩ : syracuseStep 1259895 = 1889843) B1889843
theorem B1259915 : Blo 1258447 1259915 := bstep (se 1 (by rfl) ⟨944936, by rfl⟩ : syracuseStep 1259915 = 1889873) B1889873
theorem B1259927 : Blo 1258447 1259927 := bstep (se 1 (by rfl) ⟨944945, by rfl⟩ : syracuseStep 1259927 = 1889891) B1889891
theorem B4037015 : Blo 1258447 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B1259947 : Blo 1258447 1259947 := bstep (se 1 (by rfl) ⟨944960, by rfl⟩ : syracuseStep 1259947 = 1889921) B1889921
theorem B1259959 : Blo 1258447 1259959 := bstep (se 1 (by rfl) ⟨944969, by rfl⟩ : syracuseStep 1259959 = 1889939) B1889939
theorem B1259979 : Blo 1258447 1259979 := bstep (se 1 (by rfl) ⟨944984, by rfl⟩ : syracuseStep 1259979 = 1889969) B1889969
theorem B1259991 : Blo 1258447 1259991 := bstep (se 1 (by rfl) ⟨944993, by rfl⟩ : syracuseStep 1259991 = 1889987) B1889987
theorem B2832857 : Blo 1258447 2832857 := bstep (se 2 (by rfl) ⟨1062321, by rfl⟩ : syracuseStep 2832857 = 2124643) B2124643
theorem B1260011 : Blo 1258447 1260011 := bstep (se 1 (by rfl) ⟨945008, by rfl⟩ : syracuseStep 1260011 = 1890017) B1890017
theorem B1260023 : Blo 1258447 1260023 := bstep (se 1 (by rfl) ⟨945017, by rfl⟩ : syracuseStep 1260023 = 1890035) B1890035
theorem B1260043 : Blo 1258447 1260043 := bstep (se 1 (by rfl) ⟨945032, by rfl⟩ : syracuseStep 1260043 = 1890065) B1890065
theorem B1260055 : Blo 1258447 1260055 := bstep (se 1 (by rfl) ⟨945041, by rfl⟩ : syracuseStep 1260055 = 1890083) B1890083
theorem B1260075 : Blo 1258447 1260075 := bstep (se 1 (by rfl) ⟨945056, by rfl⟩ : syracuseStep 1260075 = 1890113) B1890113
theorem B2832947 : Blo 1258447 2832947 := bstep (se 1 (by rfl) ⟨2124710, by rfl⟩ : syracuseStep 2832947 = 4249421) B4249421
theorem B1260087 : Blo 1258447 1260087 := bstep (se 1 (by rfl) ⟨945065, by rfl⟩ : syracuseStep 1260087 = 1890131) B1890131
theorem B4250177 : Blo 1258447 4250177 := bstep (se 2 (by rfl) ⟨1593816, by rfl⟩ : syracuseStep 4250177 = 3187633) B3187633
theorem B16136779 : Blo 1258447 16136779 := bstep (se 1 (by rfl) ⟨12102584, by rfl⟩ : syracuseStep 16136779 = 24205169) B24205169
theorem B1260107 : Blo 1258447 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B4037195 : Blo 1258447 4037195 := bstep (se 1 (by rfl) ⟨3027896, by rfl⟩ : syracuseStep 4037195 = 6055793) B6055793
theorem B1415767 : Blo 1258447 1415767 := bstep (se 1 (by rfl) ⟨1061825, by rfl⟩ : syracuseStep 1415767 = 2123651) B2123651
theorem B2832983 : Blo 1258447 2832983 := bstep (se 1 (by rfl) ⟨2124737, by rfl⟩ : syracuseStep 2832983 = 4249475) B4249475
theorem B1260119 : Blo 1258447 1260119 := bstep (se 1 (by rfl) ⟨945089, by rfl⟩ : syracuseStep 1260119 = 1890179) B1890179
theorem B1260139 : Blo 1258447 1260139 := bstep (se 1 (by rfl) ⟨945104, by rfl⟩ : syracuseStep 1260139 = 1890209) B1890209
theorem B1260151 : Blo 1258447 1260151 := bstep (se 1 (by rfl) ⟨945113, by rfl⟩ : syracuseStep 1260151 = 1890227) B1890227
theorem B5380739 : Blo 1258447 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B1260171 : Blo 1258447 1260171 := bstep (se 1 (by rfl) ⟨945128, by rfl⟩ : syracuseStep 1260171 = 1890257) B1890257
theorem B1260183 : Blo 1258447 1260183 := bstep (se 1 (by rfl) ⟨945137, by rfl⟩ : syracuseStep 1260183 = 1890275) B1890275
theorem B1260203 : Blo 1258447 1260203 := bstep (se 1 (by rfl) ⟨945152, by rfl⟩ : syracuseStep 1260203 = 1890305) B1890305
theorem B1260215 : Blo 1258447 1260215 := bstep (se 1 (by rfl) ⟨945161, by rfl⟩ : syracuseStep 1260215 = 1890323) B1890323
theorem B1260235 : Blo 1258447 1260235 := bstep (se 1 (by rfl) ⟨945176, by rfl⟩ : syracuseStep 1260235 = 1890353) B1890353
theorem B4037323 : Blo 1258447 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B1260247 : Blo 1258447 1260247 := bstep (se 1 (by rfl) ⟨945185, by rfl⟩ : syracuseStep 1260247 = 1890371) B1890371
theorem B1260267 : Blo 1258447 1260267 := bstep (se 1 (by rfl) ⟨945200, by rfl⟩ : syracuseStep 1260267 = 1890401) B1890401
theorem B20708081 : Blo 1258447 20708081 := bstep (se 2 (by rfl) ⟨7765530, by rfl⟩ : syracuseStep 20708081 = 15531061) B15531061
theorem B2390771 : Blo 1258447 2390771 := bstep (se 1 (by rfl) ⟨1793078, by rfl⟩ : syracuseStep 2390771 = 3586157) B3586157
theorem B1260279 : Blo 1258447 1260279 := bstep (se 1 (by rfl) ⟨945209, by rfl⟩ : syracuseStep 1260279 = 1890419) B1890419
theorem B1415947 : Blo 1258447 1415947 := bstep (se 1 (by rfl) ⟨1061960, by rfl⟩ : syracuseStep 1415947 = 2123921) B2123921
theorem B2833163 : Blo 1258447 2833163 := bstep (se 1 (by rfl) ⟨2124872, by rfl⟩ : syracuseStep 2833163 = 4249745) B4249745
theorem B1260299 : Blo 1258447 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B1260311 : Blo 1258447 1260311 := bstep (se 1 (by rfl) ⟨945233, by rfl⟩ : syracuseStep 1260311 = 1890467) B1890467
theorem B2390809 : Blo 1258447 2390809 := bstep (se 2 (by rfl) ⟨896553, by rfl⟩ : syracuseStep 2390809 = 1793107) B1793107
theorem B1260331 : Blo 1258447 1260331 := bstep (se 1 (by rfl) ⟨945248, by rfl⟩ : syracuseStep 1260331 = 1890497) B1890497
theorem B1260343 : Blo 1258447 1260343 := bstep (se 1 (by rfl) ⟨945257, by rfl⟩ : syracuseStep 1260343 = 1890515) B1890515
theorem B2833217 : Blo 1258447 2833217 := bstep (se 2 (by rfl) ⟨1062456, by rfl⟩ : syracuseStep 2833217 = 2124913) B2124913
theorem B130898753 : Blo 1258447 130898753 := bstep (se 2 (by rfl) ⟨49087032, by rfl⟩ : syracuseStep 130898753 = 98174065) B98174065
theorem B1260363 : Blo 1258447 1260363 := bstep (se 1 (by rfl) ⟨945272, by rfl⟩ : syracuseStep 1260363 = 1890545) B1890545
theorem B1260375 : Blo 1258447 1260375 := bstep (se 1 (by rfl) ⟨945281, by rfl⟩ : syracuseStep 1260375 = 1890563) B1890563
theorem B4848473 : Blo 1258447 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B3152729 : Blo 1258447 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B4037465 : Blo 1258447 4037465 := bstep (se 2 (by rfl) ⟨1514049, by rfl⟩ : syracuseStep 4037465 = 3028099) B3028099
theorem B1260395 : Blo 1258447 1260395 := bstep (se 1 (by rfl) ⟨945296, by rfl⟩ : syracuseStep 1260395 = 1890593) B1890593
theorem B1416055 : Blo 1258447 1416055 := bstep (se 1 (by rfl) ⟨1062041, by rfl⟩ : syracuseStep 1416055 = 2124083) B2124083
theorem B1260407 : Blo 1258447 1260407 := bstep (se 1 (by rfl) ⟨945305, by rfl⟩ : syracuseStep 1260407 = 1890611) B1890611
theorem B1915787 : Blo 1258447 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B1260427 : Blo 1258447 1260427 := bstep (se 1 (by rfl) ⟨945320, by rfl⟩ : syracuseStep 1260427 = 1890641) B1890641
theorem B1260439 : Blo 1258447 1260439 := bstep (se 1 (by rfl) ⟨945329, by rfl⟩ : syracuseStep 1260439 = 1890659) B1890659
theorem B4037579 : Blo 1258447 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B6904793 : Blo 1258447 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B4783121 : Blo 1258447 4783121 := bstep (se 2 (by rfl) ⟨1793670, by rfl⟩ : syracuseStep 4783121 = 3587341) B3587341
theorem B2833433 : Blo 1258447 2833433 := bstep (se 2 (by rfl) ⟨1062537, by rfl⟩ : syracuseStep 2833433 = 2125075) B2125075
theorem B1416235 : Blo 1258447 1416235 := bstep (se 1 (by rfl) ⟨1062176, by rfl⟩ : syracuseStep 1416235 = 2124353) B2124353
theorem B4537433 : Blo 1258447 4537433 := bstep (se 2 (by rfl) ⟨1701537, by rfl⟩ : syracuseStep 4537433 = 3403075) B3403075
theorem B9559133 : Blo 1258447 9559133 := bstep (se 3 (by rfl) ⟨1792337, by rfl⟩ : syracuseStep 9559133 = 3584675) B3584675
theorem B4250717 : Blo 1258447 4250717 := bstep (se 3 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 4250717 = 1594019) B1594019
theorem B2833523 : Blo 1258447 2833523 := bstep (se 1 (by rfl) ⟨2125142, by rfl⟩ : syracuseStep 2833523 = 4250285) B4250285
theorem B1416343 : Blo 1258447 1416343 := bstep (se 1 (by rfl) ⟨1062257, by rfl⟩ : syracuseStep 1416343 = 2124515) B2124515
theorem B2833559 : Blo 1258447 2833559 := bstep (se 1 (by rfl) ⟨2125169, by rfl⟩ : syracuseStep 2833559 = 4250339) B4250339
theorem B5102795 : Blo 1258447 5102795 := bstep (se 1 (by rfl) ⟨3827096, by rfl⟩ : syracuseStep 5102795 = 7654193) B7654193
theorem B4537547 : Blo 1258447 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B2391257 : Blo 1258447 2391257 := bstep (se 2 (by rfl) ⟨896721, by rfl⟩ : syracuseStep 2391257 = 1793443) B1793443
theorem B1416523 : Blo 1258447 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B2833739 : Blo 1258447 2833739 := bstep (se 1 (by rfl) ⟨2125304, by rfl⟩ : syracuseStep 2833739 = 4250609) B4250609
theorem B2833793 : Blo 1258447 2833793 := bstep (se 2 (by rfl) ⟨1062672, by rfl⟩ : syracuseStep 2833793 = 2125345) B2125345
theorem B1793431 : Blo 1258447 1793431 := bstep (se 1 (by rfl) ⟨1345073, by rfl⟩ : syracuseStep 1793431 = 2690147) B2690147
theorem B9829811 : Blo 1258447 9829811 := bstep (se 1 (by rfl) ⟨7372358, by rfl⟩ : syracuseStep 9829811 = 14744717) B14744717
theorem B1416631 : Blo 1258447 1416631 := bstep (se 1 (by rfl) ⟨1062473, by rfl⟩ : syracuseStep 1416631 = 2124947) B2124947
theorem B6381017 : Blo 1258447 6381017 := bstep (se 2 (by rfl) ⟨2392881, by rfl⟩ : syracuseStep 6381017 = 4785763) B4785763
theorem B5103121 : Blo 1258447 5103121 := bstep (se 2 (by rfl) ⟨1913670, by rfl⟩ : syracuseStep 5103121 = 3827341) B3827341
theorem B2834009 : Blo 1258447 2834009 := bstep (se 2 (by rfl) ⟨1062753, by rfl⟩ : syracuseStep 2834009 = 2125507) B2125507
theorem B1416811 : Blo 1258447 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B12099203 : Blo 1258447 12099203 := bstep (se 1 (by rfl) ⟨9074402, by rfl⟩ : syracuseStep 12099203 = 18148805) B18148805
theorem B2834099 : Blo 1258447 2834099 := bstep (se 1 (by rfl) ⟨2125574, by rfl⟩ : syracuseStep 2834099 = 4251149) B4251149
theorem B4783819 : Blo 1258447 4783819 := bstep (se 1 (by rfl) ⟨3587864, by rfl⟩ : syracuseStep 4783819 = 7175729) B7175729
theorem B1416919 : Blo 1258447 1416919 := bstep (se 1 (by rfl) ⟨1062689, by rfl⟩ : syracuseStep 1416919 = 2125379) B2125379
theorem B2834135 : Blo 1258447 2834135 := bstep (se 1 (by rfl) ⟨2125601, by rfl⟩ : syracuseStep 2834135 = 4251203) B4251203
theorem B1417099 : Blo 1258447 1417099 := bstep (se 1 (by rfl) ⟨1062824, by rfl⟩ : syracuseStep 1417099 = 2125649) B2125649
theorem B2834315 : Blo 1258447 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B3186611 : Blo 1258447 3186611 := bstep (se 1 (by rfl) ⟨2389958, by rfl⟩ : syracuseStep 3186611 = 4779917) B4779917
theorem B2834369 : Blo 1258447 2834369 := bstep (se 2 (by rfl) ⟨1062888, by rfl⟩ : syracuseStep 2834369 = 2125777) B2125777
theorem B2392001 : Blo 1258447 2392001 := bstep (se 2 (by rfl) ⟨897000, by rfl⟩ : syracuseStep 2392001 = 1794001) B1794001
theorem B4784093 : Blo 1258447 4784093 := bstep (se 3 (by rfl) ⟨897017, by rfl⟩ : syracuseStep 4784093 = 1794035) B1794035
theorem B1417207 : Blo 1258447 1417207 := bstep (se 1 (by rfl) ⟨1062905, by rfl⟩ : syracuseStep 1417207 = 2125811) B2125811
theorem B3186803 : Blo 1258447 3186803 := bstep (se 1 (by rfl) ⟨2390102, by rfl⟩ : syracuseStep 3186803 = 4780205) B4780205
theorem B2392183 : Blo 1258447 2392183 := bstep (se 1 (by rfl) ⟨1794137, by rfl⟩ : syracuseStep 2392183 = 3588275) B3588275
theorem B3186823 : Blo 1258447 3186823 := bstep (se 1 (by rfl) ⟨2390117, by rfl⟩ : syracuseStep 3186823 = 4780235) B4780235
theorem B2834567 : Blo 1258447 2834567 := bstep (se 1 (by rfl) ⟨2125925, by rfl⟩ : syracuseStep 2834567 = 4251851) B4251851
theorem B1417351 : Blo 1258447 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B2490515 : Blo 1258447 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B6054061 : Blo 1258447 6054061 := bstep (se 3 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 6054061 = 2270273) B2270273
theorem B4251905 : Blo 1258447 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B2834747 : Blo 1258447 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B1417531 : Blo 1258447 1417531 := bstep (se 1 (by rfl) ⟨1063148, by rfl⟩ : syracuseStep 1417531 = 2126297) B2126297
theorem B9085243 : Blo 1258447 9085243 := bstep (se 1 (by rfl) ⟨6813932, by rfl⟩ : syracuseStep 9085243 = 13627865) B13627865
theorem B2154871 : Blo 1258447 2154871 := bstep (se 1 (by rfl) ⟨1616153, by rfl⟩ : syracuseStep 2154871 = 3232307) B3232307
theorem B3187097 : Blo 1258447 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B2834873 : Blo 1258447 2834873 := bstep (se 2 (by rfl) ⟨1063077, by rfl⟩ : syracuseStep 2834873 = 2126155) B2126155
theorem B13607453 : Blo 1258447 13607453 := bstep (se 3 (by rfl) ⟨2551397, by rfl⟩ : syracuseStep 13607453 = 5102795) B5102795
theorem B3187259 : Blo 1258447 3187259 := bstep (se 1 (by rfl) ⟨2390444, by rfl⟩ : syracuseStep 3187259 = 4780889) B4780889
theorem B2015945 : Blo 1258447 2015945 := bstep (se 2 (by rfl) ⟨755979, by rfl⟩ : syracuseStep 2015945 = 1511959) B1511959
theorem B3187471 : Blo 1258447 3187471 := bstep (se 1 (by rfl) ⟨2390603, by rfl⟩ : syracuseStep 3187471 = 4781207) B4781207
theorem B2835215 : Blo 1258447 2835215 := bstep (se 1 (by rfl) ⟨2126411, by rfl⟩ : syracuseStep 2835215 = 4252823) B4252823
theorem B1417999 : Blo 1258447 1417999 := bstep (se 1 (by rfl) ⟨1063499, by rfl⟩ : syracuseStep 1417999 = 2126999) B2126999
theorem B2835233 : Blo 1258447 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B5383027 : Blo 1258447 5383027 := bstep (se 1 (by rfl) ⟨4037270, by rfl⟩ : syracuseStep 5383027 = 8074541) B8074541
theorem B5383097 : Blo 1258447 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B3589049 : Blo 1258447 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B3187745 : Blo 1258447 3187745 := bstep (se 2 (by rfl) ⟨1195404, by rfl⟩ : syracuseStep 3187745 = 2390809) B2390809
theorem B4252715 : Blo 1258447 4252715 := bstep (se 1 (by rfl) ⟨3189536, by rfl⟩ : syracuseStep 4252715 = 6379073) B6379073
theorem B14345261 : Blo 1258447 14345261 := bstep (se 3 (by rfl) ⟨2689736, by rfl⟩ : syracuseStep 14345261 = 5379473) B5379473
theorem B2835575 : Blo 1258447 2835575 := bstep (se 1 (by rfl) ⟨2126681, by rfl⟩ : syracuseStep 2835575 = 4253363) B4253363
theorem B2835755 : Blo 1258447 2835755 := bstep (se 1 (by rfl) ⟨2126816, by rfl⟩ : syracuseStep 2835755 = 4253633) B4253633
theorem B3024263 : Blo 1258447 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B11494865 : Blo 1258447 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B7169579 : Blo 1258447 7169579 := bstep (se 1 (by rfl) ⟨5377184, by rfl⟩ : syracuseStep 7169579 = 10754369) B10754369
theorem B3884663 : Blo 1258447 3884663 := bstep (se 1 (by rfl) ⟨2913497, by rfl⟩ : syracuseStep 3884663 = 5826995) B5826995
theorem B14534437 : Blo 1258447 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B13805387 : Blo 1258447 13805387 := bstep (se 1 (by rfl) ⟨10354040, by rfl⟩ : syracuseStep 13805387 = 20708081) B20708081
theorem B1345415 : Blo 1258447 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B2123705 : Blo 1258447 2123705 := bstep (se 2 (by rfl) ⟨796389, by rfl⟩ : syracuseStep 2123705 = 1592779) B1592779
theorem B3188747 : Blo 1258447 3188747 := bstep (se 1 (by rfl) ⟨2391560, by rfl⟩ : syracuseStep 3188747 = 4783121) B4783121
theorem B3024955 : Blo 1258447 3024955 := bstep (se 1 (by rfl) ⟨2268716, by rfl⟩ : syracuseStep 3024955 = 4537433) B4537433
theorem B13625405 : Blo 1258447 13625405 := bstep (se 3 (by rfl) ⟨2554763, by rfl⟩ : syracuseStep 13625405 = 5109527) B5109527
theorem B7178327 : Blo 1258447 7178327 := bstep (se 1 (by rfl) ⟨5383745, by rfl⟩ : syracuseStep 7178327 = 10767491) B10767491
theorem B3025031 : Blo 1258447 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B6056137 : Blo 1258447 6056137 := bstep (se 2 (by rfl) ⟨2271051, by rfl⟩ : syracuseStep 6056137 = 4542103) B4542103
theorem B8407277 : Blo 1258447 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B4254011 : Blo 1258447 4254011 := bstep (se 1 (by rfl) ⟨3190508, by rfl⟩ : syracuseStep 4254011 = 6381017) B6381017
theorem B6375833 : Blo 1258447 6375833 := bstep (se 2 (by rfl) ⟨2390937, by rfl⟩ : syracuseStep 6375833 = 4781875) B4781875
theorem B11495965 : Blo 1258447 11495965 := bstep (se 3 (by rfl) ⟨2155493, by rfl⟩ : syracuseStep 11495965 = 4310987) B4310987
theorem B2124407 : Blo 1258447 2124407 := bstep (se 1 (by rfl) ⟨1593305, by rfl⟩ : syracuseStep 2124407 = 3186611) B3186611
theorem B3189395 : Blo 1258447 3189395 := bstep (se 1 (by rfl) ⟨2392046, by rfl⟩ : syracuseStep 3189395 = 4784093) B4784093
theorem B55200473 : Blo 1258447 55200473 := bstep (se 2 (by rfl) ⟨20700177, by rfl⟩ : syracuseStep 55200473 = 41400355) B41400355
theorem B4844441 : Blo 1258447 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B3189689 : Blo 1258447 3189689 := bstep (se 2 (by rfl) ⟨1196133, by rfl⟩ : syracuseStep 3189689 = 2392267) B2392267
theorem B7171037 : Blo 1258447 7171037 := bstep (se 3 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 7171037 = 2689139) B2689139
theorem B14355467 : Blo 1258447 14355467 := bstep (se 1 (by rfl) ⟨10766600, by rfl⟩ : syracuseStep 14355467 = 21533201) B21533201
theorem B2124859 : Blo 1258447 2124859 := bstep (se 1 (by rfl) ⟨1593644, by rfl⟩ : syracuseStep 2124859 = 3187289) B3187289
theorem B6991049 : Blo 1258447 6991049 := bstep (se 2 (by rfl) ⟨2621643, by rfl⟩ : syracuseStep 6991049 = 5243287) B5243287
theorem B2125001 : Blo 1258447 2125001 := bstep (se 2 (by rfl) ⟨796875, by rfl⟩ : syracuseStep 2125001 = 1593751) B1593751
theorem B8064289 : Blo 1258447 8064289 := bstep (se 2 (by rfl) ⟨3024108, by rfl⟩ : syracuseStep 8064289 = 6048217) B6048217
theorem B20417923 : Blo 1258447 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B21515705 : Blo 1258447 21515705 := bstep (se 2 (by rfl) ⟨8068389, by rfl⟩ : syracuseStep 21515705 = 16136779) B16136779
theorem B2690489 : Blo 1258447 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B1887689 : Blo 1258447 1887689 := bstep (se 2 (by rfl) ⟨707883, by rfl⟩ : syracuseStep 1887689 = 1415767) B1415767
theorem B7171537 : Blo 1258447 7171537 := bstep (se 2 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 7171537 = 5378653) B5378653
theorem B1592875 : Blo 1258447 1592875 := bstep (se 1 (by rfl) ⟨1194656, by rfl⟩ : syracuseStep 1592875 = 2389313) B2389313
theorem B1887803 : Blo 1258447 1887803 := bstep (se 1 (by rfl) ⟨1415852, by rfl⟩ : syracuseStep 1887803 = 2831705) B2831705
theorem B20434531 : Blo 1258447 20434531 := bstep (se 1 (by rfl) ⟨15325898, by rfl⟩ : syracuseStep 20434531 = 30651797) B30651797
theorem B3190387 : Blo 1258447 3190387 := bstep (se 1 (by rfl) ⟨2392790, by rfl⟩ : syracuseStep 3190387 = 4785581) B4785581
theorem B1887863 : Blo 1258447 1887863 := bstep (se 1 (by rfl) ⟨1415897, by rfl⟩ : syracuseStep 1887863 = 2831795) B2831795
theorem B1887887 : Blo 1258447 1887887 := bstep (se 1 (by rfl) ⟨1415915, by rfl⟩ : syracuseStep 1887887 = 2831831) B2831831
theorem B3583673 : Blo 1258447 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B1887929 : Blo 1258447 1887929 := bstep (se 2 (by rfl) ⟨707973, by rfl⟩ : syracuseStep 1887929 = 1415947) B1415947
theorem B1888007 : Blo 1258447 1888007 := bstep (se 1 (by rfl) ⟨1416005, by rfl⟩ : syracuseStep 1888007 = 2832011) B2832011
theorem B1593103 : Blo 1258447 1593103 := bstep (se 1 (by rfl) ⟨1194827, by rfl⟩ : syracuseStep 1593103 = 2389655) B2389655
theorem B1888043 : Blo 1258447 1888043 := bstep (se 1 (by rfl) ⟨1416032, by rfl⟩ : syracuseStep 1888043 = 2832065) B2832065
theorem B1888073 : Blo 1258447 1888073 := bstep (se 2 (by rfl) ⟨708027, by rfl⟩ : syracuseStep 1888073 = 1416055) B1416055
theorem B9563993 : Blo 1258447 9563993 := bstep (se 2 (by rfl) ⟨3586497, by rfl⟩ : syracuseStep 9563993 = 7172995) B7172995
theorem B2125703 : Blo 1258447 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B1888187 : Blo 1258447 1888187 := bstep (se 1 (by rfl) ⟨1416140, by rfl⟩ : syracuseStep 1888187 = 2832281) B2832281
theorem B1888247 : Blo 1258447 1888247 := bstep (se 1 (by rfl) ⟨1416185, by rfl⟩ : syracuseStep 1888247 = 2832371) B2832371
theorem B3026945 : Blo 1258447 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B1888271 : Blo 1258447 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B6049835 : Blo 1258447 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B1888313 : Blo 1258447 1888313 := bstep (se 2 (by rfl) ⟨708117, by rfl⟩ : syracuseStep 1888313 = 1416235) B1416235
theorem B4247639 : Blo 1258447 4247639 := bstep (se 1 (by rfl) ⟨3185729, by rfl⟩ : syracuseStep 4247639 = 6371459) B6371459
theorem B3829847 : Blo 1258447 3829847 := bstep (se 1 (by rfl) ⟨2872385, by rfl⟩ : syracuseStep 3829847 = 5744771) B5744771
theorem B1888391 : Blo 1258447 1888391 := bstep (se 1 (by rfl) ⟨1416293, by rfl⟩ : syracuseStep 1888391 = 2832587) B2832587
theorem B1888427 : Blo 1258447 1888427 := bstep (se 1 (by rfl) ⟨1416320, by rfl⟩ : syracuseStep 1888427 = 2832641) B2832641
theorem B3633353 : Blo 1258447 3633353 := bstep (se 2 (by rfl) ⟨1362507, by rfl⟩ : syracuseStep 3633353 = 2725015) B2725015
theorem B1888457 : Blo 1258447 1888457 := bstep (se 2 (by rfl) ⟨708171, by rfl⟩ : syracuseStep 1888457 = 1416343) B1416343
theorem B24875209 : Blo 1258447 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B2691343 : Blo 1258447 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B1888571 : Blo 1258447 1888571 := bstep (se 1 (by rfl) ⟨1416428, by rfl⟩ : syracuseStep 1888571 = 2832857) B2832857
theorem B4780403 : Blo 1258447 4780403 := bstep (se 1 (by rfl) ⟨3585302, by rfl⟩ : syracuseStep 4780403 = 7170605) B7170605
theorem B1888631 : Blo 1258447 1888631 := bstep (se 1 (by rfl) ⟨1416473, by rfl⟩ : syracuseStep 1888631 = 2832947) B2832947
theorem B2691463 : Blo 1258447 2691463 := bstep (se 1 (by rfl) ⟨2018597, by rfl⟩ : syracuseStep 2691463 = 4037195) B4037195
theorem B1888655 : Blo 1258447 1888655 := bstep (se 1 (by rfl) ⟨1416491, by rfl⟩ : syracuseStep 1888655 = 2832983) B2832983
theorem B1888697 : Blo 1258447 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B1593847 : Blo 1258447 1593847 := bstep (se 1 (by rfl) ⟨1195385, by rfl⟩ : syracuseStep 1593847 = 2390771) B2390771
theorem B1888775 : Blo 1258447 1888775 := bstep (se 1 (by rfl) ⟨1416581, by rfl⟩ : syracuseStep 1888775 = 2833163) B2833163
theorem B2126351 : Blo 1258447 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B1888811 : Blo 1258447 1888811 := bstep (se 1 (by rfl) ⟨1416608, by rfl⟩ : syracuseStep 1888811 = 2833217) B2833217
theorem B87265835 : Blo 1258447 87265835 := bstep (se 1 (by rfl) ⟨65449376, by rfl⟩ : syracuseStep 87265835 = 130898753) B130898753
theorem B3232315 : Blo 1258447 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B2691643 : Blo 1258447 2691643 := bstep (se 1 (by rfl) ⟨2018732, by rfl⟩ : syracuseStep 2691643 = 4037465) B4037465
theorem B4248125 : Blo 1258447 4248125 := bstep (se 3 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 4248125 = 1593047) B1593047
theorem B1888841 : Blo 1258447 1888841 := bstep (se 2 (by rfl) ⟨708315, by rfl⟩ : syracuseStep 1888841 = 1416631) B1416631
theorem B2691719 : Blo 1258447 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B1888955 : Blo 1258447 1888955 := bstep (se 1 (by rfl) ⟨1416716, by rfl⟩ : syracuseStep 1888955 = 2833433) B2833433
theorem B6804161 : Blo 1258447 6804161 := bstep (se 2 (by rfl) ⟨2551560, by rfl⟩ : syracuseStep 6804161 = 5103121) B5103121
theorem B1889015 : Blo 1258447 1889015 := bstep (se 1 (by rfl) ⟨1416761, by rfl⟩ : syracuseStep 1889015 = 2833523) B2833523
theorem B1889039 : Blo 1258447 1889039 := bstep (se 1 (by rfl) ⟨1416779, by rfl⟩ : syracuseStep 1889039 = 2833559) B2833559
theorem B9564965 : Blo 1258447 9564965 := bstep (se 4 (by rfl) ⟨896715, by rfl⟩ : syracuseStep 9564965 = 1793431) B1793431
theorem B1889081 : Blo 1258447 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B1594171 : Blo 1258447 1594171 := bstep (se 1 (by rfl) ⟨1195628, by rfl⟩ : syracuseStep 1594171 = 2391257) B2391257
theorem B3027799 : Blo 1258447 3027799 := bstep (se 1 (by rfl) ⟨2270849, by rfl⟩ : syracuseStep 3027799 = 4541699) B4541699
theorem B1889159 : Blo 1258447 1889159 := bstep (se 1 (by rfl) ⟨1416869, by rfl⟩ : syracuseStep 1889159 = 2833739) B2833739
theorem B1913743 : Blo 1258447 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B1889195 : Blo 1258447 1889195 := bstep (se 1 (by rfl) ⟨1416896, by rfl⟩ : syracuseStep 1889195 = 2833793) B2833793
theorem B6378425 : Blo 1258447 6378425 := bstep (se 2 (by rfl) ⟨2391909, by rfl⟩ : syracuseStep 6378425 = 4783819) B4783819
theorem B1889225 : Blo 1258447 1889225 := bstep (se 2 (by rfl) ⟨708459, by rfl⟩ : syracuseStep 1889225 = 1416919) B1416919
theorem B1258503 : Blo 1258447 1258503 := bstep (se 1 (by rfl) ⟨943877, by rfl⟩ : syracuseStep 1258503 = 1887755) B1887755
theorem B1258511 : Blo 1258447 1258511 := bstep (se 1 (by rfl) ⟨943883, by rfl⟩ : syracuseStep 1258511 = 1887767) B1887767
theorem B2126891 : Blo 1258447 2126891 := bstep (se 1 (by rfl) ⟨1595168, by rfl⟩ : syracuseStep 2126891 = 3190337) B3190337
theorem B1258555 : Blo 1258447 1258555 := bstep (se 1 (by rfl) ⟨943916, by rfl⟩ : syracuseStep 1258555 = 1887833) B1887833
theorem B1889339 : Blo 1258447 1889339 := bstep (se 1 (by rfl) ⟨1417004, by rfl⟩ : syracuseStep 1889339 = 2834009) B2834009
theorem B3830843 : Blo 1258447 3830843 := bstep (se 1 (by rfl) ⟨2873132, by rfl⟩ : syracuseStep 3830843 = 5746265) B5746265
theorem B8066135 : Blo 1258447 8066135 := bstep (se 1 (by rfl) ⟨6049601, by rfl⟩ : syracuseStep 8066135 = 12099203) B12099203
theorem B1889399 : Blo 1258447 1889399 := bstep (se 1 (by rfl) ⟨1417049, by rfl⟩ : syracuseStep 1889399 = 2834099) B2834099
theorem B1258631 : Blo 1258447 1258631 := bstep (se 1 (by rfl) ⟨943973, by rfl⟩ : syracuseStep 1258631 = 1887947) B1887947
theorem B1258639 : Blo 1258447 1258639 := bstep (se 1 (by rfl) ⟨943979, by rfl⟩ : syracuseStep 1258639 = 1887959) B1887959
theorem B1889423 : Blo 1258447 1889423 := bstep (se 1 (by rfl) ⟨1417067, by rfl⟩ : syracuseStep 1889423 = 2834135) B2834135
theorem B2831507 : Blo 1258447 2831507 := bstep (se 1 (by rfl) ⟨2123630, by rfl⟩ : syracuseStep 2831507 = 4247261) B4247261
theorem B1889465 : Blo 1258447 1889465 := bstep (se 2 (by rfl) ⟨708549, by rfl⟩ : syracuseStep 1889465 = 1417099) B1417099
theorem B1258683 : Blo 1258447 1258683 := bstep (se 1 (by rfl) ⟨944012, by rfl⟩ : syracuseStep 1258683 = 1888025) B1888025
theorem B2831561 : Blo 1258447 2831561 := bstep (se 2 (by rfl) ⟨1061835, by rfl⟩ : syracuseStep 2831561 = 2123671) B2123671
theorem B1258759 : Blo 1258447 1258759 := bstep (se 1 (by rfl) ⟨944069, by rfl⟩ : syracuseStep 1258759 = 1888139) B1888139
theorem B1889543 : Blo 1258447 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B1258767 : Blo 1258447 1258767 := bstep (se 1 (by rfl) ⟨944075, by rfl⟩ : syracuseStep 1258767 = 1888151) B1888151
theorem B3585313 : Blo 1258447 3585313 := bstep (se 2 (by rfl) ⟨1344492, by rfl⟩ : syracuseStep 3585313 = 2688985) B2688985
theorem B1889579 : Blo 1258447 1889579 := bstep (se 1 (by rfl) ⟨1417184, by rfl⟩ : syracuseStep 1889579 = 2834369) B2834369
theorem B1594667 : Blo 1258447 1594667 := bstep (se 1 (by rfl) ⟨1196000, by rfl⟩ : syracuseStep 1594667 = 2392001) B2392001
theorem B1258811 : Blo 1258447 1258811 := bstep (se 1 (by rfl) ⟨944108, by rfl⟩ : syracuseStep 1258811 = 1888217) B1888217
theorem B1889609 : Blo 1258447 1889609 := bstep (se 2 (by rfl) ⟨708603, by rfl⟩ : syracuseStep 1889609 = 1417207) B1417207
theorem B1258887 : Blo 1258447 1258887 := bstep (se 1 (by rfl) ⟨944165, by rfl⟩ : syracuseStep 1258887 = 1888331) B1888331
theorem B1258895 : Blo 1258447 1258895 := bstep (se 1 (by rfl) ⟨944171, by rfl⟩ : syracuseStep 1258895 = 1888343) B1888343
theorem B7173521 : Blo 1258447 7173521 := bstep (se 2 (by rfl) ⟨2690070, by rfl⟩ : syracuseStep 7173521 = 5380141) B5380141
theorem B1258939 : Blo 1258447 1258939 := bstep (se 1 (by rfl) ⟨944204, by rfl⟩ : syracuseStep 1258939 = 1888409) B1888409
theorem B1889723 : Blo 1258447 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B1889783 : Blo 1258447 1889783 := bstep (se 1 (by rfl) ⟨1417337, by rfl⟩ : syracuseStep 1889783 = 2834675) B2834675
theorem B1259015 : Blo 1258447 1259015 := bstep (se 1 (by rfl) ⟨944261, by rfl⟩ : syracuseStep 1259015 = 1888523) B1888523
theorem B1259023 : Blo 1258447 1259023 := bstep (se 1 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 1259023 = 1888535) B1888535
theorem B1889807 : Blo 1258447 1889807 := bstep (se 1 (by rfl) ⟨1417355, by rfl⟩ : syracuseStep 1889807 = 2834711) B2834711
theorem B1889849 : Blo 1258447 1889849 := bstep (se 2 (by rfl) ⟨708693, by rfl⟩ : syracuseStep 1889849 = 1417387) B1417387
theorem B1259067 : Blo 1258447 1259067 := bstep (se 1 (by rfl) ⟨944300, by rfl⟩ : syracuseStep 1259067 = 1888601) B1888601
theorem B2553403 : Blo 1258447 2553403 := bstep (se 1 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 2553403 = 3830105) B3830105
theorem B1259143 : Blo 1258447 1259143 := bstep (se 1 (by rfl) ⟨944357, by rfl⟩ : syracuseStep 1259143 = 1888715) B1888715
theorem B1889927 : Blo 1258447 1889927 := bstep (se 1 (by rfl) ⟨1417445, by rfl⟩ : syracuseStep 1889927 = 2834891) B2834891
theorem B1259151 : Blo 1258447 1259151 := bstep (se 1 (by rfl) ⟨944363, by rfl⟩ : syracuseStep 1259151 = 1888727) B1888727
theorem B1889963 : Blo 1258447 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B1259195 : Blo 1258447 1259195 := bstep (se 1 (by rfl) ⟨944396, by rfl⟩ : syracuseStep 1259195 = 1888793) B1888793
theorem B1889993 : Blo 1258447 1889993 := bstep (se 2 (by rfl) ⟨708747, by rfl⟩ : syracuseStep 1889993 = 1417495) B1417495
theorem B20412161 : Blo 1258447 20412161 := bstep (se 2 (by rfl) ⟨7654560, by rfl⟩ : syracuseStep 20412161 = 15309121) B15309121
theorem B1259271 : Blo 1258447 1259271 := bstep (se 1 (by rfl) ⟨944453, by rfl⟩ : syracuseStep 1259271 = 1888907) B1888907
theorem B1595143 : Blo 1258447 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B1259279 : Blo 1258447 1259279 := bstep (se 1 (by rfl) ⟨944459, by rfl⟩ : syracuseStep 1259279 = 1888919) B1888919
theorem B1259323 : Blo 1258447 1259323 := bstep (se 1 (by rfl) ⟨944492, by rfl⟩ : syracuseStep 1259323 = 1888985) B1888985
theorem B1890107 : Blo 1258447 1890107 := bstep (se 1 (by rfl) ⟨1417580, by rfl⟩ : syracuseStep 1890107 = 2835161) B2835161
theorem B1890167 : Blo 1258447 1890167 := bstep (se 1 (by rfl) ⟨1417625, by rfl⟩ : syracuseStep 1890167 = 2835251) B2835251
theorem B2832263 : Blo 1258447 2832263 := bstep (se 1 (by rfl) ⟨2124197, by rfl⟩ : syracuseStep 2832263 = 4248395) B4248395
theorem B1259399 : Blo 1258447 1259399 := bstep (se 1 (by rfl) ⟨944549, by rfl⟩ : syracuseStep 1259399 = 1889099) B1889099
theorem B1259407 : Blo 1258447 1259407 := bstep (se 1 (by rfl) ⟨944555, by rfl⟩ : syracuseStep 1259407 = 1889111) B1889111
theorem B1890191 : Blo 1258447 1890191 := bstep (se 1 (by rfl) ⟨1417643, by rfl⟩ : syracuseStep 1890191 = 2835287) B2835287
theorem B14931863 : Blo 1258447 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B4249529 : Blo 1258447 4249529 := bstep (se 2 (by rfl) ⟨1593573, by rfl⟩ : syracuseStep 4249529 = 3187147) B3187147
theorem B1890233 : Blo 1258447 1890233 := bstep (se 2 (by rfl) ⟨708837, by rfl⟩ : syracuseStep 1890233 = 1417675) B1417675
theorem B1259451 : Blo 1258447 1259451 := bstep (se 1 (by rfl) ⟨944588, by rfl⟩ : syracuseStep 1259451 = 1889177) B1889177
theorem B1259527 : Blo 1258447 1259527 := bstep (se 1 (by rfl) ⟨944645, by rfl⟩ : syracuseStep 1259527 = 1889291) B1889291
theorem B1890311 : Blo 1258447 1890311 := bstep (se 1 (by rfl) ⟨1417733, by rfl⟩ : syracuseStep 1890311 = 2835467) B2835467
theorem B1259535 : Blo 1258447 1259535 := bstep (se 1 (by rfl) ⟨944651, by rfl⟩ : syracuseStep 1259535 = 1889303) B1889303
theorem B1890347 : Blo 1258447 1890347 := bstep (se 1 (by rfl) ⟨1417760, by rfl⟩ : syracuseStep 1890347 = 2835521) B2835521
theorem B2832443 : Blo 1258447 2832443 := bstep (se 1 (by rfl) ⟨2124332, by rfl⟩ : syracuseStep 2832443 = 4248665) B4248665
theorem B1259579 : Blo 1258447 1259579 := bstep (se 1 (by rfl) ⟨944684, by rfl⟩ : syracuseStep 1259579 = 1889369) B1889369
theorem B5380157 : Blo 1258447 5380157 := bstep (se 3 (by rfl) ⟨1008779, by rfl⟩ : syracuseStep 5380157 = 2017559) B2017559
theorem B1890377 : Blo 1258447 1890377 := bstep (se 2 (by rfl) ⟨708891, by rfl⟩ : syracuseStep 1890377 = 1417783) B1417783
theorem B1259655 : Blo 1258447 1259655 := bstep (se 1 (by rfl) ⟨944741, by rfl⟩ : syracuseStep 1259655 = 1889483) B1889483
theorem B1259663 : Blo 1258447 1259663 := bstep (se 1 (by rfl) ⟨944747, by rfl⟩ : syracuseStep 1259663 = 1889495) B1889495
theorem B2832569 : Blo 1258447 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B1259707 : Blo 1258447 1259707 := bstep (se 1 (by rfl) ⟨944780, by rfl⟩ : syracuseStep 1259707 = 1889561) B1889561
theorem B1890491 : Blo 1258447 1890491 := bstep (se 1 (by rfl) ⟨1417868, by rfl⟩ : syracuseStep 1890491 = 2835737) B2835737
theorem B1792201 : Blo 1258447 1792201 := bstep (se 2 (by rfl) ⟨672075, by rfl⟩ : syracuseStep 1792201 = 1344151) B1344151
theorem B14342345 : Blo 1258447 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B6379721 : Blo 1258447 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B1890551 : Blo 1258447 1890551 := bstep (se 1 (by rfl) ⟨1417913, by rfl⟩ : syracuseStep 1890551 = 2835827) B2835827
theorem B1259783 : Blo 1258447 1259783 := bstep (se 1 (by rfl) ⟨944837, by rfl⟩ : syracuseStep 1259783 = 1889675) B1889675
theorem B1259791 : Blo 1258447 1259791 := bstep (se 1 (by rfl) ⟨944843, by rfl⟩ : syracuseStep 1259791 = 1889687) B1889687
theorem B1890575 : Blo 1258447 1890575 := bstep (se 1 (by rfl) ⟨1417931, by rfl⟩ : syracuseStep 1890575 = 2835863) B2835863
theorem B1890617 : Blo 1258447 1890617 := bstep (se 2 (by rfl) ⟨708981, by rfl⟩ : syracuseStep 1890617 = 1417963) B1417963
theorem B1792315 : Blo 1258447 1792315 := bstep (se 1 (by rfl) ⟨1344236, by rfl⟩ : syracuseStep 1792315 = 2688473) B2688473
theorem B1259835 : Blo 1258447 1259835 := bstep (se 1 (by rfl) ⟨944876, by rfl⟩ : syracuseStep 1259835 = 1889753) B1889753
theorem B1259911 : Blo 1258447 1259911 := bstep (se 1 (by rfl) ⟨944933, by rfl⟩ : syracuseStep 1259911 = 1889867) B1889867
theorem B1259919 : Blo 1258447 1259919 := bstep (se 1 (by rfl) ⟨944939, by rfl⟩ : syracuseStep 1259919 = 1889879) B1889879
theorem B12097937 : Blo 1258447 12097937 := bstep (se 2 (by rfl) ⟨4536726, by rfl⟩ : syracuseStep 12097937 = 9073453) B9073453
theorem B24205715 : Blo 1258447 24205715 := bstep (se 1 (by rfl) ⟨18154286, by rfl⟩ : syracuseStep 24205715 = 36308573) B36308573
theorem B5380499 : Blo 1258447 5380499 := bstep (se 1 (by rfl) ⟨4035374, by rfl⟩ : syracuseStep 5380499 = 8070749) B8070749
theorem B1259963 : Blo 1258447 1259963 := bstep (se 1 (by rfl) ⟨944972, by rfl⟩ : syracuseStep 1259963 = 1889945) B1889945
theorem B1260039 : Blo 1258447 1260039 := bstep (se 1 (by rfl) ⟨945029, by rfl⟩ : syracuseStep 1260039 = 1890059) B1890059
theorem B4250123 : Blo 1258447 4250123 := bstep (se 1 (by rfl) ⟨3187592, by rfl⟩ : syracuseStep 4250123 = 6375185) B6375185
theorem B2832911 : Blo 1258447 2832911 := bstep (se 1 (by rfl) ⟨2124683, by rfl⟩ : syracuseStep 2832911 = 4249367) B4249367
theorem B2390543 : Blo 1258447 2390543 := bstep (se 1 (by rfl) ⟨1792907, by rfl⟩ : syracuseStep 2390543 = 3585815) B3585815
theorem B1260047 : Blo 1258447 1260047 := bstep (se 1 (by rfl) ⟨945035, by rfl⟩ : syracuseStep 1260047 = 1890071) B1890071
theorem B3586589 : Blo 1258447 3586589 := bstep (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) B1344971
theorem B2832929 : Blo 1258447 2832929 := bstep (se 2 (by rfl) ⟨1062348, by rfl⟩ : syracuseStep 2832929 = 2124697) B2124697
theorem B4782635 : Blo 1258447 4782635 := bstep (se 1 (by rfl) ⟨3586976, by rfl⟩ : syracuseStep 4782635 = 7173953) B7173953
theorem B1260091 : Blo 1258447 1260091 := bstep (se 1 (by rfl) ⟨945068, by rfl⟩ : syracuseStep 1260091 = 1890137) B1890137
theorem B21502583 : Blo 1258447 21502583 := bstep (se 1 (by rfl) ⟨16126937, by rfl⟩ : syracuseStep 21502583 = 32253875) B32253875
theorem B9558647 : Blo 1258447 9558647 := bstep (se 1 (by rfl) ⟨7168985, by rfl⟩ : syracuseStep 9558647 = 14337971) B14337971
theorem B4250231 : Blo 1258447 4250231 := bstep (se 1 (by rfl) ⟨3187673, by rfl⟩ : syracuseStep 4250231 = 6375347) B6375347
theorem B1260167 : Blo 1258447 1260167 := bstep (se 1 (by rfl) ⟨945125, by rfl⟩ : syracuseStep 1260167 = 1890251) B1890251
theorem B1260175 : Blo 1258447 1260175 := bstep (se 1 (by rfl) ⟨945131, by rfl⟩ : syracuseStep 1260175 = 1890263) B1890263
theorem B1260219 : Blo 1258447 1260219 := bstep (se 1 (by rfl) ⟨945164, by rfl⟩ : syracuseStep 1260219 = 1890329) B1890329
theorem B3586817 : Blo 1258447 3586817 := bstep (se 2 (by rfl) ⟨1345056, by rfl⟩ : syracuseStep 3586817 = 2690113) B2690113
theorem B1260295 : Blo 1258447 1260295 := bstep (se 1 (by rfl) ⟨945221, by rfl⟩ : syracuseStep 1260295 = 1890443) B1890443
theorem B1260303 : Blo 1258447 1260303 := bstep (se 1 (by rfl) ⟨945227, by rfl⟩ : syracuseStep 1260303 = 1890455) B1890455
theorem B1260347 : Blo 1258447 1260347 := bstep (se 1 (by rfl) ⟨945260, by rfl⟩ : syracuseStep 1260347 = 1890521) B1890521
theorem B3185527 : Blo 1258447 3185527 := bstep (se 1 (by rfl) ⟨2389145, by rfl⟩ : syracuseStep 3185527 = 4778291) B4778291
theorem B2833271 : Blo 1258447 2833271 := bstep (se 1 (by rfl) ⟨2124953, by rfl⟩ : syracuseStep 2833271 = 4249907) B4249907
theorem B1260423 : Blo 1258447 1260423 := bstep (se 1 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 1260423 = 1890635) B1890635
theorem B1260431 : Blo 1258447 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B1416199 : Blo 1258447 1416199 := bstep (se 1 (by rfl) ⟨1062149, by rfl⟩ : syracuseStep 1416199 = 2124299) B2124299
theorem B7658525 : Blo 1258447 7658525 := bstep (se 3 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 7658525 = 2871947) B2871947
theorem B2874401 : Blo 1258447 2874401 := bstep (se 2 (by rfl) ⟨1077900, by rfl⟩ : syracuseStep 2874401 = 2155801) B2155801
theorem B2833451 : Blo 1258447 2833451 := bstep (se 1 (by rfl) ⟨2125088, by rfl⟩ : syracuseStep 2833451 = 4250177) B4250177
theorem B3587159 : Blo 1258447 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B1416379 : Blo 1258447 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B13098185 : Blo 1258447 13098185 := bstep (se 2 (by rfl) ⟨4911819, by rfl⟩ : syracuseStep 13098185 = 9823639) B9823639
theorem B4250825 : Blo 1258447 4250825 := bstep (se 2 (by rfl) ⟨1594059, by rfl⟩ : syracuseStep 4250825 = 3188119) B3188119
theorem B3587273 : Blo 1258447 3587273 := bstep (se 2 (by rfl) ⟨1345227, by rfl⟩ : syracuseStep 3587273 = 2690455) B2690455
theorem B1277191 : Blo 1258447 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B3185963 : Blo 1258447 3185963 := bstep (se 1 (by rfl) ⟨2389472, by rfl⟩ : syracuseStep 3185963 = 4778945) B4778945
theorem B4603195 : Blo 1258447 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B6372755 : Blo 1258447 6372755 := bstep (se 1 (by rfl) ⟨4779566, by rfl⟩ : syracuseStep 6372755 = 9559133) B9559133
theorem B2833811 : Blo 1258447 2833811 := bstep (se 1 (by rfl) ⟨2125358, by rfl⟩ : syracuseStep 2833811 = 4250717) B4250717
theorem B2833865 : Blo 1258447 2833865 := bstep (se 2 (by rfl) ⟨1062699, by rfl⟩ : syracuseStep 2833865 = 2125399) B2125399
theorem B9559619 : Blo 1258447 9559619 := bstep (se 1 (by rfl) ⟨7169714, by rfl⟩ : syracuseStep 9559619 = 14339429) B14339429
theorem B6553207 : Blo 1258447 6553207 := bstep (se 1 (by rfl) ⟨4914905, by rfl⟩ : syracuseStep 6553207 = 9829811) B9829811
theorem B1416847 : Blo 1258447 1416847 := bstep (se 1 (by rfl) ⟨1062635, by rfl⟩ : syracuseStep 1416847 = 2125271) B2125271
theorem B7167689 : Blo 1258447 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B24207173 : Blo 1258447 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B7659353 : Blo 1258447 7659353 := bstep (se 2 (by rfl) ⟨2872257, by rfl⟩ : syracuseStep 7659353 = 5744515) B5744515
theorem B4251527 : Blo 1258447 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B1793927 : Blo 1258447 1793927 := bstep (se 1 (by rfl) ⟨1345445, by rfl⟩ : syracuseStep 1793927 = 2690891) B2690891
theorem B2834603 : Blo 1258447 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B3186935 : Blo 1258447 3186935 := bstep (se 1 (by rfl) ⟨2390201, by rfl⟩ : syracuseStep 3186935 = 4780403) B4780403
theorem B1417567 : Blo 1258447 1417567 := bstep (se 1 (by rfl) ⟨1063175, by rfl⟩ : syracuseStep 1417567 = 2126351) B2126351
theorem B3588457 : Blo 1258447 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B1794479 : Blo 1258447 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B1343963 : Blo 1258447 1343963 := bstep (se 1 (by rfl) ⟨1007972, by rfl⟩ : syracuseStep 1343963 = 2015945) B2015945
theorem B3588617 : Blo 1258447 3588617 := bstep (se 2 (by rfl) ⟨1345731, by rfl⟩ : syracuseStep 3588617 = 2691463) B2691463
theorem B4252283 : Blo 1258447 4252283 := bstep (se 1 (by rfl) ⟨3189212, by rfl⟩ : syracuseStep 4252283 = 6378425) B6378425
theorem B3588731 : Blo 1258447 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B2835143 : Blo 1258447 2835143 := bstep (se 1 (by rfl) ⟨2126357, by rfl⟩ : syracuseStep 2835143 = 4252715) B4252715
theorem B1417927 : Blo 1258447 1417927 := bstep (se 1 (by rfl) ⟨1063445, by rfl⟩ : syracuseStep 1417927 = 2126891) B2126891
theorem B15327953 : Blo 1258447 15327953 := bstep (se 2 (by rfl) ⟨5747982, by rfl⟩ : syracuseStep 15327953 = 11495965) B11495965
theorem B3588857 : Blo 1258447 3588857 := bstep (se 2 (by rfl) ⟨1345821, by rfl⟩ : syracuseStep 3588857 = 2691643) B2691643
theorem B4252445 : Blo 1258447 4252445 := bstep (se 3 (by rfl) ⟨797333, by rfl⟩ : syracuseStep 4252445 = 1594667) B1594667
theorem B2016175 : Blo 1258447 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B2589775 : Blo 1258447 2589775 := bstep (se 1 (by rfl) ⟨1942331, by rfl⟩ : syracuseStep 2589775 = 3884663) B3884663
theorem B7177369 : Blo 1258447 7177369 := bstep (se 2 (by rfl) ⟨2691513, by rfl⟩ : syracuseStep 7177369 = 5383027) B5383027
theorem B13608107 : Blo 1258447 13608107 := bstep (se 1 (by rfl) ⟨10206080, by rfl⟩ : syracuseStep 13608107 = 20412161) B20412161
theorem B9954575 : Blo 1258447 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B4785551 : Blo 1258447 4785551 := bstep (se 1 (by rfl) ⟨3589163, by rfl⟩ : syracuseStep 4785551 = 7178327) B7178327
theorem B9561563 : Blo 1258447 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B4253147 : Blo 1258447 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B5604851 : Blo 1258447 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B2836007 : Blo 1258447 2836007 := bstep (se 1 (by rfl) ⟨2127005, by rfl⟩ : syracuseStep 2836007 = 4254011) B4254011
theorem B3188423 : Blo 1258447 3188423 := bstep (se 1 (by rfl) ⟨2391317, by rfl⟩ : syracuseStep 3188423 = 4782635) B4782635
theorem B6137593 : Blo 1258447 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B16148261 : Blo 1258447 16148261 := bstep (se 4 (by rfl) ⟨1513899, by rfl⟩ : syracuseStep 16148261 = 3027799) B3027799
theorem B36800315 : Blo 1258447 36800315 := bstep (se 1 (by rfl) ⟨27600236, by rfl⟩ : syracuseStep 36800315 = 55200473) B55200473
theorem B27223897 : Blo 1258447 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B3229627 : Blo 1258447 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B9562049 : Blo 1258447 9562049 := bstep (se 2 (by rfl) ⟨3585768, by rfl⟩ : syracuseStep 9562049 = 7171537) B7171537
theorem B9570311 : Blo 1258447 9570311 := bstep (se 1 (by rfl) ⟨7177733, by rfl⟩ : syracuseStep 9570311 = 14355467) B14355467
theorem B5105683 : Blo 1258447 5105683 := bstep (se 1 (by rfl) ⟨3829262, by rfl⟩ : syracuseStep 5105683 = 7658525) B7658525
theorem B2123833 : Blo 1258447 2123833 := bstep (se 2 (by rfl) ⟨796437, by rfl⟩ : syracuseStep 2123833 = 1592875) B1592875
theorem B4253849 : Blo 1258447 4253849 := bstep (se 2 (by rfl) ⟨1595193, by rfl⟩ : syracuseStep 4253849 = 3190387) B3190387
theorem B2123975 : Blo 1258447 2123975 := bstep (se 1 (by rfl) ⟨1592981, by rfl⟩ : syracuseStep 2123975 = 3185963) B3185963
theorem B2124137 : Blo 1258447 2124137 := bstep (se 2 (by rfl) ⟨796551, by rfl⟩ : syracuseStep 2124137 = 1593103) B1593103
theorem B4778459 : Blo 1258447 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B9570797 : Blo 1258447 9570797 := bstep (se 3 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 9570797 = 3589049) B3589049
theorem B5106235 : Blo 1258447 5106235 := bstep (se 1 (by rfl) ⟨3829676, by rfl⟩ : syracuseStep 5106235 = 7659353) B7659353
theorem B6375995 : Blo 1258447 6375995 := bstep (se 1 (by rfl) ⟨4781996, by rfl⟩ : syracuseStep 6375995 = 9563993) B9563993
theorem B2017963 : Blo 1258447 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B4033223 : Blo 1258447 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B2124535 : Blo 1258447 2124535 := bstep (se 1 (by rfl) ⟨1593401, by rfl⟩ : syracuseStep 2124535 = 3186803) B3186803
theorem B4033273 : Blo 1258447 4033273 := bstep (se 2 (by rfl) ⟨1512477, by rfl⟩ : syracuseStep 4033273 = 3024955) B3024955
theorem B3189577 : Blo 1258447 3189577 := bstep (se 2 (by rfl) ⟨1196091, by rfl⟩ : syracuseStep 3189577 = 2392183) B2392183
theorem B8072081 : Blo 1258447 8072081 := bstep (se 2 (by rfl) ⟨3027030, by rfl⟩ : syracuseStep 8072081 = 6054061) B6054061
theorem B2124731 : Blo 1258447 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B17239013 : Blo 1258447 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B9071635 : Blo 1258447 9071635 := bstep (se 1 (by rfl) ⟨6803726, by rfl⟩ : syracuseStep 9071635 = 13607453) B13607453
theorem B2124839 : Blo 1258447 2124839 := bstep (se 1 (by rfl) ⟨1593629, by rfl⟩ : syracuseStep 2124839 = 3187259) B3187259
theorem B6376643 : Blo 1258447 6376643 := bstep (se 1 (by rfl) ⟨4782482, by rfl⟩ : syracuseStep 6376643 = 9564965) B9564965
theorem B34950437 : Blo 1258447 34950437 := bstep (se 4 (by rfl) ⟨3276603, by rfl⟩ : syracuseStep 34950437 = 6553207) B6553207
theorem B2125129 : Blo 1258447 2125129 := bstep (se 2 (by rfl) ⟨796923, by rfl⟩ : syracuseStep 2125129 = 1593847) B1593847
theorem B2125163 : Blo 1258447 2125163 := bstep (se 1 (by rfl) ⟨1593872, by rfl⟩ : syracuseStep 2125163 = 3187745) B3187745
theorem B9563507 : Blo 1258447 9563507 := bstep (se 1 (by rfl) ⟨7172630, by rfl⟩ : syracuseStep 9563507 = 14345261) B14345261
theorem B5377423 : Blo 1258447 5377423 := bstep (se 1 (by rfl) ⟨4033067, by rfl⟩ : syracuseStep 5377423 = 8066135) B8066135
theorem B1887671 : Blo 1258447 1887671 := bstep (se 1 (by rfl) ⟨1415753, by rfl⟩ : syracuseStep 1887671 = 2831507) B2831507
theorem B1887707 : Blo 1258447 1887707 := bstep (se 1 (by rfl) ⟨1415780, by rfl⟩ : syracuseStep 1887707 = 2831561) B2831561
theorem B7663243 : Blo 1258447 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B4779719 : Blo 1258447 4779719 := bstep (se 1 (by rfl) ⟨3584789, by rfl⟩ : syracuseStep 4779719 = 7169579) B7169579
theorem B2125561 : Blo 1258447 2125561 := bstep (se 2 (by rfl) ⟨797085, by rfl⟩ : syracuseStep 2125561 = 1594171) B1594171
theorem B4247369 : Blo 1258447 4247369 := bstep (se 2 (by rfl) ⟨1592763, by rfl⟩ : syracuseStep 4247369 = 3185527) B3185527
theorem B2551657 : Blo 1258447 2551657 := bstep (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) B1913743
theorem B9203591 : Blo 1258447 9203591 := bstep (se 1 (by rfl) ⟨6902693, by rfl⟩ : syracuseStep 9203591 = 13805387) B13805387
theorem B1888175 : Blo 1258447 1888175 := bstep (se 1 (by rfl) ⟨1416131, by rfl⟩ : syracuseStep 1888175 = 2832263) B2832263
theorem B2125831 : Blo 1258447 2125831 := bstep (se 1 (by rfl) ⟨1594373, by rfl⟩ : syracuseStep 2125831 = 3188747) B3188747
theorem B1888265 : Blo 1258447 1888265 := bstep (se 2 (by rfl) ⟨708099, by rfl⟩ : syracuseStep 1888265 = 1416199) B1416199
theorem B6811685 : Blo 1258447 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B1888295 : Blo 1258447 1888295 := bstep (se 1 (by rfl) ⟨1416221, by rfl⟩ : syracuseStep 1888295 = 2832443) B2832443
theorem B1888379 : Blo 1258447 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B1888505 : Blo 1258447 1888505 := bstep (se 2 (by rfl) ⟨708189, by rfl⟩ : syracuseStep 1888505 = 1416379) B1416379
theorem B8065291 : Blo 1258447 8065291 := bstep (se 1 (by rfl) ⟨6048968, by rfl⟩ : syracuseStep 8065291 = 12097937) B12097937
theorem B1888607 : Blo 1258447 1888607 := bstep (se 1 (by rfl) ⟨1416455, by rfl⟩ : syracuseStep 1888607 = 2832911) B2832911
theorem B1593695 : Blo 1258447 1593695 := bstep (se 1 (by rfl) ⟨1195271, by rfl⟩ : syracuseStep 1593695 = 2390543) B2390543
theorem B1888619 : Blo 1258447 1888619 := bstep (se 1 (by rfl) ⟨1416464, by rfl⟩ : syracuseStep 1888619 = 2832929) B2832929
theorem B10752385 : Blo 1258447 10752385 := bstep (se 2 (by rfl) ⟨4032144, by rfl⟩ : syracuseStep 10752385 = 8064289) B8064289
theorem B4780417 : Blo 1258447 4780417 := bstep (se 2 (by rfl) ⟨1792656, by rfl⟩ : syracuseStep 4780417 = 3585313) B3585313
theorem B2126263 : Blo 1258447 2126263 := bstep (se 1 (by rfl) ⟨1594697, by rfl⟩ : syracuseStep 2126263 = 3189395) B3189395
theorem B1888847 : Blo 1258447 1888847 := bstep (se 1 (by rfl) ⟨1416635, by rfl⟩ : syracuseStep 1888847 = 2833271) B2833271
theorem B2126459 : Blo 1258447 2126459 := bstep (se 1 (by rfl) ⟨1594844, by rfl⟩ : syracuseStep 2126459 = 3189689) B3189689
theorem B4780691 : Blo 1258447 4780691 := bstep (se 1 (by rfl) ⟨3585518, by rfl⟩ : syracuseStep 4780691 = 7171037) B7171037
theorem B1888967 : Blo 1258447 1888967 := bstep (se 1 (by rfl) ⟨1416725, by rfl⟩ : syracuseStep 1888967 = 2833451) B2833451
theorem B3404537 : Blo 1258447 3404537 := bstep (se 2 (by rfl) ⟨1276701, by rfl⟩ : syracuseStep 3404537 = 2553403) B2553403
theorem B1889129 : Blo 1258447 1889129 := bstep (se 2 (by rfl) ⟨708423, by rfl⟩ : syracuseStep 1889129 = 1416847) B1416847
theorem B4248503 : Blo 1258447 4248503 := bstep (se 1 (by rfl) ⟨3186377, by rfl⟩ : syracuseStep 4248503 = 6372755) B6372755
theorem B1889207 : Blo 1258447 1889207 := bstep (se 1 (by rfl) ⟨1416905, by rfl⟩ : syracuseStep 1889207 = 2833811) B2833811
theorem B1258459 : Blo 1258447 1258459 := bstep (se 1 (by rfl) ⟨943844, by rfl⟩ : syracuseStep 1258459 = 1887689) B1887689
theorem B1889243 : Blo 1258447 1889243 := bstep (se 1 (by rfl) ⟨1416932, by rfl⟩ : syracuseStep 1889243 = 2833865) B2833865
theorem B2126857 : Blo 1258447 2126857 := bstep (se 2 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 2126857 = 1595143) B1595143
theorem B1258535 : Blo 1258447 1258535 := bstep (se 1 (by rfl) ⟨943901, by rfl⟩ : syracuseStep 1258535 = 1887803) B1887803
theorem B19379249 : Blo 1258447 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B1258575 : Blo 1258447 1258575 := bstep (se 1 (by rfl) ⟨943931, by rfl⟩ : syracuseStep 1258575 = 1887863) B1887863
theorem B1258591 : Blo 1258447 1258591 := bstep (se 1 (by rfl) ⟨943943, by rfl⟩ : syracuseStep 1258591 = 1887887) B1887887
theorem B2389115 : Blo 1258447 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B1258619 : Blo 1258447 1258619 := bstep (se 1 (by rfl) ⟨943964, by rfl⟩ : syracuseStep 1258619 = 1887929) B1887929
theorem B1258671 : Blo 1258447 1258671 := bstep (se 1 (by rfl) ⟨944003, by rfl⟩ : syracuseStep 1258671 = 1888007) B1888007
theorem B1258695 : Blo 1258447 1258695 := bstep (se 1 (by rfl) ⟨944021, by rfl⟩ : syracuseStep 1258695 = 1888043) B1888043
theorem B1258715 : Blo 1258447 1258715 := bstep (se 1 (by rfl) ⟨944036, by rfl⟩ : syracuseStep 1258715 = 1888073) B1888073
theorem B1258791 : Blo 1258447 1258791 := bstep (se 1 (by rfl) ⟨944093, by rfl⟩ : syracuseStep 1258791 = 1888187) B1888187
theorem B1258831 : Blo 1258447 1258831 := bstep (se 1 (by rfl) ⟨944123, by rfl⟩ : syracuseStep 1258831 = 1888247) B1888247
theorem B1258847 : Blo 1258447 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B1258875 : Blo 1258447 1258875 := bstep (se 1 (by rfl) ⟨944156, by rfl⟩ : syracuseStep 1258875 = 1888313) B1888313
theorem B2831759 : Blo 1258447 2831759 := bstep (se 1 (by rfl) ⟨2123819, by rfl⟩ : syracuseStep 2831759 = 4247639) B4247639
theorem B1258927 : Blo 1258447 1258927 := bstep (se 1 (by rfl) ⟨944195, by rfl⟩ : syracuseStep 1258927 = 1888391) B1888391
theorem B1889711 : Blo 1258447 1889711 := bstep (se 1 (by rfl) ⟨1417283, by rfl⟩ : syracuseStep 1889711 = 2834567) B2834567
theorem B1660343 : Blo 1258447 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B1258951 : Blo 1258447 1258951 := bstep (se 1 (by rfl) ⟨944213, by rfl⟩ : syracuseStep 1258951 = 1888427) B1888427
theorem B2422235 : Blo 1258447 2422235 := bstep (se 1 (by rfl) ⟨1816676, by rfl⟩ : syracuseStep 2422235 = 3633353) B3633353
theorem B1258971 : Blo 1258447 1258971 := bstep (se 1 (by rfl) ⟨944228, by rfl⟩ : syracuseStep 1258971 = 1888457) B1888457
theorem B4249097 : Blo 1258447 4249097 := bstep (se 2 (by rfl) ⟨1593411, by rfl⟩ : syracuseStep 4249097 = 3186823) B3186823
theorem B1889801 : Blo 1258447 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B1259047 : Blo 1258447 1259047 := bstep (se 1 (by rfl) ⟨944285, by rfl⟩ : syracuseStep 1259047 = 1888571) B1888571
theorem B1889831 : Blo 1258447 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B10212925 : Blo 1258447 10212925 := bstep (se 3 (by rfl) ⟨1914923, by rfl⟩ : syracuseStep 10212925 = 3829847) B3829847
theorem B1259087 : Blo 1258447 1259087 := bstep (se 1 (by rfl) ⟨944315, by rfl⟩ : syracuseStep 1259087 = 1888631) B1888631
theorem B1259103 : Blo 1258447 1259103 := bstep (se 1 (by rfl) ⟨944327, by rfl⟩ : syracuseStep 1259103 = 1888655) B1888655
theorem B2389601 : Blo 1258447 2389601 := bstep (se 2 (by rfl) ⟨896100, by rfl⟩ : syracuseStep 2389601 = 1792201) B1792201
theorem B33166945 : Blo 1258447 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B8074849 : Blo 1258447 8074849 := bstep (se 2 (by rfl) ⟨3028068, by rfl⟩ : syracuseStep 8074849 = 6056137) B6056137
theorem B1259131 : Blo 1258447 1259131 := bstep (se 1 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 1259131 = 1888697) B1888697
theorem B1889915 : Blo 1258447 1889915 := bstep (se 1 (by rfl) ⟨1417436, by rfl⟩ : syracuseStep 1889915 = 2834873) B2834873
theorem B1259183 : Blo 1258447 1259183 := bstep (se 1 (by rfl) ⟨944387, by rfl⟩ : syracuseStep 1259183 = 1888775) B1888775
theorem B1259207 : Blo 1258447 1259207 := bstep (se 1 (by rfl) ⟨944405, by rfl⟩ : syracuseStep 1259207 = 1888811) B1888811
theorem B58177223 : Blo 1258447 58177223 := bstep (se 1 (by rfl) ⟨43632917, by rfl⟩ : syracuseStep 58177223 = 87265835) B87265835
theorem B2832083 : Blo 1258447 2832083 := bstep (se 1 (by rfl) ⟨2124062, by rfl⟩ : syracuseStep 2832083 = 4248125) B4248125
theorem B1259227 : Blo 1258447 1259227 := bstep (se 1 (by rfl) ⟨944420, by rfl⟩ : syracuseStep 1259227 = 1888841) B1888841
theorem B2389753 : Blo 1258447 2389753 := bstep (se 2 (by rfl) ⟨896157, by rfl⟩ : syracuseStep 2389753 = 1792315) B1792315
theorem B1890041 : Blo 1258447 1890041 := bstep (se 2 (by rfl) ⟨708765, by rfl⟩ : syracuseStep 1890041 = 1417531) B1417531
theorem B12113657 : Blo 1258447 12113657 := bstep (se 2 (by rfl) ⟨4542621, by rfl⟩ : syracuseStep 12113657 = 9085243) B9085243
theorem B1259303 : Blo 1258447 1259303 := bstep (se 1 (by rfl) ⟨944477, by rfl⟩ : syracuseStep 1259303 = 1888955) B1888955
theorem B4536107 : Blo 1258447 4536107 := bstep (se 1 (by rfl) ⟨3402080, by rfl⟩ : syracuseStep 4536107 = 6804161) B6804161
theorem B2873161 : Blo 1258447 2873161 := bstep (se 2 (by rfl) ⟨1077435, by rfl⟩ : syracuseStep 2873161 = 2154871) B2154871
theorem B1259343 : Blo 1258447 1259343 := bstep (se 1 (by rfl) ⟨944507, by rfl⟩ : syracuseStep 1259343 = 1889015) B1889015
theorem B1259359 : Blo 1258447 1259359 := bstep (se 1 (by rfl) ⟨944519, by rfl⟩ : syracuseStep 1259359 = 1889039) B1889039
theorem B1890143 : Blo 1258447 1890143 := bstep (se 1 (by rfl) ⟨1417607, by rfl⟩ : syracuseStep 1890143 = 2835215) B2835215
theorem B1890155 : Blo 1258447 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B1259387 : Blo 1258447 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B1259439 : Blo 1258447 1259439 := bstep (se 1 (by rfl) ⟨944579, by rfl⟩ : syracuseStep 1259439 = 1889159) B1889159
theorem B1259463 : Blo 1258447 1259463 := bstep (se 1 (by rfl) ⟨944597, by rfl⟩ : syracuseStep 1259463 = 1889195) B1889195
theorem B1259483 : Blo 1258447 1259483 := bstep (se 1 (by rfl) ⟨944612, by rfl⟩ : syracuseStep 1259483 = 1889225) B1889225
theorem B1259559 : Blo 1258447 1259559 := bstep (se 1 (by rfl) ⟨944669, by rfl⟩ : syracuseStep 1259559 = 1889339) B1889339
theorem B2553895 : Blo 1258447 2553895 := bstep (se 1 (by rfl) ⟨1915421, by rfl⟩ : syracuseStep 2553895 = 3830843) B3830843
theorem B1259599 : Blo 1258447 1259599 := bstep (se 1 (by rfl) ⟨944699, by rfl⟩ : syracuseStep 1259599 = 1889399) B1889399
theorem B1890383 : Blo 1258447 1890383 := bstep (se 1 (by rfl) ⟨1417787, by rfl⟩ : syracuseStep 1890383 = 2835575) B2835575
theorem B1259615 : Blo 1258447 1259615 := bstep (se 1 (by rfl) ⟨944711, by rfl⟩ : syracuseStep 1259615 = 1889423) B1889423
theorem B1259643 : Blo 1258447 1259643 := bstep (se 1 (by rfl) ⟨944732, by rfl⟩ : syracuseStep 1259643 = 1889465) B1889465
theorem B1259695 : Blo 1258447 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B1259719 : Blo 1258447 1259719 := bstep (se 1 (by rfl) ⟨944789, by rfl⟩ : syracuseStep 1259719 = 1889579) B1889579
theorem B1890503 : Blo 1258447 1890503 := bstep (se 1 (by rfl) ⟨1417877, by rfl⟩ : syracuseStep 1890503 = 2835755) B2835755
theorem B1259739 : Blo 1258447 1259739 := bstep (se 1 (by rfl) ⟨944804, by rfl⟩ : syracuseStep 1259739 = 1889609) B1889609
theorem B4782347 : Blo 1258447 4782347 := bstep (se 1 (by rfl) ⟨3586760, by rfl⟩ : syracuseStep 4782347 = 7173521) B7173521
theorem B1259815 : Blo 1258447 1259815 := bstep (se 1 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 1259815 = 1889723) B1889723
theorem B1259855 : Blo 1258447 1259855 := bstep (se 1 (by rfl) ⟨944891, by rfl⟩ : syracuseStep 1259855 = 1889783) B1889783
theorem B1259871 : Blo 1258447 1259871 := bstep (se 1 (by rfl) ⟨944903, by rfl⟩ : syracuseStep 1259871 = 1889807) B1889807
theorem B4249961 : Blo 1258447 4249961 := bstep (se 2 (by rfl) ⟨1593735, by rfl⟩ : syracuseStep 4249961 = 3187471) B3187471
theorem B1890665 : Blo 1258447 1890665 := bstep (se 2 (by rfl) ⟨708999, by rfl⟩ : syracuseStep 1890665 = 1417999) B1417999
theorem B1259899 : Blo 1258447 1259899 := bstep (se 1 (by rfl) ⟨944924, by rfl⟩ : syracuseStep 1259899 = 1889849) B1889849
theorem B1259951 : Blo 1258447 1259951 := bstep (se 1 (by rfl) ⟨944963, by rfl⟩ : syracuseStep 1259951 = 1889927) B1889927
theorem B1259975 : Blo 1258447 1259975 := bstep (se 1 (by rfl) ⟨944981, by rfl⟩ : syracuseStep 1259975 = 1889963) B1889963
theorem B1259995 : Blo 1258447 1259995 := bstep (se 1 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 1259995 = 1889993) B1889993
theorem B1260071 : Blo 1258447 1260071 := bstep (se 1 (by rfl) ⟨945053, by rfl⟩ : syracuseStep 1260071 = 1890107) B1890107
theorem B1260111 : Blo 1258447 1260111 := bstep (se 1 (by rfl) ⟨945083, by rfl⟩ : syracuseStep 1260111 = 1890167) B1890167
theorem B1260127 : Blo 1258447 1260127 := bstep (se 1 (by rfl) ⟨945095, by rfl⟩ : syracuseStep 1260127 = 1890191) B1890191
theorem B1415803 : Blo 1258447 1415803 := bstep (se 1 (by rfl) ⟨1061852, by rfl⟩ : syracuseStep 1415803 = 2123705) B2123705
theorem B2833019 : Blo 1258447 2833019 := bstep (se 1 (by rfl) ⟨2124764, by rfl⟩ : syracuseStep 2833019 = 4249529) B4249529
theorem B1260155 : Blo 1258447 1260155 := bstep (se 1 (by rfl) ⟨945116, by rfl⟩ : syracuseStep 1260155 = 1890233) B1890233
theorem B1260207 : Blo 1258447 1260207 := bstep (se 1 (by rfl) ⟨945155, by rfl⟩ : syracuseStep 1260207 = 1890311) B1890311
theorem B1260231 : Blo 1258447 1260231 := bstep (se 1 (by rfl) ⟨945173, by rfl⟩ : syracuseStep 1260231 = 1890347) B1890347
theorem B3586771 : Blo 1258447 3586771 := bstep (se 1 (by rfl) ⟨2690078, by rfl⟩ : syracuseStep 3586771 = 5380157) B5380157
theorem B9083603 : Blo 1258447 9083603 := bstep (se 1 (by rfl) ⟨6812702, by rfl⟩ : syracuseStep 9083603 = 13625405) B13625405
theorem B1260251 : Blo 1258447 1260251 := bstep (se 1 (by rfl) ⟨945188, by rfl⟩ : syracuseStep 1260251 = 1890377) B1890377
theorem B32266997 : Blo 1258447 32266997 := bstep (se 5 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 32266997 = 3025031) B3025031
theorem B14351093 : Blo 1258447 14351093 := bstep (se 5 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 14351093 = 1345415) B1345415
theorem B2833145 : Blo 1258447 2833145 := bstep (se 2 (by rfl) ⟨1062429, by rfl⟩ : syracuseStep 2833145 = 2124859) B2124859
theorem B1260327 : Blo 1258447 1260327 := bstep (se 1 (by rfl) ⟨945245, by rfl⟩ : syracuseStep 1260327 = 1890491) B1890491
theorem B1260367 : Blo 1258447 1260367 := bstep (se 1 (by rfl) ⟨945275, by rfl⟩ : syracuseStep 1260367 = 1890551) B1890551
theorem B1260383 : Blo 1258447 1260383 := bstep (se 1 (by rfl) ⟨945287, by rfl⟩ : syracuseStep 1260383 = 1890575) B1890575
theorem B1260411 : Blo 1258447 1260411 := bstep (se 1 (by rfl) ⟨945308, by rfl⟩ : syracuseStep 1260411 = 1890617) B1890617
theorem B16137143 : Blo 1258447 16137143 := bstep (se 1 (by rfl) ⟨12102857, by rfl⟩ : syracuseStep 16137143 = 24205715) B24205715
theorem B3586999 : Blo 1258447 3586999 := bstep (se 1 (by rfl) ⟨2690249, by rfl⟩ : syracuseStep 3586999 = 5380499) B5380499
theorem B4250555 : Blo 1258447 4250555 := bstep (se 1 (by rfl) ⟨3187916, by rfl⟩ : syracuseStep 4250555 = 6375833) B6375833
theorem B2833415 : Blo 1258447 2833415 := bstep (se 1 (by rfl) ⟨2125061, by rfl⟩ : syracuseStep 2833415 = 4250123) B4250123
theorem B2391059 : Blo 1258447 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B14335055 : Blo 1258447 14335055 := bstep (se 1 (by rfl) ⟨10751291, by rfl⟩ : syracuseStep 14335055 = 21502583) B21502583
theorem B6372431 : Blo 1258447 6372431 := bstep (se 1 (by rfl) ⟨4779323, by rfl⟩ : syracuseStep 6372431 = 9558647) B9558647
theorem B1416271 : Blo 1258447 1416271 := bstep (se 1 (by rfl) ⟨1062203, by rfl⟩ : syracuseStep 1416271 = 2124407) B2124407
theorem B2833487 : Blo 1258447 2833487 := bstep (se 1 (by rfl) ⟨2125115, by rfl⟩ : syracuseStep 2833487 = 4250231) B4250231
theorem B2391211 : Blo 1258447 2391211 := bstep (se 1 (by rfl) ⟨1793408, by rfl⟩ : syracuseStep 2391211 = 3586817) B3586817
theorem B1916267 : Blo 1258447 1916267 := bstep (se 1 (by rfl) ⟨1437200, by rfl⟩ : syracuseStep 1916267 = 2874401) B2874401
theorem B2391439 : Blo 1258447 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B27246041 : Blo 1258447 27246041 := bstep (se 2 (by rfl) ⟨10217265, by rfl⟩ : syracuseStep 27246041 = 20434531) B20434531
theorem B1416667 : Blo 1258447 1416667 := bstep (se 1 (by rfl) ⟨1062500, by rfl⟩ : syracuseStep 1416667 = 2125001) B2125001
theorem B4660699 : Blo 1258447 4660699 := bstep (se 1 (by rfl) ⟨3495524, by rfl⟩ : syracuseStep 4660699 = 6991049) B6991049
theorem B8732123 : Blo 1258447 8732123 := bstep (se 1 (by rfl) ⟨6549092, by rfl⟩ : syracuseStep 8732123 = 13098185) B13098185
theorem B2833883 : Blo 1258447 2833883 := bstep (se 1 (by rfl) ⟨2125412, by rfl⟩ : syracuseStep 2833883 = 4250825) B4250825
theorem B2391515 : Blo 1258447 2391515 := bstep (se 1 (by rfl) ⟨1793636, by rfl⟩ : syracuseStep 2391515 = 3587273) B3587273
theorem B14343803 : Blo 1258447 14343803 := bstep (se 1 (by rfl) ⟨10757852, by rfl⟩ : syracuseStep 14343803 = 21515705) B21515705
theorem B1793659 : Blo 1258447 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B4783805 : Blo 1258447 4783805 := bstep (se 3 (by rfl) ⟨896963, by rfl⟩ : syracuseStep 4783805 = 1793927) B1793927
theorem B6373079 : Blo 1258447 6373079 := bstep (se 1 (by rfl) ⟨4779809, by rfl⟩ : syracuseStep 6373079 = 9559619) B9559619
theorem B16138115 : Blo 1258447 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B1417135 : Blo 1258447 1417135 := bstep (se 1 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 1417135 = 2125703) B2125703
theorem B2834351 : Blo 1258447 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B2834441 : Blo 1258447 2834441 := bstep (se 2 (by rfl) ⟨1062915, by rfl⟩ : syracuseStep 2834441 = 2125831) B2125831
theorem B6807577 : Blo 1258447 6807577 := bstep (se 2 (by rfl) ⟨2552841, by rfl⟩ : syracuseStep 6807577 = 5105683) B5105683
theorem B2392411 : Blo 1258447 2392411 := bstep (se 1 (by rfl) ⟨1794308, by rfl⟩ : syracuseStep 2392411 = 3588617) B3588617
theorem B13812133 : Blo 1258447 13812133 := bstep (se 4 (by rfl) ⟨1294887, by rfl⟩ : syracuseStep 13812133 = 2589775) B2589775
theorem B2834855 : Blo 1258447 2834855 := bstep (se 1 (by rfl) ⟨2126141, by rfl⟩ : syracuseStep 2834855 = 4252283) B4252283
theorem B1417639 : Blo 1258447 1417639 := bstep (se 1 (by rfl) ⟨1063229, by rfl⟩ : syracuseStep 1417639 = 2126459) B2126459
theorem B2392487 : Blo 1258447 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B3187127 : Blo 1258447 3187127 := bstep (se 1 (by rfl) ⟨2390345, by rfl⟩ : syracuseStep 3187127 = 4780691) B4780691
theorem B4784609 : Blo 1258447 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B2269691 : Blo 1258447 2269691 := bstep (se 1 (by rfl) ⟨1702268, by rfl⟩ : syracuseStep 2269691 = 3404537) B3404537
theorem B2392571 : Blo 1258447 2392571 := bstep (se 1 (by rfl) ⟨1794428, by rfl⟩ : syracuseStep 2392571 = 3588857) B3588857
theorem B14336513 : Blo 1258447 14336513 := bstep (se 2 (by rfl) ⟨5376192, by rfl⟩ : syracuseStep 14336513 = 10752385) B10752385
theorem B6373889 : Blo 1258447 6373889 := bstep (se 2 (by rfl) ⟨2390208, by rfl⟩ : syracuseStep 6373889 = 4780417) B4780417
theorem B2834963 : Blo 1258447 2834963 := bstep (se 1 (by rfl) ⟨2126222, by rfl⟩ : syracuseStep 2834963 = 4252445) B4252445
theorem B2835017 : Blo 1258447 2835017 := bstep (se 2 (by rfl) ⟨1063131, by rfl⟩ : syracuseStep 2835017 = 2126263) B2126263
theorem B12919499 : Blo 1258447 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B6808313 : Blo 1258447 6808313 := bstep (se 2 (by rfl) ⟨2553117, by rfl⟩ : syracuseStep 6808313 = 5106235) B5106235
theorem B6636383 : Blo 1258447 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B1614823 : Blo 1258447 1614823 := bstep (se 1 (by rfl) ⟨1211117, by rfl⟩ : syracuseStep 1614823 = 2422235) B2422235
theorem B6374375 : Blo 1258447 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B2835431 : Blo 1258447 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B3736567 : Blo 1258447 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B4252769 : Blo 1258447 4252769 := bstep (se 2 (by rfl) ⟨1594788, by rfl⟩ : syracuseStep 4252769 = 3189577) B3189577
theorem B20440181 : Blo 1258447 20440181 := bstep (se 5 (by rfl) ⟨958133, by rfl⟩ : syracuseStep 20440181 = 1916267) B1916267
theorem B4785277 : Blo 1258447 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B10765507 : Blo 1258447 10765507 := bstep (se 1 (by rfl) ⟨8074130, by rfl⟩ : syracuseStep 10765507 = 16148261) B16148261
theorem B3024071 : Blo 1258447 3024071 := bstep (se 1 (by rfl) ⟨2268053, by rfl⟩ : syracuseStep 3024071 = 4536107) B4536107
theorem B2688233 : Blo 1258447 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B6374699 : Blo 1258447 6374699 := bstep (se 1 (by rfl) ⟨4781024, by rfl⟩ : syracuseStep 6374699 = 9562049) B9562049
theorem B2835809 : Blo 1258447 2835809 := bstep (se 2 (by rfl) ⟨1063428, by rfl⟩ : syracuseStep 2835809 = 2126857) B2126857
theorem B2835899 : Blo 1258447 2835899 := bstep (se 1 (by rfl) ⟨2126924, by rfl⟩ : syracuseStep 2835899 = 4253849) B4253849
theorem B3188231 : Blo 1258447 3188231 := bstep (se 1 (by rfl) ⟨2391173, by rfl⟩ : syracuseStep 3188231 = 4782347) B4782347
theorem B9569825 : Blo 1258447 9569825 := bstep (se 2 (by rfl) ⟨3588684, by rfl⟩ : syracuseStep 9569825 = 7177369) B7177369
theorem B3188281 : Blo 1258447 3188281 := bstep (se 2 (by rfl) ⟨1195605, by rfl⟩ : syracuseStep 3188281 = 2391211) B2391211
theorem B2688815 : Blo 1258447 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B6055735 : Blo 1258447 6055735 := bstep (se 1 (by rfl) ⟨4541801, by rfl⟩ : syracuseStep 6055735 = 9083603) B9083603
theorem B7169897 : Blo 1258447 7169897 := bstep (se 2 (by rfl) ⟨2688711, by rfl⟩ : syracuseStep 7169897 = 5377423) B5377423
theorem B3188585 : Blo 1258447 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B10758095 : Blo 1258447 10758095 := bstep (se 1 (by rfl) ⟨8068571, by rfl⟩ : syracuseStep 10758095 = 16137143) B16137143
theorem B13617233 : Blo 1258447 13617233 := bstep (se 2 (by rfl) ⟨5106462, by rfl⟩ : syracuseStep 13617233 = 10212925) B10212925
theorem B44222593 : Blo 1258447 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B10766465 : Blo 1258447 10766465 := bstep (se 2 (by rfl) ⟨4037424, by rfl⟩ : syracuseStep 10766465 = 8074849) B8074849
theorem B10217657 : Blo 1258447 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B23300291 : Blo 1258447 23300291 := bstep (se 1 (by rfl) ⟨17475218, by rfl⟩ : syracuseStep 23300291 = 34950437) B34950437
theorem B6375671 : Blo 1258447 6375671 := bstep (se 1 (by rfl) ⟨4781753, by rfl⟩ : syracuseStep 6375671 = 9563507) B9563507
theorem B18164027 : Blo 1258447 18164027 := bstep (se 1 (by rfl) ⟨13623020, by rfl⟩ : syracuseStep 18164027 = 27246041) B27246041
theorem B9562535 : Blo 1258447 9562535 := bstep (se 1 (by rfl) ⟨7171901, by rfl⟩ : syracuseStep 9562535 = 14343803) B14343803
theorem B3189203 : Blo 1258447 3189203 := bstep (se 1 (by rfl) ⟨2391902, by rfl⟩ : syracuseStep 3189203 = 4783805) B4783805
theorem B3402209 : Blo 1258447 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B10758743 : Blo 1258447 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B4541123 : Blo 1258447 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B6376157 : Blo 1258447 6376157 := bstep (se 3 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 6376157 = 2391059) B2391059
theorem B2124623 : Blo 1258447 2124623 := bstep (se 1 (by rfl) ⟨1593467, by rfl⟩ : syracuseStep 2124623 = 3186935) B3186935
theorem B10218635 : Blo 1258447 10218635 := bstep (se 1 (by rfl) ⟨7663976, by rfl⟩ : syracuseStep 10218635 = 15327953) B15327953
theorem B9072071 : Blo 1258447 9072071 := bstep (se 1 (by rfl) ⟨6804053, by rfl⟩ : syracuseStep 9072071 = 13608107) B13608107
theorem B1887737 : Blo 1258447 1887737 := bstep (se 2 (by rfl) ⟨707901, by rfl⟩ : syracuseStep 1887737 = 1415803) B1415803
theorem B1887839 : Blo 1258447 1887839 := bstep (se 1 (by rfl) ⟨1415879, by rfl⟩ : syracuseStep 1887839 = 2831759) B2831759
theorem B3190367 : Blo 1258447 3190367 := bstep (se 1 (by rfl) ⟨2392775, by rfl⟩ : syracuseStep 3190367 = 4785551) B4785551
theorem B5377697 : Blo 1258447 5377697 := bstep (se 2 (by rfl) ⟨2016636, by rfl⟩ : syracuseStep 5377697 = 4033273) B4033273
theorem B2125615 : Blo 1258447 2125615 := bstep (se 1 (by rfl) ⟨1594211, by rfl⟩ : syracuseStep 2125615 = 3188423) B3188423
theorem B38784815 : Blo 1258447 38784815 := bstep (se 1 (by rfl) ⟨29088611, by rfl⟩ : syracuseStep 38784815 = 58177223) B58177223
theorem B1888055 : Blo 1258447 1888055 := bstep (se 1 (by rfl) ⟨1416041, by rfl⟩ : syracuseStep 1888055 = 2832083) B2832083
theorem B4427581 : Blo 1258447 4427581 := bstep (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) B1660343
theorem B3583901 : Blo 1258447 3583901 := bstep (se 3 (by rfl) ⟨671981, by rfl⟩ : syracuseStep 3583901 = 1343963) B1343963
theorem B12095513 : Blo 1258447 12095513 := bstep (se 2 (by rfl) ⟨4535817, by rfl⟩ : syracuseStep 12095513 = 9071635) B9071635
theorem B1888361 : Blo 1258447 1888361 := bstep (se 2 (by rfl) ⟨708135, by rfl⟩ : syracuseStep 1888361 = 1416271) B1416271
theorem B15323525 : Blo 1258447 15323525 := bstep (se 4 (by rfl) ⟨1436580, by rfl⟩ : syracuseStep 15323525 = 2873161) B2873161
theorem B1888679 : Blo 1258447 1888679 := bstep (se 1 (by rfl) ⟨1416509, by rfl⟩ : syracuseStep 1888679 = 2833019) B2833019
theorem B1888763 : Blo 1258447 1888763 := bstep (se 1 (by rfl) ⟨1416572, by rfl⟩ : syracuseStep 1888763 = 2833145) B2833145
theorem B6214265 : Blo 1258447 6214265 := bstep (se 2 (by rfl) ⟨2330349, by rfl⟩ : syracuseStep 6214265 = 4660699) B4660699
theorem B1888889 : Blo 1258447 1888889 := bstep (se 2 (by rfl) ⟨708333, by rfl⟩ : syracuseStep 1888889 = 1416667) B1416667
theorem B1888943 : Blo 1258447 1888943 := bstep (se 1 (by rfl) ⟨1416707, by rfl⟩ : syracuseStep 1888943 = 2833415) B2833415
theorem B9556703 : Blo 1258447 9556703 := bstep (se 1 (by rfl) ⟨7167527, by rfl⟩ : syracuseStep 9556703 = 14335055) B14335055
theorem B4248287 : Blo 1258447 4248287 := bstep (se 1 (by rfl) ⟨3186215, by rfl⟩ : syracuseStep 4248287 = 6372431) B6372431
theorem B1888991 : Blo 1258447 1888991 := bstep (se 1 (by rfl) ⟨1416743, by rfl⟩ : syracuseStep 1888991 = 2833487) B2833487
theorem B1258447 : Blo 1258447 1258447 := bstep (se 1 (by rfl) ⟨943835, by rfl⟩ : syracuseStep 1258447 = 1887671) B1887671
theorem B1258471 : Blo 1258447 1258471 := bstep (se 1 (by rfl) ⟨943853, by rfl⟩ : syracuseStep 1258471 = 1887707) B1887707
theorem B5821415 : Blo 1258447 5821415 := bstep (se 1 (by rfl) ⟨4366061, by rfl⟩ : syracuseStep 5821415 = 8732123) B8732123
theorem B1889255 : Blo 1258447 1889255 := bstep (se 1 (by rfl) ⟨1416941, by rfl⟩ : syracuseStep 1889255 = 2833883) B2833883
theorem B1594343 : Blo 1258447 1594343 := bstep (se 1 (by rfl) ⟨1195757, by rfl⟩ : syracuseStep 1594343 = 2391515) B2391515
theorem B4248719 : Blo 1258447 4248719 := bstep (se 1 (by rfl) ⟨3186539, by rfl⟩ : syracuseStep 4248719 = 6373079) B6373079
theorem B2831579 : Blo 1258447 2831579 := bstep (se 1 (by rfl) ⟨2123684, by rfl⟩ : syracuseStep 2831579 = 4247369) B4247369
theorem B1889513 : Blo 1258447 1889513 := bstep (se 2 (by rfl) ⟨708567, by rfl⟩ : syracuseStep 1889513 = 1417135) B1417135
theorem B4306169 : Blo 1258447 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B1258783 : Blo 1258447 1258783 := bstep (se 1 (by rfl) ⟨944087, by rfl⟩ : syracuseStep 1258783 = 1888175) B1888175
theorem B1889567 : Blo 1258447 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B1258843 : Blo 1258447 1258843 := bstep (se 1 (by rfl) ⟨944132, by rfl⟩ : syracuseStep 1258843 = 1888265) B1888265
theorem B1258863 : Blo 1258447 1258863 := bstep (se 1 (by rfl) ⟨944147, by rfl⟩ : syracuseStep 1258863 = 1888295) B1888295
theorem B2831777 : Blo 1258447 2831777 := bstep (se 2 (by rfl) ⟨1061916, by rfl⟩ : syracuseStep 2831777 = 2123833) B2123833
theorem B1258919 : Blo 1258447 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B1889735 : Blo 1258447 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B1259003 : Blo 1258447 1259003 := bstep (se 1 (by rfl) ⟨944252, by rfl⟩ : syracuseStep 1259003 = 1888505) B1888505
theorem B13620773 : Blo 1258447 13620773 := bstep (se 4 (by rfl) ⟨1276947, by rfl⟩ : syracuseStep 13620773 = 2553895) B2553895
theorem B1259071 : Blo 1258447 1259071 := bstep (se 1 (by rfl) ⟨944303, by rfl⟩ : syracuseStep 1259071 = 1888607) B1888607
theorem B1259079 : Blo 1258447 1259079 := bstep (se 1 (by rfl) ⟨944309, by rfl⟩ : syracuseStep 1259079 = 1888619) B1888619
theorem B6370973 : Blo 1258447 6370973 := bstep (se 3 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 6370973 = 2389115) B2389115
theorem B10753721 : Blo 1258447 10753721 := bstep (se 2 (by rfl) ⟨4032645, by rfl⟩ : syracuseStep 10753721 = 8065291) B8065291
theorem B1259231 : Blo 1258447 1259231 := bstep (se 1 (by rfl) ⟨944423, by rfl⟩ : syracuseStep 1259231 = 1888847) B1888847
theorem B1890089 : Blo 1258447 1890089 := bstep (se 2 (by rfl) ⟨708783, by rfl⟩ : syracuseStep 1890089 = 1417567) B1417567
theorem B1259311 : Blo 1258447 1259311 := bstep (se 1 (by rfl) ⟨944483, by rfl⟩ : syracuseStep 1259311 = 1888967) B1888967
theorem B1890095 : Blo 1258447 1890095 := bstep (se 1 (by rfl) ⟨1417571, by rfl⟩ : syracuseStep 1890095 = 2835143) B2835143
theorem B1259419 : Blo 1258447 1259419 := bstep (se 1 (by rfl) ⟨944564, by rfl⟩ : syracuseStep 1259419 = 1889129) B1889129
theorem B2832335 : Blo 1258447 2832335 := bstep (se 1 (by rfl) ⟨2124251, by rfl⟩ : syracuseStep 2832335 = 4248503) B4248503
theorem B1259471 : Blo 1258447 1259471 := bstep (se 1 (by rfl) ⟨944603, by rfl⟩ : syracuseStep 1259471 = 1889207) B1889207
theorem B1259495 : Blo 1258447 1259495 := bstep (se 1 (by rfl) ⟨944621, by rfl⟩ : syracuseStep 1259495 = 1889243) B1889243
theorem B10762469 : Blo 1258447 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B4249853 : Blo 1258447 4249853 := bstep (se 3 (by rfl) ⟨796847, by rfl⟩ : syracuseStep 4249853 = 1593695) B1593695
theorem B1890569 : Blo 1258447 1890569 := bstep (se 2 (by rfl) ⟨708963, by rfl⟩ : syracuseStep 1890569 = 1417927) B1417927
theorem B4782361 : Blo 1258447 4782361 := bstep (se 2 (by rfl) ⟨1793385, by rfl⟩ : syracuseStep 4782361 = 3586771) B3586771
theorem B1259807 : Blo 1258447 1259807 := bstep (se 1 (by rfl) ⟨944855, by rfl⟩ : syracuseStep 1259807 = 1889711) B1889711
theorem B2832713 : Blo 1258447 2832713 := bstep (se 2 (by rfl) ⟨1062267, by rfl⟩ : syracuseStep 2832713 = 2124535) B2124535
theorem B2832731 : Blo 1258447 2832731 := bstep (se 1 (by rfl) ⟨2124548, by rfl⟩ : syracuseStep 2832731 = 4249097) B4249097
theorem B1259867 : Blo 1258447 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1259887 : Blo 1258447 1259887 := bstep (se 1 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 1259887 = 1889831) B1889831
theorem B1890671 : Blo 1258447 1890671 := bstep (se 1 (by rfl) ⟨1418003, by rfl⟩ : syracuseStep 1890671 = 2836007) B2836007
theorem B1259943 : Blo 1258447 1259943 := bstep (se 1 (by rfl) ⟨944957, by rfl⟩ : syracuseStep 1259943 = 1889915) B1889915
theorem B1260027 : Blo 1258447 1260027 := bstep (se 1 (by rfl) ⟨945020, by rfl⟩ : syracuseStep 1260027 = 1890041) B1890041
theorem B8075771 : Blo 1258447 8075771 := bstep (se 1 (by rfl) ⟨6056828, by rfl⟩ : syracuseStep 8075771 = 12113657) B12113657
theorem B24533543 : Blo 1258447 24533543 := bstep (se 1 (by rfl) ⟨18400157, by rfl⟩ : syracuseStep 24533543 = 36800315) B36800315
theorem B1260095 : Blo 1258447 1260095 := bstep (se 1 (by rfl) ⟨945071, by rfl⟩ : syracuseStep 1260095 = 1890143) B1890143
theorem B4782665 : Blo 1258447 4782665 := bstep (se 2 (by rfl) ⟨1793499, by rfl⟩ : syracuseStep 4782665 = 3586999) B3586999
theorem B1260103 : Blo 1258447 1260103 := bstep (se 1 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 1260103 = 1890155) B1890155
theorem B32733829 : Blo 1258447 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B6380207 : Blo 1258447 6380207 := bstep (se 1 (by rfl) ⟨4785155, by rfl⟩ : syracuseStep 6380207 = 9570311) B9570311
theorem B1260255 : Blo 1258447 1260255 := bstep (se 1 (by rfl) ⟨945191, by rfl⟩ : syracuseStep 1260255 = 1890383) B1890383
theorem B1415983 : Blo 1258447 1415983 := bstep (se 1 (by rfl) ⟨1061987, by rfl⟩ : syracuseStep 1415983 = 2123975) B2123975
theorem B1260335 : Blo 1258447 1260335 := bstep (se 1 (by rfl) ⟨945251, by rfl⟩ : syracuseStep 1260335 = 1890503) B1890503
theorem B1416091 : Blo 1258447 1416091 := bstep (se 1 (by rfl) ⟨1062068, by rfl⟩ : syracuseStep 1416091 = 2124137) B2124137
theorem B2833307 : Blo 1258447 2833307 := bstep (se 1 (by rfl) ⟨2124980, by rfl⟩ : syracuseStep 2833307 = 4249961) B4249961
theorem B1260443 : Blo 1258447 1260443 := bstep (se 1 (by rfl) ⟨945332, by rfl⟩ : syracuseStep 1260443 = 1890665) B1890665
theorem B6372269 : Blo 1258447 6372269 := bstep (se 3 (by rfl) ⟨1194800, by rfl⟩ : syracuseStep 6372269 = 2389601) B2389601
theorem B3185639 : Blo 1258447 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B6380531 : Blo 1258447 6380531 := bstep (se 1 (by rfl) ⟨4785398, by rfl⟩ : syracuseStep 6380531 = 9570797) B9570797
theorem B4250663 : Blo 1258447 4250663 := bstep (se 1 (by rfl) ⟨3187997, by rfl⟩ : syracuseStep 4250663 = 6375995) B6375995
theorem B2833505 : Blo 1258447 2833505 := bstep (se 2 (by rfl) ⟨1062564, by rfl⟩ : syracuseStep 2833505 = 2125129) B2125129
theorem B21511331 : Blo 1258447 21511331 := bstep (se 1 (by rfl) ⟨16133498, by rfl⟩ : syracuseStep 21511331 = 32266997) B32266997
theorem B9567395 : Blo 1258447 9567395 := bstep (se 1 (by rfl) ⟨7175546, by rfl⟩ : syracuseStep 9567395 = 14351093) B14351093
theorem B5381387 : Blo 1258447 5381387 := bstep (se 1 (by rfl) ⟨4036040, by rfl⟩ : syracuseStep 5381387 = 8072081) B8072081
theorem B1416487 : Blo 1258447 1416487 := bstep (se 1 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 1416487 = 2124731) B2124731
theorem B2833703 : Blo 1258447 2833703 := bstep (se 1 (by rfl) ⟨2125277, by rfl⟩ : syracuseStep 2833703 = 4250555) B4250555
theorem B11492675 : Blo 1258447 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B1416559 : Blo 1258447 1416559 := bstep (se 1 (by rfl) ⟨1062419, by rfl⟩ : syracuseStep 1416559 = 2124839) B2124839
theorem B4251095 : Blo 1258447 4251095 := bstep (se 1 (by rfl) ⟨3188321, by rfl⟩ : syracuseStep 4251095 = 6376643) B6376643
theorem B2391545 : Blo 1258447 2391545 := bstep (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) B1793659
theorem B1416775 : Blo 1258447 1416775 := bstep (se 1 (by rfl) ⟨1062581, by rfl⟩ : syracuseStep 1416775 = 2125163) B2125163
theorem B3186337 : Blo 1258447 3186337 := bstep (se 2 (by rfl) ⟨1194876, by rfl⟩ : syracuseStep 3186337 = 2389753) B2389753
theorem B2834081 : Blo 1258447 2834081 := bstep (se 2 (by rfl) ⟨1062780, by rfl⟩ : syracuseStep 2834081 = 2125561) B2125561
theorem B24542909 : Blo 1258447 24542909 := bstep (se 3 (by rfl) ⟨4601795, by rfl⟩ : syracuseStep 24542909 = 9203591) B9203591
theorem B36298529 : Blo 1258447 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B3186479 : Blo 1258447 3186479 := bstep (se 1 (by rfl) ⟨2389859, by rfl⟩ : syracuseStep 3186479 = 4779719) B4779719
theorem B9076769 : Blo 1258447 9076769 := bstep (se 2 (by rfl) ⟨3403788, by rfl⟩ : syracuseStep 9076769 = 6807577) B6807577
theorem B10215683 : Blo 1258447 10215683 := bstep (se 1 (by rfl) ⟨7661762, by rfl⟩ : syracuseStep 10215683 = 15323525) B15323525
theorem B4538875 : Blo 1258447 4538875 := bstep (se 1 (by rfl) ⟨3404156, by rfl⟩ : syracuseStep 4538875 = 6808313) B6808313
theorem B18416177 : Blo 1258447 18416177 := bstep (se 2 (by rfl) ⟨6906066, by rfl⟩ : syracuseStep 18416177 = 13812133) B13812133
theorem B4424255 : Blo 1258447 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B7168621 : Blo 1258447 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B2835179 : Blo 1258447 2835179 := bstep (se 1 (by rfl) ⟨2126384, by rfl⟩ : syracuseStep 2835179 = 4252769) B4252769
theorem B2016047 : Blo 1258447 2016047 := bstep (se 1 (by rfl) ⟨1512035, by rfl⟩ : syracuseStep 2016047 = 3024071) B3024071
theorem B7169147 : Blo 1258447 7169147 := bstep (se 1 (by rfl) ⟨5376860, by rfl⟩ : syracuseStep 7169147 = 10753721) B10753721
theorem B9078155 : Blo 1258447 9078155 := bstep (se 1 (by rfl) ⟨6808616, by rfl⟩ : syracuseStep 9078155 = 13617233) B13617233
theorem B7177643 : Blo 1258447 7177643 := bstep (se 1 (by rfl) ⟨5383232, by rfl⟩ : syracuseStep 7177643 = 10766465) B10766465
theorem B15533527 : Blo 1258447 15533527 := bstep (se 1 (by rfl) ⟨11650145, by rfl⟩ : syracuseStep 15533527 = 23300291) B23300291
theorem B12109351 : Blo 1258447 12109351 := bstep (se 1 (by rfl) ⟨9082013, by rfl⟩ : syracuseStep 12109351 = 18164027) B18164027
theorem B14354009 : Blo 1258447 14354009 := bstep (se 2 (by rfl) ⟨5382753, by rfl⟩ : syracuseStep 14354009 = 10765507) B10765507
theorem B6375023 : Blo 1258447 6375023 := bstep (se 1 (by rfl) ⟨4781267, by rfl⟩ : syracuseStep 6375023 = 9562535) B9562535
theorem B5383847 : Blo 1258447 5383847 := bstep (se 1 (by rfl) ⟨4037885, by rfl⟩ : syracuseStep 5383847 = 8075771) B8075771
theorem B3188443 : Blo 1258447 3188443 := bstep (se 1 (by rfl) ⟨2391332, by rfl⟩ : syracuseStep 3188443 = 4782665) B4782665
theorem B4253471 : Blo 1258447 4253471 := bstep (se 1 (by rfl) ⟨3190103, by rfl⟩ : syracuseStep 4253471 = 6380207) B6380207
theorem B12109661 : Blo 1258447 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B2123759 : Blo 1258447 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B4253687 : Blo 1258447 4253687 := bstep (se 1 (by rfl) ⟨3190265, by rfl⟩ : syracuseStep 4253687 = 6380531) B6380531
theorem B7661783 : Blo 1258447 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B6048047 : Blo 1258447 6048047 := bstep (se 1 (by rfl) ⟨4536035, by rfl⟩ : syracuseStep 6048047 = 9072071) B9072071
theorem B16361939 : Blo 1258447 16361939 := bstep (se 1 (by rfl) ⟨12271454, by rfl⟩ : syracuseStep 16361939 = 24542909) B24542909
theorem B2124319 : Blo 1258447 2124319 := bstep (se 1 (by rfl) ⟨1593239, by rfl⟩ : syracuseStep 2124319 = 3186479) B3186479
theorem B25856543 : Blo 1258447 25856543 := bstep (se 1 (by rfl) ⟨19392407, by rfl⟩ : syracuseStep 25856543 = 38784815) B38784815
theorem B8612389 : Blo 1258447 8612389 := bstep (se 4 (by rfl) ⟨807411, by rfl⟩ : syracuseStep 8612389 = 1614823) B1614823
theorem B8063675 : Blo 1258447 8063675 := bstep (se 1 (by rfl) ⟨6047756, by rfl⟩ : syracuseStep 8063675 = 12095513) B12095513
theorem B2124751 : Blo 1258447 2124751 := bstep (se 1 (by rfl) ⟨1593563, by rfl⟩ : syracuseStep 2124751 = 3187127) B3187127
theorem B3189739 : Blo 1258447 3189739 := bstep (se 1 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 3189739 = 4784609) B4784609
theorem B6376481 : Blo 1258447 6376481 := bstep (se 2 (by rfl) ⟨2391180, by rfl⟩ : syracuseStep 6376481 = 4782361) B4782361
theorem B3189881 : Blo 1258447 3189881 := bstep (se 2 (by rfl) ⟨1196205, by rfl⟩ : syracuseStep 3189881 = 2392411) B2392411
theorem B8612999 : Blo 1258447 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B13626787 : Blo 1258447 13626787 := bstep (se 1 (by rfl) ⟨10220090, by rfl⟩ : syracuseStep 13626787 = 20440181) B20440181
theorem B1887719 : Blo 1258447 1887719 := bstep (se 1 (by rfl) ⟨1415789, by rfl⟩ : syracuseStep 1887719 = 2831579) B2831579
theorem B1887851 : Blo 1258447 1887851 := bstep (se 1 (by rfl) ⟨1415888, by rfl⟩ : syracuseStep 1887851 = 2831777) B2831777
theorem B2125487 : Blo 1258447 2125487 := bstep (se 1 (by rfl) ⟨1594115, by rfl⟩ : syracuseStep 2125487 = 3188231) B3188231
theorem B9080515 : Blo 1258447 9080515 := bstep (se 1 (by rfl) ⟨6810386, by rfl⟩ : syracuseStep 9080515 = 13620773) B13620773
theorem B1887977 : Blo 1258447 1887977 := bstep (se 2 (by rfl) ⟨707991, by rfl⟩ : syracuseStep 1887977 = 1415983) B1415983
theorem B4247315 : Blo 1258447 4247315 := bstep (se 1 (by rfl) ⟨3185486, by rfl⟩ : syracuseStep 4247315 = 6370973) B6370973
theorem B1888121 : Blo 1258447 1888121 := bstep (se 2 (by rfl) ⟨708045, by rfl⟩ : syracuseStep 1888121 = 1416091) B1416091
theorem B4779931 : Blo 1258447 4779931 := bstep (se 1 (by rfl) ⟨3584948, by rfl⟩ : syracuseStep 4779931 = 7169897) B7169897
theorem B2125723 : Blo 1258447 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B9072557 : Blo 1258447 9072557 := bstep (se 3 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 9072557 = 3402209) B3402209
theorem B1888223 : Blo 1258447 1888223 := bstep (se 1 (by rfl) ⟨1416167, by rfl⟩ : syracuseStep 1888223 = 2832335) B2832335
theorem B7172063 : Blo 1258447 7172063 := bstep (se 1 (by rfl) ⟨5379047, by rfl⟩ : syracuseStep 7172063 = 10758095) B10758095
theorem B6377453 : Blo 1258447 6377453 := bstep (se 3 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 6377453 = 2391545) B2391545
theorem B6811771 : Blo 1258447 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B1888475 : Blo 1258447 1888475 := bstep (se 1 (by rfl) ⟨1416356, by rfl⟩ : syracuseStep 1888475 = 2832713) B2832713
theorem B1888487 : Blo 1258447 1888487 := bstep (se 1 (by rfl) ⟨1416365, by rfl⟩ : syracuseStep 1888487 = 2832731) B2832731
theorem B2126135 : Blo 1258447 2126135 := bstep (se 1 (by rfl) ⟨1594601, by rfl⟩ : syracuseStep 2126135 = 3189203) B3189203
theorem B16355695 : Blo 1258447 16355695 := bstep (se 1 (by rfl) ⟨12266771, by rfl⟩ : syracuseStep 16355695 = 24533543) B24533543
theorem B1888649 : Blo 1258447 1888649 := bstep (se 2 (by rfl) ⟨708243, by rfl⟩ : syracuseStep 1888649 = 1416487) B1416487
theorem B7172495 : Blo 1258447 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B1888745 : Blo 1258447 1888745 := bstep (se 2 (by rfl) ⟨708279, by rfl⟩ : syracuseStep 1888745 = 1416559) B1416559
theorem B1888871 : Blo 1258447 1888871 := bstep (se 1 (by rfl) ⟨1416653, by rfl⟩ : syracuseStep 1888871 = 2833307) B2833307
theorem B4248179 : Blo 1258447 4248179 := bstep (se 1 (by rfl) ⟨3186134, by rfl⟩ : syracuseStep 4248179 = 6372269) B6372269
theorem B1889003 : Blo 1258447 1889003 := bstep (se 1 (by rfl) ⟨1416752, by rfl⟩ : syracuseStep 1889003 = 2833505) B2833505
theorem B6812423 : Blo 1258447 6812423 := bstep (se 1 (by rfl) ⟨5109317, by rfl⟩ : syracuseStep 6812423 = 10218635) B10218635
theorem B1889033 : Blo 1258447 1889033 := bstep (se 2 (by rfl) ⟨708387, by rfl⟩ : syracuseStep 1889033 = 1416775) B1416775
theorem B14340887 : Blo 1258447 14340887 := bstep (se 1 (by rfl) ⟨10755665, by rfl⟩ : syracuseStep 14340887 = 21511331) B21511331
theorem B6378263 : Blo 1258447 6378263 := bstep (se 1 (by rfl) ⟨4783697, by rfl⟩ : syracuseStep 6378263 = 9567395) B9567395
theorem B1889135 : Blo 1258447 1889135 := bstep (se 1 (by rfl) ⟨1416851, by rfl⟩ : syracuseStep 1889135 = 2833703) B2833703
theorem B4248449 : Blo 1258447 4248449 := bstep (se 2 (by rfl) ⟨1593168, by rfl⟩ : syracuseStep 4248449 = 3186337) B3186337
theorem B1258491 : Blo 1258447 1258491 := bstep (se 1 (by rfl) ⟨943868, by rfl⟩ : syracuseStep 1258491 = 1887737) B1887737
theorem B1258559 : Blo 1258447 1258559 := bstep (se 1 (by rfl) ⟨943919, by rfl⟩ : syracuseStep 1258559 = 1887839) B1887839
theorem B2126911 : Blo 1258447 2126911 := bstep (se 1 (by rfl) ⟨1595183, by rfl⟩ : syracuseStep 2126911 = 3190367) B3190367
theorem B8074313 : Blo 1258447 8074313 := bstep (se 2 (by rfl) ⟨3027867, by rfl⟩ : syracuseStep 8074313 = 6055735) B6055735
theorem B5903441 : Blo 1258447 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B3585131 : Blo 1258447 3585131 := bstep (se 1 (by rfl) ⟨2688848, by rfl⟩ : syracuseStep 3585131 = 5377697) B5377697
theorem B1889387 : Blo 1258447 1889387 := bstep (se 1 (by rfl) ⟨1417040, by rfl⟩ : syracuseStep 1889387 = 2834081) B2834081
theorem B1258703 : Blo 1258447 1258703 := bstep (se 1 (by rfl) ⟨944027, by rfl⟩ : syracuseStep 1258703 = 1888055) B1888055
theorem B2389267 : Blo 1258447 2389267 := bstep (se 1 (by rfl) ⟨1791950, by rfl⟩ : syracuseStep 2389267 = 3583901) B3583901
theorem B19928357 : Blo 1258447 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B1889627 : Blo 1258447 1889627 := bstep (se 1 (by rfl) ⟨1417220, by rfl⟩ : syracuseStep 1889627 = 2834441) B2834441
theorem B1258907 : Blo 1258447 1258907 := bstep (se 1 (by rfl) ⟨944180, by rfl⟩ : syracuseStep 1258907 = 1888361) B1888361
theorem B58963457 : Blo 1258447 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B1259119 : Blo 1258447 1259119 := bstep (se 1 (by rfl) ⟨944339, by rfl⟩ : syracuseStep 1259119 = 1888679) B1888679
theorem B1889903 : Blo 1258447 1889903 := bstep (se 1 (by rfl) ⟨1417427, by rfl⟩ : syracuseStep 1889903 = 2834855) B2834855
theorem B1594991 : Blo 1258447 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B1259175 : Blo 1258447 1259175 := bstep (se 1 (by rfl) ⟨944381, by rfl⟩ : syracuseStep 1259175 = 1888763) B1888763
theorem B1513127 : Blo 1258447 1513127 := bstep (se 1 (by rfl) ⟨1134845, by rfl⟩ : syracuseStep 1513127 = 2269691) B2269691
theorem B1595047 : Blo 1258447 1595047 := bstep (se 1 (by rfl) ⟨1196285, by rfl⟩ : syracuseStep 1595047 = 2392571) B2392571
theorem B9557675 : Blo 1258447 9557675 := bstep (se 1 (by rfl) ⟨7168256, by rfl⟩ : syracuseStep 9557675 = 14336513) B14336513
theorem B4249259 : Blo 1258447 4249259 := bstep (se 1 (by rfl) ⟨3186944, by rfl⟩ : syracuseStep 4249259 = 6373889) B6373889
theorem B1889975 : Blo 1258447 1889975 := bstep (se 1 (by rfl) ⟨1417481, by rfl⟩ : syracuseStep 1889975 = 2834963) B2834963
theorem B1890011 : Blo 1258447 1890011 := bstep (se 1 (by rfl) ⟨1417508, by rfl⟩ : syracuseStep 1890011 = 2835017) B2835017
theorem B4142843 : Blo 1258447 4142843 := bstep (se 1 (by rfl) ⟨3107132, by rfl⟩ : syracuseStep 4142843 = 6214265) B6214265
theorem B1259259 : Blo 1258447 1259259 := bstep (se 1 (by rfl) ⟨944444, by rfl⟩ : syracuseStep 1259259 = 1888889) B1888889
theorem B1259295 : Blo 1258447 1259295 := bstep (se 1 (by rfl) ⟨944471, by rfl⟩ : syracuseStep 1259295 = 1888943) B1888943
theorem B6371135 : Blo 1258447 6371135 := bstep (se 1 (by rfl) ⟨4778351, by rfl⟩ : syracuseStep 6371135 = 9556703) B9556703
theorem B2832191 : Blo 1258447 2832191 := bstep (se 1 (by rfl) ⟨2124143, by rfl⟩ : syracuseStep 2832191 = 4248287) B4248287
theorem B1259327 : Blo 1258447 1259327 := bstep (se 1 (by rfl) ⟨944495, by rfl⟩ : syracuseStep 1259327 = 1888991) B1888991
theorem B1890185 : Blo 1258447 1890185 := bstep (se 2 (by rfl) ⟨708819, by rfl⟩ : syracuseStep 1890185 = 1417639) B1417639
theorem B11483117 : Blo 1258447 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B4249583 : Blo 1258447 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B3880943 : Blo 1258447 3880943 := bstep (se 1 (by rfl) ⟨2910707, by rfl⟩ : syracuseStep 3880943 = 5821415) B5821415
theorem B1259503 : Blo 1258447 1259503 := bstep (se 1 (by rfl) ⟨944627, by rfl⟩ : syracuseStep 1259503 = 1889255) B1889255
theorem B1890287 : Blo 1258447 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B2832479 : Blo 1258447 2832479 := bstep (se 1 (by rfl) ⟨2124359, by rfl⟩ : syracuseStep 2832479 = 4248719) B4248719
theorem B1259675 : Blo 1258447 1259675 := bstep (se 1 (by rfl) ⟨944756, by rfl⟩ : syracuseStep 1259675 = 1889513) B1889513
theorem B43645105 : Blo 1258447 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B1259711 : Blo 1258447 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B4249799 : Blo 1258447 4249799 := bstep (se 1 (by rfl) ⟨3187349, by rfl⟩ : syracuseStep 4249799 = 6374699) B6374699
theorem B1890539 : Blo 1258447 1890539 := bstep (se 1 (by rfl) ⟨1417904, by rfl⟩ : syracuseStep 1890539 = 2835809) B2835809
theorem B1890599 : Blo 1258447 1890599 := bstep (se 1 (by rfl) ⟨1417949, by rfl⟩ : syracuseStep 1890599 = 2835899) B2835899
theorem B1259823 : Blo 1258447 1259823 := bstep (se 1 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 1259823 = 1889735) B1889735
theorem B6379883 : Blo 1258447 6379883 := bstep (se 1 (by rfl) ⟨4784912, by rfl⟩ : syracuseStep 6379883 = 9569825) B9569825
theorem B1260059 : Blo 1258447 1260059 := bstep (se 1 (by rfl) ⟨945044, by rfl⟩ : syracuseStep 1260059 = 1890089) B1890089
theorem B1792543 : Blo 1258447 1792543 := bstep (se 1 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 1792543 = 2688815) B2688815
theorem B1260063 : Blo 1258447 1260063 := bstep (se 1 (by rfl) ⟨945047, by rfl⟩ : syracuseStep 1260063 = 1890095) B1890095
theorem B7174979 : Blo 1258447 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B4250447 : Blo 1258447 4250447 := bstep (se 1 (by rfl) ⟨3187835, by rfl⟩ : syracuseStep 4250447 = 6375671) B6375671
theorem B6380369 : Blo 1258447 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B2833235 : Blo 1258447 2833235 := bstep (se 1 (by rfl) ⟨2124926, by rfl⟩ : syracuseStep 2833235 = 4249853) B4249853
theorem B1260379 : Blo 1258447 1260379 := bstep (se 1 (by rfl) ⟨945284, by rfl⟩ : syracuseStep 1260379 = 1890569) B1890569
theorem B1260447 : Blo 1258447 1260447 := bstep (se 1 (by rfl) ⟨945335, by rfl⟩ : syracuseStep 1260447 = 1890671) B1890671
theorem B4250771 : Blo 1258447 4250771 := bstep (se 1 (by rfl) ⟨3188078, by rfl⟩ : syracuseStep 4250771 = 6376157) B6376157
theorem B1416415 : Blo 1258447 1416415 := bstep (se 1 (by rfl) ⟨1062311, by rfl⟩ : syracuseStep 1416415 = 2124623) B2124623
theorem B2833775 : Blo 1258447 2833775 := bstep (se 1 (by rfl) ⟨2125331, by rfl⟩ : syracuseStep 2833775 = 4250663) B4250663
theorem B4251041 : Blo 1258447 4251041 := bstep (se 2 (by rfl) ⟨1594140, by rfl⟩ : syracuseStep 4251041 = 3188281) B3188281
theorem B3587591 : Blo 1258447 3587591 := bstep (se 1 (by rfl) ⟨2690693, by rfl⟩ : syracuseStep 3587591 = 5381387) B5381387
theorem B2834063 : Blo 1258447 2834063 := bstep (se 1 (by rfl) ⟨2125547, by rfl⟩ : syracuseStep 2834063 = 4251095) B4251095
theorem B2834153 : Blo 1258447 2834153 := bstep (se 2 (by rfl) ⟨1062807, by rfl⟩ : syracuseStep 2834153 = 2125615) B2125615
theorem B24199019 : Blo 1258447 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B4251581 : Blo 1258447 4251581 := bstep (se 3 (by rfl) ⟨797171, by rfl⟩ : syracuseStep 4251581 = 1594343) B1594343
theorem B45932741 : Blo 1258447 45932741 := bstep (se 4 (by rfl) ⟨4306194, by rfl⟩ : syracuseStep 45932741 = 8612389) B8612389
theorem B1417423 : Blo 1258447 1417423 := bstep (se 1 (by rfl) ⟨1063067, by rfl⟩ : syracuseStep 1417423 = 2126135) B2126135
theorem B2949503 : Blo 1258447 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B21807593 : Blo 1258447 21807593 := bstep (se 2 (by rfl) ⟨8177847, by rfl⟩ : syracuseStep 21807593 = 16355695) B16355695
theorem B9560591 : Blo 1258447 9560591 := bstep (se 1 (by rfl) ⟨7170443, by rfl⟩ : syracuseStep 9560591 = 14340887) B14340887
theorem B4252175 : Blo 1258447 4252175 := bstep (se 1 (by rfl) ⟨3189131, by rfl⟩ : syracuseStep 4252175 = 6378263) B6378263
theorem B5382875 : Blo 1258447 5382875 := bstep (se 1 (by rfl) ⟨4037156, by rfl⟩ : syracuseStep 5382875 = 8074313) B8074313
theorem B4785095 : Blo 1258447 4785095 := bstep (se 1 (by rfl) ⟨3588821, by rfl⟩ : syracuseStep 4785095 = 7177643) B7177643
theorem B9569339 : Blo 1258447 9569339 := bstep (se 1 (by rfl) ⟨7177004, by rfl⟩ : syracuseStep 9569339 = 14354009) B14354009
theorem B2761895 : Blo 1258447 2761895 := bstep (se 1 (by rfl) ⟨2071421, by rfl⟩ : syracuseStep 2761895 = 4142843) B4142843
theorem B2835647 : Blo 1258447 2835647 := bstep (se 1 (by rfl) ⟨2126735, by rfl⟩ : syracuseStep 2835647 = 4253471) B4253471
theorem B4252985 : Blo 1258447 4252985 := bstep (se 2 (by rfl) ⟨1594869, by rfl⟩ : syracuseStep 4252985 = 3189739) B3189739
theorem B2835791 : Blo 1258447 2835791 := bstep (se 1 (by rfl) ⟨2126843, by rfl⟩ : syracuseStep 2835791 = 4253687) B4253687
theorem B2835881 : Blo 1258447 2835881 := bstep (se 2 (by rfl) ⟨1063455, by rfl⟩ : syracuseStep 2835881 = 2126911) B2126911
theorem B4032031 : Blo 1258447 4032031 := bstep (se 1 (by rfl) ⟨3024023, by rfl⟩ : syracuseStep 4032031 = 6048047) B6048047
theorem B4253255 : Blo 1258447 4253255 := bstep (se 1 (by rfl) ⟨3189941, by rfl⟩ : syracuseStep 4253255 = 6379883) B6379883
theorem B4253309 : Blo 1258447 4253309 := bstep (se 3 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 4253309 = 1594991) B1594991
theorem B17237695 : Blo 1258447 17237695 := bstep (se 1 (by rfl) ⟨12928271, by rfl⟩ : syracuseStep 17237695 = 25856543) B25856543
theorem B5375783 : Blo 1258447 5375783 := bstep (se 1 (by rfl) ⟨4031837, by rfl⟩ : syracuseStep 5375783 = 8063675) B8063675
theorem B4253579 : Blo 1258447 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B20711369 : Blo 1258447 20711369 := bstep (se 2 (by rfl) ⟨7766763, by rfl⟩ : syracuseStep 20711369 = 15533527) B15533527
theorem B5376125 : Blo 1258447 5376125 := bstep (se 3 (by rfl) ⟨1008023, by rfl⟩ : syracuseStep 5376125 = 2016047) B2016047
theorem B16132679 : Blo 1258447 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B6048371 : Blo 1258447 6048371 := bstep (se 1 (by rfl) ⟨4536278, by rfl⟩ : syracuseStep 6048371 = 9072557) B9072557
theorem B6810455 : Blo 1258447 6810455 := bstep (se 1 (by rfl) ⟨5107841, by rfl⟩ : syracuseStep 6810455 = 10215683) B10215683
theorem B4541615 : Blo 1258447 4541615 := bstep (se 1 (by rfl) ⟨3406211, by rfl⟩ : syracuseStep 4541615 = 6812423) B6812423
theorem B3935627 : Blo 1258447 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B4779431 : Blo 1258447 4779431 := bstep (se 1 (by rfl) ⟨3584573, by rfl⟩ : syracuseStep 4779431 = 7169147) B7169147
theorem B39308971 : Blo 1258447 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B4247423 : Blo 1258447 4247423 := bstep (se 1 (by rfl) ⟨3185567, by rfl⟩ : syracuseStep 4247423 = 6371135) B6371135
theorem B1888127 : Blo 1258447 1888127 := bstep (se 1 (by rfl) ⟨1416095, by rfl⟩ : syracuseStep 1888127 = 2832191) B2832191
theorem B8073107 : Blo 1258447 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B7655411 : Blo 1258447 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B1888319 : Blo 1258447 1888319 := bstep (se 1 (by rfl) ⟨1416239, by rfl⟩ : syracuseStep 1888319 = 2832479) B2832479
theorem B5107855 : Blo 1258447 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B1888553 : Blo 1258447 1888553 := bstep (se 2 (by rfl) ⟨708207, by rfl⟩ : syracuseStep 1888553 = 1416415) B1416415
theorem B10907959 : Blo 1258447 10907959 := bstep (se 1 (by rfl) ⟨8180969, by rfl⟩ : syracuseStep 10907959 = 16361939) B16361939
theorem B4035005 : Blo 1258447 4035005 := bstep (se 3 (by rfl) ⟨756563, by rfl⟩ : syracuseStep 4035005 = 1513127) B1513127
theorem B14356925 : Blo 1258447 14356925 := bstep (se 3 (by rfl) ⟨2691923, by rfl⟩ : syracuseStep 14356925 = 5383847) B5383847
theorem B1888823 : Blo 1258447 1888823 := bstep (se 1 (by rfl) ⟨1416617, by rfl⟩ : syracuseStep 1888823 = 2833235) B2833235
theorem B2126587 : Blo 1258447 2126587 := bstep (se 1 (by rfl) ⟨1594940, by rfl⟩ : syracuseStep 2126587 = 3189881) B3189881
theorem B2126729 : Blo 1258447 2126729 := bstep (se 2 (by rfl) ⟨797523, by rfl⟩ : syracuseStep 2126729 = 1595047) B1595047
theorem B1889183 : Blo 1258447 1889183 := bstep (se 1 (by rfl) ⟨1416887, by rfl⟩ : syracuseStep 1889183 = 2833775) B2833775
theorem B1258479 : Blo 1258447 1258479 := bstep (se 1 (by rfl) ⟨943859, by rfl⟩ : syracuseStep 1258479 = 1887719) B1887719
theorem B1258567 : Blo 1258447 1258567 := bstep (se 1 (by rfl) ⟨943925, by rfl⟩ : syracuseStep 1258567 = 1887851) B1887851
theorem B1889375 : Blo 1258447 1889375 := bstep (se 1 (by rfl) ⟨1417031, by rfl⟩ : syracuseStep 1889375 = 2834063) B2834063
theorem B1258651 : Blo 1258447 1258651 := bstep (se 1 (by rfl) ⟨943988, by rfl⟩ : syracuseStep 1258651 = 1887977) B1887977
theorem B1889435 : Blo 1258447 1889435 := bstep (se 1 (by rfl) ⟨1417076, by rfl⟩ : syracuseStep 1889435 = 2834153) B2834153
theorem B2831543 : Blo 1258447 2831543 := bstep (se 1 (by rfl) ⟨2123657, by rfl⟩ : syracuseStep 2831543 = 4247315) B4247315
theorem B1258747 : Blo 1258447 1258747 := bstep (se 1 (by rfl) ⟨944060, by rfl⟩ : syracuseStep 1258747 = 1888121) B1888121
theorem B1258815 : Blo 1258447 1258815 := bstep (se 1 (by rfl) ⟨944111, by rfl⟩ : syracuseStep 1258815 = 1888223) B1888223
theorem B4781375 : Blo 1258447 4781375 := bstep (se 1 (by rfl) ⟨3586031, by rfl⟩ : syracuseStep 4781375 = 7172063) B7172063
theorem B6051179 : Blo 1258447 6051179 := bstep (se 1 (by rfl) ⟨4538384, by rfl⟩ : syracuseStep 6051179 = 9076769) B9076769
theorem B1258983 : Blo 1258447 1258983 := bstep (se 1 (by rfl) ⟨944237, by rfl⟩ : syracuseStep 1258983 = 1888475) B1888475
theorem B1258991 : Blo 1258447 1258991 := bstep (se 1 (by rfl) ⟨944243, by rfl⟩ : syracuseStep 1258991 = 1888487) B1888487
theorem B9082361 : Blo 1258447 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B58193473 : Blo 1258447 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B1259099 : Blo 1258447 1259099 := bstep (se 1 (by rfl) ⟨944324, by rfl⟩ : syracuseStep 1259099 = 1888649) B1888649
theorem B4781663 : Blo 1258447 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B1259163 : Blo 1258447 1259163 := bstep (se 1 (by rfl) ⟨944372, by rfl⟩ : syracuseStep 1259163 = 1888745) B1888745
theorem B12277451 : Blo 1258447 12277451 := bstep (se 1 (by rfl) ⟨9208088, by rfl⟩ : syracuseStep 12277451 = 18416177) B18416177
theorem B1259247 : Blo 1258447 1259247 := bstep (se 1 (by rfl) ⟨944435, by rfl⟩ : syracuseStep 1259247 = 1888871) B1888871
theorem B2832119 : Blo 1258447 2832119 := bstep (se 1 (by rfl) ⟨2124089, by rfl⟩ : syracuseStep 2832119 = 4248179) B4248179
theorem B1259335 : Blo 1258447 1259335 := bstep (se 1 (by rfl) ⟨944501, by rfl⟩ : syracuseStep 1259335 = 1889003) B1889003
theorem B1890119 : Blo 1258447 1890119 := bstep (se 1 (by rfl) ⟨1417589, by rfl⟩ : syracuseStep 1890119 = 2835179) B2835179
theorem B1259355 : Blo 1258447 1259355 := bstep (se 1 (by rfl) ⟨944516, by rfl⟩ : syracuseStep 1259355 = 1889033) B1889033
theorem B1259423 : Blo 1258447 1259423 := bstep (se 1 (by rfl) ⟨944567, by rfl⟩ : syracuseStep 1259423 = 1889135) B1889135
theorem B2832299 : Blo 1258447 2832299 := bstep (se 1 (by rfl) ⟨2124224, by rfl⟩ : syracuseStep 2832299 = 4248449) B4248449
theorem B6051833 : Blo 1258447 6051833 := bstep (se 2 (by rfl) ⟨2269437, by rfl⟩ : syracuseStep 6051833 = 4538875) B4538875
theorem B2832425 : Blo 1258447 2832425 := bstep (se 2 (by rfl) ⟨1062159, by rfl⟩ : syracuseStep 2832425 = 2124319) B2124319
theorem B2390057 : Blo 1258447 2390057 := bstep (se 2 (by rfl) ⟨896271, by rfl⟩ : syracuseStep 2390057 = 1792543) B1792543
theorem B2390087 : Blo 1258447 2390087 := bstep (se 1 (by rfl) ⟨1792565, by rfl⟩ : syracuseStep 2390087 = 3585131) B3585131
theorem B1259591 : Blo 1258447 1259591 := bstep (se 1 (by rfl) ⟨944693, by rfl⟩ : syracuseStep 1259591 = 1889387) B1889387
theorem B9558161 : Blo 1258447 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B13285571 : Blo 1258447 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B1259751 : Blo 1258447 1259751 := bstep (se 1 (by rfl) ⟨944813, by rfl⟩ : syracuseStep 1259751 = 1889627) B1889627
theorem B6052103 : Blo 1258447 6052103 := bstep (se 1 (by rfl) ⟨4539077, by rfl⟩ : syracuseStep 6052103 = 9078155) B9078155
theorem B4250015 : Blo 1258447 4250015 := bstep (se 1 (by rfl) ⟨3187511, by rfl⟩ : syracuseStep 4250015 = 6375023) B6375023
theorem B1259935 : Blo 1258447 1259935 := bstep (se 1 (by rfl) ⟨944951, by rfl⟩ : syracuseStep 1259935 = 1889903) B1889903
theorem B6371783 : Blo 1258447 6371783 := bstep (se 1 (by rfl) ⟨4778837, by rfl⟩ : syracuseStep 6371783 = 9557675) B9557675
theorem B2832839 : Blo 1258447 2832839 := bstep (se 1 (by rfl) ⟨2124629, by rfl⟩ : syracuseStep 2832839 = 4249259) B4249259
theorem B1259983 : Blo 1258447 1259983 := bstep (se 1 (by rfl) ⟨944987, by rfl⟩ : syracuseStep 1259983 = 1889975) B1889975
theorem B1260007 : Blo 1258447 1260007 := bstep (se 1 (by rfl) ⟨945005, by rfl⟩ : syracuseStep 1260007 = 1890011) B1890011
theorem B1260123 : Blo 1258447 1260123 := bstep (se 1 (by rfl) ⟨945092, by rfl⟩ : syracuseStep 1260123 = 1890185) B1890185
theorem B2833001 : Blo 1258447 2833001 := bstep (se 2 (by rfl) ⟨1062375, by rfl⟩ : syracuseStep 2833001 = 2124751) B2124751
theorem B1415839 : Blo 1258447 1415839 := bstep (se 1 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 1415839 = 2123759) B2123759
theorem B2587295 : Blo 1258447 2587295 := bstep (se 1 (by rfl) ⟨1940471, by rfl⟩ : syracuseStep 2587295 = 3880943) B3880943
theorem B2833055 : Blo 1258447 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B1260191 : Blo 1258447 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B9566909 : Blo 1258447 9566909 := bstep (se 3 (by rfl) ⟨1793795, by rfl⟩ : syracuseStep 9566909 = 3587591) B3587591
theorem B2833199 : Blo 1258447 2833199 := bstep (se 1 (by rfl) ⟨2124899, by rfl⟩ : syracuseStep 2833199 = 4249799) B4249799
theorem B1260359 : Blo 1258447 1260359 := bstep (se 1 (by rfl) ⟨945269, by rfl⟩ : syracuseStep 1260359 = 1890539) B1890539
theorem B1260399 : Blo 1258447 1260399 := bstep (se 1 (by rfl) ⟨945299, by rfl⟩ : syracuseStep 1260399 = 1890599) B1890599
theorem B3185689 : Blo 1258447 3185689 := bstep (se 2 (by rfl) ⟨1194633, by rfl⟩ : syracuseStep 3185689 = 2389267) B2389267
theorem B4783319 : Blo 1258447 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B18169049 : Blo 1258447 18169049 := bstep (se 2 (by rfl) ⟨6813393, by rfl⟩ : syracuseStep 18169049 = 13626787) B13626787
theorem B2833631 : Blo 1258447 2833631 := bstep (se 1 (by rfl) ⟨2125223, by rfl⟩ : syracuseStep 2833631 = 4250447) B4250447
theorem B4250987 : Blo 1258447 4250987 := bstep (se 1 (by rfl) ⟨3188240, by rfl⟩ : syracuseStep 4250987 = 6376481) B6376481
theorem B16145801 : Blo 1258447 16145801 := bstep (se 2 (by rfl) ⟨6054675, by rfl⟩ : syracuseStep 16145801 = 12109351) B12109351
theorem B5741999 : Blo 1258447 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B2833847 : Blo 1258447 2833847 := bstep (se 1 (by rfl) ⟨2125385, by rfl⟩ : syracuseStep 2833847 = 4250771) B4250771
theorem B12107353 : Blo 1258447 12107353 := bstep (se 2 (by rfl) ⟨4540257, by rfl⟩ : syracuseStep 12107353 = 9080515) B9080515
theorem B2834027 : Blo 1258447 2834027 := bstep (se 1 (by rfl) ⟨2125520, by rfl⟩ : syracuseStep 2834027 = 4251041) B4251041
theorem B4251257 : Blo 1258447 4251257 := bstep (se 2 (by rfl) ⟨1594221, by rfl⟩ : syracuseStep 4251257 = 3188443) B3188443
theorem B1416991 : Blo 1258447 1416991 := bstep (se 1 (by rfl) ⟨1062743, by rfl⟩ : syracuseStep 1416991 = 2125487) B2125487
theorem B6373241 : Blo 1258447 6373241 := bstep (se 2 (by rfl) ⟨2389965, by rfl⟩ : syracuseStep 6373241 = 4779931) B4779931
theorem B2834297 : Blo 1258447 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B2834387 : Blo 1258447 2834387 := bstep (se 1 (by rfl) ⟨2125790, by rfl⟩ : syracuseStep 2834387 = 4251581) B4251581
theorem B4251635 : Blo 1258447 4251635 := bstep (se 1 (by rfl) ⟨3188726, by rfl⟩ : syracuseStep 4251635 = 6377453) B6377453
theorem B30621827 : Blo 1258447 30621827 := bstep (se 1 (by rfl) ⟨22966370, by rfl⟩ : syracuseStep 30621827 = 45932741) B45932741
theorem B6373565 : Blo 1258447 6373565 := bstep (se 3 (by rfl) ⟨1195043, by rfl⟩ : syracuseStep 6373565 = 2390087) B2390087
theorem B6373727 : Blo 1258447 6373727 := bstep (se 1 (by rfl) ⟨4780295, by rfl⟩ : syracuseStep 6373727 = 9560591) B9560591
theorem B2834783 : Blo 1258447 2834783 := bstep (se 1 (by rfl) ⟨2126087, by rfl⟩ : syracuseStep 2834783 = 4252175) B4252175
theorem B7365053 : Blo 1258447 7365053 := bstep (se 3 (by rfl) ⟨1380947, by rfl⟩ : syracuseStep 7365053 = 2761895) B2761895
theorem B3588583 : Blo 1258447 3588583 := bstep (se 1 (by rfl) ⟨2691437, by rfl⟩ : syracuseStep 3588583 = 5382875) B5382875
theorem B1417819 : Blo 1258447 1417819 := bstep (se 1 (by rfl) ⟨1063364, by rfl⟩ : syracuseStep 1417819 = 2126729) B2126729
theorem B2835323 : Blo 1258447 2835323 := bstep (se 1 (by rfl) ⟨2126492, by rfl⟩ : syracuseStep 2835323 = 4252985) B4252985
theorem B3187583 : Blo 1258447 3187583 := bstep (se 1 (by rfl) ⟨2390687, by rfl⟩ : syracuseStep 3187583 = 4781375) B4781375
theorem B2835449 : Blo 1258447 2835449 := bstep (se 2 (by rfl) ⟨1063293, by rfl⟩ : syracuseStep 2835449 = 2126587) B2126587
theorem B6054907 : Blo 1258447 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B2835503 : Blo 1258447 2835503 := bstep (se 1 (by rfl) ⟨2126627, by rfl⟩ : syracuseStep 2835503 = 4253255) B4253255
theorem B3187775 : Blo 1258447 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B2835539 : Blo 1258447 2835539 := bstep (se 1 (by rfl) ⟨2126654, by rfl⟩ : syracuseStep 2835539 = 4253309) B4253309
theorem B2835719 : Blo 1258447 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B4540303 : Blo 1258447 4540303 := bstep (se 1 (by rfl) ⟨3405227, by rfl⟩ : syracuseStep 4540303 = 6810455) B6810455
theorem B5376041 : Blo 1258447 5376041 := bstep (se 2 (by rfl) ⟨2016015, by rfl⟩ : syracuseStep 5376041 = 4032031) B4032031
theorem B3188879 : Blo 1258447 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B2623751 : Blo 1258447 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B3827999 : Blo 1258447 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B6810473 : Blo 1258447 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B2690003 : Blo 1258447 2690003 := bstep (se 1 (by rfl) ⟨2017502, by rfl⟩ : syracuseStep 2690003 = 4035005) B4035005
theorem B9571283 : Blo 1258447 9571283 := bstep (se 1 (by rfl) ⟨7178462, by rfl⟩ : syracuseStep 9571283 = 14356925) B14356925
theorem B14543945 : Blo 1258447 14543945 := bstep (se 2 (by rfl) ⟨5453979, by rfl⟩ : syracuseStep 14543945 = 10907959) B10907959
theorem B3190063 : Blo 1258447 3190063 := bstep (se 1 (by rfl) ⟨2392547, by rfl⟩ : syracuseStep 3190063 = 4785095) B4785095
theorem B1887695 : Blo 1258447 1887695 := bstep (se 1 (by rfl) ⟨1415771, by rfl⟩ : syracuseStep 1887695 = 2831543) B2831543
theorem B1887785 : Blo 1258447 1887785 := bstep (se 2 (by rfl) ⟨707919, by rfl⟩ : syracuseStep 1887785 = 1415839) B1415839
theorem B4034119 : Blo 1258447 4034119 := bstep (se 1 (by rfl) ⟨3025589, by rfl⟩ : syracuseStep 4034119 = 6051179) B6051179
theorem B1888079 : Blo 1258447 1888079 := bstep (se 1 (by rfl) ⟨1416059, by rfl⟩ : syracuseStep 1888079 = 2832119) B2832119
theorem B3583855 : Blo 1258447 3583855 := bstep (se 1 (by rfl) ⟨2687891, by rfl⟩ : syracuseStep 3583855 = 5375783) B5375783
theorem B1888199 : Blo 1258447 1888199 := bstep (se 1 (by rfl) ⟨1416149, by rfl⟩ : syracuseStep 1888199 = 2832299) B2832299
theorem B13807579 : Blo 1258447 13807579 := bstep (se 1 (by rfl) ⟨10355684, by rfl⟩ : syracuseStep 13807579 = 20711369) B20711369
theorem B31461365 : Blo 1258447 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B4034555 : Blo 1258447 4034555 := bstep (se 1 (by rfl) ⟨3025916, by rfl⟩ : syracuseStep 4034555 = 6051833) B6051833
theorem B1888283 : Blo 1258447 1888283 := bstep (se 1 (by rfl) ⟨1416212, by rfl⟩ : syracuseStep 1888283 = 2832425) B2832425
theorem B1593371 : Blo 1258447 1593371 := bstep (se 1 (by rfl) ⟨1195028, by rfl⟩ : syracuseStep 1593371 = 2390057) B2390057
theorem B4247585 : Blo 1258447 4247585 := bstep (se 2 (by rfl) ⟨1592844, by rfl⟩ : syracuseStep 4247585 = 3185689) B3185689
theorem B3584083 : Blo 1258447 3584083 := bstep (se 1 (by rfl) ⟨2688062, by rfl⟩ : syracuseStep 3584083 = 5376125) B5376125
theorem B4034735 : Blo 1258447 4034735 := bstep (se 1 (by rfl) ⟨3026051, by rfl⟩ : syracuseStep 4034735 = 6052103) B6052103
theorem B4247855 : Blo 1258447 4247855 := bstep (se 1 (by rfl) ⟨3185891, by rfl⟩ : syracuseStep 4247855 = 6371783) B6371783
theorem B1888559 : Blo 1258447 1888559 := bstep (se 1 (by rfl) ⟨1416419, by rfl⟩ : syracuseStep 1888559 = 2832839) B2832839
theorem B1888667 : Blo 1258447 1888667 := bstep (se 1 (by rfl) ⟨1416500, by rfl⟩ : syracuseStep 1888667 = 2833001) B2833001
theorem B1724863 : Blo 1258447 1724863 := bstep (se 1 (by rfl) ⟨1293647, by rfl⟩ : syracuseStep 1724863 = 2587295) B2587295
theorem B1888703 : Blo 1258447 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B6377939 : Blo 1258447 6377939 := bstep (se 1 (by rfl) ⟨4783454, by rfl⟩ : syracuseStep 6377939 = 9566909) B9566909
theorem B32739869 : Blo 1258447 32739869 := bstep (se 3 (by rfl) ⟨6138725, by rfl⟩ : syracuseStep 32739869 = 12277451) B12277451
theorem B1888799 : Blo 1258447 1888799 := bstep (se 1 (by rfl) ⟨1416599, by rfl⟩ : syracuseStep 1888799 = 2833199) B2833199
theorem B77591297 : Blo 1258447 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B3027743 : Blo 1258447 3027743 := bstep (se 1 (by rfl) ⟨2270807, by rfl⟩ : syracuseStep 3027743 = 4541615) B4541615
theorem B16143137 : Blo 1258447 16143137 := bstep (se 2 (by rfl) ⟨6053676, by rfl⟩ : syracuseStep 16143137 = 12107353) B12107353
theorem B12112699 : Blo 1258447 12112699 := bstep (se 1 (by rfl) ⟨9084524, by rfl⟩ : syracuseStep 12112699 = 18169049) B18169049
theorem B1889087 : Blo 1258447 1889087 := bstep (se 1 (by rfl) ⟨1416815, by rfl⟩ : syracuseStep 1889087 = 2833631) B2833631
theorem B22983593 : Blo 1258447 22983593 := bstep (se 2 (by rfl) ⟨8618847, by rfl⟩ : syracuseStep 22983593 = 17237695) B17237695
theorem B1889231 : Blo 1258447 1889231 := bstep (se 1 (by rfl) ⟨1416923, by rfl⟩ : syracuseStep 1889231 = 2833847) B2833847
theorem B1889321 : Blo 1258447 1889321 := bstep (se 2 (by rfl) ⟨708495, by rfl⟩ : syracuseStep 1889321 = 1416991) B1416991
theorem B1889351 : Blo 1258447 1889351 := bstep (se 1 (by rfl) ⟨1417013, by rfl⟩ : syracuseStep 1889351 = 2834027) B2834027
theorem B4248827 : Blo 1258447 4248827 := bstep (se 1 (by rfl) ⟨3186620, by rfl⟩ : syracuseStep 4248827 = 6373241) B6373241
theorem B1889531 : Blo 1258447 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B2831615 : Blo 1258447 2831615 := bstep (se 1 (by rfl) ⟨2123711, by rfl⟩ : syracuseStep 2831615 = 4247423) B4247423
theorem B1258751 : Blo 1258447 1258751 := bstep (se 1 (by rfl) ⟨944063, by rfl⟩ : syracuseStep 1258751 = 1888127) B1888127
theorem B1889591 : Blo 1258447 1889591 := bstep (se 1 (by rfl) ⟨1417193, by rfl⟩ : syracuseStep 1889591 = 2834387) B2834387
theorem B1258879 : Blo 1258447 1258879 := bstep (se 1 (by rfl) ⟨944159, by rfl⟩ : syracuseStep 1258879 = 1888319) B1888319
theorem B1259035 : Blo 1258447 1259035 := bstep (se 1 (by rfl) ⟨944276, by rfl⟩ : syracuseStep 1259035 = 1888553) B1888553
theorem B1889897 : Blo 1258447 1889897 := bstep (se 2 (by rfl) ⟨708711, by rfl⟩ : syracuseStep 1889897 = 1417423) B1417423
theorem B14538395 : Blo 1258447 14538395 := bstep (se 1 (by rfl) ⟨10903796, by rfl⟩ : syracuseStep 14538395 = 21807593) B21807593
theorem B1259215 : Blo 1258447 1259215 := bstep (se 1 (by rfl) ⟨944411, by rfl⟩ : syracuseStep 1259215 = 1888823) B1888823
theorem B1259455 : Blo 1258447 1259455 := bstep (se 1 (by rfl) ⟨944591, by rfl⟩ : syracuseStep 1259455 = 1889183) B1889183
theorem B6379559 : Blo 1258447 6379559 := bstep (se 1 (by rfl) ⟨4784669, by rfl⟩ : syracuseStep 6379559 = 9569339) B9569339
theorem B1259583 : Blo 1258447 1259583 := bstep (se 1 (by rfl) ⟨944687, by rfl⟩ : syracuseStep 1259583 = 1889375) B1889375
theorem B1259623 : Blo 1258447 1259623 := bstep (se 1 (by rfl) ⟨944717, by rfl⟩ : syracuseStep 1259623 = 1889435) B1889435
theorem B1890431 : Blo 1258447 1890431 := bstep (se 1 (by rfl) ⟨1417823, by rfl⟩ : syracuseStep 1890431 = 2835647) B2835647
theorem B1890527 : Blo 1258447 1890527 := bstep (se 1 (by rfl) ⟨1417895, by rfl⟩ : syracuseStep 1890527 = 2835791) B2835791
theorem B1890587 : Blo 1258447 1890587 := bstep (se 1 (by rfl) ⟨1417940, by rfl⟩ : syracuseStep 1890587 = 2835881) B2835881
theorem B2834423 : Blo 1258447 2834423 := bstep (se 1 (by rfl) ⟨2125817, by rfl⟩ : syracuseStep 2834423 = 4251635) B4251635
theorem B1260079 : Blo 1258447 1260079 := bstep (se 1 (by rfl) ⟨945059, by rfl⟩ : syracuseStep 1260079 = 1890119) B1890119
theorem B6372107 : Blo 1258447 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B2833343 : Blo 1258447 2833343 := bstep (se 1 (by rfl) ⟨2125007, by rfl⟩ : syracuseStep 2833343 = 4250015) B4250015
theorem B16128989 : Blo 1258447 16128989 := bstep (se 3 (by rfl) ⟨3024185, by rfl⟩ : syracuseStep 16128989 = 6048371) B6048371
theorem B10755119 : Blo 1258447 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B141712757 : Blo 1258447 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B52411961 : Blo 1258447 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B2833991 : Blo 1258447 2833991 := bstep (se 1 (by rfl) ⟨2125493, by rfl⟩ : syracuseStep 2833991 = 4250987) B4250987
theorem B10763867 : Blo 1258447 10763867 := bstep (se 1 (by rfl) ⟨8072900, by rfl⟩ : syracuseStep 10763867 = 16145801) B16145801
theorem B3186287 : Blo 1258447 3186287 := bstep (se 1 (by rfl) ⟨2389715, by rfl⟩ : syracuseStep 3186287 = 4779431) B4779431
theorem B2834171 : Blo 1258447 2834171 := bstep (se 1 (by rfl) ⟨2125628, by rfl⟩ : syracuseStep 2834171 = 4251257) B4251257
theorem B5382071 : Blo 1258447 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B20414429 : Blo 1258447 20414429 := bstep (se 3 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 20414429 = 7655411) B7655411
theorem B4251959 : Blo 1258447 4251959 := bstep (se 1 (by rfl) ⟨3188969, by rfl⟩ : syracuseStep 4251959 = 6377939) B6377939
theorem B81658205 : Blo 1258447 81658205 := bstep (se 3 (by rfl) ⟨15310913, by rfl⟩ : syracuseStep 81658205 = 30621827) B30621827
theorem B4784777 : Blo 1258447 4784777 := bstep (se 2 (by rfl) ⟨1794291, by rfl⟩ : syracuseStep 4784777 = 3588583) B3588583
theorem B9692263 : Blo 1258447 9692263 := bstep (se 1 (by rfl) ⟨7269197, by rfl⟩ : syracuseStep 9692263 = 14538395) B14538395
theorem B4253039 : Blo 1258447 4253039 := bstep (se 1 (by rfl) ⟨3189779, by rfl⟩ : syracuseStep 4253039 = 6379559) B6379559
theorem B4253417 : Blo 1258447 4253417 := bstep (se 2 (by rfl) ⟨1595031, by rfl⟩ : syracuseStep 4253417 = 3190063) B3190063
theorem B4540315 : Blo 1258447 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B7170079 : Blo 1258447 7170079 := bstep (se 1 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 7170079 = 10755119) B10755119
theorem B34941307 : Blo 1258447 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B2124191 : Blo 1258447 2124191 := bstep (se 1 (by rfl) ⟨1593143, by rfl⟩ : syracuseStep 2124191 = 3186287) B3186287
theorem B4778473 : Blo 1258447 4778473 := bstep (se 2 (by rfl) ⟨1791927, by rfl⟩ : syracuseStep 4778473 = 3583855) B3583855
theorem B18410105 : Blo 1258447 18410105 := bstep (se 2 (by rfl) ⟨6903789, by rfl⟩ : syracuseStep 18410105 = 13807579) B13807579
theorem B13609619 : Blo 1258447 13609619 := bstep (se 1 (by rfl) ⟨10207214, by rfl⟩ : syracuseStep 13609619 = 20414429) B20414429
theorem B20974243 : Blo 1258447 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B2689703 : Blo 1258447 2689703 := bstep (se 1 (by rfl) ⟨2017277, by rfl⟩ : syracuseStep 2689703 = 4034555) B4034555
theorem B4778777 : Blo 1258447 4778777 := bstep (se 2 (by rfl) ⟨1792041, by rfl⟩ : syracuseStep 4778777 = 3584083) B3584083
theorem B2689823 : Blo 1258447 2689823 := bstep (se 1 (by rfl) ⟨2017367, by rfl⟩ : syracuseStep 2689823 = 4034735) B4034735
theorem B21826579 : Blo 1258447 21826579 := bstep (se 1 (by rfl) ⟨16369934, by rfl⟩ : syracuseStep 21826579 = 32739869) B32739869
theorem B2018495 : Blo 1258447 2018495 := bstep (se 1 (by rfl) ⟨1513871, by rfl⟩ : syracuseStep 2018495 = 3027743) B3027743
theorem B2125055 : Blo 1258447 2125055 := bstep (se 1 (by rfl) ⟨1593791, by rfl⟩ : syracuseStep 2125055 = 3187583) B3187583
theorem B2125183 : Blo 1258447 2125183 := bstep (se 1 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 2125183 = 3187775) B3187775
theorem B1887743 : Blo 1258447 1887743 := bstep (se 1 (by rfl) ⟨1415807, by rfl⟩ : syracuseStep 1887743 = 2831615) B2831615
theorem B16150265 : Blo 1258447 16150265 := bstep (se 2 (by rfl) ⟨6056349, by rfl⟩ : syracuseStep 16150265 = 12112699) B12112699
theorem B19640141 : Blo 1258447 19640141 := bstep (se 3 (by rfl) ⟨3682526, by rfl⟩ : syracuseStep 19640141 = 7365053) B7365053
theorem B8073209 : Blo 1258447 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B3584027 : Blo 1258447 3584027 := bstep (se 1 (by rfl) ⟨2688020, by rfl⟩ : syracuseStep 3584027 = 5376041) B5376041
theorem B2125919 : Blo 1258447 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B1749167 : Blo 1258447 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B2551999 : Blo 1258447 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B4248071 : Blo 1258447 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B1888895 : Blo 1258447 1888895 := bstep (se 1 (by rfl) ⟨1416671, by rfl⟩ : syracuseStep 1888895 = 2833343) B2833343
theorem B10752659 : Blo 1258447 10752659 := bstep (se 1 (by rfl) ⟨8064494, by rfl⟩ : syracuseStep 10752659 = 16128989) B16128989
theorem B206910125 : Blo 1258447 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B9695963 : Blo 1258447 9695963 := bstep (se 1 (by rfl) ⟨7271972, by rfl⟩ : syracuseStep 9695963 = 14543945) B14543945
theorem B5378825 : Blo 1258447 5378825 := bstep (se 2 (by rfl) ⟨2017059, by rfl⟩ : syracuseStep 5378825 = 4034119) B4034119
theorem B94475171 : Blo 1258447 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B1258463 : Blo 1258447 1258463 := bstep (se 1 (by rfl) ⟨943847, by rfl⟩ : syracuseStep 1258463 = 1887695) B1887695
theorem B1258523 : Blo 1258447 1258523 := bstep (se 1 (by rfl) ⟨943892, by rfl⟩ : syracuseStep 1258523 = 1887785) B1887785
theorem B1889327 : Blo 1258447 1889327 := bstep (se 1 (by rfl) ⟨1416995, by rfl⟩ : syracuseStep 1889327 = 2833991) B2833991
theorem B61289581 : Blo 1258447 61289581 := bstep (se 3 (by rfl) ⟨11491796, by rfl⟩ : syracuseStep 61289581 = 22983593) B22983593
theorem B1889447 : Blo 1258447 1889447 := bstep (se 1 (by rfl) ⟨1417085, by rfl⟩ : syracuseStep 1889447 = 2834171) B2834171
theorem B1258719 : Blo 1258447 1258719 := bstep (se 1 (by rfl) ⟨944039, by rfl⟩ : syracuseStep 1258719 = 1888079) B1888079
theorem B1258799 : Blo 1258447 1258799 := bstep (se 1 (by rfl) ⟨944099, by rfl⟩ : syracuseStep 1258799 = 1888199) B1888199
theorem B1889615 : Blo 1258447 1889615 := bstep (se 1 (by rfl) ⟨1417211, by rfl⟩ : syracuseStep 1889615 = 2834423) B2834423
theorem B1258855 : Blo 1258447 1258855 := bstep (se 1 (by rfl) ⟨944141, by rfl⟩ : syracuseStep 1258855 = 1888283) B1888283
theorem B2831723 : Blo 1258447 2831723 := bstep (se 1 (by rfl) ⟨2123792, by rfl⟩ : syracuseStep 2831723 = 4247585) B4247585
theorem B4248989 : Blo 1258447 4248989 := bstep (se 3 (by rfl) ⟨796685, by rfl⟩ : syracuseStep 4248989 = 1593371) B1593371
theorem B4249043 : Blo 1258447 4249043 := bstep (se 1 (by rfl) ⟨3186782, by rfl⟩ : syracuseStep 4249043 = 6373565) B6373565
theorem B2831903 : Blo 1258447 2831903 := bstep (se 1 (by rfl) ⟨2123927, by rfl⟩ : syracuseStep 2831903 = 4247855) B4247855
theorem B1259039 : Blo 1258447 1259039 := bstep (se 1 (by rfl) ⟨944279, by rfl⟩ : syracuseStep 1259039 = 1888559) B1888559
theorem B4249151 : Blo 1258447 4249151 := bstep (se 1 (by rfl) ⟨3186863, by rfl⟩ : syracuseStep 4249151 = 6373727) B6373727
theorem B1889855 : Blo 1258447 1889855 := bstep (se 1 (by rfl) ⟨1417391, by rfl⟩ : syracuseStep 1889855 = 2834783) B2834783
theorem B1259111 : Blo 1258447 1259111 := bstep (se 1 (by rfl) ⟨944333, by rfl⟩ : syracuseStep 1259111 = 1888667) B1888667
theorem B1259135 : Blo 1258447 1259135 := bstep (se 1 (by rfl) ⟨944351, by rfl⟩ : syracuseStep 1259135 = 1888703) B1888703
theorem B1259199 : Blo 1258447 1259199 := bstep (se 1 (by rfl) ⟨944399, by rfl⟩ : syracuseStep 1259199 = 1888799) B1888799
theorem B10762091 : Blo 1258447 10762091 := bstep (se 1 (by rfl) ⟨8071568, by rfl⟩ : syracuseStep 10762091 = 16143137) B16143137
theorem B1259391 : Blo 1258447 1259391 := bstep (se 1 (by rfl) ⟨944543, by rfl⟩ : syracuseStep 1259391 = 1889087) B1889087
theorem B1890215 : Blo 1258447 1890215 := bstep (se 1 (by rfl) ⟨1417661, by rfl⟩ : syracuseStep 1890215 = 2835323) B2835323
theorem B2299817 : Blo 1258447 2299817 := bstep (se 2 (by rfl) ⟨862431, by rfl⟩ : syracuseStep 2299817 = 1724863) B1724863
theorem B1259487 : Blo 1258447 1259487 := bstep (se 1 (by rfl) ⟨944615, by rfl⟩ : syracuseStep 1259487 = 1889231) B1889231
theorem B1890299 : Blo 1258447 1890299 := bstep (se 1 (by rfl) ⟨1417724, by rfl⟩ : syracuseStep 1890299 = 2835449) B2835449
theorem B1259547 : Blo 1258447 1259547 := bstep (se 1 (by rfl) ⟨944660, by rfl⟩ : syracuseStep 1259547 = 1889321) B1889321
theorem B1890335 : Blo 1258447 1890335 := bstep (se 1 (by rfl) ⟨1417751, by rfl⟩ : syracuseStep 1890335 = 2835503) B2835503
theorem B1259567 : Blo 1258447 1259567 := bstep (se 1 (by rfl) ⟨944675, by rfl⟩ : syracuseStep 1259567 = 1889351) B1889351
theorem B1890359 : Blo 1258447 1890359 := bstep (se 1 (by rfl) ⟨1417769, by rfl⟩ : syracuseStep 1890359 = 2835539) B2835539
theorem B1890425 : Blo 1258447 1890425 := bstep (se 2 (by rfl) ⟨708909, by rfl⟩ : syracuseStep 1890425 = 1417819) B1417819
theorem B2832551 : Blo 1258447 2832551 := bstep (se 1 (by rfl) ⟨2124413, by rfl⟩ : syracuseStep 2832551 = 4248827) B4248827
theorem B1259687 : Blo 1258447 1259687 := bstep (se 1 (by rfl) ⟨944765, by rfl⟩ : syracuseStep 1259687 = 1889531) B1889531
theorem B1890479 : Blo 1258447 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B1259727 : Blo 1258447 1259727 := bstep (se 1 (by rfl) ⟨944795, by rfl⟩ : syracuseStep 1259727 = 1889591) B1889591
theorem B1259931 : Blo 1258447 1259931 := bstep (se 1 (by rfl) ⟨944948, by rfl⟩ : syracuseStep 1259931 = 1889897) B1889897
theorem B1260287 : Blo 1258447 1260287 := bstep (se 1 (by rfl) ⟨945215, by rfl⟩ : syracuseStep 1260287 = 1890431) B1890431
theorem B1260351 : Blo 1258447 1260351 := bstep (se 1 (by rfl) ⟨945263, by rfl⟩ : syracuseStep 1260351 = 1890527) B1890527
theorem B1260391 : Blo 1258447 1260391 := bstep (se 1 (by rfl) ⟨945293, by rfl⟩ : syracuseStep 1260391 = 1890587) B1890587
theorem B1793335 : Blo 1258447 1793335 := bstep (se 1 (by rfl) ⟨1345001, by rfl⟩ : syracuseStep 1793335 = 2690003) B2690003
theorem B6380855 : Blo 1258447 6380855 := bstep (se 1 (by rfl) ⟨4785641, by rfl⟩ : syracuseStep 6380855 = 9571283) B9571283
theorem B7175911 : Blo 1258447 7175911 := bstep (se 1 (by rfl) ⟨5381933, by rfl⟩ : syracuseStep 7175911 = 10763867) B10763867
theorem B6053737 : Blo 1258447 6053737 := bstep (se 2 (by rfl) ⟨2270151, by rfl⟩ : syracuseStep 6053737 = 4540303) B4540303
theorem B3588047 : Blo 1258447 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B9560105 : Blo 1258447 9560105 := bstep (se 2 (by rfl) ⟨3585039, by rfl⟩ : syracuseStep 9560105 = 7170079) B7170079
theorem B1417279 : Blo 1258447 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B2834639 : Blo 1258447 2834639 := bstep (se 1 (by rfl) ⟨2125979, by rfl⟩ : syracuseStep 2834639 = 4251959) B4251959
theorem B7168439 : Blo 1258447 7168439 := bstep (se 1 (by rfl) ⟨5376329, by rfl⟩ : syracuseStep 7168439 = 10752659) B10752659
theorem B6463975 : Blo 1258447 6463975 := bstep (se 1 (by rfl) ⟨4847981, by rfl⟩ : syracuseStep 6463975 = 9695963) B9695963
theorem B46588409 : Blo 1258447 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B51692069 : Blo 1258447 51692069 := bstep (se 4 (by rfl) ⟨4846131, by rfl⟩ : syracuseStep 51692069 = 9692263) B9692263
theorem B2835359 : Blo 1258447 2835359 := bstep (se 1 (by rfl) ⟨2126519, by rfl⟩ : syracuseStep 2835359 = 4253039) B4253039
theorem B2835611 : Blo 1258447 2835611 := bstep (se 1 (by rfl) ⟨2126708, by rfl⟩ : syracuseStep 2835611 = 4253417) B4253417
theorem B1533211 : Blo 1258447 1533211 := bstep (se 1 (by rfl) ⟨1149908, by rfl⟩ : syracuseStep 1533211 = 2299817) B2299817
theorem B12273403 : Blo 1258447 12273403 := bstep (se 1 (by rfl) ⟨9205052, by rfl⟩ : syracuseStep 12273403 = 18410105) B18410105
theorem B74631125 : Blo 1258447 74631125 := bstep (se 7 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 74631125 = 1749167) B1749167
theorem B1345663 : Blo 1258447 1345663 := bstep (se 1 (by rfl) ⟨1009247, by rfl⟩ : syracuseStep 1345663 = 2018495) B2018495
theorem B4253903 : Blo 1258447 4253903 := bstep (se 1 (by rfl) ⟨3190427, by rfl⟩ : syracuseStep 4253903 = 6380855) B6380855
theorem B8071649 : Blo 1258447 8071649 := bstep (se 2 (by rfl) ⟨3026868, by rfl⟩ : syracuseStep 8071649 = 6053737) B6053737
theorem B10766843 : Blo 1258447 10766843 := bstep (se 1 (by rfl) ⟨8075132, by rfl⟩ : syracuseStep 10766843 = 16150265) B16150265
theorem B13093427 : Blo 1258447 13093427 := bstep (se 1 (by rfl) ⟨9820070, by rfl⟩ : syracuseStep 13093427 = 19640141) B19640141
theorem B54438803 : Blo 1258447 54438803 := bstep (se 1 (by rfl) ⟨40829102, by rfl⟩ : syracuseStep 54438803 = 81658205) B81658205
theorem B3402665 : Blo 1258447 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B3189851 : Blo 1258447 3189851 := bstep (se 1 (by rfl) ⟨2392388, by rfl⟩ : syracuseStep 3189851 = 4784777) B4784777
theorem B137940083 : Blo 1258447 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B1887815 : Blo 1258447 1887815 := bstep (se 1 (by rfl) ⟨1415861, by rfl⟩ : syracuseStep 1887815 = 2831723) B2831723
theorem B1887935 : Blo 1258447 1887935 := bstep (se 1 (by rfl) ⟨1415951, by rfl⟩ : syracuseStep 1887935 = 2831903) B2831903
theorem B29102105 : Blo 1258447 29102105 := bstep (se 2 (by rfl) ⟨10913289, by rfl⟩ : syracuseStep 29102105 = 21826579) B21826579
theorem B1888367 : Blo 1258447 1888367 := bstep (se 1 (by rfl) ⟨1416275, by rfl⟩ : syracuseStep 1888367 = 2832551) B2832551
theorem B81719441 : Blo 1258447 81719441 := bstep (se 2 (by rfl) ⟨30644790, by rfl⟩ : syracuseStep 81719441 = 61289581) B61289581
theorem B5382139 : Blo 1258447 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B9073079 : Blo 1258447 9073079 := bstep (se 1 (by rfl) ⟨6804809, by rfl⟩ : syracuseStep 9073079 = 13609619) B13609619
theorem B1258495 : Blo 1258447 1258495 := bstep (se 1 (by rfl) ⟨943871, by rfl⟩ : syracuseStep 1258495 = 1887743) B1887743
theorem B251933789 : Blo 1258447 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B2389351 : Blo 1258447 2389351 := bstep (se 1 (by rfl) ⟨1792013, by rfl⟩ : syracuseStep 2389351 = 3584027) B3584027
theorem B2832047 : Blo 1258447 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B1259263 : Blo 1258447 1259263 := bstep (se 1 (by rfl) ⟨944447, by rfl⟩ : syracuseStep 1259263 = 1888895) B1888895
theorem B3585883 : Blo 1258447 3585883 := bstep (se 1 (by rfl) ⟨2689412, by rfl⟩ : syracuseStep 3585883 = 5378825) B5378825
theorem B6371297 : Blo 1258447 6371297 := bstep (se 2 (by rfl) ⟨2389236, by rfl⟩ : syracuseStep 6371297 = 4778473) B4778473
theorem B1259551 : Blo 1258447 1259551 := bstep (se 1 (by rfl) ⟨944663, by rfl⟩ : syracuseStep 1259551 = 1889327) B1889327
theorem B1259631 : Blo 1258447 1259631 := bstep (se 1 (by rfl) ⟨944723, by rfl⟩ : syracuseStep 1259631 = 1889447) B1889447
theorem B27965657 : Blo 1258447 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B1259743 : Blo 1258447 1259743 := bstep (se 1 (by rfl) ⟨944807, by rfl⟩ : syracuseStep 1259743 = 1889615) B1889615
theorem B2832659 : Blo 1258447 2832659 := bstep (se 1 (by rfl) ⟨2124494, by rfl⟩ : syracuseStep 2832659 = 4248989) B4248989
theorem B2832695 : Blo 1258447 2832695 := bstep (se 1 (by rfl) ⟨2124521, by rfl⟩ : syracuseStep 2832695 = 4249043) B4249043
theorem B2832767 : Blo 1258447 2832767 := bstep (se 1 (by rfl) ⟨2124575, by rfl⟩ : syracuseStep 2832767 = 4249151) B4249151
theorem B1259903 : Blo 1258447 1259903 := bstep (se 1 (by rfl) ⟨944927, by rfl⟩ : syracuseStep 1259903 = 1889855) B1889855
theorem B7174727 : Blo 1258447 7174727 := bstep (se 1 (by rfl) ⟨5381045, by rfl⟩ : syracuseStep 7174727 = 10762091) B10762091
theorem B1260143 : Blo 1258447 1260143 := bstep (se 1 (by rfl) ⟨945107, by rfl⟩ : syracuseStep 1260143 = 1890215) B1890215
theorem B1260199 : Blo 1258447 1260199 := bstep (se 1 (by rfl) ⟨945149, by rfl⟩ : syracuseStep 1260199 = 1890299) B1890299
theorem B1260223 : Blo 1258447 1260223 := bstep (se 1 (by rfl) ⟨945167, by rfl⟩ : syracuseStep 1260223 = 1890335) B1890335
theorem B1260239 : Blo 1258447 1260239 := bstep (se 1 (by rfl) ⟨945179, by rfl⟩ : syracuseStep 1260239 = 1890359) B1890359
theorem B1260283 : Blo 1258447 1260283 := bstep (se 1 (by rfl) ⟨945212, by rfl⟩ : syracuseStep 1260283 = 1890425) B1890425
theorem B1260319 : Blo 1258447 1260319 := bstep (se 1 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 1260319 = 1890479) B1890479
theorem B1416127 : Blo 1258447 1416127 := bstep (se 1 (by rfl) ⟨1062095, by rfl⟩ : syracuseStep 1416127 = 2124191) B2124191
theorem B2391113 : Blo 1258447 2391113 := bstep (se 2 (by rfl) ⟨896667, by rfl⟩ : syracuseStep 2391113 = 1793335) B1793335
theorem B1793135 : Blo 1258447 1793135 := bstep (se 1 (by rfl) ⟨1344851, by rfl⟩ : syracuseStep 1793135 = 2689703) B2689703
theorem B2833577 : Blo 1258447 2833577 := bstep (se 2 (by rfl) ⟨1062591, by rfl⟩ : syracuseStep 2833577 = 2125183) B2125183
theorem B3185851 : Blo 1258447 3185851 := bstep (se 1 (by rfl) ⟨2389388, by rfl⟩ : syracuseStep 3185851 = 4778777) B4778777
theorem B1793215 : Blo 1258447 1793215 := bstep (se 1 (by rfl) ⟨1344911, by rfl⟩ : syracuseStep 1793215 = 2689823) B2689823
theorem B1416703 : Blo 1258447 1416703 := bstep (se 1 (by rfl) ⟨1062527, by rfl⟩ : syracuseStep 1416703 = 2125055) B2125055
theorem B9567881 : Blo 1258447 9567881 := bstep (se 2 (by rfl) ⟨3587955, by rfl⟩ : syracuseStep 9567881 = 7175911) B7175911
theorem B6053753 : Blo 1258447 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B2392031 : Blo 1258447 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B6373403 : Blo 1258447 6373403 := bstep (se 1 (by rfl) ⟨4780052, by rfl⟩ : syracuseStep 6373403 = 9560105) B9560105
theorem B8618633 : Blo 1258447 8618633 := bstep (se 2 (by rfl) ⟨3231987, by rfl⟩ : syracuseStep 8618633 = 6463975) B6463975
theorem B7176869 : Blo 1258447 7176869 := bstep (se 4 (by rfl) ⟨672831, by rfl⟩ : syracuseStep 7176869 = 1345663) B1345663
theorem B34915805 : Blo 1258447 34915805 := bstep (se 3 (by rfl) ⟨6546713, by rfl⟩ : syracuseStep 34915805 = 13093427) B13093427
theorem B2835935 : Blo 1258447 2835935 := bstep (se 1 (by rfl) ⟨2126951, by rfl⟩ : syracuseStep 2835935 = 4253903) B4253903
theorem B8177125 : Blo 1258447 8177125 := bstep (se 4 (by rfl) ⟨766605, by rfl⟩ : syracuseStep 8177125 = 1533211) B1533211
theorem B7177895 : Blo 1258447 7177895 := bstep (se 1 (by rfl) ⟨5383421, by rfl⟩ : syracuseStep 7177895 = 10766843) B10766843
theorem B36292535 : Blo 1258447 36292535 := bstep (se 1 (by rfl) ⟨27219401, by rfl⟩ : syracuseStep 36292535 = 54438803) B54438803
theorem B77605613 : Blo 1258447 77605613 := bstep (se 3 (by rfl) ⟨14551052, by rfl⟩ : syracuseStep 77605613 = 29102105) B29102105
theorem B54479627 : Blo 1258447 54479627 := bstep (se 1 (by rfl) ⟨40859720, by rfl⟩ : syracuseStep 54479627 = 81719441) B81719441
theorem B4778959 : Blo 1258447 4778959 := bstep (se 1 (by rfl) ⟨3584219, by rfl⟩ : syracuseStep 4778959 = 7168439) B7168439
theorem B6048719 : Blo 1258447 6048719 := bstep (se 1 (by rfl) ⟨4536539, by rfl⟩ : syracuseStep 6048719 = 9073079) B9073079
theorem B31058939 : Blo 1258447 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B167955859 : Blo 1258447 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B1888031 : Blo 1258447 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B1888169 : Blo 1258447 1888169 := bstep (se 2 (by rfl) ⟨708063, by rfl⟩ : syracuseStep 1888169 = 1416127) B1416127
theorem B49754083 : Blo 1258447 49754083 := bstep (se 1 (by rfl) ⟨37315562, by rfl⟩ : syracuseStep 49754083 = 74631125) B74631125
theorem B4247531 : Blo 1258447 4247531 := bstep (se 1 (by rfl) ⟨3185648, by rfl⟩ : syracuseStep 4247531 = 6371297) B6371297
theorem B1888439 : Blo 1258447 1888439 := bstep (se 1 (by rfl) ⟨1416329, by rfl⟩ : syracuseStep 1888439 = 2832659) B2832659
theorem B1888463 : Blo 1258447 1888463 := bstep (se 1 (by rfl) ⟨1416347, by rfl⟩ : syracuseStep 1888463 = 2832695) B2832695
theorem B4247801 : Blo 1258447 4247801 := bstep (se 2 (by rfl) ⟨1592925, by rfl⟩ : syracuseStep 4247801 = 3185851) B3185851
theorem B1888511 : Blo 1258447 1888511 := bstep (se 1 (by rfl) ⟨1416383, by rfl⟩ : syracuseStep 1888511 = 2832767) B2832767
theorem B1888937 : Blo 1258447 1888937 := bstep (se 2 (by rfl) ⟨708351, by rfl⟩ : syracuseStep 1888937 = 1416703) B1416703
theorem B1594075 : Blo 1258447 1594075 := bstep (se 1 (by rfl) ⟨1195556, by rfl⟩ : syracuseStep 1594075 = 2391113) B2391113
theorem B2126567 : Blo 1258447 2126567 := bstep (se 1 (by rfl) ⟨1594925, by rfl⟩ : syracuseStep 2126567 = 3189851) B3189851
theorem B91960055 : Blo 1258447 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B1889051 : Blo 1258447 1889051 := bstep (se 1 (by rfl) ⟨1416788, by rfl⟩ : syracuseStep 1889051 = 2833577) B2833577
theorem B16364537 : Blo 1258447 16364537 := bstep (se 2 (by rfl) ⟨6136701, by rfl⟩ : syracuseStep 16364537 = 12273403) B12273403
theorem B1258543 : Blo 1258447 1258543 := bstep (se 1 (by rfl) ⟨943907, by rfl⟩ : syracuseStep 1258543 = 1887815) B1887815
theorem B6378587 : Blo 1258447 6378587 := bstep (se 1 (by rfl) ⟨4783940, by rfl⟩ : syracuseStep 6378587 = 9567881) B9567881
theorem B4781177 : Blo 1258447 4781177 := bstep (se 2 (by rfl) ⟨1792941, by rfl⟩ : syracuseStep 4781177 = 3585883) B3585883
theorem B1258623 : Blo 1258447 1258623 := bstep (se 1 (by rfl) ⟨943967, by rfl⟩ : syracuseStep 1258623 = 1887935) B1887935
theorem B4035835 : Blo 1258447 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B6378749 : Blo 1258447 6378749 := bstep (se 3 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 6378749 = 2392031) B2392031
theorem B1258911 : Blo 1258447 1258911 := bstep (se 1 (by rfl) ⟨944183, by rfl⟩ : syracuseStep 1258911 = 1888367) B1888367
theorem B1889705 : Blo 1258447 1889705 := bstep (se 2 (by rfl) ⟨708639, by rfl⟩ : syracuseStep 1889705 = 1417279) B1417279
theorem B1889759 : Blo 1258447 1889759 := bstep (se 1 (by rfl) ⟨1417319, by rfl⟩ : syracuseStep 1889759 = 2834639) B2834639
theorem B4781693 : Blo 1258447 4781693 := bstep (se 3 (by rfl) ⟨896567, by rfl⟩ : syracuseStep 4781693 = 1793135) B1793135
theorem B34461379 : Blo 1258447 34461379 := bstep (se 1 (by rfl) ⟨25846034, by rfl⟩ : syracuseStep 34461379 = 51692069) B51692069
theorem B1890239 : Blo 1258447 1890239 := bstep (se 1 (by rfl) ⟨1417679, by rfl⟩ : syracuseStep 1890239 = 2835359) B2835359
theorem B1890407 : Blo 1258447 1890407 := bstep (se 1 (by rfl) ⟨1417805, by rfl⟩ : syracuseStep 1890407 = 2835611) B2835611
theorem B18643771 : Blo 1258447 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B2390953 : Blo 1258447 2390953 := bstep (se 2 (by rfl) ⟨896607, by rfl⟩ : syracuseStep 2390953 = 1793215) B1793215
theorem B5381099 : Blo 1258447 5381099 := bstep (se 1 (by rfl) ⟨4035824, by rfl⟩ : syracuseStep 5381099 = 8071649) B8071649
theorem B4783151 : Blo 1258447 4783151 := bstep (se 1 (by rfl) ⟨3587363, by rfl⟩ : syracuseStep 4783151 = 7174727) B7174727
theorem B3185801 : Blo 1258447 3185801 := bstep (se 2 (by rfl) ⟨1194675, by rfl⟩ : syracuseStep 3185801 = 2389351) B2389351
theorem B2268443 : Blo 1258447 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B7176185 : Blo 1258447 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B4784579 : Blo 1258447 4784579 := bstep (se 1 (by rfl) ⟨3588434, by rfl⟩ : syracuseStep 4784579 = 7176869) B7176869
theorem B1417711 : Blo 1258447 1417711 := bstep (se 1 (by rfl) ⟨1063283, by rfl⟩ : syracuseStep 1417711 = 2126567) B2126567
theorem B4252391 : Blo 1258447 4252391 := bstep (se 1 (by rfl) ⟨3189293, by rfl⟩ : syracuseStep 4252391 = 6378587) B6378587
theorem B3187451 : Blo 1258447 3187451 := bstep (se 1 (by rfl) ⟨2390588, by rfl⟩ : syracuseStep 3187451 = 4781177) B4781177
theorem B4252499 : Blo 1258447 4252499 := bstep (se 1 (by rfl) ⟨3189374, by rfl⟩ : syracuseStep 4252499 = 6378749) B6378749
theorem B3187795 : Blo 1258447 3187795 := bstep (se 1 (by rfl) ⟨2390846, by rfl⟩ : syracuseStep 3187795 = 4781693) B4781693
theorem B4785263 : Blo 1258447 4785263 := bstep (se 1 (by rfl) ⟨3588947, by rfl⟩ : syracuseStep 4785263 = 7177895) B7177895
theorem B3187937 : Blo 1258447 3187937 := bstep (se 2 (by rfl) ⟨1195476, by rfl⟩ : syracuseStep 3187937 = 2390953) B2390953
theorem B4032479 : Blo 1258447 4032479 := bstep (se 1 (by rfl) ⟨3024359, by rfl⟩ : syracuseStep 4032479 = 6048719) B6048719
theorem B4784123 : Blo 1258447 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B3188767 : Blo 1258447 3188767 := bstep (se 1 (by rfl) ⟨2391575, by rfl⟩ : syracuseStep 3188767 = 4783151) B4783151
theorem B2123867 : Blo 1258447 2123867 := bstep (se 1 (by rfl) ⟨1592900, by rfl⟩ : syracuseStep 2123867 = 3185801) B3185801
theorem B5745755 : Blo 1258447 5745755 := bstep (se 1 (by rfl) ⟨4309316, by rfl⟩ : syracuseStep 5745755 = 8618633) B8618633
theorem B6049181 : Blo 1258447 6049181 := bstep (se 3 (by rfl) ⟨1134221, by rfl⟩ : syracuseStep 6049181 = 2268443) B2268443
theorem B2125433 : Blo 1258447 2125433 := bstep (se 2 (by rfl) ⟨797037, by rfl⟩ : syracuseStep 2125433 = 1594075) B1594075
theorem B23277203 : Blo 1258447 23277203 := bstep (se 1 (by rfl) ⟨17457902, by rfl⟩ : syracuseStep 23277203 = 34915805) B34915805
theorem B24858361 : Blo 1258447 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B24195023 : Blo 1258447 24195023 := bstep (se 1 (by rfl) ⟨18146267, by rfl⟩ : syracuseStep 24195023 = 36292535) B36292535
theorem B21524453 : Blo 1258447 21524453 := bstep (se 4 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 21524453 = 4035835) B4035835
theorem B51737075 : Blo 1258447 51737075 := bstep (se 1 (by rfl) ⟨38802806, by rfl⟩ : syracuseStep 51737075 = 77605613) B77605613
theorem B36319751 : Blo 1258447 36319751 := bstep (se 1 (by rfl) ⟨27239813, by rfl⟩ : syracuseStep 36319751 = 54479627) B54479627
theorem B223941145 : Blo 1258447 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B20705959 : Blo 1258447 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B1258687 : Blo 1258447 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B1258779 : Blo 1258447 1258779 := bstep (se 1 (by rfl) ⟨944084, by rfl⟩ : syracuseStep 1258779 = 1888169) B1888169
theorem B2831687 : Blo 1258447 2831687 := bstep (se 1 (by rfl) ⟨2123765, by rfl⟩ : syracuseStep 2831687 = 4247531) B4247531
theorem B4248935 : Blo 1258447 4248935 := bstep (se 1 (by rfl) ⟨3186701, by rfl⟩ : syracuseStep 4248935 = 6373403) B6373403
theorem B1258959 : Blo 1258447 1258959 := bstep (se 1 (by rfl) ⟨944219, by rfl⟩ : syracuseStep 1258959 = 1888439) B1888439
theorem B1258975 : Blo 1258447 1258975 := bstep (se 1 (by rfl) ⟨944231, by rfl⟩ : syracuseStep 1258975 = 1888463) B1888463
theorem B2831867 : Blo 1258447 2831867 := bstep (se 1 (by rfl) ⟨2123900, by rfl⟩ : syracuseStep 2831867 = 4247801) B4247801
theorem B1259007 : Blo 1258447 1259007 := bstep (se 1 (by rfl) ⟨944255, by rfl⟩ : syracuseStep 1259007 = 1888511) B1888511
theorem B1259291 : Blo 1258447 1259291 := bstep (se 1 (by rfl) ⟨944468, by rfl⟩ : syracuseStep 1259291 = 1888937) B1888937
theorem B61306703 : Blo 1258447 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B1259367 : Blo 1258447 1259367 := bstep (se 1 (by rfl) ⟨944525, by rfl⟩ : syracuseStep 1259367 = 1889051) B1889051
theorem B10909691 : Blo 1258447 10909691 := bstep (se 1 (by rfl) ⟨8182268, by rfl⟩ : syracuseStep 10909691 = 16364537) B16364537
theorem B1259803 : Blo 1258447 1259803 := bstep (se 1 (by rfl) ⟨944852, by rfl⟩ : syracuseStep 1259803 = 1889705) B1889705
theorem B1259839 : Blo 1258447 1259839 := bstep (se 1 (by rfl) ⟨944879, by rfl⟩ : syracuseStep 1259839 = 1889759) B1889759
theorem B1890623 : Blo 1258447 1890623 := bstep (se 1 (by rfl) ⟨1417967, by rfl⟩ : syracuseStep 1890623 = 2835935) B2835935
theorem B6371945 : Blo 1258447 6371945 := bstep (se 2 (by rfl) ⟨2389479, by rfl⟩ : syracuseStep 6371945 = 4778959) B4778959
theorem B1260159 : Blo 1258447 1260159 := bstep (se 1 (by rfl) ⟨945119, by rfl⟩ : syracuseStep 1260159 = 1890239) B1890239
theorem B1260271 : Blo 1258447 1260271 := bstep (se 1 (by rfl) ⟨945203, by rfl⟩ : syracuseStep 1260271 = 1890407) B1890407
theorem B10902833 : Blo 1258447 10902833 := bstep (se 2 (by rfl) ⟨4088562, by rfl⟩ : syracuseStep 10902833 = 8177125) B8177125
theorem B3587399 : Blo 1258447 3587399 := bstep (se 1 (by rfl) ⟨2690549, by rfl⟩ : syracuseStep 3587399 = 5381099) B5381099
theorem B45948505 : Blo 1258447 45948505 := bstep (se 2 (by rfl) ⟨17230689, by rfl⟩ : syracuseStep 45948505 = 34461379) B34461379
theorem B66338777 : Blo 1258447 66338777 := bstep (se 2 (by rfl) ⟨24877041, by rfl⟩ : syracuseStep 66338777 = 49754083) B49754083
theorem B4251689 : Blo 1258447 4251689 := bstep (se 2 (by rfl) ⟨1594383, by rfl⟩ : syracuseStep 4251689 = 3188767) B3188767
theorem B2834927 : Blo 1258447 2834927 := bstep (se 1 (by rfl) ⟨2126195, by rfl⟩ : syracuseStep 2834927 = 4252391) B4252391
theorem B2834999 : Blo 1258447 2834999 := bstep (se 1 (by rfl) ⟨2126249, by rfl⟩ : syracuseStep 2834999 = 4252499) B4252499
theorem B27607945 : Blo 1258447 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B40871135 : Blo 1258447 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B2688319 : Blo 1258447 2688319 := bstep (se 1 (by rfl) ⟨2016239, by rfl⟩ : syracuseStep 2688319 = 4032479) B4032479
theorem B7268555 : Blo 1258447 7268555 := bstep (se 1 (by rfl) ⟨5451416, by rfl⟩ : syracuseStep 7268555 = 10902833) B10902833
theorem B4032787 : Blo 1258447 4032787 := bstep (se 1 (by rfl) ⟨3024590, by rfl⟩ : syracuseStep 4032787 = 6049181) B6049181
theorem B15518135 : Blo 1258447 15518135 := bstep (se 1 (by rfl) ⟨11638601, by rfl⟩ : syracuseStep 15518135 = 23277203) B23277203
theorem B3189415 : Blo 1258447 3189415 := bstep (se 1 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 3189415 = 4784123) B4784123
theorem B3189719 : Blo 1258447 3189719 := bstep (se 1 (by rfl) ⟨2392289, by rfl⟩ : syracuseStep 3189719 = 4784579) B4784579
theorem B34491383 : Blo 1258447 34491383 := bstep (se 1 (by rfl) ⟨25868537, by rfl⟩ : syracuseStep 34491383 = 51737075) B51737075
theorem B2124967 : Blo 1258447 2124967 := bstep (se 1 (by rfl) ⟨1593725, by rfl⟩ : syracuseStep 2124967 = 3187451) B3187451
theorem B3190175 : Blo 1258447 3190175 := bstep (se 1 (by rfl) ⟨2392631, by rfl⟩ : syracuseStep 3190175 = 4785263) B4785263
theorem B2125291 : Blo 1258447 2125291 := bstep (se 1 (by rfl) ⟨1593968, by rfl⟩ : syracuseStep 2125291 = 3187937) B3187937
theorem B1887791 : Blo 1258447 1887791 := bstep (se 1 (by rfl) ⟨1415843, by rfl⟩ : syracuseStep 1887791 = 2831687) B2831687
theorem B1887911 : Blo 1258447 1887911 := bstep (se 1 (by rfl) ⟨1415933, by rfl⟩ : syracuseStep 1887911 = 2831867) B2831867
theorem B4247963 : Blo 1258447 4247963 := bstep (se 1 (by rfl) ⟨3185972, by rfl⟩ : syracuseStep 4247963 = 6371945) B6371945
theorem B3830503 : Blo 1258447 3830503 := bstep (se 1 (by rfl) ⟨2872877, by rfl⟩ : syracuseStep 3830503 = 5745755) B5745755
theorem B61264673 : Blo 1258447 61264673 := bstep (se 2 (by rfl) ⟨22974252, by rfl⟩ : syracuseStep 61264673 = 45948505) B45948505
theorem B44225851 : Blo 1258447 44225851 := bstep (se 1 (by rfl) ⟨33169388, by rfl⟩ : syracuseStep 44225851 = 66338777) B66338777
theorem B14349635 : Blo 1258447 14349635 := bstep (se 1 (by rfl) ⟨10762226, by rfl⟩ : syracuseStep 14349635 = 21524453) B21524453
theorem B24213167 : Blo 1258447 24213167 := bstep (se 1 (by rfl) ⟨18159875, by rfl⟩ : syracuseStep 24213167 = 36319751) B36319751
theorem B1890281 : Blo 1258447 1890281 := bstep (se 2 (by rfl) ⟨708855, by rfl⟩ : syracuseStep 1890281 = 1417711) B1417711
theorem B298588193 : Blo 1258447 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B2832623 : Blo 1258447 2832623 := bstep (se 1 (by rfl) ⟨2124467, by rfl⟩ : syracuseStep 2832623 = 4248935) B4248935
theorem B7273127 : Blo 1258447 7273127 := bstep (se 1 (by rfl) ⟨5454845, by rfl⟩ : syracuseStep 7273127 = 10909691) B10909691
theorem B1415911 : Blo 1258447 1415911 := bstep (se 1 (by rfl) ⟨1061933, by rfl⟩ : syracuseStep 1415911 = 2123867) B2123867
theorem B4250393 : Blo 1258447 4250393 := bstep (se 2 (by rfl) ⟨1593897, by rfl⟩ : syracuseStep 4250393 = 3187795) B3187795
theorem B1260415 : Blo 1258447 1260415 := bstep (se 1 (by rfl) ⟨945311, by rfl⟩ : syracuseStep 1260415 = 1890623) B1890623
theorem B2391599 : Blo 1258447 2391599 := bstep (se 1 (by rfl) ⟨1793699, by rfl⟩ : syracuseStep 2391599 = 3587399) B3587399
theorem B33144481 : Blo 1258447 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B1416955 : Blo 1258447 1416955 := bstep (se 1 (by rfl) ⟨1062716, by rfl⟩ : syracuseStep 1416955 = 2125433) B2125433
theorem B16130015 : Blo 1258447 16130015 := bstep (se 1 (by rfl) ⟨12097511, by rfl⟩ : syracuseStep 16130015 = 24195023) B24195023
theorem B2834459 : Blo 1258447 2834459 := bstep (se 1 (by rfl) ⟨2125844, by rfl⟩ : syracuseStep 2834459 = 4251689) B4251689
theorem B19382813 : Blo 1258447 19382813 := bstep (se 3 (by rfl) ⟨3634277, by rfl⟩ : syracuseStep 19382813 = 7268555) B7268555
theorem B27247423 : Blo 1258447 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B4252553 : Blo 1258447 4252553 := bstep (se 2 (by rfl) ⟨1594707, by rfl⟩ : syracuseStep 4252553 = 3189415) B3189415
theorem B199058795 : Blo 1258447 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B58967801 : Blo 1258447 58967801 := bstep (se 2 (by rfl) ⟨22112925, by rfl⟩ : syracuseStep 58967801 = 44225851) B44225851
theorem B5377049 : Blo 1258447 5377049 := bstep (se 2 (by rfl) ⟨2016393, by rfl⟩ : syracuseStep 5377049 = 4032787) B4032787
theorem B1887881 : Blo 1258447 1887881 := bstep (se 2 (by rfl) ⟨707955, by rfl⟩ : syracuseStep 1887881 = 1415911) B1415911
theorem B5107337 : Blo 1258447 5107337 := bstep (se 2 (by rfl) ⟨1915251, by rfl⟩ : syracuseStep 5107337 = 3830503) B3830503
theorem B16142111 : Blo 1258447 16142111 := bstep (se 1 (by rfl) ⟨12106583, by rfl⟩ : syracuseStep 16142111 = 24213167) B24213167
theorem B36810593 : Blo 1258447 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B1888415 : Blo 1258447 1888415 := bstep (se 1 (by rfl) ⟨1416311, by rfl⟩ : syracuseStep 1888415 = 2832623) B2832623
theorem B3584425 : Blo 1258447 3584425 := bstep (se 2 (by rfl) ⟨1344159, by rfl⟩ : syracuseStep 3584425 = 2688319) B2688319
theorem B2126479 : Blo 1258447 2126479 := bstep (se 1 (by rfl) ⟨1594859, by rfl⟩ : syracuseStep 2126479 = 3189719) B3189719
theorem B44192641 : Blo 1258447 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B2126783 : Blo 1258447 2126783 := bstep (se 1 (by rfl) ⟨1595087, by rfl⟩ : syracuseStep 2126783 = 3190175) B3190175
theorem B1889273 : Blo 1258447 1889273 := bstep (se 2 (by rfl) ⟨708477, by rfl⟩ : syracuseStep 1889273 = 1416955) B1416955
theorem B1258527 : Blo 1258447 1258527 := bstep (se 1 (by rfl) ⟨943895, by rfl⟩ : syracuseStep 1258527 = 1887791) B1887791
theorem B1594399 : Blo 1258447 1594399 := bstep (se 1 (by rfl) ⟨1195799, by rfl⟩ : syracuseStep 1594399 = 2391599) B2391599
theorem B1258607 : Blo 1258447 1258607 := bstep (se 1 (by rfl) ⟨943955, by rfl⟩ : syracuseStep 1258607 = 1887911) B1887911
theorem B10753343 : Blo 1258447 10753343 := bstep (se 1 (by rfl) ⟨8065007, by rfl⟩ : syracuseStep 10753343 = 16130015) B16130015
theorem B2831975 : Blo 1258447 2831975 := bstep (se 1 (by rfl) ⟨2123981, by rfl⟩ : syracuseStep 2831975 = 4247963) B4247963
theorem B1889951 : Blo 1258447 1889951 := bstep (se 1 (by rfl) ⟨1417463, by rfl⟩ : syracuseStep 1889951 = 2834927) B2834927
theorem B1889999 : Blo 1258447 1889999 := bstep (se 1 (by rfl) ⟨1417499, by rfl⟩ : syracuseStep 1889999 = 2834999) B2834999
theorem B40843115 : Blo 1258447 40843115 := bstep (se 1 (by rfl) ⟨30632336, by rfl⟩ : syracuseStep 40843115 = 61264673) B61264673
theorem B9566423 : Blo 1258447 9566423 := bstep (se 1 (by rfl) ⟨7174817, by rfl⟩ : syracuseStep 9566423 = 14349635) B14349635
theorem B1260187 : Blo 1258447 1260187 := bstep (se 1 (by rfl) ⟨945140, by rfl⟩ : syracuseStep 1260187 = 1890281) B1890281
theorem B2833289 : Blo 1258447 2833289 := bstep (se 2 (by rfl) ⟨1062483, by rfl⟩ : syracuseStep 2833289 = 2124967) B2124967
theorem B10345423 : Blo 1258447 10345423 := bstep (se 1 (by rfl) ⟨7759067, by rfl⟩ : syracuseStep 10345423 = 15518135) B15518135
theorem B4848751 : Blo 1258447 4848751 := bstep (se 1 (by rfl) ⟨3636563, by rfl⟩ : syracuseStep 4848751 = 7273127) B7273127
theorem B2833595 : Blo 1258447 2833595 := bstep (se 1 (by rfl) ⟨2125196, by rfl⟩ : syracuseStep 2833595 = 4250393) B4250393
theorem B2833721 : Blo 1258447 2833721 := bstep (se 2 (by rfl) ⟨1062645, by rfl⟩ : syracuseStep 2833721 = 2125291) B2125291
theorem B22994255 : Blo 1258447 22994255 := bstep (se 1 (by rfl) ⟨17245691, by rfl⟩ : syracuseStep 22994255 = 34491383) B34491383
theorem B2835035 : Blo 1258447 2835035 := bstep (se 1 (by rfl) ⟨2126276, by rfl⟩ : syracuseStep 2835035 = 4252553) B4252553
theorem B1417855 : Blo 1258447 1417855 := bstep (se 1 (by rfl) ⟨1063391, by rfl⟩ : syracuseStep 1417855 = 2126783) B2126783
theorem B2835305 : Blo 1258447 2835305 := bstep (se 2 (by rfl) ⟨1063239, by rfl⟩ : syracuseStep 2835305 = 2126479) B2126479
theorem B7168895 : Blo 1258447 7168895 := bstep (se 1 (by rfl) ⟨5376671, by rfl⟩ : syracuseStep 7168895 = 10753343) B10753343
theorem B15329503 : Blo 1258447 15329503 := bstep (se 1 (by rfl) ⟨11497127, by rfl⟩ : syracuseStep 15329503 = 22994255) B22994255
theorem B12921875 : Blo 1258447 12921875 := bstep (se 1 (by rfl) ⟨9691406, by rfl⟩ : syracuseStep 12921875 = 19382813) B19382813
theorem B4779233 : Blo 1258447 4779233 := bstep (se 2 (by rfl) ⟨1792212, by rfl⟩ : syracuseStep 4779233 = 3584425) B3584425
theorem B132705863 : Blo 1258447 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B1887983 : Blo 1258447 1887983 := bstep (se 1 (by rfl) ⟨1415987, by rfl⟩ : syracuseStep 1887983 = 2831975) B2831975
theorem B2125865 : Blo 1258447 2125865 := bstep (se 2 (by rfl) ⟨797199, by rfl⟩ : syracuseStep 2125865 = 1594399) B1594399
theorem B6377615 : Blo 1258447 6377615 := bstep (se 1 (by rfl) ⟨4783211, by rfl⟩ : syracuseStep 6377615 = 9566423) B9566423
theorem B1888859 : Blo 1258447 1888859 := bstep (se 1 (by rfl) ⟨1416644, by rfl⟩ : syracuseStep 1888859 = 2833289) B2833289
theorem B3584699 : Blo 1258447 3584699 := bstep (se 1 (by rfl) ⟨2688524, by rfl⟩ : syracuseStep 3584699 = 5377049) B5377049
theorem B1889063 : Blo 1258447 1889063 := bstep (se 1 (by rfl) ⟨1416797, by rfl⟩ : syracuseStep 1889063 = 2833595) B2833595
theorem B1889147 : Blo 1258447 1889147 := bstep (se 1 (by rfl) ⟨1416860, by rfl⟩ : syracuseStep 1889147 = 2833721) B2833721
theorem B1258587 : Blo 1258447 1258587 := bstep (se 1 (by rfl) ⟨943940, by rfl⟩ : syracuseStep 1258587 = 1887881) B1887881
theorem B3404891 : Blo 1258447 3404891 := bstep (se 1 (by rfl) ⟨2553668, by rfl⟩ : syracuseStep 3404891 = 5107337) B5107337
theorem B10761407 : Blo 1258447 10761407 := bstep (se 1 (by rfl) ⟨8071055, by rfl⟩ : syracuseStep 10761407 = 16142111) B16142111
theorem B1889639 : Blo 1258447 1889639 := bstep (se 1 (by rfl) ⟨1417229, by rfl⟩ : syracuseStep 1889639 = 2834459) B2834459
theorem B1258943 : Blo 1258447 1258943 := bstep (se 1 (by rfl) ⟨944207, by rfl⟩ : syracuseStep 1258943 = 1888415) B1888415
theorem B25860005 : Blo 1258447 25860005 := bstep (se 4 (by rfl) ⟨2424375, by rfl⟩ : syracuseStep 25860005 = 4848751) B4848751
theorem B1259515 : Blo 1258447 1259515 := bstep (se 1 (by rfl) ⟨944636, by rfl⟩ : syracuseStep 1259515 = 1889273) B1889273
theorem B36329897 : Blo 1258447 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B1259967 : Blo 1258447 1259967 := bstep (se 1 (by rfl) ⟨944975, by rfl⟩ : syracuseStep 1259967 = 1889951) B1889951
theorem B1259999 : Blo 1258447 1259999 := bstep (se 1 (by rfl) ⟨944999, by rfl⟩ : syracuseStep 1259999 = 1889999) B1889999
theorem B39311867 : Blo 1258447 39311867 := bstep (se 1 (by rfl) ⟨29483900, by rfl⟩ : syracuseStep 39311867 = 58967801) B58967801
theorem B58923521 : Blo 1258447 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B27228743 : Blo 1258447 27228743 := bstep (se 1 (by rfl) ⟨20421557, by rfl⟩ : syracuseStep 27228743 = 40843115) B40843115
theorem B13793897 : Blo 1258447 13793897 := bstep (se 2 (by rfl) ⟨5172711, by rfl⟩ : syracuseStep 13793897 = 10345423) B10345423
theorem B1570585301 : Blo 1258447 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B1417243 : Blo 1258447 1417243 := bstep (se 1 (by rfl) ⟨1062932, by rfl⟩ : syracuseStep 1417243 = 2125865) B2125865
theorem B4251743 : Blo 1258447 4251743 := bstep (se 1 (by rfl) ⟨3188807, by rfl⟩ : syracuseStep 4251743 = 6377615) B6377615
theorem B20439337 : Blo 1258447 20439337 := bstep (se 2 (by rfl) ⟨7664751, by rfl⟩ : syracuseStep 20439337 = 15329503) B15329503
theorem B2269927 : Blo 1258447 2269927 := bstep (se 1 (by rfl) ⟨1702445, by rfl⟩ : syracuseStep 2269927 = 3404891) B3404891
theorem B26207911 : Blo 1258447 26207911 := bstep (se 1 (by rfl) ⟨19655933, by rfl⟩ : syracuseStep 26207911 = 39311867) B39311867
theorem B39282347 : Blo 1258447 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B4779263 : Blo 1258447 4779263 := bstep (se 1 (by rfl) ⟨3584447, by rfl⟩ : syracuseStep 4779263 = 7168895) B7168895
theorem B17240003 : Blo 1258447 17240003 := bstep (se 1 (by rfl) ⟨12930002, by rfl⟩ : syracuseStep 17240003 = 25860005) B25860005
theorem B24219931 : Blo 1258447 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B9195931 : Blo 1258447 9195931 := bstep (se 1 (by rfl) ⟨6896948, by rfl⟩ : syracuseStep 9195931 = 13793897) B13793897
theorem B1047056867 : Blo 1258447 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B8614583 : Blo 1258447 8614583 := bstep (se 1 (by rfl) ⟨6460937, by rfl⟩ : syracuseStep 8614583 = 12921875) B12921875
theorem B88470575 : Blo 1258447 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B1258655 : Blo 1258447 1258655 := bstep (se 1 (by rfl) ⟨943991, by rfl⟩ : syracuseStep 1258655 = 1887983) B1887983
theorem B1259239 : Blo 1258447 1259239 := bstep (se 1 (by rfl) ⟨944429, by rfl⟩ : syracuseStep 1259239 = 1888859) B1888859
theorem B1890023 : Blo 1258447 1890023 := bstep (se 1 (by rfl) ⟨1417517, by rfl⟩ : syracuseStep 1890023 = 2835035) B2835035
theorem B2389799 : Blo 1258447 2389799 := bstep (se 1 (by rfl) ⟨1792349, by rfl⟩ : syracuseStep 2389799 = 3584699) B3584699
theorem B1259375 : Blo 1258447 1259375 := bstep (se 1 (by rfl) ⟨944531, by rfl⟩ : syracuseStep 1259375 = 1889063) B1889063
theorem B1890203 : Blo 1258447 1890203 := bstep (se 1 (by rfl) ⟨1417652, by rfl⟩ : syracuseStep 1890203 = 2835305) B2835305
theorem B1259431 : Blo 1258447 1259431 := bstep (se 1 (by rfl) ⟨944573, by rfl⟩ : syracuseStep 1259431 = 1889147) B1889147
theorem B7174271 : Blo 1258447 7174271 := bstep (se 1 (by rfl) ⟨5380703, by rfl⟩ : syracuseStep 7174271 = 10761407) B10761407
theorem B1890473 : Blo 1258447 1890473 := bstep (se 2 (by rfl) ⟨708927, by rfl⟩ : syracuseStep 1890473 = 1417855) B1417855
theorem B1259759 : Blo 1258447 1259759 := bstep (se 1 (by rfl) ⟨944819, by rfl⟩ : syracuseStep 1259759 = 1889639) B1889639
theorem B18152495 : Blo 1258447 18152495 := bstep (se 1 (by rfl) ⟨13614371, by rfl⟩ : syracuseStep 18152495 = 27228743) B27228743
theorem B3186155 : Blo 1258447 3186155 := bstep (se 1 (by rfl) ⟨2389616, by rfl⟩ : syracuseStep 3186155 = 4779233) B4779233
theorem B2834495 : Blo 1258447 2834495 := bstep (se 1 (by rfl) ⟨2125871, by rfl⟩ : syracuseStep 2834495 = 4251743) B4251743
theorem B32293241 : Blo 1258447 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B5743055 : Blo 1258447 5743055 := bstep (se 1 (by rfl) ⟨4307291, by rfl⟩ : syracuseStep 5743055 = 8614583) B8614583
theorem B12101663 : Blo 1258447 12101663 := bstep (se 1 (by rfl) ⟨9076247, by rfl⟩ : syracuseStep 12101663 = 18152495) B18152495
theorem B2124103 : Blo 1258447 2124103 := bstep (se 1 (by rfl) ⟨1593077, by rfl⟩ : syracuseStep 2124103 = 3186155) B3186155
theorem B3026569 : Blo 1258447 3026569 := bstep (se 2 (by rfl) ⟨1134963, by rfl⟩ : syracuseStep 3026569 = 2269927) B2269927
theorem B1593199 : Blo 1258447 1593199 := bstep (se 1 (by rfl) ⟨1194899, by rfl⟩ : syracuseStep 1593199 = 2389799) B2389799
theorem B34943881 : Blo 1258447 34943881 := bstep (se 2 (by rfl) ⟨13103955, by rfl⟩ : syracuseStep 34943881 = 26207911) B26207911
theorem B1889657 : Blo 1258447 1889657 := bstep (se 2 (by rfl) ⟨708621, by rfl⟩ : syracuseStep 1889657 = 1417243) B1417243
theorem B698037911 : Blo 1258447 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B27252449 : Blo 1258447 27252449 := bstep (se 2 (by rfl) ⟨10219668, by rfl⟩ : syracuseStep 27252449 = 20439337) B20439337
theorem B12261241 : Blo 1258447 12261241 := bstep (se 2 (by rfl) ⟨4597965, by rfl⟩ : syracuseStep 12261241 = 9195931) B9195931
theorem B58980383 : Blo 1258447 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B26188231 : Blo 1258447 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B1260015 : Blo 1258447 1260015 := bstep (se 1 (by rfl) ⟨945011, by rfl⟩ : syracuseStep 1260015 = 1890023) B1890023
theorem B1260135 : Blo 1258447 1260135 := bstep (se 1 (by rfl) ⟨945101, by rfl⟩ : syracuseStep 1260135 = 1890203) B1890203
theorem B4782847 : Blo 1258447 4782847 := bstep (se 1 (by rfl) ⟨3587135, by rfl⟩ : syracuseStep 4782847 = 7174271) B7174271
theorem B1260315 : Blo 1258447 1260315 := bstep (se 1 (by rfl) ⟨945236, by rfl⟩ : syracuseStep 1260315 = 1890473) B1890473
theorem B3186175 : Blo 1258447 3186175 := bstep (se 1 (by rfl) ⟨2389631, by rfl⟩ : syracuseStep 3186175 = 4779263) B4779263
theorem B11493335 : Blo 1258447 11493335 := bstep (se 1 (by rfl) ⟨8620001, by rfl⟩ : syracuseStep 11493335 = 17240003) B17240003
theorem B21528827 : Blo 1258447 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B2124265 : Blo 1258447 2124265 := bstep (se 2 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 2124265 = 1593199) B1593199
theorem B7662223 : Blo 1258447 7662223 := bstep (se 1 (by rfl) ⟨5746667, by rfl⟩ : syracuseStep 7662223 = 11493335) B11493335
theorem B3828703 : Blo 1258447 3828703 := bstep (se 1 (by rfl) ⟨2871527, by rfl⟩ : syracuseStep 3828703 = 5743055) B5743055
theorem B34917641 : Blo 1258447 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B6377129 : Blo 1258447 6377129 := bstep (se 2 (by rfl) ⟨2391423, by rfl⟩ : syracuseStep 6377129 = 4782847) B4782847
theorem B465358607 : Blo 1258447 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B46591841 : Blo 1258447 46591841 := bstep (se 2 (by rfl) ⟨17471940, by rfl⟩ : syracuseStep 46591841 = 34943881) B34943881
theorem B4248233 : Blo 1258447 4248233 := bstep (se 2 (by rfl) ⟨1593087, by rfl⟩ : syracuseStep 4248233 = 3186175) B3186175
theorem B4035425 : Blo 1258447 4035425 := bstep (se 2 (by rfl) ⟨1513284, by rfl⟩ : syracuseStep 4035425 = 3026569) B3026569
theorem B16348321 : Blo 1258447 16348321 := bstep (se 2 (by rfl) ⟨6130620, by rfl⟩ : syracuseStep 16348321 = 12261241) B12261241
theorem B1889663 : Blo 1258447 1889663 := bstep (se 1 (by rfl) ⟨1417247, by rfl⟩ : syracuseStep 1889663 = 2834495) B2834495
theorem B2832137 : Blo 1258447 2832137 := bstep (se 2 (by rfl) ⟨1062051, by rfl⟩ : syracuseStep 2832137 = 2124103) B2124103
theorem B1259771 : Blo 1258447 1259771 := bstep (se 1 (by rfl) ⟨944828, by rfl⟩ : syracuseStep 1259771 = 1889657) B1889657
theorem B18168299 : Blo 1258447 18168299 := bstep (se 1 (by rfl) ⟨13626224, by rfl⟩ : syracuseStep 18168299 = 27252449) B27252449
theorem B8067775 : Blo 1258447 8067775 := bstep (se 1 (by rfl) ⟨6050831, by rfl⟩ : syracuseStep 8067775 = 12101663) B12101663
theorem B39320255 : Blo 1258447 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B14352551 : Blo 1258447 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B10216297 : Blo 1258447 10216297 := bstep (se 2 (by rfl) ⟨3831111, by rfl⟩ : syracuseStep 10216297 = 7662223) B7662223
theorem B10757033 : Blo 1258447 10757033 := bstep (se 2 (by rfl) ⟨4033887, by rfl⟩ : syracuseStep 10757033 = 8067775) B8067775
theorem B5104937 : Blo 1258447 5104937 := bstep (se 2 (by rfl) ⟨1914351, by rfl⟩ : syracuseStep 5104937 = 3828703) B3828703
theorem B1888091 : Blo 1258447 1888091 := bstep (se 1 (by rfl) ⟨1416068, by rfl⟩ : syracuseStep 1888091 = 2832137) B2832137
theorem B12112199 : Blo 1258447 12112199 := bstep (se 1 (by rfl) ⟨9084149, by rfl⟩ : syracuseStep 12112199 = 18168299) B18168299
theorem B23278427 : Blo 1258447 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B10761133 : Blo 1258447 10761133 := bstep (se 3 (by rfl) ⟨2017712, by rfl⟩ : syracuseStep 10761133 = 4035425) B4035425
theorem B31061227 : Blo 1258447 31061227 := bstep (se 1 (by rfl) ⟨23295920, by rfl⟩ : syracuseStep 31061227 = 46591841) B46591841
theorem B2832155 : Blo 1258447 2832155 := bstep (se 1 (by rfl) ⟨2124116, by rfl⟩ : syracuseStep 2832155 = 4248233) B4248233
theorem B2832353 : Blo 1258447 2832353 := bstep (se 2 (by rfl) ⟨1062132, by rfl⟩ : syracuseStep 2832353 = 2124265) B2124265
theorem B1259775 : Blo 1258447 1259775 := bstep (se 1 (by rfl) ⟨944831, by rfl⟩ : syracuseStep 1259775 = 1889663) B1889663
theorem B21797761 : Blo 1258447 21797761 := bstep (se 2 (by rfl) ⟨8174160, by rfl⟩ : syracuseStep 21797761 = 16348321) B16348321
theorem B26213503 : Blo 1258447 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B4251419 : Blo 1258447 4251419 := bstep (se 1 (by rfl) ⟨3188564, by rfl⟩ : syracuseStep 4251419 = 6377129) B6377129
theorem B310239071 : Blo 1258447 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B9568367 : Blo 1258447 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B206826047 : Blo 1258447 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B15518951 : Blo 1258447 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B7171355 : Blo 1258447 7171355 := bstep (se 1 (by rfl) ⟨5378516, by rfl⟩ : syracuseStep 7171355 = 10757033) B10757033
theorem B3403291 : Blo 1258447 3403291 := bstep (se 1 (by rfl) ⟨2552468, by rfl⟩ : syracuseStep 3403291 = 5104937) B5104937
theorem B1888103 : Blo 1258447 1888103 := bstep (se 1 (by rfl) ⟨1416077, by rfl⟩ : syracuseStep 1888103 = 2832155) B2832155
theorem B14348177 : Blo 1258447 14348177 := bstep (se 2 (by rfl) ⟨5380566, by rfl⟩ : syracuseStep 14348177 = 10761133) B10761133
theorem B1888235 : Blo 1258447 1888235 := bstep (se 1 (by rfl) ⟨1416176, by rfl⟩ : syracuseStep 1888235 = 2832353) B2832353
theorem B34951337 : Blo 1258447 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B41414969 : Blo 1258447 41414969 := bstep (se 2 (by rfl) ⟨15530613, by rfl⟩ : syracuseStep 41414969 = 31061227) B31061227
theorem B1258727 : Blo 1258447 1258727 := bstep (se 1 (by rfl) ⟨944045, by rfl⟩ : syracuseStep 1258727 = 1888091) B1888091
theorem B8074799 : Blo 1258447 8074799 := bstep (se 1 (by rfl) ⟨6056099, by rfl⟩ : syracuseStep 8074799 = 12112199) B12112199
theorem B13621729 : Blo 1258447 13621729 := bstep (se 2 (by rfl) ⟨5108148, by rfl⟩ : syracuseStep 13621729 = 10216297) B10216297
theorem B29063681 : Blo 1258447 29063681 := bstep (se 2 (by rfl) ⟨10898880, by rfl⟩ : syracuseStep 29063681 = 21797761) B21797761
theorem B2834279 : Blo 1258447 2834279 := bstep (se 1 (by rfl) ⟨2125709, by rfl⟩ : syracuseStep 2834279 = 4251419) B4251419
theorem B18162305 : Blo 1258447 18162305 := bstep (se 2 (by rfl) ⟨6810864, by rfl⟩ : syracuseStep 18162305 = 13621729) B13621729
theorem B5383199 : Blo 1258447 5383199 := bstep (se 1 (by rfl) ⟨4037399, by rfl⟩ : syracuseStep 5383199 = 8074799) B8074799
theorem B19375787 : Blo 1258447 19375787 := bstep (se 1 (by rfl) ⟨14531840, by rfl⟩ : syracuseStep 19375787 = 29063681) B29063681
theorem B23300891 : Blo 1258447 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B27609979 : Blo 1258447 27609979 := bstep (se 1 (by rfl) ⟨20707484, by rfl⟩ : syracuseStep 27609979 = 41414969) B41414969
theorem B137884031 : Blo 1258447 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B4780903 : Blo 1258447 4780903 := bstep (se 1 (by rfl) ⟨3585677, by rfl⟩ : syracuseStep 4780903 = 7171355) B7171355
theorem B1258735 : Blo 1258447 1258735 := bstep (se 1 (by rfl) ⟨944051, by rfl⟩ : syracuseStep 1258735 = 1888103) B1888103
theorem B1889519 : Blo 1258447 1889519 := bstep (se 1 (by rfl) ⟨1417139, by rfl⟩ : syracuseStep 1889519 = 2834279) B2834279
theorem B9565451 : Blo 1258447 9565451 := bstep (se 1 (by rfl) ⟨7174088, by rfl⟩ : syracuseStep 9565451 = 14348177) B14348177
theorem B1258823 : Blo 1258447 1258823 := bstep (se 1 (by rfl) ⟨944117, by rfl⟩ : syracuseStep 1258823 = 1888235) B1888235
theorem B6378911 : Blo 1258447 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B4537721 : Blo 1258447 4537721 := bstep (se 2 (by rfl) ⟨1701645, by rfl⟩ : syracuseStep 4537721 = 3403291) B3403291
theorem B10345967 : Blo 1258447 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B91922687 : Blo 1258447 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B12108203 : Blo 1258447 12108203 := bstep (se 1 (by rfl) ⟨9081152, by rfl⟩ : syracuseStep 12108203 = 18162305) B18162305
theorem B3588799 : Blo 1258447 3588799 := bstep (se 1 (by rfl) ⟨2691599, by rfl⟩ : syracuseStep 3588799 = 5383199) B5383199
theorem B4252607 : Blo 1258447 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B12100589 : Blo 1258447 12100589 := bstep (se 3 (by rfl) ⟨2268860, by rfl⟩ : syracuseStep 12100589 = 4537721) B4537721
theorem B6374537 : Blo 1258447 6374537 := bstep (se 2 (by rfl) ⟨2390451, by rfl⟩ : syracuseStep 6374537 = 4780903) B4780903
theorem B51668765 : Blo 1258447 51668765 := bstep (se 3 (by rfl) ⟨9687893, by rfl⟩ : syracuseStep 51668765 = 19375787) B19375787
theorem B15533927 : Blo 1258447 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B6376967 : Blo 1258447 6376967 := bstep (se 1 (by rfl) ⟨4782725, by rfl⟩ : syracuseStep 6376967 = 9565451) B9565451
theorem B1259679 : Blo 1258447 1259679 := bstep (se 1 (by rfl) ⟨944759, by rfl⟩ : syracuseStep 1259679 = 1889519) B1889519
theorem B36813305 : Blo 1258447 36813305 := bstep (se 2 (by rfl) ⟨13804989, by rfl⟩ : syracuseStep 36813305 = 27609979) B27609979
theorem B6897311 : Blo 1258447 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B2835071 : Blo 1258447 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B4785065 : Blo 1258447 4785065 := bstep (se 2 (by rfl) ⟨1794399, by rfl⟩ : syracuseStep 4785065 = 3588799) B3588799
theorem B10355951 : Blo 1258447 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B4598207 : Blo 1258447 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B8072135 : Blo 1258447 8072135 := bstep (se 1 (by rfl) ⟨6054101, by rfl⟩ : syracuseStep 8072135 = 12108203) B12108203
theorem B61281791 : Blo 1258447 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B8067059 : Blo 1258447 8067059 := bstep (se 1 (by rfl) ⟨6050294, by rfl⟩ : syracuseStep 8067059 = 12100589) B12100589
theorem B4249691 : Blo 1258447 4249691 := bstep (se 1 (by rfl) ⟨3187268, by rfl⟩ : syracuseStep 4249691 = 6374537) B6374537
theorem B34445843 : Blo 1258447 34445843 := bstep (se 1 (by rfl) ⟨25834382, by rfl⟩ : syracuseStep 34445843 = 51668765) B51668765
theorem B24542203 : Blo 1258447 24542203 := bstep (se 1 (by rfl) ⟨18406652, by rfl⟩ : syracuseStep 24542203 = 36813305) B36813305
theorem B4251311 : Blo 1258447 4251311 := bstep (se 1 (by rfl) ⟨3188483, by rfl⟩ : syracuseStep 4251311 = 6376967) B6376967
theorem B40854527 : Blo 1258447 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B3065471 : Blo 1258447 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B22963895 : Blo 1258447 22963895 := bstep (se 1 (by rfl) ⟨17222921, by rfl⟩ : syracuseStep 22963895 = 34445843) B34445843
theorem B3190043 : Blo 1258447 3190043 := bstep (se 1 (by rfl) ⟨2392532, by rfl⟩ : syracuseStep 3190043 = 4785065) B4785065
theorem B5378039 : Blo 1258447 5378039 := bstep (se 1 (by rfl) ⟨4033529, by rfl⟩ : syracuseStep 5378039 = 8067059) B8067059
theorem B32722937 : Blo 1258447 32722937 := bstep (se 2 (by rfl) ⟨12271101, by rfl⟩ : syracuseStep 32722937 = 24542203) B24542203
theorem B1890047 : Blo 1258447 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B6903967 : Blo 1258447 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B2833127 : Blo 1258447 2833127 := bstep (se 1 (by rfl) ⟨2124845, by rfl⟩ : syracuseStep 2833127 = 4249691) B4249691
theorem B5381423 : Blo 1258447 5381423 := bstep (se 1 (by rfl) ⟨4036067, by rfl⟩ : syracuseStep 5381423 = 8072135) B8072135
theorem B2834207 : Blo 1258447 2834207 := bstep (se 1 (by rfl) ⟨2125655, by rfl⟩ : syracuseStep 2834207 = 4251311) B4251311
theorem B2043647 : Blo 1258447 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B1888751 : Blo 1258447 1888751 := bstep (se 1 (by rfl) ⟨1416563, by rfl⟩ : syracuseStep 1888751 = 2833127) B2833127
theorem B2126695 : Blo 1258447 2126695 := bstep (se 1 (by rfl) ⟨1595021, by rfl⟩ : syracuseStep 2126695 = 3190043) B3190043
theorem B1889471 : Blo 1258447 1889471 := bstep (se 1 (by rfl) ⟨1417103, by rfl⟩ : syracuseStep 1889471 = 2834207) B2834207
theorem B3585359 : Blo 1258447 3585359 := bstep (se 1 (by rfl) ⟨2689019, by rfl⟩ : syracuseStep 3585359 = 5378039) B5378039
theorem B9205289 : Blo 1258447 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B27236351 : Blo 1258447 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B15309263 : Blo 1258447 15309263 := bstep (se 1 (by rfl) ⟨11481947, by rfl⟩ : syracuseStep 15309263 = 22963895) B22963895
theorem B1260031 : Blo 1258447 1260031 := bstep (se 1 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 1260031 = 1890047) B1890047
theorem B3587615 : Blo 1258447 3587615 := bstep (se 1 (by rfl) ⟨2690711, by rfl⟩ : syracuseStep 3587615 = 5381423) B5381423
theorem B21815291 : Blo 1258447 21815291 := bstep (se 1 (by rfl) ⟨16361468, by rfl⟩ : syracuseStep 21815291 = 32722937) B32722937
theorem B6136859 : Blo 1258447 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B2835593 : Blo 1258447 2835593 := bstep (se 2 (by rfl) ⟨1063347, by rfl⟩ : syracuseStep 2835593 = 2126695) B2126695
theorem B1362431 : Blo 1258447 1362431 := bstep (se 1 (by rfl) ⟨1021823, by rfl⟩ : syracuseStep 1362431 = 2043647) B2043647
theorem B58174109 : Blo 1258447 58174109 := bstep (se 3 (by rfl) ⟨10907645, by rfl⟩ : syracuseStep 58174109 = 21815291) B21815291
theorem B1259167 : Blo 1258447 1259167 := bstep (se 1 (by rfl) ⟨944375, by rfl⟩ : syracuseStep 1259167 = 1888751) B1888751
theorem B1259647 : Blo 1258447 1259647 := bstep (se 1 (by rfl) ⟨944735, by rfl⟩ : syracuseStep 1259647 = 1889471) B1889471
theorem B2390239 : Blo 1258447 2390239 := bstep (se 1 (by rfl) ⟨1792679, by rfl⟩ : syracuseStep 2390239 = 3585359) B3585359
theorem B10206175 : Blo 1258447 10206175 := bstep (se 1 (by rfl) ⟨7654631, by rfl⟩ : syracuseStep 10206175 = 15309263) B15309263
theorem B2391743 : Blo 1258447 2391743 := bstep (se 1 (by rfl) ⟨1793807, by rfl⟩ : syracuseStep 2391743 = 3587615) B3587615
theorem B72630269 : Blo 1258447 72630269 := bstep (se 3 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 72630269 = 27236351) B27236351
theorem B3186985 : Blo 1258447 3186985 := bstep (se 2 (by rfl) ⟨1195119, by rfl⟩ : syracuseStep 3186985 = 2390239) B2390239
theorem B13608233 : Blo 1258447 13608233 := bstep (se 2 (by rfl) ⟨5103087, by rfl⟩ : syracuseStep 13608233 = 10206175) B10206175
theorem B38782739 : Blo 1258447 38782739 := bstep (se 1 (by rfl) ⟨29087054, by rfl⟩ : syracuseStep 38782739 = 58174109) B58174109
theorem B4091239 : Blo 1258447 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B3633149 : Blo 1258447 3633149 := bstep (se 3 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 3633149 = 1362431) B1362431
theorem B1594495 : Blo 1258447 1594495 := bstep (se 1 (by rfl) ⟨1195871, by rfl⟩ : syracuseStep 1594495 = 2391743) B2391743
theorem B48420179 : Blo 1258447 48420179 := bstep (se 1 (by rfl) ⟨36315134, by rfl⟩ : syracuseStep 48420179 = 72630269) B72630269
theorem B1890395 : Blo 1258447 1890395 := bstep (se 1 (by rfl) ⟨1417796, by rfl⟩ : syracuseStep 1890395 = 2835593) B2835593
theorem B25855159 : Blo 1258447 25855159 := bstep (se 1 (by rfl) ⟨19391369, by rfl⟩ : syracuseStep 25855159 = 38782739) B38782739
theorem B9072155 : Blo 1258447 9072155 := bstep (se 1 (by rfl) ⟨6804116, by rfl⟩ : syracuseStep 9072155 = 13608233) B13608233
theorem B32280119 : Blo 1258447 32280119 := bstep (se 1 (by rfl) ⟨24210089, by rfl⟩ : syracuseStep 32280119 = 48420179) B48420179
theorem B2125993 : Blo 1258447 2125993 := bstep (se 2 (by rfl) ⟨797247, by rfl⟩ : syracuseStep 2125993 = 1594495) B1594495
theorem B21819941 : Blo 1258447 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B2422099 : Blo 1258447 2422099 := bstep (se 1 (by rfl) ⟨1816574, by rfl⟩ : syracuseStep 2422099 = 3633149) B3633149
theorem B4249313 : Blo 1258447 4249313 := bstep (se 2 (by rfl) ⟨1593492, by rfl⟩ : syracuseStep 4249313 = 3186985) B3186985
theorem B1260263 : Blo 1258447 1260263 := bstep (se 1 (by rfl) ⟨945197, by rfl⟩ : syracuseStep 1260263 = 1890395) B1890395
theorem B2834657 : Blo 1258447 2834657 := bstep (se 2 (by rfl) ⟨1062996, by rfl⟩ : syracuseStep 2834657 = 2125993) B2125993
theorem B34473545 : Blo 1258447 34473545 := bstep (se 2 (by rfl) ⟨12927579, by rfl⟩ : syracuseStep 34473545 = 25855159) B25855159
theorem B3229465 : Blo 1258447 3229465 := bstep (se 2 (by rfl) ⟨1211049, by rfl⟩ : syracuseStep 3229465 = 2422099) B2422099
theorem B6048103 : Blo 1258447 6048103 := bstep (se 1 (by rfl) ⟨4536077, by rfl⟩ : syracuseStep 6048103 = 9072155) B9072155
theorem B14546627 : Blo 1258447 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B2832875 : Blo 1258447 2832875 := bstep (se 1 (by rfl) ⟨2124656, by rfl⟩ : syracuseStep 2832875 = 4249313) B4249313
theorem B21520079 : Blo 1258447 21520079 := bstep (se 1 (by rfl) ⟨16140059, by rfl⟩ : syracuseStep 21520079 = 32280119) B32280119
theorem B14346719 : Blo 1258447 14346719 := bstep (se 1 (by rfl) ⟨10760039, by rfl⟩ : syracuseStep 14346719 = 21520079) B21520079
theorem B8064137 : Blo 1258447 8064137 := bstep (se 2 (by rfl) ⟨3024051, by rfl⟩ : syracuseStep 8064137 = 6048103) B6048103
theorem B22982363 : Blo 1258447 22982363 := bstep (se 1 (by rfl) ⟨17236772, by rfl⟩ : syracuseStep 22982363 = 34473545) B34473545
theorem B1888583 : Blo 1258447 1888583 := bstep (se 1 (by rfl) ⟨1416437, by rfl⟩ : syracuseStep 1888583 = 2832875) B2832875
theorem B4305953 : Blo 1258447 4305953 := bstep (se 2 (by rfl) ⟨1614732, by rfl⟩ : syracuseStep 4305953 = 3229465) B3229465
theorem B1889771 : Blo 1258447 1889771 := bstep (se 1 (by rfl) ⟨1417328, by rfl⟩ : syracuseStep 1889771 = 2834657) B2834657
theorem B9697751 : Blo 1258447 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B6465167 : Blo 1258447 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B5376091 : Blo 1258447 5376091 := bstep (se 1 (by rfl) ⟨4032068, by rfl⟩ : syracuseStep 5376091 = 8064137) B8064137
theorem B15321575 : Blo 1258447 15321575 := bstep (se 1 (by rfl) ⟨11491181, by rfl⟩ : syracuseStep 15321575 = 22982363) B22982363
theorem B2870635 : Blo 1258447 2870635 := bstep (se 1 (by rfl) ⟨2152976, by rfl⟩ : syracuseStep 2870635 = 4305953) B4305953
theorem B9564479 : Blo 1258447 9564479 := bstep (se 1 (by rfl) ⟨7173359, by rfl⟩ : syracuseStep 9564479 = 14346719) B14346719
theorem B1259055 : Blo 1258447 1259055 := bstep (se 1 (by rfl) ⟨944291, by rfl⟩ : syracuseStep 1259055 = 1888583) B1888583
theorem B1259847 : Blo 1258447 1259847 := bstep (se 1 (by rfl) ⟨944885, by rfl⟩ : syracuseStep 1259847 = 1889771) B1889771
theorem B7168121 : Blo 1258447 7168121 := bstep (se 2 (by rfl) ⟨2688045, by rfl⟩ : syracuseStep 7168121 = 5376091) B5376091
theorem B4310111 : Blo 1258447 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B3827513 : Blo 1258447 3827513 := bstep (se 2 (by rfl) ⟨1435317, by rfl⟩ : syracuseStep 3827513 = 2870635) B2870635
theorem B6376319 : Blo 1258447 6376319 := bstep (se 1 (by rfl) ⟨4782239, by rfl⟩ : syracuseStep 6376319 = 9564479) B9564479
theorem B40857533 : Blo 1258447 40857533 := bstep (se 3 (by rfl) ⟨7660787, by rfl⟩ : syracuseStep 40857533 = 15321575) B15321575
theorem B4778747 : Blo 1258447 4778747 := bstep (se 1 (by rfl) ⟨3584060, by rfl⟩ : syracuseStep 4778747 = 7168121) B7168121
theorem B2551675 : Blo 1258447 2551675 := bstep (se 1 (by rfl) ⟨1913756, by rfl⟩ : syracuseStep 2551675 = 3827513) B3827513
theorem B2873407 : Blo 1258447 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B4250879 : Blo 1258447 4250879 := bstep (se 1 (by rfl) ⟨3188159, by rfl⟩ : syracuseStep 4250879 = 6376319) B6376319
theorem B27238355 : Blo 1258447 27238355 := bstep (se 1 (by rfl) ⟨20428766, by rfl⟩ : syracuseStep 27238355 = 40857533) B40857533
theorem B3402233 : Blo 1258447 3402233 := bstep (se 2 (by rfl) ⟨1275837, by rfl⟩ : syracuseStep 3402233 = 2551675) B2551675
theorem B18158903 : Blo 1258447 18158903 := bstep (se 1 (by rfl) ⟨13619177, by rfl⟩ : syracuseStep 18158903 = 27238355) B27238355
theorem B3831209 : Blo 1258447 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B3185831 : Blo 1258447 3185831 := bstep (se 1 (by rfl) ⟨2389373, by rfl⟩ : syracuseStep 3185831 = 4778747) B4778747
theorem B2833919 : Blo 1258447 2833919 := bstep (se 1 (by rfl) ⟨2125439, by rfl⟩ : syracuseStep 2833919 = 4250879) B4250879
theorem B2123887 : Blo 1258447 2123887 := bstep (se 1 (by rfl) ⟨1592915, by rfl⟩ : syracuseStep 2123887 = 3185831) B3185831
theorem B1889279 : Blo 1258447 1889279 := bstep (se 1 (by rfl) ⟨1416959, by rfl⟩ : syracuseStep 1889279 = 2833919) B2833919
theorem B12105935 : Blo 1258447 12105935 := bstep (se 1 (by rfl) ⟨9079451, by rfl⟩ : syracuseStep 12105935 = 18158903) B18158903
theorem B2554139 : Blo 1258447 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B2268155 : Blo 1258447 2268155 := bstep (se 1 (by rfl) ⟨1701116, by rfl⟩ : syracuseStep 2268155 = 3402233) B3402233
theorem B8070623 : Blo 1258447 8070623 := bstep (se 1 (by rfl) ⟨6052967, by rfl⟩ : syracuseStep 8070623 = 12105935) B12105935
theorem B6811037 : Blo 1258447 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B1512103 : Blo 1258447 1512103 := bstep (se 1 (by rfl) ⟨1134077, by rfl⟩ : syracuseStep 1512103 = 2268155) B2268155
theorem B2831849 : Blo 1258447 2831849 := bstep (se 2 (by rfl) ⟨1061943, by rfl⟩ : syracuseStep 2831849 = 2123887) B2123887
theorem B1259519 : Blo 1258447 1259519 := bstep (se 1 (by rfl) ⟨944639, by rfl⟩ : syracuseStep 1259519 = 1889279) B1889279
theorem B2016137 : Blo 1258447 2016137 := bstep (se 2 (by rfl) ⟨756051, by rfl⟩ : syracuseStep 2016137 = 1512103) B1512103
theorem B4540691 : Blo 1258447 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B1887899 : Blo 1258447 1887899 := bstep (se 1 (by rfl) ⟨1415924, by rfl⟩ : syracuseStep 1887899 = 2831849) B2831849
theorem B5380415 : Blo 1258447 5380415 := bstep (se 1 (by rfl) ⟨4035311, by rfl⟩ : syracuseStep 5380415 = 8070623) B8070623
theorem B5376365 : Blo 1258447 5376365 := bstep (se 3 (by rfl) ⟨1008068, by rfl⟩ : syracuseStep 5376365 = 2016137) B2016137
theorem B3027127 : Blo 1258447 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B1258599 : Blo 1258447 1258599 := bstep (se 1 (by rfl) ⟨943949, by rfl⟩ : syracuseStep 1258599 = 1887899) B1887899
theorem B3586943 : Blo 1258447 3586943 := bstep (se 1 (by rfl) ⟨2690207, by rfl⟩ : syracuseStep 3586943 = 5380415) B5380415
theorem B3584243 : Blo 1258447 3584243 := bstep (se 1 (by rfl) ⟨2688182, by rfl⟩ : syracuseStep 3584243 = 5376365) B5376365
theorem B4036169 : Blo 1258447 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B2391295 : Blo 1258447 2391295 := bstep (se 1 (by rfl) ⟨1793471, by rfl⟩ : syracuseStep 2391295 = 3586943) B3586943
theorem B3188393 : Blo 1258447 3188393 := bstep (se 2 (by rfl) ⟨1195647, by rfl⟩ : syracuseStep 3188393 = 2391295) B2391295
theorem B2389495 : Blo 1258447 2389495 := bstep (se 1 (by rfl) ⟨1792121, by rfl⟩ : syracuseStep 2389495 = 3584243) B3584243
theorem B10763117 : Blo 1258447 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B2125595 : Blo 1258447 2125595 := bstep (se 1 (by rfl) ⟨1594196, by rfl⟩ : syracuseStep 2125595 = 3188393) B3188393
theorem B7175411 : Blo 1258447 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B3185993 : Blo 1258447 3185993 := bstep (se 2 (by rfl) ⟨1194747, by rfl⟩ : syracuseStep 3185993 = 2389495) B2389495
theorem B2123995 : Blo 1258447 2123995 := bstep (se 1 (by rfl) ⟨1592996, by rfl⟩ : syracuseStep 2123995 = 3185993) B3185993
theorem B4783607 : Blo 1258447 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B1417063 : Blo 1258447 1417063 := bstep (se 1 (by rfl) ⟨1062797, by rfl⟩ : syracuseStep 1417063 = 2125595) B2125595
theorem B3189071 : Blo 1258447 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B1889417 : Blo 1258447 1889417 := bstep (se 2 (by rfl) ⟨708531, by rfl⟩ : syracuseStep 1889417 = 1417063) B1417063
theorem B2831993 : Blo 1258447 2831993 := bstep (se 2 (by rfl) ⟨1061997, by rfl⟩ : syracuseStep 2831993 = 2123995) B2123995
theorem B1887995 : Blo 1258447 1887995 := bstep (se 1 (by rfl) ⟨1415996, by rfl⟩ : syracuseStep 1887995 = 2831993) B2831993
theorem B2126047 : Blo 1258447 2126047 := bstep (se 1 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 2126047 = 3189071) B3189071
theorem B1259611 : Blo 1258447 1259611 := bstep (se 1 (by rfl) ⟨944708, by rfl⟩ : syracuseStep 1259611 = 1889417) B1889417
theorem B2834729 : Blo 1258447 2834729 := bstep (se 2 (by rfl) ⟨1063023, by rfl⟩ : syracuseStep 2834729 = 2126047) B2126047
theorem B1258663 : Blo 1258447 1258663 := bstep (se 1 (by rfl) ⟨943997, by rfl⟩ : syracuseStep 1258663 = 1887995) B1887995
theorem B1889819 : Blo 1258447 1889819 := bstep (se 1 (by rfl) ⟨1417364, by rfl⟩ : syracuseStep 1889819 = 2834729) B2834729
theorem B1259879 : Blo 1258447 1259879 := bstep (se 1 (by rfl) ⟨944909, by rfl⟩ : syracuseStep 1259879 = 1889819) B1889819

theorem C0 (j : ℕ) (h1 : 314611 ≤ j) (h2 : j ≤ 315111) : Blo 1258447 (4 * j + 3) := by
  interval_cases j
  · exact B1258447
  · exact B1258451
  · exact B1258455
  · exact B1258459
  · exact B1258463
  · exact B1258467
  · exact B1258471
  · exact B1258475
  · exact B1258479
  · exact B1258483
  · exact B1258487
  · exact B1258491
  · exact B1258495
  · exact B1258499
  · exact B1258503
  · exact B1258507
  · exact B1258511
  · exact B1258515
  · exact B1258519
  · exact B1258523
  · exact B1258527
  · exact B1258531
  · exact B1258535
  · exact B1258539
  · exact B1258543
  · exact B1258547
  · exact B1258551
  · exact B1258555
  · exact B1258559
  · exact B1258563
  · exact B1258567
  · exact B1258571
  · exact B1258575
  · exact B1258579
  · exact B1258583
  · exact B1258587
  · exact B1258591
  · exact B1258595
  · exact B1258599
  · exact B1258603
  · exact B1258607
  · exact B1258611
  · exact B1258615
  · exact B1258619
  · exact B1258623
  · exact B1258627
  · exact B1258631
  · exact B1258635
  · exact B1258639
  · exact B1258643
  · exact B1258647
  · exact B1258651
  · exact B1258655
  · exact B1258659
  · exact B1258663
  · exact B1258667
  · exact B1258671
  · exact B1258675
  · exact B1258679
  · exact B1258683
  · exact B1258687
  · exact B1258691
  · exact B1258695
  · exact B1258699
  · exact B1258703
  · exact B1258707
  · exact B1258711
  · exact B1258715
  · exact B1258719
  · exact B1258723
  · exact B1258727
  · exact B1258731
  · exact B1258735
  · exact B1258739
  · exact B1258743
  · exact B1258747
  · exact B1258751
  · exact B1258755
  · exact B1258759
  · exact B1258763
  · exact B1258767
  · exact B1258771
  · exact B1258775
  · exact B1258779
  · exact B1258783
  · exact B1258787
  · exact B1258791
  · exact B1258795
  · exact B1258799
  · exact B1258803
  · exact B1258807
  · exact B1258811
  · exact B1258815
  · exact B1258819
  · exact B1258823
  · exact B1258827
  · exact B1258831
  · exact B1258835
  · exact B1258839
  · exact B1258843
  · exact B1258847
  · exact B1258851
  · exact B1258855
  · exact B1258859
  · exact B1258863
  · exact B1258867
  · exact B1258871
  · exact B1258875
  · exact B1258879
  · exact B1258883
  · exact B1258887
  · exact B1258891
  · exact B1258895
  · exact B1258899
  · exact B1258903
  · exact B1258907
  · exact B1258911
  · exact B1258915
  · exact B1258919
  · exact B1258923
  · exact B1258927
  · exact B1258931
  · exact B1258935
  · exact B1258939
  · exact B1258943
  · exact B1258947
  · exact B1258951
  · exact B1258955
  · exact B1258959
  · exact B1258963
  · exact B1258967
  · exact B1258971
  · exact B1258975
  · exact B1258979
  · exact B1258983
  · exact B1258987
  · exact B1258991
  · exact B1258995
  · exact B1258999
  · exact B1259003
  · exact B1259007
  · exact B1259011
  · exact B1259015
  · exact B1259019
  · exact B1259023
  · exact B1259027
  · exact B1259031
  · exact B1259035
  · exact B1259039
  · exact B1259043
  · exact B1259047
  · exact B1259051
  · exact B1259055
  · exact B1259059
  · exact B1259063
  · exact B1259067
  · exact B1259071
  · exact B1259075
  · exact B1259079
  · exact B1259083
  · exact B1259087
  · exact B1259091
  · exact B1259095
  · exact B1259099
  · exact B1259103
  · exact B1259107
  · exact B1259111
  · exact B1259115
  · exact B1259119
  · exact B1259123
  · exact B1259127
  · exact B1259131
  · exact B1259135
  · exact B1259139
  · exact B1259143
  · exact B1259147
  · exact B1259151
  · exact B1259155
  · exact B1259159
  · exact B1259163
  · exact B1259167
  · exact B1259171
  · exact B1259175
  · exact B1259179
  · exact B1259183
  · exact B1259187
  · exact B1259191
  · exact B1259195
  · exact B1259199
  · exact B1259203
  · exact B1259207
  · exact B1259211
  · exact B1259215
  · exact B1259219
  · exact B1259223
  · exact B1259227
  · exact B1259231
  · exact B1259235
  · exact B1259239
  · exact B1259243
  · exact B1259247
  · exact B1259251
  · exact B1259255
  · exact B1259259
  · exact B1259263
  · exact B1259267
  · exact B1259271
  · exact B1259275
  · exact B1259279
  · exact B1259283
  · exact B1259287
  · exact B1259291
  · exact B1259295
  · exact B1259299
  · exact B1259303
  · exact B1259307
  · exact B1259311
  · exact B1259315
  · exact B1259319
  · exact B1259323
  · exact B1259327
  · exact B1259331
  · exact B1259335
  · exact B1259339
  · exact B1259343
  · exact B1259347
  · exact B1259351
  · exact B1259355
  · exact B1259359
  · exact B1259363
  · exact B1259367
  · exact B1259371
  · exact B1259375
  · exact B1259379
  · exact B1259383
  · exact B1259387
  · exact B1259391
  · exact B1259395
  · exact B1259399
  · exact B1259403
  · exact B1259407
  · exact B1259411
  · exact B1259415
  · exact B1259419
  · exact B1259423
  · exact B1259427
  · exact B1259431
  · exact B1259435
  · exact B1259439
  · exact B1259443
  · exact B1259447
  · exact B1259451
  · exact B1259455
  · exact B1259459
  · exact B1259463
  · exact B1259467
  · exact B1259471
  · exact B1259475
  · exact B1259479
  · exact B1259483
  · exact B1259487
  · exact B1259491
  · exact B1259495
  · exact B1259499
  · exact B1259503
  · exact B1259507
  · exact B1259511
  · exact B1259515
  · exact B1259519
  · exact B1259523
  · exact B1259527
  · exact B1259531
  · exact B1259535
  · exact B1259539
  · exact B1259543
  · exact B1259547
  · exact B1259551
  · exact B1259555
  · exact B1259559
  · exact B1259563
  · exact B1259567
  · exact B1259571
  · exact B1259575
  · exact B1259579
  · exact B1259583
  · exact B1259587
  · exact B1259591
  · exact B1259595
  · exact B1259599
  · exact B1259603
  · exact B1259607
  · exact B1259611
  · exact B1259615
  · exact B1259619
  · exact B1259623
  · exact B1259627
  · exact B1259631
  · exact B1259635
  · exact B1259639
  · exact B1259643
  · exact B1259647
  · exact B1259651
  · exact B1259655
  · exact B1259659
  · exact B1259663
  · exact B1259667
  · exact B1259671
  · exact B1259675
  · exact B1259679
  · exact B1259683
  · exact B1259687
  · exact B1259691
  · exact B1259695
  · exact B1259699
  · exact B1259703
  · exact B1259707
  · exact B1259711
  · exact B1259715
  · exact B1259719
  · exact B1259723
  · exact B1259727
  · exact B1259731
  · exact B1259735
  · exact B1259739
  · exact B1259743
  · exact B1259747
  · exact B1259751
  · exact B1259755
  · exact B1259759
  · exact B1259763
  · exact B1259767
  · exact B1259771
  · exact B1259775
  · exact B1259779
  · exact B1259783
  · exact B1259787
  · exact B1259791
  · exact B1259795
  · exact B1259799
  · exact B1259803
  · exact B1259807
  · exact B1259811
  · exact B1259815
  · exact B1259819
  · exact B1259823
  · exact B1259827
  · exact B1259831
  · exact B1259835
  · exact B1259839
  · exact B1259843
  · exact B1259847
  · exact B1259851
  · exact B1259855
  · exact B1259859
  · exact B1259863
  · exact B1259867
  · exact B1259871
  · exact B1259875
  · exact B1259879
  · exact B1259883
  · exact B1259887
  · exact B1259891
  · exact B1259895
  · exact B1259899
  · exact B1259903
  · exact B1259907
  · exact B1259911
  · exact B1259915
  · exact B1259919
  · exact B1259923
  · exact B1259927
  · exact B1259931
  · exact B1259935
  · exact B1259939
  · exact B1259943
  · exact B1259947
  · exact B1259951
  · exact B1259955
  · exact B1259959
  · exact B1259963
  · exact B1259967
  · exact B1259971
  · exact B1259975
  · exact B1259979
  · exact B1259983
  · exact B1259987
  · exact B1259991
  · exact B1259995
  · exact B1259999
  · exact B1260003
  · exact B1260007
  · exact B1260011
  · exact B1260015
  · exact B1260019
  · exact B1260023
  · exact B1260027
  · exact B1260031
  · exact B1260035
  · exact B1260039
  · exact B1260043
  · exact B1260047
  · exact B1260051
  · exact B1260055
  · exact B1260059
  · exact B1260063
  · exact B1260067
  · exact B1260071
  · exact B1260075
  · exact B1260079
  · exact B1260083
  · exact B1260087
  · exact B1260091
  · exact B1260095
  · exact B1260099
  · exact B1260103
  · exact B1260107
  · exact B1260111
  · exact B1260115
  · exact B1260119
  · exact B1260123
  · exact B1260127
  · exact B1260131
  · exact B1260135
  · exact B1260139
  · exact B1260143
  · exact B1260147
  · exact B1260151
  · exact B1260155
  · exact B1260159
  · exact B1260163
  · exact B1260167
  · exact B1260171
  · exact B1260175
  · exact B1260179
  · exact B1260183
  · exact B1260187
  · exact B1260191
  · exact B1260195
  · exact B1260199
  · exact B1260203
  · exact B1260207
  · exact B1260211
  · exact B1260215
  · exact B1260219
  · exact B1260223
  · exact B1260227
  · exact B1260231
  · exact B1260235
  · exact B1260239
  · exact B1260243
  · exact B1260247
  · exact B1260251
  · exact B1260255
  · exact B1260259
  · exact B1260263
  · exact B1260267
  · exact B1260271
  · exact B1260275
  · exact B1260279
  · exact B1260283
  · exact B1260287
  · exact B1260291
  · exact B1260295
  · exact B1260299
  · exact B1260303
  · exact B1260307
  · exact B1260311
  · exact B1260315
  · exact B1260319
  · exact B1260323
  · exact B1260327
  · exact B1260331
  · exact B1260335
  · exact B1260339
  · exact B1260343
  · exact B1260347
  · exact B1260351
  · exact B1260355
  · exact B1260359
  · exact B1260363
  · exact B1260367
  · exact B1260371
  · exact B1260375
  · exact B1260379
  · exact B1260383
  · exact B1260387
  · exact B1260391
  · exact B1260395
  · exact B1260399
  · exact B1260403
  · exact B1260407
  · exact B1260411
  · exact B1260415
  · exact B1260419
  · exact B1260423
  · exact B1260427
  · exact B1260431
  · exact B1260435
  · exact B1260439
  · exact B1260443
  · exact B1260447

theorem solution (m : ℕ) (hlo : 1258447 ≤ m) (hhi : m ≤ 1260447) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 314611 ≤ j := by omega
    have hj2 : j ≤ 315111 := by omega
    have hb : Blo 1258447 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
