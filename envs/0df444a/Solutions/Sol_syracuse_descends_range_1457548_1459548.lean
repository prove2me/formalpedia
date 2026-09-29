-- Prove2me | solution 1 for syracuse_descends_range_1457548_1459548
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:14:07.508774+00:00
-- url     : https://prove2.me/submissions/3758597a-ca89-43c0-96e7-219138959e06

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


theorem B2187269 : Blo 1457548 2187269 := bbase (se 4 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 2187269 = 410113) (by norm_num)
theorem B1753105 : Blo 1457548 1753105 := bbase (se 2 (by rfl) ⟨657414, by rfl⟩ : syracuseStep 1753105 = 1314829) (by norm_num)
theorem B2768917 : Blo 1457548 2768917 := bbase (se 6 (by rfl) ⟨64896, by rfl⟩ : syracuseStep 2768917 = 129793) (by norm_num)
theorem B2187293 : Blo 1457548 2187293 := bbase (se 3 (by rfl) ⟨410117, by rfl⟩ : syracuseStep 2187293 = 820235) (by norm_num)
theorem B2187317 : Blo 1457548 2187317 := bbase (se 5 (by rfl) ⟨102530, by rfl⟩ : syracuseStep 2187317 = 205061) (by norm_num)
theorem B2629693 : Blo 1457548 2629693 := bbase (se 3 (by rfl) ⟨493067, by rfl⟩ : syracuseStep 2629693 = 986135) (by norm_num)
theorem B2187341 : Blo 1457548 2187341 := bbase (se 3 (by rfl) ⟨410126, by rfl⟩ : syracuseStep 2187341 = 820253) (by norm_num)
theorem B2187365 : Blo 1457548 2187365 := bbase (se 4 (by rfl) ⟨205065, by rfl⟩ : syracuseStep 2187365 = 410131) (by norm_num)
theorem B3506285 : Blo 1457548 3506285 := bbase (se 3 (by rfl) ⟨657428, by rfl⟩ : syracuseStep 3506285 = 1314857) (by norm_num)
theorem B5537909 : Blo 1457548 5537909 := bbase (se 5 (by rfl) ⟨259589, by rfl⟩ : syracuseStep 5537909 = 519179) (by norm_num)
theorem B2334845 : Blo 1457548 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B2187389 : Blo 1457548 2187389 := bbase (se 3 (by rfl) ⟨410135, by rfl⟩ : syracuseStep 2187389 = 820271) (by norm_num)
theorem B2629757 : Blo 1457548 2629757 := bbase (se 3 (by rfl) ⟨493079, by rfl⟩ : syracuseStep 2629757 = 986159) (by norm_num)
theorem B3113093 : Blo 1457548 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B2187413 : Blo 1457548 2187413 := bbase (se 6 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 2187413 = 102535) (by norm_num)
theorem B2769061 : Blo 1457548 2769061 := bbase (se 4 (by rfl) ⟨259599, by rfl⟩ : syracuseStep 2769061 = 519199) (by norm_num)
theorem B4923557 : Blo 1457548 4923557 := bbase (se 4 (by rfl) ⟨461583, by rfl⟩ : syracuseStep 4923557 = 923167) (by norm_num)
theorem B2187437 : Blo 1457548 2187437 := bbase (se 3 (by rfl) ⟨410144, by rfl⟩ : syracuseStep 2187437 = 820289) (by norm_num)
theorem B2187461 : Blo 1457548 2187461 := bbase (se 4 (by rfl) ⟨205074, by rfl⟩ : syracuseStep 2187461 = 410149) (by norm_num)
theorem B7381205 : Blo 1457548 7381205 := bbase (se 7 (by rfl) ⟨86498, by rfl⟩ : syracuseStep 7381205 = 172997) (by norm_num)
theorem B14016725 : Blo 1457548 14016725 := bbase (se 7 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 14016725 = 328517) (by norm_num)
theorem B2187485 : Blo 1457548 2187485 := bbase (se 3 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 2187485 = 820307) (by norm_num)
theorem B1753321 : Blo 1457548 1753321 := bbase (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) (by norm_num)
theorem B1556717 : Blo 1457548 1556717 := bbase (se 3 (by rfl) ⟨291884, by rfl⟩ : syracuseStep 1556717 = 583769) (by norm_num)
theorem B2187509 : Blo 1457548 2187509 := bbase (se 5 (by rfl) ⟨102539, by rfl⟩ : syracuseStep 2187509 = 205079) (by norm_num)
theorem B2187533 : Blo 1457548 2187533 := bbase (se 3 (by rfl) ⟨410162, by rfl⟩ : syracuseStep 2187533 = 820325) (by norm_num)
theorem B2187557 : Blo 1457548 2187557 := bbase (se 4 (by rfl) ⟨205083, by rfl⟩ : syracuseStep 2187557 = 410167) (by norm_num)
theorem B1556777 : Blo 1457548 1556777 := bbase (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) (by norm_num)
theorem B2187581 : Blo 1457548 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B1663301 : Blo 1457548 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B2769221 : Blo 1457548 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B2187605 : Blo 1457548 2187605 := bbase (se 10 (by rfl) ⟨3204, by rfl⟩ : syracuseStep 2187605 = 6409) (by norm_num)
theorem B3326309 : Blo 1457548 3326309 := bbase (se 4 (by rfl) ⟨311841, by rfl⟩ : syracuseStep 3326309 = 623683) (by norm_num)
theorem B2187629 : Blo 1457548 2187629 := bbase (se 3 (by rfl) ⟨410180, by rfl⟩ : syracuseStep 2187629 = 820361) (by norm_num)
theorem B2187653 : Blo 1457548 2187653 := bbase (se 4 (by rfl) ⟨205092, by rfl⟩ : syracuseStep 2187653 = 410185) (by norm_num)
theorem B2187677 : Blo 1457548 2187677 := bbase (se 3 (by rfl) ⟨410189, by rfl⟩ : syracuseStep 2187677 = 820379) (by norm_num)
theorem B1556905 : Blo 1457548 1556905 := bbase (se 2 (by rfl) ⟨583839, by rfl⟩ : syracuseStep 1556905 = 1167679) (by norm_num)
theorem B2187701 : Blo 1457548 2187701 := bbase (se 5 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 2187701 = 205097) (by norm_num)
theorem B2187725 : Blo 1457548 2187725 := bbase (se 3 (by rfl) ⟨410198, by rfl⟩ : syracuseStep 2187725 = 820397) (by norm_num)
theorem B2769365 : Blo 1457548 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B2187749 : Blo 1457548 2187749 := bbase (se 4 (by rfl) ⟨205101, by rfl⟩ : syracuseStep 2187749 = 410203) (by norm_num)
theorem B2187773 : Blo 1457548 2187773 := bbase (se 3 (by rfl) ⟨410207, by rfl⟩ : syracuseStep 2187773 = 820415) (by norm_num)
theorem B2187797 : Blo 1457548 2187797 := bbase (se 6 (by rfl) ⟨51276, by rfl⟩ : syracuseStep 2187797 = 102553) (by norm_num)
theorem B16613909 : Blo 1457548 16613909 := bbase (se 6 (by rfl) ⟨389388, by rfl⟩ : syracuseStep 16613909 = 778777) (by norm_num)
theorem B2187821 : Blo 1457548 2187821 := bbase (se 3 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 2187821 = 820433) (by norm_num)
theorem B2335301 : Blo 1457548 2335301 := bbase (se 4 (by rfl) ⟨218934, by rfl⟩ : syracuseStep 2335301 = 437869) (by norm_num)
theorem B2187845 : Blo 1457548 2187845 := bbase (se 4 (by rfl) ⟨205110, by rfl⟩ : syracuseStep 2187845 = 410221) (by norm_num)
theorem B4923989 : Blo 1457548 4923989 := bbase (se 8 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 4923989 = 57703) (by norm_num)
theorem B2957909 : Blo 1457548 2957909 := bbase (se 8 (by rfl) ⟨17331, by rfl⟩ : syracuseStep 2957909 = 34663) (by norm_num)
theorem B2187869 : Blo 1457548 2187869 := bbase (se 3 (by rfl) ⟨410225, by rfl⟩ : syracuseStep 2187869 = 820451) (by norm_num)
theorem B2187893 : Blo 1457548 2187893 := bbase (se 5 (by rfl) ⟨102557, by rfl⟩ : syracuseStep 2187893 = 205115) (by norm_num)
theorem B2187917 : Blo 1457548 2187917 := bbase (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) (by norm_num)
theorem B3744397 : Blo 1457548 3744397 := bbase (se 3 (by rfl) ⟨702074, by rfl⟩ : syracuseStep 3744397 = 1404149) (by norm_num)
theorem B21013141 : Blo 1457548 21013141 := bbase (se 6 (by rfl) ⟨492495, by rfl⟩ : syracuseStep 21013141 = 984991) (by norm_num)
theorem B2187941 : Blo 1457548 2187941 := bbase (se 4 (by rfl) ⟨205119, by rfl⟩ : syracuseStep 2187941 = 410239) (by norm_num)
theorem B2187965 : Blo 1457548 2187965 := bbase (se 3 (by rfl) ⟨410243, by rfl⟩ : syracuseStep 2187965 = 820487) (by norm_num)
theorem B2187989 : Blo 1457548 2187989 := bbase (se 7 (by rfl) ⟨25640, by rfl⟩ : syracuseStep 2187989 = 51281) (by norm_num)
theorem B2188013 : Blo 1457548 2188013 := bbase (se 3 (by rfl) ⟨410252, by rfl⟩ : syracuseStep 2188013 = 820505) (by norm_num)
theorem B2769653 : Blo 1457548 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B2188037 : Blo 1457548 2188037 := bbase (se 4 (by rfl) ⟨205128, by rfl⟩ : syracuseStep 2188037 = 410257) (by norm_num)
theorem B2188061 : Blo 1457548 2188061 := bbase (se 3 (by rfl) ⟨410261, by rfl⟩ : syracuseStep 2188061 = 820523) (by norm_num)
theorem B2188085 : Blo 1457548 2188085 := bbase (se 5 (by rfl) ⟨102566, by rfl⟩ : syracuseStep 2188085 = 205133) (by norm_num)
theorem B2188109 : Blo 1457548 2188109 := bbase (se 3 (by rfl) ⟨410270, by rfl⟩ : syracuseStep 2188109 = 820541) (by norm_num)
theorem B4670293 : Blo 1457548 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B1557349 : Blo 1457548 1557349 := bbase (se 4 (by rfl) ⟨146001, by rfl⟩ : syracuseStep 1557349 = 292003) (by norm_num)
theorem B2188133 : Blo 1457548 2188133 := bbase (se 4 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 2188133 = 410275) (by norm_num)
theorem B2253685 : Blo 1457548 2253685 := bbase (se 5 (by rfl) ⟨105641, by rfl⟩ : syracuseStep 2253685 = 211283) (by norm_num)
theorem B2188157 : Blo 1457548 2188157 := bbase (se 3 (by rfl) ⟨410279, by rfl⟩ : syracuseStep 2188157 = 820559) (by norm_num)
theorem B2769805 : Blo 1457548 2769805 := bbase (se 3 (by rfl) ⟨519338, by rfl⟩ : syracuseStep 2769805 = 1038677) (by norm_num)
theorem B2188181 : Blo 1457548 2188181 := bbase (se 6 (by rfl) ⟨51285, by rfl⟩ : syracuseStep 2188181 = 102571) (by norm_num)
theorem B2188205 : Blo 1457548 2188205 := bbase (se 3 (by rfl) ⟨410288, by rfl⟩ : syracuseStep 2188205 = 820577) (by norm_num)
theorem B2188229 : Blo 1457548 2188229 := bbase (se 4 (by rfl) ⟨205146, by rfl⟩ : syracuseStep 2188229 = 410293) (by norm_num)
theorem B1557469 : Blo 1457548 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B2188253 : Blo 1457548 2188253 := bbase (se 3 (by rfl) ⟨410297, by rfl⟩ : syracuseStep 2188253 = 820595) (by norm_num)
theorem B9339893 : Blo 1457548 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B2188277 : Blo 1457548 2188277 := bbase (se 5 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 2188277 = 205151) (by norm_num)
theorem B3113981 : Blo 1457548 3113981 := bbase (se 3 (by rfl) ⟨583871, by rfl⟩ : syracuseStep 3113981 = 1167743) (by norm_num)
theorem B1663997 : Blo 1457548 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B4924421 : Blo 1457548 4924421 := bbase (se 4 (by rfl) ⟨461664, by rfl⟩ : syracuseStep 4924421 = 923329) (by norm_num)
theorem B2188301 : Blo 1457548 2188301 := bbase (se 3 (by rfl) ⟨410306, by rfl⟩ : syracuseStep 2188301 = 820613) (by norm_num)
theorem B2188325 : Blo 1457548 2188325 := bbase (se 4 (by rfl) ⟨205155, by rfl⟩ : syracuseStep 2188325 = 410311) (by norm_num)
theorem B2188349 : Blo 1457548 2188349 := bbase (se 3 (by rfl) ⟨410315, by rfl⟩ : syracuseStep 2188349 = 820631) (by norm_num)
theorem B2188373 : Blo 1457548 2188373 := bbase (se 8 (by rfl) ⟨12822, by rfl⟩ : syracuseStep 2188373 = 25645) (by norm_num)
theorem B2188397 : Blo 1457548 2188397 := bbase (se 3 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 2188397 = 820649) (by norm_num)
theorem B3114101 : Blo 1457548 3114101 := bbase (se 5 (by rfl) ⟨145973, by rfl⟩ : syracuseStep 3114101 = 291947) (by norm_num)
theorem B2188421 : Blo 1457548 2188421 := bbase (se 4 (by rfl) ⟨205164, by rfl⟩ : syracuseStep 2188421 = 410329) (by norm_num)
theorem B2188445 : Blo 1457548 2188445 := bbase (se 3 (by rfl) ⟨410333, by rfl⟩ : syracuseStep 2188445 = 820667) (by norm_num)
theorem B2188469 : Blo 1457548 2188469 := bbase (se 5 (by rfl) ⟨102584, by rfl⟩ : syracuseStep 2188469 = 205169) (by norm_num)
theorem B2770109 : Blo 1457548 2770109 := bbase (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) (by norm_num)
theorem B2188493 : Blo 1457548 2188493 := bbase (se 3 (by rfl) ⟨410342, by rfl⟩ : syracuseStep 2188493 = 820685) (by norm_num)
theorem B1557721 : Blo 1457548 1557721 := bbase (se 2 (by rfl) ⟨584145, by rfl⟩ : syracuseStep 1557721 = 1168291) (by norm_num)
theorem B1557725 : Blo 1457548 1557725 := bbase (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) (by norm_num)
theorem B2188517 : Blo 1457548 2188517 := bbase (se 4 (by rfl) ⟨205173, by rfl⟩ : syracuseStep 2188517 = 410347) (by norm_num)
theorem B12625141 : Blo 1457548 12625141 := bbase (se 5 (by rfl) ⟨591803, by rfl⟩ : syracuseStep 12625141 = 1183607) (by norm_num)
theorem B2188541 : Blo 1457548 2188541 := bbase (se 3 (by rfl) ⟨410351, by rfl⟩ : syracuseStep 2188541 = 820703) (by norm_num)
theorem B2188565 : Blo 1457548 2188565 := bbase (se 6 (by rfl) ⟨51294, by rfl⟩ : syracuseStep 2188565 = 102589) (by norm_num)
theorem B2188589 : Blo 1457548 2188589 := bbase (se 3 (by rfl) ⟨410360, by rfl⟩ : syracuseStep 2188589 = 820721) (by norm_num)
theorem B2188613 : Blo 1457548 2188613 := bbase (se 4 (by rfl) ⟨205182, by rfl⟩ : syracuseStep 2188613 = 410365) (by norm_num)
theorem B2188637 : Blo 1457548 2188637 := bbase (se 3 (by rfl) ⟨410369, by rfl⟩ : syracuseStep 2188637 = 820739) (by norm_num)
theorem B1639777 : Blo 1457548 1639777 := bbase (se 2 (by rfl) ⟨614916, by rfl⟩ : syracuseStep 1639777 = 1229833) (by norm_num)
theorem B2188661 : Blo 1457548 2188661 := bbase (se 5 (by rfl) ⟨102593, by rfl⟩ : syracuseStep 2188661 = 205187) (by norm_num)
theorem B1639813 : Blo 1457548 1639813 := bbase (se 4 (by rfl) ⟨153732, by rfl⟩ : syracuseStep 1639813 = 307465) (by norm_num)
theorem B2188685 : Blo 1457548 2188685 := bbase (se 3 (by rfl) ⟨410378, by rfl⟩ : syracuseStep 2188685 = 820757) (by norm_num)
theorem B2188709 : Blo 1457548 2188709 := bbase (se 4 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 2188709 = 410383) (by norm_num)
theorem B1639849 : Blo 1457548 1639849 := bbase (se 2 (by rfl) ⟨614943, by rfl⟩ : syracuseStep 1639849 = 1229887) (by norm_num)
theorem B6227381 : Blo 1457548 6227381 := bbase (se 5 (by rfl) ⟨291908, by rfl⟩ : syracuseStep 6227381 = 583817) (by norm_num)
theorem B4924853 : Blo 1457548 4924853 := bbase (se 5 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 4924853 = 461705) (by norm_num)
theorem B2188733 : Blo 1457548 2188733 := bbase (se 3 (by rfl) ⟨410387, by rfl⟩ : syracuseStep 2188733 = 820775) (by norm_num)
theorem B1639885 : Blo 1457548 1639885 := bbase (se 3 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 1639885 = 614957) (by norm_num)
theorem B2188757 : Blo 1457548 2188757 := bbase (se 7 (by rfl) ⟨25649, by rfl⟩ : syracuseStep 2188757 = 51299) (by norm_num)
theorem B7382501 : Blo 1457548 7382501 := bbase (se 4 (by rfl) ⟨692109, by rfl⟩ : syracuseStep 7382501 = 1384219) (by norm_num)
theorem B2188781 : Blo 1457548 2188781 := bbase (se 3 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 2188781 = 820793) (by norm_num)
theorem B1639921 : Blo 1457548 1639921 := bbase (se 2 (by rfl) ⟨614970, by rfl⟩ : syracuseStep 1639921 = 1229941) (by norm_num)
theorem B2188805 : Blo 1457548 2188805 := bbase (se 4 (by rfl) ⟨205200, by rfl⟩ : syracuseStep 2188805 = 410401) (by norm_num)
theorem B1639957 : Blo 1457548 1639957 := bbase (se 6 (by rfl) ⟨38436, by rfl⟩ : syracuseStep 1639957 = 76873) (by norm_num)
theorem B2188829 : Blo 1457548 2188829 := bbase (se 3 (by rfl) ⟨410405, by rfl⟩ : syracuseStep 2188829 = 820811) (by norm_num)
theorem B2336293 : Blo 1457548 2336293 := bbase (se 4 (by rfl) ⟨219027, by rfl⟩ : syracuseStep 2336293 = 438055) (by norm_num)
theorem B1844785 : Blo 1457548 1844785 := bbase (se 2 (by rfl) ⟨691794, by rfl⟩ : syracuseStep 1844785 = 1383589) (by norm_num)
theorem B8308277 : Blo 1457548 8308277 := bbase (se 5 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 8308277 = 778901) (by norm_num)
theorem B2188853 : Blo 1457548 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B1639993 : Blo 1457548 1639993 := bbase (se 2 (by rfl) ⟨614997, by rfl⟩ : syracuseStep 1639993 = 1229995) (by norm_num)
theorem B2188877 : Blo 1457548 2188877 := bbase (se 3 (by rfl) ⟨410414, by rfl⟩ : syracuseStep 2188877 = 820829) (by norm_num)
theorem B1640029 : Blo 1457548 1640029 := bbase (se 3 (by rfl) ⟨307505, by rfl⟩ : syracuseStep 1640029 = 615011) (by norm_num)
theorem B2188901 : Blo 1457548 2188901 := bbase (se 4 (by rfl) ⟨205209, by rfl⟩ : syracuseStep 2188901 = 410419) (by norm_num)
theorem B2188925 : Blo 1457548 2188925 := bbase (se 3 (by rfl) ⟨410423, by rfl⟩ : syracuseStep 2188925 = 820847) (by norm_num)
theorem B1640065 : Blo 1457548 1640065 := bbase (se 2 (by rfl) ⟨615024, by rfl⟩ : syracuseStep 1640065 = 1230049) (by norm_num)
theorem B4671125 : Blo 1457548 4671125 := bbase (se 6 (by rfl) ⟨109479, by rfl⟩ : syracuseStep 4671125 = 218959) (by norm_num)
theorem B2188949 : Blo 1457548 2188949 := bbase (se 6 (by rfl) ⟨51303, by rfl⟩ : syracuseStep 2188949 = 102607) (by norm_num)
theorem B1640101 : Blo 1457548 1640101 := bbase (se 4 (by rfl) ⟨153759, by rfl⟩ : syracuseStep 1640101 = 307519) (by norm_num)
theorem B2188973 : Blo 1457548 2188973 := bbase (se 3 (by rfl) ⟨410432, by rfl⟩ : syracuseStep 2188973 = 820865) (by norm_num)
theorem B2188997 : Blo 1457548 2188997 := bbase (se 4 (by rfl) ⟨205218, by rfl⟩ : syracuseStep 2188997 = 410437) (by norm_num)
theorem B1640137 : Blo 1457548 1640137 := bbase (se 2 (by rfl) ⟨615051, by rfl⟩ : syracuseStep 1640137 = 1230103) (by norm_num)
theorem B1754833 : Blo 1457548 1754833 := bbase (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) (by norm_num)
theorem B1844957 : Blo 1457548 1844957 := bbase (se 3 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 1844957 = 691859) (by norm_num)
theorem B2189021 : Blo 1457548 2189021 := bbase (se 3 (by rfl) ⟨410441, by rfl⟩ : syracuseStep 2189021 = 820883) (by norm_num)
theorem B1640173 : Blo 1457548 1640173 := bbase (se 3 (by rfl) ⟨307532, by rfl⟩ : syracuseStep 1640173 = 615065) (by norm_num)
theorem B3114733 : Blo 1457548 3114733 := bbase (se 3 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 3114733 = 1168025) (by norm_num)
theorem B2189045 : Blo 1457548 2189045 := bbase (se 5 (by rfl) ⟨102611, by rfl⟩ : syracuseStep 2189045 = 205223) (by norm_num)
theorem B2189069 : Blo 1457548 2189069 := bbase (se 3 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 2189069 = 820901) (by norm_num)
theorem B1640209 : Blo 1457548 1640209 := bbase (se 2 (by rfl) ⟨615078, by rfl⟩ : syracuseStep 1640209 = 1230157) (by norm_num)
theorem B1558289 : Blo 1457548 1558289 := bbase (se 2 (by rfl) ⟨584358, by rfl⟩ : syracuseStep 1558289 = 1168717) (by norm_num)
theorem B1845013 : Blo 1457548 1845013 := bbase (se 6 (by rfl) ⟨43242, by rfl⟩ : syracuseStep 1845013 = 86485) (by norm_num)
theorem B11077397 : Blo 1457548 11077397 := bbase (se 6 (by rfl) ⟨259626, by rfl⟩ : syracuseStep 11077397 = 519253) (by norm_num)
theorem B2189093 : Blo 1457548 2189093 := bbase (se 4 (by rfl) ⟨205227, by rfl⟩ : syracuseStep 2189093 = 410455) (by norm_num)
theorem B1640245 : Blo 1457548 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B4433717 : Blo 1457548 4433717 := bbase (se 5 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 4433717 = 415661) (by norm_num)
theorem B2189117 : Blo 1457548 2189117 := bbase (se 3 (by rfl) ⟨410459, by rfl⟩ : syracuseStep 2189117 = 820919) (by norm_num)
theorem B2189141 : Blo 1457548 2189141 := bbase (se 9 (by rfl) ⟨6413, by rfl⟩ : syracuseStep 2189141 = 12827) (by norm_num)
theorem B1640281 : Blo 1457548 1640281 := bbase (se 2 (by rfl) ⟨615105, by rfl⟩ : syracuseStep 1640281 = 1230211) (by norm_num)
theorem B4925285 : Blo 1457548 4925285 := bbase (se 4 (by rfl) ⟨461745, by rfl⟩ : syracuseStep 4925285 = 923491) (by norm_num)
theorem B2189165 : Blo 1457548 2189165 := bbase (se 3 (by rfl) ⟨410468, by rfl⟩ : syracuseStep 2189165 = 820937) (by norm_num)
theorem B1845109 : Blo 1457548 1845109 := bbase (se 5 (by rfl) ⟨86489, by rfl⟩ : syracuseStep 1845109 = 172979) (by norm_num)
theorem B1640317 : Blo 1457548 1640317 := bbase (se 3 (by rfl) ⟨307559, by rfl⟩ : syracuseStep 1640317 = 615119) (by norm_num)
theorem B2189189 : Blo 1457548 2189189 := bbase (se 4 (by rfl) ⟨205236, by rfl⟩ : syracuseStep 2189189 = 410473) (by norm_num)
theorem B2189213 : Blo 1457548 2189213 := bbase (se 3 (by rfl) ⟨410477, by rfl⟩ : syracuseStep 2189213 = 820955) (by norm_num)
theorem B1640353 : Blo 1457548 1640353 := bbase (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) (by norm_num)
theorem B2770861 : Blo 1457548 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B2189237 : Blo 1457548 2189237 := bbase (se 5 (by rfl) ⟨102620, by rfl⟩ : syracuseStep 2189237 = 205241) (by norm_num)
theorem B1640389 : Blo 1457548 1640389 := bbase (se 4 (by rfl) ⟨153786, by rfl⟩ : syracuseStep 1640389 = 307573) (by norm_num)
theorem B1558477 : Blo 1457548 1558477 := bbase (se 3 (by rfl) ⟨292214, by rfl⟩ : syracuseStep 1558477 = 584429) (by norm_num)
theorem B2189261 : Blo 1457548 2189261 := bbase (se 3 (by rfl) ⟨410486, by rfl⟩ : syracuseStep 2189261 = 820973) (by norm_num)
theorem B10512341 : Blo 1457548 10512341 := bbase (se 7 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 10512341 = 246383) (by norm_num)
theorem B2189285 : Blo 1457548 2189285 := bbase (se 4 (by rfl) ⟨205245, by rfl⟩ : syracuseStep 2189285 = 410491) (by norm_num)
theorem B1640425 : Blo 1457548 1640425 := bbase (se 2 (by rfl) ⟨615159, by rfl⟩ : syracuseStep 1640425 = 1230319) (by norm_num)
theorem B2189309 : Blo 1457548 2189309 := bbase (se 3 (by rfl) ⟨410495, by rfl⟩ : syracuseStep 2189309 = 820991) (by norm_num)
theorem B1640461 : Blo 1457548 1640461 := bbase (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) (by norm_num)
theorem B1845281 : Blo 1457548 1845281 := bbase (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) (by norm_num)
theorem B2459693 : Blo 1457548 2459693 := bbase (se 3 (by rfl) ⟨461192, by rfl⟩ : syracuseStep 2459693 = 922385) (by norm_num)
theorem B1640497 : Blo 1457548 1640497 := bbase (se 2 (by rfl) ⟨615186, by rfl⟩ : syracuseStep 1640497 = 1230373) (by norm_num)
theorem B1640533 : Blo 1457548 1640533 := bbase (se 8 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 1640533 = 19225) (by norm_num)
theorem B1845337 : Blo 1457548 1845337 := bbase (se 2 (by rfl) ⟨692001, by rfl⟩ : syracuseStep 1845337 = 1384003) (by norm_num)
theorem B1640569 : Blo 1457548 1640569 := bbase (se 2 (by rfl) ⟨615213, by rfl⟩ : syracuseStep 1640569 = 1230427) (by norm_num)
theorem B1640605 : Blo 1457548 1640605 := bbase (se 3 (by rfl) ⟨307613, by rfl⟩ : syracuseStep 1640605 = 615227) (by norm_num)
theorem B2459821 : Blo 1457548 2459821 := bbase (se 3 (by rfl) ⟨461216, by rfl⟩ : syracuseStep 2459821 = 922433) (by norm_num)
theorem B2336941 : Blo 1457548 2336941 := bbase (se 3 (by rfl) ⟨438176, by rfl⟩ : syracuseStep 2336941 = 876353) (by norm_num)
theorem B11069621 : Blo 1457548 11069621 := bbase (se 5 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 11069621 = 1037777) (by norm_num)
theorem B5540021 : Blo 1457548 5540021 := bbase (se 5 (by rfl) ⟨259688, by rfl⟩ : syracuseStep 5540021 = 519377) (by norm_num)
theorem B1845433 : Blo 1457548 1845433 := bbase (se 2 (by rfl) ⟨692037, by rfl⟩ : syracuseStep 1845433 = 1384075) (by norm_num)
theorem B1640641 : Blo 1457548 1640641 := bbase (se 2 (by rfl) ⟨615240, by rfl⟩ : syracuseStep 1640641 = 1230481) (by norm_num)
theorem B3795149 : Blo 1457548 3795149 := bbase (se 3 (by rfl) ⟨711590, by rfl⟩ : syracuseStep 3795149 = 1423181) (by norm_num)
theorem B1640677 : Blo 1457548 1640677 := bbase (se 4 (by rfl) ⟨153813, by rfl⟩ : syracuseStep 1640677 = 307627) (by norm_num)
theorem B2459909 : Blo 1457548 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B1640713 : Blo 1457548 1640713 := bbase (se 2 (by rfl) ⟨615267, by rfl⟩ : syracuseStep 1640713 = 1230535) (by norm_num)
theorem B4925717 : Blo 1457548 4925717 := bbase (se 6 (by rfl) ⟨115446, by rfl⟩ : syracuseStep 4925717 = 230893) (by norm_num)
theorem B1640749 : Blo 1457548 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B1640785 : Blo 1457548 1640785 := bbase (se 2 (by rfl) ⟨615294, by rfl⟩ : syracuseStep 1640785 = 1230589) (by norm_num)
theorem B1845605 : Blo 1457548 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B1640821 : Blo 1457548 1640821 := bbase (se 5 (by rfl) ⟨76913, by rfl⟩ : syracuseStep 1640821 = 153827) (by norm_num)
theorem B2460037 : Blo 1457548 2460037 := bbase (se 4 (by rfl) ⟨230628, by rfl⟩ : syracuseStep 2460037 = 461257) (by norm_num)
theorem B1640857 : Blo 1457548 1640857 := bbase (se 2 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 1640857 = 1230643) (by norm_num)
theorem B1845661 : Blo 1457548 1845661 := bbase (se 3 (by rfl) ⟨346061, by rfl⟩ : syracuseStep 1845661 = 692123) (by norm_num)
theorem B1640893 : Blo 1457548 1640893 := bbase (se 3 (by rfl) ⟨307667, by rfl⟩ : syracuseStep 1640893 = 615335) (by norm_num)
theorem B1870273 : Blo 1457548 1870273 := bbase (se 2 (by rfl) ⟨701352, by rfl⟩ : syracuseStep 1870273 = 1402705) (by norm_num)
theorem B5540309 : Blo 1457548 5540309 := bbase (se 7 (by rfl) ⟨64925, by rfl⟩ : syracuseStep 5540309 = 129851) (by norm_num)
theorem B2460125 : Blo 1457548 2460125 := bbase (se 3 (by rfl) ⟨461273, by rfl⟩ : syracuseStep 2460125 = 922547) (by norm_num)
theorem B1640929 : Blo 1457548 1640929 := bbase (se 2 (by rfl) ⟨615348, by rfl⟩ : syracuseStep 1640929 = 1230697) (by norm_num)
theorem B4155893 : Blo 1457548 4155893 := bbase (se 5 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 4155893 = 389615) (by norm_num)
theorem B1845757 : Blo 1457548 1845757 := bbase (se 3 (by rfl) ⟨346079, by rfl⟩ : syracuseStep 1845757 = 692159) (by norm_num)
theorem B1640965 : Blo 1457548 1640965 := bbase (se 4 (by rfl) ⟨153840, by rfl⟩ : syracuseStep 1640965 = 307681) (by norm_num)
theorem B1641001 : Blo 1457548 1641001 := bbase (se 2 (by rfl) ⟨615375, by rfl⟩ : syracuseStep 1641001 = 1230751) (by norm_num)
theorem B1641037 : Blo 1457548 1641037 := bbase (se 3 (by rfl) ⟨307694, by rfl⟩ : syracuseStep 1641037 = 615389) (by norm_num)
theorem B2460253 : Blo 1457548 2460253 := bbase (se 3 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 2460253 = 922595) (by norm_num)
theorem B3115621 : Blo 1457548 3115621 := bbase (se 4 (by rfl) ⟨292089, by rfl⟩ : syracuseStep 3115621 = 584179) (by norm_num)
theorem B1641073 : Blo 1457548 1641073 := bbase (se 2 (by rfl) ⟨615402, by rfl⟩ : syracuseStep 1641073 = 1230805) (by norm_num)
theorem B3279509 : Blo 1457548 3279509 := bbase (se 6 (by rfl) ⟨76863, by rfl⟩ : syracuseStep 3279509 = 153727) (by norm_num)
theorem B1641109 : Blo 1457548 1641109 := bbase (se 6 (by rfl) ⟨38463, by rfl⟩ : syracuseStep 1641109 = 76927) (by norm_num)
theorem B1870489 : Blo 1457548 1870489 := bbase (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) (by norm_num)
theorem B1845929 : Blo 1457548 1845929 := bbase (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) (by norm_num)
theorem B2460341 : Blo 1457548 2460341 := bbase (se 5 (by rfl) ⟨115328, by rfl⟩ : syracuseStep 2460341 = 230657) (by norm_num)
theorem B1641145 : Blo 1457548 1641145 := bbase (se 2 (by rfl) ⟨615429, by rfl⟩ : syracuseStep 1641145 = 1230859) (by norm_num)
theorem B3279581 : Blo 1457548 3279581 := bbase (se 3 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 3279581 = 1229843) (by norm_num)
theorem B1641181 : Blo 1457548 1641181 := bbase (se 3 (by rfl) ⟨307721, by rfl⟩ : syracuseStep 1641181 = 615443) (by norm_num)
theorem B3115741 : Blo 1457548 3115741 := bbase (se 3 (by rfl) ⟨584201, by rfl⟩ : syracuseStep 3115741 = 1168403) (by norm_num)
theorem B1845985 : Blo 1457548 1845985 := bbase (se 2 (by rfl) ⟨692244, by rfl⟩ : syracuseStep 1845985 = 1384489) (by norm_num)
theorem B7383797 : Blo 1457548 7383797 := bbase (se 5 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 7383797 = 692231) (by norm_num)
theorem B1641217 : Blo 1457548 1641217 := bbase (se 2 (by rfl) ⟨615456, by rfl⟩ : syracuseStep 1641217 = 1230913) (by norm_num)
theorem B5253893 : Blo 1457548 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B3279653 : Blo 1457548 3279653 := bbase (se 4 (by rfl) ⟨307467, by rfl⟩ : syracuseStep 3279653 = 614935) (by norm_num)
theorem B2075429 : Blo 1457548 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B1641253 : Blo 1457548 1641253 := bbase (se 4 (by rfl) ⟨153867, by rfl⟩ : syracuseStep 1641253 = 307735) (by norm_num)
theorem B2460469 : Blo 1457548 2460469 := bbase (se 5 (by rfl) ⟨115334, by rfl⟩ : syracuseStep 2460469 = 230669) (by norm_num)
theorem B1846081 : Blo 1457548 1846081 := bbase (se 2 (by rfl) ⟨692280, by rfl⟩ : syracuseStep 1846081 = 1384561) (by norm_num)
theorem B1641289 : Blo 1457548 1641289 := bbase (se 2 (by rfl) ⟨615483, by rfl⟩ : syracuseStep 1641289 = 1230967) (by norm_num)
theorem B3279725 : Blo 1457548 3279725 := bbase (se 3 (by rfl) ⟨614948, by rfl⟩ : syracuseStep 3279725 = 1229897) (by norm_num)
theorem B1641325 : Blo 1457548 1641325 := bbase (se 3 (by rfl) ⟨307748, by rfl⟩ : syracuseStep 1641325 = 615497) (by norm_num)
theorem B2460557 : Blo 1457548 2460557 := bbase (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) (by norm_num)
theorem B1641361 : Blo 1457548 1641361 := bbase (se 2 (by rfl) ⟨615510, by rfl⟩ : syracuseStep 1641361 = 1231021) (by norm_num)
theorem B3279797 : Blo 1457548 3279797 := bbase (se 5 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 3279797 = 307481) (by norm_num)
theorem B1641397 : Blo 1457548 1641397 := bbase (se 5 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 1641397 = 153881) (by norm_num)
theorem B1641433 : Blo 1457548 1641433 := bbase (se 2 (by rfl) ⟨615537, by rfl⟩ : syracuseStep 1641433 = 1231075) (by norm_num)
theorem B3115997 : Blo 1457548 3115997 := bbase (se 3 (by rfl) ⟨584249, by rfl⟩ : syracuseStep 3115997 = 1168499) (by norm_num)
theorem B1846253 : Blo 1457548 1846253 := bbase (se 3 (by rfl) ⟨346172, by rfl⟩ : syracuseStep 1846253 = 692345) (by norm_num)
theorem B3279869 : Blo 1457548 3279869 := bbase (se 3 (by rfl) ⟨614975, by rfl⟩ : syracuseStep 3279869 = 1229951) (by norm_num)
theorem B1641469 : Blo 1457548 1641469 := bbase (se 3 (by rfl) ⟨307775, by rfl⟩ : syracuseStep 1641469 = 615551) (by norm_num)
theorem B2460685 : Blo 1457548 2460685 := bbase (se 3 (by rfl) ⟨461378, by rfl⟩ : syracuseStep 2460685 = 922757) (by norm_num)
theorem B1641505 : Blo 1457548 1641505 := bbase (se 2 (by rfl) ⟨615564, by rfl⟩ : syracuseStep 1641505 = 1231129) (by norm_num)
theorem B3689509 : Blo 1457548 3689509 := bbase (se 4 (by rfl) ⟨345891, by rfl⟩ : syracuseStep 3689509 = 691783) (by norm_num)
theorem B1870885 : Blo 1457548 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B1846309 : Blo 1457548 1846309 := bbase (se 4 (by rfl) ⟨173091, by rfl⟩ : syracuseStep 1846309 = 346183) (by norm_num)
theorem B7007285 : Blo 1457548 7007285 := bbase (se 5 (by rfl) ⟨328466, by rfl⟩ : syracuseStep 7007285 = 656933) (by norm_num)
theorem B3279941 : Blo 1457548 3279941 := bbase (se 4 (by rfl) ⟨307494, by rfl⟩ : syracuseStep 3279941 = 614989) (by norm_num)
theorem B1641541 : Blo 1457548 1641541 := bbase (se 4 (by rfl) ⟨153894, by rfl⟩ : syracuseStep 1641541 = 307789) (by norm_num)
theorem B2337869 : Blo 1457548 2337869 := bbase (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) (by norm_num)
theorem B2460773 : Blo 1457548 2460773 := bbase (se 4 (by rfl) ⟨230697, by rfl⟩ : syracuseStep 2460773 = 461395) (by norm_num)
theorem B1641577 : Blo 1457548 1641577 := bbase (se 2 (by rfl) ⟨615591, by rfl⟩ : syracuseStep 1641577 = 1231183) (by norm_num)
theorem B1846405 : Blo 1457548 1846405 := bbase (se 4 (by rfl) ⟨173100, by rfl⟩ : syracuseStep 1846405 = 346201) (by norm_num)
theorem B3280013 : Blo 1457548 3280013 := bbase (se 3 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 3280013 = 1230005) (by norm_num)
theorem B1641613 : Blo 1457548 1641613 := bbase (se 3 (by rfl) ⟨307802, by rfl⟩ : syracuseStep 1641613 = 615605) (by norm_num)
theorem B3689621 : Blo 1457548 3689621 := bbase (se 6 (by rfl) ⟨86475, by rfl⟩ : syracuseStep 3689621 = 172951) (by norm_num)
theorem B7007381 : Blo 1457548 7007381 := bbase (se 6 (by rfl) ⟨164235, by rfl⟩ : syracuseStep 7007381 = 328471) (by norm_num)
theorem B1641649 : Blo 1457548 1641649 := bbase (se 2 (by rfl) ⟨615618, by rfl⟩ : syracuseStep 1641649 = 1231237) (by norm_num)
theorem B3280085 : Blo 1457548 3280085 := bbase (se 7 (by rfl) ⟨38438, by rfl⟩ : syracuseStep 3280085 = 76877) (by norm_num)
theorem B1641685 : Blo 1457548 1641685 := bbase (se 7 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 1641685 = 38477) (by norm_num)
theorem B2460901 : Blo 1457548 2460901 := bbase (se 4 (by rfl) ⟨230709, by rfl⟩ : syracuseStep 2460901 = 461419) (by norm_num)
theorem B1641721 : Blo 1457548 1641721 := bbase (se 2 (by rfl) ⟨615645, by rfl⟩ : syracuseStep 1641721 = 1231291) (by norm_num)
theorem B1871105 : Blo 1457548 1871105 := bbase (se 2 (by rfl) ⟨701664, by rfl⟩ : syracuseStep 1871105 = 1403329) (by norm_num)
theorem B3280157 : Blo 1457548 3280157 := bbase (se 3 (by rfl) ⟨615029, by rfl⟩ : syracuseStep 3280157 = 1230059) (by norm_num)
theorem B2493725 : Blo 1457548 2493725 := bbase (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) (by norm_num)
theorem B1641757 : Blo 1457548 1641757 := bbase (se 3 (by rfl) ⟨307829, by rfl⟩ : syracuseStep 1641757 = 615659) (by norm_num)
theorem B1846577 : Blo 1457548 1846577 := bbase (se 2 (by rfl) ⟨692466, by rfl⟩ : syracuseStep 1846577 = 1384933) (by norm_num)
theorem B3599677 : Blo 1457548 3599677 := bbase (se 3 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 3599677 = 1349879) (by norm_num)
theorem B2460989 : Blo 1457548 2460989 := bbase (se 3 (by rfl) ⟨461435, by rfl⟩ : syracuseStep 2460989 = 922871) (by norm_num)
theorem B1641793 : Blo 1457548 1641793 := bbase (se 2 (by rfl) ⟨615672, by rfl⟩ : syracuseStep 1641793 = 1231345) (by norm_num)
theorem B3689813 : Blo 1457548 3689813 := bbase (se 11 (by rfl) ⟨2702, by rfl⟩ : syracuseStep 3689813 = 5405) (by norm_num)
theorem B3280229 : Blo 1457548 3280229 := bbase (se 4 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 3280229 = 615043) (by norm_num)
theorem B1641829 : Blo 1457548 1641829 := bbase (se 4 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 1641829 = 307843) (by norm_num)
theorem B1846633 : Blo 1457548 1846633 := bbase (se 2 (by rfl) ⟨692487, by rfl⟩ : syracuseStep 1846633 = 1384975) (by norm_num)
theorem B1641865 : Blo 1457548 1641865 := bbase (se 2 (by rfl) ⟨615699, by rfl⟩ : syracuseStep 1641865 = 1231399) (by norm_num)
theorem B3280301 : Blo 1457548 3280301 := bbase (se 3 (by rfl) ⟨615056, by rfl⟩ : syracuseStep 3280301 = 1230113) (by norm_num)
theorem B1641901 : Blo 1457548 1641901 := bbase (se 3 (by rfl) ⟨307856, by rfl⟩ : syracuseStep 1641901 = 615713) (by norm_num)
theorem B2461117 : Blo 1457548 2461117 := bbase (se 3 (by rfl) ⟨461459, by rfl⟩ : syracuseStep 2461117 = 922919) (by norm_num)
theorem B1846729 : Blo 1457548 1846729 := bbase (se 2 (by rfl) ⟨692523, by rfl⟩ : syracuseStep 1846729 = 1385047) (by norm_num)
theorem B1641937 : Blo 1457548 1641937 := bbase (se 2 (by rfl) ⟨615726, by rfl⟩ : syracuseStep 1641937 = 1231453) (by norm_num)
theorem B8424917 : Blo 1457548 8424917 := bbase (se 7 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 8424917 = 197459) (by norm_num)
theorem B4672997 : Blo 1457548 4672997 := bbase (se 4 (by rfl) ⟨438093, by rfl⟩ : syracuseStep 4672997 = 876187) (by norm_num)
theorem B3280373 : Blo 1457548 3280373 := bbase (se 5 (by rfl) ⟨153767, by rfl⟩ : syracuseStep 3280373 = 307535) (by norm_num)
theorem B1641973 : Blo 1457548 1641973 := bbase (se 5 (by rfl) ⟨76967, by rfl⟩ : syracuseStep 1641973 = 153935) (by norm_num)
theorem B2461205 : Blo 1457548 2461205 := bbase (se 6 (by rfl) ⟨57684, by rfl⟩ : syracuseStep 2461205 = 115369) (by norm_num)
theorem B9473557 : Blo 1457548 9473557 := bbase (se 6 (by rfl) ⟨222036, by rfl⟩ : syracuseStep 9473557 = 444073) (by norm_num)
theorem B7884341 : Blo 1457548 7884341 := bbase (se 5 (by rfl) ⟨369578, by rfl⟩ : syracuseStep 7884341 = 739157) (by norm_num)
theorem B3280445 : Blo 1457548 3280445 := bbase (se 3 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 3280445 = 1230167) (by norm_num)
theorem B1478233 : Blo 1457548 1478233 := bbase (se 2 (by rfl) ⟨554337, by rfl⟩ : syracuseStep 1478233 = 1108675) (by norm_num)
theorem B1846901 : Blo 1457548 1846901 := bbase (se 5 (by rfl) ⟨86573, by rfl⟩ : syracuseStep 1846901 = 173147) (by norm_num)
theorem B5541493 : Blo 1457548 5541493 := bbase (se 5 (by rfl) ⟨259757, by rfl⟩ : syracuseStep 5541493 = 519515) (by norm_num)
theorem B3280517 : Blo 1457548 3280517 := bbase (se 4 (by rfl) ⟨307548, by rfl⟩ : syracuseStep 3280517 = 615097) (by norm_num)
theorem B2461333 : Blo 1457548 2461333 := bbase (se 6 (by rfl) ⟨57687, by rfl⟩ : syracuseStep 2461333 = 115375) (by norm_num)
theorem B3690157 : Blo 1457548 3690157 := bbase (se 3 (by rfl) ⟨691904, by rfl⟩ : syracuseStep 3690157 = 1383809) (by norm_num)
theorem B1846957 : Blo 1457548 1846957 := bbase (se 3 (by rfl) ⟨346304, by rfl⟩ : syracuseStep 1846957 = 692609) (by norm_num)
theorem B3280589 : Blo 1457548 3280589 := bbase (se 3 (by rfl) ⟨615110, by rfl⟩ : syracuseStep 3280589 = 1230221) (by norm_num)
theorem B2461421 : Blo 1457548 2461421 := bbase (se 3 (by rfl) ⟨461516, by rfl⟩ : syracuseStep 2461421 = 923033) (by norm_num)
theorem B5254901 : Blo 1457548 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B1847053 : Blo 1457548 1847053 := bbase (se 3 (by rfl) ⟨346322, by rfl⟩ : syracuseStep 1847053 = 692645) (by norm_num)
theorem B3280661 : Blo 1457548 3280661 := bbase (se 6 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 3280661 = 153781) (by norm_num)
theorem B3690269 : Blo 1457548 3690269 := bbase (se 3 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 3690269 = 1383851) (by norm_num)
theorem B3116885 : Blo 1457548 3116885 := bbase (se 9 (by rfl) ⟨9131, by rfl⟩ : syracuseStep 3116885 = 18263) (by norm_num)
theorem B3280733 : Blo 1457548 3280733 := bbase (se 3 (by rfl) ⟨615137, by rfl⟩ : syracuseStep 3280733 = 1230275) (by norm_num)
theorem B2461549 : Blo 1457548 2461549 := bbase (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) (by norm_num)
theorem B3280805 : Blo 1457548 3280805 := bbase (se 4 (by rfl) ⟨307575, by rfl⟩ : syracuseStep 3280805 = 615151) (by norm_num)
theorem B1847225 : Blo 1457548 1847225 := bbase (se 2 (by rfl) ⟨692709, by rfl⟩ : syracuseStep 1847225 = 1385419) (by norm_num)
theorem B4919237 : Blo 1457548 4919237 := bbase (se 4 (by rfl) ⟨461178, by rfl⟩ : syracuseStep 4919237 = 922357) (by norm_num)
theorem B2461637 : Blo 1457548 2461637 := bbase (se 4 (by rfl) ⟨230778, by rfl⟩ : syracuseStep 2461637 = 461557) (by norm_num)
theorem B4992965 : Blo 1457548 4992965 := bbase (se 4 (by rfl) ⟨468090, by rfl⟩ : syracuseStep 4992965 = 936181) (by norm_num)
theorem B1871833 : Blo 1457548 1871833 := bbase (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) (by norm_num)
theorem B3690461 : Blo 1457548 3690461 := bbase (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) (by norm_num)
theorem B3280877 : Blo 1457548 3280877 := bbase (se 3 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 3280877 = 1230329) (by norm_num)
theorem B7385093 : Blo 1457548 7385093 := bbase (se 4 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 7385093 = 1384705) (by norm_num)
theorem B3280949 : Blo 1457548 3280949 := bbase (se 5 (by rfl) ⟨153794, by rfl⟩ : syracuseStep 3280949 = 307589) (by norm_num)
theorem B2461765 : Blo 1457548 2461765 := bbase (se 4 (by rfl) ⟨230790, by rfl⟩ : syracuseStep 2461765 = 461581) (by norm_num)
theorem B3117125 : Blo 1457548 3117125 := bbase (se 4 (by rfl) ⟨292230, by rfl⟩ : syracuseStep 3117125 = 584461) (by norm_num)
theorem B1970285 : Blo 1457548 1970285 := bbase (se 3 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 1970285 = 738857) (by norm_num)
theorem B3281021 : Blo 1457548 3281021 := bbase (se 3 (by rfl) ⟨615191, by rfl⟩ : syracuseStep 3281021 = 1230383) (by norm_num)
theorem B3158165 : Blo 1457548 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B2461853 : Blo 1457548 2461853 := bbase (se 3 (by rfl) ⟨461597, by rfl⟩ : syracuseStep 2461853 = 923195) (by norm_num)
theorem B2076853 : Blo 1457548 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B1478849 : Blo 1457548 1478849 := bbase (se 2 (by rfl) ⟨554568, by rfl⟩ : syracuseStep 1478849 = 1109137) (by norm_num)
theorem B3281093 : Blo 1457548 3281093 := bbase (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) (by norm_num)
theorem B3281165 : Blo 1457548 3281165 := bbase (se 3 (by rfl) ⟨615218, by rfl⟩ : syracuseStep 3281165 = 1230437) (by norm_num)
theorem B2461981 : Blo 1457548 2461981 := bbase (se 3 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 2461981 = 923243) (by norm_num)
theorem B3690805 : Blo 1457548 3690805 := bbase (se 5 (by rfl) ⟨173006, by rfl⟩ : syracuseStep 3690805 = 346013) (by norm_num)
theorem B3281237 : Blo 1457548 3281237 := bbase (se 10 (by rfl) ⟨4806, by rfl⟩ : syracuseStep 3281237 = 9613) (by norm_num)
theorem B4919669 : Blo 1457548 4919669 := bbase (se 5 (by rfl) ⟨230609, by rfl⟩ : syracuseStep 4919669 = 461219) (by norm_num)
theorem B2462069 : Blo 1457548 2462069 := bbase (se 5 (by rfl) ⟨115409, by rfl⟩ : syracuseStep 2462069 = 230819) (by norm_num)
theorem B3281309 : Blo 1457548 3281309 := bbase (se 3 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 3281309 = 1230491) (by norm_num)
theorem B3690917 : Blo 1457548 3690917 := bbase (se 4 (by rfl) ⟨346023, by rfl⟩ : syracuseStep 3690917 = 692047) (by norm_num)
theorem B3281381 : Blo 1457548 3281381 := bbase (se 4 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 3281381 = 615259) (by norm_num)
theorem B2494957 : Blo 1457548 2494957 := bbase (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) (by norm_num)
theorem B2462197 : Blo 1457548 2462197 := bbase (se 5 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 2462197 = 230831) (by norm_num)
theorem B3944981 : Blo 1457548 3944981 := bbase (se 6 (by rfl) ⟨92460, by rfl⟩ : syracuseStep 3944981 = 184921) (by norm_num)
theorem B3281453 : Blo 1457548 3281453 := bbase (se 3 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 3281453 = 1230545) (by norm_num)
theorem B2462285 : Blo 1457548 2462285 := bbase (se 3 (by rfl) ⟨461678, by rfl⟩ : syracuseStep 2462285 = 923357) (by norm_num)
theorem B3691109 : Blo 1457548 3691109 := bbase (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) (by norm_num)
theorem B3281525 : Blo 1457548 3281525 := bbase (se 5 (by rfl) ⟨153821, by rfl⟩ : syracuseStep 3281525 = 307643) (by norm_num)
theorem B3281597 : Blo 1457548 3281597 := bbase (se 3 (by rfl) ⟨615299, by rfl⟩ : syracuseStep 3281597 = 1230599) (by norm_num)
theorem B2462413 : Blo 1457548 2462413 := bbase (se 3 (by rfl) ⟨461702, by rfl⟩ : syracuseStep 2462413 = 923405) (by norm_num)
theorem B3740381 : Blo 1457548 3740381 := bbase (se 3 (by rfl) ⟨701321, by rfl⟩ : syracuseStep 3740381 = 1402643) (by norm_num)
theorem B2216693 : Blo 1457548 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B3281669 : Blo 1457548 3281669 := bbase (se 4 (by rfl) ⟨307656, by rfl⟩ : syracuseStep 3281669 = 615313) (by norm_num)
theorem B2077445 : Blo 1457548 2077445 := bbase (se 4 (by rfl) ⟨194760, by rfl⟩ : syracuseStep 2077445 = 389521) (by norm_num)
theorem B4920101 : Blo 1457548 4920101 := bbase (se 4 (by rfl) ⟨461259, by rfl⟩ : syracuseStep 4920101 = 922519) (by norm_num)
theorem B2462501 : Blo 1457548 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B3281741 : Blo 1457548 3281741 := bbase (se 3 (by rfl) ⟨615326, by rfl⟩ : syracuseStep 3281741 = 1230653) (by norm_num)
theorem B2077525 : Blo 1457548 2077525 := bbase (se 9 (by rfl) ⟨6086, by rfl⟩ : syracuseStep 2077525 = 12173) (by norm_num)
theorem B3281813 : Blo 1457548 3281813 := bbase (se 6 (by rfl) ⟨76917, by rfl⟩ : syracuseStep 3281813 = 153835) (by norm_num)
theorem B14021525 : Blo 1457548 14021525 := bbase (se 6 (by rfl) ⟨328629, by rfl⟩ : syracuseStep 14021525 = 657259) (by norm_num)
theorem B2462629 : Blo 1457548 2462629 := bbase (se 4 (by rfl) ⟨230871, by rfl⟩ : syracuseStep 2462629 = 461743) (by norm_num)
theorem B3691453 : Blo 1457548 3691453 := bbase (se 3 (by rfl) ⟨692147, by rfl⟩ : syracuseStep 3691453 = 1384295) (by norm_num)
theorem B2077645 : Blo 1457548 2077645 := bbase (se 3 (by rfl) ⟨389558, by rfl⟩ : syracuseStep 2077645 = 779117) (by norm_num)
theorem B3281885 : Blo 1457548 3281885 := bbase (se 3 (by rfl) ⟨615353, by rfl⟩ : syracuseStep 3281885 = 1230707) (by norm_num)
theorem B2462717 : Blo 1457548 2462717 := bbase (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) (by norm_num)
theorem B7009301 : Blo 1457548 7009301 := bbase (se 6 (by rfl) ⟨164280, by rfl⟩ : syracuseStep 7009301 = 328561) (by norm_num)
theorem B3281957 : Blo 1457548 3281957 := bbase (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) (by norm_num)
theorem B3691565 : Blo 1457548 3691565 := bbase (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) (by norm_num)
theorem B2077741 : Blo 1457548 2077741 := bbase (se 3 (by rfl) ⟨389576, by rfl⟩ : syracuseStep 2077741 = 779153) (by norm_num)
theorem B10515541 : Blo 1457548 10515541 := bbase (se 8 (by rfl) ⟨61614, by rfl⟩ : syracuseStep 10515541 = 123229) (by norm_num)
theorem B3282029 : Blo 1457548 3282029 := bbase (se 3 (by rfl) ⟨615380, by rfl⟩ : syracuseStep 3282029 = 1230761) (by norm_num)
theorem B2462845 : Blo 1457548 2462845 := bbase (se 3 (by rfl) ⟨461783, by rfl⟩ : syracuseStep 2462845 = 923567) (by norm_num)
theorem B3282101 : Blo 1457548 3282101 := bbase (se 5 (by rfl) ⟨153848, by rfl⟩ : syracuseStep 3282101 = 307697) (by norm_num)
theorem B4920533 : Blo 1457548 4920533 := bbase (se 7 (by rfl) ⟨57662, by rfl⟩ : syracuseStep 4920533 = 115325) (by norm_num)
theorem B2462933 : Blo 1457548 2462933 := bbase (se 7 (by rfl) ⟨28862, by rfl⟩ : syracuseStep 2462933 = 57725) (by norm_num)
theorem B3691757 : Blo 1457548 3691757 := bbase (se 3 (by rfl) ⟨692204, by rfl⟩ : syracuseStep 3691757 = 1384409) (by norm_num)
theorem B3282173 : Blo 1457548 3282173 := bbase (se 3 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 3282173 = 1230815) (by norm_num)
theorem B7386389 : Blo 1457548 7386389 := bbase (se 6 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 7386389 = 346237) (by norm_num)
theorem B3282245 : Blo 1457548 3282245 := bbase (se 4 (by rfl) ⟨307710, by rfl⟩ : syracuseStep 3282245 = 615421) (by norm_num)
theorem B3282317 : Blo 1457548 3282317 := bbase (se 3 (by rfl) ⟨615434, by rfl⟩ : syracuseStep 3282317 = 1230869) (by norm_num)
theorem B3282389 : Blo 1457548 3282389 := bbase (se 7 (by rfl) ⟨38465, by rfl⟩ : syracuseStep 3282389 = 76931) (by norm_num)
theorem B3282461 : Blo 1457548 3282461 := bbase (se 3 (by rfl) ⟨615461, by rfl⟩ : syracuseStep 3282461 = 1230923) (by norm_num)
theorem B3692101 : Blo 1457548 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B6231653 : Blo 1457548 6231653 := bbase (se 4 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 6231653 = 1168435) (by norm_num)
theorem B3282533 : Blo 1457548 3282533 := bbase (se 4 (by rfl) ⟨307737, by rfl⟩ : syracuseStep 3282533 = 615475) (by norm_num)
theorem B4920965 : Blo 1457548 4920965 := bbase (se 4 (by rfl) ⟨461340, by rfl⟩ : syracuseStep 4920965 = 922681) (by norm_num)
theorem B3503749 : Blo 1457548 3503749 := bbase (se 4 (by rfl) ⟨328476, by rfl⟩ : syracuseStep 3503749 = 656953) (by norm_num)
theorem B2954909 : Blo 1457548 2954909 := bbase (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) (by norm_num)
theorem B3282605 : Blo 1457548 3282605 := bbase (se 3 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 3282605 = 1230977) (by norm_num)
theorem B3692213 : Blo 1457548 3692213 := bbase (se 5 (by rfl) ⟨173072, by rfl⟩ : syracuseStep 3692213 = 346145) (by norm_num)
theorem B1578737 : Blo 1457548 1578737 := bbase (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) (by norm_num)
theorem B3282677 : Blo 1457548 3282677 := bbase (se 5 (by rfl) ⟨153875, by rfl⟩ : syracuseStep 3282677 = 307751) (by norm_num)
theorem B2807557 : Blo 1457548 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B3282749 : Blo 1457548 3282749 := bbase (se 3 (by rfl) ⟨615515, by rfl⟩ : syracuseStep 3282749 = 1231031) (by norm_num)
theorem B3692405 : Blo 1457548 3692405 := bbase (se 5 (by rfl) ⟨173081, by rfl⟩ : syracuseStep 3692405 = 346163) (by norm_num)
theorem B3282821 : Blo 1457548 3282821 := bbase (se 4 (by rfl) ⟨307764, by rfl⟩ : syracuseStep 3282821 = 615529) (by norm_num)
theorem B4151189 : Blo 1457548 4151189 := bbase (se 6 (by rfl) ⟨97293, by rfl⟩ : syracuseStep 4151189 = 194587) (by norm_num)
theorem B3741605 : Blo 1457548 3741605 := bbase (se 4 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 3741605 = 701551) (by norm_num)
theorem B3282893 : Blo 1457548 3282893 := bbase (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) (by norm_num)
theorem B5691365 : Blo 1457548 5691365 := bbase (se 4 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 5691365 = 1067131) (by norm_num)
theorem B1751053 : Blo 1457548 1751053 := bbase (se 3 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 1751053 = 656645) (by norm_num)
theorem B3282965 : Blo 1457548 3282965 := bbase (se 6 (by rfl) ⟨76944, by rfl⟩ : syracuseStep 3282965 = 153889) (by norm_num)
theorem B4921397 : Blo 1457548 4921397 := bbase (se 5 (by rfl) ⟨230690, by rfl⟩ : syracuseStep 4921397 = 461381) (by norm_num)
theorem B2627653 : Blo 1457548 2627653 := bbase (se 4 (by rfl) ⟨246342, by rfl⟩ : syracuseStep 2627653 = 492685) (by norm_num)
theorem B3283037 : Blo 1457548 3283037 := bbase (se 3 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 3283037 = 1231139) (by norm_num)
theorem B1751153 : Blo 1457548 1751153 := bbase (se 2 (by rfl) ⟨656682, by rfl⟩ : syracuseStep 1751153 = 1313365) (by norm_num)
theorem B5257381 : Blo 1457548 5257381 := bbase (se 4 (by rfl) ⟨492879, by rfl⟩ : syracuseStep 5257381 = 985759) (by norm_num)
theorem B3283109 : Blo 1457548 3283109 := bbase (se 4 (by rfl) ⟨307791, by rfl⟩ : syracuseStep 3283109 = 615583) (by norm_num)
theorem B4675765 : Blo 1457548 4675765 := bbase (se 5 (by rfl) ⟨219176, by rfl⟩ : syracuseStep 4675765 = 438353) (by norm_num)
theorem B3692749 : Blo 1457548 3692749 := bbase (se 3 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 3692749 = 1384781) (by norm_num)
theorem B2627797 : Blo 1457548 2627797 := bbase (se 7 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 2627797 = 61589) (by norm_num)
theorem B3283181 : Blo 1457548 3283181 := bbase (se 3 (by rfl) ⟨615596, by rfl⟩ : syracuseStep 3283181 = 1231193) (by norm_num)
theorem B2767117 : Blo 1457548 2767117 := bbase (se 3 (by rfl) ⟨518834, by rfl⟩ : syracuseStep 2767117 = 1037669) (by norm_num)
theorem B1775893 : Blo 1457548 1775893 := bbase (se 6 (by rfl) ⟨41622, by rfl⟩ : syracuseStep 1775893 = 83245) (by norm_num)
theorem B21035285 : Blo 1457548 21035285 := bbase (se 6 (by rfl) ⟨493014, by rfl⟩ : syracuseStep 21035285 = 986029) (by norm_num)
theorem B2627869 : Blo 1457548 2627869 := bbase (se 3 (by rfl) ⟨492725, by rfl⟩ : syracuseStep 2627869 = 985451) (by norm_num)
theorem B6650149 : Blo 1457548 6650149 := bbase (se 4 (by rfl) ⟨623451, by rfl⟩ : syracuseStep 6650149 = 1246903) (by norm_num)
theorem B3283253 : Blo 1457548 3283253 := bbase (se 5 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 3283253 = 307805) (by norm_num)
theorem B3692861 : Blo 1457548 3692861 := bbase (se 3 (by rfl) ⟨692411, by rfl⟩ : syracuseStep 3692861 = 1384823) (by norm_num)
theorem B5257541 : Blo 1457548 5257541 := bbase (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) (by norm_num)
theorem B3283325 : Blo 1457548 3283325 := bbase (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) (by norm_num)
theorem B5536133 : Blo 1457548 5536133 := bbase (se 4 (by rfl) ⟨519012, by rfl⟩ : syracuseStep 5536133 = 1038025) (by norm_num)
theorem B7010725 : Blo 1457548 7010725 := bbase (se 4 (by rfl) ⟨657255, by rfl⟩ : syracuseStep 7010725 = 1314511) (by norm_num)
theorem B2767277 : Blo 1457548 2767277 := bbase (se 3 (by rfl) ⟨518864, by rfl⟩ : syracuseStep 2767277 = 1037729) (by norm_num)
theorem B3283397 : Blo 1457548 3283397 := bbase (se 4 (by rfl) ⟨307818, by rfl⟩ : syracuseStep 3283397 = 615637) (by norm_num)
theorem B4921829 : Blo 1457548 4921829 := bbase (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) (by norm_num)
theorem B3693053 : Blo 1457548 3693053 := bbase (se 3 (by rfl) ⟨692447, by rfl⟩ : syracuseStep 3693053 = 1384895) (by norm_num)
theorem B1751557 : Blo 1457548 1751557 := bbase (se 4 (by rfl) ⟨164208, by rfl⟩ : syracuseStep 1751557 = 328417) (by norm_num)
theorem B3283469 : Blo 1457548 3283469 := bbase (se 3 (by rfl) ⟨615650, by rfl⟩ : syracuseStep 3283469 = 1231301) (by norm_num)
theorem B7387685 : Blo 1457548 7387685 := bbase (se 4 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 7387685 = 1385191) (by norm_num)
theorem B4151861 : Blo 1457548 4151861 := bbase (se 5 (by rfl) ⟨194618, by rfl⟩ : syracuseStep 4151861 = 389237) (by norm_num)
theorem B2767421 : Blo 1457548 2767421 := bbase (se 3 (by rfl) ⟨518891, by rfl⟩ : syracuseStep 2767421 = 1037783) (by norm_num)
theorem B3283541 : Blo 1457548 3283541 := bbase (se 8 (by rfl) ⟨19239, by rfl⟩ : syracuseStep 3283541 = 38479) (by norm_num)
theorem B2808445 : Blo 1457548 2808445 := bbase (se 3 (by rfl) ⟨526583, by rfl⟩ : syracuseStep 2808445 = 1053167) (by norm_num)
theorem B3324557 : Blo 1457548 3324557 := bbase (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) (by norm_num)
theorem B3324565 : Blo 1457548 3324565 := bbase (se 6 (by rfl) ⟨77919, by rfl⟩ : syracuseStep 3324565 = 155839) (by norm_num)
theorem B24918677 : Blo 1457548 24918677 := bbase (se 6 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 24918677 = 1168063) (by norm_num)
theorem B3283613 : Blo 1457548 3283613 := bbase (se 3 (by rfl) ⟨615677, by rfl⟩ : syracuseStep 3283613 = 1231355) (by norm_num)
theorem B5536421 : Blo 1457548 5536421 := bbase (se 4 (by rfl) ⟨519039, by rfl⟩ : syracuseStep 5536421 = 1038079) (by norm_num)
theorem B3283685 : Blo 1457548 3283685 := bbase (se 4 (by rfl) ⟨307845, by rfl⟩ : syracuseStep 3283685 = 615691) (by norm_num)
theorem B3283757 : Blo 1457548 3283757 := bbase (se 3 (by rfl) ⟨615704, by rfl⟩ : syracuseStep 3283757 = 1231409) (by norm_num)
theorem B11377493 : Blo 1457548 11377493 := bbase (se 9 (by rfl) ⟨33332, by rfl⟩ : syracuseStep 11377493 = 66665) (by norm_num)
theorem B3693397 : Blo 1457548 3693397 := bbase (se 9 (by rfl) ⟨10820, by rfl⟩ : syracuseStep 3693397 = 21641) (by norm_num)
theorem B2767709 : Blo 1457548 2767709 := bbase (se 3 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 2767709 = 1037891) (by norm_num)
theorem B3283829 : Blo 1457548 3283829 := bbase (se 5 (by rfl) ⟨153929, by rfl⟩ : syracuseStep 3283829 = 307859) (by norm_num)
theorem B1751941 : Blo 1457548 1751941 := bbase (se 4 (by rfl) ⟨164244, by rfl⟩ : syracuseStep 1751941 = 328489) (by norm_num)
theorem B4922261 : Blo 1457548 4922261 := bbase (se 6 (by rfl) ⟨115365, by rfl⟩ : syracuseStep 4922261 = 230731) (by norm_num)
theorem B9345941 : Blo 1457548 9345941 := bbase (se 6 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 9345941 = 438091) (by norm_num)
theorem B3283901 : Blo 1457548 3283901 := bbase (se 3 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 3283901 = 1231463) (by norm_num)
theorem B7379909 : Blo 1457548 7379909 := bbase (se 4 (by rfl) ⟨691866, by rfl⟩ : syracuseStep 7379909 = 1383733) (by norm_num)
theorem B3693509 : Blo 1457548 3693509 := bbase (se 4 (by rfl) ⟨346266, by rfl⟩ : syracuseStep 3693509 = 692533) (by norm_num)
theorem B23657429 : Blo 1457548 23657429 := bbase (se 7 (by rfl) ⟨277235, by rfl⟩ : syracuseStep 23657429 = 554471) (by norm_num)
theorem B4152293 : Blo 1457548 4152293 := bbase (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) (by norm_num)
theorem B2767861 : Blo 1457548 2767861 := bbase (se 5 (by rfl) ⟨129743, by rfl⟩ : syracuseStep 2767861 = 259487) (by norm_num)
theorem B3283973 : Blo 1457548 3283973 := bbase (se 4 (by rfl) ⟨307872, by rfl⟩ : syracuseStep 3283973 = 615745) (by norm_num)
theorem B22461461 : Blo 1457548 22461461 := bbase (se 6 (by rfl) ⟨526440, by rfl⟩ : syracuseStep 22461461 = 1052881) (by norm_num)
theorem B3505189 : Blo 1457548 3505189 := bbase (se 4 (by rfl) ⟨328611, by rfl⟩ : syracuseStep 3505189 = 657223) (by norm_num)
theorem B2186333 : Blo 1457548 2186333 := bbase (se 3 (by rfl) ⟨409937, by rfl⟩ : syracuseStep 2186333 = 819875) (by norm_num)
theorem B2186357 : Blo 1457548 2186357 := bbase (se 5 (by rfl) ⟨102485, by rfl⟩ : syracuseStep 2186357 = 204971) (by norm_num)
theorem B3693701 : Blo 1457548 3693701 := bbase (se 4 (by rfl) ⟨346284, by rfl⟩ : syracuseStep 3693701 = 692569) (by norm_num)
theorem B2186381 : Blo 1457548 2186381 := bbase (se 3 (by rfl) ⟨409946, by rfl⟩ : syracuseStep 2186381 = 819893) (by norm_num)
theorem B2186405 : Blo 1457548 2186405 := bbase (se 4 (by rfl) ⟨204975, by rfl⟩ : syracuseStep 2186405 = 409951) (by norm_num)
theorem B2186429 : Blo 1457548 2186429 := bbase (se 3 (by rfl) ⟨409955, by rfl⟩ : syracuseStep 2186429 = 819911) (by norm_num)
theorem B2186453 : Blo 1457548 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B2186477 : Blo 1457548 2186477 := bbase (se 3 (by rfl) ⟨409964, by rfl⟩ : syracuseStep 2186477 = 819929) (by norm_num)
theorem B2186501 : Blo 1457548 2186501 := bbase (se 4 (by rfl) ⟨204984, by rfl⟩ : syracuseStep 2186501 = 409969) (by norm_num)
theorem B4799765 : Blo 1457548 4799765 := bbase (se 6 (by rfl) ⟨112494, by rfl⟩ : syracuseStep 4799765 = 224989) (by norm_num)
theorem B2186525 : Blo 1457548 2186525 := bbase (se 3 (by rfl) ⟨409973, by rfl⟩ : syracuseStep 2186525 = 819947) (by norm_num)
theorem B2768165 : Blo 1457548 2768165 := bbase (se 4 (by rfl) ⟨259515, by rfl⟩ : syracuseStep 2768165 = 519031) (by norm_num)
theorem B2186549 : Blo 1457548 2186549 := bbase (se 5 (by rfl) ⟨102494, by rfl⟩ : syracuseStep 2186549 = 204989) (by norm_num)
theorem B4922693 : Blo 1457548 4922693 := bbase (se 4 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 4922693 = 923005) (by norm_num)
theorem B2186573 : Blo 1457548 2186573 := bbase (se 3 (by rfl) ⟨409982, by rfl⟩ : syracuseStep 2186573 = 819965) (by norm_num)
theorem B6233429 : Blo 1457548 6233429 := bbase (se 11 (by rfl) ⟨4565, by rfl⟩ : syracuseStep 6233429 = 9131) (by norm_num)
theorem B2186597 : Blo 1457548 2186597 := bbase (se 4 (by rfl) ⟨204993, by rfl⟩ : syracuseStep 2186597 = 409987) (by norm_num)
theorem B2186621 : Blo 1457548 2186621 := bbase (se 3 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 2186621 = 819983) (by norm_num)
theorem B2186645 : Blo 1457548 2186645 := bbase (se 6 (by rfl) ⟨51249, by rfl⟩ : syracuseStep 2186645 = 102499) (by norm_num)
theorem B2186669 : Blo 1457548 2186669 := bbase (se 3 (by rfl) ⟨410000, by rfl⟩ : syracuseStep 2186669 = 820001) (by norm_num)
theorem B1686977 : Blo 1457548 1686977 := bbase (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) (by norm_num)
theorem B2186693 : Blo 1457548 2186693 := bbase (se 4 (by rfl) ⟨205002, by rfl⟩ : syracuseStep 2186693 = 410005) (by norm_num)
theorem B2186717 : Blo 1457548 2186717 := bbase (se 3 (by rfl) ⟨410009, by rfl⟩ : syracuseStep 2186717 = 820019) (by norm_num)
theorem B3694045 : Blo 1457548 3694045 := bbase (se 3 (by rfl) ⟨692633, by rfl⟩ : syracuseStep 3694045 = 1385267) (by norm_num)
theorem B2186741 : Blo 1457548 2186741 := bbase (se 5 (by rfl) ⟨102503, by rfl⟩ : syracuseStep 2186741 = 205007) (by norm_num)
theorem B2186765 : Blo 1457548 2186765 := bbase (se 3 (by rfl) ⟨410018, by rfl⟩ : syracuseStep 2186765 = 820037) (by norm_num)
theorem B3792413 : Blo 1457548 3792413 := bbase (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) (by norm_num)
theorem B2186789 : Blo 1457548 2186789 := bbase (se 4 (by rfl) ⟨205011, by rfl⟩ : syracuseStep 2186789 = 410023) (by norm_num)
theorem B2186813 : Blo 1457548 2186813 := bbase (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) (by norm_num)
theorem B2629181 : Blo 1457548 2629181 := bbase (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) (by norm_num)
theorem B6233669 : Blo 1457548 6233669 := bbase (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) (by norm_num)
theorem B3694157 : Blo 1457548 3694157 := bbase (se 3 (by rfl) ⟨692654, by rfl⟩ : syracuseStep 3694157 = 1385309) (by norm_num)
theorem B2186837 : Blo 1457548 2186837 := bbase (se 8 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 2186837 = 25627) (by norm_num)
theorem B2186861 : Blo 1457548 2186861 := bbase (se 3 (by rfl) ⟨410036, by rfl⟩ : syracuseStep 2186861 = 820073) (by norm_num)
theorem B2186885 : Blo 1457548 2186885 := bbase (se 4 (by rfl) ⟨205020, by rfl⟩ : syracuseStep 2186885 = 410041) (by norm_num)
theorem B3505805 : Blo 1457548 3505805 := bbase (se 3 (by rfl) ⟨657338, by rfl⟩ : syracuseStep 3505805 = 1314677) (by norm_num)
theorem B2186909 : Blo 1457548 2186909 := bbase (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) (by norm_num)
theorem B2186933 : Blo 1457548 2186933 := bbase (se 5 (by rfl) ⟨102512, by rfl⟩ : syracuseStep 2186933 = 205025) (by norm_num)
theorem B2186957 : Blo 1457548 2186957 := bbase (se 3 (by rfl) ⟨410054, by rfl⟩ : syracuseStep 2186957 = 820109) (by norm_num)
theorem B4153045 : Blo 1457548 4153045 := bbase (se 7 (by rfl) ⟨48668, by rfl⟩ : syracuseStep 4153045 = 97337) (by norm_num)
theorem B1752797 : Blo 1457548 1752797 := bbase (se 3 (by rfl) ⟨328649, by rfl⟩ : syracuseStep 1752797 = 657299) (by norm_num)
theorem B2186981 : Blo 1457548 2186981 := bbase (se 4 (by rfl) ⟨205029, by rfl⟩ : syracuseStep 2186981 = 410059) (by norm_num)
theorem B4923125 : Blo 1457548 4923125 := bbase (se 5 (by rfl) ⟨230771, by rfl⟩ : syracuseStep 4923125 = 461543) (by norm_num)
theorem B2187005 : Blo 1457548 2187005 := bbase (se 3 (by rfl) ⟨410063, by rfl⟩ : syracuseStep 2187005 = 820127) (by norm_num)
theorem B3694349 : Blo 1457548 3694349 := bbase (se 3 (by rfl) ⟨692690, by rfl⟩ : syracuseStep 3694349 = 1385381) (by norm_num)
theorem B2187029 : Blo 1457548 2187029 := bbase (se 6 (by rfl) ⟨51258, by rfl⟩ : syracuseStep 2187029 = 102517) (by norm_num)
theorem B2187053 : Blo 1457548 2187053 := bbase (se 3 (by rfl) ⟨410072, by rfl⟩ : syracuseStep 2187053 = 820145) (by norm_num)
theorem B2187077 : Blo 1457548 2187077 := bbase (se 4 (by rfl) ⟨205038, by rfl⟩ : syracuseStep 2187077 = 410077) (by norm_num)
theorem B5537605 : Blo 1457548 5537605 := bbase (se 4 (by rfl) ⟨519150, by rfl⟩ : syracuseStep 5537605 = 1038301) (by norm_num)
theorem B3505997 : Blo 1457548 3505997 := bbase (se 3 (by rfl) ⟨657374, by rfl⟩ : syracuseStep 3505997 = 1314749) (by norm_num)
theorem B2187101 : Blo 1457548 2187101 := bbase (se 3 (by rfl) ⟨410081, by rfl⟩ : syracuseStep 2187101 = 820163) (by norm_num)
theorem B2629469 : Blo 1457548 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B2187125 : Blo 1457548 2187125 := bbase (se 5 (by rfl) ⟨102521, by rfl⟩ : syracuseStep 2187125 = 205043) (by norm_num)
theorem B2187149 : Blo 1457548 2187149 := bbase (se 3 (by rfl) ⟨410090, by rfl⟩ : syracuseStep 2187149 = 820181) (by norm_num)
theorem B2187173 : Blo 1457548 2187173 := bbase (se 4 (by rfl) ⟨205047, by rfl⟩ : syracuseStep 2187173 = 410095) (by norm_num)
theorem B6651829 : Blo 1457548 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B2187197 : Blo 1457548 2187197 := bbase (se 3 (by rfl) ⟨410099, by rfl⟩ : syracuseStep 2187197 = 820199) (by norm_num)
theorem B2187221 : Blo 1457548 2187221 := bbase (se 7 (by rfl) ⟨25631, by rfl⟩ : syracuseStep 2187221 = 51263) (by norm_num)
theorem B2187245 : Blo 1457548 2187245 := bbase (se 3 (by rfl) ⟨410108, by rfl⟩ : syracuseStep 2187245 = 820217) (by norm_num)
theorem B1458179 : Blo 1457548 1458179 := bstep (se 1 (by rfl) ⟨1093634, by rfl⟩ : syracuseStep 1458179 = 2187269) B2187269
theorem B4923395 : Blo 1457548 4923395 := bstep (se 1 (by rfl) ⟨3692546, by rfl⟩ : syracuseStep 4923395 = 7385093) B7385093
theorem B2334737 : Blo 1457548 2334737 := bstep (se 2 (by rfl) ⟨875526, by rfl⟩ : syracuseStep 2334737 = 1751053) B1751053
theorem B2187281 : Blo 1457548 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B1458195 : Blo 1457548 1458195 := bstep (se 1 (by rfl) ⟨1093646, by rfl⟩ : syracuseStep 1458195 = 2187293) B2187293
theorem B2187299 : Blo 1457548 2187299 := bstep (se 1 (by rfl) ⟨1640474, by rfl⟩ : syracuseStep 2187299 = 3280949) B3280949
theorem B1458211 : Blo 1457548 1458211 := bstep (se 1 (by rfl) ⟨1093658, by rfl⟩ : syracuseStep 1458211 = 2187317) B2187317
theorem B1458227 : Blo 1457548 1458227 := bstep (se 1 (by rfl) ⟨1093670, by rfl⟩ : syracuseStep 1458227 = 2187341) B2187341
theorem B2187329 : Blo 1457548 2187329 := bstep (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) B1640497
theorem B1458243 : Blo 1457548 1458243 := bstep (se 1 (by rfl) ⟨1093682, by rfl⟩ : syracuseStep 1458243 = 2187365) B2187365
theorem B3506257 : Blo 1457548 3506257 := bstep (se 2 (by rfl) ⟨1314846, by rfl⟩ : syracuseStep 3506257 = 2629693) B2629693
theorem B2187347 : Blo 1457548 2187347 := bstep (se 1 (by rfl) ⟨1640510, by rfl⟩ : syracuseStep 2187347 = 3281021) B3281021
theorem B1458259 : Blo 1457548 1458259 := bstep (se 1 (by rfl) ⟨1093694, by rfl⟩ : syracuseStep 1458259 = 2187389) B2187389
theorem B1753171 : Blo 1457548 1753171 := bstep (se 1 (by rfl) ⟨1314878, by rfl⟩ : syracuseStep 1753171 = 2629757) B2629757
theorem B1458275 : Blo 1457548 1458275 := bstep (se 1 (by rfl) ⟨1093706, by rfl⟩ : syracuseStep 1458275 = 2187413) B2187413
theorem B2105443 : Blo 1457548 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B2187377 : Blo 1457548 2187377 := bstep (se 2 (by rfl) ⟨820266, by rfl⟩ : syracuseStep 2187377 = 1640533) B1640533
theorem B1458291 : Blo 1457548 1458291 := bstep (se 1 (by rfl) ⟨1093718, by rfl⟩ : syracuseStep 1458291 = 2187437) B2187437
theorem B2187395 : Blo 1457548 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B1458307 : Blo 1457548 1458307 := bstep (se 1 (by rfl) ⟨1093730, by rfl⟩ : syracuseStep 1458307 = 2187461) B2187461
theorem B1458323 : Blo 1457548 1458323 := bstep (se 1 (by rfl) ⟨1093742, by rfl⟩ : syracuseStep 1458323 = 2187485) B2187485
theorem B2187425 : Blo 1457548 2187425 := bstep (se 2 (by rfl) ⟨820284, by rfl⟩ : syracuseStep 2187425 = 1640569) B1640569
theorem B1458339 : Blo 1457548 1458339 := bstep (se 1 (by rfl) ⟨1093754, by rfl⟩ : syracuseStep 1458339 = 2187509) B2187509
theorem B2187443 : Blo 1457548 2187443 := bstep (se 1 (by rfl) ⟨1640582, by rfl⟩ : syracuseStep 2187443 = 3281165) B3281165
theorem B1458355 : Blo 1457548 1458355 := bstep (se 1 (by rfl) ⟨1093766, by rfl⟩ : syracuseStep 1458355 = 2187533) B2187533
theorem B1458371 : Blo 1457548 1458371 := bstep (se 1 (by rfl) ⟨1093778, by rfl⟩ : syracuseStep 1458371 = 2187557) B2187557
theorem B12460229 : Blo 1457548 12460229 := bstep (se 4 (by rfl) ⟨1168146, by rfl⟩ : syracuseStep 12460229 = 2336293) B2336293
theorem B6234317 : Blo 1457548 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B2187473 : Blo 1457548 2187473 := bstep (se 2 (by rfl) ⟨820302, by rfl⟩ : syracuseStep 2187473 = 1640605) B1640605
theorem B1458387 : Blo 1457548 1458387 := bstep (se 1 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 1458387 = 2187581) B2187581
theorem B2187491 : Blo 1457548 2187491 := bstep (se 1 (by rfl) ⟨1640618, by rfl⟩ : syracuseStep 2187491 = 3281237) B3281237
theorem B1458403 : Blo 1457548 1458403 := bstep (se 1 (by rfl) ⟨1093802, by rfl⟩ : syracuseStep 1458403 = 2187605) B2187605
theorem B2769137 : Blo 1457548 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B6234353 : Blo 1457548 6234353 := bstep (se 2 (by rfl) ⟨2337882, by rfl⟩ : syracuseStep 6234353 = 4675765) B4675765
theorem B1458419 : Blo 1457548 1458419 := bstep (se 1 (by rfl) ⟨1093814, by rfl⟩ : syracuseStep 1458419 = 2187629) B2187629
theorem B2187521 : Blo 1457548 2187521 := bstep (se 2 (by rfl) ⟨820320, by rfl⟩ : syracuseStep 2187521 = 1640641) B1640641
theorem B1458435 : Blo 1457548 1458435 := bstep (se 1 (by rfl) ⟨1093826, by rfl⟩ : syracuseStep 1458435 = 2187653) B2187653
theorem B4923665 : Blo 1457548 4923665 := bstep (se 2 (by rfl) ⟨1846374, by rfl⟩ : syracuseStep 4923665 = 3692749) B3692749
theorem B2187539 : Blo 1457548 2187539 := bstep (se 1 (by rfl) ⟨1640654, by rfl⟩ : syracuseStep 2187539 = 3281309) B3281309
theorem B1458451 : Blo 1457548 1458451 := bstep (se 1 (by rfl) ⟨1093838, by rfl⟩ : syracuseStep 1458451 = 2187677) B2187677
theorem B1458467 : Blo 1457548 1458467 := bstep (se 1 (by rfl) ⟨1093850, by rfl⟩ : syracuseStep 1458467 = 2187701) B2187701
theorem B4669741 : Blo 1457548 4669741 := bstep (se 3 (by rfl) ⟨875576, by rfl⟩ : syracuseStep 4669741 = 1751153) B1751153
theorem B2187569 : Blo 1457548 2187569 := bstep (se 2 (by rfl) ⟨820338, by rfl⟩ : syracuseStep 2187569 = 1640677) B1640677
theorem B1458483 : Blo 1457548 1458483 := bstep (se 1 (by rfl) ⟨1093862, by rfl⟩ : syracuseStep 1458483 = 2187725) B2187725
theorem B2187587 : Blo 1457548 2187587 := bstep (se 1 (by rfl) ⟨1640690, by rfl⟩ : syracuseStep 2187587 = 3281381) B3281381
theorem B1458499 : Blo 1457548 1458499 := bstep (se 1 (by rfl) ⟨1093874, by rfl⟩ : syracuseStep 1458499 = 2187749) B2187749
theorem B6226253 : Blo 1457548 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B1458515 : Blo 1457548 1458515 := bstep (se 1 (by rfl) ⟨1093886, by rfl⟩ : syracuseStep 1458515 = 2187773) B2187773
theorem B2187617 : Blo 1457548 2187617 := bstep (se 2 (by rfl) ⟨820356, by rfl⟩ : syracuseStep 2187617 = 1640713) B1640713
theorem B1458531 : Blo 1457548 1458531 := bstep (se 1 (by rfl) ⟨1093898, by rfl⟩ : syracuseStep 1458531 = 2187797) B2187797
theorem B11075939 : Blo 1457548 11075939 := bstep (se 1 (by rfl) ⟨8306954, by rfl⟩ : syracuseStep 11075939 = 16613909) B16613909
theorem B2367857 : Blo 1457548 2367857 := bstep (se 2 (by rfl) ⟨887946, by rfl⟩ : syracuseStep 2367857 = 1775893) B1775893
theorem B2187635 : Blo 1457548 2187635 := bstep (se 1 (by rfl) ⟨1640726, by rfl⟩ : syracuseStep 2187635 = 3281453) B3281453
theorem B1458547 : Blo 1457548 1458547 := bstep (se 1 (by rfl) ⟨1093910, by rfl⟩ : syracuseStep 1458547 = 2187821) B2187821
theorem B1556867 : Blo 1457548 1556867 := bstep (se 1 (by rfl) ⟨1167650, by rfl⟩ : syracuseStep 1556867 = 2335301) B2335301
theorem B1458563 : Blo 1457548 1458563 := bstep (se 1 (by rfl) ⟨1093922, by rfl⟩ : syracuseStep 1458563 = 2187845) B2187845
theorem B2187665 : Blo 1457548 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B1458579 : Blo 1457548 1458579 := bstep (se 1 (by rfl) ⟨1093934, by rfl⟩ : syracuseStep 1458579 = 2187869) B2187869
theorem B2187683 : Blo 1457548 2187683 := bstep (se 1 (by rfl) ⟨1640762, by rfl⟩ : syracuseStep 2187683 = 3281525) B3281525
theorem B1458595 : Blo 1457548 1458595 := bstep (se 1 (by rfl) ⟨1093946, by rfl⟩ : syracuseStep 1458595 = 2187893) B2187893
theorem B1458611 : Blo 1457548 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B2187713 : Blo 1457548 2187713 := bstep (se 2 (by rfl) ⟨820392, by rfl⟩ : syracuseStep 2187713 = 1640785) B1640785
theorem B1458627 : Blo 1457548 1458627 := bstep (se 1 (by rfl) ⟨1093970, by rfl⟩ : syracuseStep 1458627 = 2187941) B2187941
theorem B2187731 : Blo 1457548 2187731 := bstep (se 1 (by rfl) ⟨1640798, by rfl⟩ : syracuseStep 2187731 = 3281597) B3281597
theorem B1458643 : Blo 1457548 1458643 := bstep (se 1 (by rfl) ⟨1093982, by rfl⟩ : syracuseStep 1458643 = 2187965) B2187965
theorem B1458659 : Blo 1457548 1458659 := bstep (se 1 (by rfl) ⟨1093994, by rfl⟩ : syracuseStep 1458659 = 2187989) B2187989
theorem B2187761 : Blo 1457548 2187761 := bstep (se 2 (by rfl) ⟨820410, by rfl⟩ : syracuseStep 2187761 = 1640821) B1640821
theorem B1458675 : Blo 1457548 1458675 := bstep (se 1 (by rfl) ⟨1094006, by rfl⟩ : syracuseStep 1458675 = 2188013) B2188013
theorem B2187779 : Blo 1457548 2187779 := bstep (se 1 (by rfl) ⟨1640834, by rfl⟩ : syracuseStep 2187779 = 3281669) B3281669
theorem B1458691 : Blo 1457548 1458691 := bstep (se 1 (by rfl) ⟨1094018, by rfl⟩ : syracuseStep 1458691 = 2188037) B2188037
theorem B1458707 : Blo 1457548 1458707 := bstep (se 1 (by rfl) ⟨1094030, by rfl⟩ : syracuseStep 1458707 = 2188061) B2188061
theorem B2187809 : Blo 1457548 2187809 := bstep (se 2 (by rfl) ⟨820428, by rfl⟩ : syracuseStep 2187809 = 1640857) B1640857
theorem B1458723 : Blo 1457548 1458723 := bstep (se 1 (by rfl) ⟨1094042, by rfl⟩ : syracuseStep 1458723 = 2188085) B2188085
theorem B9347633 : Blo 1457548 9347633 := bstep (se 2 (by rfl) ⟨3505362, by rfl⟩ : syracuseStep 9347633 = 7010725) B7010725
theorem B2187827 : Blo 1457548 2187827 := bstep (se 1 (by rfl) ⟨1640870, by rfl⟩ : syracuseStep 2187827 = 3281741) B3281741
theorem B1458739 : Blo 1457548 1458739 := bstep (se 1 (by rfl) ⟨1094054, by rfl⟩ : syracuseStep 1458739 = 2188109) B2188109
theorem B1458755 : Blo 1457548 1458755 := bstep (se 1 (by rfl) ⟨1094066, by rfl⟩ : syracuseStep 1458755 = 2188133) B2188133
theorem B4153933 : Blo 1457548 4153933 := bstep (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) B1557725
theorem B2187857 : Blo 1457548 2187857 := bstep (se 2 (by rfl) ⟨820446, by rfl⟩ : syracuseStep 2187857 = 1640893) B1640893
theorem B1458771 : Blo 1457548 1458771 := bstep (se 1 (by rfl) ⟨1094078, by rfl⟩ : syracuseStep 1458771 = 2188157) B2188157
theorem B2187875 : Blo 1457548 2187875 := bstep (se 1 (by rfl) ⟨1640906, by rfl⟩ : syracuseStep 2187875 = 3281813) B3281813
theorem B1458787 : Blo 1457548 1458787 := bstep (se 1 (by rfl) ⟨1094090, by rfl⟩ : syracuseStep 1458787 = 2188181) B2188181
theorem B9347683 : Blo 1457548 9347683 := bstep (se 1 (by rfl) ⟨7010762, by rfl⟩ : syracuseStep 9347683 = 14021525) B14021525
theorem B1458803 : Blo 1457548 1458803 := bstep (se 1 (by rfl) ⟨1094102, by rfl⟩ : syracuseStep 1458803 = 2188205) B2188205
theorem B2187905 : Blo 1457548 2187905 := bstep (se 2 (by rfl) ⟨820464, by rfl⟩ : syracuseStep 2187905 = 1640929) B1640929
theorem B1458819 : Blo 1457548 1458819 := bstep (se 1 (by rfl) ⟨1094114, by rfl⟩ : syracuseStep 1458819 = 2188229) B2188229
theorem B3326609 : Blo 1457548 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B2187923 : Blo 1457548 2187923 := bstep (se 1 (by rfl) ⟨1640942, by rfl⟩ : syracuseStep 2187923 = 3281885) B3281885
theorem B1458835 : Blo 1457548 1458835 := bstep (se 1 (by rfl) ⟨1094126, by rfl⟩ : syracuseStep 1458835 = 2188253) B2188253
theorem B6226595 : Blo 1457548 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B1458851 : Blo 1457548 1458851 := bstep (se 1 (by rfl) ⟨1094138, by rfl⟩ : syracuseStep 1458851 = 2188277) B2188277
theorem B4989613 : Blo 1457548 4989613 := bstep (se 3 (by rfl) ⟨935552, by rfl⟩ : syracuseStep 4989613 = 1871105) B1871105
theorem B2335409 : Blo 1457548 2335409 := bstep (se 2 (by rfl) ⟨875778, by rfl⟩ : syracuseStep 2335409 = 1751557) B1751557
theorem B2187953 : Blo 1457548 2187953 := bstep (se 2 (by rfl) ⟨820482, by rfl⟩ : syracuseStep 2187953 = 1640965) B1640965
theorem B1458867 : Blo 1457548 1458867 := bstep (se 1 (by rfl) ⟨1094150, by rfl⟩ : syracuseStep 1458867 = 2188301) B2188301
theorem B2187971 : Blo 1457548 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B1458883 : Blo 1457548 1458883 := bstep (se 1 (by rfl) ⟨1094162, by rfl⟩ : syracuseStep 1458883 = 2188325) B2188325
theorem B1458899 : Blo 1457548 1458899 := bstep (se 1 (by rfl) ⟨1094174, by rfl⟩ : syracuseStep 1458899 = 2188349) B2188349
theorem B2188001 : Blo 1457548 2188001 := bstep (se 2 (by rfl) ⟨820500, by rfl⟩ : syracuseStep 2188001 = 1641001) B1641001
theorem B1458915 : Blo 1457548 1458915 := bstep (se 1 (by rfl) ⟨1094186, by rfl⟩ : syracuseStep 1458915 = 2188373) B2188373
theorem B2188019 : Blo 1457548 2188019 := bstep (se 1 (by rfl) ⟨1641014, by rfl⟩ : syracuseStep 2188019 = 3282029) B3282029
theorem B1458931 : Blo 1457548 1458931 := bstep (se 1 (by rfl) ⟨1094198, by rfl⟩ : syracuseStep 1458931 = 2188397) B2188397
theorem B1458947 : Blo 1457548 1458947 := bstep (se 1 (by rfl) ⟨1094210, by rfl⟩ : syracuseStep 1458947 = 2188421) B2188421
theorem B2188049 : Blo 1457548 2188049 := bstep (se 2 (by rfl) ⟨820518, by rfl⟩ : syracuseStep 2188049 = 1641037) B1641037
theorem B1458963 : Blo 1457548 1458963 := bstep (se 1 (by rfl) ⟨1094222, by rfl⟩ : syracuseStep 1458963 = 2188445) B2188445
theorem B2188067 : Blo 1457548 2188067 := bstep (se 1 (by rfl) ⟨1641050, by rfl⟩ : syracuseStep 2188067 = 3282101) B3282101
theorem B1458979 : Blo 1457548 1458979 := bstep (se 1 (by rfl) ⟨1094234, by rfl⟩ : syracuseStep 1458979 = 2188469) B2188469
theorem B4924205 : Blo 1457548 4924205 := bstep (se 3 (by rfl) ⟨923288, by rfl⟩ : syracuseStep 4924205 = 1846577) B1846577
theorem B4154161 : Blo 1457548 4154161 := bstep (se 2 (by rfl) ⟨1557810, by rfl⟩ : syracuseStep 4154161 = 3115621) B3115621
theorem B1458995 : Blo 1457548 1458995 := bstep (se 1 (by rfl) ⟨1094246, by rfl⟩ : syracuseStep 1458995 = 2188493) B2188493
theorem B2188097 : Blo 1457548 2188097 := bstep (se 2 (by rfl) ⟨820536, by rfl⟩ : syracuseStep 2188097 = 1641073) B1641073
theorem B1459011 : Blo 1457548 1459011 := bstep (se 1 (by rfl) ⟨1094258, by rfl⟩ : syracuseStep 1459011 = 2188517) B2188517
theorem B3744593 : Blo 1457548 3744593 := bstep (se 2 (by rfl) ⟨1404222, by rfl⟩ : syracuseStep 3744593 = 2808445) B2808445
theorem B2188115 : Blo 1457548 2188115 := bstep (se 1 (by rfl) ⟨1641086, by rfl⟩ : syracuseStep 2188115 = 3282173) B3282173
theorem B1459027 : Blo 1457548 1459027 := bstep (se 1 (by rfl) ⟨1094270, by rfl⟩ : syracuseStep 1459027 = 2188541) B2188541
theorem B4924259 : Blo 1457548 4924259 := bstep (se 1 (by rfl) ⟨3693194, by rfl⟩ : syracuseStep 4924259 = 7386389) B7386389
theorem B1459043 : Blo 1457548 1459043 := bstep (se 1 (by rfl) ⟨1094282, by rfl⟩ : syracuseStep 1459043 = 2188565) B2188565
theorem B28017521 : Blo 1457548 28017521 := bstep (se 2 (by rfl) ⟨10506570, by rfl⟩ : syracuseStep 28017521 = 21013141) B21013141
theorem B4432753 : Blo 1457548 4432753 := bstep (se 2 (by rfl) ⟨1662282, by rfl⟩ : syracuseStep 4432753 = 3324565) B3324565
theorem B2188145 : Blo 1457548 2188145 := bstep (se 2 (by rfl) ⟨820554, by rfl⟩ : syracuseStep 2188145 = 1641109) B1641109
theorem B1459059 : Blo 1457548 1459059 := bstep (se 1 (by rfl) ⟨1094294, by rfl⟩ : syracuseStep 1459059 = 2188589) B2188589
theorem B2188163 : Blo 1457548 2188163 := bstep (se 1 (by rfl) ⟨1641122, by rfl⟩ : syracuseStep 2188163 = 3282245) B3282245
theorem B1459075 : Blo 1457548 1459075 := bstep (se 1 (by rfl) ⟨1094306, by rfl⟩ : syracuseStep 1459075 = 2188613) B2188613
theorem B1459091 : Blo 1457548 1459091 := bstep (se 1 (by rfl) ⟨1094318, by rfl⟩ : syracuseStep 1459091 = 2188637) B2188637
theorem B2188193 : Blo 1457548 2188193 := bstep (se 2 (by rfl) ⟨820572, by rfl⟩ : syracuseStep 2188193 = 1641145) B1641145
theorem B1459107 : Blo 1457548 1459107 := bstep (se 1 (by rfl) ⟨1094330, by rfl⟩ : syracuseStep 1459107 = 2188661) B2188661
theorem B2188211 : Blo 1457548 2188211 := bstep (se 1 (by rfl) ⟨1641158, by rfl⟩ : syracuseStep 2188211 = 3282317) B3282317
theorem B1459123 : Blo 1457548 1459123 := bstep (se 1 (by rfl) ⟨1094342, by rfl⟩ : syracuseStep 1459123 = 2188685) B2188685
theorem B1459139 : Blo 1457548 1459139 := bstep (se 1 (by rfl) ⟨1094354, by rfl⟩ : syracuseStep 1459139 = 2188709) B2188709
theorem B2188241 : Blo 1457548 2188241 := bstep (se 2 (by rfl) ⟨820590, by rfl⟩ : syracuseStep 2188241 = 1641181) B1641181
theorem B4154321 : Blo 1457548 4154321 := bstep (se 2 (by rfl) ⟨1557870, by rfl⟩ : syracuseStep 4154321 = 3115741) B3115741
theorem B1459155 : Blo 1457548 1459155 := bstep (se 1 (by rfl) ⟨1094366, by rfl⟩ : syracuseStep 1459155 = 2188733) B2188733
theorem B2188259 : Blo 1457548 2188259 := bstep (se 1 (by rfl) ⟨1641194, by rfl⟩ : syracuseStep 2188259 = 3282389) B3282389
theorem B1459171 : Blo 1457548 1459171 := bstep (se 1 (by rfl) ⟨1094378, by rfl⟩ : syracuseStep 1459171 = 2188757) B2188757
theorem B1459187 : Blo 1457548 1459187 := bstep (se 1 (by rfl) ⟨1094390, by rfl⟩ : syracuseStep 1459187 = 2188781) B2188781
theorem B2188289 : Blo 1457548 2188289 := bstep (se 2 (by rfl) ⟨820608, by rfl⟩ : syracuseStep 2188289 = 1641217) B1641217
theorem B1459203 : Blo 1457548 1459203 := bstep (se 1 (by rfl) ⟨1094402, by rfl⟩ : syracuseStep 1459203 = 2188805) B2188805
theorem B2188307 : Blo 1457548 2188307 := bstep (se 1 (by rfl) ⟨1641230, by rfl⟩ : syracuseStep 2188307 = 3282461) B3282461
theorem B1459219 : Blo 1457548 1459219 := bstep (se 1 (by rfl) ⟨1094414, by rfl⟩ : syracuseStep 1459219 = 2188829) B2188829
theorem B5538851 : Blo 1457548 5538851 := bstep (se 1 (by rfl) ⟨4154138, by rfl⟩ : syracuseStep 5538851 = 8308277) B8308277
theorem B1459235 : Blo 1457548 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B2188337 : Blo 1457548 2188337 := bstep (se 2 (by rfl) ⟨820626, by rfl⟩ : syracuseStep 2188337 = 1641253) B1641253
theorem B1459251 : Blo 1457548 1459251 := bstep (se 1 (by rfl) ⟨1094438, by rfl⟩ : syracuseStep 1459251 = 2188877) B2188877
theorem B4154435 : Blo 1457548 4154435 := bstep (se 1 (by rfl) ⟨3115826, by rfl⟩ : syracuseStep 4154435 = 6231653) B6231653
theorem B2188355 : Blo 1457548 2188355 := bstep (se 1 (by rfl) ⟨1641266, by rfl⟩ : syracuseStep 2188355 = 3282533) B3282533
theorem B1459267 : Blo 1457548 1459267 := bstep (se 1 (by rfl) ⟨1094450, by rfl⟩ : syracuseStep 1459267 = 2188901) B2188901
theorem B1459283 : Blo 1457548 1459283 := bstep (se 1 (by rfl) ⟨1094462, by rfl⟩ : syracuseStep 1459283 = 2188925) B2188925
theorem B2188385 : Blo 1457548 2188385 := bstep (se 2 (by rfl) ⟨820644, by rfl⟩ : syracuseStep 2188385 = 1641289) B1641289
theorem B3114083 : Blo 1457548 3114083 := bstep (se 1 (by rfl) ⟨2335562, by rfl⟩ : syracuseStep 3114083 = 4671125) B4671125
theorem B1459299 : Blo 1457548 1459299 := bstep (se 1 (by rfl) ⟨1094474, by rfl⟩ : syracuseStep 1459299 = 2188949) B2188949
theorem B6227057 : Blo 1457548 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B2770033 : Blo 1457548 2770033 := bstep (se 2 (by rfl) ⟨1038762, by rfl⟩ : syracuseStep 2770033 = 2077525) B2077525
theorem B2188403 : Blo 1457548 2188403 := bstep (se 1 (by rfl) ⟨1641302, by rfl⟩ : syracuseStep 2188403 = 3282605) B3282605
theorem B4924529 : Blo 1457548 4924529 := bstep (se 2 (by rfl) ⟨1846698, by rfl⟩ : syracuseStep 4924529 = 3693397) B3693397
theorem B1459315 : Blo 1457548 1459315 := bstep (se 1 (by rfl) ⟨1094486, by rfl⟩ : syracuseStep 1459315 = 2188973) B2188973
theorem B1459331 : Blo 1457548 1459331 := bstep (se 1 (by rfl) ⟨1094498, by rfl⟩ : syracuseStep 1459331 = 2188997) B2188997
theorem B8307845 : Blo 1457548 8307845 := bstep (se 4 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 8307845 = 1557721) B1557721
theorem B2188433 : Blo 1457548 2188433 := bstep (se 2 (by rfl) ⟨820662, by rfl⟩ : syracuseStep 2188433 = 1641325) B1641325
theorem B1459347 : Blo 1457548 1459347 := bstep (se 1 (by rfl) ⟨1094510, by rfl⟩ : syracuseStep 1459347 = 2189021) B2189021
theorem B2188451 : Blo 1457548 2188451 := bstep (se 1 (by rfl) ⟨1641338, by rfl⟩ : syracuseStep 2188451 = 3282677) B3282677
theorem B1459363 : Blo 1457548 1459363 := bstep (se 1 (by rfl) ⟨1094522, by rfl⟩ : syracuseStep 1459363 = 2189045) B2189045
theorem B2335921 : Blo 1457548 2335921 := bstep (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) B1751941
theorem B1459379 : Blo 1457548 1459379 := bstep (se 1 (by rfl) ⟨1094534, by rfl⟩ : syracuseStep 1459379 = 2189069) B2189069
theorem B2188481 : Blo 1457548 2188481 := bstep (se 2 (by rfl) ⟨820680, by rfl⟩ : syracuseStep 2188481 = 1641361) B1641361
theorem B1459395 : Blo 1457548 1459395 := bstep (se 1 (by rfl) ⟨1094546, by rfl⟩ : syracuseStep 1459395 = 2189093) B2189093
theorem B2188499 : Blo 1457548 2188499 := bstep (se 1 (by rfl) ⟨1641374, by rfl⟩ : syracuseStep 2188499 = 3282749) B3282749
theorem B1459411 : Blo 1457548 1459411 := bstep (se 1 (by rfl) ⟨1094558, by rfl⟩ : syracuseStep 1459411 = 2189117) B2189117
theorem B1459427 : Blo 1457548 1459427 := bstep (se 1 (by rfl) ⟨1094570, by rfl⟩ : syracuseStep 1459427 = 2189141) B2189141
theorem B2188529 : Blo 1457548 2188529 := bstep (se 2 (by rfl) ⟨820698, by rfl⟩ : syracuseStep 2188529 = 1641397) B1641397
theorem B1459443 : Blo 1457548 1459443 := bstep (se 1 (by rfl) ⟨1094582, by rfl⟩ : syracuseStep 1459443 = 2189165) B2189165
theorem B2188547 : Blo 1457548 2188547 := bstep (se 1 (by rfl) ⟨1641410, by rfl⟩ : syracuseStep 2188547 = 3282821) B3282821
theorem B1459459 : Blo 1457548 1459459 := bstep (se 1 (by rfl) ⟨1094594, by rfl⟩ : syracuseStep 1459459 = 2189189) B2189189
theorem B2770193 : Blo 1457548 2770193 := bstep (se 2 (by rfl) ⟨1038822, by rfl⟩ : syracuseStep 2770193 = 2077645) B2077645
theorem B1459475 : Blo 1457548 1459475 := bstep (se 1 (by rfl) ⟨1094606, by rfl⟩ : syracuseStep 1459475 = 2189213) B2189213
theorem B2188577 : Blo 1457548 2188577 := bstep (se 2 (by rfl) ⟨820716, by rfl⟩ : syracuseStep 2188577 = 1641433) B1641433
theorem B1459491 : Blo 1457548 1459491 := bstep (se 1 (by rfl) ⟨1094618, by rfl⟩ : syracuseStep 1459491 = 2189237) B2189237
theorem B2188595 : Blo 1457548 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B1459507 : Blo 1457548 1459507 := bstep (se 1 (by rfl) ⟨1094630, by rfl⟩ : syracuseStep 1459507 = 2189261) B2189261
theorem B3794243 : Blo 1457548 3794243 := bstep (se 1 (by rfl) ⟨2845682, by rfl⟩ : syracuseStep 3794243 = 5691365) B5691365
theorem B1459523 : Blo 1457548 1459523 := bstep (se 1 (by rfl) ⟨1094642, by rfl⟩ : syracuseStep 1459523 = 2189285) B2189285
theorem B2188625 : Blo 1457548 2188625 := bstep (se 2 (by rfl) ⟨820734, by rfl⟩ : syracuseStep 2188625 = 1641469) B1641469
theorem B1459539 : Blo 1457548 1459539 := bstep (se 1 (by rfl) ⟨1094654, by rfl⟩ : syracuseStep 1459539 = 2189309) B2189309
theorem B2188643 : Blo 1457548 2188643 := bstep (se 1 (by rfl) ⟨1641482, by rfl⟩ : syracuseStep 2188643 = 3282965) B3282965
theorem B1639795 : Blo 1457548 1639795 := bstep (se 1 (by rfl) ⟨1229846, by rfl⟩ : syracuseStep 1639795 = 2459693) B2459693
theorem B2188673 : Blo 1457548 2188673 := bstep (se 2 (by rfl) ⟨820752, by rfl⟩ : syracuseStep 2188673 = 1641505) B1641505
theorem B10519949 : Blo 1457548 10519949 := bstep (se 3 (by rfl) ⟨1972490, by rfl⟩ : syracuseStep 10519949 = 3944981) B3944981
theorem B2188691 : Blo 1457548 2188691 := bstep (se 1 (by rfl) ⟨1641518, by rfl⟩ : syracuseStep 2188691 = 3283037) B3283037
theorem B2188721 : Blo 1457548 2188721 := bstep (se 2 (by rfl) ⟨820770, by rfl⟩ : syracuseStep 2188721 = 1641541) B1641541
theorem B2188739 : Blo 1457548 2188739 := bstep (se 1 (by rfl) ⟨1641554, by rfl⟩ : syracuseStep 2188739 = 3283109) B3283109
theorem B2188769 : Blo 1457548 2188769 := bstep (se 2 (by rfl) ⟨820788, by rfl⟩ : syracuseStep 2188769 = 1641577) B1641577
theorem B2188787 : Blo 1457548 2188787 := bstep (se 1 (by rfl) ⟨1641590, by rfl⟩ : syracuseStep 2188787 = 3283181) B3283181
theorem B1639939 : Blo 1457548 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B2188817 : Blo 1457548 2188817 := bstep (se 2 (by rfl) ⟨820806, by rfl⟩ : syracuseStep 2188817 = 1641613) B1641613
theorem B2188835 : Blo 1457548 2188835 := bstep (se 1 (by rfl) ⟨1641626, by rfl⟩ : syracuseStep 2188835 = 3283253) B3283253
theorem B2188865 : Blo 1457548 2188865 := bstep (se 2 (by rfl) ⟨820824, by rfl⟩ : syracuseStep 2188865 = 1641649) B1641649
theorem B2188883 : Blo 1457548 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B2188913 : Blo 1457548 2188913 := bstep (se 2 (by rfl) ⟨820842, by rfl⟩ : syracuseStep 2188913 = 1641685) B1641685
theorem B1844851 : Blo 1457548 1844851 := bstep (se 1 (by rfl) ⟨1383638, by rfl⟩ : syracuseStep 1844851 = 2767277) B2767277
theorem B2188931 : Blo 1457548 2188931 := bstep (se 1 (by rfl) ⟨1641698, by rfl⟩ : syracuseStep 2188931 = 3283397) B3283397
theorem B4925069 : Blo 1457548 4925069 := bstep (se 3 (by rfl) ⟨923450, by rfl⟩ : syracuseStep 4925069 = 1846901) B1846901
theorem B1640083 : Blo 1457548 1640083 := bstep (se 1 (by rfl) ⟨1230062, by rfl⟩ : syracuseStep 1640083 = 2460125) B2460125
theorem B2188961 : Blo 1457548 2188961 := bstep (se 2 (by rfl) ⟨820860, by rfl⟩ : syracuseStep 2188961 = 1641721) B1641721
theorem B2770595 : Blo 1457548 2770595 := bstep (se 1 (by rfl) ⟨2077946, by rfl⟩ : syracuseStep 2770595 = 4155893) B4155893
theorem B2188979 : Blo 1457548 2188979 := bstep (se 1 (by rfl) ⟨1641734, by rfl⟩ : syracuseStep 2188979 = 3283469) B3283469
theorem B4925123 : Blo 1457548 4925123 := bstep (se 1 (by rfl) ⟨3693842, by rfl⟩ : syracuseStep 4925123 = 7387685) B7387685
theorem B2189009 : Blo 1457548 2189009 := bstep (se 2 (by rfl) ⟨820878, by rfl⟩ : syracuseStep 2189009 = 1641757) B1641757
theorem B1844947 : Blo 1457548 1844947 := bstep (se 1 (by rfl) ⟨1383710, by rfl⟩ : syracuseStep 1844947 = 2767421) B2767421
theorem B2189027 : Blo 1457548 2189027 := bstep (se 1 (by rfl) ⟨1641770, by rfl⟩ : syracuseStep 2189027 = 3283541) B3283541
theorem B2189057 : Blo 1457548 2189057 := bstep (se 2 (by rfl) ⟨820896, by rfl⟩ : syracuseStep 2189057 = 1641793) B1641793
theorem B2189075 : Blo 1457548 2189075 := bstep (se 1 (by rfl) ⟨1641806, by rfl⟩ : syracuseStep 2189075 = 3283613) B3283613
theorem B1640227 : Blo 1457548 1640227 := bstep (se 1 (by rfl) ⟨1230170, by rfl⟩ : syracuseStep 1640227 = 2460341) B2460341
theorem B2189105 : Blo 1457548 2189105 := bstep (se 2 (by rfl) ⟨820914, by rfl⟩ : syracuseStep 2189105 = 1641829) B1641829
theorem B2189123 : Blo 1457548 2189123 := bstep (se 1 (by rfl) ⟨1641842, by rfl⟩ : syracuseStep 2189123 = 3283685) B3283685
theorem B2189153 : Blo 1457548 2189153 := bstep (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) B1641865
theorem B2189171 : Blo 1457548 2189171 := bstep (se 1 (by rfl) ⟨1641878, by rfl⟩ : syracuseStep 2189171 = 3283757) B3283757
theorem B2189201 : Blo 1457548 2189201 := bstep (se 2 (by rfl) ⟨820950, by rfl⟩ : syracuseStep 2189201 = 1641901) B1641901
theorem B2189219 : Blo 1457548 2189219 := bstep (se 1 (by rfl) ⟨1641914, by rfl⟩ : syracuseStep 2189219 = 3283829) B3283829
theorem B1640371 : Blo 1457548 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B2189249 : Blo 1457548 2189249 := bstep (se 2 (by rfl) ⟨820968, by rfl⟩ : syracuseStep 2189249 = 1641937) B1641937
theorem B4925393 : Blo 1457548 4925393 := bstep (se 2 (by rfl) ⟨1847022, by rfl⟩ : syracuseStep 4925393 = 3694045) B3694045
theorem B2189267 : Blo 1457548 2189267 := bstep (se 1 (by rfl) ⟨1641950, by rfl⟩ : syracuseStep 2189267 = 3283901) B3283901
theorem B15771619 : Blo 1457548 15771619 := bstep (se 1 (by rfl) ⟨11828714, by rfl⟩ : syracuseStep 15771619 = 23657429) B23657429
theorem B2189297 : Blo 1457548 2189297 := bstep (se 2 (by rfl) ⟨820986, by rfl⟩ : syracuseStep 2189297 = 1641973) B1641973
theorem B2189315 : Blo 1457548 2189315 := bstep (se 1 (by rfl) ⟨1641986, by rfl⟩ : syracuseStep 2189315 = 3283973) B3283973
theorem B5539853 : Blo 1457548 5539853 := bstep (se 3 (by rfl) ⟨1038722, by rfl⟩ : syracuseStep 5539853 = 2077445) B2077445
theorem B4671523 : Blo 1457548 4671523 := bstep (se 1 (by rfl) ⟨3503642, by rfl⟩ : syracuseStep 4671523 = 7007285) B7007285
theorem B4155437 : Blo 1457548 4155437 := bstep (se 3 (by rfl) ⟨779144, by rfl⟩ : syracuseStep 4155437 = 1558289) B1558289
theorem B2459713 : Blo 1457548 2459713 := bstep (se 2 (by rfl) ⟨922392, by rfl⟩ : syracuseStep 2459713 = 1844785) B1844785
theorem B1640515 : Blo 1457548 1640515 := bstep (se 1 (by rfl) ⟨1230386, by rfl⟩ : syracuseStep 1640515 = 2460773) B2460773
theorem B2459747 : Blo 1457548 2459747 := bstep (se 1 (by rfl) ⟨1844810, by rfl⟩ : syracuseStep 2459747 = 3689621) B3689621
theorem B4671587 : Blo 1457548 4671587 := bstep (se 1 (by rfl) ⟨3503690, by rfl⟩ : syracuseStep 4671587 = 7007381) B7007381
theorem B4671665 : Blo 1457548 4671665 := bstep (se 2 (by rfl) ⟨1751874, by rfl⟩ : syracuseStep 4671665 = 3503749) B3503749
theorem B1845443 : Blo 1457548 1845443 := bstep (se 1 (by rfl) ⟨1384082, by rfl⟩ : syracuseStep 1845443 = 2768165) B2768165
theorem B1640659 : Blo 1457548 1640659 := bstep (se 1 (by rfl) ⟨1230494, by rfl⟩ : syracuseStep 1640659 = 2460989) B2460989
theorem B2459875 : Blo 1457548 2459875 := bstep (se 1 (by rfl) ⟨1844906, by rfl⟩ : syracuseStep 2459875 = 3689813) B3689813
theorem B4155619 : Blo 1457548 4155619 := bstep (se 1 (by rfl) ⟨3116714, by rfl⟩ : syracuseStep 4155619 = 6233429) B6233429
theorem B3115331 : Blo 1457548 3115331 := bstep (se 1 (by rfl) ⟨2336498, by rfl⟩ : syracuseStep 3115331 = 4672997) B4672997
theorem B1640803 : Blo 1457548 1640803 := bstep (se 1 (by rfl) ⟨1230602, by rfl⟩ : syracuseStep 1640803 = 2461205) B2461205
theorem B2460017 : Blo 1457548 2460017 := bstep (se 2 (by rfl) ⟨922506, by rfl⟩ : syracuseStep 2460017 = 1845013) B1845013
theorem B4155779 : Blo 1457548 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B7383473 : Blo 1457548 7383473 := bstep (se 2 (by rfl) ⟨2768802, by rfl⟩ : syracuseStep 7383473 = 5537605) B5537605
theorem B2337203 : Blo 1457548 2337203 := bstep (se 1 (by rfl) ⟨1752902, by rfl⟩ : syracuseStep 2337203 = 3505805) B3505805
theorem B4925933 : Blo 1457548 4925933 := bstep (se 3 (by rfl) ⟨923612, by rfl⟩ : syracuseStep 4925933 = 1847225) B1847225
theorem B2460145 : Blo 1457548 2460145 := bstep (se 2 (by rfl) ⟨922554, by rfl⟩ : syracuseStep 2460145 = 1845109) B1845109
theorem B1640947 : Blo 1457548 1640947 := bstep (se 1 (by rfl) ⟨1230710, by rfl⟩ : syracuseStep 1640947 = 2461421) B2461421
theorem B2460179 : Blo 1457548 2460179 := bstep (se 1 (by rfl) ⟨1845134, by rfl⟩ : syracuseStep 2460179 = 3690269) B3690269
theorem B2337331 : Blo 1457548 2337331 := bstep (se 1 (by rfl) ⟨1752998, by rfl⟩ : syracuseStep 2337331 = 3505997) B3505997
theorem B3279491 : Blo 1457548 3279491 := bstep (se 1 (by rfl) ⟨2459618, by rfl⟩ : syracuseStep 3279491 = 4919237) B4919237
theorem B1641091 : Blo 1457548 1641091 := bstep (se 1 (by rfl) ⟨1230818, by rfl⟩ : syracuseStep 1641091 = 2461637) B2461637
theorem B3328643 : Blo 1457548 3328643 := bstep (se 1 (by rfl) ⟨2496482, by rfl⟩ : syracuseStep 3328643 = 4992965) B4992965
theorem B2460307 : Blo 1457548 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B2337473 : Blo 1457548 2337473 := bstep (se 2 (by rfl) ⟨876552, by rfl⟩ : syracuseStep 2337473 = 1753105) B1753105
theorem B2075395 : Blo 1457548 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1641235 : Blo 1457548 1641235 := bstep (se 1 (by rfl) ⟨1230926, by rfl⟩ : syracuseStep 1641235 = 2461853) B2461853
theorem B59894549 : Blo 1457548 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B2460449 : Blo 1457548 2460449 := bstep (se 2 (by rfl) ⟨922668, by rfl⟩ : syracuseStep 2460449 = 1845337) B1845337
theorem B1846147 : Blo 1457548 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B3279761 : Blo 1457548 3279761 := bstep (se 2 (by rfl) ⟨1229910, by rfl⟩ : syracuseStep 3279761 = 2459821) B2459821
theorem B3115921 : Blo 1457548 3115921 := bstep (se 2 (by rfl) ⟨1168470, by rfl⟩ : syracuseStep 3115921 = 2336941) B2336941
theorem B2460577 : Blo 1457548 2460577 := bstep (se 2 (by rfl) ⟨922716, by rfl⟩ : syracuseStep 2460577 = 1845433) B1845433
theorem B3279779 : Blo 1457548 3279779 := bstep (se 1 (by rfl) ⟨2459834, by rfl⟩ : syracuseStep 3279779 = 4919669) B4919669
theorem B1641379 : Blo 1457548 1641379 := bstep (se 1 (by rfl) ⟨1231034, by rfl⟩ : syracuseStep 1641379 = 2462069) B2462069
theorem B2460611 : Blo 1457548 2460611 := bstep (se 1 (by rfl) ⟨1845458, by rfl⟩ : syracuseStep 2460611 = 3690917) B3690917
theorem B5254093 : Blo 1457548 5254093 := bstep (se 3 (by rfl) ⟨985142, by rfl⟩ : syracuseStep 5254093 = 1970285) B1970285
theorem B9350093 : Blo 1457548 9350093 := bstep (se 3 (by rfl) ⟨1753142, by rfl⟩ : syracuseStep 9350093 = 3506285) B3506285
theorem B2337761 : Blo 1457548 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B1846243 : Blo 1457548 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B3689489 : Blo 1457548 3689489 := bstep (se 2 (by rfl) ⟨1383558, by rfl⟩ : syracuseStep 3689489 = 2767117) B2767117
theorem B8866865 : Blo 1457548 8866865 := bstep (se 2 (by rfl) ⟨3325074, by rfl⟩ : syracuseStep 8866865 = 6650149) B6650149
theorem B1641523 : Blo 1457548 1641523 := bstep (se 1 (by rfl) ⟨1231142, by rfl⟩ : syracuseStep 1641523 = 2462285) B2462285
theorem B2460739 : Blo 1457548 2460739 := bstep (se 1 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 2460739 = 3691109) B3691109
theorem B2493587 : Blo 1457548 2493587 := bstep (se 1 (by rfl) ⟨1870190, by rfl⟩ : syracuseStep 2493587 = 3740381) B3740381
theorem B3943597 : Blo 1457548 3943597 := bstep (se 3 (by rfl) ⟨739424, by rfl⟩ : syracuseStep 3943597 = 1478849) B1478849
theorem B3280049 : Blo 1457548 3280049 := bstep (se 2 (by rfl) ⟨1230018, by rfl⟩ : syracuseStep 3280049 = 2460037) B2460037
theorem B3280067 : Blo 1457548 3280067 := bstep (se 1 (by rfl) ⟨2460050, by rfl⟩ : syracuseStep 3280067 = 4920101) B4920101
theorem B1641667 : Blo 1457548 1641667 := bstep (se 1 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 1641667 = 2462501) B2462501
theorem B2460881 : Blo 1457548 2460881 := bstep (se 2 (by rfl) ⟨922830, by rfl⟩ : syracuseStep 2460881 = 1845661) B1845661
theorem B2075873 : Blo 1457548 2075873 := bstep (se 2 (by rfl) ⟨778452, by rfl⟩ : syracuseStep 2075873 = 1556905) B1556905
theorem B2461009 : Blo 1457548 2461009 := bstep (se 2 (by rfl) ⟨922878, by rfl⟩ : syracuseStep 2461009 = 1845757) B1845757
theorem B2075987 : Blo 1457548 2075987 := bstep (se 1 (by rfl) ⟨1556990, by rfl⟩ : syracuseStep 2075987 = 3113981) B3113981
theorem B1641811 : Blo 1457548 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B2461043 : Blo 1457548 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B2076067 : Blo 1457548 2076067 := bstep (se 1 (by rfl) ⟨1557050, by rfl⟩ : syracuseStep 2076067 = 3114101) B3114101
theorem B3280337 : Blo 1457548 3280337 := bstep (se 2 (by rfl) ⟨1230126, by rfl⟩ : syracuseStep 3280337 = 2460253) B2460253
theorem B1846739 : Blo 1457548 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B3280355 : Blo 1457548 3280355 := bstep (se 1 (by rfl) ⟨2460266, by rfl⟩ : syracuseStep 3280355 = 4920533) B4920533
theorem B1641955 : Blo 1457548 1641955 := bstep (se 1 (by rfl) ⟨1231466, by rfl⟩ : syracuseStep 1641955 = 2462933) B2462933
theorem B2461171 : Blo 1457548 2461171 := bstep (se 1 (by rfl) ⟨1845878, by rfl⟩ : syracuseStep 2461171 = 3691757) B3691757
theorem B4435469 : Blo 1457548 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B4992529 : Blo 1457548 4992529 := bstep (se 2 (by rfl) ⟨1872198, by rfl⟩ : syracuseStep 4992529 = 3744397) B3744397
theorem B2493985 : Blo 1457548 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B31551029 : Blo 1457548 31551029 := bstep (se 5 (by rfl) ⟨1478954, by rfl⟩ : syracuseStep 31551029 = 2957909) B2957909
theorem B2461313 : Blo 1457548 2461313 := bstep (se 2 (by rfl) ⟨922992, by rfl⟩ : syracuseStep 2461313 = 1845985) B1845985
theorem B3280625 : Blo 1457548 3280625 := bstep (se 2 (by rfl) ⟨1230234, by rfl⟩ : syracuseStep 3280625 = 2460469) B2460469
theorem B2461441 : Blo 1457548 2461441 := bstep (se 2 (by rfl) ⟨923040, by rfl⟩ : syracuseStep 2461441 = 1846081) B1846081
theorem B3280643 : Blo 1457548 3280643 := bstep (se 1 (by rfl) ⟨2460482, by rfl⟩ : syracuseStep 3280643 = 4920965) B4920965
theorem B1969939 : Blo 1457548 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B2461475 : Blo 1457548 2461475 := bstep (se 1 (by rfl) ⟨1846106, by rfl⟩ : syracuseStep 2461475 = 3692213) B3692213
theorem B7384931 : Blo 1457548 7384931 := bstep (se 1 (by rfl) ⟨5538698, by rfl⟩ : syracuseStep 7384931 = 11077397) B11077397
theorem B2461603 : Blo 1457548 2461603 := bstep (se 1 (by rfl) ⟨1846202, by rfl⟩ : syracuseStep 2461603 = 3692405) B3692405
theorem B2494403 : Blo 1457548 2494403 := bstep (se 1 (by rfl) ⟨1870802, by rfl⟩ : syracuseStep 2494403 = 3741605) B3741605
theorem B2076625 : Blo 1457548 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B7008227 : Blo 1457548 7008227 := bstep (se 1 (by rfl) ⟨5256170, by rfl⟩ : syracuseStep 7008227 = 10512341) B10512341
theorem B3690481 : Blo 1457548 3690481 := bstep (se 2 (by rfl) ⟨1383930, by rfl⟩ : syracuseStep 3690481 = 2767861) B2767861
theorem B3280913 : Blo 1457548 3280913 := bstep (se 2 (by rfl) ⟨1230342, by rfl⟩ : syracuseStep 3280913 = 2460685) B2460685
theorem B3280931 : Blo 1457548 3280931 := bstep (se 1 (by rfl) ⟨2460698, by rfl⟩ : syracuseStep 3280931 = 4921397) B4921397
theorem B4919345 : Blo 1457548 4919345 := bstep (se 2 (by rfl) ⟨1844754, by rfl⟩ : syracuseStep 4919345 = 3689509) B3689509
theorem B2494513 : Blo 1457548 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B2461745 : Blo 1457548 2461745 := bstep (se 2 (by rfl) ⟨923154, by rfl⟩ : syracuseStep 2461745 = 1846309) B1846309
theorem B4673585 : Blo 1457548 4673585 := bstep (se 2 (by rfl) ⟨1752594, by rfl⟩ : syracuseStep 4673585 = 3505189) B3505189
theorem B14020721 : Blo 1457548 14020721 := bstep (se 2 (by rfl) ⟨5257770, by rfl⟩ : syracuseStep 14020721 = 10515541) B10515541
theorem B2461873 : Blo 1457548 2461873 := bstep (se 2 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 2461873 = 1846405) B1846405
theorem B2461907 : Blo 1457548 2461907 := bstep (se 1 (by rfl) ⟨1846430, by rfl⟩ : syracuseStep 2461907 = 3692861) B3692861
theorem B3690755 : Blo 1457548 3690755 := bstep (se 1 (by rfl) ⟨2768066, by rfl⟩ : syracuseStep 3690755 = 5536133) B5536133
theorem B3281201 : Blo 1457548 3281201 := bstep (se 2 (by rfl) ⟨1230450, by rfl⟩ : syracuseStep 3281201 = 2460901) B2460901
theorem B3281219 : Blo 1457548 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B2462035 : Blo 1457548 2462035 := bstep (se 1 (by rfl) ⟨1846526, by rfl⟩ : syracuseStep 2462035 = 3693053) B3693053
theorem B2216371 : Blo 1457548 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B3690947 : Blo 1457548 3690947 := bstep (se 1 (by rfl) ⟨2768210, by rfl⟩ : syracuseStep 3690947 = 5536421) B5536421
theorem B2462177 : Blo 1457548 2462177 := bstep (se 2 (by rfl) ⟨923316, by rfl⟩ : syracuseStep 2462177 = 1846633) B1846633
theorem B3502595 : Blo 1457548 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B4919885 : Blo 1457548 4919885 := bstep (se 3 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 4919885 = 1844957) B1844957
theorem B4674125 : Blo 1457548 4674125 := bstep (se 3 (by rfl) ⟨876398, by rfl⟩ : syracuseStep 4674125 = 1752797) B1752797
theorem B3281489 : Blo 1457548 3281489 := bstep (se 2 (by rfl) ⟨1230558, by rfl⟩ : syracuseStep 3281489 = 2461117) B2461117
theorem B2462305 : Blo 1457548 2462305 := bstep (se 2 (by rfl) ⟨923364, by rfl⟩ : syracuseStep 2462305 = 1846729) B1846729
theorem B3281507 : Blo 1457548 3281507 := bstep (se 1 (by rfl) ⟨2461130, by rfl⟩ : syracuseStep 3281507 = 4922261) B4922261
theorem B6230627 : Blo 1457548 6230627 := bstep (se 1 (by rfl) ⟨4672970, by rfl⟩ : syracuseStep 6230627 = 9345941) B9345941
theorem B4919939 : Blo 1457548 4919939 := bstep (se 1 (by rfl) ⟨3689954, by rfl⟩ : syracuseStep 4919939 = 7379909) B7379909
theorem B2462339 : Blo 1457548 2462339 := bstep (se 1 (by rfl) ⟨1846754, by rfl⟩ : syracuseStep 2462339 = 3693509) B3693509
theorem B5911181 : Blo 1457548 5911181 := bstep (se 3 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 5911181 = 2216693) B2216693
theorem B7385741 : Blo 1457548 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B2077331 : Blo 1457548 2077331 := bstep (se 1 (by rfl) ⟨1557998, by rfl⟩ : syracuseStep 2077331 = 3115997) B3115997
theorem B17994421 : Blo 1457548 17994421 := bstep (se 5 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 17994421 = 1686977) B1686977
theorem B2462467 : Blo 1457548 2462467 := bstep (se 1 (by rfl) ⟨1846850, by rfl⟩ : syracuseStep 2462467 = 3693701) B3693701
theorem B5534477 : Blo 1457548 5534477 := bstep (se 3 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 5534477 = 2075429) B2075429
theorem B1970977 : Blo 1457548 1970977 := bstep (se 2 (by rfl) ⟨739116, by rfl⟩ : syracuseStep 1970977 = 1478233) B1478233
theorem B3199843 : Blo 1457548 3199843 := bstep (se 1 (by rfl) ⟨2399882, by rfl⟩ : syracuseStep 3199843 = 4799765) B4799765
theorem B3281777 : Blo 1457548 3281777 := bstep (se 2 (by rfl) ⟨1230666, by rfl⟩ : syracuseStep 3281777 = 2461333) B2461333
theorem B3281795 : Blo 1457548 3281795 := bstep (se 1 (by rfl) ⟨2461346, by rfl⟩ : syracuseStep 3281795 = 4922693) B4922693
theorem B8311693 : Blo 1457548 8311693 := bstep (se 3 (by rfl) ⟨1558442, by rfl⟩ : syracuseStep 8311693 = 3116885) B3116885
theorem B4920209 : Blo 1457548 4920209 := bstep (se 2 (by rfl) ⟨1845078, by rfl⟩ : syracuseStep 4920209 = 3690157) B3690157
theorem B2462609 : Blo 1457548 2462609 := bstep (se 2 (by rfl) ⟨923478, by rfl⟩ : syracuseStep 2462609 = 1846957) B1846957
theorem B2339777 : Blo 1457548 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B5616611 : Blo 1457548 5616611 := bstep (se 1 (by rfl) ⟨4212458, by rfl⟩ : syracuseStep 5616611 = 8424917) B8424917
theorem B9974789 : Blo 1457548 9974789 := bstep (se 4 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 9974789 = 1870273) B1870273
theorem B2462737 : Blo 1457548 2462737 := bstep (se 2 (by rfl) ⟨923526, by rfl⟩ : syracuseStep 2462737 = 1847053) B1847053
theorem B2528275 : Blo 1457548 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B5256227 : Blo 1457548 5256227 := bstep (se 1 (by rfl) ⟨3942170, by rfl⟩ : syracuseStep 5256227 = 7884341) B7884341
theorem B2462771 : Blo 1457548 2462771 := bstep (se 1 (by rfl) ⟨1847078, by rfl⟩ : syracuseStep 2462771 = 3694157) B3694157
theorem B3282065 : Blo 1457548 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B3503267 : Blo 1457548 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B3282083 : Blo 1457548 3282083 := bstep (se 1 (by rfl) ⟨2461562, by rfl⟩ : syracuseStep 3282083 = 4923125) B4923125
theorem B2462899 : Blo 1457548 2462899 := bstep (se 1 (by rfl) ⟨1847174, by rfl⟩ : syracuseStep 2462899 = 3694349) B3694349
theorem B8869105 : Blo 1457548 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B2077969 : Blo 1457548 2077969 := bstep (se 2 (by rfl) ⟨779238, by rfl⟩ : syracuseStep 2077969 = 1558477) B1558477
theorem B2495777 : Blo 1457548 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B4437325 : Blo 1457548 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B3691889 : Blo 1457548 3691889 := bstep (se 2 (by rfl) ⟨1384458, by rfl⟩ : syracuseStep 3691889 = 2768917) B2768917
theorem B2078083 : Blo 1457548 2078083 := bstep (se 1 (by rfl) ⟨1558562, by rfl⟩ : syracuseStep 2078083 = 3117125) B3117125
theorem B18691469 : Blo 1457548 18691469 := bstep (se 3 (by rfl) ⟨3504650, by rfl⟩ : syracuseStep 18691469 = 7009301) B7009301
theorem B3691939 : Blo 1457548 3691939 := bstep (se 1 (by rfl) ⟨2768954, by rfl⟩ : syracuseStep 3691939 = 5537909) B5537909
theorem B4920749 : Blo 1457548 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B3503537 : Blo 1457548 3503537 := bstep (se 2 (by rfl) ⟨1313826, by rfl⟩ : syracuseStep 3503537 = 2627653) B2627653
theorem B3282353 : Blo 1457548 3282353 := bstep (se 2 (by rfl) ⟨1230882, by rfl⟩ : syracuseStep 3282353 = 2461765) B2461765
theorem B3282371 : Blo 1457548 3282371 := bstep (se 1 (by rfl) ⟨2461778, by rfl⟩ : syracuseStep 3282371 = 4923557) B4923557
theorem B4920803 : Blo 1457548 4920803 := bstep (se 1 (by rfl) ⟨3690602, by rfl⟩ : syracuseStep 4920803 = 7381205) B7381205
theorem B9344483 : Blo 1457548 9344483 := bstep (se 1 (by rfl) ⟨7008362, by rfl⟩ : syracuseStep 9344483 = 14016725) B14016725
theorem B3692081 : Blo 1457548 3692081 := bstep (se 2 (by rfl) ⟨1384530, by rfl⟩ : syracuseStep 3692081 = 2769061) B2769061
theorem B7009841 : Blo 1457548 7009841 := bstep (se 2 (by rfl) ⟨2628690, by rfl⟩ : syracuseStep 7009841 = 5257381) B5257381
theorem B2217539 : Blo 1457548 2217539 := bstep (se 1 (by rfl) ⟨1663154, by rfl⟩ : syracuseStep 2217539 = 3326309) B3326309
theorem B11081285 : Blo 1457548 11081285 := bstep (se 4 (by rfl) ⟨1038870, by rfl⟩ : syracuseStep 11081285 = 2077741) B2077741
theorem B3503729 : Blo 1457548 3503729 := bstep (se 2 (by rfl) ⟨1313898, by rfl⟩ : syracuseStep 3503729 = 2627797) B2627797
theorem B3503825 : Blo 1457548 3503825 := bstep (se 2 (by rfl) ⟨1313934, by rfl⟩ : syracuseStep 3503825 = 2627869) B2627869
theorem B3282641 : Blo 1457548 3282641 := bstep (se 2 (by rfl) ⟨1230990, by rfl⟩ : syracuseStep 3282641 = 2461981) B2461981
theorem B3282659 : Blo 1457548 3282659 := bstep (se 1 (by rfl) ⟨2461994, by rfl⟩ : syracuseStep 3282659 = 4923989) B4923989
theorem B4921073 : Blo 1457548 4921073 := bstep (se 2 (by rfl) ⟨1845402, by rfl⟩ : syracuseStep 4921073 = 3690805) B3690805
theorem B4151245 : Blo 1457548 4151245 := bstep (se 3 (by rfl) ⟨778358, by rfl⟩ : syracuseStep 4151245 = 1556717) B1556717
theorem B3282929 : Blo 1457548 3282929 := bstep (se 2 (by rfl) ⟨1231098, by rfl⟩ : syracuseStep 3282929 = 2462197) B2462197
theorem B3282947 : Blo 1457548 3282947 := bstep (se 1 (by rfl) ⟨2462210, by rfl⟩ : syracuseStep 3282947 = 4924421) B4924421
theorem B6649933 : Blo 1457548 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B4151405 : Blo 1457548 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B4921613 : Blo 1457548 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B3283217 : Blo 1457548 3283217 := bstep (se 2 (by rfl) ⟨1231206, by rfl⟩ : syracuseStep 3283217 = 2462413) B2462413
theorem B4151587 : Blo 1457548 4151587 := bstep (se 1 (by rfl) ⟨3113690, by rfl⟩ : syracuseStep 4151587 = 6227381) B6227381
theorem B3283235 : Blo 1457548 3283235 := bstep (se 1 (by rfl) ⟨2462426, by rfl⟩ : syracuseStep 3283235 = 4924853) B4924853
theorem B4921667 : Blo 1457548 4921667 := bstep (se 1 (by rfl) ⟨3691250, by rfl⟩ : syracuseStep 4921667 = 7382501) B7382501
theorem B3004913 : Blo 1457548 3004913 := bstep (se 2 (by rfl) ⟨1126842, by rfl⟩ : syracuseStep 3004913 = 2253685) B2253685
theorem B3693073 : Blo 1457548 3693073 := bstep (se 2 (by rfl) ⟨1384902, by rfl⟩ : syracuseStep 3693073 = 2769805) B2769805
theorem B2955811 : Blo 1457548 2955811 := bstep (se 1 (by rfl) ⟨2216858, by rfl⟩ : syracuseStep 2955811 = 4433717) B4433717
theorem B3283505 : Blo 1457548 3283505 := bstep (se 2 (by rfl) ⟨1231314, by rfl⟩ : syracuseStep 3283505 = 2462629) B2462629
theorem B3283523 : Blo 1457548 3283523 := bstep (se 1 (by rfl) ⟨2462642, by rfl⟩ : syracuseStep 3283523 = 4925285) B4925285
theorem B4921937 : Blo 1457548 4921937 := bstep (se 2 (by rfl) ⟨1845726, by rfl⟩ : syracuseStep 4921937 = 3691453) B3691453
theorem B2767459 : Blo 1457548 2767459 := bstep (se 1 (by rfl) ⟨2075594, by rfl⟩ : syracuseStep 2767459 = 4151189) B4151189
theorem B7379747 : Blo 1457548 7379747 := bstep (se 1 (by rfl) ⟨5534810, by rfl⟩ : syracuseStep 7379747 = 11069621) B11069621
theorem B3693347 : Blo 1457548 3693347 := bstep (se 1 (by rfl) ⟨2770010, by rfl⟩ : syracuseStep 3693347 = 5540021) B5540021
theorem B2530099 : Blo 1457548 2530099 := bstep (se 1 (by rfl) ⟨1897574, by rfl⟩ : syracuseStep 2530099 = 3795149) B3795149
theorem B3283793 : Blo 1457548 3283793 := bstep (se 2 (by rfl) ⟨1231422, by rfl⟩ : syracuseStep 3283793 = 2462845) B2462845
theorem B14023523 : Blo 1457548 14023523 := bstep (se 1 (by rfl) ⟨10517642, by rfl⟩ : syracuseStep 14023523 = 21035285) B21035285
theorem B3283811 : Blo 1457548 3283811 := bstep (se 1 (by rfl) ⟨2462858, by rfl⟩ : syracuseStep 3283811 = 4925717) B4925717
theorem B3505027 : Blo 1457548 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B3693539 : Blo 1457548 3693539 := bstep (se 1 (by rfl) ⟨2770154, by rfl⟩ : syracuseStep 3693539 = 5540309) B5540309
theorem B16833521 : Blo 1457548 16833521 := bstep (se 2 (by rfl) ⟨6312570, by rfl⟩ : syracuseStep 16833521 = 12625141) B12625141
theorem B2767907 : Blo 1457548 2767907 := bstep (se 1 (by rfl) ⟨2075930, by rfl⟩ : syracuseStep 2767907 = 4151861) B4151861
theorem B4799569 : Blo 1457548 4799569 := bstep (se 2 (by rfl) ⟨1799838, by rfl⟩ : syracuseStep 4799569 = 3599677) B3599677
theorem B2186339 : Blo 1457548 2186339 := bstep (se 1 (by rfl) ⟨1639754, by rfl⟩ : syracuseStep 2186339 = 3279509) B3279509
theorem B16612451 : Blo 1457548 16612451 := bstep (se 1 (by rfl) ⟨12459338, by rfl⟩ : syracuseStep 16612451 = 24918677) B24918677
theorem B4922477 : Blo 1457548 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B2186369 : Blo 1457548 2186369 := bstep (se 2 (by rfl) ⟨819888, by rfl⟩ : syracuseStep 2186369 = 1639777) B1639777
theorem B2186387 : Blo 1457548 2186387 := bstep (se 1 (by rfl) ⟨1639790, by rfl⟩ : syracuseStep 2186387 = 3279581) B3279581
theorem B4922531 : Blo 1457548 4922531 := bstep (se 1 (by rfl) ⟨3691898, by rfl⟩ : syracuseStep 4922531 = 7383797) B7383797
theorem B2186417 : Blo 1457548 2186417 := bstep (se 2 (by rfl) ⟨819906, by rfl⟩ : syracuseStep 2186417 = 1639813) B1639813
theorem B2186435 : Blo 1457548 2186435 := bstep (se 1 (by rfl) ⟨1639826, by rfl⟩ : syracuseStep 2186435 = 3279653) B3279653
theorem B8305861 : Blo 1457548 8305861 := bstep (se 4 (by rfl) ⟨778674, by rfl⟩ : syracuseStep 8305861 = 1557349) B1557349
theorem B2186465 : Blo 1457548 2186465 := bstep (se 2 (by rfl) ⟨819924, by rfl⟩ : syracuseStep 2186465 = 1639849) B1639849
theorem B7584995 : Blo 1457548 7584995 := bstep (se 1 (by rfl) ⟨5688746, by rfl⟩ : syracuseStep 7584995 = 11377493) B11377493
theorem B2186483 : Blo 1457548 2186483 := bstep (se 1 (by rfl) ⟨1639862, by rfl⟩ : syracuseStep 2186483 = 3279725) B3279725
theorem B2186513 : Blo 1457548 2186513 := bstep (se 2 (by rfl) ⟨819942, by rfl⟩ : syracuseStep 2186513 = 1639885) B1639885
theorem B2186531 : Blo 1457548 2186531 := bstep (se 1 (by rfl) ⟨1639898, by rfl⟩ : syracuseStep 2186531 = 3279797) B3279797
theorem B4209965 : Blo 1457548 4209965 := bstep (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) B1578737
theorem B2186561 : Blo 1457548 2186561 := bstep (se 2 (by rfl) ⟨819960, by rfl⟩ : syracuseStep 2186561 = 1639921) B1639921
theorem B2768195 : Blo 1457548 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B2186579 : Blo 1457548 2186579 := bstep (se 1 (by rfl) ⟨1639934, by rfl⟩ : syracuseStep 2186579 = 3279869) B3279869
theorem B14974307 : Blo 1457548 14974307 := bstep (se 1 (by rfl) ⟨11230730, by rfl⟩ : syracuseStep 14974307 = 22461461) B22461461
theorem B2186609 : Blo 1457548 2186609 := bstep (se 2 (by rfl) ⟨819978, by rfl⟩ : syracuseStep 2186609 = 1639957) B1639957
theorem B12631409 : Blo 1457548 12631409 := bstep (se 2 (by rfl) ⟨4736778, by rfl⟩ : syracuseStep 12631409 = 9473557) B9473557
theorem B2186627 : Blo 1457548 2186627 := bstep (se 1 (by rfl) ⟨1639970, by rfl⟩ : syracuseStep 2186627 = 3279941) B3279941
theorem B1457555 : Blo 1457548 1457555 := bstep (se 1 (by rfl) ⟨1093166, by rfl⟩ : syracuseStep 1457555 = 2186333) B2186333
theorem B2186657 : Blo 1457548 2186657 := bstep (se 2 (by rfl) ⟨819996, by rfl⟩ : syracuseStep 2186657 = 1639993) B1639993
theorem B1457571 : Blo 1457548 1457571 := bstep (se 1 (by rfl) ⟨1093178, by rfl⟩ : syracuseStep 1457571 = 2186357) B2186357
theorem B4922801 : Blo 1457548 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B1457587 : Blo 1457548 1457587 := bstep (se 1 (by rfl) ⟨1093190, by rfl⟩ : syracuseStep 1457587 = 2186381) B2186381
theorem B2186675 : Blo 1457548 2186675 := bstep (se 1 (by rfl) ⟨1640006, by rfl⟩ : syracuseStep 2186675 = 3280013) B3280013
theorem B1457603 : Blo 1457548 1457603 := bstep (se 1 (by rfl) ⟨1093202, by rfl⟩ : syracuseStep 1457603 = 2186405) B2186405
theorem B2186705 : Blo 1457548 2186705 := bstep (se 2 (by rfl) ⟨820014, by rfl⟩ : syracuseStep 2186705 = 1640029) B1640029
theorem B1457619 : Blo 1457548 1457619 := bstep (se 1 (by rfl) ⟨1093214, by rfl⟩ : syracuseStep 1457619 = 2186429) B2186429
theorem B1457635 : Blo 1457548 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B2186723 : Blo 1457548 2186723 := bstep (se 1 (by rfl) ⟨1640042, by rfl⟩ : syracuseStep 2186723 = 3280085) B3280085
theorem B7388657 : Blo 1457548 7388657 := bstep (se 2 (by rfl) ⟨2770746, by rfl⟩ : syracuseStep 7388657 = 5541493) B5541493
theorem B1457651 : Blo 1457548 1457651 := bstep (se 1 (by rfl) ⟨1093238, by rfl⟩ : syracuseStep 1457651 = 2186477) B2186477
theorem B2186753 : Blo 1457548 2186753 := bstep (se 2 (by rfl) ⟨820032, by rfl⟩ : syracuseStep 2186753 = 1640065) B1640065
theorem B1457667 : Blo 1457548 1457667 := bstep (se 1 (by rfl) ⟨1093250, by rfl⟩ : syracuseStep 1457667 = 2186501) B2186501
theorem B1457683 : Blo 1457548 1457683 := bstep (se 1 (by rfl) ⟨1093262, by rfl⟩ : syracuseStep 1457683 = 2186525) B2186525
theorem B2186771 : Blo 1457548 2186771 := bstep (se 1 (by rfl) ⟨1640078, by rfl⟩ : syracuseStep 2186771 = 3280157) B3280157
theorem B1457699 : Blo 1457548 1457699 := bstep (se 1 (by rfl) ⟨1093274, by rfl⟩ : syracuseStep 1457699 = 2186549) B2186549
theorem B2186801 : Blo 1457548 2186801 := bstep (se 2 (by rfl) ⟨820050, by rfl⟩ : syracuseStep 2186801 = 1640101) B1640101
theorem B1457715 : Blo 1457548 1457715 := bstep (se 1 (by rfl) ⟨1093286, by rfl⟩ : syracuseStep 1457715 = 2186573) B2186573
theorem B1457731 : Blo 1457548 1457731 := bstep (se 1 (by rfl) ⟨1093298, by rfl⟩ : syracuseStep 1457731 = 2186597) B2186597
theorem B2186819 : Blo 1457548 2186819 := bstep (se 1 (by rfl) ⟨1640114, by rfl⟩ : syracuseStep 2186819 = 3280229) B3280229
theorem B7380557 : Blo 1457548 7380557 := bstep (se 3 (by rfl) ⟨1383854, by rfl⟩ : syracuseStep 7380557 = 2767709) B2767709
theorem B7011917 : Blo 1457548 7011917 := bstep (se 3 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 7011917 = 2629469) B2629469
theorem B1457747 : Blo 1457548 1457747 := bstep (se 1 (by rfl) ⟨1093310, by rfl⟩ : syracuseStep 1457747 = 2186621) B2186621
theorem B2186849 : Blo 1457548 2186849 := bstep (se 2 (by rfl) ⟨820068, by rfl⟩ : syracuseStep 2186849 = 1640137) B1640137
theorem B1457763 : Blo 1457548 1457763 := bstep (se 1 (by rfl) ⟨1093322, by rfl⟩ : syracuseStep 1457763 = 2186645) B2186645
theorem B5537393 : Blo 1457548 5537393 := bstep (se 2 (by rfl) ⟨2076522, by rfl⟩ : syracuseStep 5537393 = 4153045) B4153045
theorem B1457779 : Blo 1457548 1457779 := bstep (se 1 (by rfl) ⟨1093334, by rfl⟩ : syracuseStep 1457779 = 2186669) B2186669
theorem B2186867 : Blo 1457548 2186867 := bstep (se 1 (by rfl) ⟨1640150, by rfl⟩ : syracuseStep 2186867 = 3280301) B3280301
theorem B1457795 : Blo 1457548 1457795 := bstep (se 1 (by rfl) ⟨1093346, by rfl⟩ : syracuseStep 1457795 = 2186693) B2186693
theorem B2186897 : Blo 1457548 2186897 := bstep (se 2 (by rfl) ⟨820086, by rfl⟩ : syracuseStep 2186897 = 1640173) B1640173
theorem B4152977 : Blo 1457548 4152977 := bstep (se 2 (by rfl) ⟨1557366, by rfl⟩ : syracuseStep 4152977 = 3114733) B3114733
theorem B1457811 : Blo 1457548 1457811 := bstep (se 1 (by rfl) ⟨1093358, by rfl⟩ : syracuseStep 1457811 = 2186717) B2186717
theorem B1457827 : Blo 1457548 1457827 := bstep (se 1 (by rfl) ⟨1093370, by rfl⟩ : syracuseStep 1457827 = 2186741) B2186741
theorem B2186915 : Blo 1457548 2186915 := bstep (se 1 (by rfl) ⟨1640186, by rfl⟩ : syracuseStep 2186915 = 3280373) B3280373
theorem B1457843 : Blo 1457548 1457843 := bstep (se 1 (by rfl) ⟨1093382, by rfl⟩ : syracuseStep 1457843 = 2186765) B2186765
theorem B2186945 : Blo 1457548 2186945 := bstep (se 2 (by rfl) ⟨820104, by rfl⟩ : syracuseStep 2186945 = 1640209) B1640209
theorem B1457859 : Blo 1457548 1457859 := bstep (se 1 (by rfl) ⟨1093394, by rfl⟩ : syracuseStep 1457859 = 2186789) B2186789
theorem B1457875 : Blo 1457548 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B2186963 : Blo 1457548 2186963 := bstep (se 1 (by rfl) ⟨1640222, by rfl⟩ : syracuseStep 2186963 = 3280445) B3280445
theorem B1752787 : Blo 1457548 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B1457891 : Blo 1457548 1457891 := bstep (se 1 (by rfl) ⟨1093418, by rfl⟩ : syracuseStep 1457891 = 2186837) B2186837
theorem B2186993 : Blo 1457548 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B1457907 : Blo 1457548 1457907 := bstep (se 1 (by rfl) ⟨1093430, by rfl⟩ : syracuseStep 1457907 = 2186861) B2186861
theorem B1457923 : Blo 1457548 1457923 := bstep (se 1 (by rfl) ⟨1093442, by rfl⟩ : syracuseStep 1457923 = 2186885) B2186885
theorem B2187011 : Blo 1457548 2187011 := bstep (se 1 (by rfl) ⟨1640258, by rfl⟩ : syracuseStep 2187011 = 3280517) B3280517
theorem B1457939 : Blo 1457548 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B2187041 : Blo 1457548 2187041 := bstep (se 2 (by rfl) ⟨820140, by rfl⟩ : syracuseStep 2187041 = 1640281) B1640281
theorem B1457955 : Blo 1457548 1457955 := bstep (se 1 (by rfl) ⟨1093466, by rfl⟩ : syracuseStep 1457955 = 2186933) B2186933
theorem B1457971 : Blo 1457548 1457971 := bstep (se 1 (by rfl) ⟨1093478, by rfl⟩ : syracuseStep 1457971 = 2186957) B2186957
theorem B2187059 : Blo 1457548 2187059 := bstep (se 1 (by rfl) ⟨1640294, by rfl⟩ : syracuseStep 2187059 = 3280589) B3280589
theorem B1457987 : Blo 1457548 1457987 := bstep (se 1 (by rfl) ⟨1093490, by rfl⟩ : syracuseStep 1457987 = 2186981) B2186981
theorem B2187089 : Blo 1457548 2187089 := bstep (se 2 (by rfl) ⟨820158, by rfl⟩ : syracuseStep 2187089 = 1640317) B1640317
theorem B1458003 : Blo 1457548 1458003 := bstep (se 1 (by rfl) ⟨1093502, by rfl⟩ : syracuseStep 1458003 = 2187005) B2187005
theorem B1458019 : Blo 1457548 1458019 := bstep (se 1 (by rfl) ⟨1093514, by rfl⟩ : syracuseStep 1458019 = 2187029) B2187029
theorem B2187107 : Blo 1457548 2187107 := bstep (se 1 (by rfl) ⟨1640330, by rfl⟩ : syracuseStep 2187107 = 3280661) B3280661
theorem B1458035 : Blo 1457548 1458035 := bstep (se 1 (by rfl) ⟨1093526, by rfl⟩ : syracuseStep 1458035 = 2187053) B2187053
theorem B2187137 : Blo 1457548 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B1458051 : Blo 1457548 1458051 := bstep (se 1 (by rfl) ⟨1093538, by rfl⟩ : syracuseStep 1458051 = 2187077) B2187077
theorem B3694481 : Blo 1457548 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B1458067 : Blo 1457548 1458067 := bstep (se 1 (by rfl) ⟨1093550, by rfl⟩ : syracuseStep 1458067 = 2187101) B2187101
theorem B2187155 : Blo 1457548 2187155 := bstep (se 1 (by rfl) ⟨1640366, by rfl⟩ : syracuseStep 2187155 = 3280733) B3280733
theorem B1458083 : Blo 1457548 1458083 := bstep (se 1 (by rfl) ⟨1093562, by rfl⟩ : syracuseStep 1458083 = 2187125) B2187125
theorem B2187185 : Blo 1457548 2187185 := bstep (se 2 (by rfl) ⟨820194, by rfl⟩ : syracuseStep 2187185 = 1640389) B1640389
theorem B1458099 : Blo 1457548 1458099 := bstep (se 1 (by rfl) ⟨1093574, by rfl⟩ : syracuseStep 1458099 = 2187149) B2187149
theorem B1458115 : Blo 1457548 1458115 := bstep (se 1 (by rfl) ⟨1093586, by rfl⟩ : syracuseStep 1458115 = 2187173) B2187173
theorem B2187203 : Blo 1457548 2187203 := bstep (se 1 (by rfl) ⟨1640402, by rfl⟩ : syracuseStep 2187203 = 3280805) B3280805
theorem B4923341 : Blo 1457548 4923341 := bstep (se 3 (by rfl) ⟨923126, by rfl⟩ : syracuseStep 4923341 = 1846253) B1846253
theorem B1458131 : Blo 1457548 1458131 := bstep (se 1 (by rfl) ⟨1093598, by rfl⟩ : syracuseStep 1458131 = 2187197) B2187197
theorem B2187233 : Blo 1457548 2187233 := bstep (se 2 (by rfl) ⟨820212, by rfl⟩ : syracuseStep 2187233 = 1640425) B1640425
theorem B1458147 : Blo 1457548 1458147 := bstep (se 1 (by rfl) ⟨1093610, by rfl⟩ : syracuseStep 1458147 = 2187221) B2187221
theorem B1458163 : Blo 1457548 1458163 := bstep (se 1 (by rfl) ⟨1093622, by rfl⟩ : syracuseStep 1458163 = 2187245) B2187245
theorem B2187251 : Blo 1457548 2187251 := bstep (se 1 (by rfl) ⟨1640438, by rfl⟩ : syracuseStep 2187251 = 3280877) B3280877
theorem B1556491 : Blo 1457548 1556491 := bstep (se 1 (by rfl) ⟨1167368, by rfl⟩ : syracuseStep 1556491 = 2334737) B2334737
theorem B2187275 : Blo 1457548 2187275 := bstep (se 1 (by rfl) ⟨1640456, by rfl⟩ : syracuseStep 2187275 = 3280913) B3280913
theorem B1458187 : Blo 1457548 1458187 := bstep (se 1 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 1458187 = 2187281) B2187281
theorem B2187287 : Blo 1457548 2187287 := bstep (se 1 (by rfl) ⟨1640465, by rfl⟩ : syracuseStep 2187287 = 3280931) B3280931
theorem B1458199 : Blo 1457548 1458199 := bstep (se 1 (by rfl) ⟨1093649, by rfl⟩ : syracuseStep 1458199 = 2187299) B2187299
theorem B1458219 : Blo 1457548 1458219 := bstep (se 1 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 1458219 = 2187329) B2187329
theorem B1458231 : Blo 1457548 1458231 := bstep (se 1 (by rfl) ⟨1093673, by rfl⟩ : syracuseStep 1458231 = 2187347) B2187347
theorem B3326017 : Blo 1457548 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B1458251 : Blo 1457548 1458251 := bstep (se 1 (by rfl) ⟨1093688, by rfl⟩ : syracuseStep 1458251 = 2187377) B2187377
theorem B9347147 : Blo 1457548 9347147 := bstep (se 1 (by rfl) ⟨7010360, by rfl⟩ : syracuseStep 9347147 = 14020721) B14020721
theorem B1458263 : Blo 1457548 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B2187353 : Blo 1457548 2187353 := bstep (se 2 (by rfl) ⟨820257, by rfl⟩ : syracuseStep 2187353 = 1640515) B1640515
theorem B1458283 : Blo 1457548 1458283 := bstep (se 1 (by rfl) ⟨1093712, by rfl⟩ : syracuseStep 1458283 = 2187425) B2187425
theorem B1458295 : Blo 1457548 1458295 := bstep (se 1 (by rfl) ⟨1093721, by rfl⟩ : syracuseStep 1458295 = 2187443) B2187443
theorem B8306819 : Blo 1457548 8306819 := bstep (se 1 (by rfl) ⟨6230114, by rfl⟩ : syracuseStep 8306819 = 12460229) B12460229
theorem B1458315 : Blo 1457548 1458315 := bstep (se 1 (by rfl) ⟨1093736, by rfl⟩ : syracuseStep 1458315 = 2187473) B2187473
theorem B1458327 : Blo 1457548 1458327 := bstep (se 1 (by rfl) ⟨1093745, by rfl⟩ : syracuseStep 1458327 = 2187491) B2187491
theorem B1458347 : Blo 1457548 1458347 := bstep (se 1 (by rfl) ⟨1093760, by rfl⟩ : syracuseStep 1458347 = 2187521) B2187521
theorem B1458359 : Blo 1457548 1458359 := bstep (se 1 (by rfl) ⟨1093769, by rfl⟩ : syracuseStep 1458359 = 2187539) B2187539
theorem B2187467 : Blo 1457548 2187467 := bstep (se 1 (by rfl) ⟨1640600, by rfl⟩ : syracuseStep 2187467 = 3281201) B3281201
theorem B1458379 : Blo 1457548 1458379 := bstep (se 1 (by rfl) ⟨1093784, by rfl⟩ : syracuseStep 1458379 = 2187569) B2187569
theorem B2187479 : Blo 1457548 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B1458391 : Blo 1457548 1458391 := bstep (se 1 (by rfl) ⟨1093793, by rfl⟩ : syracuseStep 1458391 = 2187587) B2187587
theorem B1458411 : Blo 1457548 1458411 := bstep (se 1 (by rfl) ⟨1093808, by rfl⟩ : syracuseStep 1458411 = 2187617) B2187617
theorem B1458423 : Blo 1457548 1458423 := bstep (se 1 (by rfl) ⟨1093817, by rfl⟩ : syracuseStep 1458423 = 2187635) B2187635
theorem B1458443 : Blo 1457548 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B1458455 : Blo 1457548 1458455 := bstep (se 1 (by rfl) ⟨1093841, by rfl⟩ : syracuseStep 1458455 = 2187683) B2187683
theorem B2187545 : Blo 1457548 2187545 := bstep (se 2 (by rfl) ⟨820329, by rfl⟩ : syracuseStep 2187545 = 1640659) B1640659
theorem B1458475 : Blo 1457548 1458475 := bstep (se 1 (by rfl) ⟨1093856, by rfl⟩ : syracuseStep 1458475 = 2187713) B2187713
theorem B1458487 : Blo 1457548 1458487 := bstep (se 1 (by rfl) ⟨1093865, by rfl⟩ : syracuseStep 1458487 = 2187731) B2187731
theorem B1458507 : Blo 1457548 1458507 := bstep (se 1 (by rfl) ⟨1093880, by rfl⟩ : syracuseStep 1458507 = 2187761) B2187761
theorem B2335063 : Blo 1457548 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1458519 : Blo 1457548 1458519 := bstep (se 1 (by rfl) ⟨1093889, by rfl⟩ : syracuseStep 1458519 = 2187779) B2187779
theorem B1458539 : Blo 1457548 1458539 := bstep (se 1 (by rfl) ⟨1093904, by rfl⟩ : syracuseStep 1458539 = 2187809) B2187809
theorem B1458551 : Blo 1457548 1458551 := bstep (se 1 (by rfl) ⟨1093913, by rfl⟩ : syracuseStep 1458551 = 2187827) B2187827
theorem B2187659 : Blo 1457548 2187659 := bstep (se 1 (by rfl) ⟨1640744, by rfl⟩ : syracuseStep 2187659 = 3281489) B3281489
theorem B1458571 : Blo 1457548 1458571 := bstep (se 1 (by rfl) ⟨1093928, by rfl⟩ : syracuseStep 1458571 = 2187857) B2187857
theorem B6226321 : Blo 1457548 6226321 := bstep (se 2 (by rfl) ⟨2334870, by rfl⟩ : syracuseStep 6226321 = 4669741) B4669741
theorem B2187671 : Blo 1457548 2187671 := bstep (se 1 (by rfl) ⟨1640753, by rfl⟩ : syracuseStep 2187671 = 3281507) B3281507
theorem B1458583 : Blo 1457548 1458583 := bstep (se 1 (by rfl) ⟨1093937, by rfl⟩ : syracuseStep 1458583 = 2187875) B2187875
theorem B4153751 : Blo 1457548 4153751 := bstep (se 1 (by rfl) ⟨3115313, by rfl⟩ : syracuseStep 4153751 = 6230627) B6230627
theorem B1458603 : Blo 1457548 1458603 := bstep (se 1 (by rfl) ⟨1093952, by rfl⟩ : syracuseStep 1458603 = 2187905) B2187905
theorem B3940787 : Blo 1457548 3940787 := bstep (se 1 (by rfl) ⟨2955590, by rfl⟩ : syracuseStep 3940787 = 5911181) B5911181
theorem B4923827 : Blo 1457548 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B1458615 : Blo 1457548 1458615 := bstep (se 1 (by rfl) ⟨1093961, by rfl⟩ : syracuseStep 1458615 = 2187923) B2187923
theorem B1556939 : Blo 1457548 1556939 := bstep (se 1 (by rfl) ⟨1167704, by rfl⟩ : syracuseStep 1556939 = 2335409) B2335409
theorem B1458635 : Blo 1457548 1458635 := bstep (se 1 (by rfl) ⟨1093976, by rfl⟩ : syracuseStep 1458635 = 2187953) B2187953
theorem B1458647 : Blo 1457548 1458647 := bstep (se 1 (by rfl) ⟨1093985, by rfl⟩ : syracuseStep 1458647 = 2187971) B2187971
theorem B2187737 : Blo 1457548 2187737 := bstep (se 2 (by rfl) ⟨820401, by rfl⟩ : syracuseStep 2187737 = 1640803) B1640803
theorem B1458667 : Blo 1457548 1458667 := bstep (se 1 (by rfl) ⟨1094000, by rfl⟩ : syracuseStep 1458667 = 2188001) B2188001
theorem B1458679 : Blo 1457548 1458679 := bstep (se 1 (by rfl) ⟨1094009, by rfl⟩ : syracuseStep 1458679 = 2188019) B2188019
theorem B1458699 : Blo 1457548 1458699 := bstep (se 1 (by rfl) ⟨1094024, by rfl⟩ : syracuseStep 1458699 = 2188049) B2188049
theorem B1458711 : Blo 1457548 1458711 := bstep (se 1 (by rfl) ⟨1094033, by rfl⟩ : syracuseStep 1458711 = 2188067) B2188067
theorem B1458731 : Blo 1457548 1458731 := bstep (se 1 (by rfl) ⟨1094048, by rfl⟩ : syracuseStep 1458731 = 2188097) B2188097
theorem B1458743 : Blo 1457548 1458743 := bstep (se 1 (by rfl) ⟨1094057, by rfl⟩ : syracuseStep 1458743 = 2188115) B2188115
theorem B18678347 : Blo 1457548 18678347 := bstep (se 1 (by rfl) ⟨14008760, by rfl⟩ : syracuseStep 18678347 = 28017521) B28017521
theorem B2187851 : Blo 1457548 2187851 := bstep (se 1 (by rfl) ⟨1640888, by rfl⟩ : syracuseStep 2187851 = 3281777) B3281777
theorem B1458763 : Blo 1457548 1458763 := bstep (se 1 (by rfl) ⟨1094072, by rfl⟩ : syracuseStep 1458763 = 2188145) B2188145
theorem B2187863 : Blo 1457548 2187863 := bstep (se 1 (by rfl) ⟨1640897, by rfl⟩ : syracuseStep 2187863 = 3281795) B3281795
theorem B1458775 : Blo 1457548 1458775 := bstep (se 1 (by rfl) ⟨1094081, by rfl⟩ : syracuseStep 1458775 = 2188163) B2188163
theorem B1458795 : Blo 1457548 1458795 := bstep (se 1 (by rfl) ⟨1094096, by rfl⟩ : syracuseStep 1458795 = 2188193) B2188193
theorem B1458807 : Blo 1457548 1458807 := bstep (se 1 (by rfl) ⟨1094105, by rfl⟩ : syracuseStep 1458807 = 2188211) B2188211
theorem B1458827 : Blo 1457548 1458827 := bstep (se 1 (by rfl) ⟨1094120, by rfl⟩ : syracuseStep 1458827 = 2188241) B2188241
theorem B2769547 : Blo 1457548 2769547 := bstep (se 1 (by rfl) ⟨2077160, by rfl⟩ : syracuseStep 2769547 = 4154321) B4154321
theorem B1458839 : Blo 1457548 1458839 := bstep (se 1 (by rfl) ⟨1094129, by rfl⟩ : syracuseStep 1458839 = 2188259) B2188259
theorem B3744407 : Blo 1457548 3744407 := bstep (se 1 (by rfl) ⟨2808305, by rfl⟩ : syracuseStep 3744407 = 5616611) B5616611
theorem B2187929 : Blo 1457548 2187929 := bstep (se 2 (by rfl) ⟨820473, by rfl⟩ : syracuseStep 2187929 = 1640947) B1640947
theorem B1458859 : Blo 1457548 1458859 := bstep (se 1 (by rfl) ⟨1094144, by rfl⟩ : syracuseStep 1458859 = 2188289) B2188289
theorem B1458871 : Blo 1457548 1458871 := bstep (se 1 (by rfl) ⟨1094153, by rfl⟩ : syracuseStep 1458871 = 2188307) B2188307
theorem B4924097 : Blo 1457548 4924097 := bstep (se 2 (by rfl) ⟨1846536, by rfl⟩ : syracuseStep 4924097 = 3693073) B3693073
theorem B1458891 : Blo 1457548 1458891 := bstep (se 1 (by rfl) ⟨1094168, by rfl⟩ : syracuseStep 1458891 = 2188337) B2188337
theorem B2769623 : Blo 1457548 2769623 := bstep (se 1 (by rfl) ⟨2077217, by rfl⟩ : syracuseStep 2769623 = 4154435) B4154435
theorem B1458903 : Blo 1457548 1458903 := bstep (se 1 (by rfl) ⟨1094177, by rfl⟩ : syracuseStep 1458903 = 2188355) B2188355
theorem B3941081 : Blo 1457548 3941081 := bstep (se 2 (by rfl) ⟨1477905, by rfl⟩ : syracuseStep 3941081 = 2955811) B2955811
theorem B1458923 : Blo 1457548 1458923 := bstep (se 1 (by rfl) ⟨1094192, by rfl⟩ : syracuseStep 1458923 = 2188385) B2188385
theorem B1458935 : Blo 1457548 1458935 := bstep (se 1 (by rfl) ⟨1094201, by rfl⟩ : syracuseStep 1458935 = 2188403) B2188403
theorem B5538563 : Blo 1457548 5538563 := bstep (se 1 (by rfl) ⟨4153922, by rfl⟩ : syracuseStep 5538563 = 8307845) B8307845
theorem B2188043 : Blo 1457548 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B1458955 : Blo 1457548 1458955 := bstep (se 1 (by rfl) ⟨1094216, by rfl⟩ : syracuseStep 1458955 = 2188433) B2188433
theorem B5538577 : Blo 1457548 5538577 := bstep (se 2 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 5538577 = 4153933) B4153933
theorem B2335511 : Blo 1457548 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B2188055 : Blo 1457548 2188055 := bstep (se 1 (by rfl) ⟨1641041, by rfl⟩ : syracuseStep 2188055 = 3282083) B3282083
theorem B1458967 : Blo 1457548 1458967 := bstep (se 1 (by rfl) ⟨1094225, by rfl⟩ : syracuseStep 1458967 = 2188451) B2188451
theorem B1458987 : Blo 1457548 1458987 := bstep (se 1 (by rfl) ⟨1094240, by rfl⟩ : syracuseStep 1458987 = 2188481) B2188481
theorem B1458999 : Blo 1457548 1458999 := bstep (se 1 (by rfl) ⟨1094249, by rfl⟩ : syracuseStep 1458999 = 2188499) B2188499
theorem B1459019 : Blo 1457548 1459019 := bstep (se 1 (by rfl) ⟨1094264, by rfl⟩ : syracuseStep 1459019 = 2188529) B2188529
theorem B1459031 : Blo 1457548 1459031 := bstep (se 1 (by rfl) ⟨1094273, by rfl⟩ : syracuseStep 1459031 = 2188547) B2188547
theorem B2188121 : Blo 1457548 2188121 := bstep (se 2 (by rfl) ⟨820545, by rfl⟩ : syracuseStep 2188121 = 1641091) B1641091
theorem B7381853 : Blo 1457548 7381853 := bstep (se 3 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 7381853 = 2768195) B2768195
theorem B10117981 : Blo 1457548 10117981 := bstep (se 3 (by rfl) ⟨1897121, by rfl⟩ : syracuseStep 10117981 = 3794243) B3794243
theorem B1459051 : Blo 1457548 1459051 := bstep (se 1 (by rfl) ⟨1094288, by rfl⟩ : syracuseStep 1459051 = 2188577) B2188577
theorem B1459063 : Blo 1457548 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B1459083 : Blo 1457548 1459083 := bstep (se 1 (by rfl) ⟨1094312, by rfl⟩ : syracuseStep 1459083 = 2188625) B2188625
theorem B6652817 : Blo 1457548 6652817 := bstep (se 2 (by rfl) ⟨2494806, by rfl⟩ : syracuseStep 6652817 = 4989613) B4989613
theorem B1459095 : Blo 1457548 1459095 := bstep (se 1 (by rfl) ⟨1094321, by rfl⟩ : syracuseStep 1459095 = 2188643) B2188643
theorem B1459115 : Blo 1457548 1459115 := bstep (se 1 (by rfl) ⟨1094336, by rfl⟩ : syracuseStep 1459115 = 2188673) B2188673
theorem B12460979 : Blo 1457548 12460979 := bstep (se 1 (by rfl) ⟨9345734, by rfl⟩ : syracuseStep 12460979 = 18691469) B18691469
theorem B7013299 : Blo 1457548 7013299 := bstep (se 1 (by rfl) ⟨5259974, by rfl⟩ : syracuseStep 7013299 = 10519949) B10519949
theorem B1459127 : Blo 1457548 1459127 := bstep (se 1 (by rfl) ⟨1094345, by rfl⟩ : syracuseStep 1459127 = 2188691) B2188691
theorem B2335691 : Blo 1457548 2335691 := bstep (se 1 (by rfl) ⟨1751768, by rfl⟩ : syracuseStep 2335691 = 3503537) B3503537
theorem B2188235 : Blo 1457548 2188235 := bstep (se 1 (by rfl) ⟨1641176, by rfl⟩ : syracuseStep 2188235 = 3282353) B3282353
theorem B1459147 : Blo 1457548 1459147 := bstep (se 1 (by rfl) ⟨1094360, by rfl⟩ : syracuseStep 1459147 = 2188721) B2188721
theorem B2188247 : Blo 1457548 2188247 := bstep (se 1 (by rfl) ⟨1641185, by rfl⟩ : syracuseStep 2188247 = 3282371) B3282371
theorem B1459159 : Blo 1457548 1459159 := bstep (se 1 (by rfl) ⟨1094369, by rfl⟩ : syracuseStep 1459159 = 2188739) B2188739
theorem B1459179 : Blo 1457548 1459179 := bstep (se 1 (by rfl) ⟨1094384, by rfl⟩ : syracuseStep 1459179 = 2188769) B2188769
theorem B1459191 : Blo 1457548 1459191 := bstep (se 1 (by rfl) ⟨1094393, by rfl⟩ : syracuseStep 1459191 = 2188787) B2188787
theorem B1459211 : Blo 1457548 1459211 := bstep (se 1 (by rfl) ⟨1094408, by rfl⟩ : syracuseStep 1459211 = 2188817) B2188817
theorem B1459223 : Blo 1457548 1459223 := bstep (se 1 (by rfl) ⟨1094417, by rfl⟩ : syracuseStep 1459223 = 2188835) B2188835
theorem B2188313 : Blo 1457548 2188313 := bstep (se 2 (by rfl) ⟨820617, by rfl⟩ : syracuseStep 2188313 = 1641235) B1641235
theorem B1459243 : Blo 1457548 1459243 := bstep (se 1 (by rfl) ⟨1094432, by rfl⟩ : syracuseStep 1459243 = 2188865) B2188865
theorem B1459255 : Blo 1457548 1459255 := bstep (se 1 (by rfl) ⟨1094441, by rfl⟩ : syracuseStep 1459255 = 2188883) B2188883
theorem B5538881 : Blo 1457548 5538881 := bstep (se 2 (by rfl) ⟨2077080, by rfl⟩ : syracuseStep 5538881 = 4154161) B4154161
theorem B2335819 : Blo 1457548 2335819 := bstep (se 1 (by rfl) ⟨1751864, by rfl⟩ : syracuseStep 2335819 = 3503729) B3503729
theorem B1459275 : Blo 1457548 1459275 := bstep (se 1 (by rfl) ⟨1094456, by rfl⟩ : syracuseStep 1459275 = 2188913) B2188913
theorem B1459287 : Blo 1457548 1459287 := bstep (se 1 (by rfl) ⟨1094465, by rfl⟩ : syracuseStep 1459287 = 2188931) B2188931
theorem B1459307 : Blo 1457548 1459307 := bstep (se 1 (by rfl) ⟨1094480, by rfl⟩ : syracuseStep 1459307 = 2188961) B2188961
theorem B1459319 : Blo 1457548 1459319 := bstep (se 1 (by rfl) ⟨1094489, by rfl⟩ : syracuseStep 1459319 = 2188979) B2188979
theorem B2335883 : Blo 1457548 2335883 := bstep (se 1 (by rfl) ⟨1751912, by rfl⟩ : syracuseStep 2335883 = 3503825) B3503825
theorem B2188427 : Blo 1457548 2188427 := bstep (se 1 (by rfl) ⟨1641320, by rfl⟩ : syracuseStep 2188427 = 3282641) B3282641
theorem B1459339 : Blo 1457548 1459339 := bstep (se 1 (by rfl) ⟨1094504, by rfl⟩ : syracuseStep 1459339 = 2189009) B2189009
theorem B2188439 : Blo 1457548 2188439 := bstep (se 1 (by rfl) ⟨1641329, by rfl⟩ : syracuseStep 2188439 = 3282659) B3282659
theorem B1459351 : Blo 1457548 1459351 := bstep (se 1 (by rfl) ⟨1094513, by rfl⟩ : syracuseStep 1459351 = 2189027) B2189027
theorem B1459371 : Blo 1457548 1459371 := bstep (se 1 (by rfl) ⟨1094528, by rfl⟩ : syracuseStep 1459371 = 2189057) B2189057
theorem B1459383 : Blo 1457548 1459383 := bstep (se 1 (by rfl) ⟨1094537, by rfl⟩ : syracuseStep 1459383 = 2189075) B2189075
theorem B4154561 : Blo 1457548 4154561 := bstep (se 2 (by rfl) ⟨1557960, by rfl⟩ : syracuseStep 4154561 = 3115921) B3115921
theorem B1459403 : Blo 1457548 1459403 := bstep (se 1 (by rfl) ⟨1094552, by rfl⟩ : syracuseStep 1459403 = 2189105) B2189105
theorem B1459415 : Blo 1457548 1459415 := bstep (se 1 (by rfl) ⟨1094561, by rfl⟩ : syracuseStep 1459415 = 2189123) B2189123
theorem B2188505 : Blo 1457548 2188505 := bstep (se 2 (by rfl) ⟨820689, by rfl⟩ : syracuseStep 2188505 = 1641379) B1641379
theorem B4924637 : Blo 1457548 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B1459435 : Blo 1457548 1459435 := bstep (se 1 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 1459435 = 2189153) B2189153
theorem B1459447 : Blo 1457548 1459447 := bstep (se 1 (by rfl) ⟨1094585, by rfl⟩ : syracuseStep 1459447 = 2189171) B2189171
theorem B47301893 : Blo 1457548 47301893 := bstep (se 4 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 47301893 = 8869105) B8869105
theorem B1459467 : Blo 1457548 1459467 := bstep (se 1 (by rfl) ⟨1094600, by rfl⟩ : syracuseStep 1459467 = 2189201) B2189201
theorem B7005457 : Blo 1457548 7005457 := bstep (se 2 (by rfl) ⟨2627046, by rfl⟩ : syracuseStep 7005457 = 5254093) B5254093
theorem B1459479 : Blo 1457548 1459479 := bstep (se 1 (by rfl) ⟨1094609, by rfl⟩ : syracuseStep 1459479 = 2189219) B2189219
theorem B1459499 : Blo 1457548 1459499 := bstep (se 1 (by rfl) ⟨1094624, by rfl⟩ : syracuseStep 1459499 = 2189249) B2189249
theorem B1459511 : Blo 1457548 1459511 := bstep (se 1 (by rfl) ⟨1094633, by rfl⟩ : syracuseStep 1459511 = 2189267) B2189267
theorem B2188619 : Blo 1457548 2188619 := bstep (se 1 (by rfl) ⟨1641464, by rfl⟩ : syracuseStep 2188619 = 3282929) B3282929
theorem B1459531 : Blo 1457548 1459531 := bstep (se 1 (by rfl) ⟨1094648, by rfl⟩ : syracuseStep 1459531 = 2189297) B2189297
theorem B2188631 : Blo 1457548 2188631 := bstep (se 1 (by rfl) ⟨1641473, by rfl⟩ : syracuseStep 2188631 = 3282947) B3282947
theorem B1459543 : Blo 1457548 1459543 := bstep (se 1 (by rfl) ⟨1094657, by rfl⟩ : syracuseStep 1459543 = 2189315) B2189315
theorem B2770291 : Blo 1457548 2770291 := bstep (se 1 (by rfl) ⟨2077718, by rfl⟩ : syracuseStep 2770291 = 4155437) B4155437
theorem B3114391 : Blo 1457548 3114391 := bstep (se 1 (by rfl) ⟨2335793, by rfl⟩ : syracuseStep 3114391 = 4671587) B4671587
theorem B1639831 : Blo 1457548 1639831 := bstep (se 1 (by rfl) ⟨1229873, by rfl⟩ : syracuseStep 1639831 = 2459747) B2459747
theorem B2188697 : Blo 1457548 2188697 := bstep (se 2 (by rfl) ⟨820761, by rfl⟩ : syracuseStep 2188697 = 1641523) B1641523
theorem B6399425 : Blo 1457548 6399425 := bstep (se 2 (by rfl) ⟨2399784, by rfl⟩ : syracuseStep 6399425 = 4799569) B4799569
theorem B3114443 : Blo 1457548 3114443 := bstep (se 1 (by rfl) ⟨2335832, by rfl⟩ : syracuseStep 3114443 = 4671665) B4671665
theorem B2188811 : Blo 1457548 2188811 := bstep (se 1 (by rfl) ⟨1641608, by rfl⟩ : syracuseStep 2188811 = 3283217) B3283217
theorem B2188823 : Blo 1457548 2188823 := bstep (se 1 (by rfl) ⟨1641617, by rfl⟩ : syracuseStep 2188823 = 3283235) B3283235
theorem B1640011 : Blo 1457548 1640011 := bstep (se 1 (by rfl) ⟨1230008, by rfl⟩ : syracuseStep 1640011 = 2460017) B2460017
theorem B2770519 : Blo 1457548 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B2188889 : Blo 1457548 2188889 := bstep (se 2 (by rfl) ⟨820833, by rfl⟩ : syracuseStep 2188889 = 1641667) B1641667
theorem B13493861 : Blo 1457548 13493861 := bstep (se 4 (by rfl) ⟨1265049, by rfl⟩ : syracuseStep 13493861 = 2530099) B2530099
theorem B1558135 : Blo 1457548 1558135 := bstep (se 1 (by rfl) ⟨1168601, by rfl⟩ : syracuseStep 1558135 = 2337203) B2337203
theorem B1640119 : Blo 1457548 1640119 := bstep (se 1 (by rfl) ⟨1230089, by rfl⟩ : syracuseStep 1640119 = 2460179) B2460179
theorem B2770625 : Blo 1457548 2770625 := bstep (se 2 (by rfl) ⟨1038984, by rfl⟩ : syracuseStep 2770625 = 2077969) B2077969
theorem B2189003 : Blo 1457548 2189003 := bstep (se 1 (by rfl) ⟨1641752, by rfl⟩ : syracuseStep 2189003 = 3283505) B3283505
theorem B2189015 : Blo 1457548 2189015 := bstep (se 1 (by rfl) ⟨1641761, by rfl⟩ : syracuseStep 2189015 = 3283523) B3283523
theorem B5539549 : Blo 1457548 5539549 := bstep (se 3 (by rfl) ⟨1038665, by rfl⟩ : syracuseStep 5539549 = 2077331) B2077331
theorem B2189081 : Blo 1457548 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B1558315 : Blo 1457548 1558315 := bstep (se 1 (by rfl) ⟨1168736, by rfl⟩ : syracuseStep 1558315 = 2337473) B2337473
theorem B2770777 : Blo 1457548 2770777 := bstep (se 2 (by rfl) ⟨1039041, by rfl⟩ : syracuseStep 2770777 = 2078083) B2078083
theorem B39929699 : Blo 1457548 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B17065829 : Blo 1457548 17065829 := bstep (se 4 (by rfl) ⟨1599921, by rfl⟩ : syracuseStep 17065829 = 3199843) B3199843
theorem B1640299 : Blo 1457548 1640299 := bstep (se 1 (by rfl) ⟨1230224, by rfl⟩ : syracuseStep 1640299 = 2460449) B2460449
theorem B2189195 : Blo 1457548 2189195 := bstep (se 1 (by rfl) ⟨1641896, by rfl⟩ : syracuseStep 2189195 = 3283793) B3283793
theorem B9349015 : Blo 1457548 9349015 := bstep (se 1 (by rfl) ⟨7011761, by rfl⟩ : syracuseStep 9349015 = 14023523) B14023523
theorem B2189207 : Blo 1457548 2189207 := bstep (se 1 (by rfl) ⟨1641905, by rfl⟩ : syracuseStep 2189207 = 3283811) B3283811
theorem B1640407 : Blo 1457548 1640407 := bstep (se 1 (by rfl) ⟨1230305, by rfl⟩ : syracuseStep 1640407 = 2460611) B2460611
theorem B2189273 : Blo 1457548 2189273 := bstep (se 2 (by rfl) ⟨820977, by rfl⟩ : syracuseStep 2189273 = 1641955) B1641955
theorem B2459659 : Blo 1457548 2459659 := bstep (se 1 (by rfl) ⟨1844744, by rfl⟩ : syracuseStep 2459659 = 3689489) B3689489
theorem B1845271 : Blo 1457548 1845271 := bstep (se 1 (by rfl) ⟨1383953, by rfl⟩ : syracuseStep 1845271 = 2767907) B2767907
theorem B1640587 : Blo 1457548 1640587 := bstep (se 1 (by rfl) ⟨1230440, by rfl⟩ : syracuseStep 1640587 = 2460881) B2460881
theorem B5056663 : Blo 1457548 5056663 := bstep (se 1 (by rfl) ⟨3792497, by rfl⟩ : syracuseStep 5056663 = 7584995) B7584995
theorem B2459801 : Blo 1457548 2459801 := bstep (se 2 (by rfl) ⟨922425, by rfl⟩ : syracuseStep 2459801 = 1844851) B1844851
theorem B1640695 : Blo 1457548 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B2459929 : Blo 1457548 2459929 := bstep (se 2 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 2459929 = 1844947) B1844947
theorem B2337049 : Blo 1457548 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B4925771 : Blo 1457548 4925771 := bstep (se 1 (by rfl) ⟨3694328, by rfl⟩ : syracuseStep 4925771 = 7388657) B7388657
theorem B1640875 : Blo 1457548 1640875 := bstep (se 1 (by rfl) ⟨1230656, by rfl⟩ : syracuseStep 1640875 = 2461313) B2461313
theorem B1640983 : Blo 1457548 1640983 := bstep (se 1 (by rfl) ⟨1230737, by rfl⟩ : syracuseStep 1640983 = 2461475) B2461475
theorem B4672151 : Blo 1457548 4672151 := bstep (se 1 (by rfl) ⟨3504113, by rfl⟩ : syracuseStep 4672151 = 7008227) B7008227
theorem B3279563 : Blo 1457548 3279563 := bstep (se 1 (by rfl) ⟨2459672, by rfl⟩ : syracuseStep 3279563 = 4919345) B4919345
theorem B1641163 : Blo 1457548 1641163 := bstep (se 1 (by rfl) ⟨1230872, by rfl⟩ : syracuseStep 1641163 = 2461745) B2461745
theorem B99830485 : Blo 1457548 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B6228697 : Blo 1457548 6228697 := bstep (se 2 (by rfl) ⟨2335761, by rfl⟩ : syracuseStep 6228697 = 4671523) B4671523
theorem B3279617 : Blo 1457548 3279617 := bstep (se 2 (by rfl) ⟨1229856, by rfl⟩ : syracuseStep 3279617 = 2459713) B2459713
theorem B8866577 : Blo 1457548 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B23644973 : Blo 1457548 23644973 := bstep (se 3 (by rfl) ⟨4433432, by rfl⟩ : syracuseStep 23644973 = 8866865) B8866865
theorem B12462893 : Blo 1457548 12462893 := bstep (se 3 (by rfl) ⟨2336792, by rfl⟩ : syracuseStep 12462893 = 4673585) B4673585
theorem B4156211 : Blo 1457548 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B1641271 : Blo 1457548 1641271 := bstep (se 1 (by rfl) ⟨1230953, by rfl⟩ : syracuseStep 1641271 = 2461907) B2461907
theorem B1846091 : Blo 1457548 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B4156235 : Blo 1457548 4156235 := bstep (se 1 (by rfl) ⟨3117176, by rfl⟩ : syracuseStep 4156235 = 6234353) B6234353
theorem B2460503 : Blo 1457548 2460503 := bstep (se 1 (by rfl) ⟨1845377, by rfl⟩ : syracuseStep 2460503 = 3690755) B3690755
theorem B7383959 : Blo 1457548 7383959 := bstep (se 1 (by rfl) ⟨5537969, by rfl⟩ : syracuseStep 7383959 = 11075939) B11075939
theorem B2460631 : Blo 1457548 2460631 := bstep (se 1 (by rfl) ⟨1845473, by rfl⟩ : syracuseStep 2460631 = 3690947) B3690947
theorem B3279833 : Blo 1457548 3279833 := bstep (se 2 (by rfl) ⟨1229937, by rfl⟩ : syracuseStep 3279833 = 2459875) B2459875
theorem B5540825 : Blo 1457548 5540825 := bstep (se 2 (by rfl) ⟨2077809, by rfl⟩ : syracuseStep 5540825 = 4155619) B4155619
theorem B1641451 : Blo 1457548 1641451 := bstep (se 1 (by rfl) ⟨1231088, by rfl⟩ : syracuseStep 1641451 = 2462177) B2462177
theorem B3279923 : Blo 1457548 3279923 := bstep (se 1 (by rfl) ⟨2459942, by rfl⟩ : syracuseStep 3279923 = 4919885) B4919885
theorem B3116083 : Blo 1457548 3116083 := bstep (se 1 (by rfl) ⟨2337062, by rfl⟩ : syracuseStep 3116083 = 4674125) B4674125
theorem B3279959 : Blo 1457548 3279959 := bstep (se 1 (by rfl) ⟨2459969, by rfl⟩ : syracuseStep 3279959 = 4919939) B4919939
theorem B1641559 : Blo 1457548 1641559 := bstep (se 1 (by rfl) ⟨1231169, by rfl⟩ : syracuseStep 1641559 = 2462339) B2462339
theorem B9350245 : Blo 1457548 9350245 := bstep (se 4 (by rfl) ⟨876585, by rfl⟩ : syracuseStep 9350245 = 1753171) B1753171
theorem B3689651 : Blo 1457548 3689651 := bstep (se 1 (by rfl) ⟨2767238, by rfl⟩ : syracuseStep 3689651 = 5534477) B5534477
theorem B3280139 : Blo 1457548 3280139 := bstep (se 1 (by rfl) ⟨2460104, by rfl⟩ : syracuseStep 3280139 = 4920209) B4920209
theorem B1641739 : Blo 1457548 1641739 := bstep (se 1 (by rfl) ⟨1231304, by rfl⟩ : syracuseStep 1641739 = 2462609) B2462609
theorem B3280193 : Blo 1457548 3280193 := bstep (se 2 (by rfl) ⟨1230072, by rfl⟩ : syracuseStep 3280193 = 2460145) B2460145
theorem B1641847 : Blo 1457548 1641847 := bstep (se 1 (by rfl) ⟨1231385, by rfl⟩ : syracuseStep 1641847 = 2462771) B2462771
theorem B3116441 : Blo 1457548 3116441 := bstep (se 2 (by rfl) ⟨1168665, by rfl⟩ : syracuseStep 3116441 = 2337331) B2337331
theorem B3689945 : Blo 1457548 3689945 := bstep (se 2 (by rfl) ⟨1383729, by rfl⟩ : syracuseStep 3689945 = 2767459) B2767459
theorem B12463577 : Blo 1457548 12463577 := bstep (se 2 (by rfl) ⟨4673841, by rfl⟩ : syracuseStep 12463577 = 9347683) B9347683
theorem B1846795 : Blo 1457548 1846795 := bstep (se 1 (by rfl) ⟨1385096, by rfl⟩ : syracuseStep 1846795 = 2770193) B2770193
theorem B3280409 : Blo 1457548 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B2461259 : Blo 1457548 2461259 := bstep (se 1 (by rfl) ⟨1845944, by rfl⟩ : syracuseStep 2461259 = 3691889) B3691889
theorem B3280499 : Blo 1457548 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B3280535 : Blo 1457548 3280535 := bstep (se 1 (by rfl) ⟨2460401, by rfl⟩ : syracuseStep 3280535 = 4920803) B4920803
theorem B6229655 : Blo 1457548 6229655 := bstep (se 1 (by rfl) ⟨4672241, by rfl⟩ : syracuseStep 6229655 = 9344483) B9344483
theorem B2461387 : Blo 1457548 2461387 := bstep (se 1 (by rfl) ⟨1846040, by rfl⟩ : syracuseStep 2461387 = 3692081) B3692081
theorem B4673227 : Blo 1457548 4673227 := bstep (se 1 (by rfl) ⟨3504920, by rfl⟩ : syracuseStep 4673227 = 7009841) B7009841
theorem B1478359 : Blo 1457548 1478359 := bstep (se 1 (by rfl) ⟨1108769, by rfl⟩ : syracuseStep 1478359 = 2217539) B2217539
theorem B1847063 : Blo 1457548 1847063 := bstep (se 1 (by rfl) ⟨1385297, by rfl⟩ : syracuseStep 1847063 = 2770595) B2770595
theorem B5910337 : Blo 1457548 5910337 := bstep (se 2 (by rfl) ⟨2216376, by rfl⟩ : syracuseStep 5910337 = 4432753) B4432753
theorem B3280715 : Blo 1457548 3280715 := bstep (se 1 (by rfl) ⟨2460536, by rfl⟩ : syracuseStep 3280715 = 4921073) B4921073
theorem B2461529 : Blo 1457548 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B4673369 : Blo 1457548 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B3280769 : Blo 1457548 3280769 := bstep (se 2 (by rfl) ⟨1230288, by rfl⟩ : syracuseStep 3280769 = 2460577) B2460577
theorem B2461657 : Blo 1457548 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B3371033 : Blo 1457548 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B3280985 : Blo 1457548 3280985 := bstep (se 2 (by rfl) ⟨1230369, by rfl⟩ : syracuseStep 3280985 = 2460739) B2460739
theorem B10506341 : Blo 1457548 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B3281075 : Blo 1457548 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B3281111 : Blo 1457548 3281111 := bstep (se 1 (by rfl) ⟨2460833, by rfl⟩ : syracuseStep 3281111 = 4921667) B4921667
theorem B2076887 : Blo 1457548 2076887 := bstep (se 1 (by rfl) ⟨1557665, by rfl⟩ : syracuseStep 2076887 = 3115331) B3115331
theorem B2003275 : Blo 1457548 2003275 := bstep (se 1 (by rfl) ⟨1502456, by rfl⟩ : syracuseStep 2003275 = 3004913) B3004913
theorem B3281291 : Blo 1457548 3281291 := bstep (se 1 (by rfl) ⟨2460968, by rfl⟩ : syracuseStep 3281291 = 4921937) B4921937
theorem B3281345 : Blo 1457548 3281345 := bstep (se 2 (by rfl) ⟨1230504, by rfl⟩ : syracuseStep 3281345 = 2461009) B2461009
theorem B4919831 : Blo 1457548 4919831 := bstep (se 1 (by rfl) ⟨3689873, by rfl⟩ : syracuseStep 4919831 = 7379747) B7379747
theorem B2462231 : Blo 1457548 2462231 := bstep (se 1 (by rfl) ⟨1846673, by rfl⟩ : syracuseStep 2462231 = 3693347) B3693347
theorem B2462359 : Blo 1457548 2462359 := bstep (se 1 (by rfl) ⟨1846769, by rfl⟩ : syracuseStep 2462359 = 3693539) B3693539
theorem B3281561 : Blo 1457548 3281561 := bstep (se 2 (by rfl) ⟨1230585, by rfl⟩ : syracuseStep 3281561 = 2461171) B2461171
theorem B6656705 : Blo 1457548 6656705 := bstep (se 2 (by rfl) ⟨2496264, by rfl⟩ : syracuseStep 6656705 = 4992529) B4992529
theorem B3281651 : Blo 1457548 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B3281687 : Blo 1457548 3281687 := bstep (se 1 (by rfl) ⟨2461265, by rfl⟩ : syracuseStep 3281687 = 4922531) B4922531
theorem B2806643 : Blo 1457548 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B9982871 : Blo 1457548 9982871 := bstep (se 1 (by rfl) ⟨7487153, by rfl⟩ : syracuseStep 9982871 = 14974307) B14974307
theorem B3281867 : Blo 1457548 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B3281921 : Blo 1457548 3281921 := bstep (se 2 (by rfl) ⟨1230720, by rfl⟩ : syracuseStep 3281921 = 2461441) B2461441
theorem B21034019 : Blo 1457548 21034019 := bstep (se 1 (by rfl) ⟨15775514, by rfl⟩ : syracuseStep 21034019 = 31551029) B31551029
theorem B4920371 : Blo 1457548 4920371 := bstep (se 1 (by rfl) ⟨3690278, by rfl⟩ : syracuseStep 4920371 = 7380557) B7380557
theorem B4674611 : Blo 1457548 4674611 := bstep (se 1 (by rfl) ⟨3505958, by rfl⟩ : syracuseStep 4674611 = 7011917) B7011917
theorem B3691595 : Blo 1457548 3691595 := bstep (se 1 (by rfl) ⟨2768696, by rfl⟩ : syracuseStep 3691595 = 5537393) B5537393
theorem B3282137 : Blo 1457548 3282137 := bstep (se 2 (by rfl) ⟨1230801, by rfl⟩ : syracuseStep 3282137 = 2461603) B2461603
theorem B2462987 : Blo 1457548 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B5534993 : Blo 1457548 5534993 := bstep (se 2 (by rfl) ⟨2075622, by rfl⟩ : syracuseStep 5534993 = 4151245) B4151245
theorem B3282227 : Blo 1457548 3282227 := bstep (se 1 (by rfl) ⟨2461670, by rfl⟩ : syracuseStep 3282227 = 4923341) B4923341
theorem B4920641 : Blo 1457548 4920641 := bstep (se 2 (by rfl) ⟨1845240, by rfl⟩ : syracuseStep 4920641 = 3690481) B3690481
theorem B3282263 : Blo 1457548 3282263 := bstep (se 1 (by rfl) ⟨2461697, by rfl⟩ : syracuseStep 3282263 = 4923395) B4923395
theorem B4675009 : Blo 1457548 4675009 := bstep (se 2 (by rfl) ⟨1753128, by rfl⟩ : syracuseStep 4675009 = 3506257) B3506257
theorem B2807257 : Blo 1457548 2807257 := bstep (se 2 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 2807257 = 2105443) B2105443
theorem B3282443 : Blo 1457548 3282443 := bstep (se 1 (by rfl) ⟨2461832, by rfl⟩ : syracuseStep 3282443 = 4923665) B4923665
theorem B4150835 : Blo 1457548 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B3282497 : Blo 1457548 3282497 := bstep (se 2 (by rfl) ⟨1230936, by rfl⟩ : syracuseStep 3282497 = 2461873) B2461873
theorem B8304221 : Blo 1457548 8304221 := bstep (se 3 (by rfl) ⟨1557041, by rfl⟩ : syracuseStep 8304221 = 3114083) B3114083
theorem B26621621 : Blo 1457548 26621621 := bstep (se 5 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 26621621 = 2495777) B2495777
theorem B6231755 : Blo 1457548 6231755 := bstep (se 1 (by rfl) ⟨4673816, by rfl⟩ : syracuseStep 6231755 = 9347633) B9347633
theorem B5535449 : Blo 1457548 5535449 := bstep (se 2 (by rfl) ⟨2075793, by rfl⟩ : syracuseStep 5535449 = 4151587) B4151587
theorem B6649565 : Blo 1457548 6649565 := bstep (se 3 (by rfl) ⟨1246793, by rfl⟩ : syracuseStep 6649565 = 2493587) B2493587
theorem B4151063 : Blo 1457548 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B3282713 : Blo 1457548 3282713 := bstep (se 2 (by rfl) ⟨1231017, by rfl⟩ : syracuseStep 3282713 = 2462035) B2462035
theorem B4921181 : Blo 1457548 4921181 := bstep (se 3 (by rfl) ⟨922721, by rfl⟩ : syracuseStep 4921181 = 1845443) B1845443
theorem B3282803 : Blo 1457548 3282803 := bstep (se 1 (by rfl) ⟨2462102, by rfl⟩ : syracuseStep 3282803 = 4924205) B4924205
theorem B2496395 : Blo 1457548 2496395 := bstep (se 1 (by rfl) ⟨1872296, by rfl⟩ : syracuseStep 2496395 = 3744593) B3744593
theorem B3282839 : Blo 1457548 3282839 := bstep (se 1 (by rfl) ⟨2462129, by rfl⟩ : syracuseStep 3282839 = 4924259) B4924259
theorem B2955161 : Blo 1457548 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B5535661 : Blo 1457548 5535661 := bstep (se 3 (by rfl) ⟨1037936, by rfl⟩ : syracuseStep 5535661 = 2075873) B2075873
theorem B6649859 : Blo 1457548 6649859 := bstep (se 1 (by rfl) ⟨4987394, by rfl⟩ : syracuseStep 6649859 = 9974789) B9974789
theorem B3504151 : Blo 1457548 3504151 := bstep (se 1 (by rfl) ⟨2628113, by rfl⟩ : syracuseStep 3504151 = 5256227) B5256227
theorem B3692567 : Blo 1457548 3692567 := bstep (se 1 (by rfl) ⟨2769425, by rfl⟩ : syracuseStep 3692567 = 5538851) B5538851
theorem B4151371 : Blo 1457548 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B3283019 : Blo 1457548 3283019 := bstep (se 1 (by rfl) ⟨2462264, by rfl⟩ : syracuseStep 3283019 = 4924529) B4924529
theorem B3283073 : Blo 1457548 3283073 := bstep (se 2 (by rfl) ⟨1231152, by rfl⟩ : syracuseStep 3283073 = 2462305) B2462305
theorem B5535965 : Blo 1457548 5535965 := bstep (se 3 (by rfl) ⟨1037993, by rfl⟩ : syracuseStep 5535965 = 2075987) B2075987
theorem B23992561 : Blo 1457548 23992561 := bstep (se 2 (by rfl) ⟨8997210, by rfl⟩ : syracuseStep 23992561 = 17994421) B17994421
theorem B12458245 : Blo 1457548 12458245 := bstep (se 4 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 12458245 = 2335921) B2335921
theorem B6314285 : Blo 1457548 6314285 := bstep (se 3 (by rfl) ⟨1183928, by rfl⟩ : syracuseStep 6314285 = 2367857) B2367857
theorem B2767193 : Blo 1457548 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B3283289 : Blo 1457548 3283289 := bstep (se 2 (by rfl) ⟨1231233, by rfl⟩ : syracuseStep 3283289 = 2462467) B2462467
theorem B4151645 : Blo 1457548 4151645 := bstep (se 3 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 4151645 = 1556867) B1556867
theorem B2627969 : Blo 1457548 2627969 := bstep (se 2 (by rfl) ⟨985488, by rfl⟩ : syracuseStep 2627969 = 1970977) B1970977
theorem B7387523 : Blo 1457548 7387523 := bstep (se 1 (by rfl) ⟨5540642, by rfl⟩ : syracuseStep 7387523 = 11081285) B11081285
theorem B3283379 : Blo 1457548 3283379 := bstep (se 1 (by rfl) ⟨2462534, by rfl⟩ : syracuseStep 3283379 = 4925069) B4925069
theorem B3283415 : Blo 1457548 3283415 := bstep (se 1 (by rfl) ⟨2462561, by rfl⟩ : syracuseStep 3283415 = 4925123) B4925123
theorem B11082257 : Blo 1457548 11082257 := bstep (se 2 (by rfl) ⟨4155846, by rfl⟩ : syracuseStep 11082257 = 8311693) B8311693
theorem B3283595 : Blo 1457548 3283595 := bstep (se 1 (by rfl) ⟨2462696, by rfl⟩ : syracuseStep 3283595 = 4925393) B4925393
theorem B3693235 : Blo 1457548 3693235 := bstep (se 1 (by rfl) ⟨2769926, by rfl⟩ : syracuseStep 3693235 = 5539853) B5539853
theorem B3283649 : Blo 1457548 3283649 := bstep (se 2 (by rfl) ⟨1231368, by rfl⟩ : syracuseStep 3283649 = 2462737) B2462737
theorem B2767603 : Blo 1457548 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B3693377 : Blo 1457548 3693377 := bstep (se 2 (by rfl) ⟨1385016, by rfl⟩ : syracuseStep 3693377 = 2770033) B2770033
theorem B5258129 : Blo 1457548 5258129 := bstep (se 2 (by rfl) ⟨1971798, by rfl⟩ : syracuseStep 5258129 = 3943597) B3943597
theorem B3283865 : Blo 1457548 3283865 := bstep (se 2 (by rfl) ⟨1231449, by rfl⟩ : syracuseStep 3283865 = 2462899) B2462899
theorem B11074481 : Blo 1457548 11074481 := bstep (se 2 (by rfl) ⟨4152930, by rfl⟩ : syracuseStep 11074481 = 8305861) B8305861
theorem B4922315 : Blo 1457548 4922315 := bstep (se 1 (by rfl) ⟨3691736, by rfl⟩ : syracuseStep 4922315 = 7383473) B7383473
theorem B3283955 : Blo 1457548 3283955 := bstep (se 1 (by rfl) ⟨2462966, by rfl⟩ : syracuseStep 3283955 = 4925933) B4925933
theorem B8870957 : Blo 1457548 8870957 := bstep (se 3 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 8870957 = 3326609) B3326609
theorem B23665733 : Blo 1457548 23665733 := bstep (se 4 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 23665733 = 4437325) B4437325
theorem B2186327 : Blo 1457548 2186327 := bstep (se 1 (by rfl) ⟨1639745, by rfl⟩ : syracuseStep 2186327 = 3279491) B3279491
theorem B2219095 : Blo 1457548 2219095 := bstep (se 1 (by rfl) ⟨1664321, by rfl⟩ : syracuseStep 2219095 = 3328643) B3328643
theorem B2186393 : Blo 1457548 2186393 := bstep (se 2 (by rfl) ⟨819897, by rfl⟩ : syracuseStep 2186393 = 1639795) B1639795
theorem B2768089 : Blo 1457548 2768089 := bstep (se 2 (by rfl) ⟨1038033, by rfl⟩ : syracuseStep 2768089 = 2076067) B2076067
theorem B4922585 : Blo 1457548 4922585 := bstep (se 2 (by rfl) ⟨1845969, by rfl⟩ : syracuseStep 4922585 = 3691939) B3691939
theorem B2186507 : Blo 1457548 2186507 := bstep (se 1 (by rfl) ⟨1639880, by rfl⟩ : syracuseStep 2186507 = 3279761) B3279761
theorem B2186519 : Blo 1457548 2186519 := bstep (se 1 (by rfl) ⟨1639889, by rfl⟩ : syracuseStep 2186519 = 3279779) B3279779
theorem B6233395 : Blo 1457548 6233395 := bstep (se 1 (by rfl) ⟨4675046, by rfl⟩ : syracuseStep 6233395 = 9350093) B9350093
theorem B11222347 : Blo 1457548 11222347 := bstep (se 1 (by rfl) ⟨8416760, by rfl⟩ : syracuseStep 11222347 = 16833521) B16833521
theorem B2186585 : Blo 1457548 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B3325313 : Blo 1457548 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B1457559 : Blo 1457548 1457559 := bstep (se 1 (by rfl) ⟨1093169, by rfl⟩ : syracuseStep 1457559 = 2186339) B2186339
theorem B11074967 : Blo 1457548 11074967 := bstep (se 1 (by rfl) ⟨8306225, by rfl⟩ : syracuseStep 11074967 = 16612451) B16612451
theorem B1457579 : Blo 1457548 1457579 := bstep (se 1 (by rfl) ⟨1093184, by rfl⟩ : syracuseStep 1457579 = 2186369) B2186369
theorem B1457591 : Blo 1457548 1457591 := bstep (se 1 (by rfl) ⟨1093193, by rfl⟩ : syracuseStep 1457591 = 2186387) B2186387
theorem B1457611 : Blo 1457548 1457611 := bstep (se 1 (by rfl) ⟨1093208, by rfl⟩ : syracuseStep 1457611 = 2186417) B2186417
theorem B2186699 : Blo 1457548 2186699 := bstep (se 1 (by rfl) ⟨1640024, by rfl⟩ : syracuseStep 2186699 = 3280049) B3280049
theorem B1457623 : Blo 1457548 1457623 := bstep (se 1 (by rfl) ⟨1093217, by rfl⟩ : syracuseStep 1457623 = 2186435) B2186435
theorem B2186711 : Blo 1457548 2186711 := bstep (se 1 (by rfl) ⟨1640033, by rfl⟩ : syracuseStep 2186711 = 3280067) B3280067
theorem B1457643 : Blo 1457548 1457643 := bstep (se 1 (by rfl) ⟨1093232, by rfl⟩ : syracuseStep 1457643 = 2186465) B2186465
theorem B1457655 : Blo 1457548 1457655 := bstep (se 1 (by rfl) ⟨1093241, by rfl⟩ : syracuseStep 1457655 = 2186483) B2186483
theorem B1457675 : Blo 1457548 1457675 := bstep (se 1 (by rfl) ⟨1093256, by rfl⟩ : syracuseStep 1457675 = 2186513) B2186513
theorem B1457687 : Blo 1457548 1457687 := bstep (se 1 (by rfl) ⟨1093265, by rfl⟩ : syracuseStep 1457687 = 2186531) B2186531
theorem B2186777 : Blo 1457548 2186777 := bstep (se 2 (by rfl) ⟨820041, by rfl⟩ : syracuseStep 2186777 = 1640083) B1640083
theorem B1457707 : Blo 1457548 1457707 := bstep (se 1 (by rfl) ⟨1093280, by rfl⟩ : syracuseStep 1457707 = 2186561) B2186561
theorem B1457719 : Blo 1457548 1457719 := bstep (se 1 (by rfl) ⟨1093289, by rfl⟩ : syracuseStep 1457719 = 2186579) B2186579
theorem B1457739 : Blo 1457548 1457739 := bstep (se 1 (by rfl) ⟨1093304, by rfl⟩ : syracuseStep 1457739 = 2186609) B2186609
theorem B8420939 : Blo 1457548 8420939 := bstep (se 1 (by rfl) ⟨6315704, by rfl⟩ : syracuseStep 8420939 = 12631409) B12631409
theorem B1457751 : Blo 1457548 1457751 := bstep (se 1 (by rfl) ⟨1093313, by rfl⟩ : syracuseStep 1457751 = 2186627) B2186627
theorem B1457771 : Blo 1457548 1457771 := bstep (se 1 (by rfl) ⟨1093328, by rfl⟩ : syracuseStep 1457771 = 2186657) B2186657
theorem B1457783 : Blo 1457548 1457783 := bstep (se 1 (by rfl) ⟨1093337, by rfl⟩ : syracuseStep 1457783 = 2186675) B2186675
theorem B1457803 : Blo 1457548 1457803 := bstep (se 1 (by rfl) ⟨1093352, by rfl⟩ : syracuseStep 1457803 = 2186705) B2186705
theorem B2186891 : Blo 1457548 2186891 := bstep (se 1 (by rfl) ⟨1640168, by rfl⟩ : syracuseStep 2186891 = 3280337) B3280337
theorem B1457815 : Blo 1457548 1457815 := bstep (se 1 (by rfl) ⟨1093361, by rfl⟩ : syracuseStep 1457815 = 2186723) B2186723
theorem B2186903 : Blo 1457548 2186903 := bstep (se 1 (by rfl) ⟨1640177, by rfl⟩ : syracuseStep 2186903 = 3280355) B3280355
theorem B1457835 : Blo 1457548 1457835 := bstep (se 1 (by rfl) ⟨1093376, by rfl⟩ : syracuseStep 1457835 = 2186753) B2186753
theorem B2956979 : Blo 1457548 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1457847 : Blo 1457548 1457847 := bstep (se 1 (by rfl) ⟨1093385, by rfl⟩ : syracuseStep 1457847 = 2186771) B2186771
theorem B1457867 : Blo 1457548 1457867 := bstep (se 1 (by rfl) ⟨1093400, by rfl⟩ : syracuseStep 1457867 = 2186801) B2186801
theorem B1457879 : Blo 1457548 1457879 := bstep (se 1 (by rfl) ⟨1093409, by rfl⟩ : syracuseStep 1457879 = 2186819) B2186819
theorem B2186969 : Blo 1457548 2186969 := bstep (se 2 (by rfl) ⟨820113, by rfl⟩ : syracuseStep 2186969 = 1640227) B1640227
theorem B1457899 : Blo 1457548 1457899 := bstep (se 1 (by rfl) ⟨1093424, by rfl⟩ : syracuseStep 1457899 = 2186849) B2186849
theorem B1457911 : Blo 1457548 1457911 := bstep (se 1 (by rfl) ⟨1093433, by rfl⟩ : syracuseStep 1457911 = 2186867) B2186867
theorem B1457931 : Blo 1457548 1457931 := bstep (se 1 (by rfl) ⟨1093448, by rfl⟩ : syracuseStep 1457931 = 2186897) B2186897
theorem B2768651 : Blo 1457548 2768651 := bstep (se 1 (by rfl) ⟨2076488, by rfl⟩ : syracuseStep 2768651 = 4152977) B4152977
theorem B1457943 : Blo 1457548 1457943 := bstep (se 1 (by rfl) ⟨1093457, by rfl⟩ : syracuseStep 1457943 = 2186915) B2186915
theorem B1457963 : Blo 1457548 1457963 := bstep (se 1 (by rfl) ⟨1093472, by rfl⟩ : syracuseStep 1457963 = 2186945) B2186945
theorem B1457975 : Blo 1457548 1457975 := bstep (se 1 (by rfl) ⟨1093481, by rfl⟩ : syracuseStep 1457975 = 2186963) B2186963
theorem B1457995 : Blo 1457548 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B2187083 : Blo 1457548 2187083 := bstep (se 1 (by rfl) ⟨1640312, by rfl⟩ : syracuseStep 2187083 = 3280625) B3280625
theorem B1458007 : Blo 1457548 1458007 := bstep (se 1 (by rfl) ⟨1093505, by rfl⟩ : syracuseStep 1458007 = 2187011) B2187011
theorem B2187095 : Blo 1457548 2187095 := bstep (se 1 (by rfl) ⟨1640321, by rfl⟩ : syracuseStep 2187095 = 3280643) B3280643
theorem B1458027 : Blo 1457548 1458027 := bstep (se 1 (by rfl) ⟨1093520, by rfl⟩ : syracuseStep 1458027 = 2187041) B2187041
theorem B1458039 : Blo 1457548 1458039 := bstep (se 1 (by rfl) ⟨1093529, by rfl⟩ : syracuseStep 1458039 = 2187059) B2187059
theorem B1458059 : Blo 1457548 1458059 := bstep (se 1 (by rfl) ⟨1093544, by rfl⟩ : syracuseStep 1458059 = 2187089) B2187089
theorem B1458071 : Blo 1457548 1458071 := bstep (se 1 (by rfl) ⟨1093553, by rfl⟩ : syracuseStep 1458071 = 2187107) B2187107
theorem B4923287 : Blo 1457548 4923287 := bstep (se 1 (by rfl) ⟨3692465, by rfl⟩ : syracuseStep 4923287 = 7384931) B7384931
theorem B2187161 : Blo 1457548 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B1458091 : Blo 1457548 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B6234029 : Blo 1457548 6234029 := bstep (se 3 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 6234029 = 2337761) B2337761
theorem B1458103 : Blo 1457548 1458103 := bstep (se 1 (by rfl) ⟨1093577, by rfl⟩ : syracuseStep 1458103 = 2187155) B2187155
theorem B2768833 : Blo 1457548 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B1458123 : Blo 1457548 1458123 := bstep (se 1 (by rfl) ⟨1093592, by rfl⟩ : syracuseStep 1458123 = 2187185) B2187185
theorem B1458135 : Blo 1457548 1458135 := bstep (se 1 (by rfl) ⟨1093601, by rfl⟩ : syracuseStep 1458135 = 2187203) B2187203
theorem B1662935 : Blo 1457548 1662935 := bstep (se 1 (by rfl) ⟨1247201, by rfl⟩ : syracuseStep 1662935 = 2494403) B2494403
theorem B21028825 : Blo 1457548 21028825 := bstep (se 2 (by rfl) ⟨7885809, by rfl⟩ : syracuseStep 21028825 = 15771619) B15771619
theorem B1458155 : Blo 1457548 1458155 := bstep (se 1 (by rfl) ⟨1093616, by rfl⟩ : syracuseStep 1458155 = 2187233) B2187233
theorem B1458167 : Blo 1457548 1458167 := bstep (se 1 (by rfl) ⟨1093625, by rfl⟩ : syracuseStep 1458167 = 2187251) B2187251
theorem B1458183 : Blo 1457548 1458183 := bstep (se 1 (by rfl) ⟨1093637, by rfl⟩ : syracuseStep 1458183 = 2187275) B2187275
theorem B1458191 : Blo 1457548 1458191 := bstep (se 1 (by rfl) ⟨1093643, by rfl⟩ : syracuseStep 1458191 = 2187287) B2187287
theorem B2187323 : Blo 1457548 2187323 := bstep (se 1 (by rfl) ⟨1640492, by rfl⟩ : syracuseStep 2187323 = 3280985) B3280985
theorem B1458235 : Blo 1457548 1458235 := bstep (se 1 (by rfl) ⟨1093676, by rfl⟩ : syracuseStep 1458235 = 2187353) B2187353
theorem B7004227 : Blo 1457548 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B5537879 : Blo 1457548 5537879 := bstep (se 1 (by rfl) ⟨4153409, by rfl⟩ : syracuseStep 5537879 = 8306819) B8306819
theorem B2187383 : Blo 1457548 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B1458311 : Blo 1457548 1458311 := bstep (se 1 (by rfl) ⟨1093733, by rfl⟩ : syracuseStep 1458311 = 2187467) B2187467
theorem B2187407 : Blo 1457548 2187407 := bstep (se 1 (by rfl) ⟨1640555, by rfl⟩ : syracuseStep 2187407 = 3281111) B3281111
theorem B1458319 : Blo 1457548 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B2187449 : Blo 1457548 2187449 := bstep (se 2 (by rfl) ⟨820293, by rfl⟩ : syracuseStep 2187449 = 1640587) B1640587
theorem B1458363 : Blo 1457548 1458363 := bstep (se 1 (by rfl) ⟨1093772, by rfl⟩ : syracuseStep 1458363 = 2187545) B2187545
theorem B6742217 : Blo 1457548 6742217 := bstep (se 2 (by rfl) ⟨2528331, by rfl⟩ : syracuseStep 6742217 = 5056663) B5056663
theorem B2187527 : Blo 1457548 2187527 := bstep (se 1 (by rfl) ⟨1640645, by rfl⟩ : syracuseStep 2187527 = 3281291) B3281291
theorem B1458439 : Blo 1457548 1458439 := bstep (se 1 (by rfl) ⟨1093829, by rfl⟩ : syracuseStep 1458439 = 2187659) B2187659
theorem B1458447 : Blo 1457548 1458447 := bstep (se 1 (by rfl) ⟨1093835, by rfl⟩ : syracuseStep 1458447 = 2187671) B2187671
theorem B2769167 : Blo 1457548 2769167 := bstep (se 1 (by rfl) ⟨2076875, by rfl⟩ : syracuseStep 2769167 = 4153751) B4153751
theorem B2187563 : Blo 1457548 2187563 := bstep (se 1 (by rfl) ⟨1640672, by rfl⟩ : syracuseStep 2187563 = 3281345) B3281345
theorem B1458491 : Blo 1457548 1458491 := bstep (se 1 (by rfl) ⟨1093868, by rfl⟩ : syracuseStep 1458491 = 2187737) B2187737
theorem B31990081 : Blo 1457548 31990081 := bstep (se 2 (by rfl) ⟨11996280, by rfl⟩ : syracuseStep 31990081 = 23992561) B23992561
theorem B2187593 : Blo 1457548 2187593 := bstep (se 2 (by rfl) ⟨820347, by rfl⟩ : syracuseStep 2187593 = 1640695) B1640695
theorem B12452231 : Blo 1457548 12452231 := bstep (se 1 (by rfl) ⟨9339173, by rfl⟩ : syracuseStep 12452231 = 18678347) B18678347
theorem B1458567 : Blo 1457548 1458567 := bstep (se 1 (by rfl) ⟨1093925, by rfl⟩ : syracuseStep 1458567 = 2187851) B2187851
theorem B1458575 : Blo 1457548 1458575 := bstep (se 1 (by rfl) ⟨1093931, by rfl⟩ : syracuseStep 1458575 = 2187863) B2187863
theorem B2187707 : Blo 1457548 2187707 := bstep (se 1 (by rfl) ⟨1640780, by rfl⟩ : syracuseStep 2187707 = 3281561) B3281561
theorem B1458619 : Blo 1457548 1458619 := bstep (se 1 (by rfl) ⟨1093964, by rfl⟩ : syracuseStep 1458619 = 2187929) B2187929
theorem B3113417 : Blo 1457548 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B2187767 : Blo 1457548 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B1458695 : Blo 1457548 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B2187791 : Blo 1457548 2187791 := bstep (se 1 (by rfl) ⟨1640843, by rfl⟩ : syracuseStep 2187791 = 3281687) B3281687
theorem B1458703 : Blo 1457548 1458703 := bstep (se 1 (by rfl) ⟨1094027, by rfl⟩ : syracuseStep 1458703 = 2188055) B2188055
theorem B2187833 : Blo 1457548 2187833 := bstep (se 2 (by rfl) ⟨820437, by rfl⟩ : syracuseStep 2187833 = 1640875) B1640875
theorem B1458747 : Blo 1457548 1458747 := bstep (se 1 (by rfl) ⟨1094060, by rfl⟩ : syracuseStep 1458747 = 2188121) B2188121
theorem B5538365 : Blo 1457548 5538365 := bstep (se 3 (by rfl) ⟨1038443, by rfl⟩ : syracuseStep 5538365 = 2076887) B2076887
theorem B8307319 : Blo 1457548 8307319 := bstep (se 1 (by rfl) ⟨6230489, by rfl⟩ : syracuseStep 8307319 = 12460979) B12460979
theorem B1557127 : Blo 1457548 1557127 := bstep (se 1 (by rfl) ⟨1167845, by rfl⟩ : syracuseStep 1557127 = 2335691) B2335691
theorem B2187911 : Blo 1457548 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B1458823 : Blo 1457548 1458823 := bstep (se 1 (by rfl) ⟨1094117, by rfl⟩ : syracuseStep 1458823 = 2188235) B2188235
theorem B1458831 : Blo 1457548 1458831 := bstep (se 1 (by rfl) ⟨1094123, by rfl⟩ : syracuseStep 1458831 = 2188247) B2188247
theorem B2187947 : Blo 1457548 2187947 := bstep (se 1 (by rfl) ⟨1640960, by rfl⟩ : syracuseStep 2187947 = 3281921) B3281921
theorem B1458875 : Blo 1457548 1458875 := bstep (se 1 (by rfl) ⟨1094156, by rfl⟩ : syracuseStep 1458875 = 2188313) B2188313
theorem B2187977 : Blo 1457548 2187977 := bstep (se 2 (by rfl) ⟨820491, by rfl⟩ : syracuseStep 2187977 = 1640983) B1640983
theorem B1458951 : Blo 1457548 1458951 := bstep (se 1 (by rfl) ⟨1094213, by rfl⟩ : syracuseStep 1458951 = 2188427) B2188427
theorem B1458959 : Blo 1457548 1458959 := bstep (se 1 (by rfl) ⟨1094219, by rfl⟩ : syracuseStep 1458959 = 2188439) B2188439
theorem B2769707 : Blo 1457548 2769707 := bstep (se 1 (by rfl) ⟨2077280, by rfl⟩ : syracuseStep 2769707 = 4154561) B4154561
theorem B2188091 : Blo 1457548 2188091 := bstep (se 1 (by rfl) ⟨1641068, by rfl⟩ : syracuseStep 2188091 = 3282137) B3282137
theorem B1459003 : Blo 1457548 1459003 := bstep (se 1 (by rfl) ⟨1094252, by rfl⟩ : syracuseStep 1459003 = 2188505) B2188505
theorem B2188151 : Blo 1457548 2188151 := bstep (se 1 (by rfl) ⟨1641113, by rfl⟩ : syracuseStep 2188151 = 3282227) B3282227
theorem B1459079 : Blo 1457548 1459079 := bstep (se 1 (by rfl) ⟨1094309, by rfl⟩ : syracuseStep 1459079 = 2188619) B2188619
theorem B2188175 : Blo 1457548 2188175 := bstep (se 1 (by rfl) ⟨1641131, by rfl⟩ : syracuseStep 2188175 = 3282263) B3282263
theorem B1459087 : Blo 1457548 1459087 := bstep (se 1 (by rfl) ⟨1094315, by rfl⟩ : syracuseStep 1459087 = 2188631) B2188631
theorem B4924313 : Blo 1457548 4924313 := bstep (se 2 (by rfl) ⟨1846617, by rfl⟩ : syracuseStep 4924313 = 3693235) B3693235
theorem B2188217 : Blo 1457548 2188217 := bstep (se 2 (by rfl) ⟨820581, by rfl⟩ : syracuseStep 2188217 = 1641163) B1641163
theorem B1459131 : Blo 1457548 1459131 := bstep (se 1 (by rfl) ⟨1094348, by rfl⟩ : syracuseStep 1459131 = 2188697) B2188697
theorem B2188295 : Blo 1457548 2188295 := bstep (se 1 (by rfl) ⟨1641221, by rfl⟩ : syracuseStep 2188295 = 3282443) B3282443
theorem B1459207 : Blo 1457548 1459207 := bstep (se 1 (by rfl) ⟨1094405, by rfl⟩ : syracuseStep 1459207 = 2188811) B2188811
theorem B1459215 : Blo 1457548 1459215 := bstep (se 1 (by rfl) ⟨1094411, by rfl⟩ : syracuseStep 1459215 = 2188823) B2188823
theorem B2188331 : Blo 1457548 2188331 := bstep (se 1 (by rfl) ⟨1641248, by rfl⟩ : syracuseStep 2188331 = 3282497) B3282497
theorem B1459259 : Blo 1457548 1459259 := bstep (se 1 (by rfl) ⟨1094444, by rfl⟩ : syracuseStep 1459259 = 2188889) B2188889
theorem B8995907 : Blo 1457548 8995907 := bstep (se 1 (by rfl) ⟨6746930, by rfl⟩ : syracuseStep 8995907 = 13493861) B13493861
theorem B2188361 : Blo 1457548 2188361 := bstep (se 2 (by rfl) ⟨820635, by rfl⟩ : syracuseStep 2188361 = 1641271) B1641271
theorem B4154503 : Blo 1457548 4154503 := bstep (se 1 (by rfl) ⟨3115877, by rfl⟩ : syracuseStep 4154503 = 6231755) B6231755
theorem B1459335 : Blo 1457548 1459335 := bstep (se 1 (by rfl) ⟨1094501, by rfl⟩ : syracuseStep 1459335 = 2189003) B2189003
theorem B1459343 : Blo 1457548 1459343 := bstep (se 1 (by rfl) ⟨1094507, by rfl⟩ : syracuseStep 1459343 = 2189015) B2189015
theorem B2188475 : Blo 1457548 2188475 := bstep (se 1 (by rfl) ⟨1641356, by rfl⟩ : syracuseStep 2188475 = 3282713) B3282713
theorem B1459387 : Blo 1457548 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B2188535 : Blo 1457548 2188535 := bstep (se 1 (by rfl) ⟨1641401, by rfl⟩ : syracuseStep 2188535 = 3282803) B3282803
theorem B1664263 : Blo 1457548 1664263 := bstep (se 1 (by rfl) ⟨1248197, by rfl⟩ : syracuseStep 1664263 = 2496395) B2496395
theorem B1459463 : Blo 1457548 1459463 := bstep (se 1 (by rfl) ⟨1094597, by rfl⟩ : syracuseStep 1459463 = 2189195) B2189195
theorem B2188559 : Blo 1457548 2188559 := bstep (se 1 (by rfl) ⟨1641419, by rfl⟩ : syracuseStep 2188559 = 3282839) B3282839
theorem B1459471 : Blo 1457548 1459471 := bstep (se 1 (by rfl) ⟨1094603, by rfl⟩ : syracuseStep 1459471 = 2189207) B2189207
theorem B2188601 : Blo 1457548 2188601 := bstep (se 2 (by rfl) ⟨820725, by rfl⟩ : syracuseStep 2188601 = 1641451) B1641451
theorem B1459515 : Blo 1457548 1459515 := bstep (se 1 (by rfl) ⟨1094636, by rfl⟩ : syracuseStep 1459515 = 2189273) B2189273
theorem B4433239 : Blo 1457548 4433239 := bstep (se 1 (by rfl) ⟨3324929, by rfl⟩ : syracuseStep 4433239 = 6649859) B6649859
theorem B2188679 : Blo 1457548 2188679 := bstep (se 1 (by rfl) ⟨1641509, by rfl⟩ : syracuseStep 2188679 = 3283019) B3283019
theorem B4154777 : Blo 1457548 4154777 := bstep (se 2 (by rfl) ⟨1558041, by rfl⟩ : syracuseStep 4154777 = 3116083) B3116083
theorem B2188715 : Blo 1457548 2188715 := bstep (se 1 (by rfl) ⟨1641536, by rfl⟩ : syracuseStep 2188715 = 3283073) B3283073
theorem B3114425 : Blo 1457548 3114425 := bstep (se 2 (by rfl) ⟨1167909, by rfl⟩ : syracuseStep 3114425 = 2335819) B2335819
theorem B1639867 : Blo 1457548 1639867 := bstep (se 1 (by rfl) ⟨1229900, by rfl⟩ : syracuseStep 1639867 = 2459801) B2459801
theorem B2188745 : Blo 1457548 2188745 := bstep (se 2 (by rfl) ⟨820779, by rfl⟩ : syracuseStep 2188745 = 1641559) B1641559
theorem B1844795 : Blo 1457548 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B2188859 : Blo 1457548 2188859 := bstep (se 1 (by rfl) ⟨1641644, by rfl⟩ : syracuseStep 2188859 = 3283289) B3283289
theorem B4925015 : Blo 1457548 4925015 := bstep (se 1 (by rfl) ⟨3693761, by rfl⟩ : syracuseStep 4925015 = 7387523) B7387523
theorem B2188919 : Blo 1457548 2188919 := bstep (se 1 (by rfl) ⟨1641689, by rfl⟩ : syracuseStep 2188919 = 3283379) B3283379
theorem B2188943 : Blo 1457548 2188943 := bstep (se 1 (by rfl) ⟨1641707, by rfl⟩ : syracuseStep 2188943 = 3283415) B3283415
theorem B2188985 : Blo 1457548 2188985 := bstep (se 2 (by rfl) ⟨820869, by rfl⟩ : syracuseStep 2188985 = 1641739) B1641739
theorem B9340609 : Blo 1457548 9340609 := bstep (se 2 (by rfl) ⟨3502728, by rfl⟩ : syracuseStep 9340609 = 7005457) B7005457
theorem B10684133 : Blo 1457548 10684133 := bstep (se 4 (by rfl) ⟨1001637, by rfl⟩ : syracuseStep 10684133 = 2003275) B2003275
theorem B2189063 : Blo 1457548 2189063 := bstep (se 1 (by rfl) ⟨1641797, by rfl⟩ : syracuseStep 2189063 = 3283595) B3283595
theorem B3114767 : Blo 1457548 3114767 := bstep (se 1 (by rfl) ⟨2336075, by rfl⟩ : syracuseStep 3114767 = 4672151) B4672151
theorem B2189099 : Blo 1457548 2189099 := bstep (se 1 (by rfl) ⟨1641824, by rfl⟩ : syracuseStep 2189099 = 3283649) B3283649
theorem B2189129 : Blo 1457548 2189129 := bstep (se 2 (by rfl) ⟨820923, by rfl⟩ : syracuseStep 2189129 = 1641847) B1641847
theorem B8308595 : Blo 1457548 8308595 := bstep (se 1 (by rfl) ⟨6231446, by rfl⟩ : syracuseStep 8308595 = 12462893) B12462893
theorem B2770823 : Blo 1457548 2770823 := bstep (se 1 (by rfl) ⟨2078117, by rfl⟩ : syracuseStep 2770823 = 4156235) B4156235
theorem B1640335 : Blo 1457548 1640335 := bstep (se 1 (by rfl) ⟨1230251, by rfl⟩ : syracuseStep 1640335 = 2460503) B2460503
theorem B2189243 : Blo 1457548 2189243 := bstep (se 1 (by rfl) ⟨1641932, by rfl⟩ : syracuseStep 2189243 = 3283865) B3283865
theorem B7382987 : Blo 1457548 7382987 := bstep (se 1 (by rfl) ⟨5537240, by rfl⟩ : syracuseStep 7382987 = 11074481) B11074481
theorem B2189303 : Blo 1457548 2189303 := bstep (se 1 (by rfl) ⟨1641977, by rfl⟩ : syracuseStep 2189303 = 3283955) B3283955
theorem B6228029 : Blo 1457548 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B4925501 : Blo 1457548 4925501 := bstep (se 3 (by rfl) ⟨923531, by rfl⟩ : syracuseStep 4925501 = 1847063) B1847063
theorem B2459767 : Blo 1457548 2459767 := bstep (se 1 (by rfl) ⟨1844825, by rfl⟩ : syracuseStep 2459767 = 3689651) B3689651
theorem B17737973 : Blo 1457548 17737973 := bstep (se 5 (by rfl) ⟨831467, by rfl⟩ : syracuseStep 17737973 = 1662935) B1662935
theorem B7383311 : Blo 1457548 7383311 := bstep (se 1 (by rfl) ⟨5537483, by rfl⟩ : syracuseStep 7383311 = 11074967) B11074967
theorem B70928693 : Blo 1457548 70928693 := bstep (se 5 (by rfl) ⟨3324782, by rfl⟩ : syracuseStep 70928693 = 6649565) B6649565
theorem B2459963 : Blo 1457548 2459963 := bstep (se 1 (by rfl) ⟨1844972, by rfl⟩ : syracuseStep 2459963 = 3689945) B3689945
theorem B8309051 : Blo 1457548 8309051 := bstep (se 1 (by rfl) ⟨6231788, by rfl⟩ : syracuseStep 8309051 = 12463577) B12463577
theorem B1640839 : Blo 1457548 1640839 := bstep (se 1 (by rfl) ⟨1230629, by rfl⟩ : syracuseStep 1640839 = 2461259) B2461259
theorem B5613959 : Blo 1457548 5613959 := bstep (se 1 (by rfl) ⟨4210469, by rfl⟩ : syracuseStep 5613959 = 8420939) B8420939
theorem B1845767 : Blo 1457548 1845767 := bstep (se 1 (by rfl) ⟨1384325, by rfl⟩ : syracuseStep 1845767 = 2768651) B2768651
theorem B1641019 : Blo 1457548 1641019 := bstep (se 1 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 1641019 = 2461529) B2461529
theorem B3115579 : Blo 1457548 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B4156019 : Blo 1457548 4156019 := bstep (se 1 (by rfl) ⟨3117014, by rfl⟩ : syracuseStep 4156019 = 6234029) B6234029
theorem B2075321 : Blo 1457548 2075321 := bstep (se 2 (by rfl) ⟨778245, by rfl⟩ : syracuseStep 2075321 = 1556491) B1556491
theorem B3279545 : Blo 1457548 3279545 := bstep (se 2 (by rfl) ⟨1229829, by rfl⟩ : syracuseStep 3279545 = 2459659) B2459659
theorem B2247355 : Blo 1457548 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B2460361 : Blo 1457548 2460361 := bstep (se 2 (by rfl) ⟨922635, by rfl⟩ : syracuseStep 2460361 = 1845271) B1845271
theorem B4434689 : Blo 1457548 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B18688805 : Blo 1457548 18688805 := bstep (se 4 (by rfl) ⟨1752075, by rfl⟩ : syracuseStep 18688805 = 3504151) B3504151
theorem B3279887 : Blo 1457548 3279887 := bstep (se 1 (by rfl) ⟨2459915, by rfl⟩ : syracuseStep 3279887 = 4919831) B4919831
theorem B1641487 : Blo 1457548 1641487 := bstep (se 1 (by rfl) ⟨1231115, by rfl⟩ : syracuseStep 1641487 = 2462231) B2462231
theorem B6229021 : Blo 1457548 6229021 := bstep (se 3 (by rfl) ⟨1167941, by rfl⟩ : syracuseStep 6229021 = 2335883) B2335883
theorem B3279905 : Blo 1457548 3279905 := bstep (se 2 (by rfl) ⟨1229964, by rfl⟩ : syracuseStep 3279905 = 2459929) B2459929
theorem B3116065 : Blo 1457548 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B1846415 : Blo 1457548 1846415 := bstep (se 1 (by rfl) ⟨1384811, by rfl⟩ : syracuseStep 1846415 = 2769623) B2769623
theorem B8301761 : Blo 1457548 8301761 := bstep (se 2 (by rfl) ⟨3113160, by rfl⟩ : syracuseStep 8301761 = 6226321) B6226321
theorem B1871095 : Blo 1457548 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B4435211 : Blo 1457548 4435211 := bstep (se 1 (by rfl) ⟨3326408, by rfl⟩ : syracuseStep 4435211 = 6652817) B6652817
theorem B6655247 : Blo 1457548 6655247 := bstep (se 1 (by rfl) ⟨4991435, by rfl⟩ : syracuseStep 6655247 = 9982871) B9982871
theorem B8310053 : Blo 1457548 8310053 := bstep (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) B1558135
theorem B3280247 : Blo 1457548 3280247 := bstep (se 1 (by rfl) ⟨2460185, by rfl⟩ : syracuseStep 3280247 = 4920371) B4920371
theorem B3116407 : Blo 1457548 3116407 := bstep (se 1 (by rfl) ⟨2337305, by rfl⟩ : syracuseStep 3116407 = 4674611) B4674611
theorem B2461063 : Blo 1457548 2461063 := bstep (se 1 (by rfl) ⟨1845797, by rfl⟩ : syracuseStep 2461063 = 3691595) B3691595
theorem B16838093 : Blo 1457548 16838093 := bstep (se 3 (by rfl) ⟨3157142, by rfl⟩ : syracuseStep 16838093 = 6314285) B6314285
theorem B31534595 : Blo 1457548 31534595 := bstep (se 1 (by rfl) ⟨23650946, by rfl⟩ : syracuseStep 31534595 = 47301893) B47301893
theorem B1641991 : Blo 1457548 1641991 := bstep (se 1 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 1641991 = 2462987) B2462987
theorem B3689995 : Blo 1457548 3689995 := bstep (se 1 (by rfl) ⟨2767496, by rfl⟩ : syracuseStep 3689995 = 5534993) B5534993
theorem B3280427 : Blo 1457548 3280427 := bstep (se 1 (by rfl) ⟨2460320, by rfl⟩ : syracuseStep 3280427 = 4920641) B4920641
theorem B133107313 : Blo 1457548 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B2076295 : Blo 1457548 2076295 := bstep (se 1 (by rfl) ⟨1557221, by rfl⟩ : syracuseStep 2076295 = 3114443) B3114443
theorem B3690137 : Blo 1457548 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B7384769 : Blo 1457548 7384769 := bstep (se 2 (by rfl) ⟨2769288, by rfl⟩ : syracuseStep 7384769 = 5538577) B5538577
theorem B8310509 : Blo 1457548 8310509 := bstep (se 3 (by rfl) ⟨1558220, by rfl⟩ : syracuseStep 8310509 = 3116441) B3116441
theorem B17747747 : Blo 1457548 17747747 := bstep (se 1 (by rfl) ⟨13310810, by rfl⟩ : syracuseStep 17747747 = 26621621) B26621621
theorem B3690299 : Blo 1457548 3690299 := bstep (se 1 (by rfl) ⟨2767724, by rfl⟩ : syracuseStep 3690299 = 5535449) B5535449
theorem B3280787 : Blo 1457548 3280787 := bstep (se 1 (by rfl) ⟨2460590, by rfl⟩ : syracuseStep 3280787 = 4921181) B4921181
theorem B26619799 : Blo 1457548 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B9351065 : Blo 1457548 9351065 := bstep (se 2 (by rfl) ⟨3506649, by rfl⟩ : syracuseStep 9351065 = 7013299) B7013299
theorem B3280841 : Blo 1457548 3280841 := bstep (se 2 (by rfl) ⟨1230315, by rfl⟩ : syracuseStep 3280841 = 2460631) B2460631
theorem B2461711 : Blo 1457548 2461711 := bstep (se 1 (by rfl) ⟨1846283, by rfl⟩ : syracuseStep 2461711 = 3692567) B3692567
theorem B3690643 : Blo 1457548 3690643 := bstep (se 1 (by rfl) ⟨2767982, by rfl⟩ : syracuseStep 3690643 = 5535965) B5535965
theorem B3690785 : Blo 1457548 3690785 := bstep (se 2 (by rfl) ⟨1384044, by rfl⟩ : syracuseStep 3690785 = 2768089) B2768089
theorem B8311193 : Blo 1457548 8311193 := bstep (se 2 (by rfl) ⟨3116697, by rfl⟩ : syracuseStep 8311193 = 6233395) B6233395
theorem B14963129 : Blo 1457548 14963129 := bstep (se 2 (by rfl) ⟨5611173, by rfl⟩ : syracuseStep 14963129 = 11222347) B11222347
theorem B5911051 : Blo 1457548 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B2462251 : Blo 1457548 2462251 := bstep (se 1 (by rfl) ⟨1846688, by rfl⟩ : syracuseStep 2462251 = 3693377) B3693377
theorem B3281543 : Blo 1457548 3281543 := bstep (se 1 (by rfl) ⟨2461157, by rfl⟩ : syracuseStep 3281543 = 4922315) B4922315
theorem B2462393 : Blo 1457548 2462393 := bstep (se 2 (by rfl) ⟨923397, by rfl⟩ : syracuseStep 2462393 = 1846795) B1846795
theorem B3281723 : Blo 1457548 3281723 := bstep (se 1 (by rfl) ⟨2461292, by rfl⟩ : syracuseStep 3281723 = 4922585) B4922585
theorem B2216875 : Blo 1457548 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B3281849 : Blo 1457548 3281849 := bstep (se 2 (by rfl) ⟨1230693, by rfl⟩ : syracuseStep 3281849 = 2461387) B2461387
theorem B6230969 : Blo 1457548 6230969 := bstep (se 2 (by rfl) ⟨2336613, by rfl⟩ : syracuseStep 6230969 = 4673227) B4673227
theorem B1971145 : Blo 1457548 1971145 := bstep (se 2 (by rfl) ⟨739179, by rfl⟩ : syracuseStep 1971145 = 1478359) B1478359
theorem B7386065 : Blo 1457548 7386065 := bstep (se 2 (by rfl) ⟨2769774, by rfl⟩ : syracuseStep 7386065 = 5539549) B5539549
theorem B14021677 : Blo 1457548 14021677 := bstep (se 3 (by rfl) ⟨2629064, by rfl⟩ : syracuseStep 14021677 = 5258129) B5258129
theorem B2077753 : Blo 1457548 2077753 := bstep (se 2 (by rfl) ⟨779157, by rfl⟩ : syracuseStep 2077753 = 1558315) B1558315
theorem B1971319 : Blo 1457548 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B12465353 : Blo 1457548 12465353 := bstep (se 2 (by rfl) ⟨4674507, by rfl⟩ : syracuseStep 12465353 = 9349015) B9349015
theorem B3691777 : Blo 1457548 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B3282191 : Blo 1457548 3282191 := bstep (se 1 (by rfl) ⟨2461643, by rfl⟩ : syracuseStep 3282191 = 4923287) B4923287
theorem B28038433 : Blo 1457548 28038433 := bstep (se 2 (by rfl) ⟨10514412, by rfl⟩ : syracuseStep 28038433 = 21028825) B21028825
theorem B3282209 : Blo 1457548 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B6231431 : Blo 1457548 6231431 := bstep (se 1 (by rfl) ⟨4673573, by rfl⟩ : syracuseStep 6231431 = 9347147) B9347147
theorem B5535161 : Blo 1457548 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B2627191 : Blo 1457548 2627191 := bstep (se 1 (by rfl) ⟨1970393, by rfl⟩ : syracuseStep 2627191 = 3940787) B3940787
theorem B3282551 : Blo 1457548 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B16610993 : Blo 1457548 16610993 := bstep (se 2 (by rfl) ⟨6229122, by rfl⟩ : syracuseStep 16610993 = 12458245) B12458245
theorem B2496271 : Blo 1457548 2496271 := bstep (se 1 (by rfl) ⟨1872203, by rfl⟩ : syracuseStep 2496271 = 3744407) B3744407
theorem B11835173 : Blo 1457548 11835173 := bstep (se 4 (by rfl) ⟨1109547, by rfl⟩ : syracuseStep 11835173 = 2219095) B2219095
theorem B3282731 : Blo 1457548 3282731 := bstep (se 1 (by rfl) ⟨2462048, by rfl⟩ : syracuseStep 3282731 = 4924097) B4924097
theorem B4437803 : Blo 1457548 4437803 := bstep (se 1 (by rfl) ⟨3328352, by rfl⟩ : syracuseStep 4437803 = 6656705) B6656705
theorem B2627387 : Blo 1457548 2627387 := bstep (se 1 (by rfl) ⟨1970540, by rfl⟩ : syracuseStep 2627387 = 3941081) B3941081
theorem B3692375 : Blo 1457548 3692375 := bstep (se 1 (by rfl) ⟨2769281, by rfl⟩ : syracuseStep 3692375 = 5538563) B5538563
theorem B4921235 : Blo 1457548 4921235 := bstep (se 1 (by rfl) ⟨3690926, by rfl⟩ : syracuseStep 4921235 = 7381853) B7381853
theorem B14022679 : Blo 1457548 14022679 := bstep (se 1 (by rfl) ⟨10517009, by rfl⟩ : syracuseStep 14022679 = 21034019) B21034019
theorem B3692587 : Blo 1457548 3692587 := bstep (se 1 (by rfl) ⟨2769440, by rfl⟩ : syracuseStep 3692587 = 5538881) B5538881
theorem B3283091 : Blo 1457548 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B3692729 : Blo 1457548 3692729 := bstep (se 2 (by rfl) ⟨1384773, by rfl⟩ : syracuseStep 3692729 = 2769547) B2769547
theorem B3283145 : Blo 1457548 3283145 := bstep (se 2 (by rfl) ⟨1231179, by rfl⟩ : syracuseStep 3283145 = 2462359) B2462359
theorem B8304929 : Blo 1457548 8304929 := bstep (se 2 (by rfl) ⟨3114348, by rfl⟩ : syracuseStep 8304929 = 6228697) B6228697
theorem B4266283 : Blo 1457548 4266283 := bstep (se 1 (by rfl) ⟨3199712, by rfl⟩ : syracuseStep 4266283 = 6399425) B6399425
theorem B2767223 : Blo 1457548 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B5536147 : Blo 1457548 5536147 := bstep (se 1 (by rfl) ⟨4152110, by rfl⟩ : syracuseStep 5536147 = 8304221) B8304221
theorem B13490641 : Blo 1457548 13490641 := bstep (se 2 (by rfl) ⟨5058990, by rfl⟩ : syracuseStep 13490641 = 10117981) B10117981
theorem B2767375 : Blo 1457548 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B4151837 : Blo 1457548 4151837 := bstep (se 3 (by rfl) ⟨778469, by rfl⟩ : syracuseStep 4151837 = 1556939) B1556939
theorem B11377219 : Blo 1457548 11377219 := bstep (se 1 (by rfl) ⟨8532914, by rfl⟩ : syracuseStep 11377219 = 17065829) B17065829
theorem B28031669 : Blo 1457548 28031669 := bstep (se 5 (by rfl) ⟨1313984, by rfl⟩ : syracuseStep 28031669 = 2627969) B2627969
theorem B12466993 : Blo 1457548 12466993 := bstep (se 2 (by rfl) ⟨4675122, by rfl⟩ : syracuseStep 12466993 = 9350245) B9350245
theorem B3283847 : Blo 1457548 3283847 := bstep (se 1 (by rfl) ⟨2462885, by rfl⟩ : syracuseStep 3283847 = 4925771) B4925771
theorem B2767763 : Blo 1457548 2767763 := bstep (se 1 (by rfl) ⟨2075822, by rfl⟩ : syracuseStep 2767763 = 4151645) B4151645
theorem B7388171 : Blo 1457548 7388171 := bstep (se 1 (by rfl) ⟨5541128, by rfl⟩ : syracuseStep 7388171 = 11082257) B11082257
theorem B2186375 : Blo 1457548 2186375 := bstep (se 1 (by rfl) ⟨1639781, by rfl⟩ : syracuseStep 2186375 = 3279563) B3279563
theorem B3693721 : Blo 1457548 3693721 := bstep (se 2 (by rfl) ⟨1385145, by rfl⟩ : syracuseStep 3693721 = 2770291) B2770291
theorem B2186411 : Blo 1457548 2186411 := bstep (se 1 (by rfl) ⟨1639808, by rfl⟩ : syracuseStep 2186411 = 3279617) B3279617
theorem B7388333 : Blo 1457548 7388333 := bstep (se 3 (by rfl) ⟨1385312, by rfl⟩ : syracuseStep 7388333 = 2770625) B2770625
theorem B2186441 : Blo 1457548 2186441 := bstep (se 2 (by rfl) ⟨819915, by rfl⟩ : syracuseStep 2186441 = 1639831) B1639831
theorem B4152521 : Blo 1457548 4152521 := bstep (se 2 (by rfl) ⟨1557195, by rfl⟩ : syracuseStep 4152521 = 3114391) B3114391
theorem B6233345 : Blo 1457548 6233345 := bstep (se 2 (by rfl) ⟨2337504, by rfl⟩ : syracuseStep 6233345 = 4675009) B4675009
theorem B4922639 : Blo 1457548 4922639 := bstep (se 1 (by rfl) ⟨3691979, by rfl⟩ : syracuseStep 4922639 = 7383959) B7383959
theorem B3743009 : Blo 1457548 3743009 := bstep (se 2 (by rfl) ⟨1403628, by rfl⟩ : syracuseStep 3743009 = 2807257) B2807257
theorem B2186555 : Blo 1457548 2186555 := bstep (se 1 (by rfl) ⟨1639916, by rfl⟩ : syracuseStep 2186555 = 3279833) B3279833
theorem B3693883 : Blo 1457548 3693883 := bstep (se 1 (by rfl) ⟨2770412, by rfl⟩ : syracuseStep 3693883 = 5540825) B5540825
theorem B5913971 : Blo 1457548 5913971 := bstep (se 1 (by rfl) ⟨4435478, by rfl⟩ : syracuseStep 5913971 = 8870957) B8870957
theorem B2186615 : Blo 1457548 2186615 := bstep (se 1 (by rfl) ⟨1639961, by rfl⟩ : syracuseStep 2186615 = 3279923) B3279923
theorem B15777155 : Blo 1457548 15777155 := bstep (se 1 (by rfl) ⟨11832866, by rfl⟩ : syracuseStep 15777155 = 23665733) B23665733
theorem B1457551 : Blo 1457548 1457551 := bstep (se 1 (by rfl) ⟨1093163, by rfl⟩ : syracuseStep 1457551 = 2186327) B2186327
theorem B2186639 : Blo 1457548 2186639 := bstep (se 1 (by rfl) ⟨1639979, by rfl⟩ : syracuseStep 2186639 = 3279959) B3279959
theorem B2186681 : Blo 1457548 2186681 := bstep (se 2 (by rfl) ⟨820005, by rfl⟩ : syracuseStep 2186681 = 1640011) B1640011
theorem B1457595 : Blo 1457548 1457595 := bstep (se 1 (by rfl) ⟨1093196, by rfl⟩ : syracuseStep 1457595 = 2186393) B2186393
theorem B3694025 : Blo 1457548 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B63053261 : Blo 1457548 63053261 := bstep (se 3 (by rfl) ⟨11822486, by rfl⟩ : syracuseStep 63053261 = 23644973) B23644973
theorem B11083229 : Blo 1457548 11083229 := bstep (se 3 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 11083229 = 4156211) B4156211
theorem B1457671 : Blo 1457548 1457671 := bstep (se 1 (by rfl) ⟨1093253, by rfl⟩ : syracuseStep 1457671 = 2186507) B2186507
theorem B2186759 : Blo 1457548 2186759 := bstep (se 1 (by rfl) ⟨1640069, by rfl⟩ : syracuseStep 2186759 = 3280139) B3280139
theorem B1457679 : Blo 1457548 1457679 := bstep (se 1 (by rfl) ⟨1093259, by rfl⟩ : syracuseStep 1457679 = 2186519) B2186519
theorem B4922909 : Blo 1457548 4922909 := bstep (se 3 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 4922909 = 1846091) B1846091
theorem B2186795 : Blo 1457548 2186795 := bstep (se 1 (by rfl) ⟨1640096, by rfl⟩ : syracuseStep 2186795 = 3280193) B3280193
theorem B1457723 : Blo 1457548 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B2186825 : Blo 1457548 2186825 := bstep (se 2 (by rfl) ⟨820059, by rfl⟩ : syracuseStep 2186825 = 1640119) B1640119
theorem B1457799 : Blo 1457548 1457799 := bstep (se 1 (by rfl) ⟨1093349, by rfl⟩ : syracuseStep 1457799 = 2186699) B2186699
theorem B1457807 : Blo 1457548 1457807 := bstep (se 1 (by rfl) ⟨1093355, by rfl⟩ : syracuseStep 1457807 = 2186711) B2186711
theorem B1457851 : Blo 1457548 1457851 := bstep (se 1 (by rfl) ⟨1093388, by rfl⟩ : syracuseStep 1457851 = 2186777) B2186777
theorem B2186939 : Blo 1457548 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B7880429 : Blo 1457548 7880429 := bstep (se 3 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 7880429 = 2955161) B2955161
theorem B2186999 : Blo 1457548 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B7880449 : Blo 1457548 7880449 := bstep (se 2 (by rfl) ⟨2955168, by rfl⟩ : syracuseStep 7880449 = 5910337) B5910337
theorem B1457927 : Blo 1457548 1457927 := bstep (se 1 (by rfl) ⟨1093445, by rfl⟩ : syracuseStep 1457927 = 2186891) B2186891
theorem B1457935 : Blo 1457548 1457935 := bstep (se 1 (by rfl) ⟨1093451, by rfl⟩ : syracuseStep 1457935 = 2186903) B2186903
theorem B2187023 : Blo 1457548 2187023 := bstep (se 1 (by rfl) ⟨1640267, by rfl⟩ : syracuseStep 2187023 = 3280535) B3280535
theorem B4153103 : Blo 1457548 4153103 := bstep (se 1 (by rfl) ⟨3114827, by rfl⟩ : syracuseStep 4153103 = 6229655) B6229655
theorem B3694369 : Blo 1457548 3694369 := bstep (se 2 (by rfl) ⟨1385388, by rfl⟩ : syracuseStep 3694369 = 2770777) B2770777
theorem B2187065 : Blo 1457548 2187065 := bstep (se 2 (by rfl) ⟨820149, by rfl⟩ : syracuseStep 2187065 = 1640299) B1640299
theorem B1457979 : Blo 1457548 1457979 := bstep (se 1 (by rfl) ⟨1093484, by rfl⟩ : syracuseStep 1457979 = 2186969) B2186969
theorem B1458055 : Blo 1457548 1458055 := bstep (se 1 (by rfl) ⟨1093541, by rfl⟩ : syracuseStep 1458055 = 2187083) B2187083
theorem B2187143 : Blo 1457548 2187143 := bstep (se 1 (by rfl) ⟨1640357, by rfl⟩ : syracuseStep 2187143 = 3280715) B3280715
theorem B1458063 : Blo 1457548 1458063 := bstep (se 1 (by rfl) ⟨1093547, by rfl⟩ : syracuseStep 1458063 = 2187095) B2187095
theorem B7380881 : Blo 1457548 7380881 := bstep (se 2 (by rfl) ⟨2767830, by rfl⟩ : syracuseStep 7380881 = 5535661) B5535661
theorem B2187179 : Blo 1457548 2187179 := bstep (se 1 (by rfl) ⟨1640384, by rfl⟩ : syracuseStep 2187179 = 3280769) B3280769
theorem B1458107 : Blo 1457548 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B2187209 : Blo 1457548 2187209 := bstep (se 2 (by rfl) ⟨820203, by rfl⟩ : syracuseStep 2187209 = 1640407) B1640407
theorem B1458215 : Blo 1457548 1458215 := bstep (se 1 (by rfl) ⟨1093661, by rfl⟩ : syracuseStep 1458215 = 2187323) B2187323
theorem B4923449 : Blo 1457548 4923449 := bstep (se 2 (by rfl) ⟨1846293, by rfl⟩ : syracuseStep 4923449 = 3692587) B3692587
theorem B1458255 : Blo 1457548 1458255 := bstep (se 1 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 1458255 = 2187383) B2187383
theorem B9338969 : Blo 1457548 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B1458271 : Blo 1457548 1458271 := bstep (se 1 (by rfl) ⟨1093703, by rfl⟩ : syracuseStep 1458271 = 2187407) B2187407
theorem B1458299 : Blo 1457548 1458299 := bstep (se 1 (by rfl) ⟨1093724, by rfl⟩ : syracuseStep 1458299 = 2187449) B2187449
theorem B1458351 : Blo 1457548 1458351 := bstep (se 1 (by rfl) ⟨1093763, by rfl⟩ : syracuseStep 1458351 = 2187527) B2187527
theorem B1458375 : Blo 1457548 1458375 := bstep (se 1 (by rfl) ⟨1093781, by rfl⟩ : syracuseStep 1458375 = 2187563) B2187563
theorem B1458395 : Blo 1457548 1458395 := bstep (se 1 (by rfl) ⟨1093796, by rfl⟩ : syracuseStep 1458395 = 2187593) B2187593
theorem B1458471 : Blo 1457548 1458471 := bstep (se 1 (by rfl) ⟨1093853, by rfl⟩ : syracuseStep 1458471 = 2187707) B2187707
theorem B1458511 : Blo 1457548 1458511 := bstep (se 1 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 1458511 = 2187767) B2187767
theorem B1458527 : Blo 1457548 1458527 := bstep (se 1 (by rfl) ⟨1093895, by rfl⟩ : syracuseStep 1458527 = 2187791) B2187791
theorem B1458555 : Blo 1457548 1458555 := bstep (se 1 (by rfl) ⟨1093916, by rfl⟩ : syracuseStep 1458555 = 2187833) B2187833
theorem B4923773 : Blo 1457548 4923773 := bstep (se 3 (by rfl) ⟨923207, by rfl⟩ : syracuseStep 4923773 = 1846415) B1846415
theorem B2187695 : Blo 1457548 2187695 := bstep (se 1 (by rfl) ⟨1640771, by rfl⟩ : syracuseStep 2187695 = 3281543) B3281543
theorem B1458607 : Blo 1457548 1458607 := bstep (se 1 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 1458607 = 2187911) B2187911
theorem B1458631 : Blo 1457548 1458631 := bstep (se 1 (by rfl) ⟨1093973, by rfl⟩ : syracuseStep 1458631 = 2187947) B2187947
theorem B1458651 : Blo 1457548 1458651 := bstep (se 1 (by rfl) ⟨1093988, by rfl⟩ : syracuseStep 1458651 = 2187977) B2187977
theorem B2187785 : Blo 1457548 2187785 := bstep (se 2 (by rfl) ⟨820419, by rfl⟩ : syracuseStep 2187785 = 1640839) B1640839
theorem B7381529 : Blo 1457548 7381529 := bstep (se 2 (by rfl) ⟨2768073, by rfl⟩ : syracuseStep 7381529 = 5536147) B5536147
theorem B2187815 : Blo 1457548 2187815 := bstep (se 1 (by rfl) ⟨1640861, by rfl⟩ : syracuseStep 2187815 = 3281723) B3281723
theorem B1458727 : Blo 1457548 1458727 := bstep (se 1 (by rfl) ⟨1094045, by rfl⟩ : syracuseStep 1458727 = 2188091) B2188091
theorem B1458767 : Blo 1457548 1458767 := bstep (se 1 (by rfl) ⟨1094075, by rfl⟩ : syracuseStep 1458767 = 2188151) B2188151
theorem B1458783 : Blo 1457548 1458783 := bstep (se 1 (by rfl) ⟨1094087, by rfl⟩ : syracuseStep 1458783 = 2188175) B2188175
theorem B2187899 : Blo 1457548 2187899 := bstep (se 1 (by rfl) ⟨1640924, by rfl⟩ : syracuseStep 2187899 = 3281849) B3281849
theorem B4153979 : Blo 1457548 4153979 := bstep (se 1 (by rfl) ⟨3115484, by rfl⟩ : syracuseStep 4153979 = 6230969) B6230969
theorem B1458811 : Blo 1457548 1458811 := bstep (se 1 (by rfl) ⟨1094108, by rfl⟩ : syracuseStep 1458811 = 2188217) B2188217
theorem B4924043 : Blo 1457548 4924043 := bstep (se 1 (by rfl) ⟨3693032, by rfl⟩ : syracuseStep 4924043 = 7386065) B7386065
theorem B1458863 : Blo 1457548 1458863 := bstep (se 1 (by rfl) ⟨1094147, by rfl⟩ : syracuseStep 1458863 = 2188295) B2188295
theorem B7881401 : Blo 1457548 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B1458887 : Blo 1457548 1458887 := bstep (se 1 (by rfl) ⟨1094165, by rfl⟩ : syracuseStep 1458887 = 2188331) B2188331
theorem B1458907 : Blo 1457548 1458907 := bstep (se 1 (by rfl) ⟨1094180, by rfl⟩ : syracuseStep 1458907 = 2188361) B2188361
theorem B2188025 : Blo 1457548 2188025 := bstep (se 2 (by rfl) ⟨820509, by rfl⟩ : syracuseStep 2188025 = 1641019) B1641019
theorem B4154105 : Blo 1457548 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B1458983 : Blo 1457548 1458983 := bstep (se 1 (by rfl) ⟨1094237, by rfl⟩ : syracuseStep 1458983 = 2188475) B2188475
theorem B11076425 : Blo 1457548 11076425 := bstep (se 2 (by rfl) ⟨4153659, by rfl⟩ : syracuseStep 11076425 = 8307319) B8307319
theorem B1459023 : Blo 1457548 1459023 := bstep (se 1 (by rfl) ⟨1094267, by rfl⟩ : syracuseStep 1459023 = 2188535) B2188535
theorem B2188127 : Blo 1457548 2188127 := bstep (se 1 (by rfl) ⟨1641095, by rfl⟩ : syracuseStep 2188127 = 3282191) B3282191
theorem B1459039 : Blo 1457548 1459039 := bstep (se 1 (by rfl) ⟨1094279, by rfl⟩ : syracuseStep 1459039 = 2188559) B2188559
theorem B2188139 : Blo 1457548 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B1459067 : Blo 1457548 1459067 := bstep (se 1 (by rfl) ⟨1094300, by rfl⟩ : syracuseStep 1459067 = 2188601) B2188601
theorem B4154287 : Blo 1457548 4154287 := bstep (se 1 (by rfl) ⟨3115715, by rfl⟩ : syracuseStep 4154287 = 6231431) B6231431
theorem B1459119 : Blo 1457548 1459119 := bstep (se 1 (by rfl) ⟨1094339, by rfl⟩ : syracuseStep 1459119 = 2188679) B2188679
theorem B2769851 : Blo 1457548 2769851 := bstep (se 1 (by rfl) ⟨2077388, by rfl⟩ : syracuseStep 2769851 = 4154777) B4154777
theorem B1459143 : Blo 1457548 1459143 := bstep (se 1 (by rfl) ⟨1094357, by rfl⟩ : syracuseStep 1459143 = 2188715) B2188715
theorem B1459163 : Blo 1457548 1459163 := bstep (se 1 (by rfl) ⟨1094372, by rfl⟩ : syracuseStep 1459163 = 2188745) B2188745
theorem B11985893 : Blo 1457548 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B1459239 : Blo 1457548 1459239 := bstep (se 1 (by rfl) ⟨1094429, by rfl⟩ : syracuseStep 1459239 = 2188859) B2188859
theorem B16622657 : Blo 1457548 16622657 := bstep (se 2 (by rfl) ⟨6233496, by rfl⟩ : syracuseStep 16622657 = 12466993) B12466993
theorem B2188367 : Blo 1457548 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B1459279 : Blo 1457548 1459279 := bstep (se 1 (by rfl) ⟨1094459, by rfl⟩ : syracuseStep 1459279 = 2188919) B2188919
theorem B1459295 : Blo 1457548 1459295 := bstep (se 1 (by rfl) ⟨1094471, by rfl⟩ : syracuseStep 1459295 = 2188943) B2188943
theorem B1459323 : Blo 1457548 1459323 := bstep (se 1 (by rfl) ⟨1094492, by rfl⟩ : syracuseStep 1459323 = 2188985) B2188985
theorem B1459375 : Blo 1457548 1459375 := bstep (se 1 (by rfl) ⟨1094531, by rfl⟩ : syracuseStep 1459375 = 2189063) B2189063
theorem B2188487 : Blo 1457548 2188487 := bstep (se 1 (by rfl) ⟨1641365, by rfl⟩ : syracuseStep 2188487 = 3282731) B3282731
theorem B2958535 : Blo 1457548 2958535 := bstep (se 1 (by rfl) ⟨2218901, by rfl⟩ : syracuseStep 2958535 = 4437803) B4437803
theorem B1459399 : Blo 1457548 1459399 := bstep (se 1 (by rfl) ⟨1094549, by rfl⟩ : syracuseStep 1459399 = 2189099) B2189099
theorem B1459419 : Blo 1457548 1459419 := bstep (se 1 (by rfl) ⟨1094564, by rfl⟩ : syracuseStep 1459419 = 2189129) B2189129
theorem B5539063 : Blo 1457548 5539063 := bstep (se 1 (by rfl) ⟨4154297, by rfl⟩ : syracuseStep 5539063 = 8308595) B8308595
theorem B1459495 : Blo 1457548 1459495 := bstep (se 1 (by rfl) ⟨1094621, by rfl⟩ : syracuseStep 1459495 = 2189243) B2189243
theorem B1459535 : Blo 1457548 1459535 := bstep (se 1 (by rfl) ⟨1094651, by rfl⟩ : syracuseStep 1459535 = 2189303) B2189303
theorem B2188649 : Blo 1457548 2188649 := bstep (se 2 (by rfl) ⟨820743, by rfl⟩ : syracuseStep 2188649 = 1641487) B1641487
theorem B4154753 : Blo 1457548 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B18695569 : Blo 1457548 18695569 := bstep (se 2 (by rfl) ⟨7010838, by rfl⟩ : syracuseStep 18695569 = 14021677) B14021677
theorem B2770337 : Blo 1457548 2770337 := bstep (se 2 (by rfl) ⟨1038876, by rfl⟩ : syracuseStep 2770337 = 2077753) B2077753
theorem B2188727 : Blo 1457548 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B2188763 : Blo 1457548 2188763 := bstep (se 1 (by rfl) ⟨1641572, by rfl⟩ : syracuseStep 2188763 = 3283145) B3283145
theorem B5539337 : Blo 1457548 5539337 := bstep (se 2 (by rfl) ⟨2077251, by rfl⟩ : syracuseStep 5539337 = 4154503) B4154503
theorem B4924961 : Blo 1457548 4924961 := bstep (se 2 (by rfl) ⟨1846860, by rfl⟩ : syracuseStep 4924961 = 3693721) B3693721
theorem B47285795 : Blo 1457548 47285795 := bstep (se 1 (by rfl) ⟨35464346, by rfl⟩ : syracuseStep 47285795 = 70928693) B70928693
theorem B1639975 : Blo 1457548 1639975 := bstep (se 1 (by rfl) ⟨1229981, by rfl⟩ : syracuseStep 1639975 = 2459963) B2459963
theorem B5539367 : Blo 1457548 5539367 := bstep (se 1 (by rfl) ⟨4154525, by rfl⟩ : syracuseStep 5539367 = 8309051) B8309051
theorem B2770679 : Blo 1457548 2770679 := bstep (se 1 (by rfl) ⟨2078009, by rfl⟩ : syracuseStep 2770679 = 4156019) B4156019
theorem B4925177 : Blo 1457548 4925177 := bstep (se 2 (by rfl) ⟨1846941, by rfl⟩ : syracuseStep 4925177 = 3693883) B3693883
theorem B18687779 : Blo 1457548 18687779 := bstep (se 1 (by rfl) ⟨14015834, by rfl⟩ : syracuseStep 18687779 = 28031669) B28031669
theorem B4155209 : Blo 1457548 4155209 := bstep (se 2 (by rfl) ⟨1558203, by rfl⟩ : syracuseStep 4155209 = 3116407) B3116407
theorem B2189231 : Blo 1457548 2189231 := bstep (se 1 (by rfl) ⟨1641923, by rfl⟩ : syracuseStep 2189231 = 3283847) B3283847
theorem B1845175 : Blo 1457548 1845175 := bstep (se 1 (by rfl) ⟨1383881, by rfl⟩ : syracuseStep 1845175 = 2767763) B2767763
theorem B4925447 : Blo 1457548 4925447 := bstep (se 1 (by rfl) ⟨3694085, by rfl⟩ : syracuseStep 4925447 = 7388171) B7388171
theorem B2189321 : Blo 1457548 2189321 := bstep (se 2 (by rfl) ⟨820995, by rfl⟩ : syracuseStep 2189321 = 1641991) B1641991
theorem B4925555 : Blo 1457548 4925555 := bstep (se 1 (by rfl) ⟨3694166, by rfl⟩ : syracuseStep 4925555 = 7388333) B7388333
theorem B4155563 : Blo 1457548 4155563 := bstep (se 1 (by rfl) ⟨3116672, by rfl⟩ : syracuseStep 4155563 = 6233345) B6233345
theorem B5540035 : Blo 1457548 5540035 := bstep (se 1 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 5540035 = 8310053) B8310053
theorem B3942647 : Blo 1457548 3942647 := bstep (se 1 (by rfl) ⟨2956985, by rfl⟩ : syracuseStep 3942647 = 5913971) B5913971
theorem B12454145 : Blo 1457548 12454145 := bstep (se 2 (by rfl) ⟨4670304, by rfl⟩ : syracuseStep 12454145 = 9340609) B9340609
theorem B42035507 : Blo 1457548 42035507 := bstep (se 1 (by rfl) ⟨31526630, by rfl⟩ : syracuseStep 42035507 = 63053261) B63053261
theorem B11225395 : Blo 1457548 11225395 := bstep (se 1 (by rfl) ⟨8419046, by rfl⟩ : syracuseStep 11225395 = 16838093) B16838093
theorem B21023063 : Blo 1457548 21023063 := bstep (se 1 (by rfl) ⟨15767297, by rfl⟩ : syracuseStep 21023063 = 31534595) B31534595
theorem B3328361 : Blo 1457548 3328361 := bstep (se 2 (by rfl) ⟨1248135, by rfl⟩ : syracuseStep 3328361 = 2496271) B2496271
theorem B4925825 : Blo 1457548 4925825 := bstep (se 2 (by rfl) ⟨1847184, by rfl⟩ : syracuseStep 4925825 = 3694369) B3694369
theorem B10512773 : Blo 1457548 10512773 := bstep (se 4 (by rfl) ⟨985572, by rfl⟩ : syracuseStep 10512773 = 1971145) B1971145
theorem B2460091 : Blo 1457548 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B5253619 : Blo 1457548 5253619 := bstep (se 1 (by rfl) ⟨3940214, by rfl⟩ : syracuseStep 5253619 = 7880429) B7880429
theorem B5540339 : Blo 1457548 5540339 := bstep (se 1 (by rfl) ⟨4155254, by rfl⟩ : syracuseStep 5540339 = 8310509) B8310509
theorem B11831831 : Blo 1457548 11831831 := bstep (se 1 (by rfl) ⟨8873873, by rfl⟩ : syracuseStep 11831831 = 17747747) B17747747
theorem B2460199 : Blo 1457548 2460199 := bstep (se 1 (by rfl) ⟨1845149, by rfl⟩ : syracuseStep 2460199 = 3690299) B3690299
theorem B18696905 : Blo 1457548 18696905 := bstep (se 2 (by rfl) ⟨7011339, by rfl⟩ : syracuseStep 18696905 = 14022679) B14022679
theorem B3279689 : Blo 1457548 3279689 := bstep (se 2 (by rfl) ⟨1229883, by rfl⟩ : syracuseStep 3279689 = 2459767) B2459767
theorem B16608077 : Blo 1457548 16608077 := bstep (se 3 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 16608077 = 6228029) B6228029
theorem B23989085 : Blo 1457548 23989085 := bstep (se 3 (by rfl) ⟨4497953, by rfl⟩ : syracuseStep 23989085 = 8995907) B8995907
theorem B2460523 : Blo 1457548 2460523 := bstep (se 1 (by rfl) ⟨1845392, by rfl⟩ : syracuseStep 2460523 = 3690785) B3690785
theorem B8301487 : Blo 1457548 8301487 := bstep (se 1 (by rfl) ⟨6226115, by rfl⟩ : syracuseStep 8301487 = 12452231) B12452231
theorem B5540795 : Blo 1457548 5540795 := bstep (se 1 (by rfl) ⟨4155596, by rfl⟩ : syracuseStep 5540795 = 8311193) B8311193
theorem B5688377 : Blo 1457548 5688377 := bstep (se 2 (by rfl) ⟨2133141, by rfl⟩ : syracuseStep 5688377 = 4266283) B4266283
theorem B1641595 : Blo 1457548 1641595 := bstep (se 1 (by rfl) ⟨1231196, by rfl⟩ : syracuseStep 1641595 = 2462393) B2462393
theorem B1846471 : Blo 1457548 1846471 := bstep (se 1 (by rfl) ⟨1384853, by rfl⟩ : syracuseStep 1846471 = 2769707) B2769707
theorem B3689833 : Blo 1457548 3689833 := bstep (se 2 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 3689833 = 2767375) B2767375
theorem B7384445 : Blo 1457548 7384445 := bstep (se 3 (by rfl) ⟨1384583, by rfl⟩ : syracuseStep 7384445 = 2769167) B2769167
theorem B8310235 : Blo 1457548 8310235 := bstep (se 1 (by rfl) ⟨6232676, by rfl⟩ : syracuseStep 8310235 = 12465353) B12465353
theorem B3280481 : Blo 1457548 3280481 := bstep (se 2 (by rfl) ⟨1230180, by rfl⟩ : syracuseStep 3280481 = 2460361) B2460361
theorem B3690107 : Blo 1457548 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B2076283 : Blo 1457548 2076283 := bstep (se 1 (by rfl) ⟨1557212, by rfl⟩ : syracuseStep 2076283 = 3114425) B3114425
theorem B14970557 : Blo 1457548 14970557 := bstep (se 3 (by rfl) ⟨2806979, by rfl⟩ : syracuseStep 14970557 = 5613959) B5613959
theorem B7122755 : Blo 1457548 7122755 := bstep (se 1 (by rfl) ⟨5342066, by rfl⟩ : syracuseStep 7122755 = 10684133) B10684133
theorem B2076511 : Blo 1457548 2076511 := bstep (se 1 (by rfl) ⟨1557383, by rfl⟩ : syracuseStep 2076511 = 3114767) B3114767
theorem B8302445 : Blo 1457548 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B2461583 : Blo 1457548 2461583 := bstep (se 1 (by rfl) ⟨1846187, by rfl⟩ : syracuseStep 2461583 = 3692375) B3692375
theorem B1847215 : Blo 1457548 1847215 := bstep (se 1 (by rfl) ⟨1385411, by rfl⟩ : syracuseStep 1847215 = 2770823) B2770823
theorem B3280823 : Blo 1457548 3280823 := bstep (se 1 (by rfl) ⟨2460617, by rfl⟩ : syracuseStep 3280823 = 4921235) B4921235
theorem B11071565 : Blo 1457548 11071565 := bstep (se 3 (by rfl) ⟨2075918, by rfl⟩ : syracuseStep 11071565 = 4151837) B4151837
theorem B2461819 : Blo 1457548 2461819 := bstep (se 1 (by rfl) ⟨1846364, by rfl⟩ : syracuseStep 2461819 = 3692729) B3692729
theorem B4919453 : Blo 1457548 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B11825315 : Blo 1457548 11825315 := bstep (se 1 (by rfl) ⟨8868986, by rfl⟩ : syracuseStep 11825315 = 17737973) B17737973
theorem B2494793 : Blo 1457548 2494793 := bstep (se 2 (by rfl) ⟨935547, by rfl⟩ : syracuseStep 2494793 = 1871095) B1871095
theorem B37384577 : Blo 1457548 37384577 := bstep (se 2 (by rfl) ⟨14019216, by rfl⟩ : syracuseStep 37384577 = 28038433) B28038433
theorem B5910985 : Blo 1457548 5910985 := bstep (se 2 (by rfl) ⟨2216619, by rfl⟩ : syracuseStep 5910985 = 4433239) B4433239
theorem B5534189 : Blo 1457548 5534189 := bstep (se 3 (by rfl) ⟨1037660, by rfl⟩ : syracuseStep 5534189 = 2075321) B2075321
theorem B3281417 : Blo 1457548 3281417 := bstep (se 2 (by rfl) ⟨1230531, by rfl⟩ : syracuseStep 3281417 = 2461063) B2461063
theorem B11825837 : Blo 1457548 11825837 := bstep (se 3 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 11825837 = 4434689) B4434689
theorem B4919993 : Blo 1457548 4919993 := bstep (se 2 (by rfl) ⟨1844997, by rfl⟩ : syracuseStep 4919993 = 3689995) B3689995
theorem B31560461 : Blo 1457548 31560461 := bstep (se 3 (by rfl) ⟨5917586, by rfl⟩ : syracuseStep 31560461 = 11835173) B11835173
theorem B5534507 : Blo 1457548 5534507 := bstep (se 1 (by rfl) ⟨4150880, by rfl⟩ : syracuseStep 5534507 = 8301761) B8301761
theorem B177476417 : Blo 1457548 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B3502921 : Blo 1457548 3502921 := bstep (se 2 (by rfl) ⟨1313595, by rfl⟩ : syracuseStep 3502921 = 2627191) B2627191
theorem B3281759 : Blo 1457548 3281759 := bstep (se 1 (by rfl) ⟨2461319, by rfl⟩ : syracuseStep 3281759 = 4922639) B4922639
theorem B4436831 : Blo 1457548 4436831 := bstep (se 1 (by rfl) ⟨3327623, by rfl⟩ : syracuseStep 4436831 = 6655247) B6655247
theorem B2495339 : Blo 1457548 2495339 := bstep (se 1 (by rfl) ⟨1871504, by rfl⟩ : syracuseStep 2495339 = 3743009) B3743009
theorem B2462683 : Blo 1457548 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B10507265 : Blo 1457548 10507265 := bstep (se 2 (by rfl) ⟨3940224, by rfl⟩ : syracuseStep 10507265 = 7880449) B7880449
theorem B3281939 : Blo 1457548 3281939 := bstep (se 1 (by rfl) ⟨2461454, by rfl⟩ : syracuseStep 3281939 = 4922909) B4922909
theorem B35493065 : Blo 1457548 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B4920587 : Blo 1457548 4920587 := bstep (se 1 (by rfl) ⟨3690440, by rfl⟩ : syracuseStep 4920587 = 7380881) B7380881
theorem B3282281 : Blo 1457548 3282281 := bstep (se 2 (by rfl) ⟨1230855, by rfl⟩ : syracuseStep 3282281 = 2461711) B2461711
theorem B3691919 : Blo 1457548 3691919 := bstep (se 1 (by rfl) ⟨2768939, by rfl⟩ : syracuseStep 3691919 = 5537879) B5537879
theorem B4920857 : Blo 1457548 4920857 := bstep (se 2 (by rfl) ⟨1845321, by rfl⟩ : syracuseStep 4920857 = 3690643) B3690643
theorem B9975419 : Blo 1457548 9975419 := bstep (se 1 (by rfl) ⟨7481564, by rfl⟩ : syracuseStep 9975419 = 14963129) B14963129
theorem B3692243 : Blo 1457548 3692243 := bstep (se 1 (by rfl) ⟨2769182, by rfl⟩ : syracuseStep 3692243 = 5538365) B5538365
theorem B42653441 : Blo 1457548 42653441 := bstep (se 2 (by rfl) ⟨15995040, by rfl⟩ : syracuseStep 42653441 = 31990081) B31990081
theorem B17979245 : Blo 1457548 17979245 := bstep (se 3 (by rfl) ⟨3371108, by rfl⟩ : syracuseStep 17979245 = 6742217) B6742217
theorem B3282875 : Blo 1457548 3282875 := bstep (se 1 (by rfl) ⟨2462156, by rfl⟩ : syracuseStep 3282875 = 4924313) B4924313
theorem B17987521 : Blo 1457548 17987521 := bstep (se 2 (by rfl) ⟨6745320, by rfl⟩ : syracuseStep 17987521 = 13490641) B13490641
theorem B8304677 : Blo 1457548 8304677 := bstep (se 4 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 8304677 = 1557127) B1557127
theorem B3283001 : Blo 1457548 3283001 := bstep (se 2 (by rfl) ⟨1231125, by rfl⟩ : syracuseStep 3283001 = 2462251) B2462251
theorem B15169625 : Blo 1457548 15169625 := bstep (se 2 (by rfl) ⟨5688609, by rfl⟩ : syracuseStep 15169625 = 11377219) B11377219
theorem B7379261 : Blo 1457548 7379261 := bstep (se 3 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 7379261 = 2767223) B2767223
theorem B3283343 : Blo 1457548 3283343 := bstep (se 1 (by rfl) ⟨2462507, by rfl⟩ : syracuseStep 3283343 = 4925015) B4925015
theorem B11073995 : Blo 1457548 11073995 := bstep (se 1 (by rfl) ⟨8305496, by rfl⟩ : syracuseStep 11073995 = 16610993) B16610993
theorem B1751591 : Blo 1457548 1751591 := bstep (se 1 (by rfl) ⟨1313693, by rfl⟩ : syracuseStep 1751591 = 2627387) B2627387
theorem B2955833 : Blo 1457548 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B4921991 : Blo 1457548 4921991 := bstep (se 1 (by rfl) ⟨3691493, by rfl⟩ : syracuseStep 4921991 = 7382987) B7382987
theorem B4922045 : Blo 1457548 4922045 := bstep (se 3 (by rfl) ⟨922883, by rfl⟩ : syracuseStep 4922045 = 1845767) B1845767
theorem B8305361 : Blo 1457548 8305361 := bstep (se 2 (by rfl) ⟨3114510, by rfl⟩ : syracuseStep 8305361 = 6229021) B6229021
theorem B3283667 : Blo 1457548 3283667 := bstep (se 1 (by rfl) ⟨2462750, by rfl⟩ : syracuseStep 3283667 = 4925501) B4925501
theorem B2628425 : Blo 1457548 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B4922207 : Blo 1457548 4922207 := bstep (se 1 (by rfl) ⟨3691655, by rfl⟩ : syracuseStep 4922207 = 7383311) B7383311
theorem B5536619 : Blo 1457548 5536619 := bstep (se 1 (by rfl) ⟨4152464, by rfl⟩ : syracuseStep 5536619 = 8304929) B8304929
theorem B4922369 : Blo 1457548 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B2219017 : Blo 1457548 2219017 := bstep (se 2 (by rfl) ⟨832131, by rfl⟩ : syracuseStep 2219017 = 1664263) B1664263
theorem B2186363 : Blo 1457548 2186363 := bstep (se 1 (by rfl) ⟨1639772, by rfl⟩ : syracuseStep 2186363 = 3279545) B3279545
theorem B12459203 : Blo 1457548 12459203 := bstep (se 1 (by rfl) ⟨9344402, by rfl⟩ : syracuseStep 12459203 = 18688805) B18688805
theorem B2186489 : Blo 1457548 2186489 := bstep (se 2 (by rfl) ⟨819933, by rfl⟩ : syracuseStep 2186489 = 1639867) B1639867
theorem B2186591 : Blo 1457548 2186591 := bstep (se 1 (by rfl) ⟨1639943, by rfl⟩ : syracuseStep 2186591 = 3279887) B3279887
theorem B2186603 : Blo 1457548 2186603 := bstep (se 1 (by rfl) ⟨1639952, by rfl⟩ : syracuseStep 2186603 = 3279905) B3279905
theorem B1457583 : Blo 1457548 1457583 := bstep (se 1 (by rfl) ⟨1093187, by rfl⟩ : syracuseStep 1457583 = 2186375) B2186375
theorem B1457607 : Blo 1457548 1457607 := bstep (se 1 (by rfl) ⟨1093205, by rfl⟩ : syracuseStep 1457607 = 2186411) B2186411
theorem B1457627 : Blo 1457548 1457627 := bstep (se 1 (by rfl) ⟨1093220, by rfl⟩ : syracuseStep 1457627 = 2186441) B2186441
theorem B2768347 : Blo 1457548 2768347 := bstep (se 1 (by rfl) ⟨2076260, by rfl⟩ : syracuseStep 2768347 = 4152521) B4152521
theorem B2768393 : Blo 1457548 2768393 := bstep (se 2 (by rfl) ⟨1038147, by rfl⟩ : syracuseStep 2768393 = 2076295) B2076295
theorem B2956807 : Blo 1457548 2956807 := bstep (se 1 (by rfl) ⟨2217605, by rfl⟩ : syracuseStep 2956807 = 4435211) B4435211
theorem B1457703 : Blo 1457548 1457703 := bstep (se 1 (by rfl) ⟨1093277, by rfl⟩ : syracuseStep 1457703 = 2186555) B2186555
theorem B1457743 : Blo 1457548 1457743 := bstep (se 1 (by rfl) ⟨1093307, by rfl⟩ : syracuseStep 1457743 = 2186615) B2186615
theorem B2186831 : Blo 1457548 2186831 := bstep (se 1 (by rfl) ⟨1640123, by rfl⟩ : syracuseStep 2186831 = 3280247) B3280247
theorem B10518103 : Blo 1457548 10518103 := bstep (se 1 (by rfl) ⟨7888577, by rfl⟩ : syracuseStep 10518103 = 15777155) B15777155
theorem B1457759 : Blo 1457548 1457759 := bstep (se 1 (by rfl) ⟨1093319, by rfl⟩ : syracuseStep 1457759 = 2186639) B2186639
theorem B1457787 : Blo 1457548 1457787 := bstep (se 1 (by rfl) ⟨1093340, by rfl⟩ : syracuseStep 1457787 = 2186681) B2186681
theorem B7388819 : Blo 1457548 7388819 := bstep (se 1 (by rfl) ⟨5541614, by rfl⟩ : syracuseStep 7388819 = 11083229) B11083229
theorem B1457839 : Blo 1457548 1457839 := bstep (se 1 (by rfl) ⟨1093379, by rfl⟩ : syracuseStep 1457839 = 2186759) B2186759
theorem B1457863 : Blo 1457548 1457863 := bstep (se 1 (by rfl) ⟨1093397, by rfl⟩ : syracuseStep 1457863 = 2186795) B2186795
theorem B2186951 : Blo 1457548 2186951 := bstep (se 1 (by rfl) ⟨1640213, by rfl⟩ : syracuseStep 2186951 = 3280427) B3280427
theorem B1457883 : Blo 1457548 1457883 := bstep (se 1 (by rfl) ⟨1093412, by rfl⟩ : syracuseStep 1457883 = 2186825) B2186825
theorem B24936173 : Blo 1457548 24936173 := bstep (se 3 (by rfl) ⟨4675532, by rfl⟩ : syracuseStep 24936173 = 9351065) B9351065
theorem B1457959 : Blo 1457548 1457959 := bstep (se 1 (by rfl) ⟨1093469, by rfl⟩ : syracuseStep 1457959 = 2186939) B2186939
theorem B4923179 : Blo 1457548 4923179 := bstep (se 1 (by rfl) ⟨3692384, by rfl⟩ : syracuseStep 4923179 = 7384769) B7384769
theorem B1457999 : Blo 1457548 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B1458015 : Blo 1457548 1458015 := bstep (se 1 (by rfl) ⟨1093511, by rfl⟩ : syracuseStep 1458015 = 2187023) B2187023
theorem B2768735 : Blo 1457548 2768735 := bstep (se 1 (by rfl) ⟨2076551, by rfl⟩ : syracuseStep 2768735 = 4153103) B4153103
theorem B2187113 : Blo 1457548 2187113 := bstep (se 2 (by rfl) ⟨820167, by rfl⟩ : syracuseStep 2187113 = 1640335) B1640335
theorem B1458043 : Blo 1457548 1458043 := bstep (se 1 (by rfl) ⟨1093532, by rfl⟩ : syracuseStep 1458043 = 2187065) B2187065
theorem B1458095 : Blo 1457548 1458095 := bstep (se 1 (by rfl) ⟨1093571, by rfl⟩ : syracuseStep 1458095 = 2187143) B2187143
theorem B2187191 : Blo 1457548 2187191 := bstep (se 1 (by rfl) ⟨1640393, by rfl⟩ : syracuseStep 2187191 = 3280787) B3280787
theorem B1458119 : Blo 1457548 1458119 := bstep (se 1 (by rfl) ⟨1093589, by rfl⟩ : syracuseStep 1458119 = 2187179) B2187179
theorem B1458139 : Blo 1457548 1458139 := bstep (se 1 (by rfl) ⟨1093604, by rfl⟩ : syracuseStep 1458139 = 2187209) B2187209
theorem B2187227 : Blo 1457548 2187227 := bstep (se 1 (by rfl) ⟨1640420, by rfl⟩ : syracuseStep 2187227 = 3280841) B3280841
theorem B15769637 : Blo 1457548 15769637 := bstep (se 4 (by rfl) ⟨1478403, by rfl⟩ : syracuseStep 15769637 = 2956807) B2956807
theorem B7381043 : Blo 1457548 7381043 := bstep (se 1 (by rfl) ⟨5535782, by rfl⟩ : syracuseStep 7381043 = 11071565) B11071565
theorem B6225979 : Blo 1457548 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B1663195 : Blo 1457548 1663195 := bstep (se 1 (by rfl) ⟨1247396, by rfl⟩ : syracuseStep 1663195 = 2494793) B2494793
theorem B1458463 : Blo 1457548 1458463 := bstep (se 1 (by rfl) ⟨1093847, by rfl⟩ : syracuseStep 1458463 = 2187695) B2187695
theorem B2187611 : Blo 1457548 2187611 := bstep (se 1 (by rfl) ⟨1640708, by rfl⟩ : syracuseStep 2187611 = 3281417) B3281417
theorem B1458523 : Blo 1457548 1458523 := bstep (se 1 (by rfl) ⟨1093892, by rfl⟩ : syracuseStep 1458523 = 2187785) B2187785
theorem B1458543 : Blo 1457548 1458543 := bstep (se 1 (by rfl) ⟨1093907, by rfl⟩ : syracuseStep 1458543 = 2187815) B2187815
theorem B14967193 : Blo 1457548 14967193 := bstep (se 2 (by rfl) ⟨5612697, by rfl⟩ : syracuseStep 14967193 = 11225395) B11225395
theorem B1458599 : Blo 1457548 1458599 := bstep (se 1 (by rfl) ⟨1093949, by rfl⟩ : syracuseStep 1458599 = 2187899) B2187899
theorem B2769319 : Blo 1457548 2769319 := bstep (se 1 (by rfl) ⟨2076989, by rfl⟩ : syracuseStep 2769319 = 4153979) B4153979
theorem B1458683 : Blo 1457548 1458683 := bstep (se 1 (by rfl) ⟨1094012, by rfl⟩ : syracuseStep 1458683 = 2188025) B2188025
theorem B2769403 : Blo 1457548 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B118317611 : Blo 1457548 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B2187839 : Blo 1457548 2187839 := bstep (se 1 (by rfl) ⟨1640879, by rfl⟩ : syracuseStep 2187839 = 3281759) B3281759
theorem B1458751 : Blo 1457548 1458751 := bstep (se 1 (by rfl) ⟨1094063, by rfl⟩ : syracuseStep 1458751 = 2188127) B2188127
theorem B2957887 : Blo 1457548 2957887 := bstep (se 1 (by rfl) ⟨2218415, by rfl⟩ : syracuseStep 2957887 = 4436831) B4436831
theorem B1458759 : Blo 1457548 1458759 := bstep (se 1 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 1458759 = 2188139) B2188139
theorem B1663559 : Blo 1457548 1663559 := bstep (se 1 (by rfl) ⟨1247669, by rfl⟩ : syracuseStep 1663559 = 2495339) B2495339
theorem B7881313 : Blo 1457548 7881313 := bstep (se 2 (by rfl) ⟨2955492, by rfl⟩ : syracuseStep 7881313 = 5910985) B5910985
theorem B7004825 : Blo 1457548 7004825 := bstep (se 2 (by rfl) ⟨2626809, by rfl⟩ : syracuseStep 7004825 = 5253619) B5253619
theorem B7004843 : Blo 1457548 7004843 := bstep (se 1 (by rfl) ⟨5253632, by rfl⟩ : syracuseStep 7004843 = 10507265) B10507265
theorem B2187959 : Blo 1457548 2187959 := bstep (se 1 (by rfl) ⟨1640969, by rfl⟩ : syracuseStep 2187959 = 3281939) B3281939
theorem B1458911 : Blo 1457548 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B1458991 : Blo 1457548 1458991 := bstep (se 1 (by rfl) ⟨1094243, by rfl⟩ : syracuseStep 1458991 = 2188487) B2188487
theorem B2188187 : Blo 1457548 2188187 := bstep (se 1 (by rfl) ⟨1641140, by rfl⟩ : syracuseStep 2188187 = 3282281) B3282281
theorem B1459099 : Blo 1457548 1459099 := bstep (se 1 (by rfl) ⟨1094324, by rfl⟩ : syracuseStep 1459099 = 2188649) B2188649
theorem B1459151 : Blo 1457548 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B1459175 : Blo 1457548 1459175 := bstep (se 1 (by rfl) ⟨1094381, by rfl⟩ : syracuseStep 1459175 = 2188763) B2188763
theorem B31523863 : Blo 1457548 31523863 := bstep (se 1 (by rfl) ⟨23642897, by rfl⟩ : syracuseStep 31523863 = 47285795) B47285795
theorem B4670561 : Blo 1457548 4670561 := bstep (se 2 (by rfl) ⟨1751460, by rfl⟩ : syracuseStep 4670561 = 3502921) B3502921
theorem B28435627 : Blo 1457548 28435627 := bstep (se 1 (by rfl) ⟨21326720, by rfl⟩ : syracuseStep 28435627 = 42653441) B42653441
theorem B2770139 : Blo 1457548 2770139 := bstep (se 1 (by rfl) ⟨2077604, by rfl⟩ : syracuseStep 2770139 = 4155209) B4155209
theorem B11068649 : Blo 1457548 11068649 := bstep (se 2 (by rfl) ⟨4150743, by rfl⟩ : syracuseStep 11068649 = 8301487) B8301487
theorem B5539049 : Blo 1457548 5539049 := bstep (se 2 (by rfl) ⟨2077143, by rfl⟩ : syracuseStep 5539049 = 4154287) B4154287
theorem B11986163 : Blo 1457548 11986163 := bstep (se 1 (by rfl) ⟨8989622, by rfl⟩ : syracuseStep 11986163 = 17979245) B17979245
theorem B1459487 : Blo 1457548 1459487 := bstep (se 1 (by rfl) ⟨1094615, by rfl⟩ : syracuseStep 1459487 = 2189231) B2189231
theorem B2188583 : Blo 1457548 2188583 := bstep (se 1 (by rfl) ⟨1641437, by rfl⟩ : syracuseStep 2188583 = 3282875) B3282875
theorem B1459547 : Blo 1457548 1459547 := bstep (se 1 (by rfl) ⟨1094660, by rfl⟩ : syracuseStep 1459547 = 2189321) B2189321
theorem B2958689 : Blo 1457548 2958689 := bstep (se 2 (by rfl) ⟨1109508, by rfl⟩ : syracuseStep 2958689 = 2219017) B2219017
theorem B2188667 : Blo 1457548 2188667 := bstep (se 1 (by rfl) ⟨1641500, by rfl⟩ : syracuseStep 2188667 = 3283001) B3283001
theorem B4670909 : Blo 1457548 4670909 := bstep (se 3 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 4670909 = 1751591) B1751591
theorem B2770375 : Blo 1457548 2770375 := bstep (se 1 (by rfl) ⟨2077781, by rfl⟩ : syracuseStep 2770375 = 4155563) B4155563
theorem B2188793 : Blo 1457548 2188793 := bstep (se 2 (by rfl) ⟨820797, by rfl⟩ : syracuseStep 2188793 = 1641595) B1641595
theorem B2188895 : Blo 1457548 2188895 := bstep (se 1 (by rfl) ⟨1641671, by rfl⟩ : syracuseStep 2188895 = 3283343) B3283343
theorem B7382663 : Blo 1457548 7382663 := bstep (se 1 (by rfl) ⟨5536997, by rfl⟩ : syracuseStep 7382663 = 11073995) B11073995
theorem B2189111 : Blo 1457548 2189111 := bstep (se 1 (by rfl) ⟨1641833, by rfl⟩ : syracuseStep 2189111 = 3283667) B3283667
theorem B15992723 : Blo 1457548 15992723 := bstep (se 1 (by rfl) ⟨11994542, by rfl⟩ : syracuseStep 15992723 = 23989085) B23989085
theorem B1845595 : Blo 1457548 1845595 := bstep (se 1 (by rfl) ⟨1384196, by rfl⟩ : syracuseStep 1845595 = 2768393) B2768393
theorem B2460071 : Blo 1457548 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B4925879 : Blo 1457548 4925879 := bstep (se 1 (by rfl) ⟨3694409, by rfl⟩ : syracuseStep 4925879 = 7388819) B7388819
theorem B9980371 : Blo 1457548 9980371 := bstep (se 1 (by rfl) ⟨7485278, by rfl⟩ : syracuseStep 9980371 = 14970557) B14970557
theorem B16624115 : Blo 1457548 16624115 := bstep (se 1 (by rfl) ⟨12468086, by rfl⟩ : syracuseStep 16624115 = 24936173) B24936173
theorem B1845823 : Blo 1457548 1845823 := bstep (se 1 (by rfl) ⟨1384367, by rfl⟩ : syracuseStep 1845823 = 2768735) B2768735
theorem B2460233 : Blo 1457548 2460233 := bstep (se 2 (by rfl) ⟨922587, by rfl⟩ : syracuseStep 2460233 = 1845175) B1845175
theorem B1641055 : Blo 1457548 1641055 := bstep (se 1 (by rfl) ⟨1230791, by rfl⟩ : syracuseStep 1641055 = 2461583) B2461583
theorem B3279635 : Blo 1457548 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B7883543 : Blo 1457548 7883543 := bstep (se 1 (by rfl) ⟨5912657, by rfl⟩ : syracuseStep 7883543 = 11825315) B11825315
theorem B24923051 : Blo 1457548 24923051 := bstep (se 1 (by rfl) ⟨18692288, by rfl⟩ : syracuseStep 24923051 = 37384577) B37384577
theorem B3689459 : Blo 1457548 3689459 := bstep (se 1 (by rfl) ⟨2767094, by rfl⟩ : syracuseStep 3689459 = 5534189) B5534189
theorem B7883891 : Blo 1457548 7883891 := bstep (se 1 (by rfl) ⟨5912918, by rfl⟩ : syracuseStep 7883891 = 11825837) B11825837
theorem B3279995 : Blo 1457548 3279995 := bstep (se 1 (by rfl) ⟨2459996, by rfl⟩ : syracuseStep 3279995 = 4919993) B4919993
theorem B21040307 : Blo 1457548 21040307 := bstep (se 1 (by rfl) ⟨15780230, by rfl⟩ : syracuseStep 21040307 = 31560461) B31560461
theorem B3689671 : Blo 1457548 3689671 := bstep (se 1 (by rfl) ⟨2767253, by rfl⟩ : syracuseStep 3689671 = 5534507) B5534507
theorem B7384283 : Blo 1457548 7384283 := bstep (se 1 (by rfl) ⟨5538212, by rfl⟩ : syracuseStep 7384283 = 11076425) B11076425
theorem B3280121 : Blo 1457548 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B1846567 : Blo 1457548 1846567 := bstep (se 1 (by rfl) ⟨1384925, by rfl⟩ : syracuseStep 1846567 = 2769851) B2769851
theorem B7990595 : Blo 1457548 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B3280265 : Blo 1457548 3280265 := bstep (se 2 (by rfl) ⟨1230099, by rfl⟩ : syracuseStep 3280265 = 2460199) B2460199
theorem B23662043 : Blo 1457548 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B3280391 : Blo 1457548 3280391 := bstep (se 1 (by rfl) ⟨2460293, by rfl⟩ : syracuseStep 3280391 = 4920587) B4920587
theorem B2461279 : Blo 1457548 2461279 := bstep (se 1 (by rfl) ⟨1845959, by rfl⟩ : syracuseStep 2461279 = 3691919) B3691919
theorem B1846891 : Blo 1457548 1846891 := bstep (se 1 (by rfl) ⟨1385168, by rfl⟩ : syracuseStep 1846891 = 2770337) B2770337
theorem B11079341 : Blo 1457548 11079341 := bstep (se 3 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 11079341 = 4154753) B4154753
theorem B3280571 : Blo 1457548 3280571 := bstep (se 1 (by rfl) ⟨2460428, by rfl⟩ : syracuseStep 3280571 = 4920857) B4920857
theorem B2461495 : Blo 1457548 2461495 := bstep (se 1 (by rfl) ⟨1846121, by rfl⟩ : syracuseStep 2461495 = 3692243) B3692243
theorem B3280697 : Blo 1457548 3280697 := bstep (se 2 (by rfl) ⟨1230261, by rfl⟩ : syracuseStep 3280697 = 2460523) B2460523
theorem B1847119 : Blo 1457548 1847119 := bstep (se 1 (by rfl) ⟨1385339, by rfl⟩ : syracuseStep 1847119 = 2770679) B2770679
theorem B10113083 : Blo 1457548 10113083 := bstep (se 1 (by rfl) ⟨7584812, by rfl⟩ : syracuseStep 10113083 = 15169625) B15169625
theorem B8302763 : Blo 1457548 8302763 := bstep (se 1 (by rfl) ⟨6227072, by rfl⟩ : syracuseStep 8302763 = 12454145) B12454145
theorem B4919507 : Blo 1457548 4919507 := bstep (se 1 (by rfl) ⟨3689630, by rfl⟩ : syracuseStep 4919507 = 7379261) B7379261
theorem B7008515 : Blo 1457548 7008515 := bstep (se 1 (by rfl) ⟨5256386, by rfl⟩ : syracuseStep 7008515 = 10512773) B10512773
theorem B2461961 : Blo 1457548 2461961 := bstep (se 2 (by rfl) ⟨923235, by rfl⟩ : syracuseStep 2461961 = 1846471) B1846471
theorem B3944713 : Blo 1457548 3944713 := bstep (se 2 (by rfl) ⟨1479267, by rfl⟩ : syracuseStep 3944713 = 2958535) B2958535
theorem B7385417 : Blo 1457548 7385417 := bstep (se 2 (by rfl) ⟨2769531, by rfl⟩ : syracuseStep 7385417 = 5539063) B5539063
theorem B3281327 : Blo 1457548 3281327 := bstep (se 1 (by rfl) ⟨2460995, by rfl⟩ : syracuseStep 3281327 = 4921991) B4921991
theorem B3281363 : Blo 1457548 3281363 := bstep (se 1 (by rfl) ⟨2461022, by rfl⟩ : syracuseStep 3281363 = 4922045) B4922045
theorem B12464603 : Blo 1457548 12464603 := bstep (se 1 (by rfl) ⟨9348452, by rfl⟩ : syracuseStep 12464603 = 18696905) B18696905
theorem B4919777 : Blo 1457548 4919777 := bstep (se 2 (by rfl) ⟨1844916, by rfl⟩ : syracuseStep 4919777 = 3689833) B3689833
theorem B21017069 : Blo 1457548 21017069 := bstep (se 3 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 21017069 = 7881401) B7881401
theorem B11072051 : Blo 1457548 11072051 := bstep (se 1 (by rfl) ⟨8304038, by rfl⟩ : syracuseStep 11072051 = 16608077) B16608077
theorem B3281471 : Blo 1457548 3281471 := bstep (se 1 (by rfl) ⟨2461103, by rfl⟩ : syracuseStep 3281471 = 4922207) B4922207
theorem B3691079 : Blo 1457548 3691079 := bstep (se 1 (by rfl) ⟨2768309, by rfl⟩ : syracuseStep 3691079 = 5536619) B5536619
theorem B3691129 : Blo 1457548 3691129 := bstep (se 2 (by rfl) ⟨1384173, by rfl⟩ : syracuseStep 3691129 = 2768347) B2768347
theorem B11080313 : Blo 1457548 11080313 := bstep (se 2 (by rfl) ⟨4155117, by rfl⟩ : syracuseStep 11080313 = 8310235) B8310235
theorem B3281579 : Blo 1457548 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B3282119 : Blo 1457548 3282119 := bstep (se 1 (by rfl) ⟨2461589, by rfl⟩ : syracuseStep 3282119 = 4923179) B4923179
theorem B4748503 : Blo 1457548 4748503 := bstep (se 1 (by rfl) ⟨3561377, by rfl⟩ : syracuseStep 4748503 = 7122755) B7122755
theorem B2462953 : Blo 1457548 2462953 := bstep (se 2 (by rfl) ⟨923607, by rfl⟩ : syracuseStep 2462953 = 1847215) B1847215
theorem B5534963 : Blo 1457548 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B23983361 : Blo 1457548 23983361 := bstep (se 2 (by rfl) ⟨8993760, by rfl⟩ : syracuseStep 23983361 = 17987521) B17987521
theorem B3282299 : Blo 1457548 3282299 := bstep (se 1 (by rfl) ⟨2461724, by rfl⟩ : syracuseStep 3282299 = 4923449) B4923449
theorem B3282425 : Blo 1457548 3282425 := bstep (se 2 (by rfl) ⟨1230909, by rfl⟩ : syracuseStep 3282425 = 2461819) B2461819
theorem B3282515 : Blo 1457548 3282515 := bstep (se 1 (by rfl) ⟨2461886, by rfl⟩ : syracuseStep 3282515 = 4923773) B4923773
theorem B7386713 : Blo 1457548 7386713 := bstep (se 2 (by rfl) ⟨2770017, by rfl⟩ : syracuseStep 7386713 = 5540035) B5540035
theorem B4921019 : Blo 1457548 4921019 := bstep (se 1 (by rfl) ⟨3690764, by rfl⟩ : syracuseStep 4921019 = 7381529) B7381529
theorem B3282695 : Blo 1457548 3282695 := bstep (se 1 (by rfl) ⟨2462021, by rfl⟩ : syracuseStep 3282695 = 4924043) B4924043
theorem B56096549 : Blo 1457548 56096549 := bstep (se 4 (by rfl) ⟨5259051, by rfl⟩ : syracuseStep 56096549 = 10518103) B10518103
theorem B31528885 : Blo 1457548 31528885 := bstep (se 5 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 31528885 = 2955833) B2955833
theorem B11073509 : Blo 1457548 11073509 := bstep (se 4 (by rfl) ⟨1038141, by rfl⟩ : syracuseStep 11073509 = 2076283) B2076283
theorem B11081771 : Blo 1457548 11081771 := bstep (se 1 (by rfl) ⟨8311328, by rfl⟩ : syracuseStep 11081771 = 16622657) B16622657
theorem B3692891 : Blo 1457548 3692891 := bstep (se 1 (by rfl) ⟨2769668, by rfl⟩ : syracuseStep 3692891 = 5539337) B5539337
theorem B3283307 : Blo 1457548 3283307 := bstep (se 1 (by rfl) ⟨2462480, by rfl⟩ : syracuseStep 3283307 = 4924961) B4924961
theorem B3692911 : Blo 1457548 3692911 := bstep (se 1 (by rfl) ⟨2769683, by rfl⟩ : syracuseStep 3692911 = 5539367) B5539367
theorem B6650279 : Blo 1457548 6650279 := bstep (se 1 (by rfl) ⟨4987709, by rfl⟩ : syracuseStep 6650279 = 9975419) B9975419
theorem B3283451 : Blo 1457548 3283451 := bstep (se 1 (by rfl) ⟨2462588, by rfl⟩ : syracuseStep 3283451 = 4925177) B4925177
theorem B12458519 : Blo 1457548 12458519 := bstep (se 1 (by rfl) ⟨9343889, by rfl⟩ : syracuseStep 12458519 = 18687779) B18687779
theorem B3283577 : Blo 1457548 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B3283631 : Blo 1457548 3283631 := bstep (se 1 (by rfl) ⟨2462723, by rfl⟩ : syracuseStep 3283631 = 4925447) B4925447
theorem B5536451 : Blo 1457548 5536451 := bstep (se 1 (by rfl) ⟨4152338, by rfl⟩ : syracuseStep 5536451 = 8304677) B8304677
theorem B3283703 : Blo 1457548 3283703 := bstep (se 1 (by rfl) ⟨2462777, by rfl⟩ : syracuseStep 3283703 = 4925555) B4925555
theorem B2628431 : Blo 1457548 2628431 := bstep (se 1 (by rfl) ⟨1971323, by rfl⟩ : syracuseStep 2628431 = 3942647) B3942647
theorem B28023671 : Blo 1457548 28023671 := bstep (se 1 (by rfl) ⟨21017753, by rfl⟩ : syracuseStep 28023671 = 42035507) B42035507
theorem B14015375 : Blo 1457548 14015375 := bstep (se 1 (by rfl) ⟨10511531, by rfl⟩ : syracuseStep 14015375 = 21023063) B21023063
theorem B2218907 : Blo 1457548 2218907 := bstep (se 1 (by rfl) ⟨1664180, by rfl⟩ : syracuseStep 2218907 = 3328361) B3328361
theorem B3283883 : Blo 1457548 3283883 := bstep (se 1 (by rfl) ⟨2462912, by rfl⟩ : syracuseStep 3283883 = 4925825) B4925825
theorem B3693559 : Blo 1457548 3693559 := bstep (se 1 (by rfl) ⟨2770169, by rfl⟩ : syracuseStep 3693559 = 5540339) B5540339
theorem B7887887 : Blo 1457548 7887887 := bstep (se 1 (by rfl) ⟨5915915, by rfl⟩ : syracuseStep 7887887 = 11831831) B11831831
theorem B5536907 : Blo 1457548 5536907 := bstep (se 1 (by rfl) ⟨4152680, by rfl⟩ : syracuseStep 5536907 = 8305361) B8305361
theorem B24927425 : Blo 1457548 24927425 := bstep (se 2 (by rfl) ⟨9347784, by rfl⟩ : syracuseStep 24927425 = 18695569) B18695569
theorem B2186459 : Blo 1457548 2186459 := bstep (se 1 (by rfl) ⟨1639844, by rfl⟩ : syracuseStep 2186459 = 3279689) B3279689
theorem B1752283 : Blo 1457548 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B3693863 : Blo 1457548 3693863 := bstep (se 1 (by rfl) ⟨2770397, by rfl⟩ : syracuseStep 3693863 = 5540795) B5540795
theorem B3792251 : Blo 1457548 3792251 := bstep (se 1 (by rfl) ⟨2844188, by rfl⟩ : syracuseStep 3792251 = 5688377) B5688377
theorem B2186633 : Blo 1457548 2186633 := bstep (se 2 (by rfl) ⟨819987, by rfl⟩ : syracuseStep 2186633 = 1639975) B1639975
theorem B1457575 : Blo 1457548 1457575 := bstep (se 1 (by rfl) ⟨1093181, by rfl⟩ : syracuseStep 1457575 = 2186363) B2186363
theorem B8306135 : Blo 1457548 8306135 := bstep (se 1 (by rfl) ⟨6229601, by rfl⟩ : syracuseStep 8306135 = 12459203) B12459203
theorem B1457659 : Blo 1457548 1457659 := bstep (se 1 (by rfl) ⟨1093244, by rfl⟩ : syracuseStep 1457659 = 2186489) B2186489
theorem B1457727 : Blo 1457548 1457727 := bstep (se 1 (by rfl) ⟨1093295, by rfl⟩ : syracuseStep 1457727 = 2186591) B2186591
theorem B1457735 : Blo 1457548 1457735 := bstep (se 1 (by rfl) ⟨1093301, by rfl⟩ : syracuseStep 1457735 = 2186603) B2186603
theorem B4922963 : Blo 1457548 4922963 := bstep (se 1 (by rfl) ⟨3692222, by rfl⟩ : syracuseStep 4922963 = 7384445) B7384445
theorem B1457887 : Blo 1457548 1457887 := bstep (se 1 (by rfl) ⟨1093415, by rfl⟩ : syracuseStep 1457887 = 2186831) B2186831
theorem B2186987 : Blo 1457548 2186987 := bstep (se 1 (by rfl) ⟨1640240, by rfl⟩ : syracuseStep 2186987 = 3280481) B3280481
theorem B2768681 : Blo 1457548 2768681 := bstep (se 2 (by rfl) ⟨1038255, by rfl⟩ : syracuseStep 2768681 = 2076511) B2076511
theorem B1457967 : Blo 1457548 1457967 := bstep (se 1 (by rfl) ⟨1093475, by rfl⟩ : syracuseStep 1457967 = 2186951) B2186951
theorem B1458075 : Blo 1457548 1458075 := bstep (se 1 (by rfl) ⟨1093556, by rfl⟩ : syracuseStep 1458075 = 2187113) B2187113
theorem B1458127 : Blo 1457548 1458127 := bstep (se 1 (by rfl) ⟨1093595, by rfl⟩ : syracuseStep 1458127 = 2187191) B2187191
theorem B2187215 : Blo 1457548 2187215 := bstep (se 1 (by rfl) ⟨1640411, by rfl⟩ : syracuseStep 2187215 = 3280823) B3280823
theorem B1458151 : Blo 1457548 1458151 := bstep (se 1 (by rfl) ⟨1093613, by rfl⟩ : syracuseStep 1458151 = 2187227) B2187227
theorem B6742055 : Blo 1457548 6742055 := bstep (se 1 (by rfl) ⟨5056541, by rfl⟩ : syracuseStep 6742055 = 10113083) B10113083
theorem B4923611 : Blo 1457548 4923611 := bstep (se 1 (by rfl) ⟨3692708, by rfl⟩ : syracuseStep 4923611 = 7385417) B7385417
theorem B1458407 : Blo 1457548 1458407 := bstep (se 1 (by rfl) ⟨1093805, by rfl⟩ : syracuseStep 1458407 = 2187611) B2187611
theorem B2187551 : Blo 1457548 2187551 := bstep (se 1 (by rfl) ⟨1640663, by rfl⟩ : syracuseStep 2187551 = 3281327) B3281327
theorem B2187575 : Blo 1457548 2187575 := bstep (se 1 (by rfl) ⟨1640681, by rfl⟩ : syracuseStep 2187575 = 3281363) B3281363
theorem B5259617 : Blo 1457548 5259617 := bstep (se 2 (by rfl) ⟨1972356, by rfl⟩ : syracuseStep 5259617 = 3944713) B3944713
theorem B7381367 : Blo 1457548 7381367 := bstep (se 1 (by rfl) ⟨5536025, by rfl⟩ : syracuseStep 7381367 = 11072051) B11072051
theorem B2187647 : Blo 1457548 2187647 := bstep (se 1 (by rfl) ⟨1640735, by rfl⟩ : syracuseStep 2187647 = 3281471) B3281471
theorem B1458559 : Blo 1457548 1458559 := bstep (se 1 (by rfl) ⟨1093919, by rfl⟩ : syracuseStep 1458559 = 2187839) B2187839
theorem B4669883 : Blo 1457548 4669883 := bstep (se 1 (by rfl) ⟨3502412, by rfl⟩ : syracuseStep 4669883 = 7004825) B7004825
theorem B4669895 : Blo 1457548 4669895 := bstep (se 1 (by rfl) ⟨3502421, by rfl⟩ : syracuseStep 4669895 = 7004843) B7004843
theorem B2187719 : Blo 1457548 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B1458639 : Blo 1457548 1458639 := bstep (se 1 (by rfl) ⟨1093979, by rfl⟩ : syracuseStep 1458639 = 2187959) B2187959
theorem B4923881 : Blo 1457548 4923881 := bstep (se 2 (by rfl) ⟨1846455, by rfl⟩ : syracuseStep 4923881 = 3692911) B3692911
theorem B19956257 : Blo 1457548 19956257 := bstep (se 2 (by rfl) ⟨7483596, by rfl⟩ : syracuseStep 19956257 = 14967193) B14967193
theorem B1458791 : Blo 1457548 1458791 := bstep (se 1 (by rfl) ⟨1094093, by rfl⟩ : syracuseStep 1458791 = 2188187) B2188187
theorem B2188073 : Blo 1457548 2188073 := bstep (se 2 (by rfl) ⟨820527, by rfl⟩ : syracuseStep 2188073 = 1641055) B1641055
theorem B2188079 : Blo 1457548 2188079 := bstep (se 1 (by rfl) ⟨1641059, by rfl⟩ : syracuseStep 2188079 = 3282119) B3282119
theorem B1459055 : Blo 1457548 1459055 := bstep (se 1 (by rfl) ⟨1094291, by rfl⟩ : syracuseStep 1459055 = 2188583) B2188583
theorem B2188199 : Blo 1457548 2188199 := bstep (se 1 (by rfl) ⟨1641149, by rfl⟩ : syracuseStep 2188199 = 3282299) B3282299
theorem B1459111 : Blo 1457548 1459111 := bstep (se 1 (by rfl) ⟨1094333, by rfl⟩ : syracuseStep 1459111 = 2188667) B2188667
theorem B3113939 : Blo 1457548 3113939 := bstep (se 1 (by rfl) ⟨2335454, by rfl⟩ : syracuseStep 3113939 = 4670909) B4670909
theorem B2188283 : Blo 1457548 2188283 := bstep (se 1 (by rfl) ⟨1641212, by rfl⟩ : syracuseStep 2188283 = 3282425) B3282425
theorem B1459195 : Blo 1457548 1459195 := bstep (se 1 (by rfl) ⟨1094396, by rfl⟩ : syracuseStep 1459195 = 2188793) B2188793
theorem B2188343 : Blo 1457548 2188343 := bstep (se 1 (by rfl) ⟨1641257, by rfl⟩ : syracuseStep 2188343 = 3282515) B3282515
theorem B4924475 : Blo 1457548 4924475 := bstep (se 1 (by rfl) ⟨3693356, by rfl⟩ : syracuseStep 4924475 = 7386713) B7386713
theorem B1459263 : Blo 1457548 1459263 := bstep (se 1 (by rfl) ⟨1094447, by rfl⟩ : syracuseStep 1459263 = 2188895) B2188895
theorem B2188463 : Blo 1457548 2188463 := bstep (se 1 (by rfl) ⟨1641347, by rfl⟩ : syracuseStep 2188463 = 3282695) B3282695
theorem B37397699 : Blo 1457548 37397699 := bstep (se 1 (by rfl) ⟨28048274, by rfl⟩ : syracuseStep 37397699 = 56096549) B56096549
theorem B1459407 : Blo 1457548 1459407 := bstep (se 1 (by rfl) ⟨1094555, by rfl⟩ : syracuseStep 1459407 = 2189111) B2189111
theorem B7382339 : Blo 1457548 7382339 := bstep (se 1 (by rfl) ⟨5536754, by rfl⟩ : syracuseStep 7382339 = 11073509) B11073509
theorem B4924745 : Blo 1457548 4924745 := bstep (se 2 (by rfl) ⟨1846779, by rfl⟩ : syracuseStep 4924745 = 3693559) B3693559
theorem B37914169 : Blo 1457548 37914169 := bstep (se 2 (by rfl) ⟨14217813, by rfl⟩ : syracuseStep 37914169 = 28435627) B28435627
theorem B2188871 : Blo 1457548 2188871 := bstep (se 1 (by rfl) ⟨1641653, by rfl⟩ : syracuseStep 2188871 = 3283307) B3283307
theorem B1640047 : Blo 1457548 1640047 := bstep (se 1 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 1640047 = 2460071) B2460071
theorem B4433519 : Blo 1457548 4433519 := bstep (se 1 (by rfl) ⟨3325139, by rfl⟩ : syracuseStep 4433519 = 6650279) B6650279
theorem B2336377 : Blo 1457548 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B2188967 : Blo 1457548 2188967 := bstep (se 1 (by rfl) ⟨1641725, by rfl⟩ : syracuseStep 2188967 = 3283451) B3283451
theorem B1640155 : Blo 1457548 1640155 := bstep (se 1 (by rfl) ⟨1230116, by rfl⟩ : syracuseStep 1640155 = 2460233) B2460233
theorem B2189051 : Blo 1457548 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B2189087 : Blo 1457548 2189087 := bstep (se 1 (by rfl) ⟨1641815, by rfl⟩ : syracuseStep 2189087 = 3283631) B3283631
theorem B2189135 : Blo 1457548 2189135 := bstep (se 1 (by rfl) ⟨1641851, by rfl⟩ : syracuseStep 2189135 = 3283703) B3283703
theorem B16615367 : Blo 1457548 16615367 := bstep (se 1 (by rfl) ⟨12461525, by rfl⟩ : syracuseStep 16615367 = 24923051) B24923051
theorem B2189255 : Blo 1457548 2189255 := bstep (se 1 (by rfl) ⟨1641941, by rfl⟩ : syracuseStep 2189255 = 3283883) B3283883
theorem B2459639 : Blo 1457548 2459639 := bstep (se 1 (by rfl) ⟨1844729, by rfl⟩ : syracuseStep 2459639 = 3689459) B3689459
theorem B7383149 : Blo 1457548 7383149 := bstep (se 3 (by rfl) ⟨1384340, by rfl⟩ : syracuseStep 7383149 = 2768681) B2768681
theorem B14026871 : Blo 1457548 14026871 := bstep (se 1 (by rfl) ⟨10520153, by rfl⟩ : syracuseStep 14026871 = 21040307) B21040307
theorem B5327063 : Blo 1457548 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B10513091 : Blo 1457548 10513091 := bstep (se 1 (by rfl) ⟨7884818, by rfl⟩ : syracuseStep 10513091 = 15769637) B15769637
theorem B8301305 : Blo 1457548 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B3279671 : Blo 1457548 3279671 := bstep (se 1 (by rfl) ⟨2459753, by rfl⟩ : syracuseStep 3279671 = 4919507) B4919507
theorem B4672343 : Blo 1457548 4672343 := bstep (se 1 (by rfl) ⟨3504257, by rfl⟩ : syracuseStep 4672343 = 7008515) B7008515
theorem B1641307 : Blo 1457548 1641307 := bstep (se 1 (by rfl) ⟨1230980, by rfl⟩ : syracuseStep 1641307 = 2461961) B2461961
theorem B12454829 : Blo 1457548 12454829 := bstep (se 3 (by rfl) ⟨2335280, by rfl⟩ : syracuseStep 12454829 = 4670561) B4670561
theorem B70978517 : Blo 1457548 70978517 := bstep (se 7 (by rfl) ⟨831779, by rfl⟩ : syracuseStep 70978517 = 1663559) B1663559
theorem B8309735 : Blo 1457548 8309735 := bstep (se 1 (by rfl) ⟨6232301, by rfl⟩ : syracuseStep 8309735 = 12464603) B12464603
theorem B3279851 : Blo 1457548 3279851 := bstep (se 1 (by rfl) ⟨2459888, by rfl⟩ : syracuseStep 3279851 = 4919777) B4919777
theorem B14011379 : Blo 1457548 14011379 := bstep (se 1 (by rfl) ⟨10508534, by rfl⟩ : syracuseStep 14011379 = 21017069) B21017069
theorem B2460719 : Blo 1457548 2460719 := bstep (se 1 (by rfl) ⟨1845539, by rfl⟩ : syracuseStep 2460719 = 3691079) B3691079
theorem B2460793 : Blo 1457548 2460793 := bstep (se 2 (by rfl) ⟨922797, by rfl⟩ : syracuseStep 2460793 = 1845595) B1845595
theorem B13307161 : Blo 1457548 13307161 := bstep (se 2 (by rfl) ⟨4990185, by rfl⟩ : syracuseStep 13307161 = 9980371) B9980371
theorem B2461097 : Blo 1457548 2461097 := bstep (se 2 (by rfl) ⟨922911, by rfl⟩ : syracuseStep 2461097 = 1845823) B1845823
theorem B3943849 : Blo 1457548 3943849 := bstep (se 2 (by rfl) ⟨1478943, by rfl⟩ : syracuseStep 3943849 = 2957887) B2957887
theorem B3689975 : Blo 1457548 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B7990775 : Blo 1457548 7990775 := bstep (se 1 (by rfl) ⟨5993081, by rfl⟩ : syracuseStep 7990775 = 11986163) B11986163
theorem B3280679 : Blo 1457548 3280679 := bstep (se 1 (by rfl) ⟨2460509, by rfl⟩ : syracuseStep 3280679 = 4921019) B4921019
theorem B10661815 : Blo 1457548 10661815 := bstep (se 1 (by rfl) ⟨7996361, by rfl⟩ : syracuseStep 10661815 = 15992723) B15992723
theorem B2461927 : Blo 1457548 2461927 := bstep (se 1 (by rfl) ⟨1846445, by rfl⟩ : syracuseStep 2461927 = 3692891) B3692891
theorem B4919561 : Blo 1457548 4919561 := bstep (se 2 (by rfl) ⟨1844835, by rfl⟩ : syracuseStep 4919561 = 3689671) B3689671
theorem B2462089 : Blo 1457548 2462089 := bstep (se 2 (by rfl) ⟨923283, by rfl⟩ : syracuseStep 2462089 = 1846567) B1846567
theorem B3690967 : Blo 1457548 3690967 := bstep (se 1 (by rfl) ⟨2768225, by rfl⟩ : syracuseStep 3690967 = 5536451) B5536451
theorem B5255695 : Blo 1457548 5255695 := bstep (se 1 (by rfl) ⟨3941771, by rfl⟩ : syracuseStep 5255695 = 7883543) B7883543
theorem B18682447 : Blo 1457548 18682447 := bstep (se 1 (by rfl) ⟨14011835, by rfl⟩ : syracuseStep 18682447 = 28023671) B28023671
theorem B9343583 : Blo 1457548 9343583 := bstep (se 1 (by rfl) ⟨7007687, by rfl⟩ : syracuseStep 9343583 = 14015375) B14015375
theorem B1479271 : Blo 1457548 1479271 := bstep (se 1 (by rfl) ⟨1109453, by rfl⟩ : syracuseStep 1479271 = 2218907) B2218907
theorem B5255927 : Blo 1457548 5255927 := bstep (se 1 (by rfl) ⟨3941945, by rfl⟩ : syracuseStep 5255927 = 7883891) B7883891
theorem B3691271 : Blo 1457548 3691271 := bstep (se 1 (by rfl) ⟨2768453, by rfl⟩ : syracuseStep 3691271 = 5536907) B5536907
theorem B3281705 : Blo 1457548 3281705 := bstep (se 2 (by rfl) ⟨1230639, by rfl⟩ : syracuseStep 3281705 = 2461279) B2461279
theorem B16618283 : Blo 1457548 16618283 := bstep (se 1 (by rfl) ⟨12463712, by rfl⟩ : syracuseStep 16618283 = 24927425) B24927425
theorem B2462521 : Blo 1457548 2462521 := bstep (se 2 (by rfl) ⟨923445, by rfl⟩ : syracuseStep 2462521 = 1846891) B1846891
theorem B2462575 : Blo 1457548 2462575 := bstep (se 1 (by rfl) ⟨1846931, by rfl⟩ : syracuseStep 2462575 = 3693863) B3693863
theorem B2528167 : Blo 1457548 2528167 := bstep (se 1 (by rfl) ⟨1896125, by rfl⟩ : syracuseStep 2528167 = 3792251) B3792251
theorem B15774695 : Blo 1457548 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B3281975 : Blo 1457548 3281975 := bstep (se 1 (by rfl) ⟨2461481, by rfl⟩ : syracuseStep 3281975 = 4922963) B4922963
theorem B3281993 : Blo 1457548 3281993 := bstep (se 2 (by rfl) ⟨1230747, by rfl⟩ : syracuseStep 3281993 = 2461495) B2461495
theorem B2462825 : Blo 1457548 2462825 := bstep (se 2 (by rfl) ⟨923559, by rfl⟩ : syracuseStep 2462825 = 1847119) B1847119
theorem B7386227 : Blo 1457548 7386227 := bstep (se 1 (by rfl) ⟨5539670, by rfl⟩ : syracuseStep 7386227 = 11079341) B11079341
theorem B42038513 : Blo 1457548 42038513 := bstep (se 2 (by rfl) ⟨15764442, by rfl⟩ : syracuseStep 42038513 = 31528885) B31528885
theorem B4920695 : Blo 1457548 4920695 := bstep (se 1 (by rfl) ⟨3690521, by rfl⟩ : syracuseStep 4920695 = 7381043) B7381043
theorem B5535175 : Blo 1457548 5535175 := bstep (se 1 (by rfl) ⟨4151381, by rfl⟩ : syracuseStep 5535175 = 8302763) B8302763
theorem B2217593 : Blo 1457548 2217593 := bstep (se 2 (by rfl) ⟨831597, by rfl⟩ : syracuseStep 2217593 = 1663195) B1663195
theorem B78878407 : Blo 1457548 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B7386875 : Blo 1457548 7386875 := bstep (se 1 (by rfl) ⟨5540156, by rfl⟩ : syracuseStep 7386875 = 11080313) B11080313
theorem B3692425 : Blo 1457548 3692425 := bstep (se 2 (by rfl) ⟨1384659, by rfl⟩ : syracuseStep 3692425 = 2769319) B2769319
theorem B7387037 : Blo 1457548 7387037 := bstep (se 3 (by rfl) ⟨1385069, by rfl⟩ : syracuseStep 7387037 = 2770139) B2770139
theorem B3692537 : Blo 1457548 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B10508417 : Blo 1457548 10508417 := bstep (se 2 (by rfl) ⟨3940656, by rfl⟩ : syracuseStep 10508417 = 7881313) B7881313
theorem B7379099 : Blo 1457548 7379099 := bstep (se 1 (by rfl) ⟨5534324, by rfl⟩ : syracuseStep 7379099 = 11068649) B11068649
theorem B3692699 : Blo 1457548 3692699 := bstep (se 1 (by rfl) ⟨2769524, by rfl⟩ : syracuseStep 3692699 = 5539049) B5539049
theorem B4921505 : Blo 1457548 4921505 := bstep (se 2 (by rfl) ⟨1845564, by rfl⟩ : syracuseStep 4921505 = 3691129) B3691129
theorem B15988907 : Blo 1457548 15988907 := bstep (se 1 (by rfl) ⟨11991680, by rfl⟩ : syracuseStep 15988907 = 23983361) B23983361
theorem B1972459 : Blo 1457548 1972459 := bstep (se 1 (by rfl) ⟨1479344, by rfl⟩ : syracuseStep 1972459 = 2958689) B2958689
theorem B4921775 : Blo 1457548 4921775 := bstep (se 1 (by rfl) ⟨3691331, by rfl⟩ : syracuseStep 4921775 = 7382663) B7382663
theorem B7387847 : Blo 1457548 7387847 := bstep (se 1 (by rfl) ⟨5540885, by rfl⟩ : syracuseStep 7387847 = 11081771) B11081771
theorem B42031817 : Blo 1457548 42031817 := bstep (se 2 (by rfl) ⟨15761931, by rfl⟩ : syracuseStep 42031817 = 31523863) B31523863
theorem B6331337 : Blo 1457548 6331337 := bstep (se 2 (by rfl) ⟨2374251, by rfl⟩ : syracuseStep 6331337 = 4748503) B4748503
theorem B3283919 : Blo 1457548 3283919 := bstep (se 1 (by rfl) ⟨2462939, by rfl⟩ : syracuseStep 3283919 = 4925879) B4925879
theorem B3283937 : Blo 1457548 3283937 := bstep (se 2 (by rfl) ⟨1231476, by rfl⟩ : syracuseStep 3283937 = 2462953) B2462953
theorem B11082743 : Blo 1457548 11082743 := bstep (se 1 (by rfl) ⟨8312057, by rfl⟩ : syracuseStep 11082743 = 16624115) B16624115
theorem B8305679 : Blo 1457548 8305679 := bstep (se 1 (by rfl) ⟨6229259, by rfl⟩ : syracuseStep 8305679 = 12458519) B12458519
theorem B2186423 : Blo 1457548 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1752287 : Blo 1457548 1752287 := bstep (se 1 (by rfl) ⟨1314215, by rfl⟩ : syracuseStep 1752287 = 2628431) B2628431
theorem B3693833 : Blo 1457548 3693833 := bstep (se 2 (by rfl) ⟨1385187, by rfl⟩ : syracuseStep 3693833 = 2770375) B2770375
theorem B5258591 : Blo 1457548 5258591 := bstep (se 1 (by rfl) ⟨3943943, by rfl⟩ : syracuseStep 5258591 = 7887887) B7887887
theorem B2186663 : Blo 1457548 2186663 := bstep (se 1 (by rfl) ⟨1639997, by rfl⟩ : syracuseStep 2186663 = 3279995) B3279995
theorem B1457639 : Blo 1457548 1457639 := bstep (se 1 (by rfl) ⟨1093229, by rfl⟩ : syracuseStep 1457639 = 2186459) B2186459
theorem B4922855 : Blo 1457548 4922855 := bstep (se 1 (by rfl) ⟨3692141, by rfl⟩ : syracuseStep 4922855 = 7384283) B7384283
theorem B2186747 : Blo 1457548 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B1457755 : Blo 1457548 1457755 := bstep (se 1 (by rfl) ⟨1093316, by rfl⟩ : syracuseStep 1457755 = 2186633) B2186633
theorem B2186843 : Blo 1457548 2186843 := bstep (se 1 (by rfl) ⟨1640132, by rfl⟩ : syracuseStep 2186843 = 3280265) B3280265
theorem B5537423 : Blo 1457548 5537423 := bstep (se 1 (by rfl) ⟨4153067, by rfl⟩ : syracuseStep 5537423 = 8306135) B8306135
theorem B2186927 : Blo 1457548 2186927 := bstep (se 1 (by rfl) ⟨1640195, by rfl⟩ : syracuseStep 2186927 = 3280391) B3280391
theorem B2187047 : Blo 1457548 2187047 := bstep (se 1 (by rfl) ⟨1640285, by rfl⟩ : syracuseStep 2187047 = 3280571) B3280571
theorem B1457991 : Blo 1457548 1457991 := bstep (se 1 (by rfl) ⟨1093493, by rfl⟩ : syracuseStep 1457991 = 2186987) B2186987
theorem B2187131 : Blo 1457548 2187131 := bstep (se 1 (by rfl) ⟨1640348, by rfl⟩ : syracuseStep 2187131 = 3280697) B3280697
theorem B1458143 : Blo 1457548 1458143 := bstep (se 1 (by rfl) ⟨1093607, by rfl⟩ : syracuseStep 1458143 = 2187215) B2187215
theorem B1458367 : Blo 1457548 1458367 := bstep (se 1 (by rfl) ⟨1093775, by rfl⟩ : syracuseStep 1458367 = 2187551) B2187551
theorem B1458383 : Blo 1457548 1458383 := bstep (se 1 (by rfl) ⟨1093787, by rfl⟩ : syracuseStep 1458383 = 2187575) B2187575
theorem B3506411 : Blo 1457548 3506411 := bstep (se 1 (by rfl) ⟨2629808, by rfl⟩ : syracuseStep 3506411 = 5259617) B5259617
theorem B1458431 : Blo 1457548 1458431 := bstep (se 1 (by rfl) ⟨1093823, by rfl⟩ : syracuseStep 1458431 = 2187647) B2187647
theorem B3113255 : Blo 1457548 3113255 := bstep (se 1 (by rfl) ⟨2334941, by rfl⟩ : syracuseStep 3113255 = 4669883) B4669883
theorem B3113263 : Blo 1457548 3113263 := bstep (se 1 (by rfl) ⟨2334947, by rfl⟩ : syracuseStep 3113263 = 4669895) B4669895
theorem B1458479 : Blo 1457548 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B2629945 : Blo 1457548 2629945 := bstep (se 2 (by rfl) ⟨986229, by rfl⟩ : syracuseStep 2629945 = 1972459) B1972459
theorem B13304171 : Blo 1457548 13304171 := bstep (se 1 (by rfl) ⟨9978128, by rfl⟩ : syracuseStep 13304171 = 19956257) B19956257
theorem B2187803 : Blo 1457548 2187803 := bstep (se 1 (by rfl) ⟨1640852, by rfl⟩ : syracuseStep 2187803 = 3281705) B3281705
theorem B1458715 : Blo 1457548 1458715 := bstep (se 1 (by rfl) ⟨1094036, by rfl⟩ : syracuseStep 1458715 = 2188073) B2188073
theorem B1458719 : Blo 1457548 1458719 := bstep (se 1 (by rfl) ⟨1094039, by rfl⟩ : syracuseStep 1458719 = 2188079) B2188079
theorem B1458799 : Blo 1457548 1458799 := bstep (se 1 (by rfl) ⟨1094099, by rfl⟩ : syracuseStep 1458799 = 2188199) B2188199
theorem B1458855 : Blo 1457548 1458855 := bstep (se 1 (by rfl) ⟨1094141, by rfl⟩ : syracuseStep 1458855 = 2188283) B2188283
theorem B2187983 : Blo 1457548 2187983 := bstep (se 1 (by rfl) ⟨1640987, by rfl⟩ : syracuseStep 2187983 = 3281975) B3281975
theorem B1458895 : Blo 1457548 1458895 := bstep (se 1 (by rfl) ⟨1094171, by rfl⟩ : syracuseStep 1458895 = 2188343) B2188343
theorem B2187995 : Blo 1457548 2187995 := bstep (se 1 (by rfl) ⟨1640996, by rfl⟩ : syracuseStep 2187995 = 3281993) B3281993
theorem B4924151 : Blo 1457548 4924151 := bstep (se 1 (by rfl) ⟨3693113, by rfl⟩ : syracuseStep 4924151 = 7386227) B7386227
theorem B1458975 : Blo 1457548 1458975 := bstep (se 1 (by rfl) ⟨1094231, by rfl⟩ : syracuseStep 1458975 = 2188463) B2188463
theorem B28025675 : Blo 1457548 28025675 := bstep (se 1 (by rfl) ⟨21019256, by rfl⟩ : syracuseStep 28025675 = 42038513) B42038513
theorem B1459247 : Blo 1457548 1459247 := bstep (se 1 (by rfl) ⟨1094435, by rfl⟩ : syracuseStep 1459247 = 2188871) B2188871
theorem B1459311 : Blo 1457548 1459311 := bstep (se 1 (by rfl) ⟨1094483, by rfl⟩ : syracuseStep 1459311 = 2188967) B2188967
theorem B2188409 : Blo 1457548 2188409 := bstep (se 2 (by rfl) ⟨820653, by rfl⟩ : syracuseStep 2188409 = 1641307) B1641307
theorem B4924583 : Blo 1457548 4924583 := bstep (se 1 (by rfl) ⟨3693437, by rfl⟩ : syracuseStep 4924583 = 7386875) B7386875
theorem B1459367 : Blo 1457548 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B1459391 : Blo 1457548 1459391 := bstep (se 1 (by rfl) ⟨1094543, by rfl⟩ : syracuseStep 1459391 = 2189087) B2189087
theorem B1459423 : Blo 1457548 1459423 := bstep (se 1 (by rfl) ⟨1094567, by rfl⟩ : syracuseStep 1459423 = 2189135) B2189135
theorem B4924691 : Blo 1457548 4924691 := bstep (se 1 (by rfl) ⟨3693518, by rfl⟩ : syracuseStep 4924691 = 7387037) B7387037
theorem B11076911 : Blo 1457548 11076911 := bstep (se 1 (by rfl) ⟨8307683, by rfl⟩ : syracuseStep 11076911 = 16615367) B16615367
theorem B1459503 : Blo 1457548 1459503 := bstep (se 1 (by rfl) ⟨1094627, by rfl⟩ : syracuseStep 1459503 = 2189255) B2189255
theorem B1639759 : Blo 1457548 1639759 := bstep (se 1 (by rfl) ⟨1229819, by rfl⟩ : syracuseStep 1639759 = 2459639) B2459639
theorem B7005611 : Blo 1457548 7005611 := bstep (se 1 (by rfl) ⟨5254208, by rfl⟩ : syracuseStep 7005611 = 10508417) B10508417
theorem B10659271 : Blo 1457548 10659271 := bstep (se 1 (by rfl) ⟨7994453, by rfl⟩ : syracuseStep 10659271 = 15988907) B15988907
theorem B11822717 : Blo 1457548 11822717 := bstep (se 3 (by rfl) ⟨2216759, by rfl⟩ : syracuseStep 11822717 = 4433519) B4433519
theorem B4925231 : Blo 1457548 4925231 := bstep (se 1 (by rfl) ⟨3693923, by rfl⟩ : syracuseStep 4925231 = 7387847) B7387847
theorem B4220891 : Blo 1457548 4220891 := bstep (se 1 (by rfl) ⟨3165668, by rfl⟩ : syracuseStep 4220891 = 6331337) B6331337
theorem B2189279 : Blo 1457548 2189279 := bstep (se 1 (by rfl) ⟨1641959, by rfl⟩ : syracuseStep 2189279 = 3283919) B3283919
theorem B47319011 : Blo 1457548 47319011 := bstep (se 1 (by rfl) ⟨35489258, by rfl⟩ : syracuseStep 47319011 = 70978517) B70978517
theorem B2189291 : Blo 1457548 2189291 := bstep (se 1 (by rfl) ⟨1641968, by rfl⟩ : syracuseStep 2189291 = 3283937) B3283937
theorem B5539823 : Blo 1457548 5539823 := bstep (se 1 (by rfl) ⟨4154867, by rfl⟩ : syracuseStep 5539823 = 8309735) B8309735
theorem B9340919 : Blo 1457548 9340919 := bstep (se 1 (by rfl) ⟨7005689, by rfl⟩ : syracuseStep 9340919 = 14011379) B14011379
theorem B1640479 : Blo 1457548 1640479 := bstep (se 1 (by rfl) ⟨1230359, by rfl⟩ : syracuseStep 1640479 = 2460719) B2460719
theorem B3115169 : Blo 1457548 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B105171209 : Blo 1457548 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B1640731 : Blo 1457548 1640731 := bstep (se 1 (by rfl) ⟨1230548, by rfl⟩ : syracuseStep 1640731 = 2461097) B2461097
theorem B2459983 : Blo 1457548 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B5327183 : Blo 1457548 5327183 := bstep (se 1 (by rfl) ⟨3995387, by rfl⟩ : syracuseStep 5327183 = 7990775) B7990775
theorem B14215753 : Blo 1457548 14215753 := bstep (se 2 (by rfl) ⟨5330907, by rfl⟩ : syracuseStep 14215753 = 10661815) B10661815
theorem B3279707 : Blo 1457548 3279707 := bstep (se 1 (by rfl) ⟨2459780, by rfl⟩ : syracuseStep 3279707 = 4919561) B4919561
theorem B6229055 : Blo 1457548 6229055 := bstep (se 1 (by rfl) ⟨4671791, by rfl⟩ : syracuseStep 6229055 = 9343583) B9343583
theorem B2460847 : Blo 1457548 2460847 := bstep (se 1 (by rfl) ⟨1845635, by rfl⟩ : syracuseStep 2460847 = 3691271) B3691271
theorem B11078855 : Blo 1457548 11078855 := bstep (se 1 (by rfl) ⟨8309141, by rfl⟩ : syracuseStep 11078855 = 16618283) B16618283
theorem B4672765 : Blo 1457548 4672765 := bstep (se 3 (by rfl) ⟨876143, by rfl⟩ : syracuseStep 4672765 = 1752287) B1752287
theorem B2075959 : Blo 1457548 2075959 := bstep (se 1 (by rfl) ⟨1556969, by rfl⟩ : syracuseStep 2075959 = 3113939) B3113939
theorem B7007593 : Blo 1457548 7007593 := bstep (se 2 (by rfl) ⟨2627847, by rfl⟩ : syracuseStep 7007593 = 5255695) B5255695
theorem B1641883 : Blo 1457548 1641883 := bstep (se 1 (by rfl) ⟨1231412, by rfl⟩ : syracuseStep 1641883 = 2462825) B2462825
theorem B24931799 : Blo 1457548 24931799 := bstep (se 1 (by rfl) ⟨18698849, by rfl⟩ : syracuseStep 24931799 = 37397699) B37397699
theorem B3280463 : Blo 1457548 3280463 := bstep (se 1 (by rfl) ⟨2460347, by rfl⟩ : syracuseStep 3280463 = 4920695) B4920695
theorem B1478395 : Blo 1457548 1478395 := bstep (se 1 (by rfl) ⟨1108796, by rfl⟩ : syracuseStep 1478395 = 2217593) B2217593
theorem B3370889 : Blo 1457548 3370889 := bstep (se 2 (by rfl) ⟨1264083, by rfl⟩ : syracuseStep 3370889 = 2528167) B2528167
theorem B2461691 : Blo 1457548 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B9351247 : Blo 1457548 9351247 := bstep (se 1 (by rfl) ⟨7013435, by rfl⟩ : syracuseStep 9351247 = 14026871) B14026871
theorem B4919399 : Blo 1457548 4919399 := bstep (se 1 (by rfl) ⟨3689549, by rfl⟩ : syracuseStep 4919399 = 7379099) B7379099
theorem B2461799 : Blo 1457548 2461799 := bstep (se 1 (by rfl) ⟨1846349, by rfl⟩ : syracuseStep 2461799 = 3692699) B3692699
theorem B3281003 : Blo 1457548 3281003 := bstep (se 1 (by rfl) ⟨2460752, by rfl⟩ : syracuseStep 3281003 = 4921505) B4921505
theorem B3551375 : Blo 1457548 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B3281057 : Blo 1457548 3281057 := bstep (se 2 (by rfl) ⟨1230396, by rfl⟩ : syracuseStep 3281057 = 2460793) B2460793
theorem B3281183 : Blo 1457548 3281183 := bstep (se 1 (by rfl) ⟨2460887, by rfl⟩ : syracuseStep 3281183 = 4921775) B4921775
theorem B7008727 : Blo 1457548 7008727 := bstep (se 1 (by rfl) ⟨5256545, by rfl⟩ : syracuseStep 7008727 = 10513091) B10513091
theorem B28021211 : Blo 1457548 28021211 := bstep (se 1 (by rfl) ⟨21015908, by rfl⟩ : syracuseStep 28021211 = 42031817) B42031817
theorem B5534203 : Blo 1457548 5534203 := bstep (se 1 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 5534203 = 8301305) B8301305
theorem B8303219 : Blo 1457548 8303219 := bstep (se 1 (by rfl) ⟨6227414, by rfl⟩ : syracuseStep 8303219 = 12454829) B12454829
theorem B2462555 : Blo 1457548 2462555 := bstep (se 1 (by rfl) ⟨1846916, by rfl⟩ : syracuseStep 2462555 = 3693833) B3693833
theorem B3281903 : Blo 1457548 3281903 := bstep (se 1 (by rfl) ⟨2461427, by rfl⟩ : syracuseStep 3281903 = 4922855) B4922855
theorem B3691615 : Blo 1457548 3691615 := bstep (se 1 (by rfl) ⟨2768711, by rfl⟩ : syracuseStep 3691615 = 5537423) B5537423
theorem B4494703 : Blo 1457548 4494703 := bstep (se 1 (by rfl) ⟨3371027, by rfl⟩ : syracuseStep 4494703 = 6742055) B6742055
theorem B3282407 : Blo 1457548 3282407 := bstep (se 1 (by rfl) ⟨2461805, by rfl⟩ : syracuseStep 3282407 = 4923611) B4923611
theorem B4920911 : Blo 1457548 4920911 := bstep (se 1 (by rfl) ⟨3690683, by rfl⟩ : syracuseStep 4920911 = 7381367) B7381367
theorem B3282569 : Blo 1457548 3282569 := bstep (se 2 (by rfl) ⟨1230963, by rfl⟩ : syracuseStep 3282569 = 2461927) B2461927
theorem B3282587 : Blo 1457548 3282587 := bstep (se 1 (by rfl) ⟨2461940, by rfl⟩ : syracuseStep 3282587 = 4923881) B4923881
theorem B3503951 : Blo 1457548 3503951 := bstep (se 1 (by rfl) ⟨2627963, by rfl⟩ : syracuseStep 3503951 = 5255927) B5255927
theorem B3282785 : Blo 1457548 3282785 := bstep (se 2 (by rfl) ⟨1231044, by rfl⟩ : syracuseStep 3282785 = 2462089) B2462089
theorem B4921289 : Blo 1457548 4921289 := bstep (se 2 (by rfl) ⟨1845483, by rfl⟩ : syracuseStep 4921289 = 3690967) B3690967
theorem B10516463 : Blo 1457548 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B3282983 : Blo 1457548 3282983 := bstep (se 1 (by rfl) ⟨2462237, by rfl⟩ : syracuseStep 3282983 = 4924475) B4924475
theorem B24909929 : Blo 1457548 24909929 := bstep (se 2 (by rfl) ⟨9341223, by rfl⟩ : syracuseStep 24909929 = 18682447) B18682447
theorem B1972361 : Blo 1457548 1972361 := bstep (se 2 (by rfl) ⟨739635, by rfl⟩ : syracuseStep 1972361 = 1479271) B1479271
theorem B4921559 : Blo 1457548 4921559 := bstep (se 1 (by rfl) ⟨3691169, by rfl⟩ : syracuseStep 4921559 = 7382339) B7382339
theorem B3283163 : Blo 1457548 3283163 := bstep (se 1 (by rfl) ⟨2462372, by rfl⟩ : syracuseStep 3283163 = 4924745) B4924745
theorem B3283361 : Blo 1457548 3283361 := bstep (se 2 (by rfl) ⟨1231260, by rfl⟩ : syracuseStep 3283361 = 2462521) B2462521
theorem B3283433 : Blo 1457548 3283433 := bstep (se 2 (by rfl) ⟨1231287, by rfl⟩ : syracuseStep 3283433 = 2462575) B2462575
theorem B4922099 : Blo 1457548 4922099 := bstep (se 1 (by rfl) ⟨3691574, by rfl⟩ : syracuseStep 4922099 = 7383149) B7383149
theorem B17742881 : Blo 1457548 17742881 := bstep (se 2 (by rfl) ⟨6653580, by rfl⟩ : syracuseStep 17742881 = 13307161) B13307161
theorem B2186447 : Blo 1457548 2186447 := bstep (se 1 (by rfl) ⟨1639835, by rfl⟩ : syracuseStep 2186447 = 3279671) B3279671
theorem B5258465 : Blo 1457548 5258465 := bstep (se 2 (by rfl) ⟨1971924, by rfl⟩ : syracuseStep 5258465 = 3943849) B3943849
theorem B7380233 : Blo 1457548 7380233 := bstep (se 2 (by rfl) ⟨2767587, by rfl⟩ : syracuseStep 7380233 = 5535175) B5535175
theorem B2186567 : Blo 1457548 2186567 := bstep (se 1 (by rfl) ⟨1639925, by rfl⟩ : syracuseStep 2186567 = 3279851) B3279851
theorem B7388495 : Blo 1457548 7388495 := bstep (se 1 (by rfl) ⟨5541371, by rfl⟩ : syracuseStep 7388495 = 11082743) B11082743
theorem B5537119 : Blo 1457548 5537119 := bstep (se 1 (by rfl) ⟨4152839, by rfl⟩ : syracuseStep 5537119 = 8305679) B8305679
theorem B50552225 : Blo 1457548 50552225 := bstep (se 2 (by rfl) ⟨18957084, by rfl⟩ : syracuseStep 50552225 = 37914169) B37914169
theorem B1457615 : Blo 1457548 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B2186729 : Blo 1457548 2186729 := bstep (se 2 (by rfl) ⟨820023, by rfl⟩ : syracuseStep 2186729 = 1640047) B1640047
theorem B12459581 : Blo 1457548 12459581 := bstep (se 3 (by rfl) ⟨2336171, by rfl⟩ : syracuseStep 12459581 = 4672343) B4672343
theorem B3505727 : Blo 1457548 3505727 := bstep (se 1 (by rfl) ⟨2629295, by rfl⟩ : syracuseStep 3505727 = 5258591) B5258591
theorem B1457775 : Blo 1457548 1457775 := bstep (se 1 (by rfl) ⟨1093331, by rfl⟩ : syracuseStep 1457775 = 2186663) B2186663
theorem B2186873 : Blo 1457548 2186873 := bstep (se 2 (by rfl) ⟨820077, by rfl⟩ : syracuseStep 2186873 = 1640155) B1640155
theorem B1457831 : Blo 1457548 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B1457895 : Blo 1457548 1457895 := bstep (se 1 (by rfl) ⟨1093421, by rfl⟩ : syracuseStep 1457895 = 2186843) B2186843
theorem B1457951 : Blo 1457548 1457951 := bstep (se 1 (by rfl) ⟨1093463, by rfl⟩ : syracuseStep 1457951 = 2186927) B2186927
theorem B4923233 : Blo 1457548 4923233 := bstep (se 2 (by rfl) ⟨1846212, by rfl⟩ : syracuseStep 4923233 = 3692425) B3692425
theorem B1458031 : Blo 1457548 1458031 := bstep (se 1 (by rfl) ⟨1093523, by rfl⟩ : syracuseStep 1458031 = 2187047) B2187047
theorem B2187119 : Blo 1457548 2187119 := bstep (se 1 (by rfl) ⟨1640339, by rfl⟩ : syracuseStep 2187119 = 3280679) B3280679
theorem B1458087 : Blo 1457548 1458087 := bstep (se 1 (by rfl) ⟨1093565, by rfl⟩ : syracuseStep 1458087 = 2187131) B2187131
theorem B2187305 : Blo 1457548 2187305 := bstep (se 2 (by rfl) ⟨820239, by rfl⟩ : syracuseStep 2187305 = 1640479) B1640479
theorem B2187335 : Blo 1457548 2187335 := bstep (se 1 (by rfl) ⟨1640501, by rfl⟩ : syracuseStep 2187335 = 3281003) B3281003
theorem B12468329 : Blo 1457548 12468329 := bstep (se 2 (by rfl) ⟨4675623, by rfl⟩ : syracuseStep 12468329 = 9351247) B9351247
theorem B2187371 : Blo 1457548 2187371 := bstep (se 1 (by rfl) ⟨1640528, by rfl⟩ : syracuseStep 2187371 = 3281057) B3281057
theorem B2187455 : Blo 1457548 2187455 := bstep (se 1 (by rfl) ⟨1640591, by rfl⟩ : syracuseStep 2187455 = 3281183) B3281183
theorem B1458535 : Blo 1457548 1458535 := bstep (se 1 (by rfl) ⟨1093901, by rfl⟩ : syracuseStep 1458535 = 2187803) B2187803
theorem B5259629 : Blo 1457548 5259629 := bstep (se 3 (by rfl) ⟨986180, by rfl⟩ : syracuseStep 5259629 = 1972361) B1972361
theorem B2187641 : Blo 1457548 2187641 := bstep (se 2 (by rfl) ⟨820365, by rfl⟩ : syracuseStep 2187641 = 1640731) B1640731
theorem B9470333 : Blo 1457548 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B3506593 : Blo 1457548 3506593 := bstep (se 2 (by rfl) ⟨1314972, by rfl⟩ : syracuseStep 3506593 = 2629945) B2629945
theorem B1458655 : Blo 1457548 1458655 := bstep (se 1 (by rfl) ⟨1093991, by rfl⟩ : syracuseStep 1458655 = 2187983) B2187983
theorem B1458663 : Blo 1457548 1458663 := bstep (se 1 (by rfl) ⟨1093997, by rfl⟩ : syracuseStep 1458663 = 2187995) B2187995
theorem B2187935 : Blo 1457548 2187935 := bstep (se 1 (by rfl) ⟨1640951, by rfl⟩ : syracuseStep 2187935 = 3281903) B3281903
theorem B1458939 : Blo 1457548 1458939 := bstep (se 1 (by rfl) ⟨1094204, by rfl⟩ : syracuseStep 1458939 = 2188409) B2188409
theorem B4670407 : Blo 1457548 4670407 := bstep (se 1 (by rfl) ⟨3502805, by rfl⟩ : syracuseStep 4670407 = 7005611) B7005611
theorem B2188271 : Blo 1457548 2188271 := bstep (se 1 (by rfl) ⟨1641203, by rfl⟩ : syracuseStep 2188271 = 3282407) B3282407
theorem B2188379 : Blo 1457548 2188379 := bstep (se 1 (by rfl) ⟨1641284, by rfl⟩ : syracuseStep 2188379 = 3282569) B3282569
theorem B2188391 : Blo 1457548 2188391 := bstep (se 1 (by rfl) ⟨1641293, by rfl⟩ : syracuseStep 2188391 = 3282587) B3282587
theorem B2335967 : Blo 1457548 2335967 := bstep (se 1 (by rfl) ⟨1751975, by rfl⟩ : syracuseStep 2335967 = 3503951) B3503951
theorem B2188523 : Blo 1457548 2188523 := bstep (se 1 (by rfl) ⟨1641392, by rfl⟩ : syracuseStep 2188523 = 3282785) B3282785
theorem B1459519 : Blo 1457548 1459519 := bstep (se 1 (by rfl) ⟨1094639, by rfl⟩ : syracuseStep 1459519 = 2189279) B2189279
theorem B1459527 : Blo 1457548 1459527 := bstep (se 1 (by rfl) ⟨1094645, by rfl⟩ : syracuseStep 1459527 = 2189291) B2189291
theorem B6227279 : Blo 1457548 6227279 := bstep (se 1 (by rfl) ⟨4670459, by rfl⟩ : syracuseStep 6227279 = 9340919) B9340919
theorem B2188655 : Blo 1457548 2188655 := bstep (se 1 (by rfl) ⟨1641491, by rfl⟩ : syracuseStep 2188655 = 3282983) B3282983
theorem B16606619 : Blo 1457548 16606619 := bstep (se 1 (by rfl) ⟨12454964, by rfl⟩ : syracuseStep 16606619 = 24909929) B24909929
theorem B2188775 : Blo 1457548 2188775 := bstep (se 1 (by rfl) ⟨1641581, by rfl⟩ : syracuseStep 2188775 = 3283163) B3283163
theorem B9348605 : Blo 1457548 9348605 := bstep (se 3 (by rfl) ⟨1752863, by rfl⟩ : syracuseStep 9348605 = 3505727) B3505727
theorem B2188907 : Blo 1457548 2188907 := bstep (se 1 (by rfl) ⟨1641680, by rfl⟩ : syracuseStep 2188907 = 3283361) B3283361
theorem B2188955 : Blo 1457548 2188955 := bstep (se 1 (by rfl) ⟨1641716, by rfl⟩ : syracuseStep 2188955 = 3283433) B3283433
theorem B7382825 : Blo 1457548 7382825 := bstep (se 2 (by rfl) ⟨2768559, by rfl⟩ : syracuseStep 7382825 = 5537119) B5537119
theorem B2189177 : Blo 1457548 2189177 := bstep (se 2 (by rfl) ⟨820941, by rfl⟩ : syracuseStep 2189177 = 1641883) B1641883
theorem B4925663 : Blo 1457548 4925663 := bstep (se 1 (by rfl) ⟨3694247, by rfl⟩ : syracuseStep 4925663 = 7388495) B7388495
theorem B2247259 : Blo 1457548 2247259 := bstep (se 1 (by rfl) ⟨1685444, by rfl⟩ : syracuseStep 2247259 = 3370889) B3370889
theorem B1641127 : Blo 1457548 1641127 := bstep (se 1 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 1641127 = 2461691) B2461691
theorem B3279599 : Blo 1457548 3279599 := bstep (se 1 (by rfl) ⟨2459699, by rfl⟩ : syracuseStep 3279599 = 4919399) B4919399
theorem B1641199 : Blo 1457548 1641199 := bstep (se 1 (by rfl) ⟨1230899, by rfl⟩ : syracuseStep 1641199 = 2461799) B2461799
theorem B2337607 : Blo 1457548 2337607 := bstep (se 1 (by rfl) ⟨1753205, by rfl⟩ : syracuseStep 2337607 = 3506411) B3506411
theorem B18680807 : Blo 1457548 18680807 := bstep (se 1 (by rfl) ⟨14010605, by rfl⟩ : syracuseStep 18680807 = 28021211) B28021211
theorem B3279977 : Blo 1457548 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B1641703 : Blo 1457548 1641703 := bstep (se 1 (by rfl) ⟨1231277, by rfl⟩ : syracuseStep 1641703 = 2462555) B2462555
theorem B8302013 : Blo 1457548 8302013 := bstep (se 3 (by rfl) ⟨1556627, by rfl⟩ : syracuseStep 8302013 = 3113255) B3113255
theorem B7384607 : Blo 1457548 7384607 := bstep (se 1 (by rfl) ⟨5538455, by rfl⟩ : syracuseStep 7384607 = 11076911) B11076911
theorem B3280607 : Blo 1457548 3280607 := bstep (se 1 (by rfl) ⟨2460455, by rfl⟩ : syracuseStep 3280607 = 4920911) B4920911
theorem B3280859 : Blo 1457548 3280859 := bstep (se 1 (by rfl) ⟨2460644, by rfl⟩ : syracuseStep 3280859 = 4921289) B4921289
theorem B7884773 : Blo 1457548 7884773 := bstep (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) B1478395
theorem B2813927 : Blo 1457548 2813927 := bstep (se 1 (by rfl) ⟨2110445, by rfl⟩ : syracuseStep 2813927 = 4220891) B4220891
theorem B2076779 : Blo 1457548 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B3281039 : Blo 1457548 3281039 := bstep (se 1 (by rfl) ⟨2460779, by rfl⟩ : syracuseStep 3281039 = 4921559) B4921559
theorem B3551455 : Blo 1457548 3551455 := bstep (se 1 (by rfl) ⟨2663591, by rfl⟩ : syracuseStep 3551455 = 5327183) B5327183
theorem B3281129 : Blo 1457548 3281129 := bstep (se 2 (by rfl) ⟨1230423, by rfl⟩ : syracuseStep 3281129 = 2460847) B2460847
theorem B31527245 : Blo 1457548 31527245 := bstep (se 3 (by rfl) ⟨5911358, by rfl⟩ : syracuseStep 31527245 = 11822717) B11822717
theorem B6230353 : Blo 1457548 6230353 := bstep (se 2 (by rfl) ⟨2336382, by rfl⟩ : syracuseStep 6230353 = 4672765) B4672765
theorem B9343457 : Blo 1457548 9343457 := bstep (se 2 (by rfl) ⟨3503796, by rfl⟩ : syracuseStep 9343457 = 7007593) B7007593
theorem B5992937 : Blo 1457548 5992937 := bstep (se 2 (by rfl) ⟨2247351, by rfl⟩ : syracuseStep 5992937 = 4494703) B4494703
theorem B3281399 : Blo 1457548 3281399 := bstep (se 1 (by rfl) ⟨2461049, by rfl⟩ : syracuseStep 3281399 = 4922099) B4922099
theorem B7385903 : Blo 1457548 7385903 := bstep (se 1 (by rfl) ⟨5539427, by rfl⟩ : syracuseStep 7385903 = 11078855) B11078855
theorem B4920155 : Blo 1457548 4920155 := bstep (se 1 (by rfl) ⟨3690116, by rfl⟩ : syracuseStep 4920155 = 7380233) B7380233
theorem B3282155 : Blo 1457548 3282155 := bstep (se 1 (by rfl) ⟨2461616, by rfl⟩ : syracuseStep 3282155 = 4923233) B4923233
theorem B8869447 : Blo 1457548 8869447 := bstep (se 1 (by rfl) ⟨6652085, by rfl⟩ : syracuseStep 8869447 = 13304171) B13304171
theorem B4151017 : Blo 1457548 4151017 := bstep (se 2 (by rfl) ⟨1556631, by rfl⟩ : syracuseStep 4151017 = 3113263) B3113263
theorem B5535479 : Blo 1457548 5535479 := bstep (se 1 (by rfl) ⟨4151609, by rfl⟩ : syracuseStep 5535479 = 8303219) B8303219
theorem B3282767 : Blo 1457548 3282767 := bstep (se 1 (by rfl) ⟨2462075, by rfl⟩ : syracuseStep 3282767 = 4924151) B4924151
theorem B18683783 : Blo 1457548 18683783 := bstep (se 1 (by rfl) ⟨14012837, by rfl⟩ : syracuseStep 18683783 = 28025675) B28025675
theorem B9344969 : Blo 1457548 9344969 := bstep (se 2 (by rfl) ⟨3504363, by rfl⟩ : syracuseStep 9344969 = 7008727) B7008727
theorem B7378937 : Blo 1457548 7378937 := bstep (se 2 (by rfl) ⟨2767101, by rfl⟩ : syracuseStep 7378937 = 5534203) B5534203
theorem B18954337 : Blo 1457548 18954337 := bstep (se 2 (by rfl) ⟨7107876, by rfl⟩ : syracuseStep 18954337 = 14215753) B14215753
theorem B3283055 : Blo 1457548 3283055 := bstep (se 1 (by rfl) ⟨2462291, by rfl⟩ : syracuseStep 3283055 = 4924583) B4924583
theorem B3283127 : Blo 1457548 3283127 := bstep (se 1 (by rfl) ⟨2462345, by rfl⟩ : syracuseStep 3283127 = 4924691) B4924691
theorem B3283487 : Blo 1457548 3283487 := bstep (se 1 (by rfl) ⟨2462615, by rfl⟩ : syracuseStep 3283487 = 4925231) B4925231
theorem B31546007 : Blo 1457548 31546007 := bstep (se 1 (by rfl) ⟨23659505, by rfl⟩ : syracuseStep 31546007 = 47319011) B47319011
theorem B7010975 : Blo 1457548 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B3693215 : Blo 1457548 3693215 := bstep (se 1 (by rfl) ⟨2769911, by rfl⟩ : syracuseStep 3693215 = 5539823) B5539823
theorem B4922153 : Blo 1457548 4922153 := bstep (se 2 (by rfl) ⟨1845807, by rfl⟩ : syracuseStep 4922153 = 3691615) B3691615
theorem B70114139 : Blo 1457548 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B2767945 : Blo 1457548 2767945 := bstep (se 2 (by rfl) ⟨1037979, by rfl⟩ : syracuseStep 2767945 = 2075959) B2075959
theorem B2186345 : Blo 1457548 2186345 := bstep (se 2 (by rfl) ⟨819879, by rfl⟩ : syracuseStep 2186345 = 1639759) B1639759
theorem B2186471 : Blo 1457548 2186471 := bstep (se 1 (by rfl) ⟨1639853, by rfl⟩ : syracuseStep 2186471 = 3279707) B3279707
theorem B14212361 : Blo 1457548 14212361 := bstep (se 2 (by rfl) ⟨5329635, by rfl⟩ : syracuseStep 14212361 = 10659271) B10659271
theorem B11828587 : Blo 1457548 11828587 := bstep (se 1 (by rfl) ⟨8871440, by rfl⟩ : syracuseStep 11828587 = 17742881) B17742881
theorem B4152703 : Blo 1457548 4152703 := bstep (se 1 (by rfl) ⟨3114527, by rfl⟩ : syracuseStep 4152703 = 6229055) B6229055
theorem B1457631 : Blo 1457548 1457631 := bstep (se 1 (by rfl) ⟨1093223, by rfl⟩ : syracuseStep 1457631 = 2186447) B2186447
theorem B3505643 : Blo 1457548 3505643 := bstep (se 1 (by rfl) ⟨2629232, by rfl⟩ : syracuseStep 3505643 = 5258465) B5258465
theorem B1457711 : Blo 1457548 1457711 := bstep (se 1 (by rfl) ⟨1093283, by rfl⟩ : syracuseStep 1457711 = 2186567) B2186567
theorem B33701483 : Blo 1457548 33701483 := bstep (se 1 (by rfl) ⟨25276112, by rfl⟩ : syracuseStep 33701483 = 50552225) B50552225
theorem B16621199 : Blo 1457548 16621199 := bstep (se 1 (by rfl) ⟨12465899, by rfl⟩ : syracuseStep 16621199 = 24931799) B24931799
theorem B1457819 : Blo 1457548 1457819 := bstep (se 1 (by rfl) ⟨1093364, by rfl⟩ : syracuseStep 1457819 = 2186729) B2186729
theorem B8306387 : Blo 1457548 8306387 := bstep (se 1 (by rfl) ⟨6229790, by rfl⟩ : syracuseStep 8306387 = 12459581) B12459581
theorem B2186975 : Blo 1457548 2186975 := bstep (se 1 (by rfl) ⟨1640231, by rfl⟩ : syracuseStep 2186975 = 3280463) B3280463
theorem B1457915 : Blo 1457548 1457915 := bstep (se 1 (by rfl) ⟨1093436, by rfl⟩ : syracuseStep 1457915 = 2186873) B2186873
theorem B1458079 : Blo 1457548 1458079 := bstep (se 1 (by rfl) ⟨1093559, by rfl⟩ : syracuseStep 1458079 = 2187119) B2187119
theorem B1458203 : Blo 1457548 1458203 := bstep (se 1 (by rfl) ⟨1093652, by rfl⟩ : syracuseStep 1458203 = 2187305) B2187305
theorem B1458223 : Blo 1457548 1458223 := bstep (se 1 (by rfl) ⟨1093667, by rfl⟩ : syracuseStep 1458223 = 2187335) B2187335
theorem B1458247 : Blo 1457548 1458247 := bstep (se 1 (by rfl) ⟨1093685, by rfl⟩ : syracuseStep 1458247 = 2187371) B2187371
theorem B2187359 : Blo 1457548 2187359 := bstep (se 1 (by rfl) ⟨1640519, by rfl⟩ : syracuseStep 2187359 = 3281039) B3281039
theorem B1458303 : Blo 1457548 1458303 := bstep (se 1 (by rfl) ⟨1093727, by rfl⟩ : syracuseStep 1458303 = 2187455) B2187455
theorem B25272449 : Blo 1457548 25272449 := bstep (se 2 (by rfl) ⟨9477168, by rfl⟩ : syracuseStep 25272449 = 18954337) B18954337
theorem B2187419 : Blo 1457548 2187419 := bstep (se 1 (by rfl) ⟨1640564, by rfl⟩ : syracuseStep 2187419 = 3281129) B3281129
theorem B3506419 : Blo 1457548 3506419 := bstep (se 1 (by rfl) ⟨2629814, by rfl⟩ : syracuseStep 3506419 = 5259629) B5259629
theorem B1458427 : Blo 1457548 1458427 := bstep (se 1 (by rfl) ⟨1093820, by rfl⟩ : syracuseStep 1458427 = 2187641) B2187641
theorem B5538077 : Blo 1457548 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B4735273 : Blo 1457548 4735273 := bstep (se 2 (by rfl) ⟨1775727, by rfl⟩ : syracuseStep 4735273 = 3551455) B3551455
theorem B2187599 : Blo 1457548 2187599 := bstep (se 1 (by rfl) ⟨1640699, by rfl⟩ : syracuseStep 2187599 = 3281399) B3281399
theorem B1458623 : Blo 1457548 1458623 := bstep (se 1 (by rfl) ⟨1093967, by rfl⟩ : syracuseStep 1458623 = 2187935) B2187935
theorem B8307137 : Blo 1457548 8307137 := bstep (se 2 (by rfl) ⟨3115176, by rfl⟩ : syracuseStep 8307137 = 6230353) B6230353
theorem B4923935 : Blo 1457548 4923935 := bstep (se 1 (by rfl) ⟨3692951, by rfl⟩ : syracuseStep 4923935 = 7385903) B7385903
theorem B1458847 : Blo 1457548 1458847 := bstep (se 1 (by rfl) ⟨1094135, by rfl⟩ : syracuseStep 1458847 = 2188271) B2188271
theorem B1458919 : Blo 1457548 1458919 := bstep (se 1 (by rfl) ⟨1094189, by rfl⟩ : syracuseStep 1458919 = 2188379) B2188379
theorem B1458927 : Blo 1457548 1458927 := bstep (se 1 (by rfl) ⟨1094195, by rfl⟩ : syracuseStep 1458927 = 2188391) B2188391
theorem B1557311 : Blo 1457548 1557311 := bstep (se 1 (by rfl) ⟨1167983, by rfl⟩ : syracuseStep 1557311 = 2335967) B2335967
theorem B2188103 : Blo 1457548 2188103 := bstep (se 1 (by rfl) ⟨1641077, by rfl⟩ : syracuseStep 2188103 = 3282155) B3282155
theorem B1459015 : Blo 1457548 1459015 := bstep (se 1 (by rfl) ⟨1094261, by rfl⟩ : syracuseStep 1459015 = 2188523) B2188523
theorem B2188169 : Blo 1457548 2188169 := bstep (se 2 (by rfl) ⟨820563, by rfl⟩ : syracuseStep 2188169 = 1641127) B1641127
theorem B1459103 : Blo 1457548 1459103 := bstep (se 1 (by rfl) ⟨1094327, by rfl⟩ : syracuseStep 1459103 = 2188655) B2188655
theorem B2188265 : Blo 1457548 2188265 := bstep (se 2 (by rfl) ⟨820599, by rfl⟩ : syracuseStep 2188265 = 1641199) B1641199
theorem B1459183 : Blo 1457548 1459183 := bstep (se 1 (by rfl) ⟨1094387, by rfl⟩ : syracuseStep 1459183 = 2188775) B2188775
theorem B1459271 : Blo 1457548 1459271 := bstep (se 1 (by rfl) ⟨1094453, by rfl⟩ : syracuseStep 1459271 = 2188907) B2188907
theorem B1459303 : Blo 1457548 1459303 := bstep (se 1 (by rfl) ⟨1094477, by rfl⟩ : syracuseStep 1459303 = 2188955) B2188955
theorem B2188511 : Blo 1457548 2188511 := bstep (se 1 (by rfl) ⟨1641383, by rfl⟩ : syracuseStep 2188511 = 3282767) B3282767
theorem B1459451 : Blo 1457548 1459451 := bstep (se 1 (by rfl) ⟨1094588, by rfl⟩ : syracuseStep 1459451 = 2189177) B2189177
theorem B6227209 : Blo 1457548 6227209 := bstep (se 2 (by rfl) ⟨2335203, by rfl⟩ : syracuseStep 6227209 = 4670407) B4670407
theorem B2188703 : Blo 1457548 2188703 := bstep (se 1 (by rfl) ⟨1641527, by rfl⟩ : syracuseStep 2188703 = 3283055) B3283055
theorem B2188751 : Blo 1457548 2188751 := bstep (se 1 (by rfl) ⟨1641563, by rfl⟩ : syracuseStep 2188751 = 3283127) B3283127
theorem B2188937 : Blo 1457548 2188937 := bstep (se 2 (by rfl) ⟨820851, by rfl⟩ : syracuseStep 2188937 = 1641703) B1641703
theorem B2188991 : Blo 1457548 2188991 := bstep (se 1 (by rfl) ⟨1641743, by rfl⟩ : syracuseStep 2188991 = 3283487) B3283487
theorem B18695933 : Blo 1457548 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B21030671 : Blo 1457548 21030671 := bstep (se 1 (by rfl) ⟨15773003, by rfl⟩ : syracuseStep 21030671 = 31546007) B31546007
theorem B15771449 : Blo 1457548 15771449 := bstep (se 2 (by rfl) ⟨5914293, by rfl⟩ : syracuseStep 15771449 = 11828587) B11828587
theorem B12453871 : Blo 1457548 12453871 := bstep (se 1 (by rfl) ⟨9340403, by rfl⟩ : syracuseStep 12453871 = 18680807) B18680807
theorem B2337095 : Blo 1457548 2337095 := bstep (se 1 (by rfl) ⟨1752821, by rfl⟩ : syracuseStep 2337095 = 3505643) B3505643
theorem B6228971 : Blo 1457548 6228971 := bstep (se 1 (by rfl) ⟨4671728, by rfl⟩ : syracuseStep 6228971 = 9343457) B9343457
theorem B3280103 : Blo 1457548 3280103 := bstep (se 1 (by rfl) ⟨2460077, by rfl⟩ : syracuseStep 3280103 = 4920155) B4920155
theorem B11071079 : Blo 1457548 11071079 := bstep (se 1 (by rfl) ⟨8303309, by rfl⟩ : syracuseStep 11071079 = 16606619) B16606619
theorem B3116809 : Blo 1457548 3116809 := bstep (se 2 (by rfl) ⟨1168803, by rfl⟩ : syracuseStep 3116809 = 2337607) B2337607
theorem B3690319 : Blo 1457548 3690319 := bstep (se 1 (by rfl) ⟨2767739, by rfl⟩ : syracuseStep 3690319 = 5535479) B5535479
theorem B12455855 : Blo 1457548 12455855 := bstep (se 1 (by rfl) ⟨9341891, by rfl⟩ : syracuseStep 12455855 = 18683783) B18683783
theorem B6229979 : Blo 1457548 6229979 := bstep (se 1 (by rfl) ⟨4672484, by rfl⟩ : syracuseStep 6229979 = 9344969) B9344969
theorem B4919291 : Blo 1457548 4919291 := bstep (se 1 (by rfl) ⟨3689468, by rfl⟩ : syracuseStep 4919291 = 7378937) B7378937
theorem B3690593 : Blo 1457548 3690593 := bstep (se 2 (by rfl) ⟨1383972, by rfl⟩ : syracuseStep 3690593 = 2767945) B2767945
theorem B2462143 : Blo 1457548 2462143 := bstep (se 1 (by rfl) ⟨1846607, by rfl⟩ : syracuseStep 2462143 = 3693215) B3693215
theorem B3281435 : Blo 1457548 3281435 := bstep (se 1 (by rfl) ⟨2461076, by rfl⟩ : syracuseStep 3281435 = 4922153) B4922153
theorem B11825929 : Blo 1457548 11825929 := bstep (se 2 (by rfl) ⟨4434723, by rfl⟩ : syracuseStep 11825929 = 8869447) B8869447
theorem B9474907 : Blo 1457548 9474907 := bstep (se 1 (by rfl) ⟨7106180, by rfl⟩ : syracuseStep 9474907 = 14212361) B14212361
theorem B5534675 : Blo 1457548 5534675 := bstep (se 1 (by rfl) ⟨4151006, by rfl⟩ : syracuseStep 5534675 = 8302013) B8302013
theorem B5534689 : Blo 1457548 5534689 := bstep (se 2 (by rfl) ⟨2075508, by rfl⟩ : syracuseStep 5534689 = 4151017) B4151017
theorem B22467655 : Blo 1457548 22467655 := bstep (se 1 (by rfl) ⟨16850741, by rfl⟩ : syracuseStep 22467655 = 33701483) B33701483
theorem B11080799 : Blo 1457548 11080799 := bstep (se 1 (by rfl) ⟨8310599, by rfl⟩ : syracuseStep 11080799 = 16621199) B16621199
theorem B5256515 : Blo 1457548 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B8312219 : Blo 1457548 8312219 := bstep (se 1 (by rfl) ⟨6234164, by rfl⟩ : syracuseStep 8312219 = 12468329) B12468329
theorem B21018163 : Blo 1457548 21018163 := bstep (se 1 (by rfl) ⟨15763622, by rfl⟩ : syracuseStep 21018163 = 31527245) B31527245
theorem B6313555 : Blo 1457548 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B3995291 : Blo 1457548 3995291 := bstep (se 1 (by rfl) ⟨2996468, by rfl⟩ : syracuseStep 3995291 = 5992937) B5992937
theorem B4675457 : Blo 1457548 4675457 := bstep (se 2 (by rfl) ⟨1753296, by rfl⟩ : syracuseStep 4675457 = 3506593) B3506593
theorem B2996345 : Blo 1457548 2996345 := bstep (se 2 (by rfl) ⟨1123629, by rfl⟩ : syracuseStep 2996345 = 2247259) B2247259
theorem B4151519 : Blo 1457548 4151519 := bstep (se 1 (by rfl) ⟨3113639, by rfl⟩ : syracuseStep 4151519 = 6227279) B6227279
theorem B6232403 : Blo 1457548 6232403 := bstep (se 1 (by rfl) ⟨4674302, by rfl⟩ : syracuseStep 6232403 = 9348605) B9348605
theorem B4921883 : Blo 1457548 4921883 := bstep (se 1 (by rfl) ⟨3691412, by rfl⟩ : syracuseStep 4921883 = 7382825) B7382825
theorem B3283775 : Blo 1457548 3283775 := bstep (se 1 (by rfl) ⟨2462831, by rfl⟩ : syracuseStep 3283775 = 4925663) B4925663
theorem B2186399 : Blo 1457548 2186399 := bstep (se 1 (by rfl) ⟨1639799, by rfl⟩ : syracuseStep 2186399 = 3279599) B3279599
theorem B5536937 : Blo 1457548 5536937 := bstep (se 2 (by rfl) ⟨2076351, by rfl⟩ : syracuseStep 5536937 = 4152703) B4152703
theorem B46742759 : Blo 1457548 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B1457563 : Blo 1457548 1457563 := bstep (se 1 (by rfl) ⟨1093172, by rfl⟩ : syracuseStep 1457563 = 2186345) B2186345
theorem B2186651 : Blo 1457548 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B1457647 : Blo 1457548 1457647 := bstep (se 1 (by rfl) ⟨1093235, by rfl⟩ : syracuseStep 1457647 = 2186471) B2186471
theorem B4923071 : Blo 1457548 4923071 := bstep (se 1 (by rfl) ⟨3692303, by rfl⟩ : syracuseStep 4923071 = 7384607) B7384607
theorem B5537591 : Blo 1457548 5537591 := bstep (se 1 (by rfl) ⟨4153193, by rfl⟩ : syracuseStep 5537591 = 8306387) B8306387
theorem B1457983 : Blo 1457548 1457983 := bstep (se 1 (by rfl) ⟨1093487, by rfl⟩ : syracuseStep 1457983 = 2186975) B2186975
theorem B2187071 : Blo 1457548 2187071 := bstep (se 1 (by rfl) ⟨1640303, by rfl⟩ : syracuseStep 2187071 = 3280607) B3280607
theorem B7503805 : Blo 1457548 7503805 := bstep (se 3 (by rfl) ⟨1406963, by rfl⟩ : syracuseStep 7503805 = 2813927) B2813927
theorem B2187239 : Blo 1457548 2187239 := bstep (se 1 (by rfl) ⟨1640429, by rfl⟩ : syracuseStep 2187239 = 3280859) B3280859
theorem B1458239 : Blo 1457548 1458239 := bstep (se 1 (by rfl) ⟨1093679, by rfl⟩ : syracuseStep 1458239 = 2187359) B2187359
theorem B1458279 : Blo 1457548 1458279 := bstep (se 1 (by rfl) ⟨1093709, by rfl⟩ : syracuseStep 1458279 = 2187419) B2187419
theorem B1458399 : Blo 1457548 1458399 := bstep (se 1 (by rfl) ⟨1093799, by rfl⟩ : syracuseStep 1458399 = 2187599) B2187599
theorem B5538091 : Blo 1457548 5538091 := bstep (se 1 (by rfl) ⟨4153568, by rfl⟩ : syracuseStep 5538091 = 8307137) B8307137
theorem B2187623 : Blo 1457548 2187623 := bstep (se 1 (by rfl) ⟨1640717, by rfl⟩ : syracuseStep 2187623 = 3281435) B3281435
theorem B1458735 : Blo 1457548 1458735 := bstep (se 1 (by rfl) ⟨1094051, by rfl⟩ : syracuseStep 1458735 = 2188103) B2188103
theorem B1458779 : Blo 1457548 1458779 := bstep (se 1 (by rfl) ⟨1094084, by rfl⟩ : syracuseStep 1458779 = 2188169) B2188169
theorem B1458843 : Blo 1457548 1458843 := bstep (se 1 (by rfl) ⟨1094132, by rfl⟩ : syracuseStep 1458843 = 2188265) B2188265
theorem B1459007 : Blo 1457548 1459007 := bstep (se 1 (by rfl) ⟨1094255, by rfl⟩ : syracuseStep 1459007 = 2188511) B2188511
theorem B14017373 : Blo 1457548 14017373 := bstep (se 3 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 14017373 = 5256515) B5256515
theorem B1459135 : Blo 1457548 1459135 := bstep (se 1 (by rfl) ⟨1094351, by rfl⟩ : syracuseStep 1459135 = 2188703) B2188703
theorem B1459167 : Blo 1457548 1459167 := bstep (se 1 (by rfl) ⟨1094375, by rfl⟩ : syracuseStep 1459167 = 2188751) B2188751
theorem B1459291 : Blo 1457548 1459291 := bstep (se 1 (by rfl) ⟨1094468, by rfl⟩ : syracuseStep 1459291 = 2188937) B2188937
theorem B2663527 : Blo 1457548 2663527 := bstep (se 1 (by rfl) ⟨1997645, by rfl⟩ : syracuseStep 2663527 = 3995291) B3995291
theorem B12633209 : Blo 1457548 12633209 := bstep (se 2 (by rfl) ⟨4737453, by rfl⟩ : syracuseStep 12633209 = 9474907) B9474907
theorem B1459327 : Blo 1457548 1459327 := bstep (se 1 (by rfl) ⟨1094495, by rfl⟩ : syracuseStep 1459327 = 2188991) B2188991
theorem B1558063 : Blo 1457548 1558063 := bstep (se 1 (by rfl) ⟨1168547, by rfl⟩ : syracuseStep 1558063 = 2337095) B2337095
theorem B2189183 : Blo 1457548 2189183 := bstep (se 1 (by rfl) ⟨1641887, by rfl⟩ : syracuseStep 2189183 = 3283775) B3283775
theorem B40020293 : Blo 1457548 40020293 := bstep (se 4 (by rfl) ⟨3751902, by rfl⟩ : syracuseStep 40020293 = 7503805) B7503805
theorem B4155745 : Blo 1457548 4155745 := bstep (se 2 (by rfl) ⟨1558404, by rfl⟩ : syracuseStep 4155745 = 3116809) B3116809
theorem B3279527 : Blo 1457548 3279527 := bstep (se 1 (by rfl) ⟨2459645, by rfl⟩ : syracuseStep 3279527 = 4919291) B4919291
theorem B2460395 : Blo 1457548 2460395 := bstep (se 1 (by rfl) ⟨1845296, by rfl⟩ : syracuseStep 2460395 = 3690593) B3690593
theorem B3689783 : Blo 1457548 3689783 := bstep (se 1 (by rfl) ⟨2767337, by rfl⟩ : syracuseStep 3689783 = 5534675) B5534675
theorem B5541479 : Blo 1457548 5541479 := bstep (se 1 (by rfl) ⟨4156109, by rfl⟩ : syracuseStep 5541479 = 8312219) B8312219
theorem B12463955 : Blo 1457548 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B14020447 : Blo 1457548 14020447 := bstep (se 1 (by rfl) ⟨10515335, by rfl⟩ : syracuseStep 14020447 = 21030671) B21030671
theorem B10514299 : Blo 1457548 10514299 := bstep (se 1 (by rfl) ⟨7885724, by rfl⟩ : syracuseStep 10514299 = 15771449) B15771449
theorem B3116971 : Blo 1457548 3116971 := bstep (se 1 (by rfl) ⟨2337728, by rfl⟩ : syracuseStep 3116971 = 4675457) B4675457
theorem B8302945 : Blo 1457548 8302945 := bstep (se 2 (by rfl) ⟨3113604, by rfl⟩ : syracuseStep 8302945 = 6227209) B6227209
theorem B3281255 : Blo 1457548 3281255 := bstep (se 1 (by rfl) ⟨2460941, by rfl⟩ : syracuseStep 3281255 = 4921883) B4921883
theorem B8418073 : Blo 1457548 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B3691291 : Blo 1457548 3691291 := bstep (se 1 (by rfl) ⟨2768468, by rfl⟩ : syracuseStep 3691291 = 5536937) B5536937
theorem B4920425 : Blo 1457548 4920425 := bstep (se 2 (by rfl) ⟨1845159, by rfl⟩ : syracuseStep 4920425 = 3690319) B3690319
theorem B3282047 : Blo 1457548 3282047 := bstep (se 1 (by rfl) ⟨2461535, by rfl⟩ : syracuseStep 3282047 = 4923071) B4923071
theorem B3691727 : Blo 1457548 3691727 := bstep (se 1 (by rfl) ⟨2768795, by rfl⟩ : syracuseStep 3691727 = 5537591) B5537591
theorem B8303903 : Blo 1457548 8303903 := bstep (se 1 (by rfl) ⟨6227927, by rfl⟩ : syracuseStep 8303903 = 12455855) B12455855
theorem B16848299 : Blo 1457548 16848299 := bstep (se 1 (by rfl) ⟨12636224, by rfl⟩ : syracuseStep 16848299 = 25272449) B25272449
theorem B3692051 : Blo 1457548 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B3282623 : Blo 1457548 3282623 := bstep (se 1 (by rfl) ⟨2461967, by rfl⟩ : syracuseStep 3282623 = 4923935) B4923935
theorem B6313697 : Blo 1457548 6313697 := bstep (se 2 (by rfl) ⟨2367636, by rfl⟩ : syracuseStep 6313697 = 4735273) B4735273
theorem B3282857 : Blo 1457548 3282857 := bstep (se 2 (by rfl) ⟨1231071, by rfl⟩ : syracuseStep 3282857 = 2462143) B2462143
theorem B7387199 : Blo 1457548 7387199 := bstep (se 1 (by rfl) ⟨5540399, by rfl⟩ : syracuseStep 7387199 = 11080799) B11080799
theorem B16619741 : Blo 1457548 16619741 := bstep (se 3 (by rfl) ⟨3116201, by rfl⟩ : syracuseStep 16619741 = 6232403) B6232403
theorem B15767905 : Blo 1457548 15767905 := bstep (se 2 (by rfl) ⟨5912964, by rfl⟩ : syracuseStep 15767905 = 11825929) B11825929
theorem B18700901 : Blo 1457548 18700901 := bstep (se 4 (by rfl) ⟨1753209, by rfl⟩ : syracuseStep 18700901 = 3506419) B3506419
theorem B7379585 : Blo 1457548 7379585 := bstep (se 2 (by rfl) ⟨2767344, by rfl⟩ : syracuseStep 7379585 = 5534689) B5534689
theorem B1997563 : Blo 1457548 1997563 := bstep (se 1 (by rfl) ⟨1498172, by rfl⟩ : syracuseStep 1997563 = 2996345) B2996345
theorem B29956873 : Blo 1457548 29956873 := bstep (se 2 (by rfl) ⟨11233827, by rfl⟩ : syracuseStep 29956873 = 22467655) B22467655
theorem B2767679 : Blo 1457548 2767679 := bstep (se 1 (by rfl) ⟨2075759, by rfl⟩ : syracuseStep 2767679 = 4151519) B4151519
theorem B4152647 : Blo 1457548 4152647 := bstep (se 1 (by rfl) ⟨3114485, by rfl⟩ : syracuseStep 4152647 = 6228971) B6228971
theorem B28024217 : Blo 1457548 28024217 := bstep (se 2 (by rfl) ⟨10509081, by rfl⟩ : syracuseStep 28024217 = 21018163) B21018163
theorem B1457599 : Blo 1457548 1457599 := bstep (se 1 (by rfl) ⟨1093199, by rfl⟩ : syracuseStep 1457599 = 2186399) B2186399
theorem B31161839 : Blo 1457548 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B2186735 : Blo 1457548 2186735 := bstep (se 1 (by rfl) ⟨1640051, by rfl⟩ : syracuseStep 2186735 = 3280103) B3280103
theorem B4152829 : Blo 1457548 4152829 := bstep (se 3 (by rfl) ⟨778655, by rfl⟩ : syracuseStep 4152829 = 1557311) B1557311
theorem B1457767 : Blo 1457548 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B7380719 : Blo 1457548 7380719 := bstep (se 1 (by rfl) ⟨5535539, by rfl⟩ : syracuseStep 7380719 = 11071079) B11071079
theorem B1458047 : Blo 1457548 1458047 := bstep (se 1 (by rfl) ⟨1093535, by rfl⟩ : syracuseStep 1458047 = 2187071) B2187071
theorem B16605161 : Blo 1457548 16605161 := bstep (se 2 (by rfl) ⟨6226935, by rfl⟩ : syracuseStep 16605161 = 12453871) B12453871
theorem B4153319 : Blo 1457548 4153319 := bstep (se 1 (by rfl) ⟨3114989, by rfl⟩ : syracuseStep 4153319 = 6229979) B6229979
theorem B1458159 : Blo 1457548 1458159 := bstep (se 1 (by rfl) ⟨1093619, by rfl⟩ : syracuseStep 1458159 = 2187239) B2187239
theorem B2187503 : Blo 1457548 2187503 := bstep (se 1 (by rfl) ⟨1640627, by rfl⟩ : syracuseStep 2187503 = 3281255) B3281255
theorem B1458415 : Blo 1457548 1458415 := bstep (se 1 (by rfl) ⟨1093811, by rfl⟩ : syracuseStep 1458415 = 2187623) B2187623
theorem B8422139 : Blo 1457548 8422139 := bstep (se 1 (by rfl) ⟨6316604, by rfl⟩ : syracuseStep 8422139 = 12633209) B12633209
theorem B2188031 : Blo 1457548 2188031 := bstep (se 1 (by rfl) ⟨1641023, by rfl⟩ : syracuseStep 2188031 = 3282047) B3282047
theorem B11232199 : Blo 1457548 11232199 := bstep (se 1 (by rfl) ⟨8424149, by rfl⟩ : syracuseStep 11232199 = 16848299) B16848299
theorem B2663417 : Blo 1457548 2663417 := bstep (se 2 (by rfl) ⟨998781, by rfl⟩ : syracuseStep 2663417 = 1997563) B1997563
theorem B11224097 : Blo 1457548 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B2188415 : Blo 1457548 2188415 := bstep (se 1 (by rfl) ⟨1641311, by rfl⟩ : syracuseStep 2188415 = 3282623) B3282623
theorem B1459455 : Blo 1457548 1459455 := bstep (se 1 (by rfl) ⟨1094591, by rfl⟩ : syracuseStep 1459455 = 2189183) B2189183
theorem B2188571 : Blo 1457548 2188571 := bstep (se 1 (by rfl) ⟨1641428, by rfl⟩ : syracuseStep 2188571 = 3282857) B3282857
theorem B4924799 : Blo 1457548 4924799 := bstep (se 1 (by rfl) ⟨3693599, by rfl⟩ : syracuseStep 4924799 = 7387199) B7387199
theorem B1640263 : Blo 1457548 1640263 := bstep (se 1 (by rfl) ⟨1230197, by rfl⟩ : syracuseStep 1640263 = 2460395) B2460395
theorem B1845119 : Blo 1457548 1845119 := bstep (se 1 (by rfl) ⟨1383839, by rfl⟩ : syracuseStep 1845119 = 2767679) B2767679
theorem B2459855 : Blo 1457548 2459855 := bstep (se 1 (by rfl) ⟨1844891, by rfl⟩ : syracuseStep 2459855 = 3689783) B3689783
theorem B14019065 : Blo 1457548 14019065 := bstep (se 2 (by rfl) ⟨5257149, by rfl⟩ : syracuseStep 14019065 = 10514299) B10514299
theorem B8309303 : Blo 1457548 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B4155961 : Blo 1457548 4155961 := bstep (se 2 (by rfl) ⟨1558485, by rfl⟩ : syracuseStep 4155961 = 3116971) B3116971
theorem B11070107 : Blo 1457548 11070107 := bstep (se 1 (by rfl) ⟨8302580, by rfl⟩ : syracuseStep 11070107 = 16605161) B16605161
theorem B7384121 : Blo 1457548 7384121 := bstep (se 2 (by rfl) ⟨2769045, by rfl⟩ : syracuseStep 7384121 = 5538091) B5538091
theorem B11070593 : Blo 1457548 11070593 := bstep (se 2 (by rfl) ⟨4151472, by rfl⟩ : syracuseStep 11070593 = 8302945) B8302945
theorem B21023873 : Blo 1457548 21023873 := bstep (se 2 (by rfl) ⟨7883952, by rfl⟩ : syracuseStep 21023873 = 15767905) B15767905
theorem B5540993 : Blo 1457548 5540993 := bstep (se 2 (by rfl) ⟨2077872, by rfl⟩ : syracuseStep 5540993 = 4155745) B4155745
theorem B3280283 : Blo 1457548 3280283 := bstep (se 1 (by rfl) ⟨2460212, by rfl⟩ : syracuseStep 3280283 = 4920425) B4920425
theorem B2461151 : Blo 1457548 2461151 := bstep (se 1 (by rfl) ⟨1845863, by rfl⟩ : syracuseStep 2461151 = 3691727) B3691727
theorem B2461367 : Blo 1457548 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B3551369 : Blo 1457548 3551369 := bstep (se 2 (by rfl) ⟨1331763, by rfl⟩ : syracuseStep 3551369 = 2663527) B2663527
theorem B11079827 : Blo 1457548 11079827 := bstep (se 1 (by rfl) ⟨8309870, by rfl⟩ : syracuseStep 11079827 = 16619741) B16619741
theorem B4919723 : Blo 1457548 4919723 := bstep (se 1 (by rfl) ⟨3689792, by rfl⟩ : syracuseStep 4919723 = 7379585) B7379585
theorem B2077417 : Blo 1457548 2077417 := bstep (se 2 (by rfl) ⟨779031, by rfl⟩ : syracuseStep 2077417 = 1558063) B1558063
theorem B18682811 : Blo 1457548 18682811 := bstep (se 1 (by rfl) ⟨14012108, by rfl⟩ : syracuseStep 18682811 = 28024217) B28024217
theorem B4920479 : Blo 1457548 4920479 := bstep (se 1 (by rfl) ⟨3690359, by rfl⟩ : syracuseStep 4920479 = 7380719) B7380719
theorem B9344915 : Blo 1457548 9344915 := bstep (se 1 (by rfl) ⟨7008686, by rfl⟩ : syracuseStep 9344915 = 14017373) B14017373
theorem B5535935 : Blo 1457548 5535935 := bstep (se 1 (by rfl) ⟨4151951, by rfl⟩ : syracuseStep 5535935 = 8303903) B8303903
theorem B39942497 : Blo 1457548 39942497 := bstep (se 2 (by rfl) ⟨14978436, by rfl⟩ : syracuseStep 39942497 = 29956873) B29956873
theorem B4921721 : Blo 1457548 4921721 := bstep (se 2 (by rfl) ⟨1845645, by rfl⟩ : syracuseStep 4921721 = 3691291) B3691291
theorem B4209131 : Blo 1457548 4209131 := bstep (se 1 (by rfl) ⟨3156848, by rfl⟩ : syracuseStep 4209131 = 6313697) B6313697
theorem B83098237 : Blo 1457548 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B26680195 : Blo 1457548 26680195 := bstep (se 1 (by rfl) ⟨20010146, by rfl⟩ : syracuseStep 26680195 = 40020293) B40020293
theorem B12467267 : Blo 1457548 12467267 := bstep (se 1 (by rfl) ⟨9350450, by rfl⟩ : syracuseStep 12467267 = 18700901) B18700901
theorem B2186351 : Blo 1457548 2186351 := bstep (se 1 (by rfl) ⟨1639763, by rfl⟩ : syracuseStep 2186351 = 3279527) B3279527
theorem B5537105 : Blo 1457548 5537105 := bstep (se 2 (by rfl) ⟨2076414, by rfl⟩ : syracuseStep 5537105 = 4152829) B4152829
theorem B2768431 : Blo 1457548 2768431 := bstep (se 1 (by rfl) ⟨2076323, by rfl⟩ : syracuseStep 2768431 = 4152647) B4152647
theorem B1457823 : Blo 1457548 1457823 := bstep (se 1 (by rfl) ⟨1093367, by rfl⟩ : syracuseStep 1457823 = 2186735) B2186735
theorem B3694319 : Blo 1457548 3694319 := bstep (se 1 (by rfl) ⟨2770739, by rfl⟩ : syracuseStep 3694319 = 5541479) B5541479
theorem B18693929 : Blo 1457548 18693929 := bstep (se 2 (by rfl) ⟨7010223, by rfl⟩ : syracuseStep 18693929 = 14020447) B14020447
theorem B2768879 : Blo 1457548 2768879 := bstep (se 1 (by rfl) ⟨2076659, by rfl⟩ : syracuseStep 2768879 = 4153319) B4153319
theorem B1458335 : Blo 1457548 1458335 := bstep (se 1 (by rfl) ⟨1093751, by rfl⟩ : syracuseStep 1458335 = 2187503) B2187503
theorem B1458687 : Blo 1457548 1458687 := bstep (se 1 (by rfl) ⟨1094015, by rfl⟩ : syracuseStep 1458687 = 2188031) B2188031
theorem B1458943 : Blo 1457548 1458943 := bstep (se 1 (by rfl) ⟨1094207, by rfl⟩ : syracuseStep 1458943 = 2188415) B2188415
theorem B110797649 : Blo 1457548 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B1459047 : Blo 1457548 1459047 := bstep (se 1 (by rfl) ⟨1094285, by rfl⟩ : syracuseStep 1459047 = 2188571) B2188571
theorem B106513325 : Blo 1457548 106513325 := bstep (se 3 (by rfl) ⟨19971248, by rfl⟩ : syracuseStep 106513325 = 39942497) B39942497
theorem B2769889 : Blo 1457548 2769889 := bstep (se 2 (by rfl) ⟨1038708, by rfl⟩ : syracuseStep 2769889 = 2077417) B2077417
theorem B14976265 : Blo 1457548 14976265 := bstep (se 2 (by rfl) ⟨5616099, by rfl⟩ : syracuseStep 14976265 = 11232199) B11232199
theorem B37881269 : Blo 1457548 37881269 := bstep (se 5 (by rfl) ⟨1775684, by rfl⟩ : syracuseStep 37881269 = 3551369) B3551369
theorem B1639903 : Blo 1457548 1639903 := bstep (se 1 (by rfl) ⟨1229927, by rfl⟩ : syracuseStep 1639903 = 2459855) B2459855
theorem B5539535 : Blo 1457548 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B1640767 : Blo 1457548 1640767 := bstep (se 1 (by rfl) ⟨1230575, by rfl⟩ : syracuseStep 1640767 = 2461151) B2461151
theorem B1640911 : Blo 1457548 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B12462619 : Blo 1457548 12462619 := bstep (se 1 (by rfl) ⟨9346964, by rfl⟩ : syracuseStep 12462619 = 18693929) B18693929
theorem B1845919 : Blo 1457548 1845919 := bstep (se 1 (by rfl) ⟨1384439, by rfl⟩ : syracuseStep 1845919 = 2768879) B2768879
theorem B3279815 : Blo 1457548 3279815 := bstep (se 1 (by rfl) ⟨2459861, by rfl⟩ : syracuseStep 3279815 = 4919723) B4919723
theorem B5614759 : Blo 1457548 5614759 := bstep (se 1 (by rfl) ⟨4211069, by rfl⟩ : syracuseStep 5614759 = 8422139) B8422139
theorem B12455207 : Blo 1457548 12455207 := bstep (se 1 (by rfl) ⟨9341405, by rfl⟩ : syracuseStep 12455207 = 18682811) B18682811
theorem B7482731 : Blo 1457548 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B5541281 : Blo 1457548 5541281 := bstep (se 2 (by rfl) ⟨2077980, by rfl⟩ : syracuseStep 5541281 = 4155961) B4155961
theorem B3280319 : Blo 1457548 3280319 := bstep (se 1 (by rfl) ⟨2460239, by rfl⟩ : syracuseStep 3280319 = 4920479) B4920479
theorem B35573593 : Blo 1457548 35573593 := bstep (se 2 (by rfl) ⟨13340097, by rfl⟩ : syracuseStep 35573593 = 26680195) B26680195
theorem B6229943 : Blo 1457548 6229943 := bstep (se 1 (by rfl) ⟨4672457, by rfl⟩ : syracuseStep 6229943 = 9344915) B9344915
theorem B3690623 : Blo 1457548 3690623 := bstep (se 1 (by rfl) ⟨2767967, by rfl⟩ : syracuseStep 3690623 = 5535935) B5535935
theorem B3281147 : Blo 1457548 3281147 := bstep (se 1 (by rfl) ⟨2460860, by rfl⟩ : syracuseStep 3281147 = 4921721) B4921721
theorem B2806087 : Blo 1457548 2806087 := bstep (se 1 (by rfl) ⟨2104565, by rfl⟩ : syracuseStep 2806087 = 4209131) B4209131
theorem B8311511 : Blo 1457548 8311511 := bstep (se 1 (by rfl) ⟨6233633, by rfl⟩ : syracuseStep 8311511 = 12467267) B12467267
theorem B3691241 : Blo 1457548 3691241 := bstep (se 2 (by rfl) ⟨1384215, by rfl⟩ : syracuseStep 3691241 = 2768431) B2768431
theorem B3691403 : Blo 1457548 3691403 := bstep (se 1 (by rfl) ⟨2768552, by rfl⟩ : syracuseStep 3691403 = 5537105) B5537105
theorem B4920317 : Blo 1457548 4920317 := bstep (se 3 (by rfl) ⟨922559, by rfl⟩ : syracuseStep 4920317 = 1845119) B1845119
theorem B2462879 : Blo 1457548 2462879 := bstep (se 1 (by rfl) ⟨1847159, by rfl⟩ : syracuseStep 2462879 = 3694319) B3694319
theorem B7386551 : Blo 1457548 7386551 := bstep (se 1 (by rfl) ⟨5539913, by rfl⟩ : syracuseStep 7386551 = 11079827) B11079827
theorem B1775611 : Blo 1457548 1775611 := bstep (se 1 (by rfl) ⟨1331708, by rfl⟩ : syracuseStep 1775611 = 2663417) B2663417
theorem B3283199 : Blo 1457548 3283199 := bstep (se 1 (by rfl) ⟨2462399, by rfl⟩ : syracuseStep 3283199 = 4924799) B4924799
theorem B9346043 : Blo 1457548 9346043 := bstep (se 1 (by rfl) ⟨7009532, by rfl⟩ : syracuseStep 9346043 = 14019065) B14019065
theorem B7380071 : Blo 1457548 7380071 := bstep (se 1 (by rfl) ⟨5535053, by rfl⟩ : syracuseStep 7380071 = 11070107) B11070107
theorem B4922747 : Blo 1457548 4922747 := bstep (se 1 (by rfl) ⟨3692060, by rfl⟩ : syracuseStep 4922747 = 7384121) B7384121
theorem B1457567 : Blo 1457548 1457567 := bstep (se 1 (by rfl) ⟨1093175, by rfl⟩ : syracuseStep 1457567 = 2186351) B2186351
theorem B14015915 : Blo 1457548 14015915 := bstep (se 1 (by rfl) ⟨10511936, by rfl⟩ : syracuseStep 14015915 = 21023873) B21023873
theorem B7380395 : Blo 1457548 7380395 := bstep (se 1 (by rfl) ⟨5535296, by rfl⟩ : syracuseStep 7380395 = 11070593) B11070593
theorem B3693995 : Blo 1457548 3693995 := bstep (se 1 (by rfl) ⟨2770496, by rfl⟩ : syracuseStep 3693995 = 5540993) B5540993
theorem B2186855 : Blo 1457548 2186855 := bstep (se 1 (by rfl) ⟨1640141, by rfl⟩ : syracuseStep 2186855 = 3280283) B3280283
theorem B2187017 : Blo 1457548 2187017 := bstep (se 2 (by rfl) ⟨820131, by rfl⟩ : syracuseStep 2187017 = 1640263) B1640263
theorem B2187431 : Blo 1457548 2187431 := bstep (se 1 (by rfl) ⟨1640573, by rfl⟩ : syracuseStep 2187431 = 3281147) B3281147
theorem B2187689 : Blo 1457548 2187689 := bstep (se 2 (by rfl) ⟨820383, by rfl⟩ : syracuseStep 2187689 = 1640767) B1640767
theorem B2187881 : Blo 1457548 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B71008883 : Blo 1457548 71008883 := bstep (se 1 (by rfl) ⟨53256662, by rfl⟩ : syracuseStep 71008883 = 106513325) B106513325
theorem B4924367 : Blo 1457548 4924367 := bstep (se 1 (by rfl) ⟨3693275, by rfl⟩ : syracuseStep 4924367 = 7386551) B7386551
theorem B2188799 : Blo 1457548 2188799 := bstep (se 1 (by rfl) ⟨1641599, by rfl⟩ : syracuseStep 2188799 = 3283199) B3283199
theorem B2460415 : Blo 1457548 2460415 := bstep (se 1 (by rfl) ⟨1845311, by rfl⟩ : syracuseStep 2460415 = 3690623) B3690623
theorem B5541007 : Blo 1457548 5541007 := bstep (se 1 (by rfl) ⟨4155755, by rfl⟩ : syracuseStep 5541007 = 8311511) B8311511
theorem B2460827 : Blo 1457548 2460827 := bstep (se 1 (by rfl) ⟨1845620, by rfl⟩ : syracuseStep 2460827 = 3691241) B3691241
theorem B2460935 : Blo 1457548 2460935 := bstep (se 1 (by rfl) ⟨1845701, by rfl⟩ : syracuseStep 2460935 = 3691403) B3691403
theorem B3280211 : Blo 1457548 3280211 := bstep (se 1 (by rfl) ⟨2460158, by rfl⟩ : syracuseStep 3280211 = 4920317) B4920317
theorem B16616825 : Blo 1457548 16616825 := bstep (se 2 (by rfl) ⟨6231309, by rfl⟩ : syracuseStep 16616825 = 12462619) B12462619
theorem B1641919 : Blo 1457548 1641919 := bstep (se 1 (by rfl) ⟨1231439, by rfl⟩ : syracuseStep 1641919 = 2462879) B2462879
theorem B2461225 : Blo 1457548 2461225 := bstep (se 2 (by rfl) ⟨922959, by rfl⟩ : syracuseStep 2461225 = 1845919) B1845919
theorem B19968353 : Blo 1457548 19968353 := bstep (se 2 (by rfl) ⟨7488132, by rfl⟩ : syracuseStep 19968353 = 14976265) B14976265
theorem B6230695 : Blo 1457548 6230695 := bstep (se 1 (by rfl) ⟨4673021, by rfl⟩ : syracuseStep 6230695 = 9346043) B9346043
theorem B4920047 : Blo 1457548 4920047 := bstep (se 1 (by rfl) ⟨3690035, by rfl⟩ : syracuseStep 4920047 = 7380071) B7380071
theorem B8303471 : Blo 1457548 8303471 := bstep (se 1 (by rfl) ⟨6227603, by rfl⟩ : syracuseStep 8303471 = 12455207) B12455207
theorem B3281831 : Blo 1457548 3281831 := bstep (se 1 (by rfl) ⟨2461373, by rfl⟩ : syracuseStep 3281831 = 4922747) B4922747
theorem B4920263 : Blo 1457548 4920263 := bstep (se 1 (by rfl) ⟨3690197, by rfl⟩ : syracuseStep 4920263 = 7380395) B7380395
theorem B9343943 : Blo 1457548 9343943 := bstep (se 1 (by rfl) ⟨7007957, by rfl⟩ : syracuseStep 9343943 = 14015915) B14015915
theorem B2462663 : Blo 1457548 2462663 := bstep (se 1 (by rfl) ⟨1846997, by rfl⟩ : syracuseStep 2462663 = 3693995) B3693995
theorem B3741449 : Blo 1457548 3741449 := bstep (se 2 (by rfl) ⟨1403043, by rfl⟩ : syracuseStep 3741449 = 2806087) B2806087
theorem B73865099 : Blo 1457548 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B19953949 : Blo 1457548 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B25254179 : Blo 1457548 25254179 := bstep (se 1 (by rfl) ⟨18940634, by rfl⟩ : syracuseStep 25254179 = 37881269) B37881269
theorem B3693023 : Blo 1457548 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B3693185 : Blo 1457548 3693185 := bstep (se 2 (by rfl) ⟨1384944, by rfl⟩ : syracuseStep 3693185 = 2769889) B2769889
theorem B7486345 : Blo 1457548 7486345 := bstep (se 2 (by rfl) ⟨2807379, by rfl⟩ : syracuseStep 7486345 = 5614759) B5614759
theorem B2186537 : Blo 1457548 2186537 := bstep (se 2 (by rfl) ⟨819951, by rfl⟩ : syracuseStep 2186537 = 1639903) B1639903
theorem B2186543 : Blo 1457548 2186543 := bstep (se 1 (by rfl) ⟨1639907, by rfl⟩ : syracuseStep 2186543 = 3279815) B3279815
theorem B3694187 : Blo 1457548 3694187 := bstep (se 1 (by rfl) ⟨2770640, by rfl⟩ : syracuseStep 3694187 = 5541281) B5541281
theorem B2186879 : Blo 1457548 2186879 := bstep (se 1 (by rfl) ⟨1640159, by rfl⟩ : syracuseStep 2186879 = 3280319) B3280319
theorem B1457903 : Blo 1457548 1457903 := bstep (se 1 (by rfl) ⟨1093427, by rfl⟩ : syracuseStep 1457903 = 2186855) B2186855
theorem B47431457 : Blo 1457548 47431457 := bstep (se 2 (by rfl) ⟨17786796, by rfl⟩ : syracuseStep 47431457 = 35573593) B35573593
theorem B1458011 : Blo 1457548 1458011 := bstep (se 1 (by rfl) ⟨1093508, by rfl⟩ : syracuseStep 1458011 = 2187017) B2187017
theorem B4153295 : Blo 1457548 4153295 := bstep (se 1 (by rfl) ⟨3114971, by rfl⟩ : syracuseStep 4153295 = 6229943) B6229943
theorem B2367481 : Blo 1457548 2367481 := bstep (se 2 (by rfl) ⟨887805, by rfl⟩ : syracuseStep 2367481 = 1775611) B1775611
theorem B1458287 : Blo 1457548 1458287 := bstep (se 1 (by rfl) ⟨1093715, by rfl⟩ : syracuseStep 1458287 = 2187431) B2187431
theorem B13312235 : Blo 1457548 13312235 := bstep (se 1 (by rfl) ⟨9984176, by rfl⟩ : syracuseStep 13312235 = 19968353) B19968353
theorem B1458459 : Blo 1457548 1458459 := bstep (se 1 (by rfl) ⟨1093844, by rfl⟩ : syracuseStep 1458459 = 2187689) B2187689
theorem B1458587 : Blo 1457548 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B2187887 : Blo 1457548 2187887 := bstep (se 1 (by rfl) ⟨1640915, by rfl⟩ : syracuseStep 2187887 = 3281831) B3281831
theorem B8307593 : Blo 1457548 8307593 := bstep (se 2 (by rfl) ⟨3115347, by rfl⟩ : syracuseStep 8307593 = 6230695) B6230695
theorem B1459199 : Blo 1457548 1459199 := bstep (se 1 (by rfl) ⟨1094399, by rfl⟩ : syracuseStep 1459199 = 2188799) B2188799
theorem B49243399 : Blo 1457548 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B16836119 : Blo 1457548 16836119 := bstep (se 1 (by rfl) ⟨12627089, by rfl⟩ : syracuseStep 16836119 = 25254179) B25254179
theorem B2189225 : Blo 1457548 2189225 := bstep (se 2 (by rfl) ⟨820959, by rfl⟩ : syracuseStep 2189225 = 1641919) B1641919
theorem B1640551 : Blo 1457548 1640551 := bstep (se 1 (by rfl) ⟨1230413, by rfl⟩ : syracuseStep 1640551 = 2460827) B2460827
theorem B1640623 : Blo 1457548 1640623 := bstep (se 1 (by rfl) ⟨1230467, by rfl⟩ : syracuseStep 1640623 = 2460935) B2460935
theorem B11077883 : Blo 1457548 11077883 := bstep (se 1 (by rfl) ⟨8308412, by rfl⟩ : syracuseStep 11077883 = 16616825) B16616825
theorem B3156641 : Blo 1457548 3156641 := bstep (se 2 (by rfl) ⟨1183740, by rfl⟩ : syracuseStep 3156641 = 2367481) B2367481
theorem B3280031 : Blo 1457548 3280031 := bstep (se 1 (by rfl) ⟨2460023, by rfl⟩ : syracuseStep 3280031 = 4920047) B4920047
theorem B3280175 : Blo 1457548 3280175 := bstep (se 1 (by rfl) ⟨2460131, by rfl⟩ : syracuseStep 3280175 = 4920263) B4920263
theorem B6229295 : Blo 1457548 6229295 := bstep (se 1 (by rfl) ⟨4671971, by rfl⟩ : syracuseStep 6229295 = 9343943) B9343943
theorem B1641775 : Blo 1457548 1641775 := bstep (se 1 (by rfl) ⟨1231331, by rfl⟩ : syracuseStep 1641775 = 2462663) B2462663
theorem B3280553 : Blo 1457548 3280553 := bstep (se 2 (by rfl) ⟨1230207, by rfl⟩ : syracuseStep 3280553 = 2460415) B2460415
theorem B9981793 : Blo 1457548 9981793 := bstep (se 2 (by rfl) ⟨3743172, by rfl⟩ : syracuseStep 9981793 = 7486345) B7486345
theorem B2462015 : Blo 1457548 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B2462123 : Blo 1457548 2462123 := bstep (se 1 (by rfl) ⟨1846592, by rfl⟩ : syracuseStep 2462123 = 3693185) B3693185
theorem B3281633 : Blo 1457548 3281633 := bstep (se 2 (by rfl) ⟨1230612, by rfl⟩ : syracuseStep 3281633 = 2461225) B2461225
theorem B2462791 : Blo 1457548 2462791 := bstep (se 1 (by rfl) ⟨1847093, by rfl⟩ : syracuseStep 2462791 = 3694187) B3694187
theorem B26605265 : Blo 1457548 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B47339255 : Blo 1457548 47339255 := bstep (se 1 (by rfl) ⟨35504441, by rfl⟩ : syracuseStep 47339255 = 71008883) B71008883
theorem B5535647 : Blo 1457548 5535647 := bstep (se 1 (by rfl) ⟨4151735, by rfl⟩ : syracuseStep 5535647 = 8303471) B8303471
theorem B3282911 : Blo 1457548 3282911 := bstep (se 1 (by rfl) ⟨2462183, by rfl⟩ : syracuseStep 3282911 = 4924367) B4924367
theorem B7388009 : Blo 1457548 7388009 := bstep (se 2 (by rfl) ⟨2770503, by rfl⟩ : syracuseStep 7388009 = 5541007) B5541007
theorem B9977197 : Blo 1457548 9977197 := bstep (se 3 (by rfl) ⟨1870724, by rfl⟩ : syracuseStep 9977197 = 3741449) B3741449
theorem B1457691 : Blo 1457548 1457691 := bstep (se 1 (by rfl) ⟨1093268, by rfl⟩ : syracuseStep 1457691 = 2186537) B2186537
theorem B1457695 : Blo 1457548 1457695 := bstep (se 1 (by rfl) ⟨1093271, by rfl⟩ : syracuseStep 1457695 = 2186543) B2186543
theorem B2186807 : Blo 1457548 2186807 := bstep (se 1 (by rfl) ⟨1640105, by rfl⟩ : syracuseStep 2186807 = 3280211) B3280211
theorem B1457919 : Blo 1457548 1457919 := bstep (se 1 (by rfl) ⟨1093439, by rfl⟩ : syracuseStep 1457919 = 2186879) B2186879
theorem B31620971 : Blo 1457548 31620971 := bstep (se 1 (by rfl) ⟨23715728, by rfl⟩ : syracuseStep 31620971 = 47431457) B47431457
theorem B11075453 : Blo 1457548 11075453 := bstep (se 3 (by rfl) ⟨2076647, by rfl⟩ : syracuseStep 11075453 = 4153295) B4153295
theorem B2187401 : Blo 1457548 2187401 := bstep (se 2 (by rfl) ⟨820275, by rfl⟩ : syracuseStep 2187401 = 1640551) B1640551
theorem B1050525845 : Blo 1457548 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B2187497 : Blo 1457548 2187497 := bstep (se 2 (by rfl) ⟨820311, by rfl⟩ : syracuseStep 2187497 = 1640623) B1640623
theorem B1458591 : Blo 1457548 1458591 := bstep (se 1 (by rfl) ⟨1093943, by rfl⟩ : syracuseStep 1458591 = 2187887) B2187887
theorem B2187755 : Blo 1457548 2187755 := bstep (se 1 (by rfl) ⟨1640816, by rfl⟩ : syracuseStep 2187755 = 3281633) B3281633
theorem B5538395 : Blo 1457548 5538395 := bstep (se 1 (by rfl) ⟨4153796, by rfl⟩ : syracuseStep 5538395 = 8307593) B8307593
theorem B11224079 : Blo 1457548 11224079 := bstep (se 1 (by rfl) ⟨8418059, by rfl⟩ : syracuseStep 11224079 = 16836119) B16836119
theorem B1459483 : Blo 1457548 1459483 := bstep (se 1 (by rfl) ⟨1094612, by rfl⟩ : syracuseStep 1459483 = 2189225) B2189225
theorem B2188607 : Blo 1457548 2188607 := bstep (se 1 (by rfl) ⟨1641455, by rfl⟩ : syracuseStep 2188607 = 3282911) B3282911
theorem B2189033 : Blo 1457548 2189033 := bstep (se 2 (by rfl) ⟨820887, by rfl⟩ : syracuseStep 2189033 = 1641775) B1641775
theorem B4925339 : Blo 1457548 4925339 := bstep (se 1 (by rfl) ⟨3694004, by rfl⟩ : syracuseStep 4925339 = 7388009) B7388009
theorem B283789493 : Blo 1457548 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B21080647 : Blo 1457548 21080647 := bstep (se 1 (by rfl) ⟨15810485, by rfl⟩ : syracuseStep 21080647 = 31620971) B31620971
theorem B7383635 : Blo 1457548 7383635 := bstep (se 1 (by rfl) ⟨5537726, by rfl⟩ : syracuseStep 7383635 = 11075453) B11075453
theorem B1641343 : Blo 1457548 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B1641415 : Blo 1457548 1641415 := bstep (se 1 (by rfl) ⟨1231061, by rfl⟩ : syracuseStep 1641415 = 2462123) B2462123
theorem B35499293 : Blo 1457548 35499293 := bstep (se 3 (by rfl) ⟨6656117, by rfl⟩ : syracuseStep 35499293 = 13312235) B13312235
theorem B31559503 : Blo 1457548 31559503 := bstep (se 1 (by rfl) ⟨23669627, by rfl⟩ : syracuseStep 31559503 = 47339255) B47339255
theorem B3690431 : Blo 1457548 3690431 := bstep (se 1 (by rfl) ⟨2767823, by rfl⟩ : syracuseStep 3690431 = 5535647) B5535647
theorem B7385255 : Blo 1457548 7385255 := bstep (se 1 (by rfl) ⟨5538941, by rfl⟩ : syracuseStep 7385255 = 11077883) B11077883
theorem B13309057 : Blo 1457548 13309057 := bstep (se 2 (by rfl) ⟨4990896, by rfl⟩ : syracuseStep 13309057 = 9981793) B9981793
theorem B3283721 : Blo 1457548 3283721 := bstep (se 2 (by rfl) ⟨1231395, by rfl⟩ : syracuseStep 3283721 = 2462791) B2462791
theorem B2104427 : Blo 1457548 2104427 := bstep (se 1 (by rfl) ⟨1578320, by rfl⟩ : syracuseStep 2104427 = 3156641) B3156641
theorem B13302929 : Blo 1457548 13302929 := bstep (se 2 (by rfl) ⟨4988598, by rfl⟩ : syracuseStep 13302929 = 9977197) B9977197
theorem B2186687 : Blo 1457548 2186687 := bstep (se 1 (by rfl) ⟨1640015, by rfl⟩ : syracuseStep 2186687 = 3280031) B3280031
theorem B2186783 : Blo 1457548 2186783 := bstep (se 1 (by rfl) ⟨1640087, by rfl⟩ : syracuseStep 2186783 = 3280175) B3280175
theorem B4152863 : Blo 1457548 4152863 := bstep (se 1 (by rfl) ⟨3114647, by rfl⟩ : syracuseStep 4152863 = 6229295) B6229295
theorem B1457871 : Blo 1457548 1457871 := bstep (se 1 (by rfl) ⟨1093403, by rfl⟩ : syracuseStep 1457871 = 2186807) B2186807
theorem B2187035 : Blo 1457548 2187035 := bstep (se 1 (by rfl) ⟨1640276, by rfl⟩ : syracuseStep 2187035 = 3280553) B3280553
theorem B1458267 : Blo 1457548 1458267 := bstep (se 1 (by rfl) ⟨1093700, by rfl⟩ : syracuseStep 1458267 = 2187401) B2187401
theorem B700350563 : Blo 1457548 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B4923503 : Blo 1457548 4923503 := bstep (se 1 (by rfl) ⟨3692627, by rfl⟩ : syracuseStep 4923503 = 7385255) B7385255
theorem B1458331 : Blo 1457548 1458331 := bstep (se 1 (by rfl) ⟨1093748, by rfl⟩ : syracuseStep 1458331 = 2187497) B2187497
theorem B5611805 : Blo 1457548 5611805 := bstep (se 3 (by rfl) ⟨1052213, by rfl⟩ : syracuseStep 5611805 = 2104427) B2104427
theorem B1458503 : Blo 1457548 1458503 := bstep (se 1 (by rfl) ⟨1093877, by rfl⟩ : syracuseStep 1458503 = 2187755) B2187755
theorem B28107529 : Blo 1457548 28107529 := bstep (se 2 (by rfl) ⟨10540323, by rfl⟩ : syracuseStep 28107529 = 21080647) B21080647
theorem B1459071 : Blo 1457548 1459071 := bstep (se 1 (by rfl) ⟨1094303, by rfl⟩ : syracuseStep 1459071 = 2188607) B2188607
theorem B1459355 : Blo 1457548 1459355 := bstep (se 1 (by rfl) ⟨1094516, by rfl⟩ : syracuseStep 1459355 = 2189033) B2189033
theorem B2188457 : Blo 1457548 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B2188553 : Blo 1457548 2188553 := bstep (se 2 (by rfl) ⟨820707, by rfl⟩ : syracuseStep 2188553 = 1641415) B1641415
theorem B17745409 : Blo 1457548 17745409 := bstep (se 2 (by rfl) ⟨6654528, by rfl⟩ : syracuseStep 17745409 = 13309057) B13309057
theorem B2189147 : Blo 1457548 2189147 := bstep (se 1 (by rfl) ⟨1641860, by rfl⟩ : syracuseStep 2189147 = 3283721) B3283721
theorem B2460287 : Blo 1457548 2460287 := bstep (se 1 (by rfl) ⟨1845215, by rfl⟩ : syracuseStep 2460287 = 3690431) B3690431
theorem B7482719 : Blo 1457548 7482719 := bstep (se 1 (by rfl) ⟨5612039, by rfl⟩ : syracuseStep 7482719 = 11224079) B11224079
theorem B8868619 : Blo 1457548 8868619 := bstep (se 1 (by rfl) ⟨6651464, by rfl⟩ : syracuseStep 8868619 = 13302929) B13302929
theorem B42079337 : Blo 1457548 42079337 := bstep (se 2 (by rfl) ⟨15779751, by rfl⟩ : syracuseStep 42079337 = 31559503) B31559503
theorem B3692263 : Blo 1457548 3692263 := bstep (se 1 (by rfl) ⟨2769197, by rfl⟩ : syracuseStep 3692263 = 5538395) B5538395
theorem B3283559 : Blo 1457548 3283559 := bstep (se 1 (by rfl) ⟨2462669, by rfl⟩ : syracuseStep 3283559 = 4925339) B4925339
theorem B189192995 : Blo 1457548 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B4922423 : Blo 1457548 4922423 := bstep (se 1 (by rfl) ⟨3691817, by rfl⟩ : syracuseStep 4922423 = 7383635) B7383635
theorem B23666195 : Blo 1457548 23666195 := bstep (se 1 (by rfl) ⟨17749646, by rfl⟩ : syracuseStep 23666195 = 35499293) B35499293
theorem B1457791 : Blo 1457548 1457791 := bstep (se 1 (by rfl) ⟨1093343, by rfl⟩ : syracuseStep 1457791 = 2186687) B2186687
theorem B1457855 : Blo 1457548 1457855 := bstep (se 1 (by rfl) ⟨1093391, by rfl⟩ : syracuseStep 1457855 = 2186783) B2186783
theorem B2768575 : Blo 1457548 2768575 := bstep (se 1 (by rfl) ⟨2076431, by rfl⟩ : syracuseStep 2768575 = 4152863) B4152863
theorem B1458023 : Blo 1457548 1458023 := bstep (se 1 (by rfl) ⟨1093517, by rfl⟩ : syracuseStep 1458023 = 2187035) B2187035
theorem B1458971 : Blo 1457548 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B1459035 : Blo 1457548 1459035 := bstep (se 1 (by rfl) ⟨1094276, by rfl⟩ : syracuseStep 1459035 = 2188553) B2188553
theorem B1459431 : Blo 1457548 1459431 := bstep (se 1 (by rfl) ⟨1094573, by rfl⟩ : syracuseStep 1459431 = 2189147) B2189147
theorem B149906821 : Blo 1457548 149906821 := bstep (se 4 (by rfl) ⟨14053764, by rfl⟩ : syracuseStep 149906821 = 28107529) B28107529
theorem B2189039 : Blo 1457548 2189039 := bstep (se 1 (by rfl) ⟨1641779, by rfl⟩ : syracuseStep 2189039 = 3283559) B3283559
theorem B1640191 : Blo 1457548 1640191 := bstep (se 1 (by rfl) ⟨1230143, by rfl⟩ : syracuseStep 1640191 = 2460287) B2460287
theorem B23660545 : Blo 1457548 23660545 := bstep (se 2 (by rfl) ⟨8872704, by rfl⟩ : syracuseStep 23660545 = 17745409) B17745409
theorem B28052891 : Blo 1457548 28052891 := bstep (se 1 (by rfl) ⟨21039668, by rfl⟩ : syracuseStep 28052891 = 42079337) B42079337
theorem B11824825 : Blo 1457548 11824825 := bstep (se 2 (by rfl) ⟨4434309, by rfl⟩ : syracuseStep 11824825 = 8868619) B8868619
theorem B126128663 : Blo 1457548 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B3281615 : Blo 1457548 3281615 := bstep (se 1 (by rfl) ⟨2461211, by rfl⟩ : syracuseStep 3281615 = 4922423) B4922423
theorem B3691433 : Blo 1457548 3691433 := bstep (se 2 (by rfl) ⟨1384287, by rfl⟩ : syracuseStep 3691433 = 2768575) B2768575
theorem B466900375 : Blo 1457548 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B3282335 : Blo 1457548 3282335 := bstep (se 1 (by rfl) ⟨2461751, by rfl⟩ : syracuseStep 3282335 = 4923503) B4923503
theorem B3741203 : Blo 1457548 3741203 := bstep (se 1 (by rfl) ⟨2805902, by rfl⟩ : syracuseStep 3741203 = 5611805) B5611805
theorem B4988479 : Blo 1457548 4988479 := bstep (se 1 (by rfl) ⟨3741359, by rfl⟩ : syracuseStep 4988479 = 7482719) B7482719
theorem B4923017 : Blo 1457548 4923017 := bstep (se 2 (by rfl) ⟨1846131, by rfl⟩ : syracuseStep 4923017 = 3692263) B3692263
theorem B15777463 : Blo 1457548 15777463 := bstep (se 1 (by rfl) ⟨11833097, by rfl⟩ : syracuseStep 15777463 = 23666195) B23666195
theorem B31547393 : Blo 1457548 31547393 := bstep (se 2 (by rfl) ⟨11830272, by rfl⟩ : syracuseStep 31547393 = 23660545) B23660545
theorem B2187743 : Blo 1457548 2187743 := bstep (se 1 (by rfl) ⟨1640807, by rfl⟩ : syracuseStep 2187743 = 3281615) B3281615
theorem B2188223 : Blo 1457548 2188223 := bstep (se 1 (by rfl) ⟨1641167, by rfl⟩ : syracuseStep 2188223 = 3282335) B3282335
theorem B1459359 : Blo 1457548 1459359 := bstep (se 1 (by rfl) ⟨1094519, by rfl⟩ : syracuseStep 1459359 = 2189039) B2189039
theorem B84085775 : Blo 1457548 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B2460955 : Blo 1457548 2460955 := bstep (se 1 (by rfl) ⟨1845716, by rfl⟩ : syracuseStep 2460955 = 3691433) B3691433
theorem B2494135 : Blo 1457548 2494135 := bstep (se 1 (by rfl) ⟨1870601, by rfl⟩ : syracuseStep 2494135 = 3741203) B3741203
theorem B15766433 : Blo 1457548 15766433 := bstep (se 2 (by rfl) ⟨5912412, by rfl⟩ : syracuseStep 15766433 = 11824825) B11824825
theorem B3282011 : Blo 1457548 3282011 := bstep (se 1 (by rfl) ⟨2461508, by rfl⟩ : syracuseStep 3282011 = 4923017) B4923017
theorem B199875761 : Blo 1457548 199875761 := bstep (se 2 (by rfl) ⟨74953410, by rfl⟩ : syracuseStep 199875761 = 149906821) B149906821
theorem B622533833 : Blo 1457548 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B6651305 : Blo 1457548 6651305 := bstep (se 2 (by rfl) ⟨2494239, by rfl⟩ : syracuseStep 6651305 = 4988479) B4988479
theorem B21036617 : Blo 1457548 21036617 := bstep (se 2 (by rfl) ⟨7888731, by rfl⟩ : syracuseStep 21036617 = 15777463) B15777463
theorem B18701927 : Blo 1457548 18701927 := bstep (se 1 (by rfl) ⟨14026445, by rfl⟩ : syracuseStep 18701927 = 28052891) B28052891
theorem B2186921 : Blo 1457548 2186921 := bstep (se 2 (by rfl) ⟨820095, by rfl⟩ : syracuseStep 2186921 = 1640191) B1640191
theorem B1458495 : Blo 1457548 1458495 := bstep (se 1 (by rfl) ⟨1093871, by rfl⟩ : syracuseStep 1458495 = 2187743) B2187743
theorem B10510955 : Blo 1457548 10510955 := bstep (se 1 (by rfl) ⟨7883216, by rfl⟩ : syracuseStep 10510955 = 15766433) B15766433
theorem B1458815 : Blo 1457548 1458815 := bstep (se 1 (by rfl) ⟨1094111, by rfl⟩ : syracuseStep 1458815 = 2188223) B2188223
theorem B2188007 : Blo 1457548 2188007 := bstep (se 1 (by rfl) ⟨1641005, by rfl⟩ : syracuseStep 2188007 = 3282011) B3282011
theorem B4434203 : Blo 1457548 4434203 := bstep (se 1 (by rfl) ⟨3325652, by rfl⟩ : syracuseStep 4434203 = 6651305) B6651305
theorem B21031595 : Blo 1457548 21031595 := bstep (se 1 (by rfl) ⟨15773696, by rfl⟩ : syracuseStep 21031595 = 31547393) B31547393
theorem B3281273 : Blo 1457548 3281273 := bstep (se 2 (by rfl) ⟨1230477, by rfl⟩ : syracuseStep 3281273 = 2460955) B2460955
theorem B13302053 : Blo 1457548 13302053 := bstep (se 4 (by rfl) ⟨1247067, by rfl⟩ : syracuseStep 13302053 = 2494135) B2494135
theorem B56057183 : Blo 1457548 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B133250507 : Blo 1457548 133250507 := bstep (se 1 (by rfl) ⟨99937880, by rfl⟩ : syracuseStep 133250507 = 199875761) B199875761
theorem B415022555 : Blo 1457548 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B14024411 : Blo 1457548 14024411 := bstep (se 1 (by rfl) ⟨10518308, by rfl⟩ : syracuseStep 14024411 = 21036617) B21036617
theorem B12467951 : Blo 1457548 12467951 := bstep (se 1 (by rfl) ⟨9350963, by rfl⟩ : syracuseStep 12467951 = 18701927) B18701927
theorem B1457947 : Blo 1457548 1457947 := bstep (se 1 (by rfl) ⟨1093460, by rfl⟩ : syracuseStep 1457947 = 2186921) B2186921
theorem B2187515 : Blo 1457548 2187515 := bstep (se 1 (by rfl) ⟨1640636, by rfl⟩ : syracuseStep 2187515 = 3281273) B3281273
theorem B1458671 : Blo 1457548 1458671 := bstep (se 1 (by rfl) ⟨1094003, by rfl⟩ : syracuseStep 1458671 = 2188007) B2188007
theorem B9349607 : Blo 1457548 9349607 := bstep (se 1 (by rfl) ⟨7012205, by rfl⟩ : syracuseStep 9349607 = 14024411) B14024411
theorem B7007303 : Blo 1457548 7007303 := bstep (se 1 (by rfl) ⟨5255477, by rfl⟩ : syracuseStep 7007303 = 10510955) B10510955
theorem B11824541 : Blo 1457548 11824541 := bstep (se 3 (by rfl) ⟨2217101, by rfl⟩ : syracuseStep 11824541 = 4434203) B4434203
theorem B8868035 : Blo 1457548 8868035 := bstep (se 1 (by rfl) ⟨6651026, by rfl⟩ : syracuseStep 8868035 = 13302053) B13302053
theorem B14021063 : Blo 1457548 14021063 := bstep (se 1 (by rfl) ⟨10515797, by rfl⟩ : syracuseStep 14021063 = 21031595) B21031595
theorem B276681703 : Blo 1457548 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B8311967 : Blo 1457548 8311967 := bstep (se 1 (by rfl) ⟨6233975, by rfl⟩ : syracuseStep 8311967 = 12467951) B12467951
theorem B37371455 : Blo 1457548 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B88833671 : Blo 1457548 88833671 := bstep (se 1 (by rfl) ⟨66625253, by rfl⟩ : syracuseStep 88833671 = 133250507) B133250507
theorem B1458343 : Blo 1457548 1458343 := bstep (se 1 (by rfl) ⟨1093757, by rfl⟩ : syracuseStep 1458343 = 2187515) B2187515
theorem B9347375 : Blo 1457548 9347375 := bstep (se 1 (by rfl) ⟨7010531, by rfl⟩ : syracuseStep 9347375 = 14021063) B14021063
theorem B4671535 : Blo 1457548 4671535 := bstep (se 1 (by rfl) ⟨3503651, by rfl⟩ : syracuseStep 4671535 = 7007303) B7007303
theorem B7883027 : Blo 1457548 7883027 := bstep (se 1 (by rfl) ⟨5912270, by rfl⟩ : syracuseStep 7883027 = 11824541) B11824541
theorem B24914303 : Blo 1457548 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B59222447 : Blo 1457548 59222447 := bstep (se 1 (by rfl) ⟨44416835, by rfl⟩ : syracuseStep 59222447 = 88833671) B88833671
theorem B5541311 : Blo 1457548 5541311 := bstep (se 1 (by rfl) ⟨4155983, by rfl⟩ : syracuseStep 5541311 = 8311967) B8311967
theorem B5912023 : Blo 1457548 5912023 := bstep (se 1 (by rfl) ⟨4434017, by rfl⟩ : syracuseStep 5912023 = 8868035) B8868035
theorem B368908937 : Blo 1457548 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B6233071 : Blo 1457548 6233071 := bstep (se 1 (by rfl) ⟨4674803, by rfl⟩ : syracuseStep 6233071 = 9349607) B9349607
theorem B7882697 : Blo 1457548 7882697 := bstep (se 2 (by rfl) ⟨2956011, by rfl⟩ : syracuseStep 7882697 = 5912023) B5912023
theorem B6228713 : Blo 1457548 6228713 := bstep (se 2 (by rfl) ⟨2335767, by rfl⟩ : syracuseStep 6228713 = 4671535) B4671535
theorem B8310761 : Blo 1457548 8310761 := bstep (se 2 (by rfl) ⟨3116535, by rfl⟩ : syracuseStep 8310761 = 6233071) B6233071
theorem B5255351 : Blo 1457548 5255351 := bstep (se 1 (by rfl) ⟨3941513, by rfl⟩ : syracuseStep 5255351 = 7883027) B7883027
theorem B16609535 : Blo 1457548 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B39481631 : Blo 1457548 39481631 := bstep (se 1 (by rfl) ⟨29611223, by rfl⟩ : syracuseStep 39481631 = 59222447) B59222447
theorem B6231583 : Blo 1457548 6231583 := bstep (se 1 (by rfl) ⟨4673687, by rfl⟩ : syracuseStep 6231583 = 9347375) B9347375
theorem B245939291 : Blo 1457548 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B3694207 : Blo 1457548 3694207 := bstep (se 1 (by rfl) ⟨2770655, by rfl⟩ : syracuseStep 3694207 = 5541311) B5541311
theorem B26321087 : Blo 1457548 26321087 := bstep (se 1 (by rfl) ⟨19740815, by rfl⟩ : syracuseStep 26321087 = 39481631) B39481631
theorem B8308777 : Blo 1457548 8308777 := bstep (se 2 (by rfl) ⟨3115791, by rfl⟩ : syracuseStep 8308777 = 6231583) B6231583
theorem B4925609 : Blo 1457548 4925609 := bstep (se 2 (by rfl) ⟨1847103, by rfl⟩ : syracuseStep 4925609 = 3694207) B3694207
theorem B5540507 : Blo 1457548 5540507 := bstep (se 1 (by rfl) ⟨4155380, by rfl⟩ : syracuseStep 5540507 = 8310761) B8310761
theorem B5255131 : Blo 1457548 5255131 := bstep (se 1 (by rfl) ⟨3941348, by rfl⟩ : syracuseStep 5255131 = 7882697) B7882697
theorem B163959527 : Blo 1457548 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B3503567 : Blo 1457548 3503567 := bstep (se 1 (by rfl) ⟨2627675, by rfl⟩ : syracuseStep 3503567 = 5255351) B5255351
theorem B11073023 : Blo 1457548 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B4152475 : Blo 1457548 4152475 := bstep (se 1 (by rfl) ⟨3114356, by rfl⟩ : syracuseStep 4152475 = 6228713) B6228713
theorem B109306351 : Blo 1457548 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B70189565 : Blo 1457548 70189565 := bstep (se 3 (by rfl) ⟨13160543, by rfl⟩ : syracuseStep 70189565 = 26321087) B26321087
theorem B2335711 : Blo 1457548 2335711 := bstep (se 1 (by rfl) ⟨1751783, by rfl⟩ : syracuseStep 2335711 = 3503567) B3503567
theorem B7382015 : Blo 1457548 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B7006841 : Blo 1457548 7006841 := bstep (se 2 (by rfl) ⟨2627565, by rfl⟩ : syracuseStep 7006841 = 5255131) B5255131
theorem B11078369 : Blo 1457548 11078369 := bstep (se 2 (by rfl) ⟨4154388, by rfl⟩ : syracuseStep 11078369 = 8308777) B8308777
theorem B3283739 : Blo 1457548 3283739 := bstep (se 1 (by rfl) ⟨2462804, by rfl⟩ : syracuseStep 3283739 = 4925609) B4925609
theorem B5536633 : Blo 1457548 5536633 := bstep (se 2 (by rfl) ⟨2076237, by rfl⟩ : syracuseStep 5536633 = 4152475) B4152475
theorem B3693671 : Blo 1457548 3693671 := bstep (se 1 (by rfl) ⟨2770253, by rfl⟩ : syracuseStep 3693671 = 5540507) B5540507
theorem B7382177 : Blo 1457548 7382177 := bstep (se 2 (by rfl) ⟨2768316, by rfl⟩ : syracuseStep 7382177 = 5536633) B5536633
theorem B3114281 : Blo 1457548 3114281 := bstep (se 2 (by rfl) ⟨1167855, by rfl⟩ : syracuseStep 3114281 = 2335711) B2335711
theorem B187172173 : Blo 1457548 187172173 := bstep (se 3 (by rfl) ⟨35094782, by rfl⟩ : syracuseStep 187172173 = 70189565) B70189565
theorem B4671227 : Blo 1457548 4671227 := bstep (se 1 (by rfl) ⟨3503420, by rfl⟩ : syracuseStep 4671227 = 7006841) B7006841
theorem B2189159 : Blo 1457548 2189159 := bstep (se 1 (by rfl) ⟨1641869, by rfl⟩ : syracuseStep 2189159 = 3283739) B3283739
theorem B7385579 : Blo 1457548 7385579 := bstep (se 1 (by rfl) ⟨5539184, by rfl⟩ : syracuseStep 7385579 = 11078369) B11078369
theorem B2462447 : Blo 1457548 2462447 := bstep (se 1 (by rfl) ⟨1846835, by rfl⟩ : syracuseStep 2462447 = 3693671) B3693671
theorem B145741801 : Blo 1457548 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B4921343 : Blo 1457548 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B4923719 : Blo 1457548 4923719 := bstep (se 1 (by rfl) ⟨3692789, by rfl⟩ : syracuseStep 4923719 = 7385579) B7385579
theorem B1459439 : Blo 1457548 1459439 := bstep (se 1 (by rfl) ⟨1094579, by rfl⟩ : syracuseStep 1459439 = 2189159) B2189159
theorem B1641631 : Blo 1457548 1641631 := bstep (se 1 (by rfl) ⟨1231223, by rfl⟩ : syracuseStep 1641631 = 2462447) B2462447
theorem B2076187 : Blo 1457548 2076187 := bstep (se 1 (by rfl) ⟨1557140, by rfl⟩ : syracuseStep 2076187 = 3114281) B3114281
theorem B3280895 : Blo 1457548 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B12456605 : Blo 1457548 12456605 := bstep (se 3 (by rfl) ⟨2335613, by rfl⟩ : syracuseStep 12456605 = 4671227) B4671227
theorem B4921451 : Blo 1457548 4921451 := bstep (se 1 (by rfl) ⟨3691088, by rfl⟩ : syracuseStep 4921451 = 7382177) B7382177
theorem B998251589 : Blo 1457548 998251589 := bstep (se 4 (by rfl) ⟨93586086, by rfl⟩ : syracuseStep 998251589 = 187172173) B187172173
theorem B194322401 : Blo 1457548 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B2188841 : Blo 1457548 2188841 := bstep (se 2 (by rfl) ⟨820815, by rfl⟩ : syracuseStep 2188841 = 1641631) B1641631
theorem B3280967 : Blo 1457548 3280967 := bstep (se 1 (by rfl) ⟨2460725, by rfl⟩ : syracuseStep 3280967 = 4921451) B4921451
theorem B3282479 : Blo 1457548 3282479 := bstep (se 1 (by rfl) ⟨2461859, by rfl⟩ : syracuseStep 3282479 = 4923719) B4923719
theorem B8304403 : Blo 1457548 8304403 := bstep (se 1 (by rfl) ⟨6228302, by rfl⟩ : syracuseStep 8304403 = 12456605) B12456605
theorem B2768249 : Blo 1457548 2768249 := bstep (se 2 (by rfl) ⟨1038093, by rfl⟩ : syracuseStep 2768249 = 2076187) B2076187
theorem B665501059 : Blo 1457548 665501059 := bstep (se 1 (by rfl) ⟨499125794, by rfl⟩ : syracuseStep 665501059 = 998251589) B998251589
theorem B129548267 : Blo 1457548 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B2187263 : Blo 1457548 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B2187311 : Blo 1457548 2187311 := bstep (se 1 (by rfl) ⟨1640483, by rfl⟩ : syracuseStep 2187311 = 3280967) B3280967
theorem B1459227 : Blo 1457548 1459227 := bstep (se 1 (by rfl) ⟨1094420, by rfl⟩ : syracuseStep 1459227 = 2188841) B2188841
theorem B2188319 : Blo 1457548 2188319 := bstep (se 1 (by rfl) ⟨1641239, by rfl⟩ : syracuseStep 2188319 = 3282479) B3282479
theorem B887334745 : Blo 1457548 887334745 := bstep (se 2 (by rfl) ⟨332750529, by rfl⟩ : syracuseStep 887334745 = 665501059) B665501059
theorem B1845499 : Blo 1457548 1845499 := bstep (se 1 (by rfl) ⟨1384124, by rfl⟩ : syracuseStep 1845499 = 2768249) B2768249
theorem B1458175 : Blo 1457548 1458175 := bstep (se 1 (by rfl) ⟨1093631, by rfl⟩ : syracuseStep 1458175 = 2187263) B2187263
theorem B11072537 : Blo 1457548 11072537 := bstep (se 2 (by rfl) ⟨4152201, by rfl⟩ : syracuseStep 11072537 = 8304403) B8304403
theorem B86365511 : Blo 1457548 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B1458207 : Blo 1457548 1458207 := bstep (se 1 (by rfl) ⟨1093655, by rfl⟩ : syracuseStep 1458207 = 2187311) B2187311
theorem B7381691 : Blo 1457548 7381691 := bstep (se 1 (by rfl) ⟨5536268, by rfl⟩ : syracuseStep 7381691 = 11072537) B11072537
theorem B1458879 : Blo 1457548 1458879 := bstep (se 1 (by rfl) ⟨1094159, by rfl⟩ : syracuseStep 1458879 = 2188319) B2188319
theorem B2460665 : Blo 1457548 2460665 := bstep (se 2 (by rfl) ⟨922749, by rfl⟩ : syracuseStep 2460665 = 1845499) B1845499
theorem B57577007 : Blo 1457548 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B1183112993 : Blo 1457548 1183112993 := bstep (se 2 (by rfl) ⟨443667372, by rfl⟩ : syracuseStep 1183112993 = 887334745) B887334745
theorem B1640443 : Blo 1457548 1640443 := bstep (se 1 (by rfl) ⟨1230332, by rfl⟩ : syracuseStep 1640443 = 2460665) B2460665
theorem B38384671 : Blo 1457548 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B4921127 : Blo 1457548 4921127 := bstep (se 1 (by rfl) ⟨3690845, by rfl⟩ : syracuseStep 4921127 = 7381691) B7381691
theorem B788741995 : Blo 1457548 788741995 := bstep (se 1 (by rfl) ⟨591556496, by rfl⟩ : syracuseStep 788741995 = 1183112993) B1183112993
theorem B2187257 : Blo 1457548 2187257 := bstep (se 2 (by rfl) ⟨820221, by rfl⟩ : syracuseStep 2187257 = 1640443) B1640443
theorem B3280751 : Blo 1457548 3280751 := bstep (se 1 (by rfl) ⟨2460563, by rfl⟩ : syracuseStep 3280751 = 4921127) B4921127
theorem B51179561 : Blo 1457548 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B1051655993 : Blo 1457548 1051655993 := bstep (se 2 (by rfl) ⟨394370997, by rfl⟩ : syracuseStep 1051655993 = 788741995) B788741995
theorem B34119707 : Blo 1457548 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B701103995 : Blo 1457548 701103995 := bstep (se 1 (by rfl) ⟨525827996, by rfl⟩ : syracuseStep 701103995 = 1051655993) B1051655993
theorem B2187167 : Blo 1457548 2187167 := bstep (se 1 (by rfl) ⟨1640375, by rfl⟩ : syracuseStep 2187167 = 3280751) B3280751
theorem B1458171 : Blo 1457548 1458171 := bstep (se 1 (by rfl) ⟨1093628, by rfl⟩ : syracuseStep 1458171 = 2187257) B2187257
theorem B90985885 : Blo 1457548 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B467402663 : Blo 1457548 467402663 := bstep (se 1 (by rfl) ⟨350551997, by rfl⟩ : syracuseStep 467402663 = 701103995) B701103995
theorem B1458111 : Blo 1457548 1458111 := bstep (se 1 (by rfl) ⟨1093583, by rfl⟩ : syracuseStep 1458111 = 2187167) B2187167
theorem B311601775 : Blo 1457548 311601775 := bstep (se 1 (by rfl) ⟨233701331, by rfl⟩ : syracuseStep 311601775 = 467402663) B467402663
theorem B485258053 : Blo 1457548 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B415469033 : Blo 1457548 415469033 := bstep (se 2 (by rfl) ⟨155800887, by rfl⟩ : syracuseStep 415469033 = 311601775) B311601775
theorem B647010737 : Blo 1457548 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B431340491 : Blo 1457548 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B276979355 : Blo 1457548 276979355 := bstep (se 1 (by rfl) ⟨207734516, by rfl⟩ : syracuseStep 276979355 = 415469033) B415469033
theorem B287560327 : Blo 1457548 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B184652903 : Blo 1457548 184652903 := bstep (se 1 (by rfl) ⟨138489677, by rfl⟩ : syracuseStep 184652903 = 276979355) B276979355
theorem B492407741 : Blo 1457548 492407741 := bstep (se 3 (by rfl) ⟨92326451, by rfl⟩ : syracuseStep 492407741 = 184652903) B184652903
theorem B383413769 : Blo 1457548 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B328271827 : Blo 1457548 328271827 := bstep (se 1 (by rfl) ⟨246203870, by rfl⟩ : syracuseStep 328271827 = 492407741) B492407741
theorem B255609179 : Blo 1457548 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B170406119 : Blo 1457548 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B437695769 : Blo 1457548 437695769 := bstep (se 2 (by rfl) ⟨164135913, by rfl⟩ : syracuseStep 437695769 = 328271827) B328271827
theorem B1167188717 : Blo 1457548 1167188717 := bstep (se 3 (by rfl) ⟨218847884, by rfl⟩ : syracuseStep 1167188717 = 437695769) B437695769
theorem B454416317 : Blo 1457548 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B778125811 : Blo 1457548 778125811 := bstep (se 1 (by rfl) ⟨583594358, by rfl⟩ : syracuseStep 778125811 = 1167188717) B1167188717
theorem B302944211 : Blo 1457548 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B1037501081 : Blo 1457548 1037501081 := bstep (se 2 (by rfl) ⟨389062905, by rfl⟩ : syracuseStep 1037501081 = 778125811) B778125811
theorem B201962807 : Blo 1457548 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B691667387 : Blo 1457548 691667387 := bstep (se 1 (by rfl) ⟨518750540, by rfl⟩ : syracuseStep 691667387 = 1037501081) B1037501081
theorem B134641871 : Blo 1457548 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B461111591 : Blo 1457548 461111591 := bstep (se 1 (by rfl) ⟨345833693, by rfl⟩ : syracuseStep 461111591 = 691667387) B691667387
theorem B89761247 : Blo 1457548 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B307407727 : Blo 1457548 307407727 := bstep (se 1 (by rfl) ⟨230555795, by rfl⟩ : syracuseStep 307407727 = 461111591) B461111591
theorem B59840831 : Blo 1457548 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B409876969 : Blo 1457548 409876969 := bstep (se 2 (by rfl) ⟨153703863, by rfl⟩ : syracuseStep 409876969 = 307407727) B307407727
theorem B39893887 : Blo 1457548 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B53191849 : Blo 1457548 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B546502625 : Blo 1457548 546502625 := bstep (se 2 (by rfl) ⟨204938484, by rfl⟩ : syracuseStep 546502625 = 409876969) B409876969
theorem B364335083 : Blo 1457548 364335083 := bstep (se 1 (by rfl) ⟨273251312, by rfl⟩ : syracuseStep 364335083 = 546502625) B546502625
theorem B70922465 : Blo 1457548 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B242890055 : Blo 1457548 242890055 := bstep (se 1 (by rfl) ⟨182167541, by rfl⟩ : syracuseStep 242890055 = 364335083) B364335083
theorem B47281643 : Blo 1457548 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B161926703 : Blo 1457548 161926703 := bstep (se 1 (by rfl) ⟨121445027, by rfl⟩ : syracuseStep 161926703 = 242890055) B242890055
theorem B31521095 : Blo 1457548 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B21014063 : Blo 1457548 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B107951135 : Blo 1457548 107951135 := bstep (se 1 (by rfl) ⟨80963351, by rfl⟩ : syracuseStep 107951135 = 161926703) B161926703
theorem B14009375 : Blo 1457548 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B1151478773 : Blo 1457548 1151478773 := bstep (se 5 (by rfl) ⟨53975567, by rfl⟩ : syracuseStep 1151478773 = 107951135) B107951135
theorem B37358333 : Blo 1457548 37358333 := bstep (se 3 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 37358333 = 14009375) B14009375
theorem B767652515 : Blo 1457548 767652515 := bstep (se 1 (by rfl) ⟨575739386, by rfl⟩ : syracuseStep 767652515 = 1151478773) B1151478773
theorem B24905555 : Blo 1457548 24905555 := bstep (se 1 (by rfl) ⟨18679166, by rfl⟩ : syracuseStep 24905555 = 37358333) B37358333
theorem B511768343 : Blo 1457548 511768343 := bstep (se 1 (by rfl) ⟨383826257, by rfl⟩ : syracuseStep 511768343 = 767652515) B767652515
theorem B341178895 : Blo 1457548 341178895 := bstep (se 1 (by rfl) ⟨255884171, by rfl⟩ : syracuseStep 341178895 = 511768343) B511768343
theorem B16603703 : Blo 1457548 16603703 := bstep (se 1 (by rfl) ⟨12452777, by rfl⟩ : syracuseStep 16603703 = 24905555) B24905555
theorem B11069135 : Blo 1457548 11069135 := bstep (se 1 (by rfl) ⟨8301851, by rfl⟩ : syracuseStep 11069135 = 16603703) B16603703
theorem B454905193 : Blo 1457548 454905193 := bstep (se 2 (by rfl) ⟨170589447, by rfl⟩ : syracuseStep 454905193 = 341178895) B341178895
theorem B606540257 : Blo 1457548 606540257 := bstep (se 2 (by rfl) ⟨227452596, by rfl⟩ : syracuseStep 606540257 = 454905193) B454905193
theorem B7379423 : Blo 1457548 7379423 := bstep (se 1 (by rfl) ⟨5534567, by rfl⟩ : syracuseStep 7379423 = 11069135) B11069135
theorem B404360171 : Blo 1457548 404360171 := bstep (se 1 (by rfl) ⟨303270128, by rfl⟩ : syracuseStep 404360171 = 606540257) B606540257
theorem B4919615 : Blo 1457548 4919615 := bstep (se 1 (by rfl) ⟨3689711, by rfl⟩ : syracuseStep 4919615 = 7379423) B7379423
theorem B3279743 : Blo 1457548 3279743 := bstep (se 1 (by rfl) ⟨2459807, by rfl⟩ : syracuseStep 3279743 = 4919615) B4919615
theorem B269573447 : Blo 1457548 269573447 := bstep (se 1 (by rfl) ⟨202180085, by rfl⟩ : syracuseStep 269573447 = 404360171) B404360171
theorem B2186495 : Blo 1457548 2186495 := bstep (se 1 (by rfl) ⟨1639871, by rfl⟩ : syracuseStep 2186495 = 3279743) B3279743
theorem B179715631 : Blo 1457548 179715631 := bstep (se 1 (by rfl) ⟨134786723, by rfl⟩ : syracuseStep 179715631 = 269573447) B269573447
theorem B239620841 : Blo 1457548 239620841 := bstep (se 2 (by rfl) ⟨89857815, by rfl⟩ : syracuseStep 239620841 = 179715631) B179715631
theorem B1457663 : Blo 1457548 1457663 := bstep (se 1 (by rfl) ⟨1093247, by rfl⟩ : syracuseStep 1457663 = 2186495) B2186495
theorem B159747227 : Blo 1457548 159747227 := bstep (se 1 (by rfl) ⟨119810420, by rfl⟩ : syracuseStep 159747227 = 239620841) B239620841
theorem B106498151 : Blo 1457548 106498151 := bstep (se 1 (by rfl) ⟨79873613, by rfl⟩ : syracuseStep 106498151 = 159747227) B159747227
theorem B70998767 : Blo 1457548 70998767 := bstep (se 1 (by rfl) ⟨53249075, by rfl⟩ : syracuseStep 70998767 = 106498151) B106498151
theorem B47332511 : Blo 1457548 47332511 := bstep (se 1 (by rfl) ⟨35499383, by rfl⟩ : syracuseStep 47332511 = 70998767) B70998767
theorem B31555007 : Blo 1457548 31555007 := bstep (se 1 (by rfl) ⟨23666255, by rfl⟩ : syracuseStep 31555007 = 47332511) B47332511
theorem B21036671 : Blo 1457548 21036671 := bstep (se 1 (by rfl) ⟨15777503, by rfl⟩ : syracuseStep 21036671 = 31555007) B31555007
theorem B14024447 : Blo 1457548 14024447 := bstep (se 1 (by rfl) ⟨10518335, by rfl⟩ : syracuseStep 14024447 = 21036671) B21036671
theorem B9349631 : Blo 1457548 9349631 := bstep (se 1 (by rfl) ⟨7012223, by rfl⟩ : syracuseStep 9349631 = 14024447) B14024447
theorem B6233087 : Blo 1457548 6233087 := bstep (se 1 (by rfl) ⟨4674815, by rfl⟩ : syracuseStep 6233087 = 9349631) B9349631
theorem B4155391 : Blo 1457548 4155391 := bstep (se 1 (by rfl) ⟨3116543, by rfl⟩ : syracuseStep 4155391 = 6233087) B6233087
theorem B5540521 : Blo 1457548 5540521 := bstep (se 2 (by rfl) ⟨2077695, by rfl⟩ : syracuseStep 5540521 = 4155391) B4155391
theorem B7387361 : Blo 1457548 7387361 := bstep (se 2 (by rfl) ⟨2770260, by rfl⟩ : syracuseStep 7387361 = 5540521) B5540521
theorem B4924907 : Blo 1457548 4924907 := bstep (se 1 (by rfl) ⟨3693680, by rfl⟩ : syracuseStep 4924907 = 7387361) B7387361
theorem B3283271 : Blo 1457548 3283271 := bstep (se 1 (by rfl) ⟨2462453, by rfl⟩ : syracuseStep 3283271 = 4924907) B4924907
theorem B2188847 : Blo 1457548 2188847 := bstep (se 1 (by rfl) ⟨1641635, by rfl⟩ : syracuseStep 2188847 = 3283271) B3283271
theorem B1459231 : Blo 1457548 1459231 := bstep (se 1 (by rfl) ⟨1094423, by rfl⟩ : syracuseStep 1459231 = 2188847) B2188847

theorem C0 (j : ℕ) (h1 : 364387 ≤ j) (h2 : j ≤ 364886) : Blo 1457548 (4 * j + 3) := by
  interval_cases j
  · exact B1457551
  · exact B1457555
  · exact B1457559
  · exact B1457563
  · exact B1457567
  · exact B1457571
  · exact B1457575
  · exact B1457579
  · exact B1457583
  · exact B1457587
  · exact B1457591
  · exact B1457595
  · exact B1457599
  · exact B1457603
  · exact B1457607
  · exact B1457611
  · exact B1457615
  · exact B1457619
  · exact B1457623
  · exact B1457627
  · exact B1457631
  · exact B1457635
  · exact B1457639
  · exact B1457643
  · exact B1457647
  · exact B1457651
  · exact B1457655
  · exact B1457659
  · exact B1457663
  · exact B1457667
  · exact B1457671
  · exact B1457675
  · exact B1457679
  · exact B1457683
  · exact B1457687
  · exact B1457691
  · exact B1457695
  · exact B1457699
  · exact B1457703
  · exact B1457707
  · exact B1457711
  · exact B1457715
  · exact B1457719
  · exact B1457723
  · exact B1457727
  · exact B1457731
  · exact B1457735
  · exact B1457739
  · exact B1457743
  · exact B1457747
  · exact B1457751
  · exact B1457755
  · exact B1457759
  · exact B1457763
  · exact B1457767
  · exact B1457771
  · exact B1457775
  · exact B1457779
  · exact B1457783
  · exact B1457787
  · exact B1457791
  · exact B1457795
  · exact B1457799
  · exact B1457803
  · exact B1457807
  · exact B1457811
  · exact B1457815
  · exact B1457819
  · exact B1457823
  · exact B1457827
  · exact B1457831
  · exact B1457835
  · exact B1457839
  · exact B1457843
  · exact B1457847
  · exact B1457851
  · exact B1457855
  · exact B1457859
  · exact B1457863
  · exact B1457867
  · exact B1457871
  · exact B1457875
  · exact B1457879
  · exact B1457883
  · exact B1457887
  · exact B1457891
  · exact B1457895
  · exact B1457899
  · exact B1457903
  · exact B1457907
  · exact B1457911
  · exact B1457915
  · exact B1457919
  · exact B1457923
  · exact B1457927
  · exact B1457931
  · exact B1457935
  · exact B1457939
  · exact B1457943
  · exact B1457947
  · exact B1457951
  · exact B1457955
  · exact B1457959
  · exact B1457963
  · exact B1457967
  · exact B1457971
  · exact B1457975
  · exact B1457979
  · exact B1457983
  · exact B1457987
  · exact B1457991
  · exact B1457995
  · exact B1457999
  · exact B1458003
  · exact B1458007
  · exact B1458011
  · exact B1458015
  · exact B1458019
  · exact B1458023
  · exact B1458027
  · exact B1458031
  · exact B1458035
  · exact B1458039
  · exact B1458043
  · exact B1458047
  · exact B1458051
  · exact B1458055
  · exact B1458059
  · exact B1458063
  · exact B1458067
  · exact B1458071
  · exact B1458075
  · exact B1458079
  · exact B1458083
  · exact B1458087
  · exact B1458091
  · exact B1458095
  · exact B1458099
  · exact B1458103
  · exact B1458107
  · exact B1458111
  · exact B1458115
  · exact B1458119
  · exact B1458123
  · exact B1458127
  · exact B1458131
  · exact B1458135
  · exact B1458139
  · exact B1458143
  · exact B1458147
  · exact B1458151
  · exact B1458155
  · exact B1458159
  · exact B1458163
  · exact B1458167
  · exact B1458171
  · exact B1458175
  · exact B1458179
  · exact B1458183
  · exact B1458187
  · exact B1458191
  · exact B1458195
  · exact B1458199
  · exact B1458203
  · exact B1458207
  · exact B1458211
  · exact B1458215
  · exact B1458219
  · exact B1458223
  · exact B1458227
  · exact B1458231
  · exact B1458235
  · exact B1458239
  · exact B1458243
  · exact B1458247
  · exact B1458251
  · exact B1458255
  · exact B1458259
  · exact B1458263
  · exact B1458267
  · exact B1458271
  · exact B1458275
  · exact B1458279
  · exact B1458283
  · exact B1458287
  · exact B1458291
  · exact B1458295
  · exact B1458299
  · exact B1458303
  · exact B1458307
  · exact B1458311
  · exact B1458315
  · exact B1458319
  · exact B1458323
  · exact B1458327
  · exact B1458331
  · exact B1458335
  · exact B1458339
  · exact B1458343
  · exact B1458347
  · exact B1458351
  · exact B1458355
  · exact B1458359
  · exact B1458363
  · exact B1458367
  · exact B1458371
  · exact B1458375
  · exact B1458379
  · exact B1458383
  · exact B1458387
  · exact B1458391
  · exact B1458395
  · exact B1458399
  · exact B1458403
  · exact B1458407
  · exact B1458411
  · exact B1458415
  · exact B1458419
  · exact B1458423
  · exact B1458427
  · exact B1458431
  · exact B1458435
  · exact B1458439
  · exact B1458443
  · exact B1458447
  · exact B1458451
  · exact B1458455
  · exact B1458459
  · exact B1458463
  · exact B1458467
  · exact B1458471
  · exact B1458475
  · exact B1458479
  · exact B1458483
  · exact B1458487
  · exact B1458491
  · exact B1458495
  · exact B1458499
  · exact B1458503
  · exact B1458507
  · exact B1458511
  · exact B1458515
  · exact B1458519
  · exact B1458523
  · exact B1458527
  · exact B1458531
  · exact B1458535
  · exact B1458539
  · exact B1458543
  · exact B1458547
  · exact B1458551
  · exact B1458555
  · exact B1458559
  · exact B1458563
  · exact B1458567
  · exact B1458571
  · exact B1458575
  · exact B1458579
  · exact B1458583
  · exact B1458587
  · exact B1458591
  · exact B1458595
  · exact B1458599
  · exact B1458603
  · exact B1458607
  · exact B1458611
  · exact B1458615
  · exact B1458619
  · exact B1458623
  · exact B1458627
  · exact B1458631
  · exact B1458635
  · exact B1458639
  · exact B1458643
  · exact B1458647
  · exact B1458651
  · exact B1458655
  · exact B1458659
  · exact B1458663
  · exact B1458667
  · exact B1458671
  · exact B1458675
  · exact B1458679
  · exact B1458683
  · exact B1458687
  · exact B1458691
  · exact B1458695
  · exact B1458699
  · exact B1458703
  · exact B1458707
  · exact B1458711
  · exact B1458715
  · exact B1458719
  · exact B1458723
  · exact B1458727
  · exact B1458731
  · exact B1458735
  · exact B1458739
  · exact B1458743
  · exact B1458747
  · exact B1458751
  · exact B1458755
  · exact B1458759
  · exact B1458763
  · exact B1458767
  · exact B1458771
  · exact B1458775
  · exact B1458779
  · exact B1458783
  · exact B1458787
  · exact B1458791
  · exact B1458795
  · exact B1458799
  · exact B1458803
  · exact B1458807
  · exact B1458811
  · exact B1458815
  · exact B1458819
  · exact B1458823
  · exact B1458827
  · exact B1458831
  · exact B1458835
  · exact B1458839
  · exact B1458843
  · exact B1458847
  · exact B1458851
  · exact B1458855
  · exact B1458859
  · exact B1458863
  · exact B1458867
  · exact B1458871
  · exact B1458875
  · exact B1458879
  · exact B1458883
  · exact B1458887
  · exact B1458891
  · exact B1458895
  · exact B1458899
  · exact B1458903
  · exact B1458907
  · exact B1458911
  · exact B1458915
  · exact B1458919
  · exact B1458923
  · exact B1458927
  · exact B1458931
  · exact B1458935
  · exact B1458939
  · exact B1458943
  · exact B1458947
  · exact B1458951
  · exact B1458955
  · exact B1458959
  · exact B1458963
  · exact B1458967
  · exact B1458971
  · exact B1458975
  · exact B1458979
  · exact B1458983
  · exact B1458987
  · exact B1458991
  · exact B1458995
  · exact B1458999
  · exact B1459003
  · exact B1459007
  · exact B1459011
  · exact B1459015
  · exact B1459019
  · exact B1459023
  · exact B1459027
  · exact B1459031
  · exact B1459035
  · exact B1459039
  · exact B1459043
  · exact B1459047
  · exact B1459051
  · exact B1459055
  · exact B1459059
  · exact B1459063
  · exact B1459067
  · exact B1459071
  · exact B1459075
  · exact B1459079
  · exact B1459083
  · exact B1459087
  · exact B1459091
  · exact B1459095
  · exact B1459099
  · exact B1459103
  · exact B1459107
  · exact B1459111
  · exact B1459115
  · exact B1459119
  · exact B1459123
  · exact B1459127
  · exact B1459131
  · exact B1459135
  · exact B1459139
  · exact B1459143
  · exact B1459147
  · exact B1459151
  · exact B1459155
  · exact B1459159
  · exact B1459163
  · exact B1459167
  · exact B1459171
  · exact B1459175
  · exact B1459179
  · exact B1459183
  · exact B1459187
  · exact B1459191
  · exact B1459195
  · exact B1459199
  · exact B1459203
  · exact B1459207
  · exact B1459211
  · exact B1459215
  · exact B1459219
  · exact B1459223
  · exact B1459227
  · exact B1459231
  · exact B1459235
  · exact B1459239
  · exact B1459243
  · exact B1459247
  · exact B1459251
  · exact B1459255
  · exact B1459259
  · exact B1459263
  · exact B1459267
  · exact B1459271
  · exact B1459275
  · exact B1459279
  · exact B1459283
  · exact B1459287
  · exact B1459291
  · exact B1459295
  · exact B1459299
  · exact B1459303
  · exact B1459307
  · exact B1459311
  · exact B1459315
  · exact B1459319
  · exact B1459323
  · exact B1459327
  · exact B1459331
  · exact B1459335
  · exact B1459339
  · exact B1459343
  · exact B1459347
  · exact B1459351
  · exact B1459355
  · exact B1459359
  · exact B1459363
  · exact B1459367
  · exact B1459371
  · exact B1459375
  · exact B1459379
  · exact B1459383
  · exact B1459387
  · exact B1459391
  · exact B1459395
  · exact B1459399
  · exact B1459403
  · exact B1459407
  · exact B1459411
  · exact B1459415
  · exact B1459419
  · exact B1459423
  · exact B1459427
  · exact B1459431
  · exact B1459435
  · exact B1459439
  · exact B1459443
  · exact B1459447
  · exact B1459451
  · exact B1459455
  · exact B1459459
  · exact B1459463
  · exact B1459467
  · exact B1459471
  · exact B1459475
  · exact B1459479
  · exact B1459483
  · exact B1459487
  · exact B1459491
  · exact B1459495
  · exact B1459499
  · exact B1459503
  · exact B1459507
  · exact B1459511
  · exact B1459515
  · exact B1459519
  · exact B1459523
  · exact B1459527
  · exact B1459531
  · exact B1459535
  · exact B1459539
  · exact B1459543
  · exact B1459547

theorem solution (m : ℕ) (hlo : 1457548 ≤ m) (hhi : m ≤ 1459548) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 364387 ≤ j := by omega
    have hj2 : j ≤ 364886 := by omega
    have hb : Blo 1457548 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
