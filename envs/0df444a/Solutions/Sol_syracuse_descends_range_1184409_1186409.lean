-- Prove2me | solution 1 for syracuse_descends_range_1184409_1186409
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:34.242325+00:00
-- url     : https://prove2.me/submissions/7e3abbaa-8674-46e0-ae5a-dbdca8b15bde

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


theorem B1777685 : Blo 1184409 1777685 := bbase (se 6 (by rfl) ⟨41664, by rfl⟩ : syracuseStep 1777685 = 83329) (by norm_num)
theorem B3604501 : Blo 1184409 3604501 := bbase (se 6 (by rfl) ⟨84480, by rfl⟩ : syracuseStep 3604501 = 168961) (by norm_num)
theorem B3424277 : Blo 1184409 3424277 := bbase (se 6 (by rfl) ⟨80256, by rfl⟩ : syracuseStep 3424277 = 160513) (by norm_num)
theorem B1998877 : Blo 1184409 1998877 := bbase (se 3 (by rfl) ⟨374789, by rfl⟩ : syracuseStep 1998877 = 749579) (by norm_num)
theorem B3039277 : Blo 1184409 3039277 := bbase (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) (by norm_num)
theorem B1777709 : Blo 1184409 1777709 := bbase (se 3 (by rfl) ⟨333320, by rfl⟩ : syracuseStep 1777709 = 666641) (by norm_num)
theorem B1777733 : Blo 1184409 1777733 := bbase (se 4 (by rfl) ⟨166662, by rfl⟩ : syracuseStep 1777733 = 333325) (by norm_num)
theorem B3997781 : Blo 1184409 3997781 := bbase (se 8 (by rfl) ⟨23424, by rfl⟩ : syracuseStep 3997781 = 46849) (by norm_num)
theorem B6406229 : Blo 1184409 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B1777757 : Blo 1184409 1777757 := bbase (se 3 (by rfl) ⟨333329, by rfl⟩ : syracuseStep 1777757 = 666659) (by norm_num)
theorem B1499249 : Blo 1184409 1499249 := bbase (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) (by norm_num)
theorem B1998965 : Blo 1184409 1998965 := bbase (se 5 (by rfl) ⟨93701, by rfl⟩ : syracuseStep 1998965 = 187403) (by norm_num)
theorem B1777781 : Blo 1184409 1777781 := bbase (se 5 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 1777781 = 166667) (by norm_num)
theorem B6004853 : Blo 1184409 6004853 := bbase (se 5 (by rfl) ⟨281477, by rfl⟩ : syracuseStep 6004853 = 562955) (by norm_num)
theorem B2998397 : Blo 1184409 2998397 := bbase (se 3 (by rfl) ⟨562199, by rfl⟩ : syracuseStep 2998397 = 1124399) (by norm_num)
theorem B1777805 : Blo 1184409 1777805 := bbase (se 3 (by rfl) ⟨333338, by rfl⟩ : syracuseStep 1777805 = 666677) (by norm_num)
theorem B1777829 : Blo 1184409 1777829 := bbase (se 4 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 1777829 = 333343) (by norm_num)
theorem B1499305 : Blo 1184409 1499305 := bbase (se 2 (by rfl) ⟨562239, by rfl⟩ : syracuseStep 1499305 = 1124479) (by norm_num)
theorem B5062837 : Blo 1184409 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B1777853 : Blo 1184409 1777853 := bbase (se 3 (by rfl) ⟨333347, by rfl⟩ : syracuseStep 1777853 = 666695) (by norm_num)
theorem B1851589 : Blo 1184409 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B1777877 : Blo 1184409 1777877 := bbase (se 7 (by rfl) ⟨20834, by rfl⟩ : syracuseStep 1777877 = 41669) (by norm_num)
theorem B1777901 : Blo 1184409 1777901 := bbase (se 3 (by rfl) ⟨333356, by rfl⟩ : syracuseStep 1777901 = 666713) (by norm_num)
theorem B3465461 : Blo 1184409 3465461 := bbase (se 5 (by rfl) ⟨162443, by rfl⟩ : syracuseStep 3465461 = 324887) (by norm_num)
theorem B1999093 : Blo 1184409 1999093 := bbase (se 5 (by rfl) ⟨93707, by rfl⟩ : syracuseStep 1999093 = 187415) (by norm_num)
theorem B1777925 : Blo 1184409 1777925 := bbase (se 4 (by rfl) ⟨166680, by rfl⟩ : syracuseStep 1777925 = 333361) (by norm_num)
theorem B1499401 : Blo 1184409 1499401 := bbase (se 2 (by rfl) ⟨562275, by rfl⟩ : syracuseStep 1499401 = 1124551) (by norm_num)
theorem B1777949 : Blo 1184409 1777949 := bbase (se 3 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 1777949 = 666731) (by norm_num)
theorem B1777973 : Blo 1184409 1777973 := bbase (se 5 (by rfl) ⟨83342, by rfl⟩ : syracuseStep 1777973 = 166685) (by norm_num)
theorem B1999181 : Blo 1184409 1999181 := bbase (se 3 (by rfl) ⟨374846, by rfl⟩ : syracuseStep 1999181 = 749693) (by norm_num)
theorem B1777997 : Blo 1184409 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B1778021 : Blo 1184409 1778021 := bbase (se 4 (by rfl) ⟨166689, by rfl⟩ : syracuseStep 1778021 = 333379) (by norm_num)
theorem B1778045 : Blo 1184409 1778045 := bbase (se 3 (by rfl) ⟨333383, by rfl⟩ : syracuseStep 1778045 = 666767) (by norm_num)
theorem B1778069 : Blo 1184409 1778069 := bbase (se 6 (by rfl) ⟨41673, by rfl⟩ : syracuseStep 1778069 = 83347) (by norm_num)
theorem B1778093 : Blo 1184409 1778093 := bbase (se 3 (by rfl) ⟨333392, by rfl⟩ : syracuseStep 1778093 = 666785) (by norm_num)
theorem B1499573 : Blo 1184409 1499573 := bbase (se 5 (by rfl) ⟨70292, by rfl⟩ : syracuseStep 1499573 = 140585) (by norm_num)
theorem B3203525 : Blo 1184409 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B1778117 : Blo 1184409 1778117 := bbase (se 4 (by rfl) ⟨166698, by rfl⟩ : syracuseStep 1778117 = 333397) (by norm_num)
theorem B1999309 : Blo 1184409 1999309 := bbase (se 3 (by rfl) ⟨374870, by rfl⟩ : syracuseStep 1999309 = 749741) (by norm_num)
theorem B2998741 : Blo 1184409 2998741 := bbase (se 7 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 2998741 = 70283) (by norm_num)
theorem B1778141 : Blo 1184409 1778141 := bbase (se 3 (by rfl) ⟨333401, by rfl⟩ : syracuseStep 1778141 = 666803) (by norm_num)
theorem B3375589 : Blo 1184409 3375589 := bbase (se 4 (by rfl) ⟨316461, by rfl⟩ : syracuseStep 3375589 = 632923) (by norm_num)
theorem B1499629 : Blo 1184409 1499629 := bbase (se 3 (by rfl) ⟨281180, by rfl⟩ : syracuseStep 1499629 = 562361) (by norm_num)
theorem B1688045 : Blo 1184409 1688045 := bbase (se 3 (by rfl) ⟨316508, by rfl⟩ : syracuseStep 1688045 = 633017) (by norm_num)
theorem B1778165 : Blo 1184409 1778165 := bbase (se 5 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 1778165 = 166703) (by norm_num)
theorem B3998213 : Blo 1184409 3998213 := bbase (se 4 (by rfl) ⟨374832, by rfl⟩ : syracuseStep 3998213 = 749665) (by norm_num)
theorem B1778189 : Blo 1184409 1778189 := bbase (se 3 (by rfl) ⟨333410, by rfl⟩ : syracuseStep 1778189 = 666821) (by norm_num)
theorem B5997077 : Blo 1184409 5997077 := bbase (se 6 (by rfl) ⟨140556, by rfl⟩ : syracuseStep 5997077 = 281113) (by norm_num)
theorem B1999397 : Blo 1184409 1999397 := bbase (se 4 (by rfl) ⟨187443, by rfl⟩ : syracuseStep 1999397 = 374887) (by norm_num)
theorem B1778213 : Blo 1184409 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B1778237 : Blo 1184409 1778237 := bbase (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) (by norm_num)
theorem B2998853 : Blo 1184409 2998853 := bbase (se 4 (by rfl) ⟨281142, by rfl⟩ : syracuseStep 2998853 = 562285) (by norm_num)
theorem B1499725 : Blo 1184409 1499725 := bbase (se 3 (by rfl) ⟨281198, by rfl⟩ : syracuseStep 1499725 = 562397) (by norm_num)
theorem B1778261 : Blo 1184409 1778261 := bbase (se 8 (by rfl) ⟨10419, by rfl⟩ : syracuseStep 1778261 = 20839) (by norm_num)
theorem B1778285 : Blo 1184409 1778285 := bbase (se 3 (by rfl) ⟨333428, by rfl⟩ : syracuseStep 1778285 = 666857) (by norm_num)
theorem B4498037 : Blo 1184409 4498037 := bbase (se 5 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 4498037 = 421691) (by norm_num)
theorem B3375749 : Blo 1184409 3375749 := bbase (se 4 (by rfl) ⟨316476, by rfl⟩ : syracuseStep 3375749 = 632953) (by norm_num)
theorem B1778309 : Blo 1184409 1778309 := bbase (se 4 (by rfl) ⟨166716, by rfl⟩ : syracuseStep 1778309 = 333433) (by norm_num)
theorem B1778333 : Blo 1184409 1778333 := bbase (se 3 (by rfl) ⟨333437, by rfl⟩ : syracuseStep 1778333 = 666875) (by norm_num)
theorem B1999525 : Blo 1184409 1999525 := bbase (se 4 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 1999525 = 374911) (by norm_num)
theorem B1778357 : Blo 1184409 1778357 := bbase (se 5 (by rfl) ⟨83360, by rfl⟩ : syracuseStep 1778357 = 166721) (by norm_num)
theorem B1778381 : Blo 1184409 1778381 := bbase (se 3 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 1778381 = 666893) (by norm_num)
theorem B1778405 : Blo 1184409 1778405 := bbase (se 4 (by rfl) ⟨166725, by rfl⟩ : syracuseStep 1778405 = 333451) (by norm_num)
theorem B1499897 : Blo 1184409 1499897 := bbase (se 2 (by rfl) ⟨562461, by rfl⟩ : syracuseStep 1499897 = 1124923) (by norm_num)
theorem B1999613 : Blo 1184409 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B1778429 : Blo 1184409 1778429 := bbase (se 3 (by rfl) ⟨333455, by rfl⟩ : syracuseStep 1778429 = 666911) (by norm_num)
theorem B2999045 : Blo 1184409 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B1778453 : Blo 1184409 1778453 := bbase (se 6 (by rfl) ⟨41682, by rfl⟩ : syracuseStep 1778453 = 83365) (by norm_num)
theorem B1778477 : Blo 1184409 1778477 := bbase (se 3 (by rfl) ⟨333464, by rfl⟩ : syracuseStep 1778477 = 666929) (by norm_num)
theorem B1499953 : Blo 1184409 1499953 := bbase (se 2 (by rfl) ⟨562482, by rfl⟩ : syracuseStep 1499953 = 1124965) (by norm_num)
theorem B1778501 : Blo 1184409 1778501 := bbase (se 4 (by rfl) ⟨166734, by rfl⟩ : syracuseStep 1778501 = 333469) (by norm_num)
theorem B1778525 : Blo 1184409 1778525 := bbase (se 3 (by rfl) ⟨333473, by rfl⟩ : syracuseStep 1778525 = 666947) (by norm_num)
theorem B2532197 : Blo 1184409 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B3375989 : Blo 1184409 3375989 := bbase (se 5 (by rfl) ⟨158249, by rfl⟩ : syracuseStep 3375989 = 316499) (by norm_num)
theorem B1778549 : Blo 1184409 1778549 := bbase (se 5 (by rfl) ⟨83369, by rfl⟩ : syracuseStep 1778549 = 166739) (by norm_num)
theorem B1999741 : Blo 1184409 1999741 := bbase (se 3 (by rfl) ⟨374951, by rfl⟩ : syracuseStep 1999741 = 749903) (by norm_num)
theorem B1778573 : Blo 1184409 1778573 := bbase (se 3 (by rfl) ⟨333482, by rfl⟩ : syracuseStep 1778573 = 666965) (by norm_num)
theorem B1500049 : Blo 1184409 1500049 := bbase (se 2 (by rfl) ⟨562518, by rfl⟩ : syracuseStep 1500049 = 1125037) (by norm_num)
theorem B4498325 : Blo 1184409 4498325 := bbase (se 6 (by rfl) ⟨105429, by rfl⟩ : syracuseStep 4498325 = 210859) (by norm_num)
theorem B5063573 : Blo 1184409 5063573 := bbase (se 6 (by rfl) ⟨118677, by rfl⟩ : syracuseStep 5063573 = 237355) (by norm_num)
theorem B1778597 : Blo 1184409 1778597 := bbase (se 4 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 1778597 = 333487) (by norm_num)
theorem B3998645 : Blo 1184409 3998645 := bbase (se 5 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 3998645 = 374873) (by norm_num)
theorem B1778621 : Blo 1184409 1778621 := bbase (se 3 (by rfl) ⟨333491, by rfl⟩ : syracuseStep 1778621 = 666983) (by norm_num)
theorem B1999829 : Blo 1184409 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B1778645 : Blo 1184409 1778645 := bbase (se 7 (by rfl) ⟨20843, by rfl⟩ : syracuseStep 1778645 = 41687) (by norm_num)
theorem B1778669 : Blo 1184409 1778669 := bbase (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) (by norm_num)
theorem B2532341 : Blo 1184409 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B1778693 : Blo 1184409 1778693 := bbase (se 4 (by rfl) ⟨166752, by rfl⟩ : syracuseStep 1778693 = 333505) (by norm_num)
theorem B1778717 : Blo 1184409 1778717 := bbase (se 3 (by rfl) ⟨333509, by rfl⟩ : syracuseStep 1778717 = 667019) (by norm_num)
theorem B3376181 : Blo 1184409 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B1778741 : Blo 1184409 1778741 := bbase (se 5 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 1778741 = 166757) (by norm_num)
theorem B1500221 : Blo 1184409 1500221 := bbase (se 3 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 1500221 = 562583) (by norm_num)
theorem B1778765 : Blo 1184409 1778765 := bbase (se 3 (by rfl) ⟨333518, by rfl⟩ : syracuseStep 1778765 = 667037) (by norm_num)
theorem B1999957 : Blo 1184409 1999957 := bbase (se 8 (by rfl) ⟨11718, by rfl⟩ : syracuseStep 1999957 = 23437) (by norm_num)
theorem B2999389 : Blo 1184409 2999389 := bbase (se 3 (by rfl) ⟨562385, by rfl⟩ : syracuseStep 2999389 = 1124771) (by norm_num)
theorem B1778789 : Blo 1184409 1778789 := bbase (se 4 (by rfl) ⟨166761, by rfl⟩ : syracuseStep 1778789 = 333523) (by norm_num)
theorem B1500277 : Blo 1184409 1500277 := bbase (se 5 (by rfl) ⟨70325, by rfl⟩ : syracuseStep 1500277 = 140651) (by norm_num)
theorem B1778813 : Blo 1184409 1778813 := bbase (se 3 (by rfl) ⟨333527, by rfl⟩ : syracuseStep 1778813 = 667055) (by norm_num)
theorem B1778837 : Blo 1184409 1778837 := bbase (se 6 (by rfl) ⟨41691, by rfl⟩ : syracuseStep 1778837 = 83383) (by norm_num)
theorem B2000045 : Blo 1184409 2000045 := bbase (se 3 (by rfl) ⟨375008, by rfl⟩ : syracuseStep 2000045 = 750017) (by norm_num)
theorem B1778861 : Blo 1184409 1778861 := bbase (se 3 (by rfl) ⟨333536, by rfl⟩ : syracuseStep 1778861 = 667073) (by norm_num)
theorem B1778885 : Blo 1184409 1778885 := bbase (se 4 (by rfl) ⟨166770, by rfl⟩ : syracuseStep 1778885 = 333541) (by norm_num)
theorem B2999501 : Blo 1184409 2999501 := bbase (se 3 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 2999501 = 1124813) (by norm_num)
theorem B2401493 : Blo 1184409 2401493 := bbase (se 7 (by rfl) ⟨28142, by rfl⟩ : syracuseStep 2401493 = 56285) (by norm_num)
theorem B1500373 : Blo 1184409 1500373 := bbase (se 7 (by rfl) ⟨17582, by rfl⟩ : syracuseStep 1500373 = 35165) (by norm_num)
theorem B1778909 : Blo 1184409 1778909 := bbase (se 3 (by rfl) ⟨333545, by rfl⟩ : syracuseStep 1778909 = 667091) (by norm_num)
theorem B1688797 : Blo 1184409 1688797 := bbase (se 3 (by rfl) ⟨316649, by rfl⟩ : syracuseStep 1688797 = 633299) (by norm_num)
theorem B1778933 : Blo 1184409 1778933 := bbase (se 5 (by rfl) ⟨83387, by rfl⟩ : syracuseStep 1778933 = 166775) (by norm_num)
theorem B1778957 : Blo 1184409 1778957 := bbase (se 3 (by rfl) ⟨333554, by rfl⟩ : syracuseStep 1778957 = 667109) (by norm_num)
theorem B1803541 : Blo 1184409 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B1778981 : Blo 1184409 1778981 := bbase (se 4 (by rfl) ⟨166779, by rfl⟩ : syracuseStep 1778981 = 333559) (by norm_num)
theorem B2000173 : Blo 1184409 2000173 := bbase (se 3 (by rfl) ⟨375032, by rfl⟩ : syracuseStep 2000173 = 750065) (by norm_num)
theorem B1779005 : Blo 1184409 1779005 := bbase (se 3 (by rfl) ⟨333563, by rfl⟩ : syracuseStep 1779005 = 667127) (by norm_num)
theorem B1779029 : Blo 1184409 1779029 := bbase (se 12 (by rfl) ⟨651, by rfl⟩ : syracuseStep 1779029 = 1303) (by norm_num)
theorem B2532701 : Blo 1184409 2532701 := bbase (se 3 (by rfl) ⟨474881, by rfl⟩ : syracuseStep 2532701 = 949763) (by norm_num)
theorem B3999077 : Blo 1184409 3999077 := bbase (se 4 (by rfl) ⟨374913, by rfl⟩ : syracuseStep 3999077 = 749827) (by norm_num)
theorem B1779053 : Blo 1184409 1779053 := bbase (se 3 (by rfl) ⟨333572, by rfl⟩ : syracuseStep 1779053 = 667145) (by norm_num)
theorem B5776757 : Blo 1184409 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B1500545 : Blo 1184409 1500545 := bbase (se 2 (by rfl) ⟨562704, by rfl⟩ : syracuseStep 1500545 = 1125409) (by norm_num)
theorem B2000261 : Blo 1184409 2000261 := bbase (se 4 (by rfl) ⟨187524, by rfl⟩ : syracuseStep 2000261 = 375049) (by norm_num)
theorem B1779077 : Blo 1184409 1779077 := bbase (se 4 (by rfl) ⟨166788, by rfl⟩ : syracuseStep 1779077 = 333577) (by norm_num)
theorem B6006149 : Blo 1184409 6006149 := bbase (se 4 (by rfl) ⟨563076, by rfl⟩ : syracuseStep 6006149 = 1126153) (by norm_num)
theorem B2999693 : Blo 1184409 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B1779101 : Blo 1184409 1779101 := bbase (se 3 (by rfl) ⟨333581, by rfl⟩ : syracuseStep 1779101 = 667163) (by norm_num)
theorem B1779125 : Blo 1184409 1779125 := bbase (se 5 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 1779125 = 166793) (by norm_num)
theorem B1500601 : Blo 1184409 1500601 := bbase (se 2 (by rfl) ⟨562725, by rfl⟩ : syracuseStep 1500601 = 1125451) (by norm_num)
theorem B1779149 : Blo 1184409 1779149 := bbase (se 3 (by rfl) ⟨333590, by rfl⟩ : syracuseStep 1779149 = 667181) (by norm_num)
theorem B30377429 : Blo 1184409 30377429 := bbase (se 7 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 30377429 = 711971) (by norm_num)
theorem B1779173 : Blo 1184409 1779173 := bbase (se 4 (by rfl) ⟨166797, by rfl⟩ : syracuseStep 1779173 = 333595) (by norm_num)
theorem B1779197 : Blo 1184409 1779197 := bbase (se 3 (by rfl) ⟨333599, by rfl⟩ : syracuseStep 1779197 = 667199) (by norm_num)
theorem B2000389 : Blo 1184409 2000389 := bbase (se 4 (by rfl) ⟨187536, by rfl⟩ : syracuseStep 2000389 = 375073) (by norm_num)
theorem B1779221 : Blo 1184409 1779221 := bbase (se 6 (by rfl) ⟨41700, by rfl⟩ : syracuseStep 1779221 = 83401) (by norm_num)
theorem B1500697 : Blo 1184409 1500697 := bbase (se 2 (by rfl) ⟨562761, by rfl⟩ : syracuseStep 1500697 = 1125523) (by norm_num)
theorem B1779245 : Blo 1184409 1779245 := bbase (se 3 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 1779245 = 667217) (by norm_num)
theorem B1779269 : Blo 1184409 1779269 := bbase (se 4 (by rfl) ⟨166806, by rfl⟩ : syracuseStep 1779269 = 333613) (by norm_num)
theorem B2000477 : Blo 1184409 2000477 := bbase (se 3 (by rfl) ⟨375089, by rfl⟩ : syracuseStep 2000477 = 750179) (by norm_num)
theorem B1779293 : Blo 1184409 1779293 := bbase (se 3 (by rfl) ⟨333617, by rfl⟩ : syracuseStep 1779293 = 667235) (by norm_num)
theorem B1779317 : Blo 1184409 1779317 := bbase (se 5 (by rfl) ⟨83405, by rfl⟩ : syracuseStep 1779317 = 166811) (by norm_num)
theorem B1779341 : Blo 1184409 1779341 := bbase (se 3 (by rfl) ⟨333626, by rfl⟩ : syracuseStep 1779341 = 667253) (by norm_num)
theorem B1779365 : Blo 1184409 1779365 := bbase (se 4 (by rfl) ⟨166815, by rfl⟩ : syracuseStep 1779365 = 333631) (by norm_num)
theorem B1779389 : Blo 1184409 1779389 := bbase (se 3 (by rfl) ⟨333635, by rfl⟩ : syracuseStep 1779389 = 667271) (by norm_num)
theorem B6080197 : Blo 1184409 6080197 := bbase (se 4 (by rfl) ⟨570018, by rfl⟩ : syracuseStep 6080197 = 1140037) (by norm_num)
theorem B1500869 : Blo 1184409 1500869 := bbase (se 4 (by rfl) ⟨140706, by rfl⟩ : syracuseStep 1500869 = 281413) (by norm_num)
theorem B2164429 : Blo 1184409 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B1779413 : Blo 1184409 1779413 := bbase (se 7 (by rfl) ⟨20852, by rfl⟩ : syracuseStep 1779413 = 41705) (by norm_num)
theorem B2000605 : Blo 1184409 2000605 := bbase (se 3 (by rfl) ⟨375113, by rfl⟩ : syracuseStep 2000605 = 750227) (by norm_num)
theorem B3000037 : Blo 1184409 3000037 := bbase (se 4 (by rfl) ⟨281253, by rfl⟩ : syracuseStep 3000037 = 562507) (by norm_num)
theorem B1779437 : Blo 1184409 1779437 := bbase (se 3 (by rfl) ⟨333644, by rfl⟩ : syracuseStep 1779437 = 667289) (by norm_num)
theorem B1500925 : Blo 1184409 1500925 := bbase (se 3 (by rfl) ⟨281423, by rfl⟩ : syracuseStep 1500925 = 562847) (by norm_num)
theorem B1779461 : Blo 1184409 1779461 := bbase (se 4 (by rfl) ⟨166824, by rfl⟩ : syracuseStep 1779461 = 333649) (by norm_num)
theorem B3999509 : Blo 1184409 3999509 := bbase (se 6 (by rfl) ⟨93738, by rfl⟩ : syracuseStep 3999509 = 187477) (by norm_num)
theorem B1779485 : Blo 1184409 1779485 := bbase (se 3 (by rfl) ⟨333653, by rfl⟩ : syracuseStep 1779485 = 667307) (by norm_num)
theorem B5998373 : Blo 1184409 5998373 := bbase (se 4 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 5998373 = 1124695) (by norm_num)
theorem B1443625 : Blo 1184409 1443625 := bbase (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) (by norm_num)
theorem B2000693 : Blo 1184409 2000693 := bbase (se 5 (by rfl) ⟨93782, by rfl⟩ : syracuseStep 2000693 = 187565) (by norm_num)
theorem B1779509 : Blo 1184409 1779509 := bbase (se 5 (by rfl) ⟨83414, by rfl⟩ : syracuseStep 1779509 = 166829) (by norm_num)
theorem B1779533 : Blo 1184409 1779533 := bbase (se 3 (by rfl) ⟨333662, by rfl⟩ : syracuseStep 1779533 = 667325) (by norm_num)
theorem B3000149 : Blo 1184409 3000149 := bbase (se 9 (by rfl) ⟨8789, by rfl⟩ : syracuseStep 3000149 = 17579) (by norm_num)
theorem B1501021 : Blo 1184409 1501021 := bbase (se 3 (by rfl) ⟨281441, by rfl⟩ : syracuseStep 1501021 = 562883) (by norm_num)
theorem B1779557 : Blo 1184409 1779557 := bbase (se 4 (by rfl) ⟨166833, by rfl⟩ : syracuseStep 1779557 = 333667) (by norm_num)
theorem B1779581 : Blo 1184409 1779581 := bbase (se 3 (by rfl) ⟨333671, by rfl⟩ : syracuseStep 1779581 = 667343) (by norm_num)
theorem B1779605 : Blo 1184409 1779605 := bbase (se 6 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 1779605 = 83419) (by norm_num)
theorem B2000821 : Blo 1184409 2000821 := bbase (se 5 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 2000821 = 187577) (by norm_num)
theorem B1501193 : Blo 1184409 1501193 := bbase (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) (by norm_num)
theorem B2000909 : Blo 1184409 2000909 := bbase (se 3 (by rfl) ⟨375170, by rfl⟩ : syracuseStep 2000909 = 750341) (by norm_num)
theorem B3000341 : Blo 1184409 3000341 := bbase (se 6 (by rfl) ⟨70320, by rfl⟩ : syracuseStep 3000341 = 140641) (by norm_num)
theorem B3377173 : Blo 1184409 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B4802597 : Blo 1184409 4802597 := bbase (se 4 (by rfl) ⟨450243, by rfl⟩ : syracuseStep 4802597 = 900487) (by norm_num)
theorem B4499509 : Blo 1184409 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B5695541 : Blo 1184409 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B1501249 : Blo 1184409 1501249 := bbase (se 2 (by rfl) ⟨562968, by rfl⟩ : syracuseStep 1501249 = 1125937) (by norm_num)
theorem B2001037 : Blo 1184409 2001037 := bbase (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) (by norm_num)
theorem B2435221 : Blo 1184409 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B1501345 : Blo 1184409 1501345 := bbase (se 2 (by rfl) ⟨563004, by rfl⟩ : syracuseStep 1501345 = 1126009) (by norm_num)
theorem B3999941 : Blo 1184409 3999941 := bbase (se 4 (by rfl) ⟨374994, by rfl⟩ : syracuseStep 3999941 = 749989) (by norm_num)
theorem B2533589 : Blo 1184409 2533589 := bbase (se 7 (by rfl) ⟨29690, by rfl⟩ : syracuseStep 2533589 = 59381) (by norm_num)
theorem B2001125 : Blo 1184409 2001125 := bbase (se 4 (by rfl) ⟨187605, by rfl⟩ : syracuseStep 2001125 = 375211) (by norm_num)
theorem B4270357 : Blo 1184409 4270357 := bbase (se 6 (by rfl) ⟨100086, by rfl⟩ : syracuseStep 4270357 = 200173) (by norm_num)
theorem B1501517 : Blo 1184409 1501517 := bbase (se 3 (by rfl) ⟨281534, by rfl⟩ : syracuseStep 1501517 = 563069) (by norm_num)
theorem B2279773 : Blo 1184409 2279773 := bbase (se 3 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 2279773 = 854915) (by norm_num)
theorem B4499813 : Blo 1184409 4499813 := bbase (se 4 (by rfl) ⟨421857, by rfl⟩ : syracuseStep 4499813 = 843715) (by norm_num)
theorem B2001253 : Blo 1184409 2001253 := bbase (se 4 (by rfl) ⟨187617, by rfl⟩ : syracuseStep 2001253 = 375235) (by norm_num)
theorem B3000685 : Blo 1184409 3000685 := bbase (se 3 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 3000685 = 1125257) (by norm_num)
theorem B2001341 : Blo 1184409 2001341 := bbase (se 3 (by rfl) ⟨375251, by rfl⟩ : syracuseStep 2001341 = 750503) (by norm_num)
theorem B2533837 : Blo 1184409 2533837 := bbase (se 3 (by rfl) ⟨475094, by rfl⟩ : syracuseStep 2533837 = 950189) (by norm_num)
theorem B3000797 : Blo 1184409 3000797 := bbase (se 3 (by rfl) ⟨562649, by rfl⟩ : syracuseStep 3000797 = 1125299) (by norm_num)
theorem B10127861 : Blo 1184409 10127861 := bbase (se 5 (by rfl) ⟨474743, by rfl⟩ : syracuseStep 10127861 = 949487) (by norm_num)
theorem B2664989 : Blo 1184409 2664989 := bbase (se 3 (by rfl) ⟨499685, by rfl⟩ : syracuseStep 2664989 = 999371) (by norm_num)
theorem B2001469 : Blo 1184409 2001469 := bbase (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) (by norm_num)
theorem B2665061 : Blo 1184409 2665061 := bbase (se 4 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 2665061 = 499699) (by norm_num)
theorem B4000373 : Blo 1184409 4000373 := bbase (se 5 (by rfl) ⟨187517, by rfl⟩ : syracuseStep 4000373 = 375035) (by norm_num)
theorem B2026109 : Blo 1184409 2026109 := bbase (se 3 (by rfl) ⟨379895, by rfl⟩ : syracuseStep 2026109 = 759791) (by norm_num)
theorem B2001557 : Blo 1184409 2001557 := bbase (se 6 (by rfl) ⟨46911, by rfl⟩ : syracuseStep 2001557 = 93823) (by norm_num)
theorem B3000989 : Blo 1184409 3000989 := bbase (se 3 (by rfl) ⟨562685, by rfl⟩ : syracuseStep 3000989 = 1125371) (by norm_num)
theorem B2665133 : Blo 1184409 2665133 := bbase (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) (by norm_num)
theorem B2665205 : Blo 1184409 2665205 := bbase (se 5 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 2665205 = 249863) (by norm_num)
theorem B2001685 : Blo 1184409 2001685 := bbase (se 6 (by rfl) ⟨46914, by rfl⟩ : syracuseStep 2001685 = 93829) (by norm_num)
theorem B2665277 : Blo 1184409 2665277 := bbase (se 3 (by rfl) ⟨499739, by rfl⟩ : syracuseStep 2665277 = 999479) (by norm_num)
theorem B2001773 : Blo 1184409 2001773 := bbase (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) (by norm_num)
theorem B2665349 : Blo 1184409 2665349 := bbase (se 4 (by rfl) ⟨249876, by rfl⟩ : syracuseStep 2665349 = 499753) (by norm_num)
theorem B2665421 : Blo 1184409 2665421 := bbase (se 3 (by rfl) ⟨499766, by rfl⟩ : syracuseStep 2665421 = 999533) (by norm_num)
theorem B2001901 : Blo 1184409 2001901 := bbase (se 3 (by rfl) ⟨375356, by rfl⟩ : syracuseStep 2001901 = 750713) (by norm_num)
theorem B3001333 : Blo 1184409 3001333 := bbase (se 5 (by rfl) ⟨140687, by rfl⟩ : syracuseStep 3001333 = 281375) (by norm_num)
theorem B2665493 : Blo 1184409 2665493 := bbase (se 6 (by rfl) ⟨62472, by rfl⟩ : syracuseStep 2665493 = 124945) (by norm_num)
theorem B4000805 : Blo 1184409 4000805 := bbase (se 4 (by rfl) ⟨375075, by rfl⟩ : syracuseStep 4000805 = 750151) (by norm_num)
theorem B5999669 : Blo 1184409 5999669 := bbase (se 5 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 5999669 = 562469) (by norm_num)
theorem B2001989 : Blo 1184409 2001989 := bbase (se 4 (by rfl) ⟨187686, by rfl⟩ : syracuseStep 2001989 = 375373) (by norm_num)
theorem B6753365 : Blo 1184409 6753365 := bbase (se 8 (by rfl) ⟨39570, by rfl⟩ : syracuseStep 6753365 = 79141) (by norm_num)
theorem B2665565 : Blo 1184409 2665565 := bbase (se 3 (by rfl) ⟨499793, by rfl⟩ : syracuseStep 2665565 = 999587) (by norm_num)
theorem B3001445 : Blo 1184409 3001445 := bbase (se 4 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 3001445 = 562771) (by norm_num)
theorem B3378277 : Blo 1184409 3378277 := bbase (se 4 (by rfl) ⟨316713, by rfl⟩ : syracuseStep 3378277 = 633427) (by norm_num)
theorem B2845829 : Blo 1184409 2845829 := bbase (se 4 (by rfl) ⟨266796, by rfl⟩ : syracuseStep 2845829 = 533593) (by norm_num)
theorem B3083405 : Blo 1184409 3083405 := bbase (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) (by norm_num)
theorem B2665637 : Blo 1184409 2665637 := bbase (se 4 (by rfl) ⟨249903, by rfl⟩ : syracuseStep 2665637 = 499807) (by norm_num)
theorem B2845925 : Blo 1184409 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B2665709 : Blo 1184409 2665709 := bbase (se 3 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 2665709 = 999641) (by norm_num)
theorem B3001637 : Blo 1184409 3001637 := bbase (se 4 (by rfl) ⟨281403, by rfl⟩ : syracuseStep 3001637 = 562807) (by norm_num)
theorem B2665781 : Blo 1184409 2665781 := bbase (se 5 (by rfl) ⟨124958, by rfl⟩ : syracuseStep 2665781 = 249917) (by norm_num)
theorem B3042613 : Blo 1184409 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B1265005 : Blo 1184409 1265005 := bbase (se 3 (by rfl) ⟨237188, by rfl⟩ : syracuseStep 1265005 = 474377) (by norm_num)
theorem B5696885 : Blo 1184409 5696885 := bbase (se 5 (by rfl) ⟨267041, by rfl⟩ : syracuseStep 5696885 = 534083) (by norm_num)
theorem B2665853 : Blo 1184409 2665853 := bbase (se 3 (by rfl) ⟨499847, by rfl⟩ : syracuseStep 2665853 = 999695) (by norm_num)
theorem B2846117 : Blo 1184409 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B1265077 : Blo 1184409 1265077 := bbase (se 5 (by rfl) ⟨59300, by rfl⟩ : syracuseStep 1265077 = 118601) (by norm_num)
theorem B2665925 : Blo 1184409 2665925 := bbase (se 4 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 2665925 = 499861) (by norm_num)
theorem B4001237 : Blo 1184409 4001237 := bbase (se 7 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 4001237 = 93779) (by norm_num)
theorem B2665997 : Blo 1184409 2665997 := bbase (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) (by norm_num)
theorem B2666069 : Blo 1184409 2666069 := bbase (se 8 (by rfl) ⟨15621, by rfl⟩ : syracuseStep 2666069 = 31243) (by norm_num)
theorem B1265257 : Blo 1184409 1265257 := bbase (se 2 (by rfl) ⟨474471, by rfl⟩ : syracuseStep 1265257 = 948943) (by norm_num)
theorem B3001981 : Blo 1184409 3001981 := bbase (se 3 (by rfl) ⟨562871, by rfl⟩ : syracuseStep 3001981 = 1125743) (by norm_num)
theorem B5484181 : Blo 1184409 5484181 := bbase (se 6 (by rfl) ⟨128535, by rfl⟩ : syracuseStep 5484181 = 257071) (by norm_num)
theorem B2666141 : Blo 1184409 2666141 := bbase (se 3 (by rfl) ⟨499901, by rfl⟩ : syracuseStep 2666141 = 999803) (by norm_num)
theorem B2666213 : Blo 1184409 2666213 := bbase (se 4 (by rfl) ⟨249957, by rfl⟩ : syracuseStep 2666213 = 499915) (by norm_num)
theorem B3002093 : Blo 1184409 3002093 := bbase (se 3 (by rfl) ⟨562892, by rfl⟩ : syracuseStep 3002093 = 1125785) (by norm_num)
theorem B1601309 : Blo 1184409 1601309 := bbase (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) (by norm_num)
theorem B2666285 : Blo 1184409 2666285 := bbase (se 3 (by rfl) ⟨499928, by rfl⟩ : syracuseStep 2666285 = 999857) (by norm_num)
theorem B2666357 : Blo 1184409 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B4001669 : Blo 1184409 4001669 := bbase (se 4 (by rfl) ⟨375156, by rfl⟩ : syracuseStep 4001669 = 750313) (by norm_num)
theorem B3002285 : Blo 1184409 3002285 := bbase (se 3 (by rfl) ⟨562928, by rfl⟩ : syracuseStep 3002285 = 1125857) (by norm_num)
theorem B2666429 : Blo 1184409 2666429 := bbase (se 3 (by rfl) ⟨499955, by rfl⟩ : syracuseStep 2666429 = 999911) (by norm_num)
theorem B2248661 : Blo 1184409 2248661 := bbase (se 7 (by rfl) ⟨26351, by rfl⟩ : syracuseStep 2248661 = 52703) (by norm_num)
theorem B4558805 : Blo 1184409 4558805 := bbase (se 7 (by rfl) ⟨53423, by rfl⟩ : syracuseStep 4558805 = 106847) (by norm_num)
theorem B2666501 : Blo 1184409 2666501 := bbase (se 4 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 2666501 = 499969) (by norm_num)
theorem B1265701 : Blo 1184409 1265701 := bbase (se 4 (by rfl) ⟨118659, by rfl⟩ : syracuseStep 1265701 = 237319) (by norm_num)
theorem B2404397 : Blo 1184409 2404397 := bbase (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) (by norm_num)
theorem B2666573 : Blo 1184409 2666573 := bbase (se 3 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 2666573 = 999965) (by norm_num)
theorem B4329557 : Blo 1184409 4329557 := bbase (se 8 (by rfl) ⟨25368, by rfl⟩ : syracuseStep 4329557 = 50737) (by norm_num)
theorem B3797077 : Blo 1184409 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B2404453 : Blo 1184409 2404453 := bbase (se 4 (by rfl) ⟨225417, by rfl⟩ : syracuseStep 2404453 = 450835) (by norm_num)
theorem B2248813 : Blo 1184409 2248813 := bbase (se 3 (by rfl) ⟨421652, by rfl⟩ : syracuseStep 2248813 = 843305) (by norm_num)
theorem B5066869 : Blo 1184409 5066869 := bbase (se 5 (by rfl) ⟨237509, by rfl⟩ : syracuseStep 5066869 = 475019) (by norm_num)
theorem B2666645 : Blo 1184409 2666645 := bbase (se 6 (by rfl) ⟨62499, by rfl⟩ : syracuseStep 2666645 = 124999) (by norm_num)
theorem B2281621 : Blo 1184409 2281621 := bbase (se 6 (by rfl) ⟨53475, by rfl⟩ : syracuseStep 2281621 = 106951) (by norm_num)
theorem B1265825 : Blo 1184409 1265825 := bbase (se 2 (by rfl) ⟨474684, by rfl⟩ : syracuseStep 1265825 = 949369) (by norm_num)
theorem B25972949 : Blo 1184409 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B25628885 : Blo 1184409 25628885 := bbase (se 7 (by rfl) ⟨300338, by rfl⟩ : syracuseStep 25628885 = 600677) (by norm_num)
theorem B13693141 : Blo 1184409 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B2666717 : Blo 1184409 2666717 := bbase (se 3 (by rfl) ⟨500009, by rfl⟩ : syracuseStep 2666717 = 1000019) (by norm_num)
theorem B6754549 : Blo 1184409 6754549 := bbase (se 5 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 6754549 = 633239) (by norm_num)
theorem B3002629 : Blo 1184409 3002629 := bbase (se 4 (by rfl) ⟨281496, by rfl⟩ : syracuseStep 3002629 = 562993) (by norm_num)
theorem B7598357 : Blo 1184409 7598357 := bbase (se 6 (by rfl) ⟨178086, by rfl⟩ : syracuseStep 7598357 = 356173) (by norm_num)
theorem B2666789 : Blo 1184409 2666789 := bbase (se 4 (by rfl) ⟨250011, by rfl⟩ : syracuseStep 2666789 = 500023) (by norm_num)
theorem B8106293 : Blo 1184409 8106293 := bbase (se 5 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 8106293 = 759965) (by norm_num)
theorem B4002101 : Blo 1184409 4002101 := bbase (se 5 (by rfl) ⟨187598, by rfl⟩ : syracuseStep 4002101 = 375197) (by norm_num)
theorem B6000965 : Blo 1184409 6000965 := bbase (se 4 (by rfl) ⟨562590, by rfl⟩ : syracuseStep 6000965 = 1125181) (by norm_num)
theorem B13873493 : Blo 1184409 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B2666861 : Blo 1184409 2666861 := bbase (se 3 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 2666861 = 1000073) (by norm_num)
theorem B9613685 : Blo 1184409 9613685 := bbase (se 5 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 9613685 = 901283) (by norm_num)
theorem B3002741 : Blo 1184409 3002741 := bbase (se 5 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 3002741 = 281507) (by norm_num)
theorem B2281861 : Blo 1184409 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B2249117 : Blo 1184409 2249117 := bbase (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) (by norm_num)
theorem B1266077 : Blo 1184409 1266077 := bbase (se 3 (by rfl) ⟨237389, by rfl⟩ : syracuseStep 1266077 = 474779) (by norm_num)
theorem B4501925 : Blo 1184409 4501925 := bbase (se 4 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 4501925 = 844111) (by norm_num)
theorem B2666933 : Blo 1184409 2666933 := bbase (se 5 (by rfl) ⟨125012, by rfl⟩ : syracuseStep 2666933 = 250025) (by norm_num)
theorem B2667005 : Blo 1184409 2667005 := bbase (se 3 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 2667005 = 1000127) (by norm_num)
theorem B2437661 : Blo 1184409 2437661 := bbase (se 3 (by rfl) ⟨457061, by rfl⟩ : syracuseStep 2437661 = 914123) (by norm_num)
theorem B2847269 : Blo 1184409 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B3002933 : Blo 1184409 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B2667077 : Blo 1184409 2667077 := bbase (se 4 (by rfl) ⟨250038, by rfl⟩ : syracuseStep 2667077 = 500077) (by norm_num)
theorem B2667149 : Blo 1184409 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B2134717 : Blo 1184409 2134717 := bbase (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) (by norm_num)
theorem B4502213 : Blo 1184409 4502213 := bbase (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) (by norm_num)
theorem B8540885 : Blo 1184409 8540885 := bbase (se 7 (by rfl) ⟨100088, by rfl⟩ : syracuseStep 8540885 = 200177) (by norm_num)
theorem B2667221 : Blo 1184409 2667221 := bbase (se 7 (by rfl) ⟨31256, by rfl⟩ : syracuseStep 2667221 = 62513) (by norm_num)
theorem B4002533 : Blo 1184409 4002533 := bbase (se 4 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 4002533 = 750475) (by norm_num)
theorem B11383541 : Blo 1184409 11383541 := bbase (se 5 (by rfl) ⟨533603, by rfl⟩ : syracuseStep 11383541 = 1067207) (by norm_num)
theorem B17330965 : Blo 1184409 17330965 := bbase (se 6 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 17330965 = 812389) (by norm_num)
theorem B2667293 : Blo 1184409 2667293 := bbase (se 3 (by rfl) ⟨500117, by rfl⟩ : syracuseStep 2667293 = 1000235) (by norm_num)
theorem B2028325 : Blo 1184409 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B1200965 : Blo 1184409 1200965 := bbase (se 4 (by rfl) ⟨112590, by rfl⟩ : syracuseStep 1200965 = 225181) (by norm_num)
theorem B1266521 : Blo 1184409 1266521 := bbase (se 2 (by rfl) ⟨474945, by rfl⟩ : syracuseStep 1266521 = 949891) (by norm_num)
theorem B2667365 : Blo 1184409 2667365 := bbase (se 4 (by rfl) ⟨250065, by rfl⟩ : syracuseStep 2667365 = 500131) (by norm_num)
theorem B2667437 : Blo 1184409 2667437 := bbase (se 3 (by rfl) ⟨500144, by rfl⟩ : syracuseStep 2667437 = 1000289) (by norm_num)
theorem B1602509 : Blo 1184409 1602509 := bbase (se 3 (by rfl) ⟨300470, by rfl⟩ : syracuseStep 1602509 = 600941) (by norm_num)
theorem B1602541 : Blo 1184409 1602541 := bbase (se 3 (by rfl) ⟨300476, by rfl⟩ : syracuseStep 1602541 = 600953) (by norm_num)
theorem B2667509 : Blo 1184409 2667509 := bbase (se 5 (by rfl) ⟨125039, by rfl⟩ : syracuseStep 2667509 = 250079) (by norm_num)
theorem B2667581 : Blo 1184409 2667581 := bbase (se 3 (by rfl) ⟨500171, by rfl⟩ : syracuseStep 2667581 = 1000343) (by norm_num)
theorem B1266769 : Blo 1184409 1266769 := bbase (se 2 (by rfl) ⟨475038, by rfl⟩ : syracuseStep 1266769 = 950077) (by norm_num)
theorem B1250389 : Blo 1184409 1250389 := bbase (se 8 (by rfl) ⟨7326, by rfl⟩ : syracuseStep 1250389 = 14653) (by norm_num)
theorem B2667653 : Blo 1184409 2667653 := bbase (se 4 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 2667653 = 500185) (by norm_num)
theorem B2249869 : Blo 1184409 2249869 := bbase (se 3 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 2249869 = 843701) (by norm_num)
theorem B4002965 : Blo 1184409 4002965 := bbase (se 6 (by rfl) ⟨93819, by rfl⟩ : syracuseStep 4002965 = 187639) (by norm_num)
theorem B2667725 : Blo 1184409 2667725 := bbase (se 3 (by rfl) ⟨500198, by rfl⟩ : syracuseStep 2667725 = 1000397) (by norm_num)
theorem B1332481 : Blo 1184409 1332481 := bbase (se 2 (by rfl) ⟨499680, by rfl⟩ : syracuseStep 1332481 = 999361) (by norm_num)
theorem B2667797 : Blo 1184409 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B2250013 : Blo 1184409 2250013 := bbase (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) (by norm_num)
theorem B1332517 : Blo 1184409 1332517 := bbase (se 4 (by rfl) ⟨124923, by rfl⟩ : syracuseStep 1332517 = 249847) (by norm_num)
theorem B1332553 : Blo 1184409 1332553 := bbase (se 2 (by rfl) ⟨499707, by rfl⟩ : syracuseStep 1332553 = 999415) (by norm_num)
theorem B2667869 : Blo 1184409 2667869 := bbase (se 3 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 2667869 = 1000451) (by norm_num)
theorem B1332589 : Blo 1184409 1332589 := bbase (se 3 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 1332589 = 499721) (by norm_num)
theorem B1332625 : Blo 1184409 1332625 := bbase (se 2 (by rfl) ⟨499734, by rfl⟩ : syracuseStep 1332625 = 999469) (by norm_num)
theorem B1602973 : Blo 1184409 1602973 := bbase (se 3 (by rfl) ⟨300557, by rfl⟩ : syracuseStep 1602973 = 601115) (by norm_num)
theorem B2667941 : Blo 1184409 2667941 := bbase (se 4 (by rfl) ⟨250119, by rfl⟩ : syracuseStep 2667941 = 500239) (by norm_num)
theorem B1332661 : Blo 1184409 1332661 := bbase (se 5 (by rfl) ⟨62468, by rfl⟩ : syracuseStep 1332661 = 124937) (by norm_num)
theorem B2250173 : Blo 1184409 2250173 := bbase (se 3 (by rfl) ⟨421907, by rfl⟩ : syracuseStep 2250173 = 843815) (by norm_num)
theorem B1332697 : Blo 1184409 1332697 := bbase (se 2 (by rfl) ⟨499761, by rfl⟩ : syracuseStep 1332697 = 999523) (by norm_num)
theorem B1897949 : Blo 1184409 1897949 := bbase (se 3 (by rfl) ⟨355865, by rfl⟩ : syracuseStep 1897949 = 711731) (by norm_num)
theorem B2668013 : Blo 1184409 2668013 := bbase (se 3 (by rfl) ⟨500252, by rfl⟩ : syracuseStep 2668013 = 1000505) (by norm_num)
theorem B1332733 : Blo 1184409 1332733 := bbase (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) (by norm_num)
theorem B1283581 : Blo 1184409 1283581 := bbase (se 3 (by rfl) ⟨240671, by rfl⟩ : syracuseStep 1283581 = 481343) (by norm_num)
theorem B1332769 : Blo 1184409 1332769 := bbase (se 2 (by rfl) ⟨499788, by rfl⟩ : syracuseStep 1332769 = 999577) (by norm_num)
theorem B2668085 : Blo 1184409 2668085 := bbase (se 5 (by rfl) ⟨125066, by rfl⟩ : syracuseStep 2668085 = 250133) (by norm_num)
theorem B1332805 : Blo 1184409 1332805 := bbase (se 4 (by rfl) ⟨124950, by rfl⟩ : syracuseStep 1332805 = 249901) (by norm_num)
theorem B4003397 : Blo 1184409 4003397 := bbase (se 4 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 4003397 = 750637) (by norm_num)
theorem B2250317 : Blo 1184409 2250317 := bbase (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) (by norm_num)
theorem B4806229 : Blo 1184409 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B6002261 : Blo 1184409 6002261 := bbase (se 8 (by rfl) ⟨35169, by rfl⟩ : syracuseStep 6002261 = 70339) (by norm_num)
theorem B1898077 : Blo 1184409 1898077 := bbase (se 3 (by rfl) ⟨355889, by rfl⟩ : syracuseStep 1898077 = 711779) (by norm_num)
theorem B6084197 : Blo 1184409 6084197 := bbase (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) (by norm_num)
theorem B1332841 : Blo 1184409 1332841 := bbase (se 2 (by rfl) ⟨499815, by rfl⟩ : syracuseStep 1332841 = 999631) (by norm_num)
theorem B2668157 : Blo 1184409 2668157 := bbase (se 3 (by rfl) ⟨500279, by rfl⟩ : syracuseStep 2668157 = 1000559) (by norm_num)
theorem B1332877 : Blo 1184409 1332877 := bbase (se 3 (by rfl) ⟨249914, by rfl⟩ : syracuseStep 1332877 = 499829) (by norm_num)
theorem B1201825 : Blo 1184409 1201825 := bbase (se 2 (by rfl) ⟨450684, by rfl⟩ : syracuseStep 1201825 = 901369) (by norm_num)
theorem B5404325 : Blo 1184409 5404325 := bbase (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) (by norm_num)
theorem B1332913 : Blo 1184409 1332913 := bbase (se 2 (by rfl) ⟨499842, by rfl⟩ : syracuseStep 1332913 = 999685) (by norm_num)
theorem B2668229 : Blo 1184409 2668229 := bbase (se 4 (by rfl) ⟨250146, by rfl⟩ : syracuseStep 2668229 = 500293) (by norm_num)
theorem B1332949 : Blo 1184409 1332949 := bbase (se 7 (by rfl) ⟨15620, by rfl⟩ : syracuseStep 1332949 = 31241) (by norm_num)
theorem B1332985 : Blo 1184409 1332985 := bbase (se 2 (by rfl) ⟨499869, by rfl⟩ : syracuseStep 1332985 = 999739) (by norm_num)
theorem B2668301 : Blo 1184409 2668301 := bbase (se 3 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 2668301 = 1000613) (by norm_num)
theorem B1333021 : Blo 1184409 1333021 := bbase (se 3 (by rfl) ⟨249941, by rfl⟩ : syracuseStep 1333021 = 499883) (by norm_num)
theorem B1333057 : Blo 1184409 1333057 := bbase (se 2 (by rfl) ⟨499896, by rfl⟩ : syracuseStep 1333057 = 999793) (by norm_num)
theorem B2668373 : Blo 1184409 2668373 := bbase (se 9 (by rfl) ⟨7817, by rfl⟩ : syracuseStep 2668373 = 15635) (by norm_num)
theorem B9008981 : Blo 1184409 9008981 := bbase (se 9 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 9008981 = 52787) (by norm_num)
theorem B1333093 : Blo 1184409 1333093 := bbase (se 4 (by rfl) ⟨124977, by rfl⟩ : syracuseStep 1333093 = 249955) (by norm_num)
theorem B4503397 : Blo 1184409 4503397 := bbase (se 4 (by rfl) ⟨422193, by rfl⟩ : syracuseStep 4503397 = 844387) (by norm_num)
theorem B2250605 : Blo 1184409 2250605 := bbase (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) (by norm_num)
theorem B1333129 : Blo 1184409 1333129 := bbase (se 2 (by rfl) ⟨499923, by rfl⟩ : syracuseStep 1333129 = 999847) (by norm_num)
theorem B2135965 : Blo 1184409 2135965 := bbase (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) (by norm_num)
theorem B2668445 : Blo 1184409 2668445 := bbase (se 3 (by rfl) ⟨500333, by rfl⟩ : syracuseStep 2668445 = 1000667) (by norm_num)
theorem B1333165 : Blo 1184409 1333165 := bbase (se 3 (by rfl) ⟨249968, by rfl⟩ : syracuseStep 1333165 = 499937) (by norm_num)
theorem B1423289 : Blo 1184409 1423289 := bbase (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) (by norm_num)
theorem B1333201 : Blo 1184409 1333201 := bbase (se 2 (by rfl) ⟨499950, by rfl⟩ : syracuseStep 1333201 = 999901) (by norm_num)
theorem B2668517 : Blo 1184409 2668517 := bbase (se 4 (by rfl) ⟨250173, by rfl⟩ : syracuseStep 2668517 = 500347) (by norm_num)
theorem B1333237 : Blo 1184409 1333237 := bbase (se 5 (by rfl) ⟨62495, by rfl⟩ : syracuseStep 1333237 = 124991) (by norm_num)
theorem B4003829 : Blo 1184409 4003829 := bbase (se 5 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 4003829 = 375359) (by norm_num)
theorem B2250757 : Blo 1184409 2250757 := bbase (se 4 (by rfl) ⟨211008, by rfl⟩ : syracuseStep 2250757 = 422017) (by norm_num)
theorem B1333273 : Blo 1184409 1333273 := bbase (se 2 (by rfl) ⟨499977, by rfl⟩ : syracuseStep 1333273 = 999955) (by norm_num)
theorem B2668589 : Blo 1184409 2668589 := bbase (se 3 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 2668589 = 1000721) (by norm_num)
theorem B1333309 : Blo 1184409 1333309 := bbase (se 3 (by rfl) ⟨249995, by rfl⟩ : syracuseStep 1333309 = 499991) (by norm_num)
theorem B1333345 : Blo 1184409 1333345 := bbase (se 2 (by rfl) ⟨500004, by rfl⟩ : syracuseStep 1333345 = 1000009) (by norm_num)
theorem B2668661 : Blo 1184409 2668661 := bbase (se 5 (by rfl) ⟨125093, by rfl⟩ : syracuseStep 2668661 = 250187) (by norm_num)
theorem B1333381 : Blo 1184409 1333381 := bbase (se 4 (by rfl) ⟨125004, by rfl⟩ : syracuseStep 1333381 = 250009) (by norm_num)
theorem B9615509 : Blo 1184409 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B4503701 : Blo 1184409 4503701 := bbase (se 6 (by rfl) ⟨105555, by rfl⟩ : syracuseStep 4503701 = 211111) (by norm_num)
theorem B1333417 : Blo 1184409 1333417 := bbase (se 2 (by rfl) ⟨500031, by rfl⟩ : syracuseStep 1333417 = 1000063) (by norm_num)
theorem B6756533 : Blo 1184409 6756533 := bbase (se 5 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 6756533 = 633425) (by norm_num)
theorem B2668733 : Blo 1184409 2668733 := bbase (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) (by norm_num)
theorem B1333453 : Blo 1184409 1333453 := bbase (se 3 (by rfl) ⟨250022, by rfl⟩ : syracuseStep 1333453 = 500045) (by norm_num)
theorem B46807253 : Blo 1184409 46807253 := bbase (se 7 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 46807253 = 1097045) (by norm_num)
theorem B1423597 : Blo 1184409 1423597 := bbase (se 3 (by rfl) ⟨266924, by rfl⟩ : syracuseStep 1423597 = 533849) (by norm_num)
theorem B1333489 : Blo 1184409 1333489 := bbase (se 2 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 1333489 = 1000117) (by norm_num)
theorem B9001205 : Blo 1184409 9001205 := bbase (se 5 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 9001205 = 843863) (by norm_num)
theorem B2668805 : Blo 1184409 2668805 := bbase (se 4 (by rfl) ⟨250200, by rfl⟩ : syracuseStep 2668805 = 500401) (by norm_num)
theorem B1333525 : Blo 1184409 1333525 := bbase (se 6 (by rfl) ⟨31254, by rfl⟩ : syracuseStep 1333525 = 62509) (by norm_num)
theorem B2251061 : Blo 1184409 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B1333561 : Blo 1184409 1333561 := bbase (se 2 (by rfl) ⟨500085, by rfl⟩ : syracuseStep 1333561 = 1000171) (by norm_num)
theorem B1423693 : Blo 1184409 1423693 := bbase (se 3 (by rfl) ⟨266942, by rfl⟩ : syracuseStep 1423693 = 533885) (by norm_num)
theorem B2668877 : Blo 1184409 2668877 := bbase (se 3 (by rfl) ⟨500414, by rfl⟩ : syracuseStep 2668877 = 1000829) (by norm_num)
theorem B10819925 : Blo 1184409 10819925 := bbase (se 10 (by rfl) ⟨15849, by rfl⟩ : syracuseStep 10819925 = 31699) (by norm_num)
theorem B1333597 : Blo 1184409 1333597 := bbase (se 3 (by rfl) ⟨250049, by rfl⟩ : syracuseStep 1333597 = 500099) (by norm_num)
theorem B1333633 : Blo 1184409 1333633 := bbase (se 2 (by rfl) ⟨500112, by rfl⟩ : syracuseStep 1333633 = 1000225) (by norm_num)
theorem B2668949 : Blo 1184409 2668949 := bbase (se 6 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 2668949 = 125107) (by norm_num)
theorem B8550805 : Blo 1184409 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B1333669 : Blo 1184409 1333669 := bbase (se 4 (by rfl) ⟨125031, by rfl⟩ : syracuseStep 1333669 = 250063) (by norm_num)
theorem B1333705 : Blo 1184409 1333705 := bbase (se 2 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 1333705 = 1000279) (by norm_num)
theorem B1268177 : Blo 1184409 1268177 := bbase (se 2 (by rfl) ⟨475566, by rfl⟩ : syracuseStep 1268177 = 951133) (by norm_num)
theorem B2669021 : Blo 1184409 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B1333741 : Blo 1184409 1333741 := bbase (se 3 (by rfl) ⟨250076, by rfl⟩ : syracuseStep 1333741 = 500153) (by norm_num)
theorem B2849269 : Blo 1184409 2849269 := bbase (se 5 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 2849269 = 267119) (by norm_num)
theorem B2529805 : Blo 1184409 2529805 := bbase (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) (by norm_num)
theorem B1333777 : Blo 1184409 1333777 := bbase (se 2 (by rfl) ⟨500166, by rfl⟩ : syracuseStep 1333777 = 1000333) (by norm_num)
theorem B2669093 : Blo 1184409 2669093 := bbase (se 4 (by rfl) ⟨250227, by rfl⟩ : syracuseStep 2669093 = 500455) (by norm_num)
theorem B1333813 : Blo 1184409 1333813 := bbase (se 5 (by rfl) ⟨62522, by rfl⟩ : syracuseStep 1333813 = 125045) (by norm_num)
theorem B2849365 : Blo 1184409 2849365 := bbase (se 8 (by rfl) ⟨16695, by rfl⟩ : syracuseStep 2849365 = 33391) (by norm_num)
theorem B1333849 : Blo 1184409 1333849 := bbase (se 2 (by rfl) ⟨500193, by rfl⟩ : syracuseStep 1333849 = 1000387) (by norm_num)
theorem B1423981 : Blo 1184409 1423981 := bbase (se 3 (by rfl) ⟨266996, by rfl⟩ : syracuseStep 1423981 = 533993) (by norm_num)
theorem B2669165 : Blo 1184409 2669165 := bbase (se 3 (by rfl) ⟨500468, by rfl⟩ : syracuseStep 2669165 = 1000937) (by norm_num)
theorem B1333885 : Blo 1184409 1333885 := bbase (se 3 (by rfl) ⟨250103, by rfl⟩ : syracuseStep 1333885 = 500207) (by norm_num)
theorem B2529949 : Blo 1184409 2529949 := bbase (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) (by norm_num)
theorem B1333921 : Blo 1184409 1333921 := bbase (se 2 (by rfl) ⟨500220, by rfl⟩ : syracuseStep 1333921 = 1000441) (by norm_num)
theorem B2669237 : Blo 1184409 2669237 := bbase (se 5 (by rfl) ⟨125120, by rfl⟩ : syracuseStep 2669237 = 250241) (by norm_num)
theorem B1333957 : Blo 1184409 1333957 := bbase (se 4 (by rfl) ⟨125058, by rfl⟩ : syracuseStep 1333957 = 250117) (by norm_num)
theorem B1333993 : Blo 1184409 1333993 := bbase (se 2 (by rfl) ⟨500247, by rfl⟩ : syracuseStep 1333993 = 1000495) (by norm_num)
theorem B2669309 : Blo 1184409 2669309 := bbase (se 3 (by rfl) ⟨500495, by rfl⟩ : syracuseStep 2669309 = 1000991) (by norm_num)
theorem B1334029 : Blo 1184409 1334029 := bbase (se 3 (by rfl) ⟨250130, by rfl⟩ : syracuseStep 1334029 = 500261) (by norm_num)
theorem B1424173 : Blo 1184409 1424173 := bbase (se 3 (by rfl) ⟨267032, by rfl⟩ : syracuseStep 1424173 = 534065) (by norm_num)
theorem B1334065 : Blo 1184409 1334065 := bbase (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) (by norm_num)
theorem B2669381 : Blo 1184409 2669381 := bbase (se 4 (by rfl) ⟨250254, by rfl⟩ : syracuseStep 2669381 = 500509) (by norm_num)
theorem B1334101 : Blo 1184409 1334101 := bbase (se 9 (by rfl) ⟨3908, by rfl⟩ : syracuseStep 1334101 = 7817) (by norm_num)
theorem B6003557 : Blo 1184409 6003557 := bbase (se 4 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 6003557 = 1125667) (by norm_num)
theorem B1334137 : Blo 1184409 1334137 := bbase (se 2 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 1334137 = 1000603) (by norm_num)
theorem B9124757 : Blo 1184409 9124757 := bbase (se 6 (by rfl) ⟨213861, by rfl⟩ : syracuseStep 9124757 = 427723) (by norm_num)
theorem B1334173 : Blo 1184409 1334173 := bbase (se 3 (by rfl) ⟨250157, by rfl⟩ : syracuseStep 1334173 = 500315) (by norm_num)
theorem B3799973 : Blo 1184409 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B1334209 : Blo 1184409 1334209 := bbase (se 2 (by rfl) ⟨500328, by rfl⟩ : syracuseStep 1334209 = 1000657) (by norm_num)
theorem B1899461 : Blo 1184409 1899461 := bbase (se 4 (by rfl) ⟨178074, by rfl⟩ : syracuseStep 1899461 = 356149) (by norm_num)
theorem B1334245 : Blo 1184409 1334245 := bbase (se 4 (by rfl) ⟨125085, by rfl⟩ : syracuseStep 1334245 = 250171) (by norm_num)
theorem B1776629 : Blo 1184409 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B6085637 : Blo 1184409 6085637 := bbase (se 4 (by rfl) ⟨570528, by rfl⟩ : syracuseStep 6085637 = 1141057) (by norm_num)
theorem B5700613 : Blo 1184409 5700613 := bbase (se 4 (by rfl) ⟨534432, by rfl⟩ : syracuseStep 5700613 = 1068865) (by norm_num)
theorem B1334281 : Blo 1184409 1334281 := bbase (se 2 (by rfl) ⟨500355, by rfl⟩ : syracuseStep 1334281 = 1000711) (by norm_num)
theorem B1776653 : Blo 1184409 1776653 := bbase (se 3 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 1776653 = 666245) (by norm_num)
theorem B2530325 : Blo 1184409 2530325 := bbase (se 6 (by rfl) ⟨59304, by rfl⟩ : syracuseStep 2530325 = 118609) (by norm_num)
theorem B1776677 : Blo 1184409 1776677 := bbase (se 4 (by rfl) ⟨166563, by rfl⟩ : syracuseStep 1776677 = 333127) (by norm_num)
theorem B2251813 : Blo 1184409 2251813 := bbase (se 4 (by rfl) ⟨211107, by rfl⟩ : syracuseStep 2251813 = 422215) (by norm_num)
theorem B1334317 : Blo 1184409 1334317 := bbase (se 3 (by rfl) ⟨250184, by rfl⟩ : syracuseStep 1334317 = 500369) (by norm_num)
theorem B1776701 : Blo 1184409 1776701 := bbase (se 3 (by rfl) ⟨333131, by rfl⟩ : syracuseStep 1776701 = 666263) (by norm_num)
theorem B1334353 : Blo 1184409 1334353 := bbase (se 2 (by rfl) ⟨500382, by rfl⟩ : syracuseStep 1334353 = 1000765) (by norm_num)
theorem B1776725 : Blo 1184409 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B1776749 : Blo 1184409 1776749 := bbase (se 3 (by rfl) ⟨333140, by rfl⟩ : syracuseStep 1776749 = 666281) (by norm_num)
theorem B1334389 : Blo 1184409 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B1776773 : Blo 1184409 1776773 := bbase (se 4 (by rfl) ⟨166572, by rfl⟩ : syracuseStep 1776773 = 333145) (by norm_num)
theorem B1334425 : Blo 1184409 1334425 := bbase (se 2 (by rfl) ⟨500409, by rfl⟩ : syracuseStep 1334425 = 1000819) (by norm_num)
theorem B1776797 : Blo 1184409 1776797 := bbase (se 3 (by rfl) ⟨333149, by rfl⟩ : syracuseStep 1776797 = 666299) (by norm_num)
theorem B5061797 : Blo 1184409 5061797 := bbase (se 4 (by rfl) ⟨474543, by rfl⟩ : syracuseStep 5061797 = 949087) (by norm_num)
theorem B1686701 : Blo 1184409 1686701 := bbase (se 3 (by rfl) ⟨316256, by rfl⟩ : syracuseStep 1686701 = 632513) (by norm_num)
theorem B1776821 : Blo 1184409 1776821 := bbase (se 5 (by rfl) ⟨83288, by rfl⟩ : syracuseStep 1776821 = 166577) (by norm_num)
theorem B2251957 : Blo 1184409 2251957 := bbase (se 5 (by rfl) ⟨105560, by rfl⟩ : syracuseStep 2251957 = 211121) (by norm_num)
theorem B1334461 : Blo 1184409 1334461 := bbase (se 3 (by rfl) ⟨250211, by rfl⟩ : syracuseStep 1334461 = 500423) (by norm_num)
theorem B1776845 : Blo 1184409 1776845 := bbase (se 3 (by rfl) ⟨333158, by rfl⟩ : syracuseStep 1776845 = 666317) (by norm_num)
theorem B1334497 : Blo 1184409 1334497 := bbase (se 2 (by rfl) ⟨500436, by rfl⟩ : syracuseStep 1334497 = 1000873) (by norm_num)
theorem B1776869 : Blo 1184409 1776869 := bbase (se 4 (by rfl) ⟨166581, by rfl⟩ : syracuseStep 1776869 = 333163) (by norm_num)
theorem B1776893 : Blo 1184409 1776893 := bbase (se 3 (by rfl) ⟨333167, by rfl⟩ : syracuseStep 1776893 = 666335) (by norm_num)
theorem B1686781 : Blo 1184409 1686781 := bbase (se 3 (by rfl) ⟨316271, by rfl⟩ : syracuseStep 1686781 = 632543) (by norm_num)
theorem B2137349 : Blo 1184409 2137349 := bbase (se 4 (by rfl) ⟨200376, by rfl⟩ : syracuseStep 2137349 = 400753) (by norm_num)
theorem B1334533 : Blo 1184409 1334533 := bbase (se 4 (by rfl) ⟨125112, by rfl⟩ : syracuseStep 1334533 = 250225) (by norm_num)
theorem B1776917 : Blo 1184409 1776917 := bbase (se 6 (by rfl) ⟨41646, by rfl⟩ : syracuseStep 1776917 = 83293) (by norm_num)
theorem B5692693 : Blo 1184409 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B1334569 : Blo 1184409 1334569 := bbase (se 2 (by rfl) ⟨500463, by rfl⟩ : syracuseStep 1334569 = 1000927) (by norm_num)
theorem B1776941 : Blo 1184409 1776941 := bbase (se 3 (by rfl) ⟨333176, by rfl⟩ : syracuseStep 1776941 = 666353) (by norm_num)
theorem B1776965 : Blo 1184409 1776965 := bbase (se 4 (by rfl) ⟨166590, by rfl⟩ : syracuseStep 1776965 = 333181) (by norm_num)
theorem B3374405 : Blo 1184409 3374405 := bbase (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) (by norm_num)
theorem B1334605 : Blo 1184409 1334605 := bbase (se 3 (by rfl) ⟨250238, by rfl⟩ : syracuseStep 1334605 = 500477) (by norm_num)
theorem B17096021 : Blo 1184409 17096021 := bbase (se 11 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 17096021 = 25043) (by norm_num)
theorem B2252117 : Blo 1184409 2252117 := bbase (se 11 (by rfl) ⟨1649, by rfl⟩ : syracuseStep 2252117 = 3299) (by norm_num)
theorem B1776989 : Blo 1184409 1776989 := bbase (se 3 (by rfl) ⟨333185, by rfl⟩ : syracuseStep 1776989 = 666371) (by norm_num)
theorem B1334641 : Blo 1184409 1334641 := bbase (se 2 (by rfl) ⟨500490, by rfl⟩ : syracuseStep 1334641 = 1000981) (by norm_num)
theorem B1777013 : Blo 1184409 1777013 := bbase (se 5 (by rfl) ⟨83297, by rfl⟩ : syracuseStep 1777013 = 166595) (by norm_num)
theorem B1686901 : Blo 1184409 1686901 := bbase (se 5 (by rfl) ⟨79073, by rfl⟩ : syracuseStep 1686901 = 158147) (by norm_num)
theorem B2530693 : Blo 1184409 2530693 := bbase (se 4 (by rfl) ⟨237252, by rfl⟩ : syracuseStep 2530693 = 474505) (by norm_num)
theorem B1777037 : Blo 1184409 1777037 := bbase (se 3 (by rfl) ⟨333194, by rfl⟩ : syracuseStep 1777037 = 666389) (by norm_num)
theorem B1334677 : Blo 1184409 1334677 := bbase (se 6 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 1334677 = 62563) (by norm_num)
theorem B1777061 : Blo 1184409 1777061 := bbase (se 4 (by rfl) ⟨166599, by rfl⟩ : syracuseStep 1777061 = 333199) (by norm_num)
theorem B1777085 : Blo 1184409 1777085 := bbase (se 3 (by rfl) ⟨333203, by rfl⟩ : syracuseStep 1777085 = 666407) (by norm_num)
theorem B5062085 : Blo 1184409 5062085 := bbase (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) (by norm_num)
theorem B1777109 : Blo 1184409 1777109 := bbase (se 7 (by rfl) ⟨20825, by rfl⟩ : syracuseStep 1777109 = 41651) (by norm_num)
theorem B1686997 : Blo 1184409 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B2252261 : Blo 1184409 2252261 := bbase (se 4 (by rfl) ⟨211149, by rfl⟩ : syracuseStep 2252261 = 422299) (by norm_num)
theorem B1777133 : Blo 1184409 1777133 := bbase (se 3 (by rfl) ⟨333212, by rfl⟩ : syracuseStep 1777133 = 666425) (by norm_num)
theorem B1777157 : Blo 1184409 1777157 := bbase (se 4 (by rfl) ⟨166608, by rfl⟩ : syracuseStep 1777157 = 333217) (by norm_num)
theorem B1777181 : Blo 1184409 1777181 := bbase (se 3 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 1777181 = 666443) (by norm_num)
theorem B1777205 : Blo 1184409 1777205 := bbase (se 5 (by rfl) ⟨83306, by rfl⟩ : syracuseStep 1777205 = 166613) (by norm_num)
theorem B1777229 : Blo 1184409 1777229 := bbase (se 3 (by rfl) ⟨333230, by rfl⟩ : syracuseStep 1777229 = 666461) (by norm_num)
theorem B1777253 : Blo 1184409 1777253 := bbase (se 4 (by rfl) ⟨166617, by rfl⟩ : syracuseStep 1777253 = 333235) (by norm_num)
theorem B1777277 : Blo 1184409 1777277 := bbase (se 3 (by rfl) ⟨333239, by rfl⟩ : syracuseStep 1777277 = 666479) (by norm_num)
theorem B1777301 : Blo 1184409 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B1425053 : Blo 1184409 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B2850461 : Blo 1184409 2850461 := bbase (se 3 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 2850461 = 1068923) (by norm_num)
theorem B1777325 : Blo 1184409 1777325 := bbase (se 3 (by rfl) ⟨333248, by rfl⟩ : syracuseStep 1777325 = 666497) (by norm_num)
theorem B1777349 : Blo 1184409 1777349 := bbase (se 4 (by rfl) ⟨166626, by rfl⟩ : syracuseStep 1777349 = 333253) (by norm_num)
theorem B1777373 : Blo 1184409 1777373 := bbase (se 3 (by rfl) ⟨333257, by rfl⟩ : syracuseStep 1777373 = 666515) (by norm_num)
theorem B1777397 : Blo 1184409 1777397 := bbase (se 5 (by rfl) ⟨83315, by rfl⟩ : syracuseStep 1777397 = 166631) (by norm_num)
theorem B1777421 : Blo 1184409 1777421 := bbase (se 3 (by rfl) ⟨333266, by rfl⟩ : syracuseStep 1777421 = 666533) (by norm_num)
theorem B1777445 : Blo 1184409 1777445 := bbase (se 4 (by rfl) ⟨166635, by rfl⟩ : syracuseStep 1777445 = 333271) (by norm_num)
theorem B1777469 : Blo 1184409 1777469 := bbase (se 3 (by rfl) ⟨333275, by rfl⟩ : syracuseStep 1777469 = 666551) (by norm_num)
theorem B2998093 : Blo 1184409 2998093 := bbase (se 3 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 2998093 = 1124285) (by norm_num)
theorem B1777493 : Blo 1184409 1777493 := bbase (se 9 (by rfl) ⟨5207, by rfl⟩ : syracuseStep 1777493 = 10415) (by norm_num)
theorem B1777517 : Blo 1184409 1777517 := bbase (se 3 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 1777517 = 666569) (by norm_num)
theorem B1900397 : Blo 1184409 1900397 := bbase (se 3 (by rfl) ⟨356324, by rfl⟩ : syracuseStep 1900397 = 712649) (by norm_num)
theorem B1777541 : Blo 1184409 1777541 := bbase (se 4 (by rfl) ⟨166644, by rfl⟩ : syracuseStep 1777541 = 333289) (by norm_num)
theorem B1998749 : Blo 1184409 1998749 := bbase (se 3 (by rfl) ⟨374765, by rfl⟩ : syracuseStep 1998749 = 749531) (by norm_num)
theorem B1777565 : Blo 1184409 1777565 := bbase (se 3 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 1777565 = 666587) (by norm_num)
theorem B1777589 : Blo 1184409 1777589 := bbase (se 5 (by rfl) ⟨83324, by rfl⟩ : syracuseStep 1777589 = 166649) (by norm_num)
theorem B12173237 : Blo 1184409 12173237 := bbase (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) (by norm_num)
theorem B2998205 : Blo 1184409 2998205 := bbase (se 3 (by rfl) ⟨562163, by rfl⟩ : syracuseStep 2998205 = 1124327) (by norm_num)
theorem B1499077 : Blo 1184409 1499077 := bbase (se 4 (by rfl) ⟨140538, by rfl⟩ : syracuseStep 1499077 = 281077) (by norm_num)
theorem B1687493 : Blo 1184409 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B1777613 : Blo 1184409 1777613 := bbase (se 3 (by rfl) ⟨333302, by rfl⟩ : syracuseStep 1777613 = 666605) (by norm_num)
theorem B1777637 : Blo 1184409 1777637 := bbase (se 4 (by rfl) ⟨166653, by rfl⟩ : syracuseStep 1777637 = 333307) (by norm_num)
theorem B1777661 : Blo 1184409 1777661 := bbase (se 3 (by rfl) ⟨333311, by rfl⟩ : syracuseStep 1777661 = 666623) (by norm_num)
theorem B1777667 : Blo 1184409 1777667 := bstep (se 1 (by rfl) ⟨1333250, by rfl⟩ : syracuseStep 1777667 = 2666501) B2666501
theorem B1777697 : Blo 1184409 1777697 := bstep (se 2 (by rfl) ⟨666636, by rfl⟩ : syracuseStep 1777697 = 1333273) B1333273
theorem B1687601 : Blo 1184409 1687601 := bstep (se 2 (by rfl) ⟨632850, by rfl⟩ : syracuseStep 1687601 = 1265701) B1265701
theorem B1777715 : Blo 1184409 1777715 := bstep (se 1 (by rfl) ⟨1333286, by rfl⟩ : syracuseStep 1777715 = 2666573) B2666573
theorem B1777745 : Blo 1184409 1777745 := bstep (se 2 (by rfl) ⟨666654, by rfl⟩ : syracuseStep 1777745 = 1333309) B1333309
theorem B1998931 : Blo 1184409 1998931 := bstep (se 1 (by rfl) ⟨1499198, by rfl⟩ : syracuseStep 1998931 = 2998397) B2998397
theorem B1777763 : Blo 1184409 1777763 := bstep (se 1 (by rfl) ⟨1333322, by rfl⟩ : syracuseStep 1777763 = 2666645) B2666645
theorem B5062769 : Blo 1184409 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B1777793 : Blo 1184409 1777793 := bstep (se 2 (by rfl) ⟨666672, by rfl⟩ : syracuseStep 1777793 = 1333345) B1333345
theorem B9003149 : Blo 1184409 9003149 := bstep (se 3 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 9003149 = 3376181) B3376181
theorem B2998417 : Blo 1184409 2998417 := bstep (se 2 (by rfl) ⟨1124406, by rfl⟩ : syracuseStep 2998417 = 2248813) B2248813
theorem B1777811 : Blo 1184409 1777811 := bstep (se 1 (by rfl) ⟨1333358, by rfl⟩ : syracuseStep 1777811 = 2666717) B2666717
theorem B1777841 : Blo 1184409 1777841 := bstep (se 2 (by rfl) ⟨666690, by rfl⟩ : syracuseStep 1777841 = 1333381) B1333381
theorem B1777859 : Blo 1184409 1777859 := bstep (se 1 (by rfl) ⟨1333394, by rfl⟩ : syracuseStep 1777859 = 2666789) B2666789
theorem B1999073 : Blo 1184409 1999073 := bstep (se 2 (by rfl) ⟨749652, by rfl⟩ : syracuseStep 1999073 = 1499305) B1499305
theorem B1777889 : Blo 1184409 1777889 := bstep (se 2 (by rfl) ⟨666708, by rfl⟩ : syracuseStep 1777889 = 1333417) B1333417
theorem B9248995 : Blo 1184409 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B6750449 : Blo 1184409 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B1777907 : Blo 1184409 1777907 := bstep (se 1 (by rfl) ⟨1333430, by rfl⟩ : syracuseStep 1777907 = 2666861) B2666861
theorem B1777937 : Blo 1184409 1777937 := bstep (se 2 (by rfl) ⟨666726, by rfl⟩ : syracuseStep 1777937 = 1333453) B1333453
theorem B1499411 : Blo 1184409 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B1777955 : Blo 1184409 1777955 := bstep (se 1 (by rfl) ⟨1333466, by rfl⟩ : syracuseStep 1777955 = 2666933) B2666933
theorem B3997997 : Blo 1184409 3997997 := bstep (se 3 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 3997997 = 1499249) B1499249
theorem B1777985 : Blo 1184409 1777985 := bstep (se 2 (by rfl) ⟨666744, by rfl⟩ : syracuseStep 1777985 = 1333489) B1333489
theorem B1778003 : Blo 1184409 1778003 := bstep (se 1 (by rfl) ⟨1333502, by rfl⟩ : syracuseStep 1778003 = 2667005) B2667005
theorem B1999201 : Blo 1184409 1999201 := bstep (se 2 (by rfl) ⟨749700, by rfl⟩ : syracuseStep 1999201 = 1499401) B1499401
theorem B3998051 : Blo 1184409 3998051 := bstep (se 1 (by rfl) ⟨2998538, by rfl⟩ : syracuseStep 3998051 = 5997077) B5997077
theorem B5693809 : Blo 1184409 5693809 := bstep (se 2 (by rfl) ⟨2135178, by rfl⟩ : syracuseStep 5693809 = 4270357) B4270357
theorem B1778033 : Blo 1184409 1778033 := bstep (se 2 (by rfl) ⟨666762, by rfl⟩ : syracuseStep 1778033 = 1333525) B1333525
theorem B1999235 : Blo 1184409 1999235 := bstep (se 1 (by rfl) ⟨1499426, by rfl⟩ : syracuseStep 1999235 = 2998853) B2998853
theorem B1778051 : Blo 1184409 1778051 := bstep (se 1 (by rfl) ⟨1333538, by rfl⟩ : syracuseStep 1778051 = 2667077) B2667077
theorem B1778081 : Blo 1184409 1778081 := bstep (se 2 (by rfl) ⟨666780, by rfl⟩ : syracuseStep 1778081 = 1333561) B1333561
theorem B2998691 : Blo 1184409 2998691 := bstep (se 1 (by rfl) ⟨2249018, by rfl⟩ : syracuseStep 2998691 = 4498037) B4498037
theorem B3375533 : Blo 1184409 3375533 := bstep (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) B1265825
theorem B1778099 : Blo 1184409 1778099 := bstep (se 1 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 1778099 = 2667149) B2667149
theorem B6668741 : Blo 1184409 6668741 := bstep (se 4 (by rfl) ⟨625194, by rfl⟩ : syracuseStep 6668741 = 1250389) B1250389
theorem B4497869 : Blo 1184409 4497869 := bstep (se 3 (by rfl) ⟨843350, by rfl⟩ : syracuseStep 4497869 = 1686701) B1686701
theorem B3039697 : Blo 1184409 3039697 := bstep (se 2 (by rfl) ⟨1139886, by rfl⟩ : syracuseStep 3039697 = 2279773) B2279773
theorem B1778129 : Blo 1184409 1778129 := bstep (se 2 (by rfl) ⟨666798, by rfl⟩ : syracuseStep 1778129 = 1333597) B1333597
theorem B5693923 : Blo 1184409 5693923 := bstep (se 1 (by rfl) ⟨4270442, by rfl⟩ : syracuseStep 5693923 = 8540885) B8540885
theorem B1778147 : Blo 1184409 1778147 := bstep (se 1 (by rfl) ⟨1333610, by rfl⟩ : syracuseStep 1778147 = 2667221) B2667221
theorem B1778177 : Blo 1184409 1778177 := bstep (se 2 (by rfl) ⟨666816, by rfl⟩ : syracuseStep 1778177 = 1333633) B1333633
theorem B1999363 : Blo 1184409 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B1778195 : Blo 1184409 1778195 := bstep (se 1 (by rfl) ⟨1333646, by rfl⟩ : syracuseStep 1778195 = 2667293) B2667293
theorem B1778225 : Blo 1184409 1778225 := bstep (se 2 (by rfl) ⟨666834, by rfl⟩ : syracuseStep 1778225 = 1333669) B1333669
theorem B1778243 : Blo 1184409 1778243 := bstep (se 1 (by rfl) ⟨1333682, by rfl⟩ : syracuseStep 1778243 = 2667365) B2667365
theorem B1688131 : Blo 1184409 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B1778273 : Blo 1184409 1778273 := bstep (se 2 (by rfl) ⟨666852, by rfl⟩ : syracuseStep 1778273 = 1333705) B1333705
theorem B2998883 : Blo 1184409 2998883 := bstep (se 1 (by rfl) ⟨2249162, by rfl⟩ : syracuseStep 2998883 = 4498325) B4498325
theorem B3375715 : Blo 1184409 3375715 := bstep (se 1 (by rfl) ⟨2531786, by rfl⟩ : syracuseStep 3375715 = 5063573) B5063573
theorem B3998321 : Blo 1184409 3998321 := bstep (se 2 (by rfl) ⟨1499370, by rfl⟩ : syracuseStep 3998321 = 2998741) B2998741
theorem B1778291 : Blo 1184409 1778291 := bstep (se 1 (by rfl) ⟨1333718, by rfl⟩ : syracuseStep 1778291 = 2667437) B2667437
theorem B9241229 : Blo 1184409 9241229 := bstep (se 3 (by rfl) ⟨1732730, by rfl⟩ : syracuseStep 9241229 = 3465461) B3465461
theorem B1999505 : Blo 1184409 1999505 := bstep (se 2 (by rfl) ⟨749814, by rfl⟩ : syracuseStep 1999505 = 1499629) B1499629
theorem B1778321 : Blo 1184409 1778321 := bstep (se 2 (by rfl) ⟨666870, by rfl⟩ : syracuseStep 1778321 = 1333741) B1333741
theorem B1778339 : Blo 1184409 1778339 := bstep (se 1 (by rfl) ⟨1333754, by rfl⟩ : syracuseStep 1778339 = 2667509) B2667509
theorem B1778369 : Blo 1184409 1778369 := bstep (se 2 (by rfl) ⟨666888, by rfl⟩ : syracuseStep 1778369 = 1333777) B1333777
theorem B1778387 : Blo 1184409 1778387 := bstep (se 1 (by rfl) ⟨1333790, by rfl⟩ : syracuseStep 1778387 = 2667581) B2667581
theorem B1778417 : Blo 1184409 1778417 := bstep (se 2 (by rfl) ⟨666906, by rfl⟩ : syracuseStep 1778417 = 1333813) B1333813
theorem B1778435 : Blo 1184409 1778435 := bstep (se 1 (by rfl) ⟨1333826, by rfl⟩ : syracuseStep 1778435 = 2667653) B2667653
theorem B1999633 : Blo 1184409 1999633 := bstep (se 2 (by rfl) ⟨749862, by rfl⟩ : syracuseStep 1999633 = 1499725) B1499725
theorem B1778465 : Blo 1184409 1778465 := bstep (se 2 (by rfl) ⟨666924, by rfl⟩ : syracuseStep 1778465 = 1333849) B1333849
theorem B1999667 : Blo 1184409 1999667 := bstep (se 1 (by rfl) ⟨1499750, by rfl⟩ : syracuseStep 1999667 = 2999501) B2999501
theorem B1778483 : Blo 1184409 1778483 := bstep (se 1 (by rfl) ⟨1333862, by rfl⟩ : syracuseStep 1778483 = 2667725) B2667725
theorem B1778513 : Blo 1184409 1778513 := bstep (se 2 (by rfl) ⟨666942, by rfl⟩ : syracuseStep 1778513 = 1333885) B1333885
theorem B1778531 : Blo 1184409 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B1778561 : Blo 1184409 1778561 := bstep (se 2 (by rfl) ⟨666960, by rfl⟩ : syracuseStep 1778561 = 1333921) B1333921
theorem B1778579 : Blo 1184409 1778579 := bstep (se 1 (by rfl) ⟨1333934, by rfl⟩ : syracuseStep 1778579 = 2667869) B2667869
theorem B1688467 : Blo 1184409 1688467 := bstep (se 1 (by rfl) ⟨1266350, by rfl⟩ : syracuseStep 1688467 = 2532701) B2532701
theorem B3851171 : Blo 1184409 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B1778609 : Blo 1184409 1778609 := bstep (se 2 (by rfl) ⟨666978, by rfl⟩ : syracuseStep 1778609 = 1333957) B1333957
theorem B1999795 : Blo 1184409 1999795 := bstep (se 1 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 1999795 = 2999693) B2999693
theorem B1778627 : Blo 1184409 1778627 := bstep (se 1 (by rfl) ⟨1333970, by rfl⟩ : syracuseStep 1778627 = 2667941) B2667941
theorem B1500115 : Blo 1184409 1500115 := bstep (se 1 (by rfl) ⟨1125086, by rfl⟩ : syracuseStep 1500115 = 2250173) B2250173
theorem B1778657 : Blo 1184409 1778657 := bstep (se 2 (by rfl) ⟨666996, by rfl⟩ : syracuseStep 1778657 = 1333993) B1333993
theorem B20251619 : Blo 1184409 20251619 := bstep (se 1 (by rfl) ⟨15188714, by rfl⟩ : syracuseStep 20251619 = 30377429) B30377429
theorem B1778675 : Blo 1184409 1778675 := bstep (se 1 (by rfl) ⟨1334006, by rfl⟩ : syracuseStep 1778675 = 2668013) B2668013
theorem B1778705 : Blo 1184409 1778705 := bstep (se 2 (by rfl) ⟨667014, by rfl⟩ : syracuseStep 1778705 = 1334029) B1334029
theorem B1778723 : Blo 1184409 1778723 := bstep (se 1 (by rfl) ⟨1334042, by rfl⟩ : syracuseStep 1778723 = 2668085) B2668085
theorem B2704433 : Blo 1184409 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B1500211 : Blo 1184409 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B1999937 : Blo 1184409 1999937 := bstep (se 2 (by rfl) ⟨749976, by rfl⟩ : syracuseStep 1999937 = 1499953) B1499953
theorem B1778753 : Blo 1184409 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B4056131 : Blo 1184409 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B3376205 : Blo 1184409 3376205 := bstep (se 3 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 3376205 = 1266077) B1266077
theorem B1778771 : Blo 1184409 1778771 := bstep (se 1 (by rfl) ⟨1334078, by rfl⟩ : syracuseStep 1778771 = 2668157) B2668157
theorem B1778801 : Blo 1184409 1778801 := bstep (se 2 (by rfl) ⟨667050, by rfl⟩ : syracuseStep 1778801 = 1334101) B1334101
theorem B1778819 : Blo 1184409 1778819 := bstep (se 1 (by rfl) ⟨1334114, by rfl⟩ : syracuseStep 1778819 = 2668229) B2668229
theorem B3998861 : Blo 1184409 3998861 := bstep (se 3 (by rfl) ⟨749786, by rfl⟩ : syracuseStep 3998861 = 1499573) B1499573
theorem B1778849 : Blo 1184409 1778849 := bstep (se 2 (by rfl) ⟨667068, by rfl⟩ : syracuseStep 1778849 = 1334137) B1334137
theorem B1778867 : Blo 1184409 1778867 := bstep (se 1 (by rfl) ⟨1334150, by rfl⟩ : syracuseStep 1778867 = 2668301) B2668301
theorem B2000065 : Blo 1184409 2000065 := bstep (se 2 (by rfl) ⟨750024, by rfl⟩ : syracuseStep 2000065 = 1500049) B1500049
theorem B3998915 : Blo 1184409 3998915 := bstep (se 1 (by rfl) ⟨2999186, by rfl⟩ : syracuseStep 3998915 = 5998373) B5998373
theorem B1778897 : Blo 1184409 1778897 := bstep (se 2 (by rfl) ⟨667086, by rfl⟩ : syracuseStep 1778897 = 1334173) B1334173
theorem B2000099 : Blo 1184409 2000099 := bstep (se 1 (by rfl) ⟨1500074, by rfl⟩ : syracuseStep 2000099 = 3000149) B3000149
theorem B1778915 : Blo 1184409 1778915 := bstep (se 1 (by rfl) ⟨1334186, by rfl⟩ : syracuseStep 1778915 = 2668373) B2668373
theorem B6005987 : Blo 1184409 6005987 := bstep (se 1 (by rfl) ⟨4504490, by rfl⟩ : syracuseStep 6005987 = 9008981) B9008981
theorem B1778945 : Blo 1184409 1778945 := bstep (se 2 (by rfl) ⟨667104, by rfl⟩ : syracuseStep 1778945 = 1334209) B1334209
theorem B1778963 : Blo 1184409 1778963 := bstep (se 1 (by rfl) ⟨1334222, by rfl⟩ : syracuseStep 1778963 = 2668445) B2668445
theorem B1778993 : Blo 1184409 1778993 := bstep (se 2 (by rfl) ⟨667122, by rfl⟩ : syracuseStep 1778993 = 1334245) B1334245
theorem B1779011 : Blo 1184409 1779011 := bstep (se 1 (by rfl) ⟨1334258, by rfl⟩ : syracuseStep 1779011 = 2668517) B2668517
theorem B1779041 : Blo 1184409 1779041 := bstep (se 2 (by rfl) ⟨667140, by rfl⟩ : syracuseStep 1779041 = 1334281) B1334281
theorem B2000227 : Blo 1184409 2000227 := bstep (se 1 (by rfl) ⟨1500170, by rfl⟩ : syracuseStep 2000227 = 3000341) B3000341
theorem B1779059 : Blo 1184409 1779059 := bstep (se 1 (by rfl) ⟨1334294, by rfl⟩ : syracuseStep 1779059 = 2668589) B2668589
theorem B1779089 : Blo 1184409 1779089 := bstep (se 2 (by rfl) ⟨667158, by rfl⟩ : syracuseStep 1779089 = 1334317) B1334317
theorem B1779107 : Blo 1184409 1779107 := bstep (se 1 (by rfl) ⟨1334330, by rfl⟩ : syracuseStep 1779107 = 2668661) B2668661
theorem B1779137 : Blo 1184409 1779137 := bstep (se 2 (by rfl) ⟨667176, by rfl⟩ : syracuseStep 1779137 = 1334353) B1334353
theorem B1689025 : Blo 1184409 1689025 := bstep (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) B1266769
theorem B92431813 : Blo 1184409 92431813 := bstep (se 4 (by rfl) ⟨8665482, by rfl⟩ : syracuseStep 92431813 = 17330965) B17330965
theorem B3999185 : Blo 1184409 3999185 := bstep (se 2 (by rfl) ⟨1499694, by rfl⟩ : syracuseStep 3999185 = 2999389) B2999389
theorem B1779155 : Blo 1184409 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B31204835 : Blo 1184409 31204835 := bstep (se 1 (by rfl) ⟨23403626, by rfl⟩ : syracuseStep 31204835 = 46807253) B46807253
theorem B1689059 : Blo 1184409 1689059 := bstep (se 1 (by rfl) ⟨1266794, by rfl⟩ : syracuseStep 1689059 = 2533589) B2533589
theorem B2000369 : Blo 1184409 2000369 := bstep (se 2 (by rfl) ⟨750138, by rfl⟩ : syracuseStep 2000369 = 1500277) B1500277
theorem B1779185 : Blo 1184409 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1779203 : Blo 1184409 1779203 := bstep (se 1 (by rfl) ⟨1334402, by rfl⟩ : syracuseStep 1779203 = 2668805) B2668805
theorem B2999825 : Blo 1184409 2999825 := bstep (se 2 (by rfl) ⟨1124934, by rfl⟩ : syracuseStep 2999825 = 2249869) B2249869
theorem B1779233 : Blo 1184409 1779233 := bstep (se 2 (by rfl) ⟨667212, by rfl⟩ : syracuseStep 1779233 = 1334425) B1334425
theorem B1500707 : Blo 1184409 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B1779251 : Blo 1184409 1779251 := bstep (se 1 (by rfl) ⟨1334438, by rfl⟩ : syracuseStep 1779251 = 2668877) B2668877
theorem B2999875 : Blo 1184409 2999875 := bstep (se 1 (by rfl) ⟨2249906, by rfl⟩ : syracuseStep 2999875 = 4499813) B4499813
theorem B1779281 : Blo 1184409 1779281 := bstep (se 2 (by rfl) ⟨667230, by rfl⟩ : syracuseStep 1779281 = 1334461) B1334461
theorem B1779299 : Blo 1184409 1779299 := bstep (se 1 (by rfl) ⟨1334474, by rfl⟩ : syracuseStep 1779299 = 2668949) B2668949
theorem B2000497 : Blo 1184409 2000497 := bstep (se 2 (by rfl) ⟨750186, by rfl⟩ : syracuseStep 2000497 = 1500373) B1500373
theorem B1779329 : Blo 1184409 1779329 := bstep (se 2 (by rfl) ⟨667248, by rfl⟩ : syracuseStep 1779329 = 1334497) B1334497
theorem B2000531 : Blo 1184409 2000531 := bstep (se 1 (by rfl) ⟨1500398, by rfl⟩ : syracuseStep 2000531 = 3000797) B3000797
theorem B1779347 : Blo 1184409 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B6751907 : Blo 1184409 6751907 := bstep (se 1 (by rfl) ⟨5063930, by rfl⟩ : syracuseStep 6751907 = 10127861) B10127861
theorem B1779377 : Blo 1184409 1779377 := bstep (se 2 (by rfl) ⟨667266, by rfl⟩ : syracuseStep 1779377 = 1334533) B1334533
theorem B1779395 : Blo 1184409 1779395 := bstep (se 1 (by rfl) ⟨1334546, by rfl⟩ : syracuseStep 1779395 = 2669093) B2669093
theorem B3000017 : Blo 1184409 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B1779425 : Blo 1184409 1779425 := bstep (se 2 (by rfl) ⟨667284, by rfl⟩ : syracuseStep 1779425 = 1334569) B1334569
theorem B4056817 : Blo 1184409 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1779443 : Blo 1184409 1779443 := bstep (se 1 (by rfl) ⟨1334582, by rfl⟩ : syracuseStep 1779443 = 2669165) B2669165
theorem B14411533 : Blo 1184409 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B1779473 : Blo 1184409 1779473 := bstep (se 2 (by rfl) ⟨667302, by rfl⟩ : syracuseStep 1779473 = 1334605) B1334605
theorem B2000659 : Blo 1184409 2000659 := bstep (se 1 (by rfl) ⟨1500494, by rfl⟩ : syracuseStep 2000659 = 3000989) B3000989
theorem B1779491 : Blo 1184409 1779491 := bstep (se 1 (by rfl) ⟨1334618, by rfl⟩ : syracuseStep 1779491 = 2669237) B2669237
theorem B1779521 : Blo 1184409 1779521 := bstep (se 2 (by rfl) ⟨667320, by rfl⟩ : syracuseStep 1779521 = 1334641) B1334641
theorem B1779539 : Blo 1184409 1779539 := bstep (se 1 (by rfl) ⟨1334654, by rfl⟩ : syracuseStep 1779539 = 2669309) B2669309
theorem B1779569 : Blo 1184409 1779569 := bstep (se 2 (by rfl) ⟨667338, by rfl⟩ : syracuseStep 1779569 = 1334677) B1334677
theorem B1779587 : Blo 1184409 1779587 := bstep (se 1 (by rfl) ⟨1334690, by rfl⟩ : syracuseStep 1779587 = 2669381) B2669381
theorem B2000801 : Blo 1184409 2000801 := bstep (se 2 (by rfl) ⟨750300, by rfl⟩ : syracuseStep 2000801 = 1500601) B1500601
theorem B3999725 : Blo 1184409 3999725 := bstep (se 3 (by rfl) ⟨749948, by rfl⟩ : syracuseStep 3999725 = 1499897) B1499897
theorem B4057091 : Blo 1184409 4057091 := bstep (se 1 (by rfl) ⟨3042818, by rfl⟩ : syracuseStep 4057091 = 6085637) B6085637
theorem B2000929 : Blo 1184409 2000929 := bstep (se 2 (by rfl) ⟨750348, by rfl⟩ : syracuseStep 2000929 = 1500697) B1500697
theorem B3999779 : Blo 1184409 3999779 := bstep (se 1 (by rfl) ⟨2999834, by rfl⟩ : syracuseStep 3999779 = 5999669) B5999669
theorem B2000963 : Blo 1184409 2000963 := bstep (se 1 (by rfl) ⟨1500722, by rfl⟩ : syracuseStep 2000963 = 3001445) B3001445
theorem B4270157 : Blo 1184409 4270157 := bstep (se 3 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 4270157 = 1601309) B1601309
theorem B6408305 : Blo 1184409 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B2001091 : Blo 1184409 2001091 := bstep (se 1 (by rfl) ⟨1500818, by rfl⟩ : syracuseStep 2001091 = 3001637) B3001637
theorem B11397347 : Blo 1184409 11397347 := bstep (se 1 (by rfl) ⟨8548010, by rfl⟩ : syracuseStep 11397347 = 17096021) B17096021
theorem B1501411 : Blo 1184409 1501411 := bstep (se 1 (by rfl) ⟨1126058, by rfl⟩ : syracuseStep 1501411 = 2252117) B2252117
theorem B3377389 : Blo 1184409 3377389 := bstep (se 3 (by rfl) ⟨633260, by rfl⟩ : syracuseStep 3377389 = 1266521) B1266521
theorem B2885905 : Blo 1184409 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B4000049 : Blo 1184409 4000049 := bstep (se 2 (by rfl) ⟨1500018, by rfl⟩ : syracuseStep 4000049 = 3000037) B3000037
theorem B1501507 : Blo 1184409 1501507 := bstep (se 1 (by rfl) ⟨1126130, by rfl⟩ : syracuseStep 1501507 = 2252261) B2252261
theorem B2001233 : Blo 1184409 2001233 := bstep (se 2 (by rfl) ⟨750462, by rfl⟩ : syracuseStep 2001233 = 1500925) B1500925
theorem B8997317 : Blo 1184409 8997317 := bstep (se 4 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 8997317 = 1686997) B1686997
theorem B2001361 : Blo 1184409 2001361 := bstep (se 2 (by rfl) ⟨750510, by rfl⟩ : syracuseStep 2001361 = 1501021) B1501021
theorem B3795437 : Blo 1184409 3795437 := bstep (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) B1423289
theorem B2001395 : Blo 1184409 2001395 := bstep (se 1 (by rfl) ⟨1501046, by rfl⟩ : syracuseStep 2001395 = 3002093) B3002093
theorem B4499981 : Blo 1184409 4499981 := bstep (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) B1687493
theorem B5065229 : Blo 1184409 5065229 := bstep (se 3 (by rfl) ⟨949730, by rfl⟩ : syracuseStep 5065229 = 1899461) B1899461
theorem B2001523 : Blo 1184409 2001523 := bstep (se 1 (by rfl) ⟨1501142, by rfl⟩ : syracuseStep 2001523 = 3002285) B3002285
theorem B6752909 : Blo 1184409 6752909 := bstep (se 3 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 6752909 = 2532341) B2532341
theorem B3001009 : Blo 1184409 3001009 := bstep (se 2 (by rfl) ⟨1125378, by rfl⟩ : syracuseStep 3001009 = 2250757) B2250757
theorem B2665169 : Blo 1184409 2665169 := bstep (se 2 (by rfl) ⟨999438, by rfl⟩ : syracuseStep 2665169 = 1998877) B1998877
theorem B2665187 : Blo 1184409 2665187 := bstep (se 1 (by rfl) ⟨1998890, by rfl⟩ : syracuseStep 2665187 = 3997781) B3997781
theorem B4270819 : Blo 1184409 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B2886371 : Blo 1184409 2886371 := bstep (se 1 (by rfl) ⟨2164778, by rfl⟩ : syracuseStep 2886371 = 4329557) B4329557
theorem B5999345 : Blo 1184409 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B2001665 : Blo 1184409 2001665 := bstep (se 2 (by rfl) ⟨750624, by rfl⟩ : syracuseStep 2001665 = 1501249) B1501249
theorem B3205937 : Blo 1184409 3205937 := bstep (se 2 (by rfl) ⟨1202226, by rfl⟩ : syracuseStep 3205937 = 2404453) B2404453
theorem B4000589 : Blo 1184409 4000589 := bstep (se 3 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 4000589 = 1500221) B1500221
theorem B5065571 : Blo 1184409 5065571 := bstep (se 1 (by rfl) ⟨3799178, by rfl⟩ : syracuseStep 5065571 = 7598357) B7598357
theorem B3246961 : Blo 1184409 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B3042161 : Blo 1184409 3042161 := bstep (se 2 (by rfl) ⟨1140810, by rfl⟩ : syracuseStep 3042161 = 2281621) B2281621
theorem B2001793 : Blo 1184409 2001793 := bstep (se 2 (by rfl) ⟨750672, by rfl⟩ : syracuseStep 2001793 = 1501345) B1501345
theorem B4000643 : Blo 1184409 4000643 := bstep (se 1 (by rfl) ⟨3000482, by rfl⟩ : syracuseStep 4000643 = 6000965) B6000965
theorem B2001827 : Blo 1184409 2001827 := bstep (se 1 (by rfl) ⟨1501370, by rfl⟩ : syracuseStep 2001827 = 3002741) B3002741
theorem B3001283 : Blo 1184409 3001283 := bstep (se 1 (by rfl) ⟨2250962, by rfl⟩ : syracuseStep 3001283 = 4501925) B4501925
theorem B2665457 : Blo 1184409 2665457 := bstep (se 2 (by rfl) ⟨999546, by rfl⟩ : syracuseStep 2665457 = 1999093) B1999093
theorem B9006065 : Blo 1184409 9006065 := bstep (se 2 (by rfl) ⟨3377274, by rfl⟩ : syracuseStep 9006065 = 6754549) B6754549
theorem B2665475 : Blo 1184409 2665475 := bstep (se 1 (by rfl) ⟨1999106, by rfl⟩ : syracuseStep 2665475 = 3998213) B3998213
theorem B1625107 : Blo 1184409 1625107 := bstep (se 1 (by rfl) ⟨1218830, by rfl⟩ : syracuseStep 1625107 = 2437661) B2437661
theorem B2001955 : Blo 1184409 2001955 := bstep (se 1 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 2001955 = 3002933) B3002933
theorem B3001475 : Blo 1184409 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B4000913 : Blo 1184409 4000913 := bstep (se 2 (by rfl) ⟨1500342, by rfl⟩ : syracuseStep 4000913 = 3000685) B3000685
theorem B7589027 : Blo 1184409 7589027 := bstep (se 1 (by rfl) ⟨5691770, by rfl⟩ : syracuseStep 7589027 = 11383541) B11383541
theorem B2665745 : Blo 1184409 2665745 := bstep (se 2 (by rfl) ⟨999654, by rfl⟩ : syracuseStep 2665745 = 1999309) B1999309
theorem B3378449 : Blo 1184409 3378449 := bstep (se 2 (by rfl) ⟨1266918, by rfl⟩ : syracuseStep 3378449 = 2533837) B2533837
theorem B2665763 : Blo 1184409 2665763 := bstep (se 1 (by rfl) ⟨1999322, by rfl⟩ : syracuseStep 2665763 = 3998645) B3998645
theorem B4500785 : Blo 1184409 4500785 := bstep (se 2 (by rfl) ⟨1687794, by rfl⟩ : syracuseStep 4500785 = 3375589) B3375589
theorem B30797333 : Blo 1184409 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B2666033 : Blo 1184409 2666033 := bstep (se 2 (by rfl) ⟨999762, by rfl⟩ : syracuseStep 2666033 = 1999525) B1999525
theorem B2666051 : Blo 1184409 2666051 := bstep (se 1 (by rfl) ⟨1999538, by rfl⟩ : syracuseStep 2666051 = 3999077) B3999077
theorem B25636493 : Blo 1184409 25636493 := bstep (se 3 (by rfl) ⟨4806842, by rfl⟩ : syracuseStep 25636493 = 9613685) B9613685
theorem B4001453 : Blo 1184409 4001453 := bstep (se 3 (by rfl) ⟨750272, by rfl⟩ : syracuseStep 4001453 = 1500545) B1500545
theorem B9875141 : Blo 1184409 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B4001507 : Blo 1184409 4001507 := bstep (se 1 (by rfl) ⟨3001130, by rfl⟩ : syracuseStep 4001507 = 6002261) B6002261
theorem B2666321 : Blo 1184409 2666321 := bstep (se 2 (by rfl) ⟨999870, by rfl⟩ : syracuseStep 2666321 = 1999741) B1999741
theorem B2666339 : Blo 1184409 2666339 := bstep (se 1 (by rfl) ⟨1999754, by rfl⟩ : syracuseStep 2666339 = 3999509) B3999509
theorem B4501453 : Blo 1184409 4501453 := bstep (se 3 (by rfl) ⟨844022, by rfl⟩ : syracuseStep 4501453 = 1688045) B1688045
theorem B4001777 : Blo 1184409 4001777 := bstep (se 2 (by rfl) ⟨1500666, by rfl⟩ : syracuseStep 4001777 = 3001333) B3001333
theorem B3797027 : Blo 1184409 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B3002417 : Blo 1184409 3002417 := bstep (se 2 (by rfl) ⟨1125906, by rfl⟩ : syracuseStep 3002417 = 2251813) B2251813
theorem B6410339 : Blo 1184409 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B3002467 : Blo 1184409 3002467 := bstep (se 1 (by rfl) ⟨2251850, by rfl⟩ : syracuseStep 3002467 = 4503701) B4503701
theorem B2666609 : Blo 1184409 2666609 := bstep (se 2 (by rfl) ⟨999978, by rfl⟩ : syracuseStep 2666609 = 1999957) B1999957
theorem B2666627 : Blo 1184409 2666627 := bstep (se 1 (by rfl) ⟨1999970, by rfl⟩ : syracuseStep 2666627 = 3999941) B3999941
theorem B6000803 : Blo 1184409 6000803 := bstep (se 1 (by rfl) ⟨4500602, by rfl⟩ : syracuseStep 6000803 = 9001205) B9001205
theorem B7213283 : Blo 1184409 7213283 := bstep (se 1 (by rfl) ⟨5409962, by rfl⟩ : syracuseStep 7213283 = 10819925) B10819925
theorem B3002609 : Blo 1184409 3002609 := bstep (se 2 (by rfl) ⟨1125978, by rfl⟩ : syracuseStep 3002609 = 2251957) B2251957
theorem B2249041 : Blo 1184409 2249041 := bstep (se 2 (by rfl) ⟨843390, by rfl⟩ : syracuseStep 2249041 = 1686781) B1686781
theorem B7590257 : Blo 1184409 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B2404721 : Blo 1184409 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B2666897 : Blo 1184409 2666897 := bstep (se 2 (by rfl) ⟨1000086, by rfl⟩ : syracuseStep 2666897 = 2000173) B2000173
theorem B2666915 : Blo 1184409 2666915 := bstep (se 1 (by rfl) ⟨2000186, by rfl⟩ : syracuseStep 2666915 = 4000373) B4000373
theorem B2249201 : Blo 1184409 2249201 := bstep (se 2 (by rfl) ⟨843450, by rfl⟩ : syracuseStep 2249201 = 1686901) B1686901
theorem B4002317 : Blo 1184409 4002317 := bstep (se 3 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 4002317 = 1500869) B1500869
theorem B4002371 : Blo 1184409 4002371 := bstep (se 1 (by rfl) ⟨3001778, by rfl⟩ : syracuseStep 4002371 = 6003557) B6003557
theorem B6083171 : Blo 1184409 6083171 := bstep (se 1 (by rfl) ⟨4562378, by rfl⟩ : syracuseStep 6083171 = 9124757) B9124757
theorem B1184419 : Blo 1184409 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B2667185 : Blo 1184409 2667185 := bstep (se 2 (by rfl) ⟨1000194, by rfl⟩ : syracuseStep 2667185 = 2000389) B2000389
theorem B1184435 : Blo 1184409 1184435 := bstep (se 1 (by rfl) ⟨888326, by rfl⟩ : syracuseStep 1184435 = 1776653) B1776653
theorem B1184451 : Blo 1184409 1184451 := bstep (se 1 (by rfl) ⟨888338, by rfl⟩ : syracuseStep 1184451 = 1776677) B1776677
theorem B2667203 : Blo 1184409 2667203 := bstep (se 1 (by rfl) ⟨2000402, by rfl⟩ : syracuseStep 2667203 = 4000805) B4000805
theorem B12169925 : Blo 1184409 12169925 := bstep (se 4 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 12169925 = 2281861) B2281861
theorem B1184467 : Blo 1184409 1184467 := bstep (se 1 (by rfl) ⟨888350, by rfl⟩ : syracuseStep 1184467 = 1776701) B1776701
theorem B1184483 : Blo 1184409 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B4502243 : Blo 1184409 4502243 := bstep (se 1 (by rfl) ⟨3376682, by rfl⟩ : syracuseStep 4502243 = 6753365) B6753365
theorem B1184499 : Blo 1184409 1184499 := bstep (se 1 (by rfl) ⟨888374, by rfl⟩ : syracuseStep 1184499 = 1776749) B1776749
theorem B1897219 : Blo 1184409 1897219 := bstep (se 1 (by rfl) ⟨1422914, by rfl⟩ : syracuseStep 1897219 = 2845829) B2845829
theorem B1184515 : Blo 1184409 1184515 := bstep (se 1 (by rfl) ⟨888386, by rfl⟩ : syracuseStep 1184515 = 1776773) B1776773
theorem B1184531 : Blo 1184409 1184531 := bstep (se 1 (by rfl) ⟨888398, by rfl⟩ : syracuseStep 1184531 = 1776797) B1776797
theorem B1184547 : Blo 1184409 1184547 := bstep (se 1 (by rfl) ⟨888410, by rfl⟩ : syracuseStep 1184547 = 1776821) B1776821
theorem B1184563 : Blo 1184409 1184563 := bstep (se 1 (by rfl) ⟨888422, by rfl⟩ : syracuseStep 1184563 = 1776845) B1776845
theorem B1897283 : Blo 1184409 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B1184579 : Blo 1184409 1184579 := bstep (se 1 (by rfl) ⟨888434, by rfl⟩ : syracuseStep 1184579 = 1776869) B1776869
theorem B8549189 : Blo 1184409 8549189 := bstep (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) B1602973
theorem B4002641 : Blo 1184409 4002641 := bstep (se 2 (by rfl) ⟨1500990, by rfl⟩ : syracuseStep 4002641 = 3001981) B3001981
theorem B1184595 : Blo 1184409 1184595 := bstep (se 1 (by rfl) ⟨888446, by rfl⟩ : syracuseStep 1184595 = 1776893) B1776893
theorem B1184611 : Blo 1184409 1184611 := bstep (se 1 (by rfl) ⟨888458, by rfl⟩ : syracuseStep 1184611 = 1776917) B1776917
theorem B7312241 : Blo 1184409 7312241 := bstep (se 2 (by rfl) ⟨2742090, by rfl⟩ : syracuseStep 7312241 = 5484181) B5484181
theorem B1184627 : Blo 1184409 1184627 := bstep (se 1 (by rfl) ⟨888470, by rfl⟩ : syracuseStep 1184627 = 1776941) B1776941
theorem B1602433 : Blo 1184409 1602433 := bstep (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) B1201825
theorem B1184643 : Blo 1184409 1184643 := bstep (se 1 (by rfl) ⟨888482, by rfl⟩ : syracuseStep 1184643 = 1776965) B1776965
theorem B2249603 : Blo 1184409 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B1184659 : Blo 1184409 1184659 := bstep (se 1 (by rfl) ⟨888494, by rfl⟩ : syracuseStep 1184659 = 1776989) B1776989
theorem B1184675 : Blo 1184409 1184675 := bstep (se 1 (by rfl) ⟨888506, by rfl⟩ : syracuseStep 1184675 = 1777013) B1777013
theorem B3797923 : Blo 1184409 3797923 := bstep (se 1 (by rfl) ⟨2848442, by rfl⟩ : syracuseStep 3797923 = 5696885) B5696885
theorem B8106929 : Blo 1184409 8106929 := bstep (se 2 (by rfl) ⟨3040098, by rfl⟩ : syracuseStep 8106929 = 6080197) B6080197
theorem B1184691 : Blo 1184409 1184691 := bstep (se 1 (by rfl) ⟨888518, by rfl⟩ : syracuseStep 1184691 = 1777037) B1777037
theorem B1897411 : Blo 1184409 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B6747077 : Blo 1184409 6747077 := bstep (se 4 (by rfl) ⟨632538, by rfl⟩ : syracuseStep 6747077 = 1265077) B1265077
theorem B1184707 : Blo 1184409 1184707 := bstep (se 1 (by rfl) ⟨888530, by rfl⟩ : syracuseStep 1184707 = 1777061) B1777061
theorem B6001613 : Blo 1184409 6001613 := bstep (se 3 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 6001613 = 2250605) B2250605
theorem B2667473 : Blo 1184409 2667473 := bstep (se 2 (by rfl) ⟨1000302, by rfl⟩ : syracuseStep 2667473 = 2000605) B2000605
theorem B1184723 : Blo 1184409 1184723 := bstep (se 1 (by rfl) ⟨888542, by rfl⟩ : syracuseStep 1184723 = 1777085) B1777085
theorem B1184739 : Blo 1184409 1184739 := bstep (se 1 (by rfl) ⟨888554, by rfl⟩ : syracuseStep 1184739 = 1777109) B1777109
theorem B2667491 : Blo 1184409 2667491 := bstep (se 1 (by rfl) ⟨2000618, by rfl⟩ : syracuseStep 2667491 = 4001237) B4001237
theorem B1184755 : Blo 1184409 1184755 := bstep (se 1 (by rfl) ⟨888566, by rfl⟩ : syracuseStep 1184755 = 1777133) B1777133
theorem B1184771 : Blo 1184409 1184771 := bstep (se 1 (by rfl) ⟨888578, by rfl⟩ : syracuseStep 1184771 = 1777157) B1777157
theorem B1184787 : Blo 1184409 1184787 := bstep (se 1 (by rfl) ⟨888590, by rfl⟩ : syracuseStep 1184787 = 1777181) B1777181
theorem B1184803 : Blo 1184409 1184803 := bstep (se 1 (by rfl) ⟨888602, by rfl⟩ : syracuseStep 1184803 = 1777205) B1777205
theorem B1184819 : Blo 1184409 1184819 := bstep (se 1 (by rfl) ⟨888614, by rfl⟩ : syracuseStep 1184819 = 1777229) B1777229
theorem B1184835 : Blo 1184409 1184835 := bstep (se 1 (by rfl) ⟨888626, by rfl⟩ : syracuseStep 1184835 = 1777253) B1777253
theorem B1184851 : Blo 1184409 1184851 := bstep (se 1 (by rfl) ⟨888638, by rfl⟩ : syracuseStep 1184851 = 1777277) B1777277
theorem B1184867 : Blo 1184409 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B1184883 : Blo 1184409 1184883 := bstep (se 1 (by rfl) ⟨888662, by rfl⟩ : syracuseStep 1184883 = 1777325) B1777325
theorem B1184899 : Blo 1184409 1184899 := bstep (se 1 (by rfl) ⟨888674, by rfl⟩ : syracuseStep 1184899 = 1777349) B1777349
theorem B1184915 : Blo 1184409 1184915 := bstep (se 1 (by rfl) ⟨888686, by rfl⟩ : syracuseStep 1184915 = 1777373) B1777373
theorem B1184931 : Blo 1184409 1184931 := bstep (se 1 (by rfl) ⟨888698, by rfl⟩ : syracuseStep 1184931 = 1777397) B1777397
theorem B1184947 : Blo 1184409 1184947 := bstep (se 1 (by rfl) ⟨888710, by rfl⟩ : syracuseStep 1184947 = 1777421) B1777421
theorem B1184963 : Blo 1184409 1184963 := bstep (se 1 (by rfl) ⟨888722, by rfl⟩ : syracuseStep 1184963 = 1777445) B1777445
theorem B4273357 : Blo 1184409 4273357 := bstep (se 3 (by rfl) ⟨801254, by rfl⟩ : syracuseStep 4273357 = 1602509) B1602509
theorem B2847953 : Blo 1184409 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B1184979 : Blo 1184409 1184979 := bstep (se 1 (by rfl) ⟨888734, by rfl⟩ : syracuseStep 1184979 = 1777469) B1777469
theorem B1184995 : Blo 1184409 1184995 := bstep (se 1 (by rfl) ⟨888746, by rfl⟩ : syracuseStep 1184995 = 1777493) B1777493
theorem B2667761 : Blo 1184409 2667761 := bstep (se 2 (by rfl) ⟨1000410, by rfl⟩ : syracuseStep 2667761 = 2000821) B2000821
theorem B1185011 : Blo 1184409 1185011 := bstep (se 1 (by rfl) ⟨888758, by rfl⟩ : syracuseStep 1185011 = 1777517) B1777517
theorem B1266931 : Blo 1184409 1266931 := bstep (se 1 (by rfl) ⟨950198, by rfl⟩ : syracuseStep 1266931 = 1900397) B1900397
theorem B1185027 : Blo 1184409 1185027 := bstep (se 1 (by rfl) ⟨888770, by rfl⟩ : syracuseStep 1185027 = 1777541) B1777541
theorem B2667779 : Blo 1184409 2667779 := bstep (se 1 (by rfl) ⟨2000834, by rfl⟩ : syracuseStep 2667779 = 4001669) B4001669
theorem B1332499 : Blo 1184409 1332499 := bstep (se 1 (by rfl) ⟨999374, by rfl⟩ : syracuseStep 1332499 = 1998749) B1998749
theorem B1185043 : Blo 1184409 1185043 := bstep (se 1 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 1185043 = 1777565) B1777565
theorem B1185059 : Blo 1184409 1185059 := bstep (se 1 (by rfl) ⟨888794, by rfl⟩ : syracuseStep 1185059 = 1777589) B1777589
theorem B8115491 : Blo 1184409 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B1185075 : Blo 1184409 1185075 := bstep (se 1 (by rfl) ⟨888806, by rfl⟩ : syracuseStep 1185075 = 1777613) B1777613
theorem B1185091 : Blo 1184409 1185091 := bstep (se 1 (by rfl) ⟨888818, by rfl⟩ : syracuseStep 1185091 = 1777637) B1777637
theorem B1185107 : Blo 1184409 1185107 := bstep (se 1 (by rfl) ⟨888830, by rfl⟩ : syracuseStep 1185107 = 1777661) B1777661
theorem B1185123 : Blo 1184409 1185123 := bstep (se 1 (by rfl) ⟨888842, by rfl⟩ : syracuseStep 1185123 = 1777685) B1777685
theorem B2282851 : Blo 1184409 2282851 := bstep (se 1 (by rfl) ⟨1712138, by rfl⟩ : syracuseStep 2282851 = 3424277) B3424277
theorem B4003181 : Blo 1184409 4003181 := bstep (se 3 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 4003181 = 1501193) B1501193
theorem B4806001 : Blo 1184409 4806001 := bstep (se 2 (by rfl) ⟨1802250, by rfl⟩ : syracuseStep 4806001 = 3604501) B3604501
theorem B4502897 : Blo 1184409 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B1185139 : Blo 1184409 1185139 := bstep (se 1 (by rfl) ⟨888854, by rfl⟩ : syracuseStep 1185139 = 1777709) B1777709
theorem B1602931 : Blo 1184409 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B1185155 : Blo 1184409 1185155 := bstep (se 1 (by rfl) ⟨888866, by rfl⟩ : syracuseStep 1185155 = 1777733) B1777733
theorem B6747533 : Blo 1184409 6747533 := bstep (se 3 (by rfl) ⟨1265162, by rfl⟩ : syracuseStep 6747533 = 2530325) B2530325
theorem B4052369 : Blo 1184409 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B1185171 : Blo 1184409 1185171 := bstep (se 1 (by rfl) ⟨888878, by rfl⟩ : syracuseStep 1185171 = 1777757) B1777757
theorem B1185187 : Blo 1184409 1185187 := bstep (se 1 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 1185187 = 1777781) B1777781
theorem B1332643 : Blo 1184409 1332643 := bstep (se 1 (by rfl) ⟨999482, by rfl⟩ : syracuseStep 1332643 = 1998965) B1998965
theorem B4003235 : Blo 1184409 4003235 := bstep (se 1 (by rfl) ⟨3002426, by rfl⟩ : syracuseStep 4003235 = 6004853) B6004853
theorem B1185203 : Blo 1184409 1185203 := bstep (se 1 (by rfl) ⟨888902, by rfl⟩ : syracuseStep 1185203 = 1777805) B1777805
theorem B1185219 : Blo 1184409 1185219 := bstep (se 1 (by rfl) ⟨888914, by rfl⟩ : syracuseStep 1185219 = 1777829) B1777829
theorem B1185235 : Blo 1184409 1185235 := bstep (se 1 (by rfl) ⟨888926, by rfl⟩ : syracuseStep 1185235 = 1777853) B1777853
theorem B17315299 : Blo 1184409 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B17085923 : Blo 1184409 17085923 := bstep (se 1 (by rfl) ⟨12814442, by rfl⟩ : syracuseStep 17085923 = 25628885) B25628885
theorem B1185251 : Blo 1184409 1185251 := bstep (se 1 (by rfl) ⟨888938, by rfl⟩ : syracuseStep 1185251 = 1777877) B1777877
theorem B6755825 : Blo 1184409 6755825 := bstep (se 2 (by rfl) ⟨2533434, by rfl⟩ : syracuseStep 6755825 = 5066869) B5066869
theorem B1185267 : Blo 1184409 1185267 := bstep (se 1 (by rfl) ⟨888950, by rfl⟩ : syracuseStep 1185267 = 1777901) B1777901
theorem B1185283 : Blo 1184409 1185283 := bstep (se 1 (by rfl) ⟨888962, by rfl⟩ : syracuseStep 1185283 = 1777925) B1777925
theorem B2668049 : Blo 1184409 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B1185299 : Blo 1184409 1185299 := bstep (se 1 (by rfl) ⟨888974, by rfl⟩ : syracuseStep 1185299 = 1777949) B1777949
theorem B5404195 : Blo 1184409 5404195 := bstep (se 1 (by rfl) ⟨4053146, by rfl⟩ : syracuseStep 5404195 = 8106293) B8106293
theorem B1185315 : Blo 1184409 1185315 := bstep (se 1 (by rfl) ⟨888986, by rfl⟩ : syracuseStep 1185315 = 1777973) B1777973
theorem B2668067 : Blo 1184409 2668067 := bstep (se 1 (by rfl) ⟨2001050, by rfl⟩ : syracuseStep 2668067 = 4002101) B4002101
theorem B1332787 : Blo 1184409 1332787 := bstep (se 1 (by rfl) ⟨999590, by rfl⟩ : syracuseStep 1332787 = 1999181) B1999181
theorem B1185331 : Blo 1184409 1185331 := bstep (se 1 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 1185331 = 1777997) B1777997
theorem B1185347 : Blo 1184409 1185347 := bstep (se 1 (by rfl) ⟨889010, by rfl⟩ : syracuseStep 1185347 = 1778021) B1778021
theorem B1185363 : Blo 1184409 1185363 := bstep (se 1 (by rfl) ⟨889022, by rfl⟩ : syracuseStep 1185363 = 1778045) B1778045
theorem B1185379 : Blo 1184409 1185379 := bstep (se 1 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 1185379 = 1778069) B1778069
theorem B18257521 : Blo 1184409 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B1185395 : Blo 1184409 1185395 := bstep (se 1 (by rfl) ⟨889046, by rfl⟩ : syracuseStep 1185395 = 1778093) B1778093
theorem B2135683 : Blo 1184409 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B1185411 : Blo 1184409 1185411 := bstep (se 1 (by rfl) ⟨889058, by rfl⟩ : syracuseStep 1185411 = 1778117) B1778117
theorem B1898129 : Blo 1184409 1898129 := bstep (se 2 (by rfl) ⟨711798, by rfl⟩ : syracuseStep 1898129 = 1423597) B1423597
theorem B1185427 : Blo 1184409 1185427 := bstep (se 1 (by rfl) ⟨889070, by rfl⟩ : syracuseStep 1185427 = 1778141) B1778141
theorem B1185443 : Blo 1184409 1185443 := bstep (se 1 (by rfl) ⟨889082, by rfl⟩ : syracuseStep 1185443 = 1778165) B1778165
theorem B4003505 : Blo 1184409 4003505 := bstep (se 2 (by rfl) ⟨1501314, by rfl⟩ : syracuseStep 4003505 = 3002629) B3002629
theorem B1185459 : Blo 1184409 1185459 := bstep (se 1 (by rfl) ⟨889094, by rfl⟩ : syracuseStep 1185459 = 1778189) B1778189
theorem B1332931 : Blo 1184409 1332931 := bstep (se 1 (by rfl) ⟨999698, by rfl⟩ : syracuseStep 1332931 = 1999397) B1999397
theorem B1185475 : Blo 1184409 1185475 := bstep (se 1 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 1185475 = 1778213) B1778213
theorem B1185491 : Blo 1184409 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B1185507 : Blo 1184409 1185507 := bstep (se 1 (by rfl) ⟨889130, by rfl⟩ : syracuseStep 1185507 = 1778261) B1778261
theorem B1185523 : Blo 1184409 1185523 := bstep (se 1 (by rfl) ⟨889142, by rfl⟩ : syracuseStep 1185523 = 1778285) B1778285
theorem B2250499 : Blo 1184409 2250499 := bstep (se 1 (by rfl) ⟨1687874, by rfl⟩ : syracuseStep 2250499 = 3375749) B3375749
theorem B1185539 : Blo 1184409 1185539 := bstep (se 1 (by rfl) ⟨889154, by rfl⟩ : syracuseStep 1185539 = 1778309) B1778309
theorem B1898257 : Blo 1184409 1898257 := bstep (se 2 (by rfl) ⟨711846, by rfl⟩ : syracuseStep 1898257 = 1423693) B1423693
theorem B1185555 : Blo 1184409 1185555 := bstep (se 1 (by rfl) ⟨889166, by rfl⟩ : syracuseStep 1185555 = 1778333) B1778333
theorem B1185571 : Blo 1184409 1185571 := bstep (se 1 (by rfl) ⟨889178, by rfl⟩ : syracuseStep 1185571 = 1778357) B1778357
theorem B2668337 : Blo 1184409 2668337 := bstep (se 2 (by rfl) ⟨1000626, by rfl⟩ : syracuseStep 2668337 = 2001253) B2001253
theorem B1185587 : Blo 1184409 1185587 := bstep (se 1 (by rfl) ⟨889190, by rfl⟩ : syracuseStep 1185587 = 1778381) B1778381
theorem B1185603 : Blo 1184409 1185603 := bstep (se 1 (by rfl) ⟨889202, by rfl⟩ : syracuseStep 1185603 = 1778405) B1778405
theorem B2668355 : Blo 1184409 2668355 := bstep (se 1 (by rfl) ⟨2001266, by rfl⟩ : syracuseStep 2668355 = 4002533) B4002533
theorem B1333075 : Blo 1184409 1333075 := bstep (se 1 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 1333075 = 1999613) B1999613
theorem B1185619 : Blo 1184409 1185619 := bstep (se 1 (by rfl) ⟨889214, by rfl⟩ : syracuseStep 1185619 = 1778429) B1778429
theorem B1185635 : Blo 1184409 1185635 := bstep (se 1 (by rfl) ⟨889226, by rfl⟩ : syracuseStep 1185635 = 1778453) B1778453
theorem B11401073 : Blo 1184409 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B1185651 : Blo 1184409 1185651 := bstep (se 1 (by rfl) ⟨889238, by rfl⟩ : syracuseStep 1185651 = 1778477) B1778477
theorem B1185667 : Blo 1184409 1185667 := bstep (se 1 (by rfl) ⟨889250, by rfl⟩ : syracuseStep 1185667 = 1778501) B1778501
theorem B6403981 : Blo 1184409 6403981 := bstep (se 3 (by rfl) ⟨1200746, by rfl⟩ : syracuseStep 6403981 = 2401493) B2401493
theorem B1185683 : Blo 1184409 1185683 := bstep (se 1 (by rfl) ⟨889262, by rfl⟩ : syracuseStep 1185683 = 1778525) B1778525
theorem B2250659 : Blo 1184409 2250659 := bstep (se 1 (by rfl) ⟨1687994, by rfl⟩ : syracuseStep 2250659 = 3375989) B3375989
theorem B1185699 : Blo 1184409 1185699 := bstep (se 1 (by rfl) ⟨889274, by rfl⟩ : syracuseStep 1185699 = 1778549) B1778549
theorem B1185715 : Blo 1184409 1185715 := bstep (se 1 (by rfl) ⟨889286, by rfl⟩ : syracuseStep 1185715 = 1778573) B1778573
theorem B1185731 : Blo 1184409 1185731 := bstep (se 1 (by rfl) ⟨889298, by rfl⟩ : syracuseStep 1185731 = 1778597) B1778597
theorem B1185747 : Blo 1184409 1185747 := bstep (se 1 (by rfl) ⟨889310, by rfl⟩ : syracuseStep 1185747 = 1778621) B1778621
theorem B1333219 : Blo 1184409 1333219 := bstep (se 1 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 1333219 = 1999829) B1999829
theorem B1185763 : Blo 1184409 1185763 := bstep (se 1 (by rfl) ⟨889322, by rfl⟩ : syracuseStep 1185763 = 1778645) B1778645
theorem B3799025 : Blo 1184409 3799025 := bstep (se 2 (by rfl) ⟨1424634, by rfl⟩ : syracuseStep 3799025 = 2849269) B2849269
theorem B1185779 : Blo 1184409 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B1185795 : Blo 1184409 1185795 := bstep (se 1 (by rfl) ⟨889346, by rfl⟩ : syracuseStep 1185795 = 1778693) B1778693
theorem B3373073 : Blo 1184409 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B1185811 : Blo 1184409 1185811 := bstep (se 1 (by rfl) ⟨889358, by rfl⟩ : syracuseStep 1185811 = 1778717) B1778717
theorem B1185827 : Blo 1184409 1185827 := bstep (se 1 (by rfl) ⟨889370, by rfl⟩ : syracuseStep 1185827 = 1778741) B1778741
theorem B1185843 : Blo 1184409 1185843 := bstep (se 1 (by rfl) ⟨889382, by rfl⟩ : syracuseStep 1185843 = 1778765) B1778765
theorem B1185859 : Blo 1184409 1185859 := bstep (se 1 (by rfl) ⟨889394, by rfl⟩ : syracuseStep 1185859 = 1778789) B1778789
theorem B2668625 : Blo 1184409 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B1185875 : Blo 1184409 1185875 := bstep (se 1 (by rfl) ⟨889406, by rfl⟩ : syracuseStep 1185875 = 1778813) B1778813
theorem B1185891 : Blo 1184409 1185891 := bstep (se 1 (by rfl) ⟨889418, by rfl⟩ : syracuseStep 1185891 = 1778837) B1778837
theorem B2668643 : Blo 1184409 2668643 := bstep (se 1 (by rfl) ⟨2001482, by rfl⟩ : syracuseStep 2668643 = 4002965) B4002965
theorem B3799153 : Blo 1184409 3799153 := bstep (se 2 (by rfl) ⟨1424682, by rfl⟩ : syracuseStep 3799153 = 2849365) B2849365
theorem B1333363 : Blo 1184409 1333363 := bstep (se 1 (by rfl) ⟨1000022, by rfl⟩ : syracuseStep 1333363 = 2000045) B2000045
theorem B1185907 : Blo 1184409 1185907 := bstep (se 1 (by rfl) ⟨889430, by rfl⟩ : syracuseStep 1185907 = 1778861) B1778861
theorem B1185923 : Blo 1184409 1185923 := bstep (se 1 (by rfl) ⟨889442, by rfl⟩ : syracuseStep 1185923 = 1778885) B1778885
theorem B1898641 : Blo 1184409 1898641 := bstep (se 2 (by rfl) ⟨711990, by rfl⟩ : syracuseStep 1898641 = 1423981) B1423981
theorem B1185939 : Blo 1184409 1185939 := bstep (se 1 (by rfl) ⟨889454, by rfl⟩ : syracuseStep 1185939 = 1778909) B1778909
theorem B1185955 : Blo 1184409 1185955 := bstep (se 1 (by rfl) ⟨889466, by rfl⟩ : syracuseStep 1185955 = 1778933) B1778933
theorem B1185971 : Blo 1184409 1185971 := bstep (se 1 (by rfl) ⟨889478, by rfl⟩ : syracuseStep 1185971 = 1778957) B1778957
theorem B1185987 : Blo 1184409 1185987 := bstep (se 1 (by rfl) ⟨889490, by rfl⟩ : syracuseStep 1185987 = 1778981) B1778981
theorem B4004045 : Blo 1184409 4004045 := bstep (se 3 (by rfl) ⟨750758, by rfl⟩ : syracuseStep 4004045 = 1501517) B1501517
theorem B3373265 : Blo 1184409 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B1186003 : Blo 1184409 1186003 := bstep (se 1 (by rfl) ⟨889502, by rfl⟩ : syracuseStep 1186003 = 1779005) B1779005
theorem B1186019 : Blo 1184409 1186019 := bstep (se 1 (by rfl) ⟨889514, by rfl⟩ : syracuseStep 1186019 = 1779029) B1779029
theorem B1186035 : Blo 1184409 1186035 := bstep (se 1 (by rfl) ⟨889526, by rfl⟩ : syracuseStep 1186035 = 1779053) B1779053
theorem B1333507 : Blo 1184409 1333507 := bstep (se 1 (by rfl) ⟨1000130, by rfl⟩ : syracuseStep 1333507 = 2000261) B2000261
theorem B1186051 : Blo 1184409 1186051 := bstep (se 1 (by rfl) ⟨889538, by rfl⟩ : syracuseStep 1186051 = 1779077) B1779077
theorem B4004099 : Blo 1184409 4004099 := bstep (se 1 (by rfl) ⟨3003074, by rfl⟩ : syracuseStep 4004099 = 6006149) B6006149
theorem B1186067 : Blo 1184409 1186067 := bstep (se 1 (by rfl) ⟨889550, by rfl⟩ : syracuseStep 1186067 = 1779101) B1779101
theorem B1186083 : Blo 1184409 1186083 := bstep (se 1 (by rfl) ⟨889562, by rfl⟩ : syracuseStep 1186083 = 1779125) B1779125
theorem B1186099 : Blo 1184409 1186099 := bstep (se 1 (by rfl) ⟨889574, by rfl⟩ : syracuseStep 1186099 = 1779149) B1779149
theorem B1186115 : Blo 1184409 1186115 := bstep (se 1 (by rfl) ⟨889586, by rfl⟩ : syracuseStep 1186115 = 1779173) B1779173
theorem B11385157 : Blo 1184409 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B1186131 : Blo 1184409 1186131 := bstep (se 1 (by rfl) ⟨889598, by rfl⟩ : syracuseStep 1186131 = 1779197) B1779197
theorem B1186147 : Blo 1184409 1186147 := bstep (se 1 (by rfl) ⟨889610, by rfl⟩ : syracuseStep 1186147 = 1779221) B1779221
theorem B2668913 : Blo 1184409 2668913 := bstep (se 2 (by rfl) ⟨1000842, by rfl⟩ : syracuseStep 2668913 = 2001685) B2001685
theorem B1186163 : Blo 1184409 1186163 := bstep (se 1 (by rfl) ⟨889622, by rfl⟩ : syracuseStep 1186163 = 1779245) B1779245
theorem B1186179 : Blo 1184409 1186179 := bstep (se 1 (by rfl) ⟨889634, by rfl⟩ : syracuseStep 1186179 = 1779269) B1779269
theorem B2668931 : Blo 1184409 2668931 := bstep (se 1 (by rfl) ⟨2001698, by rfl⟩ : syracuseStep 2668931 = 4003397) B4003397
theorem B1898897 : Blo 1184409 1898897 := bstep (se 2 (by rfl) ⟨712086, by rfl⟩ : syracuseStep 1898897 = 1424173) B1424173
theorem B1333651 : Blo 1184409 1333651 := bstep (se 1 (by rfl) ⟨1000238, by rfl⟩ : syracuseStep 1333651 = 2000477) B2000477
theorem B1186195 : Blo 1184409 1186195 := bstep (se 1 (by rfl) ⟨889646, by rfl⟩ : syracuseStep 1186195 = 1779293) B1779293
theorem B1186211 : Blo 1184409 1186211 := bstep (se 1 (by rfl) ⟨889658, by rfl⟩ : syracuseStep 1186211 = 1779317) B1779317
theorem B1186227 : Blo 1184409 1186227 := bstep (se 1 (by rfl) ⟨889670, by rfl⟩ : syracuseStep 1186227 = 1779341) B1779341
theorem B1186243 : Blo 1184409 1186243 := bstep (se 1 (by rfl) ⟨889682, by rfl⟩ : syracuseStep 1186243 = 1779365) B1779365
theorem B1186259 : Blo 1184409 1186259 := bstep (se 1 (by rfl) ⟨889694, by rfl⟩ : syracuseStep 1186259 = 1779389) B1779389
theorem B1186275 : Blo 1184409 1186275 := bstep (se 1 (by rfl) ⟨889706, by rfl⟩ : syracuseStep 1186275 = 1779413) B1779413
theorem B1186291 : Blo 1184409 1186291 := bstep (se 1 (by rfl) ⟨889718, by rfl⟩ : syracuseStep 1186291 = 1779437) B1779437
theorem B1186307 : Blo 1184409 1186307 := bstep (se 1 (by rfl) ⟨889730, by rfl⟩ : syracuseStep 1186307 = 1779461) B1779461
theorem B1186323 : Blo 1184409 1186323 := bstep (se 1 (by rfl) ⟨889742, by rfl⟩ : syracuseStep 1186323 = 1779485) B1779485
theorem B1333795 : Blo 1184409 1333795 := bstep (se 1 (by rfl) ⟨1000346, by rfl⟩ : syracuseStep 1333795 = 2000693) B2000693
theorem B1186339 : Blo 1184409 1186339 := bstep (se 1 (by rfl) ⟨889754, by rfl⟩ : syracuseStep 1186339 = 1779509) B1779509
theorem B3381805 : Blo 1184409 3381805 := bstep (se 3 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 3381805 = 1268177) B1268177
theorem B1186355 : Blo 1184409 1186355 := bstep (se 1 (by rfl) ⟨889766, by rfl⟩ : syracuseStep 1186355 = 1779533) B1779533
theorem B1186371 : Blo 1184409 1186371 := bstep (se 1 (by rfl) ⟨889778, by rfl⟩ : syracuseStep 1186371 = 1779557) B1779557
theorem B5061197 : Blo 1184409 5061197 := bstep (se 3 (by rfl) ⟨948974, by rfl⟩ : syracuseStep 5061197 = 1897949) B1897949
theorem B1186387 : Blo 1184409 1186387 := bstep (se 1 (by rfl) ⟨889790, by rfl⟩ : syracuseStep 1186387 = 1779581) B1779581
theorem B1186403 : Blo 1184409 1186403 := bstep (se 1 (by rfl) ⟨889802, by rfl⟩ : syracuseStep 1186403 = 1779605) B1779605
theorem B2136721 : Blo 1184409 2136721 := bstep (se 2 (by rfl) ⟨801270, by rfl⟩ : syracuseStep 2136721 = 1602541) B1602541
theorem B2669201 : Blo 1184409 2669201 := bstep (se 2 (by rfl) ⟨1000950, by rfl⟩ : syracuseStep 2669201 = 2001901) B2001901
theorem B2669219 : Blo 1184409 2669219 := bstep (se 1 (by rfl) ⟨2001914, by rfl⟩ : syracuseStep 2669219 = 4003829) B4003829
theorem B7600817 : Blo 1184409 7600817 := bstep (se 2 (by rfl) ⟨2850306, by rfl⟩ : syracuseStep 7600817 = 5700613) B5700613
theorem B1333939 : Blo 1184409 1333939 := bstep (se 1 (by rfl) ⟨1000454, by rfl⟩ : syracuseStep 1333939 = 2000909) B2000909
theorem B3201731 : Blo 1184409 3201731 := bstep (se 1 (by rfl) ⟨2401298, by rfl⟩ : syracuseStep 3201731 = 4802597) B4802597
theorem B7592717 : Blo 1184409 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B4504355 : Blo 1184409 4504355 := bstep (se 1 (by rfl) ⟨3378266, by rfl⟩ : syracuseStep 4504355 = 6756533) B6756533
theorem B4504369 : Blo 1184409 4504369 := bstep (se 2 (by rfl) ⟨1689138, by rfl⟩ : syracuseStep 4504369 = 3378277) B3378277
theorem B32889653 : Blo 1184409 32889653 := bstep (se 5 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 32889653 = 3083405) B3083405
theorem B1334083 : Blo 1184409 1334083 := bstep (se 1 (by rfl) ⟨1000562, by rfl⟩ : syracuseStep 1334083 = 2001125) B2001125
theorem B2251729 : Blo 1184409 2251729 := bstep (se 2 (by rfl) ⟨844398, by rfl⟩ : syracuseStep 2251729 = 1688797) B1688797
theorem B1334227 : Blo 1184409 1334227 := bstep (se 1 (by rfl) ⟨1000670, by rfl⟩ : syracuseStep 1334227 = 2001341) B2001341
theorem B1776641 : Blo 1184409 1776641 := bstep (se 2 (by rfl) ⟨666240, by rfl⟩ : syracuseStep 1776641 = 1332481) B1332481
theorem B1776659 : Blo 1184409 1776659 := bstep (se 1 (by rfl) ⟨1332494, by rfl⟩ : syracuseStep 1776659 = 2664989) B2664989
theorem B1776689 : Blo 1184409 1776689 := bstep (se 2 (by rfl) ⟨666258, by rfl⟩ : syracuseStep 1776689 = 1332517) B1332517
theorem B1776707 : Blo 1184409 1776707 := bstep (se 1 (by rfl) ⟨1332530, by rfl⟩ : syracuseStep 1776707 = 2665061) B2665061
theorem B3800141 : Blo 1184409 3800141 := bstep (se 3 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 3800141 = 1425053) B1425053
theorem B1350739 : Blo 1184409 1350739 := bstep (se 1 (by rfl) ⟨1013054, by rfl⟩ : syracuseStep 1350739 = 2026109) B2026109
theorem B1776737 : Blo 1184409 1776737 := bstep (se 2 (by rfl) ⟨666276, by rfl⟩ : syracuseStep 1776737 = 1332553) B1332553
theorem B1334371 : Blo 1184409 1334371 := bstep (se 1 (by rfl) ⟨1000778, by rfl⟩ : syracuseStep 1334371 = 2001557) B2001557
theorem B1776755 : Blo 1184409 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1776785 : Blo 1184409 1776785 := bstep (se 2 (by rfl) ⟨666294, by rfl⟩ : syracuseStep 1776785 = 1332589) B1332589
theorem B1686673 : Blo 1184409 1686673 := bstep (se 2 (by rfl) ⟨632502, by rfl⟩ : syracuseStep 1686673 = 1265005) B1265005
theorem B1776803 : Blo 1184409 1776803 := bstep (se 1 (by rfl) ⟨1332602, by rfl⟩ : syracuseStep 1776803 = 2665205) B2665205
theorem B3374257 : Blo 1184409 3374257 := bstep (se 2 (by rfl) ⟨1265346, by rfl⟩ : syracuseStep 3374257 = 2530693) B2530693
theorem B1776833 : Blo 1184409 1776833 := bstep (se 2 (by rfl) ⟨666312, by rfl⟩ : syracuseStep 1776833 = 1332625) B1332625
theorem B1776851 : Blo 1184409 1776851 := bstep (se 1 (by rfl) ⟨1332638, by rfl⟩ : syracuseStep 1776851 = 2665277) B2665277
theorem B1776881 : Blo 1184409 1776881 := bstep (se 2 (by rfl) ⟨666330, by rfl⟩ : syracuseStep 1776881 = 1332661) B1332661
theorem B1334515 : Blo 1184409 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B1776899 : Blo 1184409 1776899 := bstep (se 1 (by rfl) ⟨1332674, by rfl⟩ : syracuseStep 1776899 = 2665349) B2665349
theorem B1776929 : Blo 1184409 1776929 := bstep (se 2 (by rfl) ⟨666348, by rfl⟩ : syracuseStep 1776929 = 1332697) B1332697
theorem B1776947 : Blo 1184409 1776947 := bstep (se 1 (by rfl) ⟨1332710, by rfl⟩ : syracuseStep 1776947 = 2665421) B2665421
theorem B1776977 : Blo 1184409 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B1711441 : Blo 1184409 1711441 := bstep (se 2 (by rfl) ⟨641790, by rfl⟩ : syracuseStep 1711441 = 1283581) B1283581
theorem B1776995 : Blo 1184409 1776995 := bstep (se 1 (by rfl) ⟨1332746, by rfl⟩ : syracuseStep 1776995 = 2665493) B2665493
theorem B1777025 : Blo 1184409 1777025 := bstep (se 2 (by rfl) ⟨666384, by rfl⟩ : syracuseStep 1777025 = 1332769) B1332769
theorem B1334659 : Blo 1184409 1334659 := bstep (se 1 (by rfl) ⟨1000994, by rfl⟩ : syracuseStep 1334659 = 2001989) B2001989
theorem B1777043 : Blo 1184409 1777043 := bstep (se 1 (by rfl) ⟨1332782, by rfl⟩ : syracuseStep 1777043 = 2665565) B2665565
theorem B1777073 : Blo 1184409 1777073 := bstep (se 2 (by rfl) ⟨666402, by rfl⟩ : syracuseStep 1777073 = 1332805) B1332805
theorem B1777091 : Blo 1184409 1777091 := bstep (se 1 (by rfl) ⟨1332818, by rfl⟩ : syracuseStep 1777091 = 2665637) B2665637
theorem B3374531 : Blo 1184409 3374531 := bstep (se 1 (by rfl) ⟨2530898, by rfl⟩ : syracuseStep 3374531 = 5061797) B5061797
theorem B2530769 : Blo 1184409 2530769 := bstep (se 2 (by rfl) ⟨949038, by rfl⟩ : syracuseStep 2530769 = 1898077) B1898077
theorem B1777121 : Blo 1184409 1777121 := bstep (se 2 (by rfl) ⟨666420, by rfl⟩ : syracuseStep 1777121 = 1332841) B1332841
theorem B1687009 : Blo 1184409 1687009 := bstep (se 2 (by rfl) ⟨632628, by rfl⟩ : syracuseStep 1687009 = 1265257) B1265257
theorem B1777139 : Blo 1184409 1777139 := bstep (se 1 (by rfl) ⟨1332854, by rfl⟩ : syracuseStep 1777139 = 2665709) B2665709
theorem B1424899 : Blo 1184409 1424899 := bstep (se 1 (by rfl) ⟨1068674, by rfl⟩ : syracuseStep 1424899 = 2137349) B2137349
theorem B3202573 : Blo 1184409 3202573 := bstep (se 3 (by rfl) ⟨600482, by rfl⟩ : syracuseStep 3202573 = 1200965) B1200965
theorem B1777169 : Blo 1184409 1777169 := bstep (se 2 (by rfl) ⟨666438, by rfl⟩ : syracuseStep 1777169 = 1332877) B1332877
theorem B1777187 : Blo 1184409 1777187 := bstep (se 1 (by rfl) ⟨1332890, by rfl⟩ : syracuseStep 1777187 = 2665781) B2665781
theorem B1777217 : Blo 1184409 1777217 := bstep (se 2 (by rfl) ⟨666456, by rfl⟩ : syracuseStep 1777217 = 1332913) B1332913
theorem B1777235 : Blo 1184409 1777235 := bstep (se 1 (by rfl) ⟨1332926, by rfl⟩ : syracuseStep 1777235 = 2665853) B2665853
theorem B1777265 : Blo 1184409 1777265 := bstep (se 2 (by rfl) ⟨666474, by rfl⟩ : syracuseStep 1777265 = 1332949) B1332949
theorem B1777283 : Blo 1184409 1777283 := bstep (se 1 (by rfl) ⟨1332962, by rfl⟩ : syracuseStep 1777283 = 2665925) B2665925
theorem B3374723 : Blo 1184409 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B1777313 : Blo 1184409 1777313 := bstep (se 2 (by rfl) ⟨666492, by rfl⟩ : syracuseStep 1777313 = 1332985) B1332985
theorem B1777331 : Blo 1184409 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B1777361 : Blo 1184409 1777361 := bstep (se 2 (by rfl) ⟨666510, by rfl⟩ : syracuseStep 1777361 = 1333021) B1333021
theorem B1777379 : Blo 1184409 1777379 := bstep (se 1 (by rfl) ⟨1333034, by rfl⟩ : syracuseStep 1777379 = 2666069) B2666069
theorem B1777409 : Blo 1184409 1777409 := bstep (se 2 (by rfl) ⟨666528, by rfl⟩ : syracuseStep 1777409 = 1333057) B1333057
theorem B10133261 : Blo 1184409 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B3997457 : Blo 1184409 3997457 := bstep (se 2 (by rfl) ⟨1499046, by rfl⟩ : syracuseStep 3997457 = 2998093) B2998093
theorem B1777427 : Blo 1184409 1777427 := bstep (se 1 (by rfl) ⟨1333070, by rfl⟩ : syracuseStep 1777427 = 2666141) B2666141
theorem B1900307 : Blo 1184409 1900307 := bstep (se 1 (by rfl) ⟨1425230, by rfl⟩ : syracuseStep 1900307 = 2850461) B2850461
theorem B1777457 : Blo 1184409 1777457 := bstep (se 2 (by rfl) ⟨666546, by rfl⟩ : syracuseStep 1777457 = 1333093) B1333093
theorem B6004529 : Blo 1184409 6004529 := bstep (se 2 (by rfl) ⟨2251698, by rfl⟩ : syracuseStep 6004529 = 4503397) B4503397
theorem B1777475 : Blo 1184409 1777475 := bstep (se 1 (by rfl) ⟨1333106, by rfl⟩ : syracuseStep 1777475 = 2666213) B2666213
theorem B1777505 : Blo 1184409 1777505 := bstep (se 2 (by rfl) ⟨666564, by rfl⟩ : syracuseStep 1777505 = 1333129) B1333129
theorem B1777523 : Blo 1184409 1777523 := bstep (se 1 (by rfl) ⟨1333142, by rfl⟩ : syracuseStep 1777523 = 2666285) B2666285
theorem B5996429 : Blo 1184409 5996429 := bstep (se 3 (by rfl) ⟨1124330, by rfl⟩ : syracuseStep 5996429 = 2248661) B2248661
theorem B1777553 : Blo 1184409 1777553 := bstep (se 2 (by rfl) ⟨666582, by rfl⟩ : syracuseStep 1777553 = 1333165) B1333165
theorem B1777571 : Blo 1184409 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B1998769 : Blo 1184409 1998769 := bstep (se 2 (by rfl) ⟨749538, by rfl⟩ : syracuseStep 1998769 = 1499077) B1499077
theorem B1777601 : Blo 1184409 1777601 := bstep (se 2 (by rfl) ⟨666600, by rfl⟩ : syracuseStep 1777601 = 1333201) B1333201
theorem B1998803 : Blo 1184409 1998803 := bstep (se 1 (by rfl) ⟨1499102, by rfl⟩ : syracuseStep 1998803 = 2998205) B2998205
theorem B1777619 : Blo 1184409 1777619 := bstep (se 1 (by rfl) ⟨1333214, by rfl⟩ : syracuseStep 1777619 = 2666429) B2666429
theorem B3039203 : Blo 1184409 3039203 := bstep (se 1 (by rfl) ⟨2279402, by rfl⟩ : syracuseStep 3039203 = 4558805) B4558805
theorem B1777649 : Blo 1184409 1777649 := bstep (se 2 (by rfl) ⟨666618, by rfl⟩ : syracuseStep 1777649 = 1333237) B1333237
theorem B2531351 : Blo 1184409 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B1777739 : Blo 1184409 1777739 := bstep (se 1 (by rfl) ⟨1333304, by rfl⟩ : syracuseStep 1777739 = 2666609) B2666609
theorem B3375179 : Blo 1184409 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B1777751 : Blo 1184409 1777751 := bstep (se 1 (by rfl) ⟨1333313, by rfl⟩ : syracuseStep 1777751 = 2666627) B2666627
theorem B4808855 : Blo 1184409 4808855 := bstep (se 1 (by rfl) ⟨3606641, by rfl⟩ : syracuseStep 4808855 = 7213283) B7213283
theorem B1777817 : Blo 1184409 1777817 := bstep (se 2 (by rfl) ⟨666681, by rfl⟩ : syracuseStep 1777817 = 1333363) B1333363
theorem B3997889 : Blo 1184409 3997889 := bstep (se 2 (by rfl) ⟨1499208, by rfl⟩ : syracuseStep 3997889 = 2998417) B2998417
theorem B2531521 : Blo 1184409 2531521 := bstep (se 2 (by rfl) ⟨949320, by rfl⟩ : syracuseStep 2531521 = 1898641) B1898641
theorem B1777931 : Blo 1184409 1777931 := bstep (se 1 (by rfl) ⟨1333448, by rfl⟩ : syracuseStep 1777931 = 2666897) B2666897
theorem B1999127 : Blo 1184409 1999127 := bstep (se 1 (by rfl) ⟨1499345, by rfl⟩ : syracuseStep 1999127 = 2998691) B2998691
theorem B1777943 : Blo 1184409 1777943 := bstep (se 1 (by rfl) ⟨1333457, by rfl⟩ : syracuseStep 1777943 = 2666915) B2666915
theorem B2998579 : Blo 1184409 2998579 := bstep (se 1 (by rfl) ⟨2248934, by rfl⟩ : syracuseStep 2998579 = 4497869) B4497869
theorem B1499467 : Blo 1184409 1499467 := bstep (se 1 (by rfl) ⟨1124600, by rfl⟩ : syracuseStep 1499467 = 2249201) B2249201
theorem B1778009 : Blo 1184409 1778009 := bstep (se 2 (by rfl) ⟨666753, by rfl⟩ : syracuseStep 1778009 = 1333507) B1333507
theorem B1999255 : Blo 1184409 1999255 := bstep (se 1 (by rfl) ⟨1499441, by rfl⟩ : syracuseStep 1999255 = 2998883) B2998883
theorem B4055447 : Blo 1184409 4055447 := bstep (se 1 (by rfl) ⟨3041585, by rfl⟩ : syracuseStep 4055447 = 6083171) B6083171
theorem B15180209 : Blo 1184409 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B2998721 : Blo 1184409 2998721 := bstep (se 2 (by rfl) ⟨1124520, by rfl⟩ : syracuseStep 2998721 = 2249041) B2249041
theorem B1778123 : Blo 1184409 1778123 := bstep (se 1 (by rfl) ⟨1333592, by rfl⟩ : syracuseStep 1778123 = 2667185) B2667185
theorem B1778135 : Blo 1184409 1778135 := bstep (se 1 (by rfl) ⟨1333601, by rfl⟩ : syracuseStep 1778135 = 2667203) B2667203
theorem B1778201 : Blo 1184409 1778201 := bstep (se 2 (by rfl) ⟨666825, by rfl⟩ : syracuseStep 1778201 = 1333651) B1333651
theorem B8995373 : Blo 1184409 8995373 := bstep (se 3 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 8995373 = 3373265) B3373265
theorem B4874827 : Blo 1184409 4874827 := bstep (se 1 (by rfl) ⟨3656120, by rfl⟩ : syracuseStep 4874827 = 7312241) B7312241
theorem B1499735 : Blo 1184409 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B4498051 : Blo 1184409 4498051 := bstep (se 1 (by rfl) ⟨3373538, by rfl⟩ : syracuseStep 4498051 = 6747077) B6747077
theorem B1778315 : Blo 1184409 1778315 := bstep (se 1 (by rfl) ⟨1333736, by rfl⟩ : syracuseStep 1778315 = 2667473) B2667473
theorem B13501079 : Blo 1184409 13501079 := bstep (se 1 (by rfl) ⟨10125809, by rfl⟩ : syracuseStep 13501079 = 20251619) B20251619
theorem B1778327 : Blo 1184409 1778327 := bstep (se 1 (by rfl) ⟨1333745, by rfl⟩ : syracuseStep 1778327 = 2667491) B2667491
theorem B2704087 : Blo 1184409 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B1778393 : Blo 1184409 1778393 := bstep (se 2 (by rfl) ⟨666897, by rfl⟩ : syracuseStep 1778393 = 1333795) B1333795
theorem B3998429 : Blo 1184409 3998429 := bstep (se 3 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 3998429 = 1499411) B1499411
theorem B1778507 : Blo 1184409 1778507 := bstep (se 1 (by rfl) ⟨1333880, by rfl⟩ : syracuseStep 1778507 = 2667761) B2667761
theorem B1778519 : Blo 1184409 1778519 := bstep (se 1 (by rfl) ⟨1333889, by rfl⟩ : syracuseStep 1778519 = 2667779) B2667779
theorem B1778585 : Blo 1184409 1778585 := bstep (se 2 (by rfl) ⟨666969, by rfl⟩ : syracuseStep 1778585 = 1333939) B1333939
theorem B4498355 : Blo 1184409 4498355 := bstep (se 1 (by rfl) ⟨3373766, by rfl⟩ : syracuseStep 4498355 = 6747533) B6747533
theorem B5694425 : Blo 1184409 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B1999883 : Blo 1184409 1999883 := bstep (se 1 (by rfl) ⟨1499912, by rfl⟩ : syracuseStep 1999883 = 2999825) B2999825
theorem B1778699 : Blo 1184409 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1778711 : Blo 1184409 1778711 := bstep (se 1 (by rfl) ⟨1334033, by rfl⟩ : syracuseStep 1778711 = 2668067) B2668067
theorem B10806317 : Blo 1184409 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B5063725 : Blo 1184409 5063725 := bstep (se 3 (by rfl) ⟨949448, by rfl⟩ : syracuseStep 5063725 = 1898897) B1898897
theorem B6005825 : Blo 1184409 6005825 := bstep (se 2 (by rfl) ⟨2252184, by rfl⟩ : syracuseStep 6005825 = 4504369) B4504369
theorem B1778777 : Blo 1184409 1778777 := bstep (se 2 (by rfl) ⟨667041, by rfl⟩ : syracuseStep 1778777 = 1334083) B1334083
theorem B2000011 : Blo 1184409 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B1778891 : Blo 1184409 1778891 := bstep (se 1 (by rfl) ⟨1334168, by rfl⟩ : syracuseStep 1778891 = 2668337) B2668337
theorem B1778903 : Blo 1184409 1778903 := bstep (se 1 (by rfl) ⟨1334177, by rfl⟩ : syracuseStep 1778903 = 2668355) B2668355
theorem B5063897 : Blo 1184409 5063897 := bstep (se 2 (by rfl) ⟨1898961, by rfl⟩ : syracuseStep 5063897 = 3797923) B3797923
theorem B1500439 : Blo 1184409 1500439 := bstep (se 1 (by rfl) ⟨1125329, by rfl⟩ : syracuseStep 1500439 = 2250659) B2250659
theorem B2000153 : Blo 1184409 2000153 := bstep (se 2 (by rfl) ⟨750057, by rfl⟩ : syracuseStep 2000153 = 1500115) B1500115
theorem B1778969 : Blo 1184409 1778969 := bstep (se 2 (by rfl) ⟨667113, by rfl⟩ : syracuseStep 1778969 = 1334227) B1334227
theorem B2532683 : Blo 1184409 2532683 := bstep (se 1 (by rfl) ⟨1899512, by rfl⟩ : syracuseStep 2532683 = 3799025) B3799025
theorem B2704727 : Blo 1184409 2704727 := bstep (se 1 (by rfl) ⟨2028545, by rfl⟩ : syracuseStep 2704727 = 4057091) B4057091
theorem B1779083 : Blo 1184409 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B1779095 : Blo 1184409 1779095 := bstep (se 1 (by rfl) ⟨1334321, by rfl⟩ : syracuseStep 1779095 = 2668643) B2668643
theorem B2000281 : Blo 1184409 2000281 := bstep (se 2 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 2000281 = 1500211) B1500211
theorem B1779161 : Blo 1184409 1779161 := bstep (se 2 (by rfl) ⟨667185, by rfl⟩ : syracuseStep 1779161 = 1334371) B1334371
theorem B4499009 : Blo 1184409 4499009 := bstep (se 2 (by rfl) ⟨1687128, by rfl⟩ : syracuseStep 4499009 = 3374257) B3374257
theorem B1779275 : Blo 1184409 1779275 := bstep (se 1 (by rfl) ⟨1334456, by rfl⟩ : syracuseStep 1779275 = 2668913) B2668913
theorem B1779287 : Blo 1184409 1779287 := bstep (se 1 (by rfl) ⟨1334465, by rfl⟩ : syracuseStep 1779287 = 2668931) B2668931
theorem B5998211 : Blo 1184409 5998211 := bstep (se 1 (by rfl) ⟨4498658, by rfl⟩ : syracuseStep 5998211 = 8997317) B8997317
theorem B1779353 : Blo 1184409 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B2999987 : Blo 1184409 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B3376819 : Blo 1184409 3376819 := bstep (se 1 (by rfl) ⟨2532614, by rfl⟩ : syracuseStep 3376819 = 5065229) B5065229
theorem B24643277 : Blo 1184409 24643277 := bstep (se 3 (by rfl) ⟨4620614, by rfl⟩ : syracuseStep 24643277 = 9241229) B9241229
theorem B1779467 : Blo 1184409 1779467 := bstep (se 1 (by rfl) ⟨1334600, by rfl⟩ : syracuseStep 1779467 = 2669201) B2669201
theorem B1779479 : Blo 1184409 1779479 := bstep (se 1 (by rfl) ⟨1334609, by rfl⟩ : syracuseStep 1779479 = 2669219) B2669219
theorem B6408001 : Blo 1184409 6408001 := bstep (se 2 (by rfl) ⟨2403000, by rfl⟩ : syracuseStep 6408001 = 4806001) B4806001
theorem B3999563 : Blo 1184409 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B1779545 : Blo 1184409 1779545 := bstep (se 2 (by rfl) ⟨667329, by rfl⟩ : syracuseStep 1779545 = 1334659) B1334659
theorem B3377047 : Blo 1184409 3377047 := bstep (se 1 (by rfl) ⟨2532785, by rfl⟩ : syracuseStep 3377047 = 5065571) B5065571
theorem B123242417 : Blo 1184409 123242417 := bstep (se 2 (by rfl) ⟨46215906, by rfl⟩ : syracuseStep 123242417 = 92431813) B92431813
theorem B2000855 : Blo 1184409 2000855 := bstep (se 1 (by rfl) ⟨1500641, by rfl⟩ : syracuseStep 2000855 = 3001283) B3001283
theorem B8546309 : Blo 1184409 8546309 := bstep (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) B1602433
theorem B4270097 : Blo 1184409 4270097 := bstep (se 2 (by rfl) ⟨1601286, by rfl⟩ : syracuseStep 4270097 = 3202573) B3202573
theorem B2533427 : Blo 1184409 2533427 := bstep (se 1 (by rfl) ⟨1900070, by rfl⟩ : syracuseStep 2533427 = 3800141) B3800141
theorem B2000983 : Blo 1184409 2000983 := bstep (se 1 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 2000983 = 3001475) B3001475
theorem B3999833 : Blo 1184409 3999833 := bstep (se 2 (by rfl) ⟨1499937, by rfl⟩ : syracuseStep 3999833 = 2999875) B2999875
theorem B3000523 : Blo 1184409 3000523 := bstep (se 1 (by rfl) ⟨2250392, by rfl⟩ : syracuseStep 3000523 = 4500785) B4500785
theorem B5409089 : Blo 1184409 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B3000665 : Blo 1184409 3000665 := bstep (se 2 (by rfl) ⟨1125249, by rfl⟩ : syracuseStep 3000665 = 2250499) B2250499
theorem B20531555 : Blo 1184409 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B17090995 : Blo 1184409 17090995 := bstep (se 1 (by rfl) ⟨12818246, by rfl⟩ : syracuseStep 17090995 = 25636493) B25636493
theorem B2664971 : Blo 1184409 2664971 := bstep (se 1 (by rfl) ⟨1998728, by rfl⟩ : syracuseStep 2664971 = 3997457) B3997457
theorem B8538641 : Blo 1184409 8538641 := bstep (se 2 (by rfl) ⟨3201990, by rfl⟩ : syracuseStep 8538641 = 6403981) B6403981
theorem B2665025 : Blo 1184409 2665025 := bstep (se 2 (by rfl) ⟨999384, by rfl⟩ : syracuseStep 2665025 = 1998769) B1998769
theorem B8104541 : Blo 1184409 8104541 := bstep (se 3 (by rfl) ⟨1519601, by rfl⟩ : syracuseStep 8104541 = 3039203) B3039203
theorem B2001611 : Blo 1184409 2001611 := bstep (se 1 (by rfl) ⟨1501208, by rfl⟩ : syracuseStep 2001611 = 3002417) B3002417
theorem B4000535 : Blo 1184409 4000535 := bstep (se 1 (by rfl) ⟨3000401, by rfl⟩ : syracuseStep 4000535 = 6000803) B6000803
theorem B2665241 : Blo 1184409 2665241 := bstep (se 2 (by rfl) ⟨999465, by rfl⟩ : syracuseStep 2665241 = 1998931) B1998931
theorem B4500269 : Blo 1184409 4500269 := bstep (se 3 (by rfl) ⟨843800, by rfl⟩ : syracuseStep 4500269 = 1687601) B1687601
theorem B7211821 : Blo 1184409 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B5065537 : Blo 1184409 5065537 := bstep (se 2 (by rfl) ⟨1899576, by rfl⟩ : syracuseStep 5065537 = 3799153) B3799153
theorem B4500299 : Blo 1184409 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B2001739 : Blo 1184409 2001739 := bstep (se 1 (by rfl) ⟨1501304, by rfl⟩ : syracuseStep 2001739 = 3002609) B3002609
theorem B2665331 : Blo 1184409 2665331 := bstep (se 1 (by rfl) ⟨1998998, by rfl⟩ : syracuseStep 2665331 = 3997997) B3997997
theorem B2665367 : Blo 1184409 2665367 := bstep (se 1 (by rfl) ⟨1999025, by rfl⟩ : syracuseStep 2665367 = 3998051) B3998051
theorem B12331993 : Blo 1184409 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B2001881 : Blo 1184409 2001881 := bstep (se 2 (by rfl) ⟨750705, by rfl⟩ : syracuseStep 2001881 = 1501411) B1501411
theorem B2665547 : Blo 1184409 2665547 := bstep (se 1 (by rfl) ⟨1999160, by rfl⟩ : syracuseStep 2665547 = 3998321) B3998321
theorem B2002009 : Blo 1184409 2002009 := bstep (se 2 (by rfl) ⟨750753, by rfl⟩ : syracuseStep 2002009 = 1501507) B1501507
theorem B7203941 : Blo 1184409 7203941 := bstep (se 4 (by rfl) ⟨675369, by rfl⟩ : syracuseStep 7203941 = 1350739) B1350739
theorem B2665601 : Blo 1184409 2665601 := bstep (se 2 (by rfl) ⟨999600, by rfl⟩ : syracuseStep 2665601 = 1999201) B1999201
theorem B8113283 : Blo 1184409 8113283 := bstep (se 1 (by rfl) ⟨6084962, by rfl⟩ : syracuseStep 8113283 = 12169925) B12169925
theorem B3001495 : Blo 1184409 3001495 := bstep (se 1 (by rfl) ⟨2251121, by rfl⟩ : syracuseStep 3001495 = 4502243) B4502243
theorem B2567447 : Blo 1184409 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B4001075 : Blo 1184409 4001075 := bstep (se 1 (by rfl) ⟨3000806, by rfl⟩ : syracuseStep 4001075 = 6001613) B6001613
theorem B2665817 : Blo 1184409 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B4509073 : Blo 1184409 4509073 := bstep (se 2 (by rfl) ⟨1690902, by rfl⟩ : syracuseStep 4509073 = 3381805) B3381805
theorem B2665907 : Blo 1184409 2665907 := bstep (se 1 (by rfl) ⟨1999430, by rfl⟩ : syracuseStep 2665907 = 3998861) B3998861
theorem B2665943 : Blo 1184409 2665943 := bstep (se 1 (by rfl) ⟨1999457, by rfl⟩ : syracuseStep 2665943 = 3998915) B3998915
theorem B4500953 : Blo 1184409 4500953 := bstep (se 2 (by rfl) ⟨1687857, by rfl⟩ : syracuseStep 4500953 = 3375715) B3375715
theorem B5410327 : Blo 1184409 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B4001345 : Blo 1184409 4001345 := bstep (se 2 (by rfl) ⟨1500504, by rfl⟩ : syracuseStep 4001345 = 3001009) B3001009
theorem B3001931 : Blo 1184409 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B2666123 : Blo 1184409 2666123 := bstep (se 1 (by rfl) ⟨1999592, by rfl⟩ : syracuseStep 2666123 = 3999185) B3999185
theorem B20803223 : Blo 1184409 20803223 := bstep (se 1 (by rfl) ⟨15602417, by rfl⟩ : syracuseStep 20803223 = 31204835) B31204835
theorem B11390615 : Blo 1184409 11390615 := bstep (se 1 (by rfl) ⟨8542961, by rfl⟩ : syracuseStep 11390615 = 17085923) B17085923
theorem B2666177 : Blo 1184409 2666177 := bstep (se 2 (by rfl) ⟨999816, by rfl⟩ : syracuseStep 2666177 = 1999633) B1999633
theorem B1265419 : Blo 1184409 1265419 := bstep (se 1 (by rfl) ⟨949064, by rfl⟩ : syracuseStep 1265419 = 1898129) B1898129
theorem B4501271 : Blo 1184409 4501271 := bstep (se 1 (by rfl) ⟨3375953, by rfl⟩ : syracuseStep 4501271 = 6751907) B6751907
theorem B4329281 : Blo 1184409 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2666393 : Blo 1184409 2666393 := bstep (se 2 (by rfl) ⟨999897, by rfl⟩ : syracuseStep 2666393 = 1999795) B1999795
theorem B3002305 : Blo 1184409 3002305 := bstep (se 2 (by rfl) ⟨1125864, by rfl⟩ : syracuseStep 3002305 = 2251729) B2251729
theorem B2666483 : Blo 1184409 2666483 := bstep (se 1 (by rfl) ⟨1999862, by rfl⟩ : syracuseStep 2666483 = 3999725) B3999725
theorem B2248715 : Blo 1184409 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B2666519 : Blo 1184409 2666519 := bstep (se 1 (by rfl) ⟨1999889, by rfl⟩ : syracuseStep 2666519 = 3999779) B3999779
theorem B2166809 : Blo 1184409 2166809 := bstep (se 2 (by rfl) ⟨812553, by rfl⟩ : syracuseStep 2166809 = 1625107) B1625107
theorem B2846771 : Blo 1184409 2846771 := bstep (se 1 (by rfl) ⟨2135078, by rfl⟩ : syracuseStep 2846771 = 4270157) B4270157
theorem B4272203 : Blo 1184409 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B4001885 : Blo 1184409 4001885 := bstep (se 3 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 4001885 = 1500707) B1500707
theorem B7598231 : Blo 1184409 7598231 := bstep (se 1 (by rfl) ⟨5698673, by rfl⟩ : syracuseStep 7598231 = 11397347) B11397347
theorem B2248897 : Blo 1184409 2248897 := bstep (se 2 (by rfl) ⟨843336, by rfl⟩ : syracuseStep 2248897 = 1686673) B1686673
theorem B2666699 : Blo 1184409 2666699 := bstep (se 1 (by rfl) ⟨2000024, by rfl⟩ : syracuseStep 2666699 = 4000049) B4000049
theorem B2666753 : Blo 1184409 2666753 := bstep (se 2 (by rfl) ⟨1000032, by rfl⟩ : syracuseStep 2666753 = 2000065) B2000065
theorem B5697809 : Blo 1184409 5697809 := bstep (se 2 (by rfl) ⟨2136678, by rfl⟩ : syracuseStep 5697809 = 4273357) B4273357
theorem B8999261 : Blo 1184409 8999261 := bstep (se 3 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 8999261 = 3374723) B3374723
theorem B4501939 : Blo 1184409 4501939 := bstep (se 1 (by rfl) ⟨3376454, by rfl⟩ : syracuseStep 4501939 = 6752909) B6752909
theorem B2281921 : Blo 1184409 2281921 := bstep (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) B1711441
theorem B5067211 : Blo 1184409 5067211 := bstep (se 1 (by rfl) ⟨3800408, by rfl⟩ : syracuseStep 5067211 = 7600817) B7600817
theorem B2134487 : Blo 1184409 2134487 := bstep (se 1 (by rfl) ⟨1600865, by rfl⟩ : syracuseStep 2134487 = 3201731) B3201731
theorem B2666969 : Blo 1184409 2666969 := bstep (se 2 (by rfl) ⟨1000113, by rfl⟩ : syracuseStep 2666969 = 2000227) B2000227
theorem B3043801 : Blo 1184409 3043801 := bstep (se 2 (by rfl) ⟨1141425, by rfl⟩ : syracuseStep 3043801 = 2282851) B2282851
theorem B3002903 : Blo 1184409 3002903 := bstep (se 1 (by rfl) ⟨2252177, by rfl⟩ : syracuseStep 3002903 = 4504355) B4504355
theorem B21926435 : Blo 1184409 21926435 := bstep (se 1 (by rfl) ⟨16444826, by rfl⟩ : syracuseStep 21926435 = 32889653) B32889653
theorem B2667059 : Blo 1184409 2667059 := bstep (se 1 (by rfl) ⟨2000294, by rfl⟩ : syracuseStep 2667059 = 4000589) B4000589
theorem B2028107 : Blo 1184409 2028107 := bstep (se 1 (by rfl) ⟨1521080, by rfl⟩ : syracuseStep 2028107 = 3042161) B3042161
theorem B2667095 : Blo 1184409 2667095 := bstep (se 1 (by rfl) ⟨2000321, by rfl⟩ : syracuseStep 2667095 = 4000643) B4000643
theorem B2249345 : Blo 1184409 2249345 := bstep (se 2 (by rfl) ⟨843504, by rfl⟩ : syracuseStep 2249345 = 1687009) B1687009
theorem B1184427 : Blo 1184409 1184427 := bstep (se 1 (by rfl) ⟨888320, by rfl⟩ : syracuseStep 1184427 = 1776641) B1776641
theorem B1184439 : Blo 1184409 1184439 := bstep (se 1 (by rfl) ⟨888329, by rfl⟩ : syracuseStep 1184439 = 1776659) B1776659
theorem B1184459 : Blo 1184409 1184459 := bstep (se 1 (by rfl) ⟨888344, by rfl⟩ : syracuseStep 1184459 = 1776689) B1776689
theorem B20247245 : Blo 1184409 20247245 := bstep (se 3 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 20247245 = 7592717) B7592717
theorem B1184471 : Blo 1184409 1184471 := bstep (se 1 (by rfl) ⟨888353, by rfl⟩ : syracuseStep 1184471 = 1776707) B1776707
theorem B7205593 : Blo 1184409 7205593 := bstep (se 2 (by rfl) ⟨2702097, by rfl⟩ : syracuseStep 7205593 = 5404195) B5404195
theorem B5067485 : Blo 1184409 5067485 := bstep (se 3 (by rfl) ⟨950153, by rfl⟩ : syracuseStep 5067485 = 1900307) B1900307
theorem B1184491 : Blo 1184409 1184491 := bstep (se 1 (by rfl) ⟨888368, by rfl⟩ : syracuseStep 1184491 = 1776737) B1776737
theorem B1184503 : Blo 1184409 1184503 := bstep (se 1 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 1184503 = 1776755) B1776755
theorem B1184523 : Blo 1184409 1184523 := bstep (se 1 (by rfl) ⟨888392, by rfl⟩ : syracuseStep 1184523 = 1776785) B1776785
theorem B2667275 : Blo 1184409 2667275 := bstep (se 1 (by rfl) ⟨2000456, by rfl⟩ : syracuseStep 2667275 = 4000913) B4000913
theorem B5059351 : Blo 1184409 5059351 := bstep (se 1 (by rfl) ⟨3794513, by rfl⟩ : syracuseStep 5059351 = 7589027) B7589027
theorem B1184535 : Blo 1184409 1184535 := bstep (se 1 (by rfl) ⟨888401, by rfl⟩ : syracuseStep 1184535 = 1776803) B1776803
theorem B1184555 : Blo 1184409 1184555 := bstep (se 1 (by rfl) ⟨888416, by rfl⟩ : syracuseStep 1184555 = 1776833) B1776833
theorem B8549165 : Blo 1184409 8549165 := bstep (se 3 (by rfl) ⟨1602968, by rfl⟩ : syracuseStep 8549165 = 3205937) B3205937
theorem B1184567 : Blo 1184409 1184567 := bstep (se 1 (by rfl) ⟨888425, by rfl⟩ : syracuseStep 1184567 = 1776851) B1776851
theorem B2667329 : Blo 1184409 2667329 := bstep (se 2 (by rfl) ⟨1000248, by rfl⟩ : syracuseStep 2667329 = 2000497) B2000497
theorem B24343361 : Blo 1184409 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B1184587 : Blo 1184409 1184587 := bstep (se 1 (by rfl) ⟨888440, by rfl⟩ : syracuseStep 1184587 = 1776881) B1776881
theorem B1184599 : Blo 1184409 1184599 := bstep (se 1 (by rfl) ⟨888449, by rfl⟩ : syracuseStep 1184599 = 1776899) B1776899
theorem B2847577 : Blo 1184409 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B5059421 : Blo 1184409 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B1184619 : Blo 1184409 1184619 := bstep (se 1 (by rfl) ⟨888464, by rfl⟩ : syracuseStep 1184619 = 1776929) B1776929
theorem B1184631 : Blo 1184409 1184631 := bstep (se 1 (by rfl) ⟨888473, by rfl⟩ : syracuseStep 1184631 = 1776947) B1776947
theorem B1184651 : Blo 1184409 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B1184663 : Blo 1184409 1184663 := bstep (se 1 (by rfl) ⟨888497, by rfl⟩ : syracuseStep 1184663 = 1776995) B1776995
theorem B1184683 : Blo 1184409 1184683 := bstep (se 1 (by rfl) ⟨888512, by rfl⟩ : syracuseStep 1184683 = 1777025) B1777025
theorem B1184695 : Blo 1184409 1184695 := bstep (se 1 (by rfl) ⟨888521, by rfl⟩ : syracuseStep 1184695 = 1777043) B1777043
theorem B1184715 : Blo 1184409 1184715 := bstep (se 1 (by rfl) ⟨888536, by rfl⟩ : syracuseStep 1184715 = 1777073) B1777073
theorem B1184727 : Blo 1184409 1184727 := bstep (se 1 (by rfl) ⟨888545, by rfl⟩ : syracuseStep 1184727 = 1777091) B1777091
theorem B2249687 : Blo 1184409 2249687 := bstep (se 1 (by rfl) ⟨1687265, by rfl⟩ : syracuseStep 2249687 = 3374531) B3374531
theorem B1184747 : Blo 1184409 1184747 := bstep (se 1 (by rfl) ⟨888560, by rfl⟩ : syracuseStep 1184747 = 1777121) B1777121
theorem B1184759 : Blo 1184409 1184759 := bstep (se 1 (by rfl) ⟨888569, by rfl⟩ : syracuseStep 1184759 = 1777139) B1777139
theorem B1184779 : Blo 1184409 1184779 := bstep (se 1 (by rfl) ⟨888584, by rfl⟩ : syracuseStep 1184779 = 1777169) B1777169
theorem B19215377 : Blo 1184409 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B1184791 : Blo 1184409 1184791 := bstep (se 1 (by rfl) ⟨888593, by rfl⟩ : syracuseStep 1184791 = 1777187) B1777187
theorem B2667545 : Blo 1184409 2667545 := bstep (se 2 (by rfl) ⟨1000329, by rfl⟩ : syracuseStep 2667545 = 2000659) B2000659
theorem B1184811 : Blo 1184409 1184811 := bstep (se 1 (by rfl) ⟨888608, by rfl⟩ : syracuseStep 1184811 = 1777217) B1777217
theorem B1184823 : Blo 1184409 1184823 := bstep (se 1 (by rfl) ⟨888617, by rfl⟩ : syracuseStep 1184823 = 1777235) B1777235
theorem B1184843 : Blo 1184409 1184843 := bstep (se 1 (by rfl) ⟨888632, by rfl⟩ : syracuseStep 1184843 = 1777265) B1777265
theorem B1184855 : Blo 1184409 1184855 := bstep (se 1 (by rfl) ⟨888641, by rfl⟩ : syracuseStep 1184855 = 1777283) B1777283
theorem B1184875 : Blo 1184409 1184875 := bstep (se 1 (by rfl) ⟨888656, by rfl⟩ : syracuseStep 1184875 = 1777313) B1777313
theorem B2667635 : Blo 1184409 2667635 := bstep (se 1 (by rfl) ⟨2000726, by rfl⟩ : syracuseStep 2667635 = 4001453) B4001453
theorem B1184887 : Blo 1184409 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B6583427 : Blo 1184409 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B1184907 : Blo 1184409 1184907 := bstep (se 1 (by rfl) ⟨888680, by rfl⟩ : syracuseStep 1184907 = 1777361) B1777361
theorem B1184919 : Blo 1184409 1184919 := bstep (se 1 (by rfl) ⟨888689, by rfl⟩ : syracuseStep 1184919 = 1777379) B1777379
theorem B2667671 : Blo 1184409 2667671 := bstep (se 1 (by rfl) ⟨2000753, by rfl⟩ : syracuseStep 2667671 = 4001507) B4001507
theorem B1184939 : Blo 1184409 1184939 := bstep (se 1 (by rfl) ⟨888704, by rfl⟩ : syracuseStep 1184939 = 1777409) B1777409
theorem B6755507 : Blo 1184409 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B1184951 : Blo 1184409 1184951 := bstep (se 1 (by rfl) ⟨888713, by rfl⟩ : syracuseStep 1184951 = 1777427) B1777427
theorem B1184971 : Blo 1184409 1184971 := bstep (se 1 (by rfl) ⟨888728, by rfl⟩ : syracuseStep 1184971 = 1777457) B1777457
theorem B4003019 : Blo 1184409 4003019 := bstep (se 1 (by rfl) ⟨3002264, by rfl⟩ : syracuseStep 4003019 = 6004529) B6004529
theorem B1184983 : Blo 1184409 1184983 := bstep (se 1 (by rfl) ⟨888737, by rfl⟩ : syracuseStep 1184983 = 1777475) B1777475
theorem B1185003 : Blo 1184409 1185003 := bstep (se 1 (by rfl) ⟨888752, by rfl⟩ : syracuseStep 1185003 = 1777505) B1777505
theorem B1185015 : Blo 1184409 1185015 := bstep (se 1 (by rfl) ⟨888761, by rfl⟩ : syracuseStep 1185015 = 1777523) B1777523
theorem B1185035 : Blo 1184409 1185035 := bstep (se 1 (by rfl) ⟨888776, by rfl⟩ : syracuseStep 1185035 = 1777553) B1777553
theorem B6001937 : Blo 1184409 6001937 := bstep (se 2 (by rfl) ⟨2250726, by rfl⟩ : syracuseStep 6001937 = 4501453) B4501453
theorem B1185047 : Blo 1184409 1185047 := bstep (se 1 (by rfl) ⟨888785, by rfl⟩ : syracuseStep 1185047 = 1777571) B1777571
theorem B1185067 : Blo 1184409 1185067 := bstep (se 1 (by rfl) ⟨888800, by rfl⟩ : syracuseStep 1185067 = 1777601) B1777601
theorem B1332535 : Blo 1184409 1332535 := bstep (se 1 (by rfl) ⟨999401, by rfl⟩ : syracuseStep 1332535 = 1998803) B1998803
theorem B1185079 : Blo 1184409 1185079 := bstep (se 1 (by rfl) ⟨888809, by rfl⟩ : syracuseStep 1185079 = 1777619) B1777619
theorem B1185099 : Blo 1184409 1185099 := bstep (se 1 (by rfl) ⟨888824, by rfl⟩ : syracuseStep 1185099 = 1777649) B1777649
theorem B2667851 : Blo 1184409 2667851 := bstep (se 1 (by rfl) ⟨2000888, by rfl⟩ : syracuseStep 2667851 = 4001777) B4001777
theorem B1185111 : Blo 1184409 1185111 := bstep (se 1 (by rfl) ⟨888833, by rfl⟩ : syracuseStep 1185111 = 1777667) B1777667
theorem B1185131 : Blo 1184409 1185131 := bstep (se 1 (by rfl) ⟨888848, by rfl⟩ : syracuseStep 1185131 = 1777697) B1777697
theorem B1185143 : Blo 1184409 1185143 := bstep (se 1 (by rfl) ⟨888857, by rfl⟩ : syracuseStep 1185143 = 1777715) B1777715
theorem B2667905 : Blo 1184409 2667905 := bstep (se 2 (by rfl) ⟨1000464, by rfl⟩ : syracuseStep 2667905 = 2000929) B2000929
theorem B1185163 : Blo 1184409 1185163 := bstep (se 1 (by rfl) ⟨888872, by rfl⟩ : syracuseStep 1185163 = 1777745) B1777745
theorem B1185175 : Blo 1184409 1185175 := bstep (se 1 (by rfl) ⟨888881, by rfl⟩ : syracuseStep 1185175 = 1777763) B1777763
theorem B4273559 : Blo 1184409 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B1185195 : Blo 1184409 1185195 := bstep (se 1 (by rfl) ⟨888896, by rfl⟩ : syracuseStep 1185195 = 1777793) B1777793
theorem B6002099 : Blo 1184409 6002099 := bstep (se 1 (by rfl) ⟨4501574, by rfl⟩ : syracuseStep 6002099 = 9003149) B9003149
theorem B1185207 : Blo 1184409 1185207 := bstep (se 1 (by rfl) ⟨888905, by rfl⟩ : syracuseStep 1185207 = 1777811) B1777811
theorem B1185227 : Blo 1184409 1185227 := bstep (se 1 (by rfl) ⟨888920, by rfl⟩ : syracuseStep 1185227 = 1777841) B1777841
theorem B1185239 : Blo 1184409 1185239 := bstep (se 1 (by rfl) ⟨888929, by rfl⟩ : syracuseStep 1185239 = 1777859) B1777859
theorem B4003289 : Blo 1184409 4003289 := bstep (se 2 (by rfl) ⟨1501233, by rfl⟩ : syracuseStep 4003289 = 3002467) B3002467
theorem B1332715 : Blo 1184409 1332715 := bstep (se 1 (by rfl) ⟨999536, by rfl⟩ : syracuseStep 1332715 = 1999073) B1999073
theorem B1185259 : Blo 1184409 1185259 := bstep (se 1 (by rfl) ⟨888944, by rfl⟩ : syracuseStep 1185259 = 1777889) B1777889
theorem B1185271 : Blo 1184409 1185271 := bstep (se 1 (by rfl) ⟨888953, by rfl⟩ : syracuseStep 1185271 = 1777907) B1777907
theorem B1185291 : Blo 1184409 1185291 := bstep (se 1 (by rfl) ⟨888968, by rfl⟩ : syracuseStep 1185291 = 1777937) B1777937
theorem B1185303 : Blo 1184409 1185303 := bstep (se 1 (by rfl) ⟨888977, by rfl⟩ : syracuseStep 1185303 = 1777955) B1777955
theorem B1185323 : Blo 1184409 1185323 := bstep (se 1 (by rfl) ⟨888992, by rfl⟩ : syracuseStep 1185323 = 1777985) B1777985
theorem B1185335 : Blo 1184409 1185335 := bstep (se 1 (by rfl) ⟨889001, by rfl⟩ : syracuseStep 1185335 = 1778003) B1778003
theorem B5060171 : Blo 1184409 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B1185355 : Blo 1184409 1185355 := bstep (se 1 (by rfl) ⟨889016, by rfl⟩ : syracuseStep 1185355 = 1778033) B1778033
theorem B1603147 : Blo 1184409 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B1332823 : Blo 1184409 1332823 := bstep (se 1 (by rfl) ⟨999617, by rfl⟩ : syracuseStep 1332823 = 1999235) B1999235
theorem B1185367 : Blo 1184409 1185367 := bstep (se 1 (by rfl) ⟨889025, by rfl⟩ : syracuseStep 1185367 = 1778051) B1778051
theorem B2668121 : Blo 1184409 2668121 := bstep (se 2 (by rfl) ⟨1000545, by rfl⟩ : syracuseStep 2668121 = 2001091) B2001091
theorem B1185387 : Blo 1184409 1185387 := bstep (se 1 (by rfl) ⟨889040, by rfl⟩ : syracuseStep 1185387 = 1778081) B1778081
theorem B2250355 : Blo 1184409 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B1185399 : Blo 1184409 1185399 := bstep (se 1 (by rfl) ⟨889049, by rfl⟩ : syracuseStep 1185399 = 1778099) B1778099
theorem B1185419 : Blo 1184409 1185419 := bstep (se 1 (by rfl) ⟨889064, by rfl⟩ : syracuseStep 1185419 = 1778129) B1778129
theorem B4503185 : Blo 1184409 4503185 := bstep (se 2 (by rfl) ⟨1688694, by rfl⟩ : syracuseStep 4503185 = 3377389) B3377389
theorem B1185431 : Blo 1184409 1185431 := bstep (se 1 (by rfl) ⟨889073, by rfl⟩ : syracuseStep 1185431 = 1778147) B1778147
theorem B1185451 : Blo 1184409 1185451 := bstep (se 1 (by rfl) ⟨889088, by rfl⟩ : syracuseStep 1185451 = 1778177) B1778177
theorem B2668211 : Blo 1184409 2668211 := bstep (se 1 (by rfl) ⟨2001158, by rfl⟩ : syracuseStep 2668211 = 4002317) B4002317
theorem B1185463 : Blo 1184409 1185463 := bstep (se 1 (by rfl) ⟨889097, by rfl⟩ : syracuseStep 1185463 = 1778195) B1778195
theorem B3847873 : Blo 1184409 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B1185483 : Blo 1184409 1185483 := bstep (se 1 (by rfl) ⟨889112, by rfl⟩ : syracuseStep 1185483 = 1778225) B1778225
theorem B1185495 : Blo 1184409 1185495 := bstep (se 1 (by rfl) ⟨889121, by rfl⟩ : syracuseStep 1185495 = 1778243) B1778243
theorem B2668247 : Blo 1184409 2668247 := bstep (se 1 (by rfl) ⟨2001185, by rfl⟩ : syracuseStep 2668247 = 4002371) B4002371
theorem B1185515 : Blo 1184409 1185515 := bstep (se 1 (by rfl) ⟨889136, by rfl⟩ : syracuseStep 1185515 = 1778273) B1778273
theorem B1185527 : Blo 1184409 1185527 := bstep (se 1 (by rfl) ⟨889145, by rfl⟩ : syracuseStep 1185527 = 1778291) B1778291
theorem B1333003 : Blo 1184409 1333003 := bstep (se 1 (by rfl) ⟨999752, by rfl⟩ : syracuseStep 1333003 = 1999505) B1999505
theorem B1185547 : Blo 1184409 1185547 := bstep (se 1 (by rfl) ⟨889160, by rfl⟩ : syracuseStep 1185547 = 1778321) B1778321
theorem B1185559 : Blo 1184409 1185559 := bstep (se 1 (by rfl) ⟨889169, by rfl⟩ : syracuseStep 1185559 = 1778339) B1778339
theorem B1185579 : Blo 1184409 1185579 := bstep (se 1 (by rfl) ⟨889184, by rfl⟩ : syracuseStep 1185579 = 1778369) B1778369
theorem B1185591 : Blo 1184409 1185591 := bstep (se 1 (by rfl) ⟨889193, by rfl⟩ : syracuseStep 1185591 = 1778387) B1778387
theorem B7591745 : Blo 1184409 7591745 := bstep (se 2 (by rfl) ⟨2846904, by rfl⟩ : syracuseStep 7591745 = 5693809) B5693809
theorem B1185611 : Blo 1184409 1185611 := bstep (se 1 (by rfl) ⟨889208, by rfl⟩ : syracuseStep 1185611 = 1778417) B1778417
theorem B1185623 : Blo 1184409 1185623 := bstep (se 1 (by rfl) ⟨889217, by rfl⟩ : syracuseStep 1185623 = 1778435) B1778435
theorem B1185643 : Blo 1184409 1185643 := bstep (se 1 (by rfl) ⟨889232, by rfl⟩ : syracuseStep 1185643 = 1778465) B1778465
theorem B1333111 : Blo 1184409 1333111 := bstep (se 1 (by rfl) ⟨999833, by rfl⟩ : syracuseStep 1333111 = 1999667) B1999667
theorem B1185655 : Blo 1184409 1185655 := bstep (se 1 (by rfl) ⟨889241, by rfl⟩ : syracuseStep 1185655 = 1778483) B1778483
theorem B5699459 : Blo 1184409 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B1185675 : Blo 1184409 1185675 := bstep (se 1 (by rfl) ⟨889256, by rfl⟩ : syracuseStep 1185675 = 1778513) B1778513
theorem B2668427 : Blo 1184409 2668427 := bstep (se 1 (by rfl) ⟨2001320, by rfl⟩ : syracuseStep 2668427 = 4002641) B4002641
theorem B1185687 : Blo 1184409 1185687 := bstep (se 1 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 1185687 = 1778531) B1778531
theorem B1185707 : Blo 1184409 1185707 := bstep (se 1 (by rfl) ⟨889280, by rfl⟩ : syracuseStep 1185707 = 1778561) B1778561
theorem B1185719 : Blo 1184409 1185719 := bstep (se 1 (by rfl) ⟨889289, by rfl⟩ : syracuseStep 1185719 = 1778579) B1778579
theorem B4052929 : Blo 1184409 4052929 := bstep (se 2 (by rfl) ⟨1519848, by rfl⟩ : syracuseStep 4052929 = 3039697) B3039697
theorem B2668481 : Blo 1184409 2668481 := bstep (se 2 (by rfl) ⟨1000680, by rfl⟩ : syracuseStep 2668481 = 2001361) B2001361
theorem B5404619 : Blo 1184409 5404619 := bstep (se 1 (by rfl) ⟨4053464, by rfl⟩ : syracuseStep 5404619 = 8106929) B8106929
theorem B1185739 : Blo 1184409 1185739 := bstep (se 1 (by rfl) ⟨889304, by rfl⟩ : syracuseStep 1185739 = 1778609) B1778609
theorem B1185751 : Blo 1184409 1185751 := bstep (se 1 (by rfl) ⟨889313, by rfl⟩ : syracuseStep 1185751 = 1778627) B1778627
theorem B7591897 : Blo 1184409 7591897 := bstep (se 2 (by rfl) ⟨2846961, by rfl⟩ : syracuseStep 7591897 = 5693923) B5693923
theorem B1185771 : Blo 1184409 1185771 := bstep (se 1 (by rfl) ⟨889328, by rfl⟩ : syracuseStep 1185771 = 1778657) B1778657
theorem B1185783 : Blo 1184409 1185783 := bstep (se 1 (by rfl) ⟨889337, by rfl⟩ : syracuseStep 1185783 = 1778675) B1778675
theorem B1185803 : Blo 1184409 1185803 := bstep (se 1 (by rfl) ⟨889352, by rfl⟩ : syracuseStep 1185803 = 1778705) B1778705
theorem B1185815 : Blo 1184409 1185815 := bstep (se 1 (by rfl) ⟨889361, by rfl⟩ : syracuseStep 1185815 = 1778723) B1778723
theorem B1333291 : Blo 1184409 1333291 := bstep (se 1 (by rfl) ⟨999968, by rfl⟩ : syracuseStep 1333291 = 1999937) B1999937
theorem B1185835 : Blo 1184409 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B2250803 : Blo 1184409 2250803 := bstep (se 1 (by rfl) ⟨1688102, by rfl⟩ : syracuseStep 2250803 = 3376205) B3376205
theorem B1185847 : Blo 1184409 1185847 := bstep (se 1 (by rfl) ⟨889385, by rfl⟩ : syracuseStep 1185847 = 1778771) B1778771
theorem B1185867 : Blo 1184409 1185867 := bstep (se 1 (by rfl) ⟨889400, by rfl⟩ : syracuseStep 1185867 = 1778801) B1778801
theorem B1185879 : Blo 1184409 1185879 := bstep (se 1 (by rfl) ⟨889409, by rfl⟩ : syracuseStep 1185879 = 1778819) B1778819
theorem B2250841 : Blo 1184409 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B1185899 : Blo 1184409 1185899 := bstep (se 1 (by rfl) ⟨889424, by rfl⟩ : syracuseStep 1185899 = 1778849) B1778849
theorem B1185911 : Blo 1184409 1185911 := bstep (se 1 (by rfl) ⟨889433, by rfl⟩ : syracuseStep 1185911 = 1778867) B1778867
theorem B1898635 : Blo 1184409 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B1185931 : Blo 1184409 1185931 := bstep (se 1 (by rfl) ⟨889448, by rfl⟩ : syracuseStep 1185931 = 1778897) B1778897
theorem B1333399 : Blo 1184409 1333399 := bstep (se 1 (by rfl) ⟨1000049, by rfl⟩ : syracuseStep 1333399 = 2000099) B2000099
theorem B1185943 : Blo 1184409 1185943 := bstep (se 1 (by rfl) ⟨889457, by rfl⟩ : syracuseStep 1185943 = 1778915) B1778915
theorem B2668697 : Blo 1184409 2668697 := bstep (se 2 (by rfl) ⟨1000761, by rfl⟩ : syracuseStep 2668697 = 2001523) B2001523
theorem B4003991 : Blo 1184409 4003991 := bstep (se 1 (by rfl) ⟨3002993, by rfl⟩ : syracuseStep 4003991 = 6005987) B6005987
theorem B1185963 : Blo 1184409 1185963 := bstep (se 1 (by rfl) ⟨889472, by rfl⟩ : syracuseStep 1185963 = 1778945) B1778945
theorem B1185975 : Blo 1184409 1185975 := bstep (se 1 (by rfl) ⟨889481, by rfl⟩ : syracuseStep 1185975 = 1778963) B1778963
theorem B2848961 : Blo 1184409 2848961 := bstep (se 2 (by rfl) ⟨1068360, by rfl⟩ : syracuseStep 2848961 = 2136721) B2136721
theorem B1185995 : Blo 1184409 1185995 := bstep (se 1 (by rfl) ⟨889496, by rfl⟩ : syracuseStep 1185995 = 1778993) B1778993
theorem B1186007 : Blo 1184409 1186007 := bstep (se 1 (by rfl) ⟨889505, by rfl⟩ : syracuseStep 1186007 = 1779011) B1779011
theorem B1186027 : Blo 1184409 1186027 := bstep (se 1 (by rfl) ⟨889520, by rfl⟩ : syracuseStep 1186027 = 1779041) B1779041
theorem B2668787 : Blo 1184409 2668787 := bstep (se 1 (by rfl) ⟨2001590, by rfl⟩ : syracuseStep 2668787 = 4003181) B4003181
theorem B1186039 : Blo 1184409 1186039 := bstep (se 1 (by rfl) ⟨889529, by rfl⟩ : syracuseStep 1186039 = 1779059) B1779059
theorem B1186059 : Blo 1184409 1186059 := bstep (se 1 (by rfl) ⟨889544, by rfl⟩ : syracuseStep 1186059 = 1779089) B1779089
theorem B1186071 : Blo 1184409 1186071 := bstep (se 1 (by rfl) ⟨889553, by rfl⟩ : syracuseStep 1186071 = 1779107) B1779107
theorem B2668823 : Blo 1184409 2668823 := bstep (se 1 (by rfl) ⟨2001617, by rfl⟩ : syracuseStep 2668823 = 4003235) B4003235
theorem B1186091 : Blo 1184409 1186091 := bstep (se 1 (by rfl) ⟨889568, by rfl⟩ : syracuseStep 1186091 = 1779137) B1779137
theorem B1186103 : Blo 1184409 1186103 := bstep (se 1 (by rfl) ⟨889577, by rfl⟩ : syracuseStep 1186103 = 1779155) B1779155
theorem B1333579 : Blo 1184409 1333579 := bstep (se 1 (by rfl) ⟨1000184, by rfl⟩ : syracuseStep 1333579 = 2000369) B2000369
theorem B1186123 : Blo 1184409 1186123 := bstep (se 1 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 1186123 = 1779185) B1779185
theorem B4503883 : Blo 1184409 4503883 := bstep (se 1 (by rfl) ⟨3377912, by rfl⟩ : syracuseStep 4503883 = 6755825) B6755825
theorem B1186135 : Blo 1184409 1186135 := bstep (se 1 (by rfl) ⟨889601, by rfl⟩ : syracuseStep 1186135 = 1779203) B1779203
theorem B2529625 : Blo 1184409 2529625 := bstep (se 2 (by rfl) ⟨948609, by rfl⟩ : syracuseStep 2529625 = 1897219) B1897219
theorem B1186155 : Blo 1184409 1186155 := bstep (se 1 (by rfl) ⟨889616, by rfl⟩ : syracuseStep 1186155 = 1779233) B1779233
theorem B1186167 : Blo 1184409 1186167 := bstep (se 1 (by rfl) ⟨889625, by rfl⟩ : syracuseStep 1186167 = 1779251) B1779251
theorem B1186187 : Blo 1184409 1186187 := bstep (se 1 (by rfl) ⟨889640, by rfl⟩ : syracuseStep 1186187 = 1779281) B1779281
theorem B1186199 : Blo 1184409 1186199 := bstep (se 1 (by rfl) ⟨889649, by rfl⟩ : syracuseStep 1186199 = 1779299) B1779299
theorem B1186219 : Blo 1184409 1186219 := bstep (se 1 (by rfl) ⟨889664, by rfl⟩ : syracuseStep 1186219 = 1779329) B1779329
theorem B1333687 : Blo 1184409 1333687 := bstep (se 1 (by rfl) ⟨1000265, by rfl⟩ : syracuseStep 1333687 = 2000531) B2000531
theorem B1186231 : Blo 1184409 1186231 := bstep (se 1 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 1186231 = 1779347) B1779347
theorem B2669003 : Blo 1184409 2669003 := bstep (se 1 (by rfl) ⟨2001752, by rfl⟩ : syracuseStep 2669003 = 4003505) B4003505
theorem B1186251 : Blo 1184409 1186251 := bstep (se 1 (by rfl) ⟨889688, by rfl⟩ : syracuseStep 1186251 = 1779377) B1779377
theorem B1186263 : Blo 1184409 1186263 := bstep (se 1 (by rfl) ⟨889697, by rfl⟩ : syracuseStep 1186263 = 1779395) B1779395
theorem B1186283 : Blo 1184409 1186283 := bstep (se 1 (by rfl) ⟨889712, by rfl⟩ : syracuseStep 1186283 = 1779425) B1779425
theorem B1186295 : Blo 1184409 1186295 := bstep (se 1 (by rfl) ⟨889721, by rfl⟩ : syracuseStep 1186295 = 1779443) B1779443
theorem B2669057 : Blo 1184409 2669057 := bstep (se 2 (by rfl) ⟨1000896, by rfl⟩ : syracuseStep 2669057 = 2001793) B2001793
theorem B1186315 : Blo 1184409 1186315 := bstep (se 1 (by rfl) ⟨889736, by rfl⟩ : syracuseStep 1186315 = 1779473) B1779473
theorem B17783309 : Blo 1184409 17783309 := bstep (se 3 (by rfl) ⟨3334370, by rfl⟩ : syracuseStep 17783309 = 6668741) B6668741
theorem B1186327 : Blo 1184409 1186327 := bstep (se 1 (by rfl) ⟨889745, by rfl⟩ : syracuseStep 1186327 = 1779491) B1779491
theorem B2251289 : Blo 1184409 2251289 := bstep (se 2 (by rfl) ⟨844233, by rfl⟩ : syracuseStep 2251289 = 1688467) B1688467
theorem B1186347 : Blo 1184409 1186347 := bstep (se 1 (by rfl) ⟨889760, by rfl⟩ : syracuseStep 1186347 = 1779521) B1779521
theorem B6748717 : Blo 1184409 6748717 := bstep (se 3 (by rfl) ⟨1265384, by rfl⟩ : syracuseStep 6748717 = 2530769) B2530769
theorem B1186359 : Blo 1184409 1186359 := bstep (se 1 (by rfl) ⟨889769, by rfl⟩ : syracuseStep 1186359 = 1779539) B1779539
theorem B7600715 : Blo 1184409 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B1186379 : Blo 1184409 1186379 := bstep (se 1 (by rfl) ⟨889784, by rfl⟩ : syracuseStep 1186379 = 1779569) B1779569
theorem B1186391 : Blo 1184409 1186391 := bstep (se 1 (by rfl) ⟨889793, by rfl⟩ : syracuseStep 1186391 = 1779587) B1779587
theorem B2529881 : Blo 1184409 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B4504157 : Blo 1184409 4504157 := bstep (se 3 (by rfl) ⟨844529, by rfl⟩ : syracuseStep 4504157 = 1689059) B1689059
theorem B6756965 : Blo 1184409 6756965 := bstep (se 4 (by rfl) ⟨633465, by rfl⟩ : syracuseStep 6756965 = 1266931) B1266931
theorem B1333867 : Blo 1184409 1333867 := bstep (se 1 (by rfl) ⟨1000400, by rfl⟩ : syracuseStep 1333867 = 2000801) B2000801
theorem B1333975 : Blo 1184409 1333975 := bstep (se 1 (by rfl) ⟨1000481, by rfl⟩ : syracuseStep 1333975 = 2000963) B2000963
theorem B2669273 : Blo 1184409 2669273 := bstep (se 2 (by rfl) ⟨1000977, by rfl⟩ : syracuseStep 2669273 = 2001955) B2001955
theorem B2669363 : Blo 1184409 2669363 := bstep (se 1 (by rfl) ⟨2002022, by rfl⟩ : syracuseStep 2669363 = 4004045) B4004045
theorem B2669399 : Blo 1184409 2669399 := bstep (se 1 (by rfl) ⟨2002049, by rfl⟩ : syracuseStep 2669399 = 4004099) B4004099
theorem B1334155 : Blo 1184409 1334155 := bstep (se 1 (by rfl) ⟨1000616, by rfl⟩ : syracuseStep 1334155 = 2001233) B2001233
theorem B2530291 : Blo 1184409 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B1334263 : Blo 1184409 1334263 := bstep (se 1 (by rfl) ⟨1000697, by rfl⟩ : syracuseStep 1334263 = 2001395) B2001395
theorem B1776665 : Blo 1184409 1776665 := bstep (se 2 (by rfl) ⟨666249, by rfl⟩ : syracuseStep 1776665 = 1332499) B1332499
theorem B3374131 : Blo 1184409 3374131 := bstep (se 1 (by rfl) ⟨2530598, by rfl⟩ : syracuseStep 3374131 = 5061197) B5061197
theorem B1776779 : Blo 1184409 1776779 := bstep (se 1 (by rfl) ⟨1332584, by rfl⟩ : syracuseStep 1776779 = 2665169) B2665169
theorem B1776791 : Blo 1184409 1776791 := bstep (se 1 (by rfl) ⟨1332593, by rfl⟩ : syracuseStep 1776791 = 2665187) B2665187
theorem B1924247 : Blo 1184409 1924247 := bstep (se 1 (by rfl) ⟨1443185, by rfl⟩ : syracuseStep 1924247 = 2886371) B2886371
theorem B2137241 : Blo 1184409 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B1334443 : Blo 1184409 1334443 := bstep (se 1 (by rfl) ⟨1000832, by rfl⟩ : syracuseStep 1334443 = 2001665) B2001665
theorem B1776857 : Blo 1184409 1776857 := bstep (se 2 (by rfl) ⟨666321, by rfl⟩ : syracuseStep 1776857 = 1332643) B1332643
theorem B2252033 : Blo 1184409 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B1334551 : Blo 1184409 1334551 := bstep (se 1 (by rfl) ⟨1000913, by rfl⟩ : syracuseStep 1334551 = 2001827) B2001827
theorem B1776971 : Blo 1184409 1776971 := bstep (se 1 (by rfl) ⟨1332728, by rfl⟩ : syracuseStep 1776971 = 2665457) B2665457
theorem B6004043 : Blo 1184409 6004043 := bstep (se 1 (by rfl) ⟨4503032, by rfl⟩ : syracuseStep 6004043 = 9006065) B9006065
theorem B1776983 : Blo 1184409 1776983 := bstep (se 1 (by rfl) ⟨1332737, by rfl⟩ : syracuseStep 1776983 = 2665475) B2665475
theorem B1899865 : Blo 1184409 1899865 := bstep (se 2 (by rfl) ⟨712449, by rfl⟩ : syracuseStep 1899865 = 1424899) B1424899
theorem B1777049 : Blo 1184409 1777049 := bstep (se 2 (by rfl) ⟨666393, by rfl⟩ : syracuseStep 1777049 = 1332787) B1332787
theorem B1777163 : Blo 1184409 1777163 := bstep (se 1 (by rfl) ⟨1332872, by rfl⟩ : syracuseStep 1777163 = 2665745) B2665745
theorem B2252299 : Blo 1184409 2252299 := bstep (se 1 (by rfl) ⟨1689224, by rfl⟩ : syracuseStep 2252299 = 3378449) B3378449
theorem B1777175 : Blo 1184409 1777175 := bstep (se 1 (by rfl) ⟨1332881, by rfl⟩ : syracuseStep 1777175 = 2665763) B2665763
theorem B1777241 : Blo 1184409 1777241 := bstep (se 2 (by rfl) ⟨666465, by rfl⟩ : syracuseStep 1777241 = 1332931) B1332931
theorem B2531009 : Blo 1184409 2531009 := bstep (se 2 (by rfl) ⟨949128, by rfl⟩ : syracuseStep 2531009 = 1898257) B1898257
theorem B1777355 : Blo 1184409 1777355 := bstep (se 1 (by rfl) ⟨1333016, by rfl⟩ : syracuseStep 1777355 = 2666033) B2666033
theorem B1777367 : Blo 1184409 1777367 := bstep (se 1 (by rfl) ⟨1333025, by rfl⟩ : syracuseStep 1777367 = 2666051) B2666051
theorem B1777433 : Blo 1184409 1777433 := bstep (se 2 (by rfl) ⟨666537, by rfl⟩ : syracuseStep 1777433 = 1333075) B1333075
theorem B92348261 : Blo 1184409 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B1777547 : Blo 1184409 1777547 := bstep (se 1 (by rfl) ⟨1333160, by rfl⟩ : syracuseStep 1777547 = 2666321) B2666321
theorem B1777559 : Blo 1184409 1777559 := bstep (se 1 (by rfl) ⟨1333169, by rfl⟩ : syracuseStep 1777559 = 2666339) B2666339
theorem B3997619 : Blo 1184409 3997619 := bstep (se 1 (by rfl) ⟨2998214, by rfl⟩ : syracuseStep 3997619 = 5996429) B5996429
theorem B1777625 : Blo 1184409 1777625 := bstep (se 2 (by rfl) ⟨666609, by rfl⟩ : syracuseStep 1777625 = 1333219) B1333219
theorem B1499143 : Blo 1184409 1499143 := bstep (se 1 (by rfl) ⟨1124357, by rfl⟩ : syracuseStep 1499143 = 2248715) B2248715
theorem B1777679 : Blo 1184409 1777679 := bstep (se 1 (by rfl) ⟨1333259, by rfl⟩ : syracuseStep 1777679 = 2666519) B2666519
theorem B1687567 : Blo 1184409 1687567 := bstep (se 1 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 1687567 = 2531351) B2531351
theorem B11386925 : Blo 1184409 11386925 := bstep (se 3 (by rfl) ⟨2135048, by rfl⟩ : syracuseStep 11386925 = 4270097) B4270097
theorem B1777721 : Blo 1184409 1777721 := bstep (se 2 (by rfl) ⟨666645, by rfl⟩ : syracuseStep 1777721 = 1333291) B1333291
theorem B1777799 : Blo 1184409 1777799 := bstep (se 1 (by rfl) ⟨1333349, by rfl⟩ : syracuseStep 1777799 = 2666699) B2666699
theorem B1777835 : Blo 1184409 1777835 := bstep (se 1 (by rfl) ⟨1333376, by rfl⟩ : syracuseStep 1777835 = 2666753) B2666753
theorem B2531513 : Blo 1184409 2531513 := bstep (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) B1898635
theorem B1777865 : Blo 1184409 1777865 := bstep (se 2 (by rfl) ⟨666699, by rfl⟩ : syracuseStep 1777865 = 1333399) B1333399
theorem B2998529 : Blo 1184409 2998529 := bstep (se 2 (by rfl) ⟨1124448, by rfl⟩ : syracuseStep 2998529 = 2248897) B2248897
theorem B3375361 : Blo 1184409 3375361 := bstep (se 2 (by rfl) ⟨1265760, by rfl⟩ : syracuseStep 3375361 = 2531521) B2531521
theorem B2703631 : Blo 1184409 2703631 := bstep (se 1 (by rfl) ⟨2027723, by rfl⟩ : syracuseStep 2703631 = 4055447) B4055447
theorem B1999147 : Blo 1184409 1999147 := bstep (se 1 (by rfl) ⟨1499360, by rfl⟩ : syracuseStep 1999147 = 2998721) B2998721
theorem B1777979 : Blo 1184409 1777979 := bstep (se 1 (by rfl) ⟨1333484, by rfl⟩ : syracuseStep 1777979 = 2666969) B2666969
theorem B5996915 : Blo 1184409 5996915 := bstep (se 1 (by rfl) ⟨4497686, by rfl⟩ : syracuseStep 5996915 = 8995373) B8995373
theorem B1778039 : Blo 1184409 1778039 := bstep (se 1 (by rfl) ⟨1333529, by rfl⟩ : syracuseStep 1778039 = 2667059) B2667059
theorem B1352071 : Blo 1184409 1352071 := bstep (se 1 (by rfl) ⟨1014053, by rfl⟩ : syracuseStep 1352071 = 2028107) B2028107
theorem B1778063 : Blo 1184409 1778063 := bstep (se 1 (by rfl) ⟨1333547, by rfl⟩ : syracuseStep 1778063 = 2667095) B2667095
theorem B3998105 : Blo 1184409 3998105 := bstep (se 2 (by rfl) ⟨1499289, by rfl⟩ : syracuseStep 3998105 = 2998579) B2998579
theorem B1499563 : Blo 1184409 1499563 := bstep (se 1 (by rfl) ⟨1124672, by rfl⟩ : syracuseStep 1499563 = 2249345) B2249345
theorem B1999289 : Blo 1184409 1999289 := bstep (se 2 (by rfl) ⟨749733, by rfl⟩ : syracuseStep 1999289 = 1499467) B1499467
theorem B1778105 : Blo 1184409 1778105 := bstep (se 2 (by rfl) ⟨666789, by rfl⟩ : syracuseStep 1778105 = 1333579) B1333579
theorem B6005177 : Blo 1184409 6005177 := bstep (se 2 (by rfl) ⟨2251941, by rfl⟩ : syracuseStep 6005177 = 4503883) B4503883
theorem B1778183 : Blo 1184409 1778183 := bstep (se 1 (by rfl) ⟨1333637, by rfl⟩ : syracuseStep 1778183 = 2667275) B2667275
theorem B1778219 : Blo 1184409 1778219 := bstep (se 1 (by rfl) ⟨1333664, by rfl⟩ : syracuseStep 1778219 = 2667329) B2667329
theorem B16228907 : Blo 1184409 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B1778249 : Blo 1184409 1778249 := bstep (se 2 (by rfl) ⟨666843, by rfl⟩ : syracuseStep 1778249 = 1333687) B1333687
theorem B2998903 : Blo 1184409 2998903 := bstep (se 1 (by rfl) ⟨2249177, by rfl⟩ : syracuseStep 2998903 = 4498355) B4498355
theorem B1499791 : Blo 1184409 1499791 := bstep (se 1 (by rfl) ⟨1124843, by rfl⟩ : syracuseStep 1499791 = 2249687) B2249687
theorem B1778363 : Blo 1184409 1778363 := bstep (se 1 (by rfl) ⟨1333772, by rfl⟩ : syracuseStep 1778363 = 2667545) B2667545
theorem B1778423 : Blo 1184409 1778423 := bstep (se 1 (by rfl) ⟨1333817, by rfl⟩ : syracuseStep 1778423 = 2667635) B2667635
theorem B1778447 : Blo 1184409 1778447 := bstep (se 1 (by rfl) ⟨1333835, by rfl⟩ : syracuseStep 1778447 = 2667671) B2667671
theorem B1778489 : Blo 1184409 1778489 := bstep (se 2 (by rfl) ⟨666933, by rfl⟩ : syracuseStep 1778489 = 1333867) B1333867
theorem B3375931 : Blo 1184409 3375931 := bstep (se 1 (by rfl) ⟨2531948, by rfl⟩ : syracuseStep 3375931 = 5063897) B5063897
theorem B5997401 : Blo 1184409 5997401 := bstep (se 2 (by rfl) ⟨2249025, by rfl⟩ : syracuseStep 5997401 = 4498051) B4498051
theorem B1778567 : Blo 1184409 1778567 := bstep (se 1 (by rfl) ⟨1333925, by rfl⟩ : syracuseStep 1778567 = 2667851) B2667851
theorem B1688455 : Blo 1184409 1688455 := bstep (se 1 (by rfl) ⟨1266341, by rfl⟩ : syracuseStep 1688455 = 2532683) B2532683
theorem B1803151 : Blo 1184409 1803151 := bstep (se 1 (by rfl) ⟨1352363, by rfl⟩ : syracuseStep 1803151 = 2704727) B2704727
theorem B1778603 : Blo 1184409 1778603 := bstep (se 1 (by rfl) ⟨1333952, by rfl⟩ : syracuseStep 1778603 = 2667905) B2667905
theorem B1778633 : Blo 1184409 1778633 := bstep (se 2 (by rfl) ⟨666987, by rfl⟩ : syracuseStep 1778633 = 1333975) B1333975
theorem B2999339 : Blo 1184409 2999339 := bstep (se 1 (by rfl) ⟨2249504, by rfl⟩ : syracuseStep 2999339 = 4499009) B4499009
theorem B1778747 : Blo 1184409 1778747 := bstep (se 1 (by rfl) ⟨1334060, by rfl⟩ : syracuseStep 1778747 = 2668121) B2668121
theorem B3998807 : Blo 1184409 3998807 := bstep (se 1 (by rfl) ⟨2999105, by rfl⟩ : syracuseStep 3998807 = 5998211) B5998211
theorem B1999991 : Blo 1184409 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B1778807 : Blo 1184409 1778807 := bstep (se 1 (by rfl) ⟨1334105, by rfl⟩ : syracuseStep 1778807 = 2668211) B2668211
theorem B1778831 : Blo 1184409 1778831 := bstep (se 1 (by rfl) ⟨1334123, by rfl⟩ : syracuseStep 1778831 = 2668247) B2668247
theorem B1778873 : Blo 1184409 1778873 := bstep (se 2 (by rfl) ⟨667077, by rfl⟩ : syracuseStep 1778873 = 1334155) B1334155
theorem B1778951 : Blo 1184409 1778951 := bstep (se 1 (by rfl) ⟨1334213, by rfl⟩ : syracuseStep 1778951 = 2668427) B2668427
theorem B16442657 : Blo 1184409 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B1778987 : Blo 1184409 1778987 := bstep (se 1 (by rfl) ⟨1334240, by rfl⟩ : syracuseStep 1778987 = 2668481) B2668481
theorem B1779017 : Blo 1184409 1779017 := bstep (se 2 (by rfl) ⟨667131, by rfl⟩ : syracuseStep 1779017 = 1334263) B1334263
theorem B1500535 : Blo 1184409 1500535 := bstep (se 1 (by rfl) ⟨1125401, by rfl⟩ : syracuseStep 1500535 = 2250803) B2250803
theorem B1688951 : Blo 1184409 1688951 := bstep (se 1 (by rfl) ⟨1266713, by rfl⟩ : syracuseStep 1688951 = 2533427) B2533427
theorem B6751633 : Blo 1184409 6751633 := bstep (se 2 (by rfl) ⟨2531862, by rfl⟩ : syracuseStep 6751633 = 5063725) B5063725
theorem B4498841 : Blo 1184409 4498841 := bstep (se 2 (by rfl) ⟨1687065, by rfl⟩ : syracuseStep 4498841 = 3374131) B3374131
theorem B1779131 : Blo 1184409 1779131 := bstep (se 1 (by rfl) ⟨1334348, by rfl⟩ : syracuseStep 1779131 = 2668697) B2668697
theorem B1779191 : Blo 1184409 1779191 := bstep (se 1 (by rfl) ⟨1334393, by rfl⟩ : syracuseStep 1779191 = 2668787) B2668787
theorem B1779215 : Blo 1184409 1779215 := bstep (se 1 (by rfl) ⟨1334411, by rfl⟩ : syracuseStep 1779215 = 2668823) B2668823
theorem B13493789 : Blo 1184409 13493789 := bstep (se 3 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 13493789 = 5060171) B5060171
theorem B3606059 : Blo 1184409 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B1779257 : Blo 1184409 1779257 := bstep (se 2 (by rfl) ⟨667221, by rfl⟩ : syracuseStep 1779257 = 1334443) B1334443
theorem B2000443 : Blo 1184409 2000443 := bstep (se 1 (by rfl) ⟨1500332, by rfl⟩ : syracuseStep 2000443 = 3000665) B3000665
theorem B3999293 : Blo 1184409 3999293 := bstep (se 3 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 3999293 = 1499735) B1499735
theorem B21612109 : Blo 1184409 21612109 := bstep (se 3 (by rfl) ⟨4052270, by rfl⟩ : syracuseStep 21612109 = 8104541) B8104541
theorem B1779335 : Blo 1184409 1779335 := bstep (se 1 (by rfl) ⟨1334501, by rfl⟩ : syracuseStep 1779335 = 2669003) B2669003
theorem B1779371 : Blo 1184409 1779371 := bstep (se 1 (by rfl) ⟨1334528, by rfl⟩ : syracuseStep 1779371 = 2669057) B2669057
theorem B1500859 : Blo 1184409 1500859 := bstep (se 1 (by rfl) ⟨1125644, by rfl⟩ : syracuseStep 1500859 = 2251289) B2251289
theorem B2000585 : Blo 1184409 2000585 := bstep (se 2 (by rfl) ⟨750219, by rfl⟩ : syracuseStep 2000585 = 1500439) B1500439
theorem B1779401 : Blo 1184409 1779401 := bstep (se 2 (by rfl) ⟨667275, by rfl⟩ : syracuseStep 1779401 = 1334551) B1334551
theorem B1779515 : Blo 1184409 1779515 := bstep (se 1 (by rfl) ⟨1334636, by rfl⟩ : syracuseStep 1779515 = 2669273) B2669273
theorem B3000179 : Blo 1184409 3000179 := bstep (se 1 (by rfl) ⟨2250134, by rfl⟩ : syracuseStep 3000179 = 4500269) B4500269
theorem B1779575 : Blo 1184409 1779575 := bstep (se 1 (by rfl) ⟨1334681, by rfl⟩ : syracuseStep 1779575 = 2669363) B2669363
theorem B3000199 : Blo 1184409 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B1779599 : Blo 1184409 1779599 := bstep (se 1 (by rfl) ⟨1334699, by rfl⟩ : syracuseStep 1779599 = 2669399) B2669399
theorem B4802627 : Blo 1184409 4802627 := bstep (se 1 (by rfl) ⟨3601970, by rfl⟩ : syracuseStep 4802627 = 7203941) B7203941
theorem B5408855 : Blo 1184409 5408855 := bstep (se 1 (by rfl) ⟨4056641, by rfl⟩ : syracuseStep 5408855 = 8113283) B8113283
theorem B3000473 : Blo 1184409 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B1501355 : Blo 1184409 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B5130497 : Blo 1184409 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B3000635 : Blo 1184409 3000635 := bstep (se 1 (by rfl) ⟨2250476, by rfl⟩ : syracuseStep 3000635 = 4500953) B4500953
theorem B2001287 : Blo 1184409 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B3000847 : Blo 1184409 3000847 := bstep (se 1 (by rfl) ⟨2250635, by rfl⟩ : syracuseStep 3000847 = 4501271) B4501271
theorem B2886187 : Blo 1184409 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B61565507 : Blo 1184409 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B2665079 : Blo 1184409 2665079 := bstep (se 1 (by rfl) ⟨1998809, by rfl⟩ : syracuseStep 2665079 = 3997619) B3997619
theorem B5778157 : Blo 1184409 5778157 := bstep (se 3 (by rfl) ⟨1083404, by rfl⟩ : syracuseStep 5778157 = 2166809) B2166809
theorem B5065487 : Blo 1184409 5065487 := bstep (se 1 (by rfl) ⟨3799115, by rfl⟩ : syracuseStep 5065487 = 7598231) B7598231
theorem B3205903 : Blo 1184409 3205903 := bstep (se 1 (by rfl) ⟨2404427, by rfl⟩ : syracuseStep 3205903 = 4808855) B4808855
theorem B3001121 : Blo 1184409 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B2665259 : Blo 1184409 2665259 := bstep (se 1 (by rfl) ⟨1998944, by rfl⟩ : syracuseStep 2665259 = 3997889) B3997889
theorem B5999507 : Blo 1184409 5999507 := bstep (se 1 (by rfl) ⟨4499630, by rfl⟩ : syracuseStep 5999507 = 8999261) B8999261
theorem B4000697 : Blo 1184409 4000697 := bstep (se 2 (by rfl) ⟨1500261, by rfl⟩ : syracuseStep 4000697 = 3000523) B3000523
theorem B10120139 : Blo 1184409 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B2001935 : Blo 1184409 2001935 := bstep (se 1 (by rfl) ⟨1501451, by rfl⟩ : syracuseStep 2001935 = 3002903) B3002903
theorem B5131325 : Blo 1184409 5131325 := bstep (se 3 (by rfl) ⟨962123, by rfl⟩ : syracuseStep 5131325 = 1924247) B1924247
theorem B2665619 : Blo 1184409 2665619 := bstep (se 1 (by rfl) ⟨1999214, by rfl⟩ : syracuseStep 2665619 = 3998429) B3998429
theorem B3378323 : Blo 1184409 3378323 := bstep (se 1 (by rfl) ⟨2533742, by rfl⟩ : syracuseStep 3378323 = 5067485) B5067485
theorem B2665673 : Blo 1184409 2665673 := bstep (se 2 (by rfl) ⟨999627, by rfl⟩ : syracuseStep 2665673 = 1999255) B1999255
theorem B3796283 : Blo 1184409 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B7204211 : Blo 1184409 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B8998289 : Blo 1184409 8998289 := bstep (se 2 (by rfl) ⟨3374358, by rfl⟩ : syracuseStep 8998289 = 6748717) B6748717
theorem B6499769 : Blo 1184409 6499769 := bstep (se 2 (by rfl) ⟨2437413, by rfl⟩ : syracuseStep 6499769 = 4874827) B4874827
theorem B4001291 : Blo 1184409 4001291 := bstep (se 1 (by rfl) ⟨3000968, by rfl⟩ : syracuseStep 4001291 = 6001937) B6001937
theorem B4001399 : Blo 1184409 4001399 := bstep (se 1 (by rfl) ⟨3001049, by rfl⟩ : syracuseStep 4001399 = 6002099) B6002099
theorem B6745801 : Blo 1184409 6745801 := bstep (se 2 (by rfl) ⟨2529675, by rfl⟩ : syracuseStep 6745801 = 5059351) B5059351
theorem B6754049 : Blo 1184409 6754049 := bstep (se 2 (by rfl) ⟨2532768, by rfl⟩ : syracuseStep 6754049 = 5065537) B5065537
theorem B3002123 : Blo 1184409 3002123 := bstep (se 1 (by rfl) ⟨2251592, by rfl⟩ : syracuseStep 3002123 = 4503185) B4503185
theorem B3796769 : Blo 1184409 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B14421797 : Blo 1184409 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B16428851 : Blo 1184409 16428851 := bstep (se 1 (by rfl) ⟨12321638, by rfl⟩ : syracuseStep 16428851 = 24643277) B24643277
theorem B2666375 : Blo 1184409 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B82161611 : Blo 1184409 82161611 := bstep (se 1 (by rfl) ⟨61621208, by rfl⟩ : syracuseStep 82161611 = 123242417) B123242417
theorem B5697539 : Blo 1184409 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B2666555 : Blo 1184409 2666555 := bstep (se 1 (by rfl) ⟨1999916, by rfl⟩ : syracuseStep 2666555 = 3999833) B3999833
theorem B58470493 : Blo 1184409 58470493 := bstep (se 3 (by rfl) ⟨10963217, by rfl⟩ : syracuseStep 58470493 = 21926435) B21926435
theorem B2666681 : Blo 1184409 2666681 := bstep (se 2 (by rfl) ⟨1000005, by rfl⟩ : syracuseStep 2666681 = 2000011) B2000011
theorem B4001993 : Blo 1184409 4001993 := bstep (se 2 (by rfl) ⟨1500747, by rfl⟩ : syracuseStep 4001993 = 3001495) B3001495
theorem B5067143 : Blo 1184409 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B3002771 : Blo 1184409 3002771 := bstep (se 1 (by rfl) ⟨2252078, by rfl⟩ : syracuseStep 3002771 = 4504157) B4504157
theorem B2667023 : Blo 1184409 2667023 := bstep (se 1 (by rfl) ⟨2000267, by rfl⟩ : syracuseStep 2667023 = 4000535) B4000535
theorem B2667041 : Blo 1184409 2667041 := bstep (se 2 (by rfl) ⟨1000140, by rfl⟩ : syracuseStep 2667041 = 2000281) B2000281
theorem B3003065 : Blo 1184409 3003065 := bstep (se 2 (by rfl) ⟨1126149, by rfl⟩ : syracuseStep 3003065 = 2252299) B2252299
theorem B1184443 : Blo 1184409 1184443 := bstep (se 1 (by rfl) ⟨888332, by rfl⟩ : syracuseStep 1184443 = 1776665) B1776665
theorem B7213769 : Blo 1184409 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B24048389 : Blo 1184409 24048389 := bstep (se 4 (by rfl) ⟨2254536, by rfl⟩ : syracuseStep 24048389 = 4509073) B4509073
theorem B1184519 : Blo 1184409 1184519 := bstep (se 1 (by rfl) ⟨888389, by rfl⟩ : syracuseStep 1184519 = 1776779) B1776779
theorem B1184527 : Blo 1184409 1184527 := bstep (se 1 (by rfl) ⟨888395, by rfl⟩ : syracuseStep 1184527 = 1776791) B1776791
theorem B1184571 : Blo 1184409 1184571 := bstep (se 1 (by rfl) ⟨888428, by rfl⟩ : syracuseStep 1184571 = 1776857) B1776857
theorem B2667383 : Blo 1184409 2667383 := bstep (se 1 (by rfl) ⟨2000537, by rfl⟩ : syracuseStep 2667383 = 4001075) B4001075
theorem B1184647 : Blo 1184409 1184647 := bstep (se 1 (by rfl) ⟨888485, by rfl⟩ : syracuseStep 1184647 = 1776971) B1776971
theorem B4002695 : Blo 1184409 4002695 := bstep (se 1 (by rfl) ⟨3002021, by rfl⟩ : syracuseStep 4002695 = 6004043) B6004043
theorem B1184655 : Blo 1184409 1184655 := bstep (se 1 (by rfl) ⟨888491, by rfl⟩ : syracuseStep 1184655 = 1776983) B1776983
theorem B4502425 : Blo 1184409 4502425 := bstep (se 2 (by rfl) ⟨1688409, by rfl⟩ : syracuseStep 4502425 = 3376819) B3376819
theorem B1184699 : Blo 1184409 1184699 := bstep (se 1 (by rfl) ⟨888524, by rfl⟩ : syracuseStep 1184699 = 1777049) B1777049
theorem B12170245 : Blo 1184409 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B1184775 : Blo 1184409 1184775 := bstep (se 1 (by rfl) ⟨888581, by rfl⟩ : syracuseStep 1184775 = 1777163) B1777163
theorem B1184783 : Blo 1184409 1184783 := bstep (se 1 (by rfl) ⟨888587, by rfl⟩ : syracuseStep 1184783 = 1777175) B1777175
theorem B2667563 : Blo 1184409 2667563 := bstep (se 1 (by rfl) ⟨2000672, by rfl⟩ : syracuseStep 2667563 = 4001345) B4001345
theorem B1184827 : Blo 1184409 1184827 := bstep (se 1 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 1184827 = 1777241) B1777241
theorem B16233605 : Blo 1184409 16233605 := bstep (se 4 (by rfl) ⟨1521900, by rfl⟩ : syracuseStep 16233605 = 3043801) B3043801
theorem B1184903 : Blo 1184409 1184903 := bstep (se 1 (by rfl) ⟨888677, by rfl⟩ : syracuseStep 1184903 = 1777355) B1777355
theorem B1184911 : Blo 1184409 1184911 := bstep (se 1 (by rfl) ⟨888683, by rfl⟩ : syracuseStep 1184911 = 1777367) B1777367
theorem B1184955 : Blo 1184409 1184955 := bstep (se 1 (by rfl) ⟨888716, by rfl⟩ : syracuseStep 1184955 = 1777433) B1777433
theorem B4502729 : Blo 1184409 4502729 := bstep (se 2 (by rfl) ⟨1688523, by rfl⟩ : syracuseStep 4502729 = 3377047) B3377047
theorem B5403905 : Blo 1184409 5403905 := bstep (se 2 (by rfl) ⟨2026464, by rfl⟩ : syracuseStep 5403905 = 4052929) B4052929
theorem B4003073 : Blo 1184409 4003073 := bstep (se 2 (by rfl) ⟨1501152, by rfl⟩ : syracuseStep 4003073 = 3002305) B3002305
theorem B1185031 : Blo 1184409 1185031 := bstep (se 1 (by rfl) ⟨888773, by rfl⟩ : syracuseStep 1185031 = 1777547) B1777547
theorem B1185039 : Blo 1184409 1185039 := bstep (se 1 (by rfl) ⟨888779, by rfl⟩ : syracuseStep 1185039 = 1777559) B1777559
theorem B10122529 : Blo 1184409 10122529 := bstep (se 2 (by rfl) ⟨3795948, by rfl⟩ : syracuseStep 10122529 = 7591897) B7591897
theorem B1185083 : Blo 1184409 1185083 := bstep (se 1 (by rfl) ⟨888812, by rfl⟩ : syracuseStep 1185083 = 1777625) B1777625
theorem B1897847 : Blo 1184409 1897847 := bstep (se 1 (by rfl) ⟨1423385, by rfl⟩ : syracuseStep 1897847 = 2846771) B2846771
theorem B1185159 : Blo 1184409 1185159 := bstep (se 1 (by rfl) ⟨888869, by rfl⟩ : syracuseStep 1185159 = 1777739) B1777739
theorem B2250119 : Blo 1184409 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B2848135 : Blo 1184409 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B1185167 : Blo 1184409 1185167 := bstep (se 1 (by rfl) ⟨888875, by rfl⟩ : syracuseStep 1185167 = 1777751) B1777751
theorem B2667923 : Blo 1184409 2667923 := bstep (se 1 (by rfl) ⟨2000942, by rfl⟩ : syracuseStep 2667923 = 4001885) B4001885
theorem B1185211 : Blo 1184409 1185211 := bstep (se 1 (by rfl) ⟨888908, by rfl⟩ : syracuseStep 1185211 = 1777817) B1777817
theorem B2667977 : Blo 1184409 2667977 := bstep (se 2 (by rfl) ⟨1000491, by rfl⟩ : syracuseStep 2667977 = 2000983) B2000983
theorem B1185287 : Blo 1184409 1185287 := bstep (se 1 (by rfl) ⟨888965, by rfl⟩ : syracuseStep 1185287 = 1777931) B1777931
theorem B3798539 : Blo 1184409 3798539 := bstep (se 1 (by rfl) ⟨2848904, by rfl⟩ : syracuseStep 3798539 = 5697809) B5697809
theorem B1332751 : Blo 1184409 1332751 := bstep (se 1 (by rfl) ⟨999563, by rfl⟩ : syracuseStep 1332751 = 1999127) B1999127
theorem B1185295 : Blo 1184409 1185295 := bstep (se 1 (by rfl) ⟨888971, by rfl⟩ : syracuseStep 1185295 = 1777943) B1777943
theorem B1185339 : Blo 1184409 1185339 := bstep (se 1 (by rfl) ⟨889004, by rfl⟩ : syracuseStep 1185339 = 1778009) B1778009
theorem B1185415 : Blo 1184409 1185415 := bstep (se 1 (by rfl) ⟨889061, by rfl⟩ : syracuseStep 1185415 = 1778123) B1778123
theorem B1422991 : Blo 1184409 1422991 := bstep (se 1 (by rfl) ⟨1067243, by rfl⟩ : syracuseStep 1422991 = 2134487) B2134487
theorem B1185423 : Blo 1184409 1185423 := bstep (se 1 (by rfl) ⟨889067, by rfl⟩ : syracuseStep 1185423 = 1778135) B1778135
theorem B1185467 : Blo 1184409 1185467 := bstep (se 1 (by rfl) ⟨889100, by rfl⟩ : syracuseStep 1185467 = 1778201) B1778201
theorem B1185543 : Blo 1184409 1185543 := bstep (se 1 (by rfl) ⟨889157, by rfl⟩ : syracuseStep 1185543 = 1778315) B1778315
theorem B9000719 : Blo 1184409 9000719 := bstep (se 1 (by rfl) ⟨6750539, by rfl⟩ : syracuseStep 9000719 = 13501079) B13501079
theorem B1185551 : Blo 1184409 1185551 := bstep (se 1 (by rfl) ⟨889163, by rfl⟩ : syracuseStep 1185551 = 1778327) B1778327
theorem B3372833 : Blo 1184409 3372833 := bstep (se 2 (by rfl) ⟨1264812, by rfl⟩ : syracuseStep 3372833 = 2529625) B2529625
theorem B13498163 : Blo 1184409 13498163 := bstep (se 1 (by rfl) ⟨10123622, by rfl⟩ : syracuseStep 13498163 = 20247245) B20247245
theorem B1185595 : Blo 1184409 1185595 := bstep (se 1 (by rfl) ⟨889196, by rfl⟩ : syracuseStep 1185595 = 1778393) B1778393
theorem B5699443 : Blo 1184409 5699443 := bstep (se 1 (by rfl) ⟨4274582, by rfl⟩ : syracuseStep 5699443 = 8549165) B8549165
theorem B1185671 : Blo 1184409 1185671 := bstep (se 1 (by rfl) ⟨889253, by rfl⟩ : syracuseStep 1185671 = 1778507) B1778507
theorem B1185679 : Blo 1184409 1185679 := bstep (se 1 (by rfl) ⟨889259, by rfl⟩ : syracuseStep 1185679 = 1778519) B1778519
theorem B3372947 : Blo 1184409 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B22787993 : Blo 1184409 22787993 := bstep (se 2 (by rfl) ⟨8545497, by rfl⟩ : syracuseStep 22787993 = 17090995) B17090995
theorem B6002585 : Blo 1184409 6002585 := bstep (se 2 (by rfl) ⟨2250969, by rfl⟩ : syracuseStep 6002585 = 4501939) B4501939
theorem B1185723 : Blo 1184409 1185723 := bstep (se 1 (by rfl) ⟨889292, by rfl⟩ : syracuseStep 1185723 = 1778585) B1778585
theorem B6756281 : Blo 1184409 6756281 := bstep (se 2 (by rfl) ⟨2533605, by rfl⟩ : syracuseStep 6756281 = 5067211) B5067211
theorem B1333255 : Blo 1184409 1333255 := bstep (se 1 (by rfl) ⟨999941, by rfl⟩ : syracuseStep 1333255 = 1999883) B1999883
theorem B1185799 : Blo 1184409 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B12810251 : Blo 1184409 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B1185807 : Blo 1184409 1185807 := bstep (se 1 (by rfl) ⟨889355, by rfl⟩ : syracuseStep 1185807 = 1778711) B1778711
theorem B4003883 : Blo 1184409 4003883 := bstep (se 1 (by rfl) ⟨3002912, by rfl⟩ : syracuseStep 4003883 = 6005825) B6005825
theorem B1185851 : Blo 1184409 1185851 := bstep (se 1 (by rfl) ⟨889388, by rfl⟩ : syracuseStep 1185851 = 1778777) B1778777
theorem B4388951 : Blo 1184409 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B4503671 : Blo 1184409 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B1185927 : Blo 1184409 1185927 := bstep (se 1 (by rfl) ⟨889445, by rfl⟩ : syracuseStep 1185927 = 1778891) B1778891
theorem B2668679 : Blo 1184409 2668679 := bstep (se 1 (by rfl) ⟨2001509, by rfl⟩ : syracuseStep 2668679 = 4003019) B4003019
theorem B1185935 : Blo 1184409 1185935 := bstep (se 1 (by rfl) ⟨889451, by rfl⟩ : syracuseStep 1185935 = 1778903) B1778903
theorem B1333435 : Blo 1184409 1333435 := bstep (se 1 (by rfl) ⟨1000076, by rfl⟩ : syracuseStep 1333435 = 2000153) B2000153
theorem B1185979 : Blo 1184409 1185979 := bstep (se 1 (by rfl) ⟨889484, by rfl⟩ : syracuseStep 1185979 = 1778969) B1778969
theorem B1186055 : Blo 1184409 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B2849039 : Blo 1184409 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B1186063 : Blo 1184409 1186063 := bstep (se 1 (by rfl) ⟨889547, by rfl⟩ : syracuseStep 1186063 = 1779095) B1779095
theorem B9607457 : Blo 1184409 9607457 := bstep (se 2 (by rfl) ⟨3602796, by rfl⟩ : syracuseStep 9607457 = 7205593) B7205593
theorem B1186107 : Blo 1184409 1186107 := bstep (se 1 (by rfl) ⟨889580, by rfl⟩ : syracuseStep 1186107 = 1779161) B1779161
theorem B2668859 : Blo 1184409 2668859 := bstep (se 1 (by rfl) ⟨2001644, by rfl⟩ : syracuseStep 2668859 = 4003289) B4003289
theorem B1186183 : Blo 1184409 1186183 := bstep (se 1 (by rfl) ⟨889637, by rfl⟩ : syracuseStep 1186183 = 1779275) B1779275
theorem B1186191 : Blo 1184409 1186191 := bstep (se 1 (by rfl) ⟨889643, by rfl⟩ : syracuseStep 1186191 = 1779287) B1779287
theorem B9615761 : Blo 1184409 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B2668985 : Blo 1184409 2668985 := bstep (se 2 (by rfl) ⟨1000869, by rfl⟩ : syracuseStep 2668985 = 2001739) B2001739
theorem B1186235 : Blo 1184409 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B1186311 : Blo 1184409 1186311 := bstep (se 1 (by rfl) ⟨889733, by rfl⟩ : syracuseStep 1186311 = 1779467) B1779467
theorem B1186319 : Blo 1184409 1186319 := bstep (se 1 (by rfl) ⟨889739, by rfl⟩ : syracuseStep 1186319 = 1779479) B1779479
theorem B5061163 : Blo 1184409 5061163 := bstep (se 1 (by rfl) ⟨3795872, by rfl⟩ : syracuseStep 5061163 = 7591745) B7591745
theorem B1186363 : Blo 1184409 1186363 := bstep (se 1 (by rfl) ⟨889772, by rfl⟩ : syracuseStep 1186363 = 1779545) B1779545
theorem B3799639 : Blo 1184409 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B3603079 : Blo 1184409 3603079 := bstep (se 1 (by rfl) ⟨2702309, by rfl⟩ : syracuseStep 3603079 = 5404619) B5404619
theorem B1333903 : Blo 1184409 1333903 := bstep (se 1 (by rfl) ⟨1000427, by rfl⟩ : syracuseStep 1333903 = 2000855) B2000855
theorem B3373721 : Blo 1184409 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B47422157 : Blo 1184409 47422157 := bstep (se 3 (by rfl) ⟨8891654, by rfl⟩ : syracuseStep 47422157 = 17783309) B17783309
theorem B2669327 : Blo 1184409 2669327 := bstep (se 1 (by rfl) ⟨2001995, by rfl⟩ : syracuseStep 2669327 = 4003991) B4003991
theorem B2669345 : Blo 1184409 2669345 := bstep (se 2 (by rfl) ⟨1001004, by rfl⟩ : syracuseStep 2669345 = 2002009) B2002009
theorem B1899307 : Blo 1184409 1899307 := bstep (se 1 (by rfl) ⟨1424480, by rfl⟩ : syracuseStep 1899307 = 2848961) B2848961
theorem B13687703 : Blo 1184409 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B1776647 : Blo 1184409 1776647 := bstep (se 1 (by rfl) ⟨1332485, by rfl⟩ : syracuseStep 1776647 = 2664971) B2664971
theorem B5692427 : Blo 1184409 5692427 := bstep (se 1 (by rfl) ⟨4269320, by rfl⟩ : syracuseStep 5692427 = 8538641) B8538641
theorem B1776683 : Blo 1184409 1776683 := bstep (se 1 (by rfl) ⟨1332512, by rfl⟩ : syracuseStep 1776683 = 2665025) B2665025
theorem B1686587 : Blo 1184409 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B4504643 : Blo 1184409 4504643 := bstep (se 1 (by rfl) ⟨3378482, by rfl⟩ : syracuseStep 4504643 = 6756965) B6756965
theorem B1776713 : Blo 1184409 1776713 := bstep (se 2 (by rfl) ⟨666267, by rfl⟩ : syracuseStep 1776713 = 1332535) B1332535
theorem B10132613 : Blo 1184409 10132613 := bstep (se 4 (by rfl) ⟨949932, by rfl⟩ : syracuseStep 10132613 = 1899865) B1899865
theorem B1334407 : Blo 1184409 1334407 := bstep (se 1 (by rfl) ⟨1000805, by rfl⟩ : syracuseStep 1334407 = 2001611) B2001611
theorem B1776827 : Blo 1184409 1776827 := bstep (se 1 (by rfl) ⟨1332620, by rfl⟩ : syracuseStep 1776827 = 2665241) B2665241
theorem B1776887 : Blo 1184409 1776887 := bstep (se 1 (by rfl) ⟨1332665, by rfl⟩ : syracuseStep 1776887 = 2665331) B2665331
theorem B1776911 : Blo 1184409 1776911 := bstep (se 1 (by rfl) ⟨1332683, by rfl⟩ : syracuseStep 1776911 = 2665367) B2665367
theorem B1776953 : Blo 1184409 1776953 := bstep (se 2 (by rfl) ⟨666357, by rfl⟩ : syracuseStep 1776953 = 1332715) B1332715
theorem B1334587 : Blo 1184409 1334587 := bstep (se 1 (by rfl) ⟨1000940, by rfl⟩ : syracuseStep 1334587 = 2001881) B2001881
theorem B1777031 : Blo 1184409 1777031 := bstep (se 1 (by rfl) ⟨1332773, by rfl⟩ : syracuseStep 1777031 = 2665547) B2665547
theorem B1777067 : Blo 1184409 1777067 := bstep (se 1 (by rfl) ⟨1332800, by rfl⟩ : syracuseStep 1777067 = 2665601) B2665601
theorem B2137529 : Blo 1184409 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B1424827 : Blo 1184409 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B1777097 : Blo 1184409 1777097 := bstep (se 2 (by rfl) ⟨666411, by rfl⟩ : syracuseStep 1777097 = 1332823) B1332823
theorem B1711631 : Blo 1184409 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B1777211 : Blo 1184409 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B1777271 : Blo 1184409 1777271 := bstep (se 1 (by rfl) ⟨1332953, by rfl⟩ : syracuseStep 1777271 = 2665907) B2665907
theorem B1777295 : Blo 1184409 1777295 := bstep (se 1 (by rfl) ⟨1332971, by rfl⟩ : syracuseStep 1777295 = 2665943) B2665943
theorem B1777337 : Blo 1184409 1777337 := bstep (se 2 (by rfl) ⟨666501, by rfl⟩ : syracuseStep 1777337 = 1333003) B1333003
theorem B1687225 : Blo 1184409 1687225 := bstep (se 2 (by rfl) ⟨632709, by rfl⟩ : syracuseStep 1687225 = 1265419) B1265419
theorem B8544001 : Blo 1184409 8544001 := bstep (se 2 (by rfl) ⟨3204000, by rfl⟩ : syracuseStep 8544001 = 6408001) B6408001
theorem B1777415 : Blo 1184409 1777415 := bstep (se 1 (by rfl) ⟨1333061, by rfl⟩ : syracuseStep 1777415 = 2666123) B2666123
theorem B13868815 : Blo 1184409 13868815 := bstep (se 1 (by rfl) ⟨10401611, by rfl⟩ : syracuseStep 13868815 = 20803223) B20803223
theorem B7593743 : Blo 1184409 7593743 := bstep (se 1 (by rfl) ⟨5695307, by rfl⟩ : syracuseStep 7593743 = 11390615) B11390615
theorem B1777451 : Blo 1184409 1777451 := bstep (se 1 (by rfl) ⟨1333088, by rfl⟩ : syracuseStep 1777451 = 2666177) B2666177
theorem B1687339 : Blo 1184409 1687339 := bstep (se 1 (by rfl) ⟨1265504, by rfl⟩ : syracuseStep 1687339 = 2531009) B2531009
theorem B1777481 : Blo 1184409 1777481 := bstep (se 2 (by rfl) ⟨666555, by rfl⟩ : syracuseStep 1777481 = 1333111) B1333111
theorem B1777595 : Blo 1184409 1777595 := bstep (se 1 (by rfl) ⟨1333196, by rfl⟩ : syracuseStep 1777595 = 2666393) B2666393
theorem B1777655 : Blo 1184409 1777655 := bstep (se 1 (by rfl) ⟨1333241, by rfl⟩ : syracuseStep 1777655 = 2666483) B2666483
theorem B1998857 : Blo 1184409 1998857 := bstep (se 2 (by rfl) ⟨749571, by rfl⟩ : syracuseStep 1998857 = 1499143) B1499143
theorem B1777673 : Blo 1184409 1777673 := bstep (se 2 (by rfl) ⟨666627, by rfl⟩ : syracuseStep 1777673 = 1333255) B1333255
theorem B1777703 : Blo 1184409 1777703 := bstep (se 1 (by rfl) ⟨1333277, by rfl⟩ : syracuseStep 1777703 = 2666555) B2666555
theorem B1777787 : Blo 1184409 1777787 := bstep (se 1 (by rfl) ⟨1333340, by rfl⟩ : syracuseStep 1777787 = 2666681) B2666681
theorem B4497565 : Blo 1184409 4497565 := bstep (se 3 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 4497565 = 1686587) B1686587
theorem B1999019 : Blo 1184409 1999019 := bstep (se 1 (by rfl) ⟨1499264, by rfl⟩ : syracuseStep 1999019 = 2998529) B2998529
theorem B3997943 : Blo 1184409 3997943 := bstep (se 1 (by rfl) ⟨2998457, by rfl⟩ : syracuseStep 3997943 = 5996915) B5996915
theorem B1777913 : Blo 1184409 1777913 := bstep (se 2 (by rfl) ⟨666717, by rfl⟩ : syracuseStep 1777913 = 1333435) B1333435
theorem B1778015 : Blo 1184409 1778015 := bstep (se 1 (by rfl) ⟨1333511, by rfl⟩ : syracuseStep 1778015 = 2667023) B2667023
theorem B3604841 : Blo 1184409 3604841 := bstep (se 2 (by rfl) ⟨1351815, by rfl⟩ : syracuseStep 3604841 = 2703631) B2703631
theorem B1778027 : Blo 1184409 1778027 := bstep (se 1 (by rfl) ⟨1333520, by rfl⟩ : syracuseStep 1778027 = 2667041) B2667041
theorem B4809179 : Blo 1184409 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B6750701 : Blo 1184409 6750701 := bstep (se 3 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 6750701 = 2531513) B2531513
theorem B16032259 : Blo 1184409 16032259 := bstep (se 1 (by rfl) ⟨12024194, by rfl⟩ : syracuseStep 16032259 = 24048389) B24048389
theorem B1999417 : Blo 1184409 1999417 := bstep (se 2 (by rfl) ⟨749781, by rfl⟩ : syracuseStep 1999417 = 1499563) B1499563
theorem B3998267 : Blo 1184409 3998267 := bstep (se 1 (by rfl) ⟨2998700, by rfl⟩ : syracuseStep 3998267 = 5997401) B5997401
theorem B1778255 : Blo 1184409 1778255 := bstep (se 1 (by rfl) ⟨1333691, by rfl⟩ : syracuseStep 1778255 = 2667383) B2667383
theorem B13681325 : Blo 1184409 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B1999559 : Blo 1184409 1999559 := bstep (se 1 (by rfl) ⟨1499669, by rfl⟩ : syracuseStep 1999559 = 2999339) B2999339
theorem B1778375 : Blo 1184409 1778375 := bstep (se 1 (by rfl) ⟨1333781, by rfl⟩ : syracuseStep 1778375 = 2667563) B2667563
theorem B10822403 : Blo 1184409 10822403 := bstep (se 1 (by rfl) ⟨8116802, by rfl⟩ : syracuseStep 10822403 = 16233605) B16233605
theorem B3998537 : Blo 1184409 3998537 := bstep (se 2 (by rfl) ⟨1499451, by rfl⟩ : syracuseStep 3998537 = 2998903) B2998903
theorem B1999721 : Blo 1184409 1999721 := bstep (se 2 (by rfl) ⟨749895, by rfl⟩ : syracuseStep 1999721 = 1499791) B1499791
theorem B1778537 : Blo 1184409 1778537 := bstep (se 2 (by rfl) ⟨666951, by rfl⟩ : syracuseStep 1778537 = 1333903) B1333903
theorem B10961771 : Blo 1184409 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B1778615 : Blo 1184409 1778615 := bstep (se 1 (by rfl) ⟨1333961, by rfl⟩ : syracuseStep 1778615 = 2667923) B2667923
theorem B2999227 : Blo 1184409 2999227 := bstep (se 1 (by rfl) ⟨2249420, by rfl⟩ : syracuseStep 2999227 = 4498841) B4498841
theorem B1778651 : Blo 1184409 1778651 := bstep (se 1 (by rfl) ⟨1333988, by rfl⟩ : syracuseStep 1778651 = 2667977) B2667977
theorem B2532359 : Blo 1184409 2532359 := bstep (se 1 (by rfl) ⟨1899269, by rfl⟩ : syracuseStep 2532359 = 3798539) B3798539
theorem B8995859 : Blo 1184409 8995859 := bstep (se 1 (by rfl) ⟨6746894, by rfl⟩ : syracuseStep 8995859 = 13493789) B13493789
theorem B2000119 : Blo 1184409 2000119 := bstep (se 1 (by rfl) ⟨1500089, by rfl⟩ : syracuseStep 2000119 = 3000179) B3000179
theorem B4564349 : Blo 1184409 4564349 := bstep (se 3 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 4564349 = 1711631) B1711631
theorem B2925967 : Blo 1184409 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B3605903 : Blo 1184409 3605903 := bstep (se 1 (by rfl) ⟨2704427, by rfl⟩ : syracuseStep 3605903 = 5408855) B5408855
theorem B1779119 : Blo 1184409 1779119 := bstep (se 1 (by rfl) ⟨1334339, by rfl⟩ : syracuseStep 1779119 = 2668679) B2668679
theorem B2000315 : Blo 1184409 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B1779209 : Blo 1184409 1779209 := bstep (se 2 (by rfl) ⟨667203, by rfl⟩ : syracuseStep 1779209 = 1334407) B1334407
theorem B2000423 : Blo 1184409 2000423 := bstep (se 1 (by rfl) ⟨1500317, by rfl⟩ : syracuseStep 2000423 = 3000635) B3000635
theorem B1779239 : Blo 1184409 1779239 := bstep (se 1 (by rfl) ⟨1334429, by rfl⟩ : syracuseStep 1779239 = 2668859) B2668859
theorem B1779323 : Blo 1184409 1779323 := bstep (se 1 (by rfl) ⟨1334492, by rfl⟩ : syracuseStep 1779323 = 2668985) B2668985
theorem B41043671 : Blo 1184409 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B1779449 : Blo 1184409 1779449 := bstep (se 2 (by rfl) ⟨667293, by rfl⟩ : syracuseStep 1779449 = 1334587) B1334587
theorem B2000713 : Blo 1184409 2000713 := bstep (se 2 (by rfl) ⟨750267, by rfl⟩ : syracuseStep 2000713 = 1500535) B1500535
theorem B3376991 : Blo 1184409 3376991 := bstep (se 1 (by rfl) ⟨2532743, by rfl⟩ : syracuseStep 3376991 = 5065487) B5065487
theorem B1779551 : Blo 1184409 1779551 := bstep (se 1 (by rfl) ⟨1334663, by rfl⟩ : syracuseStep 1779551 = 2669327) B2669327
theorem B2000747 : Blo 1184409 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B1779563 : Blo 1184409 1779563 := bstep (se 1 (by rfl) ⟨1334672, by rfl⟩ : syracuseStep 1779563 = 2669345) B2669345
theorem B3999671 : Blo 1184409 3999671 := bstep (se 1 (by rfl) ⟨2999753, by rfl⟩ : syracuseStep 3999671 = 5999507) B5999507
theorem B3794951 : Blo 1184409 3794951 := bstep (se 1 (by rfl) ⟨2846213, by rfl⟩ : syracuseStep 3794951 = 5692427) B5692427
theorem B7211045 : Blo 1184409 7211045 := bstep (se 4 (by rfl) ⟨676035, by rfl⟩ : syracuseStep 7211045 = 1352071) B1352071
theorem B9005093 : Blo 1184409 9005093 := bstep (se 4 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 9005093 = 1688455) B1688455
theorem B4802807 : Blo 1184409 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B2001145 : Blo 1184409 2001145 := bstep (se 2 (by rfl) ⟨750429, by rfl⟩ : syracuseStep 2001145 = 1500859) B1500859
theorem B5998859 : Blo 1184409 5998859 := bstep (se 1 (by rfl) ⟨4499144, by rfl⟩ : syracuseStep 5998859 = 8998289) B8998289
theorem B18491753 : Blo 1184409 18491753 := bstep (se 2 (by rfl) ⟨6934407, by rfl⟩ : syracuseStep 18491753 = 13868815) B13868815
theorem B2001415 : Blo 1184409 2001415 := bstep (se 1 (by rfl) ⟨1501061, by rfl⟩ : syracuseStep 2001415 = 3002123) B3002123
theorem B4000265 : Blo 1184409 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B54774407 : Blo 1184409 54774407 := bstep (se 1 (by rfl) ⟨41080805, by rfl⟩ : syracuseStep 54774407 = 82161611) B82161611
theorem B3378095 : Blo 1184409 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B2001847 : Blo 1184409 2001847 := bstep (se 1 (by rfl) ⟨1501385, by rfl⟩ : syracuseStep 2001847 = 3002771) B3002771
theorem B2665403 : Blo 1184409 2665403 := bstep (se 1 (by rfl) ⟨1999052, by rfl⟩ : syracuseStep 2665403 = 3998105) B3998105
theorem B4500481 : Blo 1184409 4500481 := bstep (se 2 (by rfl) ⟨1687680, by rfl⟩ : syracuseStep 4500481 = 3375361) B3375361
theorem B2665529 : Blo 1184409 2665529 := bstep (se 2 (by rfl) ⟨999573, by rfl⟩ : syracuseStep 2665529 = 1999147) B1999147
theorem B2002043 : Blo 1184409 2002043 := bstep (se 1 (by rfl) ⟨1501532, by rfl⟩ : syracuseStep 2002043 = 3003065) B3003065
theorem B4001129 : Blo 1184409 4001129 := bstep (se 2 (by rfl) ⟨1500423, by rfl⟩ : syracuseStep 4001129 = 3000847) B3000847
theorem B2665871 : Blo 1184409 2665871 := bstep (se 1 (by rfl) ⟨1999403, by rfl⟩ : syracuseStep 2665871 = 3998807) B3998807
theorem B7589285 : Blo 1184409 7589285 := bstep (se 4 (by rfl) ⟨711495, by rfl⟩ : syracuseStep 7589285 = 1422991) B1422991
theorem B25619885 : Blo 1184409 25619885 := bstep (se 3 (by rfl) ⟨4803728, by rfl⟩ : syracuseStep 25619885 = 9607457) B9607457
theorem B3001819 : Blo 1184409 3001819 := bstep (se 1 (by rfl) ⟨2251364, by rfl⟩ : syracuseStep 3001819 = 4502729) B4502729
theorem B4804105 : Blo 1184409 4804105 := bstep (se 2 (by rfl) ⟨1801539, by rfl⟩ : syracuseStep 4804105 = 3603079) B3603079
theorem B1265231 : Blo 1184409 1265231 := bstep (se 1 (by rfl) ⟨948923, by rfl⟩ : syracuseStep 1265231 = 1897847) B1897847
theorem B7704209 : Blo 1184409 7704209 := bstep (se 2 (by rfl) ⟨2889078, by rfl⟩ : syracuseStep 7704209 = 5778157) B5778157
theorem B6000317 : Blo 1184409 6000317 := bstep (se 3 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 6000317 = 2250119) B2250119
theorem B2666195 : Blo 1184409 2666195 := bstep (se 1 (by rfl) ⟨1999646, by rfl⟩ : syracuseStep 2666195 = 3999293) B3999293
theorem B4501241 : Blo 1184409 4501241 := bstep (se 2 (by rfl) ⟨1687965, by rfl⟩ : syracuseStep 4501241 = 3375931) B3375931
theorem B6000479 : Blo 1184409 6000479 := bstep (se 1 (by rfl) ⟨4500359, by rfl⟩ : syracuseStep 6000479 = 9000719) B9000719
theorem B2404201 : Blo 1184409 2404201 := bstep (se 2 (by rfl) ⟨901575, by rfl⟩ : syracuseStep 2404201 = 1803151) B1803151
theorem B2248555 : Blo 1184409 2248555 := bstep (se 1 (by rfl) ⟨1686416, by rfl⟩ : syracuseStep 2248555 = 3372833) B3372833
theorem B8998775 : Blo 1184409 8998775 := bstep (se 1 (by rfl) ⟨6749081, by rfl⟩ : syracuseStep 8998775 = 13498163) B13498163
theorem B2248631 : Blo 1184409 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B15191995 : Blo 1184409 15191995 := bstep (se 1 (by rfl) ⟨11393996, by rfl⟩ : syracuseStep 15191995 = 22787993) B22787993
theorem B4001723 : Blo 1184409 4001723 := bstep (se 1 (by rfl) ⟨3001292, by rfl⟩ : syracuseStep 4001723 = 6002585) B6002585
theorem B8540167 : Blo 1184409 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B3002447 : Blo 1184409 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B10129637 : Blo 1184409 10129637 := bstep (se 4 (by rfl) ⟨949653, by rfl⟩ : syracuseStep 10129637 = 1899307) B1899307
theorem B6410507 : Blo 1184409 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B13496705 : Blo 1184409 13496705 := bstep (se 2 (by rfl) ⟨5061264, by rfl⟩ : syracuseStep 13496705 = 10122529) B10122529
theorem B2249147 : Blo 1184409 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B3797513 : Blo 1184409 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B2667131 : Blo 1184409 2667131 := bstep (se 1 (by rfl) ⟨2000348, by rfl⟩ : syracuseStep 2667131 = 4000697) B4000697
theorem B6746759 : Blo 1184409 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B1184431 : Blo 1184409 1184431 := bstep (se 1 (by rfl) ⟨888323, by rfl⟩ : syracuseStep 1184431 = 1776647) B1776647
theorem B1184455 : Blo 1184409 1184455 := bstep (se 1 (by rfl) ⟨888341, by rfl⟩ : syracuseStep 1184455 = 1776683) B1776683
theorem B3420883 : Blo 1184409 3420883 := bstep (se 1 (by rfl) ⟨2565662, by rfl⟩ : syracuseStep 3420883 = 5131325) B5131325
theorem B3003095 : Blo 1184409 3003095 := bstep (se 1 (by rfl) ⟨2252321, by rfl⟩ : syracuseStep 3003095 = 4504643) B4504643
theorem B1184475 : Blo 1184409 1184475 := bstep (se 1 (by rfl) ⟨888356, by rfl⟩ : syracuseStep 1184475 = 1776713) B1776713
theorem B2667257 : Blo 1184409 2667257 := bstep (se 2 (by rfl) ⟨1000221, by rfl⟩ : syracuseStep 2667257 = 2000443) B2000443
theorem B6755075 : Blo 1184409 6755075 := bstep (se 1 (by rfl) ⟨5066306, by rfl⟩ : syracuseStep 6755075 = 10132613) B10132613
theorem B28816145 : Blo 1184409 28816145 := bstep (se 2 (by rfl) ⟨10806054, by rfl⟩ : syracuseStep 28816145 = 21612109) B21612109
theorem B1184551 : Blo 1184409 1184551 := bstep (se 1 (by rfl) ⟨888413, by rfl⟩ : syracuseStep 1184551 = 1776827) B1776827
theorem B1184591 : Blo 1184409 1184591 := bstep (se 1 (by rfl) ⟨888443, by rfl⟩ : syracuseStep 1184591 = 1776887) B1776887
theorem B1184607 : Blo 1184409 1184607 := bstep (se 1 (by rfl) ⟨888455, by rfl⟩ : syracuseStep 1184607 = 1776911) B1776911
theorem B1184635 : Blo 1184409 1184635 := bstep (se 1 (by rfl) ⟨888476, by rfl⟩ : syracuseStep 1184635 = 1776953) B1776953
theorem B2249633 : Blo 1184409 2249633 := bstep (se 2 (by rfl) ⟨843612, by rfl⟩ : syracuseStep 2249633 = 1687225) B1687225
theorem B1184687 : Blo 1184409 1184687 := bstep (se 1 (by rfl) ⟨888515, by rfl⟩ : syracuseStep 1184687 = 1777031) B1777031
theorem B1184711 : Blo 1184409 1184711 := bstep (se 1 (by rfl) ⟨888533, by rfl⟩ : syracuseStep 1184711 = 1777067) B1777067
theorem B1184731 : Blo 1184409 1184731 := bstep (se 1 (by rfl) ⟨888548, by rfl⟩ : syracuseStep 1184731 = 1777097) B1777097
theorem B11392001 : Blo 1184409 11392001 := bstep (se 2 (by rfl) ⟨4272000, by rfl⟩ : syracuseStep 11392001 = 8544001) B8544001
theorem B2667527 : Blo 1184409 2667527 := bstep (se 1 (by rfl) ⟨2000645, by rfl⟩ : syracuseStep 2667527 = 4001291) B4001291
theorem B1184807 : Blo 1184409 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B2249785 : Blo 1184409 2249785 := bstep (se 2 (by rfl) ⟨843669, by rfl⟩ : syracuseStep 2249785 = 1687339) B1687339
theorem B1184847 : Blo 1184409 1184847 := bstep (se 1 (by rfl) ⟨888635, by rfl⟩ : syracuseStep 1184847 = 1777271) B1777271
theorem B2667599 : Blo 1184409 2667599 := bstep (se 1 (by rfl) ⟨2000699, by rfl⟩ : syracuseStep 2667599 = 4001399) B4001399
theorem B1184863 : Blo 1184409 1184863 := bstep (se 1 (by rfl) ⟨888647, by rfl⟩ : syracuseStep 1184863 = 1777295) B1777295
theorem B1184891 : Blo 1184409 1184891 := bstep (se 1 (by rfl) ⟨888668, by rfl⟩ : syracuseStep 1184891 = 1777337) B1777337
theorem B7599257 : Blo 1184409 7599257 := bstep (se 2 (by rfl) ⟨2849721, by rfl⟩ : syracuseStep 7599257 = 5699443) B5699443
theorem B4502699 : Blo 1184409 4502699 := bstep (se 1 (by rfl) ⟨3377024, by rfl⟩ : syracuseStep 4502699 = 6754049) B6754049
theorem B1184943 : Blo 1184409 1184943 := bstep (se 1 (by rfl) ⟨888707, by rfl⟩ : syracuseStep 1184943 = 1777415) B1777415
theorem B9614531 : Blo 1184409 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B1184967 : Blo 1184409 1184967 := bstep (se 1 (by rfl) ⟨888725, by rfl⟩ : syracuseStep 1184967 = 1777451) B1777451
theorem B1184987 : Blo 1184409 1184987 := bstep (se 1 (by rfl) ⟨888740, by rfl⟩ : syracuseStep 1184987 = 1777481) B1777481
theorem B1185063 : Blo 1184409 1185063 := bstep (se 1 (by rfl) ⟨888797, by rfl⟩ : syracuseStep 1185063 = 1777595) B1777595
theorem B1185103 : Blo 1184409 1185103 := bstep (se 1 (by rfl) ⟨888827, by rfl⟩ : syracuseStep 1185103 = 1777655) B1777655
theorem B3798359 : Blo 1184409 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B1185119 : Blo 1184409 1185119 := bstep (se 1 (by rfl) ⟨888839, by rfl⟩ : syracuseStep 1185119 = 1777679) B1777679
theorem B2250089 : Blo 1184409 2250089 := bstep (se 2 (by rfl) ⟨843783, by rfl⟩ : syracuseStep 2250089 = 1687567) B1687567
theorem B7591283 : Blo 1184409 7591283 := bstep (se 1 (by rfl) ⟨5693462, by rfl⟩ : syracuseStep 7591283 = 11386925) B11386925
theorem B1185147 : Blo 1184409 1185147 := bstep (se 1 (by rfl) ⟨888860, by rfl⟩ : syracuseStep 1185147 = 1777721) B1777721
theorem B1185199 : Blo 1184409 1185199 := bstep (se 1 (by rfl) ⟨888899, by rfl⟩ : syracuseStep 1185199 = 1777799) B1777799
theorem B1185223 : Blo 1184409 1185223 := bstep (se 1 (by rfl) ⟨888917, by rfl⟩ : syracuseStep 1185223 = 1777835) B1777835
theorem B77960657 : Blo 1184409 77960657 := bstep (se 2 (by rfl) ⟨29235246, by rfl⟩ : syracuseStep 77960657 = 58470493) B58470493
theorem B1185243 : Blo 1184409 1185243 := bstep (se 1 (by rfl) ⟨888932, by rfl⟩ : syracuseStep 1185243 = 1777865) B1777865
theorem B2667995 : Blo 1184409 2667995 := bstep (se 1 (by rfl) ⟨2000996, by rfl⟩ : syracuseStep 2667995 = 4001993) B4001993
theorem B1185319 : Blo 1184409 1185319 := bstep (se 1 (by rfl) ⟨888989, by rfl⟩ : syracuseStep 1185319 = 1777979) B1777979
theorem B1185359 : Blo 1184409 1185359 := bstep (se 1 (by rfl) ⟨889019, by rfl⟩ : syracuseStep 1185359 = 1778039) B1778039
theorem B1185375 : Blo 1184409 1185375 := bstep (se 1 (by rfl) ⟨889031, by rfl⟩ : syracuseStep 1185375 = 1778063) B1778063
theorem B1332859 : Blo 1184409 1332859 := bstep (se 1 (by rfl) ⟨999644, by rfl⟩ : syracuseStep 1332859 = 1999289) B1999289
theorem B1185403 : Blo 1184409 1185403 := bstep (se 1 (by rfl) ⟨889052, by rfl⟩ : syracuseStep 1185403 = 1778105) B1778105
theorem B4003451 : Blo 1184409 4003451 := bstep (se 1 (by rfl) ⟨3002588, by rfl⟩ : syracuseStep 4003451 = 6005177) B6005177
theorem B1185455 : Blo 1184409 1185455 := bstep (se 1 (by rfl) ⟨889091, by rfl⟩ : syracuseStep 1185455 = 1778183) B1778183
theorem B1185479 : Blo 1184409 1185479 := bstep (se 1 (by rfl) ⟨889109, by rfl⟩ : syracuseStep 1185479 = 1778219) B1778219
theorem B10819271 : Blo 1184409 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B1185499 : Blo 1184409 1185499 := bstep (se 1 (by rfl) ⟨889124, by rfl⟩ : syracuseStep 1185499 = 1778249) B1778249
theorem B4003613 : Blo 1184409 4003613 := bstep (se 3 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 4003613 = 1501355) B1501355
theorem B20264741 : Blo 1184409 20264741 := bstep (se 4 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 20264741 = 3799639) B3799639
theorem B1185575 : Blo 1184409 1185575 := bstep (se 1 (by rfl) ⟨889181, by rfl⟩ : syracuseStep 1185575 = 1778363) B1778363
theorem B1185615 : Blo 1184409 1185615 := bstep (se 1 (by rfl) ⟨889211, by rfl⟩ : syracuseStep 1185615 = 1778423) B1778423
theorem B1185631 : Blo 1184409 1185631 := bstep (se 1 (by rfl) ⟨889223, by rfl⟩ : syracuseStep 1185631 = 1778447) B1778447
theorem B1185659 : Blo 1184409 1185659 := bstep (se 1 (by rfl) ⟨889244, by rfl⟩ : syracuseStep 1185659 = 1778489) B1778489
theorem B1185711 : Blo 1184409 1185711 := bstep (se 1 (by rfl) ⟨889283, by rfl⟩ : syracuseStep 1185711 = 1778567) B1778567
theorem B2668463 : Blo 1184409 2668463 := bstep (se 1 (by rfl) ⟨2001347, by rfl⟩ : syracuseStep 2668463 = 4002695) B4002695
theorem B1185735 : Blo 1184409 1185735 := bstep (se 1 (by rfl) ⟨889301, by rfl⟩ : syracuseStep 1185735 = 1778603) B1778603
theorem B1185755 : Blo 1184409 1185755 := bstep (se 1 (by rfl) ⟨889316, by rfl⟩ : syracuseStep 1185755 = 1778633) B1778633
theorem B1185831 : Blo 1184409 1185831 := bstep (se 1 (by rfl) ⟨889373, by rfl⟩ : syracuseStep 1185831 = 1778747) B1778747
theorem B6748217 : Blo 1184409 6748217 := bstep (se 2 (by rfl) ⟨2530581, by rfl⟩ : syracuseStep 6748217 = 5061163) B5061163
theorem B3848249 : Blo 1184409 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B1333327 : Blo 1184409 1333327 := bstep (se 1 (by rfl) ⟨999995, by rfl⟩ : syracuseStep 1333327 = 1999991) B1999991
theorem B1185871 : Blo 1184409 1185871 := bstep (se 1 (by rfl) ⟨889403, by rfl⟩ : syracuseStep 1185871 = 1778807) B1778807
theorem B1185887 : Blo 1184409 1185887 := bstep (se 1 (by rfl) ⟨889415, by rfl⟩ : syracuseStep 1185887 = 1778831) B1778831
theorem B1185915 : Blo 1184409 1185915 := bstep (se 1 (by rfl) ⟨889436, by rfl⟩ : syracuseStep 1185915 = 1778873) B1778873
theorem B3602603 : Blo 1184409 3602603 := bstep (se 1 (by rfl) ⟨2701952, by rfl⟩ : syracuseStep 3602603 = 5403905) B5403905
theorem B2668715 : Blo 1184409 2668715 := bstep (se 1 (by rfl) ⟨2001536, by rfl⟩ : syracuseStep 2668715 = 4003073) B4003073
theorem B1185967 : Blo 1184409 1185967 := bstep (se 1 (by rfl) ⟨889475, by rfl⟩ : syracuseStep 1185967 = 1778951) B1778951
theorem B1185991 : Blo 1184409 1185991 := bstep (se 1 (by rfl) ⟨889493, by rfl⟩ : syracuseStep 1185991 = 1778987) B1778987
theorem B1186011 : Blo 1184409 1186011 := bstep (se 1 (by rfl) ⟨889508, by rfl⟩ : syracuseStep 1186011 = 1779017) B1779017
theorem B1186087 : Blo 1184409 1186087 := bstep (se 1 (by rfl) ⟨889565, by rfl⟩ : syracuseStep 1186087 = 1779131) B1779131
theorem B4503869 : Blo 1184409 4503869 := bstep (se 3 (by rfl) ⟨844475, by rfl⟩ : syracuseStep 4503869 = 1688951) B1688951
theorem B1186127 : Blo 1184409 1186127 := bstep (se 1 (by rfl) ⟨889595, by rfl⟩ : syracuseStep 1186127 = 1779191) B1779191
theorem B1186143 : Blo 1184409 1186143 := bstep (se 1 (by rfl) ⟨889607, by rfl⟩ : syracuseStep 1186143 = 1779215) B1779215
theorem B4274537 : Blo 1184409 4274537 := bstep (se 2 (by rfl) ⟨1602951, by rfl⟩ : syracuseStep 4274537 = 3205903) B3205903
theorem B1186171 : Blo 1184409 1186171 := bstep (se 1 (by rfl) ⟨889628, by rfl⟩ : syracuseStep 1186171 = 1779257) B1779257
theorem B1186223 : Blo 1184409 1186223 := bstep (se 1 (by rfl) ⟨889667, by rfl⟩ : syracuseStep 1186223 = 1779335) B1779335
theorem B1186247 : Blo 1184409 1186247 := bstep (se 1 (by rfl) ⟨889685, by rfl⟩ : syracuseStep 1186247 = 1779371) B1779371
theorem B1333723 : Blo 1184409 1333723 := bstep (se 1 (by rfl) ⟨1000292, by rfl⟩ : syracuseStep 1333723 = 2000585) B2000585
theorem B1186267 : Blo 1184409 1186267 := bstep (se 1 (by rfl) ⟨889700, by rfl⟩ : syracuseStep 1186267 = 1779401) B1779401
theorem B17332717 : Blo 1184409 17332717 := bstep (se 3 (by rfl) ⟨3249884, by rfl⟩ : syracuseStep 17332717 = 6499769) B6499769
theorem B6003233 : Blo 1184409 6003233 := bstep (se 2 (by rfl) ⟨2251212, by rfl⟩ : syracuseStep 6003233 = 4502425) B4502425
theorem B1186343 : Blo 1184409 1186343 := bstep (se 1 (by rfl) ⟨889757, by rfl⟩ : syracuseStep 1186343 = 1779515) B1779515
theorem B1186383 : Blo 1184409 1186383 := bstep (se 1 (by rfl) ⟨889787, by rfl⟩ : syracuseStep 1186383 = 1779575) B1779575
theorem B1186399 : Blo 1184409 1186399 := bstep (se 1 (by rfl) ⟨889799, by rfl⟩ : syracuseStep 1186399 = 1779599) B1779599
theorem B4504187 : Blo 1184409 4504187 := bstep (se 1 (by rfl) ⟨3378140, by rfl⟩ : syracuseStep 4504187 = 6756281) B6756281
theorem B16226993 : Blo 1184409 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B2669255 : Blo 1184409 2669255 := bstep (se 1 (by rfl) ⟨2001941, by rfl⟩ : syracuseStep 2669255 = 4003883) B4003883
theorem B3201751 : Blo 1184409 3201751 := bstep (se 1 (by rfl) ⟨2401313, by rfl⟩ : syracuseStep 3201751 = 4802627) B4802627
theorem B9616157 : Blo 1184409 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B1899359 : Blo 1184409 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B1334191 : Blo 1184409 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B1776719 : Blo 1184409 1776719 := bstep (se 1 (by rfl) ⟨1332539, by rfl⟩ : syracuseStep 1776719 = 2665079) B2665079
theorem B9002177 : Blo 1184409 9002177 := bstep (se 2 (by rfl) ⟨3375816, by rfl⟩ : syracuseStep 9002177 = 6751633) B6751633
theorem B1776839 : Blo 1184409 1776839 := bstep (se 1 (by rfl) ⟨1332629, by rfl⟩ : syracuseStep 1776839 = 2665259) B2665259
theorem B126459085 : Blo 1184409 126459085 := bstep (se 3 (by rfl) ⟨23711078, by rfl⟩ : syracuseStep 126459085 = 47422157) B47422157
theorem B1899769 : Blo 1184409 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B9125135 : Blo 1184409 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B1334623 : Blo 1184409 1334623 := bstep (se 1 (by rfl) ⟨1000967, by rfl⟩ : syracuseStep 1334623 = 2001935) B2001935
theorem B1777001 : Blo 1184409 1777001 := bstep (se 2 (by rfl) ⟨666375, by rfl⟩ : syracuseStep 1777001 = 1332751) B1332751
theorem B1777079 : Blo 1184409 1777079 := bstep (se 1 (by rfl) ⟨1332809, by rfl⟩ : syracuseStep 1777079 = 2665619) B2665619
theorem B2252215 : Blo 1184409 2252215 := bstep (se 1 (by rfl) ⟨1689161, by rfl⟩ : syracuseStep 2252215 = 3378323) B3378323
theorem B1777115 : Blo 1184409 1777115 := bstep (se 1 (by rfl) ⟨1332836, by rfl⟩ : syracuseStep 1777115 = 2665673) B2665673
theorem B2530855 : Blo 1184409 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B8994401 : Blo 1184409 8994401 := bstep (se 2 (by rfl) ⟨3372900, by rfl⟩ : syracuseStep 8994401 = 6745801) B6745801
theorem B1425019 : Blo 1184409 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B5062495 : Blo 1184409 5062495 := bstep (se 1 (by rfl) ⟨3796871, by rfl⟩ : syracuseStep 5062495 = 7593743) B7593743
theorem B2531179 : Blo 1184409 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B10952567 : Blo 1184409 10952567 := bstep (se 1 (by rfl) ⟨8214425, by rfl⟩ : syracuseStep 10952567 = 16428851) B16428851
theorem B1777583 : Blo 1184409 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B11386889 : Blo 1184409 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B1777769 : Blo 1184409 1777769 := bstep (se 2 (by rfl) ⟨666663, by rfl⟩ : syracuseStep 1777769 = 1333327) B1333327
theorem B68378741 : Blo 1184409 68378741 := bstep (se 5 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 68378741 = 6410507) B6410507
theorem B5996753 : Blo 1184409 5996753 := bstep (se 2 (by rfl) ⟨2248782, by rfl⟩ : syracuseStep 5996753 = 4497565) B4497565
theorem B2531675 : Blo 1184409 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B1778087 : Blo 1184409 1778087 := bstep (se 1 (by rfl) ⟨1333565, by rfl⟩ : syracuseStep 1778087 = 2667131) B2667131
theorem B4497839 : Blo 1184409 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B1778171 : Blo 1184409 1778171 := bstep (se 1 (by rfl) ⟨1333628, by rfl⟩ : syracuseStep 1778171 = 2667257) B2667257
theorem B19210763 : Blo 1184409 19210763 := bstep (se 1 (by rfl) ⟨14408072, by rfl⟩ : syracuseStep 19210763 = 28816145) B28816145
theorem B1778297 : Blo 1184409 1778297 := bstep (se 2 (by rfl) ⟨666861, by rfl⟩ : syracuseStep 1778297 = 1333723) B1333723
theorem B23110289 : Blo 1184409 23110289 := bstep (se 2 (by rfl) ⟨8666358, by rfl⟩ : syracuseStep 23110289 = 17332717) B17332717
theorem B7594667 : Blo 1184409 7594667 := bstep (se 1 (by rfl) ⟨5696000, by rfl⟩ : syracuseStep 7594667 = 11392001) B11392001
theorem B1778351 : Blo 1184409 1778351 := bstep (se 1 (by rfl) ⟨1333763, by rfl⟩ : syracuseStep 1778351 = 2667527) B2667527
theorem B1688239 : Blo 1184409 1688239 := bstep (se 1 (by rfl) ⟨1266179, by rfl⟩ : syracuseStep 1688239 = 2532359) B2532359
theorem B5997239 : Blo 1184409 5997239 := bstep (se 1 (by rfl) ⟨4497929, by rfl⟩ : syracuseStep 5997239 = 8995859) B8995859
theorem B1778399 : Blo 1184409 1778399 := bstep (se 1 (by rfl) ⟨1333799, by rfl⟩ : syracuseStep 1778399 = 2667599) B2667599
theorem B2532239 : Blo 1184409 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B1500059 : Blo 1184409 1500059 := bstep (se 1 (by rfl) ⟨1125044, by rfl⟩ : syracuseStep 1500059 = 2250089) B2250089
theorem B1778663 : Blo 1184409 1778663 := bstep (se 1 (by rfl) ⟨1333997, by rfl⟩ : syracuseStep 1778663 = 2667995) B2667995
theorem B27362447 : Blo 1184409 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B5997725 : Blo 1184409 5997725 := bstep (se 3 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 5997725 = 2249147) B2249147
theorem B13509827 : Blo 1184409 13509827 := bstep (se 1 (by rfl) ⟨10132370, by rfl⟩ : syracuseStep 13509827 = 20264741) B20264741
theorem B1778921 : Blo 1184409 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B3998969 : Blo 1184409 3998969 := bstep (se 2 (by rfl) ⟨1499613, by rfl⟩ : syracuseStep 3998969 = 2999227) B2999227
theorem B1778975 : Blo 1184409 1778975 := bstep (se 1 (by rfl) ⟨1334231, by rfl⟩ : syracuseStep 1778975 = 2668463) B2668463
theorem B4498811 : Blo 1184409 4498811 := bstep (se 1 (by rfl) ⟨3374108, by rfl⟩ : syracuseStep 4498811 = 6748217) B6748217
theorem B2999713 : Blo 1184409 2999713 := bstep (se 2 (by rfl) ⟨1124892, by rfl⟩ : syracuseStep 2999713 = 2249785) B2249785
theorem B2401735 : Blo 1184409 2401735 := bstep (se 1 (by rfl) ⟨1801301, by rfl⟩ : syracuseStep 2401735 = 3602603) B3602603
theorem B1779143 : Blo 1184409 1779143 := bstep (se 1 (by rfl) ⟨1334357, by rfl⟩ : syracuseStep 1779143 = 2668715) B2668715
theorem B3999239 : Blo 1184409 3999239 := bstep (se 1 (by rfl) ⟨2999429, by rfl⟩ : syracuseStep 3999239 = 5998859) B5998859
theorem B2533025 : Blo 1184409 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B1779497 : Blo 1184409 1779497 := bstep (se 2 (by rfl) ⟨667311, by rfl⟩ : syracuseStep 1779497 = 1334623) B1334623
theorem B1779503 : Blo 1184409 1779503 := bstep (se 1 (by rfl) ⟨1334627, by rfl⟩ : syracuseStep 1779503 = 2669255) B2669255
theorem B3901289 : Blo 1184409 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B29231389 : Blo 1184409 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B5999021 : Blo 1184409 5999021 := bstep (se 3 (by rfl) ⟨1124816, by rfl⟩ : syracuseStep 5999021 = 2249633) B2249633
theorem B4000211 : Blo 1184409 4000211 := bstep (se 1 (by rfl) ⟨3000158, by rfl⟩ : syracuseStep 4000211 = 6000317) B6000317
theorem B3205601 : Blo 1184409 3205601 := bstep (se 2 (by rfl) ⟨1202100, by rfl⟩ : syracuseStep 3205601 = 2404201) B2404201
theorem B3000827 : Blo 1184409 3000827 := bstep (se 1 (by rfl) ⟨2250620, by rfl⟩ : syracuseStep 3000827 = 4501241) B4501241
theorem B4000319 : Blo 1184409 4000319 := bstep (se 1 (by rfl) ⟨3000239, by rfl⟩ : syracuseStep 4000319 = 6000479) B6000479
theorem B7301711 : Blo 1184409 7301711 := bstep (se 1 (by rfl) ⟨5476283, by rfl⟩ : syracuseStep 7301711 = 10952567) B10952567
theorem B5999183 : Blo 1184409 5999183 := bstep (se 1 (by rfl) ⟨4499387, by rfl⟩ : syracuseStep 5999183 = 8998775) B8998775
theorem B2001631 : Blo 1184409 2001631 := bstep (se 1 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 2001631 = 3002447) B3002447
theorem B6753091 : Blo 1184409 6753091 := bstep (se 1 (by rfl) ⟨5064818, by rfl⟩ : syracuseStep 6753091 = 10129637) B10129637
theorem B2665295 : Blo 1184409 2665295 := bstep (se 1 (by rfl) ⟨1998971, by rfl⟩ : syracuseStep 2665295 = 3997943) B3997943
theorem B2403227 : Blo 1184409 2403227 := bstep (se 1 (by rfl) ⟨1802420, by rfl⟩ : syracuseStep 2403227 = 3604841) B3604841
theorem B8997803 : Blo 1184409 8997803 := bstep (se 1 (by rfl) ⟨6748352, by rfl⟩ : syracuseStep 8997803 = 13496705) B13496705
theorem B4500467 : Blo 1184409 4500467 := bstep (se 1 (by rfl) ⟨3375350, by rfl⟩ : syracuseStep 4500467 = 6750701) B6750701
theorem B2665511 : Blo 1184409 2665511 := bstep (se 1 (by rfl) ⟨1999133, by rfl⟩ : syracuseStep 2665511 = 3998267) B3998267
theorem B9120883 : Blo 1184409 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B2002063 : Blo 1184409 2002063 := bstep (se 1 (by rfl) ⟨1501547, by rfl⟩ : syracuseStep 2002063 = 3003095) B3003095
theorem B2665691 : Blo 1184409 2665691 := bstep (se 1 (by rfl) ⟨1999268, by rfl⟩ : syracuseStep 2665691 = 3998537) B3998537
theorem B2665889 : Blo 1184409 2665889 := bstep (se 2 (by rfl) ⟨999708, by rfl⟩ : syracuseStep 2665889 = 1999417) B1999417
theorem B5066171 : Blo 1184409 5066171 := bstep (se 1 (by rfl) ⟨3799628, by rfl⟩ : syracuseStep 5066171 = 7599257) B7599257
theorem B3001799 : Blo 1184409 3001799 := bstep (se 1 (by rfl) ⟨2251349, by rfl⟩ : syracuseStep 3001799 = 4502699) B4502699
theorem B6409687 : Blo 1184409 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B3042899 : Blo 1184409 3042899 := bstep (se 1 (by rfl) ⟨2282174, by rfl⟩ : syracuseStep 3042899 = 4564349) B4564349
theorem B2403935 : Blo 1184409 2403935 := bstep (se 1 (by rfl) ⟨1802951, by rfl⟩ : syracuseStep 2403935 = 3605903) B3605903
theorem B11398765 : Blo 1184409 11398765 := bstep (se 3 (by rfl) ⟨2137268, by rfl⟩ : syracuseStep 11398765 = 4274537) B4274537
theorem B51973771 : Blo 1184409 51973771 := bstep (se 1 (by rfl) ⟨38980328, by rfl⟩ : syracuseStep 51973771 = 77960657) B77960657
theorem B17076005 : Blo 1184409 17076005 := bstep (se 4 (by rfl) ⟨1600875, by rfl⟩ : syracuseStep 17076005 = 3201751) B3201751
theorem B7212847 : Blo 1184409 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B12824477 : Blo 1184409 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B2666447 : Blo 1184409 2666447 := bstep (se 1 (by rfl) ⟨1999835, by rfl⟩ : syracuseStep 2666447 = 3999671) B3999671
theorem B6000641 : Blo 1184409 6000641 := bstep (se 2 (by rfl) ⟨2250240, by rfl⟩ : syracuseStep 6000641 = 4500481) B4500481
theorem B3002579 : Blo 1184409 3002579 := bstep (se 1 (by rfl) ⟨2251934, by rfl⟩ : syracuseStep 3002579 = 4503869) B4503869
theorem B168612113 : Blo 1184409 168612113 := bstep (se 2 (by rfl) ⟨63229542, by rfl⟩ : syracuseStep 168612113 = 126459085) B126459085
theorem B2666825 : Blo 1184409 2666825 := bstep (se 2 (by rfl) ⟨1000059, by rfl⟩ : syracuseStep 2666825 = 2000119) B2000119
theorem B2666843 : Blo 1184409 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B4002155 : Blo 1184409 4002155 := bstep (se 1 (by rfl) ⟨3001616, by rfl⟩ : syracuseStep 4002155 = 6003233) B6003233
theorem B3002791 : Blo 1184409 3002791 := bstep (se 1 (by rfl) ⟨2252093, by rfl⟩ : syracuseStep 3002791 = 4504187) B4504187
theorem B36516271 : Blo 1184409 36516271 := bstep (se 1 (by rfl) ⟨27387203, by rfl⟩ : syracuseStep 36516271 = 54774407) B54774407
theorem B10817995 : Blo 1184409 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B6410771 : Blo 1184409 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B1266239 : Blo 1184409 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B3002953 : Blo 1184409 3002953 := bstep (se 2 (by rfl) ⟨1126107, by rfl⟩ : syracuseStep 3002953 = 2252215) B2252215
theorem B4002425 : Blo 1184409 4002425 := bstep (se 2 (by rfl) ⟨1500909, by rfl⟩ : syracuseStep 4002425 = 3001819) B3001819
theorem B1184479 : Blo 1184409 1184479 := bstep (se 1 (by rfl) ⟨888359, by rfl⟩ : syracuseStep 1184479 = 1776719) B1776719
theorem B6001451 : Blo 1184409 6001451 := bstep (se 1 (by rfl) ⟨4501088, by rfl⟩ : syracuseStep 6001451 = 9002177) B9002177
theorem B1184559 : Blo 1184409 1184559 := bstep (se 1 (by rfl) ⟨888419, by rfl⟩ : syracuseStep 1184559 = 1776839) B1776839
theorem B6083423 : Blo 1184409 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B1184667 : Blo 1184409 1184667 := bstep (se 1 (by rfl) ⟨888500, by rfl⟩ : syracuseStep 1184667 = 1777001) B1777001
theorem B2667419 : Blo 1184409 2667419 := bstep (se 1 (by rfl) ⟨2000564, by rfl⟩ : syracuseStep 2667419 = 4001129) B4001129
theorem B5059523 : Blo 1184409 5059523 := bstep (se 1 (by rfl) ⟨3794642, by rfl⟩ : syracuseStep 5059523 = 7589285) B7589285
theorem B1184719 : Blo 1184409 1184719 := bstep (se 1 (by rfl) ⟨888539, by rfl⟩ : syracuseStep 1184719 = 1777079) B1777079
theorem B1184743 : Blo 1184409 1184743 := bstep (se 1 (by rfl) ⟨888557, by rfl⟩ : syracuseStep 1184743 = 1777115) B1777115
theorem B2667617 : Blo 1184409 2667617 := bstep (se 2 (by rfl) ⟨1000356, by rfl⟩ : syracuseStep 2667617 = 2000713) B2000713
theorem B20255993 : Blo 1184409 20255993 := bstep (se 2 (by rfl) ⟨7595997, by rfl⟩ : syracuseStep 20255993 = 15191995) B15191995
theorem B1185055 : Blo 1184409 1185055 := bstep (se 1 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 1185055 = 1777583) B1777583
theorem B2667815 : Blo 1184409 2667815 := bstep (se 1 (by rfl) ⟨2000861, by rfl⟩ : syracuseStep 2667815 = 4001723) B4001723
theorem B1332571 : Blo 1184409 1332571 := bstep (se 1 (by rfl) ⟨999428, by rfl⟩ : syracuseStep 1332571 = 1998857) B1998857
theorem B1185115 : Blo 1184409 1185115 := bstep (se 1 (by rfl) ⟨888836, by rfl⟩ : syracuseStep 1185115 = 1777673) B1777673
theorem B85505381 : Blo 1184409 85505381 := bstep (se 4 (by rfl) ⟨8016129, by rfl⟩ : syracuseStep 85505381 = 16032259) B16032259
theorem B1185135 : Blo 1184409 1185135 := bstep (se 1 (by rfl) ⟨888851, by rfl⟩ : syracuseStep 1185135 = 1777703) B1777703
theorem B1185191 : Blo 1184409 1185191 := bstep (se 1 (by rfl) ⟨888893, by rfl⟩ : syracuseStep 1185191 = 1777787) B1777787
theorem B1332679 : Blo 1184409 1332679 := bstep (se 1 (by rfl) ⟨999509, by rfl⟩ : syracuseStep 1332679 = 1999019) B1999019
theorem B10261997 : Blo 1184409 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B1185275 : Blo 1184409 1185275 := bstep (se 1 (by rfl) ⟨888956, by rfl⟩ : syracuseStep 1185275 = 1777913) B1777913
theorem B1185343 : Blo 1184409 1185343 := bstep (se 1 (by rfl) ⟨889007, by rfl⟩ : syracuseStep 1185343 = 1778015) B1778015
theorem B1185351 : Blo 1184409 1185351 := bstep (se 1 (by rfl) ⟨889013, by rfl⟩ : syracuseStep 1185351 = 1778027) B1778027
theorem B2668193 : Blo 1184409 2668193 := bstep (se 2 (by rfl) ⟨1000572, by rfl⟩ : syracuseStep 2668193 = 2001145) B2001145
theorem B1185503 : Blo 1184409 1185503 := bstep (se 1 (by rfl) ⟨889127, by rfl⟩ : syracuseStep 1185503 = 1778255) B1778255
theorem B1333039 : Blo 1184409 1333039 := bstep (se 1 (by rfl) ⟨999779, by rfl⟩ : syracuseStep 1333039 = 1999559) B1999559
theorem B1185583 : Blo 1184409 1185583 := bstep (se 1 (by rfl) ⟨889187, by rfl⟩ : syracuseStep 1185583 = 1778375) B1778375
theorem B4503383 : Blo 1184409 4503383 := bstep (se 1 (by rfl) ⟨3377537, by rfl⟩ : syracuseStep 4503383 = 6755075) B6755075
theorem B7214935 : Blo 1184409 7214935 := bstep (se 1 (by rfl) ⟨5411201, by rfl⟩ : syracuseStep 7214935 = 10822403) B10822403
theorem B1333147 : Blo 1184409 1333147 := bstep (se 1 (by rfl) ⟨999860, by rfl⟩ : syracuseStep 1333147 = 1999721) B1999721
theorem B1185691 : Blo 1184409 1185691 := bstep (se 1 (by rfl) ⟨889268, by rfl⟩ : syracuseStep 1185691 = 1778537) B1778537
theorem B1185743 : Blo 1184409 1185743 := bstep (se 1 (by rfl) ⟨889307, by rfl⟩ : syracuseStep 1185743 = 1778615) B1778615
theorem B1185767 : Blo 1184409 1185767 := bstep (se 1 (by rfl) ⟨889325, by rfl⟩ : syracuseStep 1185767 = 1778651) B1778651
theorem B2668553 : Blo 1184409 2668553 := bstep (se 2 (by rfl) ⟨1000707, by rfl⟩ : syracuseStep 2668553 = 2001415) B2001415
theorem B5060855 : Blo 1184409 5060855 := bstep (se 1 (by rfl) ⟨3795641, by rfl⟩ : syracuseStep 5060855 = 7591283) B7591283
theorem B4561177 : Blo 1184409 4561177 := bstep (se 2 (by rfl) ⟨1710441, by rfl⟩ : syracuseStep 4561177 = 3420883) B3420883
theorem B1186079 : Blo 1184409 1186079 := bstep (se 1 (by rfl) ⟨889559, by rfl⟩ : syracuseStep 1186079 = 1779119) B1779119
theorem B1333543 : Blo 1184409 1333543 := bstep (se 1 (by rfl) ⟨1000157, by rfl⟩ : syracuseStep 1333543 = 2000315) B2000315
theorem B1186139 : Blo 1184409 1186139 := bstep (se 1 (by rfl) ⟨889604, by rfl⟩ : syracuseStep 1186139 = 1779209) B1779209
theorem B1333615 : Blo 1184409 1333615 := bstep (se 1 (by rfl) ⟨1000211, by rfl⟩ : syracuseStep 1333615 = 2000423) B2000423
theorem B1186159 : Blo 1184409 1186159 := bstep (se 1 (by rfl) ⟨889619, by rfl⟩ : syracuseStep 1186159 = 1779239) B1779239
theorem B2668967 : Blo 1184409 2668967 := bstep (se 1 (by rfl) ⟨2001725, by rfl⟩ : syracuseStep 2668967 = 4003451) B4003451
theorem B1186215 : Blo 1184409 1186215 := bstep (se 1 (by rfl) ⟨889661, by rfl⟩ : syracuseStep 1186215 = 1779323) B1779323
theorem B1186299 : Blo 1184409 1186299 := bstep (se 1 (by rfl) ⟨889724, by rfl⟩ : syracuseStep 1186299 = 1779449) B1779449
theorem B2669075 : Blo 1184409 2669075 := bstep (se 1 (by rfl) ⟨2001806, by rfl⟩ : syracuseStep 2669075 = 4003613) B4003613
theorem B2251327 : Blo 1184409 2251327 := bstep (se 1 (by rfl) ⟨1688495, by rfl⟩ : syracuseStep 2251327 = 3376991) B3376991
theorem B1186367 : Blo 1184409 1186367 := bstep (se 1 (by rfl) ⟨889775, by rfl⟩ : syracuseStep 1186367 = 1779551) B1779551
theorem B1333831 : Blo 1184409 1333831 := bstep (se 1 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 1333831 = 2000747) B2000747
theorem B1186375 : Blo 1184409 1186375 := bstep (se 1 (by rfl) ⟨889781, by rfl⟩ : syracuseStep 1186375 = 1779563) B1779563
theorem B2669129 : Blo 1184409 2669129 := bstep (se 2 (by rfl) ⟨1000923, by rfl⟩ : syracuseStep 2669129 = 2001847) B2001847
theorem B2529967 : Blo 1184409 2529967 := bstep (se 1 (by rfl) ⟨1897475, by rfl⟩ : syracuseStep 2529967 = 3794951) B3794951
theorem B4807363 : Blo 1184409 4807363 := bstep (se 1 (by rfl) ⟨3605522, by rfl⟩ : syracuseStep 4807363 = 7211045) B7211045
theorem B6003395 : Blo 1184409 6003395 := bstep (se 1 (by rfl) ⟨4502546, by rfl⟩ : syracuseStep 6003395 = 9005093) B9005093
theorem B3201871 : Blo 1184409 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B3373949 : Blo 1184409 3373949 := bstep (se 3 (by rfl) ⟨632615, by rfl⟩ : syracuseStep 3373949 = 1265231) B1265231
theorem B12327835 : Blo 1184409 12327835 := bstep (se 1 (by rfl) ⟨9245876, by rfl⟩ : syracuseStep 12327835 = 18491753) B18491753
theorem B13499621 : Blo 1184409 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B2252063 : Blo 1184409 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B1776935 : Blo 1184409 1776935 := bstep (se 1 (by rfl) ⟨1332701, by rfl⟩ : syracuseStep 1776935 = 2665403) B2665403
theorem B6405473 : Blo 1184409 6405473 := bstep (se 2 (by rfl) ⟨2402052, by rfl⟩ : syracuseStep 6405473 = 4804105) B4804105
theorem B1777019 : Blo 1184409 1777019 := bstep (se 1 (by rfl) ⟨1332764, by rfl⟩ : syracuseStep 1777019 = 2665529) B2665529
theorem B3374473 : Blo 1184409 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B1334695 : Blo 1184409 1334695 := bstep (se 1 (by rfl) ⟨1001021, by rfl⟩ : syracuseStep 1334695 = 2002043) B2002043
theorem B1777145 : Blo 1184409 1777145 := bstep (se 2 (by rfl) ⟨666429, by rfl⟩ : syracuseStep 1777145 = 1332859) B1332859
theorem B1900025 : Blo 1184409 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B1777247 : Blo 1184409 1777247 := bstep (se 1 (by rfl) ⟨1332935, by rfl⟩ : syracuseStep 1777247 = 2665871) B2665871
theorem B17079923 : Blo 1184409 17079923 := bstep (se 1 (by rfl) ⟨12809942, by rfl⟩ : syracuseStep 17079923 = 25619885) B25619885
theorem B5996267 : Blo 1184409 5996267 := bstep (se 1 (by rfl) ⟨4497200, by rfl⟩ : syracuseStep 5996267 = 8994401) B8994401
theorem B5136139 : Blo 1184409 5136139 := bstep (se 1 (by rfl) ⟨3852104, by rfl⟩ : syracuseStep 5136139 = 7704209) B7704209
theorem B6749993 : Blo 1184409 6749993 := bstep (se 2 (by rfl) ⟨2531247, by rfl⟩ : syracuseStep 6749993 = 5062495) B5062495
theorem B1777463 : Blo 1184409 1777463 := bstep (se 1 (by rfl) ⟨1333097, by rfl⟩ : syracuseStep 1777463 = 2666195) B2666195
theorem B2998073 : Blo 1184409 2998073 := bstep (se 2 (by rfl) ⟨1124277, by rfl⟩ : syracuseStep 2998073 = 2248555) B2248555
theorem B1499087 : Blo 1184409 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B3997835 : Blo 1184409 3997835 := bstep (se 1 (by rfl) ⟨2998376, by rfl⟩ : syracuseStep 3997835 = 5996753) B5996753
theorem B1777883 : Blo 1184409 1777883 := bstep (se 1 (by rfl) ⟨1333412, by rfl⟩ : syracuseStep 1777883 = 2666825) B2666825
theorem B1777895 : Blo 1184409 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B2998559 : Blo 1184409 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B1778057 : Blo 1184409 1778057 := bstep (se 2 (by rfl) ⟨666771, by rfl⟩ : syracuseStep 1778057 = 1333543) B1333543
theorem B5063111 : Blo 1184409 5063111 := bstep (se 1 (by rfl) ⟨3797333, by rfl⟩ : syracuseStep 5063111 = 7594667) B7594667
theorem B3998159 : Blo 1184409 3998159 := bstep (se 1 (by rfl) ⟨2998619, by rfl⟩ : syracuseStep 3998159 = 5997239) B5997239
theorem B1778153 : Blo 1184409 1778153 := bstep (se 2 (by rfl) ⟨666807, by rfl⟩ : syracuseStep 1778153 = 1333615) B1333615
theorem B4055615 : Blo 1184409 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B1688159 : Blo 1184409 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B1778279 : Blo 1184409 1778279 := bstep (se 1 (by rfl) ⟨1333709, by rfl⟩ : syracuseStep 1778279 = 2667419) B2667419
theorem B1778411 : Blo 1184409 1778411 := bstep (se 1 (by rfl) ⟨1333808, by rfl⟩ : syracuseStep 1778411 = 2667617) B2667617
theorem B6005501 : Blo 1184409 6005501 := bstep (se 3 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 6005501 = 2252063) B2252063
theorem B1778441 : Blo 1184409 1778441 := bstep (se 2 (by rfl) ⟨666915, by rfl⟩ : syracuseStep 1778441 = 1333831) B1333831
theorem B3998483 : Blo 1184409 3998483 := bstep (se 1 (by rfl) ⟨2998862, by rfl⟩ : syracuseStep 3998483 = 5997725) B5997725
theorem B1778543 : Blo 1184409 1778543 := bstep (se 1 (by rfl) ⟨1333907, by rfl⟩ : syracuseStep 1778543 = 2667815) B2667815
theorem B6751133 : Blo 1184409 6751133 := bstep (se 3 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 6751133 = 2531675) B2531675
theorem B2999207 : Blo 1184409 2999207 := bstep (se 1 (by rfl) ⟨2249405, by rfl⟩ : syracuseStep 2999207 = 4498811) B4498811
theorem B6841331 : Blo 1184409 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B9004121 : Blo 1184409 9004121 := bstep (se 2 (by rfl) ⟨3376545, by rfl⟩ : syracuseStep 9004121 = 6753091) B6753091
theorem B4269161 : Blo 1184409 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B1778795 : Blo 1184409 1778795 := bstep (se 1 (by rfl) ⟨1334096, by rfl⟩ : syracuseStep 1778795 = 2668193) B2668193
theorem B1688683 : Blo 1184409 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B1779035 : Blo 1184409 1779035 := bstep (se 1 (by rfl) ⟨1334276, by rfl⟩ : syracuseStep 1779035 = 2668553) B2668553
theorem B3376637 : Blo 1184409 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B1779311 : Blo 1184409 1779311 := bstep (se 1 (by rfl) ⟨1334483, by rfl⟩ : syracuseStep 1779311 = 2668967) B2668967
theorem B3999347 : Blo 1184409 3999347 := bstep (se 1 (by rfl) ⟨2999510, by rfl⟩ : syracuseStep 3999347 = 5999021) B5999021
theorem B2000551 : Blo 1184409 2000551 := bstep (se 1 (by rfl) ⟨1500413, by rfl⟩ : syracuseStep 2000551 = 3000827) B3000827
theorem B1779383 : Blo 1184409 1779383 := bstep (se 1 (by rfl) ⟨1334537, by rfl⟩ : syracuseStep 1779383 = 2669075) B2669075
theorem B1779419 : Blo 1184409 1779419 := bstep (se 1 (by rfl) ⟨1334564, by rfl⟩ : syracuseStep 1779419 = 2669129) B2669129
theorem B4867807 : Blo 1184409 4867807 := bstep (se 1 (by rfl) ⟨3650855, by rfl⟩ : syracuseStep 4867807 = 7301711) B7301711
theorem B3999455 : Blo 1184409 3999455 := bstep (se 1 (by rfl) ⟨2999591, by rfl⟩ : syracuseStep 3999455 = 5999183) B5999183
theorem B4499297 : Blo 1184409 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B3999617 : Blo 1184409 3999617 := bstep (se 2 (by rfl) ⟨1499856, by rfl⟩ : syracuseStep 3999617 = 2999713) B2999713
theorem B1779593 : Blo 1184409 1779593 := bstep (se 2 (by rfl) ⟨667347, by rfl⟩ : syracuseStep 1779593 = 1334695) B1334695
theorem B5998535 : Blo 1184409 5998535 := bstep (se 1 (by rfl) ⟨4498901, by rfl⟩ : syracuseStep 5998535 = 8997803) B8997803
theorem B8546249 : Blo 1184409 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B3000311 : Blo 1184409 3000311 := bstep (se 1 (by rfl) ⟨2250233, by rfl⟩ : syracuseStep 3000311 = 4500467) B4500467
theorem B15198353 : Blo 1184409 15198353 := bstep (se 2 (by rfl) ⟨5699382, by rfl⟩ : syracuseStep 15198353 = 11398765) B11398765
theorem B69298361 : Blo 1184409 69298361 := bstep (se 2 (by rfl) ⟨25986885, by rfl⟩ : syracuseStep 69298361 = 51973771) B51973771
theorem B4270315 : Blo 1184409 4270315 := bstep (se 1 (by rfl) ⟨3202736, by rfl⟩ : syracuseStep 4270315 = 6405473) B6405473
theorem B3377447 : Blo 1184409 3377447 := bstep (se 1 (by rfl) ⟨2533085, by rfl⟩ : syracuseStep 3377447 = 5066171) B5066171
theorem B2001199 : Blo 1184409 2001199 := bstep (se 1 (by rfl) ⟨1500899, by rfl⟩ : syracuseStep 2001199 = 3001799) B3001799
theorem B4000157 : Blo 1184409 4000157 := bstep (se 3 (by rfl) ⟨750029, by rfl⟩ : syracuseStep 4000157 = 1500059) B1500059
theorem B6408605 : Blo 1184409 6408605 := bstep (se 3 (by rfl) ⟨1201613, by rfl⟩ : syracuseStep 6408605 = 2403227) B2403227
theorem B9619913 : Blo 1184409 9619913 := bstep (se 2 (by rfl) ⟨3607467, by rfl⟩ : syracuseStep 9619913 = 7214935) B7214935
theorem B4499995 : Blo 1184409 4499995 := bstep (se 1 (by rfl) ⟨3374996, by rfl⟩ : syracuseStep 4499995 = 6749993) B6749993
theorem B4000427 : Blo 1184409 4000427 := bstep (se 1 (by rfl) ⟨3000320, by rfl⟩ : syracuseStep 4000427 = 6000641) B6000641
theorem B2001719 : Blo 1184409 2001719 := bstep (se 1 (by rfl) ⟨1501289, by rfl⟩ : syracuseStep 2001719 = 3002579) B3002579
theorem B12807175 : Blo 1184409 12807175 := bstep (se 1 (by rfl) ⟨9605381, by rfl⟩ : syracuseStep 12807175 = 19210763) B19210763
theorem B6081569 : Blo 1184409 6081569 := bstep (se 2 (by rfl) ⟨2280588, by rfl⟩ : syracuseStep 6081569 = 4561177) B4561177
theorem B4000967 : Blo 1184409 4000967 := bstep (se 1 (by rfl) ⟨3000725, by rfl⟩ : syracuseStep 4000967 = 6001451) B6001451
theorem B48688361 : Blo 1184409 48688361 := bstep (se 2 (by rfl) ⟨18258135, by rfl⟩ : syracuseStep 48688361 = 36516271) B36516271
theorem B3001769 : Blo 1184409 3001769 := bstep (se 2 (by rfl) ⟨1125663, by rfl⟩ : syracuseStep 3001769 = 2251327) B2251327
theorem B9006551 : Blo 1184409 9006551 := bstep (se 1 (by rfl) ⟨6754913, by rfl⟩ : syracuseStep 9006551 = 13509827) B13509827
theorem B2665979 : Blo 1184409 2665979 := bstep (se 1 (by rfl) ⟨1999484, by rfl⟩ : syracuseStep 2665979 = 3998969) B3998969
theorem B13503995 : Blo 1184409 13503995 := bstep (se 1 (by rfl) ⟨10127996, by rfl⟩ : syracuseStep 13503995 = 20255993) B20255993
theorem B57003587 : Blo 1184409 57003587 := bstep (se 1 (by rfl) ⟨42752690, by rfl⟩ : syracuseStep 57003587 = 85505381) B85505381
theorem B6409817 : Blo 1184409 6409817 := bstep (se 2 (by rfl) ⟨2403681, by rfl⟩ : syracuseStep 6409817 = 4807363) B4807363
theorem B2666159 : Blo 1184409 2666159 := bstep (se 1 (by rfl) ⟨1999619, by rfl⟩ : syracuseStep 2666159 = 3999239) B3999239
theorem B16437113 : Blo 1184409 16437113 := bstep (se 2 (by rfl) ⟨6163917, by rfl⟩ : syracuseStep 16437113 = 12327835) B12327835
theorem B3002255 : Blo 1184409 3002255 := bstep (se 1 (by rfl) ⟨2251691, by rfl⟩ : syracuseStep 3002255 = 4503383) B4503383
theorem B12161177 : Blo 1184409 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B2666807 : Blo 1184409 2666807 := bstep (se 1 (by rfl) ⟨2000105, by rfl⟩ : syracuseStep 2666807 = 4000211) B4000211
theorem B2666879 : Blo 1184409 2666879 := bstep (se 1 (by rfl) ⟨2000159, by rfl⟩ : syracuseStep 2666879 = 4000319) B4000319
theorem B4002263 : Blo 1184409 4002263 := bstep (se 1 (by rfl) ⟨3001697, by rfl⟩ : syracuseStep 4002263 = 6003395) B6003395
theorem B2249299 : Blo 1184409 2249299 := bstep (se 1 (by rfl) ⟨1686974, by rfl⟩ : syracuseStep 2249299 = 3373949) B3373949
theorem B8999747 : Blo 1184409 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B1184623 : Blo 1184409 1184623 := bstep (se 1 (by rfl) ⟨888467, by rfl⟩ : syracuseStep 1184623 = 1776935) B1776935
theorem B1184679 : Blo 1184409 1184679 := bstep (se 1 (by rfl) ⟨888509, by rfl⟩ : syracuseStep 1184679 = 1777019) B1777019
theorem B1184763 : Blo 1184409 1184763 := bstep (se 1 (by rfl) ⟨888572, by rfl⟩ : syracuseStep 1184763 = 1777145) B1777145
theorem B1266683 : Blo 1184409 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B2028599 : Blo 1184409 2028599 := bstep (se 1 (by rfl) ⟨1521449, by rfl⟩ : syracuseStep 2028599 = 3042899) B3042899
theorem B1184831 : Blo 1184409 1184831 := bstep (se 1 (by rfl) ⟨888623, by rfl⟩ : syracuseStep 1184831 = 1777247) B1777247
theorem B1602623 : Blo 1184409 1602623 := bstep (se 1 (by rfl) ⟨1201967, by rfl⟩ : syracuseStep 1602623 = 2403935) B2403935
theorem B11384003 : Blo 1184409 11384003 := bstep (se 1 (by rfl) ⟨8538002, by rfl⟩ : syracuseStep 11384003 = 17076005) B17076005
theorem B1184975 : Blo 1184409 1184975 := bstep (se 1 (by rfl) ⟨888731, by rfl⟩ : syracuseStep 1184975 = 1777463) B1777463
theorem B8549651 : Blo 1184409 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B7591259 : Blo 1184409 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B1185179 : Blo 1184409 1185179 := bstep (se 1 (by rfl) ⟨888884, by rfl⟩ : syracuseStep 1185179 = 1777769) B1777769
theorem B45585827 : Blo 1184409 45585827 := bstep (se 1 (by rfl) ⟨34189370, by rfl⟩ : syracuseStep 45585827 = 68378741) B68378741
theorem B2668103 : Blo 1184409 2668103 := bstep (se 1 (by rfl) ⟨2001077, by rfl⟩ : syracuseStep 2668103 = 4002155) B4002155
theorem B1185391 : Blo 1184409 1185391 := bstep (se 1 (by rfl) ⟨889043, by rfl⟩ : syracuseStep 1185391 = 1778087) B1778087
theorem B1185447 : Blo 1184409 1185447 := bstep (se 1 (by rfl) ⟨889085, by rfl⟩ : syracuseStep 1185447 = 1778171) B1778171
theorem B4273847 : Blo 1184409 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 1184409 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B1185531 : Blo 1184409 1185531 := bstep (se 1 (by rfl) ⟨889148, by rfl⟩ : syracuseStep 1185531 = 1778297) B1778297
theorem B2668283 : Blo 1184409 2668283 := bstep (se 1 (by rfl) ⟨2001212, by rfl⟩ : syracuseStep 2668283 = 4002425) B4002425
theorem B15406859 : Blo 1184409 15406859 := bstep (se 1 (by rfl) ⟨11555144, by rfl⟩ : syracuseStep 15406859 = 23110289) B23110289
theorem B1185567 : Blo 1184409 1185567 := bstep (se 1 (by rfl) ⟨889175, by rfl⟩ : syracuseStep 1185567 = 1778351) B1778351
theorem B1185599 : Blo 1184409 1185599 := bstep (se 1 (by rfl) ⟨889199, by rfl⟩ : syracuseStep 1185599 = 1778399) B1778399
theorem B4003721 : Blo 1184409 4003721 := bstep (se 2 (by rfl) ⟨1501395, by rfl⟩ : syracuseStep 4003721 = 3002791) B3002791
theorem B14423993 : Blo 1184409 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B3373015 : Blo 1184409 3373015 := bstep (se 1 (by rfl) ⟨2529761, by rfl⟩ : syracuseStep 3373015 = 5059523) B5059523
theorem B1185775 : Blo 1184409 1185775 := bstep (se 1 (by rfl) ⟨889331, by rfl⟩ : syracuseStep 1185775 = 1778663) B1778663
theorem B449632301 : Blo 1184409 449632301 := bstep (se 3 (by rfl) ⟨84306056, by rfl⟩ : syracuseStep 449632301 = 168612113) B168612113
theorem B18241631 : Blo 1184409 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B4003937 : Blo 1184409 4003937 := bstep (se 2 (by rfl) ⟨1501476, by rfl⟩ : syracuseStep 4003937 = 3002953) B3002953
theorem B1185947 : Blo 1184409 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B1185983 : Blo 1184409 1185983 := bstep (se 1 (by rfl) ⟨889487, by rfl⟩ : syracuseStep 1185983 = 1778975) B1778975
theorem B3373289 : Blo 1184409 3373289 := bstep (se 2 (by rfl) ⟨1264983, by rfl⟩ : syracuseStep 3373289 = 2529967) B2529967
theorem B2250985 : Blo 1184409 2250985 := bstep (se 2 (by rfl) ⟨844119, by rfl⟩ : syracuseStep 2250985 = 1688239) B1688239
theorem B2668841 : Blo 1184409 2668841 := bstep (se 2 (by rfl) ⟨1000815, by rfl⟩ : syracuseStep 2668841 = 2001631) B2001631
theorem B1186095 : Blo 1184409 1186095 := bstep (se 1 (by rfl) ⟨889571, by rfl⟩ : syracuseStep 1186095 = 1779143) B1779143
theorem B41613749 : Blo 1184409 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B1186331 : Blo 1184409 1186331 := bstep (se 1 (by rfl) ⟨889748, by rfl⟩ : syracuseStep 1186331 = 1779497) B1779497
theorem B1186335 : Blo 1184409 1186335 := bstep (se 1 (by rfl) ⟨889751, by rfl⟩ : syracuseStep 1186335 = 1779503) B1779503
theorem B3373903 : Blo 1184409 3373903 := bstep (se 1 (by rfl) ⟨2530427, by rfl⟩ : syracuseStep 3373903 = 5060855) B5060855
theorem B2669417 : Blo 1184409 2669417 := bstep (se 2 (by rfl) ⟨1001031, by rfl⟩ : syracuseStep 2669417 = 2002063) B2002063
theorem B45546461 : Blo 1184409 45546461 := bstep (se 3 (by rfl) ⟨8539961, by rfl⟩ : syracuseStep 45546461 = 17079923) B17079923
theorem B2137067 : Blo 1184409 2137067 := bstep (se 1 (by rfl) ⟨1602800, by rfl⟩ : syracuseStep 2137067 = 3205601) B3205601
theorem B1776761 : Blo 1184409 1776761 := bstep (se 2 (by rfl) ⟨666285, by rfl⟩ : syracuseStep 1776761 = 1332571) B1332571
theorem B1776863 : Blo 1184409 1776863 := bstep (se 1 (by rfl) ⟨1332647, by rfl⟩ : syracuseStep 1776863 = 2665295) B2665295
theorem B1776905 : Blo 1184409 1776905 := bstep (se 2 (by rfl) ⟨666339, by rfl⟩ : syracuseStep 1776905 = 1332679) B1332679
theorem B3202313 : Blo 1184409 3202313 := bstep (se 2 (by rfl) ⟨1200867, by rfl⟩ : syracuseStep 3202313 = 2401735) B2401735
theorem B1777007 : Blo 1184409 1777007 := bstep (se 1 (by rfl) ⟨1332755, by rfl⟩ : syracuseStep 1777007 = 2665511) B2665511
theorem B1777127 : Blo 1184409 1777127 := bstep (se 1 (by rfl) ⟨1332845, by rfl⟩ : syracuseStep 1777127 = 2665691) B2665691
theorem B1777259 : Blo 1184409 1777259 := bstep (se 1 (by rfl) ⟨1332944, by rfl⟩ : syracuseStep 1777259 = 2665889) B2665889
theorem B6848185 : Blo 1184409 6848185 := bstep (se 2 (by rfl) ⟨2568069, by rfl⟩ : syracuseStep 6848185 = 5136139) B5136139
theorem B1777385 : Blo 1184409 1777385 := bstep (se 2 (by rfl) ⟨666519, by rfl⟩ : syracuseStep 1777385 = 1333039) B1333039
theorem B9617129 : Blo 1184409 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B3997511 : Blo 1184409 3997511 := bstep (se 1 (by rfl) ⟨2998133, by rfl⟩ : syracuseStep 3997511 = 5996267) B5996267
theorem B1777529 : Blo 1184409 1777529 := bstep (se 2 (by rfl) ⟨666573, by rfl⟩ : syracuseStep 1777529 = 1333147) B1333147
theorem B1998715 : Blo 1184409 1998715 := bstep (se 1 (by rfl) ⟨1499036, by rfl⟩ : syracuseStep 1998715 = 2998073) B2998073
theorem B3997565 : Blo 1184409 3997565 := bstep (se 3 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 3997565 = 1499087) B1499087
theorem B1777631 : Blo 1184409 1777631 := bstep (se 1 (by rfl) ⟨1333223, by rfl⟩ : syracuseStep 1777631 = 2666447) B2666447
theorem B1999039 : Blo 1184409 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B1777871 : Blo 1184409 1777871 := bstep (se 1 (by rfl) ⟨1333403, by rfl⟩ : syracuseStep 1777871 = 2666807) B2666807
theorem B1777919 : Blo 1184409 1777919 := bstep (se 1 (by rfl) ⟨1333439, by rfl⟩ : syracuseStep 1777919 = 2666879) B2666879
theorem B3375407 : Blo 1184409 3375407 := bstep (se 1 (by rfl) ⟨2531555, by rfl⟩ : syracuseStep 3375407 = 5063111) B5063111
theorem B5693753 : Blo 1184409 5693753 := bstep (se 2 (by rfl) ⟨2135157, by rfl⟩ : syracuseStep 5693753 = 4270315) B4270315
theorem B2703743 : Blo 1184409 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B1999471 : Blo 1184409 1999471 := bstep (se 1 (by rfl) ⟨1499603, by rfl⟩ : syracuseStep 1999471 = 2999207) B2999207
theorem B1352399 : Blo 1184409 1352399 := bstep (se 1 (by rfl) ⟨1014299, by rfl⟩ : syracuseStep 1352399 = 2028599) B2028599
theorem B2999065 : Blo 1184409 2999065 := bstep (se 2 (by rfl) ⟨1124649, by rfl⟩ : syracuseStep 2999065 = 2249299) B2249299
theorem B1778735 : Blo 1184409 1778735 := bstep (se 1 (by rfl) ⟨1334051, by rfl⟩ : syracuseStep 1778735 = 2668103) B2668103
theorem B17089613 : Blo 1184409 17089613 := bstep (se 3 (by rfl) ⟨3204302, by rfl⟩ : syracuseStep 17089613 = 6408605) B6408605
theorem B4498537 : Blo 1184409 4498537 := bstep (se 2 (by rfl) ⟨1686951, by rfl⟩ : syracuseStep 4498537 = 3373903) B3373903
theorem B1778855 : Blo 1184409 1778855 := bstep (se 1 (by rfl) ⟨1334141, by rfl⟩ : syracuseStep 1778855 = 2668283) B2668283
theorem B2999531 : Blo 1184409 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B3999023 : Blo 1184409 3999023 := bstep (se 1 (by rfl) ⟨2999267, by rfl⟩ : syracuseStep 3999023 = 5998535) B5998535
theorem B2000207 : Blo 1184409 2000207 := bstep (se 1 (by rfl) ⟨1500155, by rfl⟩ : syracuseStep 2000207 = 3000311) B3000311
theorem B1779227 : Blo 1184409 1779227 := bstep (se 1 (by rfl) ⟨1334420, by rfl⟩ : syracuseStep 1779227 = 2668841) B2668841
theorem B1779611 : Blo 1184409 1779611 := bstep (se 1 (by rfl) ⟨1334708, by rfl⟩ : syracuseStep 1779611 = 2669417) B2669417
theorem B41084957 : Blo 1184409 41084957 := bstep (se 3 (by rfl) ⟨7703429, by rfl⟩ : syracuseStep 41084957 = 15406859) B15406859
theorem B32458907 : Blo 1184409 32458907 := bstep (se 1 (by rfl) ⟨24344180, by rfl⟩ : syracuseStep 32458907 = 48688361) B48688361
theorem B2001179 : Blo 1184409 2001179 := bstep (se 1 (by rfl) ⟨1500884, by rfl⟩ : syracuseStep 2001179 = 3001769) B3001769
theorem B6490409 : Blo 1184409 6490409 := bstep (se 2 (by rfl) ⟨2433903, by rfl⟩ : syracuseStep 6490409 = 4867807) B4867807
theorem B2664953 : Blo 1184409 2664953 := bstep (se 2 (by rfl) ⟨999357, by rfl⟩ : syracuseStep 2664953 = 1998715) B1998715
theorem B2665007 : Blo 1184409 2665007 := bstep (se 1 (by rfl) ⟨1998755, by rfl⟩ : syracuseStep 2665007 = 3997511) B3997511
theorem B2665043 : Blo 1184409 2665043 := bstep (se 1 (by rfl) ⟨1998782, by rfl⟩ : syracuseStep 2665043 = 3997565) B3997565
theorem B2001503 : Blo 1184409 2001503 := bstep (se 1 (by rfl) ⟨1501127, by rfl⟩ : syracuseStep 2001503 = 3002255) B3002255
theorem B13511285 : Blo 1184409 13511285 := bstep (se 5 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 13511285 = 1266683) B1266683
theorem B2665223 : Blo 1184409 2665223 := bstep (se 1 (by rfl) ⟨1998917, by rfl⟩ : syracuseStep 2665223 = 3997835) B3997835
theorem B2665439 : Blo 1184409 2665439 := bstep (se 1 (by rfl) ⟨1999079, by rfl⟩ : syracuseStep 2665439 = 3998159) B3998159
theorem B3001313 : Blo 1184409 3001313 := bstep (se 2 (by rfl) ⟨1125492, by rfl⟩ : syracuseStep 3001313 = 2250985) B2250985
theorem B2665655 : Blo 1184409 2665655 := bstep (se 1 (by rfl) ⟨1999241, by rfl⟩ : syracuseStep 2665655 = 3998483) B3998483
theorem B5999831 : Blo 1184409 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B4500755 : Blo 1184409 4500755 := bstep (se 1 (by rfl) ⟨3375566, by rfl⟩ : syracuseStep 4500755 = 6751133) B6751133
theorem B8539501 : Blo 1184409 8539501 := bstep (se 3 (by rfl) ⟨1601156, by rfl⟩ : syracuseStep 8539501 = 3202313) B3202313
theorem B5999993 : Blo 1184409 5999993 := bstep (se 2 (by rfl) ⟨2249997, by rfl⟩ : syracuseStep 5999993 = 4499995) B4499995
theorem B2846107 : Blo 1184409 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B7589335 : Blo 1184409 7589335 := bstep (se 1 (by rfl) ⟨5692001, by rfl⟩ : syracuseStep 7589335 = 11384003) B11384003
theorem B2666231 : Blo 1184409 2666231 := bstep (se 1 (by rfl) ⟨1999673, by rfl⟩ : syracuseStep 2666231 = 3999347) B3999347
theorem B207867653 : Blo 1184409 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B2666303 : Blo 1184409 2666303 := bstep (se 1 (by rfl) ⟨1999727, by rfl⟩ : syracuseStep 2666303 = 3999455) B3999455
theorem B2666411 : Blo 1184409 2666411 := bstep (se 1 (by rfl) ⟨1999808, by rfl⟩ : syracuseStep 2666411 = 3999617) B3999617
theorem B17076233 : Blo 1184409 17076233 := bstep (se 2 (by rfl) ⟨6403587, by rfl⟩ : syracuseStep 17076233 = 12807175) B12807175
theorem B12161087 : Blo 1184409 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B46198907 : Blo 1184409 46198907 := bstep (se 1 (by rfl) ⟨34649180, by rfl⟩ : syracuseStep 46198907 = 69298361) B69298361
theorem B2248859 : Blo 1184409 2248859 := bstep (se 1 (by rfl) ⟨1686644, by rfl⟩ : syracuseStep 2248859 = 3373289) B3373289
theorem B4501757 : Blo 1184409 4501757 := bstep (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) B1688159
theorem B2666771 : Blo 1184409 2666771 := bstep (se 1 (by rfl) ⟨2000078, by rfl⟩ : syracuseStep 2666771 = 4000157) B4000157
theorem B27742499 : Blo 1184409 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B2666951 : Blo 1184409 2666951 := bstep (se 1 (by rfl) ⟨2000213, by rfl⟩ : syracuseStep 2666951 = 4000427) B4000427
theorem B30364307 : Blo 1184409 30364307 := bstep (se 1 (by rfl) ⟨22773230, by rfl⟩ : syracuseStep 30364307 = 45546461) B45546461
theorem B1184507 : Blo 1184409 1184507 := bstep (se 1 (by rfl) ⟨888380, by rfl⟩ : syracuseStep 1184507 = 1776761) B1776761
theorem B2667311 : Blo 1184409 2667311 := bstep (se 1 (by rfl) ⟨2000483, by rfl⟩ : syracuseStep 2667311 = 4000967) B4000967
theorem B1184575 : Blo 1184409 1184575 := bstep (se 1 (by rfl) ⟨888431, by rfl⟩ : syracuseStep 1184575 = 1776863) B1776863
theorem B1184603 : Blo 1184409 1184603 := bstep (se 1 (by rfl) ⟨888452, by rfl⟩ : syracuseStep 1184603 = 1776905) B1776905
theorem B2667401 : Blo 1184409 2667401 := bstep (se 2 (by rfl) ⟨1000275, by rfl⟩ : syracuseStep 2667401 = 2000551) B2000551
theorem B1184671 : Blo 1184409 1184671 := bstep (se 1 (by rfl) ⟨888503, by rfl⟩ : syracuseStep 1184671 = 1777007) B1777007
theorem B9130913 : Blo 1184409 9130913 := bstep (se 2 (by rfl) ⟨3424092, by rfl⟩ : syracuseStep 9130913 = 6848185) B6848185
theorem B1184751 : Blo 1184409 1184751 := bstep (se 1 (by rfl) ⟨888563, by rfl⟩ : syracuseStep 1184751 = 1777127) B1777127
theorem B4273211 : Blo 1184409 4273211 := bstep (se 1 (by rfl) ⟨3204908, by rfl⟩ : syracuseStep 4273211 = 6409817) B6409817
theorem B1184839 : Blo 1184409 1184839 := bstep (se 1 (by rfl) ⟨888629, by rfl⟩ : syracuseStep 1184839 = 1777259) B1777259
theorem B1184923 : Blo 1184409 1184923 := bstep (se 1 (by rfl) ⟨888692, by rfl⟩ : syracuseStep 1184923 = 1777385) B1777385
theorem B6411419 : Blo 1184409 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B10958075 : Blo 1184409 10958075 := bstep (se 1 (by rfl) ⟨8218556, by rfl⟩ : syracuseStep 10958075 = 16437113) B16437113
theorem B1185019 : Blo 1184409 1185019 := bstep (se 1 (by rfl) ⟨888764, by rfl⟩ : syracuseStep 1185019 = 1777529) B1777529
theorem B1185087 : Blo 1184409 1185087 := bstep (se 1 (by rfl) ⟨888815, by rfl⟩ : syracuseStep 1185087 = 1777631) B1777631
theorem B8107451 : Blo 1184409 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B1199019469 : Blo 1184409 1199019469 := bstep (se 3 (by rfl) ⟨224816150, by rfl⟩ : syracuseStep 1199019469 = 449632301) B449632301
theorem B1185255 : Blo 1184409 1185255 := bstep (se 1 (by rfl) ⟨888941, by rfl⟩ : syracuseStep 1185255 = 1777883) B1777883
theorem B1185263 : Blo 1184409 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B4273661 : Blo 1184409 4273661 := bstep (se 3 (by rfl) ⟨801311, by rfl⟩ : syracuseStep 4273661 = 1602623) B1602623
theorem B1185371 : Blo 1184409 1185371 := bstep (se 1 (by rfl) ⟨889028, by rfl⟩ : syracuseStep 1185371 = 1778057) B1778057
theorem B2668175 : Blo 1184409 2668175 := bstep (se 1 (by rfl) ⟨2001131, by rfl⟩ : syracuseStep 2668175 = 4002263) B4002263
theorem B1185435 : Blo 1184409 1185435 := bstep (se 1 (by rfl) ⟨889076, by rfl⟩ : syracuseStep 1185435 = 1778153) B1778153
theorem B2668265 : Blo 1184409 2668265 := bstep (se 2 (by rfl) ⟨1000599, by rfl⟩ : syracuseStep 2668265 = 2001199) B2001199
theorem B1185519 : Blo 1184409 1185519 := bstep (se 1 (by rfl) ⟨889139, by rfl⟩ : syracuseStep 1185519 = 1778279) B1778279
theorem B1185607 : Blo 1184409 1185607 := bstep (se 1 (by rfl) ⟨889205, by rfl⟩ : syracuseStep 1185607 = 1778411) B1778411
theorem B4003667 : Blo 1184409 4003667 := bstep (se 1 (by rfl) ⟨3002750, by rfl⟩ : syracuseStep 4003667 = 6005501) B6005501
theorem B1185627 : Blo 1184409 1185627 := bstep (se 1 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 1185627 = 1778441) B1778441
theorem B1185695 : Blo 1184409 1185695 := bstep (se 1 (by rfl) ⟨889271, by rfl⟩ : syracuseStep 1185695 = 1778543) B1778543
theorem B4560887 : Blo 1184409 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B6002747 : Blo 1184409 6002747 := bstep (se 1 (by rfl) ⟨4502060, by rfl⟩ : syracuseStep 6002747 = 9004121) B9004121
theorem B1185863 : Blo 1184409 1185863 := bstep (se 1 (by rfl) ⟨889397, by rfl⟩ : syracuseStep 1185863 = 1778795) B1778795
theorem B5699767 : Blo 1184409 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B5060839 : Blo 1184409 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B1186023 : Blo 1184409 1186023 := bstep (se 1 (by rfl) ⟨889517, by rfl⟩ : syracuseStep 1186023 = 1779035) B1779035
theorem B30390551 : Blo 1184409 30390551 := bstep (se 1 (by rfl) ⟨22792913, by rfl⟩ : syracuseStep 30390551 = 45585827) B45585827
theorem B2251091 : Blo 1184409 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B1186207 : Blo 1184409 1186207 := bstep (se 1 (by rfl) ⟨889655, by rfl⟩ : syracuseStep 1186207 = 1779311) B1779311
theorem B2849231 : Blo 1184409 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B1186255 : Blo 1184409 1186255 := bstep (se 1 (by rfl) ⟨889691, by rfl⟩ : syracuseStep 1186255 = 1779383) B1779383
theorem B1186279 : Blo 1184409 1186279 := bstep (se 1 (by rfl) ⟨889709, by rfl⟩ : syracuseStep 1186279 = 1779419) B1779419
theorem B2669147 : Blo 1184409 2669147 := bstep (se 1 (by rfl) ⟨2001860, by rfl⟩ : syracuseStep 2669147 = 4003721) B4003721
theorem B1186395 : Blo 1184409 1186395 := bstep (se 1 (by rfl) ⟨889796, by rfl⟩ : syracuseStep 1186395 = 1779593) B1779593
theorem B9615995 : Blo 1184409 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B2669291 : Blo 1184409 2669291 := bstep (se 1 (by rfl) ⟨2001968, by rfl⟩ : syracuseStep 2669291 = 4003937) B4003937
theorem B10132235 : Blo 1184409 10132235 := bstep (se 1 (by rfl) ⟨7599176, by rfl⟩ : syracuseStep 10132235 = 15198353) B15198353
theorem B2251577 : Blo 1184409 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B2251631 : Blo 1184409 2251631 := bstep (se 1 (by rfl) ⟨1688723, by rfl⟩ : syracuseStep 2251631 = 3377447) B3377447
theorem B6413275 : Blo 1184409 6413275 := bstep (se 1 (by rfl) ⟨4809956, by rfl⟩ : syracuseStep 6413275 = 9619913) B9619913
theorem B1334479 : Blo 1184409 1334479 := bstep (se 1 (by rfl) ⟨1000859, by rfl⟩ : syracuseStep 1334479 = 2001719) B2001719
theorem B1424711 : Blo 1184409 1424711 := bstep (se 1 (by rfl) ⟨1068533, by rfl⟩ : syracuseStep 1424711 = 2137067) B2137067
theorem B4054379 : Blo 1184409 4054379 := bstep (se 1 (by rfl) ⟨3040784, by rfl⟩ : syracuseStep 4054379 = 6081569) B6081569
theorem B6004367 : Blo 1184409 6004367 := bstep (se 1 (by rfl) ⟨4503275, by rfl⟩ : syracuseStep 6004367 = 9006551) B9006551
theorem B1777319 : Blo 1184409 1777319 := bstep (se 1 (by rfl) ⟨1332989, by rfl⟩ : syracuseStep 1777319 = 2665979) B2665979
theorem B9002663 : Blo 1184409 9002663 := bstep (se 1 (by rfl) ⟨6751997, by rfl⟩ : syracuseStep 9002663 = 13503995) B13503995
theorem B38002391 : Blo 1184409 38002391 := bstep (se 1 (by rfl) ⟨28501793, by rfl⟩ : syracuseStep 38002391 = 57003587) B57003587
theorem B1777439 : Blo 1184409 1777439 := bstep (se 1 (by rfl) ⟨1333079, by rfl⟩ : syracuseStep 1777439 = 2666159) B2666159
theorem B22789997 : Blo 1184409 22789997 := bstep (se 3 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 22789997 = 8546249) B8546249
theorem B4497353 : Blo 1184409 4497353 := bstep (se 2 (by rfl) ⟨1686507, by rfl⟩ : syracuseStep 4497353 = 3373015) B3373015
theorem B1499239 : Blo 1184409 1499239 := bstep (se 1 (by rfl) ⟨1124429, by rfl⟩ : syracuseStep 1499239 = 2248859) B2248859
theorem B1777847 : Blo 1184409 1777847 := bstep (se 1 (by rfl) ⟨1333385, by rfl⟩ : syracuseStep 1777847 = 2666771) B2666771
theorem B1802495 : Blo 1184409 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B1777967 : Blo 1184409 1777967 := bstep (se 1 (by rfl) ⟨1333475, by rfl⟩ : syracuseStep 1777967 = 2666951) B2666951
theorem B20242871 : Blo 1184409 20242871 := bstep (se 1 (by rfl) ⟨15182153, by rfl⟩ : syracuseStep 20242871 = 30364307) B30364307
theorem B1778207 : Blo 1184409 1778207 := bstep (se 1 (by rfl) ⟨1333655, by rfl⟩ : syracuseStep 1778207 = 2667311) B2667311
theorem B1778267 : Blo 1184409 1778267 := bstep (se 1 (by rfl) ⟨1333700, by rfl⟩ : syracuseStep 1778267 = 2667401) B2667401
theorem B6087275 : Blo 1184409 6087275 := bstep (se 1 (by rfl) ⟨4565456, by rfl⟩ : syracuseStep 6087275 = 9130913) B9130913
theorem B1999687 : Blo 1184409 1999687 := bstep (se 1 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 1999687 = 2999531) B2999531
theorem B3998753 : Blo 1184409 3998753 := bstep (se 2 (by rfl) ⟨1499532, by rfl⟩ : syracuseStep 3998753 = 2999065) B2999065
theorem B1778783 : Blo 1184409 1778783 := bstep (se 1 (by rfl) ⟨1334087, by rfl⟩ : syracuseStep 1778783 = 2668175) B2668175
theorem B43246709 : Blo 1184409 43246709 := bstep (se 5 (by rfl) ⟨2027189, by rfl⟩ : syracuseStep 43246709 = 4054379) B4054379
theorem B1778843 : Blo 1184409 1778843 := bstep (se 1 (by rfl) ⟨1334132, by rfl⟩ : syracuseStep 1778843 = 2668265) B2668265
theorem B3040591 : Blo 1184409 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B5998049 : Blo 1184409 5998049 := bstep (se 2 (by rfl) ⟨2249268, by rfl⟩ : syracuseStep 5998049 = 4498537) B4498537
theorem B20260367 : Blo 1184409 20260367 := bstep (se 1 (by rfl) ⟨15195275, by rfl⟩ : syracuseStep 20260367 = 30390551) B30390551
theorem B1779305 : Blo 1184409 1779305 := bstep (se 2 (by rfl) ⟨667239, by rfl⟩ : syracuseStep 1779305 = 1334479) B1334479
theorem B1779431 : Blo 1184409 1779431 := bstep (se 1 (by rfl) ⟨1334573, by rfl⟩ : syracuseStep 1779431 = 2669147) B2669147
theorem B1779527 : Blo 1184409 1779527 := bstep (se 1 (by rfl) ⟨1334645, by rfl⟩ : syracuseStep 1779527 = 2669291) B2669291
theorem B1501087 : Blo 1184409 1501087 := bstep (se 1 (by rfl) ⟨1125815, by rfl⟩ : syracuseStep 1501087 = 2251631) B2251631
theorem B10119113 : Blo 1184409 10119113 := bstep (se 2 (by rfl) ⟨3794667, by rfl⟩ : syracuseStep 10119113 = 7589335) B7589335
theorem B2000875 : Blo 1184409 2000875 := bstep (se 1 (by rfl) ⟨1500656, by rfl⟩ : syracuseStep 2000875 = 3001313) B3001313
theorem B3999887 : Blo 1184409 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B3000503 : Blo 1184409 3000503 := bstep (se 1 (by rfl) ⟨2250377, by rfl⟩ : syracuseStep 3000503 = 4500755) B4500755
theorem B3999995 : Blo 1184409 3999995 := bstep (se 1 (by rfl) ⟨2999996, by rfl⟩ : syracuseStep 3999995 = 5999993) B5999993
theorem B34204133 : Blo 1184409 34204133 := bstep (se 4 (by rfl) ⟨3206637, by rfl⟩ : syracuseStep 34204133 = 6413275) B6413275
theorem B138578435 : Blo 1184409 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B3001171 : Blo 1184409 3001171 := bstep (se 1 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 3001171 = 4501757) B4501757
theorem B3795835 : Blo 1184409 3795835 := bstep (se 1 (by rfl) ⟨2846876, by rfl⟩ : syracuseStep 3795835 = 5693753) B5693753
theorem B2665385 : Blo 1184409 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B2665961 : Blo 1184409 2665961 := bstep (se 2 (by rfl) ⟨999735, by rfl⟩ : syracuseStep 2665961 = 1999471) B1999471
theorem B2666015 : Blo 1184409 2666015 := bstep (se 1 (by rfl) ⟨1999511, by rfl⟩ : syracuseStep 2666015 = 3999023) B3999023
theorem B27389971 : Blo 1184409 27389971 := bstep (se 1 (by rfl) ⟨20542478, by rfl⟩ : syracuseStep 27389971 = 41084957) B41084957
theorem B4001831 : Blo 1184409 4001831 := bstep (se 1 (by rfl) ⟨3001373, by rfl⟩ : syracuseStep 4001831 = 6002747) B6002747
theorem B21639271 : Blo 1184409 21639271 := bstep (se 1 (by rfl) ⟨16229453, by rfl⟩ : syracuseStep 21639271 = 32458907) B32458907
theorem B9007523 : Blo 1184409 9007523 := bstep (se 1 (by rfl) ⟨6755642, by rfl⟩ : syracuseStep 9007523 = 13511285) B13511285
theorem B6410663 : Blo 1184409 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B6754823 : Blo 1184409 6754823 := bstep (se 1 (by rfl) ⟨5066117, by rfl⟩ : syracuseStep 6754823 = 10132235) B10132235
theorem B4002911 : Blo 1184409 4002911 := bstep (se 1 (by rfl) ⟨3002183, by rfl⟩ : syracuseStep 4002911 = 6004367) B6004367
theorem B1184879 : Blo 1184409 1184879 := bstep (se 1 (by rfl) ⟨888659, by rfl⟩ : syracuseStep 1184879 = 1777319) B1777319
theorem B6001775 : Blo 1184409 6001775 := bstep (se 1 (by rfl) ⟨4501331, by rfl⟩ : syracuseStep 6001775 = 9002663) B9002663
theorem B25334927 : Blo 1184409 25334927 := bstep (se 1 (by rfl) ⟨19001195, by rfl⟩ : syracuseStep 25334927 = 38002391) B38002391
theorem B1184959 : Blo 1184409 1184959 := bstep (se 1 (by rfl) ⟨888719, by rfl⟩ : syracuseStep 1184959 = 1777439) B1777439
theorem B15193331 : Blo 1184409 15193331 := bstep (se 1 (by rfl) ⟨11394998, by rfl⟩ : syracuseStep 15193331 = 22789997) B22789997
theorem B11384155 : Blo 1184409 11384155 := bstep (se 1 (by rfl) ⟨8538116, by rfl⟩ : syracuseStep 11384155 = 17076233) B17076233
theorem B8107391 : Blo 1184409 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B30799271 : Blo 1184409 30799271 := bstep (se 1 (by rfl) ⟨23099453, by rfl⟩ : syracuseStep 30799271 = 46198907) B46198907
theorem B1185247 : Blo 1184409 1185247 := bstep (se 1 (by rfl) ⟨888935, by rfl⟩ : syracuseStep 1185247 = 1777871) B1777871
theorem B1185279 : Blo 1184409 1185279 := bstep (se 1 (by rfl) ⟨888959, by rfl⟩ : syracuseStep 1185279 = 1777919) B1777919
theorem B18494999 : Blo 1184409 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B2250271 : Blo 1184409 2250271 := bstep (se 1 (by rfl) ⟨1687703, by rfl⟩ : syracuseStep 2250271 = 3375407) B3375407
theorem B7599689 : Blo 1184409 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B6747785 : Blo 1184409 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B1185823 : Blo 1184409 1185823 := bstep (se 1 (by rfl) ⟨889367, by rfl⟩ : syracuseStep 1185823 = 1778735) B1778735
theorem B2848807 : Blo 1184409 2848807 := bstep (se 1 (by rfl) ⟨2136605, by rfl⟩ : syracuseStep 2848807 = 4273211) B4273211
theorem B11393075 : Blo 1184409 11393075 := bstep (se 1 (by rfl) ⟨8544806, by rfl⟩ : syracuseStep 11393075 = 17089613) B17089613
theorem B4274279 : Blo 1184409 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B17307757 : Blo 1184409 17307757 := bstep (se 3 (by rfl) ⟨3245204, by rfl⟩ : syracuseStep 17307757 = 6490409) B6490409
theorem B1185903 : Blo 1184409 1185903 := bstep (se 1 (by rfl) ⟨889427, by rfl⟩ : syracuseStep 1185903 = 1778855) B1778855
theorem B7305383 : Blo 1184409 7305383 := bstep (se 1 (by rfl) ⟨5479037, by rfl⟩ : syracuseStep 7305383 = 10958075) B10958075
theorem B3799229 : Blo 1184409 3799229 := bstep (se 3 (by rfl) ⟨712355, by rfl⟩ : syracuseStep 3799229 = 1424711) B1424711
theorem B6002909 : Blo 1184409 6002909 := bstep (se 3 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 6002909 = 2251091) B2251091
theorem B1333471 : Blo 1184409 1333471 := bstep (se 1 (by rfl) ⟨1000103, by rfl⟩ : syracuseStep 1333471 = 2000207) B2000207
theorem B5404967 : Blo 1184409 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B2849107 : Blo 1184409 2849107 := bstep (se 1 (by rfl) ⟨2136830, by rfl⟩ : syracuseStep 2849107 = 4273661) B4273661
theorem B1186151 : Blo 1184409 1186151 := bstep (se 1 (by rfl) ⟨889613, by rfl⟩ : syracuseStep 1186151 = 1779227) B1779227
theorem B2669111 : Blo 1184409 2669111 := bstep (se 1 (by rfl) ⟨2001833, by rfl⟩ : syracuseStep 2669111 = 4003667) B4003667
theorem B1186407 : Blo 1184409 1186407 := bstep (se 1 (by rfl) ⟨889805, by rfl⟩ : syracuseStep 1186407 = 1779611) B1779611
theorem B1334119 : Blo 1184409 1334119 := bstep (se 1 (by rfl) ⟨1000589, by rfl⟩ : syracuseStep 1334119 = 2001179) B2001179
theorem B1899487 : Blo 1184409 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B1776635 : Blo 1184409 1776635 := bstep (se 1 (by rfl) ⟨1332476, by rfl⟩ : syracuseStep 1776635 = 2664953) B2664953
theorem B1776671 : Blo 1184409 1776671 := bstep (se 1 (by rfl) ⟨1332503, by rfl⟩ : syracuseStep 1776671 = 2665007) B2665007
theorem B1776695 : Blo 1184409 1776695 := bstep (se 1 (by rfl) ⟨1332521, by rfl⟩ : syracuseStep 1776695 = 2665043) B2665043
theorem B1334335 : Blo 1184409 1334335 := bstep (se 1 (by rfl) ⟨1000751, by rfl⟩ : syracuseStep 1334335 = 2001503) B2001503
theorem B11386001 : Blo 1184409 11386001 := bstep (se 2 (by rfl) ⟨4269750, by rfl⟩ : syracuseStep 11386001 = 8539501) B8539501
theorem B1776815 : Blo 1184409 1776815 := bstep (se 1 (by rfl) ⟨1332611, by rfl⟩ : syracuseStep 1776815 = 2665223) B2665223
theorem B1598692625 : Blo 1184409 1598692625 := bstep (se 2 (by rfl) ⟨599509734, by rfl⟩ : syracuseStep 1598692625 = 1199019469) B1199019469
theorem B1776959 : Blo 1184409 1776959 := bstep (se 1 (by rfl) ⟨1332719, by rfl⟩ : syracuseStep 1776959 = 2665439) B2665439
theorem B1777103 : Blo 1184409 1777103 := bstep (se 1 (by rfl) ⟨1332827, by rfl⟩ : syracuseStep 1777103 = 2665655) B2665655
theorem B15179237 : Blo 1184409 15179237 := bstep (se 4 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 15179237 = 2846107) B2846107
theorem B6004205 : Blo 1184409 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B14425589 : Blo 1184409 14425589 := bstep (se 5 (by rfl) ⟨676199, by rfl⟩ : syracuseStep 14425589 = 1352399) B1352399
theorem B1777487 : Blo 1184409 1777487 := bstep (se 1 (by rfl) ⟨1333115, by rfl⟩ : syracuseStep 1777487 = 2666231) B2666231
theorem B1777535 : Blo 1184409 1777535 := bstep (se 1 (by rfl) ⟨1333151, by rfl⟩ : syracuseStep 1777535 = 2666303) B2666303
theorem B1777607 : Blo 1184409 1777607 := bstep (se 1 (by rfl) ⟨1333205, by rfl⟩ : syracuseStep 1777607 = 2666411) B2666411
theorem B2998235 : Blo 1184409 2998235 := bstep (se 1 (by rfl) ⟨2248676, by rfl⟩ : syracuseStep 2998235 = 4497353) B4497353
theorem B146079845 : Blo 1184409 146079845 := bstep (se 4 (by rfl) ⟨13694985, by rfl⟩ : syracuseStep 146079845 = 27389971) B27389971
theorem B1998985 : Blo 1184409 1998985 := bstep (se 2 (by rfl) ⟨749619, by rfl⟩ : syracuseStep 1998985 = 1499239) B1499239
theorem B28852361 : Blo 1184409 28852361 := bstep (se 2 (by rfl) ⟨10819635, by rfl⟩ : syracuseStep 28852361 = 21639271) B21639271
theorem B23077009 : Blo 1184409 23077009 := bstep (se 2 (by rfl) ⟨8653878, by rfl⟩ : syracuseStep 23077009 = 17307757) B17307757
theorem B6005015 : Blo 1184409 6005015 := bstep (se 1 (by rfl) ⟨4503761, by rfl⟩ : syracuseStep 6005015 = 9007523) B9007523
theorem B1777961 : Blo 1184409 1777961 := bstep (se 2 (by rfl) ⟨666735, by rfl⟩ : syracuseStep 1777961 = 1333471) B1333471
theorem B3998699 : Blo 1184409 3998699 := bstep (se 1 (by rfl) ⟨2999024, by rfl⟩ : syracuseStep 3998699 = 5998049) B5998049
theorem B12329999 : Blo 1184409 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B4498523 : Blo 1184409 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B1778825 : Blo 1184409 1778825 := bstep (se 2 (by rfl) ⟨667059, by rfl⟩ : syracuseStep 1778825 = 1334119) B1334119
theorem B2532649 : Blo 1184409 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B7595383 : Blo 1184409 7595383 := bstep (se 1 (by rfl) ⟨5696537, by rfl⟩ : syracuseStep 7595383 = 11393075) B11393075
theorem B1779113 : Blo 1184409 1779113 := bstep (se 2 (by rfl) ⟨667167, by rfl⟩ : syracuseStep 1779113 = 1334335) B1334335
theorem B2000335 : Blo 1184409 2000335 := bstep (se 1 (by rfl) ⟨1500251, by rfl⟩ : syracuseStep 2000335 = 3000503) B3000503
theorem B1779407 : Blo 1184409 1779407 := bstep (se 1 (by rfl) ⟨1334555, by rfl⟩ : syracuseStep 1779407 = 2669111) B2669111
theorem B3000361 : Blo 1184409 3000361 := bstep (se 2 (by rfl) ⟨1125135, by rfl⟩ : syracuseStep 3000361 = 2250271) B2250271
theorem B10119491 : Blo 1184409 10119491 := bstep (se 1 (by rfl) ⟨7589618, by rfl⟩ : syracuseStep 10119491 = 15179237) B15179237
theorem B2001449 : Blo 1184409 2001449 := bstep (se 2 (by rfl) ⟨750543, by rfl⟩ : syracuseStep 2001449 = 1501087) B1501087
theorem B13495247 : Blo 1184409 13495247 := bstep (se 1 (by rfl) ⟨10121435, by rfl⟩ : syracuseStep 13495247 = 20242871) B20242871
theorem B4058183 : Blo 1184409 4058183 := bstep (se 1 (by rfl) ⟨3043637, by rfl⟩ : syracuseStep 4058183 = 6087275) B6087275
theorem B2665835 : Blo 1184409 2665835 := bstep (se 1 (by rfl) ⟨1999376, by rfl⟩ : syracuseStep 2665835 = 3998753) B3998753
theorem B4001183 : Blo 1184409 4001183 := bstep (se 1 (by rfl) ⟨3000887, by rfl⟩ : syracuseStep 4001183 = 6001775) B6001775
theorem B28831139 : Blo 1184409 28831139 := bstep (se 1 (by rfl) ⟨21623354, by rfl⟩ : syracuseStep 28831139 = 43246709) B43246709
theorem B10128887 : Blo 1184409 10128887 := bstep (se 1 (by rfl) ⟨7596665, by rfl⟩ : syracuseStep 10128887 = 15193331) B15193331
theorem B20532847 : Blo 1184409 20532847 := bstep (se 1 (by rfl) ⟨15399635, by rfl⟩ : syracuseStep 20532847 = 30799271) B30799271
theorem B5066459 : Blo 1184409 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B2666249 : Blo 1184409 2666249 := bstep (se 2 (by rfl) ⟨999843, by rfl⟩ : syracuseStep 2666249 = 1999687) B1999687
theorem B4001561 : Blo 1184409 4001561 := bstep (se 2 (by rfl) ⟨1500585, by rfl⟩ : syracuseStep 4001561 = 3001171) B3001171
theorem B6746075 : Blo 1184409 6746075 := bstep (se 1 (by rfl) ⟨5059556, by rfl⟩ : syracuseStep 6746075 = 10119113) B10119113
theorem B2666591 : Blo 1184409 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B4870255 : Blo 1184409 4870255 := bstep (se 1 (by rfl) ⟨3652691, by rfl⟩ : syracuseStep 4870255 = 7305383) B7305383
theorem B4001939 : Blo 1184409 4001939 := bstep (se 1 (by rfl) ⟨3001454, by rfl⟩ : syracuseStep 4001939 = 6002909) B6002909
theorem B2666663 : Blo 1184409 2666663 := bstep (se 1 (by rfl) ⟨1999997, by rfl⟩ : syracuseStep 2666663 = 3999995) B3999995
theorem B22802755 : Blo 1184409 22802755 := bstep (se 1 (by rfl) ⟨17102066, by rfl⟩ : syracuseStep 22802755 = 34204133) B34204133
theorem B92385623 : Blo 1184409 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B1184423 : Blo 1184409 1184423 := bstep (se 1 (by rfl) ⟨888317, by rfl⟩ : syracuseStep 1184423 = 1776635) B1776635
theorem B1184447 : Blo 1184409 1184447 := bstep (se 1 (by rfl) ⟨888335, by rfl⟩ : syracuseStep 1184447 = 1776671) B1776671
theorem B1184463 : Blo 1184409 1184463 := bstep (se 1 (by rfl) ⟨888347, by rfl⟩ : syracuseStep 1184463 = 1776695) B1776695
theorem B7590667 : Blo 1184409 7590667 := bstep (se 1 (by rfl) ⟨5693000, by rfl⟩ : syracuseStep 7590667 = 11386001) B11386001
theorem B1184543 : Blo 1184409 1184543 := bstep (se 1 (by rfl) ⟨888407, by rfl⟩ : syracuseStep 1184543 = 1776815) B1776815
theorem B1184639 : Blo 1184409 1184639 := bstep (se 1 (by rfl) ⟨888479, by rfl⟩ : syracuseStep 1184639 = 1776959) B1776959
theorem B1184735 : Blo 1184409 1184735 := bstep (se 1 (by rfl) ⟨888551, by rfl⟩ : syracuseStep 1184735 = 1777103) B1777103
theorem B4002803 : Blo 1184409 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B1184991 : Blo 1184409 1184991 := bstep (se 1 (by rfl) ⟨888743, by rfl⟩ : syracuseStep 1184991 = 1777487) B1777487
theorem B1185023 : Blo 1184409 1185023 := bstep (se 1 (by rfl) ⟨888767, by rfl⟩ : syracuseStep 1185023 = 1777535) B1777535
theorem B1185071 : Blo 1184409 1185071 := bstep (se 1 (by rfl) ⟨888803, by rfl⟩ : syracuseStep 1185071 = 1777607) B1777607
theorem B2667833 : Blo 1184409 2667833 := bstep (se 2 (by rfl) ⟨1000437, by rfl⟩ : syracuseStep 2667833 = 2000875) B2000875
theorem B2667887 : Blo 1184409 2667887 := bstep (se 1 (by rfl) ⟨2000915, by rfl⟩ : syracuseStep 2667887 = 4001831) B4001831
theorem B3798409 : Blo 1184409 3798409 := bstep (se 2 (by rfl) ⟨1424403, by rfl⟩ : syracuseStep 3798409 = 2848807) B2848807
theorem B1185231 : Blo 1184409 1185231 := bstep (se 1 (by rfl) ⟨888923, by rfl⟩ : syracuseStep 1185231 = 1777847) B1777847
theorem B1201663 : Blo 1184409 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B1185311 : Blo 1184409 1185311 := bstep (se 1 (by rfl) ⟨888983, by rfl⟩ : syracuseStep 1185311 = 1777967) B1777967
theorem B4273775 : Blo 1184409 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B4503215 : Blo 1184409 4503215 := bstep (se 1 (by rfl) ⟨3377411, by rfl⟩ : syracuseStep 4503215 = 6754823) B6754823
theorem B1185471 : Blo 1184409 1185471 := bstep (se 1 (by rfl) ⟨889103, by rfl⟩ : syracuseStep 1185471 = 1778207) B1778207
theorem B1185511 : Blo 1184409 1185511 := bstep (se 1 (by rfl) ⟨889133, by rfl⟩ : syracuseStep 1185511 = 1778267) B1778267
theorem B3798809 : Blo 1184409 3798809 := bstep (se 2 (by rfl) ⟨1424553, by rfl⟩ : syracuseStep 3798809 = 2849107) B2849107
theorem B10131277 : Blo 1184409 10131277 := bstep (se 3 (by rfl) ⟨1899614, by rfl⟩ : syracuseStep 10131277 = 3799229) B3799229
theorem B1185855 : Blo 1184409 1185855 := bstep (se 1 (by rfl) ⟨889391, by rfl⟩ : syracuseStep 1185855 = 1778783) B1778783
theorem B2668607 : Blo 1184409 2668607 := bstep (se 1 (by rfl) ⟨2001455, by rfl⟩ : syracuseStep 2668607 = 4002911) B4002911
theorem B16889951 : Blo 1184409 16889951 := bstep (se 1 (by rfl) ⟨12667463, by rfl⟩ : syracuseStep 16889951 = 25334927) B25334927
theorem B1185895 : Blo 1184409 1185895 := bstep (se 1 (by rfl) ⟨889421, by rfl⟩ : syracuseStep 1185895 = 1778843) B1778843
theorem B5404927 : Blo 1184409 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B13506911 : Blo 1184409 13506911 := bstep (se 1 (by rfl) ⟨10130183, by rfl⟩ : syracuseStep 13506911 = 20260367) B20260367
theorem B1186203 : Blo 1184409 1186203 := bstep (se 1 (by rfl) ⟨889652, by rfl⟩ : syracuseStep 1186203 = 1779305) B1779305
theorem B1186287 : Blo 1184409 1186287 := bstep (se 1 (by rfl) ⟨889715, by rfl⟩ : syracuseStep 1186287 = 1779431) B1779431
theorem B5061113 : Blo 1184409 5061113 := bstep (se 2 (by rfl) ⟨1897917, by rfl⟩ : syracuseStep 5061113 = 3795835) B3795835
theorem B1186351 : Blo 1184409 1186351 := bstep (se 1 (by rfl) ⟨889763, by rfl⟩ : syracuseStep 1186351 = 1779527) B1779527
theorem B2849519 : Blo 1184409 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B3603311 : Blo 1184409 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B4054121 : Blo 1184409 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B15178873 : Blo 1184409 15178873 := bstep (se 2 (by rfl) ⟨5692077, by rfl⟩ : syracuseStep 15178873 = 11384155) B11384155
theorem B1776923 : Blo 1184409 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B1065795083 : Blo 1184409 1065795083 := bstep (se 1 (by rfl) ⟨799346312, by rfl⟩ : syracuseStep 1065795083 = 1598692625) B1598692625
theorem B1777307 : Blo 1184409 1777307 := bstep (se 1 (by rfl) ⟨1332980, by rfl⟩ : syracuseStep 1777307 = 2665961) B2665961
theorem B9617059 : Blo 1184409 9617059 := bstep (se 1 (by rfl) ⟨7212794, by rfl⟩ : syracuseStep 9617059 = 14425589) B14425589
theorem B1777343 : Blo 1184409 1777343 := bstep (se 1 (by rfl) ⟨1333007, by rfl⟩ : syracuseStep 1777343 = 2666015) B2666015
theorem B1998823 : Blo 1184409 1998823 := bstep (se 1 (by rfl) ⟨1499117, by rfl⟩ : syracuseStep 1998823 = 2998235) B2998235
theorem B1777727 : Blo 1184409 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B97386563 : Blo 1184409 97386563 := bstep (se 1 (by rfl) ⟨73039922, by rfl⟩ : syracuseStep 97386563 = 146079845) B146079845
theorem B19234907 : Blo 1184409 19234907 := bstep (se 1 (by rfl) ⟨14426180, by rfl⟩ : syracuseStep 19234907 = 28852361) B28852361
theorem B1777775 : Blo 1184409 1777775 := bstep (se 1 (by rfl) ⟨1333331, by rfl⟩ : syracuseStep 1777775 = 2666663) B2666663
theorem B30769345 : Blo 1184409 30769345 := bstep (se 2 (by rfl) ⟨11538504, by rfl⟩ : syracuseStep 30769345 = 23077009) B23077009
theorem B2999015 : Blo 1184409 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B51290981 : Blo 1184409 51290981 := bstep (se 4 (by rfl) ⟨4808529, by rfl⟩ : syracuseStep 51290981 = 9617059) B9617059
theorem B1778555 : Blo 1184409 1778555 := bstep (se 1 (by rfl) ⟨1333916, by rfl⟩ : syracuseStep 1778555 = 2667833) B2667833
theorem B1778591 : Blo 1184409 1778591 := bstep (se 1 (by rfl) ⟨1333943, by rfl⟩ : syracuseStep 1778591 = 2667887) B2667887
theorem B2532539 : Blo 1184409 2532539 := bstep (se 1 (by rfl) ⟨1899404, by rfl⟩ : syracuseStep 2532539 = 3798809) B3798809
theorem B1779071 : Blo 1184409 1779071 := bstep (se 1 (by rfl) ⟨1334303, by rfl⟩ : syracuseStep 1779071 = 2668607) B2668607
theorem B9004607 : Blo 1184409 9004607 := bstep (se 1 (by rfl) ⟨6753455, by rfl⟩ : syracuseStep 9004607 = 13506911) B13506911
theorem B3376865 : Blo 1184409 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B10127177 : Blo 1184409 10127177 := bstep (se 2 (by rfl) ⟨3797691, by rfl⟩ : syracuseStep 10127177 = 7595383) B7595383
theorem B5064545 : Blo 1184409 5064545 := bstep (se 2 (by rfl) ⟨1899204, by rfl⟩ : syracuseStep 5064545 = 3798409) B3798409
theorem B2402207 : Blo 1184409 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B8996831 : Blo 1184409 8996831 := bstep (se 1 (by rfl) ⟨6747623, by rfl⟩ : syracuseStep 8996831 = 13495247) B13495247
theorem B2705455 : Blo 1184409 2705455 := bstep (se 1 (by rfl) ⟨2029091, by rfl⟩ : syracuseStep 2705455 = 4058183) B4058183
theorem B19220759 : Blo 1184409 19220759 := bstep (se 1 (by rfl) ⟨14415569, by rfl⟩ : syracuseStep 19220759 = 28831139) B28831139
theorem B6752591 : Blo 1184409 6752591 := bstep (se 1 (by rfl) ⟨5064443, by rfl⟩ : syracuseStep 6752591 = 10128887) B10128887
theorem B3377639 : Blo 1184409 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B2665097 : Blo 1184409 2665097 := bstep (se 2 (by rfl) ⟨999411, by rfl⟩ : syracuseStep 2665097 = 1998823) B1998823
theorem B4000481 : Blo 1184409 4000481 := bstep (se 2 (by rfl) ⟨1500180, by rfl⟩ : syracuseStep 4000481 = 3000361) B3000361
theorem B2665313 : Blo 1184409 2665313 := bstep (se 2 (by rfl) ⟨999492, by rfl⟩ : syracuseStep 2665313 = 1998985) B1998985
theorem B61590415 : Blo 1184409 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B30403673 : Blo 1184409 30403673 := bstep (se 2 (by rfl) ⟨11401377, by rfl⟩ : syracuseStep 30403673 = 22802755) B22802755
theorem B2665799 : Blo 1184409 2665799 := bstep (se 1 (by rfl) ⟨1999349, by rfl⟩ : syracuseStep 2665799 = 3998699) B3998699
theorem B8219999 : Blo 1184409 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B10120889 : Blo 1184409 10120889 := bstep (se 2 (by rfl) ⟨3795333, by rfl⟩ : syracuseStep 10120889 = 7590667) B7590667
theorem B3002143 : Blo 1184409 3002143 := bstep (se 1 (by rfl) ⟨2251607, by rfl⟩ : syracuseStep 3002143 = 4503215) B4503215
theorem B11259967 : Blo 1184409 11259967 := bstep (se 1 (by rfl) ⟨8444975, by rfl⟩ : syracuseStep 11259967 = 16889951) B16889951
theorem B20238497 : Blo 1184409 20238497 := bstep (se 2 (by rfl) ⟨7589436, by rfl⟩ : syracuseStep 20238497 = 15178873) B15178873
theorem B6746327 : Blo 1184409 6746327 := bstep (se 1 (by rfl) ⟨5059745, by rfl⟩ : syracuseStep 6746327 = 10119491) B10119491
theorem B2667113 : Blo 1184409 2667113 := bstep (se 2 (by rfl) ⟨1000167, by rfl⟩ : syracuseStep 2667113 = 2000335) B2000335
theorem B7598717 : Blo 1184409 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B1602217 : Blo 1184409 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B1184615 : Blo 1184409 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B2667455 : Blo 1184409 2667455 := bstep (se 1 (by rfl) ⟨2000591, by rfl⟩ : syracuseStep 2667455 = 4001183) B4001183
theorem B710530055 : Blo 1184409 710530055 := bstep (se 1 (by rfl) ⟨532897541, by rfl⟩ : syracuseStep 710530055 = 1065795083) B1065795083
theorem B1184871 : Blo 1184409 1184871 := bstep (se 1 (by rfl) ⟨888653, by rfl⟩ : syracuseStep 1184871 = 1777307) B1777307
theorem B1184895 : Blo 1184409 1184895 := bstep (se 1 (by rfl) ⟨888671, by rfl⟩ : syracuseStep 1184895 = 1777343) B1777343
theorem B2667707 : Blo 1184409 2667707 := bstep (se 1 (by rfl) ⟨2000780, by rfl⟩ : syracuseStep 2667707 = 4001561) B4001561
theorem B2667959 : Blo 1184409 2667959 := bstep (se 1 (by rfl) ⟨2000969, by rfl⟩ : syracuseStep 2667959 = 4001939) B4001939
theorem B6493673 : Blo 1184409 6493673 := bstep (se 2 (by rfl) ⟨2435127, by rfl⟩ : syracuseStep 6493673 = 4870255) B4870255
theorem B4003343 : Blo 1184409 4003343 := bstep (se 1 (by rfl) ⟨3002507, by rfl⟩ : syracuseStep 4003343 = 6005015) B6005015
theorem B1185307 : Blo 1184409 1185307 := bstep (se 1 (by rfl) ⟨888980, by rfl⟩ : syracuseStep 1185307 = 1777961) B1777961
theorem B7206569 : Blo 1184409 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B2668535 : Blo 1184409 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B1185883 : Blo 1184409 1185883 := bstep (se 1 (by rfl) ⟨889412, by rfl⟩ : syracuseStep 1185883 = 1778825) B1778825
theorem B1186075 : Blo 1184409 1186075 := bstep (se 1 (by rfl) ⟨889556, by rfl⟩ : syracuseStep 1186075 = 1779113) B1779113
theorem B2849183 : Blo 1184409 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B1186271 : Blo 1184409 1186271 := bstep (se 1 (by rfl) ⟨889703, by rfl⟩ : syracuseStep 1186271 = 1779407) B1779407
theorem B3374075 : Blo 1184409 3374075 := bstep (se 1 (by rfl) ⟨2530556, by rfl⟩ : syracuseStep 3374075 = 5061113) B5061113
theorem B1334299 : Blo 1184409 1334299 := bstep (se 1 (by rfl) ⟨1000724, by rfl⟩ : syracuseStep 1334299 = 2001449) B2001449
theorem B2702747 : Blo 1184409 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B27377129 : Blo 1184409 27377129 := bstep (se 2 (by rfl) ⟨10266423, by rfl⟩ : syracuseStep 27377129 = 20532847) B20532847
theorem B1777223 : Blo 1184409 1777223 := bstep (se 1 (by rfl) ⟨1332917, by rfl⟩ : syracuseStep 1777223 = 2665835) B2665835
theorem B13508369 : Blo 1184409 13508369 := bstep (se 2 (by rfl) ⟨5065638, by rfl⟩ : syracuseStep 13508369 = 10131277) B10131277
theorem B1777499 : Blo 1184409 1777499 := bstep (se 1 (by rfl) ⟨1333124, by rfl⟩ : syracuseStep 1777499 = 2666249) B2666249
theorem B4497383 : Blo 1184409 4497383 := bstep (se 1 (by rfl) ⟨3373037, by rfl⟩ : syracuseStep 4497383 = 6746075) B6746075
theorem B13492331 : Blo 1184409 13492331 := bstep (se 1 (by rfl) ⟨10119248, by rfl⟩ : syracuseStep 13492331 = 20238497) B20238497
theorem B4497551 : Blo 1184409 4497551 := bstep (se 1 (by rfl) ⟨3373163, by rfl⟩ : syracuseStep 4497551 = 6746327) B6746327
theorem B41025793 : Blo 1184409 41025793 := bstep (se 2 (by rfl) ⟨15384672, by rfl⟩ : syracuseStep 41025793 = 30769345) B30769345
theorem B1778075 : Blo 1184409 1778075 := bstep (se 1 (by rfl) ⟨1333556, by rfl⟩ : syracuseStep 1778075 = 2667113) B2667113
theorem B1999343 : Blo 1184409 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B34193987 : Blo 1184409 34193987 := bstep (se 1 (by rfl) ⟨25645490, by rfl⟩ : syracuseStep 34193987 = 51290981) B51290981
theorem B1778303 : Blo 1184409 1778303 := bstep (se 1 (by rfl) ⟨1333727, by rfl⟩ : syracuseStep 1778303 = 2667455) B2667455
theorem B473686703 : Blo 1184409 473686703 := bstep (se 1 (by rfl) ⟨355265027, by rfl⟩ : syracuseStep 473686703 = 710530055) B710530055
theorem B1778471 : Blo 1184409 1778471 := bstep (se 1 (by rfl) ⟨1333853, by rfl⟩ : syracuseStep 1778471 = 2667707) B2667707
theorem B1688359 : Blo 1184409 1688359 := bstep (se 1 (by rfl) ⟨1266269, by rfl⟩ : syracuseStep 1688359 = 2532539) B2532539
theorem B1778639 : Blo 1184409 1778639 := bstep (se 1 (by rfl) ⟨1333979, by rfl⟩ : syracuseStep 1778639 = 2667959) B2667959
theorem B6751451 : Blo 1184409 6751451 := bstep (se 1 (by rfl) ⟨5063588, by rfl⟩ : syracuseStep 6751451 = 10127177) B10127177
theorem B5997887 : Blo 1184409 5997887 := bstep (se 1 (by rfl) ⟨4498415, by rfl⟩ : syracuseStep 5997887 = 8996831) B8996831
theorem B1779023 : Blo 1184409 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B1779065 : Blo 1184409 1779065 := bstep (se 2 (by rfl) ⟨667149, by rfl⟩ : syracuseStep 1779065 = 1334299) B1334299
theorem B12813839 : Blo 1184409 12813839 := bstep (se 1 (by rfl) ⟨9610379, by rfl⟩ : syracuseStep 12813839 = 19220759) B19220759
theorem B20269115 : Blo 1184409 20269115 := bstep (se 1 (by rfl) ⟨15201836, by rfl⟩ : syracuseStep 20269115 = 30403673) B30403673
theorem B9005579 : Blo 1184409 9005579 := bstep (se 1 (by rfl) ⟨6754184, by rfl⟩ : syracuseStep 9005579 = 13508369) B13508369
theorem B64924375 : Blo 1184409 64924375 := bstep (se 1 (by rfl) ⟨48693281, by rfl⟩ : syracuseStep 64924375 = 97386563) B97386563
theorem B12823271 : Blo 1184409 12823271 := bstep (se 1 (by rfl) ⟨9617453, by rfl⟩ : syracuseStep 12823271 = 19234907) B19234907
theorem B3607273 : Blo 1184409 3607273 := bstep (se 2 (by rfl) ⟨1352727, by rfl⟩ : syracuseStep 3607273 = 2705455) B2705455
theorem B5065811 : Blo 1184409 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B4804379 : Blo 1184409 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B82120553 : Blo 1184409 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B9007037 : Blo 1184409 9007037 := bstep (se 3 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 9007037 = 3377639) B3377639
theorem B1601471 : Blo 1184409 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B4501727 : Blo 1184409 4501727 := bstep (se 1 (by rfl) ⟨3376295, by rfl⟩ : syracuseStep 4501727 = 6752591) B6752591
theorem B2666987 : Blo 1184409 2666987 := bstep (se 1 (by rfl) ⟨2000240, by rfl⟩ : syracuseStep 2666987 = 4000481) B4000481
theorem B2249383 : Blo 1184409 2249383 := bstep (se 1 (by rfl) ⟨1687037, by rfl⟩ : syracuseStep 2249383 = 3374075) B3374075
theorem B13505453 : Blo 1184409 13505453 := bstep (se 3 (by rfl) ⟨2532272, by rfl⟩ : syracuseStep 13505453 = 5064545) B5064545
theorem B4002857 : Blo 1184409 4002857 := bstep (se 2 (by rfl) ⟨1501071, by rfl⟩ : syracuseStep 4002857 = 3002143) B3002143
theorem B1184815 : Blo 1184409 1184815 := bstep (se 1 (by rfl) ⟨888611, by rfl⟩ : syracuseStep 1184815 = 1777223) B1777223
theorem B6747259 : Blo 1184409 6747259 := bstep (se 1 (by rfl) ⟨5060444, by rfl⟩ : syracuseStep 6747259 = 10120889) B10120889
theorem B1184999 : Blo 1184409 1184999 := bstep (se 1 (by rfl) ⟨888749, by rfl⟩ : syracuseStep 1184999 = 1777499) B1777499
theorem B1185151 : Blo 1184409 1185151 := bstep (se 1 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 1185151 = 1777727) B1777727
theorem B1185183 : Blo 1184409 1185183 := bstep (se 1 (by rfl) ⟨888887, by rfl⟩ : syracuseStep 1185183 = 1777775) B1777775
theorem B15013289 : Blo 1184409 15013289 := bstep (se 2 (by rfl) ⟨5629983, by rfl⟩ : syracuseStep 15013289 = 11259967) B11259967
theorem B1185703 : Blo 1184409 1185703 := bstep (se 1 (by rfl) ⟨889277, by rfl⟩ : syracuseStep 1185703 = 1778555) B1778555
theorem B1185727 : Blo 1184409 1185727 := bstep (se 1 (by rfl) ⟨889295, by rfl⟩ : syracuseStep 1185727 = 1778591) B1778591
theorem B2136289 : Blo 1184409 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B21919997 : Blo 1184409 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B1186047 : Blo 1184409 1186047 := bstep (se 1 (by rfl) ⟨889535, by rfl⟩ : syracuseStep 1186047 = 1779071) B1779071
theorem B2668895 : Blo 1184409 2668895 := bstep (se 1 (by rfl) ⟨2001671, by rfl⟩ : syracuseStep 2668895 = 4003343) B4003343
theorem B6003071 : Blo 1184409 6003071 := bstep (se 1 (by rfl) ⟨4502303, by rfl⟩ : syracuseStep 6003071 = 9004607) B9004607
theorem B7207325 : Blo 1184409 7207325 := bstep (se 3 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 7207325 = 2702747) B2702747
theorem B2251243 : Blo 1184409 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B17316461 : Blo 1184409 17316461 := bstep (se 3 (by rfl) ⟨3246836, by rfl⟩ : syracuseStep 17316461 = 6493673) B6493673
theorem B1899455 : Blo 1184409 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B1776731 : Blo 1184409 1776731 := bstep (se 1 (by rfl) ⟨1332548, by rfl⟩ : syracuseStep 1776731 = 2665097) B2665097
theorem B1776875 : Blo 1184409 1776875 := bstep (se 1 (by rfl) ⟨1332656, by rfl⟩ : syracuseStep 1776875 = 2665313) B2665313
theorem B1777199 : Blo 1184409 1777199 := bstep (se 1 (by rfl) ⟨1332899, by rfl⟩ : syracuseStep 1777199 = 2665799) B2665799
theorem B18251419 : Blo 1184409 18251419 := bstep (se 1 (by rfl) ⟨13688564, by rfl⟩ : syracuseStep 18251419 = 27377129) B27377129
theorem B2998255 : Blo 1184409 2998255 := bstep (se 1 (by rfl) ⟨2248691, by rfl⟩ : syracuseStep 2998255 = 4497383) B4497383
theorem B8994887 : Blo 1184409 8994887 := bstep (se 1 (by rfl) ⟨6746165, by rfl⟩ : syracuseStep 8994887 = 13492331) B13492331
theorem B2998367 : Blo 1184409 2998367 := bstep (se 1 (by rfl) ⟨2248775, by rfl⟩ : syracuseStep 2998367 = 4497551) B4497551
theorem B1777991 : Blo 1184409 1777991 := bstep (se 1 (by rfl) ⟨1333493, by rfl⟩ : syracuseStep 1777991 = 2666987) B2666987
theorem B9003635 : Blo 1184409 9003635 := bstep (se 1 (by rfl) ⟨6752726, by rfl⟩ : syracuseStep 9003635 = 13505453) B13505453
theorem B3998591 : Blo 1184409 3998591 := bstep (se 1 (by rfl) ⟨2998943, by rfl⟩ : syracuseStep 3998591 = 5997887) B5997887
theorem B2999177 : Blo 1184409 2999177 := bstep (se 2 (by rfl) ⟨1124691, by rfl⟩ : syracuseStep 2999177 = 2249383) B2249383
theorem B86565833 : Blo 1184409 86565833 := bstep (se 2 (by rfl) ⟨32462187, by rfl⟩ : syracuseStep 86565833 = 64924375) B64924375
theorem B40035437 : Blo 1184409 40035437 := bstep (se 3 (by rfl) ⟨7506644, by rfl⟩ : syracuseStep 40035437 = 15013289) B15013289
theorem B8996345 : Blo 1184409 8996345 := bstep (se 2 (by rfl) ⟨3373629, by rfl⟩ : syracuseStep 8996345 = 6747259) B6747259
theorem B1779263 : Blo 1184409 1779263 := bstep (se 1 (by rfl) ⟨1334447, by rfl⟩ : syracuseStep 1779263 = 2668895) B2668895
theorem B3377207 : Blo 1184409 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B4270589 : Blo 1184409 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B5065213 : Blo 1184409 5065213 := bstep (se 3 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 5065213 = 1899455) B1899455
theorem B3001151 : Blo 1184409 3001151 := bstep (se 1 (by rfl) ⟨2250863, by rfl⟩ : syracuseStep 3001151 = 4501727) B4501727
theorem B54701057 : Blo 1184409 54701057 := bstep (se 2 (by rfl) ⟨20512896, by rfl⟩ : syracuseStep 54701057 = 41025793) B41025793
theorem B3001657 : Blo 1184409 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B58453325 : Blo 1184409 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B4500967 : Blo 1184409 4500967 := bstep (se 1 (by rfl) ⟨3375725, by rfl⟩ : syracuseStep 4500967 = 6751451) B6751451
theorem B19238789 : Blo 1184409 19238789 := bstep (se 4 (by rfl) ⟨1803636, by rfl⟩ : syracuseStep 19238789 = 3607273) B3607273
theorem B13512743 : Blo 1184409 13512743 := bstep (se 1 (by rfl) ⟨10134557, by rfl⟩ : syracuseStep 13512743 = 20269115) B20269115
theorem B4002047 : Blo 1184409 4002047 := bstep (se 1 (by rfl) ⟨3001535, by rfl⟩ : syracuseStep 4002047 = 6003071) B6003071
theorem B4804883 : Blo 1184409 4804883 := bstep (se 1 (by rfl) ⟨3603662, by rfl⟩ : syracuseStep 4804883 = 7207325) B7207325
theorem B8548847 : Blo 1184409 8548847 := bstep (se 1 (by rfl) ⟨6411635, by rfl⟩ : syracuseStep 8548847 = 12823271) B12823271
theorem B1184487 : Blo 1184409 1184487 := bstep (se 1 (by rfl) ⟨888365, by rfl⟩ : syracuseStep 1184487 = 1776731) B1776731
theorem B1184583 : Blo 1184409 1184583 := bstep (se 1 (by rfl) ⟨888437, by rfl⟩ : syracuseStep 1184583 = 1776875) B1776875
theorem B24335225 : Blo 1184409 24335225 := bstep (se 2 (by rfl) ⟨9125709, by rfl⟩ : syracuseStep 24335225 = 18251419) B18251419
theorem B1184799 : Blo 1184409 1184799 := bstep (se 1 (by rfl) ⟨888599, by rfl⟩ : syracuseStep 1184799 = 1777199) B1777199
theorem B1185383 : Blo 1184409 1185383 := bstep (se 1 (by rfl) ⟨889037, by rfl⟩ : syracuseStep 1185383 = 1778075) B1778075
theorem B2848385 : Blo 1184409 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B1332895 : Blo 1184409 1332895 := bstep (se 1 (by rfl) ⟨999671, by rfl⟩ : syracuseStep 1332895 = 1999343) B1999343
theorem B22795991 : Blo 1184409 22795991 := bstep (se 1 (by rfl) ⟨17096993, by rfl⟩ : syracuseStep 22795991 = 34193987) B34193987
theorem B1185535 : Blo 1184409 1185535 := bstep (se 1 (by rfl) ⟨889151, by rfl⟩ : syracuseStep 1185535 = 1778303) B1778303
theorem B315791135 : Blo 1184409 315791135 := bstep (se 1 (by rfl) ⟨236843351, by rfl⟩ : syracuseStep 315791135 = 473686703) B473686703
theorem B1185647 : Blo 1184409 1185647 := bstep (se 1 (by rfl) ⟨889235, by rfl⟩ : syracuseStep 1185647 = 1778471) B1778471
theorem B1185759 : Blo 1184409 1185759 := bstep (se 1 (by rfl) ⟨889319, by rfl⟩ : syracuseStep 1185759 = 1778639) B1778639
theorem B2668571 : Blo 1184409 2668571 := bstep (se 1 (by rfl) ⟨2001428, by rfl⟩ : syracuseStep 2668571 = 4002857) B4002857
theorem B1186015 : Blo 1184409 1186015 := bstep (se 1 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 1186015 = 1779023) B1779023
theorem B1186043 : Blo 1184409 1186043 := bstep (se 1 (by rfl) ⟨889532, by rfl⟩ : syracuseStep 1186043 = 1779065) B1779065
theorem B8542559 : Blo 1184409 8542559 := bstep (se 1 (by rfl) ⟨6406919, by rfl⟩ : syracuseStep 8542559 = 12813839) B12813839
theorem B2251145 : Blo 1184409 2251145 := bstep (se 2 (by rfl) ⟨844179, by rfl⟩ : syracuseStep 2251145 = 1688359) B1688359
theorem B46177229 : Blo 1184409 46177229 := bstep (se 3 (by rfl) ⟨8658230, by rfl⟩ : syracuseStep 46177229 = 17316461) B17316461
theorem B6003719 : Blo 1184409 6003719 := bstep (se 1 (by rfl) ⟨4502789, by rfl⟩ : syracuseStep 6003719 = 9005579) B9005579
theorem B3202919 : Blo 1184409 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B54747035 : Blo 1184409 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B6004691 : Blo 1184409 6004691 := bstep (se 1 (by rfl) ⟨4503518, by rfl⟩ : syracuseStep 6004691 = 9007037) B9007037
theorem B3997673 : Blo 1184409 3997673 := bstep (se 2 (by rfl) ⟨1499127, by rfl⟩ : syracuseStep 3997673 = 2998255) B2998255
theorem B5996591 : Blo 1184409 5996591 := bstep (se 1 (by rfl) ⟨4497443, by rfl⟩ : syracuseStep 5996591 = 8994887) B8994887
theorem B1998911 : Blo 1184409 1998911 := bstep (se 1 (by rfl) ⟨1499183, by rfl⟩ : syracuseStep 1998911 = 2998367) B2998367
theorem B3203255 : Blo 1184409 3203255 := bstep (se 1 (by rfl) ⟨2402441, by rfl⟩ : syracuseStep 3203255 = 4804883) B4804883
theorem B1999451 : Blo 1184409 1999451 := bstep (se 1 (by rfl) ⟨1499588, by rfl⟩ : syracuseStep 1999451 = 2999177) B2999177
theorem B26690291 : Blo 1184409 26690291 := bstep (se 1 (by rfl) ⟨20017718, by rfl⟩ : syracuseStep 26690291 = 40035437) B40035437
theorem B5997563 : Blo 1184409 5997563 := bstep (se 1 (by rfl) ⟨4498172, by rfl⟩ : syracuseStep 5997563 = 8996345) B8996345
theorem B15197327 : Blo 1184409 15197327 := bstep (se 1 (by rfl) ⟨11397995, by rfl⟩ : syracuseStep 15197327 = 22795991) B22795991
theorem B210527423 : Blo 1184409 210527423 := bstep (se 1 (by rfl) ⟨157895567, by rfl⟩ : syracuseStep 210527423 = 315791135) B315791135
theorem B1779047 : Blo 1184409 1779047 := bstep (se 1 (by rfl) ⟨1334285, by rfl⟩ : syracuseStep 1779047 = 2668571) B2668571
theorem B5695039 : Blo 1184409 5695039 := bstep (se 1 (by rfl) ⟨4271279, by rfl⟩ : syracuseStep 5695039 = 8542559) B8542559
theorem B1500763 : Blo 1184409 1500763 := bstep (se 1 (by rfl) ⟨1125572, by rfl⟩ : syracuseStep 1500763 = 2251145) B2251145
theorem B7595693 : Blo 1184409 7595693 := bstep (se 3 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 7595693 = 2848385) B2848385
theorem B2000767 : Blo 1184409 2000767 := bstep (se 1 (by rfl) ⟨1500575, by rfl⟩ : syracuseStep 2000767 = 3001151) B3001151
theorem B36498023 : Blo 1184409 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B2665115 : Blo 1184409 2665115 := bstep (se 1 (by rfl) ⟨1998836, by rfl⟩ : syracuseStep 2665115 = 3997673) B3997673
theorem B16223483 : Blo 1184409 16223483 := bstep (se 1 (by rfl) ⟨12167612, by rfl⟩ : syracuseStep 16223483 = 24335225) B24335225
theorem B2665727 : Blo 1184409 2665727 := bstep (se 1 (by rfl) ⟨1999295, by rfl⟩ : syracuseStep 2665727 = 3998591) B3998591
theorem B6753617 : Blo 1184409 6753617 := bstep (se 2 (by rfl) ⟨2532606, by rfl⟩ : syracuseStep 6753617 = 5065213) B5065213
theorem B2847059 : Blo 1184409 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B4002209 : Blo 1184409 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B6001289 : Blo 1184409 6001289 := bstep (se 2 (by rfl) ⟨2250483, by rfl⟩ : syracuseStep 6001289 = 4500967) B4500967
theorem B36467371 : Blo 1184409 36467371 := bstep (se 1 (by rfl) ⟨27350528, by rfl⟩ : syracuseStep 36467371 = 54701057) B54701057
theorem B4002479 : Blo 1184409 4002479 := bstep (se 1 (by rfl) ⟨3001859, by rfl⟩ : syracuseStep 4002479 = 6003719) B6003719
theorem B123139277 : Blo 1184409 123139277 := bstep (se 3 (by rfl) ⟨23088614, by rfl⟩ : syracuseStep 123139277 = 46177229) B46177229
theorem B2135279 : Blo 1184409 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B12825859 : Blo 1184409 12825859 := bstep (se 1 (by rfl) ⟨9619394, by rfl⟩ : syracuseStep 12825859 = 19238789) B19238789
theorem B4003127 : Blo 1184409 4003127 := bstep (se 1 (by rfl) ⟨3002345, by rfl⟩ : syracuseStep 4003127 = 6004691) B6004691
theorem B9008495 : Blo 1184409 9008495 := bstep (se 1 (by rfl) ⟨6756371, by rfl⟩ : syracuseStep 9008495 = 13512743) B13512743
theorem B2668031 : Blo 1184409 2668031 := bstep (se 1 (by rfl) ⟨2001023, by rfl⟩ : syracuseStep 2668031 = 4002047) B4002047
theorem B1185327 : Blo 1184409 1185327 := bstep (se 1 (by rfl) ⟨888995, by rfl⟩ : syracuseStep 1185327 = 1777991) B1777991
theorem B5699231 : Blo 1184409 5699231 := bstep (se 1 (by rfl) ⟨4274423, by rfl⟩ : syracuseStep 5699231 = 8548847) B8548847
theorem B6002423 : Blo 1184409 6002423 := bstep (se 1 (by rfl) ⟨4501817, by rfl⟩ : syracuseStep 6002423 = 9003635) B9003635
theorem B57710555 : Blo 1184409 57710555 := bstep (se 1 (by rfl) ⟨43282916, by rfl⟩ : syracuseStep 57710555 = 86565833) B86565833
theorem B1186175 : Blo 1184409 1186175 := bstep (se 1 (by rfl) ⟨889631, by rfl⟩ : syracuseStep 1186175 = 1779263) B1779263
theorem B2251471 : Blo 1184409 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B1777193 : Blo 1184409 1777193 := bstep (se 2 (by rfl) ⟨666447, by rfl⟩ : syracuseStep 1777193 = 1332895) B1332895
theorem B38968883 : Blo 1184409 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B3997727 : Blo 1184409 3997727 := bstep (se 1 (by rfl) ⟨2998295, by rfl⟩ : syracuseStep 3997727 = 5996591) B5996591
theorem B17793527 : Blo 1184409 17793527 := bstep (se 1 (by rfl) ⟨13345145, by rfl⟩ : syracuseStep 17793527 = 26690291) B26690291
theorem B5694077 : Blo 1184409 5694077 := bstep (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) B2135279
theorem B3998375 : Blo 1184409 3998375 := bstep (se 1 (by rfl) ⟨2998781, by rfl⟩ : syracuseStep 3998375 = 5997563) B5997563
theorem B82092851 : Blo 1184409 82092851 := bstep (se 1 (by rfl) ⟨61569638, by rfl⟩ : syracuseStep 82092851 = 123139277) B123139277
theorem B6005663 : Blo 1184409 6005663 := bstep (se 1 (by rfl) ⟨4504247, by rfl⟩ : syracuseStep 6005663 = 9008495) B9008495
theorem B1778687 : Blo 1184409 1778687 := bstep (se 1 (by rfl) ⟨1334015, by rfl⟩ : syracuseStep 1778687 = 2668031) B2668031
theorem B5063795 : Blo 1184409 5063795 := bstep (se 1 (by rfl) ⟨3797846, by rfl⟩ : syracuseStep 5063795 = 7595693) B7595693
theorem B24332015 : Blo 1184409 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B2001017 : Blo 1184409 2001017 := bstep (se 2 (by rfl) ⟨750381, by rfl⟩ : syracuseStep 2001017 = 1500763) B1500763
theorem B10815655 : Blo 1184409 10815655 := bstep (se 1 (by rfl) ⟨8111741, by rfl⟩ : syracuseStep 10815655 = 16223483) B16223483
theorem B25979255 : Blo 1184409 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B4000859 : Blo 1184409 4000859 := bstep (se 1 (by rfl) ⟨3000644, by rfl⟩ : syracuseStep 4000859 = 6001289) B6001289
theorem B48623161 : Blo 1184409 48623161 := bstep (se 2 (by rfl) ⟨18233685, by rfl⟩ : syracuseStep 48623161 = 36467371) B36467371
theorem B3001961 : Blo 1184409 3001961 := bstep (se 2 (by rfl) ⟨1125735, by rfl⟩ : syracuseStep 3001961 = 2251471) B2251471
theorem B4001615 : Blo 1184409 4001615 := bstep (se 1 (by rfl) ⟨3001211, by rfl⟩ : syracuseStep 4001615 = 6002423) B6002423
theorem B38473703 : Blo 1184409 38473703 := bstep (se 1 (by rfl) ⟨28855277, by rfl⟩ : syracuseStep 38473703 = 57710555) B57710555
theorem B17101145 : Blo 1184409 17101145 := bstep (se 2 (by rfl) ⟨6412929, by rfl⟩ : syracuseStep 17101145 = 12825859) B12825859
theorem B4502411 : Blo 1184409 4502411 := bstep (se 1 (by rfl) ⟨3376808, by rfl⟩ : syracuseStep 4502411 = 6753617) B6753617
theorem B1184795 : Blo 1184409 1184795 := bstep (se 1 (by rfl) ⟨888596, by rfl⟩ : syracuseStep 1184795 = 1777193) B1777193
theorem B2667689 : Blo 1184409 2667689 := bstep (se 2 (by rfl) ⟨1000383, by rfl⟩ : syracuseStep 2667689 = 2000767) B2000767
theorem B1332607 : Blo 1184409 1332607 := bstep (se 1 (by rfl) ⟨999455, by rfl⟩ : syracuseStep 1332607 = 1998911) B1998911
theorem B2135503 : Blo 1184409 2135503 := bstep (se 1 (by rfl) ⟨1601627, by rfl⟩ : syracuseStep 2135503 = 3203255) B3203255
theorem B1898039 : Blo 1184409 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B2668139 : Blo 1184409 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B1332967 : Blo 1184409 1332967 := bstep (se 1 (by rfl) ⟨999725, by rfl⟩ : syracuseStep 1332967 = 1999451) B1999451
theorem B2668319 : Blo 1184409 2668319 := bstep (se 1 (by rfl) ⟨2001239, by rfl⟩ : syracuseStep 2668319 = 4002479) B4002479
theorem B10131551 : Blo 1184409 10131551 := bstep (se 1 (by rfl) ⟨7598663, by rfl⟩ : syracuseStep 10131551 = 15197327) B15197327
theorem B140351615 : Blo 1184409 140351615 := bstep (se 1 (by rfl) ⟨105263711, by rfl⟩ : syracuseStep 140351615 = 210527423) B210527423
theorem B2668751 : Blo 1184409 2668751 := bstep (se 1 (by rfl) ⟨2001563, by rfl⟩ : syracuseStep 2668751 = 4003127) B4003127
theorem B1186031 : Blo 1184409 1186031 := bstep (se 1 (by rfl) ⟨889523, by rfl⟩ : syracuseStep 1186031 = 1779047) B1779047
theorem B3799487 : Blo 1184409 3799487 := bstep (se 1 (by rfl) ⟨2849615, by rfl⟩ : syracuseStep 3799487 = 5699231) B5699231
theorem B1776743 : Blo 1184409 1776743 := bstep (se 1 (by rfl) ⟨1332557, by rfl⟩ : syracuseStep 1776743 = 2665115) B2665115
theorem B7593385 : Blo 1184409 7593385 := bstep (se 2 (by rfl) ⟨2847519, by rfl⟩ : syracuseStep 7593385 = 5695039) B5695039
theorem B1777151 : Blo 1184409 1777151 := bstep (se 1 (by rfl) ⟨1332863, by rfl⟩ : syracuseStep 1777151 = 2665727) B2665727
theorem B3375863 : Blo 1184409 3375863 := bstep (se 1 (by rfl) ⟨2531897, by rfl⟩ : syracuseStep 3375863 = 5063795) B5063795
theorem B1778459 : Blo 1184409 1778459 := bstep (se 1 (by rfl) ⟨1333844, by rfl⟩ : syracuseStep 1778459 = 2667689) B2667689
theorem B1778759 : Blo 1184409 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B1778879 : Blo 1184409 1778879 := bstep (se 1 (by rfl) ⟨1334159, by rfl⟩ : syracuseStep 1778879 = 2668319) B2668319
theorem B47449405 : Blo 1184409 47449405 := bstep (se 3 (by rfl) ⟨8896763, by rfl⟩ : syracuseStep 47449405 = 17793527) B17793527
theorem B1779167 : Blo 1184409 1779167 := bstep (se 1 (by rfl) ⟨1334375, by rfl⟩ : syracuseStep 1779167 = 2668751) B2668751
theorem B17319503 : Blo 1184409 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B2532991 : Blo 1184409 2532991 := bstep (se 1 (by rfl) ⟨1899743, by rfl⟩ : syracuseStep 2532991 = 3799487) B3799487
theorem B2001307 : Blo 1184409 2001307 := bstep (se 1 (by rfl) ⟨1500980, by rfl⟩ : syracuseStep 2001307 = 3001961) B3001961
theorem B11389349 : Blo 1184409 11389349 := bstep (se 4 (by rfl) ⟨1067751, by rfl⟩ : syracuseStep 11389349 = 2135503) B2135503
theorem B2665151 : Blo 1184409 2665151 := bstep (se 1 (by rfl) ⟨1998863, by rfl⟩ : syracuseStep 2665151 = 3997727) B3997727
theorem B14420873 : Blo 1184409 14420873 := bstep (se 2 (by rfl) ⟨5407827, by rfl⟩ : syracuseStep 14420873 = 10815655) B10815655
theorem B2665583 : Blo 1184409 2665583 := bstep (se 1 (by rfl) ⟨1999187, by rfl⟩ : syracuseStep 2665583 = 3998375) B3998375
theorem B3001607 : Blo 1184409 3001607 := bstep (se 1 (by rfl) ⟨2251205, by rfl⟩ : syracuseStep 3001607 = 4502411) B4502411
theorem B6754367 : Blo 1184409 6754367 := bstep (se 1 (by rfl) ⟨5065775, by rfl⟩ : syracuseStep 6754367 = 10131551) B10131551
theorem B15184205 : Blo 1184409 15184205 := bstep (se 3 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 15184205 = 5694077) B5694077
theorem B64885373 : Blo 1184409 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B2667239 : Blo 1184409 2667239 := bstep (se 1 (by rfl) ⟨2000429, by rfl⟩ : syracuseStep 2667239 = 4000859) B4000859
theorem B1184495 : Blo 1184409 1184495 := bstep (se 1 (by rfl) ⟨888371, by rfl⟩ : syracuseStep 1184495 = 1776743) B1776743
theorem B1184767 : Blo 1184409 1184767 := bstep (se 1 (by rfl) ⟨888575, by rfl⟩ : syracuseStep 1184767 = 1777151) B1777151
theorem B2667743 : Blo 1184409 2667743 := bstep (se 1 (by rfl) ⟨2000807, by rfl⟩ : syracuseStep 2667743 = 4001615) B4001615
theorem B11400763 : Blo 1184409 11400763 := bstep (se 1 (by rfl) ⟨8550572, by rfl⟩ : syracuseStep 11400763 = 17101145) B17101145
theorem B54728567 : Blo 1184409 54728567 := bstep (se 1 (by rfl) ⟨41046425, by rfl⟩ : syracuseStep 54728567 = 82092851) B82092851
theorem B4003775 : Blo 1184409 4003775 := bstep (se 1 (by rfl) ⟨3002831, by rfl⟩ : syracuseStep 4003775 = 6005663) B6005663
theorem B1185791 : Blo 1184409 1185791 := bstep (se 1 (by rfl) ⟨889343, by rfl⟩ : syracuseStep 1185791 = 1778687) B1778687
theorem B1334011 : Blo 1184409 1334011 := bstep (se 1 (by rfl) ⟨1000508, by rfl⟩ : syracuseStep 1334011 = 2001017) B2001017
theorem B93567743 : Blo 1184409 93567743 := bstep (se 1 (by rfl) ⟨70175807, by rfl⟩ : syracuseStep 93567743 = 140351615) B140351615
theorem B5061437 : Blo 1184409 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B1776809 : Blo 1184409 1776809 := bstep (se 2 (by rfl) ⟨666303, by rfl⟩ : syracuseStep 1776809 = 1332607) B1332607
theorem B10124513 : Blo 1184409 10124513 := bstep (se 2 (by rfl) ⟨3796692, by rfl⟩ : syracuseStep 10124513 = 7593385) B7593385
theorem B64830881 : Blo 1184409 64830881 := bstep (se 2 (by rfl) ⟨24311580, by rfl⟩ : syracuseStep 64830881 = 48623161) B48623161
theorem B1777289 : Blo 1184409 1777289 := bstep (se 2 (by rfl) ⟨666483, by rfl⟩ : syracuseStep 1777289 = 1332967) B1332967
theorem B25649135 : Blo 1184409 25649135 := bstep (se 1 (by rfl) ⟨19236851, by rfl⟩ : syracuseStep 25649135 = 38473703) B38473703
theorem B1778159 : Blo 1184409 1778159 := bstep (se 1 (by rfl) ⟨1333619, by rfl⟩ : syracuseStep 1778159 = 2667239) B2667239
theorem B1778495 : Blo 1184409 1778495 := bstep (se 1 (by rfl) ⟨1333871, by rfl⟩ : syracuseStep 1778495 = 2667743) B2667743
theorem B1778681 : Blo 1184409 1778681 := bstep (se 2 (by rfl) ⟨667005, by rfl⟩ : syracuseStep 1778681 = 1334011) B1334011
theorem B3377321 : Blo 1184409 3377321 := bstep (se 2 (by rfl) ⟨1266495, by rfl⟩ : syracuseStep 3377321 = 2532991) B2532991
theorem B2001071 : Blo 1184409 2001071 := bstep (se 1 (by rfl) ⟨1500803, by rfl⟩ : syracuseStep 2001071 = 3001607) B3001607
theorem B38455661 : Blo 1184409 38455661 := bstep (se 3 (by rfl) ⟨7210436, by rfl⟩ : syracuseStep 38455661 = 14420873) B14420873
theorem B17099423 : Blo 1184409 17099423 := bstep (se 1 (by rfl) ⟨12824567, by rfl⟩ : syracuseStep 17099423 = 25649135) B25649135
theorem B43256915 : Blo 1184409 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B11546335 : Blo 1184409 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B62378495 : Blo 1184409 62378495 := bstep (se 1 (by rfl) ⟨46783871, by rfl⟩ : syracuseStep 62378495 = 93567743) B93567743
theorem B15201017 : Blo 1184409 15201017 := bstep (se 2 (by rfl) ⟨5700381, by rfl⟩ : syracuseStep 15201017 = 11400763) B11400763
theorem B1184539 : Blo 1184409 1184539 := bstep (se 1 (by rfl) ⟨888404, by rfl⟩ : syracuseStep 1184539 = 1776809) B1776809
theorem B1184859 : Blo 1184409 1184859 := bstep (se 1 (by rfl) ⟨888644, by rfl⟩ : syracuseStep 1184859 = 1777289) B1777289
theorem B4502911 : Blo 1184409 4502911 := bstep (se 1 (by rfl) ⟨3377183, by rfl⟩ : syracuseStep 4502911 = 6754367) B6754367
theorem B10122803 : Blo 1184409 10122803 := bstep (se 1 (by rfl) ⟨7592102, by rfl⟩ : syracuseStep 10122803 = 15184205) B15184205
theorem B2250575 : Blo 1184409 2250575 := bstep (se 1 (by rfl) ⟨1687931, by rfl⟩ : syracuseStep 2250575 = 3375863) B3375863
theorem B1185639 : Blo 1184409 1185639 := bstep (se 1 (by rfl) ⟨889229, by rfl⟩ : syracuseStep 1185639 = 1778459) B1778459
theorem B2668409 : Blo 1184409 2668409 := bstep (se 2 (by rfl) ⟨1000653, by rfl⟩ : syracuseStep 2668409 = 2001307) B2001307
theorem B1185839 : Blo 1184409 1185839 := bstep (se 1 (by rfl) ⟨889379, by rfl⟩ : syracuseStep 1185839 = 1778759) B1778759
theorem B1185919 : Blo 1184409 1185919 := bstep (se 1 (by rfl) ⟨889439, by rfl⟩ : syracuseStep 1185919 = 1778879) B1778879
theorem B1186111 : Blo 1184409 1186111 := bstep (se 1 (by rfl) ⟨889583, by rfl⟩ : syracuseStep 1186111 = 1779167) B1779167
theorem B36485711 : Blo 1184409 36485711 := bstep (se 1 (by rfl) ⟨27364283, by rfl⟩ : syracuseStep 36485711 = 54728567) B54728567
theorem B2669183 : Blo 1184409 2669183 := bstep (se 1 (by rfl) ⟨2001887, by rfl⟩ : syracuseStep 2669183 = 4003775) B4003775
theorem B7592899 : Blo 1184409 7592899 := bstep (se 1 (by rfl) ⟨5694674, by rfl⟩ : syracuseStep 7592899 = 11389349) B11389349
theorem B63265873 : Blo 1184409 63265873 := bstep (se 2 (by rfl) ⟨23724702, by rfl⟩ : syracuseStep 63265873 = 47449405) B47449405
theorem B1776767 : Blo 1184409 1776767 := bstep (se 1 (by rfl) ⟨1332575, by rfl⟩ : syracuseStep 1776767 = 2665151) B2665151
theorem B3374291 : Blo 1184409 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B1777055 : Blo 1184409 1777055 := bstep (se 1 (by rfl) ⟨1332791, by rfl⟩ : syracuseStep 1777055 = 2665583) B2665583
theorem B6749675 : Blo 1184409 6749675 := bstep (se 1 (by rfl) ⟨5062256, by rfl⟩ : syracuseStep 6749675 = 10124513) B10124513
theorem B43220587 : Blo 1184409 43220587 := bstep (se 1 (by rfl) ⟨32415440, by rfl⟩ : syracuseStep 43220587 = 64830881) B64830881
theorem B10134011 : Blo 1184409 10134011 := bstep (se 1 (by rfl) ⟨7600508, by rfl⟩ : syracuseStep 10134011 = 15201017) B15201017
theorem B1500383 : Blo 1184409 1500383 := bstep (se 1 (by rfl) ⟨1125287, by rfl⟩ : syracuseStep 1500383 = 2250575) B2250575
theorem B1778939 : Blo 1184409 1778939 := bstep (se 1 (by rfl) ⟨1334204, by rfl⟩ : syracuseStep 1778939 = 2668409) B2668409
theorem B84354497 : Blo 1184409 84354497 := bstep (se 2 (by rfl) ⟨31632936, by rfl⟩ : syracuseStep 84354497 = 63265873) B63265873
theorem B24323807 : Blo 1184409 24323807 := bstep (se 1 (by rfl) ⟨18242855, by rfl⟩ : syracuseStep 24323807 = 36485711) B36485711
theorem B1779455 : Blo 1184409 1779455 := bstep (se 1 (by rfl) ⟨1334591, by rfl⟩ : syracuseStep 1779455 = 2669183) B2669183
theorem B28837943 : Blo 1184409 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B15395113 : Blo 1184409 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B4499783 : Blo 1184409 4499783 := bstep (se 1 (by rfl) ⟨3374837, by rfl⟩ : syracuseStep 4499783 = 6749675) B6749675
theorem B41585663 : Blo 1184409 41585663 := bstep (se 1 (by rfl) ⟨31189247, by rfl⟩ : syracuseStep 41585663 = 62378495) B62378495
theorem B25637107 : Blo 1184409 25637107 := bstep (se 1 (by rfl) ⟨19227830, by rfl⟩ : syracuseStep 25637107 = 38455661) B38455661
theorem B11399615 : Blo 1184409 11399615 := bstep (se 1 (by rfl) ⟨8549711, by rfl⟩ : syracuseStep 11399615 = 17099423) B17099423
theorem B1184511 : Blo 1184409 1184511 := bstep (se 1 (by rfl) ⟨888383, by rfl⟩ : syracuseStep 1184511 = 1776767) B1776767
theorem B2249527 : Blo 1184409 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B57627449 : Blo 1184409 57627449 := bstep (se 2 (by rfl) ⟨21610293, by rfl⟩ : syracuseStep 57627449 = 43220587) B43220587
theorem B1184703 : Blo 1184409 1184703 := bstep (se 1 (by rfl) ⟨888527, by rfl⟩ : syracuseStep 1184703 = 1777055) B1777055
theorem B1185439 : Blo 1184409 1185439 := bstep (se 1 (by rfl) ⟨889079, by rfl⟩ : syracuseStep 1185439 = 1778159) B1778159
theorem B1185663 : Blo 1184409 1185663 := bstep (se 1 (by rfl) ⟨889247, by rfl⟩ : syracuseStep 1185663 = 1778495) B1778495
theorem B1185787 : Blo 1184409 1185787 := bstep (se 1 (by rfl) ⟨889340, by rfl⟩ : syracuseStep 1185787 = 1778681) B1778681
theorem B6748535 : Blo 1184409 6748535 := bstep (se 1 (by rfl) ⟨5061401, by rfl⟩ : syracuseStep 6748535 = 10122803) B10122803
theorem B10123865 : Blo 1184409 10123865 := bstep (se 2 (by rfl) ⟨3796449, by rfl⟩ : syracuseStep 10123865 = 7592899) B7592899
theorem B2251547 : Blo 1184409 2251547 := bstep (se 1 (by rfl) ⟨1688660, by rfl⟩ : syracuseStep 2251547 = 3377321) B3377321
theorem B1334047 : Blo 1184409 1334047 := bstep (se 1 (by rfl) ⟨1000535, by rfl⟩ : syracuseStep 1334047 = 2001071) B2001071
theorem B6003881 : Blo 1184409 6003881 := bstep (se 2 (by rfl) ⟨2251455, by rfl⟩ : syracuseStep 6003881 = 4502911) B4502911
theorem B110895101 : Blo 1184409 110895101 := bstep (se 3 (by rfl) ⟨20792831, by rfl⟩ : syracuseStep 110895101 = 41585663) B41585663
theorem B1778729 : Blo 1184409 1778729 := bstep (se 2 (by rfl) ⟨667023, by rfl⟩ : syracuseStep 1778729 = 1334047) B1334047
theorem B2999369 : Blo 1184409 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B2999855 : Blo 1184409 2999855 := bstep (se 1 (by rfl) ⟨2249891, by rfl⟩ : syracuseStep 2999855 = 4499783) B4499783
theorem B4499023 : Blo 1184409 4499023 := bstep (se 1 (by rfl) ⟨3374267, by rfl⟩ : syracuseStep 4499023 = 6748535) B6748535
theorem B1501031 : Blo 1184409 1501031 := bstep (se 1 (by rfl) ⟨1125773, by rfl⟩ : syracuseStep 1501031 = 2251547) B2251547
theorem B4001021 : Blo 1184409 4001021 := bstep (se 3 (by rfl) ⟨750191, by rfl⟩ : syracuseStep 4001021 = 1500383) B1500383
theorem B16215871 : Blo 1184409 16215871 := bstep (se 1 (by rfl) ⟨12161903, by rfl⟩ : syracuseStep 16215871 = 24323807) B24323807
theorem B4002587 : Blo 1184409 4002587 := bstep (se 1 (by rfl) ⟨3001940, by rfl⟩ : syracuseStep 4002587 = 6003881) B6003881
theorem B7599743 : Blo 1184409 7599743 := bstep (se 1 (by rfl) ⟨5699807, by rfl⟩ : syracuseStep 7599743 = 11399615) B11399615
theorem B34182809 : Blo 1184409 34182809 := bstep (se 2 (by rfl) ⟨12818553, by rfl⟩ : syracuseStep 34182809 = 25637107) B25637107
theorem B6756007 : Blo 1184409 6756007 := bstep (se 1 (by rfl) ⟨5067005, by rfl⟩ : syracuseStep 6756007 = 10134011) B10134011
theorem B20526817 : Blo 1184409 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B38418299 : Blo 1184409 38418299 := bstep (se 1 (by rfl) ⟨28813724, by rfl⟩ : syracuseStep 38418299 = 57627449) B57627449
theorem B1185959 : Blo 1184409 1185959 := bstep (se 1 (by rfl) ⟨889469, by rfl⟩ : syracuseStep 1185959 = 1778939) B1778939
theorem B56236331 : Blo 1184409 56236331 := bstep (se 1 (by rfl) ⟨42177248, by rfl⟩ : syracuseStep 56236331 = 84354497) B84354497
theorem B1186303 : Blo 1184409 1186303 := bstep (se 1 (by rfl) ⟨889727, by rfl⟩ : syracuseStep 1186303 = 1779455) B1779455
theorem B19225295 : Blo 1184409 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B6749243 : Blo 1184409 6749243 := bstep (se 1 (by rfl) ⟨5061932, by rfl⟩ : syracuseStep 6749243 = 10123865) B10123865
theorem B1999579 : Blo 1184409 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B1999903 : Blo 1184409 1999903 := bstep (se 1 (by rfl) ⟨1499927, by rfl⟩ : syracuseStep 1999903 = 2999855) B2999855
theorem B4499495 : Blo 1184409 4499495 := bstep (se 1 (by rfl) ⟨3374621, by rfl⟩ : syracuseStep 4499495 = 6749243) B6749243
theorem B5998697 : Blo 1184409 5998697 := bstep (se 2 (by rfl) ⟨2249511, by rfl⟩ : syracuseStep 5998697 = 4499023) B4499023
theorem B21621161 : Blo 1184409 21621161 := bstep (se 2 (by rfl) ⟨8107935, by rfl⟩ : syracuseStep 21621161 = 16215871) B16215871
theorem B5066495 : Blo 1184409 5066495 := bstep (se 1 (by rfl) ⟨3799871, by rfl⟩ : syracuseStep 5066495 = 7599743) B7599743
theorem B25612199 : Blo 1184409 25612199 := bstep (se 1 (by rfl) ⟨19209149, by rfl⟩ : syracuseStep 25612199 = 38418299) B38418299
theorem B37490887 : Blo 1184409 37490887 := bstep (se 1 (by rfl) ⟨28118165, by rfl⟩ : syracuseStep 37490887 = 56236331) B56236331
theorem B12816863 : Blo 1184409 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B2667347 : Blo 1184409 2667347 := bstep (se 1 (by rfl) ⟨2000510, by rfl⟩ : syracuseStep 2667347 = 4001021) B4001021
theorem B9008009 : Blo 1184409 9008009 := bstep (se 2 (by rfl) ⟨3378003, by rfl⟩ : syracuseStep 9008009 = 6756007) B6756007
theorem B4002749 : Blo 1184409 4002749 := bstep (se 3 (by rfl) ⟨750515, by rfl⟩ : syracuseStep 4002749 = 1501031) B1501031
theorem B73930067 : Blo 1184409 73930067 := bstep (se 1 (by rfl) ⟨55447550, by rfl⟩ : syracuseStep 73930067 = 110895101) B110895101
theorem B2668391 : Blo 1184409 2668391 := bstep (se 1 (by rfl) ⟨2001293, by rfl⟩ : syracuseStep 2668391 = 4002587) B4002587
theorem B1185819 : Blo 1184409 1185819 := bstep (se 1 (by rfl) ⟨889364, by rfl⟩ : syracuseStep 1185819 = 1778729) B1778729
theorem B22788539 : Blo 1184409 22788539 := bstep (se 1 (by rfl) ⟨17091404, by rfl⟩ : syracuseStep 22788539 = 34182809) B34182809
theorem B27369089 : Blo 1184409 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B49987849 : Blo 1184409 49987849 := bstep (se 2 (by rfl) ⟨18745443, by rfl⟩ : syracuseStep 49987849 = 37490887) B37490887
theorem B8544575 : Blo 1184409 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B1778231 : Blo 1184409 1778231 := bstep (se 1 (by rfl) ⟨1333673, by rfl⟩ : syracuseStep 1778231 = 2667347) B2667347
theorem B6005339 : Blo 1184409 6005339 := bstep (se 1 (by rfl) ⟨4504004, by rfl⟩ : syracuseStep 6005339 = 9008009) B9008009
theorem B1778927 : Blo 1184409 1778927 := bstep (se 1 (by rfl) ⟨1334195, by rfl⟩ : syracuseStep 1778927 = 2668391) B2668391
theorem B2999663 : Blo 1184409 2999663 := bstep (se 1 (by rfl) ⟨2249747, by rfl⟩ : syracuseStep 2999663 = 4499495) B4499495
theorem B3999131 : Blo 1184409 3999131 := bstep (se 1 (by rfl) ⟨2999348, by rfl⟩ : syracuseStep 3999131 = 5998697) B5998697
theorem B18246059 : Blo 1184409 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B3377663 : Blo 1184409 3377663 := bstep (se 1 (by rfl) ⟨2533247, by rfl⟩ : syracuseStep 3377663 = 5066495) B5066495
theorem B17074799 : Blo 1184409 17074799 := bstep (se 1 (by rfl) ⟨12806099, by rfl⟩ : syracuseStep 17074799 = 25612199) B25612199
theorem B49286711 : Blo 1184409 49286711 := bstep (se 1 (by rfl) ⟨36965033, by rfl⟩ : syracuseStep 49286711 = 73930067) B73930067
theorem B2666105 : Blo 1184409 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B2666537 : Blo 1184409 2666537 := bstep (se 2 (by rfl) ⟨999951, by rfl⟩ : syracuseStep 2666537 = 1999903) B1999903
theorem B14414107 : Blo 1184409 14414107 := bstep (se 1 (by rfl) ⟨10810580, by rfl⟩ : syracuseStep 14414107 = 21621161) B21621161
theorem B15192359 : Blo 1184409 15192359 := bstep (se 1 (by rfl) ⟨11394269, by rfl⟩ : syracuseStep 15192359 = 22788539) B22788539
theorem B2668499 : Blo 1184409 2668499 := bstep (se 1 (by rfl) ⟨2001374, by rfl⟩ : syracuseStep 2668499 = 4002749) B4002749
theorem B1777691 : Blo 1184409 1777691 := bstep (se 1 (by rfl) ⟨1333268, by rfl⟩ : syracuseStep 1777691 = 2666537) B2666537
theorem B66650465 : Blo 1184409 66650465 := bstep (se 2 (by rfl) ⟨24993924, by rfl⟩ : syracuseStep 66650465 = 49987849) B49987849
theorem B19218809 : Blo 1184409 19218809 := bstep (se 2 (by rfl) ⟨7207053, by rfl⟩ : syracuseStep 19218809 = 14414107) B14414107
theorem B1999775 : Blo 1184409 1999775 := bstep (se 1 (by rfl) ⟨1499831, by rfl⟩ : syracuseStep 1999775 = 2999663) B2999663
theorem B1778999 : Blo 1184409 1778999 := bstep (se 1 (by rfl) ⟨1334249, by rfl⟩ : syracuseStep 1778999 = 2668499) B2668499
theorem B10128239 : Blo 1184409 10128239 := bstep (se 1 (by rfl) ⟨7596179, by rfl⟩ : syracuseStep 10128239 = 15192359) B15192359
theorem B22785533 : Blo 1184409 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B2666087 : Blo 1184409 2666087 := bstep (se 1 (by rfl) ⟨1999565, by rfl⟩ : syracuseStep 2666087 = 3999131) B3999131
theorem B11383199 : Blo 1184409 11383199 := bstep (se 1 (by rfl) ⟨8537399, by rfl⟩ : syracuseStep 11383199 = 17074799) B17074799
theorem B1185487 : Blo 1184409 1185487 := bstep (se 1 (by rfl) ⟨889115, by rfl⟩ : syracuseStep 1185487 = 1778231) B1778231
theorem B4003559 : Blo 1184409 4003559 := bstep (se 1 (by rfl) ⟨3002669, by rfl⟩ : syracuseStep 4003559 = 6005339) B6005339
theorem B1185951 : Blo 1184409 1185951 := bstep (se 1 (by rfl) ⟨889463, by rfl⟩ : syracuseStep 1185951 = 1778927) B1778927
theorem B12164039 : Blo 1184409 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B2251775 : Blo 1184409 2251775 := bstep (se 1 (by rfl) ⟨1688831, by rfl⟩ : syracuseStep 2251775 = 3377663) B3377663
theorem B32857807 : Blo 1184409 32857807 := bstep (se 1 (by rfl) ⟨24643355, by rfl⟩ : syracuseStep 32857807 = 49286711) B49286711
theorem B1777403 : Blo 1184409 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B177734573 : Blo 1184409 177734573 := bstep (se 3 (by rfl) ⟨33325232, by rfl⟩ : syracuseStep 177734573 = 66650465) B66650465
theorem B51250157 : Blo 1184409 51250157 := bstep (se 3 (by rfl) ⟨9609404, by rfl⟩ : syracuseStep 51250157 = 19218809) B19218809
theorem B6752159 : Blo 1184409 6752159 := bstep (se 1 (by rfl) ⟨5064119, by rfl⟩ : syracuseStep 6752159 = 10128239) B10128239
theorem B1501183 : Blo 1184409 1501183 := bstep (se 1 (by rfl) ⟨1125887, by rfl⟩ : syracuseStep 1501183 = 2251775) B2251775
theorem B15190355 : Blo 1184409 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B7588799 : Blo 1184409 7588799 := bstep (se 1 (by rfl) ⟨5691599, by rfl⟩ : syracuseStep 7588799 = 11383199) B11383199
theorem B1184935 : Blo 1184409 1184935 := bstep (se 1 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 1184935 = 1777403) B1777403
theorem B1185127 : Blo 1184409 1185127 := bstep (se 1 (by rfl) ⟨888845, by rfl⟩ : syracuseStep 1185127 = 1777691) B1777691
theorem B1333183 : Blo 1184409 1333183 := bstep (se 1 (by rfl) ⟨999887, by rfl⟩ : syracuseStep 1333183 = 1999775) B1999775
theorem B1185999 : Blo 1184409 1185999 := bstep (se 1 (by rfl) ⟨889499, by rfl⟩ : syracuseStep 1185999 = 1778999) B1778999
theorem B2669039 : Blo 1184409 2669039 := bstep (se 1 (by rfl) ⟨2001779, by rfl⟩ : syracuseStep 2669039 = 4003559) B4003559
theorem B8109359 : Blo 1184409 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B43810409 : Blo 1184409 43810409 := bstep (se 2 (by rfl) ⟨16428903, by rfl⟩ : syracuseStep 43810409 = 32857807) B32857807
theorem B1777391 : Blo 1184409 1777391 := bstep (se 1 (by rfl) ⟨1333043, by rfl⟩ : syracuseStep 1777391 = 2666087) B2666087
theorem B118489715 : Blo 1184409 118489715 := bstep (se 1 (by rfl) ⟨88867286, by rfl⟩ : syracuseStep 118489715 = 177734573) B177734573
theorem B10126903 : Blo 1184409 10126903 := bstep (se 1 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 10126903 = 15190355) B15190355
theorem B116827757 : Blo 1184409 116827757 := bstep (se 3 (by rfl) ⟨21905204, by rfl⟩ : syracuseStep 116827757 = 43810409) B43810409
theorem B1779359 : Blo 1184409 1779359 := bstep (se 1 (by rfl) ⟨1334519, by rfl⟩ : syracuseStep 1779359 = 2669039) B2669039
theorem B2001577 : Blo 1184409 2001577 := bstep (se 2 (by rfl) ⟨750591, by rfl⟩ : syracuseStep 2001577 = 1501183) B1501183
theorem B4501439 : Blo 1184409 4501439 := bstep (se 1 (by rfl) ⟨3376079, by rfl⟩ : syracuseStep 4501439 = 6752159) B6752159
theorem B5059199 : Blo 1184409 5059199 := bstep (se 1 (by rfl) ⟨3794399, by rfl⟩ : syracuseStep 5059199 = 7588799) B7588799
theorem B1184927 : Blo 1184409 1184927 := bstep (se 1 (by rfl) ⟨888695, by rfl⟩ : syracuseStep 1184927 = 1777391) B1777391
theorem B34166771 : Blo 1184409 34166771 := bstep (se 1 (by rfl) ⟨25625078, by rfl⟩ : syracuseStep 34166771 = 51250157) B51250157
theorem B5406239 : Blo 1184409 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B1777577 : Blo 1184409 1777577 := bstep (se 2 (by rfl) ⟨666591, by rfl⟩ : syracuseStep 1777577 = 1333183) B1333183
theorem B13502537 : Blo 1184409 13502537 := bstep (se 2 (by rfl) ⟨5063451, by rfl⟩ : syracuseStep 13502537 = 10126903) B10126903
theorem B3000959 : Blo 1184409 3000959 := bstep (se 1 (by rfl) ⟨2250719, by rfl⟩ : syracuseStep 3000959 = 4501439) B4501439
theorem B77885171 : Blo 1184409 77885171 := bstep (se 1 (by rfl) ⟨58413878, by rfl⟩ : syracuseStep 77885171 = 116827757) B116827757
theorem B22777847 : Blo 1184409 22777847 := bstep (se 1 (by rfl) ⟨17083385, by rfl⟩ : syracuseStep 22777847 = 34166771) B34166771
theorem B1185051 : Blo 1184409 1185051 := bstep (se 1 (by rfl) ⟨888788, by rfl⟩ : syracuseStep 1185051 = 1777577) B1777577
theorem B78993143 : Blo 1184409 78993143 := bstep (se 1 (by rfl) ⟨59244857, by rfl⟩ : syracuseStep 78993143 = 118489715) B118489715
theorem B3372799 : Blo 1184409 3372799 := bstep (se 1 (by rfl) ⟨2529599, by rfl⟩ : syracuseStep 3372799 = 5059199) B5059199
theorem B2668769 : Blo 1184409 2668769 := bstep (se 2 (by rfl) ⟨1000788, by rfl⟩ : syracuseStep 2668769 = 2001577) B2001577
theorem B1186239 : Blo 1184409 1186239 := bstep (se 1 (by rfl) ⟨889679, by rfl⟩ : syracuseStep 1186239 = 1779359) B1779359
theorem B3604159 : Blo 1184409 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B1779179 : Blo 1184409 1779179 := bstep (se 1 (by rfl) ⟨1334384, by rfl⟩ : syracuseStep 1779179 = 2668769) B2668769
theorem B2000639 : Blo 1184409 2000639 := bstep (se 1 (by rfl) ⟨1500479, by rfl⟩ : syracuseStep 2000639 = 3000959) B3000959
theorem B51923447 : Blo 1184409 51923447 := bstep (se 1 (by rfl) ⟨38942585, by rfl⟩ : syracuseStep 51923447 = 77885171) B77885171
theorem B19222181 : Blo 1184409 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B52662095 : Blo 1184409 52662095 := bstep (se 1 (by rfl) ⟨39496571, by rfl⟩ : syracuseStep 52662095 = 78993143) B78993143
theorem B15185231 : Blo 1184409 15185231 := bstep (se 1 (by rfl) ⟨11388923, by rfl⟩ : syracuseStep 15185231 = 22777847) B22777847
theorem B9001691 : Blo 1184409 9001691 := bstep (se 1 (by rfl) ⟨6751268, by rfl⟩ : syracuseStep 9001691 = 13502537) B13502537
theorem B4497065 : Blo 1184409 4497065 := bstep (se 2 (by rfl) ⟨1686399, by rfl⟩ : syracuseStep 4497065 = 3372799) B3372799
theorem B12814787 : Blo 1184409 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B34615631 : Blo 1184409 34615631 := bstep (se 1 (by rfl) ⟨25961723, by rfl⟩ : syracuseStep 34615631 = 51923447) B51923447
theorem B6001127 : Blo 1184409 6001127 := bstep (se 1 (by rfl) ⟨4500845, by rfl⟩ : syracuseStep 6001127 = 9001691) B9001691
theorem B35108063 : Blo 1184409 35108063 := bstep (se 1 (by rfl) ⟨26331047, by rfl⟩ : syracuseStep 35108063 = 52662095) B52662095
theorem B10123487 : Blo 1184409 10123487 := bstep (se 1 (by rfl) ⟨7592615, by rfl⟩ : syracuseStep 10123487 = 15185231) B15185231
theorem B1186119 : Blo 1184409 1186119 := bstep (se 1 (by rfl) ⟨889589, by rfl⟩ : syracuseStep 1186119 = 1779179) B1779179
theorem B1333759 : Blo 1184409 1333759 := bstep (se 1 (by rfl) ⟨1000319, by rfl⟩ : syracuseStep 1333759 = 2000639) B2000639
theorem B2998043 : Blo 1184409 2998043 := bstep (se 1 (by rfl) ⟨2248532, by rfl⟩ : syracuseStep 2998043 = 4497065) B4497065
theorem B1778345 : Blo 1184409 1778345 := bstep (se 2 (by rfl) ⟨666879, by rfl⟩ : syracuseStep 1778345 = 1333759) B1333759
theorem B23405375 : Blo 1184409 23405375 := bstep (se 1 (by rfl) ⟨17554031, by rfl⟩ : syracuseStep 23405375 = 35108063) B35108063
theorem B92308349 : Blo 1184409 92308349 := bstep (se 3 (by rfl) ⟨17307815, by rfl⟩ : syracuseStep 92308349 = 34615631) B34615631
theorem B4000751 : Blo 1184409 4000751 := bstep (se 1 (by rfl) ⟨3000563, by rfl⟩ : syracuseStep 4000751 = 6001127) B6001127
theorem B34172765 : Blo 1184409 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B6748991 : Blo 1184409 6748991 := bstep (se 1 (by rfl) ⟨5061743, by rfl⟩ : syracuseStep 6748991 = 10123487) B10123487
theorem B1998695 : Blo 1184409 1998695 := bstep (se 1 (by rfl) ⟨1499021, by rfl⟩ : syracuseStep 1998695 = 2998043) B2998043
theorem B61538899 : Blo 1184409 61538899 := bstep (se 1 (by rfl) ⟨46154174, by rfl⟩ : syracuseStep 61538899 = 92308349) B92308349
theorem B4499327 : Blo 1184409 4499327 := bstep (se 1 (by rfl) ⟨3374495, by rfl⟩ : syracuseStep 4499327 = 6748991) B6748991
theorem B2667167 : Blo 1184409 2667167 := bstep (se 1 (by rfl) ⟨2000375, by rfl⟩ : syracuseStep 2667167 = 4000751) B4000751
theorem B1332463 : Blo 1184409 1332463 := bstep (se 1 (by rfl) ⟨999347, by rfl⟩ : syracuseStep 1332463 = 1998695) B1998695
theorem B1185563 : Blo 1184409 1185563 := bstep (se 1 (by rfl) ⟨889172, by rfl⟩ : syracuseStep 1185563 = 1778345) B1778345
theorem B62414333 : Blo 1184409 62414333 := bstep (se 3 (by rfl) ⟨11702687, by rfl⟩ : syracuseStep 62414333 = 23405375) B23405375
theorem B22781843 : Blo 1184409 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B1778111 : Blo 1184409 1778111 := bstep (se 1 (by rfl) ⟨1333583, by rfl⟩ : syracuseStep 1778111 = 2667167) B2667167
theorem B82051865 : Blo 1184409 82051865 := bstep (se 2 (by rfl) ⟨30769449, by rfl⟩ : syracuseStep 82051865 = 61538899) B61538899
theorem B2999551 : Blo 1184409 2999551 := bstep (se 1 (by rfl) ⟨2249663, by rfl⟩ : syracuseStep 2999551 = 4499327) B4499327
theorem B41609555 : Blo 1184409 41609555 := bstep (se 1 (by rfl) ⟨31207166, by rfl⟩ : syracuseStep 41609555 = 62414333) B62414333
theorem B1776617 : Blo 1184409 1776617 := bstep (se 2 (by rfl) ⟨666231, by rfl⟩ : syracuseStep 1776617 = 1332463) B1332463
theorem B15187895 : Blo 1184409 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B27739703 : Blo 1184409 27739703 := bstep (se 1 (by rfl) ⟨20804777, by rfl⟩ : syracuseStep 27739703 = 41609555) B41609555
theorem B3999401 : Blo 1184409 3999401 := bstep (se 2 (by rfl) ⟨1499775, by rfl⟩ : syracuseStep 3999401 = 2999551) B2999551
theorem B54701243 : Blo 1184409 54701243 := bstep (se 1 (by rfl) ⟨41025932, by rfl⟩ : syracuseStep 54701243 = 82051865) B82051865
theorem B1184411 : Blo 1184409 1184411 := bstep (se 1 (by rfl) ⟨888308, by rfl⟩ : syracuseStep 1184411 = 1776617) B1776617
theorem B1185407 : Blo 1184409 1185407 := bstep (se 1 (by rfl) ⟨889055, by rfl⟩ : syracuseStep 1185407 = 1778111) B1778111
theorem B10125263 : Blo 1184409 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B2666267 : Blo 1184409 2666267 := bstep (se 1 (by rfl) ⟨1999700, by rfl⟩ : syracuseStep 2666267 = 3999401) B3999401
theorem B36467495 : Blo 1184409 36467495 := bstep (se 1 (by rfl) ⟨27350621, by rfl⟩ : syracuseStep 36467495 = 54701243) B54701243
theorem B73972541 : Blo 1184409 73972541 := bstep (se 3 (by rfl) ⟨13869851, by rfl⟩ : syracuseStep 73972541 = 27739703) B27739703
theorem B6750175 : Blo 1184409 6750175 := bstep (se 1 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 6750175 = 10125263) B10125263
theorem B197260109 : Blo 1184409 197260109 := bstep (se 3 (by rfl) ⟨36986270, by rfl⟩ : syracuseStep 197260109 = 73972541) B73972541
theorem B9000233 : Blo 1184409 9000233 := bstep (se 2 (by rfl) ⟨3375087, by rfl⟩ : syracuseStep 9000233 = 6750175) B6750175
theorem B24311663 : Blo 1184409 24311663 := bstep (se 1 (by rfl) ⟨18233747, by rfl⟩ : syracuseStep 24311663 = 36467495) B36467495
theorem B1777511 : Blo 1184409 1777511 := bstep (se 1 (by rfl) ⟨1333133, by rfl⟩ : syracuseStep 1777511 = 2666267) B2666267
theorem B131506739 : Blo 1184409 131506739 := bstep (se 1 (by rfl) ⟨98630054, by rfl⟩ : syracuseStep 131506739 = 197260109) B197260109
theorem B6000155 : Blo 1184409 6000155 := bstep (se 1 (by rfl) ⟨4500116, by rfl⟩ : syracuseStep 6000155 = 9000233) B9000233
theorem B16207775 : Blo 1184409 16207775 := bstep (se 1 (by rfl) ⟨12155831, by rfl⟩ : syracuseStep 16207775 = 24311663) B24311663
theorem B1185007 : Blo 1184409 1185007 := bstep (se 1 (by rfl) ⟨888755, by rfl⟩ : syracuseStep 1185007 = 1777511) B1777511
theorem B87671159 : Blo 1184409 87671159 := bstep (se 1 (by rfl) ⟨65753369, by rfl⟩ : syracuseStep 87671159 = 131506739) B131506739
theorem B4000103 : Blo 1184409 4000103 := bstep (se 1 (by rfl) ⟨3000077, by rfl⟩ : syracuseStep 4000103 = 6000155) B6000155
theorem B10805183 : Blo 1184409 10805183 := bstep (se 1 (by rfl) ⟨8103887, by rfl⟩ : syracuseStep 10805183 = 16207775) B16207775
theorem B7203455 : Blo 1184409 7203455 := bstep (se 1 (by rfl) ⟨5402591, by rfl⟩ : syracuseStep 7203455 = 10805183) B10805183
theorem B2666735 : Blo 1184409 2666735 := bstep (se 1 (by rfl) ⟨2000051, by rfl⟩ : syracuseStep 2666735 = 4000103) B4000103
theorem B58447439 : Blo 1184409 58447439 := bstep (se 1 (by rfl) ⟨43835579, by rfl⟩ : syracuseStep 58447439 = 87671159) B87671159
theorem B1777823 : Blo 1184409 1777823 := bstep (se 1 (by rfl) ⟨1333367, by rfl⟩ : syracuseStep 1777823 = 2666735) B2666735
theorem B4802303 : Blo 1184409 4802303 := bstep (se 1 (by rfl) ⟨3601727, by rfl⟩ : syracuseStep 4802303 = 7203455) B7203455
theorem B38964959 : Blo 1184409 38964959 := bstep (se 1 (by rfl) ⟨29223719, by rfl⟩ : syracuseStep 38964959 = 58447439) B58447439
theorem B1185215 : Blo 1184409 1185215 := bstep (se 1 (by rfl) ⟨888911, by rfl⟩ : syracuseStep 1185215 = 1777823) B1777823
theorem B3201535 : Blo 1184409 3201535 := bstep (se 1 (by rfl) ⟨2401151, by rfl⟩ : syracuseStep 3201535 = 4802303) B4802303
theorem B25976639 : Blo 1184409 25976639 := bstep (se 1 (by rfl) ⟨19482479, by rfl⟩ : syracuseStep 25976639 = 38964959) B38964959
theorem B4268713 : Blo 1184409 4268713 := bstep (se 2 (by rfl) ⟨1600767, by rfl⟩ : syracuseStep 4268713 = 3201535) B3201535
theorem B69271037 : Blo 1184409 69271037 := bstep (se 3 (by rfl) ⟨12988319, by rfl⟩ : syracuseStep 69271037 = 25976639) B25976639
theorem B46180691 : Blo 1184409 46180691 := bstep (se 1 (by rfl) ⟨34635518, by rfl⟩ : syracuseStep 46180691 = 69271037) B69271037
theorem B5691617 : Blo 1184409 5691617 := bstep (se 2 (by rfl) ⟨2134356, by rfl⟩ : syracuseStep 5691617 = 4268713) B4268713
theorem B3794411 : Blo 1184409 3794411 := bstep (se 1 (by rfl) ⟨2845808, by rfl⟩ : syracuseStep 3794411 = 5691617) B5691617
theorem B30787127 : Blo 1184409 30787127 := bstep (se 1 (by rfl) ⟨23090345, by rfl⟩ : syracuseStep 30787127 = 46180691) B46180691
theorem B10118429 : Blo 1184409 10118429 := bstep (se 3 (by rfl) ⟨1897205, by rfl⟩ : syracuseStep 10118429 = 3794411) B3794411
theorem B20524751 : Blo 1184409 20524751 := bstep (se 1 (by rfl) ⟨15393563, by rfl⟩ : syracuseStep 20524751 = 30787127) B30787127
theorem B13683167 : Blo 1184409 13683167 := bstep (se 1 (by rfl) ⟨10262375, by rfl⟩ : syracuseStep 13683167 = 20524751) B20524751
theorem B6745619 : Blo 1184409 6745619 := bstep (se 1 (by rfl) ⟨5059214, by rfl⟩ : syracuseStep 6745619 = 10118429) B10118429
theorem B9122111 : Blo 1184409 9122111 := bstep (se 1 (by rfl) ⟨6841583, by rfl⟩ : syracuseStep 9122111 = 13683167) B13683167
theorem B4497079 : Blo 1184409 4497079 := bstep (se 1 (by rfl) ⟨3372809, by rfl⟩ : syracuseStep 4497079 = 6745619) B6745619
theorem B6081407 : Blo 1184409 6081407 := bstep (se 1 (by rfl) ⟨4561055, by rfl⟩ : syracuseStep 6081407 = 9122111) B9122111
theorem B5996105 : Blo 1184409 5996105 := bstep (se 2 (by rfl) ⟨2248539, by rfl⟩ : syracuseStep 5996105 = 4497079) B4497079
theorem B4054271 : Blo 1184409 4054271 := bstep (se 1 (by rfl) ⟨3040703, by rfl⟩ : syracuseStep 4054271 = 6081407) B6081407
theorem B3997403 : Blo 1184409 3997403 := bstep (se 1 (by rfl) ⟨2998052, by rfl⟩ : syracuseStep 3997403 = 5996105) B5996105
theorem B2664935 : Blo 1184409 2664935 := bstep (se 1 (by rfl) ⟨1998701, by rfl⟩ : syracuseStep 2664935 = 3997403) B3997403
theorem B10811389 : Blo 1184409 10811389 := bstep (se 3 (by rfl) ⟨2027135, by rfl⟩ : syracuseStep 10811389 = 4054271) B4054271
theorem B14415185 : Blo 1184409 14415185 := bstep (se 2 (by rfl) ⟨5405694, by rfl⟩ : syracuseStep 14415185 = 10811389) B10811389
theorem B1776623 : Blo 1184409 1776623 := bstep (se 1 (by rfl) ⟨1332467, by rfl⟩ : syracuseStep 1776623 = 2664935) B2664935
theorem B9610123 : Blo 1184409 9610123 := bstep (se 1 (by rfl) ⟨7207592, by rfl⟩ : syracuseStep 9610123 = 14415185) B14415185
theorem B1184415 : Blo 1184409 1184415 := bstep (se 1 (by rfl) ⟨888311, by rfl⟩ : syracuseStep 1184415 = 1776623) B1776623
theorem B12813497 : Blo 1184409 12813497 := bstep (se 2 (by rfl) ⟨4805061, by rfl⟩ : syracuseStep 12813497 = 9610123) B9610123
theorem B8542331 : Blo 1184409 8542331 := bstep (se 1 (by rfl) ⟨6406748, by rfl⟩ : syracuseStep 8542331 = 12813497) B12813497
theorem B5694887 : Blo 1184409 5694887 := bstep (se 1 (by rfl) ⟨4271165, by rfl⟩ : syracuseStep 5694887 = 8542331) B8542331
theorem B3796591 : Blo 1184409 3796591 := bstep (se 1 (by rfl) ⟨2847443, by rfl⟩ : syracuseStep 3796591 = 5694887) B5694887
theorem B5062121 : Blo 1184409 5062121 := bstep (se 2 (by rfl) ⟨1898295, by rfl⟩ : syracuseStep 5062121 = 3796591) B3796591
theorem B3374747 : Blo 1184409 3374747 := bstep (se 1 (by rfl) ⟨2531060, by rfl⟩ : syracuseStep 3374747 = 5062121) B5062121
theorem B2249831 : Blo 1184409 2249831 := bstep (se 1 (by rfl) ⟨1687373, by rfl⟩ : syracuseStep 2249831 = 3374747) B3374747
theorem B1499887 : Blo 1184409 1499887 := bstep (se 1 (by rfl) ⟨1124915, by rfl⟩ : syracuseStep 1499887 = 2249831) B2249831
theorem B1999849 : Blo 1184409 1999849 := bstep (se 2 (by rfl) ⟨749943, by rfl⟩ : syracuseStep 1999849 = 1499887) B1499887
theorem B2666465 : Blo 1184409 2666465 := bstep (se 2 (by rfl) ⟨999924, by rfl⟩ : syracuseStep 2666465 = 1999849) B1999849
theorem B1777643 : Blo 1184409 1777643 := bstep (se 1 (by rfl) ⟨1333232, by rfl⟩ : syracuseStep 1777643 = 2666465) B2666465
theorem B1185095 : Blo 1184409 1185095 := bstep (se 1 (by rfl) ⟨888821, by rfl⟩ : syracuseStep 1185095 = 1777643) B1777643

theorem C0 (j : ℕ) (h1 : 296102 ≤ j) (h2 : j ≤ 296601) : Blo 1184409 (4 * j + 3) := by
  interval_cases j
  · exact B1184411
  · exact B1184415
  · exact B1184419
  · exact B1184423
  · exact B1184427
  · exact B1184431
  · exact B1184435
  · exact B1184439
  · exact B1184443
  · exact B1184447
  · exact B1184451
  · exact B1184455
  · exact B1184459
  · exact B1184463
  · exact B1184467
  · exact B1184471
  · exact B1184475
  · exact B1184479
  · exact B1184483
  · exact B1184487
  · exact B1184491
  · exact B1184495
  · exact B1184499
  · exact B1184503
  · exact B1184507
  · exact B1184511
  · exact B1184515
  · exact B1184519
  · exact B1184523
  · exact B1184527
  · exact B1184531
  · exact B1184535
  · exact B1184539
  · exact B1184543
  · exact B1184547
  · exact B1184551
  · exact B1184555
  · exact B1184559
  · exact B1184563
  · exact B1184567
  · exact B1184571
  · exact B1184575
  · exact B1184579
  · exact B1184583
  · exact B1184587
  · exact B1184591
  · exact B1184595
  · exact B1184599
  · exact B1184603
  · exact B1184607
  · exact B1184611
  · exact B1184615
  · exact B1184619
  · exact B1184623
  · exact B1184627
  · exact B1184631
  · exact B1184635
  · exact B1184639
  · exact B1184643
  · exact B1184647
  · exact B1184651
  · exact B1184655
  · exact B1184659
  · exact B1184663
  · exact B1184667
  · exact B1184671
  · exact B1184675
  · exact B1184679
  · exact B1184683
  · exact B1184687
  · exact B1184691
  · exact B1184695
  · exact B1184699
  · exact B1184703
  · exact B1184707
  · exact B1184711
  · exact B1184715
  · exact B1184719
  · exact B1184723
  · exact B1184727
  · exact B1184731
  · exact B1184735
  · exact B1184739
  · exact B1184743
  · exact B1184747
  · exact B1184751
  · exact B1184755
  · exact B1184759
  · exact B1184763
  · exact B1184767
  · exact B1184771
  · exact B1184775
  · exact B1184779
  · exact B1184783
  · exact B1184787
  · exact B1184791
  · exact B1184795
  · exact B1184799
  · exact B1184803
  · exact B1184807
  · exact B1184811
  · exact B1184815
  · exact B1184819
  · exact B1184823
  · exact B1184827
  · exact B1184831
  · exact B1184835
  · exact B1184839
  · exact B1184843
  · exact B1184847
  · exact B1184851
  · exact B1184855
  · exact B1184859
  · exact B1184863
  · exact B1184867
  · exact B1184871
  · exact B1184875
  · exact B1184879
  · exact B1184883
  · exact B1184887
  · exact B1184891
  · exact B1184895
  · exact B1184899
  · exact B1184903
  · exact B1184907
  · exact B1184911
  · exact B1184915
  · exact B1184919
  · exact B1184923
  · exact B1184927
  · exact B1184931
  · exact B1184935
  · exact B1184939
  · exact B1184943
  · exact B1184947
  · exact B1184951
  · exact B1184955
  · exact B1184959
  · exact B1184963
  · exact B1184967
  · exact B1184971
  · exact B1184975
  · exact B1184979
  · exact B1184983
  · exact B1184987
  · exact B1184991
  · exact B1184995
  · exact B1184999
  · exact B1185003
  · exact B1185007
  · exact B1185011
  · exact B1185015
  · exact B1185019
  · exact B1185023
  · exact B1185027
  · exact B1185031
  · exact B1185035
  · exact B1185039
  · exact B1185043
  · exact B1185047
  · exact B1185051
  · exact B1185055
  · exact B1185059
  · exact B1185063
  · exact B1185067
  · exact B1185071
  · exact B1185075
  · exact B1185079
  · exact B1185083
  · exact B1185087
  · exact B1185091
  · exact B1185095
  · exact B1185099
  · exact B1185103
  · exact B1185107
  · exact B1185111
  · exact B1185115
  · exact B1185119
  · exact B1185123
  · exact B1185127
  · exact B1185131
  · exact B1185135
  · exact B1185139
  · exact B1185143
  · exact B1185147
  · exact B1185151
  · exact B1185155
  · exact B1185159
  · exact B1185163
  · exact B1185167
  · exact B1185171
  · exact B1185175
  · exact B1185179
  · exact B1185183
  · exact B1185187
  · exact B1185191
  · exact B1185195
  · exact B1185199
  · exact B1185203
  · exact B1185207
  · exact B1185211
  · exact B1185215
  · exact B1185219
  · exact B1185223
  · exact B1185227
  · exact B1185231
  · exact B1185235
  · exact B1185239
  · exact B1185243
  · exact B1185247
  · exact B1185251
  · exact B1185255
  · exact B1185259
  · exact B1185263
  · exact B1185267
  · exact B1185271
  · exact B1185275
  · exact B1185279
  · exact B1185283
  · exact B1185287
  · exact B1185291
  · exact B1185295
  · exact B1185299
  · exact B1185303
  · exact B1185307
  · exact B1185311
  · exact B1185315
  · exact B1185319
  · exact B1185323
  · exact B1185327
  · exact B1185331
  · exact B1185335
  · exact B1185339
  · exact B1185343
  · exact B1185347
  · exact B1185351
  · exact B1185355
  · exact B1185359
  · exact B1185363
  · exact B1185367
  · exact B1185371
  · exact B1185375
  · exact B1185379
  · exact B1185383
  · exact B1185387
  · exact B1185391
  · exact B1185395
  · exact B1185399
  · exact B1185403
  · exact B1185407
  · exact B1185411
  · exact B1185415
  · exact B1185419
  · exact B1185423
  · exact B1185427
  · exact B1185431
  · exact B1185435
  · exact B1185439
  · exact B1185443
  · exact B1185447
  · exact B1185451
  · exact B1185455
  · exact B1185459
  · exact B1185463
  · exact B1185467
  · exact B1185471
  · exact B1185475
  · exact B1185479
  · exact B1185483
  · exact B1185487
  · exact B1185491
  · exact B1185495
  · exact B1185499
  · exact B1185503
  · exact B1185507
  · exact B1185511
  · exact B1185515
  · exact B1185519
  · exact B1185523
  · exact B1185527
  · exact B1185531
  · exact B1185535
  · exact B1185539
  · exact B1185543
  · exact B1185547
  · exact B1185551
  · exact B1185555
  · exact B1185559
  · exact B1185563
  · exact B1185567
  · exact B1185571
  · exact B1185575
  · exact B1185579
  · exact B1185583
  · exact B1185587
  · exact B1185591
  · exact B1185595
  · exact B1185599
  · exact B1185603
  · exact B1185607
  · exact B1185611
  · exact B1185615
  · exact B1185619
  · exact B1185623
  · exact B1185627
  · exact B1185631
  · exact B1185635
  · exact B1185639
  · exact B1185643
  · exact B1185647
  · exact B1185651
  · exact B1185655
  · exact B1185659
  · exact B1185663
  · exact B1185667
  · exact B1185671
  · exact B1185675
  · exact B1185679
  · exact B1185683
  · exact B1185687
  · exact B1185691
  · exact B1185695
  · exact B1185699
  · exact B1185703
  · exact B1185707
  · exact B1185711
  · exact B1185715
  · exact B1185719
  · exact B1185723
  · exact B1185727
  · exact B1185731
  · exact B1185735
  · exact B1185739
  · exact B1185743
  · exact B1185747
  · exact B1185751
  · exact B1185755
  · exact B1185759
  · exact B1185763
  · exact B1185767
  · exact B1185771
  · exact B1185775
  · exact B1185779
  · exact B1185783
  · exact B1185787
  · exact B1185791
  · exact B1185795
  · exact B1185799
  · exact B1185803
  · exact B1185807
  · exact B1185811
  · exact B1185815
  · exact B1185819
  · exact B1185823
  · exact B1185827
  · exact B1185831
  · exact B1185835
  · exact B1185839
  · exact B1185843
  · exact B1185847
  · exact B1185851
  · exact B1185855
  · exact B1185859
  · exact B1185863
  · exact B1185867
  · exact B1185871
  · exact B1185875
  · exact B1185879
  · exact B1185883
  · exact B1185887
  · exact B1185891
  · exact B1185895
  · exact B1185899
  · exact B1185903
  · exact B1185907
  · exact B1185911
  · exact B1185915
  · exact B1185919
  · exact B1185923
  · exact B1185927
  · exact B1185931
  · exact B1185935
  · exact B1185939
  · exact B1185943
  · exact B1185947
  · exact B1185951
  · exact B1185955
  · exact B1185959
  · exact B1185963
  · exact B1185967
  · exact B1185971
  · exact B1185975
  · exact B1185979
  · exact B1185983
  · exact B1185987
  · exact B1185991
  · exact B1185995
  · exact B1185999
  · exact B1186003
  · exact B1186007
  · exact B1186011
  · exact B1186015
  · exact B1186019
  · exact B1186023
  · exact B1186027
  · exact B1186031
  · exact B1186035
  · exact B1186039
  · exact B1186043
  · exact B1186047
  · exact B1186051
  · exact B1186055
  · exact B1186059
  · exact B1186063
  · exact B1186067
  · exact B1186071
  · exact B1186075
  · exact B1186079
  · exact B1186083
  · exact B1186087
  · exact B1186091
  · exact B1186095
  · exact B1186099
  · exact B1186103
  · exact B1186107
  · exact B1186111
  · exact B1186115
  · exact B1186119
  · exact B1186123
  · exact B1186127
  · exact B1186131
  · exact B1186135
  · exact B1186139
  · exact B1186143
  · exact B1186147
  · exact B1186151
  · exact B1186155
  · exact B1186159
  · exact B1186163
  · exact B1186167
  · exact B1186171
  · exact B1186175
  · exact B1186179
  · exact B1186183
  · exact B1186187
  · exact B1186191
  · exact B1186195
  · exact B1186199
  · exact B1186203
  · exact B1186207
  · exact B1186211
  · exact B1186215
  · exact B1186219
  · exact B1186223
  · exact B1186227
  · exact B1186231
  · exact B1186235
  · exact B1186239
  · exact B1186243
  · exact B1186247
  · exact B1186251
  · exact B1186255
  · exact B1186259
  · exact B1186263
  · exact B1186267
  · exact B1186271
  · exact B1186275
  · exact B1186279
  · exact B1186283
  · exact B1186287
  · exact B1186291
  · exact B1186295
  · exact B1186299
  · exact B1186303
  · exact B1186307
  · exact B1186311
  · exact B1186315
  · exact B1186319
  · exact B1186323
  · exact B1186327
  · exact B1186331
  · exact B1186335
  · exact B1186339
  · exact B1186343
  · exact B1186347
  · exact B1186351
  · exact B1186355
  · exact B1186359
  · exact B1186363
  · exact B1186367
  · exact B1186371
  · exact B1186375
  · exact B1186379
  · exact B1186383
  · exact B1186387
  · exact B1186391
  · exact B1186395
  · exact B1186399
  · exact B1186403
  · exact B1186407

theorem solution (m : ℕ) (hlo : 1184409 ≤ m) (hhi : m ≤ 1186409) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 296102 ≤ j := by omega
    have hj2 : j ≤ 296601 := by omega
    have hb : Blo 1184409 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
