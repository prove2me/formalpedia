-- Prove2me | solution 1 for syracuse_descends_range_822348_826348
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:45.603001+00:00
-- url     : https://prove2.me/submissions/48c4fe5d-29a7-4bd9-9aee-a926dfcccc04

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


theorem B4227349 : Blo 822348 4227349 := bbase (se 6 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 4227349 = 198157) (by norm_num)
theorem B2785589 : Blo 822348 2785589 := bbase (se 5 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 2785589 = 261149) (by norm_num)
theorem B1114501 : Blo 822348 1114501 := bbase (se 4 (by rfl) ⟨104484, by rfl⟩ : syracuseStep 1114501 = 208969) (by norm_num)
theorem B1671605 : Blo 822348 1671605 := bbase (se 5 (by rfl) ⟨78356, by rfl⟩ : syracuseStep 1671605 = 156713) (by norm_num)
theorem B10584533 : Blo 822348 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B1409501 : Blo 822348 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B1671653 : Blo 822348 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B1114717 : Blo 822348 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B1508053 : Blo 822348 1508053 := bbase (se 7 (by rfl) ⟨17672, by rfl⟩ : syracuseStep 1508053 = 35345) (by norm_num)
theorem B2786021 : Blo 822348 2786021 := bbase (se 4 (by rfl) ⟨261189, by rfl⟩ : syracuseStep 2786021 = 522379) (by norm_num)
theorem B1114997 : Blo 822348 1114997 := bbase (se 5 (by rfl) ⟨52265, by rfl⟩ : syracuseStep 1114997 = 104531) (by norm_num)
theorem B1606541 : Blo 822348 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B2786453 : Blo 822348 2786453 := bbase (se 6 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 2786453 = 130615) (by norm_num)
theorem B3802405 : Blo 822348 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B2786885 : Blo 822348 2786885 := bbase (se 4 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 2786885 = 522541) (by norm_num)
theorem B9537173 : Blo 822348 9537173 := bbase (se 6 (by rfl) ⟨223527, by rfl⟩ : syracuseStep 9537173 = 447055) (by norm_num)
theorem B4163237 : Blo 822348 4163237 := bbase (se 4 (by rfl) ⟨390303, by rfl⟩ : syracuseStep 4163237 = 780607) (by norm_num)
theorem B2787317 : Blo 822348 2787317 := bbase (se 5 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 2787317 = 261311) (by norm_num)
theorem B2820149 : Blo 822348 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B2787749 : Blo 822348 2787749 := bbase (se 4 (by rfl) ⟨261351, by rfl⟩ : syracuseStep 2787749 = 522703) (by norm_num)
theorem B1411525 : Blo 822348 1411525 := bbase (se 4 (by rfl) ⟨132330, by rfl⟩ : syracuseStep 1411525 = 264661) (by norm_num)
theorem B3574277 : Blo 822348 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B2231077 : Blo 822348 2231077 := bbase (se 4 (by rfl) ⟨209163, by rfl⟩ : syracuseStep 2231077 = 418327) (by norm_num)
theorem B2788181 : Blo 822348 2788181 := bbase (se 9 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 2788181 = 16337) (by norm_num)
theorem B4164533 : Blo 822348 4164533 := bbase (se 5 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 4164533 = 390425) (by norm_num)
theorem B2788613 : Blo 822348 2788613 := bbase (se 4 (by rfl) ⟨261432, by rfl⟩ : syracuseStep 2788613 = 522865) (by norm_num)
theorem B1674589 : Blo 822348 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B7048565 : Blo 822348 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B1413085 : Blo 822348 1413085 := bbase (se 3 (by rfl) ⟨264953, by rfl⟩ : syracuseStep 1413085 = 529907) (by norm_num)
theorem B21139541 : Blo 822348 21139541 := bbase (se 8 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 21139541 = 247729) (by norm_num)
theorem B3969125 : Blo 822348 3969125 := bbase (se 4 (by rfl) ⟨372105, by rfl⟩ : syracuseStep 3969125 = 744211) (by norm_num)
theorem B4165829 : Blo 822348 4165829 := bbase (se 4 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 4165829 = 781093) (by norm_num)
theorem B9539797 : Blo 822348 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B7508213 : Blo 822348 7508213 := bbase (se 5 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 7508213 = 703895) (by norm_num)
theorem B954865 : Blo 822348 954865 := bbase (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) (by norm_num)
theorem B5083829 : Blo 822348 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B2233109 : Blo 822348 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B4232357 : Blo 822348 4232357 := bbase (se 4 (by rfl) ⟨396783, by rfl⟩ : syracuseStep 4232357 = 793567) (by norm_num)
theorem B2233541 : Blo 822348 2233541 := bbase (se 4 (by rfl) ⟨209394, by rfl⟩ : syracuseStep 2233541 = 418789) (by norm_num)
theorem B6264053 : Blo 822348 6264053 := bbase (se 5 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 6264053 = 587255) (by norm_num)
theorem B1250621 : Blo 822348 1250621 := bbase (se 3 (by rfl) ⟨234491, by rfl⟩ : syracuseStep 1250621 = 468983) (by norm_num)
theorem B1250669 : Blo 822348 1250669 := bbase (se 3 (by rfl) ⟨234500, by rfl⟩ : syracuseStep 1250669 = 469001) (by norm_num)
theorem B4167125 : Blo 822348 4167125 := bbase (se 7 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 4167125 = 97667) (by norm_num)
theorem B890785 : Blo 822348 890785 := bbase (se 2 (by rfl) ⟨334044, by rfl⟩ : syracuseStep 890785 = 668089) (by norm_num)
theorem B989105 : Blo 822348 989105 := bbase (se 2 (by rfl) ⟨370914, by rfl⟩ : syracuseStep 989105 = 741829) (by norm_num)
theorem B989129 : Blo 822348 989129 := bbase (se 2 (by rfl) ⟨370923, by rfl⟩ : syracuseStep 989129 = 741847) (by norm_num)
theorem B9050069 : Blo 822348 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B989437 : Blo 822348 989437 := bbase (se 3 (by rfl) ⟨185519, by rfl⟩ : syracuseStep 989437 = 371039) (by norm_num)
theorem B891169 : Blo 822348 891169 := bbase (se 2 (by rfl) ⟨334188, by rfl⟩ : syracuseStep 891169 = 668377) (by norm_num)
theorem B1317269 : Blo 822348 1317269 := bbase (se 6 (by rfl) ⟨30873, by rfl⟩ : syracuseStep 1317269 = 61747) (by norm_num)
theorem B989609 : Blo 822348 989609 := bbase (se 2 (by rfl) ⟨371103, by rfl⟩ : syracuseStep 989609 = 742207) (by norm_num)
theorem B4692437 : Blo 822348 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B989725 : Blo 822348 989725 := bbase (se 3 (by rfl) ⟨185573, by rfl⟩ : syracuseStep 989725 = 371147) (by norm_num)
theorem B4463189 : Blo 822348 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B1317493 : Blo 822348 1317493 := bbase (se 5 (by rfl) ⟨61757, by rfl⟩ : syracuseStep 1317493 = 123515) (by norm_num)
theorem B989821 : Blo 822348 989821 := bbase (se 3 (by rfl) ⟨185591, by rfl⟩ : syracuseStep 989821 = 371183) (by norm_num)
theorem B1252037 : Blo 822348 1252037 := bbase (se 4 (by rfl) ⟨117378, by rfl⟩ : syracuseStep 1252037 = 234757) (by norm_num)
theorem B4168421 : Blo 822348 4168421 := bbase (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) (by norm_num)
theorem B1088257 : Blo 822348 1088257 := bbase (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) (by norm_num)
theorem B989965 : Blo 822348 989965 := bbase (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) (by norm_num)
theorem B2038733 : Blo 822348 2038733 := bbase (se 3 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 2038733 = 764525) (by norm_num)
theorem B10722709 : Blo 822348 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B1252829 : Blo 822348 1252829 := bbase (se 3 (by rfl) ⟨234905, by rfl⟩ : syracuseStep 1252829 = 469811) (by norm_num)
theorem B925177 : Blo 822348 925177 := bbase (se 2 (by rfl) ⟨346941, by rfl⟩ : syracuseStep 925177 = 693883) (by norm_num)
theorem B925213 : Blo 822348 925213 := bbase (se 3 (by rfl) ⟨173477, by rfl⟩ : syracuseStep 925213 = 346955) (by norm_num)
theorem B925249 : Blo 822348 925249 := bbase (se 2 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 925249 = 693937) (by norm_num)
theorem B925285 : Blo 822348 925285 := bbase (se 4 (by rfl) ⟨86745, by rfl⟩ : syracuseStep 925285 = 173491) (by norm_num)
theorem B925321 : Blo 822348 925321 := bbase (se 2 (by rfl) ⟨346995, by rfl⟩ : syracuseStep 925321 = 693991) (by norm_num)
theorem B14294677 : Blo 822348 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B925357 : Blo 822348 925357 := bbase (se 3 (by rfl) ⟨173504, by rfl⟩ : syracuseStep 925357 = 347009) (by norm_num)
theorem B925393 : Blo 822348 925393 := bbase (se 2 (by rfl) ⟨347022, by rfl⟩ : syracuseStep 925393 = 694045) (by norm_num)
theorem B1318621 : Blo 822348 1318621 := bbase (se 3 (by rfl) ⟨247241, by rfl⟩ : syracuseStep 1318621 = 494483) (by norm_num)
theorem B925429 : Blo 822348 925429 := bbase (se 5 (by rfl) ⟨43379, by rfl⟩ : syracuseStep 925429 = 86759) (by norm_num)
theorem B925465 : Blo 822348 925465 := bbase (se 2 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 925465 = 694099) (by norm_num)
theorem B892729 : Blo 822348 892729 := bbase (se 2 (by rfl) ⟨334773, by rfl⟩ : syracuseStep 892729 = 669547) (by norm_num)
theorem B925501 : Blo 822348 925501 := bbase (se 3 (by rfl) ⟨173531, by rfl⟩ : syracuseStep 925501 = 347063) (by norm_num)
theorem B925537 : Blo 822348 925537 := bbase (se 2 (by rfl) ⟨347076, by rfl⟩ : syracuseStep 925537 = 694153) (by norm_num)
theorem B925573 : Blo 822348 925573 := bbase (se 4 (by rfl) ⟨86772, by rfl⟩ : syracuseStep 925573 = 173545) (by norm_num)
theorem B925609 : Blo 822348 925609 := bbase (se 2 (by rfl) ⟨347103, by rfl⟩ : syracuseStep 925609 = 694207) (by norm_num)
theorem B925645 : Blo 822348 925645 := bbase (se 3 (by rfl) ⟨173558, by rfl⟩ : syracuseStep 925645 = 347117) (by norm_num)
theorem B925681 : Blo 822348 925681 := bbase (se 2 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 925681 = 694261) (by norm_num)
theorem B4169717 : Blo 822348 4169717 := bbase (se 5 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 4169717 = 390911) (by norm_num)
theorem B3514373 : Blo 822348 3514373 := bbase (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) (by norm_num)
theorem B925717 : Blo 822348 925717 := bbase (se 6 (by rfl) ⟨21696, by rfl⟩ : syracuseStep 925717 = 43393) (by norm_num)
theorem B925753 : Blo 822348 925753 := bbase (se 2 (by rfl) ⟨347157, by rfl⟩ : syracuseStep 925753 = 694315) (by norm_num)
theorem B925789 : Blo 822348 925789 := bbase (se 3 (by rfl) ⟨173585, by rfl⟩ : syracuseStep 925789 = 347171) (by norm_num)
theorem B925825 : Blo 822348 925825 := bbase (se 2 (by rfl) ⟨347184, by rfl⟩ : syracuseStep 925825 = 694369) (by norm_num)
theorem B1319069 : Blo 822348 1319069 := bbase (se 3 (by rfl) ⟨247325, by rfl⟩ : syracuseStep 1319069 = 494651) (by norm_num)
theorem B925861 : Blo 822348 925861 := bbase (se 4 (by rfl) ⟨86799, by rfl⟩ : syracuseStep 925861 = 173599) (by norm_num)
theorem B925897 : Blo 822348 925897 := bbase (se 2 (by rfl) ⟨347211, by rfl⟩ : syracuseStep 925897 = 694423) (by norm_num)
theorem B925933 : Blo 822348 925933 := bbase (se 3 (by rfl) ⟨173612, by rfl⟩ : syracuseStep 925933 = 347225) (by norm_num)
theorem B925969 : Blo 822348 925969 := bbase (se 2 (by rfl) ⟨347238, by rfl⟩ : syracuseStep 925969 = 694477) (by norm_num)
theorem B926005 : Blo 822348 926005 := bbase (se 5 (by rfl) ⟨43406, by rfl⟩ : syracuseStep 926005 = 86813) (by norm_num)
theorem B1253693 : Blo 822348 1253693 := bbase (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) (by norm_num)
theorem B926041 : Blo 822348 926041 := bbase (se 2 (by rfl) ⟨347265, by rfl⟩ : syracuseStep 926041 = 694531) (by norm_num)
theorem B926077 : Blo 822348 926077 := bbase (se 3 (by rfl) ⟨173639, by rfl⟩ : syracuseStep 926077 = 347279) (by norm_num)
theorem B926113 : Blo 822348 926113 := bbase (se 2 (by rfl) ⟨347292, by rfl⟩ : syracuseStep 926113 = 694585) (by norm_num)
theorem B926149 : Blo 822348 926149 := bbase (se 4 (by rfl) ⟨86826, by rfl⟩ : syracuseStep 926149 = 173653) (by norm_num)
theorem B991685 : Blo 822348 991685 := bbase (se 4 (by rfl) ⟨92970, by rfl⟩ : syracuseStep 991685 = 185941) (by norm_num)
theorem B926185 : Blo 822348 926185 := bbase (se 2 (by rfl) ⟨347319, by rfl⟩ : syracuseStep 926185 = 694639) (by norm_num)
theorem B926221 : Blo 822348 926221 := bbase (se 3 (by rfl) ⟨173666, by rfl⟩ : syracuseStep 926221 = 347333) (by norm_num)
theorem B926257 : Blo 822348 926257 := bbase (se 2 (by rfl) ⟨347346, by rfl⟩ : syracuseStep 926257 = 694693) (by norm_num)
theorem B991801 : Blo 822348 991801 := bbase (se 2 (by rfl) ⟨371925, by rfl⟩ : syracuseStep 991801 = 743851) (by norm_num)
theorem B926293 : Blo 822348 926293 := bbase (se 8 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 926293 = 10855) (by norm_num)
theorem B926329 : Blo 822348 926329 := bbase (se 2 (by rfl) ⟨347373, by rfl⟩ : syracuseStep 926329 = 694747) (by norm_num)
theorem B991873 : Blo 822348 991873 := bbase (se 2 (by rfl) ⟨371952, by rfl⟩ : syracuseStep 991873 = 743905) (by norm_num)
theorem B926365 : Blo 822348 926365 := bbase (se 3 (by rfl) ⟨173693, by rfl⟩ : syracuseStep 926365 = 347387) (by norm_num)
theorem B5415605 : Blo 822348 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B926401 : Blo 822348 926401 := bbase (se 2 (by rfl) ⟨347400, by rfl⟩ : syracuseStep 926401 = 694801) (by norm_num)
theorem B926437 : Blo 822348 926437 := bbase (se 4 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 926437 = 173707) (by norm_num)
theorem B991993 : Blo 822348 991993 := bbase (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) (by norm_num)
theorem B926473 : Blo 822348 926473 := bbase (se 2 (by rfl) ⟨347427, by rfl⟩ : syracuseStep 926473 = 694855) (by norm_num)
theorem B1057577 : Blo 822348 1057577 := bbase (se 2 (by rfl) ⟨396591, by rfl⟩ : syracuseStep 1057577 = 793183) (by norm_num)
theorem B926509 : Blo 822348 926509 := bbase (se 3 (by rfl) ⟨173720, by rfl⟩ : syracuseStep 926509 = 347441) (by norm_num)
theorem B926545 : Blo 822348 926545 := bbase (se 2 (by rfl) ⟨347454, by rfl⟩ : syracuseStep 926545 = 694909) (by norm_num)
theorem B926581 : Blo 822348 926581 := bbase (se 5 (by rfl) ⟨43433, by rfl⟩ : syracuseStep 926581 = 86867) (by norm_num)
theorem B926617 : Blo 822348 926617 := bbase (se 2 (by rfl) ⟨347481, by rfl⟩ : syracuseStep 926617 = 694963) (by norm_num)
theorem B926653 : Blo 822348 926653 := bbase (se 3 (by rfl) ⟨173747, by rfl⟩ : syracuseStep 926653 = 347495) (by norm_num)
theorem B926689 : Blo 822348 926689 := bbase (se 2 (by rfl) ⟨347508, by rfl⟩ : syracuseStep 926689 = 695017) (by norm_num)
theorem B926725 : Blo 822348 926725 := bbase (se 4 (by rfl) ⟨86880, by rfl⟩ : syracuseStep 926725 = 173761) (by norm_num)
theorem B926761 : Blo 822348 926761 := bbase (se 2 (by rfl) ⟨347535, by rfl⟩ : syracuseStep 926761 = 695071) (by norm_num)
theorem B926797 : Blo 822348 926797 := bbase (se 3 (by rfl) ⟨173774, by rfl⟩ : syracuseStep 926797 = 347549) (by norm_num)
theorem B1188965 : Blo 822348 1188965 := bbase (se 4 (by rfl) ⟨111465, by rfl⟩ : syracuseStep 1188965 = 222931) (by norm_num)
theorem B926833 : Blo 822348 926833 := bbase (se 2 (by rfl) ⟨347562, by rfl⟩ : syracuseStep 926833 = 695125) (by norm_num)
theorem B992377 : Blo 822348 992377 := bbase (se 2 (by rfl) ⟨372141, by rfl⟩ : syracuseStep 992377 = 744283) (by norm_num)
theorem B926869 : Blo 822348 926869 := bbase (se 6 (by rfl) ⟨21723, by rfl⟩ : syracuseStep 926869 = 43447) (by norm_num)
theorem B926905 : Blo 822348 926905 := bbase (se 2 (by rfl) ⟨347589, by rfl⟩ : syracuseStep 926905 = 695179) (by norm_num)
theorem B926941 : Blo 822348 926941 := bbase (se 3 (by rfl) ⟨173801, by rfl⟩ : syracuseStep 926941 = 347603) (by norm_num)
theorem B926977 : Blo 822348 926977 := bbase (se 2 (by rfl) ⟨347616, by rfl⟩ : syracuseStep 926977 = 695233) (by norm_num)
theorem B4171013 : Blo 822348 4171013 := bbase (se 4 (by rfl) ⟨391032, by rfl⟩ : syracuseStep 4171013 = 782065) (by norm_num)
theorem B927013 : Blo 822348 927013 := bbase (se 4 (by rfl) ⟨86907, by rfl⟩ : syracuseStep 927013 = 173815) (by norm_num)
theorem B927049 : Blo 822348 927049 := bbase (se 2 (by rfl) ⟨347643, by rfl⟩ : syracuseStep 927049 = 695287) (by norm_num)
theorem B927085 : Blo 822348 927085 := bbase (se 3 (by rfl) ⟨173828, by rfl⟩ : syracuseStep 927085 = 347657) (by norm_num)
theorem B927121 : Blo 822348 927121 := bbase (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) (by norm_num)
theorem B927157 : Blo 822348 927157 := bbase (se 5 (by rfl) ⟨43460, by rfl⟩ : syracuseStep 927157 = 86921) (by norm_num)
theorem B927193 : Blo 822348 927193 := bbase (se 2 (by rfl) ⟨347697, by rfl⟩ : syracuseStep 927193 = 695395) (by norm_num)
theorem B927229 : Blo 822348 927229 := bbase (se 3 (by rfl) ⟨173855, by rfl⟩ : syracuseStep 927229 = 347711) (by norm_num)
theorem B894461 : Blo 822348 894461 := bbase (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) (by norm_num)
theorem B927265 : Blo 822348 927265 := bbase (se 2 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 927265 = 695449) (by norm_num)
theorem B927301 : Blo 822348 927301 := bbase (se 4 (by rfl) ⟨86934, by rfl⟩ : syracuseStep 927301 = 173869) (by norm_num)
theorem B927337 : Blo 822348 927337 := bbase (se 2 (by rfl) ⟨347751, by rfl⟩ : syracuseStep 927337 = 695503) (by norm_num)
theorem B1320581 : Blo 822348 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B927373 : Blo 822348 927373 := bbase (se 3 (by rfl) ⟨173882, by rfl⟩ : syracuseStep 927373 = 347765) (by norm_num)
theorem B927409 : Blo 822348 927409 := bbase (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) (by norm_num)
theorem B4236997 : Blo 822348 4236997 := bbase (se 4 (by rfl) ⟨397218, by rfl⟩ : syracuseStep 4236997 = 794437) (by norm_num)
theorem B927445 : Blo 822348 927445 := bbase (se 7 (by rfl) ⟨10868, by rfl⟩ : syracuseStep 927445 = 21737) (by norm_num)
theorem B3516149 : Blo 822348 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B927481 : Blo 822348 927481 := bbase (se 2 (by rfl) ⟨347805, by rfl⟩ : syracuseStep 927481 = 695611) (by norm_num)
theorem B1320709 : Blo 822348 1320709 := bbase (se 4 (by rfl) ⟨123816, by rfl⟩ : syracuseStep 1320709 = 247633) (by norm_num)
theorem B927517 : Blo 822348 927517 := bbase (se 3 (by rfl) ⟨173909, by rfl⟩ : syracuseStep 927517 = 347819) (by norm_num)
theorem B1484581 : Blo 822348 1484581 := bbase (se 4 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 1484581 = 278359) (by norm_num)
theorem B927553 : Blo 822348 927553 := bbase (se 2 (by rfl) ⟨347832, by rfl⟩ : syracuseStep 927553 = 695665) (by norm_num)
theorem B927589 : Blo 822348 927589 := bbase (se 4 (by rfl) ⟨86961, by rfl⟩ : syracuseStep 927589 = 173923) (by norm_num)
theorem B927625 : Blo 822348 927625 := bbase (se 2 (by rfl) ⟨347859, by rfl⟩ : syracuseStep 927625 = 695719) (by norm_num)
theorem B927661 : Blo 822348 927661 := bbase (se 3 (by rfl) ⟨173936, by rfl⟩ : syracuseStep 927661 = 347873) (by norm_num)
theorem B927697 : Blo 822348 927697 := bbase (se 2 (by rfl) ⟨347886, by rfl⟩ : syracuseStep 927697 = 695773) (by norm_num)
theorem B30418901 : Blo 822348 30418901 := bbase (se 7 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 30418901 = 712943) (by norm_num)
theorem B3123157 : Blo 822348 3123157 := bbase (se 7 (by rfl) ⟨36599, by rfl⟩ : syracuseStep 3123157 = 73199) (by norm_num)
theorem B927733 : Blo 822348 927733 := bbase (se 5 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 927733 = 86975) (by norm_num)
theorem B927769 : Blo 822348 927769 := bbase (se 2 (by rfl) ⟨347913, by rfl⟩ : syracuseStep 927769 = 695827) (by norm_num)
theorem B927805 : Blo 822348 927805 := bbase (se 3 (by rfl) ⟨173963, by rfl⟩ : syracuseStep 927805 = 347927) (by norm_num)
theorem B1976413 : Blo 822348 1976413 := bbase (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) (by norm_num)
theorem B927841 : Blo 822348 927841 := bbase (se 2 (by rfl) ⟨347940, by rfl⟩ : syracuseStep 927841 = 695881) (by norm_num)
theorem B927877 : Blo 822348 927877 := bbase (se 4 (by rfl) ⟨86988, by rfl⟩ : syracuseStep 927877 = 173977) (by norm_num)
theorem B5646485 : Blo 822348 5646485 := bbase (se 6 (by rfl) ⟨132339, by rfl⟩ : syracuseStep 5646485 = 264679) (by norm_num)
theorem B927913 : Blo 822348 927913 := bbase (se 2 (by rfl) ⟨347967, by rfl⟩ : syracuseStep 927913 = 695935) (by norm_num)
theorem B927949 : Blo 822348 927949 := bbase (se 3 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 927949 = 347981) (by norm_num)
theorem B927985 : Blo 822348 927985 := bbase (se 2 (by rfl) ⟨347994, by rfl⟩ : syracuseStep 927985 = 695989) (by norm_num)
theorem B3123461 : Blo 822348 3123461 := bbase (se 4 (by rfl) ⟨292824, by rfl⟩ : syracuseStep 3123461 = 585649) (by norm_num)
theorem B928021 : Blo 822348 928021 := bbase (se 6 (by rfl) ⟨21750, by rfl⟩ : syracuseStep 928021 = 43501) (by norm_num)
theorem B3385637 : Blo 822348 3385637 := bbase (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) (by norm_num)
theorem B928057 : Blo 822348 928057 := bbase (se 2 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 928057 = 696043) (by norm_num)
theorem B2500949 : Blo 822348 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B9382229 : Blo 822348 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B928093 : Blo 822348 928093 := bbase (se 3 (by rfl) ⟨174017, by rfl⟩ : syracuseStep 928093 = 348035) (by norm_num)
theorem B928129 : Blo 822348 928129 := bbase (se 2 (by rfl) ⟨348048, by rfl⟩ : syracuseStep 928129 = 696097) (by norm_num)
theorem B1485221 : Blo 822348 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B928165 : Blo 822348 928165 := bbase (se 4 (by rfl) ⟨87015, by rfl⟩ : syracuseStep 928165 = 174031) (by norm_num)
theorem B928201 : Blo 822348 928201 := bbase (se 2 (by rfl) ⟨348075, by rfl⟩ : syracuseStep 928201 = 696151) (by norm_num)
theorem B928237 : Blo 822348 928237 := bbase (se 3 (by rfl) ⟨174044, by rfl⟩ : syracuseStep 928237 = 348089) (by norm_num)
theorem B928273 : Blo 822348 928273 := bbase (se 2 (by rfl) ⟨348102, by rfl⟩ : syracuseStep 928273 = 696205) (by norm_num)
theorem B4172309 : Blo 822348 4172309 := bbase (se 6 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 4172309 = 195577) (by norm_num)
theorem B928309 : Blo 822348 928309 := bbase (se 5 (by rfl) ⟨43514, by rfl⟩ : syracuseStep 928309 = 87029) (by norm_num)
theorem B928345 : Blo 822348 928345 := bbase (se 2 (by rfl) ⟨348129, by rfl⟩ : syracuseStep 928345 = 696259) (by norm_num)
theorem B928381 : Blo 822348 928381 := bbase (se 3 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 928381 = 348143) (by norm_num)
theorem B1976989 : Blo 822348 1976989 := bbase (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) (by norm_num)
theorem B1059485 : Blo 822348 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B928417 : Blo 822348 928417 := bbase (se 2 (by rfl) ⟨348156, by rfl⟩ : syracuseStep 928417 = 696313) (by norm_num)
theorem B928453 : Blo 822348 928453 := bbase (se 4 (by rfl) ⟨87042, by rfl⟩ : syracuseStep 928453 = 174085) (by norm_num)
theorem B3517141 : Blo 822348 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B928489 : Blo 822348 928489 := bbase (se 2 (by rfl) ⟨348183, by rfl⟩ : syracuseStep 928489 = 696367) (by norm_num)
theorem B1780469 : Blo 822348 1780469 := bbase (se 5 (by rfl) ⟨83459, by rfl⟩ : syracuseStep 1780469 = 166919) (by norm_num)
theorem B928525 : Blo 822348 928525 := bbase (se 3 (by rfl) ⟨174098, by rfl⟩ : syracuseStep 928525 = 348197) (by norm_num)
theorem B928561 : Blo 822348 928561 := bbase (se 2 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 928561 = 696421) (by norm_num)
theorem B928597 : Blo 822348 928597 := bbase (se 9 (by rfl) ⟨2720, by rfl⟩ : syracuseStep 928597 = 5441) (by norm_num)
theorem B928633 : Blo 822348 928633 := bbase (se 2 (by rfl) ⟨348237, by rfl⟩ : syracuseStep 928633 = 696475) (by norm_num)
theorem B928669 : Blo 822348 928669 := bbase (se 3 (by rfl) ⟨174125, by rfl⟩ : syracuseStep 928669 = 348251) (by norm_num)
theorem B928705 : Blo 822348 928705 := bbase (se 2 (by rfl) ⟨348264, by rfl⟩ : syracuseStep 928705 = 696529) (by norm_num)
theorem B1977317 : Blo 822348 1977317 := bbase (se 4 (by rfl) ⟨185373, by rfl⟩ : syracuseStep 1977317 = 370747) (by norm_num)
theorem B928741 : Blo 822348 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B928777 : Blo 822348 928777 := bbase (se 2 (by rfl) ⟨348291, by rfl⟩ : syracuseStep 928777 = 696583) (by norm_num)
theorem B1977373 : Blo 822348 1977373 := bbase (se 3 (by rfl) ⟨370757, by rfl⟩ : syracuseStep 1977373 = 741515) (by norm_num)
theorem B928813 : Blo 822348 928813 := bbase (se 3 (by rfl) ⟨174152, by rfl⟩ : syracuseStep 928813 = 348305) (by norm_num)
theorem B928849 : Blo 822348 928849 := bbase (se 2 (by rfl) ⟨348318, by rfl⟩ : syracuseStep 928849 = 696637) (by norm_num)
theorem B1322093 : Blo 822348 1322093 := bbase (se 3 (by rfl) ⟨247892, by rfl⟩ : syracuseStep 1322093 = 495785) (by norm_num)
theorem B928885 : Blo 822348 928885 := bbase (se 5 (by rfl) ⟨43541, by rfl⟩ : syracuseStep 928885 = 87083) (by norm_num)
theorem B928921 : Blo 822348 928921 := bbase (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) (by norm_num)
theorem B928957 : Blo 822348 928957 := bbase (se 3 (by rfl) ⟨174179, by rfl⟩ : syracuseStep 928957 = 348359) (by norm_num)
theorem B928993 : Blo 822348 928993 := bbase (se 2 (by rfl) ⟨348372, by rfl⟩ : syracuseStep 928993 = 696745) (by norm_num)
theorem B7056629 : Blo 822348 7056629 := bbase (se 5 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 7056629 = 661559) (by norm_num)
theorem B1977605 : Blo 822348 1977605 := bbase (se 4 (by rfl) ⟨185400, by rfl⟩ : syracuseStep 1977605 = 370801) (by norm_num)
theorem B929029 : Blo 822348 929029 := bbase (se 4 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 929029 = 174193) (by norm_num)
theorem B1387813 : Blo 822348 1387813 := bbase (se 4 (by rfl) ⟨130107, by rfl⟩ : syracuseStep 1387813 = 260215) (by norm_num)
theorem B929065 : Blo 822348 929065 := bbase (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) (by norm_num)
theorem B929101 : Blo 822348 929101 := bbase (se 3 (by rfl) ⟨174206, by rfl⟩ : syracuseStep 929101 = 348413) (by norm_num)
theorem B929137 : Blo 822348 929137 := bbase (se 2 (by rfl) ⟨348426, by rfl⟩ : syracuseStep 929137 = 696853) (by norm_num)
theorem B1387901 : Blo 822348 1387901 := bbase (se 3 (by rfl) ⟨260231, by rfl⟩ : syracuseStep 1387901 = 520463) (by norm_num)
theorem B929173 : Blo 822348 929173 := bbase (se 6 (by rfl) ⟨21777, by rfl⟩ : syracuseStep 929173 = 43555) (by norm_num)
theorem B929209 : Blo 822348 929209 := bbase (se 2 (by rfl) ⟨348453, by rfl⟩ : syracuseStep 929209 = 696907) (by norm_num)
theorem B1977797 : Blo 822348 1977797 := bbase (se 4 (by rfl) ⟨185418, by rfl⟩ : syracuseStep 1977797 = 370837) (by norm_num)
theorem B1879517 : Blo 822348 1879517 := bbase (se 3 (by rfl) ⟨352409, by rfl⟩ : syracuseStep 1879517 = 704819) (by norm_num)
theorem B929245 : Blo 822348 929245 := bbase (se 3 (by rfl) ⟨174233, by rfl⟩ : syracuseStep 929245 = 348467) (by norm_num)
theorem B1388029 : Blo 822348 1388029 := bbase (se 3 (by rfl) ⟨260255, by rfl⟩ : syracuseStep 1388029 = 520511) (by norm_num)
theorem B929281 : Blo 822348 929281 := bbase (se 2 (by rfl) ⟨348480, by rfl⟩ : syracuseStep 929281 = 696961) (by norm_num)
theorem B6696469 : Blo 822348 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B929317 : Blo 822348 929317 := bbase (se 4 (by rfl) ⟨87123, by rfl⟩ : syracuseStep 929317 = 174247) (by norm_num)
theorem B929353 : Blo 822348 929353 := bbase (se 2 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 929353 = 697015) (by norm_num)
theorem B1388117 : Blo 822348 1388117 := bbase (se 8 (by rfl) ⟨8133, by rfl⟩ : syracuseStep 1388117 = 16267) (by norm_num)
theorem B929389 : Blo 822348 929389 := bbase (se 3 (by rfl) ⟨174260, by rfl⟩ : syracuseStep 929389 = 348521) (by norm_num)
theorem B929425 : Blo 822348 929425 := bbase (se 2 (by rfl) ⟨348534, by rfl⟩ : syracuseStep 929425 = 697069) (by norm_num)
theorem B929461 : Blo 822348 929461 := bbase (se 5 (by rfl) ⟨43568, by rfl⟩ : syracuseStep 929461 = 87137) (by norm_num)
theorem B1388245 : Blo 822348 1388245 := bbase (se 7 (by rfl) ⟨16268, by rfl⟩ : syracuseStep 1388245 = 32537) (by norm_num)
theorem B929497 : Blo 822348 929497 := bbase (se 2 (by rfl) ⟨348561, by rfl⟩ : syracuseStep 929497 = 697123) (by norm_num)
theorem B2502373 : Blo 822348 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B929533 : Blo 822348 929533 := bbase (se 3 (by rfl) ⟨174287, by rfl⟩ : syracuseStep 929533 = 348575) (by norm_num)
theorem B1781509 : Blo 822348 1781509 := bbase (se 4 (by rfl) ⟨167016, by rfl⟩ : syracuseStep 1781509 = 334033) (by norm_num)
theorem B929569 : Blo 822348 929569 := bbase (se 2 (by rfl) ⟨348588, by rfl⟩ : syracuseStep 929569 = 697177) (by norm_num)
theorem B4173605 : Blo 822348 4173605 := bbase (se 4 (by rfl) ⟨391275, by rfl⟩ : syracuseStep 4173605 = 782551) (by norm_num)
theorem B1388333 : Blo 822348 1388333 := bbase (se 3 (by rfl) ⟨260312, by rfl⟩ : syracuseStep 1388333 = 520625) (by norm_num)
theorem B929605 : Blo 822348 929605 := bbase (se 4 (by rfl) ⟨87150, by rfl⟩ : syracuseStep 929605 = 174301) (by norm_num)
theorem B929641 : Blo 822348 929641 := bbase (se 2 (by rfl) ⟨348615, by rfl⟩ : syracuseStep 929641 = 697231) (by norm_num)
theorem B1388461 : Blo 822348 1388461 := bbase (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) (by norm_num)
theorem B1388549 : Blo 822348 1388549 := bbase (se 4 (by rfl) ⟨130176, by rfl⟩ : syracuseStep 1388549 = 260353) (by norm_num)
theorem B1323029 : Blo 822348 1323029 := bbase (se 6 (by rfl) ⟨31008, by rfl⟩ : syracuseStep 1323029 = 62017) (by norm_num)
theorem B4239397 : Blo 822348 4239397 := bbase (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) (by norm_num)
theorem B1388677 : Blo 822348 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B1388765 : Blo 822348 1388765 := bbase (se 3 (by rfl) ⟨260393, by rfl⟩ : syracuseStep 1388765 = 520787) (by norm_num)
theorem B1880317 : Blo 822348 1880317 := bbase (se 3 (by rfl) ⟨352559, by rfl⟩ : syracuseStep 1880317 = 705119) (by norm_num)
theorem B3125573 : Blo 822348 3125573 := bbase (se 4 (by rfl) ⟨293022, by rfl⟩ : syracuseStep 3125573 = 586045) (by norm_num)
theorem B1388893 : Blo 822348 1388893 := bbase (se 3 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 1388893 = 520835) (by norm_num)
theorem B1978757 : Blo 822348 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B1388981 : Blo 822348 1388981 := bbase (se 5 (by rfl) ⟨65108, by rfl⟩ : syracuseStep 1388981 = 130217) (by norm_num)
theorem B7516597 : Blo 822348 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B1389109 : Blo 822348 1389109 := bbase (se 5 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 1389109 = 130229) (by norm_num)
theorem B1487413 : Blo 822348 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B3125861 : Blo 822348 3125861 := bbase (se 4 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 3125861 = 586099) (by norm_num)
theorem B1487485 : Blo 822348 1487485 := bbase (se 3 (by rfl) ⟨278903, by rfl⟩ : syracuseStep 1487485 = 557807) (by norm_num)
theorem B1389197 : Blo 822348 1389197 := bbase (se 3 (by rfl) ⟨260474, by rfl⟩ : syracuseStep 1389197 = 520949) (by norm_num)
theorem B1389325 : Blo 822348 1389325 := bbase (se 3 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 1389325 = 520997) (by norm_num)
theorem B8926037 : Blo 822348 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B6271829 : Blo 822348 6271829 := bbase (se 9 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 6271829 = 36749) (by norm_num)
theorem B1389413 : Blo 822348 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B5288885 : Blo 822348 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B1389541 : Blo 822348 1389541 := bbase (se 4 (by rfl) ⟨130269, by rfl⟩ : syracuseStep 1389541 = 260539) (by norm_num)
theorem B2503685 : Blo 822348 2503685 := bbase (se 4 (by rfl) ⟨234720, by rfl⟩ : syracuseStep 2503685 = 469441) (by norm_num)
theorem B1586213 : Blo 822348 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B4174901 : Blo 822348 4174901 := bbase (se 5 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 4174901 = 391397) (by norm_num)
theorem B1389629 : Blo 822348 1389629 := bbase (se 3 (by rfl) ⟨260555, by rfl⟩ : syracuseStep 1389629 = 521111) (by norm_num)
theorem B1881269 : Blo 822348 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B1389757 : Blo 822348 1389757 := bbase (se 3 (by rfl) ⟨260579, by rfl⟩ : syracuseStep 1389757 = 521159) (by norm_num)
theorem B1389845 : Blo 822348 1389845 := bbase (se 6 (by rfl) ⟨32574, by rfl⟩ : syracuseStep 1389845 = 65149) (by norm_num)
theorem B1881485 : Blo 822348 1881485 := bbase (se 3 (by rfl) ⟨352778, by rfl⟩ : syracuseStep 1881485 = 705557) (by norm_num)
theorem B1389973 : Blo 822348 1389973 := bbase (se 6 (by rfl) ⟨32577, by rfl⟩ : syracuseStep 1389973 = 65155) (by norm_num)
theorem B1390061 : Blo 822348 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B1390189 : Blo 822348 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B1390277 : Blo 822348 1390277 := bbase (se 4 (by rfl) ⟨130338, by rfl⟩ : syracuseStep 1390277 = 260677) (by norm_num)
theorem B3127045 : Blo 822348 3127045 := bbase (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) (by norm_num)
theorem B1390405 : Blo 822348 1390405 := bbase (se 4 (by rfl) ⟨130350, by rfl⟩ : syracuseStep 1390405 = 260701) (by norm_num)
theorem B1390493 : Blo 822348 1390493 := bbase (se 3 (by rfl) ⟨260717, by rfl⟩ : syracuseStep 1390493 = 521435) (by norm_num)
theorem B1488797 : Blo 822348 1488797 := bbase (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) (by norm_num)
theorem B1488869 : Blo 822348 1488869 := bbase (se 4 (by rfl) ⟨139581, by rfl⟩ : syracuseStep 1488869 = 279163) (by norm_num)
theorem B1390621 : Blo 822348 1390621 := bbase (se 3 (by rfl) ⟨260741, by rfl⟩ : syracuseStep 1390621 = 521483) (by norm_num)
theorem B3127349 : Blo 822348 3127349 := bbase (se 5 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 3127349 = 293189) (by norm_num)
theorem B1390709 : Blo 822348 1390709 := bbase (se 5 (by rfl) ⟨65189, by rfl⟩ : syracuseStep 1390709 = 130379) (by norm_num)
theorem B2635973 : Blo 822348 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B1390837 : Blo 822348 1390837 := bbase (se 5 (by rfl) ⟨65195, by rfl⟩ : syracuseStep 1390837 = 130391) (by norm_num)
theorem B4176197 : Blo 822348 4176197 := bbase (se 4 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 4176197 = 783037) (by norm_num)
theorem B1390925 : Blo 822348 1390925 := bbase (se 3 (by rfl) ⟨260798, by rfl⟩ : syracuseStep 1390925 = 521597) (by norm_num)
theorem B4700501 : Blo 822348 4700501 := bbase (se 10 (by rfl) ⟨6885, by rfl⟩ : syracuseStep 4700501 = 13771) (by norm_num)
theorem B1391053 : Blo 822348 1391053 := bbase (se 3 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 1391053 = 521645) (by norm_num)
theorem B5945845 : Blo 822348 5945845 := bbase (se 5 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 5945845 = 557423) (by norm_num)
theorem B1391141 : Blo 822348 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B1391269 : Blo 822348 1391269 := bbase (se 4 (by rfl) ⟨130431, by rfl⟩ : syracuseStep 1391269 = 260863) (by norm_num)
theorem B834221 : Blo 822348 834221 := bbase (se 3 (by rfl) ⟨156416, by rfl⟩ : syracuseStep 834221 = 312833) (by norm_num)
theorem B834269 : Blo 822348 834269 := bbase (se 3 (by rfl) ⟨156425, by rfl⟩ : syracuseStep 834269 = 312851) (by norm_num)
theorem B1391357 : Blo 822348 1391357 := bbase (se 3 (by rfl) ⟨260879, by rfl⟩ : syracuseStep 1391357 = 521759) (by norm_num)
theorem B1391485 : Blo 822348 1391485 := bbase (se 3 (by rfl) ⟨260903, by rfl⟩ : syracuseStep 1391485 = 521807) (by norm_num)
theorem B1850309 : Blo 822348 1850309 := bbase (se 4 (by rfl) ⟨173466, by rfl⟩ : syracuseStep 1850309 = 346933) (by norm_num)
theorem B1391573 : Blo 822348 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B1850381 : Blo 822348 1850381 := bbase (se 3 (by rfl) ⟨346946, by rfl⟩ : syracuseStep 1850381 = 693893) (by norm_num)
theorem B1850453 : Blo 822348 1850453 := bbase (se 8 (by rfl) ⟨10842, by rfl⟩ : syracuseStep 1850453 = 21685) (by norm_num)
theorem B1981525 : Blo 822348 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B1391701 : Blo 822348 1391701 := bbase (se 8 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 1391701 = 16309) (by norm_num)
theorem B1850525 : Blo 822348 1850525 := bbase (se 3 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 1850525 = 693947) (by norm_num)
theorem B1391789 : Blo 822348 1391789 := bbase (se 3 (by rfl) ⟨260960, by rfl⟩ : syracuseStep 1391789 = 521921) (by norm_num)
theorem B1850597 : Blo 822348 1850597 := bbase (se 4 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 1850597 = 346987) (by norm_num)
theorem B1850669 : Blo 822348 1850669 := bbase (se 3 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 1850669 = 694001) (by norm_num)
theorem B1391917 : Blo 822348 1391917 := bbase (se 3 (by rfl) ⟨260984, by rfl⟩ : syracuseStep 1391917 = 521969) (by norm_num)
theorem B1850741 : Blo 822348 1850741 := bbase (se 5 (by rfl) ⟨86753, by rfl⟩ : syracuseStep 1850741 = 173507) (by norm_num)
theorem B1392005 : Blo 822348 1392005 := bbase (se 4 (by rfl) ⟨130500, by rfl⟩ : syracuseStep 1392005 = 261001) (by norm_num)
theorem B1850813 : Blo 822348 1850813 := bbase (se 3 (by rfl) ⟨347027, by rfl⟩ : syracuseStep 1850813 = 694055) (by norm_num)
theorem B1981901 : Blo 822348 1981901 := bbase (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) (by norm_num)
theorem B4701685 : Blo 822348 4701685 := bbase (se 5 (by rfl) ⟨220391, by rfl⟩ : syracuseStep 4701685 = 440783) (by norm_num)
theorem B1850885 : Blo 822348 1850885 := bbase (se 4 (by rfl) ⟨173520, by rfl⟩ : syracuseStep 1850885 = 347041) (by norm_num)
theorem B2637317 : Blo 822348 2637317 := bbase (se 4 (by rfl) ⟨247248, by rfl⟩ : syracuseStep 2637317 = 494497) (by norm_num)
theorem B1392133 : Blo 822348 1392133 := bbase (se 4 (by rfl) ⟨130512, by rfl⟩ : syracuseStep 1392133 = 261025) (by norm_num)
theorem B1850957 : Blo 822348 1850957 := bbase (se 3 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 1850957 = 694109) (by norm_num)
theorem B4177493 : Blo 822348 4177493 := bbase (se 8 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 4177493 = 48955) (by norm_num)
theorem B1392221 : Blo 822348 1392221 := bbase (se 3 (by rfl) ⟨261041, by rfl⟩ : syracuseStep 1392221 = 522083) (by norm_num)
theorem B3522149 : Blo 822348 3522149 := bbase (se 4 (by rfl) ⟨330201, by rfl⟩ : syracuseStep 3522149 = 660403) (by norm_num)
theorem B1523333 : Blo 822348 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B1851029 : Blo 822348 1851029 := bbase (se 6 (by rfl) ⟨43383, by rfl⟩ : syracuseStep 1851029 = 86767) (by norm_num)
theorem B3391141 : Blo 822348 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B1851101 : Blo 822348 1851101 := bbase (se 3 (by rfl) ⟨347081, by rfl⟩ : syracuseStep 1851101 = 694163) (by norm_num)
theorem B1392349 : Blo 822348 1392349 := bbase (se 3 (by rfl) ⟨261065, by rfl⟩ : syracuseStep 1392349 = 522131) (by norm_num)
theorem B1851173 : Blo 822348 1851173 := bbase (se 4 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 1851173 = 347095) (by norm_num)
theorem B835381 : Blo 822348 835381 := bbase (se 5 (by rfl) ⟨39158, by rfl⟩ : syracuseStep 835381 = 78317) (by norm_num)
theorem B1392437 : Blo 822348 1392437 := bbase (se 5 (by rfl) ⟨65270, by rfl⟩ : syracuseStep 1392437 = 130541) (by norm_num)
theorem B1884005 : Blo 822348 1884005 := bbase (se 4 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 1884005 = 353251) (by norm_num)
theorem B1851245 : Blo 822348 1851245 := bbase (se 3 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 1851245 = 694217) (by norm_num)
theorem B1982333 : Blo 822348 1982333 := bbase (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) (by norm_num)
theorem B3522437 : Blo 822348 3522437 := bbase (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) (by norm_num)
theorem B1884077 : Blo 822348 1884077 := bbase (se 3 (by rfl) ⟨353264, by rfl⟩ : syracuseStep 1884077 = 706529) (by norm_num)
theorem B1851317 : Blo 822348 1851317 := bbase (se 5 (by rfl) ⟨86780, by rfl⟩ : syracuseStep 1851317 = 173561) (by norm_num)
theorem B1392565 : Blo 822348 1392565 := bbase (se 5 (by rfl) ⟨65276, by rfl⟩ : syracuseStep 1392565 = 130553) (by norm_num)
theorem B1851389 : Blo 822348 1851389 := bbase (se 3 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 1851389 = 694271) (by norm_num)
theorem B1392653 : Blo 822348 1392653 := bbase (se 3 (by rfl) ⟨261122, by rfl⟩ : syracuseStep 1392653 = 522245) (by norm_num)
theorem B1851461 : Blo 822348 1851461 := bbase (se 4 (by rfl) ⟨173574, by rfl⟩ : syracuseStep 1851461 = 347149) (by norm_num)
theorem B3129461 : Blo 822348 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B1851533 : Blo 822348 1851533 := bbase (se 3 (by rfl) ⟨347162, by rfl⟩ : syracuseStep 1851533 = 694325) (by norm_num)
theorem B1392781 : Blo 822348 1392781 := bbase (se 3 (by rfl) ⟨261146, by rfl⟩ : syracuseStep 1392781 = 522293) (by norm_num)
theorem B1851605 : Blo 822348 1851605 := bbase (se 7 (by rfl) ⟨21698, by rfl⟩ : syracuseStep 1851605 = 43397) (by norm_num)
theorem B1392869 : Blo 822348 1392869 := bbase (se 4 (by rfl) ⟨130581, by rfl⟩ : syracuseStep 1392869 = 261163) (by norm_num)
theorem B1851677 : Blo 822348 1851677 := bbase (se 3 (by rfl) ⟨347189, by rfl⟩ : syracuseStep 1851677 = 694379) (by norm_num)
theorem B2343269 : Blo 822348 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B1851749 : Blo 822348 1851749 := bbase (se 4 (by rfl) ⟨173601, by rfl⟩ : syracuseStep 1851749 = 347203) (by norm_num)
theorem B1392997 : Blo 822348 1392997 := bbase (se 4 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 1392997 = 261187) (by norm_num)
theorem B3129749 : Blo 822348 3129749 := bbase (se 6 (by rfl) ⟨73353, by rfl⟩ : syracuseStep 3129749 = 146707) (by norm_num)
theorem B1130917 : Blo 822348 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B1851821 : Blo 822348 1851821 := bbase (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) (by norm_num)
theorem B1982909 : Blo 822348 1982909 := bbase (se 3 (by rfl) ⟨371795, by rfl⟩ : syracuseStep 1982909 = 743591) (by norm_num)
theorem B1393085 : Blo 822348 1393085 := bbase (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) (by norm_num)
theorem B1851893 : Blo 822348 1851893 := bbase (se 5 (by rfl) ⟨86807, by rfl⟩ : syracuseStep 1851893 = 173615) (by norm_num)
theorem B1851965 : Blo 822348 1851965 := bbase (se 3 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 1851965 = 694487) (by norm_num)
theorem B1393213 : Blo 822348 1393213 := bbase (se 3 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 1393213 = 522455) (by norm_num)
theorem B2114117 : Blo 822348 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B1786445 : Blo 822348 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B3523189 : Blo 822348 3523189 := bbase (se 5 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 3523189 = 330299) (by norm_num)
theorem B1852037 : Blo 822348 1852037 := bbase (se 4 (by rfl) ⟨173628, by rfl⟩ : syracuseStep 1852037 = 347257) (by norm_num)
theorem B1393301 : Blo 822348 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B836281 : Blo 822348 836281 := bbase (se 2 (by rfl) ⟨313605, by rfl⟩ : syracuseStep 836281 = 627211) (by norm_num)
theorem B1852109 : Blo 822348 1852109 := bbase (se 3 (by rfl) ⟨347270, by rfl⟩ : syracuseStep 1852109 = 694541) (by norm_num)
theorem B1852181 : Blo 822348 1852181 := bbase (se 6 (by rfl) ⟨43410, by rfl⟩ : syracuseStep 1852181 = 86821) (by norm_num)
theorem B1393429 : Blo 822348 1393429 := bbase (se 6 (by rfl) ⟨32658, by rfl⟩ : syracuseStep 1393429 = 65317) (by norm_num)
theorem B2114333 : Blo 822348 2114333 := bbase (se 3 (by rfl) ⟨396437, by rfl⟩ : syracuseStep 2114333 = 792875) (by norm_num)
theorem B1852253 : Blo 822348 1852253 := bbase (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) (by norm_num)
theorem B4178789 : Blo 822348 4178789 := bbase (se 4 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 4178789 = 783523) (by norm_num)
theorem B1393517 : Blo 822348 1393517 := bbase (se 3 (by rfl) ⟨261284, by rfl⟩ : syracuseStep 1393517 = 522569) (by norm_num)
theorem B1852325 : Blo 822348 1852325 := bbase (se 4 (by rfl) ⟨173655, by rfl⟩ : syracuseStep 1852325 = 347311) (by norm_num)
theorem B836573 : Blo 822348 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B1852397 : Blo 822348 1852397 := bbase (se 3 (by rfl) ⟨347324, by rfl⟩ : syracuseStep 1852397 = 694649) (by norm_num)
theorem B1393645 : Blo 822348 1393645 := bbase (se 3 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 1393645 = 522617) (by norm_num)
theorem B2343941 : Blo 822348 2343941 := bbase (se 4 (by rfl) ⟨219744, by rfl⟩ : syracuseStep 2343941 = 439489) (by norm_num)
theorem B8471573 : Blo 822348 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B2081821 : Blo 822348 2081821 := bbase (se 3 (by rfl) ⟨390341, by rfl⟩ : syracuseStep 2081821 = 780683) (by norm_num)
theorem B1852469 : Blo 822348 1852469 := bbase (se 5 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 1852469 = 173669) (by norm_num)
theorem B1393733 : Blo 822348 1393733 := bbase (se 4 (by rfl) ⟨130662, by rfl⟩ : syracuseStep 1393733 = 261325) (by norm_num)
theorem B1852541 : Blo 822348 1852541 := bbase (se 3 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 1852541 = 694703) (by norm_num)
theorem B2081933 : Blo 822348 2081933 := bbase (se 3 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 2081933 = 780725) (by norm_num)
theorem B1852613 : Blo 822348 1852613 := bbase (se 4 (by rfl) ⟨173682, by rfl⟩ : syracuseStep 1852613 = 347365) (by norm_num)
theorem B1393861 : Blo 822348 1393861 := bbase (se 4 (by rfl) ⟨130674, by rfl⟩ : syracuseStep 1393861 = 261349) (by norm_num)
theorem B1852685 : Blo 822348 1852685 := bbase (se 3 (by rfl) ⟨347378, by rfl⟩ : syracuseStep 1852685 = 694757) (by norm_num)
theorem B1393949 : Blo 822348 1393949 := bbase (se 3 (by rfl) ⟨261365, by rfl⟩ : syracuseStep 1393949 = 522731) (by norm_num)
theorem B2082125 : Blo 822348 2082125 := bbase (se 3 (by rfl) ⟨390398, by rfl⟩ : syracuseStep 2082125 = 780797) (by norm_num)
theorem B1852757 : Blo 822348 1852757 := bbase (se 12 (by rfl) ⟨678, by rfl⟩ : syracuseStep 1852757 = 1357) (by norm_num)
theorem B3523925 : Blo 822348 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B1852829 : Blo 822348 1852829 := bbase (se 3 (by rfl) ⟨347405, by rfl⟩ : syracuseStep 1852829 = 694811) (by norm_num)
theorem B1394077 : Blo 822348 1394077 := bbase (se 3 (by rfl) ⟨261389, by rfl⟩ : syracuseStep 1394077 = 522779) (by norm_num)
theorem B2344373 : Blo 822348 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B4703669 : Blo 822348 4703669 := bbase (se 5 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 4703669 = 440969) (by norm_num)
theorem B2639317 : Blo 822348 2639317 := bbase (se 7 (by rfl) ⟨30929, by rfl⟩ : syracuseStep 2639317 = 61859) (by norm_num)
theorem B1852901 : Blo 822348 1852901 := bbase (se 4 (by rfl) ⟨173709, by rfl⟩ : syracuseStep 1852901 = 347419) (by norm_num)
theorem B1394165 : Blo 822348 1394165 := bbase (se 5 (by rfl) ⟨65351, by rfl⟩ : syracuseStep 1394165 = 130703) (by norm_num)
theorem B1852973 : Blo 822348 1852973 := bbase (se 3 (by rfl) ⟨347432, by rfl⟩ : syracuseStep 1852973 = 694865) (by norm_num)
theorem B3130933 : Blo 822348 3130933 := bbase (se 5 (by rfl) ⟨146762, by rfl⟩ : syracuseStep 3130933 = 293525) (by norm_num)
theorem B837173 : Blo 822348 837173 := bbase (se 5 (by rfl) ⟨39242, by rfl⟩ : syracuseStep 837173 = 78485) (by norm_num)
theorem B1853045 : Blo 822348 1853045 := bbase (se 5 (by rfl) ⟨86861, by rfl⟩ : syracuseStep 1853045 = 173723) (by norm_num)
theorem B1394293 : Blo 822348 1394293 := bbase (se 5 (by rfl) ⟨65357, by rfl⟩ : syracuseStep 1394293 = 130715) (by norm_num)
theorem B2082469 : Blo 822348 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B1853117 : Blo 822348 1853117 := bbase (se 3 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 1853117 = 694919) (by norm_num)
theorem B1394381 : Blo 822348 1394381 := bbase (se 3 (by rfl) ⟨261446, by rfl⟩ : syracuseStep 1394381 = 522893) (by norm_num)
theorem B1853189 : Blo 822348 1853189 := bbase (se 4 (by rfl) ⟨173736, by rfl⟩ : syracuseStep 1853189 = 347473) (by norm_num)
theorem B2082581 : Blo 822348 2082581 := bbase (se 6 (by rfl) ⟨48810, by rfl⟩ : syracuseStep 2082581 = 97621) (by norm_num)
theorem B1853261 : Blo 822348 1853261 := bbase (se 3 (by rfl) ⟨347486, by rfl⟩ : syracuseStep 1853261 = 694973) (by norm_num)
theorem B3131237 : Blo 822348 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B1853333 : Blo 822348 1853333 := bbase (se 6 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 1853333 = 86875) (by norm_num)
theorem B2082773 : Blo 822348 2082773 := bbase (se 7 (by rfl) ⟨24407, by rfl⟩ : syracuseStep 2082773 = 48815) (by norm_num)
theorem B1853405 : Blo 822348 1853405 := bbase (se 3 (by rfl) ⟨347513, by rfl⟩ : syracuseStep 1853405 = 695027) (by norm_num)
theorem B1853477 : Blo 822348 1853477 := bbase (se 4 (by rfl) ⟨173763, by rfl⟩ : syracuseStep 1853477 = 347527) (by norm_num)
theorem B1853549 : Blo 822348 1853549 := bbase (se 3 (by rfl) ⟨347540, by rfl⟩ : syracuseStep 1853549 = 695081) (by norm_num)
theorem B4180085 : Blo 822348 4180085 := bbase (se 5 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 4180085 = 391883) (by norm_num)
theorem B2345125 : Blo 822348 2345125 := bbase (se 4 (by rfl) ⟨219855, by rfl⟩ : syracuseStep 2345125 = 439711) (by norm_num)
theorem B2508965 : Blo 822348 2508965 := bbase (se 4 (by rfl) ⟨235215, by rfl⟩ : syracuseStep 2508965 = 470431) (by norm_num)
theorem B1853621 : Blo 822348 1853621 := bbase (se 5 (by rfl) ⟨86888, by rfl⟩ : syracuseStep 1853621 = 173777) (by norm_num)
theorem B1853693 : Blo 822348 1853693 := bbase (se 3 (by rfl) ⟨347567, by rfl⟩ : syracuseStep 1853693 = 695135) (by norm_num)
theorem B2083117 : Blo 822348 2083117 := bbase (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) (by norm_num)
theorem B1853765 : Blo 822348 1853765 := bbase (se 4 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 1853765 = 347581) (by norm_num)
theorem B1853837 : Blo 822348 1853837 := bbase (se 3 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 1853837 = 695189) (by norm_num)
theorem B2083229 : Blo 822348 2083229 := bbase (se 3 (by rfl) ⟨390605, by rfl⟩ : syracuseStep 2083229 = 781211) (by norm_num)
theorem B1853909 : Blo 822348 1853909 := bbase (se 7 (by rfl) ⟨21725, by rfl⟩ : syracuseStep 1853909 = 43451) (by norm_num)
theorem B1853981 : Blo 822348 1853981 := bbase (se 3 (by rfl) ⟨347621, by rfl⟩ : syracuseStep 1853981 = 695243) (by norm_num)
theorem B2083421 : Blo 822348 2083421 := bbase (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) (by norm_num)
theorem B1854053 : Blo 822348 1854053 := bbase (se 4 (by rfl) ⟨173817, by rfl⟩ : syracuseStep 1854053 = 347635) (by norm_num)
theorem B1854125 : Blo 822348 1854125 := bbase (se 3 (by rfl) ⟨347648, by rfl⟩ : syracuseStep 1854125 = 695297) (by norm_num)
theorem B1854197 : Blo 822348 1854197 := bbase (se 5 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 1854197 = 173831) (by norm_num)
theorem B1854269 : Blo 822348 1854269 := bbase (se 3 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 1854269 = 695351) (by norm_num)
theorem B1854341 : Blo 822348 1854341 := bbase (se 4 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 1854341 = 347689) (by norm_num)
theorem B2083765 : Blo 822348 2083765 := bbase (se 5 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 2083765 = 195353) (by norm_num)
theorem B1854413 : Blo 822348 1854413 := bbase (se 3 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 1854413 = 695405) (by norm_num)
theorem B1002449 : Blo 822348 1002449 := bbase (se 2 (by rfl) ⟨375918, by rfl⟩ : syracuseStep 1002449 = 751837) (by norm_num)
theorem B1854485 : Blo 822348 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B2083877 : Blo 822348 2083877 := bbase (se 4 (by rfl) ⟨195363, by rfl⟩ : syracuseStep 2083877 = 390727) (by norm_num)
theorem B1854557 : Blo 822348 1854557 := bbase (se 3 (by rfl) ⟨347729, by rfl⟩ : syracuseStep 1854557 = 695459) (by norm_num)
theorem B1854629 : Blo 822348 1854629 := bbase (se 4 (by rfl) ⟨173871, by rfl⟩ : syracuseStep 1854629 = 347743) (by norm_num)
theorem B2084069 : Blo 822348 2084069 := bbase (se 4 (by rfl) ⟨195381, by rfl⟩ : syracuseStep 2084069 = 390763) (by norm_num)
theorem B1854701 : Blo 822348 1854701 := bbase (se 3 (by rfl) ⟨347756, by rfl⟩ : syracuseStep 1854701 = 695513) (by norm_num)
theorem B1854773 : Blo 822348 1854773 := bbase (se 5 (by rfl) ⟨86942, by rfl⟩ : syracuseStep 1854773 = 173885) (by norm_num)
theorem B1854845 : Blo 822348 1854845 := bbase (se 3 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 1854845 = 695567) (by norm_num)
theorem B4181381 : Blo 822348 4181381 := bbase (se 4 (by rfl) ⟨392004, by rfl⟩ : syracuseStep 4181381 = 784009) (by norm_num)
theorem B1854917 : Blo 822348 1854917 := bbase (se 4 (by rfl) ⟨173898, by rfl⟩ : syracuseStep 1854917 = 347797) (by norm_num)
theorem B1854989 : Blo 822348 1854989 := bbase (se 3 (by rfl) ⟨347810, by rfl⟩ : syracuseStep 1854989 = 695621) (by norm_num)
theorem B2084413 : Blo 822348 2084413 := bbase (se 3 (by rfl) ⟨390827, by rfl⟩ : syracuseStep 2084413 = 781655) (by norm_num)
theorem B3395141 : Blo 822348 3395141 := bbase (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) (by norm_num)
theorem B1855061 : Blo 822348 1855061 := bbase (se 8 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 1855061 = 21739) (by norm_num)
theorem B4705877 : Blo 822348 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B1855133 : Blo 822348 1855133 := bbase (se 3 (by rfl) ⟨347837, by rfl⟩ : syracuseStep 1855133 = 695675) (by norm_num)
theorem B2084525 : Blo 822348 2084525 := bbase (se 3 (by rfl) ⟨390848, by rfl⟩ : syracuseStep 2084525 = 781697) (by norm_num)
theorem B1855205 : Blo 822348 1855205 := bbase (se 4 (by rfl) ⟨173925, by rfl⟩ : syracuseStep 1855205 = 347851) (by norm_num)
theorem B1855277 : Blo 822348 1855277 := bbase (se 3 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 1855277 = 695729) (by norm_num)
theorem B1756981 : Blo 822348 1756981 := bbase (se 5 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 1756981 = 164717) (by norm_num)
theorem B2084717 : Blo 822348 2084717 := bbase (se 3 (by rfl) ⟨390884, by rfl⟩ : syracuseStep 2084717 = 781769) (by norm_num)
theorem B1855349 : Blo 822348 1855349 := bbase (se 5 (by rfl) ⟨86969, by rfl⟩ : syracuseStep 1855349 = 173939) (by norm_num)
theorem B3133349 : Blo 822348 3133349 := bbase (se 4 (by rfl) ⟨293751, by rfl⟩ : syracuseStep 3133349 = 587503) (by norm_num)
theorem B1855421 : Blo 822348 1855421 := bbase (se 3 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 1855421 = 695783) (by norm_num)
theorem B937969 : Blo 822348 937969 := bbase (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) (by norm_num)
theorem B1855493 : Blo 822348 1855493 := bbase (se 4 (by rfl) ⟨173952, by rfl⟩ : syracuseStep 1855493 = 347905) (by norm_num)
theorem B1855565 : Blo 822348 1855565 := bbase (se 3 (by rfl) ⟨347918, by rfl⟩ : syracuseStep 1855565 = 695837) (by norm_num)
theorem B6672469 : Blo 822348 6672469 := bbase (se 8 (by rfl) ⟨39096, by rfl⟩ : syracuseStep 6672469 = 78193) (by norm_num)
theorem B1855637 : Blo 822348 1855637 := bbase (se 6 (by rfl) ⟨43491, by rfl⟩ : syracuseStep 1855637 = 86983) (by norm_num)
theorem B2085061 : Blo 822348 2085061 := bbase (se 4 (by rfl) ⟨195474, by rfl⟩ : syracuseStep 2085061 = 390949) (by norm_num)
theorem B3133637 : Blo 822348 3133637 := bbase (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) (by norm_num)
theorem B1855709 : Blo 822348 1855709 := bbase (se 3 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 1855709 = 695891) (by norm_num)
theorem B3952901 : Blo 822348 3952901 := bbase (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) (by norm_num)
theorem B938261 : Blo 822348 938261 := bbase (se 6 (by rfl) ⟨21990, by rfl⟩ : syracuseStep 938261 = 43981) (by norm_num)
theorem B1757477 : Blo 822348 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B1855781 : Blo 822348 1855781 := bbase (se 4 (by rfl) ⟨173979, by rfl⟩ : syracuseStep 1855781 = 347959) (by norm_num)
theorem B2085173 : Blo 822348 2085173 := bbase (se 5 (by rfl) ⟨97742, by rfl⟩ : syracuseStep 2085173 = 195485) (by norm_num)
theorem B1855853 : Blo 822348 1855853 := bbase (se 3 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 1855853 = 695945) (by norm_num)
theorem B2642341 : Blo 822348 2642341 := bbase (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) (by norm_num)
theorem B1855925 : Blo 822348 1855925 := bbase (se 5 (by rfl) ⟨86996, by rfl⟩ : syracuseStep 1855925 = 173993) (by norm_num)
theorem B2085365 : Blo 822348 2085365 := bbase (se 5 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 2085365 = 195503) (by norm_num)
theorem B1855997 : Blo 822348 1855997 := bbase (se 3 (by rfl) ⟨347999, by rfl⟩ : syracuseStep 1855997 = 695999) (by norm_num)
theorem B3527221 : Blo 822348 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B1856069 : Blo 822348 1856069 := bbase (se 4 (by rfl) ⟨174006, by rfl⟩ : syracuseStep 1856069 = 348013) (by norm_num)
theorem B1233533 : Blo 822348 1233533 := bbase (se 3 (by rfl) ⟨231287, by rfl⟩ : syracuseStep 1233533 = 462575) (by norm_num)
theorem B1856141 : Blo 822348 1856141 := bbase (se 3 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 1856141 = 696053) (by norm_num)
theorem B1233557 : Blo 822348 1233557 := bbase (se 6 (by rfl) ⟨28911, by rfl⟩ : syracuseStep 1233557 = 57823) (by norm_num)
theorem B4182677 : Blo 822348 4182677 := bbase (se 6 (by rfl) ⟨98031, by rfl⟩ : syracuseStep 4182677 = 196063) (by norm_num)
theorem B1233581 : Blo 822348 1233581 := bbase (se 3 (by rfl) ⟨231296, by rfl⟩ : syracuseStep 1233581 = 462593) (by norm_num)
theorem B1233605 : Blo 822348 1233605 := bbase (se 4 (by rfl) ⟨115650, by rfl⟩ : syracuseStep 1233605 = 231301) (by norm_num)
theorem B1856213 : Blo 822348 1856213 := bbase (se 7 (by rfl) ⟨21752, by rfl⟩ : syracuseStep 1856213 = 43505) (by norm_num)
theorem B1233629 : Blo 822348 1233629 := bbase (se 3 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 1233629 = 462611) (by norm_num)
theorem B1233653 : Blo 822348 1233653 := bbase (se 5 (by rfl) ⟨57827, by rfl⟩ : syracuseStep 1233653 = 115655) (by norm_num)
theorem B1233677 : Blo 822348 1233677 := bbase (se 3 (by rfl) ⟨231314, by rfl⟩ : syracuseStep 1233677 = 462629) (by norm_num)
theorem B1856285 : Blo 822348 1856285 := bbase (se 3 (by rfl) ⟨348053, by rfl⟩ : syracuseStep 1856285 = 696107) (by norm_num)
theorem B1233701 : Blo 822348 1233701 := bbase (se 4 (by rfl) ⟨115659, by rfl⟩ : syracuseStep 1233701 = 231319) (by norm_num)
theorem B1233725 : Blo 822348 1233725 := bbase (se 3 (by rfl) ⟨231323, by rfl⟩ : syracuseStep 1233725 = 462647) (by norm_num)
theorem B2085709 : Blo 822348 2085709 := bbase (se 3 (by rfl) ⟨391070, by rfl⟩ : syracuseStep 2085709 = 782141) (by norm_num)
theorem B1233749 : Blo 822348 1233749 := bbase (se 9 (by rfl) ⟨3614, by rfl⟩ : syracuseStep 1233749 = 7229) (by norm_num)
theorem B1856357 : Blo 822348 1856357 := bbase (se 4 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 1856357 = 348067) (by norm_num)
theorem B1233773 : Blo 822348 1233773 := bbase (se 3 (by rfl) ⟨231332, by rfl⟩ : syracuseStep 1233773 = 462665) (by norm_num)
theorem B1233797 : Blo 822348 1233797 := bbase (se 4 (by rfl) ⟨115668, by rfl⟩ : syracuseStep 1233797 = 231337) (by norm_num)
theorem B1233821 : Blo 822348 1233821 := bbase (se 3 (by rfl) ⟨231341, by rfl⟩ : syracuseStep 1233821 = 462683) (by norm_num)
theorem B1856429 : Blo 822348 1856429 := bbase (se 3 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 1856429 = 696161) (by norm_num)
theorem B1233845 : Blo 822348 1233845 := bbase (se 5 (by rfl) ⟨57836, by rfl⟩ : syracuseStep 1233845 = 115673) (by norm_num)
theorem B2085821 : Blo 822348 2085821 := bbase (se 3 (by rfl) ⟨391091, by rfl⟩ : syracuseStep 2085821 = 782183) (by norm_num)
theorem B2347973 : Blo 822348 2347973 := bbase (se 4 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 2347973 = 440245) (by norm_num)
theorem B1233869 : Blo 822348 1233869 := bbase (se 3 (by rfl) ⟨231350, by rfl⟩ : syracuseStep 1233869 = 462701) (by norm_num)
theorem B1233893 : Blo 822348 1233893 := bbase (se 4 (by rfl) ⟨115677, by rfl⟩ : syracuseStep 1233893 = 231355) (by norm_num)
theorem B1856501 : Blo 822348 1856501 := bbase (se 5 (by rfl) ⟨87023, by rfl⟩ : syracuseStep 1856501 = 174047) (by norm_num)
theorem B1233917 : Blo 822348 1233917 := bbase (se 3 (by rfl) ⟨231359, by rfl⟩ : syracuseStep 1233917 = 462719) (by norm_num)
theorem B1233941 : Blo 822348 1233941 := bbase (se 6 (by rfl) ⟨28920, by rfl⟩ : syracuseStep 1233941 = 57841) (by norm_num)
theorem B939037 : Blo 822348 939037 := bbase (se 3 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 939037 = 352139) (by norm_num)
theorem B1233965 : Blo 822348 1233965 := bbase (se 3 (by rfl) ⟨231368, by rfl⟩ : syracuseStep 1233965 = 462737) (by norm_num)
theorem B1856573 : Blo 822348 1856573 := bbase (se 3 (by rfl) ⟨348107, by rfl⟩ : syracuseStep 1856573 = 696215) (by norm_num)
theorem B1233989 : Blo 822348 1233989 := bbase (se 4 (by rfl) ⟨115686, by rfl⟩ : syracuseStep 1233989 = 231373) (by norm_num)
theorem B1561693 : Blo 822348 1561693 := bbase (se 3 (by rfl) ⟨292817, by rfl⟩ : syracuseStep 1561693 = 585635) (by norm_num)
theorem B1234013 : Blo 822348 1234013 := bbase (se 3 (by rfl) ⟨231377, by rfl⟩ : syracuseStep 1234013 = 462755) (by norm_num)
theorem B1234037 : Blo 822348 1234037 := bbase (se 5 (by rfl) ⟨57845, by rfl⟩ : syracuseStep 1234037 = 115691) (by norm_num)
theorem B939133 : Blo 822348 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B2086013 : Blo 822348 2086013 := bbase (se 3 (by rfl) ⟨391127, by rfl⟩ : syracuseStep 2086013 = 782255) (by norm_num)
theorem B1758341 : Blo 822348 1758341 := bbase (se 4 (by rfl) ⟨164844, by rfl⟩ : syracuseStep 1758341 = 329689) (by norm_num)
theorem B1856645 : Blo 822348 1856645 := bbase (se 4 (by rfl) ⟨174060, by rfl⟩ : syracuseStep 1856645 = 348121) (by norm_num)
theorem B1234061 : Blo 822348 1234061 := bbase (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) (by norm_num)
theorem B1234085 : Blo 822348 1234085 := bbase (se 4 (by rfl) ⟨115695, by rfl⟩ : syracuseStep 1234085 = 231391) (by norm_num)
theorem B1234109 : Blo 822348 1234109 := bbase (se 3 (by rfl) ⟨231395, by rfl⟩ : syracuseStep 1234109 = 462791) (by norm_num)
theorem B1856717 : Blo 822348 1856717 := bbase (se 3 (by rfl) ⟨348134, by rfl⟩ : syracuseStep 1856717 = 696269) (by norm_num)
theorem B1234133 : Blo 822348 1234133 := bbase (se 7 (by rfl) ⟨14462, by rfl⟩ : syracuseStep 1234133 = 28925) (by norm_num)
theorem B1561837 : Blo 822348 1561837 := bbase (se 3 (by rfl) ⟨292844, by rfl⟩ : syracuseStep 1561837 = 585689) (by norm_num)
theorem B1234157 : Blo 822348 1234157 := bbase (se 3 (by rfl) ⟨231404, by rfl⟩ : syracuseStep 1234157 = 462809) (by norm_num)
theorem B1234181 : Blo 822348 1234181 := bbase (se 4 (by rfl) ⟨115704, by rfl⟩ : syracuseStep 1234181 = 231409) (by norm_num)
theorem B1758485 : Blo 822348 1758485 := bbase (se 6 (by rfl) ⟨41214, by rfl⟩ : syracuseStep 1758485 = 82429) (by norm_num)
theorem B1856789 : Blo 822348 1856789 := bbase (se 6 (by rfl) ⟨43518, by rfl⟩ : syracuseStep 1856789 = 87037) (by norm_num)
theorem B1234205 : Blo 822348 1234205 := bbase (se 3 (by rfl) ⟨231413, by rfl⟩ : syracuseStep 1234205 = 462827) (by norm_num)
theorem B1234229 : Blo 822348 1234229 := bbase (se 5 (by rfl) ⟨57854, by rfl⟩ : syracuseStep 1234229 = 115709) (by norm_num)
theorem B1234253 : Blo 822348 1234253 := bbase (se 3 (by rfl) ⟨231422, by rfl⟩ : syracuseStep 1234253 = 462845) (by norm_num)
theorem B1856861 : Blo 822348 1856861 := bbase (se 3 (by rfl) ⟨348161, by rfl⟩ : syracuseStep 1856861 = 696323) (by norm_num)
theorem B1234277 : Blo 822348 1234277 := bbase (se 4 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 1234277 = 231427) (by norm_num)
theorem B3134821 : Blo 822348 3134821 := bbase (se 4 (by rfl) ⟨293889, by rfl⟩ : syracuseStep 3134821 = 587779) (by norm_num)
theorem B1234301 : Blo 822348 1234301 := bbase (se 3 (by rfl) ⟨231431, by rfl⟩ : syracuseStep 1234301 = 462863) (by norm_num)
theorem B1561997 : Blo 822348 1561997 := bbase (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) (by norm_num)
theorem B1234325 : Blo 822348 1234325 := bbase (se 6 (by rfl) ⟨28929, by rfl⟩ : syracuseStep 1234325 = 57859) (by norm_num)
theorem B1856933 : Blo 822348 1856933 := bbase (se 4 (by rfl) ⟨174087, by rfl⟩ : syracuseStep 1856933 = 348175) (by norm_num)
theorem B1234349 : Blo 822348 1234349 := bbase (se 3 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 1234349 = 462881) (by norm_num)
theorem B1234373 : Blo 822348 1234373 := bbase (se 4 (by rfl) ⟨115722, by rfl⟩ : syracuseStep 1234373 = 231445) (by norm_num)
theorem B2086357 : Blo 822348 2086357 := bbase (se 7 (by rfl) ⟨24449, by rfl⟩ : syracuseStep 2086357 = 48899) (by norm_num)
theorem B1234397 : Blo 822348 1234397 := bbase (se 3 (by rfl) ⟨231449, by rfl⟩ : syracuseStep 1234397 = 462899) (by norm_num)
theorem B1857005 : Blo 822348 1857005 := bbase (se 3 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 1857005 = 696377) (by norm_num)
theorem B1234421 : Blo 822348 1234421 := bbase (se 5 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 1234421 = 115727) (by norm_num)
theorem B1005061 : Blo 822348 1005061 := bbase (se 4 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 1005061 = 188449) (by norm_num)
theorem B1234445 : Blo 822348 1234445 := bbase (se 3 (by rfl) ⟨231458, by rfl⟩ : syracuseStep 1234445 = 462917) (by norm_num)
theorem B1562141 : Blo 822348 1562141 := bbase (se 3 (by rfl) ⟨292901, by rfl⟩ : syracuseStep 1562141 = 585803) (by norm_num)
theorem B1234469 : Blo 822348 1234469 := bbase (se 4 (by rfl) ⟨115731, by rfl⟩ : syracuseStep 1234469 = 231463) (by norm_num)
theorem B1857077 : Blo 822348 1857077 := bbase (se 5 (by rfl) ⟨87050, by rfl⟩ : syracuseStep 1857077 = 174101) (by norm_num)
theorem B1234493 : Blo 822348 1234493 := bbase (se 3 (by rfl) ⟨231467, by rfl⟩ : syracuseStep 1234493 = 462935) (by norm_num)
theorem B2086469 : Blo 822348 2086469 := bbase (se 4 (by rfl) ⟨195606, by rfl⟩ : syracuseStep 2086469 = 391213) (by norm_num)
theorem B1234517 : Blo 822348 1234517 := bbase (se 8 (by rfl) ⟨7233, by rfl⟩ : syracuseStep 1234517 = 14467) (by norm_num)
theorem B2971237 : Blo 822348 2971237 := bbase (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) (by norm_num)
theorem B1234541 : Blo 822348 1234541 := bbase (se 3 (by rfl) ⟨231476, by rfl⟩ : syracuseStep 1234541 = 462953) (by norm_num)
theorem B7034485 : Blo 822348 7034485 := bbase (se 5 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 7034485 = 659483) (by norm_num)
theorem B1857149 : Blo 822348 1857149 := bbase (se 3 (by rfl) ⟨348215, by rfl⟩ : syracuseStep 1857149 = 696431) (by norm_num)
theorem B1234565 : Blo 822348 1234565 := bbase (se 4 (by rfl) ⟨115740, by rfl⟩ : syracuseStep 1234565 = 231481) (by norm_num)
theorem B3135125 : Blo 822348 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B1234589 : Blo 822348 1234589 := bbase (se 3 (by rfl) ⟨231485, by rfl⟩ : syracuseStep 1234589 = 462971) (by norm_num)
theorem B1234613 : Blo 822348 1234613 := bbase (se 5 (by rfl) ⟨57872, by rfl⟩ : syracuseStep 1234613 = 115745) (by norm_num)
theorem B1857221 : Blo 822348 1857221 := bbase (se 4 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 1857221 = 348229) (by norm_num)
theorem B939721 : Blo 822348 939721 := bbase (se 2 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 939721 = 704791) (by norm_num)
theorem B1234637 : Blo 822348 1234637 := bbase (se 3 (by rfl) ⟨231494, by rfl⟩ : syracuseStep 1234637 = 462989) (by norm_num)
theorem B1234661 : Blo 822348 1234661 := bbase (se 4 (by rfl) ⟨115749, by rfl⟩ : syracuseStep 1234661 = 231499) (by norm_num)
theorem B1234685 : Blo 822348 1234685 := bbase (se 3 (by rfl) ⟨231503, by rfl⟩ : syracuseStep 1234685 = 463007) (by norm_num)
theorem B2086661 : Blo 822348 2086661 := bbase (se 4 (by rfl) ⟨195624, by rfl⟩ : syracuseStep 2086661 = 391249) (by norm_num)
theorem B1857293 : Blo 822348 1857293 := bbase (se 3 (by rfl) ⟨348242, by rfl⟩ : syracuseStep 1857293 = 696485) (by norm_num)
theorem B1234709 : Blo 822348 1234709 := bbase (se 6 (by rfl) ⟨28938, by rfl⟩ : syracuseStep 1234709 = 57877) (by norm_num)
theorem B1234733 : Blo 822348 1234733 := bbase (se 3 (by rfl) ⟨231512, by rfl⟩ : syracuseStep 1234733 = 463025) (by norm_num)
theorem B1562429 : Blo 822348 1562429 := bbase (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) (by norm_num)
theorem B1234757 : Blo 822348 1234757 := bbase (se 4 (by rfl) ⟨115758, by rfl⟩ : syracuseStep 1234757 = 231517) (by norm_num)
theorem B1857365 : Blo 822348 1857365 := bbase (se 9 (by rfl) ⟨5441, by rfl⟩ : syracuseStep 1857365 = 10883) (by norm_num)
theorem B1234781 : Blo 822348 1234781 := bbase (se 3 (by rfl) ⟨231521, by rfl⟩ : syracuseStep 1234781 = 463043) (by norm_num)
theorem B1234805 : Blo 822348 1234805 := bbase (se 5 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 1234805 = 115763) (by norm_num)
theorem B1234829 : Blo 822348 1234829 := bbase (se 3 (by rfl) ⟨231530, by rfl⟩ : syracuseStep 1234829 = 463061) (by norm_num)
theorem B1857437 : Blo 822348 1857437 := bbase (se 3 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 1857437 = 696539) (by norm_num)
theorem B1234853 : Blo 822348 1234853 := bbase (se 4 (by rfl) ⟨115767, by rfl⟩ : syracuseStep 1234853 = 231535) (by norm_num)
theorem B1234877 : Blo 822348 1234877 := bbase (se 3 (by rfl) ⟨231539, by rfl⟩ : syracuseStep 1234877 = 463079) (by norm_num)
theorem B1562581 : Blo 822348 1562581 := bbase (se 7 (by rfl) ⟨18311, by rfl⟩ : syracuseStep 1562581 = 36623) (by norm_num)
theorem B1234901 : Blo 822348 1234901 := bbase (se 7 (by rfl) ⟨14471, by rfl⟩ : syracuseStep 1234901 = 28943) (by norm_num)
theorem B22566869 : Blo 822348 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B1857509 : Blo 822348 1857509 := bbase (se 4 (by rfl) ⟨174141, by rfl⟩ : syracuseStep 1857509 = 348283) (by norm_num)
theorem B1234925 : Blo 822348 1234925 := bbase (se 3 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 1234925 = 463097) (by norm_num)
theorem B1759229 : Blo 822348 1759229 := bbase (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) (by norm_num)
theorem B1234949 : Blo 822348 1234949 := bbase (se 4 (by rfl) ⟨115776, by rfl⟩ : syracuseStep 1234949 = 231553) (by norm_num)
theorem B1234973 : Blo 822348 1234973 := bbase (se 3 (by rfl) ⟨231557, by rfl⟩ : syracuseStep 1234973 = 463115) (by norm_num)
theorem B1857581 : Blo 822348 1857581 := bbase (se 3 (by rfl) ⟨348296, by rfl⟩ : syracuseStep 1857581 = 696593) (by norm_num)
theorem B6248501 : Blo 822348 6248501 := bbase (se 5 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 6248501 = 585797) (by norm_num)
theorem B1234997 : Blo 822348 1234997 := bbase (se 5 (by rfl) ⟨57890, by rfl⟩ : syracuseStep 1234997 = 115781) (by norm_num)
theorem B1235021 : Blo 822348 1235021 := bbase (se 3 (by rfl) ⟨231566, by rfl⟩ : syracuseStep 1235021 = 463133) (by norm_num)
theorem B2087005 : Blo 822348 2087005 := bbase (se 3 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 2087005 = 782627) (by norm_num)
theorem B1235045 : Blo 822348 1235045 := bbase (se 4 (by rfl) ⟨115785, by rfl⟩ : syracuseStep 1235045 = 231571) (by norm_num)
theorem B2349157 : Blo 822348 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B1857653 : Blo 822348 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B1235069 : Blo 822348 1235069 := bbase (se 3 (by rfl) ⟨231575, by rfl⟩ : syracuseStep 1235069 = 463151) (by norm_num)
theorem B1235093 : Blo 822348 1235093 := bbase (se 6 (by rfl) ⟨28947, by rfl⟩ : syracuseStep 1235093 = 57895) (by norm_num)
theorem B6871189 : Blo 822348 6871189 := bbase (se 6 (by rfl) ⟨161043, by rfl⟩ : syracuseStep 6871189 = 322087) (by norm_num)
theorem B1235117 : Blo 822348 1235117 := bbase (se 3 (by rfl) ⟨231584, by rfl⟩ : syracuseStep 1235117 = 463169) (by norm_num)
theorem B940205 : Blo 822348 940205 := bbase (se 3 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 940205 = 352577) (by norm_num)
theorem B1857725 : Blo 822348 1857725 := bbase (se 3 (by rfl) ⟨348323, by rfl⟩ : syracuseStep 1857725 = 696647) (by norm_num)
theorem B1235141 : Blo 822348 1235141 := bbase (se 4 (by rfl) ⟨115794, by rfl⟩ : syracuseStep 1235141 = 231589) (by norm_num)
theorem B2087117 : Blo 822348 2087117 := bbase (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) (by norm_num)
theorem B5003477 : Blo 822348 5003477 := bbase (se 7 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 5003477 = 117269) (by norm_num)
theorem B1235165 : Blo 822348 1235165 := bbase (se 3 (by rfl) ⟨231593, by rfl⟩ : syracuseStep 1235165 = 463187) (by norm_num)
theorem B1235189 : Blo 822348 1235189 := bbase (se 5 (by rfl) ⟨57899, by rfl⟩ : syracuseStep 1235189 = 115799) (by norm_num)
theorem B1562885 : Blo 822348 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B2349317 : Blo 822348 2349317 := bbase (se 4 (by rfl) ⟨220248, by rfl⟩ : syracuseStep 2349317 = 440497) (by norm_num)
theorem B1857797 : Blo 822348 1857797 := bbase (se 4 (by rfl) ⟨174168, by rfl⟩ : syracuseStep 1857797 = 348337) (by norm_num)
theorem B1235213 : Blo 822348 1235213 := bbase (se 3 (by rfl) ⟨231602, by rfl⟩ : syracuseStep 1235213 = 463205) (by norm_num)
theorem B1235237 : Blo 822348 1235237 := bbase (se 4 (by rfl) ⟨115803, by rfl⟩ : syracuseStep 1235237 = 231607) (by norm_num)
theorem B1235261 : Blo 822348 1235261 := bbase (se 3 (by rfl) ⟨231611, by rfl⟩ : syracuseStep 1235261 = 463223) (by norm_num)
theorem B1857869 : Blo 822348 1857869 := bbase (se 3 (by rfl) ⟨348350, by rfl⟩ : syracuseStep 1857869 = 696701) (by norm_num)
theorem B1235285 : Blo 822348 1235285 := bbase (se 10 (by rfl) ⟨1809, by rfl⟩ : syracuseStep 1235285 = 3619) (by norm_num)
theorem B1235309 : Blo 822348 1235309 := bbase (se 3 (by rfl) ⟨231620, by rfl⟩ : syracuseStep 1235309 = 463241) (by norm_num)
theorem B4446581 : Blo 822348 4446581 := bbase (se 5 (by rfl) ⟨208433, by rfl⟩ : syracuseStep 4446581 = 416867) (by norm_num)
theorem B1235333 : Blo 822348 1235333 := bbase (se 4 (by rfl) ⟨115812, by rfl⟩ : syracuseStep 1235333 = 231625) (by norm_num)
theorem B2087309 : Blo 822348 2087309 := bbase (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) (by norm_num)
theorem B5003669 : Blo 822348 5003669 := bbase (se 6 (by rfl) ⟨117273, by rfl⟩ : syracuseStep 5003669 = 234547) (by norm_num)
theorem B1857941 : Blo 822348 1857941 := bbase (se 6 (by rfl) ⟨43545, by rfl⟩ : syracuseStep 1857941 = 87091) (by norm_num)
theorem B1235357 : Blo 822348 1235357 := bbase (se 3 (by rfl) ⟨231629, by rfl⟩ : syracuseStep 1235357 = 463259) (by norm_num)
theorem B1235381 : Blo 822348 1235381 := bbase (se 5 (by rfl) ⟨57908, by rfl⟩ : syracuseStep 1235381 = 115817) (by norm_num)
theorem B1235405 : Blo 822348 1235405 := bbase (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) (by norm_num)
theorem B1858013 : Blo 822348 1858013 := bbase (se 3 (by rfl) ⟨348377, by rfl⟩ : syracuseStep 1858013 = 696755) (by norm_num)
theorem B1235429 : Blo 822348 1235429 := bbase (se 4 (by rfl) ⟨115821, by rfl⟩ : syracuseStep 1235429 = 231643) (by norm_num)
theorem B2349557 : Blo 822348 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B1235453 : Blo 822348 1235453 := bbase (se 3 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 1235453 = 463295) (by norm_num)
theorem B1235477 : Blo 822348 1235477 := bbase (se 6 (by rfl) ⟨28956, by rfl⟩ : syracuseStep 1235477 = 57913) (by norm_num)
theorem B1858085 : Blo 822348 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B1235501 : Blo 822348 1235501 := bbase (se 3 (by rfl) ⟨231656, by rfl⟩ : syracuseStep 1235501 = 463313) (by norm_num)
theorem B1235525 : Blo 822348 1235525 := bbase (se 4 (by rfl) ⟨115830, by rfl⟩ : syracuseStep 1235525 = 231661) (by norm_num)
theorem B1235549 : Blo 822348 1235549 := bbase (se 3 (by rfl) ⟨231665, by rfl⟩ : syracuseStep 1235549 = 463331) (by norm_num)
theorem B2775653 : Blo 822348 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1858157 : Blo 822348 1858157 := bbase (se 3 (by rfl) ⟨348404, by rfl⟩ : syracuseStep 1858157 = 696809) (by norm_num)
theorem B1235573 : Blo 822348 1235573 := bbase (se 5 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 1235573 = 115835) (by norm_num)
theorem B1235597 : Blo 822348 1235597 := bbase (se 3 (by rfl) ⟨231674, by rfl⟩ : syracuseStep 1235597 = 463349) (by norm_num)
theorem B1235621 : Blo 822348 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B2349749 : Blo 822348 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B1858229 : Blo 822348 1858229 := bbase (se 5 (by rfl) ⟨87104, by rfl⟩ : syracuseStep 1858229 = 174209) (by norm_num)
theorem B1235645 : Blo 822348 1235645 := bbase (se 3 (by rfl) ⟨231683, by rfl⟩ : syracuseStep 1235645 = 463367) (by norm_num)
theorem B1235669 : Blo 822348 1235669 := bbase (se 7 (by rfl) ⟨14480, by rfl⟩ : syracuseStep 1235669 = 28961) (by norm_num)
theorem B2087653 : Blo 822348 2087653 := bbase (se 4 (by rfl) ⟨195717, by rfl⟩ : syracuseStep 2087653 = 391435) (by norm_num)
theorem B1235693 : Blo 822348 1235693 := bbase (se 3 (by rfl) ⟨231692, by rfl⟩ : syracuseStep 1235693 = 463385) (by norm_num)
theorem B1759981 : Blo 822348 1759981 := bbase (se 3 (by rfl) ⟨329996, by rfl⟩ : syracuseStep 1759981 = 659993) (by norm_num)
theorem B1858301 : Blo 822348 1858301 := bbase (se 3 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 1858301 = 696863) (by norm_num)
theorem B1235717 : Blo 822348 1235717 := bbase (se 4 (by rfl) ⟨115848, by rfl⟩ : syracuseStep 1235717 = 231697) (by norm_num)
theorem B1235741 : Blo 822348 1235741 := bbase (se 3 (by rfl) ⟨231701, by rfl⟩ : syracuseStep 1235741 = 463403) (by norm_num)
theorem B1235765 : Blo 822348 1235765 := bbase (se 5 (by rfl) ⟨57926, by rfl⟩ : syracuseStep 1235765 = 115853) (by norm_num)
theorem B1858373 : Blo 822348 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B1235789 : Blo 822348 1235789 := bbase (se 3 (by rfl) ⟨231710, by rfl⟩ : syracuseStep 1235789 = 463421) (by norm_num)
theorem B4447061 : Blo 822348 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B2087765 : Blo 822348 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1235813 : Blo 822348 1235813 := bbase (se 4 (by rfl) ⟨115857, by rfl⟩ : syracuseStep 1235813 = 231715) (by norm_num)
theorem B1235837 : Blo 822348 1235837 := bbase (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) (by norm_num)
theorem B1760125 : Blo 822348 1760125 := bbase (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) (by norm_num)
theorem B1858445 : Blo 822348 1858445 := bbase (se 3 (by rfl) ⟨348458, by rfl⟩ : syracuseStep 1858445 = 696917) (by norm_num)
theorem B1235861 : Blo 822348 1235861 := bbase (se 6 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 1235861 = 57931) (by norm_num)
theorem B1235885 : Blo 822348 1235885 := bbase (se 3 (by rfl) ⟨231728, by rfl⟩ : syracuseStep 1235885 = 463457) (by norm_num)
theorem B1235909 : Blo 822348 1235909 := bbase (se 4 (by rfl) ⟨115866, by rfl⟩ : syracuseStep 1235909 = 231733) (by norm_num)
theorem B1858517 : Blo 822348 1858517 := bbase (se 7 (by rfl) ⟨21779, by rfl⟩ : syracuseStep 1858517 = 43559) (by norm_num)
theorem B1235933 : Blo 822348 1235933 := bbase (se 3 (by rfl) ⟨231737, by rfl⟩ : syracuseStep 1235933 = 463475) (by norm_num)
theorem B1563637 : Blo 822348 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B1235957 : Blo 822348 1235957 := bbase (se 5 (by rfl) ⟨57935, by rfl⟩ : syracuseStep 1235957 = 115871) (by norm_num)
theorem B1235981 : Blo 822348 1235981 := bbase (se 3 (by rfl) ⟨231746, by rfl⟩ : syracuseStep 1235981 = 463493) (by norm_num)
theorem B2776085 : Blo 822348 2776085 := bbase (se 6 (by rfl) ⟨65064, by rfl⟩ : syracuseStep 2776085 = 130129) (by norm_num)
theorem B2087957 : Blo 822348 2087957 := bbase (se 6 (by rfl) ⟨48936, by rfl⟩ : syracuseStep 2087957 = 97873) (by norm_num)
theorem B1858589 : Blo 822348 1858589 := bbase (se 3 (by rfl) ⟨348485, by rfl⟩ : syracuseStep 1858589 = 696971) (by norm_num)
theorem B1236005 : Blo 822348 1236005 := bbase (se 4 (by rfl) ⟨115875, by rfl⟩ : syracuseStep 1236005 = 231751) (by norm_num)
theorem B1236029 : Blo 822348 1236029 := bbase (se 3 (by rfl) ⟨231755, by rfl⟩ : syracuseStep 1236029 = 463511) (by norm_num)
theorem B1236053 : Blo 822348 1236053 := bbase (se 8 (by rfl) ⟨7242, by rfl⟩ : syracuseStep 1236053 = 14485) (by norm_num)
theorem B1858661 : Blo 822348 1858661 := bbase (se 4 (by rfl) ⟨174249, by rfl⟩ : syracuseStep 1858661 = 348499) (by norm_num)
theorem B1236077 : Blo 822348 1236077 := bbase (se 3 (by rfl) ⟨231764, by rfl⟩ : syracuseStep 1236077 = 463529) (by norm_num)
theorem B941177 : Blo 822348 941177 := bbase (se 2 (by rfl) ⟨352941, by rfl⟩ : syracuseStep 941177 = 705883) (by norm_num)
theorem B1563781 : Blo 822348 1563781 := bbase (se 4 (by rfl) ⟨146604, by rfl⟩ : syracuseStep 1563781 = 293209) (by norm_num)
theorem B1236101 : Blo 822348 1236101 := bbase (se 4 (by rfl) ⟨115884, by rfl⟩ : syracuseStep 1236101 = 231769) (by norm_num)
theorem B1236125 : Blo 822348 1236125 := bbase (se 3 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 1236125 = 463547) (by norm_num)
theorem B1858733 : Blo 822348 1858733 := bbase (se 3 (by rfl) ⟨348512, by rfl⟩ : syracuseStep 1858733 = 697025) (by norm_num)
theorem B1236149 : Blo 822348 1236149 := bbase (se 5 (by rfl) ⟨57944, by rfl⟩ : syracuseStep 1236149 = 115889) (by norm_num)
theorem B1236173 : Blo 822348 1236173 := bbase (se 3 (by rfl) ⟨231782, by rfl⟩ : syracuseStep 1236173 = 463565) (by norm_num)
theorem B1236197 : Blo 822348 1236197 := bbase (se 4 (by rfl) ⟨115893, by rfl⟩ : syracuseStep 1236197 = 231787) (by norm_num)
theorem B1760501 : Blo 822348 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B2645237 : Blo 822348 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B1858805 : Blo 822348 1858805 := bbase (se 5 (by rfl) ⟨87131, by rfl⟩ : syracuseStep 1858805 = 174263) (by norm_num)
theorem B1236221 : Blo 822348 1236221 := bbase (se 3 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 1236221 = 463583) (by norm_num)
theorem B1236245 : Blo 822348 1236245 := bbase (se 6 (by rfl) ⟨28974, by rfl⟩ : syracuseStep 1236245 = 57949) (by norm_num)
theorem B1563941 : Blo 822348 1563941 := bbase (se 4 (by rfl) ⟨146619, by rfl⟩ : syracuseStep 1563941 = 293239) (by norm_num)
theorem B1236269 : Blo 822348 1236269 := bbase (se 3 (by rfl) ⟨231800, by rfl⟩ : syracuseStep 1236269 = 463601) (by norm_num)
theorem B7920949 : Blo 822348 7920949 := bbase (se 5 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 7920949 = 742589) (by norm_num)
theorem B1858877 : Blo 822348 1858877 := bbase (se 3 (by rfl) ⟨348539, by rfl⟩ : syracuseStep 1858877 = 697079) (by norm_num)
theorem B1236293 : Blo 822348 1236293 := bbase (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) (by norm_num)
theorem B57105749 : Blo 822348 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B1236317 : Blo 822348 1236317 := bbase (se 3 (by rfl) ⟨231809, by rfl⟩ : syracuseStep 1236317 = 463619) (by norm_num)
theorem B2088301 : Blo 822348 2088301 := bbase (se 3 (by rfl) ⟨391556, by rfl⟩ : syracuseStep 2088301 = 783113) (by norm_num)
theorem B1236341 : Blo 822348 1236341 := bbase (se 5 (by rfl) ⟨57953, by rfl⟩ : syracuseStep 1236341 = 115907) (by norm_num)
theorem B1858949 : Blo 822348 1858949 := bbase (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) (by norm_num)
theorem B1236365 : Blo 822348 1236365 := bbase (se 3 (by rfl) ⟨231818, by rfl⟩ : syracuseStep 1236365 = 463637) (by norm_num)
theorem B1236389 : Blo 822348 1236389 := bbase (se 4 (by rfl) ⟨115911, by rfl⟩ : syracuseStep 1236389 = 231823) (by norm_num)
theorem B1564085 : Blo 822348 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B1236413 : Blo 822348 1236413 := bbase (se 3 (by rfl) ⟨231827, by rfl⟩ : syracuseStep 1236413 = 463655) (by norm_num)
theorem B2776517 : Blo 822348 2776517 := bbase (se 4 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 2776517 = 520597) (by norm_num)
theorem B2973125 : Blo 822348 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B1859021 : Blo 822348 1859021 := bbase (se 3 (by rfl) ⟨348566, by rfl⟩ : syracuseStep 1859021 = 697133) (by norm_num)
theorem B1236437 : Blo 822348 1236437 := bbase (se 7 (by rfl) ⟨14489, by rfl⟩ : syracuseStep 1236437 = 28979) (by norm_num)
theorem B2088413 : Blo 822348 2088413 := bbase (se 3 (by rfl) ⟨391577, by rfl⟩ : syracuseStep 2088413 = 783155) (by norm_num)
theorem B1236461 : Blo 822348 1236461 := bbase (se 3 (by rfl) ⟨231836, by rfl⟩ : syracuseStep 1236461 = 463673) (by norm_num)
theorem B1269245 : Blo 822348 1269245 := bbase (se 3 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 1269245 = 475967) (by norm_num)
theorem B1236485 : Blo 822348 1236485 := bbase (se 4 (by rfl) ⟨115920, by rfl⟩ : syracuseStep 1236485 = 231841) (by norm_num)
theorem B1859093 : Blo 822348 1859093 := bbase (se 6 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 1859093 = 87145) (by norm_num)
theorem B1236509 : Blo 822348 1236509 := bbase (se 3 (by rfl) ⟨231845, by rfl⟩ : syracuseStep 1236509 = 463691) (by norm_num)
theorem B7036469 : Blo 822348 7036469 := bbase (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) (by norm_num)
theorem B1236533 : Blo 822348 1236533 := bbase (se 5 (by rfl) ⟨57962, by rfl⟩ : syracuseStep 1236533 = 115925) (by norm_num)
theorem B1236557 : Blo 822348 1236557 := bbase (se 3 (by rfl) ⟨231854, by rfl⟩ : syracuseStep 1236557 = 463709) (by norm_num)
theorem B1859165 : Blo 822348 1859165 := bbase (se 3 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 1859165 = 697187) (by norm_num)
theorem B1236581 : Blo 822348 1236581 := bbase (se 4 (by rfl) ⟨115929, by rfl⟩ : syracuseStep 1236581 = 231859) (by norm_num)
theorem B1760869 : Blo 822348 1760869 := bbase (se 4 (by rfl) ⟨165081, by rfl⟩ : syracuseStep 1760869 = 330163) (by norm_num)
theorem B1236605 : Blo 822348 1236605 := bbase (se 3 (by rfl) ⟨231863, by rfl⟩ : syracuseStep 1236605 = 463727) (by norm_num)
theorem B2350741 : Blo 822348 2350741 := bbase (se 6 (by rfl) ⟨55095, by rfl⟩ : syracuseStep 2350741 = 110191) (by norm_num)
theorem B1171093 : Blo 822348 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B1236629 : Blo 822348 1236629 := bbase (se 6 (by rfl) ⟨28983, by rfl⟩ : syracuseStep 1236629 = 57967) (by norm_num)
theorem B2088605 : Blo 822348 2088605 := bbase (se 3 (by rfl) ⟨391613, by rfl⟩ : syracuseStep 2088605 = 783227) (by norm_num)
theorem B1859237 : Blo 822348 1859237 := bbase (se 4 (by rfl) ⟨174303, by rfl⟩ : syracuseStep 1859237 = 348607) (by norm_num)
theorem B1236653 : Blo 822348 1236653 := bbase (se 3 (by rfl) ⟨231872, by rfl⟩ : syracuseStep 1236653 = 463745) (by norm_num)
theorem B1236677 : Blo 822348 1236677 := bbase (se 4 (by rfl) ⟨115938, by rfl⟩ : syracuseStep 1236677 = 231877) (by norm_num)
theorem B1564373 : Blo 822348 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B3137237 : Blo 822348 3137237 := bbase (se 7 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 3137237 = 73529) (by norm_num)
theorem B1236701 : Blo 822348 1236701 := bbase (se 3 (by rfl) ⟨231881, by rfl⟩ : syracuseStep 1236701 = 463763) (by norm_num)
theorem B1236725 : Blo 822348 1236725 := bbase (se 5 (by rfl) ⟨57971, by rfl⟩ : syracuseStep 1236725 = 115943) (by norm_num)
theorem B1236749 : Blo 822348 1236749 := bbase (se 3 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 1236749 = 463781) (by norm_num)
theorem B1236773 : Blo 822348 1236773 := bbase (se 4 (by rfl) ⟨115947, by rfl⟩ : syracuseStep 1236773 = 231895) (by norm_num)
theorem B1236797 : Blo 822348 1236797 := bbase (se 3 (by rfl) ⟨231899, by rfl⟩ : syracuseStep 1236797 = 463799) (by norm_num)
theorem B1236821 : Blo 822348 1236821 := bbase (se 9 (by rfl) ⟨3623, by rfl⟩ : syracuseStep 1236821 = 7247) (by norm_num)
theorem B1564525 : Blo 822348 1564525 := bbase (se 3 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 1564525 = 586697) (by norm_num)
theorem B1236845 : Blo 822348 1236845 := bbase (se 3 (by rfl) ⟨231908, by rfl⟩ : syracuseStep 1236845 = 463817) (by norm_num)
theorem B2776949 : Blo 822348 2776949 := bbase (se 5 (by rfl) ⟨130169, by rfl⟩ : syracuseStep 2776949 = 260339) (by norm_num)
theorem B1236869 : Blo 822348 1236869 := bbase (se 4 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 1236869 = 231913) (by norm_num)
theorem B1236893 : Blo 822348 1236893 := bbase (se 3 (by rfl) ⟨231917, by rfl⟩ : syracuseStep 1236893 = 463835) (by norm_num)
theorem B1236917 : Blo 822348 1236917 := bbase (se 5 (by rfl) ⟨57980, by rfl⟩ : syracuseStep 1236917 = 115961) (by norm_num)
theorem B1236941 : Blo 822348 1236941 := bbase (se 3 (by rfl) ⟨231926, by rfl⟩ : syracuseStep 1236941 = 463853) (by norm_num)
theorem B1236965 : Blo 822348 1236965 := bbase (se 4 (by rfl) ⟨115965, by rfl⟩ : syracuseStep 1236965 = 231931) (by norm_num)
theorem B2088949 : Blo 822348 2088949 := bbase (se 5 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 2088949 = 195839) (by norm_num)
theorem B3137525 : Blo 822348 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B1236989 : Blo 822348 1236989 := bbase (se 3 (by rfl) ⟨231935, by rfl⟩ : syracuseStep 1236989 = 463871) (by norm_num)
theorem B1171469 : Blo 822348 1171469 := bbase (se 3 (by rfl) ⟨219650, by rfl⟩ : syracuseStep 1171469 = 439301) (by norm_num)
theorem B1237013 : Blo 822348 1237013 := bbase (se 6 (by rfl) ⟨28992, by rfl⟩ : syracuseStep 1237013 = 57985) (by norm_num)
theorem B1237037 : Blo 822348 1237037 := bbase (se 3 (by rfl) ⟨231944, by rfl⟩ : syracuseStep 1237037 = 463889) (by norm_num)
theorem B1237061 : Blo 822348 1237061 := bbase (se 4 (by rfl) ⟨115974, by rfl⟩ : syracuseStep 1237061 = 231949) (by norm_num)
theorem B1237085 : Blo 822348 1237085 := bbase (se 3 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 1237085 = 463907) (by norm_num)
theorem B2089061 : Blo 822348 2089061 := bbase (se 4 (by rfl) ⟨195849, by rfl⟩ : syracuseStep 2089061 = 391699) (by norm_num)
theorem B1237109 : Blo 822348 1237109 := bbase (se 5 (by rfl) ⟨57989, by rfl⟩ : syracuseStep 1237109 = 115979) (by norm_num)
theorem B1237133 : Blo 822348 1237133 := bbase (se 3 (by rfl) ⟨231962, by rfl⟩ : syracuseStep 1237133 = 463925) (by norm_num)
theorem B1564829 : Blo 822348 1564829 := bbase (se 3 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 1564829 = 586811) (by norm_num)
theorem B1237157 : Blo 822348 1237157 := bbase (se 4 (by rfl) ⟨115983, by rfl⟩ : syracuseStep 1237157 = 231967) (by norm_num)
theorem B1237181 : Blo 822348 1237181 := bbase (se 3 (by rfl) ⟨231971, by rfl⟩ : syracuseStep 1237181 = 463943) (by norm_num)
theorem B1237205 : Blo 822348 1237205 := bbase (se 7 (by rfl) ⟨14498, by rfl⟩ : syracuseStep 1237205 = 28997) (by norm_num)
theorem B1237229 : Blo 822348 1237229 := bbase (se 3 (by rfl) ⟨231980, by rfl⟩ : syracuseStep 1237229 = 463961) (by norm_num)
theorem B1237253 : Blo 822348 1237253 := bbase (se 4 (by rfl) ⟨115992, by rfl⟩ : syracuseStep 1237253 = 231985) (by norm_num)
theorem B1237277 : Blo 822348 1237277 := bbase (se 3 (by rfl) ⟨231989, by rfl⟩ : syracuseStep 1237277 = 463979) (by norm_num)
theorem B2777381 : Blo 822348 2777381 := bbase (se 4 (by rfl) ⟨260379, by rfl⟩ : syracuseStep 2777381 = 520759) (by norm_num)
theorem B2089253 : Blo 822348 2089253 := bbase (se 4 (by rfl) ⟨195867, by rfl⟩ : syracuseStep 2089253 = 391735) (by norm_num)
theorem B1237301 : Blo 822348 1237301 := bbase (se 5 (by rfl) ⟨57998, by rfl⟩ : syracuseStep 1237301 = 115997) (by norm_num)
theorem B1237325 : Blo 822348 1237325 := bbase (se 3 (by rfl) ⟨231998, by rfl⟩ : syracuseStep 1237325 = 463997) (by norm_num)
theorem B1237349 : Blo 822348 1237349 := bbase (se 4 (by rfl) ⟨116001, by rfl⟩ : syracuseStep 1237349 = 232003) (by norm_num)
theorem B1237373 : Blo 822348 1237373 := bbase (se 3 (by rfl) ⟨232007, by rfl⟩ : syracuseStep 1237373 = 464015) (by norm_num)
theorem B1040789 : Blo 822348 1040789 := bbase (se 6 (by rfl) ⟨24393, by rfl⟩ : syracuseStep 1040789 = 48787) (by norm_num)
theorem B1237397 : Blo 822348 1237397 := bbase (se 6 (by rfl) ⟨29001, by rfl⟩ : syracuseStep 1237397 = 58003) (by norm_num)
theorem B1237421 : Blo 822348 1237421 := bbase (se 3 (by rfl) ⟨232016, by rfl⟩ : syracuseStep 1237421 = 464033) (by norm_num)
theorem B2974133 : Blo 822348 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B1237445 : Blo 822348 1237445 := bbase (se 4 (by rfl) ⟨116010, by rfl⟩ : syracuseStep 1237445 = 232021) (by norm_num)
theorem B1040845 : Blo 822348 1040845 := bbase (se 3 (by rfl) ⟨195158, by rfl⟩ : syracuseStep 1040845 = 390317) (by norm_num)
theorem B1237469 : Blo 822348 1237469 := bbase (se 3 (by rfl) ⟨232025, by rfl⟩ : syracuseStep 1237469 = 464051) (by norm_num)
theorem B1237493 : Blo 822348 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B2646533 : Blo 822348 2646533 := bbase (se 4 (by rfl) ⟨248112, by rfl⟩ : syracuseStep 2646533 = 496225) (by norm_num)
theorem B1237517 : Blo 822348 1237517 := bbase (se 3 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 1237517 = 464069) (by norm_num)
theorem B1237541 : Blo 822348 1237541 := bbase (se 4 (by rfl) ⟨116019, by rfl⟩ : syracuseStep 1237541 = 232039) (by norm_num)
theorem B1040941 : Blo 822348 1040941 := bbase (se 3 (by rfl) ⟨195176, by rfl⟩ : syracuseStep 1040941 = 390353) (by norm_num)
theorem B1237565 : Blo 822348 1237565 := bbase (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) (by norm_num)
theorem B1237589 : Blo 822348 1237589 := bbase (se 8 (by rfl) ⟨7251, by rfl⟩ : syracuseStep 1237589 = 14503) (by norm_num)
theorem B1237613 : Blo 822348 1237613 := bbase (se 3 (by rfl) ⟨232052, by rfl⟩ : syracuseStep 1237613 = 464105) (by norm_num)
theorem B2089597 : Blo 822348 2089597 := bbase (se 3 (by rfl) ⟨391799, by rfl⟩ : syracuseStep 2089597 = 783599) (by norm_num)
theorem B1237637 : Blo 822348 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B1237661 : Blo 822348 1237661 := bbase (se 3 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 1237661 = 464123) (by norm_num)
theorem B1237685 : Blo 822348 1237685 := bbase (se 5 (by rfl) ⟨58016, by rfl⟩ : syracuseStep 1237685 = 116033) (by norm_num)
theorem B1237709 : Blo 822348 1237709 := bbase (se 3 (by rfl) ⟨232070, by rfl⟩ : syracuseStep 1237709 = 464141) (by norm_num)
theorem B2777813 : Blo 822348 2777813 := bbase (se 7 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 2777813 = 65105) (by norm_num)
theorem B1041113 : Blo 822348 1041113 := bbase (se 2 (by rfl) ⟨390417, by rfl⟩ : syracuseStep 1041113 = 780835) (by norm_num)
theorem B1237733 : Blo 822348 1237733 := bbase (se 4 (by rfl) ⟨116037, by rfl⟩ : syracuseStep 1237733 = 232075) (by norm_num)
theorem B2351845 : Blo 822348 2351845 := bbase (se 4 (by rfl) ⟨220485, by rfl⟩ : syracuseStep 2351845 = 440971) (by norm_num)
theorem B2089709 : Blo 822348 2089709 := bbase (se 3 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 2089709 = 783641) (by norm_num)
theorem B1237757 : Blo 822348 1237757 := bbase (se 3 (by rfl) ⟨232079, by rfl⟩ : syracuseStep 1237757 = 464159) (by norm_num)
theorem B1041169 : Blo 822348 1041169 := bbase (se 2 (by rfl) ⟨390438, by rfl⟩ : syracuseStep 1041169 = 780877) (by norm_num)
theorem B1237781 : Blo 822348 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B1237805 : Blo 822348 1237805 := bbase (se 3 (by rfl) ⟨232088, by rfl⟩ : syracuseStep 1237805 = 464177) (by norm_num)
theorem B1237829 : Blo 822348 1237829 := bbase (se 4 (by rfl) ⟨116046, by rfl⟩ : syracuseStep 1237829 = 232093) (by norm_num)
theorem B1270613 : Blo 822348 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B1237853 : Blo 822348 1237853 := bbase (se 3 (by rfl) ⟨232097, by rfl⟩ : syracuseStep 1237853 = 464195) (by norm_num)
theorem B1041265 : Blo 822348 1041265 := bbase (se 2 (by rfl) ⟨390474, by rfl⟩ : syracuseStep 1041265 = 780949) (by norm_num)
theorem B1237877 : Blo 822348 1237877 := bbase (se 5 (by rfl) ⟨58025, by rfl⟩ : syracuseStep 1237877 = 116051) (by norm_num)
theorem B1565581 : Blo 822348 1565581 := bbase (se 3 (by rfl) ⟨293546, by rfl⟩ : syracuseStep 1565581 = 587093) (by norm_num)
theorem B1237901 : Blo 822348 1237901 := bbase (se 3 (by rfl) ⟨232106, by rfl⟩ : syracuseStep 1237901 = 464213) (by norm_num)
theorem B1237925 : Blo 822348 1237925 := bbase (se 4 (by rfl) ⟨116055, by rfl⟩ : syracuseStep 1237925 = 232111) (by norm_num)
theorem B2089901 : Blo 822348 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B1237949 : Blo 822348 1237949 := bbase (se 3 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 1237949 = 464231) (by norm_num)
theorem B1237973 : Blo 822348 1237973 := bbase (se 7 (by rfl) ⟨14507, by rfl⟩ : syracuseStep 1237973 = 29015) (by norm_num)
theorem B1237997 : Blo 822348 1237997 := bbase (se 3 (by rfl) ⟨232124, by rfl⟩ : syracuseStep 1237997 = 464249) (by norm_num)
theorem B1238021 : Blo 822348 1238021 := bbase (se 4 (by rfl) ⟨116064, by rfl⟩ : syracuseStep 1238021 = 232129) (by norm_num)
theorem B1041437 : Blo 822348 1041437 := bbase (se 3 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 1041437 = 390539) (by norm_num)
theorem B1565725 : Blo 822348 1565725 := bbase (se 3 (by rfl) ⟨293573, by rfl⟩ : syracuseStep 1565725 = 587147) (by norm_num)
theorem B1238045 : Blo 822348 1238045 := bbase (se 3 (by rfl) ⟨232133, by rfl⟩ : syracuseStep 1238045 = 464267) (by norm_num)
theorem B1238069 : Blo 822348 1238069 := bbase (se 5 (by rfl) ⟨58034, by rfl⟩ : syracuseStep 1238069 = 116069) (by norm_num)
theorem B1762373 : Blo 822348 1762373 := bbase (se 4 (by rfl) ⟨165222, by rfl⟩ : syracuseStep 1762373 = 330445) (by norm_num)
theorem B1238093 : Blo 822348 1238093 := bbase (se 3 (by rfl) ⟨232142, by rfl⟩ : syracuseStep 1238093 = 464285) (by norm_num)
theorem B1041493 : Blo 822348 1041493 := bbase (se 8 (by rfl) ⟨6102, by rfl⟩ : syracuseStep 1041493 = 12205) (by norm_num)
theorem B1238117 : Blo 822348 1238117 := bbase (se 4 (by rfl) ⟨116073, by rfl⟩ : syracuseStep 1238117 = 232147) (by norm_num)
theorem B1238141 : Blo 822348 1238141 := bbase (se 3 (by rfl) ⟨232151, by rfl⟩ : syracuseStep 1238141 = 464303) (by norm_num)
theorem B2778245 : Blo 822348 2778245 := bbase (se 4 (by rfl) ⟨260460, by rfl⟩ : syracuseStep 2778245 = 520921) (by norm_num)
theorem B1238165 : Blo 822348 1238165 := bbase (se 6 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 1238165 = 58039) (by norm_num)
theorem B1238189 : Blo 822348 1238189 := bbase (se 3 (by rfl) ⟨232160, by rfl⟩ : syracuseStep 1238189 = 464321) (by norm_num)
theorem B1041589 : Blo 822348 1041589 := bbase (se 5 (by rfl) ⟨48824, by rfl⟩ : syracuseStep 1041589 = 97649) (by norm_num)
theorem B1565885 : Blo 822348 1565885 := bbase (se 3 (by rfl) ⟨293603, by rfl⟩ : syracuseStep 1565885 = 587207) (by norm_num)
theorem B1238213 : Blo 822348 1238213 := bbase (se 4 (by rfl) ⟨116082, by rfl⟩ : syracuseStep 1238213 = 232165) (by norm_num)
theorem B1762517 : Blo 822348 1762517 := bbase (se 7 (by rfl) ⟨20654, by rfl⟩ : syracuseStep 1762517 = 41309) (by norm_num)
theorem B1238237 : Blo 822348 1238237 := bbase (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) (by norm_num)
theorem B1238261 : Blo 822348 1238261 := bbase (se 5 (by rfl) ⟨58043, by rfl⟩ : syracuseStep 1238261 = 116087) (by norm_num)
theorem B2090245 : Blo 822348 2090245 := bbase (se 4 (by rfl) ⟨195960, by rfl⟩ : syracuseStep 2090245 = 391921) (by norm_num)
theorem B1238285 : Blo 822348 1238285 := bbase (se 3 (by rfl) ⟨232178, by rfl⟩ : syracuseStep 1238285 = 464357) (by norm_num)
theorem B1238309 : Blo 822348 1238309 := bbase (se 4 (by rfl) ⟨116091, by rfl⟩ : syracuseStep 1238309 = 232183) (by norm_num)
theorem B1238333 : Blo 822348 1238333 := bbase (se 3 (by rfl) ⟨232187, by rfl⟩ : syracuseStep 1238333 = 464375) (by norm_num)
theorem B1566029 : Blo 822348 1566029 := bbase (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) (by norm_num)
theorem B1238357 : Blo 822348 1238357 := bbase (se 12 (by rfl) ⟨453, by rfl⟩ : syracuseStep 1238357 = 907) (by norm_num)
theorem B1041761 : Blo 822348 1041761 := bbase (se 2 (by rfl) ⟨390660, by rfl⟩ : syracuseStep 1041761 = 781321) (by norm_num)
theorem B1238381 : Blo 822348 1238381 := bbase (se 3 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 1238381 = 464393) (by norm_num)
theorem B2090357 : Blo 822348 2090357 := bbase (se 5 (by rfl) ⟨97985, by rfl⟩ : syracuseStep 2090357 = 195971) (by norm_num)
theorem B1238405 : Blo 822348 1238405 := bbase (se 4 (by rfl) ⟨116100, by rfl⟩ : syracuseStep 1238405 = 232201) (by norm_num)
theorem B1041817 : Blo 822348 1041817 := bbase (se 2 (by rfl) ⟨390681, by rfl⟩ : syracuseStep 1041817 = 781363) (by norm_num)
theorem B1172893 : Blo 822348 1172893 := bbase (se 3 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 1172893 = 439835) (by norm_num)
theorem B1238429 : Blo 822348 1238429 := bbase (se 3 (by rfl) ⟨232205, by rfl⟩ : syracuseStep 1238429 = 464411) (by norm_num)
theorem B1238453 : Blo 822348 1238453 := bbase (se 5 (by rfl) ⟨58052, by rfl⟩ : syracuseStep 1238453 = 116105) (by norm_num)
theorem B1238477 : Blo 822348 1238477 := bbase (se 3 (by rfl) ⟨232214, by rfl⟩ : syracuseStep 1238477 = 464429) (by norm_num)
theorem B1238501 : Blo 822348 1238501 := bbase (se 4 (by rfl) ⟨116109, by rfl⟩ : syracuseStep 1238501 = 232219) (by norm_num)
theorem B1041913 : Blo 822348 1041913 := bbase (se 2 (by rfl) ⟨390717, by rfl⟩ : syracuseStep 1041913 = 781435) (by norm_num)
theorem B1238525 : Blo 822348 1238525 := bbase (se 3 (by rfl) ⟨232223, by rfl⟩ : syracuseStep 1238525 = 464447) (by norm_num)
theorem B1238549 : Blo 822348 1238549 := bbase (se 6 (by rfl) ⟨29028, by rfl⟩ : syracuseStep 1238549 = 58057) (by norm_num)
theorem B1238573 : Blo 822348 1238573 := bbase (se 3 (by rfl) ⟨232232, by rfl⟩ : syracuseStep 1238573 = 464465) (by norm_num)
theorem B2778677 : Blo 822348 2778677 := bbase (se 5 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 2778677 = 260501) (by norm_num)
theorem B2090549 : Blo 822348 2090549 := bbase (se 5 (by rfl) ⟨97994, by rfl⟩ : syracuseStep 2090549 = 195989) (by norm_num)
theorem B1762877 : Blo 822348 1762877 := bbase (se 3 (by rfl) ⟨330539, by rfl⟩ : syracuseStep 1762877 = 661079) (by norm_num)
theorem B1238597 : Blo 822348 1238597 := bbase (se 4 (by rfl) ⟨116118, by rfl⟩ : syracuseStep 1238597 = 232237) (by norm_num)
theorem B1238621 : Blo 822348 1238621 := bbase (se 3 (by rfl) ⟨232241, by rfl⟩ : syracuseStep 1238621 = 464483) (by norm_num)
theorem B1566317 : Blo 822348 1566317 := bbase (se 3 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 1566317 = 587369) (by norm_num)
theorem B1238645 : Blo 822348 1238645 := bbase (se 5 (by rfl) ⟨58061, by rfl⟩ : syracuseStep 1238645 = 116123) (by norm_num)
theorem B1238669 : Blo 822348 1238669 := bbase (se 3 (by rfl) ⟨232250, by rfl⟩ : syracuseStep 1238669 = 464501) (by norm_num)
theorem B1042085 : Blo 822348 1042085 := bbase (se 4 (by rfl) ⟨97695, by rfl⟩ : syracuseStep 1042085 = 195391) (by norm_num)
theorem B1238693 : Blo 822348 1238693 := bbase (se 4 (by rfl) ⟨116127, by rfl⟩ : syracuseStep 1238693 = 232255) (by norm_num)
theorem B1238717 : Blo 822348 1238717 := bbase (se 3 (by rfl) ⟨232259, by rfl⟩ : syracuseStep 1238717 = 464519) (by norm_num)
theorem B1238741 : Blo 822348 1238741 := bbase (se 7 (by rfl) ⟨14516, by rfl⟩ : syracuseStep 1238741 = 29033) (by norm_num)
theorem B1042141 : Blo 822348 1042141 := bbase (se 3 (by rfl) ⟨195401, by rfl⟩ : syracuseStep 1042141 = 390803) (by norm_num)
theorem B1238765 : Blo 822348 1238765 := bbase (se 3 (by rfl) ⟨232268, by rfl⟩ : syracuseStep 1238765 = 464537) (by norm_num)
theorem B1566469 : Blo 822348 1566469 := bbase (se 4 (by rfl) ⟨146856, by rfl⟩ : syracuseStep 1566469 = 293713) (by norm_num)
theorem B1238789 : Blo 822348 1238789 := bbase (se 4 (by rfl) ⟨116136, by rfl⟩ : syracuseStep 1238789 = 232273) (by norm_num)
theorem B1238813 : Blo 822348 1238813 := bbase (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) (by norm_num)
theorem B1238837 : Blo 822348 1238837 := bbase (se 5 (by rfl) ⟨58070, by rfl⟩ : syracuseStep 1238837 = 116141) (by norm_num)
theorem B1042237 : Blo 822348 1042237 := bbase (se 3 (by rfl) ⟨195419, by rfl⟩ : syracuseStep 1042237 = 390839) (by norm_num)
theorem B1238861 : Blo 822348 1238861 := bbase (se 3 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 1238861 = 464573) (by norm_num)
theorem B1238885 : Blo 822348 1238885 := bbase (se 4 (by rfl) ⟨116145, by rfl⟩ : syracuseStep 1238885 = 232291) (by norm_num)
theorem B1238909 : Blo 822348 1238909 := bbase (se 3 (by rfl) ⟨232295, by rfl⟩ : syracuseStep 1238909 = 464591) (by norm_num)
theorem B2090893 : Blo 822348 2090893 := bbase (se 3 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 2090893 = 784085) (by norm_num)
theorem B1238933 : Blo 822348 1238933 := bbase (se 6 (by rfl) ⟨29037, by rfl⟩ : syracuseStep 1238933 = 58075) (by norm_num)
theorem B1238957 : Blo 822348 1238957 := bbase (se 3 (by rfl) ⟨232304, by rfl⟩ : syracuseStep 1238957 = 464609) (by norm_num)
theorem B878521 : Blo 822348 878521 := bbase (se 2 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 878521 = 658891) (by norm_num)
theorem B1238981 : Blo 822348 1238981 := bbase (se 4 (by rfl) ⟨116154, by rfl⟩ : syracuseStep 1238981 = 232309) (by norm_num)
theorem B15820757 : Blo 822348 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B1239005 : Blo 822348 1239005 := bbase (se 3 (by rfl) ⟨232313, by rfl⟩ : syracuseStep 1239005 = 464627) (by norm_num)
theorem B2779109 : Blo 822348 2779109 := bbase (se 4 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 2779109 = 521083) (by norm_num)
theorem B1042409 : Blo 822348 1042409 := bbase (se 2 (by rfl) ⟨390903, by rfl⟩ : syracuseStep 1042409 = 781807) (by norm_num)
theorem B1173485 : Blo 822348 1173485 := bbase (se 3 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 1173485 = 440057) (by norm_num)
theorem B1239029 : Blo 822348 1239029 := bbase (se 5 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 1239029 = 116159) (by norm_num)
theorem B2091005 : Blo 822348 2091005 := bbase (se 3 (by rfl) ⟨392063, by rfl⟩ : syracuseStep 2091005 = 784127) (by norm_num)
theorem B1239053 : Blo 822348 1239053 := bbase (se 3 (by rfl) ⟨232322, by rfl⟩ : syracuseStep 1239053 = 464645) (by norm_num)
theorem B1042465 : Blo 822348 1042465 := bbase (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) (by norm_num)
theorem B1239077 : Blo 822348 1239077 := bbase (se 4 (by rfl) ⟨116163, by rfl⟩ : syracuseStep 1239077 = 232327) (by norm_num)
theorem B1566773 : Blo 822348 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B1173565 : Blo 822348 1173565 := bbase (se 3 (by rfl) ⟨220043, by rfl⟩ : syracuseStep 1173565 = 440087) (by norm_num)
theorem B1239101 : Blo 822348 1239101 := bbase (se 3 (by rfl) ⟨232331, by rfl⟩ : syracuseStep 1239101 = 464663) (by norm_num)
theorem B1239125 : Blo 822348 1239125 := bbase (se 8 (by rfl) ⟨7260, by rfl⟩ : syracuseStep 1239125 = 14521) (by norm_num)
theorem B1239149 : Blo 822348 1239149 := bbase (se 3 (by rfl) ⟨232340, by rfl⟩ : syracuseStep 1239149 = 464681) (by norm_num)
theorem B1042561 : Blo 822348 1042561 := bbase (se 2 (by rfl) ⟨390960, by rfl⟩ : syracuseStep 1042561 = 781921) (by norm_num)
theorem B1239173 : Blo 822348 1239173 := bbase (se 4 (by rfl) ⟨116172, by rfl⟩ : syracuseStep 1239173 = 232345) (by norm_num)
theorem B1239197 : Blo 822348 1239197 := bbase (se 3 (by rfl) ⟨232349, by rfl⟩ : syracuseStep 1239197 = 464699) (by norm_num)
theorem B1173685 : Blo 822348 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B1239221 : Blo 822348 1239221 := bbase (se 5 (by rfl) ⟨58088, by rfl⟩ : syracuseStep 1239221 = 116177) (by norm_num)
theorem B2091197 : Blo 822348 2091197 := bbase (se 3 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 2091197 = 784199) (by norm_num)
theorem B1239245 : Blo 822348 1239245 := bbase (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) (by norm_num)
theorem B26699989 : Blo 822348 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B1239269 : Blo 822348 1239269 := bbase (se 4 (by rfl) ⟨116181, by rfl⟩ : syracuseStep 1239269 = 232363) (by norm_num)
theorem B1239293 : Blo 822348 1239293 := bbase (se 3 (by rfl) ⟨232367, by rfl⟩ : syracuseStep 1239293 = 464735) (by norm_num)
theorem B1173781 : Blo 822348 1173781 := bbase (se 6 (by rfl) ⟨27510, by rfl⟩ : syracuseStep 1173781 = 55021) (by norm_num)
theorem B1239317 : Blo 822348 1239317 := bbase (se 6 (by rfl) ⟨29046, by rfl⟩ : syracuseStep 1239317 = 58093) (by norm_num)
theorem B1042733 : Blo 822348 1042733 := bbase (se 3 (by rfl) ⟨195512, by rfl⟩ : syracuseStep 1042733 = 391025) (by norm_num)
theorem B1239341 : Blo 822348 1239341 := bbase (se 3 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 1239341 = 464753) (by norm_num)
theorem B878897 : Blo 822348 878897 := bbase (se 2 (by rfl) ⟨329586, by rfl⟩ : syracuseStep 878897 = 659173) (by norm_num)
theorem B1239365 : Blo 822348 1239365 := bbase (se 4 (by rfl) ⟨116190, by rfl⟩ : syracuseStep 1239365 = 232381) (by norm_num)
theorem B1239389 : Blo 822348 1239389 := bbase (se 3 (by rfl) ⟨232385, by rfl⟩ : syracuseStep 1239389 = 464771) (by norm_num)
theorem B1042789 : Blo 822348 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B1239413 : Blo 822348 1239413 := bbase (se 5 (by rfl) ⟨58097, by rfl⟩ : syracuseStep 1239413 = 116195) (by norm_num)
theorem B878969 : Blo 822348 878969 := bbase (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) (by norm_num)
theorem B1239437 : Blo 822348 1239437 := bbase (se 3 (by rfl) ⟨232394, by rfl⟩ : syracuseStep 1239437 = 464789) (by norm_num)
theorem B2779541 : Blo 822348 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B3959189 : Blo 822348 3959189 := bbase (se 6 (by rfl) ⟨92793, by rfl⟩ : syracuseStep 3959189 = 185587) (by norm_num)
theorem B1239461 : Blo 822348 1239461 := bbase (se 4 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 1239461 = 232399) (by norm_num)
theorem B1763765 : Blo 822348 1763765 := bbase (se 5 (by rfl) ⟨82676, by rfl⟩ : syracuseStep 1763765 = 165353) (by norm_num)
theorem B1239485 : Blo 822348 1239485 := bbase (se 3 (by rfl) ⟨232403, by rfl⟩ : syracuseStep 1239485 = 464807) (by norm_num)
theorem B1042885 : Blo 822348 1042885 := bbase (se 4 (by rfl) ⟨97770, by rfl⟩ : syracuseStep 1042885 = 195541) (by norm_num)
theorem B1239509 : Blo 822348 1239509 := bbase (se 7 (by rfl) ⟨14525, by rfl⟩ : syracuseStep 1239509 = 29051) (by norm_num)
theorem B2091541 : Blo 822348 2091541 := bbase (se 6 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 2091541 = 98041) (by norm_num)
theorem B879157 : Blo 822348 879157 := bbase (se 5 (by rfl) ⟨41210, by rfl⟩ : syracuseStep 879157 = 82421) (by norm_num)
theorem B1043057 : Blo 822348 1043057 := bbase (se 2 (by rfl) ⟨391146, by rfl⟩ : syracuseStep 1043057 = 782293) (by norm_num)
theorem B2091653 : Blo 822348 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1043113 : Blo 822348 1043113 := bbase (se 2 (by rfl) ⟨391167, by rfl⟩ : syracuseStep 1043113 = 782335) (by norm_num)
theorem B1764013 : Blo 822348 1764013 := bbase (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) (by norm_num)
theorem B879341 : Blo 822348 879341 := bbase (se 3 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 879341 = 329753) (by norm_num)
theorem B1174277 : Blo 822348 1174277 := bbase (se 4 (by rfl) ⟨110088, by rfl⟩ : syracuseStep 1174277 = 220177) (by norm_num)
theorem B1043209 : Blo 822348 1043209 := bbase (se 2 (by rfl) ⟨391203, by rfl⟩ : syracuseStep 1043209 = 782407) (by norm_num)
theorem B1567525 : Blo 822348 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B3337013 : Blo 822348 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B2779973 : Blo 822348 2779973 := bbase (se 4 (by rfl) ⟨260622, by rfl⟩ : syracuseStep 2779973 = 521245) (by norm_num)
theorem B1043381 : Blo 822348 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B1567669 : Blo 822348 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B1043437 : Blo 822348 1043437 := bbase (se 3 (by rfl) ⟨195644, by rfl⟩ : syracuseStep 1043437 = 391289) (by norm_num)
theorem B1043533 : Blo 822348 1043533 := bbase (se 3 (by rfl) ⟨195662, by rfl⟩ : syracuseStep 1043533 = 391325) (by norm_num)
theorem B1567829 : Blo 822348 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B1764517 : Blo 822348 1764517 := bbase (se 4 (by rfl) ⟨165423, by rfl⟩ : syracuseStep 1764517 = 330847) (by norm_num)
theorem B1567973 : Blo 822348 1567973 := bbase (se 4 (by rfl) ⟨146997, by rfl⟩ : syracuseStep 1567973 = 293995) (by norm_num)
theorem B2780405 : Blo 822348 2780405 := bbase (se 5 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 2780405 = 260663) (by norm_num)
theorem B1043705 : Blo 822348 1043705 := bbase (se 2 (by rfl) ⟨391389, by rfl⟩ : syracuseStep 1043705 = 782779) (by norm_num)
theorem B1174829 : Blo 822348 1174829 := bbase (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) (by norm_num)
theorem B1043761 : Blo 822348 1043761 := bbase (se 2 (by rfl) ⟨391410, by rfl⟩ : syracuseStep 1043761 = 782821) (by norm_num)
theorem B1043857 : Blo 822348 1043857 := bbase (se 2 (by rfl) ⟨391446, by rfl⟩ : syracuseStep 1043857 = 782893) (by norm_num)
theorem B7925141 : Blo 822348 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B880093 : Blo 822348 880093 := bbase (se 3 (by rfl) ⟨165017, by rfl⟩ : syracuseStep 880093 = 330035) (by norm_num)
theorem B1568261 : Blo 822348 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B880165 : Blo 822348 880165 := bbase (se 4 (by rfl) ⟨82515, by rfl⟩ : syracuseStep 880165 = 165031) (by norm_num)
theorem B1044029 : Blo 822348 1044029 := bbase (se 3 (by rfl) ⟨195755, by rfl⟩ : syracuseStep 1044029 = 391511) (by norm_num)
theorem B1044085 : Blo 822348 1044085 := bbase (se 5 (by rfl) ⟨48941, by rfl⟩ : syracuseStep 1044085 = 97883) (by norm_num)
theorem B1568413 : Blo 822348 1568413 := bbase (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) (by norm_num)
theorem B1502885 : Blo 822348 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B2780837 : Blo 822348 2780837 := bbase (se 4 (by rfl) ⟨260703, by rfl⟩ : syracuseStep 2780837 = 521407) (by norm_num)
theorem B1044181 : Blo 822348 1044181 := bbase (se 7 (by rfl) ⟨12236, by rfl⟩ : syracuseStep 1044181 = 24473) (by norm_num)
theorem B880345 : Blo 822348 880345 := bbase (se 2 (by rfl) ⟨330129, by rfl⟩ : syracuseStep 880345 = 660259) (by norm_num)
theorem B1044353 : Blo 822348 1044353 := bbase (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) (by norm_num)
theorem B1044409 : Blo 822348 1044409 := bbase (se 2 (by rfl) ⟨391653, by rfl⟩ : syracuseStep 1044409 = 783307) (by norm_num)
theorem B1568717 : Blo 822348 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B1044505 : Blo 822348 1044505 := bbase (se 2 (by rfl) ⟨391689, by rfl⟩ : syracuseStep 1044505 = 783379) (by norm_num)
theorem B1175581 : Blo 822348 1175581 := bbase (se 3 (by rfl) ⟨220421, by rfl⟩ : syracuseStep 1175581 = 440843) (by norm_num)
theorem B2781269 : Blo 822348 2781269 := bbase (se 8 (by rfl) ⟨16296, by rfl⟩ : syracuseStep 2781269 = 32593) (by norm_num)
theorem B880789 : Blo 822348 880789 := bbase (se 6 (by rfl) ⟨20643, by rfl⟩ : syracuseStep 880789 = 41287) (by norm_num)
theorem B1044677 : Blo 822348 1044677 := bbase (se 4 (by rfl) ⟨97938, by rfl⟩ : syracuseStep 1044677 = 195877) (by norm_num)
theorem B1044733 : Blo 822348 1044733 := bbase (se 3 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 1044733 = 391775) (by norm_num)
theorem B880913 : Blo 822348 880913 := bbase (se 2 (by rfl) ⟨330342, by rfl⟩ : syracuseStep 880913 = 660685) (by norm_num)
theorem B1667405 : Blo 822348 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B1044829 : Blo 822348 1044829 := bbase (se 3 (by rfl) ⟨195905, by rfl⟩ : syracuseStep 1044829 = 391811) (by norm_num)
theorem B4747733 : Blo 822348 4747733 := bbase (se 7 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 4747733 = 111275) (by norm_num)
theorem B2781701 : Blo 822348 2781701 := bbase (se 4 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 2781701 = 521569) (by norm_num)
theorem B1045001 : Blo 822348 1045001 := bbase (se 2 (by rfl) ⟨391875, by rfl⟩ : syracuseStep 1045001 = 783751) (by norm_num)
theorem B881165 : Blo 822348 881165 := bbase (se 3 (by rfl) ⟨165218, by rfl⟩ : syracuseStep 881165 = 330437) (by norm_num)
theorem B1045057 : Blo 822348 1045057 := bbase (se 2 (by rfl) ⟨391896, by rfl⟩ : syracuseStep 1045057 = 783793) (by norm_num)
theorem B1045153 : Blo 822348 1045153 := bbase (se 2 (by rfl) ⟨391932, by rfl⟩ : syracuseStep 1045153 = 783865) (by norm_num)
theorem B1176373 : Blo 822348 1176373 := bbase (se 5 (by rfl) ⟨55142, by rfl⟩ : syracuseStep 1176373 = 110285) (by norm_num)
theorem B1045325 : Blo 822348 1045325 := bbase (se 3 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 1045325 = 391997) (by norm_num)
theorem B1045381 : Blo 822348 1045381 := bbase (se 4 (by rfl) ⟨98004, by rfl⟩ : syracuseStep 1045381 = 196009) (by norm_num)
theorem B2782133 : Blo 822348 2782133 := bbase (se 5 (by rfl) ⟨130412, by rfl⟩ : syracuseStep 2782133 = 260825) (by norm_num)
theorem B881609 : Blo 822348 881609 := bbase (se 2 (by rfl) ⟨330603, by rfl⟩ : syracuseStep 881609 = 661207) (by norm_num)
theorem B1045477 : Blo 822348 1045477 := bbase (se 4 (by rfl) ⟨98013, by rfl⟩ : syracuseStep 1045477 = 196027) (by norm_num)
theorem B1504261 : Blo 822348 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B3339269 : Blo 822348 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B3961973 : Blo 822348 3961973 := bbase (se 5 (by rfl) ⟨185717, by rfl⟩ : syracuseStep 3961973 = 371435) (by norm_num)
theorem B1045649 : Blo 822348 1045649 := bbase (se 2 (by rfl) ⟨392118, by rfl⟩ : syracuseStep 1045649 = 784237) (by norm_num)
theorem B881857 : Blo 822348 881857 := bbase (se 2 (by rfl) ⟨330696, by rfl⟩ : syracuseStep 881857 = 661393) (by norm_num)
theorem B1045705 : Blo 822348 1045705 := bbase (se 2 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 1045705 = 784279) (by norm_num)
theorem B5272789 : Blo 822348 5272789 := bbase (se 7 (by rfl) ⟨61790, by rfl⟩ : syracuseStep 5272789 = 123581) (by norm_num)
theorem B1045801 : Blo 822348 1045801 := bbase (se 2 (by rfl) ⟨392175, by rfl⟩ : syracuseStep 1045801 = 784351) (by norm_num)
theorem B2782565 : Blo 822348 2782565 := bbase (se 4 (by rfl) ⟨260865, by rfl⟩ : syracuseStep 2782565 = 521731) (by norm_num)
theorem B2258405 : Blo 822348 2258405 := bbase (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) (by norm_num)
theorem B1111549 : Blo 822348 1111549 := bbase (se 3 (by rfl) ⟨208415, by rfl⟩ : syracuseStep 1111549 = 416831) (by norm_num)
theorem B882301 : Blo 822348 882301 := bbase (se 3 (by rfl) ⟨165431, by rfl⟩ : syracuseStep 882301 = 330863) (by norm_num)
theorem B6256277 : Blo 822348 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B882361 : Blo 822348 882361 := bbase (se 2 (by rfl) ⟨330885, by rfl⟩ : syracuseStep 882361 = 661771) (by norm_num)
theorem B2782997 : Blo 822348 2782997 := bbase (se 6 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 2782997 = 130453) (by norm_num)
theorem B1406845 : Blo 822348 1406845 := bbase (se 3 (by rfl) ⟨263783, by rfl⟩ : syracuseStep 1406845 = 527567) (by norm_num)
theorem B3766181 : Blo 822348 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B4454453 : Blo 822348 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B1669205 : Blo 822348 1669205 := bbase (se 8 (by rfl) ⟨9780, by rfl⟩ : syracuseStep 1669205 = 19561) (by norm_num)
theorem B1669285 : Blo 822348 1669285 := bbase (se 4 (by rfl) ⟨156495, by rfl⟩ : syracuseStep 1669285 = 312991) (by norm_num)
theorem B2783429 : Blo 822348 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B2783861 : Blo 822348 2783861 := bbase (se 5 (by rfl) ⟨130493, by rfl⟩ : syracuseStep 2783861 = 260987) (by norm_num)
theorem B4455125 : Blo 822348 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B1669901 : Blo 822348 1669901 := bbase (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) (by norm_num)
theorem B4225877 : Blo 822348 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B1407989 : Blo 822348 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B2784293 : Blo 822348 2784293 := bbase (se 4 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 2784293 = 522055) (by norm_num)
theorem B1113149 : Blo 822348 1113149 := bbase (se 3 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 1113149 = 417431) (by norm_num)
theorem B1670485 : Blo 822348 1670485 := bbase (se 11 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1670485 = 2447) (by norm_num)
theorem B4521365 : Blo 822348 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B2784725 : Blo 822348 2784725 := bbase (se 7 (by rfl) ⟨32633, by rfl⟩ : syracuseStep 2784725 = 65267) (by norm_num)
theorem B6356789 : Blo 822348 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B2785157 : Blo 822348 2785157 := bbase (se 4 (by rfl) ⟨261108, by rfl⟩ : syracuseStep 2785157 = 522217) (by norm_num)
theorem B5275637 : Blo 822348 5275637 := bbase (se 5 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 5275637 = 494591) (by norm_num)
theorem B22610117 : Blo 822348 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B1114403 : Blo 822348 1114403 := bstep (se 1 (by rfl) ⟨835802, by rfl⟩ : syracuseStep 1114403 = 1671605) B1671605
theorem B1114435 : Blo 822348 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B5636465 : Blo 822348 5636465 := bstep (se 2 (by rfl) ⟨2113674, by rfl⟩ : syracuseStep 5636465 = 4227349) B4227349
theorem B1409411 : Blo 822348 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B2785805 : Blo 822348 2785805 := bstep (se 3 (by rfl) ⟨522338, by rfl⟩ : syracuseStep 2785805 = 1044677) B1044677
theorem B1409555 : Blo 822348 1409555 := bstep (se 1 (by rfl) ⟨1057166, by rfl⟩ : syracuseStep 1409555 = 2114333) B2114333
theorem B1507889 : Blo 822348 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B2785859 : Blo 822348 2785859 := bstep (se 1 (by rfl) ⟨2089394, by rfl⟩ : syracuseStep 2785859 = 4178789) B4178789
theorem B4686605 : Blo 822348 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B2786129 : Blo 822348 2786129 := bstep (se 2 (by rfl) ⟨1044798, by rfl⟩ : syracuseStep 2786129 = 2089597) B2089597
theorem B1115041 : Blo 822348 1115041 := bstep (se 2 (by rfl) ⟨418140, by rfl⟩ : syracuseStep 1115041 = 836281) B836281
theorem B6358115 : Blo 822348 6358115 := bstep (se 1 (by rfl) ⟨4768586, by rfl⟩ : syracuseStep 6358115 = 9537173) B9537173
theorem B10028357 : Blo 822348 10028357 := bstep (se 4 (by rfl) ⟨940158, by rfl⟩ : syracuseStep 10028357 = 1880317) B1880317
theorem B2786669 : Blo 822348 2786669 := bstep (se 3 (by rfl) ⟨522500, by rfl⟩ : syracuseStep 2786669 = 1045001) B1045001
theorem B2786723 : Blo 822348 2786723 := bstep (se 1 (by rfl) ⟨2090042, by rfl⟩ : syracuseStep 2786723 = 4180085) B4180085
theorem B1672643 : Blo 822348 1672643 := bstep (se 1 (by rfl) ⟨1254482, by rfl⟩ : syracuseStep 1672643 = 2508965) B2508965
theorem B6260165 : Blo 822348 6260165 := bstep (se 4 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 6260165 = 1173781) B1173781
theorem B4752901 : Blo 822348 4752901 := bstep (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) B891169
theorem B2786993 : Blo 822348 2786993 := bstep (se 2 (by rfl) ⟨1045122, by rfl⟩ : syracuseStep 2786993 = 2090245) B2090245
theorem B2820205 : Blo 822348 2820205 := bstep (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) B1057577
theorem B2787533 : Blo 822348 2787533 := bstep (se 3 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 2787533 = 1045325) B1045325
theorem B2787587 : Blo 822348 2787587 := bstep (se 1 (by rfl) ⟨2090690, by rfl⟩ : syracuseStep 2787587 = 4181381) B4181381
theorem B2263427 : Blo 822348 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B2787857 : Blo 822348 2787857 := bstep (se 2 (by rfl) ⟨1045446, by rfl⟩ : syracuseStep 2787857 = 2090893) B2090893
theorem B2230861 : Blo 822348 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B4164209 : Blo 822348 4164209 := bstep (se 2 (by rfl) ⟨1561578, by rfl⟩ : syracuseStep 4164209 = 3123157) B3123157
theorem B14093027 : Blo 822348 14093027 := bstep (se 1 (by rfl) ⟨10569770, by rfl⟩ : syracuseStep 14093027 = 21139541) B21139541
theorem B4688837 : Blo 822348 4688837 := bstep (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) B879157
theorem B2788397 : Blo 822348 2788397 := bstep (se 3 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 2788397 = 1045649) B1045649
theorem B822355 : Blo 822348 822355 := bstep (se 1 (by rfl) ⟨616766, by rfl⟩ : syracuseStep 822355 = 1233533) B1233533
theorem B822371 : Blo 822348 822371 := bstep (se 1 (by rfl) ⟨616778, by rfl⟩ : syracuseStep 822371 = 1233557) B1233557
theorem B2788451 : Blo 822348 2788451 := bstep (se 1 (by rfl) ⟨2091338, by rfl⟩ : syracuseStep 2788451 = 4182677) B4182677
theorem B822387 : Blo 822348 822387 := bstep (se 1 (by rfl) ⟨616790, by rfl⟩ : syracuseStep 822387 = 1233581) B1233581
theorem B822403 : Blo 822348 822403 := bstep (se 1 (by rfl) ⟨616802, by rfl⟩ : syracuseStep 822403 = 1233605) B1233605
theorem B822419 : Blo 822348 822419 := bstep (se 1 (by rfl) ⟨616814, by rfl⟩ : syracuseStep 822419 = 1233629) B1233629
theorem B822435 : Blo 822348 822435 := bstep (se 1 (by rfl) ⟨616826, by rfl⟩ : syracuseStep 822435 = 1233653) B1233653
theorem B822451 : Blo 822348 822451 := bstep (se 1 (by rfl) ⟨616838, by rfl⟩ : syracuseStep 822451 = 1233677) B1233677
theorem B822467 : Blo 822348 822467 := bstep (se 1 (by rfl) ⟨616850, by rfl⟩ : syracuseStep 822467 = 1233701) B1233701
theorem B822483 : Blo 822348 822483 := bstep (se 1 (by rfl) ⟨616862, by rfl⟩ : syracuseStep 822483 = 1233725) B1233725
theorem B822499 : Blo 822348 822499 := bstep (se 1 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 822499 = 1233749) B1233749
theorem B822515 : Blo 822348 822515 := bstep (se 1 (by rfl) ⟨616886, by rfl⟩ : syracuseStep 822515 = 1233773) B1233773
theorem B822531 : Blo 822348 822531 := bstep (se 1 (by rfl) ⟨616898, by rfl⟩ : syracuseStep 822531 = 1233797) B1233797
theorem B822547 : Blo 822348 822547 := bstep (se 1 (by rfl) ⟨616910, by rfl⟩ : syracuseStep 822547 = 1233821) B1233821
theorem B822563 : Blo 822348 822563 := bstep (se 1 (by rfl) ⟨616922, by rfl⟩ : syracuseStep 822563 = 1233845) B1233845
theorem B822579 : Blo 822348 822579 := bstep (se 1 (by rfl) ⟨616934, by rfl⟩ : syracuseStep 822579 = 1233869) B1233869
theorem B822595 : Blo 822348 822595 := bstep (se 1 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 822595 = 1233893) B1233893
theorem B822611 : Blo 822348 822611 := bstep (se 1 (by rfl) ⟨616958, by rfl⟩ : syracuseStep 822611 = 1233917) B1233917
theorem B822627 : Blo 822348 822627 := bstep (se 1 (by rfl) ⟨616970, by rfl⟩ : syracuseStep 822627 = 1233941) B1233941
theorem B2788721 : Blo 822348 2788721 := bstep (se 2 (by rfl) ⟨1045770, by rfl⟩ : syracuseStep 2788721 = 2091541) B2091541
theorem B822643 : Blo 822348 822643 := bstep (se 1 (by rfl) ⟨616982, by rfl⟩ : syracuseStep 822643 = 1233965) B1233965
theorem B822659 : Blo 822348 822659 := bstep (se 1 (by rfl) ⟨616994, by rfl⟩ : syracuseStep 822659 = 1233989) B1233989
theorem B822675 : Blo 822348 822675 := bstep (se 1 (by rfl) ⟨617006, by rfl⟩ : syracuseStep 822675 = 1234013) B1234013
theorem B822691 : Blo 822348 822691 := bstep (se 1 (by rfl) ⟨617018, by rfl⟩ : syracuseStep 822691 = 1234037) B1234037
theorem B822707 : Blo 822348 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B822723 : Blo 822348 822723 := bstep (se 1 (by rfl) ⟨617042, by rfl⟩ : syracuseStep 822723 = 1234085) B1234085
theorem B2821571 : Blo 822348 2821571 := bstep (se 1 (by rfl) ⟨2116178, by rfl⟩ : syracuseStep 2821571 = 4232357) B4232357
theorem B822739 : Blo 822348 822739 := bstep (se 1 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 822739 = 1234109) B1234109
theorem B822755 : Blo 822348 822755 := bstep (se 1 (by rfl) ⟨617066, by rfl⟩ : syracuseStep 822755 = 1234133) B1234133
theorem B822771 : Blo 822348 822771 := bstep (se 1 (by rfl) ⟨617078, by rfl⟩ : syracuseStep 822771 = 1234157) B1234157
theorem B822787 : Blo 822348 822787 := bstep (se 1 (by rfl) ⟨617090, by rfl⟩ : syracuseStep 822787 = 1234181) B1234181
theorem B822803 : Blo 822348 822803 := bstep (se 1 (by rfl) ⟨617102, by rfl⟩ : syracuseStep 822803 = 1234205) B1234205
theorem B822819 : Blo 822348 822819 := bstep (se 1 (by rfl) ⟨617114, by rfl⟩ : syracuseStep 822819 = 1234229) B1234229
theorem B822835 : Blo 822348 822835 := bstep (se 1 (by rfl) ⟨617126, by rfl⟩ : syracuseStep 822835 = 1234253) B1234253
theorem B822851 : Blo 822348 822851 := bstep (se 1 (by rfl) ⟨617138, by rfl⟩ : syracuseStep 822851 = 1234277) B1234277
theorem B822867 : Blo 822348 822867 := bstep (se 1 (by rfl) ⟨617150, by rfl⟩ : syracuseStep 822867 = 1234301) B1234301
theorem B822883 : Blo 822348 822883 := bstep (se 1 (by rfl) ⟨617162, by rfl⟩ : syracuseStep 822883 = 1234325) B1234325
theorem B4689521 : Blo 822348 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B822899 : Blo 822348 822899 := bstep (se 1 (by rfl) ⟨617174, by rfl⟩ : syracuseStep 822899 = 1234349) B1234349
theorem B822915 : Blo 822348 822915 := bstep (se 1 (by rfl) ⟨617186, by rfl⟩ : syracuseStep 822915 = 1234373) B1234373
theorem B822931 : Blo 822348 822931 := bstep (se 1 (by rfl) ⟨617198, by rfl⟩ : syracuseStep 822931 = 1234397) B1234397
theorem B822947 : Blo 822348 822947 := bstep (se 1 (by rfl) ⟨617210, by rfl⟩ : syracuseStep 822947 = 1234421) B1234421
theorem B822963 : Blo 822348 822963 := bstep (se 1 (by rfl) ⟨617222, by rfl⟩ : syracuseStep 822963 = 1234445) B1234445
theorem B822979 : Blo 822348 822979 := bstep (se 1 (by rfl) ⟨617234, by rfl⟩ : syracuseStep 822979 = 1234469) B1234469
theorem B822995 : Blo 822348 822995 := bstep (se 1 (by rfl) ⟨617246, by rfl⟩ : syracuseStep 822995 = 1234493) B1234493
theorem B823011 : Blo 822348 823011 := bstep (se 1 (by rfl) ⟨617258, by rfl⟩ : syracuseStep 823011 = 1234517) B1234517
theorem B823027 : Blo 822348 823027 := bstep (se 1 (by rfl) ⟨617270, by rfl⟩ : syracuseStep 823027 = 1234541) B1234541
theorem B823043 : Blo 822348 823043 := bstep (se 1 (by rfl) ⟨617282, by rfl⟩ : syracuseStep 823043 = 1234565) B1234565
theorem B823059 : Blo 822348 823059 := bstep (se 1 (by rfl) ⟨617294, by rfl⟩ : syracuseStep 823059 = 1234589) B1234589
theorem B823075 : Blo 822348 823075 := bstep (se 1 (by rfl) ⟨617306, by rfl⟩ : syracuseStep 823075 = 1234613) B1234613
theorem B823091 : Blo 822348 823091 := bstep (se 1 (by rfl) ⟨617318, by rfl⟩ : syracuseStep 823091 = 1234637) B1234637
theorem B823107 : Blo 822348 823107 := bstep (se 1 (by rfl) ⟨617330, by rfl⟩ : syracuseStep 823107 = 1234661) B1234661
theorem B823123 : Blo 822348 823123 := bstep (se 1 (by rfl) ⟨617342, by rfl⟩ : syracuseStep 823123 = 1234685) B1234685
theorem B823139 : Blo 822348 823139 := bstep (se 1 (by rfl) ⟨617354, by rfl⟩ : syracuseStep 823139 = 1234709) B1234709
theorem B823155 : Blo 822348 823155 := bstep (se 1 (by rfl) ⟨617366, by rfl⟩ : syracuseStep 823155 = 1234733) B1234733
theorem B823171 : Blo 822348 823171 := bstep (se 1 (by rfl) ⟨617378, by rfl⟩ : syracuseStep 823171 = 1234757) B1234757
theorem B823187 : Blo 822348 823187 := bstep (se 1 (by rfl) ⟨617390, by rfl⟩ : syracuseStep 823187 = 1234781) B1234781
theorem B823203 : Blo 822348 823203 := bstep (se 1 (by rfl) ⟨617402, by rfl⟩ : syracuseStep 823203 = 1234805) B1234805
theorem B823219 : Blo 822348 823219 := bstep (se 1 (by rfl) ⟨617414, by rfl⟩ : syracuseStep 823219 = 1234829) B1234829
theorem B823235 : Blo 822348 823235 := bstep (se 1 (by rfl) ⟨617426, by rfl⟩ : syracuseStep 823235 = 1234853) B1234853
theorem B823251 : Blo 822348 823251 := bstep (se 1 (by rfl) ⟨617438, by rfl⟩ : syracuseStep 823251 = 1234877) B1234877
theorem B823267 : Blo 822348 823267 := bstep (se 1 (by rfl) ⟨617450, by rfl⟩ : syracuseStep 823267 = 1234901) B1234901
theorem B15044579 : Blo 822348 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B6033379 : Blo 822348 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B823283 : Blo 822348 823283 := bstep (se 1 (by rfl) ⟨617462, by rfl⟩ : syracuseStep 823283 = 1234925) B1234925
theorem B823299 : Blo 822348 823299 := bstep (se 1 (by rfl) ⟨617474, by rfl⟩ : syracuseStep 823299 = 1234949) B1234949
theorem B823315 : Blo 822348 823315 := bstep (se 1 (by rfl) ⟨617486, by rfl⟩ : syracuseStep 823315 = 1234973) B1234973
theorem B4165667 : Blo 822348 4165667 := bstep (se 1 (by rfl) ⟨3124250, by rfl⟩ : syracuseStep 4165667 = 6248501) B6248501
theorem B823331 : Blo 822348 823331 := bstep (se 1 (by rfl) ⟨617498, by rfl⟩ : syracuseStep 823331 = 1234997) B1234997
theorem B823347 : Blo 822348 823347 := bstep (se 1 (by rfl) ⟨617510, by rfl⟩ : syracuseStep 823347 = 1235021) B1235021
theorem B823363 : Blo 822348 823363 := bstep (se 1 (by rfl) ⟨617522, by rfl⟩ : syracuseStep 823363 = 1235045) B1235045
theorem B5279813 : Blo 822348 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B823379 : Blo 822348 823379 := bstep (se 1 (by rfl) ⟨617534, by rfl⟩ : syracuseStep 823379 = 1235069) B1235069
theorem B823395 : Blo 822348 823395 := bstep (se 1 (by rfl) ⟨617546, by rfl⟩ : syracuseStep 823395 = 1235093) B1235093
theorem B823411 : Blo 822348 823411 := bstep (se 1 (by rfl) ⟨617558, by rfl⟩ : syracuseStep 823411 = 1235117) B1235117
theorem B823427 : Blo 822348 823427 := bstep (se 1 (by rfl) ⟨617570, by rfl⟩ : syracuseStep 823427 = 1235141) B1235141
theorem B2232461 : Blo 822348 2232461 := bstep (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) B837173
theorem B823443 : Blo 822348 823443 := bstep (se 1 (by rfl) ⟨617582, by rfl⟩ : syracuseStep 823443 = 1235165) B1235165
theorem B823459 : Blo 822348 823459 := bstep (se 1 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 823459 = 1235189) B1235189
theorem B823475 : Blo 822348 823475 := bstep (se 1 (by rfl) ⟨617606, by rfl⟩ : syracuseStep 823475 = 1235213) B1235213
theorem B823491 : Blo 822348 823491 := bstep (se 1 (by rfl) ⟨617618, by rfl⟩ : syracuseStep 823491 = 1235237) B1235237
theorem B823507 : Blo 822348 823507 := bstep (se 1 (by rfl) ⟨617630, by rfl⟩ : syracuseStep 823507 = 1235261) B1235261
theorem B823523 : Blo 822348 823523 := bstep (se 1 (by rfl) ⟨617642, by rfl⟩ : syracuseStep 823523 = 1235285) B1235285
theorem B823539 : Blo 822348 823539 := bstep (se 1 (by rfl) ⟨617654, by rfl⟩ : syracuseStep 823539 = 1235309) B1235309
theorem B823555 : Blo 822348 823555 := bstep (se 1 (by rfl) ⟨617666, by rfl⟩ : syracuseStep 823555 = 1235333) B1235333
theorem B823571 : Blo 822348 823571 := bstep (se 1 (by rfl) ⟨617678, by rfl⟩ : syracuseStep 823571 = 1235357) B1235357
theorem B823587 : Blo 822348 823587 := bstep (se 1 (by rfl) ⟨617690, by rfl⟩ : syracuseStep 823587 = 1235381) B1235381
theorem B823603 : Blo 822348 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B823619 : Blo 822348 823619 := bstep (se 1 (by rfl) ⟨617714, by rfl⟩ : syracuseStep 823619 = 1235429) B1235429
theorem B823635 : Blo 822348 823635 := bstep (se 1 (by rfl) ⟨617726, by rfl⟩ : syracuseStep 823635 = 1235453) B1235453
theorem B823651 : Blo 822348 823651 := bstep (se 1 (by rfl) ⟨617738, by rfl⟩ : syracuseStep 823651 = 1235477) B1235477
theorem B823667 : Blo 822348 823667 := bstep (se 1 (by rfl) ⟨617750, by rfl⟩ : syracuseStep 823667 = 1235501) B1235501
theorem B823683 : Blo 822348 823683 := bstep (se 1 (by rfl) ⟨617762, by rfl⟩ : syracuseStep 823683 = 1235525) B1235525
theorem B823699 : Blo 822348 823699 := bstep (se 1 (by rfl) ⟨617774, by rfl⟩ : syracuseStep 823699 = 1235549) B1235549
theorem B823715 : Blo 822348 823715 := bstep (se 1 (by rfl) ⟨617786, by rfl⟩ : syracuseStep 823715 = 1235573) B1235573
theorem B823731 : Blo 822348 823731 := bstep (se 1 (by rfl) ⟨617798, by rfl⟩ : syracuseStep 823731 = 1235597) B1235597
theorem B10555829 : Blo 822348 10555829 := bstep (se 5 (by rfl) ⟨494804, by rfl⟩ : syracuseStep 10555829 = 989609) B989609
theorem B823747 : Blo 822348 823747 := bstep (se 1 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 823747 = 1235621) B1235621
theorem B2232785 : Blo 822348 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B823763 : Blo 822348 823763 := bstep (se 1 (by rfl) ⟨617822, by rfl⟩ : syracuseStep 823763 = 1235645) B1235645
theorem B823779 : Blo 822348 823779 := bstep (se 1 (by rfl) ⟨617834, by rfl⟩ : syracuseStep 823779 = 1235669) B1235669
theorem B823795 : Blo 822348 823795 := bstep (se 1 (by rfl) ⟨617846, by rfl⟩ : syracuseStep 823795 = 1235693) B1235693
theorem B823811 : Blo 822348 823811 := bstep (se 1 (by rfl) ⟨617858, by rfl⟩ : syracuseStep 823811 = 1235717) B1235717
theorem B823827 : Blo 822348 823827 := bstep (se 1 (by rfl) ⟨617870, by rfl⟩ : syracuseStep 823827 = 1235741) B1235741
theorem B823843 : Blo 822348 823843 := bstep (se 1 (by rfl) ⟨617882, by rfl⟩ : syracuseStep 823843 = 1235765) B1235765
theorem B823859 : Blo 822348 823859 := bstep (se 1 (by rfl) ⟨617894, by rfl⟩ : syracuseStep 823859 = 1235789) B1235789
theorem B823875 : Blo 822348 823875 := bstep (se 1 (by rfl) ⟨617906, by rfl⟩ : syracuseStep 823875 = 1235813) B1235813
theorem B823891 : Blo 822348 823891 := bstep (se 1 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 823891 = 1235837) B1235837
theorem B823907 : Blo 822348 823907 := bstep (se 1 (by rfl) ⟨617930, by rfl⟩ : syracuseStep 823907 = 1235861) B1235861
theorem B823923 : Blo 822348 823923 := bstep (se 1 (by rfl) ⟨617942, by rfl⟩ : syracuseStep 823923 = 1235885) B1235885
theorem B823939 : Blo 822348 823939 := bstep (se 1 (by rfl) ⟨617954, by rfl⟩ : syracuseStep 823939 = 1235909) B1235909
theorem B9376397 : Blo 822348 9376397 := bstep (se 3 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 9376397 = 3516149) B3516149
theorem B823955 : Blo 822348 823955 := bstep (se 1 (by rfl) ⟨617966, by rfl⟩ : syracuseStep 823955 = 1235933) B1235933
theorem B823971 : Blo 822348 823971 := bstep (se 1 (by rfl) ⟨617978, by rfl⟩ : syracuseStep 823971 = 1235957) B1235957
theorem B823987 : Blo 822348 823987 := bstep (se 1 (by rfl) ⟨617990, by rfl⟩ : syracuseStep 823987 = 1235981) B1235981
theorem B824003 : Blo 822348 824003 := bstep (se 1 (by rfl) ⟨618002, by rfl⟩ : syracuseStep 824003 = 1236005) B1236005
theorem B824019 : Blo 822348 824019 := bstep (se 1 (by rfl) ⟨618014, by rfl⟩ : syracuseStep 824019 = 1236029) B1236029
theorem B824035 : Blo 822348 824035 := bstep (se 1 (by rfl) ⟨618026, by rfl⟩ : syracuseStep 824035 = 1236053) B1236053
theorem B824051 : Blo 822348 824051 := bstep (se 1 (by rfl) ⟨618038, by rfl⟩ : syracuseStep 824051 = 1236077) B1236077
theorem B824067 : Blo 822348 824067 := bstep (se 1 (by rfl) ⟨618050, by rfl⟩ : syracuseStep 824067 = 1236101) B1236101
theorem B824083 : Blo 822348 824083 := bstep (se 1 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 824083 = 1236125) B1236125
theorem B824099 : Blo 822348 824099 := bstep (se 1 (by rfl) ⟨618074, by rfl⟩ : syracuseStep 824099 = 1236149) B1236149
theorem B824115 : Blo 822348 824115 := bstep (se 1 (by rfl) ⟨618086, by rfl⟩ : syracuseStep 824115 = 1236173) B1236173
theorem B824131 : Blo 822348 824131 := bstep (se 1 (by rfl) ⟨618098, by rfl⟩ : syracuseStep 824131 = 1236197) B1236197
theorem B4166477 : Blo 822348 4166477 := bstep (se 3 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 4166477 = 1562429) B1562429
theorem B824147 : Blo 822348 824147 := bstep (se 1 (by rfl) ⟨618110, by rfl⟩ : syracuseStep 824147 = 1236221) B1236221
theorem B824163 : Blo 822348 824163 := bstep (se 1 (by rfl) ⟨618122, by rfl⟩ : syracuseStep 824163 = 1236245) B1236245
theorem B824179 : Blo 822348 824179 := bstep (se 1 (by rfl) ⟨618134, by rfl⟩ : syracuseStep 824179 = 1236269) B1236269
theorem B824195 : Blo 822348 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B824211 : Blo 822348 824211 := bstep (se 1 (by rfl) ⟨618158, by rfl⟩ : syracuseStep 824211 = 1236317) B1236317
theorem B824227 : Blo 822348 824227 := bstep (se 1 (by rfl) ⟨618170, by rfl⟩ : syracuseStep 824227 = 1236341) B1236341
theorem B824243 : Blo 822348 824243 := bstep (se 1 (by rfl) ⟨618182, by rfl⟩ : syracuseStep 824243 = 1236365) B1236365
theorem B824259 : Blo 822348 824259 := bstep (se 1 (by rfl) ⟨618194, by rfl⟩ : syracuseStep 824259 = 1236389) B1236389
theorem B824275 : Blo 822348 824275 := bstep (se 1 (by rfl) ⟨618206, by rfl⟩ : syracuseStep 824275 = 1236413) B1236413
theorem B824291 : Blo 822348 824291 := bstep (se 1 (by rfl) ⟨618218, by rfl⟩ : syracuseStep 824291 = 1236437) B1236437
theorem B824307 : Blo 822348 824307 := bstep (se 1 (by rfl) ⟨618230, by rfl⟩ : syracuseStep 824307 = 1236461) B1236461
theorem B824323 : Blo 822348 824323 := bstep (se 1 (by rfl) ⟨618242, by rfl⟩ : syracuseStep 824323 = 1236485) B1236485
theorem B824339 : Blo 822348 824339 := bstep (se 1 (by rfl) ⟨618254, by rfl⟩ : syracuseStep 824339 = 1236509) B1236509
theorem B4690979 : Blo 822348 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B824355 : Blo 822348 824355 := bstep (se 1 (by rfl) ⟨618266, by rfl⟩ : syracuseStep 824355 = 1236533) B1236533
theorem B824371 : Blo 822348 824371 := bstep (se 1 (by rfl) ⟨618278, by rfl⟩ : syracuseStep 824371 = 1236557) B1236557
theorem B824387 : Blo 822348 824387 := bstep (se 1 (by rfl) ⟨618290, by rfl⟩ : syracuseStep 824387 = 1236581) B1236581
theorem B824403 : Blo 822348 824403 := bstep (se 1 (by rfl) ⟨618302, by rfl⟩ : syracuseStep 824403 = 1236605) B1236605
theorem B824419 : Blo 822348 824419 := bstep (se 1 (by rfl) ⟨618314, by rfl⟩ : syracuseStep 824419 = 1236629) B1236629
theorem B824435 : Blo 822348 824435 := bstep (se 1 (by rfl) ⟨618326, by rfl⟩ : syracuseStep 824435 = 1236653) B1236653
theorem B824451 : Blo 822348 824451 := bstep (se 1 (by rfl) ⟨618338, by rfl⟩ : syracuseStep 824451 = 1236677) B1236677
theorem B824467 : Blo 822348 824467 := bstep (se 1 (by rfl) ⟨618350, by rfl⟩ : syracuseStep 824467 = 1236701) B1236701
theorem B824483 : Blo 822348 824483 := bstep (se 1 (by rfl) ⟨618362, by rfl⟩ : syracuseStep 824483 = 1236725) B1236725
theorem B824499 : Blo 822348 824499 := bstep (se 1 (by rfl) ⟨618374, by rfl⟩ : syracuseStep 824499 = 1236749) B1236749
theorem B824515 : Blo 822348 824515 := bstep (se 1 (by rfl) ⟨618386, by rfl⟩ : syracuseStep 824515 = 1236773) B1236773
theorem B824531 : Blo 822348 824531 := bstep (se 1 (by rfl) ⟨618398, by rfl⟩ : syracuseStep 824531 = 1236797) B1236797
theorem B824547 : Blo 822348 824547 := bstep (se 1 (by rfl) ⟨618410, by rfl⟩ : syracuseStep 824547 = 1236821) B1236821
theorem B824563 : Blo 822348 824563 := bstep (se 1 (by rfl) ⟨618422, by rfl⟩ : syracuseStep 824563 = 1236845) B1236845
theorem B824579 : Blo 822348 824579 := bstep (se 1 (by rfl) ⟨618434, by rfl⟩ : syracuseStep 824579 = 1236869) B1236869
theorem B824595 : Blo 822348 824595 := bstep (se 1 (by rfl) ⟨618446, by rfl⟩ : syracuseStep 824595 = 1236893) B1236893
theorem B824611 : Blo 822348 824611 := bstep (se 1 (by rfl) ⟨618458, by rfl⟩ : syracuseStep 824611 = 1236917) B1236917
theorem B824627 : Blo 822348 824627 := bstep (se 1 (by rfl) ⟨618470, by rfl⟩ : syracuseStep 824627 = 1236941) B1236941
theorem B824643 : Blo 822348 824643 := bstep (se 1 (by rfl) ⟨618482, by rfl⟩ : syracuseStep 824643 = 1236965) B1236965
theorem B824659 : Blo 822348 824659 := bstep (se 1 (by rfl) ⟨618494, by rfl⟩ : syracuseStep 824659 = 1236989) B1236989
theorem B824675 : Blo 822348 824675 := bstep (se 1 (by rfl) ⟨618506, by rfl⟩ : syracuseStep 824675 = 1237013) B1237013
theorem B824691 : Blo 822348 824691 := bstep (se 1 (by rfl) ⟨618518, by rfl⟩ : syracuseStep 824691 = 1237037) B1237037
theorem B824707 : Blo 822348 824707 := bstep (se 1 (by rfl) ⟨618530, by rfl⟩ : syracuseStep 824707 = 1237061) B1237061
theorem B824723 : Blo 822348 824723 := bstep (se 1 (by rfl) ⟨618542, by rfl⟩ : syracuseStep 824723 = 1237085) B1237085
theorem B824739 : Blo 822348 824739 := bstep (se 1 (by rfl) ⟨618554, by rfl⟩ : syracuseStep 824739 = 1237109) B1237109
theorem B824755 : Blo 822348 824755 := bstep (se 1 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 824755 = 1237133) B1237133
theorem B824771 : Blo 822348 824771 := bstep (se 1 (by rfl) ⟨618578, by rfl⟩ : syracuseStep 824771 = 1237157) B1237157
theorem B824787 : Blo 822348 824787 := bstep (se 1 (by rfl) ⟨618590, by rfl⟩ : syracuseStep 824787 = 1237181) B1237181
theorem B824803 : Blo 822348 824803 := bstep (se 1 (by rfl) ⟨618602, by rfl⟩ : syracuseStep 824803 = 1237205) B1237205
theorem B824819 : Blo 822348 824819 := bstep (se 1 (by rfl) ⟨618614, by rfl⟩ : syracuseStep 824819 = 1237229) B1237229
theorem B824835 : Blo 822348 824835 := bstep (se 1 (by rfl) ⟨618626, by rfl⟩ : syracuseStep 824835 = 1237253) B1237253
theorem B824851 : Blo 822348 824851 := bstep (se 1 (by rfl) ⟨618638, by rfl⟩ : syracuseStep 824851 = 1237277) B1237277
theorem B824867 : Blo 822348 824867 := bstep (se 1 (by rfl) ⟨618650, by rfl⟩ : syracuseStep 824867 = 1237301) B1237301
theorem B824883 : Blo 822348 824883 := bstep (se 1 (by rfl) ⟨618662, by rfl⟩ : syracuseStep 824883 = 1237325) B1237325
theorem B824899 : Blo 822348 824899 := bstep (se 1 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 824899 = 1237349) B1237349
theorem B824915 : Blo 822348 824915 := bstep (se 1 (by rfl) ⟨618686, by rfl⟩ : syracuseStep 824915 = 1237373) B1237373
theorem B824931 : Blo 822348 824931 := bstep (se 1 (by rfl) ⟨618698, by rfl⟩ : syracuseStep 824931 = 1237397) B1237397
theorem B12719729 : Blo 822348 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B824947 : Blo 822348 824947 := bstep (se 1 (by rfl) ⟨618710, by rfl⟩ : syracuseStep 824947 = 1237421) B1237421
theorem B824963 : Blo 822348 824963 := bstep (se 1 (by rfl) ⟨618722, by rfl⟩ : syracuseStep 824963 = 1237445) B1237445
theorem B824979 : Blo 822348 824979 := bstep (se 1 (by rfl) ⟨618734, by rfl⟩ : syracuseStep 824979 = 1237469) B1237469
theorem B824995 : Blo 822348 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B825011 : Blo 822348 825011 := bstep (se 1 (by rfl) ⟨618758, by rfl⟩ : syracuseStep 825011 = 1237517) B1237517
theorem B825027 : Blo 822348 825027 := bstep (se 1 (by rfl) ⟨618770, by rfl⟩ : syracuseStep 825027 = 1237541) B1237541
theorem B825043 : Blo 822348 825043 := bstep (se 1 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 825043 = 1237565) B1237565
theorem B825059 : Blo 822348 825059 := bstep (se 1 (by rfl) ⟨618794, by rfl⟩ : syracuseStep 825059 = 1237589) B1237589
theorem B825075 : Blo 822348 825075 := bstep (se 1 (by rfl) ⟨618806, by rfl⟩ : syracuseStep 825075 = 1237613) B1237613
theorem B825091 : Blo 822348 825091 := bstep (se 1 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 825091 = 1237637) B1237637
theorem B825107 : Blo 822348 825107 := bstep (se 1 (by rfl) ⟨618830, by rfl⟩ : syracuseStep 825107 = 1237661) B1237661
theorem B3610403 : Blo 822348 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B825123 : Blo 822348 825123 := bstep (se 1 (by rfl) ⟨618842, by rfl⟩ : syracuseStep 825123 = 1237685) B1237685
theorem B825139 : Blo 822348 825139 := bstep (se 1 (by rfl) ⟨618854, by rfl⟩ : syracuseStep 825139 = 1237709) B1237709
theorem B825155 : Blo 822348 825155 := bstep (se 1 (by rfl) ⟨618866, by rfl⟩ : syracuseStep 825155 = 1237733) B1237733
theorem B825171 : Blo 822348 825171 := bstep (se 1 (by rfl) ⟨618878, by rfl⟩ : syracuseStep 825171 = 1237757) B1237757
theorem B825187 : Blo 822348 825187 := bstep (se 1 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 825187 = 1237781) B1237781
theorem B825203 : Blo 822348 825203 := bstep (se 1 (by rfl) ⟨618902, by rfl⟩ : syracuseStep 825203 = 1237805) B1237805
theorem B825219 : Blo 822348 825219 := bstep (se 1 (by rfl) ⟨618914, by rfl⟩ : syracuseStep 825219 = 1237829) B1237829
theorem B825235 : Blo 822348 825235 := bstep (se 1 (by rfl) ⟨618926, by rfl⟩ : syracuseStep 825235 = 1237853) B1237853
theorem B825251 : Blo 822348 825251 := bstep (se 1 (by rfl) ⟨618938, by rfl⟩ : syracuseStep 825251 = 1237877) B1237877
theorem B825267 : Blo 822348 825267 := bstep (se 1 (by rfl) ⟨618950, by rfl⟩ : syracuseStep 825267 = 1237901) B1237901
theorem B825283 : Blo 822348 825283 := bstep (se 1 (by rfl) ⟨618962, by rfl⟩ : syracuseStep 825283 = 1237925) B1237925
theorem B825299 : Blo 822348 825299 := bstep (se 1 (by rfl) ⟨618974, by rfl⟩ : syracuseStep 825299 = 1237949) B1237949
theorem B825315 : Blo 822348 825315 := bstep (se 1 (by rfl) ⟨618986, by rfl⟩ : syracuseStep 825315 = 1237973) B1237973
theorem B825331 : Blo 822348 825331 := bstep (se 1 (by rfl) ⟨618998, by rfl⟩ : syracuseStep 825331 = 1237997) B1237997
theorem B825347 : Blo 822348 825347 := bstep (se 1 (by rfl) ⟨619010, by rfl⟩ : syracuseStep 825347 = 1238021) B1238021
theorem B825363 : Blo 822348 825363 := bstep (se 1 (by rfl) ⟨619022, by rfl⟩ : syracuseStep 825363 = 1238045) B1238045
theorem B825379 : Blo 822348 825379 := bstep (se 1 (by rfl) ⟨619034, by rfl⟩ : syracuseStep 825379 = 1238069) B1238069
theorem B825395 : Blo 822348 825395 := bstep (se 1 (by rfl) ⟨619046, by rfl⟩ : syracuseStep 825395 = 1238093) B1238093
theorem B825411 : Blo 822348 825411 := bstep (se 1 (by rfl) ⟨619058, by rfl⟩ : syracuseStep 825411 = 1238117) B1238117
theorem B825427 : Blo 822348 825427 := bstep (se 1 (by rfl) ⟨619070, by rfl⟩ : syracuseStep 825427 = 1238141) B1238141
theorem B825443 : Blo 822348 825443 := bstep (se 1 (by rfl) ⟨619082, by rfl⟩ : syracuseStep 825443 = 1238165) B1238165
theorem B825459 : Blo 822348 825459 := bstep (se 1 (by rfl) ⟨619094, by rfl⟩ : syracuseStep 825459 = 1238189) B1238189
theorem B825475 : Blo 822348 825475 := bstep (se 1 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 825475 = 1238213) B1238213
theorem B825491 : Blo 822348 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B825507 : Blo 822348 825507 := bstep (se 1 (by rfl) ⟨619130, by rfl⟩ : syracuseStep 825507 = 1238261) B1238261
theorem B825523 : Blo 822348 825523 := bstep (se 1 (by rfl) ⟨619142, by rfl⟩ : syracuseStep 825523 = 1238285) B1238285
theorem B825539 : Blo 822348 825539 := bstep (se 1 (by rfl) ⟨619154, by rfl⟩ : syracuseStep 825539 = 1238309) B1238309
theorem B825555 : Blo 822348 825555 := bstep (se 1 (by rfl) ⟨619166, by rfl⟩ : syracuseStep 825555 = 1238333) B1238333
theorem B825571 : Blo 822348 825571 := bstep (se 1 (by rfl) ⟨619178, by rfl⟩ : syracuseStep 825571 = 1238357) B1238357
theorem B825587 : Blo 822348 825587 := bstep (se 1 (by rfl) ⟨619190, by rfl⟩ : syracuseStep 825587 = 1238381) B1238381
theorem B825603 : Blo 822348 825603 := bstep (se 1 (by rfl) ⟨619202, by rfl⟩ : syracuseStep 825603 = 1238405) B1238405
theorem B825619 : Blo 822348 825619 := bstep (se 1 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 825619 = 1238429) B1238429
theorem B825635 : Blo 822348 825635 := bstep (se 1 (by rfl) ⟨619226, by rfl⟩ : syracuseStep 825635 = 1238453) B1238453
theorem B825651 : Blo 822348 825651 := bstep (se 1 (by rfl) ⟨619238, by rfl⟩ : syracuseStep 825651 = 1238477) B1238477
theorem B825667 : Blo 822348 825667 := bstep (se 1 (by rfl) ⟨619250, by rfl⟩ : syracuseStep 825667 = 1238501) B1238501
theorem B825683 : Blo 822348 825683 := bstep (se 1 (by rfl) ⟨619262, by rfl⟩ : syracuseStep 825683 = 1238525) B1238525
theorem B825699 : Blo 822348 825699 := bstep (se 1 (by rfl) ⟨619274, by rfl⟩ : syracuseStep 825699 = 1238549) B1238549
theorem B825715 : Blo 822348 825715 := bstep (se 1 (by rfl) ⟨619286, by rfl⟩ : syracuseStep 825715 = 1238573) B1238573
theorem B825731 : Blo 822348 825731 := bstep (se 1 (by rfl) ⟨619298, by rfl⟩ : syracuseStep 825731 = 1238597) B1238597
theorem B3512717 : Blo 822348 3512717 := bstep (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) B1317269
theorem B825747 : Blo 822348 825747 := bstep (se 1 (by rfl) ⟨619310, by rfl⟩ : syracuseStep 825747 = 1238621) B1238621
theorem B825763 : Blo 822348 825763 := bstep (se 1 (by rfl) ⟨619322, by rfl⟩ : syracuseStep 825763 = 1238645) B1238645
theorem B825779 : Blo 822348 825779 := bstep (se 1 (by rfl) ⟨619334, by rfl⟩ : syracuseStep 825779 = 1238669) B1238669
theorem B825795 : Blo 822348 825795 := bstep (se 1 (by rfl) ⟨619346, by rfl⟩ : syracuseStep 825795 = 1238693) B1238693
theorem B825811 : Blo 822348 825811 := bstep (se 1 (by rfl) ⟨619358, by rfl⟩ : syracuseStep 825811 = 1238717) B1238717
theorem B825827 : Blo 822348 825827 := bstep (se 1 (by rfl) ⟨619370, by rfl⟩ : syracuseStep 825827 = 1238741) B1238741
theorem B825843 : Blo 822348 825843 := bstep (se 1 (by rfl) ⟨619382, by rfl⟩ : syracuseStep 825843 = 1238765) B1238765
theorem B825859 : Blo 822348 825859 := bstep (se 1 (by rfl) ⟨619394, by rfl⟩ : syracuseStep 825859 = 1238789) B1238789
theorem B825875 : Blo 822348 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B825891 : Blo 822348 825891 := bstep (se 1 (by rfl) ⟨619418, by rfl⟩ : syracuseStep 825891 = 1238837) B1238837
theorem B825907 : Blo 822348 825907 := bstep (se 1 (by rfl) ⟨619430, by rfl⟩ : syracuseStep 825907 = 1238861) B1238861
theorem B825923 : Blo 822348 825923 := bstep (se 1 (by rfl) ⟨619442, by rfl⟩ : syracuseStep 825923 = 1238885) B1238885
theorem B825939 : Blo 822348 825939 := bstep (se 1 (by rfl) ⟨619454, by rfl⟩ : syracuseStep 825939 = 1238909) B1238909
theorem B825955 : Blo 822348 825955 := bstep (se 1 (by rfl) ⟨619466, by rfl⟩ : syracuseStep 825955 = 1238933) B1238933
theorem B825971 : Blo 822348 825971 := bstep (se 1 (by rfl) ⟨619478, by rfl⟩ : syracuseStep 825971 = 1238957) B1238957
theorem B825987 : Blo 822348 825987 := bstep (se 1 (by rfl) ⟨619490, by rfl⟩ : syracuseStep 825987 = 1238981) B1238981
theorem B826003 : Blo 822348 826003 := bstep (se 1 (by rfl) ⟨619502, by rfl⟩ : syracuseStep 826003 = 1239005) B1239005
theorem B826019 : Blo 822348 826019 := bstep (se 1 (by rfl) ⟨619514, by rfl⟩ : syracuseStep 826019 = 1239029) B1239029
theorem B2005681 : Blo 822348 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B826035 : Blo 822348 826035 := bstep (se 1 (by rfl) ⟨619526, by rfl⟩ : syracuseStep 826035 = 1239053) B1239053
theorem B826051 : Blo 822348 826051 := bstep (se 1 (by rfl) ⟨619538, by rfl⟩ : syracuseStep 826051 = 1239077) B1239077
theorem B1252049 : Blo 822348 1252049 := bstep (se 2 (by rfl) ⟨469518, by rfl⟩ : syracuseStep 1252049 = 939037) B939037
theorem B826067 : Blo 822348 826067 := bstep (se 1 (by rfl) ⟨619550, by rfl⟩ : syracuseStep 826067 = 1239101) B1239101
theorem B826083 : Blo 822348 826083 := bstep (se 1 (by rfl) ⟨619562, by rfl⟩ : syracuseStep 826083 = 1239125) B1239125
theorem B826099 : Blo 822348 826099 := bstep (se 1 (by rfl) ⟨619574, by rfl⟩ : syracuseStep 826099 = 1239149) B1239149
theorem B826115 : Blo 822348 826115 := bstep (se 1 (by rfl) ⟨619586, by rfl⟩ : syracuseStep 826115 = 1239173) B1239173
theorem B826131 : Blo 822348 826131 := bstep (se 1 (by rfl) ⟨619598, by rfl⟩ : syracuseStep 826131 = 1239197) B1239197
theorem B826147 : Blo 822348 826147 := bstep (se 1 (by rfl) ⟨619610, by rfl⟩ : syracuseStep 826147 = 1239221) B1239221
theorem B826163 : Blo 822348 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B826179 : Blo 822348 826179 := bstep (se 1 (by rfl) ⟨619634, by rfl⟩ : syracuseStep 826179 = 1239269) B1239269
theorem B826195 : Blo 822348 826195 := bstep (se 1 (by rfl) ⟨619646, by rfl⟩ : syracuseStep 826195 = 1239293) B1239293
theorem B826211 : Blo 822348 826211 := bstep (se 1 (by rfl) ⟨619658, by rfl⟩ : syracuseStep 826211 = 1239317) B1239317
theorem B826227 : Blo 822348 826227 := bstep (se 1 (by rfl) ⟨619670, by rfl⟩ : syracuseStep 826227 = 1239341) B1239341
theorem B826243 : Blo 822348 826243 := bstep (se 1 (by rfl) ⟨619682, by rfl⟩ : syracuseStep 826243 = 1239365) B1239365
theorem B826259 : Blo 822348 826259 := bstep (se 1 (by rfl) ⟨619694, by rfl⟩ : syracuseStep 826259 = 1239389) B1239389
theorem B826275 : Blo 822348 826275 := bstep (se 1 (by rfl) ⟨619706, by rfl⟩ : syracuseStep 826275 = 1239413) B1239413
theorem B826291 : Blo 822348 826291 := bstep (se 1 (by rfl) ⟨619718, by rfl⟩ : syracuseStep 826291 = 1239437) B1239437
theorem B826307 : Blo 822348 826307 := bstep (se 1 (by rfl) ⟨619730, by rfl⟩ : syracuseStep 826307 = 1239461) B1239461
theorem B826323 : Blo 822348 826323 := bstep (se 1 (by rfl) ⟨619742, by rfl⟩ : syracuseStep 826323 = 1239485) B1239485
theorem B826339 : Blo 822348 826339 := bstep (se 1 (by rfl) ⟨619754, by rfl⟩ : syracuseStep 826339 = 1239509) B1239509
theorem B2825293 : Blo 822348 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B6265997 : Blo 822348 6265997 := bstep (se 3 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 6265997 = 2349749) B2349749
theorem B1186979 : Blo 822348 1186979 := bstep (se 1 (by rfl) ⟨890234, by rfl⟩ : syracuseStep 1186979 = 1780469) B1780469
theorem B1318211 : Blo 822348 1318211 := bstep (se 1 (by rfl) ⟨988658, by rfl⟩ : syracuseStep 1318211 = 1977317) B1977317
theorem B1482065 : Blo 822348 1482065 := bstep (se 2 (by rfl) ⟨555774, by rfl⟩ : syracuseStep 1482065 = 1111549) B1111549
theorem B57187781 : Blo 822348 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B9379313 : Blo 822348 9379313 := bstep (se 2 (by rfl) ⟨3517242, by rfl⟩ : syracuseStep 9379313 = 7034485) B7034485
theorem B1318403 : Blo 822348 1318403 := bstep (se 1 (by rfl) ⟨988802, by rfl⟩ : syracuseStep 1318403 = 1977605) B1977605
theorem B925267 : Blo 822348 925267 := bstep (se 1 (by rfl) ⟨693950, by rfl⟩ : syracuseStep 925267 = 1387901) B1387901
theorem B1252961 : Blo 822348 1252961 := bstep (se 2 (by rfl) ⟨469860, by rfl⟩ : syracuseStep 1252961 = 939721) B939721
theorem B5283427 : Blo 822348 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B1318531 : Blo 822348 1318531 := bstep (se 1 (by rfl) ⟨988898, by rfl⟩ : syracuseStep 1318531 = 1977797) B1977797
theorem B1253011 : Blo 822348 1253011 := bstep (se 1 (by rfl) ⟨939758, by rfl⟩ : syracuseStep 1253011 = 1879517) B1879517
theorem B4169393 : Blo 822348 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B925411 : Blo 822348 925411 := bstep (se 1 (by rfl) ⟨694058, by rfl⟩ : syracuseStep 925411 = 1388117) B1388117
theorem B1875793 : Blo 822348 1875793 := bstep (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) B1406845
theorem B925555 : Blo 822348 925555 := bstep (se 1 (by rfl) ⟨694166, by rfl⟩ : syracuseStep 925555 = 1388333) B1388333
theorem B1187713 : Blo 822348 1187713 := bstep (se 2 (by rfl) ⟨445392, by rfl⟩ : syracuseStep 1187713 = 890785) B890785
theorem B925699 : Blo 822348 925699 := bstep (se 1 (by rfl) ⟨694274, by rfl⟩ : syracuseStep 925699 = 1388549) B1388549
theorem B925843 : Blo 822348 925843 := bstep (se 1 (by rfl) ⟨694382, by rfl⟩ : syracuseStep 925843 = 1388765) B1388765
theorem B4694213 : Blo 822348 4694213 := bstep (se 4 (by rfl) ⟨440082, by rfl⟩ : syracuseStep 4694213 = 880165) B880165
theorem B1319171 : Blo 822348 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B925987 : Blo 822348 925987 := bstep (se 1 (by rfl) ⟨694490, by rfl⟩ : syracuseStep 925987 = 1388981) B1388981
theorem B1319249 : Blo 822348 1319249 := bstep (se 2 (by rfl) ⟨494718, by rfl⟩ : syracuseStep 1319249 = 989437) B989437
theorem B926131 : Blo 822348 926131 := bstep (se 1 (by rfl) ⟨694598, by rfl⟩ : syracuseStep 926131 = 1389197) B1389197
theorem B926275 : Blo 822348 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B4694669 : Blo 822348 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B7053965 : Blo 822348 7053965 := bstep (se 3 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 7053965 = 2645237) B2645237
theorem B1057475 : Blo 822348 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1319633 : Blo 822348 1319633 := bstep (se 2 (by rfl) ⟨494862, by rfl⟩ : syracuseStep 1319633 = 989725) B989725
theorem B926419 : Blo 822348 926419 := bstep (se 1 (by rfl) ⟨694814, by rfl⟩ : syracuseStep 926419 = 1389629) B1389629
theorem B1254179 : Blo 822348 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B1319761 : Blo 822348 1319761 := bstep (se 2 (by rfl) ⟨494910, by rfl⟩ : syracuseStep 1319761 = 989821) B989821
theorem B926563 : Blo 822348 926563 := bstep (se 1 (by rfl) ⟨694922, by rfl⟩ : syracuseStep 926563 = 1389845) B1389845
theorem B1254323 : Blo 822348 1254323 := bstep (se 1 (by rfl) ⟨940742, by rfl⟩ : syracuseStep 1254323 = 1881485) B1881485
theorem B926707 : Blo 822348 926707 := bstep (se 1 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 926707 = 1390061) B1390061
theorem B1451009 : Blo 822348 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B4170851 : Blo 822348 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B926851 : Blo 822348 926851 := bstep (se 1 (by rfl) ⟨695138, by rfl⟩ : syracuseStep 926851 = 1390277) B1390277
theorem B926995 : Blo 822348 926995 := bstep (se 1 (by rfl) ⟨695246, by rfl⟩ : syracuseStep 926995 = 1390493) B1390493
theorem B992531 : Blo 822348 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B992579 : Blo 822348 992579 := bstep (se 1 (by rfl) ⟨744434, by rfl⟩ : syracuseStep 992579 = 1488869) B1488869
theorem B927139 : Blo 822348 927139 := bstep (se 1 (by rfl) ⟨695354, by rfl⟩ : syracuseStep 927139 = 1390709) B1390709
theorem B927283 : Blo 822348 927283 := bstep (se 1 (by rfl) ⟨695462, by rfl⟩ : syracuseStep 927283 = 1390925) B1390925
theorem B927427 : Blo 822348 927427 := bstep (se 1 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 927427 = 1391141) B1391141
theorem B10561265 : Blo 822348 10561265 := bstep (se 2 (by rfl) ⟨3960474, by rfl⟩ : syracuseStep 10561265 = 7920949) B7920949
theorem B4007693 : Blo 822348 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B927571 : Blo 822348 927571 := bstep (se 1 (by rfl) ⟨695678, by rfl⟩ : syracuseStep 927571 = 1391357) B1391357
theorem B4171661 : Blo 822348 4171661 := bstep (se 3 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 4171661 = 1564373) B1564373
theorem B927715 : Blo 822348 927715 := bstep (se 1 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 927715 = 1391573) B1391573
theorem B6268913 : Blo 822348 6268913 := bstep (se 2 (by rfl) ⟨2350842, by rfl⟩ : syracuseStep 6268913 = 4701685) B4701685
theorem B927859 : Blo 822348 927859 := bstep (se 1 (by rfl) ⟨695894, by rfl⟩ : syracuseStep 927859 = 1391789) B1391789
theorem B928003 : Blo 822348 928003 := bstep (se 1 (by rfl) ⟨696002, by rfl⟩ : syracuseStep 928003 = 1392005) B1392005
theorem B1321267 : Blo 822348 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B5286221 : Blo 822348 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B928147 : Blo 822348 928147 := bstep (se 1 (by rfl) ⟨696110, by rfl⟩ : syracuseStep 928147 = 1392221) B1392221
theorem B1190305 : Blo 822348 1190305 := bstep (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) B892729
theorem B928291 : Blo 822348 928291 := bstep (se 1 (by rfl) ⟨696218, by rfl⟩ : syracuseStep 928291 = 1392437) B1392437
theorem B4237859 : Blo 822348 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B1256003 : Blo 822348 1256003 := bstep (se 1 (by rfl) ⟨942002, by rfl⟩ : syracuseStep 1256003 = 1884005) B1884005
theorem B1256051 : Blo 822348 1256051 := bstep (se 1 (by rfl) ⟨942038, by rfl⟩ : syracuseStep 1256051 = 1884077) B1884077
theorem B3517091 : Blo 822348 3517091 := bstep (se 1 (by rfl) ⟨2637818, by rfl⟩ : syracuseStep 3517091 = 5275637) B5275637
theorem B928435 : Blo 822348 928435 := bstep (se 1 (by rfl) ⟨696326, by rfl⟩ : syracuseStep 928435 = 1392653) B1392653
theorem B3123917 : Blo 822348 3123917 := bstep (se 3 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 3123917 = 1171469) B1171469
theorem B928579 : Blo 822348 928579 := bstep (se 1 (by rfl) ⟨696434, by rfl⟩ : syracuseStep 928579 = 1392869) B1392869
theorem B1321939 : Blo 822348 1321939 := bstep (se 1 (by rfl) ⟨991454, by rfl⟩ : syracuseStep 1321939 = 1982909) B1982909
theorem B928723 : Blo 822348 928723 := bstep (se 1 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 928723 = 1393085) B1393085
theorem B7056355 : Blo 822348 7056355 := bstep (se 1 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 7056355 = 10584533) B10584533
theorem B1190963 : Blo 822348 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B928867 : Blo 822348 928867 := bstep (se 1 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 928867 = 1393301) B1393301
theorem B1486001 : Blo 822348 1486001 := bstep (se 2 (by rfl) ⟨557250, by rfl⟩ : syracuseStep 1486001 = 1114501) B1114501
theorem B929011 : Blo 822348 929011 := bstep (se 1 (by rfl) ⟨696758, by rfl⟩ : syracuseStep 929011 = 1393517) B1393517
theorem B1387793 : Blo 822348 1387793 := bstep (se 2 (by rfl) ⟨520422, by rfl⟩ : syracuseStep 1387793 = 1040845) B1040845
theorem B5647715 : Blo 822348 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B929155 : Blo 822348 929155 := bstep (se 1 (by rfl) ⟨696866, by rfl⟩ : syracuseStep 929155 = 1393733) B1393733
theorem B2502029 : Blo 822348 2502029 := bstep (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) B938261
theorem B1387921 : Blo 822348 1387921 := bstep (se 2 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 1387921 = 1040941) B1040941
theorem B1322401 : Blo 822348 1322401 := bstep (se 2 (by rfl) ⟨495900, by rfl⟩ : syracuseStep 1322401 = 991801) B991801
theorem B1387955 : Blo 822348 1387955 := bstep (se 1 (by rfl) ⟨1040966, by rfl⟩ : syracuseStep 1387955 = 2081933) B2081933
theorem B1486289 : Blo 822348 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B4697585 : Blo 822348 4697585 := bstep (se 2 (by rfl) ⟨1761594, by rfl⟩ : syracuseStep 4697585 = 3523189) B3523189
theorem B1322497 : Blo 822348 1322497 := bstep (se 2 (by rfl) ⟨495936, by rfl⟩ : syracuseStep 1322497 = 991873) B991873
theorem B929299 : Blo 822348 929299 := bstep (se 1 (by rfl) ⟨696974, by rfl⟩ : syracuseStep 929299 = 1393949) B1393949
theorem B1388083 : Blo 822348 1388083 := bstep (se 1 (by rfl) ⟨1041062, by rfl⟩ : syracuseStep 1388083 = 2082125) B2082125
theorem B2010737 : Blo 822348 2010737 := bstep (se 2 (by rfl) ⟨754026, by rfl⟩ : syracuseStep 2010737 = 1508053) B1508053
theorem B1322657 : Blo 822348 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B929443 : Blo 822348 929443 := bstep (se 1 (by rfl) ⟨697082, by rfl⟩ : syracuseStep 929443 = 1394165) B1394165
theorem B1388225 : Blo 822348 1388225 := bstep (se 2 (by rfl) ⟨520584, by rfl⟩ : syracuseStep 1388225 = 1041169) B1041169
theorem B929587 : Blo 822348 929587 := bstep (se 1 (by rfl) ⟨697190, by rfl⟩ : syracuseStep 929587 = 1394381) B1394381
theorem B1388353 : Blo 822348 1388353 := bstep (se 2 (by rfl) ⟨520632, by rfl⟩ : syracuseStep 1388353 = 1041265) B1041265
theorem B1388387 : Blo 822348 1388387 := bstep (se 1 (by rfl) ⟨1041290, by rfl⟩ : syracuseStep 1388387 = 2082581) B2082581
theorem B1388515 : Blo 822348 1388515 := bstep (se 1 (by rfl) ⟨1041386, by rfl⟩ : syracuseStep 1388515 = 2082773) B2082773
theorem B1880099 : Blo 822348 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B1388657 : Blo 822348 1388657 := bstep (se 2 (by rfl) ⟨520746, by rfl⟩ : syracuseStep 1388657 = 1041493) B1041493
theorem B1388785 : Blo 822348 1388785 := bstep (se 2 (by rfl) ⟨520794, by rfl⟩ : syracuseStep 1388785 = 1041589) B1041589
theorem B1388819 : Blo 822348 1388819 := bstep (se 1 (by rfl) ⟨1041614, by rfl⟩ : syracuseStep 1388819 = 2083229) B2083229
theorem B1388947 : Blo 822348 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B1389089 : Blo 822348 1389089 := bstep (se 2 (by rfl) ⟨520908, by rfl⟩ : syracuseStep 1389089 = 1041817) B1041817
theorem B3519089 : Blo 822348 3519089 := bstep (se 2 (by rfl) ⟨1319658, by rfl⟩ : syracuseStep 3519089 = 2639317) B2639317
theorem B1389217 : Blo 822348 1389217 := bstep (se 2 (by rfl) ⟨520956, by rfl⟩ : syracuseStep 1389217 = 1041913) B1041913
theorem B1389251 : Blo 822348 1389251 := bstep (se 1 (by rfl) ⟨1041938, by rfl⟩ : syracuseStep 1389251 = 2083877) B2083877
theorem B4174577 : Blo 822348 4174577 := bstep (se 2 (by rfl) ⟨1565466, by rfl⟩ : syracuseStep 4174577 = 3130933) B3130933
theorem B1389379 : Blo 822348 1389379 := bstep (se 1 (by rfl) ⟨1042034, by rfl⟩ : syracuseStep 1389379 = 2084069) B2084069
theorem B3388301 : Blo 822348 3388301 := bstep (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) B1270613
theorem B4699043 : Blo 822348 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B5649329 : Blo 822348 5649329 := bstep (se 2 (by rfl) ⟨2118498, by rfl⟩ : syracuseStep 5649329 = 4236997) B4236997
theorem B1389521 : Blo 822348 1389521 := bstep (se 2 (by rfl) ⟨521070, by rfl⟩ : syracuseStep 1389521 = 1042141) B1042141
theorem B1979441 : Blo 822348 1979441 := bstep (se 2 (by rfl) ⟨742290, by rfl⟩ : syracuseStep 1979441 = 1484581) B1484581
theorem B1389649 : Blo 822348 1389649 := bstep (se 2 (by rfl) ⟨521118, by rfl⟩ : syracuseStep 1389649 = 1042237) B1042237
theorem B1389683 : Blo 822348 1389683 := bstep (se 1 (by rfl) ⟨1042262, by rfl⟩ : syracuseStep 1389683 = 2084525) B2084525
theorem B1389811 : Blo 822348 1389811 := bstep (se 1 (by rfl) ⟨1042358, by rfl⟩ : syracuseStep 1389811 = 2084717) B2084717
theorem B1389953 : Blo 822348 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B2635217 : Blo 822348 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B1390081 : Blo 822348 1390081 := bstep (se 2 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 1390081 = 1042561) B1042561
theorem B2635267 : Blo 822348 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B1390115 : Blo 822348 1390115 := bstep (se 1 (by rfl) ⟨1042586, by rfl⟩ : syracuseStep 1390115 = 2085173) B2085173
theorem B3126833 : Blo 822348 3126833 := bstep (se 2 (by rfl) ⟨1172562, by rfl⟩ : syracuseStep 3126833 = 2345125) B2345125
theorem B35599985 : Blo 822348 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B10565261 : Blo 822348 10565261 := bstep (se 3 (by rfl) ⟨1980986, by rfl⟩ : syracuseStep 10565261 = 3961973) B3961973
theorem B1390243 : Blo 822348 1390243 := bstep (se 1 (by rfl) ⟨1042682, by rfl⟩ : syracuseStep 1390243 = 2085365) B2085365
theorem B3389219 : Blo 822348 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B1390385 : Blo 822348 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B4700045 : Blo 822348 4700045 := bstep (se 3 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 4700045 = 1762517) B1762517
theorem B1390513 : Blo 822348 1390513 := bstep (se 2 (by rfl) ⟨521442, by rfl⟩ : syracuseStep 1390513 = 1042885) B1042885
theorem B1390547 : Blo 822348 1390547 := bstep (se 1 (by rfl) ⟨1042910, by rfl⟩ : syracuseStep 1390547 = 2085821) B2085821
theorem B1390675 : Blo 822348 1390675 := bstep (se 1 (by rfl) ⟨1043006, by rfl⟩ : syracuseStep 1390675 = 2086013) B2086013
theorem B1489027 : Blo 822348 1489027 := bstep (se 1 (by rfl) ⟨1116770, by rfl⟩ : syracuseStep 1489027 = 2233541) B2233541
theorem B4176035 : Blo 822348 4176035 := bstep (se 1 (by rfl) ⟨3132026, by rfl⟩ : syracuseStep 4176035 = 6264053) B6264053
theorem B2635985 : Blo 822348 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B833747 : Blo 822348 833747 := bstep (se 1 (by rfl) ⟨625310, by rfl⟩ : syracuseStep 833747 = 1250621) B1250621
theorem B1390817 : Blo 822348 1390817 := bstep (se 2 (by rfl) ⟨521556, by rfl⟩ : syracuseStep 1390817 = 1043113) B1043113
theorem B833779 : Blo 822348 833779 := bstep (se 1 (by rfl) ⟨625334, by rfl⟩ : syracuseStep 833779 = 1250669) B1250669
theorem B1390945 : Blo 822348 1390945 := bstep (se 2 (by rfl) ⟨521604, by rfl⟩ : syracuseStep 1390945 = 1043209) B1043209
theorem B1390979 : Blo 822348 1390979 := bstep (se 1 (by rfl) ⟨1043234, by rfl⟩ : syracuseStep 1390979 = 2086469) B2086469
theorem B1391107 : Blo 822348 1391107 := bstep (se 1 (by rfl) ⟨1043330, by rfl⟩ : syracuseStep 1391107 = 2086661) B2086661
theorem B1391249 : Blo 822348 1391249 := bstep (se 2 (by rfl) ⟨521718, by rfl⟩ : syracuseStep 1391249 = 1043437) B1043437
theorem B2636497 : Blo 822348 2636497 := bstep (se 2 (by rfl) ⟨988686, by rfl⟩ : syracuseStep 2636497 = 1977373) B1977373
theorem B1391377 : Blo 822348 1391377 := bstep (se 2 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 1391377 = 1043533) B1043533
theorem B1391411 : Blo 822348 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B1391539 : Blo 822348 1391539 := bstep (se 1 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 1391539 = 2087309) B2087309
theorem B4176845 : Blo 822348 4176845 := bstep (se 3 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 4176845 = 1566317) B1566317
theorem B3128291 : Blo 822348 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B3521549 : Blo 822348 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B1850417 : Blo 822348 1850417 := bstep (se 2 (by rfl) ⟨693906, by rfl⟩ : syracuseStep 1850417 = 1387813) B1387813
theorem B1391681 : Blo 822348 1391681 := bstep (se 2 (by rfl) ⟨521880, by rfl⟩ : syracuseStep 1391681 = 1043761) B1043761
theorem B1850435 : Blo 822348 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B834691 : Blo 822348 834691 := bstep (se 1 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 834691 = 1252037) B1252037
theorem B1391809 : Blo 822348 1391809 := bstep (se 2 (by rfl) ⟨521928, by rfl⟩ : syracuseStep 1391809 = 1043857) B1043857
theorem B2964707 : Blo 822348 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B1391843 : Blo 822348 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1359155 : Blo 822348 1359155 := bstep (se 1 (by rfl) ⟨1019366, by rfl⟩ : syracuseStep 1359155 = 2038733) B2038733
theorem B1850705 : Blo 822348 1850705 := bstep (se 2 (by rfl) ⟨694014, by rfl⟩ : syracuseStep 1850705 = 1388029) B1388029
theorem B1850723 : Blo 822348 1850723 := bstep (se 1 (by rfl) ⟨1388042, by rfl⟩ : syracuseStep 1850723 = 2776085) B2776085
theorem B1391971 : Blo 822348 1391971 := bstep (se 1 (by rfl) ⟨1043978, by rfl⟩ : syracuseStep 1391971 = 2087957) B2087957
theorem B8928625 : Blo 822348 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B1392113 : Blo 822348 1392113 := bstep (se 2 (by rfl) ⟨522042, by rfl⟩ : syracuseStep 1392113 = 1044085) B1044085
theorem B1850993 : Blo 822348 1850993 := bstep (se 2 (by rfl) ⟨694122, by rfl⟩ : syracuseStep 1850993 = 1388245) B1388245
theorem B1392241 : Blo 822348 1392241 := bstep (se 2 (by rfl) ⟨522090, by rfl⟩ : syracuseStep 1392241 = 1044181) B1044181
theorem B1851011 : Blo 822348 1851011 := bstep (se 1 (by rfl) ⟨1388258, by rfl⟩ : syracuseStep 1851011 = 2776517) B2776517
theorem B1982083 : Blo 822348 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B835219 : Blo 822348 835219 := bstep (se 1 (by rfl) ⟨626414, by rfl⟩ : syracuseStep 835219 = 1252829) B1252829
theorem B1392275 : Blo 822348 1392275 := bstep (se 1 (by rfl) ⟨1044206, by rfl⟩ : syracuseStep 1392275 = 2088413) B2088413
theorem B2375345 : Blo 822348 2375345 := bstep (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) B1781509
theorem B10043149 : Blo 822348 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B1392403 : Blo 822348 1392403 := bstep (se 1 (by rfl) ⟨1044302, by rfl⟩ : syracuseStep 1392403 = 2088605) B2088605
theorem B2637613 : Blo 822348 2637613 := bstep (se 3 (by rfl) ⟨494552, by rfl⟩ : syracuseStep 2637613 = 989105) B989105
theorem B2637677 : Blo 822348 2637677 := bstep (se 3 (by rfl) ⟨494564, by rfl⟩ : syracuseStep 2637677 = 989129) B989129
theorem B1851281 : Blo 822348 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1392545 : Blo 822348 1392545 := bstep (se 2 (by rfl) ⟨522204, by rfl⟩ : syracuseStep 1392545 = 1044409) B1044409
theorem B1851299 : Blo 822348 1851299 := bstep (se 1 (by rfl) ⟨1388474, by rfl⟩ : syracuseStep 1851299 = 2776949) B2776949
theorem B3129293 : Blo 822348 3129293 := bstep (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) B1173485
theorem B1884113 : Blo 822348 1884113 := bstep (se 2 (by rfl) ⟨706542, by rfl⟩ : syracuseStep 1884113 = 1413085) B1413085
theorem B2342915 : Blo 822348 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B1392673 : Blo 822348 1392673 := bstep (se 2 (by rfl) ⟨522252, by rfl⟩ : syracuseStep 1392673 = 1044505) B1044505
theorem B1392707 : Blo 822348 1392707 := bstep (se 1 (by rfl) ⟨1044530, by rfl⟩ : syracuseStep 1392707 = 2089061) B2089061
theorem B8896625 : Blo 822348 8896625 := bstep (se 2 (by rfl) ⟨3336234, by rfl⟩ : syracuseStep 8896625 = 6672469) B6672469
theorem B1851569 : Blo 822348 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1851587 : Blo 822348 1851587 := bstep (se 1 (by rfl) ⟨1388690, by rfl⟩ : syracuseStep 1851587 = 2777381) B2777381
theorem B1392835 : Blo 822348 1392835 := bstep (se 1 (by rfl) ⟨1044626, by rfl⟩ : syracuseStep 1392835 = 2089253) B2089253
theorem B835795 : Blo 822348 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B1982755 : Blo 822348 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B1392977 : Blo 822348 1392977 := bstep (se 2 (by rfl) ⟨522366, by rfl⟩ : syracuseStep 1392977 = 1044733) B1044733
theorem B2507213 : Blo 822348 2507213 := bstep (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) B940205
theorem B1851857 : Blo 822348 1851857 := bstep (se 2 (by rfl) ⟨694446, by rfl⟩ : syracuseStep 1851857 = 1388893) B1388893
theorem B1393105 : Blo 822348 1393105 := bstep (se 2 (by rfl) ⟨522414, by rfl⟩ : syracuseStep 1393105 = 1044829) B1044829
theorem B1851875 : Blo 822348 1851875 := bstep (se 1 (by rfl) ⟨1388906, by rfl⟩ : syracuseStep 1851875 = 2777813) B2777813
theorem B1393139 : Blo 822348 1393139 := bstep (se 1 (by rfl) ⟨1044854, by rfl⟩ : syracuseStep 1393139 = 2089709) B2089709
theorem B3523121 : Blo 822348 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B1393267 : Blo 822348 1393267 := bstep (se 1 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 1393267 = 2089901) B2089901
theorem B5292677 : Blo 822348 5292677 := bstep (se 4 (by rfl) ⟨496188, by rfl⟩ : syracuseStep 5292677 = 992377) B992377
theorem B1852145 : Blo 822348 1852145 := bstep (se 2 (by rfl) ⟨694554, by rfl⟩ : syracuseStep 1852145 = 1389109) B1389109
theorem B1983217 : Blo 822348 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B4702961 : Blo 822348 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B1393409 : Blo 822348 1393409 := bstep (se 2 (by rfl) ⟨522528, by rfl⟩ : syracuseStep 1393409 = 1045057) B1045057
theorem B1852163 : Blo 822348 1852163 := bstep (se 1 (by rfl) ⟨1389122, by rfl⟩ : syracuseStep 1852163 = 2778245) B2778245
theorem B2343725 : Blo 822348 2343725 := bstep (se 3 (by rfl) ⟨439448, by rfl⟩ : syracuseStep 2343725 = 878897) B878897
theorem B1983313 : Blo 822348 1983313 := bstep (se 2 (by rfl) ⟨743742, by rfl⟩ : syracuseStep 1983313 = 1487485) B1487485
theorem B1393537 : Blo 822348 1393537 := bstep (se 2 (by rfl) ⟨522576, by rfl⟩ : syracuseStep 1393537 = 1045153) B1045153
theorem B1393571 : Blo 822348 1393571 := bstep (se 1 (by rfl) ⟨1045178, by rfl⟩ : syracuseStep 1393571 = 2090357) B2090357
theorem B2343917 : Blo 822348 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B1852433 : Blo 822348 1852433 := bstep (se 2 (by rfl) ⟨694662, by rfl⟩ : syracuseStep 1852433 = 1389325) B1389325
theorem B1852451 : Blo 822348 1852451 := bstep (se 1 (by rfl) ⟨1389338, by rfl⟩ : syracuseStep 1852451 = 2778677) B2778677
theorem B1393699 : Blo 822348 1393699 := bstep (se 1 (by rfl) ⟨1045274, by rfl⟩ : syracuseStep 1393699 = 2090549) B2090549
theorem B1393841 : Blo 822348 1393841 := bstep (se 2 (by rfl) ⟨522690, by rfl⟩ : syracuseStep 1393841 = 1045381) B1045381
theorem B1852721 : Blo 822348 1852721 := bstep (se 2 (by rfl) ⟨694770, by rfl⟩ : syracuseStep 1852721 = 1389541) B1389541
theorem B1393969 : Blo 822348 1393969 := bstep (se 2 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 1393969 = 1045477) B1045477
theorem B1852739 : Blo 822348 1852739 := bstep (se 1 (by rfl) ⟨1389554, by rfl⟩ : syracuseStep 1852739 = 2779109) B2779109
theorem B1394003 : Blo 822348 1394003 := bstep (se 1 (by rfl) ⟨1045502, by rfl⟩ : syracuseStep 1394003 = 2091005) B2091005
theorem B2082257 : Blo 822348 2082257 := bstep (se 2 (by rfl) ⟨780846, by rfl⟩ : syracuseStep 2082257 = 1561693) B1561693
theorem B1394131 : Blo 822348 1394131 := bstep (se 1 (by rfl) ⟨1045598, by rfl⟩ : syracuseStep 1394131 = 2091197) B2091197
theorem B2082307 : Blo 822348 2082307 := bstep (se 1 (by rfl) ⟨1561730, by rfl⟩ : syracuseStep 2082307 = 3123461) B3123461
theorem B1853009 : Blo 822348 1853009 := bstep (se 2 (by rfl) ⟨694878, by rfl⟩ : syracuseStep 1853009 = 1389757) B1389757
theorem B1394273 : Blo 822348 1394273 := bstep (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) B1045705
theorem B1853027 : Blo 822348 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B2639459 : Blo 822348 2639459 := bstep (se 1 (by rfl) ⟨1979594, by rfl⟩ : syracuseStep 2639459 = 3959189) B3959189
theorem B7030385 : Blo 822348 7030385 := bstep (se 2 (by rfl) ⟨2636394, by rfl⟩ : syracuseStep 7030385 = 5272789) B5272789
theorem B2082449 : Blo 822348 2082449 := bstep (se 2 (by rfl) ⟨780918, by rfl⟩ : syracuseStep 2082449 = 1561837) B1561837
theorem B1394401 : Blo 822348 1394401 := bstep (se 2 (by rfl) ⟨522900, by rfl⟩ : syracuseStep 1394401 = 1045801) B1045801
theorem B1394435 : Blo 822348 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B4179761 : Blo 822348 4179761 := bstep (se 2 (by rfl) ⟨1567410, by rfl⟩ : syracuseStep 4179761 = 3134821) B3134821
theorem B1853297 : Blo 822348 1853297 := bstep (se 2 (by rfl) ⟨694986, by rfl⟩ : syracuseStep 1853297 = 1389973) B1389973
theorem B1853315 : Blo 822348 1853315 := bstep (se 1 (by rfl) ⟨1389986, by rfl⟩ : syracuseStep 1853315 = 2779973) B2779973
theorem B2344909 : Blo 822348 2344909 := bstep (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) B879341
theorem B3131405 : Blo 822348 3131405 := bstep (se 3 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 3131405 = 1174277) B1174277
theorem B1853585 : Blo 822348 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B1853603 : Blo 822348 1853603 := bstep (se 1 (by rfl) ⟨1390202, by rfl⟩ : syracuseStep 1853603 = 2780405) B2780405
theorem B4704419 : Blo 822348 4704419 := bstep (se 1 (by rfl) ⟨3528314, by rfl⟩ : syracuseStep 4704419 = 7056629) B7056629
theorem B8898869 : Blo 822348 8898869 := bstep (se 5 (by rfl) ⟨417134, by rfl⟩ : syracuseStep 8898869 = 834269) B834269
theorem B1853873 : Blo 822348 1853873 := bstep (se 2 (by rfl) ⟨695202, by rfl⟩ : syracuseStep 1853873 = 1390405) B1390405
theorem B1853891 : Blo 822348 1853891 := bstep (se 1 (by rfl) ⟨1390418, by rfl⟩ : syracuseStep 1853891 = 2780837) B2780837
theorem B2673197 : Blo 822348 2673197 := bstep (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) B1002449
theorem B2083441 : Blo 822348 2083441 := bstep (se 2 (by rfl) ⟨781290, by rfl⟩ : syracuseStep 2083441 = 1562581) B1562581
theorem B1854161 : Blo 822348 1854161 := bstep (se 2 (by rfl) ⟨695310, by rfl⟩ : syracuseStep 1854161 = 1390621) B1390621
theorem B1854179 : Blo 822348 1854179 := bstep (se 1 (by rfl) ⟨1390634, by rfl⟩ : syracuseStep 1854179 = 2781269) B2781269
theorem B3132209 : Blo 822348 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B2968397 : Blo 822348 2968397 := bstep (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) B1113149
theorem B9161585 : Blo 822348 9161585 := bstep (se 2 (by rfl) ⟨3435594, by rfl⟩ : syracuseStep 9161585 = 6871189) B6871189
theorem B2083715 : Blo 822348 2083715 := bstep (se 1 (by rfl) ⟨1562786, by rfl⟩ : syracuseStep 2083715 = 3125573) B3125573
theorem B3525581 : Blo 822348 3525581 := bstep (se 3 (by rfl) ⟨661046, by rfl⟩ : syracuseStep 3525581 = 1322093) B1322093
theorem B3165155 : Blo 822348 3165155 := bstep (se 1 (by rfl) ⟨2373866, by rfl⟩ : syracuseStep 3165155 = 4747733) B4747733
theorem B2509805 : Blo 822348 2509805 := bstep (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) B941177
theorem B1854449 : Blo 822348 1854449 := bstep (se 2 (by rfl) ⟨695418, by rfl⟩ : syracuseStep 1854449 = 1390837) B1390837
theorem B1854467 : Blo 822348 1854467 := bstep (se 1 (by rfl) ⟨1390850, by rfl⟩ : syracuseStep 1854467 = 2781701) B2781701
theorem B2083907 : Blo 822348 2083907 := bstep (se 1 (by rfl) ⟨1562930, by rfl⟩ : syracuseStep 2083907 = 3125861) B3125861
theorem B5950691 : Blo 822348 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B4181219 : Blo 822348 4181219 := bstep (se 1 (by rfl) ⟨3135914, by rfl⟩ : syracuseStep 4181219 = 6271829) B6271829
theorem B1854737 : Blo 822348 1854737 := bstep (se 2 (by rfl) ⟨695526, by rfl⟩ : syracuseStep 1854737 = 1391053) B1391053
theorem B1854755 : Blo 822348 1854755 := bstep (se 1 (by rfl) ⟨1391066, by rfl⟩ : syracuseStep 1854755 = 2782133) B2782133
theorem B3525923 : Blo 822348 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B3132877 : Blo 822348 3132877 := bstep (se 3 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 3132877 = 1174829) B1174829
theorem B1756657 : Blo 822348 1756657 := bstep (se 2 (by rfl) ⟨658746, by rfl⟩ : syracuseStep 1756657 = 1317493) B1317493
theorem B1855025 : Blo 822348 1855025 := bstep (se 2 (by rfl) ⟨695634, by rfl⟩ : syracuseStep 1855025 = 1391269) B1391269
theorem B1855043 : Blo 822348 1855043 := bstep (se 1 (by rfl) ⟨1391282, by rfl⟩ : syracuseStep 1855043 = 2782565) B2782565
theorem B2346641 : Blo 822348 2346641 := bstep (se 2 (by rfl) ⟨879990, by rfl⟩ : syracuseStep 2346641 = 1759981) B1759981
theorem B2346833 : Blo 822348 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B1855313 : Blo 822348 1855313 := bstep (se 2 (by rfl) ⟨695742, by rfl⟩ : syracuseStep 1855313 = 1391485) B1391485
theorem B1855331 : Blo 822348 1855331 := bstep (se 1 (by rfl) ⟨1391498, by rfl⟩ : syracuseStep 1855331 = 2782997) B2782997
theorem B2084849 : Blo 822348 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B7032845 : Blo 822348 7032845 := bstep (se 3 (by rfl) ⟨1318658, by rfl⟩ : syracuseStep 7032845 = 2637317) B2637317
theorem B4182029 : Blo 822348 4182029 := bstep (se 3 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 4182029 = 1568261) B1568261
theorem B2084899 : Blo 822348 2084899 := bstep (se 1 (by rfl) ⟨1563674, by rfl⟩ : syracuseStep 2084899 = 3127349) B3127349
theorem B2969635 : Blo 822348 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B2642033 : Blo 822348 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B1855601 : Blo 822348 1855601 := bstep (se 2 (by rfl) ⟨695850, by rfl⟩ : syracuseStep 1855601 = 1391701) B1391701
theorem B1757315 : Blo 822348 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1855619 : Blo 822348 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B2085041 : Blo 822348 2085041 := bstep (se 2 (by rfl) ⟨781890, by rfl⟩ : syracuseStep 2085041 = 1563781) B1563781
theorem B3133667 : Blo 822348 3133667 := bstep (se 1 (by rfl) ⟨2350250, by rfl⟩ : syracuseStep 3133667 = 4700501) B4700501
theorem B1855889 : Blo 822348 1855889 := bstep (se 2 (by rfl) ⟨695958, by rfl⟩ : syracuseStep 1855889 = 1391917) B1391917
theorem B1855907 : Blo 822348 1855907 := bstep (se 1 (by rfl) ⟨1391930, by rfl⟩ : syracuseStep 1855907 = 2783861) B2783861
theorem B2970083 : Blo 822348 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B1233539 : Blo 822348 1233539 := bstep (se 1 (by rfl) ⟨925154, by rfl⟩ : syracuseStep 1233539 = 1850309) B1850309
theorem B1233569 : Blo 822348 1233569 := bstep (se 2 (by rfl) ⟨462588, by rfl⟩ : syracuseStep 1233569 = 925177) B925177
theorem B938659 : Blo 822348 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B1856177 : Blo 822348 1856177 := bstep (se 2 (by rfl) ⟨696066, by rfl⟩ : syracuseStep 1856177 = 1392133) B1392133
theorem B1233587 : Blo 822348 1233587 := bstep (se 1 (by rfl) ⟨925190, by rfl⟩ : syracuseStep 1233587 = 1850381) B1850381
theorem B1856195 : Blo 822348 1856195 := bstep (se 1 (by rfl) ⟨1392146, by rfl⟩ : syracuseStep 1856195 = 2784293) B2784293
theorem B1233617 : Blo 822348 1233617 := bstep (se 2 (by rfl) ⟨462606, by rfl⟩ : syracuseStep 1233617 = 925213) B925213
theorem B1233635 : Blo 822348 1233635 := bstep (se 1 (by rfl) ⟨925226, by rfl⟩ : syracuseStep 1233635 = 1850453) B1850453
theorem B1233665 : Blo 822348 1233665 := bstep (se 2 (by rfl) ⟨462624, by rfl⟩ : syracuseStep 1233665 = 925249) B925249
theorem B1233683 : Blo 822348 1233683 := bstep (se 1 (by rfl) ⟨925262, by rfl⟩ : syracuseStep 1233683 = 1850525) B1850525
theorem B1233713 : Blo 822348 1233713 := bstep (se 2 (by rfl) ⟨462642, by rfl⟩ : syracuseStep 1233713 = 925285) B925285
theorem B2347825 : Blo 822348 2347825 := bstep (se 2 (by rfl) ⟨880434, by rfl⟩ : syracuseStep 2347825 = 1760869) B1760869
theorem B1233731 : Blo 822348 1233731 := bstep (se 1 (by rfl) ⟨925298, by rfl⟩ : syracuseStep 1233731 = 1850597) B1850597
theorem B1233761 : Blo 822348 1233761 := bstep (se 2 (by rfl) ⟨462660, by rfl⟩ : syracuseStep 1233761 = 925321) B925321
theorem B1561457 : Blo 822348 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B19059569 : Blo 822348 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B1233779 : Blo 822348 1233779 := bstep (se 1 (by rfl) ⟨925334, by rfl⟩ : syracuseStep 1233779 = 1850669) B1850669
theorem B3134321 : Blo 822348 3134321 := bstep (se 2 (by rfl) ⟨1175370, by rfl⟩ : syracuseStep 3134321 = 2350741) B2350741
theorem B1233809 : Blo 822348 1233809 := bstep (se 2 (by rfl) ⟨462678, by rfl⟩ : syracuseStep 1233809 = 925357) B925357
theorem B1233827 : Blo 822348 1233827 := bstep (se 1 (by rfl) ⟨925370, by rfl⟩ : syracuseStep 1233827 = 1850741) B1850741
theorem B1233857 : Blo 822348 1233857 := bstep (se 2 (by rfl) ⟨462696, by rfl⟩ : syracuseStep 1233857 = 925393) B925393
theorem B1758161 : Blo 822348 1758161 := bstep (se 2 (by rfl) ⟨659310, by rfl⟩ : syracuseStep 1758161 = 1318621) B1318621
theorem B1856465 : Blo 822348 1856465 := bstep (se 2 (by rfl) ⟨696174, by rfl⟩ : syracuseStep 1856465 = 1392349) B1392349
theorem B1233875 : Blo 822348 1233875 := bstep (se 1 (by rfl) ⟨925406, by rfl⟩ : syracuseStep 1233875 = 1850813) B1850813
theorem B1856483 : Blo 822348 1856483 := bstep (se 1 (by rfl) ⟨1392362, by rfl⟩ : syracuseStep 1856483 = 2784725) B2784725
theorem B1233905 : Blo 822348 1233905 := bstep (se 2 (by rfl) ⟨462714, by rfl⟩ : syracuseStep 1233905 = 925429) B925429
theorem B1233923 : Blo 822348 1233923 := bstep (se 1 (by rfl) ⟨925442, by rfl⟩ : syracuseStep 1233923 = 1850885) B1850885
theorem B1233953 : Blo 822348 1233953 := bstep (se 2 (by rfl) ⟨462732, by rfl⟩ : syracuseStep 1233953 = 925465) B925465
theorem B1233971 : Blo 822348 1233971 := bstep (se 1 (by rfl) ⟨925478, by rfl⟩ : syracuseStep 1233971 = 1850957) B1850957
theorem B2348099 : Blo 822348 2348099 := bstep (se 1 (by rfl) ⟨1761074, by rfl⟩ : syracuseStep 2348099 = 3522149) B3522149
theorem B1234001 : Blo 822348 1234001 := bstep (se 2 (by rfl) ⟨462750, by rfl⟩ : syracuseStep 1234001 = 925501) B925501
theorem B1234019 : Blo 822348 1234019 := bstep (se 1 (by rfl) ⟨925514, by rfl⟩ : syracuseStep 1234019 = 1851029) B1851029
theorem B1234049 : Blo 822348 1234049 := bstep (se 2 (by rfl) ⟨462768, by rfl⟩ : syracuseStep 1234049 = 925537) B925537
theorem B2086033 : Blo 822348 2086033 := bstep (se 2 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 2086033 = 1564525) B1564525
theorem B1234067 : Blo 822348 1234067 := bstep (se 1 (by rfl) ⟨925550, by rfl⟩ : syracuseStep 1234067 = 1851101) B1851101
theorem B1234097 : Blo 822348 1234097 := bstep (se 2 (by rfl) ⟨462786, by rfl⟩ : syracuseStep 1234097 = 925573) B925573
theorem B1234115 : Blo 822348 1234115 := bstep (se 1 (by rfl) ⟨925586, by rfl⟩ : syracuseStep 1234115 = 1851173) B1851173
theorem B1234145 : Blo 822348 1234145 := bstep (se 2 (by rfl) ⟨462804, by rfl⟩ : syracuseStep 1234145 = 925609) B925609
theorem B1856753 : Blo 822348 1856753 := bstep (se 2 (by rfl) ⟨696282, by rfl⟩ : syracuseStep 1856753 = 1392565) B1392565
theorem B1234163 : Blo 822348 1234163 := bstep (se 1 (by rfl) ⟨925622, by rfl⟩ : syracuseStep 1234163 = 1851245) B1851245
theorem B2348291 : Blo 822348 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B1856771 : Blo 822348 1856771 := bstep (se 1 (by rfl) ⟨1392578, by rfl⟩ : syracuseStep 1856771 = 2785157) B2785157
theorem B5002501 : Blo 822348 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B1234193 : Blo 822348 1234193 := bstep (se 2 (by rfl) ⟨462822, by rfl⟩ : syracuseStep 1234193 = 925645) B925645
theorem B1234211 : Blo 822348 1234211 := bstep (se 1 (by rfl) ⟨925658, by rfl⟩ : syracuseStep 1234211 = 1851317) B1851317
theorem B1234241 : Blo 822348 1234241 := bstep (se 2 (by rfl) ⟨462840, by rfl⟩ : syracuseStep 1234241 = 925681) B925681
theorem B1234259 : Blo 822348 1234259 := bstep (se 1 (by rfl) ⟨925694, by rfl⟩ : syracuseStep 1234259 = 1851389) B1851389
theorem B1234289 : Blo 822348 1234289 := bstep (se 2 (by rfl) ⟨462858, by rfl⟩ : syracuseStep 1234289 = 925717) B925717
theorem B1234307 : Blo 822348 1234307 := bstep (se 1 (by rfl) ⟨925730, by rfl⟩ : syracuseStep 1234307 = 1851461) B1851461
theorem B1234337 : Blo 822348 1234337 := bstep (se 2 (by rfl) ⟨462876, by rfl⟩ : syracuseStep 1234337 = 925753) B925753
theorem B2086307 : Blo 822348 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B1234355 : Blo 822348 1234355 := bstep (se 1 (by rfl) ⟨925766, by rfl⟩ : syracuseStep 1234355 = 1851533) B1851533
theorem B1234385 : Blo 822348 1234385 := bstep (se 2 (by rfl) ⟨462894, by rfl⟩ : syracuseStep 1234385 = 925789) B925789
theorem B1234403 : Blo 822348 1234403 := bstep (se 1 (by rfl) ⟨925802, by rfl⟩ : syracuseStep 1234403 = 1851605) B1851605
theorem B1234433 : Blo 822348 1234433 := bstep (se 2 (by rfl) ⟨462912, by rfl⟩ : syracuseStep 1234433 = 925825) B925825
theorem B1857041 : Blo 822348 1857041 := bstep (se 2 (by rfl) ⟨696390, by rfl⟩ : syracuseStep 1857041 = 1392781) B1392781
theorem B1234451 : Blo 822348 1234451 := bstep (se 1 (by rfl) ⟨925838, by rfl⟩ : syracuseStep 1234451 = 1851677) B1851677
theorem B1857059 : Blo 822348 1857059 := bstep (se 1 (by rfl) ⟨1392794, by rfl⟩ : syracuseStep 1857059 = 2785589) B2785589
theorem B1234481 : Blo 822348 1234481 := bstep (se 2 (by rfl) ⟨462930, by rfl⟩ : syracuseStep 1234481 = 925861) B925861
theorem B1562179 : Blo 822348 1562179 := bstep (se 1 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 1562179 = 2343269) B2343269
theorem B1234499 : Blo 822348 1234499 := bstep (se 1 (by rfl) ⟨925874, by rfl⟩ : syracuseStep 1234499 = 1851749) B1851749
theorem B1234529 : Blo 822348 1234529 := bstep (se 2 (by rfl) ⟨462948, by rfl⟩ : syracuseStep 1234529 = 925897) B925897
theorem B2086499 : Blo 822348 2086499 := bstep (se 1 (by rfl) ⟨1564874, by rfl⟩ : syracuseStep 2086499 = 3129749) B3129749
theorem B1234547 : Blo 822348 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B1234577 : Blo 822348 1234577 := bstep (se 2 (by rfl) ⟨462966, by rfl⟩ : syracuseStep 1234577 = 925933) B925933
theorem B1234595 : Blo 822348 1234595 := bstep (se 1 (by rfl) ⟨925946, by rfl⟩ : syracuseStep 1234595 = 1851893) B1851893
theorem B1234625 : Blo 822348 1234625 := bstep (se 2 (by rfl) ⟨462984, by rfl⟩ : syracuseStep 1234625 = 925969) B925969
theorem B1234643 : Blo 822348 1234643 := bstep (se 1 (by rfl) ⟨925982, by rfl⟩ : syracuseStep 1234643 = 1851965) B1851965
theorem B1234673 : Blo 822348 1234673 := bstep (se 2 (by rfl) ⟨463002, by rfl⟩ : syracuseStep 1234673 = 926005) B926005
theorem B1234691 : Blo 822348 1234691 := bstep (se 1 (by rfl) ⟨926018, by rfl⟩ : syracuseStep 1234691 = 1852037) B1852037
theorem B1234721 : Blo 822348 1234721 := bstep (se 2 (by rfl) ⟨463020, by rfl⟩ : syracuseStep 1234721 = 926041) B926041
theorem B1857329 : Blo 822348 1857329 := bstep (se 2 (by rfl) ⟨696498, by rfl⟩ : syracuseStep 1857329 = 1392997) B1392997
theorem B1234739 : Blo 822348 1234739 := bstep (se 1 (by rfl) ⟨926054, by rfl⟩ : syracuseStep 1234739 = 1852109) B1852109
theorem B1857347 : Blo 822348 1857347 := bstep (se 1 (by rfl) ⟨1393010, by rfl⟩ : syracuseStep 1857347 = 2786021) B2786021
theorem B1234769 : Blo 822348 1234769 := bstep (se 2 (by rfl) ⟨463038, by rfl⟩ : syracuseStep 1234769 = 926077) B926077
theorem B1234787 : Blo 822348 1234787 := bstep (se 1 (by rfl) ⟨926090, by rfl⟩ : syracuseStep 1234787 = 1852181) B1852181
theorem B1234817 : Blo 822348 1234817 := bstep (se 2 (by rfl) ⟨463056, by rfl⟩ : syracuseStep 1234817 = 926113) B926113
theorem B1234835 : Blo 822348 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B1234865 : Blo 822348 1234865 := bstep (se 2 (by rfl) ⟨463074, by rfl⟩ : syracuseStep 1234865 = 926149) B926149
theorem B1234883 : Blo 822348 1234883 := bstep (se 1 (by rfl) ⟨926162, by rfl⟩ : syracuseStep 1234883 = 1852325) B1852325
theorem B1234913 : Blo 822348 1234913 := bstep (se 2 (by rfl) ⟨463092, by rfl⟩ : syracuseStep 1234913 = 926185) B926185
theorem B1234931 : Blo 822348 1234931 := bstep (se 1 (by rfl) ⟨926198, by rfl⟩ : syracuseStep 1234931 = 1852397) B1852397
theorem B1562627 : Blo 822348 1562627 := bstep (se 1 (by rfl) ⟨1171970, by rfl⟩ : syracuseStep 1562627 = 2343941) B2343941
theorem B1234961 : Blo 822348 1234961 := bstep (se 2 (by rfl) ⟨463110, by rfl⟩ : syracuseStep 1234961 = 926221) B926221
theorem B1234979 : Blo 822348 1234979 := bstep (se 1 (by rfl) ⟨926234, by rfl⟩ : syracuseStep 1234979 = 1852469) B1852469
theorem B2349101 : Blo 822348 2349101 := bstep (se 3 (by rfl) ⟨440456, by rfl⟩ : syracuseStep 2349101 = 880913) B880913
theorem B1235009 : Blo 822348 1235009 := bstep (se 2 (by rfl) ⟨463128, by rfl⟩ : syracuseStep 1235009 = 926257) B926257
theorem B1857617 : Blo 822348 1857617 := bstep (se 2 (by rfl) ⟨696606, by rfl⟩ : syracuseStep 1857617 = 1393213) B1393213
theorem B1235027 : Blo 822348 1235027 := bstep (se 1 (by rfl) ⟨926270, by rfl⟩ : syracuseStep 1235027 = 1852541) B1852541
theorem B1857635 : Blo 822348 1857635 := bstep (se 1 (by rfl) ⟨1393226, by rfl⟩ : syracuseStep 1857635 = 2786453) B2786453
theorem B1235057 : Blo 822348 1235057 := bstep (se 2 (by rfl) ⟨463146, by rfl⟩ : syracuseStep 1235057 = 926293) B926293
theorem B1235075 : Blo 822348 1235075 := bstep (se 1 (by rfl) ⟨926306, by rfl⟩ : syracuseStep 1235075 = 1852613) B1852613
theorem B1235105 : Blo 822348 1235105 := bstep (se 2 (by rfl) ⟨463164, by rfl⟩ : syracuseStep 1235105 = 926329) B926329
theorem B1235123 : Blo 822348 1235123 := bstep (se 1 (by rfl) ⟨926342, by rfl⟩ : syracuseStep 1235123 = 1852685) B1852685
theorem B4446413 : Blo 822348 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B1235153 : Blo 822348 1235153 := bstep (se 2 (by rfl) ⟨463182, by rfl⟩ : syracuseStep 1235153 = 926365) B926365
theorem B1235171 : Blo 822348 1235171 := bstep (se 1 (by rfl) ⟨926378, by rfl⟩ : syracuseStep 1235171 = 1852757) B1852757
theorem B2349283 : Blo 822348 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B1235201 : Blo 822348 1235201 := bstep (se 2 (by rfl) ⟨463200, by rfl⟩ : syracuseStep 1235201 = 926401) B926401
theorem B1235219 : Blo 822348 1235219 := bstep (se 1 (by rfl) ⟨926414, by rfl⟩ : syracuseStep 1235219 = 1852829) B1852829
theorem B1562915 : Blo 822348 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B3135779 : Blo 822348 3135779 := bstep (se 1 (by rfl) ⟨2351834, by rfl⟩ : syracuseStep 3135779 = 4703669) B4703669
theorem B1235249 : Blo 822348 1235249 := bstep (se 2 (by rfl) ⟨463218, by rfl⟩ : syracuseStep 1235249 = 926437) B926437
theorem B3135793 : Blo 822348 3135793 := bstep (se 2 (by rfl) ⟨1175922, by rfl⟩ : syracuseStep 3135793 = 2351845) B2351845
theorem B1235267 : Blo 822348 1235267 := bstep (se 1 (by rfl) ⟨926450, by rfl⟩ : syracuseStep 1235267 = 1852901) B1852901
theorem B1235297 : Blo 822348 1235297 := bstep (se 2 (by rfl) ⟨463236, by rfl⟩ : syracuseStep 1235297 = 926473) B926473
theorem B1857905 : Blo 822348 1857905 := bstep (se 2 (by rfl) ⟨696714, by rfl⟩ : syracuseStep 1857905 = 1393429) B1393429
theorem B1235315 : Blo 822348 1235315 := bstep (se 1 (by rfl) ⟨926486, by rfl⟩ : syracuseStep 1235315 = 1852973) B1852973
theorem B1857923 : Blo 822348 1857923 := bstep (se 1 (by rfl) ⟨1393442, by rfl⟩ : syracuseStep 1857923 = 2786885) B2786885
theorem B2775437 : Blo 822348 2775437 := bstep (se 3 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 2775437 = 1040789) B1040789
theorem B1235345 : Blo 822348 1235345 := bstep (se 2 (by rfl) ⟨463254, by rfl⟩ : syracuseStep 1235345 = 926509) B926509
theorem B1235363 : Blo 822348 1235363 := bstep (se 1 (by rfl) ⟨926522, by rfl⟩ : syracuseStep 1235363 = 1853045) B1853045
theorem B1235393 : Blo 822348 1235393 := bstep (se 2 (by rfl) ⟨463272, by rfl⟩ : syracuseStep 1235393 = 926545) B926545
theorem B2775491 : Blo 822348 2775491 := bstep (se 1 (by rfl) ⟨2081618, by rfl⟩ : syracuseStep 2775491 = 4163237) B4163237
theorem B1235411 : Blo 822348 1235411 := bstep (se 1 (by rfl) ⟨926558, by rfl⟩ : syracuseStep 1235411 = 1853117) B1853117
theorem B1235441 : Blo 822348 1235441 := bstep (se 2 (by rfl) ⟨463290, by rfl⟩ : syracuseStep 1235441 = 926581) B926581
theorem B1235459 : Blo 822348 1235459 := bstep (se 1 (by rfl) ⟨926594, by rfl⟩ : syracuseStep 1235459 = 1853189) B1853189
theorem B2644493 : Blo 822348 2644493 := bstep (se 3 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 2644493 = 991685) B991685
theorem B2087441 : Blo 822348 2087441 := bstep (se 2 (by rfl) ⟨782790, by rfl⟩ : syracuseStep 2087441 = 1565581) B1565581
theorem B1235489 : Blo 822348 1235489 := bstep (se 2 (by rfl) ⟨463308, by rfl⟩ : syracuseStep 1235489 = 926617) B926617
theorem B1235507 : Blo 822348 1235507 := bstep (se 1 (by rfl) ⟨926630, by rfl⟩ : syracuseStep 1235507 = 1853261) B1853261
theorem B2087491 : Blo 822348 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B3758669 : Blo 822348 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1235537 : Blo 822348 1235537 := bstep (se 2 (by rfl) ⟨463326, by rfl⟩ : syracuseStep 1235537 = 926653) B926653
theorem B1235555 : Blo 822348 1235555 := bstep (se 1 (by rfl) ⟨926666, by rfl⟩ : syracuseStep 1235555 = 1853333) B1853333
theorem B1235585 : Blo 822348 1235585 := bstep (se 2 (by rfl) ⟨463344, by rfl⟩ : syracuseStep 1235585 = 926689) B926689
theorem B1858193 : Blo 822348 1858193 := bstep (se 2 (by rfl) ⟨696822, by rfl⟩ : syracuseStep 1858193 = 1393645) B1393645
theorem B1235603 : Blo 822348 1235603 := bstep (se 1 (by rfl) ⟨926702, by rfl⟩ : syracuseStep 1235603 = 1853405) B1853405
theorem B1858211 : Blo 822348 1858211 := bstep (se 1 (by rfl) ⟨1393658, by rfl⟩ : syracuseStep 1858211 = 2787317) B2787317
theorem B1235633 : Blo 822348 1235633 := bstep (se 2 (by rfl) ⟨463362, by rfl⟩ : syracuseStep 1235633 = 926725) B926725
theorem B1235651 : Blo 822348 1235651 := bstep (se 1 (by rfl) ⟨926738, by rfl⟩ : syracuseStep 1235651 = 1853477) B1853477
theorem B2349773 : Blo 822348 2349773 := bstep (se 3 (by rfl) ⟨440582, by rfl⟩ : syracuseStep 2349773 = 881165) B881165
theorem B2775761 : Blo 822348 2775761 := bstep (se 2 (by rfl) ⟨1040910, by rfl⟩ : syracuseStep 2775761 = 2081821) B2081821
theorem B2087633 : Blo 822348 2087633 := bstep (se 2 (by rfl) ⟨782862, by rfl⟩ : syracuseStep 2087633 = 1565725) B1565725
theorem B1235681 : Blo 822348 1235681 := bstep (se 2 (by rfl) ⟨463380, by rfl⟩ : syracuseStep 1235681 = 926761) B926761
theorem B1235699 : Blo 822348 1235699 := bstep (se 1 (by rfl) ⟨926774, by rfl⟩ : syracuseStep 1235699 = 1853549) B1853549
theorem B1235729 : Blo 822348 1235729 := bstep (se 2 (by rfl) ⟨463398, by rfl⟩ : syracuseStep 1235729 = 926797) B926797
theorem B1235747 : Blo 822348 1235747 := bstep (se 1 (by rfl) ⟨926810, by rfl⟩ : syracuseStep 1235747 = 1853621) B1853621
theorem B1235777 : Blo 822348 1235777 := bstep (se 2 (by rfl) ⟨463416, by rfl⟩ : syracuseStep 1235777 = 926833) B926833
theorem B1235795 : Blo 822348 1235795 := bstep (se 1 (by rfl) ⟨926846, by rfl⟩ : syracuseStep 1235795 = 1853693) B1853693
theorem B1235825 : Blo 822348 1235825 := bstep (se 2 (by rfl) ⟨463434, by rfl⟩ : syracuseStep 1235825 = 926869) B926869
theorem B1235843 : Blo 822348 1235843 := bstep (se 1 (by rfl) ⟨926882, by rfl⟩ : syracuseStep 1235843 = 1853765) B1853765
theorem B1235873 : Blo 822348 1235873 := bstep (se 2 (by rfl) ⟨463452, by rfl⟩ : syracuseStep 1235873 = 926905) B926905
theorem B1858481 : Blo 822348 1858481 := bstep (se 2 (by rfl) ⟨696930, by rfl⟩ : syracuseStep 1858481 = 1393861) B1393861
theorem B1235891 : Blo 822348 1235891 := bstep (se 1 (by rfl) ⟨926918, by rfl⟩ : syracuseStep 1235891 = 1853837) B1853837
theorem B1858499 : Blo 822348 1858499 := bstep (se 1 (by rfl) ⟨1393874, by rfl⟩ : syracuseStep 1858499 = 2787749) B2787749
theorem B1235921 : Blo 822348 1235921 := bstep (se 2 (by rfl) ⟨463470, by rfl⟩ : syracuseStep 1235921 = 926941) B926941
theorem B1235939 : Blo 822348 1235939 := bstep (se 1 (by rfl) ⟨926954, by rfl⟩ : syracuseStep 1235939 = 1853909) B1853909
theorem B1235969 : Blo 822348 1235969 := bstep (se 2 (by rfl) ⟨463488, by rfl⟩ : syracuseStep 1235969 = 926977) B926977
theorem B2382851 : Blo 822348 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1235987 : Blo 822348 1235987 := bstep (se 1 (by rfl) ⟨926990, by rfl⟩ : syracuseStep 1235987 = 1853981) B1853981
theorem B5069873 : Blo 822348 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1236017 : Blo 822348 1236017 := bstep (se 2 (by rfl) ⟨463506, by rfl⟩ : syracuseStep 1236017 = 927013) B927013
theorem B1236035 : Blo 822348 1236035 := bstep (se 1 (by rfl) ⟨927026, by rfl⟩ : syracuseStep 1236035 = 1854053) B1854053
theorem B1236065 : Blo 822348 1236065 := bstep (se 2 (by rfl) ⟨463524, by rfl⟩ : syracuseStep 1236065 = 927049) B927049
theorem B1236083 : Blo 822348 1236083 := bstep (se 1 (by rfl) ⟨927062, by rfl⟩ : syracuseStep 1236083 = 1854125) B1854125
theorem B1236113 : Blo 822348 1236113 := bstep (se 2 (by rfl) ⟨463542, by rfl⟩ : syracuseStep 1236113 = 927085) B927085
theorem B1236131 : Blo 822348 1236131 := bstep (se 1 (by rfl) ⟨927098, by rfl⟩ : syracuseStep 1236131 = 1854197) B1854197
theorem B1236161 : Blo 822348 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B1563857 : Blo 822348 1563857 := bstep (se 2 (by rfl) ⟨586446, by rfl⟩ : syracuseStep 1563857 = 1172893) B1172893
theorem B1858769 : Blo 822348 1858769 := bstep (se 2 (by rfl) ⟨697038, by rfl⟩ : syracuseStep 1858769 = 1394077) B1394077
theorem B1236179 : Blo 822348 1236179 := bstep (se 1 (by rfl) ⟨927134, by rfl⟩ : syracuseStep 1236179 = 1854269) B1854269
theorem B1858787 : Blo 822348 1858787 := bstep (se 1 (by rfl) ⟨1394090, by rfl⟩ : syracuseStep 1858787 = 2788181) B2788181
theorem B2776301 : Blo 822348 2776301 := bstep (se 3 (by rfl) ⟨520556, by rfl⟩ : syracuseStep 2776301 = 1041113) B1041113
theorem B1236209 : Blo 822348 1236209 := bstep (se 2 (by rfl) ⟨463578, by rfl⟩ : syracuseStep 1236209 = 927157) B927157
theorem B1236227 : Blo 822348 1236227 := bstep (se 1 (by rfl) ⟨927170, by rfl⟩ : syracuseStep 1236227 = 1854341) B1854341
theorem B1236257 : Blo 822348 1236257 := bstep (se 2 (by rfl) ⟨463596, by rfl⟩ : syracuseStep 1236257 = 927193) B927193
theorem B2776355 : Blo 822348 2776355 := bstep (se 1 (by rfl) ⟨2082266, by rfl⟩ : syracuseStep 2776355 = 4164533) B4164533
theorem B1236275 : Blo 822348 1236275 := bstep (se 1 (by rfl) ⟨927206, by rfl⟩ : syracuseStep 1236275 = 1854413) B1854413
theorem B1236305 : Blo 822348 1236305 := bstep (se 2 (by rfl) ⟨463614, by rfl⟩ : syracuseStep 1236305 = 927229) B927229
theorem B1236323 : Blo 822348 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B1236353 : Blo 822348 1236353 := bstep (se 2 (by rfl) ⟨463632, by rfl⟩ : syracuseStep 1236353 = 927265) B927265
theorem B5954957 : Blo 822348 5954957 := bstep (se 3 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 5954957 = 2233109) B2233109
theorem B1236371 : Blo 822348 1236371 := bstep (se 1 (by rfl) ⟨927278, by rfl⟩ : syracuseStep 1236371 = 1854557) B1854557
theorem B1236401 : Blo 822348 1236401 := bstep (se 2 (by rfl) ⟨463650, by rfl⟩ : syracuseStep 1236401 = 927301) B927301
theorem B1236419 : Blo 822348 1236419 := bstep (se 1 (by rfl) ⟨927314, by rfl⟩ : syracuseStep 1236419 = 1854629) B1854629
theorem B1236449 : Blo 822348 1236449 := bstep (se 2 (by rfl) ⟨463668, by rfl⟩ : syracuseStep 1236449 = 927337) B927337
theorem B1859057 : Blo 822348 1859057 := bstep (se 2 (by rfl) ⟨697146, by rfl⟩ : syracuseStep 1859057 = 1394293) B1394293
theorem B1236467 : Blo 822348 1236467 := bstep (se 1 (by rfl) ⟨927350, by rfl⟩ : syracuseStep 1236467 = 1854701) B1854701
theorem B1859075 : Blo 822348 1859075 := bstep (se 1 (by rfl) ⟨1394306, by rfl⟩ : syracuseStep 1859075 = 2788613) B2788613
theorem B1236497 : Blo 822348 1236497 := bstep (se 2 (by rfl) ⟨463686, by rfl⟩ : syracuseStep 1236497 = 927373) B927373
theorem B1236515 : Blo 822348 1236515 := bstep (se 1 (by rfl) ⟨927386, by rfl⟩ : syracuseStep 1236515 = 1854773) B1854773
theorem B2776625 : Blo 822348 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B1236545 : Blo 822348 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B1236563 : Blo 822348 1236563 := bstep (se 1 (by rfl) ⟨927422, by rfl⟩ : syracuseStep 1236563 = 1854845) B1854845
theorem B1236593 : Blo 822348 1236593 := bstep (se 2 (by rfl) ⟨463722, by rfl⟩ : syracuseStep 1236593 = 927445) B927445
theorem B1236611 : Blo 822348 1236611 := bstep (se 1 (by rfl) ⟨927458, by rfl⟩ : syracuseStep 1236611 = 1854917) B1854917
theorem B1236641 : Blo 822348 1236641 := bstep (se 2 (by rfl) ⟨463740, by rfl⟩ : syracuseStep 1236641 = 927481) B927481
theorem B1760945 : Blo 822348 1760945 := bstep (se 2 (by rfl) ⟨660354, by rfl⟩ : syracuseStep 1760945 = 1320709) B1320709
theorem B2088625 : Blo 822348 2088625 := bstep (se 2 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 2088625 = 1566469) B1566469
theorem B1236659 : Blo 822348 1236659 := bstep (se 1 (by rfl) ⟨927494, by rfl⟩ : syracuseStep 1236659 = 1854989) B1854989
theorem B7528133 : Blo 822348 7528133 := bstep (se 4 (by rfl) ⟨705762, by rfl⟩ : syracuseStep 7528133 = 1411525) B1411525
theorem B4284109 : Blo 822348 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B1236689 : Blo 822348 1236689 := bstep (se 2 (by rfl) ⟨463758, by rfl⟩ : syracuseStep 1236689 = 927517) B927517
theorem B1236707 : Blo 822348 1236707 := bstep (se 1 (by rfl) ⟨927530, by rfl⟩ : syracuseStep 1236707 = 1855061) B1855061
theorem B3137251 : Blo 822348 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1236737 : Blo 822348 1236737 := bstep (se 2 (by rfl) ⟨463776, by rfl⟩ : syracuseStep 1236737 = 927553) B927553
theorem B1236755 : Blo 822348 1236755 := bstep (se 1 (by rfl) ⟨927566, by rfl⟩ : syracuseStep 1236755 = 1855133) B1855133
theorem B1236785 : Blo 822348 1236785 := bstep (se 2 (by rfl) ⟨463794, by rfl⟩ : syracuseStep 1236785 = 927589) B927589
theorem B1236803 : Blo 822348 1236803 := bstep (se 1 (by rfl) ⟨927602, by rfl⟩ : syracuseStep 1236803 = 1855205) B1855205
theorem B1236833 : Blo 822348 1236833 := bstep (se 2 (by rfl) ⟨463812, by rfl⟩ : syracuseStep 1236833 = 927625) B927625
theorem B2350957 : Blo 822348 2350957 := bstep (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) B881609
theorem B1236851 : Blo 822348 1236851 := bstep (se 1 (by rfl) ⟨927638, by rfl⟩ : syracuseStep 1236851 = 1855277) B1855277
theorem B1236881 : Blo 822348 1236881 := bstep (se 2 (by rfl) ⟨463830, by rfl⟩ : syracuseStep 1236881 = 927661) B927661
theorem B1171361 : Blo 822348 1171361 := bstep (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) B878521
theorem B1236899 : Blo 822348 1236899 := bstep (se 1 (by rfl) ⟨927674, by rfl⟩ : syracuseStep 1236899 = 1855349) B1855349
theorem B1236929 : Blo 822348 1236929 := bstep (se 2 (by rfl) ⟨463848, by rfl⟩ : syracuseStep 1236929 = 927697) B927697
theorem B2088899 : Blo 822348 2088899 := bstep (se 1 (by rfl) ⟨1566674, by rfl⟩ : syracuseStep 2088899 = 3133349) B3133349
theorem B1236947 : Blo 822348 1236947 := bstep (se 1 (by rfl) ⟨927710, by rfl⟩ : syracuseStep 1236947 = 1855421) B1855421
theorem B1236977 : Blo 822348 1236977 := bstep (se 2 (by rfl) ⟨463866, by rfl⟩ : syracuseStep 1236977 = 927733) B927733
theorem B1236995 : Blo 822348 1236995 := bstep (se 1 (by rfl) ⟨927746, by rfl⟩ : syracuseStep 1236995 = 1855493) B1855493
theorem B1237025 : Blo 822348 1237025 := bstep (se 2 (by rfl) ⟨463884, by rfl⟩ : syracuseStep 1237025 = 927769) B927769
theorem B1237043 : Blo 822348 1237043 := bstep (se 1 (by rfl) ⟨927782, by rfl⟩ : syracuseStep 1237043 = 1855565) B1855565
theorem B2646083 : Blo 822348 2646083 := bstep (se 1 (by rfl) ⟨1984562, by rfl⟩ : syracuseStep 2646083 = 3969125) B3969125
theorem B2777165 : Blo 822348 2777165 := bstep (se 3 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 2777165 = 1041437) B1041437
theorem B1564753 : Blo 822348 1564753 := bstep (se 2 (by rfl) ⟨586782, by rfl⟩ : syracuseStep 1564753 = 1173565) B1173565
theorem B1237073 : Blo 822348 1237073 := bstep (se 2 (by rfl) ⟨463902, by rfl⟩ : syracuseStep 1237073 = 927805) B927805
theorem B1237091 : Blo 822348 1237091 := bstep (se 1 (by rfl) ⟨927818, by rfl⟩ : syracuseStep 1237091 = 1855637) B1855637
theorem B1237121 : Blo 822348 1237121 := bstep (se 2 (by rfl) ⟨463920, by rfl⟩ : syracuseStep 1237121 = 927841) B927841
theorem B2777219 : Blo 822348 2777219 := bstep (se 1 (by rfl) ⟨2082914, by rfl⟩ : syracuseStep 2777219 = 4165829) B4165829
theorem B2089091 : Blo 822348 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B1237139 : Blo 822348 1237139 := bstep (se 1 (by rfl) ⟨927854, by rfl⟩ : syracuseStep 1237139 = 1855709) B1855709
theorem B5005475 : Blo 822348 5005475 := bstep (se 1 (by rfl) ⟨3754106, by rfl⟩ : syracuseStep 5005475 = 7508213) B7508213
theorem B1237169 : Blo 822348 1237169 := bstep (se 2 (by rfl) ⟨463938, by rfl⟩ : syracuseStep 1237169 = 927877) B927877
theorem B1237187 : Blo 822348 1237187 := bstep (se 1 (by rfl) ⟨927890, by rfl⟩ : syracuseStep 1237187 = 1855781) B1855781
theorem B1237217 : Blo 822348 1237217 := bstep (se 2 (by rfl) ⟨463956, by rfl⟩ : syracuseStep 1237217 = 927913) B927913
theorem B1564913 : Blo 822348 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B1237235 : Blo 822348 1237235 := bstep (se 1 (by rfl) ⟨927926, by rfl⟩ : syracuseStep 1237235 = 1855853) B1855853
theorem B3170573 : Blo 822348 3170573 := bstep (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) B1188965
theorem B1237265 : Blo 822348 1237265 := bstep (se 2 (by rfl) ⟨463974, by rfl⟩ : syracuseStep 1237265 = 927949) B927949
theorem B1237283 : Blo 822348 1237283 := bstep (se 1 (by rfl) ⟨927962, by rfl⟩ : syracuseStep 1237283 = 1855925) B1855925
theorem B1237313 : Blo 822348 1237313 := bstep (se 2 (by rfl) ⟨463992, by rfl⟩ : syracuseStep 1237313 = 927985) B927985
theorem B1237331 : Blo 822348 1237331 := bstep (se 1 (by rfl) ⟨927998, by rfl⟩ : syracuseStep 1237331 = 1855997) B1855997
theorem B1237361 : Blo 822348 1237361 := bstep (se 2 (by rfl) ⟨464010, by rfl⟩ : syracuseStep 1237361 = 928021) B928021
theorem B1237379 : Blo 822348 1237379 := bstep (se 1 (by rfl) ⟨928034, by rfl⟩ : syracuseStep 1237379 = 1856069) B1856069
theorem B2777489 : Blo 822348 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B1237409 : Blo 822348 1237409 := bstep (se 2 (by rfl) ⟨464028, by rfl⟩ : syracuseStep 1237409 = 928057) B928057
theorem B1237427 : Blo 822348 1237427 := bstep (se 1 (by rfl) ⟨928070, by rfl⟩ : syracuseStep 1237427 = 1856141) B1856141
theorem B1237457 : Blo 822348 1237457 := bstep (se 2 (by rfl) ⟨464046, by rfl⟩ : syracuseStep 1237457 = 928093) B928093
theorem B1237475 : Blo 822348 1237475 := bstep (se 1 (by rfl) ⟨928106, by rfl⟩ : syracuseStep 1237475 = 1856213) B1856213
theorem B1237505 : Blo 822348 1237505 := bstep (se 2 (by rfl) ⟨464064, by rfl⟩ : syracuseStep 1237505 = 928129) B928129
theorem B1237523 : Blo 822348 1237523 := bstep (se 1 (by rfl) ⟨928142, by rfl⟩ : syracuseStep 1237523 = 1856285) B1856285
theorem B1237553 : Blo 822348 1237553 := bstep (se 2 (by rfl) ⟨464082, by rfl⟩ : syracuseStep 1237553 = 928165) B928165
theorem B1237571 : Blo 822348 1237571 := bstep (se 1 (by rfl) ⟨928178, by rfl⟩ : syracuseStep 1237571 = 1856357) B1856357
theorem B1237601 : Blo 822348 1237601 := bstep (se 2 (by rfl) ⟨464100, by rfl⟩ : syracuseStep 1237601 = 928201) B928201
theorem B1237619 : Blo 822348 1237619 := bstep (se 1 (by rfl) ⟨928214, by rfl⟩ : syracuseStep 1237619 = 1856429) B1856429
theorem B1565315 : Blo 822348 1565315 := bstep (se 1 (by rfl) ⟨1173986, by rfl⟩ : syracuseStep 1565315 = 2347973) B2347973
theorem B1237649 : Blo 822348 1237649 := bstep (se 2 (by rfl) ⟨464118, by rfl⟩ : syracuseStep 1237649 = 928237) B928237
theorem B1237667 : Blo 822348 1237667 := bstep (se 1 (by rfl) ⟨928250, by rfl⟩ : syracuseStep 1237667 = 1856501) B1856501
theorem B1237697 : Blo 822348 1237697 := bstep (se 2 (by rfl) ⟨464136, by rfl⟩ : syracuseStep 1237697 = 928273) B928273
theorem B1237715 : Blo 822348 1237715 := bstep (se 1 (by rfl) ⟨928286, by rfl⟩ : syracuseStep 1237715 = 1856573) B1856573
theorem B1237745 : Blo 822348 1237745 := bstep (se 2 (by rfl) ⟨464154, by rfl⟩ : syracuseStep 1237745 = 928309) B928309
theorem B1172227 : Blo 822348 1172227 := bstep (se 1 (by rfl) ⟨879170, by rfl⟩ : syracuseStep 1172227 = 1758341) B1758341
theorem B1237763 : Blo 822348 1237763 := bstep (se 1 (by rfl) ⟨928322, by rfl⟩ : syracuseStep 1237763 = 1856645) B1856645
theorem B1237793 : Blo 822348 1237793 := bstep (se 2 (by rfl) ⟨464172, by rfl⟩ : syracuseStep 1237793 = 928345) B928345
theorem B1237811 : Blo 822348 1237811 := bstep (se 1 (by rfl) ⟨928358, by rfl⟩ : syracuseStep 1237811 = 1856717) B1856717
theorem B1237841 : Blo 822348 1237841 := bstep (se 2 (by rfl) ⟨464190, by rfl⟩ : syracuseStep 1237841 = 928381) B928381
theorem B1172323 : Blo 822348 1172323 := bstep (se 1 (by rfl) ⟨879242, by rfl⟩ : syracuseStep 1172323 = 1758485) B1758485
theorem B1237859 : Blo 822348 1237859 := bstep (se 1 (by rfl) ⟨928394, by rfl⟩ : syracuseStep 1237859 = 1856789) B1856789
theorem B1237889 : Blo 822348 1237889 := bstep (se 2 (by rfl) ⟨464208, by rfl⟩ : syracuseStep 1237889 = 928417) B928417
theorem B2352017 : Blo 822348 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B1237907 : Blo 822348 1237907 := bstep (se 1 (by rfl) ⟨928430, by rfl⟩ : syracuseStep 1237907 = 1856861) B1856861
theorem B2778029 : Blo 822348 2778029 := bstep (se 3 (by rfl) ⟨520880, by rfl⟩ : syracuseStep 2778029 = 1041761) B1041761
theorem B1237937 : Blo 822348 1237937 := bstep (se 2 (by rfl) ⟨464226, by rfl⟩ : syracuseStep 1237937 = 928453) B928453
theorem B1041331 : Blo 822348 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B1237955 : Blo 822348 1237955 := bstep (se 1 (by rfl) ⟨928466, by rfl⟩ : syracuseStep 1237955 = 1856933) B1856933
theorem B1237985 : Blo 822348 1237985 := bstep (se 2 (by rfl) ⟨464244, by rfl⟩ : syracuseStep 1237985 = 928489) B928489
theorem B2778083 : Blo 822348 2778083 := bstep (se 1 (by rfl) ⟨2083562, by rfl⟩ : syracuseStep 2778083 = 4167125) B4167125
theorem B1238003 : Blo 822348 1238003 := bstep (se 1 (by rfl) ⟨928502, by rfl⟩ : syracuseStep 1238003 = 1857005) B1857005
theorem B1238033 : Blo 822348 1238033 := bstep (se 2 (by rfl) ⟨464262, by rfl⟩ : syracuseStep 1238033 = 928525) B928525
theorem B1041427 : Blo 822348 1041427 := bstep (se 1 (by rfl) ⟨781070, by rfl⟩ : syracuseStep 1041427 = 1562141) B1562141
theorem B1238051 : Blo 822348 1238051 := bstep (se 1 (by rfl) ⟨928538, by rfl⟩ : syracuseStep 1238051 = 1857077) B1857077
theorem B2974769 : Blo 822348 2974769 := bstep (se 2 (by rfl) ⟨1115538, by rfl⟩ : syracuseStep 2974769 = 2231077) B2231077
theorem B2090033 : Blo 822348 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1238081 : Blo 822348 1238081 := bstep (se 2 (by rfl) ⟨464280, by rfl⟩ : syracuseStep 1238081 = 928561) B928561
theorem B1238099 : Blo 822348 1238099 := bstep (se 1 (by rfl) ⟨928574, by rfl⟩ : syracuseStep 1238099 = 1857149) B1857149
theorem B2090083 : Blo 822348 2090083 := bstep (se 1 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 2090083 = 3135125) B3135125
theorem B1238129 : Blo 822348 1238129 := bstep (se 2 (by rfl) ⟨464298, by rfl⟩ : syracuseStep 1238129 = 928597) B928597
theorem B1238147 : Blo 822348 1238147 := bstep (se 1 (by rfl) ⟨928610, by rfl⟩ : syracuseStep 1238147 = 1857221) B1857221
theorem B1238177 : Blo 822348 1238177 := bstep (se 2 (by rfl) ⟨464316, by rfl⟩ : syracuseStep 1238177 = 928633) B928633
theorem B1238195 : Blo 822348 1238195 := bstep (se 1 (by rfl) ⟨928646, by rfl⟩ : syracuseStep 1238195 = 1857293) B1857293
theorem B1238225 : Blo 822348 1238225 := bstep (se 2 (by rfl) ⟨464334, by rfl⟩ : syracuseStep 1238225 = 928669) B928669
theorem B1238243 : Blo 822348 1238243 := bstep (se 1 (by rfl) ⟨928682, by rfl⟩ : syracuseStep 1238243 = 1857365) B1857365
theorem B2778353 : Blo 822348 2778353 := bstep (se 2 (by rfl) ⟨1041882, by rfl⟩ : syracuseStep 2778353 = 2083765) B2083765
theorem B2090225 : Blo 822348 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B1238273 : Blo 822348 1238273 := bstep (se 2 (by rfl) ⟨464352, by rfl⟩ : syracuseStep 1238273 = 928705) B928705
theorem B1238291 : Blo 822348 1238291 := bstep (se 1 (by rfl) ⟨928718, by rfl⟩ : syracuseStep 1238291 = 1857437) B1857437
theorem B1238321 : Blo 822348 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B1238339 : Blo 822348 1238339 := bstep (se 1 (by rfl) ⟨928754, by rfl⟩ : syracuseStep 1238339 = 1857509) B1857509
theorem B2385229 : Blo 822348 2385229 := bstep (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) B894461
theorem B1172819 : Blo 822348 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B1238369 : Blo 822348 1238369 := bstep (se 2 (by rfl) ⟨464388, by rfl⟩ : syracuseStep 1238369 = 928777) B928777
theorem B1238387 : Blo 822348 1238387 := bstep (se 1 (by rfl) ⟨928790, by rfl⟩ : syracuseStep 1238387 = 1857581) B1857581
theorem B1238417 : Blo 822348 1238417 := bstep (se 2 (by rfl) ⟨464406, by rfl⟩ : syracuseStep 1238417 = 928813) B928813
theorem B1238435 : Blo 822348 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B1238465 : Blo 822348 1238465 := bstep (se 2 (by rfl) ⟨464424, by rfl⟩ : syracuseStep 1238465 = 928849) B928849
theorem B1238483 : Blo 822348 1238483 := bstep (se 1 (by rfl) ⟨928862, by rfl⟩ : syracuseStep 1238483 = 1857725) B1857725
theorem B3335651 : Blo 822348 3335651 := bstep (se 1 (by rfl) ⟨2501738, by rfl⟩ : syracuseStep 3335651 = 5003477) B5003477
theorem B1238513 : Blo 822348 1238513 := bstep (se 2 (by rfl) ⟨464442, by rfl⟩ : syracuseStep 1238513 = 928885) B928885
theorem B1041923 : Blo 822348 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B1566211 : Blo 822348 1566211 := bstep (se 1 (by rfl) ⟨1174658, by rfl⟩ : syracuseStep 1566211 = 2349317) B2349317
theorem B1238531 : Blo 822348 1238531 := bstep (se 1 (by rfl) ⟨928898, by rfl⟩ : syracuseStep 1238531 = 1857797) B1857797
theorem B1238561 : Blo 822348 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B2352689 : Blo 822348 2352689 := bstep (se 2 (by rfl) ⟨882258, by rfl⟩ : syracuseStep 2352689 = 1764517) B1764517
theorem B1238579 : Blo 822348 1238579 := bstep (se 1 (by rfl) ⟨928934, by rfl⟩ : syracuseStep 1238579 = 1857869) B1857869
theorem B1238609 : Blo 822348 1238609 := bstep (se 2 (by rfl) ⟨464478, by rfl⟩ : syracuseStep 1238609 = 928957) B928957
theorem B3335779 : Blo 822348 3335779 := bstep (se 1 (by rfl) ⟨2501834, by rfl⟩ : syracuseStep 3335779 = 5003669) B5003669
theorem B1238627 : Blo 822348 1238627 := bstep (se 1 (by rfl) ⟨928970, by rfl⟩ : syracuseStep 1238627 = 1857941) B1857941
theorem B1238657 : Blo 822348 1238657 := bstep (se 2 (by rfl) ⟨464496, by rfl⟩ : syracuseStep 1238657 = 928993) B928993
theorem B1238675 : Blo 822348 1238675 := bstep (se 1 (by rfl) ⟨929006, by rfl⟩ : syracuseStep 1238675 = 1858013) B1858013
theorem B1566371 : Blo 822348 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B1238705 : Blo 822348 1238705 := bstep (se 2 (by rfl) ⟨464514, by rfl⟩ : syracuseStep 1238705 = 929029) B929029
theorem B1238723 : Blo 822348 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1238753 : Blo 822348 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B2975459 : Blo 822348 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B1238771 : Blo 822348 1238771 := bstep (se 1 (by rfl) ⟨929078, by rfl⟩ : syracuseStep 1238771 = 1858157) B1858157
theorem B2778893 : Blo 822348 2778893 := bstep (se 3 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 2778893 = 1042085) B1042085
theorem B1238801 : Blo 822348 1238801 := bstep (se 2 (by rfl) ⟨464550, by rfl⟩ : syracuseStep 1238801 = 929101) B929101
theorem B1238819 : Blo 822348 1238819 := bstep (se 1 (by rfl) ⟨929114, by rfl⟩ : syracuseStep 1238819 = 1858229) B1858229
theorem B1238849 : Blo 822348 1238849 := bstep (se 2 (by rfl) ⟨464568, by rfl⟩ : syracuseStep 1238849 = 929137) B929137
theorem B2778947 : Blo 822348 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B1238867 : Blo 822348 1238867 := bstep (se 1 (by rfl) ⟨929150, by rfl⟩ : syracuseStep 1238867 = 1858301) B1858301
theorem B1238897 : Blo 822348 1238897 := bstep (se 2 (by rfl) ⟨464586, by rfl⟩ : syracuseStep 1238897 = 929173) B929173
theorem B1238915 : Blo 822348 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B1238945 : Blo 822348 1238945 := bstep (se 2 (by rfl) ⟨464604, by rfl⟩ : syracuseStep 1238945 = 929209) B929209
theorem B1238963 : Blo 822348 1238963 := bstep (se 1 (by rfl) ⟨929222, by rfl⟩ : syracuseStep 1238963 = 1858445) B1858445
theorem B1173457 : Blo 822348 1173457 := bstep (se 2 (by rfl) ⟨440046, by rfl⟩ : syracuseStep 1173457 = 880093) B880093
theorem B1238993 : Blo 822348 1238993 := bstep (se 2 (by rfl) ⟨464622, by rfl⟩ : syracuseStep 1238993 = 929245) B929245
theorem B1239011 : Blo 822348 1239011 := bstep (se 1 (by rfl) ⟨929258, by rfl⟩ : syracuseStep 1239011 = 1858517) B1858517
theorem B1239041 : Blo 822348 1239041 := bstep (se 2 (by rfl) ⟨464640, by rfl⟩ : syracuseStep 1239041 = 929281) B929281
theorem B1239059 : Blo 822348 1239059 := bstep (se 1 (by rfl) ⟨929294, by rfl⟩ : syracuseStep 1239059 = 1858589) B1858589
theorem B1239089 : Blo 822348 1239089 := bstep (se 2 (by rfl) ⟨464658, by rfl⟩ : syracuseStep 1239089 = 929317) B929317
theorem B1239107 : Blo 822348 1239107 := bstep (se 1 (by rfl) ⟨929330, by rfl⟩ : syracuseStep 1239107 = 1858661) B1858661
theorem B2779217 : Blo 822348 2779217 := bstep (se 2 (by rfl) ⟨1042206, by rfl⟩ : syracuseStep 2779217 = 2084413) B2084413
theorem B1239137 : Blo 822348 1239137 := bstep (se 2 (by rfl) ⟨464676, by rfl⟩ : syracuseStep 1239137 = 929353) B929353
theorem B1239155 : Blo 822348 1239155 := bstep (se 1 (by rfl) ⟨929366, by rfl⟩ : syracuseStep 1239155 = 1858733) B1858733
theorem B1239185 : Blo 822348 1239185 := bstep (se 2 (by rfl) ⟨464694, by rfl⟩ : syracuseStep 1239185 = 929389) B929389
theorem B1239203 : Blo 822348 1239203 := bstep (se 1 (by rfl) ⟨929402, by rfl⟩ : syracuseStep 1239203 = 1858805) B1858805
theorem B1239233 : Blo 822348 1239233 := bstep (se 2 (by rfl) ⟨464712, by rfl⟩ : syracuseStep 1239233 = 929425) B929425
theorem B1042627 : Blo 822348 1042627 := bstep (se 1 (by rfl) ⟨781970, by rfl⟩ : syracuseStep 1042627 = 1563941) B1563941
theorem B2091217 : Blo 822348 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B1239251 : Blo 822348 1239251 := bstep (se 1 (by rfl) ⟨929438, by rfl⟩ : syracuseStep 1239251 = 1858877) B1858877
theorem B38070499 : Blo 822348 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B1239281 : Blo 822348 1239281 := bstep (se 2 (by rfl) ⟨464730, by rfl⟩ : syracuseStep 1239281 = 929461) B929461
theorem B1239299 : Blo 822348 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B1173793 : Blo 822348 1173793 := bstep (se 2 (by rfl) ⟨440172, by rfl⟩ : syracuseStep 1173793 = 880345) B880345
theorem B1239329 : Blo 822348 1239329 := bstep (se 2 (by rfl) ⟨464748, by rfl⟩ : syracuseStep 1239329 = 929497) B929497
theorem B1042723 : Blo 822348 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B3336497 : Blo 822348 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B1239347 : Blo 822348 1239347 := bstep (se 1 (by rfl) ⟨929510, by rfl⟩ : syracuseStep 1239347 = 1859021) B1859021
theorem B1239377 : Blo 822348 1239377 := bstep (se 2 (by rfl) ⟨464766, by rfl⟩ : syracuseStep 1239377 = 929533) B929533
theorem B846163 : Blo 822348 846163 := bstep (se 1 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 846163 = 1269245) B1269245
theorem B1239395 : Blo 822348 1239395 := bstep (se 1 (by rfl) ⟨929546, by rfl⟩ : syracuseStep 1239395 = 1859093) B1859093
theorem B1239425 : Blo 822348 1239425 := bstep (se 2 (by rfl) ⟨464784, by rfl⟩ : syracuseStep 1239425 = 929569) B929569
theorem B1239443 : Blo 822348 1239443 := bstep (se 1 (by rfl) ⟨929582, by rfl⟩ : syracuseStep 1239443 = 1859165) B1859165
theorem B1239473 : Blo 822348 1239473 := bstep (se 2 (by rfl) ⟨464802, by rfl⟩ : syracuseStep 1239473 = 929605) B929605
theorem B1239491 : Blo 822348 1239491 := bstep (se 1 (by rfl) ⟨929618, by rfl⟩ : syracuseStep 1239491 = 1859237) B1859237
theorem B1239521 : Blo 822348 1239521 := bstep (se 2 (by rfl) ⟨464820, by rfl⟩ : syracuseStep 1239521 = 929641) B929641
theorem B2091491 : Blo 822348 2091491 := bstep (se 1 (by rfl) ⟨1568618, by rfl⟩ : syracuseStep 2091491 = 3137237) B3137237
theorem B2779757 : Blo 822348 2779757 := bstep (se 3 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 2779757 = 1042409) B1042409
theorem B2779811 : Blo 822348 2779811 := bstep (se 1 (by rfl) ⟨2084858, by rfl⟩ : syracuseStep 2779811 = 4169717) B4169717
theorem B2091683 : Blo 822348 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B1567441 : Blo 822348 1567441 := bstep (se 2 (by rfl) ⟨587790, by rfl⟩ : syracuseStep 1567441 = 1175581) B1175581
theorem B879379 : Blo 822348 879379 := bstep (se 1 (by rfl) ⟨659534, by rfl⟩ : syracuseStep 879379 = 1319069) B1319069
theorem B1043219 : Blo 822348 1043219 := bstep (se 1 (by rfl) ⟨782414, by rfl⟩ : syracuseStep 1043219 = 1564829) B1564829
theorem B1174385 : Blo 822348 1174385 := bstep (se 2 (by rfl) ⟨440394, by rfl⟩ : syracuseStep 1174385 = 880789) B880789
theorem B4451213 : Blo 822348 4451213 := bstep (se 3 (by rfl) ⟨834602, by rfl⟩ : syracuseStep 4451213 = 1669205) B1669205
theorem B2780081 : Blo 822348 2780081 := bstep (se 2 (by rfl) ⟨1042530, by rfl⟩ : syracuseStep 2780081 = 2085061) B2085061
theorem B1764355 : Blo 822348 1764355 := bstep (se 1 (by rfl) ⟨1323266, by rfl⟩ : syracuseStep 1764355 = 2646533) B2646533
theorem B10022129 : Blo 822348 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B1273153 : Blo 822348 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B5008709 : Blo 822348 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B1174915 : Blo 822348 1174915 := bstep (se 1 (by rfl) ⟨881186, by rfl⟩ : syracuseStep 1174915 = 1762373) B1762373
theorem B2780621 : Blo 822348 2780621 := bstep (se 3 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 2780621 = 1042733) B1042733
theorem B1043923 : Blo 822348 1043923 := bstep (se 1 (by rfl) ⟨782942, by rfl⟩ : syracuseStep 1043923 = 1565885) B1565885
theorem B2780675 : Blo 822348 2780675 := bstep (se 1 (by rfl) ⟨2085506, by rfl⟩ : syracuseStep 2780675 = 4171013) B4171013
theorem B1044019 : Blo 822348 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B11857549 : Blo 822348 11857549 := bstep (se 3 (by rfl) ⟨2223290, by rfl⟩ : syracuseStep 11857549 = 4446581) B4446581
theorem B1175251 : Blo 822348 1175251 := bstep (se 1 (by rfl) ⟨881438, by rfl⟩ : syracuseStep 1175251 = 1762877) B1762877
theorem B1568497 : Blo 822348 1568497 := bstep (se 2 (by rfl) ⟨588186, by rfl⟩ : syracuseStep 1568497 = 1176373) B1176373
theorem B3960589 : Blo 822348 3960589 := bstep (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) B1485221
theorem B2780945 : Blo 822348 2780945 := bstep (se 2 (by rfl) ⟨1042854, by rfl⟩ : syracuseStep 2780945 = 2085709) B2085709
theorem B20279267 : Blo 822348 20279267 := bstep (se 1 (by rfl) ⟨15209450, by rfl⟩ : syracuseStep 20279267 = 30418901) B30418901
theorem B10547171 : Blo 822348 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B1044515 : Blo 822348 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B3764323 : Blo 822348 3764323 := bstep (se 1 (by rfl) ⟨2823242, by rfl⟩ : syracuseStep 3764323 = 5646485) B5646485
theorem B2257091 : Blo 822348 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B1667299 : Blo 822348 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B6254819 : Blo 822348 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B1175809 : Blo 822348 1175809 := bstep (se 2 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 1175809 = 881857) B881857
theorem B1175843 : Blo 822348 1175843 := bstep (se 1 (by rfl) ⟨881882, by rfl⟩ : syracuseStep 1175843 = 1763765) B1763765
theorem B2781485 : Blo 822348 2781485 := bstep (se 3 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 2781485 = 1043057) B1043057
theorem B2781539 : Blo 822348 2781539 := bstep (se 1 (by rfl) ⟨2086154, by rfl⟩ : syracuseStep 2781539 = 4172309) B4172309
theorem B2224589 : Blo 822348 2224589 := bstep (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) B834221
theorem B2224675 : Blo 822348 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B2781809 : Blo 822348 2781809 := bstep (se 2 (by rfl) ⟨1043178, by rfl⟩ : syracuseStep 2781809 = 2086357) B2086357
theorem B1340081 : Blo 822348 1340081 := bstep (se 2 (by rfl) ⟨502530, by rfl⟩ : syracuseStep 1340081 = 1005061) B1005061
theorem B4453069 : Blo 822348 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B1045219 : Blo 822348 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B3961649 : Blo 822348 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B1045315 : Blo 822348 1045315 := bstep (se 1 (by rfl) ⟨783986, by rfl⟩ : syracuseStep 1045315 = 1567973) B1567973
theorem B1176401 : Blo 822348 1176401 := bstep (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) B882301
theorem B1176481 : Blo 822348 1176481 := bstep (se 2 (by rfl) ⟨441180, by rfl⟩ : syracuseStep 1176481 = 882361) B882361
theorem B2782349 : Blo 822348 2782349 := bstep (se 3 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 2782349 = 1043381) B1043381
theorem B2782403 : Blo 822348 2782403 := bstep (se 1 (by rfl) ⟨2086802, by rfl⟩ : syracuseStep 2782403 = 4173605) B4173605
theorem B1045811 : Blo 822348 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B882019 : Blo 822348 882019 := bstep (se 1 (by rfl) ⟨661514, by rfl⟩ : syracuseStep 882019 = 1323029) B1323029
theorem B2782673 : Blo 822348 2782673 := bstep (se 2 (by rfl) ⟨1043502, by rfl⟩ : syracuseStep 2782673 = 2087005) B2087005
theorem B2225713 : Blo 822348 2225713 := bstep (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) B1669285
theorem B2783213 : Blo 822348 2783213 := bstep (se 3 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 2783213 = 1043705) B1043705
theorem B7927793 : Blo 822348 7927793 := bstep (se 2 (by rfl) ⟨2972922, by rfl⟩ : syracuseStep 7927793 = 5945845) B5945845
theorem B1669123 : Blo 822348 1669123 := bstep (se 1 (by rfl) ⟨1251842, by rfl⟩ : syracuseStep 1669123 = 2503685) B2503685
theorem B2226179 : Blo 822348 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B2783267 : Blo 822348 2783267 := bstep (se 1 (by rfl) ⟨2087450, by rfl⟩ : syracuseStep 2783267 = 4174901) B4174901
theorem B2783537 : Blo 822348 2783537 := bstep (se 2 (by rfl) ⟨1043826, by rfl⟩ : syracuseStep 2783537 = 2087653) B2087653
theorem B1505603 : Blo 822348 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B11893301 : Blo 822348 11893301 := bstep (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) B1114997
theorem B2784077 : Blo 822348 2784077 := bstep (se 3 (by rfl) ⟨522014, by rfl⟩ : syracuseStep 2784077 = 1044029) B1044029
theorem B2784131 : Blo 822348 2784131 := bstep (se 1 (by rfl) ⟨2088098, by rfl⟩ : syracuseStep 2784131 = 4176197) B4176197
theorem B9370565 : Blo 822348 9370565 := bstep (se 4 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 9370565 = 1756981) B1756981
theorem B4062221 : Blo 822348 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B2227313 : Blo 822348 2227313 := bstep (se 2 (by rfl) ⟨835242, by rfl⟩ : syracuseStep 2227313 = 1670485) B1670485
theorem B2784401 : Blo 822348 2784401 := bstep (se 2 (by rfl) ⟨1044150, by rfl⟩ : syracuseStep 2784401 = 2088301) B2088301
theorem B2817251 : Blo 822348 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B4521521 : Blo 822348 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B3014243 : Blo 822348 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B2784941 : Blo 822348 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B2784995 : Blo 822348 2784995 := bstep (se 1 (by rfl) ⟨2088746, by rfl⟩ : syracuseStep 2784995 = 4177493) B4177493
theorem B1113841 : Blo 822348 1113841 := bstep (se 2 (by rfl) ⟨417690, by rfl⟩ : syracuseStep 1113841 = 835381) B835381
theorem B2785265 : Blo 822348 2785265 := bstep (se 2 (by rfl) ⟨1044474, by rfl⟩ : syracuseStep 2785265 = 2088949) B2088949
theorem B5931083 : Blo 822348 5931083 := bstep (se 1 (by rfl) ⟨4448312, by rfl⟩ : syracuseStep 5931083 = 8896625) B8896625
theorem B2785373 : Blo 822348 2785373 := bstep (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) B1044515
theorem B1114393 : Blo 822348 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B4686173 : Blo 822348 4686173 := bstep (se 3 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 4686173 = 1757315) B1757315
theorem B60293645 : Blo 822348 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B6685571 : Blo 822348 6685571 := bstep (se 1 (by rfl) ⟨5014178, by rfl⟩ : syracuseStep 6685571 = 10028357) B10028357
theorem B1115095 : Blo 822348 1115095 := bstep (se 1 (by rfl) ⟨836321, by rfl⟩ : syracuseStep 1115095 = 1672643) B1672643
theorem B4686923 : Blo 822348 4686923 := bstep (se 1 (by rfl) ⟨3515192, by rfl⟩ : syracuseStep 4686923 = 7030385) B7030385
theorem B2786507 : Blo 822348 2786507 := bstep (se 1 (by rfl) ⟨2089880, by rfl⟩ : syracuseStep 2786507 = 4179761) B4179761
theorem B5932237 : Blo 822348 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B6685901 : Blo 822348 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B2786777 : Blo 822348 2786777 := bstep (se 2 (by rfl) ⟨1045041, by rfl⟩ : syracuseStep 2786777 = 2090083) B2090083
theorem B1508951 : Blo 822348 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B3180305 : Blo 822348 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B2819933 : Blo 822348 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B3967127 : Blo 822348 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B2787479 : Blo 822348 2787479 := bstep (se 1 (by rfl) ⟨2090609, by rfl⟩ : syracuseStep 2787479 = 4181219) B4181219
theorem B4163885 : Blo 822348 4163885 := bstep (se 3 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 4163885 = 1561457) B1561457
theorem B3344861 : Blo 822348 3344861 := bstep (se 3 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 3344861 = 1254323) B1254323
theorem B10029719 : Blo 822348 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B4688563 : Blo 822348 4688563 := bstep (se 1 (by rfl) ⟨3516422, by rfl⟩ : syracuseStep 4688563 = 7032845) B7032845
theorem B2788019 : Blo 822348 2788019 := bstep (se 1 (by rfl) ⟨2091014, by rfl⟩ : syracuseStep 2788019 = 4182029) B4182029
theorem B2788289 : Blo 822348 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B50760665 : Blo 822348 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B822359 : Blo 822348 822359 := bstep (se 1 (by rfl) ⟨616769, by rfl⟩ : syracuseStep 822359 = 1233539) B1233539
theorem B822379 : Blo 822348 822379 := bstep (se 1 (by rfl) ⟨616784, by rfl⟩ : syracuseStep 822379 = 1233569) B1233569
theorem B822391 : Blo 822348 822391 := bstep (se 1 (by rfl) ⟨616793, by rfl⟩ : syracuseStep 822391 = 1233587) B1233587
theorem B822411 : Blo 822348 822411 := bstep (se 1 (by rfl) ⟨616808, by rfl⟩ : syracuseStep 822411 = 1233617) B1233617
theorem B822423 : Blo 822348 822423 := bstep (se 1 (by rfl) ⟨616817, by rfl⟩ : syracuseStep 822423 = 1233635) B1233635
theorem B822443 : Blo 822348 822443 := bstep (se 1 (by rfl) ⟨616832, by rfl⟩ : syracuseStep 822443 = 1233665) B1233665
theorem B822455 : Blo 822348 822455 := bstep (se 1 (by rfl) ⟨616841, by rfl⟩ : syracuseStep 822455 = 1233683) B1233683
theorem B822475 : Blo 822348 822475 := bstep (se 1 (by rfl) ⟨616856, by rfl⟩ : syracuseStep 822475 = 1233713) B1233713
theorem B822487 : Blo 822348 822487 := bstep (se 1 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 822487 = 1233731) B1233731
theorem B822507 : Blo 822348 822507 := bstep (se 1 (by rfl) ⟨616880, by rfl⟩ : syracuseStep 822507 = 1233761) B1233761
theorem B822519 : Blo 822348 822519 := bstep (se 1 (by rfl) ⟨616889, by rfl⟩ : syracuseStep 822519 = 1233779) B1233779
theorem B822539 : Blo 822348 822539 := bstep (se 1 (by rfl) ⟨616904, by rfl⟩ : syracuseStep 822539 = 1233809) B1233809
theorem B822551 : Blo 822348 822551 := bstep (se 1 (by rfl) ⟨616913, by rfl⟩ : syracuseStep 822551 = 1233827) B1233827
theorem B822571 : Blo 822348 822571 := bstep (se 1 (by rfl) ⟨616928, by rfl⟩ : syracuseStep 822571 = 1233857) B1233857
theorem B822583 : Blo 822348 822583 := bstep (se 1 (by rfl) ⟨616937, by rfl⟩ : syracuseStep 822583 = 1233875) B1233875
theorem B822603 : Blo 822348 822603 := bstep (se 1 (by rfl) ⟨616952, by rfl⟩ : syracuseStep 822603 = 1233905) B1233905
theorem B822615 : Blo 822348 822615 := bstep (se 1 (by rfl) ⟨616961, by rfl⟩ : syracuseStep 822615 = 1233923) B1233923
theorem B6262109 : Blo 822348 6262109 := bstep (se 3 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 6262109 = 2348291) B2348291
theorem B822635 : Blo 822348 822635 := bstep (se 1 (by rfl) ⟨616976, by rfl⟩ : syracuseStep 822635 = 1233953) B1233953
theorem B10587509 : Blo 822348 10587509 := bstep (se 5 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 10587509 = 992579) B992579
theorem B822647 : Blo 822348 822647 := bstep (se 1 (by rfl) ⟨616985, by rfl⟩ : syracuseStep 822647 = 1233971) B1233971
theorem B822667 : Blo 822348 822667 := bstep (se 1 (by rfl) ⟨617000, by rfl⟩ : syracuseStep 822667 = 1234001) B1234001
theorem B822679 : Blo 822348 822679 := bstep (se 1 (by rfl) ⟨617009, by rfl⟩ : syracuseStep 822679 = 1234019) B1234019
theorem B822699 : Blo 822348 822699 := bstep (se 1 (by rfl) ⟨617024, by rfl⟩ : syracuseStep 822699 = 1234049) B1234049
theorem B822711 : Blo 822348 822711 := bstep (se 1 (by rfl) ⟨617033, by rfl⟩ : syracuseStep 822711 = 1234067) B1234067
theorem B822731 : Blo 822348 822731 := bstep (se 1 (by rfl) ⟨617048, by rfl⟩ : syracuseStep 822731 = 1234097) B1234097
theorem B822743 : Blo 822348 822743 := bstep (se 1 (by rfl) ⟨617057, by rfl⟩ : syracuseStep 822743 = 1234115) B1234115
theorem B2788829 : Blo 822348 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B822763 : Blo 822348 822763 := bstep (se 1 (by rfl) ⟨617072, by rfl⟩ : syracuseStep 822763 = 1234145) B1234145
theorem B822775 : Blo 822348 822775 := bstep (se 1 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 822775 = 1234163) B1234163
theorem B822795 : Blo 822348 822795 := bstep (se 1 (by rfl) ⟨617096, by rfl⟩ : syracuseStep 822795 = 1234193) B1234193
theorem B822807 : Blo 822348 822807 := bstep (se 1 (by rfl) ⟨617105, by rfl⟩ : syracuseStep 822807 = 1234211) B1234211
theorem B822827 : Blo 822348 822827 := bstep (se 1 (by rfl) ⟨617120, by rfl⟩ : syracuseStep 822827 = 1234241) B1234241
theorem B822839 : Blo 822348 822839 := bstep (se 1 (by rfl) ⟨617129, by rfl⟩ : syracuseStep 822839 = 1234259) B1234259
theorem B822859 : Blo 822348 822859 := bstep (se 1 (by rfl) ⟨617144, by rfl⟩ : syracuseStep 822859 = 1234289) B1234289
theorem B822871 : Blo 822348 822871 := bstep (se 1 (by rfl) ⟨617153, by rfl⟩ : syracuseStep 822871 = 1234307) B1234307
theorem B822891 : Blo 822348 822891 := bstep (se 1 (by rfl) ⟨617168, by rfl⟩ : syracuseStep 822891 = 1234337) B1234337
theorem B822903 : Blo 822348 822903 := bstep (se 1 (by rfl) ⟨617177, by rfl⟩ : syracuseStep 822903 = 1234355) B1234355
theorem B822923 : Blo 822348 822923 := bstep (se 1 (by rfl) ⟨617192, by rfl⟩ : syracuseStep 822923 = 1234385) B1234385
theorem B822935 : Blo 822348 822935 := bstep (se 1 (by rfl) ⟨617201, by rfl⟩ : syracuseStep 822935 = 1234403) B1234403
theorem B822955 : Blo 822348 822955 := bstep (se 1 (by rfl) ⟨617216, by rfl⟩ : syracuseStep 822955 = 1234433) B1234433
theorem B822967 : Blo 822348 822967 := bstep (se 1 (by rfl) ⟨617225, by rfl⟩ : syracuseStep 822967 = 1234451) B1234451
theorem B822987 : Blo 822348 822987 := bstep (se 1 (by rfl) ⟨617240, by rfl⟩ : syracuseStep 822987 = 1234481) B1234481
theorem B822999 : Blo 822348 822999 := bstep (se 1 (by rfl) ⟨617249, by rfl⟩ : syracuseStep 822999 = 1234499) B1234499
theorem B823019 : Blo 822348 823019 := bstep (se 1 (by rfl) ⟨617264, by rfl⟩ : syracuseStep 823019 = 1234529) B1234529
theorem B823031 : Blo 822348 823031 := bstep (se 1 (by rfl) ⟨617273, by rfl⟩ : syracuseStep 823031 = 1234547) B1234547
theorem B823051 : Blo 822348 823051 := bstep (se 1 (by rfl) ⟨617288, by rfl⟩ : syracuseStep 823051 = 1234577) B1234577
theorem B823063 : Blo 822348 823063 := bstep (se 1 (by rfl) ⟨617297, by rfl⟩ : syracuseStep 823063 = 1234595) B1234595
theorem B823083 : Blo 822348 823083 := bstep (se 1 (by rfl) ⟨617312, by rfl⟩ : syracuseStep 823083 = 1234625) B1234625
theorem B823095 : Blo 822348 823095 := bstep (se 1 (by rfl) ⟨617321, by rfl⟩ : syracuseStep 823095 = 1234643) B1234643
theorem B823115 : Blo 822348 823115 := bstep (se 1 (by rfl) ⟨617336, by rfl⟩ : syracuseStep 823115 = 1234673) B1234673
theorem B823127 : Blo 822348 823127 := bstep (se 1 (by rfl) ⟨617345, by rfl⟩ : syracuseStep 823127 = 1234691) B1234691
theorem B823147 : Blo 822348 823147 := bstep (se 1 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 823147 = 1234721) B1234721
theorem B823159 : Blo 822348 823159 := bstep (se 1 (by rfl) ⟨617369, by rfl⟩ : syracuseStep 823159 = 1234739) B1234739
theorem B823179 : Blo 822348 823179 := bstep (se 1 (by rfl) ⟨617384, by rfl⟩ : syracuseStep 823179 = 1234769) B1234769
theorem B823191 : Blo 822348 823191 := bstep (se 1 (by rfl) ⟨617393, by rfl⟩ : syracuseStep 823191 = 1234787) B1234787
theorem B823211 : Blo 822348 823211 := bstep (se 1 (by rfl) ⟨617408, by rfl⟩ : syracuseStep 823211 = 1234817) B1234817
theorem B823223 : Blo 822348 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B823243 : Blo 822348 823243 := bstep (se 1 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 823243 = 1234865) B1234865
theorem B823255 : Blo 822348 823255 := bstep (se 1 (by rfl) ⟨617441, by rfl⟩ : syracuseStep 823255 = 1234883) B1234883
theorem B9408473 : Blo 822348 9408473 := bstep (se 2 (by rfl) ⟨3528177, by rfl⟩ : syracuseStep 9408473 = 7056355) B7056355
theorem B823275 : Blo 822348 823275 := bstep (se 1 (by rfl) ⟨617456, by rfl⟩ : syracuseStep 823275 = 1234913) B1234913
theorem B823287 : Blo 822348 823287 := bstep (se 1 (by rfl) ⟨617465, by rfl⟩ : syracuseStep 823287 = 1234931) B1234931
theorem B823307 : Blo 822348 823307 := bstep (se 1 (by rfl) ⟨617480, by rfl⟩ : syracuseStep 823307 = 1234961) B1234961
theorem B823319 : Blo 822348 823319 := bstep (se 1 (by rfl) ⟨617489, by rfl⟩ : syracuseStep 823319 = 1234979) B1234979
theorem B823339 : Blo 822348 823339 := bstep (se 1 (by rfl) ⟨617504, by rfl⟩ : syracuseStep 823339 = 1235009) B1235009
theorem B823351 : Blo 822348 823351 := bstep (se 1 (by rfl) ⟨617513, by rfl⟩ : syracuseStep 823351 = 1235027) B1235027
theorem B823371 : Blo 822348 823371 := bstep (se 1 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 823371 = 1235057) B1235057
theorem B823383 : Blo 822348 823383 := bstep (se 1 (by rfl) ⟨617537, by rfl⟩ : syracuseStep 823383 = 1235075) B1235075
theorem B4690021 : Blo 822348 4690021 := bstep (se 4 (by rfl) ⟨439689, by rfl⟩ : syracuseStep 4690021 = 879379) B879379
theorem B823403 : Blo 822348 823403 := bstep (se 1 (by rfl) ⟨617552, by rfl⟩ : syracuseStep 823403 = 1235105) B1235105
theorem B823415 : Blo 822348 823415 := bstep (se 1 (by rfl) ⟨617561, by rfl⟩ : syracuseStep 823415 = 1235123) B1235123
theorem B823435 : Blo 822348 823435 := bstep (se 1 (by rfl) ⟨617576, by rfl⟩ : syracuseStep 823435 = 1235153) B1235153
theorem B823447 : Blo 822348 823447 := bstep (se 1 (by rfl) ⟨617585, by rfl⟩ : syracuseStep 823447 = 1235171) B1235171
theorem B823467 : Blo 822348 823467 := bstep (se 1 (by rfl) ⟨617600, by rfl⟩ : syracuseStep 823467 = 1235201) B1235201
theorem B823479 : Blo 822348 823479 := bstep (se 1 (by rfl) ⟨617609, by rfl⟩ : syracuseStep 823479 = 1235219) B1235219
theorem B823499 : Blo 822348 823499 := bstep (se 1 (by rfl) ⟨617624, by rfl⟩ : syracuseStep 823499 = 1235249) B1235249
theorem B823511 : Blo 822348 823511 := bstep (se 1 (by rfl) ⟨617633, by rfl⟩ : syracuseStep 823511 = 1235267) B1235267
theorem B823531 : Blo 822348 823531 := bstep (se 1 (by rfl) ⟨617648, by rfl⟩ : syracuseStep 823531 = 1235297) B1235297
theorem B823543 : Blo 822348 823543 := bstep (se 1 (by rfl) ⟨617657, by rfl⟩ : syracuseStep 823543 = 1235315) B1235315
theorem B823563 : Blo 822348 823563 := bstep (se 1 (by rfl) ⟨617672, by rfl⟩ : syracuseStep 823563 = 1235345) B1235345
theorem B823575 : Blo 822348 823575 := bstep (se 1 (by rfl) ⟨617681, by rfl⟩ : syracuseStep 823575 = 1235363) B1235363
theorem B823595 : Blo 822348 823595 := bstep (se 1 (by rfl) ⟨617696, by rfl⟩ : syracuseStep 823595 = 1235393) B1235393
theorem B823607 : Blo 822348 823607 := bstep (se 1 (by rfl) ⟨617705, by rfl⟩ : syracuseStep 823607 = 1235411) B1235411
theorem B823627 : Blo 822348 823627 := bstep (se 1 (by rfl) ⟨617720, by rfl⟩ : syracuseStep 823627 = 1235441) B1235441
theorem B823639 : Blo 822348 823639 := bstep (se 1 (by rfl) ⟨617729, by rfl⟩ : syracuseStep 823639 = 1235459) B1235459
theorem B823659 : Blo 822348 823659 := bstep (se 1 (by rfl) ⟨617744, by rfl⟩ : syracuseStep 823659 = 1235489) B1235489
theorem B823671 : Blo 822348 823671 := bstep (se 1 (by rfl) ⟨617753, by rfl⟩ : syracuseStep 823671 = 1235507) B1235507
theorem B823691 : Blo 822348 823691 := bstep (se 1 (by rfl) ⟨617768, by rfl⟩ : syracuseStep 823691 = 1235537) B1235537
theorem B823703 : Blo 822348 823703 := bstep (se 1 (by rfl) ⟨617777, by rfl⟩ : syracuseStep 823703 = 1235555) B1235555
theorem B823723 : Blo 822348 823723 := bstep (se 1 (by rfl) ⟨617792, by rfl⟩ : syracuseStep 823723 = 1235585) B1235585
theorem B823735 : Blo 822348 823735 := bstep (se 1 (by rfl) ⟨617801, by rfl⟩ : syracuseStep 823735 = 1235603) B1235603
theorem B823755 : Blo 822348 823755 := bstep (se 1 (by rfl) ⟨617816, by rfl⟩ : syracuseStep 823755 = 1235633) B1235633
theorem B823767 : Blo 822348 823767 := bstep (se 1 (by rfl) ⟨617825, by rfl⟩ : syracuseStep 823767 = 1235651) B1235651
theorem B823787 : Blo 822348 823787 := bstep (se 1 (by rfl) ⟨617840, by rfl⟩ : syracuseStep 823787 = 1235681) B1235681
theorem B823799 : Blo 822348 823799 := bstep (se 1 (by rfl) ⟨617849, by rfl⟩ : syracuseStep 823799 = 1235699) B1235699
theorem B823819 : Blo 822348 823819 := bstep (se 1 (by rfl) ⟨617864, by rfl⟩ : syracuseStep 823819 = 1235729) B1235729
theorem B823831 : Blo 822348 823831 := bstep (se 1 (by rfl) ⟨617873, by rfl⟩ : syracuseStep 823831 = 1235747) B1235747
theorem B823851 : Blo 822348 823851 := bstep (se 1 (by rfl) ⟨617888, by rfl⟩ : syracuseStep 823851 = 1235777) B1235777
theorem B823863 : Blo 822348 823863 := bstep (se 1 (by rfl) ⟨617897, by rfl⟩ : syracuseStep 823863 = 1235795) B1235795
theorem B823883 : Blo 822348 823883 := bstep (se 1 (by rfl) ⟨617912, by rfl⟩ : syracuseStep 823883 = 1235825) B1235825
theorem B823895 : Blo 822348 823895 := bstep (se 1 (by rfl) ⟨617921, by rfl⟩ : syracuseStep 823895 = 1235843) B1235843
theorem B7934557 : Blo 822348 7934557 := bstep (se 3 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 7934557 = 2975459) B2975459
theorem B823915 : Blo 822348 823915 := bstep (se 1 (by rfl) ⟨617936, by rfl⟩ : syracuseStep 823915 = 1235873) B1235873
theorem B823927 : Blo 822348 823927 := bstep (se 1 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 823927 = 1235891) B1235891
theorem B823947 : Blo 822348 823947 := bstep (se 1 (by rfl) ⟨617960, by rfl⟩ : syracuseStep 823947 = 1235921) B1235921
theorem B823959 : Blo 822348 823959 := bstep (se 1 (by rfl) ⟨617969, by rfl⟩ : syracuseStep 823959 = 1235939) B1235939
theorem B823979 : Blo 822348 823979 := bstep (se 1 (by rfl) ⟨617984, by rfl⟩ : syracuseStep 823979 = 1235969) B1235969
theorem B823991 : Blo 822348 823991 := bstep (se 1 (by rfl) ⟨617993, by rfl⟩ : syracuseStep 823991 = 1235987) B1235987
theorem B3379915 : Blo 822348 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B824011 : Blo 822348 824011 := bstep (se 1 (by rfl) ⟨618008, by rfl⟩ : syracuseStep 824011 = 1236017) B1236017
theorem B824023 : Blo 822348 824023 := bstep (se 1 (by rfl) ⟨618017, by rfl⟩ : syracuseStep 824023 = 1236035) B1236035
theorem B824043 : Blo 822348 824043 := bstep (se 1 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 824043 = 1236065) B1236065
theorem B824055 : Blo 822348 824055 := bstep (se 1 (by rfl) ⟨618041, by rfl⟩ : syracuseStep 824055 = 1236083) B1236083
theorem B824075 : Blo 822348 824075 := bstep (se 1 (by rfl) ⟨618056, by rfl⟩ : syracuseStep 824075 = 1236113) B1236113
theorem B824087 : Blo 822348 824087 := bstep (se 1 (by rfl) ⟨618065, by rfl⟩ : syracuseStep 824087 = 1236131) B1236131
theorem B824107 : Blo 822348 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B824119 : Blo 822348 824119 := bstep (se 1 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 824119 = 1236179) B1236179
theorem B824139 : Blo 822348 824139 := bstep (se 1 (by rfl) ⟨618104, by rfl⟩ : syracuseStep 824139 = 1236209) B1236209
theorem B824151 : Blo 822348 824151 := bstep (se 1 (by rfl) ⟨618113, by rfl⟩ : syracuseStep 824151 = 1236227) B1236227
theorem B824171 : Blo 822348 824171 := bstep (se 1 (by rfl) ⟨618128, by rfl⟩ : syracuseStep 824171 = 1236257) B1236257
theorem B824183 : Blo 822348 824183 := bstep (se 1 (by rfl) ⟨618137, by rfl⟩ : syracuseStep 824183 = 1236275) B1236275
theorem B988043 : Blo 822348 988043 := bstep (se 1 (by rfl) ⟨741032, by rfl⟩ : syracuseStep 988043 = 1482065) B1482065
theorem B824203 : Blo 822348 824203 := bstep (se 1 (by rfl) ⟨618152, by rfl⟩ : syracuseStep 824203 = 1236305) B1236305
theorem B824215 : Blo 822348 824215 := bstep (se 1 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 824215 = 1236323) B1236323
theorem B824235 : Blo 822348 824235 := bstep (se 1 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 824235 = 1236353) B1236353
theorem B3969971 : Blo 822348 3969971 := bstep (se 1 (by rfl) ⟨2977478, by rfl⟩ : syracuseStep 3969971 = 5954957) B5954957
theorem B824247 : Blo 822348 824247 := bstep (se 1 (by rfl) ⟨618185, by rfl⟩ : syracuseStep 824247 = 1236371) B1236371
theorem B824267 : Blo 822348 824267 := bstep (se 1 (by rfl) ⟨618200, by rfl⟩ : syracuseStep 824267 = 1236401) B1236401
theorem B824279 : Blo 822348 824279 := bstep (se 1 (by rfl) ⟨618209, by rfl⟩ : syracuseStep 824279 = 1236419) B1236419
theorem B824299 : Blo 822348 824299 := bstep (se 1 (by rfl) ⟨618224, by rfl⟩ : syracuseStep 824299 = 1236449) B1236449
theorem B824311 : Blo 822348 824311 := bstep (se 1 (by rfl) ⟨618233, by rfl⟩ : syracuseStep 824311 = 1236467) B1236467
theorem B824331 : Blo 822348 824331 := bstep (se 1 (by rfl) ⟨618248, by rfl⟩ : syracuseStep 824331 = 1236497) B1236497
theorem B5280785 : Blo 822348 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B824343 : Blo 822348 824343 := bstep (se 1 (by rfl) ⟨618257, by rfl⟩ : syracuseStep 824343 = 1236515) B1236515
theorem B824363 : Blo 822348 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B824375 : Blo 822348 824375 := bstep (se 1 (by rfl) ⟨618281, by rfl⟩ : syracuseStep 824375 = 1236563) B1236563
theorem B824395 : Blo 822348 824395 := bstep (se 1 (by rfl) ⟨618296, by rfl⟩ : syracuseStep 824395 = 1236593) B1236593
theorem B824407 : Blo 822348 824407 := bstep (se 1 (by rfl) ⟨618305, by rfl⟩ : syracuseStep 824407 = 1236611) B1236611
theorem B7050341 : Blo 822348 7050341 := bstep (se 4 (by rfl) ⟨660969, by rfl⟩ : syracuseStep 7050341 = 1321939) B1321939
theorem B824427 : Blo 822348 824427 := bstep (se 1 (by rfl) ⟨618320, by rfl⟩ : syracuseStep 824427 = 1236641) B1236641
theorem B824439 : Blo 822348 824439 := bstep (se 1 (by rfl) ⟨618329, by rfl⟩ : syracuseStep 824439 = 1236659) B1236659
theorem B5018755 : Blo 822348 5018755 := bstep (se 1 (by rfl) ⟨3764066, by rfl⟩ : syracuseStep 5018755 = 7528133) B7528133
theorem B824459 : Blo 822348 824459 := bstep (se 1 (by rfl) ⟨618344, by rfl⟩ : syracuseStep 824459 = 1236689) B1236689
theorem B824471 : Blo 822348 824471 := bstep (se 1 (by rfl) ⟨618353, by rfl⟩ : syracuseStep 824471 = 1236707) B1236707
theorem B824491 : Blo 822348 824491 := bstep (se 1 (by rfl) ⟨618368, by rfl⟩ : syracuseStep 824491 = 1236737) B1236737
theorem B824503 : Blo 822348 824503 := bstep (se 1 (by rfl) ⟨618377, by rfl⟩ : syracuseStep 824503 = 1236755) B1236755
theorem B824523 : Blo 822348 824523 := bstep (se 1 (by rfl) ⟨618392, by rfl⟩ : syracuseStep 824523 = 1236785) B1236785
theorem B824535 : Blo 822348 824535 := bstep (se 1 (by rfl) ⟨618401, by rfl⟩ : syracuseStep 824535 = 1236803) B1236803
theorem B824555 : Blo 822348 824555 := bstep (se 1 (by rfl) ⟨618416, by rfl⟩ : syracuseStep 824555 = 1236833) B1236833
theorem B824567 : Blo 822348 824567 := bstep (se 1 (by rfl) ⟨618425, by rfl⟩ : syracuseStep 824567 = 1236851) B1236851
theorem B824587 : Blo 822348 824587 := bstep (se 1 (by rfl) ⟨618440, by rfl⟩ : syracuseStep 824587 = 1236881) B1236881
theorem B824599 : Blo 822348 824599 := bstep (se 1 (by rfl) ⟨618449, by rfl⟩ : syracuseStep 824599 = 1236899) B1236899
theorem B824619 : Blo 822348 824619 := bstep (se 1 (by rfl) ⟨618464, by rfl⟩ : syracuseStep 824619 = 1236929) B1236929
theorem B824631 : Blo 822348 824631 := bstep (se 1 (by rfl) ⟨618473, by rfl⟩ : syracuseStep 824631 = 1236947) B1236947
theorem B824651 : Blo 822348 824651 := bstep (se 1 (by rfl) ⟨618488, by rfl⟩ : syracuseStep 824651 = 1236977) B1236977
theorem B824663 : Blo 822348 824663 := bstep (se 1 (by rfl) ⟨618497, by rfl⟩ : syracuseStep 824663 = 1236995) B1236995
theorem B824683 : Blo 822348 824683 := bstep (se 1 (by rfl) ⟨618512, by rfl⟩ : syracuseStep 824683 = 1237025) B1237025
theorem B824695 : Blo 822348 824695 := bstep (se 1 (by rfl) ⟨618521, by rfl⟩ : syracuseStep 824695 = 1237043) B1237043
theorem B824715 : Blo 822348 824715 := bstep (se 1 (by rfl) ⟨618536, by rfl⟩ : syracuseStep 824715 = 1237073) B1237073
theorem B824727 : Blo 822348 824727 := bstep (se 1 (by rfl) ⟨618545, by rfl⟩ : syracuseStep 824727 = 1237091) B1237091
theorem B824747 : Blo 822348 824747 := bstep (se 1 (by rfl) ⟨618560, by rfl⟩ : syracuseStep 824747 = 1237121) B1237121
theorem B824759 : Blo 822348 824759 := bstep (se 1 (by rfl) ⟨618569, by rfl⟩ : syracuseStep 824759 = 1237139) B1237139
theorem B824779 : Blo 822348 824779 := bstep (se 1 (by rfl) ⟨618584, by rfl⟩ : syracuseStep 824779 = 1237169) B1237169
theorem B824791 : Blo 822348 824791 := bstep (se 1 (by rfl) ⟨618593, by rfl⟩ : syracuseStep 824791 = 1237187) B1237187
theorem B5019097 : Blo 822348 5019097 := bstep (se 2 (by rfl) ⟨1882161, by rfl⟩ : syracuseStep 5019097 = 3764323) B3764323
theorem B824811 : Blo 822348 824811 := bstep (se 1 (by rfl) ⟨618608, by rfl⟩ : syracuseStep 824811 = 1237217) B1237217
theorem B824823 : Blo 822348 824823 := bstep (se 1 (by rfl) ⟨618617, by rfl⟩ : syracuseStep 824823 = 1237235) B1237235
theorem B824843 : Blo 822348 824843 := bstep (se 1 (by rfl) ⟨618632, by rfl⟩ : syracuseStep 824843 = 1237265) B1237265
theorem B824855 : Blo 822348 824855 := bstep (se 1 (by rfl) ⟨618641, by rfl⟩ : syracuseStep 824855 = 1237283) B1237283
theorem B824875 : Blo 822348 824875 := bstep (se 1 (by rfl) ⟨618656, by rfl⟩ : syracuseStep 824875 = 1237313) B1237313
theorem B824887 : Blo 822348 824887 := bstep (se 1 (by rfl) ⟨618665, by rfl⟩ : syracuseStep 824887 = 1237331) B1237331
theorem B824907 : Blo 822348 824907 := bstep (se 1 (by rfl) ⟨618680, by rfl⟩ : syracuseStep 824907 = 1237361) B1237361
theorem B824919 : Blo 822348 824919 := bstep (se 1 (by rfl) ⟨618689, by rfl⟩ : syracuseStep 824919 = 1237379) B1237379
theorem B824939 : Blo 822348 824939 := bstep (se 1 (by rfl) ⟨618704, by rfl⟩ : syracuseStep 824939 = 1237409) B1237409
theorem B824951 : Blo 822348 824951 := bstep (se 1 (by rfl) ⟨618713, by rfl⟩ : syracuseStep 824951 = 1237427) B1237427
theorem B824971 : Blo 822348 824971 := bstep (se 1 (by rfl) ⟨618728, by rfl⟩ : syracuseStep 824971 = 1237457) B1237457
theorem B824983 : Blo 822348 824983 := bstep (se 1 (by rfl) ⟨618737, by rfl⟩ : syracuseStep 824983 = 1237475) B1237475
theorem B825003 : Blo 822348 825003 := bstep (se 1 (by rfl) ⟨618752, by rfl⟩ : syracuseStep 825003 = 1237505) B1237505
theorem B825015 : Blo 822348 825015 := bstep (se 1 (by rfl) ⟨618761, by rfl⟩ : syracuseStep 825015 = 1237523) B1237523
theorem B825035 : Blo 822348 825035 := bstep (se 1 (by rfl) ⟨618776, by rfl⟩ : syracuseStep 825035 = 1237553) B1237553
theorem B825047 : Blo 822348 825047 := bstep (se 1 (by rfl) ⟨618785, by rfl⟩ : syracuseStep 825047 = 1237571) B1237571
theorem B825067 : Blo 822348 825067 := bstep (se 1 (by rfl) ⟨618800, by rfl⟩ : syracuseStep 825067 = 1237601) B1237601
theorem B825079 : Blo 822348 825079 := bstep (se 1 (by rfl) ⟨618809, by rfl⟩ : syracuseStep 825079 = 1237619) B1237619
theorem B825099 : Blo 822348 825099 := bstep (se 1 (by rfl) ⟨618824, by rfl⟩ : syracuseStep 825099 = 1237649) B1237649
theorem B825111 : Blo 822348 825111 := bstep (se 1 (by rfl) ⟨618833, by rfl⟩ : syracuseStep 825111 = 1237667) B1237667
theorem B825131 : Blo 822348 825131 := bstep (se 1 (by rfl) ⟨618848, by rfl⟩ : syracuseStep 825131 = 1237697) B1237697
theorem B825143 : Blo 822348 825143 := bstep (se 1 (by rfl) ⟨618857, by rfl⟩ : syracuseStep 825143 = 1237715) B1237715
theorem B825163 : Blo 822348 825163 := bstep (se 1 (by rfl) ⟨618872, by rfl⟩ : syracuseStep 825163 = 1237745) B1237745
theorem B825175 : Blo 822348 825175 := bstep (se 1 (by rfl) ⟨618881, by rfl⟩ : syracuseStep 825175 = 1237763) B1237763
theorem B825195 : Blo 822348 825195 := bstep (se 1 (by rfl) ⟨618896, by rfl⟩ : syracuseStep 825195 = 1237793) B1237793
theorem B825207 : Blo 822348 825207 := bstep (se 1 (by rfl) ⟨618905, by rfl⟩ : syracuseStep 825207 = 1237811) B1237811
theorem B825227 : Blo 822348 825227 := bstep (se 1 (by rfl) ⟨618920, by rfl⟩ : syracuseStep 825227 = 1237841) B1237841
theorem B825239 : Blo 822348 825239 := bstep (se 1 (by rfl) ⟨618929, by rfl⟩ : syracuseStep 825239 = 1237859) B1237859
theorem B825259 : Blo 822348 825259 := bstep (se 1 (by rfl) ⟨618944, by rfl⟩ : syracuseStep 825259 = 1237889) B1237889
theorem B825271 : Blo 822348 825271 := bstep (se 1 (by rfl) ⟨618953, by rfl⟩ : syracuseStep 825271 = 1237907) B1237907
theorem B825291 : Blo 822348 825291 := bstep (se 1 (by rfl) ⟨618968, by rfl⟩ : syracuseStep 825291 = 1237937) B1237937
theorem B825303 : Blo 822348 825303 := bstep (se 1 (by rfl) ⟨618977, by rfl⟩ : syracuseStep 825303 = 1237955) B1237955
theorem B825323 : Blo 822348 825323 := bstep (se 1 (by rfl) ⟨618992, by rfl⟩ : syracuseStep 825323 = 1237985) B1237985
theorem B825335 : Blo 822348 825335 := bstep (se 1 (by rfl) ⟨619001, by rfl⟩ : syracuseStep 825335 = 1238003) B1238003
theorem B825355 : Blo 822348 825355 := bstep (se 1 (by rfl) ⟨619016, by rfl⟩ : syracuseStep 825355 = 1238033) B1238033
theorem B825367 : Blo 822348 825367 := bstep (se 1 (by rfl) ⟨619025, by rfl⟩ : syracuseStep 825367 = 1238051) B1238051
theorem B825387 : Blo 822348 825387 := bstep (se 1 (by rfl) ⟨619040, by rfl⟩ : syracuseStep 825387 = 1238081) B1238081
theorem B825399 : Blo 822348 825399 := bstep (se 1 (by rfl) ⟨619049, by rfl⟩ : syracuseStep 825399 = 1238099) B1238099
theorem B825419 : Blo 822348 825419 := bstep (se 1 (by rfl) ⟨619064, by rfl⟩ : syracuseStep 825419 = 1238129) B1238129
theorem B825431 : Blo 822348 825431 := bstep (se 1 (by rfl) ⟨619073, by rfl⟩ : syracuseStep 825431 = 1238147) B1238147
theorem B4167773 : Blo 822348 4167773 := bstep (se 3 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 4167773 = 1562915) B1562915
theorem B825451 : Blo 822348 825451 := bstep (se 1 (by rfl) ⟨619088, by rfl⟩ : syracuseStep 825451 = 1238177) B1238177
theorem B825463 : Blo 822348 825463 := bstep (se 1 (by rfl) ⟨619097, by rfl⟩ : syracuseStep 825463 = 1238195) B1238195
theorem B825483 : Blo 822348 825483 := bstep (se 1 (by rfl) ⟨619112, by rfl⟩ : syracuseStep 825483 = 1238225) B1238225
theorem B23730317 : Blo 822348 23730317 := bstep (se 3 (by rfl) ⟨4449434, by rfl⟩ : syracuseStep 23730317 = 8898869) B8898869
theorem B825495 : Blo 822348 825495 := bstep (se 1 (by rfl) ⟨619121, by rfl⟩ : syracuseStep 825495 = 1238243) B1238243
theorem B825515 : Blo 822348 825515 := bstep (se 1 (by rfl) ⟨619136, by rfl⟩ : syracuseStep 825515 = 1238273) B1238273
theorem B825527 : Blo 822348 825527 := bstep (se 1 (by rfl) ⟨619145, by rfl⟩ : syracuseStep 825527 = 1238291) B1238291
theorem B825547 : Blo 822348 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B825559 : Blo 822348 825559 := bstep (se 1 (by rfl) ⟨619169, by rfl⟩ : syracuseStep 825559 = 1238339) B1238339
theorem B1251545 : Blo 822348 1251545 := bstep (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) B938659
theorem B825579 : Blo 822348 825579 := bstep (se 1 (by rfl) ⟨619184, by rfl⟩ : syracuseStep 825579 = 1238369) B1238369
theorem B825591 : Blo 822348 825591 := bstep (se 1 (by rfl) ⟨619193, by rfl⟩ : syracuseStep 825591 = 1238387) B1238387
theorem B825611 : Blo 822348 825611 := bstep (se 1 (by rfl) ⟨619208, by rfl⟩ : syracuseStep 825611 = 1238417) B1238417
theorem B5937425 : Blo 822348 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B825623 : Blo 822348 825623 := bstep (se 1 (by rfl) ⟨619217, by rfl⟩ : syracuseStep 825623 = 1238435) B1238435
theorem B825643 : Blo 822348 825643 := bstep (se 1 (by rfl) ⟨619232, by rfl⟩ : syracuseStep 825643 = 1238465) B1238465
theorem B825655 : Blo 822348 825655 := bstep (se 1 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 825655 = 1238483) B1238483
theorem B825675 : Blo 822348 825675 := bstep (se 1 (by rfl) ⟨619256, by rfl⟩ : syracuseStep 825675 = 1238513) B1238513
theorem B825687 : Blo 822348 825687 := bstep (se 1 (by rfl) ⟨619265, by rfl⟩ : syracuseStep 825687 = 1238531) B1238531
theorem B825707 : Blo 822348 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B825719 : Blo 822348 825719 := bstep (se 1 (by rfl) ⟨619289, by rfl⟩ : syracuseStep 825719 = 1238579) B1238579
theorem B825739 : Blo 822348 825739 := bstep (se 1 (by rfl) ⟨619304, by rfl⟩ : syracuseStep 825739 = 1238609) B1238609
theorem B825751 : Blo 822348 825751 := bstep (se 1 (by rfl) ⟨619313, by rfl⟩ : syracuseStep 825751 = 1238627) B1238627
theorem B825771 : Blo 822348 825771 := bstep (se 1 (by rfl) ⟨619328, by rfl⟩ : syracuseStep 825771 = 1238657) B1238657
theorem B825783 : Blo 822348 825783 := bstep (se 1 (by rfl) ⟨619337, by rfl⟩ : syracuseStep 825783 = 1238675) B1238675
theorem B825803 : Blo 822348 825803 := bstep (se 1 (by rfl) ⟨619352, by rfl⟩ : syracuseStep 825803 = 1238705) B1238705
theorem B825815 : Blo 822348 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B825835 : Blo 822348 825835 := bstep (se 1 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 825835 = 1238753) B1238753
theorem B825847 : Blo 822348 825847 := bstep (se 1 (by rfl) ⟨619385, by rfl⟩ : syracuseStep 825847 = 1238771) B1238771
theorem B825867 : Blo 822348 825867 := bstep (se 1 (by rfl) ⟨619400, by rfl⟩ : syracuseStep 825867 = 1238801) B1238801
theorem B825879 : Blo 822348 825879 := bstep (se 1 (by rfl) ⟨619409, by rfl⟩ : syracuseStep 825879 = 1238819) B1238819
theorem B825899 : Blo 822348 825899 := bstep (se 1 (by rfl) ⟨619424, by rfl⟩ : syracuseStep 825899 = 1238849) B1238849
theorem B825911 : Blo 822348 825911 := bstep (se 1 (by rfl) ⟨619433, by rfl⟩ : syracuseStep 825911 = 1238867) B1238867
theorem B825931 : Blo 822348 825931 := bstep (se 1 (by rfl) ⟨619448, by rfl⟩ : syracuseStep 825931 = 1238897) B1238897
theorem B825943 : Blo 822348 825943 := bstep (se 1 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 825943 = 1238915) B1238915
theorem B825963 : Blo 822348 825963 := bstep (se 1 (by rfl) ⟨619472, by rfl⟩ : syracuseStep 825963 = 1238945) B1238945
theorem B825975 : Blo 822348 825975 := bstep (se 1 (by rfl) ⟨619481, by rfl⟩ : syracuseStep 825975 = 1238963) B1238963
theorem B825995 : Blo 822348 825995 := bstep (se 1 (by rfl) ⟨619496, by rfl⟩ : syracuseStep 825995 = 1238993) B1238993
theorem B826007 : Blo 822348 826007 := bstep (se 1 (by rfl) ⟨619505, by rfl⟩ : syracuseStep 826007 = 1239011) B1239011
theorem B826027 : Blo 822348 826027 := bstep (se 1 (by rfl) ⟨619520, by rfl⟩ : syracuseStep 826027 = 1239041) B1239041
theorem B826039 : Blo 822348 826039 := bstep (se 1 (by rfl) ⟨619529, by rfl⟩ : syracuseStep 826039 = 1239059) B1239059
theorem B826059 : Blo 822348 826059 := bstep (se 1 (by rfl) ⟨619544, by rfl⟩ : syracuseStep 826059 = 1239089) B1239089
theorem B7051981 : Blo 822348 7051981 := bstep (se 3 (by rfl) ⟨1322246, by rfl⟩ : syracuseStep 7051981 = 2644493) B2644493
theorem B826071 : Blo 822348 826071 := bstep (se 1 (by rfl) ⟨619553, by rfl⟩ : syracuseStep 826071 = 1239107) B1239107
theorem B826091 : Blo 822348 826091 := bstep (se 1 (by rfl) ⟨619568, by rfl⟩ : syracuseStep 826091 = 1239137) B1239137
theorem B826103 : Blo 822348 826103 := bstep (se 1 (by rfl) ⟨619577, by rfl⟩ : syracuseStep 826103 = 1239155) B1239155
theorem B826123 : Blo 822348 826123 := bstep (se 1 (by rfl) ⟨619592, by rfl⟩ : syracuseStep 826123 = 1239185) B1239185
theorem B826135 : Blo 822348 826135 := bstep (se 1 (by rfl) ⟨619601, by rfl⟩ : syracuseStep 826135 = 1239203) B1239203
theorem B826155 : Blo 822348 826155 := bstep (se 1 (by rfl) ⟨619616, by rfl⟩ : syracuseStep 826155 = 1239233) B1239233
theorem B826167 : Blo 822348 826167 := bstep (se 1 (by rfl) ⟨619625, by rfl⟩ : syracuseStep 826167 = 1239251) B1239251
theorem B826187 : Blo 822348 826187 := bstep (se 1 (by rfl) ⟨619640, by rfl⟩ : syracuseStep 826187 = 1239281) B1239281
theorem B826199 : Blo 822348 826199 := bstep (se 1 (by rfl) ⟨619649, by rfl⟩ : syracuseStep 826199 = 1239299) B1239299
theorem B826219 : Blo 822348 826219 := bstep (se 1 (by rfl) ⟨619664, by rfl⟩ : syracuseStep 826219 = 1239329) B1239329
theorem B826231 : Blo 822348 826231 := bstep (se 1 (by rfl) ⟨619673, by rfl⟩ : syracuseStep 826231 = 1239347) B1239347
theorem B826251 : Blo 822348 826251 := bstep (se 1 (by rfl) ⟨619688, by rfl⟩ : syracuseStep 826251 = 1239377) B1239377
theorem B826263 : Blo 822348 826263 := bstep (se 1 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 826263 = 1239395) B1239395
theorem B826283 : Blo 822348 826283 := bstep (se 1 (by rfl) ⟨619712, by rfl⟩ : syracuseStep 826283 = 1239425) B1239425
theorem B826295 : Blo 822348 826295 := bstep (se 1 (by rfl) ⟨619721, by rfl⟩ : syracuseStep 826295 = 1239443) B1239443
theorem B826315 : Blo 822348 826315 := bstep (se 1 (by rfl) ⟨619736, by rfl⟩ : syracuseStep 826315 = 1239473) B1239473
theorem B826327 : Blo 822348 826327 := bstep (se 1 (by rfl) ⟨619745, by rfl⟩ : syracuseStep 826327 = 1239491) B1239491
theorem B826347 : Blo 822348 826347 := bstep (se 1 (by rfl) ⟨619760, by rfl⟩ : syracuseStep 826347 = 1239521) B1239521
theorem B3513689 : Blo 822348 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B990667 : Blo 822348 990667 := bstep (se 1 (by rfl) ⟨743000, by rfl⟩ : syracuseStep 990667 = 1486001) B1486001
theorem B925195 : Blo 822348 925195 := bstep (se 1 (by rfl) ⟨693896, by rfl⟩ : syracuseStep 925195 = 1387793) B1387793
theorem B925303 : Blo 822348 925303 := bstep (se 1 (by rfl) ⟨693977, by rfl⟩ : syracuseStep 925303 = 1387955) B1387955
theorem B925483 : Blo 822348 925483 := bstep (se 1 (by rfl) ⟨694112, by rfl⟩ : syracuseStep 925483 = 1388225) B1388225
theorem B925591 : Blo 822348 925591 := bstep (se 1 (by rfl) ⟨694193, by rfl⟩ : syracuseStep 925591 = 1388387) B1388387
theorem B6692813 : Blo 822348 6692813 := bstep (se 3 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 6692813 = 2509805) B2509805
theorem B7053317 : Blo 822348 7053317 := bstep (se 4 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 7053317 = 1322497) B1322497
theorem B1253399 : Blo 822348 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B925771 : Blo 822348 925771 := bstep (se 1 (by rfl) ⟨694328, by rfl⟩ : syracuseStep 925771 = 1388657) B1388657
theorem B4169879 : Blo 822348 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B925879 : Blo 822348 925879 := bstep (se 1 (by rfl) ⟨694409, by rfl⟩ : syracuseStep 925879 = 1388819) B1388819
theorem B926059 : Blo 822348 926059 := bstep (se 1 (by rfl) ⟨694544, by rfl⟩ : syracuseStep 926059 = 1389089) B1389089
theorem B893387 : Blo 822348 893387 := bstep (se 1 (by rfl) ⟨670040, by rfl⟩ : syracuseStep 893387 = 1340081) B1340081
theorem B926167 : Blo 822348 926167 := bstep (se 1 (by rfl) ⟨694625, by rfl⟩ : syracuseStep 926167 = 1389251) B1389251
theorem B926347 : Blo 822348 926347 := bstep (se 1 (by rfl) ⟨694760, by rfl⟩ : syracuseStep 926347 = 1389521) B1389521
theorem B1319627 : Blo 822348 1319627 := bstep (se 1 (by rfl) ⟨989720, by rfl⟩ : syracuseStep 1319627 = 1979441) B1979441
theorem B926455 : Blo 822348 926455 := bstep (se 1 (by rfl) ⟨694841, by rfl⟩ : syracuseStep 926455 = 1389683) B1389683
theorem B926635 : Blo 822348 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B3515329 : Blo 822348 3515329 := bstep (se 2 (by rfl) ⟨1318248, by rfl⟩ : syracuseStep 3515329 = 2636497) B2636497
theorem B926743 : Blo 822348 926743 := bstep (se 1 (by rfl) ⟨695057, by rfl⟩ : syracuseStep 926743 = 1390115) B1390115
theorem B22848581 : Blo 822348 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B23733323 : Blo 822348 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B926923 : Blo 822348 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B5940485 : Blo 822348 5940485 := bstep (se 4 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 5940485 = 1113841) B1113841
theorem B927031 : Blo 822348 927031 := bstep (se 1 (by rfl) ⟨695273, by rfl⟩ : syracuseStep 927031 = 1390547) B1390547
theorem B5285195 : Blo 822348 5285195 := bstep (se 1 (by rfl) ⟨3963896, by rfl⟩ : syracuseStep 5285195 = 7927793) B7927793
theorem B1484119 : Blo 822348 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B927211 : Blo 822348 927211 := bstep (se 1 (by rfl) ⟨695408, by rfl⟩ : syracuseStep 927211 = 1390817) B1390817
theorem B927319 : Blo 822348 927319 := bstep (se 1 (by rfl) ⟨695489, by rfl⟩ : syracuseStep 927319 = 1390979) B1390979
theorem B927499 : Blo 822348 927499 := bstep (se 1 (by rfl) ⟨695624, by rfl⟩ : syracuseStep 927499 = 1391249) B1391249
theorem B4695853 : Blo 822348 4695853 := bstep (se 3 (by rfl) ⟨880472, by rfl⟩ : syracuseStep 4695853 = 1760945) B1760945
theorem B11904833 : Blo 822348 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B927607 : Blo 822348 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B6334469 : Blo 822348 6334469 := bstep (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) B1187713
theorem B927787 : Blo 822348 927787 := bstep (se 1 (by rfl) ⟨695840, by rfl⟩ : syracuseStep 927787 = 1391681) B1391681
theorem B1484875 : Blo 822348 1484875 := bstep (se 1 (by rfl) ⟨1113656, by rfl⟩ : syracuseStep 1484875 = 2227313) B2227313
theorem B1976471 : Blo 822348 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B1878167 : Blo 822348 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B927895 : Blo 822348 927895 := bstep (se 1 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 927895 = 1391843) B1391843
theorem B928075 : Blo 822348 928075 := bstep (se 1 (by rfl) ⟨696056, by rfl⟩ : syracuseStep 928075 = 1392113) B1392113
theorem B3516817 : Blo 822348 3516817 := bstep (se 2 (by rfl) ⟨1318806, by rfl⟩ : syracuseStep 3516817 = 2637613) B2637613
theorem B2009495 : Blo 822348 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B3123629 : Blo 822348 3123629 := bstep (se 3 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 3123629 = 1171361) B1171361
theorem B928183 : Blo 822348 928183 := bstep (se 1 (by rfl) ⟨696137, by rfl⟩ : syracuseStep 928183 = 1392275) B1392275
theorem B2501057 : Blo 822348 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B1583563 : Blo 822348 1583563 := bstep (se 1 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 1583563 = 2375345) B2375345
theorem B928363 : Blo 822348 928363 := bstep (se 1 (by rfl) ⟨696272, by rfl⟩ : syracuseStep 928363 = 1392545) B1392545
theorem B1256075 : Blo 822348 1256075 := bstep (se 1 (by rfl) ⟨942056, by rfl⟩ : syracuseStep 1256075 = 1884113) B1884113
theorem B928471 : Blo 822348 928471 := bstep (se 1 (by rfl) ⟨696353, by rfl⟩ : syracuseStep 928471 = 1392707) B1392707
theorem B928651 : Blo 822348 928651 := bstep (se 1 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 928651 = 1392977) B1392977
theorem B928759 : Blo 822348 928759 := bstep (se 1 (by rfl) ⟨696569, by rfl⟩ : syracuseStep 928759 = 1393139) B1393139
theorem B1485913 : Blo 822348 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B928939 : Blo 822348 928939 := bstep (se 1 (by rfl) ⟨696704, by rfl⟩ : syracuseStep 928939 = 1393409) B1393409
theorem B3124403 : Blo 822348 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B929047 : Blo 822348 929047 := bstep (se 1 (by rfl) ⟨696785, by rfl⟩ : syracuseStep 929047 = 1393571) B1393571
theorem B4238743 : Blo 822348 4238743 := bstep (se 1 (by rfl) ⟨3179057, by rfl⟩ : syracuseStep 4238743 = 6358115) B6358115
theorem B929227 : Blo 822348 929227 := bstep (se 1 (by rfl) ⟨696920, by rfl⟩ : syracuseStep 929227 = 1393841) B1393841
theorem B929335 : Blo 822348 929335 := bstep (se 1 (by rfl) ⟨697001, by rfl⟩ : syracuseStep 929335 = 1394003) B1394003
theorem B4173443 : Blo 822348 4173443 := bstep (se 1 (by rfl) ⟨3130082, by rfl⟩ : syracuseStep 4173443 = 6260165) B6260165
theorem B1388171 : Blo 822348 1388171 := bstep (se 1 (by rfl) ⟨1041128, by rfl⟩ : syracuseStep 1388171 = 2082257) B2082257
theorem B929515 : Blo 822348 929515 := bstep (se 1 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 929515 = 1394273) B1394273
theorem B1388299 : Blo 822348 1388299 := bstep (se 1 (by rfl) ⟨1041224, by rfl⟩ : syracuseStep 1388299 = 2082449) B2082449
theorem B929623 : Blo 822348 929623 := bstep (se 1 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 929623 = 1394435) B1394435
theorem B1486721 : Blo 822348 1486721 := bstep (se 2 (by rfl) ⟨557520, by rfl⟩ : syracuseStep 1486721 = 1115041) B1115041
theorem B1388441 : Blo 822348 1388441 := bstep (se 2 (by rfl) ⟨520665, by rfl⟩ : syracuseStep 1388441 = 1041331) B1041331
theorem B1388569 : Blo 822348 1388569 := bstep (se 2 (by rfl) ⟨520713, by rfl⟩ : syracuseStep 1388569 = 1041427) B1041427
theorem B1782131 : Blo 822348 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1978931 : Blo 822348 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B6107723 : Blo 822348 6107723 := bstep (se 1 (by rfl) ⟨4580792, by rfl⟩ : syracuseStep 6107723 = 9161585) B9161585
theorem B1389143 : Blo 822348 1389143 := bstep (se 1 (by rfl) ⟨1041857, by rfl⟩ : syracuseStep 1389143 = 2083715) B2083715
theorem B3125891 : Blo 822348 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B2110103 : Blo 822348 2110103 := bstep (se 1 (by rfl) ⟨1582577, by rfl⟩ : syracuseStep 2110103 = 3165155) B3165155
theorem B6337201 : Blo 822348 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B1389271 : Blo 822348 1389271 := bstep (se 1 (by rfl) ⟨1041953, by rfl⟩ : syracuseStep 1389271 = 2083907) B2083907
theorem B1881047 : Blo 822348 1881047 := bstep (se 1 (by rfl) ⟨1410785, by rfl⟩ : syracuseStep 1881047 = 2821571) B2821571
theorem B3126347 : Blo 822348 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B3126545 : Blo 822348 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B1389899 : Blo 822348 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B14071157 : Blo 822348 14071157 := bstep (se 5 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 14071157 = 1319171) B1319171
theorem B3519875 : Blo 822348 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B1488307 : Blo 822348 1488307 := bstep (se 1 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 1488307 = 2232461) B2232461
theorem B1390027 : Blo 822348 1390027 := bstep (se 1 (by rfl) ⟨1042520, by rfl⟩ : syracuseStep 1390027 = 2085041) B2085041
theorem B1390169 : Blo 822348 1390169 := bstep (se 2 (by rfl) ⟨521313, by rfl⟩ : syracuseStep 1390169 = 1042627) B1042627
theorem B1980055 : Blo 822348 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B1390297 : Blo 822348 1390297 := bstep (se 2 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 1390297 = 1042723) B1042723
theorem B1128217 : Blo 822348 1128217 := bstep (se 2 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 1128217 = 846163) B846163
theorem B1587073 : Blo 822348 1587073 := bstep (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) B1190305
theorem B3127319 : Blo 822348 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B3127517 : Blo 822348 3127517 := bstep (se 3 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 3127517 = 1172819) B1172819
theorem B1390871 : Blo 822348 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B1390999 : Blo 822348 1390999 := bstep (se 1 (by rfl) ⟨1043249, by rfl⟩ : syracuseStep 1390999 = 2086499) B2086499
theorem B2406935 : Blo 822348 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B2964275 : Blo 822348 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1850291 : Blo 822348 1850291 := bstep (se 1 (by rfl) ⟨1387718, by rfl⟩ : syracuseStep 1850291 = 2775437) B2775437
theorem B2341811 : Blo 822348 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B1850327 : Blo 822348 1850327 := bstep (se 1 (by rfl) ⟨1387745, by rfl⟩ : syracuseStep 1850327 = 2775491) B2775491
theorem B1391627 : Blo 822348 1391627 := bstep (se 1 (by rfl) ⟨1043720, by rfl⟩ : syracuseStep 1391627 = 2087441) B2087441
theorem B2505779 : Blo 822348 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1850507 : Blo 822348 1850507 := bstep (se 1 (by rfl) ⟨1387880, by rfl⟩ : syracuseStep 1850507 = 2775761) B2775761
theorem B1391755 : Blo 822348 1391755 := bstep (se 1 (by rfl) ⟨1043816, by rfl⟩ : syracuseStep 1391755 = 2087633) B2087633
theorem B1850561 : Blo 822348 1850561 := bstep (se 2 (by rfl) ⟨693960, by rfl⟩ : syracuseStep 1850561 = 1387921) B1387921
theorem B4177169 : Blo 822348 4177169 := bstep (se 2 (by rfl) ⟨1566438, by rfl⟩ : syracuseStep 4177169 = 3132877) B3132877
theorem B1391897 : Blo 822348 1391897 := bstep (se 2 (by rfl) ⟨521961, by rfl⟩ : syracuseStep 1391897 = 1043923) B1043923
theorem B2342209 : Blo 822348 2342209 := bstep (se 2 (by rfl) ⟨878328, by rfl⟩ : syracuseStep 2342209 = 1756657) B1756657
theorem B1588567 : Blo 822348 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B1850777 : Blo 822348 1850777 := bstep (se 2 (by rfl) ⟨694041, by rfl⟩ : syracuseStep 1850777 = 1388083) B1388083
theorem B1392025 : Blo 822348 1392025 := bstep (se 2 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 1392025 = 1044019) B1044019
theorem B4177331 : Blo 822348 4177331 := bstep (se 1 (by rfl) ⟨3132998, by rfl⟩ : syracuseStep 4177331 = 6265997) B6265997
theorem B1850867 : Blo 822348 1850867 := bstep (se 1 (by rfl) ⟨1388150, by rfl⟩ : syracuseStep 1850867 = 2776301) B2776301
theorem B15810065 : Blo 822348 15810065 := bstep (se 2 (by rfl) ⟨5928774, by rfl⟩ : syracuseStep 15810065 = 11857549) B11857549
theorem B1850903 : Blo 822348 1850903 := bstep (se 1 (by rfl) ⟨1388177, by rfl⟩ : syracuseStep 1850903 = 2776355) B2776355
theorem B38125187 : Blo 822348 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B1851083 : Blo 822348 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B835307 : Blo 822348 835307 := bstep (se 1 (by rfl) ⟨626480, by rfl⟩ : syracuseStep 835307 = 1252961) B1252961
theorem B1851137 : Blo 822348 1851137 := bstep (se 2 (by rfl) ⟨694176, by rfl⟩ : syracuseStep 1851137 = 1388353) B1388353
theorem B1392599 : Blo 822348 1392599 := bstep (se 1 (by rfl) ⟨1044449, by rfl⟩ : syracuseStep 1392599 = 2088899) B2088899
theorem B1851353 : Blo 822348 1851353 := bstep (se 2 (by rfl) ⟨694257, by rfl⟩ : syracuseStep 1851353 = 1388515) B1388515
theorem B8044505 : Blo 822348 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B1851443 : Blo 822348 1851443 := bstep (se 1 (by rfl) ⟨1388582, by rfl⟩ : syracuseStep 1851443 = 2777165) B2777165
theorem B1851479 : Blo 822348 1851479 := bstep (se 1 (by rfl) ⟨1388609, by rfl⟩ : syracuseStep 1851479 = 2777219) B2777219
theorem B1392727 : Blo 822348 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B3129475 : Blo 822348 3129475 := bstep (se 1 (by rfl) ⟨2347106, by rfl⟩ : syracuseStep 3129475 = 4694213) B4694213
theorem B2113715 : Blo 822348 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B1851659 : Blo 822348 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B1851713 : Blo 822348 1851713 := bstep (se 2 (by rfl) ⟨694392, by rfl⟩ : syracuseStep 1851713 = 1388785) B1388785
theorem B3129779 : Blo 822348 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B4702643 : Blo 822348 4702643 := bstep (se 1 (by rfl) ⟨3526982, by rfl⟩ : syracuseStep 4702643 = 7053965) B7053965
theorem B836119 : Blo 822348 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B1851929 : Blo 822348 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B1852019 : Blo 822348 1852019 := bstep (se 1 (by rfl) ⟨1389014, by rfl⟩ : syracuseStep 1852019 = 2778029) B2778029
theorem B1852055 : Blo 822348 1852055 := bstep (se 1 (by rfl) ⟨1389041, by rfl⟩ : syracuseStep 1852055 = 2778083) B2778083
theorem B967339 : Blo 822348 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B1983179 : Blo 822348 1983179 := bstep (se 1 (by rfl) ⟨1487384, by rfl⟩ : syracuseStep 1983179 = 2974769) B2974769
theorem B1393355 : Blo 822348 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B2966233 : Blo 822348 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B1852235 : Blo 822348 1852235 := bstep (se 1 (by rfl) ⟨1389176, by rfl⟩ : syracuseStep 1852235 = 2778353) B2778353
theorem B1393483 : Blo 822348 1393483 := bstep (se 1 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 1393483 = 2090225) B2090225
theorem B1852289 : Blo 822348 1852289 := bstep (se 2 (by rfl) ⟨694608, by rfl⟩ : syracuseStep 1852289 = 1389217) B1389217
theorem B1393625 : Blo 822348 1393625 := bstep (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) B1045219
theorem B3130433 : Blo 822348 3130433 := bstep (se 2 (by rfl) ⟨1173912, by rfl⟩ : syracuseStep 3130433 = 2347825) B2347825
theorem B1852505 : Blo 822348 1852505 := bstep (se 2 (by rfl) ⟨694689, by rfl⟩ : syracuseStep 1852505 = 1389379) B1389379
theorem B1393753 : Blo 822348 1393753 := bstep (se 2 (by rfl) ⟨522657, by rfl⟩ : syracuseStep 1393753 = 1045315) B1045315
theorem B2671795 : Blo 822348 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1852595 : Blo 822348 1852595 := bstep (se 1 (by rfl) ⟨1389446, by rfl⟩ : syracuseStep 1852595 = 2778893) B2778893
theorem B1852631 : Blo 822348 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B4179275 : Blo 822348 4179275 := bstep (se 1 (by rfl) ⟨3134456, by rfl⟩ : syracuseStep 4179275 = 6268913) B6268913
theorem B1852811 : Blo 822348 1852811 := bstep (se 1 (by rfl) ⟨1389608, by rfl⟩ : syracuseStep 1852811 = 2779217) B2779217
theorem B1852865 : Blo 822348 1852865 := bstep (se 2 (by rfl) ⟨694824, by rfl⟩ : syracuseStep 1852865 = 1389649) B1389649
theorem B3524147 : Blo 822348 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B1394327 : Blo 822348 1394327 := bstep (se 1 (by rfl) ⟨1045745, by rfl⟩ : syracuseStep 1394327 = 2091491) B2091491
theorem B1853081 : Blo 822348 1853081 := bstep (se 2 (by rfl) ⟨694905, by rfl⟩ : syracuseStep 1853081 = 1389811) B1389811
theorem B6670001 : Blo 822348 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B837335 : Blo 822348 837335 := bstep (se 1 (by rfl) ⟨628001, by rfl⟩ : syracuseStep 837335 = 1256003) B1256003
theorem B1853171 : Blo 822348 1853171 := bstep (se 1 (by rfl) ⟨1389878, by rfl⟩ : syracuseStep 1853171 = 2779757) B2779757
theorem B837367 : Blo 822348 837367 := bstep (se 1 (by rfl) ⟨628025, by rfl⟩ : syracuseStep 837367 = 1256051) B1256051
theorem B2344727 : Blo 822348 2344727 := bstep (se 1 (by rfl) ⟨1758545, by rfl⟩ : syracuseStep 2344727 = 3517091) B3517091
theorem B1853207 : Blo 822348 1853207 := bstep (se 1 (by rfl) ⟨1389905, by rfl⟩ : syracuseStep 1853207 = 2779811) B2779811
theorem B1394455 : Blo 822348 1394455 := bstep (se 1 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 1394455 = 2091683) B2091683
theorem B2082611 : Blo 822348 2082611 := bstep (se 1 (by rfl) ⟨1561958, by rfl⟩ : syracuseStep 2082611 = 3123917) B3123917
theorem B4704101 : Blo 822348 4704101 := bstep (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) B882019
theorem B2967475 : Blo 822348 2967475 := bstep (se 1 (by rfl) ⟨2225606, by rfl⟩ : syracuseStep 2967475 = 4451213) B4451213
theorem B1853387 : Blo 822348 1853387 := bstep (se 1 (by rfl) ⟨1390040, by rfl⟩ : syracuseStep 1853387 = 2780081) B2780081
theorem B1853441 : Blo 822348 1853441 := bstep (se 2 (by rfl) ⟨695040, by rfl⟩ : syracuseStep 1853441 = 1390081) B1390081
theorem B2967617 : Blo 822348 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B2082905 : Blo 822348 2082905 := bstep (se 2 (by rfl) ⟨781089, by rfl⟩ : syracuseStep 2082905 = 1562179) B1562179
theorem B13355189 : Blo 822348 13355189 := bstep (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) B1252049
theorem B1853657 : Blo 822348 1853657 := bstep (se 2 (by rfl) ⟨695121, by rfl⟩ : syracuseStep 1853657 = 1390243) B1390243
theorem B3131693 : Blo 822348 3131693 := bstep (se 3 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 3131693 = 1174385) B1174385
theorem B1853747 : Blo 822348 1853747 := bstep (se 1 (by rfl) ⟨1390310, by rfl⟩ : syracuseStep 1853747 = 2780621) B2780621
theorem B3131723 : Blo 822348 3131723 := bstep (se 1 (by rfl) ⟨2348792, by rfl⟩ : syracuseStep 3131723 = 4697585) B4697585
theorem B1853783 : Blo 822348 1853783 := bstep (se 1 (by rfl) ⟨1390337, by rfl⟩ : syracuseStep 1853783 = 2780675) B2780675
theorem B1853963 : Blo 822348 1853963 := bstep (se 1 (by rfl) ⟨1390472, by rfl⟩ : syracuseStep 1853963 = 2780945) B2780945
theorem B1854017 : Blo 822348 1854017 := bstep (se 2 (by rfl) ⟨695256, by rfl⟩ : syracuseStep 1854017 = 1390513) B1390513
theorem B13519511 : Blo 822348 13519511 := bstep (se 1 (by rfl) ⟨10139633, by rfl⟩ : syracuseStep 13519511 = 20279267) B20279267
theorem B7031447 : Blo 822348 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B1854233 : Blo 822348 1854233 := bstep (se 2 (by rfl) ⟨695337, by rfl⟩ : syracuseStep 1854233 = 1390675) B1390675
theorem B1985369 : Blo 822348 1985369 := bstep (se 2 (by rfl) ⟨744513, by rfl⟩ : syracuseStep 1985369 = 1489027) B1489027
theorem B1854323 : Blo 822348 1854323 := bstep (se 1 (by rfl) ⟨1390742, by rfl⟩ : syracuseStep 1854323 = 2781485) B2781485
theorem B1854359 : Blo 822348 1854359 := bstep (se 1 (by rfl) ⟨1390769, by rfl⟩ : syracuseStep 1854359 = 2781539) B2781539
theorem B3132377 : Blo 822348 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B4181057 : Blo 822348 4181057 := bstep (se 2 (by rfl) ⟨1567896, by rfl⟩ : syracuseStep 4181057 = 3135793) B3135793
theorem B2346059 : Blo 822348 2346059 := bstep (se 1 (by rfl) ⟨1759544, by rfl⟩ : syracuseStep 2346059 = 3519089) B3519089
theorem B1854539 : Blo 822348 1854539 := bstep (se 1 (by rfl) ⟨1390904, by rfl⟩ : syracuseStep 1854539 = 2781809) B2781809
theorem B3165277 : Blo 822348 3165277 := bstep (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) B1186979
theorem B1854593 : Blo 822348 1854593 := bstep (se 2 (by rfl) ⟨695472, by rfl⟩ : syracuseStep 1854593 = 1390945) B1390945
theorem B2641099 : Blo 822348 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B3132695 : Blo 822348 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B1854809 : Blo 822348 1854809 := bstep (se 2 (by rfl) ⟨695553, by rfl⟩ : syracuseStep 1854809 = 1391107) B1391107
theorem B1854899 : Blo 822348 1854899 := bstep (se 1 (by rfl) ⟨1391174, by rfl⟩ : syracuseStep 1854899 = 2782349) B2782349
theorem B1854935 : Blo 822348 1854935 := bstep (se 1 (by rfl) ⟨1391201, by rfl⟩ : syracuseStep 1854935 = 2782403) B2782403
theorem B2674241 : Blo 822348 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B1855115 : Blo 822348 1855115 := bstep (se 1 (by rfl) ⟨1391336, by rfl⟩ : syracuseStep 1855115 = 2782673) B2782673
theorem B1756811 : Blo 822348 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B1855169 : Blo 822348 1855169 := bstep (se 2 (by rfl) ⟨695688, by rfl⟩ : syracuseStep 1855169 = 1391377) B1391377
theorem B2084555 : Blo 822348 2084555 := bstep (se 1 (by rfl) ⟨1563416, by rfl⟩ : syracuseStep 2084555 = 3126833) B3126833
theorem B6672077 : Blo 822348 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B1855385 : Blo 822348 1855385 := bstep (se 2 (by rfl) ⟨695769, by rfl⟩ : syracuseStep 1855385 = 1391539) B1391539
theorem B3133363 : Blo 822348 3133363 := bstep (se 1 (by rfl) ⟨2350022, by rfl⟩ : syracuseStep 3133363 = 4700045) B4700045
theorem B1855475 : Blo 822348 1855475 := bstep (se 1 (by rfl) ⟨1391606, by rfl⟩ : syracuseStep 1855475 = 2783213) B2783213
theorem B1855511 : Blo 822348 1855511 := bstep (se 1 (by rfl) ⟨1391633, by rfl⟩ : syracuseStep 1855511 = 2783267) B2783267
theorem B1757323 : Blo 822348 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B1855691 : Blo 822348 1855691 := bstep (se 1 (by rfl) ⟨1391768, by rfl⟩ : syracuseStep 1855691 = 2783537) B2783537
theorem B1003735 : Blo 822348 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B1855745 : Blo 822348 1855745 := bstep (se 2 (by rfl) ⟨695904, by rfl⟩ : syracuseStep 1855745 = 1391809) B1391809
theorem B1855961 : Blo 822348 1855961 := bstep (se 2 (by rfl) ⟨695985, by rfl⟩ : syracuseStep 1855961 = 1391971) B1391971
theorem B1856051 : Blo 822348 1856051 := bstep (se 1 (by rfl) ⟨1392038, by rfl⟩ : syracuseStep 1856051 = 2784077) B2784077
theorem B1856087 : Blo 822348 1856087 := bstep (se 1 (by rfl) ⟨1392065, by rfl⟩ : syracuseStep 1856087 = 2784131) B2784131
theorem B6247043 : Blo 822348 6247043 := bstep (se 1 (by rfl) ⟨4685282, by rfl⟩ : syracuseStep 6247043 = 9370565) B9370565
theorem B2085527 : Blo 822348 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B2708147 : Blo 822348 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B2347699 : Blo 822348 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B1233611 : Blo 822348 1233611 := bstep (se 1 (by rfl) ⟨925208, by rfl⟩ : syracuseStep 1233611 = 1850417) B1850417
theorem B1233623 : Blo 822348 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B1856267 : Blo 822348 1856267 := bstep (se 1 (by rfl) ⟨1392200, by rfl⟩ : syracuseStep 1856267 = 2784401) B2784401
theorem B1233689 : Blo 822348 1233689 := bstep (se 2 (by rfl) ⟨462633, by rfl⟩ : syracuseStep 1233689 = 925267) B925267
theorem B1856321 : Blo 822348 1856321 := bstep (se 2 (by rfl) ⟨696120, by rfl⟩ : syracuseStep 1856321 = 1392241) B1392241
theorem B1758041 : Blo 822348 1758041 := bstep (se 2 (by rfl) ⟨659265, by rfl⟩ : syracuseStep 1758041 = 1318531) B1318531
theorem B2642777 : Blo 822348 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B906103 : Blo 822348 906103 := bstep (se 1 (by rfl) ⟨679577, by rfl⟩ : syracuseStep 906103 = 1359155) B1359155
theorem B1233803 : Blo 822348 1233803 := bstep (se 1 (by rfl) ⟨925352, by rfl⟩ : syracuseStep 1233803 = 1850705) B1850705
theorem B1233815 : Blo 822348 1233815 := bstep (se 1 (by rfl) ⟨925361, by rfl⟩ : syracuseStep 1233815 = 1850723) B1850723
theorem B1233881 : Blo 822348 1233881 := bstep (se 2 (by rfl) ⟨462705, by rfl⟩ : syracuseStep 1233881 = 925411) B925411
theorem B4183001 : Blo 822348 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B13390865 : Blo 822348 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B1856537 : Blo 822348 1856537 := bstep (se 2 (by rfl) ⟨696201, by rfl⟩ : syracuseStep 1856537 = 1392403) B1392403
theorem B1233995 : Blo 822348 1233995 := bstep (se 1 (by rfl) ⟨925496, by rfl⟩ : syracuseStep 1233995 = 1850993) B1850993
theorem B1234007 : Blo 822348 1234007 := bstep (se 1 (by rfl) ⟨925505, by rfl⟩ : syracuseStep 1234007 = 1851011) B1851011
theorem B1856627 : Blo 822348 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B3134609 : Blo 822348 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B1856663 : Blo 822348 1856663 := bstep (se 1 (by rfl) ⟨1392497, by rfl⟩ : syracuseStep 1856663 = 2784995) B2784995
theorem B1234073 : Blo 822348 1234073 := bstep (se 2 (by rfl) ⟨462777, by rfl⟩ : syracuseStep 1234073 = 925555) B925555
theorem B1758451 : Blo 822348 1758451 := bstep (se 1 (by rfl) ⟨1318838, by rfl⟩ : syracuseStep 1758451 = 2637677) B2637677
theorem B1234187 : Blo 822348 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B1234199 : Blo 822348 1234199 := bstep (se 1 (by rfl) ⟨925649, by rfl⟩ : syracuseStep 1234199 = 1851299) B1851299
theorem B2086195 : Blo 822348 2086195 := bstep (se 1 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 2086195 = 3129293) B3129293
theorem B1856843 : Blo 822348 1856843 := bstep (se 1 (by rfl) ⟨1392632, by rfl⟩ : syracuseStep 1856843 = 2785265) B2785265
theorem B1561943 : Blo 822348 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B1234265 : Blo 822348 1234265 := bstep (se 2 (by rfl) ⟨462849, by rfl⟩ : syracuseStep 1234265 = 925699) B925699
theorem B1856897 : Blo 822348 1856897 := bstep (se 2 (by rfl) ⟨696336, by rfl⟩ : syracuseStep 1856897 = 1392673) B1392673
theorem B2086337 : Blo 822348 2086337 := bstep (se 2 (by rfl) ⟨782376, by rfl⟩ : syracuseStep 2086337 = 1564753) B1564753
theorem B1234379 : Blo 822348 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B1234391 : Blo 822348 1234391 := bstep (se 1 (by rfl) ⟨925793, by rfl⟩ : syracuseStep 1234391 = 1851587) B1851587
theorem B1234457 : Blo 822348 1234457 := bstep (se 2 (by rfl) ⟨462921, by rfl⟩ : syracuseStep 1234457 = 925843) B925843
theorem B3757643 : Blo 822348 3757643 := bstep (se 1 (by rfl) ⟨2818232, by rfl⟩ : syracuseStep 3757643 = 5636465) B5636465
theorem B939607 : Blo 822348 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B1857113 : Blo 822348 1857113 := bstep (se 2 (by rfl) ⟨696417, by rfl⟩ : syracuseStep 1857113 = 1392835) B1392835
theorem B1234571 : Blo 822348 1234571 := bstep (se 1 (by rfl) ⟨925928, by rfl⟩ : syracuseStep 1234571 = 1851857) B1851857
theorem B1234583 : Blo 822348 1234583 := bstep (se 1 (by rfl) ⟨925937, by rfl⟩ : syracuseStep 1234583 = 1851875) B1851875
theorem B1857203 : Blo 822348 1857203 := bstep (se 1 (by rfl) ⟨1392902, by rfl⟩ : syracuseStep 1857203 = 2785805) B2785805
theorem B939703 : Blo 822348 939703 := bstep (se 1 (by rfl) ⟨704777, by rfl⟩ : syracuseStep 939703 = 1409555) B1409555
theorem B1005259 : Blo 822348 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B2348747 : Blo 822348 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B1857239 : Blo 822348 1857239 := bstep (se 1 (by rfl) ⟨1392929, by rfl⟩ : syracuseStep 1857239 = 2785859) B2785859
theorem B1234649 : Blo 822348 1234649 := bstep (se 2 (by rfl) ⟨462993, by rfl⟩ : syracuseStep 1234649 = 925987) B925987
theorem B2643673 : Blo 822348 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B3528451 : Blo 822348 3528451 := bstep (se 1 (by rfl) ⟨2646338, by rfl⟩ : syracuseStep 3528451 = 5292677) B5292677
theorem B1234763 : Blo 822348 1234763 := bstep (se 1 (by rfl) ⟨926072, by rfl⟩ : syracuseStep 1234763 = 1852145) B1852145
theorem B3135307 : Blo 822348 3135307 := bstep (se 1 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 3135307 = 4702961) B4702961
theorem B1234775 : Blo 822348 1234775 := bstep (se 1 (by rfl) ⟨926081, by rfl⟩ : syracuseStep 1234775 = 1852163) B1852163
theorem B1562483 : Blo 822348 1562483 := bstep (se 1 (by rfl) ⟨1171862, by rfl⟩ : syracuseStep 1562483 = 2343725) B2343725
theorem B1857419 : Blo 822348 1857419 := bstep (se 1 (by rfl) ⟨1393064, by rfl⟩ : syracuseStep 1857419 = 2786129) B2786129
theorem B1234841 : Blo 822348 1234841 := bstep (se 2 (by rfl) ⟨463065, by rfl⟩ : syracuseStep 1234841 = 926131) B926131
theorem B1857473 : Blo 822348 1857473 := bstep (se 2 (by rfl) ⟨696552, by rfl⟩ : syracuseStep 1857473 = 1393105) B1393105
theorem B1234955 : Blo 822348 1234955 := bstep (se 1 (by rfl) ⟨926216, by rfl⟩ : syracuseStep 1234955 = 1852433) B1852433
theorem B1234967 : Blo 822348 1234967 := bstep (se 1 (by rfl) ⟨926225, by rfl⟩ : syracuseStep 1234967 = 1852451) B1852451
theorem B1235033 : Blo 822348 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B2971741 : Blo 822348 2971741 := bstep (se 3 (by rfl) ⟨557201, by rfl⟩ : syracuseStep 2971741 = 1114403) B1114403
theorem B3135581 : Blo 822348 3135581 := bstep (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) B1175843
theorem B1857689 : Blo 822348 1857689 := bstep (se 2 (by rfl) ⟨696633, by rfl⟩ : syracuseStep 1857689 = 1393267) B1393267
theorem B1235147 : Blo 822348 1235147 := bstep (se 1 (by rfl) ⟨926360, by rfl⟩ : syracuseStep 1235147 = 1852721) B1852721
theorem B1235159 : Blo 822348 1235159 := bstep (se 1 (by rfl) ⟨926369, by rfl⟩ : syracuseStep 1235159 = 1852739) B1852739
theorem B1857779 : Blo 822348 1857779 := bstep (se 1 (by rfl) ⟨1393334, by rfl⟩ : syracuseStep 1857779 = 2786669) B2786669
theorem B1857815 : Blo 822348 1857815 := bstep (se 1 (by rfl) ⟨1393361, by rfl⟩ : syracuseStep 1857815 = 2786723) B2786723
theorem B1235225 : Blo 822348 1235225 := bstep (se 2 (by rfl) ⟨463209, by rfl⟩ : syracuseStep 1235225 = 926419) B926419
theorem B2644289 : Blo 822348 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B1562969 : Blo 822348 1562969 := bstep (se 2 (by rfl) ⟨586113, by rfl⟩ : syracuseStep 1562969 = 1172227) B1172227
theorem B1235339 : Blo 822348 1235339 := bstep (se 1 (by rfl) ⟨926504, by rfl⟩ : syracuseStep 1235339 = 1853009) B1853009
theorem B1235351 : Blo 822348 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B1759639 : Blo 822348 1759639 := bstep (se 1 (by rfl) ⟨1319729, by rfl⟩ : syracuseStep 1759639 = 2639459) B2639459
theorem B1759681 : Blo 822348 1759681 := bstep (se 2 (by rfl) ⟨659880, by rfl⟩ : syracuseStep 1759681 = 1319761) B1319761
theorem B2644417 : Blo 822348 2644417 := bstep (se 2 (by rfl) ⟨991656, by rfl⟩ : syracuseStep 2644417 = 1983313) B1983313
theorem B1857995 : Blo 822348 1857995 := bstep (se 1 (by rfl) ⟨1393496, by rfl⟩ : syracuseStep 1857995 = 2786993) B2786993
theorem B1235417 : Blo 822348 1235417 := bstep (se 2 (by rfl) ⟨463281, by rfl⟩ : syracuseStep 1235417 = 926563) B926563
theorem B1858049 : Blo 822348 1858049 := bstep (se 2 (by rfl) ⟨696768, by rfl⟩ : syracuseStep 1858049 = 1393537) B1393537
theorem B5954093 : Blo 822348 5954093 := bstep (se 3 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 5954093 = 2232785) B2232785
theorem B1235531 : Blo 822348 1235531 := bstep (se 1 (by rfl) ⟨926648, by rfl⟩ : syracuseStep 1235531 = 1853297) B1853297
theorem B1235543 : Blo 822348 1235543 := bstep (se 1 (by rfl) ⟨926657, by rfl⟩ : syracuseStep 1235543 = 1853315) B1853315
theorem B4446821 : Blo 822348 4446821 := bstep (se 4 (by rfl) ⟨416889, by rfl⟩ : syracuseStep 4446821 = 833779) B833779
theorem B1235609 : Blo 822348 1235609 := bstep (se 2 (by rfl) ⟨463353, by rfl⟩ : syracuseStep 1235609 = 926707) B926707
theorem B2087603 : Blo 822348 2087603 := bstep (se 1 (by rfl) ⟨1565702, by rfl⟩ : syracuseStep 2087603 = 3131405) B3131405
theorem B1858265 : Blo 822348 1858265 := bstep (se 2 (by rfl) ⟨696849, by rfl⟩ : syracuseStep 1858265 = 1393699) B1393699
theorem B1235723 : Blo 822348 1235723 := bstep (se 1 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 1235723 = 1853585) B1853585
theorem B1235735 : Blo 822348 1235735 := bstep (se 1 (by rfl) ⟨926801, by rfl⟩ : syracuseStep 1235735 = 1853603) B1853603
theorem B3136279 : Blo 822348 3136279 := bstep (se 1 (by rfl) ⟨2352209, by rfl⟩ : syracuseStep 3136279 = 4704419) B4704419
theorem B1858355 : Blo 822348 1858355 := bstep (se 1 (by rfl) ⟨1393766, by rfl⟩ : syracuseStep 1858355 = 2787533) B2787533
theorem B1858391 : Blo 822348 1858391 := bstep (se 1 (by rfl) ⟨1393793, by rfl⟩ : syracuseStep 1858391 = 2787587) B2787587
theorem B1235801 : Blo 822348 1235801 := bstep (se 2 (by rfl) ⟨463425, by rfl⟩ : syracuseStep 1235801 = 926851) B926851
theorem B1235915 : Blo 822348 1235915 := bstep (se 1 (by rfl) ⟨926936, by rfl⟩ : syracuseStep 1235915 = 1853873) B1853873
theorem B1235927 : Blo 822348 1235927 := bstep (se 1 (by rfl) ⟨926945, by rfl⟩ : syracuseStep 1235927 = 1853891) B1853891
theorem B1858571 : Blo 822348 1858571 := bstep (se 1 (by rfl) ⟨1393928, by rfl⟩ : syracuseStep 1858571 = 2787857) B2787857
theorem B1235993 : Blo 822348 1235993 := bstep (se 2 (by rfl) ⟨463497, by rfl⟩ : syracuseStep 1235993 = 926995) B926995
theorem B1858625 : Blo 822348 1858625 := bstep (se 2 (by rfl) ⟨696984, by rfl⟩ : syracuseStep 1858625 = 1393969) B1393969
theorem B2776139 : Blo 822348 2776139 := bstep (se 1 (by rfl) ⟨2082104, by rfl⟩ : syracuseStep 2776139 = 4164209) B4164209
theorem B1236107 : Blo 822348 1236107 := bstep (se 1 (by rfl) ⟨927080, by rfl⟩ : syracuseStep 1236107 = 1854161) B1854161
theorem B1236119 : Blo 822348 1236119 := bstep (se 1 (by rfl) ⟨927089, by rfl⟩ : syracuseStep 1236119 = 1854179) B1854179
theorem B9395351 : Blo 822348 9395351 := bstep (se 1 (by rfl) ⟨7046513, by rfl⟩ : syracuseStep 9395351 = 14093027) B14093027
theorem B2088139 : Blo 822348 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B1236185 : Blo 822348 1236185 := bstep (se 2 (by rfl) ⟨463569, by rfl⟩ : syracuseStep 1236185 = 927139) B927139
theorem B1858841 : Blo 822348 1858841 := bstep (se 2 (by rfl) ⟨697065, by rfl⟩ : syracuseStep 1858841 = 1394131) B1394131
theorem B2350387 : Blo 822348 2350387 := bstep (se 1 (by rfl) ⟨1762790, by rfl⟩ : syracuseStep 2350387 = 3525581) B3525581
theorem B1236299 : Blo 822348 1236299 := bstep (se 1 (by rfl) ⟨927224, by rfl⟩ : syracuseStep 1236299 = 1854449) B1854449
theorem B1236311 : Blo 822348 1236311 := bstep (se 1 (by rfl) ⟨927233, by rfl⟩ : syracuseStep 1236311 = 1854467) B1854467
theorem B2776409 : Blo 822348 2776409 := bstep (se 2 (by rfl) ⟨1041153, by rfl⟩ : syracuseStep 2776409 = 2082307) B2082307
theorem B2088281 : Blo 822348 2088281 := bstep (se 2 (by rfl) ⟨783105, by rfl⟩ : syracuseStep 2088281 = 1566211) B1566211
theorem B1858931 : Blo 822348 1858931 := bstep (se 1 (by rfl) ⟨1394198, by rfl⟩ : syracuseStep 1858931 = 2788397) B2788397
theorem B1858967 : Blo 822348 1858967 := bstep (se 1 (by rfl) ⟨1394225, by rfl⟩ : syracuseStep 1858967 = 2788451) B2788451
theorem B1236377 : Blo 822348 1236377 := bstep (se 2 (by rfl) ⟨463641, by rfl⟩ : syracuseStep 1236377 = 927283) B927283
theorem B4447705 : Blo 822348 4447705 := bstep (se 2 (by rfl) ⟨1667889, by rfl⟩ : syracuseStep 4447705 = 3335779) B3335779
theorem B1236491 : Blo 822348 1236491 := bstep (se 1 (by rfl) ⟨927368, by rfl⟩ : syracuseStep 1236491 = 1854737) B1854737
theorem B1236503 : Blo 822348 1236503 := bstep (se 1 (by rfl) ⟨927377, by rfl⟩ : syracuseStep 1236503 = 1854755) B1854755
theorem B2350615 : Blo 822348 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B3137069 : Blo 822348 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B1859147 : Blo 822348 1859147 := bstep (se 1 (by rfl) ⟨1394360, by rfl⟩ : syracuseStep 1859147 = 2788721) B2788721
theorem B1236569 : Blo 822348 1236569 := bstep (se 2 (by rfl) ⟨463713, by rfl⟩ : syracuseStep 1236569 = 927427) B927427
theorem B1859201 : Blo 822348 1859201 := bstep (se 2 (by rfl) ⟨697200, by rfl⟩ : syracuseStep 1859201 = 1394401) B1394401
theorem B1236683 : Blo 822348 1236683 := bstep (se 1 (by rfl) ⟨927512, by rfl⟩ : syracuseStep 1236683 = 1855025) B1855025
theorem B1236695 : Blo 822348 1236695 := bstep (se 1 (by rfl) ⟨927521, by rfl⟩ : syracuseStep 1236695 = 1855043) B1855043
theorem B1564427 : Blo 822348 1564427 := bstep (se 1 (by rfl) ⟨1173320, by rfl⟩ : syracuseStep 1564427 = 2346641) B2346641
theorem B1236761 : Blo 822348 1236761 := bstep (se 2 (by rfl) ⟨463785, by rfl⟩ : syracuseStep 1236761 = 927571) B927571
theorem B1236875 : Blo 822348 1236875 := bstep (se 1 (by rfl) ⟨927656, by rfl⟩ : syracuseStep 1236875 = 1855313) B1855313
theorem B1236887 : Blo 822348 1236887 := bstep (se 1 (by rfl) ⟨927665, by rfl⟩ : syracuseStep 1236887 = 1855331) B1855331
theorem B1564609 : Blo 822348 1564609 := bstep (se 2 (by rfl) ⟨586728, by rfl⟩ : syracuseStep 1564609 = 1173457) B1173457
theorem B6250445 : Blo 822348 6250445 := bstep (se 3 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 6250445 = 2343917) B2343917
theorem B1236953 : Blo 822348 1236953 := bstep (se 2 (by rfl) ⟨463857, by rfl⟩ : syracuseStep 1236953 = 927715) B927715
theorem B2777111 : Blo 822348 2777111 := bstep (se 1 (by rfl) ⟨2082833, by rfl⟩ : syracuseStep 2777111 = 4165667) B4165667
theorem B1761355 : Blo 822348 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B1237067 : Blo 822348 1237067 := bstep (se 1 (by rfl) ⟨927800, by rfl⟩ : syracuseStep 1237067 = 1855601) B1855601
theorem B1237079 : Blo 822348 1237079 := bstep (se 1 (by rfl) ⟨927809, by rfl⟩ : syracuseStep 1237079 = 1855619) B1855619
theorem B3760273 : Blo 822348 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B2089111 : Blo 822348 2089111 := bstep (se 1 (by rfl) ⟨1566833, by rfl⟩ : syracuseStep 2089111 = 3133667) B3133667
theorem B1237145 : Blo 822348 1237145 := bstep (se 2 (by rfl) ⟨463929, by rfl⟩ : syracuseStep 1237145 = 927859) B927859
theorem B1237259 : Blo 822348 1237259 := bstep (se 1 (by rfl) ⟨927944, by rfl⟩ : syracuseStep 1237259 = 1855889) B1855889
theorem B1237271 : Blo 822348 1237271 := bstep (se 1 (by rfl) ⟨927953, by rfl⟩ : syracuseStep 1237271 = 1855907) B1855907
theorem B7037219 : Blo 822348 7037219 := bstep (se 1 (by rfl) ⟨5277914, by rfl⟩ : syracuseStep 7037219 = 10555829) B10555829
theorem B1237337 : Blo 822348 1237337 := bstep (se 2 (by rfl) ⟨464001, by rfl⟩ : syracuseStep 1237337 = 928003) B928003
theorem B1565057 : Blo 822348 1565057 := bstep (se 2 (by rfl) ⟨586896, by rfl⟩ : syracuseStep 1565057 = 1173793) B1173793
theorem B1761689 : Blo 822348 1761689 := bstep (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) B1321267
theorem B6250931 : Blo 822348 6250931 := bstep (se 1 (by rfl) ⟨4688198, by rfl⟩ : syracuseStep 6250931 = 9376397) B9376397
theorem B1237451 : Blo 822348 1237451 := bstep (se 1 (by rfl) ⟨928088, by rfl⟩ : syracuseStep 1237451 = 1856177) B1856177
theorem B1237463 : Blo 822348 1237463 := bstep (se 1 (by rfl) ⟨928097, by rfl⟩ : syracuseStep 1237463 = 1856195) B1856195
theorem B1237529 : Blo 822348 1237529 := bstep (se 2 (by rfl) ⟨464073, by rfl⟩ : syracuseStep 1237529 = 928147) B928147
theorem B2777651 : Blo 822348 2777651 := bstep (se 1 (by rfl) ⟨2083238, by rfl⟩ : syracuseStep 2777651 = 4166477) B4166477
theorem B12706379 : Blo 822348 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B2089547 : Blo 822348 2089547 := bstep (se 1 (by rfl) ⟨1567160, by rfl⟩ : syracuseStep 2089547 = 3134321) B3134321
theorem B1172107 : Blo 822348 1172107 := bstep (se 1 (by rfl) ⟨879080, by rfl⟩ : syracuseStep 1172107 = 1758161) B1758161
theorem B1237643 : Blo 822348 1237643 := bstep (se 1 (by rfl) ⟨928232, by rfl⟩ : syracuseStep 1237643 = 1856465) B1856465
theorem B1237655 : Blo 822348 1237655 := bstep (se 1 (by rfl) ⟨928241, by rfl⟩ : syracuseStep 1237655 = 1856483) B1856483
theorem B1565399 : Blo 822348 1565399 := bstep (se 1 (by rfl) ⟨1174049, by rfl⟩ : syracuseStep 1565399 = 2348099) B2348099
theorem B1237721 : Blo 822348 1237721 := bstep (se 2 (by rfl) ⟨464145, by rfl⟩ : syracuseStep 1237721 = 928291) B928291
theorem B2646749 : Blo 822348 2646749 := bstep (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) B992531
theorem B2974481 : Blo 822348 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B2777921 : Blo 822348 2777921 := bstep (se 2 (by rfl) ⟨1041720, by rfl⟩ : syracuseStep 2777921 = 2083441) B2083441
theorem B1237835 : Blo 822348 1237835 := bstep (se 1 (by rfl) ⟨928376, by rfl⟩ : syracuseStep 1237835 = 1856753) B1856753
theorem B1237847 : Blo 822348 1237847 := bstep (se 1 (by rfl) ⟨928385, by rfl⟩ : syracuseStep 1237847 = 1856771) B1856771
theorem B1237913 : Blo 822348 1237913 := bstep (se 2 (by rfl) ⟨464217, by rfl⟩ : syracuseStep 1237913 = 928435) B928435
theorem B2089921 : Blo 822348 2089921 := bstep (se 2 (by rfl) ⟨783720, by rfl⟩ : syracuseStep 2089921 = 1567441) B1567441
theorem B1238027 : Blo 822348 1238027 := bstep (se 1 (by rfl) ⟨928520, by rfl⟩ : syracuseStep 1238027 = 1857041) B1857041
theorem B1238039 : Blo 822348 1238039 := bstep (se 1 (by rfl) ⟨928529, by rfl⟩ : syracuseStep 1238039 = 1857059) B1857059
theorem B8479819 : Blo 822348 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B1238105 : Blo 822348 1238105 := bstep (se 2 (by rfl) ⟨464289, by rfl⟩ : syracuseStep 1238105 = 928579) B928579
theorem B1238219 : Blo 822348 1238219 := bstep (se 1 (by rfl) ⟨928664, by rfl⟩ : syracuseStep 1238219 = 1857329) B1857329
theorem B1238231 : Blo 822348 1238231 := bstep (se 1 (by rfl) ⟨928673, by rfl⟩ : syracuseStep 1238231 = 1857347) B1857347
theorem B1238297 : Blo 822348 1238297 := bstep (se 2 (by rfl) ⟨464361, by rfl⟩ : syracuseStep 1238297 = 928723) B928723
theorem B1041751 : Blo 822348 1041751 := bstep (se 1 (by rfl) ⟨781313, by rfl⟩ : syracuseStep 1041751 = 1562627) B1562627
theorem B2352473 : Blo 822348 2352473 := bstep (se 2 (by rfl) ⟨882177, by rfl⟩ : syracuseStep 2352473 = 1764355) B1764355
theorem B2778461 : Blo 822348 2778461 := bstep (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) B1041923
theorem B1566067 : Blo 822348 1566067 := bstep (se 1 (by rfl) ⟨1174550, by rfl⟩ : syracuseStep 1566067 = 2349101) B2349101
theorem B1238411 : Blo 822348 1238411 := bstep (se 1 (by rfl) ⟨928808, by rfl⟩ : syracuseStep 1238411 = 1857617) B1857617
theorem B1238423 : Blo 822348 1238423 := bstep (se 1 (by rfl) ⟨928817, by rfl⟩ : syracuseStep 1238423 = 1857635) B1857635
theorem B1238489 : Blo 822348 1238489 := bstep (se 2 (by rfl) ⟨464433, by rfl⟩ : syracuseStep 1238489 = 928867) B928867
theorem B2090519 : Blo 822348 2090519 := bstep (se 1 (by rfl) ⟨1567889, by rfl⟩ : syracuseStep 2090519 = 3135779) B3135779
theorem B1238603 : Blo 822348 1238603 := bstep (se 1 (by rfl) ⟨928952, by rfl⟩ : syracuseStep 1238603 = 1857905) B1857905
theorem B1238615 : Blo 822348 1238615 := bstep (se 1 (by rfl) ⟨928961, by rfl⟩ : syracuseStep 1238615 = 1857923) B1857923
theorem B1238681 : Blo 822348 1238681 := bstep (se 2 (by rfl) ⟨464505, by rfl⟩ : syracuseStep 1238681 = 929011) B929011
theorem B1697537 : Blo 822348 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B1238795 : Blo 822348 1238795 := bstep (se 1 (by rfl) ⟨929096, by rfl⟩ : syracuseStep 1238795 = 1858193) B1858193
theorem B1238807 : Blo 822348 1238807 := bstep (se 1 (by rfl) ⟨929105, by rfl⟩ : syracuseStep 1238807 = 1858211) B1858211
theorem B1566515 : Blo 822348 1566515 := bstep (se 1 (by rfl) ⟨1174886, by rfl⟩ : syracuseStep 1566515 = 2349773) B2349773
theorem B1566553 : Blo 822348 1566553 := bstep (se 2 (by rfl) ⟨587457, by rfl⟩ : syracuseStep 1566553 = 1174915) B1174915
theorem B1238873 : Blo 822348 1238873 := bstep (se 2 (by rfl) ⟨464577, by rfl⟩ : syracuseStep 1238873 = 929155) B929155
theorem B6252389 : Blo 822348 6252389 := bstep (se 4 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 6252389 = 1172323) B1172323
theorem B1763201 : Blo 822348 1763201 := bstep (se 2 (by rfl) ⟨661200, by rfl⟩ : syracuseStep 1763201 = 1322401) B1322401
theorem B1238987 : Blo 822348 1238987 := bstep (se 1 (by rfl) ⟨929240, by rfl⟩ : syracuseStep 1238987 = 1858481) B1858481
theorem B1238999 : Blo 822348 1238999 := bstep (se 1 (by rfl) ⟨929249, by rfl⟩ : syracuseStep 1238999 = 1858499) B1858499
theorem B1239065 : Blo 822348 1239065 := bstep (se 2 (by rfl) ⟨464649, by rfl⟩ : syracuseStep 1239065 = 929299) B929299
theorem B1042571 : Blo 822348 1042571 := bstep (se 1 (by rfl) ⟨781928, by rfl⟩ : syracuseStep 1042571 = 1563857) B1563857
theorem B1239179 : Blo 822348 1239179 := bstep (se 1 (by rfl) ⟨929384, by rfl⟩ : syracuseStep 1239179 = 1858769) B1858769
theorem B1239191 : Blo 822348 1239191 := bstep (se 1 (by rfl) ⟨929393, by rfl⟩ : syracuseStep 1239191 = 1858787) B1858787
theorem B878807 : Blo 822348 878807 := bstep (se 1 (by rfl) ⟨659105, by rfl⟩ : syracuseStep 878807 = 1318211) B1318211
theorem B1239257 : Blo 822348 1239257 := bstep (se 2 (by rfl) ⟨464721, by rfl⟩ : syracuseStep 1239257 = 929443) B929443
theorem B1567001 : Blo 822348 1567001 := bstep (se 2 (by rfl) ⟨587625, by rfl⟩ : syracuseStep 1567001 = 1175251) B1175251
theorem B2091329 : Blo 822348 2091329 := bstep (se 2 (by rfl) ⟨784248, by rfl⟩ : syracuseStep 2091329 = 1568497) B1568497
theorem B6252875 : Blo 822348 6252875 := bstep (se 1 (by rfl) ⟨4689656, by rfl⟩ : syracuseStep 6252875 = 9379313) B9379313
theorem B1239371 : Blo 822348 1239371 := bstep (se 1 (by rfl) ⟨929528, by rfl⟩ : syracuseStep 1239371 = 1859057) B1859057
theorem B878935 : Blo 822348 878935 := bstep (se 1 (by rfl) ⟨659201, by rfl⟩ : syracuseStep 878935 = 1318403) B1318403
theorem B1239383 : Blo 822348 1239383 := bstep (se 1 (by rfl) ⟨929537, by rfl⟩ : syracuseStep 1239383 = 1859075) B1859075
theorem B1239449 : Blo 822348 1239449 := bstep (se 2 (by rfl) ⟨464793, by rfl⟩ : syracuseStep 1239449 = 929587) B929587
theorem B2779595 : Blo 822348 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B1764055 : Blo 822348 1764055 := bstep (se 1 (by rfl) ⟨1323041, by rfl⟩ : syracuseStep 1764055 = 2646083) B2646083
theorem B2779865 : Blo 822348 2779865 := bstep (se 2 (by rfl) ⟨1042449, by rfl⟩ : syracuseStep 2779865 = 2084899) B2084899
theorem B3959513 : Blo 822348 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B3336983 : Blo 822348 3336983 := bstep (se 1 (by rfl) ⟨2502737, by rfl⟩ : syracuseStep 3336983 = 5005475) B5005475
theorem B1043275 : Blo 822348 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B879499 : Blo 822348 879499 := bstep (se 1 (by rfl) ⟨659624, by rfl⟩ : syracuseStep 879499 = 1319249) B1319249
theorem B2223065 : Blo 822348 2223065 := bstep (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) B1667299
theorem B1567745 : Blo 822348 1567745 := bstep (se 2 (by rfl) ⟨587904, by rfl⟩ : syracuseStep 1567745 = 1175809) B1175809
theorem B1043543 : Blo 822348 1043543 := bstep (se 1 (by rfl) ⟨782657, by rfl⟩ : syracuseStep 1043543 = 1565315) B1565315
theorem B879755 : Blo 822348 879755 := bstep (se 1 (by rfl) ⟨659816, by rfl⟩ : syracuseStep 879755 = 1319633) B1319633
theorem B2223325 : Blo 822348 2223325 := bstep (se 3 (by rfl) ⟨416873, by rfl⟩ : syracuseStep 2223325 = 833747) B833747
theorem B1568011 : Blo 822348 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B2780567 : Blo 822348 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B2223767 : Blo 822348 2223767 := bstep (se 1 (by rfl) ⟨1667825, by rfl⟩ : syracuseStep 2223767 = 3335651) B3335651
theorem B1568459 : Blo 822348 1568459 := bstep (se 1 (by rfl) ⟨1176344, by rfl⟩ : syracuseStep 1568459 = 2352689) B2352689
theorem B1044247 : Blo 822348 1044247 := bstep (se 1 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 1044247 = 1566371) B1566371
theorem B7040843 : Blo 822348 7040843 := bstep (se 1 (by rfl) ⟨5280632, by rfl⟩ : syracuseStep 7040843 = 10561265) B10561265
theorem B1568641 : Blo 822348 1568641 := bstep (se 2 (by rfl) ⟨588240, by rfl⟩ : syracuseStep 1568641 = 1176481) B1176481
theorem B2781107 : Blo 822348 2781107 := bstep (se 1 (by rfl) ⟨2085830, by rfl⟩ : syracuseStep 2781107 = 4171661) B4171661
theorem B11300957 : Blo 822348 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B2781377 : Blo 822348 2781377 := bstep (se 2 (by rfl) ⟨1043016, by rfl⟩ : syracuseStep 2781377 = 2086033) B2086033
theorem B2224331 : Blo 822348 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B2781917 : Blo 822348 2781917 := bstep (se 3 (by rfl) ⟨521609, by rfl⟩ : syracuseStep 2781917 = 1043219) B1043219
theorem B6681419 : Blo 822348 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B3339139 : Blo 822348 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B3765143 : Blo 822348 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B1340491 : Blo 822348 1340491 := bstep (se 1 (by rfl) ⟨1005368, by rfl⟩ : syracuseStep 1340491 = 2010737) B2010737
theorem B881771 : Blo 822348 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B2225497 : Blo 822348 2225497 := bstep (se 2 (by rfl) ⟨834561, by rfl⟩ : syracuseStep 2225497 = 1669123) B1669123
theorem B1504727 : Blo 822348 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B3175901 : Blo 822348 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B2783051 : Blo 822348 2783051 := bstep (se 1 (by rfl) ⟨2087288, by rfl⟩ : syracuseStep 2783051 = 4174577) B4174577
theorem B2258867 : Blo 822348 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B3766219 : Blo 822348 3766219 := bstep (se 1 (by rfl) ⟨2824664, by rfl⟩ : syracuseStep 3766219 = 5649329) B5649329
theorem B2783321 : Blo 822348 2783321 := bstep (se 2 (by rfl) ⟨1043745, by rfl⟩ : syracuseStep 2783321 = 2087491) B2087491
theorem B7043507 : Blo 822348 7043507 := bstep (se 1 (by rfl) ⟨5282630, by rfl⟩ : syracuseStep 7043507 = 10565261) B10565261
theorem B2259479 : Blo 822348 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B3963437 : Blo 822348 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B3767057 : Blo 822348 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2784023 : Blo 822348 2784023 := bstep (se 1 (by rfl) ⟨2088017, by rfl⟩ : syracuseStep 2784023 = 4176035) B4176035
theorem B1112921 : Blo 822348 1112921 := bstep (se 2 (by rfl) ⟨417345, by rfl⟩ : syracuseStep 1112921 = 834691) B834691
theorem B7928867 : Blo 822348 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B2784563 : Blo 822348 2784563 := bstep (se 1 (by rfl) ⟨2088422, by rfl⟩ : syracuseStep 2784563 = 4176845) B4176845
theorem B7044569 : Blo 822348 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B1113625 : Blo 822348 1113625 := bstep (se 2 (by rfl) ⟨417609, by rfl⟩ : syracuseStep 1113625 = 835219) B835219
theorem B1670681 : Blo 822348 1670681 := bstep (se 2 (by rfl) ⟨626505, by rfl⟩ : syracuseStep 1670681 = 1253011) B1253011
theorem B6258221 : Blo 822348 6258221 := bstep (se 3 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 6258221 = 2346833) B2346833
theorem B2784833 : Blo 822348 2784833 := bstep (se 2 (by rfl) ⟨1044312, by rfl⟩ : syracuseStep 2784833 = 2088625) B2088625
theorem B3014347 : Blo 822348 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B3342397 : Blo 822348 3342397 := bstep (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) B1253399
theorem B5013697 : Blo 822348 5013697 := bstep (se 2 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 5013697 = 3760273) B3760273
theorem B2785481 : Blo 822348 2785481 := bstep (se 2 (by rfl) ⟨1044555, by rfl⟩ : syracuseStep 2785481 = 2089111) B2089111
theorem B5636573 : Blo 822348 5636573 := bstep (se 3 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 5636573 = 2113715) B2113715
theorem B4457047 : Blo 822348 4457047 := bstep (se 1 (by rfl) ⟨3342785, by rfl⟩ : syracuseStep 4457047 = 6685571) B6685571
theorem B1114825 : Blo 822348 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B4457267 : Blo 822348 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B2786183 : Blo 822348 2786183 := bstep (se 1 (by rfl) ⟨2089637, by rfl⟩ : syracuseStep 2786183 = 4179275) B4179275
theorem B9405557 : Blo 822348 9405557 := bstep (se 5 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 9405557 = 881771) B881771
theorem B4687105 : Blo 822348 4687105 := bstep (se 2 (by rfl) ⟨1757664, by rfl⟩ : syracuseStep 4687105 = 3515329) B3515329
theorem B2786561 : Blo 822348 2786561 := bstep (se 2 (by rfl) ⟨1044960, by rfl⟩ : syracuseStep 2786561 = 2089921) B2089921
theorem B11306425 : Blo 822348 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B5277149 : Blo 822348 5277149 := bstep (se 3 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 5277149 = 1978931) B1978931
theorem B9013007 : Blo 822348 9013007 := bstep (se 1 (by rfl) ⟨6759755, by rfl⟩ : syracuseStep 9013007 = 13519511) B13519511
theorem B4687631 : Blo 822348 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B6686479 : Blo 822348 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B2787371 : Blo 822348 2787371 := bstep (se 1 (by rfl) ⟨2090528, by rfl⟩ : syracuseStep 2787371 = 4181057) B4181057
theorem B6261137 : Blo 822348 6261137 := bstep (se 2 (by rfl) ⟨2347926, by rfl⟩ : syracuseStep 6261137 = 4695853) B4695853
theorem B4164695 : Blo 822348 4164695 := bstep (se 1 (by rfl) ⟨3123521, by rfl⟩ : syracuseStep 4164695 = 6247043) B6247043
theorem B1805431 : Blo 822348 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B822407 : Blo 822348 822407 := bstep (se 1 (by rfl) ⟨616805, by rfl⟩ : syracuseStep 822407 = 1233611) B1233611
theorem B822415 : Blo 822348 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B822459 : Blo 822348 822459 := bstep (se 1 (by rfl) ⟨616844, by rfl⟩ : syracuseStep 822459 = 1233689) B1233689
theorem B4689089 : Blo 822348 4689089 := bstep (se 2 (by rfl) ⟨1758408, by rfl⟩ : syracuseStep 4689089 = 3516817) B3516817
theorem B822535 : Blo 822348 822535 := bstep (se 1 (by rfl) ⟨616901, by rfl⟩ : syracuseStep 822535 = 1233803) B1233803
theorem B822543 : Blo 822348 822543 := bstep (se 1 (by rfl) ⟨616907, by rfl⟩ : syracuseStep 822543 = 1233815) B1233815
theorem B822587 : Blo 822348 822587 := bstep (se 1 (by rfl) ⟨616940, by rfl⟩ : syracuseStep 822587 = 1233881) B1233881
theorem B2788667 : Blo 822348 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B822663 : Blo 822348 822663 := bstep (se 1 (by rfl) ⟨616997, by rfl⟩ : syracuseStep 822663 = 1233995) B1233995
theorem B822671 : Blo 822348 822671 := bstep (se 1 (by rfl) ⟨617003, by rfl⟩ : syracuseStep 822671 = 1234007) B1234007
theorem B822715 : Blo 822348 822715 := bstep (se 1 (by rfl) ⟨617036, by rfl⟩ : syracuseStep 822715 = 1234073) B1234073
theorem B822791 : Blo 822348 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B822799 : Blo 822348 822799 := bstep (se 1 (by rfl) ⟨617099, by rfl⟩ : syracuseStep 822799 = 1234199) B1234199
theorem B822843 : Blo 822348 822843 := bstep (se 1 (by rfl) ⟨617132, by rfl⟩ : syracuseStep 822843 = 1234265) B1234265
theorem B4165181 : Blo 822348 4165181 := bstep (se 3 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 4165181 = 1561943) B1561943
theorem B822919 : Blo 822348 822919 := bstep (se 1 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 822919 = 1234379) B1234379
theorem B822927 : Blo 822348 822927 := bstep (se 1 (by rfl) ⟨617195, by rfl⟩ : syracuseStep 822927 = 1234391) B1234391
theorem B822971 : Blo 822348 822971 := bstep (se 1 (by rfl) ⟨617228, by rfl⟩ : syracuseStep 822971 = 1234457) B1234457
theorem B823047 : Blo 822348 823047 := bstep (se 1 (by rfl) ⟨617285, by rfl⟩ : syracuseStep 823047 = 1234571) B1234571
theorem B823055 : Blo 822348 823055 := bstep (se 1 (by rfl) ⟨617291, by rfl⟩ : syracuseStep 823055 = 1234583) B1234583
theorem B823099 : Blo 822348 823099 := bstep (se 1 (by rfl) ⟨617324, by rfl⟩ : syracuseStep 823099 = 1234649) B1234649
theorem B19009397 : Blo 822348 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B823175 : Blo 822348 823175 := bstep (se 1 (by rfl) ⟨617381, by rfl⟩ : syracuseStep 823175 = 1234763) B1234763
theorem B823183 : Blo 822348 823183 := bstep (se 1 (by rfl) ⟨617387, by rfl⟩ : syracuseStep 823183 = 1234775) B1234775
theorem B823227 : Blo 822348 823227 := bstep (se 1 (by rfl) ⟨617420, by rfl⟩ : syracuseStep 823227 = 1234841) B1234841
theorem B823303 : Blo 822348 823303 := bstep (se 1 (by rfl) ⟨617477, by rfl⟩ : syracuseStep 823303 = 1234955) B1234955
theorem B823311 : Blo 822348 823311 := bstep (se 1 (by rfl) ⟨617483, by rfl⟩ : syracuseStep 823311 = 1234967) B1234967
theorem B823355 : Blo 822348 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B823431 : Blo 822348 823431 := bstep (se 1 (by rfl) ⟨617573, by rfl⟩ : syracuseStep 823431 = 1235147) B1235147
theorem B823439 : Blo 822348 823439 := bstep (se 1 (by rfl) ⟨617579, by rfl⟩ : syracuseStep 823439 = 1235159) B1235159
theorem B823483 : Blo 822348 823483 := bstep (se 1 (by rfl) ⟨617612, by rfl⟩ : syracuseStep 823483 = 1235225) B1235225
theorem B823559 : Blo 822348 823559 := bstep (se 1 (by rfl) ⟨617669, by rfl⟩ : syracuseStep 823559 = 1235339) B1235339
theorem B823567 : Blo 822348 823567 := bstep (se 1 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 823567 = 1235351) B1235351
theorem B823611 : Blo 822348 823611 := bstep (se 1 (by rfl) ⟨617708, by rfl⟩ : syracuseStep 823611 = 1235417) B1235417
theorem B3969395 : Blo 822348 3969395 := bstep (se 1 (by rfl) ⟨2977046, by rfl⟩ : syracuseStep 3969395 = 5954093) B5954093
theorem B823687 : Blo 822348 823687 := bstep (se 1 (by rfl) ⟨617765, by rfl⟩ : syracuseStep 823687 = 1235531) B1235531
theorem B823695 : Blo 822348 823695 := bstep (se 1 (by rfl) ⟨617771, by rfl⟩ : syracuseStep 823695 = 1235543) B1235543
theorem B823739 : Blo 822348 823739 := bstep (se 1 (by rfl) ⟨617804, by rfl⟩ : syracuseStep 823739 = 1235609) B1235609
theorem B823815 : Blo 822348 823815 := bstep (se 1 (by rfl) ⟨617861, by rfl⟩ : syracuseStep 823815 = 1235723) B1235723
theorem B823823 : Blo 822348 823823 := bstep (se 1 (by rfl) ⟨617867, by rfl⟩ : syracuseStep 823823 = 1235735) B1235735
theorem B823867 : Blo 822348 823867 := bstep (se 1 (by rfl) ⟨617900, by rfl⟩ : syracuseStep 823867 = 1235801) B1235801
theorem B2232893 : Blo 822348 2232893 := bstep (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) B837335
theorem B823943 : Blo 822348 823943 := bstep (se 1 (by rfl) ⟨617957, by rfl⟩ : syracuseStep 823943 = 1235915) B1235915
theorem B823951 : Blo 822348 823951 := bstep (se 1 (by rfl) ⟨617963, by rfl⟩ : syracuseStep 823951 = 1235927) B1235927
theorem B4526765 : Blo 822348 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B823995 : Blo 822348 823995 := bstep (se 1 (by rfl) ⟨617996, by rfl⟩ : syracuseStep 823995 = 1235993) B1235993
theorem B824071 : Blo 822348 824071 := bstep (se 1 (by rfl) ⟨618053, by rfl⟩ : syracuseStep 824071 = 1236107) B1236107
theorem B824079 : Blo 822348 824079 := bstep (se 1 (by rfl) ⟨618059, by rfl⟩ : syracuseStep 824079 = 1236119) B1236119
theorem B6263567 : Blo 822348 6263567 := bstep (se 1 (by rfl) ⟨4697675, by rfl⟩ : syracuseStep 6263567 = 9395351) B9395351
theorem B824123 : Blo 822348 824123 := bstep (se 1 (by rfl) ⟨618092, by rfl⟩ : syracuseStep 824123 = 1236185) B1236185
theorem B824199 : Blo 822348 824199 := bstep (se 1 (by rfl) ⟨618149, by rfl⟩ : syracuseStep 824199 = 1236299) B1236299
theorem B824207 : Blo 822348 824207 := bstep (se 1 (by rfl) ⟨618155, by rfl⟩ : syracuseStep 824207 = 1236311) B1236311
theorem B824251 : Blo 822348 824251 := bstep (se 1 (by rfl) ⟨618188, by rfl⟩ : syracuseStep 824251 = 1236377) B1236377
theorem B824327 : Blo 822348 824327 := bstep (se 1 (by rfl) ⟨618245, by rfl⟩ : syracuseStep 824327 = 1236491) B1236491
theorem B824335 : Blo 822348 824335 := bstep (se 1 (by rfl) ⟨618251, by rfl⟩ : syracuseStep 824335 = 1236503) B1236503
theorem B824379 : Blo 822348 824379 := bstep (se 1 (by rfl) ⟨618284, by rfl⟩ : syracuseStep 824379 = 1236569) B1236569
theorem B824455 : Blo 822348 824455 := bstep (se 1 (by rfl) ⟨618341, by rfl⟩ : syracuseStep 824455 = 1236683) B1236683
theorem B824463 : Blo 822348 824463 := bstep (se 1 (by rfl) ⟨618347, by rfl⟩ : syracuseStep 824463 = 1236695) B1236695
theorem B824507 : Blo 822348 824507 := bstep (se 1 (by rfl) ⟨618380, by rfl⟩ : syracuseStep 824507 = 1236761) B1236761
theorem B824583 : Blo 822348 824583 := bstep (se 1 (by rfl) ⟨618437, by rfl⟩ : syracuseStep 824583 = 1236875) B1236875
theorem B824591 : Blo 822348 824591 := bstep (se 1 (by rfl) ⟨618443, by rfl⟩ : syracuseStep 824591 = 1236887) B1236887
theorem B4461875 : Blo 822348 4461875 := bstep (se 1 (by rfl) ⟨3346406, by rfl⟩ : syracuseStep 4461875 = 6692813) B6692813
theorem B4166963 : Blo 822348 4166963 := bstep (se 1 (by rfl) ⟨3125222, by rfl⟩ : syracuseStep 4166963 = 6250445) B6250445
theorem B824635 : Blo 822348 824635 := bstep (se 1 (by rfl) ⟨618476, by rfl⟩ : syracuseStep 824635 = 1236953) B1236953
theorem B824711 : Blo 822348 824711 := bstep (se 1 (by rfl) ⟨618533, by rfl⟩ : syracuseStep 824711 = 1237067) B1237067
theorem B824719 : Blo 822348 824719 := bstep (se 1 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 824719 = 1237079) B1237079
theorem B824763 : Blo 822348 824763 := bstep (se 1 (by rfl) ⟨618572, by rfl⟩ : syracuseStep 824763 = 1237145) B1237145
theorem B824839 : Blo 822348 824839 := bstep (se 1 (by rfl) ⟨618629, by rfl⟩ : syracuseStep 824839 = 1237259) B1237259
theorem B824847 : Blo 822348 824847 := bstep (se 1 (by rfl) ⟨618635, by rfl⟩ : syracuseStep 824847 = 1237271) B1237271
theorem B4691479 : Blo 822348 4691479 := bstep (se 1 (by rfl) ⟨3518609, by rfl⟩ : syracuseStep 4691479 = 7037219) B7037219
theorem B824891 : Blo 822348 824891 := bstep (se 1 (by rfl) ⟨618668, by rfl⟩ : syracuseStep 824891 = 1237337) B1237337
theorem B4167287 : Blo 822348 4167287 := bstep (se 1 (by rfl) ⟨3125465, by rfl⟩ : syracuseStep 4167287 = 6250931) B6250931
theorem B824967 : Blo 822348 824967 := bstep (se 1 (by rfl) ⟨618725, by rfl⟩ : syracuseStep 824967 = 1237451) B1237451
theorem B824975 : Blo 822348 824975 := bstep (se 1 (by rfl) ⟨618731, by rfl⟩ : syracuseStep 824975 = 1237463) B1237463
theorem B825019 : Blo 822348 825019 := bstep (se 1 (by rfl) ⟨618764, by rfl⟩ : syracuseStep 825019 = 1237529) B1237529
theorem B825095 : Blo 822348 825095 := bstep (se 1 (by rfl) ⟨618821, by rfl⟩ : syracuseStep 825095 = 1237643) B1237643
theorem B825103 : Blo 822348 825103 := bstep (se 1 (by rfl) ⟨618827, by rfl⟩ : syracuseStep 825103 = 1237655) B1237655
theorem B825147 : Blo 822348 825147 := bstep (se 1 (by rfl) ⟨618860, by rfl⟩ : syracuseStep 825147 = 1237721) B1237721
theorem B825223 : Blo 822348 825223 := bstep (se 1 (by rfl) ⟨618917, by rfl⟩ : syracuseStep 825223 = 1237835) B1237835
theorem B825231 : Blo 822348 825231 := bstep (se 1 (by rfl) ⟨618923, by rfl⟩ : syracuseStep 825231 = 1237847) B1237847
theorem B825275 : Blo 822348 825275 := bstep (se 1 (by rfl) ⟨618956, by rfl⟩ : syracuseStep 825275 = 1237913) B1237913
theorem B825351 : Blo 822348 825351 := bstep (se 1 (by rfl) ⟨619013, by rfl⟩ : syracuseStep 825351 = 1238027) B1238027
theorem B825359 : Blo 822348 825359 := bstep (se 1 (by rfl) ⟨619019, by rfl⟩ : syracuseStep 825359 = 1238039) B1238039
theorem B825403 : Blo 822348 825403 := bstep (se 1 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 825403 = 1238105) B1238105
theorem B825479 : Blo 822348 825479 := bstep (se 1 (by rfl) ⟨619109, by rfl⟩ : syracuseStep 825479 = 1238219) B1238219
theorem B825487 : Blo 822348 825487 := bstep (se 1 (by rfl) ⟨619115, by rfl⟩ : syracuseStep 825487 = 1238231) B1238231
theorem B825531 : Blo 822348 825531 := bstep (se 1 (by rfl) ⟨619148, by rfl⟩ : syracuseStep 825531 = 1238297) B1238297
theorem B825607 : Blo 822348 825607 := bstep (se 1 (by rfl) ⟨619205, by rfl⟩ : syracuseStep 825607 = 1238411) B1238411
theorem B825615 : Blo 822348 825615 := bstep (se 1 (by rfl) ⟨619211, by rfl⟩ : syracuseStep 825615 = 1238423) B1238423
theorem B825659 : Blo 822348 825659 := bstep (se 1 (by rfl) ⟨619244, by rfl⟩ : syracuseStep 825659 = 1238489) B1238489
theorem B825735 : Blo 822348 825735 := bstep (se 1 (by rfl) ⟨619301, by rfl⟩ : syracuseStep 825735 = 1238603) B1238603
theorem B825743 : Blo 822348 825743 := bstep (se 1 (by rfl) ⟨619307, by rfl⟩ : syracuseStep 825743 = 1238615) B1238615
theorem B825787 : Blo 822348 825787 := bstep (se 1 (by rfl) ⟨619340, by rfl⟩ : syracuseStep 825787 = 1238681) B1238681
theorem B825863 : Blo 822348 825863 := bstep (se 1 (by rfl) ⟨619397, by rfl⟩ : syracuseStep 825863 = 1238795) B1238795
theorem B825871 : Blo 822348 825871 := bstep (se 1 (by rfl) ⟨619403, by rfl⟩ : syracuseStep 825871 = 1238807) B1238807
theorem B7936555 : Blo 822348 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B825915 : Blo 822348 825915 := bstep (se 1 (by rfl) ⟨619436, by rfl⟩ : syracuseStep 825915 = 1238873) B1238873
theorem B4168259 : Blo 822348 4168259 := bstep (se 1 (by rfl) ⟨3126194, by rfl⟩ : syracuseStep 4168259 = 6252389) B6252389
theorem B8919629 : Blo 822348 8919629 := bstep (se 3 (by rfl) ⟨1672430, by rfl⟩ : syracuseStep 8919629 = 3344861) B3344861
theorem B825991 : Blo 822348 825991 := bstep (se 1 (by rfl) ⟨619493, by rfl⟩ : syracuseStep 825991 = 1238987) B1238987
theorem B825999 : Blo 822348 825999 := bstep (se 1 (by rfl) ⟨619499, by rfl⟩ : syracuseStep 825999 = 1238999) B1238999
theorem B826043 : Blo 822348 826043 := bstep (se 1 (by rfl) ⟨619532, by rfl⟩ : syracuseStep 826043 = 1239065) B1239065
theorem B826119 : Blo 822348 826119 := bstep (se 1 (by rfl) ⟨619589, by rfl⟩ : syracuseStep 826119 = 1239179) B1239179
theorem B1317647 : Blo 822348 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B1252111 : Blo 822348 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B826127 : Blo 822348 826127 := bstep (se 1 (by rfl) ⟨619595, by rfl⟩ : syracuseStep 826127 = 1239191) B1239191
theorem B826171 : Blo 822348 826171 := bstep (se 1 (by rfl) ⟨619628, by rfl⟩ : syracuseStep 826171 = 1239257) B1239257
theorem B6691673 : Blo 822348 6691673 := bstep (se 2 (by rfl) ⟨2509377, by rfl⟩ : syracuseStep 6691673 = 5018755) B5018755
theorem B4168583 : Blo 822348 4168583 := bstep (se 1 (by rfl) ⟨3126437, by rfl⟩ : syracuseStep 4168583 = 6252875) B6252875
theorem B826247 : Blo 822348 826247 := bstep (se 1 (by rfl) ⟨619685, by rfl⟩ : syracuseStep 826247 = 1239371) B1239371
theorem B826255 : Blo 822348 826255 := bstep (se 1 (by rfl) ⟨619691, by rfl⟩ : syracuseStep 826255 = 1239383) B1239383
theorem B826299 : Blo 822348 826299 := bstep (se 1 (by rfl) ⟨619724, by rfl⟩ : syracuseStep 826299 = 1239449) B1239449
theorem B6692129 : Blo 822348 6692129 := bstep (se 2 (by rfl) ⟨2509548, by rfl⟩ : syracuseStep 6692129 = 5019097) B5019097
theorem B1252937 : Blo 822348 1252937 := bstep (se 2 (by rfl) ⟨469851, by rfl⟩ : syracuseStep 1252937 = 939703) B939703
theorem B925447 : Blo 822348 925447 := bstep (se 1 (by rfl) ⟨694085, by rfl⟩ : syracuseStep 925447 = 1388171) B1388171
theorem B1482511 : Blo 822348 1482511 := bstep (se 1 (by rfl) ⟨1111883, by rfl⟩ : syracuseStep 1482511 = 2223767) B2223767
theorem B4693895 : Blo 822348 4693895 := bstep (se 1 (by rfl) ⟨3520421, by rfl⟩ : syracuseStep 4693895 = 7040843) B7040843
theorem B991147 : Blo 822348 991147 := bstep (se 1 (by rfl) ⟨743360, by rfl⟩ : syracuseStep 991147 = 1486721) B1486721
theorem B925627 : Blo 822348 925627 := bstep (se 1 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 925627 = 1388441) B1388441
theorem B1482887 : Blo 822348 1482887 := bstep (se 1 (by rfl) ⟨1112165, by rfl⟩ : syracuseStep 1482887 = 2224331) B2224331
theorem B4071815 : Blo 822348 4071815 := bstep (se 1 (by rfl) ⟨3053861, by rfl⟩ : syracuseStep 4071815 = 6107723) B6107723
theorem B926095 : Blo 822348 926095 := bstep (se 1 (by rfl) ⟨694571, by rfl⟩ : syracuseStep 926095 = 1389143) B1389143
theorem B1254031 : Blo 822348 1254031 := bstep (se 1 (by rfl) ⟨940523, by rfl⟩ : syracuseStep 1254031 = 1881047) B1881047
theorem B10560293 : Blo 822348 10560293 := bstep (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) B1980055
theorem B926599 : Blo 822348 926599 := bstep (se 1 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 926599 = 1389899) B1389899
theorem B9380771 : Blo 822348 9380771 := bstep (se 1 (by rfl) ⟨7035578, by rfl⟩ : syracuseStep 9380771 = 14071157) B14071157
theorem B11871157 : Blo 822348 11871157 := bstep (se 5 (by rfl) ⟨556460, by rfl⟩ : syracuseStep 11871157 = 1112921) B1112921
theorem B926779 : Blo 822348 926779 := bstep (se 1 (by rfl) ⟨695084, by rfl⟩ : syracuseStep 926779 = 1390169) B1390169
theorem B4465957 : Blo 822348 4465957 := bstep (se 4 (by rfl) ⟨418683, by rfl⟩ : syracuseStep 4465957 = 837367) B837367
theorem B927247 : Blo 822348 927247 := bstep (se 1 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 927247 = 1390871) B1390871
theorem B4695671 : Blo 822348 4695671 := bstep (se 1 (by rfl) ⟨3521753, by rfl⟩ : syracuseStep 4695671 = 7043507) B7043507
theorem B3122945 : Blo 822348 3122945 := bstep (se 2 (by rfl) ⟨1171104, by rfl⟩ : syracuseStep 3122945 = 2342209) B2342209
theorem B1976183 : Blo 822348 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B1320889 : Blo 822348 1320889 := bstep (se 2 (by rfl) ⟨495333, by rfl⟩ : syracuseStep 1320889 = 990667) B990667
theorem B927751 : Blo 822348 927751 := bstep (se 1 (by rfl) ⟨695813, by rfl⟩ : syracuseStep 927751 = 1391627) B1391627
theorem B5285911 : Blo 822348 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B1484833 : Blo 822348 1484833 := bstep (se 2 (by rfl) ⟨556812, by rfl⟩ : syracuseStep 1484833 = 1113625) B1113625
theorem B927931 : Blo 822348 927931 := bstep (se 1 (by rfl) ⟨695948, by rfl⟩ : syracuseStep 927931 = 1391897) B1391897
theorem B4696379 : Blo 822348 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B4172147 : Blo 822348 4172147 := bstep (se 1 (by rfl) ⟨3129110, by rfl⟩ : syracuseStep 4172147 = 6258221) B6258221
theorem B928399 : Blo 822348 928399 := bstep (se 1 (by rfl) ⟨696299, by rfl⟩ : syracuseStep 928399 = 1392599) B1392599
theorem B4172633 : Blo 822348 4172633 := bstep (se 2 (by rfl) ⟨1564737, by rfl⟩ : syracuseStep 4172633 = 3129475) B3129475
theorem B3124115 : Blo 822348 3124115 := bstep (se 1 (by rfl) ⟨2343086, by rfl⟩ : syracuseStep 3124115 = 4686173) B4686173
theorem B1485857 : Blo 822348 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B1322119 : Blo 822348 1322119 := bstep (se 1 (by rfl) ⟨991589, by rfl⟩ : syracuseStep 1322119 = 1983179) B1983179
theorem B928903 : Blo 822348 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B929083 : Blo 822348 929083 := bstep (se 1 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 929083 = 1393625) B1393625
theorem B3124615 : Blo 822348 3124615 := bstep (se 1 (by rfl) ⟨2343461, by rfl⟩ : syracuseStep 3124615 = 4686923) B4686923
theorem B1289785 : Blo 822348 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B4697837 : Blo 822348 4697837 := bstep (se 3 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 4697837 = 1761689) B1761689
theorem B929551 : Blo 822348 929551 := bstep (se 1 (by rfl) ⟨697163, by rfl⟩ : syracuseStep 929551 = 1394327) B1394327
theorem B5353253 : Blo 822348 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B1388407 : Blo 822348 1388407 := bstep (se 1 (by rfl) ⟨1041305, by rfl⟩ : syracuseStep 1388407 = 2082611) B2082611
theorem B1879955 : Blo 822348 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B1486793 : Blo 822348 1486793 := bstep (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) B1115095
theorem B1388603 : Blo 822348 1388603 := bstep (se 1 (by rfl) ⟨1041452, by rfl⟩ : syracuseStep 1388603 = 2082905) B2082905
theorem B7909649 : Blo 822348 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B1389001 : Blo 822348 1389001 := bstep (se 2 (by rfl) ⟨520875, by rfl⟩ : syracuseStep 1389001 = 1041751) B1041751
theorem B1978825 : Blo 822348 1978825 := bstep (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) B1484119
theorem B4174739 : Blo 822348 4174739 := bstep (se 1 (by rfl) ⟨3131054, by rfl⟩ : syracuseStep 4174739 = 6262109) B6262109
theorem B7058339 : Blo 822348 7058339 := bstep (se 1 (by rfl) ⟨5293754, by rfl⟩ : syracuseStep 7058339 = 10587509) B10587509
theorem B2634781 : Blo 822348 2634781 := bstep (se 3 (by rfl) ⟨494021, by rfl⟩ : syracuseStep 2634781 = 988043) B988043
theorem B1782827 : Blo 822348 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B10040381 : Blo 822348 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B1389703 : Blo 822348 1389703 := bstep (se 1 (by rfl) ⟨1042277, by rfl⟩ : syracuseStep 1389703 = 2084555) B2084555
theorem B6272315 : Blo 822348 6272315 := bstep (se 1 (by rfl) ⟨4704236, by rfl⟩ : syracuseStep 6272315 = 9408473) B9408473
theorem B1390351 : Blo 822348 1390351 := bstep (se 1 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 1390351 = 2085527) B2085527
theorem B2111417 : Blo 822348 2111417 := bstep (se 2 (by rfl) ⟨791781, by rfl⟩ : syracuseStep 2111417 = 1583563) B1583563
theorem B3520523 : Blo 822348 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B8927243 : Blo 822348 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B4700227 : Blo 822348 4700227 := bstep (se 1 (by rfl) ⟨3525170, by rfl⟩ : syracuseStep 4700227 = 7050341) B7050341
theorem B1390891 : Blo 822348 1390891 := bstep (se 1 (by rfl) ⟨1043168, by rfl⟩ : syracuseStep 1390891 = 2086337) B2086337
theorem B2505095 : Blo 822348 2505095 := bstep (se 1 (by rfl) ⟨1878821, by rfl⟩ : syracuseStep 2505095 = 3757643) B3757643
theorem B1391033 : Blo 822348 1391033 := bstep (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) B1043275
theorem B1981217 : Blo 822348 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B3521465 : Blo 822348 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B2964433 : Blo 822348 2964433 := bstep (se 2 (by rfl) ⟨1111662, by rfl⟩ : syracuseStep 2964433 = 2223325) B2223325
theorem B2964547 : Blo 822348 2964547 := bstep (se 1 (by rfl) ⟨2223410, by rfl⟩ : syracuseStep 2964547 = 4446821) B4446821
theorem B1391735 : Blo 822348 1391735 := bstep (se 1 (by rfl) ⟨1043801, by rfl⟩ : syracuseStep 1391735 = 2087603) B2087603
theorem B5651657 : Blo 822348 5651657 := bstep (se 2 (by rfl) ⟨2119371, by rfl⟩ : syracuseStep 5651657 = 4238743) B4238743
theorem B1850759 : Blo 822348 1850759 := bstep (se 1 (by rfl) ⟨1388069, by rfl⟩ : syracuseStep 1850759 = 2776139) B2776139
theorem B2342459 : Blo 822348 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B1850939 : Blo 822348 1850939 := bstep (se 1 (by rfl) ⟨1388204, by rfl⟩ : syracuseStep 1850939 = 2776409) B2776409
theorem B1392187 : Blo 822348 1392187 := bstep (se 1 (by rfl) ⟨1044140, by rfl⟩ : syracuseStep 1392187 = 2088281) B2088281
theorem B1851065 : Blo 822348 1851065 := bstep (se 2 (by rfl) ⟨694149, by rfl⟩ : syracuseStep 1851065 = 1388299) B1388299
theorem B1392329 : Blo 822348 1392329 := bstep (se 2 (by rfl) ⟨522123, by rfl⟩ : syracuseStep 1392329 = 1044247) B1044247
theorem B4177817 : Blo 822348 4177817 := bstep (se 2 (by rfl) ⟨1566681, by rfl⟩ : syracuseStep 4177817 = 3133363) B3133363
theorem B4702211 : Blo 822348 4702211 := bstep (se 1 (by rfl) ⟨3526658, by rfl⟩ : syracuseStep 4702211 = 7053317) B7053317
theorem B1851407 : Blo 822348 1851407 := bstep (se 1 (by rfl) ⟨1388555, by rfl⟩ : syracuseStep 1851407 = 2777111) B2777111
theorem B1851425 : Blo 822348 1851425 := bstep (se 2 (by rfl) ⟨694284, by rfl⟩ : syracuseStep 1851425 = 1388569) B1388569
theorem B7913645 : Blo 822348 7913645 := bstep (se 3 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 7913645 = 2967617) B2967617
theorem B2343097 : Blo 822348 2343097 := bstep (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) B1757323
theorem B1851767 : Blo 822348 1851767 := bstep (se 1 (by rfl) ⟨1388825, by rfl⟩ : syracuseStep 1851767 = 2777651) B2777651
theorem B8470919 : Blo 822348 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B1393031 : Blo 822348 1393031 := bstep (se 1 (by rfl) ⟨1044773, by rfl⟩ : syracuseStep 1393031 = 2089547) B2089547
theorem B1982987 : Blo 822348 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B1851947 : Blo 822348 1851947 := bstep (se 1 (by rfl) ⟨1388960, by rfl⟩ : syracuseStep 1851947 = 2777921) B2777921
theorem B2343485 : Blo 822348 2343485 := bstep (se 3 (by rfl) ⟨439403, by rfl⟩ : syracuseStep 2343485 = 878807) B878807
theorem B3523463 : Blo 822348 3523463 := bstep (se 1 (by rfl) ⟨2642597, by rfl⟩ : syracuseStep 3523463 = 5285195) B5285195
theorem B1852307 : Blo 822348 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B3130265 : Blo 822348 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B4506553 : Blo 822348 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B1852361 : Blo 822348 1852361 := bstep (se 2 (by rfl) ⟨694635, by rfl⟩ : syracuseStep 1852361 = 1389271) B1389271
theorem B1393679 : Blo 822348 1393679 := bstep (se 1 (by rfl) ⟨1045259, by rfl⟩ : syracuseStep 1393679 = 2090519) B2090519
theorem B5358653 : Blo 822348 5358653 := bstep (se 3 (by rfl) ⟨1004747, by rfl⟩ : syracuseStep 5358653 = 2009495) B2009495
theorem B6669485 : Blo 822348 6669485 := bstep (se 3 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 6669485 = 2501057) B2501057
theorem B1787321 : Blo 822348 1787321 := bstep (se 2 (by rfl) ⟨670245, by rfl⟩ : syracuseStep 1787321 = 1340491) B1340491
theorem B1394219 : Blo 822348 1394219 := bstep (se 1 (by rfl) ⟨1045664, by rfl⟩ : syracuseStep 1394219 = 2091329) B2091329
theorem B2082419 : Blo 822348 2082419 := bstep (se 1 (by rfl) ⟨1561814, by rfl⟩ : syracuseStep 2082419 = 3123629) B3123629
theorem B1853063 : Blo 822348 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B2344601 : Blo 822348 2344601 := bstep (se 2 (by rfl) ⟨879225, by rfl⟩ : syracuseStep 2344601 = 1758451) B1758451
theorem B837383 : Blo 822348 837383 := bstep (se 1 (by rfl) ⟨628037, by rfl⟩ : syracuseStep 837383 = 1256075) B1256075
theorem B2967329 : Blo 822348 2967329 := bstep (se 2 (by rfl) ⟨1112748, by rfl⟩ : syracuseStep 2967329 = 2225497) B2225497
theorem B1853243 : Blo 822348 1853243 := bstep (se 1 (by rfl) ⟨1389932, by rfl⟩ : syracuseStep 1853243 = 2779865) B2779865
theorem B2639675 : Blo 822348 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B1984409 : Blo 822348 1984409 := bstep (se 2 (by rfl) ⟨744153, by rfl⟩ : syracuseStep 1984409 = 1488307) B1488307
theorem B1853369 : Blo 822348 1853369 := bstep (se 2 (by rfl) ⟨695013, by rfl⟩ : syracuseStep 1853369 = 1390027) B1390027
theorem B2082935 : Blo 822348 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B5294317 : Blo 822348 5294317 := bstep (se 3 (by rfl) ⟨992684, by rfl⟩ : syracuseStep 5294317 = 1985369) B1985369
theorem B1853711 : Blo 822348 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B1853729 : Blo 822348 1853729 := bstep (se 2 (by rfl) ⟨695148, by rfl⟩ : syracuseStep 1853729 = 1390297) B1390297
theorem B3524897 : Blo 822348 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B4704601 : Blo 822348 4704601 := bstep (se 2 (by rfl) ⟨1764225, by rfl⟩ : syracuseStep 4704601 = 3528451) B3528451
theorem B4180409 : Blo 822348 4180409 := bstep (se 2 (by rfl) ⟨1567653, by rfl⟩ : syracuseStep 4180409 = 3135307) B3135307
theorem B2116097 : Blo 822348 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B1854071 : Blo 822348 1854071 := bstep (se 1 (by rfl) ⟨1390553, by rfl⟩ : syracuseStep 1854071 = 2781107) B2781107
theorem B1854251 : Blo 822348 1854251 := bstep (se 1 (by rfl) ⟨1390688, by rfl⟩ : syracuseStep 1854251 = 2781377) B2781377
theorem B2346013 : Blo 822348 2346013 := bstep (se 3 (by rfl) ⟨439877, by rfl⟩ : syracuseStep 2346013 = 879755) B879755
theorem B2083927 : Blo 822348 2083927 := bstep (se 1 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 2083927 = 3125891) B3125891
theorem B1854611 : Blo 822348 1854611 := bstep (se 1 (by rfl) ⟨1390958, by rfl⟩ : syracuseStep 1854611 = 2781917) B2781917
theorem B2346185 : Blo 822348 2346185 := bstep (se 2 (by rfl) ⟨879819, by rfl⟩ : syracuseStep 2346185 = 1759639) B1759639
theorem B1854665 : Blo 822348 1854665 := bstep (se 2 (by rfl) ⟨695499, by rfl⟩ : syracuseStep 1854665 = 1390999) B1390999
theorem B2346241 : Blo 822348 2346241 := bstep (se 2 (by rfl) ⟨879840, by rfl⟩ : syracuseStep 2346241 = 1759681) B1759681
theorem B3525889 : Blo 822348 3525889 := bstep (se 2 (by rfl) ⟨1322208, by rfl⟩ : syracuseStep 3525889 = 2644417) B2644417
theorem B2084231 : Blo 822348 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B2084363 : Blo 822348 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B2346583 : Blo 822348 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B1003151 : Blo 822348 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B2117267 : Blo 822348 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B4181705 : Blo 822348 4181705 := bstep (se 2 (by rfl) ⟨1568139, by rfl⟩ : syracuseStep 4181705 = 3136279) B3136279
theorem B1855367 : Blo 822348 1855367 := bstep (se 1 (by rfl) ⟨1391525, by rfl⟩ : syracuseStep 1855367 = 2783051) B2783051
theorem B2084879 : Blo 822348 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B1855547 : Blo 822348 1855547 := bstep (se 1 (by rfl) ⟨1391660, by rfl⟩ : syracuseStep 1855547 = 2783321) B2783321
theorem B2085011 : Blo 822348 2085011 := bstep (se 1 (by rfl) ⟨1563758, by rfl⟩ : syracuseStep 2085011 = 3127517) B3127517
theorem B1855673 : Blo 822348 1855673 := bstep (se 2 (by rfl) ⟨695877, by rfl⟩ : syracuseStep 1855673 = 1391755) B1391755
theorem B2642291 : Blo 822348 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B3133849 : Blo 822348 3133849 := bstep (se 2 (by rfl) ⟨1175193, by rfl⟩ : syracuseStep 3133849 = 2350387) B2350387
theorem B2118089 : Blo 822348 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B2511371 : Blo 822348 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1856015 : Blo 822348 1856015 := bstep (se 1 (by rfl) ⟨1392011, by rfl⟩ : syracuseStep 1856015 = 2784023) B2784023
theorem B1856033 : Blo 822348 1856033 := bstep (se 2 (by rfl) ⟨696012, by rfl⟩ : syracuseStep 1856033 = 1392025) B1392025
theorem B1233527 : Blo 822348 1233527 := bstep (se 1 (by rfl) ⟨925145, by rfl⟩ : syracuseStep 1233527 = 1850291) B1850291
theorem B1561207 : Blo 822348 1561207 := bstep (se 1 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 1561207 = 2341811) B2341811
theorem B1233551 : Blo 822348 1233551 := bstep (se 1 (by rfl) ⟨925163, by rfl⟩ : syracuseStep 1233551 = 1850327) B1850327
theorem B1233593 : Blo 822348 1233593 := bstep (se 2 (by rfl) ⟨462597, by rfl⟩ : syracuseStep 1233593 = 925195) B925195
theorem B3134153 : Blo 822348 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B1233671 : Blo 822348 1233671 := bstep (se 1 (by rfl) ⟨925253, by rfl⟩ : syracuseStep 1233671 = 1850507) B1850507
theorem B1233707 : Blo 822348 1233707 := bstep (se 1 (by rfl) ⟨925280, by rfl⟩ : syracuseStep 1233707 = 1850561) B1850561
theorem B1233737 : Blo 822348 1233737 := bstep (se 2 (by rfl) ⟨462651, by rfl⟩ : syracuseStep 1233737 = 925303) B925303
theorem B1856375 : Blo 822348 1856375 := bstep (se 1 (by rfl) ⟨1392281, by rfl⟩ : syracuseStep 1856375 = 2784563) B2784563
theorem B4019129 : Blo 822348 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B1233851 : Blo 822348 1233851 := bstep (se 1 (by rfl) ⟨925388, by rfl⟩ : syracuseStep 1233851 = 1850777) B1850777
theorem B1233911 : Blo 822348 1233911 := bstep (se 1 (by rfl) ⟨925433, by rfl⟩ : syracuseStep 1233911 = 1850867) B1850867
theorem B10540043 : Blo 822348 10540043 := bstep (se 1 (by rfl) ⟨7905032, by rfl⟩ : syracuseStep 10540043 = 15810065) B15810065
theorem B1233935 : Blo 822348 1233935 := bstep (se 1 (by rfl) ⟨925451, by rfl⟩ : syracuseStep 1233935 = 1850903) B1850903
theorem B1856555 : Blo 822348 1856555 := bstep (se 1 (by rfl) ⟨1392416, by rfl⟩ : syracuseStep 1856555 = 2784833) B2784833
theorem B1233977 : Blo 822348 1233977 := bstep (se 2 (by rfl) ⟨462741, by rfl⟩ : syracuseStep 1233977 = 925483) B925483
theorem B25416791 : Blo 822348 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B1234055 : Blo 822348 1234055 := bstep (se 1 (by rfl) ⟨925541, by rfl⟩ : syracuseStep 1234055 = 1851083) B1851083
theorem B1234091 : Blo 822348 1234091 := bstep (se 1 (by rfl) ⟨925568, by rfl⟩ : syracuseStep 1234091 = 1851137) B1851137
theorem B1234121 : Blo 822348 1234121 := bstep (se 2 (by rfl) ⟨462795, by rfl⟩ : syracuseStep 1234121 = 925591) B925591
theorem B2086145 : Blo 822348 2086145 := bstep (se 2 (by rfl) ⟨782304, by rfl⟩ : syracuseStep 2086145 = 1564609) B1564609
theorem B1234235 : Blo 822348 1234235 := bstep (se 1 (by rfl) ⟨925676, by rfl⟩ : syracuseStep 1234235 = 1851353) B1851353
theorem B5363003 : Blo 822348 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B1234295 : Blo 822348 1234295 := bstep (se 1 (by rfl) ⟨925721, by rfl⟩ : syracuseStep 1234295 = 1851443) B1851443
theorem B3954055 : Blo 822348 3954055 := bstep (se 1 (by rfl) ⟨2965541, by rfl⟩ : syracuseStep 3954055 = 5931083) B5931083
theorem B1234319 : Blo 822348 1234319 := bstep (se 1 (by rfl) ⟨925739, by rfl⟩ : syracuseStep 1234319 = 1851479) B1851479
theorem B1856915 : Blo 822348 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B1234361 : Blo 822348 1234361 := bstep (se 2 (by rfl) ⟨462885, by rfl⟩ : syracuseStep 1234361 = 925771) B925771
theorem B1856969 : Blo 822348 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B1234439 : Blo 822348 1234439 := bstep (se 1 (by rfl) ⟨925829, by rfl⟩ : syracuseStep 1234439 = 1851659) B1851659
theorem B1234475 : Blo 822348 1234475 := bstep (se 1 (by rfl) ⟨925856, by rfl⟩ : syracuseStep 1234475 = 1851713) B1851713
theorem B1234505 : Blo 822348 1234505 := bstep (se 2 (by rfl) ⟨462939, by rfl⟩ : syracuseStep 1234505 = 925879) B925879
theorem B2086519 : Blo 822348 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B3135095 : Blo 822348 3135095 := bstep (se 1 (by rfl) ⟨2351321, by rfl⟩ : syracuseStep 3135095 = 4702643) B4702643
theorem B40195763 : Blo 822348 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1234619 : Blo 822348 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B7919333 : Blo 822348 7919333 := bstep (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) B1484875
theorem B9393893 : Blo 822348 9393893 := bstep (se 4 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 9393893 = 1761355) B1761355
theorem B1234679 : Blo 822348 1234679 := bstep (se 1 (by rfl) ⟨926009, by rfl⟩ : syracuseStep 1234679 = 1852019) B1852019
theorem B1234703 : Blo 822348 1234703 := bstep (se 1 (by rfl) ⟨926027, by rfl⟩ : syracuseStep 1234703 = 1852055) B1852055
theorem B1234745 : Blo 822348 1234745 := bstep (se 2 (by rfl) ⟨463029, by rfl⟩ : syracuseStep 1234745 = 926059) B926059
theorem B1234823 : Blo 822348 1234823 := bstep (se 1 (by rfl) ⟨926117, by rfl⟩ : syracuseStep 1234823 = 1852235) B1852235
theorem B1234859 : Blo 822348 1234859 := bstep (se 1 (by rfl) ⟨926144, by rfl⟩ : syracuseStep 1234859 = 1852289) B1852289
theorem B1234889 : Blo 822348 1234889 := bstep (se 2 (by rfl) ⟨463083, by rfl⟩ : syracuseStep 1234889 = 926167) B926167
theorem B2086955 : Blo 822348 2086955 := bstep (se 1 (by rfl) ⟨1565216, by rfl⟩ : syracuseStep 2086955 = 3130433) B3130433
theorem B1235003 : Blo 822348 1235003 := bstep (se 1 (by rfl) ⟨926252, by rfl⟩ : syracuseStep 1235003 = 1852505) B1852505
theorem B1235063 : Blo 822348 1235063 := bstep (se 1 (by rfl) ⟨926297, by rfl⟩ : syracuseStep 1235063 = 1852595) B1852595
theorem B1857671 : Blo 822348 1857671 := bstep (se 1 (by rfl) ⟨1393253, by rfl⟩ : syracuseStep 1857671 = 2786507) B2786507
theorem B1235087 : Blo 822348 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B1562809 : Blo 822348 1562809 := bstep (se 2 (by rfl) ⟨586053, by rfl⟩ : syracuseStep 1562809 = 1172107) B1172107
theorem B1235129 : Blo 822348 1235129 := bstep (se 2 (by rfl) ⟨463173, by rfl⟩ : syracuseStep 1235129 = 926347) B926347
theorem B1235207 : Blo 822348 1235207 := bstep (se 1 (by rfl) ⟨926405, by rfl⟩ : syracuseStep 1235207 = 1852811) B1852811
theorem B3954977 : Blo 822348 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B1235243 : Blo 822348 1235243 := bstep (se 1 (by rfl) ⟨926432, by rfl⟩ : syracuseStep 1235243 = 1852865) B1852865
theorem B1857851 : Blo 822348 1857851 := bstep (se 1 (by rfl) ⟨1393388, by rfl⟩ : syracuseStep 1857851 = 2786777) B2786777
theorem B1235273 : Blo 822348 1235273 := bstep (se 2 (by rfl) ⟨463227, by rfl⟩ : syracuseStep 1235273 = 926455) B926455
theorem B2349431 : Blo 822348 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B1005967 : Blo 822348 1005967 := bstep (se 1 (by rfl) ⟨754475, by rfl⟩ : syracuseStep 1005967 = 1508951) B1508951
theorem B1857977 : Blo 822348 1857977 := bstep (se 2 (by rfl) ⟨696741, by rfl⟩ : syracuseStep 1857977 = 1393483) B1393483
theorem B1235387 : Blo 822348 1235387 := bstep (se 1 (by rfl) ⟨926540, by rfl⟩ : syracuseStep 1235387 = 1853081) B1853081
theorem B4446667 : Blo 822348 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B1235447 : Blo 822348 1235447 := bstep (se 1 (by rfl) ⟨926585, by rfl⟩ : syracuseStep 1235447 = 1853171) B1853171
theorem B2120203 : Blo 822348 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B1563151 : Blo 822348 1563151 := bstep (se 1 (by rfl) ⟨1172363, by rfl⟩ : syracuseStep 1563151 = 2344727) B2344727
theorem B1235471 : Blo 822348 1235471 := bstep (se 1 (by rfl) ⟨926603, by rfl⟩ : syracuseStep 1235471 = 1853207) B1853207
theorem B2382365 : Blo 822348 2382365 := bstep (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) B893387
theorem B1235513 : Blo 822348 1235513 := bstep (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) B926635
theorem B3136067 : Blo 822348 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B1235591 : Blo 822348 1235591 := bstep (se 1 (by rfl) ⟨926693, by rfl⟩ : syracuseStep 1235591 = 1853387) B1853387
theorem B1235627 : Blo 822348 1235627 := bstep (se 1 (by rfl) ⟨926720, by rfl⟩ : syracuseStep 1235627 = 1853441) B1853441
theorem B1235657 : Blo 822348 1235657 := bstep (se 2 (by rfl) ⟨463371, by rfl⟩ : syracuseStep 1235657 = 926743) B926743
theorem B2644751 : Blo 822348 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B1858319 : Blo 822348 1858319 := bstep (se 1 (by rfl) ⟨1393739, by rfl⟩ : syracuseStep 1858319 = 2787479) B2787479
theorem B1858337 : Blo 822348 1858337 := bstep (se 2 (by rfl) ⟨696876, by rfl⟩ : syracuseStep 1858337 = 1393753) B1393753
theorem B8903459 : Blo 822348 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B1235771 : Blo 822348 1235771 := bstep (se 1 (by rfl) ⟨926828, by rfl⟩ : syracuseStep 1235771 = 1853657) B1853657
theorem B2775923 : Blo 822348 2775923 := bstep (se 1 (by rfl) ⟨2081942, by rfl⟩ : syracuseStep 2775923 = 4163885) B4163885
theorem B2087795 : Blo 822348 2087795 := bstep (se 1 (by rfl) ⟨1565846, by rfl⟩ : syracuseStep 2087795 = 3131693) B3131693
theorem B1235831 : Blo 822348 1235831 := bstep (se 1 (by rfl) ⟨926873, by rfl⟩ : syracuseStep 1235831 = 1853747) B1853747
theorem B2087815 : Blo 822348 2087815 := bstep (se 1 (by rfl) ⟨1565861, by rfl⟩ : syracuseStep 2087815 = 3131723) B3131723
theorem B1235855 : Blo 822348 1235855 := bstep (se 1 (by rfl) ⟨926891, by rfl⟩ : syracuseStep 1235855 = 1853783) B1853783
theorem B3562393 : Blo 822348 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B1235897 : Blo 822348 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B1235975 : Blo 822348 1235975 := bstep (se 1 (by rfl) ⟨926981, by rfl⟩ : syracuseStep 1235975 = 1853963) B1853963
theorem B1236011 : Blo 822348 1236011 := bstep (se 1 (by rfl) ⟨927008, by rfl⟩ : syracuseStep 1236011 = 1854017) B1854017
theorem B1236041 : Blo 822348 1236041 := bstep (se 2 (by rfl) ⟨463515, by rfl⟩ : syracuseStep 1236041 = 927031) B927031
theorem B1858679 : Blo 822348 1858679 := bstep (se 1 (by rfl) ⟨1394009, by rfl⟩ : syracuseStep 1858679 = 2788019) B2788019
theorem B2088089 : Blo 822348 2088089 := bstep (se 2 (by rfl) ⟨783033, by rfl⟩ : syracuseStep 2088089 = 1566067) B1566067
theorem B1236155 : Blo 822348 1236155 := bstep (se 1 (by rfl) ⟨927116, by rfl⟩ : syracuseStep 1236155 = 1854233) B1854233
theorem B1236215 : Blo 822348 1236215 := bstep (se 1 (by rfl) ⟨927161, by rfl⟩ : syracuseStep 1236215 = 1854323) B1854323
theorem B1236239 : Blo 822348 1236239 := bstep (se 1 (by rfl) ⟨927179, by rfl⟩ : syracuseStep 1236239 = 1854359) B1854359
theorem B1858859 : Blo 822348 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B1236281 : Blo 822348 1236281 := bstep (se 2 (by rfl) ⟨463605, by rfl⟩ : syracuseStep 1236281 = 927211) B927211
theorem B33840443 : Blo 822348 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B2088251 : Blo 822348 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B1564039 : Blo 822348 1564039 := bstep (se 1 (by rfl) ⟨1173029, by rfl⟩ : syracuseStep 1564039 = 2346059) B2346059
theorem B1236359 : Blo 822348 1236359 := bstep (se 1 (by rfl) ⟨927269, by rfl⟩ : syracuseStep 1236359 = 1854539) B1854539
theorem B1236395 : Blo 822348 1236395 := bstep (se 1 (by rfl) ⟨927296, by rfl⟩ : syracuseStep 1236395 = 1854593) B1854593
theorem B1236425 : Blo 822348 1236425 := bstep (se 2 (by rfl) ⟨463659, by rfl⟩ : syracuseStep 1236425 = 927319) B927319
theorem B2088463 : Blo 822348 2088463 := bstep (se 1 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 2088463 = 3132695) B3132695
theorem B1236539 : Blo 822348 1236539 := bstep (se 1 (by rfl) ⟨927404, by rfl⟩ : syracuseStep 1236539 = 1854809) B1854809
theorem B1236599 : Blo 822348 1236599 := bstep (se 1 (by rfl) ⟨927449, by rfl⟩ : syracuseStep 1236599 = 1854899) B1854899
theorem B1236623 : Blo 822348 1236623 := bstep (se 1 (by rfl) ⟨927467, by rfl⟩ : syracuseStep 1236623 = 1854935) B1854935
theorem B1859219 : Blo 822348 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B1236665 : Blo 822348 1236665 := bstep (se 2 (by rfl) ⟨463749, by rfl⟩ : syracuseStep 1236665 = 927499) B927499
theorem B1859273 : Blo 822348 1859273 := bstep (se 2 (by rfl) ⟨697227, by rfl⟩ : syracuseStep 1859273 = 1394455) B1394455
theorem B1171207 : Blo 822348 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B1236743 : Blo 822348 1236743 := bstep (se 1 (by rfl) ⟨927557, by rfl⟩ : syracuseStep 1236743 = 1855115) B1855115
theorem B2088737 : Blo 822348 2088737 := bstep (se 2 (by rfl) ⟨783276, by rfl⟩ : syracuseStep 2088737 = 1566553) B1566553
theorem B1236779 : Blo 822348 1236779 := bstep (se 1 (by rfl) ⟨927584, by rfl⟩ : syracuseStep 1236779 = 1855169) B1855169
theorem B4448051 : Blo 822348 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B1236809 : Blo 822348 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B3956633 : Blo 822348 3956633 := bstep (se 2 (by rfl) ⟨1483737, by rfl⟩ : syracuseStep 3956633 = 2967475) B2967475
theorem B1236923 : Blo 822348 1236923 := bstep (se 1 (by rfl) ⟨927692, by rfl⟩ : syracuseStep 1236923 = 1855385) B1855385
theorem B1236983 : Blo 822348 1236983 := bstep (se 1 (by rfl) ⟨927737, by rfl⟩ : syracuseStep 1236983 = 1855475) B1855475
theorem B1237007 : Blo 822348 1237007 := bstep (se 1 (by rfl) ⟨927755, by rfl⟩ : syracuseStep 1237007 = 1855511) B1855511
theorem B1237049 : Blo 822348 1237049 := bstep (se 2 (by rfl) ⟨463893, by rfl⟩ : syracuseStep 1237049 = 927787) B927787
theorem B1237127 : Blo 822348 1237127 := bstep (se 1 (by rfl) ⟨927845, by rfl⟩ : syracuseStep 1237127 = 1855691) B1855691
theorem B1237163 : Blo 822348 1237163 := bstep (se 1 (by rfl) ⟨927872, by rfl⟩ : syracuseStep 1237163 = 1855745) B1855745
theorem B1237193 : Blo 822348 1237193 := bstep (se 2 (by rfl) ⟨463947, by rfl⟩ : syracuseStep 1237193 = 927895) B927895
theorem B1237307 : Blo 822348 1237307 := bstep (se 1 (by rfl) ⟨927980, by rfl⟩ : syracuseStep 1237307 = 1855961) B1855961
theorem B1237367 : Blo 822348 1237367 := bstep (se 1 (by rfl) ⟨928025, by rfl⟩ : syracuseStep 1237367 = 1856051) B1856051
theorem B1237391 : Blo 822348 1237391 := bstep (se 1 (by rfl) ⟨928043, by rfl⟩ : syracuseStep 1237391 = 1856087) B1856087
theorem B1237433 : Blo 822348 1237433 := bstep (se 2 (by rfl) ⟨464037, by rfl⟩ : syracuseStep 1237433 = 928075) B928075
theorem B1171913 : Blo 822348 1171913 := bstep (se 2 (by rfl) ⟨439467, by rfl⟩ : syracuseStep 1171913 = 878935) B878935
theorem B1237511 : Blo 822348 1237511 := bstep (se 1 (by rfl) ⟨928133, by rfl⟩ : syracuseStep 1237511 = 1856267) B1856267
theorem B1237547 : Blo 822348 1237547 := bstep (se 1 (by rfl) ⟨928160, by rfl⟩ : syracuseStep 1237547 = 1856321) B1856321
theorem B1172027 : Blo 822348 1172027 := bstep (se 1 (by rfl) ⟨879020, by rfl⟩ : syracuseStep 1172027 = 1758041) B1758041
theorem B1761851 : Blo 822348 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1237577 : Blo 822348 1237577 := bstep (se 2 (by rfl) ⟨464091, by rfl⟩ : syracuseStep 1237577 = 928183) B928183
theorem B2646647 : Blo 822348 2646647 := bstep (se 1 (by rfl) ⟨1984985, by rfl⟩ : syracuseStep 2646647 = 3969971) B3969971
theorem B1237691 : Blo 822348 1237691 := bstep (se 1 (by rfl) ⟨928268, by rfl⟩ : syracuseStep 1237691 = 1856537) B1856537
theorem B1237751 : Blo 822348 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B2089739 : Blo 822348 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B1237775 : Blo 822348 1237775 := bstep (se 1 (by rfl) ⟨928331, by rfl⟩ : syracuseStep 1237775 = 1856663) B1856663
theorem B1237817 : Blo 822348 1237817 := bstep (se 2 (by rfl) ⟨464181, by rfl⟩ : syracuseStep 1237817 = 928363) B928363
theorem B1237895 : Blo 822348 1237895 := bstep (se 1 (by rfl) ⟨928421, by rfl⟩ : syracuseStep 1237895 = 1856843) B1856843
theorem B6251417 : Blo 822348 6251417 := bstep (se 2 (by rfl) ⟨2344281, by rfl⟩ : syracuseStep 6251417 = 4688563) B4688563
theorem B1237931 : Blo 822348 1237931 := bstep (se 1 (by rfl) ⟨928448, by rfl⟩ : syracuseStep 1237931 = 1856897) B1856897
theorem B1237961 : Blo 822348 1237961 := bstep (se 2 (by rfl) ⟨464235, by rfl⟩ : syracuseStep 1237961 = 928471) B928471
theorem B2352073 : Blo 822348 2352073 := bstep (se 2 (by rfl) ⟨882027, by rfl⟩ : syracuseStep 2352073 = 1764055) B1764055
theorem B1238075 : Blo 822348 1238075 := bstep (se 1 (by rfl) ⟨928556, by rfl⟩ : syracuseStep 1238075 = 1857113) B1857113
theorem B1238135 : Blo 822348 1238135 := bstep (se 1 (by rfl) ⟨928601, by rfl⟩ : syracuseStep 1238135 = 1857203) B1857203
theorem B1565831 : Blo 822348 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B1238159 : Blo 822348 1238159 := bstep (se 1 (by rfl) ⟨928619, by rfl⟩ : syracuseStep 1238159 = 1857239) B1857239
theorem B1172665 : Blo 822348 1172665 := bstep (se 2 (by rfl) ⟨439749, by rfl⟩ : syracuseStep 1172665 = 879499) B879499
theorem B1238201 : Blo 822348 1238201 := bstep (se 2 (by rfl) ⟨464325, by rfl⟩ : syracuseStep 1238201 = 928651) B928651
theorem B1041655 : Blo 822348 1041655 := bstep (se 1 (by rfl) ⟨781241, by rfl⟩ : syracuseStep 1041655 = 1562483) B1562483
theorem B1238279 : Blo 822348 1238279 := bstep (se 1 (by rfl) ⟨928709, by rfl⟩ : syracuseStep 1238279 = 1857419) B1857419
theorem B1238315 : Blo 822348 1238315 := bstep (se 1 (by rfl) ⟨928736, by rfl⟩ : syracuseStep 1238315 = 1857473) B1857473
theorem B1238345 : Blo 822348 1238345 := bstep (se 2 (by rfl) ⟨464379, by rfl⟩ : syracuseStep 1238345 = 928759) B928759
theorem B2778515 : Blo 822348 2778515 := bstep (se 1 (by rfl) ⟨2083886, by rfl⟩ : syracuseStep 2778515 = 4167773) B4167773
theorem B2090387 : Blo 822348 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B15820211 : Blo 822348 15820211 := bstep (se 1 (by rfl) ⟨11865158, by rfl⟩ : syracuseStep 15820211 = 23730317) B23730317
theorem B1238459 : Blo 822348 1238459 := bstep (se 1 (by rfl) ⟨928844, by rfl⟩ : syracuseStep 1238459 = 1857689) B1857689
theorem B4220369 : Blo 822348 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B1238519 : Blo 822348 1238519 := bstep (se 1 (by rfl) ⟨928889, by rfl⟩ : syracuseStep 1238519 = 1857779) B1857779
theorem B3958283 : Blo 822348 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B1238543 : Blo 822348 1238543 := bstep (se 1 (by rfl) ⟨928907, by rfl⟩ : syracuseStep 1238543 = 1857815) B1857815
theorem B1762859 : Blo 822348 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B1238585 : Blo 822348 1238585 := bstep (se 2 (by rfl) ⟨464469, by rfl⟩ : syracuseStep 1238585 = 928939) B928939
theorem B1041979 : Blo 822348 1041979 := bstep (se 1 (by rfl) ⟨781484, by rfl⟩ : syracuseStep 1041979 = 1562969) B1562969
theorem B1238663 : Blo 822348 1238663 := bstep (se 1 (by rfl) ⟨928997, by rfl⟩ : syracuseStep 1238663 = 1857995) B1857995
theorem B1238699 : Blo 822348 1238699 := bstep (se 1 (by rfl) ⟨929024, by rfl⟩ : syracuseStep 1238699 = 1858049) B1858049
theorem B2090681 : Blo 822348 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B1238729 : Blo 822348 1238729 := bstep (se 2 (by rfl) ⟨464523, by rfl⟩ : syracuseStep 1238729 = 929047) B929047
theorem B1238843 : Blo 822348 1238843 := bstep (se 1 (by rfl) ⟨929132, by rfl⟩ : syracuseStep 1238843 = 1858265) B1858265
theorem B1238903 : Blo 822348 1238903 := bstep (se 1 (by rfl) ⟨929177, by rfl⟩ : syracuseStep 1238903 = 1858355) B1858355
theorem B1238927 : Blo 822348 1238927 := bstep (se 1 (by rfl) ⟨929195, by rfl⟩ : syracuseStep 1238927 = 1858391) B1858391
theorem B1238969 : Blo 822348 1238969 := bstep (se 2 (by rfl) ⟨464613, by rfl⟩ : syracuseStep 1238969 = 929227) B929227
theorem B1239047 : Blo 822348 1239047 := bstep (se 1 (by rfl) ⟨929285, by rfl⟩ : syracuseStep 1239047 = 1858571) B1858571
theorem B1239083 : Blo 822348 1239083 := bstep (se 1 (by rfl) ⟨929312, by rfl⟩ : syracuseStep 1239083 = 1858625) B1858625
theorem B1239113 : Blo 822348 1239113 := bstep (se 2 (by rfl) ⟨464667, by rfl⟩ : syracuseStep 1239113 = 929335) B929335
theorem B1239227 : Blo 822348 1239227 := bstep (se 1 (by rfl) ⟨929420, by rfl⟩ : syracuseStep 1239227 = 1858841) B1858841
theorem B1239287 : Blo 822348 1239287 := bstep (se 1 (by rfl) ⟨929465, by rfl⟩ : syracuseStep 1239287 = 1858931) B1858931
theorem B1239311 : Blo 822348 1239311 := bstep (se 1 (by rfl) ⟨929483, by rfl⟩ : syracuseStep 1239311 = 1858967) B1858967
theorem B1239353 : Blo 822348 1239353 := bstep (se 2 (by rfl) ⟨464757, by rfl⟩ : syracuseStep 1239353 = 929515) B929515
theorem B2091379 : Blo 822348 2091379 := bstep (se 1 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 2091379 = 3137069) B3137069
theorem B1239431 : Blo 822348 1239431 := bstep (se 1 (by rfl) ⟨929573, by rfl⟩ : syracuseStep 1239431 = 1859147) B1859147
theorem B1239467 : Blo 822348 1239467 := bstep (se 1 (by rfl) ⟨929600, by rfl⟩ : syracuseStep 1239467 = 1859201) B1859201
theorem B1239497 : Blo 822348 1239497 := bstep (se 2 (by rfl) ⟨464811, by rfl⟩ : syracuseStep 1239497 = 929623) B929623
theorem B2091521 : Blo 822348 2091521 := bstep (se 2 (by rfl) ⟨784320, by rfl⟩ : syracuseStep 2091521 = 1568641) B1568641
theorem B1042951 : Blo 822348 1042951 := bstep (se 1 (by rfl) ⟨782213, by rfl⟩ : syracuseStep 1042951 = 1564427) B1564427
theorem B2779919 : Blo 822348 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B6253361 : Blo 822348 6253361 := bstep (se 2 (by rfl) ⟨2345010, by rfl⟩ : syracuseStep 6253361 = 4690021) B4690021
theorem B1043371 : Blo 822348 1043371 := bstep (se 1 (by rfl) ⟨782528, by rfl⟩ : syracuseStep 1043371 = 1565057) B1565057
theorem B2780189 : Blo 822348 2780189 := bstep (se 3 (by rfl) ⟨521285, by rfl⟩ : syracuseStep 2780189 = 1042571) B1042571
theorem B879751 : Blo 822348 879751 := bstep (se 1 (by rfl) ⟨659813, by rfl⟩ : syracuseStep 879751 = 1319627) B1319627
theorem B1043599 : Blo 822348 1043599 := bstep (se 1 (by rfl) ⟨782699, by rfl⟩ : syracuseStep 1043599 = 1565399) B1565399
theorem B1764499 : Blo 822348 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B3337453 : Blo 822348 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B15232387 : Blo 822348 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B15822215 : Blo 822348 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B10579409 : Blo 822348 10579409 := bstep (se 2 (by rfl) ⟨3967278, by rfl⟩ : syracuseStep 10579409 = 7934557) B7934557
theorem B3960323 : Blo 822348 3960323 := bstep (se 1 (by rfl) ⟨2970242, by rfl⟩ : syracuseStep 3960323 = 5940485) B5940485
theorem B1568315 : Blo 822348 1568315 := bstep (se 1 (by rfl) ⟨1176236, by rfl⟩ : syracuseStep 1568315 = 2352473) B2352473
theorem B8449601 : Blo 822348 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B1208137 : Blo 822348 1208137 := bstep (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) B906103
theorem B4452185 : Blo 822348 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B1044343 : Blo 822348 1044343 := bstep (se 1 (by rfl) ⟨783257, by rfl⟩ : syracuseStep 1044343 = 1566515) B1566515
theorem B1175467 : Blo 822348 1175467 := bstep (se 1 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 1175467 = 1763201) B1763201
theorem B4222979 : Blo 822348 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B1044667 : Blo 822348 1044667 := bstep (se 1 (by rfl) ⟨783500, by rfl⟩ : syracuseStep 1044667 = 1567001) B1567001
theorem B2781593 : Blo 822348 2781593 := bstep (se 2 (by rfl) ⟨1043097, by rfl⟩ : syracuseStep 2781593 = 2086195) B2086195
theorem B2224655 : Blo 822348 2224655 := bstep (se 1 (by rfl) ⟨1668491, by rfl⟩ : syracuseStep 2224655 = 3336983) B3336983
theorem B1045163 : Blo 822348 1045163 := bstep (se 1 (by rfl) ⟨783872, by rfl⟩ : syracuseStep 1045163 = 1567745) B1567745
theorem B1340345 : Blo 822348 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B1504289 : Blo 822348 1504289 := bstep (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) B1128217
theorem B2782295 : Blo 822348 2782295 := bstep (se 1 (by rfl) ⟨2086721, by rfl⟩ : syracuseStep 2782295 = 4173443) B4173443
theorem B8909941 : Blo 822348 8909941 := bstep (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) B835307
theorem B1045639 : Blo 822348 1045639 := bstep (se 1 (by rfl) ⟨784229, by rfl⟩ : syracuseStep 1045639 = 1568459) B1568459
theorem B5928173 : Blo 822348 5928173 := bstep (se 3 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 5928173 = 2223065) B2223065
theorem B7533971 : Blo 822348 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B3962321 : Blo 822348 3962321 := bstep (se 2 (by rfl) ⟨1485870, by rfl⟩ : syracuseStep 3962321 = 2971741) B2971741
theorem B2782781 : Blo 822348 2782781 := bstep (se 3 (by rfl) ⟨521771, by rfl⟩ : syracuseStep 2782781 = 1043543) B1043543
theorem B1406735 : Blo 822348 1406735 := bstep (se 1 (by rfl) ⟨1055051, by rfl⟩ : syracuseStep 1406735 = 2110103) B2110103
theorem B5011237 : Blo 822348 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B4454279 : Blo 822348 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B9402641 : Blo 822348 9402641 := bstep (se 2 (by rfl) ⟨3525990, by rfl⟩ : syracuseStep 9402641 = 7051981) B7051981
theorem B1505911 : Blo 822348 1505911 := bstep (se 1 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 1505911 = 2258867) B2258867
theorem B2784185 : Blo 822348 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B1604623 : Blo 822348 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B1506319 : Blo 822348 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B5930273 : Blo 822348 5930273 := bstep (se 2 (by rfl) ⟨2223852, by rfl⟩ : syracuseStep 5930273 = 4447705) B4447705
theorem B1670519 : Blo 822348 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B2784779 : Blo 822348 2784779 := bstep (se 1 (by rfl) ⟨2088584, by rfl⟩ : syracuseStep 2784779 = 4177169) B4177169
theorem B2784887 : Blo 822348 2784887 := bstep (se 1 (by rfl) ⟨2088665, by rfl⟩ : syracuseStep 2784887 = 4177331) B4177331
theorem B1113787 : Blo 822348 1113787 := bstep (se 1 (by rfl) ⟨835340, by rfl⟩ : syracuseStep 1113787 = 1670681) B1670681
theorem B20086501 : Blo 822348 20086501 := bstep (se 4 (by rfl) ⟨1883109, by rfl⟩ : syracuseStep 20086501 = 3766219) B3766219
theorem B4456529 : Blo 822348 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B5275763 : Blo 822348 5275763 := bstep (se 1 (by rfl) ⟨3956822, by rfl⟩ : syracuseStep 5275763 = 7913645) B7913645
theorem B6684929 : Blo 822348 6684929 := bstep (se 2 (by rfl) ⟨2506848, by rfl⟩ : syracuseStep 6684929 = 5013697) B5013697
theorem B3572435 : Blo 822348 3572435 := bstep (se 1 (by rfl) ⟨2679326, by rfl⟩ : syracuseStep 3572435 = 5358653) B5358653
theorem B15828209 : Blo 822348 15828209 := bstep (se 2 (by rfl) ⟨5935578, by rfl⟩ : syracuseStep 15828209 = 11871157) B11871157
theorem B2786939 : Blo 822348 2786939 := bstep (se 1 (by rfl) ⟨2090204, by rfl⟩ : syracuseStep 2786939 = 4180409) B4180409
theorem B1410731 : Blo 822348 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B2787101 : Blo 822348 2787101 := bstep (se 3 (by rfl) ⟨522581, by rfl⟩ : syracuseStep 2787101 = 1045163) B1045163
theorem B15075233 : Blo 822348 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B1411511 : Blo 822348 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B2787803 : Blo 822348 2787803 := bstep (se 1 (by rfl) ⟨2090852, by rfl⟩ : syracuseStep 2787803 = 4181705) B4181705
theorem B3574253 : Blo 822348 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B7047881 : Blo 822348 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B1674247 : Blo 822348 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B822351 : Blo 822348 822351 := bstep (se 1 (by rfl) ⟨616763, by rfl⟩ : syracuseStep 822351 = 1233527) B1233527
theorem B822367 : Blo 822348 822367 := bstep (se 1 (by rfl) ⟨616775, by rfl⟩ : syracuseStep 822367 = 1233551) B1233551
theorem B3017843 : Blo 822348 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B822395 : Blo 822348 822395 := bstep (se 1 (by rfl) ⟨616796, by rfl⟩ : syracuseStep 822395 = 1233593) B1233593
theorem B2788505 : Blo 822348 2788505 := bstep (se 2 (by rfl) ⟨1045689, by rfl⟩ : syracuseStep 2788505 = 2091379) B2091379
theorem B822447 : Blo 822348 822447 := bstep (se 1 (by rfl) ⟨616835, by rfl⟩ : syracuseStep 822447 = 1233671) B1233671
theorem B822471 : Blo 822348 822471 := bstep (se 1 (by rfl) ⟨616853, by rfl⟩ : syracuseStep 822471 = 1233707) B1233707
theorem B822491 : Blo 822348 822491 := bstep (se 1 (by rfl) ⟨616868, by rfl⟩ : syracuseStep 822491 = 1233737) B1233737
theorem B822567 : Blo 822348 822567 := bstep (se 1 (by rfl) ⟨616925, by rfl⟩ : syracuseStep 822567 = 1233851) B1233851
theorem B822607 : Blo 822348 822607 := bstep (se 1 (by rfl) ⟨616955, by rfl⟩ : syracuseStep 822607 = 1233911) B1233911
theorem B822623 : Blo 822348 822623 := bstep (se 1 (by rfl) ⟨616967, by rfl⟩ : syracuseStep 822623 = 1233935) B1233935
theorem B822651 : Blo 822348 822651 := bstep (se 1 (by rfl) ⟨616988, by rfl⟩ : syracuseStep 822651 = 1233977) B1233977
theorem B16944527 : Blo 822348 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B6688165 : Blo 822348 6688165 := bstep (se 4 (by rfl) ⟨627015, by rfl⟩ : syracuseStep 6688165 = 1254031) B1254031
theorem B822703 : Blo 822348 822703 := bstep (se 1 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 822703 = 1234055) B1234055
theorem B822727 : Blo 822348 822727 := bstep (se 1 (by rfl) ⟨617045, by rfl⟩ : syracuseStep 822727 = 1234091) B1234091
theorem B822747 : Blo 822348 822747 := bstep (se 1 (by rfl) ⟨617060, by rfl⟩ : syracuseStep 822747 = 1234121) B1234121
theorem B822823 : Blo 822348 822823 := bstep (se 1 (by rfl) ⟨617117, by rfl⟩ : syracuseStep 822823 = 1234235) B1234235
theorem B3575335 : Blo 822348 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B822863 : Blo 822348 822863 := bstep (se 1 (by rfl) ⟨617147, by rfl⟩ : syracuseStep 822863 = 1234295) B1234295
theorem B822879 : Blo 822348 822879 := bstep (se 1 (by rfl) ⟨617159, by rfl⟩ : syracuseStep 822879 = 1234319) B1234319
theorem B822907 : Blo 822348 822907 := bstep (se 1 (by rfl) ⟨617180, by rfl⟩ : syracuseStep 822907 = 1234361) B1234361
theorem B822959 : Blo 822348 822959 := bstep (se 1 (by rfl) ⟨617219, by rfl⟩ : syracuseStep 822959 = 1234439) B1234439
theorem B822983 : Blo 822348 822983 := bstep (se 1 (by rfl) ⟨617237, by rfl⟩ : syracuseStep 822983 = 1234475) B1234475
theorem B823003 : Blo 822348 823003 := bstep (se 1 (by rfl) ⟨617252, by rfl⟩ : syracuseStep 823003 = 1234505) B1234505
theorem B823079 : Blo 822348 823079 := bstep (se 1 (by rfl) ⟨617309, by rfl⟩ : syracuseStep 823079 = 1234619) B1234619
theorem B5279555 : Blo 822348 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B6262595 : Blo 822348 6262595 := bstep (se 1 (by rfl) ⟨4696946, by rfl⟩ : syracuseStep 6262595 = 9393893) B9393893
theorem B823119 : Blo 822348 823119 := bstep (se 1 (by rfl) ⟨617339, by rfl⟩ : syracuseStep 823119 = 1234679) B1234679
theorem B823135 : Blo 822348 823135 := bstep (se 1 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 823135 = 1234703) B1234703
theorem B823163 : Blo 822348 823163 := bstep (se 1 (by rfl) ⟨617372, by rfl⟩ : syracuseStep 823163 = 1234745) B1234745
theorem B823215 : Blo 822348 823215 := bstep (se 1 (by rfl) ⟨617411, by rfl⟩ : syracuseStep 823215 = 1234823) B1234823
theorem B823239 : Blo 822348 823239 := bstep (se 1 (by rfl) ⟨617429, by rfl⟩ : syracuseStep 823239 = 1234859) B1234859
theorem B823259 : Blo 822348 823259 := bstep (se 1 (by rfl) ⟨617444, by rfl⟩ : syracuseStep 823259 = 1234889) B1234889
theorem B823335 : Blo 822348 823335 := bstep (se 1 (by rfl) ⟨617501, by rfl⟩ : syracuseStep 823335 = 1235003) B1235003
theorem B823375 : Blo 822348 823375 := bstep (se 1 (by rfl) ⟨617531, by rfl⟩ : syracuseStep 823375 = 1235063) B1235063
theorem B823391 : Blo 822348 823391 := bstep (se 1 (by rfl) ⟨617543, by rfl⟩ : syracuseStep 823391 = 1235087) B1235087
theorem B823419 : Blo 822348 823419 := bstep (se 1 (by rfl) ⟨617564, by rfl⟩ : syracuseStep 823419 = 1235129) B1235129
theorem B823471 : Blo 822348 823471 := bstep (se 1 (by rfl) ⟨617603, by rfl⟩ : syracuseStep 823471 = 1235207) B1235207
theorem B823495 : Blo 822348 823495 := bstep (se 1 (by rfl) ⟨617621, by rfl⟩ : syracuseStep 823495 = 1235243) B1235243
theorem B823515 : Blo 822348 823515 := bstep (se 1 (by rfl) ⟨617636, by rfl⟩ : syracuseStep 823515 = 1235273) B1235273
theorem B823591 : Blo 822348 823591 := bstep (se 1 (by rfl) ⟨617693, by rfl⟩ : syracuseStep 823591 = 1235387) B1235387
theorem B823631 : Blo 822348 823631 := bstep (se 1 (by rfl) ⟨617723, by rfl⟩ : syracuseStep 823631 = 1235447) B1235447
theorem B823647 : Blo 822348 823647 := bstep (se 1 (by rfl) ⟨617735, by rfl⟩ : syracuseStep 823647 = 1235471) B1235471
theorem B823675 : Blo 822348 823675 := bstep (se 1 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 823675 = 1235513) B1235513
theorem B823727 : Blo 822348 823727 := bstep (se 1 (by rfl) ⟨617795, by rfl⟩ : syracuseStep 823727 = 1235591) B1235591
theorem B823751 : Blo 822348 823751 := bstep (se 1 (by rfl) ⟨617813, by rfl⟩ : syracuseStep 823751 = 1235627) B1235627
theorem B823771 : Blo 822348 823771 := bstep (se 1 (by rfl) ⟨617828, by rfl⟩ : syracuseStep 823771 = 1235657) B1235657
theorem B4166153 : Blo 822348 4166153 := bstep (se 2 (by rfl) ⟨1562307, by rfl⟩ : syracuseStep 4166153 = 3124615) B3124615
theorem B5935639 : Blo 822348 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B823847 : Blo 822348 823847 := bstep (se 1 (by rfl) ⟨617885, by rfl⟩ : syracuseStep 823847 = 1235771) B1235771
theorem B4461115 : Blo 822348 4461115 := bstep (se 1 (by rfl) ⟨3345836, by rfl⟩ : syracuseStep 4461115 = 6691673) B6691673
theorem B823887 : Blo 822348 823887 := bstep (se 1 (by rfl) ⟨617915, by rfl⟩ : syracuseStep 823887 = 1235831) B1235831
theorem B823903 : Blo 822348 823903 := bstep (se 1 (by rfl) ⟨617927, by rfl⟩ : syracuseStep 823903 = 1235855) B1235855
theorem B823931 : Blo 822348 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B823983 : Blo 822348 823983 := bstep (se 1 (by rfl) ⟨617987, by rfl⟩ : syracuseStep 823983 = 1235975) B1235975
theorem B824007 : Blo 822348 824007 := bstep (se 1 (by rfl) ⟨618005, by rfl⟩ : syracuseStep 824007 = 1236011) B1236011
theorem B824027 : Blo 822348 824027 := bstep (se 1 (by rfl) ⟨618020, by rfl⟩ : syracuseStep 824027 = 1236041) B1236041
theorem B824103 : Blo 822348 824103 := bstep (se 1 (by rfl) ⟨618077, by rfl⟩ : syracuseStep 824103 = 1236155) B1236155
theorem B824143 : Blo 822348 824143 := bstep (se 1 (by rfl) ⟨618107, by rfl⟩ : syracuseStep 824143 = 1236215) B1236215
theorem B824159 : Blo 822348 824159 := bstep (se 1 (by rfl) ⟨618119, by rfl⟩ : syracuseStep 824159 = 1236239) B1236239
theorem B4461419 : Blo 822348 4461419 := bstep (se 1 (by rfl) ⟨3346064, by rfl⟩ : syracuseStep 4461419 = 6692129) B6692129
theorem B824187 : Blo 822348 824187 := bstep (se 1 (by rfl) ⟨618140, by rfl⟩ : syracuseStep 824187 = 1236281) B1236281
theorem B824239 : Blo 822348 824239 := bstep (se 1 (by rfl) ⟨618179, by rfl⟩ : syracuseStep 824239 = 1236359) B1236359
theorem B824263 : Blo 822348 824263 := bstep (se 1 (by rfl) ⟨618197, by rfl⟩ : syracuseStep 824263 = 1236395) B1236395
theorem B824283 : Blo 822348 824283 := bstep (se 1 (by rfl) ⟨618212, by rfl⟩ : syracuseStep 824283 = 1236425) B1236425
theorem B824359 : Blo 822348 824359 := bstep (se 1 (by rfl) ⟨618269, by rfl⟩ : syracuseStep 824359 = 1236539) B1236539
theorem B824399 : Blo 822348 824399 := bstep (se 1 (by rfl) ⟨618299, by rfl⟩ : syracuseStep 824399 = 1236599) B1236599
theorem B824415 : Blo 822348 824415 := bstep (se 1 (by rfl) ⟨618311, by rfl⟩ : syracuseStep 824415 = 1236623) B1236623
theorem B1610849 : Blo 822348 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B824443 : Blo 822348 824443 := bstep (se 1 (by rfl) ⟨618332, by rfl⟩ : syracuseStep 824443 = 1236665) B1236665
theorem B824495 : Blo 822348 824495 := bstep (se 1 (by rfl) ⟨618371, by rfl⟩ : syracuseStep 824495 = 1236743) B1236743
theorem B824519 : Blo 822348 824519 := bstep (se 1 (by rfl) ⟨618389, by rfl⟩ : syracuseStep 824519 = 1236779) B1236779
theorem B824539 : Blo 822348 824539 := bstep (se 1 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 824539 = 1236809) B1236809
theorem B824615 : Blo 822348 824615 := bstep (se 1 (by rfl) ⟨618461, by rfl⟩ : syracuseStep 824615 = 1236923) B1236923
theorem B824655 : Blo 822348 824655 := bstep (se 1 (by rfl) ⟨618491, by rfl⟩ : syracuseStep 824655 = 1236983) B1236983
theorem B824671 : Blo 822348 824671 := bstep (se 1 (by rfl) ⟨618503, by rfl⟩ : syracuseStep 824671 = 1237007) B1237007
theorem B824699 : Blo 822348 824699 := bstep (se 1 (by rfl) ⟨618524, by rfl⟩ : syracuseStep 824699 = 1237049) B1237049
theorem B8033701 : Blo 822348 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B988591 : Blo 822348 988591 := bstep (se 1 (by rfl) ⟨741443, by rfl⟩ : syracuseStep 988591 = 1482887) B1482887
theorem B824751 : Blo 822348 824751 := bstep (se 1 (by rfl) ⟨618563, by rfl⟩ : syracuseStep 824751 = 1237127) B1237127
theorem B824775 : Blo 822348 824775 := bstep (se 1 (by rfl) ⟨618581, by rfl⟩ : syracuseStep 824775 = 1237163) B1237163
theorem B824795 : Blo 822348 824795 := bstep (se 1 (by rfl) ⟨618596, by rfl⟩ : syracuseStep 824795 = 1237193) B1237193
theorem B824871 : Blo 822348 824871 := bstep (se 1 (by rfl) ⟨618653, by rfl⟩ : syracuseStep 824871 = 1237307) B1237307
theorem B824911 : Blo 822348 824911 := bstep (se 1 (by rfl) ⟨618683, by rfl⟩ : syracuseStep 824911 = 1237367) B1237367
theorem B824927 : Blo 822348 824927 := bstep (se 1 (by rfl) ⟨618695, by rfl⟩ : syracuseStep 824927 = 1237391) B1237391
theorem B824955 : Blo 822348 824955 := bstep (se 1 (by rfl) ⟨618716, by rfl⟩ : syracuseStep 824955 = 1237433) B1237433
theorem B825007 : Blo 822348 825007 := bstep (se 1 (by rfl) ⟨618755, by rfl⟩ : syracuseStep 825007 = 1237511) B1237511
theorem B825031 : Blo 822348 825031 := bstep (se 1 (by rfl) ⟨618773, by rfl⟩ : syracuseStep 825031 = 1237547) B1237547
theorem B825051 : Blo 822348 825051 := bstep (se 1 (by rfl) ⟨618788, by rfl⟩ : syracuseStep 825051 = 1237577) B1237577
theorem B825127 : Blo 822348 825127 := bstep (se 1 (by rfl) ⟨618845, by rfl⟩ : syracuseStep 825127 = 1237691) B1237691
theorem B825167 : Blo 822348 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B825183 : Blo 822348 825183 := bstep (se 1 (by rfl) ⟨618887, by rfl⟩ : syracuseStep 825183 = 1237775) B1237775
theorem B825211 : Blo 822348 825211 := bstep (se 1 (by rfl) ⟨618908, by rfl⟩ : syracuseStep 825211 = 1237817) B1237817
theorem B825263 : Blo 822348 825263 := bstep (se 1 (by rfl) ⟨618947, by rfl⟩ : syracuseStep 825263 = 1237895) B1237895
theorem B4167611 : Blo 822348 4167611 := bstep (se 1 (by rfl) ⟨3125708, by rfl⟩ : syracuseStep 4167611 = 6251417) B6251417
theorem B825287 : Blo 822348 825287 := bstep (se 1 (by rfl) ⟨618965, by rfl⟩ : syracuseStep 825287 = 1237931) B1237931
theorem B825307 : Blo 822348 825307 := bstep (se 1 (by rfl) ⟨618980, by rfl⟩ : syracuseStep 825307 = 1237961) B1237961
theorem B4692005 : Blo 822348 4692005 := bstep (se 4 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 4692005 = 879751) B879751
theorem B825383 : Blo 822348 825383 := bstep (se 1 (by rfl) ⟨619037, by rfl⟩ : syracuseStep 825383 = 1238075) B1238075
theorem B825423 : Blo 822348 825423 := bstep (se 1 (by rfl) ⟨619067, by rfl⟩ : syracuseStep 825423 = 1238135) B1238135
theorem B825439 : Blo 822348 825439 := bstep (se 1 (by rfl) ⟨619079, by rfl⟩ : syracuseStep 825439 = 1238159) B1238159
theorem B825467 : Blo 822348 825467 := bstep (se 1 (by rfl) ⟨619100, by rfl⟩ : syracuseStep 825467 = 1238201) B1238201
theorem B825519 : Blo 822348 825519 := bstep (se 1 (by rfl) ⟨619139, by rfl⟩ : syracuseStep 825519 = 1238279) B1238279
theorem B825543 : Blo 822348 825543 := bstep (se 1 (by rfl) ⟨619157, by rfl⟩ : syracuseStep 825543 = 1238315) B1238315
theorem B825563 : Blo 822348 825563 := bstep (se 1 (by rfl) ⟨619172, by rfl⟩ : syracuseStep 825563 = 1238345) B1238345
theorem B825639 : Blo 822348 825639 := bstep (se 1 (by rfl) ⟨619229, by rfl⟩ : syracuseStep 825639 = 1238459) B1238459
theorem B825679 : Blo 822348 825679 := bstep (se 1 (by rfl) ⟨619259, by rfl⟩ : syracuseStep 825679 = 1238519) B1238519
theorem B825695 : Blo 822348 825695 := bstep (se 1 (by rfl) ⟨619271, by rfl⟩ : syracuseStep 825695 = 1238543) B1238543
theorem B825723 : Blo 822348 825723 := bstep (se 1 (by rfl) ⟨619292, by rfl⟩ : syracuseStep 825723 = 1238585) B1238585
theorem B825775 : Blo 822348 825775 := bstep (se 1 (by rfl) ⟨619331, by rfl⟩ : syracuseStep 825775 = 1238663) B1238663
theorem B825799 : Blo 822348 825799 := bstep (se 1 (by rfl) ⟨619349, by rfl⟩ : syracuseStep 825799 = 1238699) B1238699
theorem B825819 : Blo 822348 825819 := bstep (se 1 (by rfl) ⟨619364, by rfl⟩ : syracuseStep 825819 = 1238729) B1238729
theorem B825895 : Blo 822348 825895 := bstep (se 1 (by rfl) ⟨619421, by rfl⟩ : syracuseStep 825895 = 1238843) B1238843
theorem B1317455 : Blo 822348 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B825935 : Blo 822348 825935 := bstep (se 1 (by rfl) ⟨619451, by rfl⟩ : syracuseStep 825935 = 1238903) B1238903
theorem B825951 : Blo 822348 825951 := bstep (se 1 (by rfl) ⟨619463, by rfl⟩ : syracuseStep 825951 = 1238927) B1238927
theorem B825979 : Blo 822348 825979 := bstep (se 1 (by rfl) ⟨619484, by rfl⟩ : syracuseStep 825979 = 1238969) B1238969
theorem B826031 : Blo 822348 826031 := bstep (se 1 (by rfl) ⟨619523, by rfl⟩ : syracuseStep 826031 = 1239047) B1239047
theorem B826055 : Blo 822348 826055 := bstep (se 1 (by rfl) ⟨619541, by rfl⟩ : syracuseStep 826055 = 1239083) B1239083
theorem B3513041 : Blo 822348 3513041 := bstep (se 2 (by rfl) ⟨1317390, by rfl⟩ : syracuseStep 3513041 = 2634781) B2634781
theorem B826075 : Blo 822348 826075 := bstep (se 1 (by rfl) ⟨619556, by rfl⟩ : syracuseStep 826075 = 1239113) B1239113
theorem B826151 : Blo 822348 826151 := bstep (se 1 (by rfl) ⟨619613, by rfl⟩ : syracuseStep 826151 = 1239227) B1239227
theorem B826191 : Blo 822348 826191 := bstep (se 1 (by rfl) ⟨619643, by rfl⟩ : syracuseStep 826191 = 1239287) B1239287
theorem B826207 : Blo 822348 826207 := bstep (se 1 (by rfl) ⟨619655, by rfl⟩ : syracuseStep 826207 = 1239311) B1239311
theorem B826235 : Blo 822348 826235 := bstep (se 1 (by rfl) ⟨619676, by rfl⟩ : syracuseStep 826235 = 1239353) B1239353
theorem B826287 : Blo 822348 826287 := bstep (se 1 (by rfl) ⟨619715, by rfl⟩ : syracuseStep 826287 = 1239431) B1239431
theorem B826311 : Blo 822348 826311 := bstep (se 1 (by rfl) ⟨619733, by rfl⟩ : syracuseStep 826311 = 1239467) B1239467
theorem B826331 : Blo 822348 826331 := bstep (se 1 (by rfl) ⟨619748, by rfl⟩ : syracuseStep 826331 = 1239497) B1239497
theorem B4168907 : Blo 822348 4168907 := bstep (se 1 (by rfl) ⟨3126680, by rfl⟩ : syracuseStep 4168907 = 6253361) B6253361
theorem B990571 : Blo 822348 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B3513725 : Blo 822348 3513725 := bstep (se 3 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 3513725 = 1317647) B1317647
theorem B5283245 : Blo 822348 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B7052939 : Blo 822348 7052939 := bstep (se 1 (by rfl) ⟨5289704, by rfl⟩ : syracuseStep 7052939 = 10579409) B10579409
theorem B1253303 : Blo 822348 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B925735 : Blo 822348 925735 := bstep (se 1 (by rfl) ⟨694301, by rfl⟩ : syracuseStep 925735 = 1388603) B1388603
theorem B6266969 : Blo 822348 6266969 := bstep (se 2 (by rfl) ⟨2350113, by rfl⟩ : syracuseStep 6266969 = 4700227) B4700227
theorem B1483103 : Blo 822348 1483103 := bstep (se 1 (by rfl) ⟨1112327, by rfl⟩ : syracuseStep 1483103 = 2224655) B2224655
theorem B2826937 : Blo 822348 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B1188551 : Blo 822348 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B6693587 : Blo 822348 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B2007881 : Blo 822348 2007881 := bstep (se 2 (by rfl) ⟨752955, by rfl⟩ : syracuseStep 2007881 = 1505911) B1505911
theorem B5022647 : Blo 822348 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B2139497 : Blo 822348 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B35661221 : Blo 822348 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B6268427 : Blo 822348 6268427 := bstep (se 1 (by rfl) ⟨4701320, by rfl⟩ : syracuseStep 6268427 = 9402641) B9402641
theorem B927355 : Blo 822348 927355 := bstep (se 1 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 927355 = 1391033) B1391033
theorem B927823 : Blo 822348 927823 := bstep (se 1 (by rfl) ⟨695867, by rfl⟩ : syracuseStep 927823 = 1391735) B1391735
theorem B11872493 : Blo 822348 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B1485049 : Blo 822348 1485049 := bstep (se 2 (by rfl) ⟨556893, by rfl⟩ : syracuseStep 1485049 = 1113787) B1113787
theorem B26782001 : Blo 822348 26782001 := bstep (se 2 (by rfl) ⟨10043250, by rfl⟩ : syracuseStep 26782001 = 20086501) B20086501
theorem B1976681 : Blo 822348 1976681 := bstep (se 2 (by rfl) ⟨741255, by rfl⟩ : syracuseStep 1976681 = 1482511) B1482511
theorem B928219 : Blo 822348 928219 := bstep (se 1 (by rfl) ⟨696164, by rfl⟩ : syracuseStep 928219 = 1392329) B1392329
theorem B1321529 : Blo 822348 1321529 := bstep (se 2 (by rfl) ⟨495573, by rfl⟩ : syracuseStep 1321529 = 991147) B991147
theorem B3124129 : Blo 822348 3124129 := bstep (se 2 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 3124129 = 2343097) B2343097
theorem B5647279 : Blo 822348 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B928687 : Blo 822348 928687 := bstep (se 1 (by rfl) ⟨696515, by rfl⟩ : syracuseStep 928687 = 1393031) B1393031
theorem B1321991 : Blo 822348 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B929119 : Blo 822348 929119 := bstep (se 1 (by rfl) ⟨696839, by rfl⟩ : syracuseStep 929119 = 1393679) B1393679
theorem B6270371 : Blo 822348 6270371 := bstep (se 1 (by rfl) ⟨4702778, by rfl⟩ : syracuseStep 6270371 = 9405557) B9405557
theorem B5942729 : Blo 822348 5942729 := bstep (se 2 (by rfl) ⟨2228523, by rfl⟩ : syracuseStep 5942729 = 4457047) B4457047
theorem B1486433 : Blo 822348 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B1191547 : Blo 822348 1191547 := bstep (se 1 (by rfl) ⟨893660, by rfl⟩ : syracuseStep 1191547 = 1787321) B1787321
theorem B3518099 : Blo 822348 3518099 := bstep (se 1 (by rfl) ⟨2638574, by rfl⟩ : syracuseStep 3518099 = 5277149) B5277149
theorem B929479 : Blo 822348 929479 := bstep (se 1 (by rfl) ⟨697109, by rfl⟩ : syracuseStep 929479 = 1394219) B1394219
theorem B1388279 : Blo 822348 1388279 := bstep (se 1 (by rfl) ⟨1041209, by rfl⟩ : syracuseStep 1388279 = 2082419) B2082419
theorem B6008671 : Blo 822348 6008671 := bstep (se 1 (by rfl) ⟨4506503, by rfl⟩ : syracuseStep 6008671 = 9013007) B9013007
theorem B3125087 : Blo 822348 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B1978219 : Blo 822348 1978219 := bstep (se 1 (by rfl) ⟨1483664, by rfl⟩ : syracuseStep 1978219 = 2967329) B2967329
theorem B3125101 : Blo 822348 3125101 := bstep (se 3 (by rfl) ⟨585956, by rfl⟩ : syracuseStep 3125101 = 1171913) B1171913
theorem B5648237 : Blo 822348 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B6008737 : Blo 822348 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B1322939 : Blo 822348 1322939 := bstep (se 1 (by rfl) ⟨992204, by rfl⟩ : syracuseStep 1322939 = 1984409) B1984409
theorem B1388623 : Blo 822348 1388623 := bstep (se 1 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 1388623 = 2082935) B2082935
theorem B3125405 : Blo 822348 3125405 := bstep (se 3 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 3125405 = 1172027) B1172027
theorem B4698269 : Blo 822348 4698269 := bstep (se 3 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 4698269 = 1761851) B1761851
theorem B4174091 : Blo 822348 4174091 := bstep (se 1 (by rfl) ⟨3130568, by rfl⟩ : syracuseStep 4174091 = 6261137) B6261137
theorem B1388873 : Blo 822348 1388873 := bstep (se 2 (by rfl) ⟨520827, by rfl⟩ : syracuseStep 1388873 = 1041655) B1041655
theorem B1389305 : Blo 822348 1389305 := bstep (se 2 (by rfl) ⟨520989, by rfl⟩ : syracuseStep 1389305 = 1041979) B1041979
theorem B3126059 : Blo 822348 3126059 := bstep (se 1 (by rfl) ⟨2344544, by rfl⟩ : syracuseStep 3126059 = 4689089) B4689089
theorem B1389487 : Blo 822348 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B1389575 : Blo 822348 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B1389919 : Blo 822348 1389919 := bstep (se 1 (by rfl) ⟨1042439, by rfl⟩ : syracuseStep 1389919 = 2084879) B2084879
theorem B1979777 : Blo 822348 1979777 := bstep (se 2 (by rfl) ⟨742416, by rfl⟩ : syracuseStep 1979777 = 1484833) B1484833
theorem B4011437 : Blo 822348 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B1390007 : Blo 822348 1390007 := bstep (se 1 (by rfl) ⟨1042505, by rfl⟩ : syracuseStep 1390007 = 2085011) B2085011
theorem B7059089 : Blo 822348 7059089 := bstep (se 2 (by rfl) ⟨2647158, by rfl⟩ : syracuseStep 7059089 = 5294317) B5294317
theorem B4175549 : Blo 822348 4175549 := bstep (se 3 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 4175549 = 1565831) B1565831
theorem B6272801 : Blo 822348 6272801 := bstep (se 2 (by rfl) ⟨2352300, by rfl⟩ : syracuseStep 6272801 = 4704601) B4704601
theorem B4175711 : Blo 822348 4175711 := bstep (se 1 (by rfl) ⟨3131783, by rfl⟩ : syracuseStep 4175711 = 6263567) B6263567
theorem B7026695 : Blo 822348 7026695 := bstep (se 1 (by rfl) ⟨5270021, by rfl⟩ : syracuseStep 7026695 = 10540043) B10540043
theorem B1390601 : Blo 822348 1390601 := bstep (se 2 (by rfl) ⟨521475, by rfl⟩ : syracuseStep 1390601 = 1042951) B1042951
theorem B1390763 : Blo 822348 1390763 := bstep (se 1 (by rfl) ⟨1043072, by rfl⟩ : syracuseStep 1390763 = 2086145) B2086145
theorem B1391161 : Blo 822348 1391161 := bstep (se 2 (by rfl) ⟨521685, by rfl⟩ : syracuseStep 1391161 = 1043371) B1043371
theorem B1391303 : Blo 822348 1391303 := bstep (se 1 (by rfl) ⟨1043477, by rfl⟩ : syracuseStep 1391303 = 2086955) B2086955
theorem B3128017 : Blo 822348 3128017 := bstep (se 2 (by rfl) ⟨1173006, by rfl⟩ : syracuseStep 3128017 = 2346013) B2346013
theorem B2407241 : Blo 822348 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B1391465 : Blo 822348 1391465 := bstep (se 2 (by rfl) ⟨521799, by rfl⟩ : syracuseStep 1391465 = 1043599) B1043599
theorem B2636651 : Blo 822348 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B3128321 : Blo 822348 3128321 := bstep (se 2 (by rfl) ⟨1173120, by rfl⟩ : syracuseStep 3128321 = 2346241) B2346241
theorem B4701185 : Blo 822348 4701185 := bstep (se 2 (by rfl) ⟨1762944, by rfl⟩ : syracuseStep 4701185 = 3525889) B3525889
theorem B1588243 : Blo 822348 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B5946419 : Blo 822348 5946419 := bstep (se 1 (by rfl) ⟨4459814, by rfl⟩ : syracuseStep 5946419 = 8919629) B8919629
theorem B1850615 : Blo 822348 1850615 := bstep (se 1 (by rfl) ⟨1387961, by rfl⟩ : syracuseStep 1850615 = 2775923) B2775923
theorem B1391863 : Blo 822348 1391863 := bstep (se 1 (by rfl) ⟨1043897, by rfl⟩ : syracuseStep 1391863 = 2087795) B2087795
theorem B1719713 : Blo 822348 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B1392059 : Blo 822348 1392059 := bstep (se 1 (by rfl) ⟨1044044, by rfl⟩ : syracuseStep 1392059 = 2088089) B2088089
theorem B3128777 : Blo 822348 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B22560295 : Blo 822348 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B1392167 : Blo 822348 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B835291 : Blo 822348 835291 := bstep (se 1 (by rfl) ⟨626468, by rfl⟩ : syracuseStep 835291 = 1252937) B1252937
theorem B1851209 : Blo 822348 1851209 := bstep (se 2 (by rfl) ⟨694203, by rfl⟩ : syracuseStep 1851209 = 1388407) B1388407
theorem B1392457 : Blo 822348 1392457 := bstep (se 2 (by rfl) ⟨522171, by rfl⟩ : syracuseStep 1392457 = 1044343) B1044343
theorem B1392491 : Blo 822348 1392491 := bstep (se 1 (by rfl) ⟨1044368, by rfl⟩ : syracuseStep 1392491 = 2088737) B2088737
theorem B2965367 : Blo 822348 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B3129263 : Blo 822348 3129263 := bstep (se 1 (by rfl) ⟨2346947, by rfl⟩ : syracuseStep 3129263 = 4693895) B4693895
theorem B2637755 : Blo 822348 2637755 := bstep (se 1 (by rfl) ⟨1978316, by rfl⟩ : syracuseStep 2637755 = 3956633) B3956633
theorem B9388061 : Blo 822348 9388061 := bstep (se 3 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 9388061 = 3520523) B3520523
theorem B1392889 : Blo 822348 1392889 := bstep (se 2 (by rfl) ⟨522333, by rfl⟩ : syracuseStep 1392889 = 1044667) B1044667
theorem B1393159 : Blo 822348 1393159 := bstep (se 1 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 1393159 = 2089739) B2089739
theorem B4178465 : Blo 822348 4178465 := bstep (se 2 (by rfl) ⟨1566924, by rfl⟩ : syracuseStep 4178465 = 3133849) B3133849
theorem B1852001 : Blo 822348 1852001 := bstep (se 2 (by rfl) ⟨694500, by rfl⟩ : syracuseStep 1852001 = 1389001) B1389001
theorem B2638433 : Blo 822348 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B2081609 : Blo 822348 2081609 := bstep (se 2 (by rfl) ⟨780603, by rfl⟩ : syracuseStep 2081609 = 1561207) B1561207
theorem B1852343 : Blo 822348 1852343 := bstep (se 1 (by rfl) ⟨1389257, by rfl⟩ : syracuseStep 1852343 = 2778515) B2778515
theorem B1393591 : Blo 822348 1393591 := bstep (se 1 (by rfl) ⟨1045193, by rfl⟩ : syracuseStep 1393591 = 2090387) B2090387
theorem B2638855 : Blo 822348 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B3130447 : Blo 822348 3130447 := bstep (se 1 (by rfl) ⟨2347835, by rfl⟩ : syracuseStep 3130447 = 4695671) B4695671
theorem B1393787 : Blo 822348 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B2081963 : Blo 822348 2081963 := bstep (se 1 (by rfl) ⟨1561472, by rfl⟩ : syracuseStep 2081963 = 3122945) B3122945
theorem B11879921 : Blo 822348 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B1852937 : Blo 822348 1852937 := bstep (se 2 (by rfl) ⟨694851, by rfl⟩ : syracuseStep 1852937 = 1389703) B1389703
theorem B1394185 : Blo 822348 1394185 := bstep (se 2 (by rfl) ⟨522819, by rfl⟩ : syracuseStep 1394185 = 1045639) B1045639
theorem B3130919 : Blo 822348 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B1394347 : Blo 822348 1394347 := bstep (se 1 (by rfl) ⟨1045760, by rfl⟩ : syracuseStep 1394347 = 2091521) B2091521
theorem B1853279 : Blo 822348 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B2082743 : Blo 822348 2082743 := bstep (se 1 (by rfl) ⟨1562057, by rfl⟩ : syracuseStep 2082743 = 3124115) B3124115
theorem B1853459 : Blo 822348 1853459 := bstep (se 1 (by rfl) ⟨1390094, by rfl⟩ : syracuseStep 1853459 = 2780189) B2780189
theorem B2640215 : Blo 822348 2640215 := bstep (se 1 (by rfl) ⟨1980161, by rfl⟩ : syracuseStep 2640215 = 3960323) B3960323
theorem B1853801 : Blo 822348 1853801 := bstep (se 2 (by rfl) ⟨695175, by rfl⟩ : syracuseStep 1853801 = 1390351) B1390351
theorem B3131891 : Blo 822348 3131891 := bstep (se 1 (by rfl) ⟨2348918, by rfl⟩ : syracuseStep 3131891 = 4697837) B4697837
theorem B8932085 : Blo 822348 8932085 := bstep (se 5 (by rfl) ⟨418691, by rfl⟩ : syracuseStep 8932085 = 837383) B837383
theorem B2083745 : Blo 822348 2083745 := bstep (se 2 (by rfl) ⟨781404, by rfl⟩ : syracuseStep 2083745 = 1562809) B1562809
theorem B1854395 : Blo 822348 1854395 := bstep (se 1 (by rfl) ⟨1390796, by rfl⟩ : syracuseStep 1854395 = 2781593) B2781593
theorem B1854521 : Blo 822348 1854521 := bstep (se 2 (by rfl) ⟨695445, by rfl⟩ : syracuseStep 1854521 = 1390891) B1390891
theorem B4705559 : Blo 822348 4705559 := bstep (se 1 (by rfl) ⟨3529169, by rfl⟩ : syracuseStep 4705559 = 7058339) B7058339
theorem B2084201 : Blo 822348 2084201 := bstep (se 2 (by rfl) ⟨781575, by rfl⟩ : syracuseStep 2084201 = 1563151) B1563151
theorem B1854863 : Blo 822348 1854863 := bstep (se 1 (by rfl) ⟨1391147, by rfl⟩ : syracuseStep 1854863 = 2782295) B2782295
theorem B15814061 : Blo 822348 15814061 := bstep (se 3 (by rfl) ⟨2965136, by rfl⟩ : syracuseStep 15814061 = 5930273) B5930273
theorem B3952115 : Blo 822348 3952115 := bstep (se 1 (by rfl) ⟨2964086, by rfl⟩ : syracuseStep 3952115 = 5928173) B5928173
theorem B4181543 : Blo 822348 4181543 := bstep (se 1 (by rfl) ⟨3136157, by rfl⟩ : syracuseStep 4181543 = 6272315) B6272315
theorem B2641547 : Blo 822348 2641547 := bstep (se 1 (by rfl) ⟨1981160, by rfl⟩ : syracuseStep 2641547 = 3962321) B3962321
theorem B1855187 : Blo 822348 1855187 := bstep (se 1 (by rfl) ⟨1391390, by rfl⟩ : syracuseStep 1855187 = 2782781) B2782781
theorem B937823 : Blo 822348 937823 := bstep (se 1 (by rfl) ⟨703367, by rfl⟩ : syracuseStep 937823 = 1406735) B1406735
theorem B2969519 : Blo 822348 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B3952577 : Blo 822348 3952577 := bstep (se 2 (by rfl) ⟨1482216, by rfl⟩ : syracuseStep 3952577 = 2964433) B2964433
theorem B5951495 : Blo 822348 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B3952729 : Blo 822348 3952729 := bstep (se 2 (by rfl) ⟨1482273, by rfl⟩ : syracuseStep 3952729 = 2964547) B2964547
theorem B6246557 : Blo 822348 6246557 := bstep (se 3 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 6246557 = 2342459) B2342459
theorem B22532269 : Blo 822348 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B26726597 : Blo 822348 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B2675069 : Blo 822348 2675069 := bstep (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) B1003151
theorem B2085385 : Blo 822348 2085385 := bstep (se 2 (by rfl) ⟨782019, by rfl⟩ : syracuseStep 2085385 = 1564039) B1564039
theorem B2347643 : Blo 822348 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B1856123 : Blo 822348 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B1856249 : Blo 822348 1856249 := bstep (se 2 (by rfl) ⟨696093, by rfl⟩ : syracuseStep 1856249 = 1392187) B1392187
theorem B1233839 : Blo 822348 1233839 := bstep (se 1 (by rfl) ⟨925379, by rfl⟩ : syracuseStep 1233839 = 1850759) B1850759
theorem B1856519 : Blo 822348 1856519 := bstep (se 1 (by rfl) ⟨1392389, by rfl⟩ : syracuseStep 1856519 = 2784779) B2784779
theorem B1561609 : Blo 822348 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B1233929 : Blo 822348 1233929 := bstep (se 2 (by rfl) ⟨462723, by rfl⟩ : syracuseStep 1233929 = 925447) B925447
theorem B1233959 : Blo 822348 1233959 := bstep (se 1 (by rfl) ⟨925469, by rfl⟩ : syracuseStep 1233959 = 1850939) B1850939
theorem B1856591 : Blo 822348 1856591 := bstep (se 1 (by rfl) ⟨1392443, by rfl⟩ : syracuseStep 1856591 = 2784887) B2784887
theorem B1234043 : Blo 822348 1234043 := bstep (se 1 (by rfl) ⟨925532, by rfl⟩ : syracuseStep 1234043 = 1851065) B1851065
theorem B1234169 : Blo 822348 1234169 := bstep (se 2 (by rfl) ⟨462813, by rfl⟩ : syracuseStep 1234169 = 925627) B925627
theorem B3134807 : Blo 822348 3134807 := bstep (se 1 (by rfl) ⟨2351105, by rfl⟩ : syracuseStep 3134807 = 4702211) B4702211
theorem B1234271 : Blo 822348 1234271 := bstep (se 1 (by rfl) ⟨925703, by rfl⟩ : syracuseStep 1234271 = 1851407) B1851407
theorem B1234283 : Blo 822348 1234283 := bstep (se 1 (by rfl) ⟨925712, by rfl⟩ : syracuseStep 1234283 = 1851425) B1851425
theorem B1856987 : Blo 822348 1856987 := bstep (se 1 (by rfl) ⟨1392740, by rfl⟩ : syracuseStep 1856987 = 2785481) B2785481
theorem B1234511 : Blo 822348 1234511 := bstep (se 1 (by rfl) ⟨925883, by rfl⟩ : syracuseStep 1234511 = 1851767) B1851767
theorem B3757715 : Blo 822348 3757715 := bstep (se 1 (by rfl) ⟨2818286, by rfl⟩ : syracuseStep 3757715 = 5636573) B5636573
theorem B1234631 : Blo 822348 1234631 := bstep (se 1 (by rfl) ⟨925973, by rfl⟩ : syracuseStep 1234631 = 1851947) B1851947
theorem B1562323 : Blo 822348 1562323 := bstep (se 1 (by rfl) ⟨1171742, by rfl⟩ : syracuseStep 1562323 = 2343485) B2343485
theorem B1234793 : Blo 822348 1234793 := bstep (se 2 (by rfl) ⟨463047, by rfl⟩ : syracuseStep 1234793 = 926095) B926095
theorem B2971511 : Blo 822348 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B2348975 : Blo 822348 2348975 := bstep (se 1 (by rfl) ⟨1761731, by rfl⟩ : syracuseStep 2348975 = 3523463) B3523463
theorem B1857455 : Blo 822348 1857455 := bstep (se 1 (by rfl) ⟨1393091, by rfl⟩ : syracuseStep 1857455 = 2786183) B2786183
theorem B1234871 : Blo 822348 1234871 := bstep (se 1 (by rfl) ⟨926153, by rfl⟩ : syracuseStep 1234871 = 1852307) B1852307
theorem B2086843 : Blo 822348 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B1234907 : Blo 822348 1234907 := bstep (se 1 (by rfl) ⟨926180, by rfl⟩ : syracuseStep 1234907 = 1852361) B1852361
theorem B4446323 : Blo 822348 4446323 := bstep (se 1 (by rfl) ⟨3334742, by rfl⟩ : syracuseStep 4446323 = 6669485) B6669485
theorem B1857707 : Blo 822348 1857707 := bstep (se 1 (by rfl) ⟨1393280, by rfl⟩ : syracuseStep 1857707 = 2786561) B2786561
theorem B1235375 : Blo 822348 1235375 := bstep (se 1 (by rfl) ⟨926531, by rfl⟩ : syracuseStep 1235375 = 1853063) B1853063
theorem B1563067 : Blo 822348 1563067 := bstep (se 1 (by rfl) ⟨1172300, by rfl⟩ : syracuseStep 1563067 = 2344601) B2344601
theorem B1235465 : Blo 822348 1235465 := bstep (se 2 (by rfl) ⟨463299, by rfl⟩ : syracuseStep 1235465 = 926599) B926599
theorem B1235495 : Blo 822348 1235495 := bstep (se 1 (by rfl) ⟨926621, by rfl⟩ : syracuseStep 1235495 = 1853243) B1853243
theorem B3136097 : Blo 822348 3136097 := bstep (se 2 (by rfl) ⟨1176036, by rfl⟩ : syracuseStep 3136097 = 2352073) B2352073
theorem B1235579 : Blo 822348 1235579 := bstep (se 1 (by rfl) ⟨926684, by rfl⟩ : syracuseStep 1235579 = 1853369) B1853369
theorem B1858247 : Blo 822348 1858247 := bstep (se 1 (by rfl) ⟨1393685, by rfl⟩ : syracuseStep 1858247 = 2787371) B2787371
theorem B1235705 : Blo 822348 1235705 := bstep (se 2 (by rfl) ⟨463389, by rfl⟩ : syracuseStep 1235705 = 926779) B926779
theorem B5954381 : Blo 822348 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B1235807 : Blo 822348 1235807 := bstep (se 1 (by rfl) ⟨926855, by rfl⟩ : syracuseStep 1235807 = 1853711) B1853711
theorem B1235819 : Blo 822348 1235819 := bstep (se 1 (by rfl) ⟨926864, by rfl⟩ : syracuseStep 1235819 = 1853729) B1853729
theorem B1563553 : Blo 822348 1563553 := bstep (se 2 (by rfl) ⟨586332, by rfl⟩ : syracuseStep 1563553 = 1172665) B1172665
theorem B6249473 : Blo 822348 6249473 := bstep (se 2 (by rfl) ⟨2343552, by rfl⟩ : syracuseStep 6249473 = 4687105) B4687105
theorem B5954609 : Blo 822348 5954609 := bstep (se 2 (by rfl) ⟨2232978, by rfl⟩ : syracuseStep 5954609 = 4465957) B4465957
theorem B1236047 : Blo 822348 1236047 := bstep (se 1 (by rfl) ⟨927035, by rfl⟩ : syracuseStep 1236047 = 1854071) B1854071
theorem B1236167 : Blo 822348 1236167 := bstep (se 1 (by rfl) ⟨927125, by rfl⟩ : syracuseStep 1236167 = 1854251) B1854251
theorem B1236329 : Blo 822348 1236329 := bstep (se 2 (by rfl) ⟨463623, by rfl⟩ : syracuseStep 1236329 = 927247) B927247
theorem B2776463 : Blo 822348 2776463 := bstep (se 1 (by rfl) ⟨2082347, by rfl⟩ : syracuseStep 2776463 = 4164695) B4164695
theorem B1236407 : Blo 822348 1236407 := bstep (se 1 (by rfl) ⟨927305, by rfl⟩ : syracuseStep 1236407 = 1854611) B1854611
theorem B1564123 : Blo 822348 1564123 := bstep (se 1 (by rfl) ⟨1173092, by rfl⟩ : syracuseStep 1564123 = 2346185) B2346185
theorem B1236443 : Blo 822348 1236443 := bstep (se 1 (by rfl) ⟨927332, by rfl⟩ : syracuseStep 1236443 = 1854665) B1854665
theorem B1859111 : Blo 822348 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B2776787 : Blo 822348 2776787 := bstep (se 1 (by rfl) ⟨2082590, by rfl⟩ : syracuseStep 2776787 = 4165181) B4165181
theorem B1761185 : Blo 822348 1761185 := bstep (se 2 (by rfl) ⟨660444, by rfl⟩ : syracuseStep 1761185 = 1320889) B1320889
theorem B12672931 : Blo 822348 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B1236911 : Blo 822348 1236911 := bstep (se 1 (by rfl) ⟨927683, by rfl⟩ : syracuseStep 1236911 = 1855367) B1855367
theorem B1237001 : Blo 822348 1237001 := bstep (se 2 (by rfl) ⟨463875, by rfl⟩ : syracuseStep 1237001 = 927751) B927751
theorem B1237031 : Blo 822348 1237031 := bstep (se 1 (by rfl) ⟨927773, by rfl⟩ : syracuseStep 1237031 = 1855547) B1855547
theorem B1237115 : Blo 822348 1237115 := bstep (se 1 (by rfl) ⟨927836, by rfl⟩ : syracuseStep 1237115 = 1855673) B1855673
theorem B1761527 : Blo 822348 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B2646263 : Blo 822348 2646263 := bstep (se 1 (by rfl) ⟨1984697, by rfl⟩ : syracuseStep 2646263 = 3969395) B3969395
theorem B1237241 : Blo 822348 1237241 := bstep (se 2 (by rfl) ⟨463965, by rfl⟩ : syracuseStep 1237241 = 927931) B927931
theorem B1237343 : Blo 822348 1237343 := bstep (se 1 (by rfl) ⟨928007, by rfl⟩ : syracuseStep 1237343 = 1856015) B1856015
theorem B1237355 : Blo 822348 1237355 := bstep (se 1 (by rfl) ⟨928016, by rfl⟩ : syracuseStep 1237355 = 1856033) B1856033
theorem B2089435 : Blo 822348 2089435 := bstep (se 1 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 2089435 = 3134153) B3134153
theorem B1237583 : Blo 822348 1237583 := bstep (se 1 (by rfl) ⟨928187, by rfl⟩ : syracuseStep 1237583 = 1856375) B1856375
theorem B2679419 : Blo 822348 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B1237703 : Blo 822348 1237703 := bstep (se 1 (by rfl) ⟨928277, by rfl⟩ : syracuseStep 1237703 = 1856555) B1856555
theorem B1237865 : Blo 822348 1237865 := bstep (se 2 (by rfl) ⟨464199, by rfl⟩ : syracuseStep 1237865 = 928399) B928399
theorem B2777975 : Blo 822348 2777975 := bstep (se 1 (by rfl) ⟨2083481, by rfl⟩ : syracuseStep 2777975 = 4166963) B4166963
theorem B2974583 : Blo 822348 2974583 := bstep (se 1 (by rfl) ⟨2230937, by rfl⟩ : syracuseStep 2974583 = 4461875) B4461875
theorem B1237943 : Blo 822348 1237943 := bstep (se 1 (by rfl) ⟨928457, by rfl⟩ : syracuseStep 1237943 = 1856915) B1856915
theorem B1237979 : Blo 822348 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B2778191 : Blo 822348 2778191 := bstep (se 1 (by rfl) ⟨2083643, by rfl⟩ : syracuseStep 2778191 = 4167287) B4167287
theorem B2090063 : Blo 822348 2090063 := bstep (se 1 (by rfl) ⟨1567547, by rfl⟩ : syracuseStep 2090063 = 3135095) B3135095
theorem B26797175 : Blo 822348 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1238447 : Blo 822348 1238447 := bstep (se 1 (by rfl) ⟨928835, by rfl⟩ : syracuseStep 1238447 = 1857671) B1857671
theorem B2778569 : Blo 822348 2778569 := bstep (se 2 (by rfl) ⟨1041963, by rfl⟩ : syracuseStep 2778569 = 2083927) B2083927
theorem B1762825 : Blo 822348 1762825 := bstep (se 2 (by rfl) ⟨661059, by rfl⟩ : syracuseStep 1762825 = 1322119) B1322119
theorem B1238537 : Blo 822348 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B2352665 : Blo 822348 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B1238567 : Blo 822348 1238567 := bstep (se 1 (by rfl) ⟨928925, by rfl⟩ : syracuseStep 1238567 = 1857851) B1857851
theorem B1566287 : Blo 822348 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1238651 : Blo 822348 1238651 := bstep (se 1 (by rfl) ⟨928988, by rfl⟩ : syracuseStep 1238651 = 1857977) B1857977
theorem B4449937 : Blo 822348 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B2778839 : Blo 822348 2778839 := bstep (se 1 (by rfl) ⟨2084129, by rfl⟩ : syracuseStep 2778839 = 4168259) B4168259
theorem B2090711 : Blo 822348 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B1238777 : Blo 822348 1238777 := bstep (se 2 (by rfl) ⟨464541, by rfl⟩ : syracuseStep 1238777 = 929083) B929083
theorem B20309849 : Blo 822348 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B1763167 : Blo 822348 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B1238879 : Blo 822348 1238879 := bstep (se 1 (by rfl) ⟨929159, by rfl⟩ : syracuseStep 1238879 = 1858319) B1858319
theorem B1238891 : Blo 822348 1238891 := bstep (se 1 (by rfl) ⟨929168, by rfl⟩ : syracuseStep 1238891 = 1858337) B1858337
theorem B2779055 : Blo 822348 2779055 := bstep (se 1 (by rfl) ⟨2084291, by rfl⟩ : syracuseStep 2779055 = 4168583) B4168583
theorem B1239119 : Blo 822348 1239119 := bstep (se 1 (by rfl) ⟨929339, by rfl⟩ : syracuseStep 1239119 = 1858679) B1858679
theorem B7039133 : Blo 822348 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B1239239 : Blo 822348 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B1239401 : Blo 822348 1239401 := bstep (se 2 (by rfl) ⟨464775, by rfl⟩ : syracuseStep 1239401 = 929551) B929551
theorem B1239479 : Blo 822348 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B1239515 : Blo 822348 1239515 := bstep (se 1 (by rfl) ⟨929636, by rfl⟩ : syracuseStep 1239515 = 1859273) B1859273
theorem B1567289 : Blo 822348 1567289 := bstep (se 2 (by rfl) ⟨587733, by rfl⟩ : syracuseStep 1567289 = 1175467) B1175467
theorem B2714543 : Blo 822348 2714543 := bstep (se 1 (by rfl) ⟨2035907, by rfl⟩ : syracuseStep 2714543 = 4071815) B4071815
theorem B1764431 : Blo 822348 1764431 := bstep (se 1 (by rfl) ⟨1323323, by rfl⟩ : syracuseStep 1764431 = 2646647) B2646647
theorem B7040195 : Blo 822348 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B6253847 : Blo 822348 6253847 := bstep (se 1 (by rfl) ⟨4690385, by rfl⟩ : syracuseStep 6253847 = 9380771) B9380771
theorem B9399725 : Blo 822348 9399725 := bstep (se 3 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 9399725 = 3524897) B3524897
theorem B10546807 : Blo 822348 10546807 := bstep (se 1 (by rfl) ⟨7910105, by rfl⟩ : syracuseStep 10546807 = 15820211) B15820211
theorem B2813579 : Blo 822348 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B1175239 : Blo 822348 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B2781431 : Blo 822348 2781431 := bstep (se 1 (by rfl) ⟨2086073, by rfl⟩ : syracuseStep 2781431 = 4172147) B4172147
theorem B5272073 : Blo 822348 5272073 := bstep (se 2 (by rfl) ⟨1977027, by rfl⟩ : syracuseStep 5272073 = 3954055) B3954055
theorem B2781755 : Blo 822348 2781755 := bstep (se 1 (by rfl) ⟨2086316, by rfl⟩ : syracuseStep 2781755 = 4172633) B4172633
theorem B6255305 : Blo 822348 6255305 := bstep (se 2 (by rfl) ⟨2345739, by rfl⟩ : syracuseStep 6255305 = 4691479) B4691479
theorem B2782025 : Blo 822348 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B10548143 : Blo 822348 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B1045543 : Blo 822348 1045543 := bstep (se 1 (by rfl) ⟨784157, by rfl⟩ : syracuseStep 1045543 = 1568315) B1568315
theorem B3568835 : Blo 822348 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B2815319 : Blo 822348 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B5273099 : Blo 822348 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B1341289 : Blo 822348 1341289 := bstep (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) B1005967
theorem B2783159 : Blo 822348 2783159 := bstep (se 1 (by rfl) ⟨2087369, by rfl⟩ : syracuseStep 2783159 = 4174739) B4174739
theorem B5928889 : Blo 822348 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B10582073 : Blo 822348 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B1669481 : Blo 822348 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B2783753 : Blo 822348 2783753 := bstep (se 2 (by rfl) ⟨1043907, by rfl⟩ : syracuseStep 2783753 = 2087815) B2087815
theorem B4749857 : Blo 822348 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B1407611 : Blo 822348 1407611 := bstep (se 1 (by rfl) ⟨1055708, by rfl⟩ : syracuseStep 1407611 = 2111417) B2111417
theorem B1670063 : Blo 822348 1670063 := bstep (se 1 (by rfl) ⟨1252547, by rfl⟩ : syracuseStep 1670063 = 2505095) B2505095
theorem B2784617 : Blo 822348 2784617 := bstep (se 2 (by rfl) ⟨1044231, by rfl⟩ : syracuseStep 2784617 = 2088463) B2088463
theorem B3767771 : Blo 822348 3767771 := bstep (se 1 (by rfl) ⟨2825828, by rfl⟩ : syracuseStep 3767771 = 5651657) B5651657
theorem B1113679 : Blo 822348 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B3964781 : Blo 822348 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B2785211 : Blo 822348 2785211 := bstep (se 1 (by rfl) ⟨2088908, by rfl⟩ : syracuseStep 2785211 = 4177817) B4177817
theorem B6258707 : Blo 822348 6258707 := bstep (se 1 (by rfl) ⟨4694030, by rfl⟩ : syracuseStep 6258707 = 9388061) B9388061
theorem B4456619 : Blo 822348 4456619 := bstep (se 1 (by rfl) ⟨3342464, by rfl⟩ : syracuseStep 4456619 = 6684929) B6684929
theorem B2785643 : Blo 822348 2785643 := bstep (se 1 (by rfl) ⟨2089232, by rfl⟩ : syracuseStep 2785643 = 4178465) B4178465
theorem B2785913 : Blo 822348 2785913 := bstep (se 2 (by rfl) ⟨1044717, by rfl⟩ : syracuseStep 2785913 = 2089435) B2089435
theorem B10552139 : Blo 822348 10552139 := bstep (se 1 (by rfl) ⟨7914104, by rfl⟩ : syracuseStep 10552139 = 15828209) B15828209
theorem B3769249 : Blo 822348 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B5933249 : Blo 822348 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B2787695 : Blo 822348 2787695 := bstep (se 1 (by rfl) ⟨2090771, by rfl⟩ : syracuseStep 2787695 = 4181543) B4181543
theorem B3967663 : Blo 822348 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B4164371 : Blo 822348 4164371 := bstep (se 1 (by rfl) ⟨3123278, by rfl⟩ : syracuseStep 4164371 = 6246557) B6246557
theorem B822559 : Blo 822348 822559 := bstep (se 1 (by rfl) ⟨616919, by rfl⟩ : syracuseStep 822559 = 1233839) B1233839
theorem B822619 : Blo 822348 822619 := bstep (se 1 (by rfl) ⟨616964, by rfl⟩ : syracuseStep 822619 = 1233929) B1233929
theorem B822639 : Blo 822348 822639 := bstep (se 1 (by rfl) ⟨616979, by rfl⟩ : syracuseStep 822639 = 1233959) B1233959
theorem B822695 : Blo 822348 822695 := bstep (se 1 (by rfl) ⟨617021, by rfl⟩ : syracuseStep 822695 = 1234043) B1234043
theorem B822779 : Blo 822348 822779 := bstep (se 1 (by rfl) ⟨617084, by rfl⟩ : syracuseStep 822779 = 1234169) B1234169
theorem B822847 : Blo 822348 822847 := bstep (se 1 (by rfl) ⟨617135, by rfl⟩ : syracuseStep 822847 = 1234271) B1234271
theorem B822855 : Blo 822348 822855 := bstep (se 1 (by rfl) ⟨617141, by rfl⟩ : syracuseStep 822855 = 1234283) B1234283
theorem B823007 : Blo 822348 823007 := bstep (se 1 (by rfl) ⟨617255, by rfl⟩ : syracuseStep 823007 = 1234511) B1234511
theorem B823087 : Blo 822348 823087 := bstep (se 1 (by rfl) ⟨617315, by rfl⟩ : syracuseStep 823087 = 1234631) B1234631
theorem B4165505 : Blo 822348 4165505 := bstep (se 2 (by rfl) ⟨1562064, by rfl⟩ : syracuseStep 4165505 = 3124129) B3124129
theorem B823195 : Blo 822348 823195 := bstep (se 1 (by rfl) ⟨617396, by rfl⟩ : syracuseStep 823195 = 1234793) B1234793
theorem B823247 : Blo 822348 823247 := bstep (se 1 (by rfl) ⟨617435, by rfl⟩ : syracuseStep 823247 = 1234871) B1234871
theorem B823271 : Blo 822348 823271 := bstep (se 1 (by rfl) ⟨617453, by rfl⟩ : syracuseStep 823271 = 1234907) B1234907
theorem B2232329 : Blo 822348 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B823583 : Blo 822348 823583 := bstep (se 1 (by rfl) ⟨617687, by rfl⟩ : syracuseStep 823583 = 1235375) B1235375
theorem B823643 : Blo 822348 823643 := bstep (se 1 (by rfl) ⟨617732, by rfl⟩ : syracuseStep 823643 = 1235465) B1235465
theorem B823663 : Blo 822348 823663 := bstep (se 1 (by rfl) ⟨617747, by rfl⟩ : syracuseStep 823663 = 1235495) B1235495
theorem B823719 : Blo 822348 823719 := bstep (se 1 (by rfl) ⟨617789, by rfl⟩ : syracuseStep 823719 = 1235579) B1235579
theorem B823803 : Blo 822348 823803 := bstep (se 1 (by rfl) ⟨617852, by rfl⟩ : syracuseStep 823803 = 1235705) B1235705
theorem B8917553 : Blo 822348 8917553 := bstep (se 2 (by rfl) ⟨3344082, by rfl⟩ : syracuseStep 8917553 = 6688165) B6688165
theorem B3969587 : Blo 822348 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B823871 : Blo 822348 823871 := bstep (se 1 (by rfl) ⟨617903, by rfl⟩ : syracuseStep 823871 = 1235807) B1235807
theorem B823879 : Blo 822348 823879 := bstep (se 1 (by rfl) ⟨617909, by rfl⟩ : syracuseStep 823879 = 1235819) B1235819
theorem B4166315 : Blo 822348 4166315 := bstep (se 1 (by rfl) ⟨3124736, by rfl⟩ : syracuseStep 4166315 = 6249473) B6249473
theorem B3969739 : Blo 822348 3969739 := bstep (se 1 (by rfl) ⟨2977304, by rfl⟩ : syracuseStep 3969739 = 5954609) B5954609
theorem B824031 : Blo 822348 824031 := bstep (se 1 (by rfl) ⟨618023, by rfl⟩ : syracuseStep 824031 = 1236047) B1236047
theorem B824111 : Blo 822348 824111 := bstep (se 1 (by rfl) ⟨618083, by rfl⟩ : syracuseStep 824111 = 1236167) B1236167
theorem B14062409 : Blo 822348 14062409 := bstep (se 2 (by rfl) ⟨5273403, by rfl⟩ : syracuseStep 14062409 = 10546807) B10546807
theorem B824219 : Blo 822348 824219 := bstep (se 1 (by rfl) ⟨618164, by rfl⟩ : syracuseStep 824219 = 1236329) B1236329
theorem B824271 : Blo 822348 824271 := bstep (se 1 (by rfl) ⟨618203, by rfl⟩ : syracuseStep 824271 = 1236407) B1236407
theorem B824295 : Blo 822348 824295 := bstep (se 1 (by rfl) ⟨618221, by rfl⟩ : syracuseStep 824295 = 1236443) B1236443
theorem B4166801 : Blo 822348 4166801 := bstep (se 2 (by rfl) ⟨1562550, by rfl⟩ : syracuseStep 4166801 = 3125101) B3125101
theorem B824607 : Blo 822348 824607 := bstep (se 1 (by rfl) ⟨618455, by rfl⟩ : syracuseStep 824607 = 1236911) B1236911
theorem B824667 : Blo 822348 824667 := bstep (se 1 (by rfl) ⟨618500, by rfl⟩ : syracuseStep 824667 = 1237001) B1237001
theorem B824687 : Blo 822348 824687 := bstep (se 1 (by rfl) ⟨618515, by rfl⟩ : syracuseStep 824687 = 1237031) B1237031
theorem B824743 : Blo 822348 824743 := bstep (se 1 (by rfl) ⟨618557, by rfl⟩ : syracuseStep 824743 = 1237115) B1237115
theorem B824827 : Blo 822348 824827 := bstep (se 1 (by rfl) ⟨618620, by rfl⟩ : syracuseStep 824827 = 1237241) B1237241
theorem B988735 : Blo 822348 988735 := bstep (se 1 (by rfl) ⟨741551, by rfl⟩ : syracuseStep 988735 = 1483103) B1483103
theorem B824895 : Blo 822348 824895 := bstep (se 1 (by rfl) ⟨618671, by rfl⟩ : syracuseStep 824895 = 1237343) B1237343
theorem B824903 : Blo 822348 824903 := bstep (se 1 (by rfl) ⟨618677, by rfl⟩ : syracuseStep 824903 = 1237355) B1237355
theorem B825055 : Blo 822348 825055 := bstep (se 1 (by rfl) ⟨618791, by rfl⟩ : syracuseStep 825055 = 1237583) B1237583
theorem B825135 : Blo 822348 825135 := bstep (se 1 (by rfl) ⟨618851, by rfl⟩ : syracuseStep 825135 = 1237703) B1237703
theorem B4462391 : Blo 822348 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B825243 : Blo 822348 825243 := bstep (se 1 (by rfl) ⟨618932, by rfl⟩ : syracuseStep 825243 = 1237865) B1237865
theorem B825295 : Blo 822348 825295 := bstep (se 1 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 825295 = 1237943) B1237943
theorem B3348431 : Blo 822348 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B825319 : Blo 822348 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B17864783 : Blo 822348 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B825631 : Blo 822348 825631 := bstep (se 1 (by rfl) ⟨619223, by rfl⟩ : syracuseStep 825631 = 1238447) B1238447
theorem B825691 : Blo 822348 825691 := bstep (se 1 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 825691 = 1238537) B1238537
theorem B825711 : Blo 822348 825711 := bstep (se 1 (by rfl) ⟨619283, by rfl⟩ : syracuseStep 825711 = 1238567) B1238567
theorem B825767 : Blo 822348 825767 := bstep (se 1 (by rfl) ⟨619325, by rfl⟩ : syracuseStep 825767 = 1238651) B1238651
theorem B825851 : Blo 822348 825851 := bstep (se 1 (by rfl) ⟨619388, by rfl⟩ : syracuseStep 825851 = 1238777) B1238777
theorem B13539899 : Blo 822348 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B825919 : Blo 822348 825919 := bstep (se 1 (by rfl) ⟨619439, by rfl⟩ : syracuseStep 825919 = 1238879) B1238879
theorem B825927 : Blo 822348 825927 := bstep (se 1 (by rfl) ⟨619445, by rfl⟩ : syracuseStep 825927 = 1238891) B1238891
theorem B826079 : Blo 822348 826079 := bstep (se 1 (by rfl) ⟨619559, by rfl⟩ : syracuseStep 826079 = 1239119) B1239119
theorem B4692755 : Blo 822348 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B826159 : Blo 822348 826159 := bstep (se 1 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 826159 = 1239239) B1239239
theorem B826267 : Blo 822348 826267 := bstep (se 1 (by rfl) ⟨619700, by rfl⟩ : syracuseStep 826267 = 1239401) B1239401
theorem B826319 : Blo 822348 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B826343 : Blo 822348 826343 := bstep (se 1 (by rfl) ⟨619757, by rfl⟩ : syracuseStep 826343 = 1239515) B1239515
theorem B1318121 : Blo 822348 1318121 := bstep (se 2 (by rfl) ⟨494295, by rfl⟩ : syracuseStep 1318121 = 988591) B988591
theorem B1809695 : Blo 822348 1809695 := bstep (se 1 (by rfl) ⟨1357271, by rfl⟩ : syracuseStep 1809695 = 2714543) B2714543
theorem B4693463 : Blo 822348 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B4169231 : Blo 822348 4169231 := bstep (se 1 (by rfl) ⟨3126923, by rfl⟩ : syracuseStep 4169231 = 6253847) B6253847
theorem B6266483 : Blo 822348 6266483 := bstep (se 1 (by rfl) ⟨4699862, by rfl⟩ : syracuseStep 6266483 = 9399725) B9399725
theorem B990955 : Blo 822348 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B1875719 : Blo 822348 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B925519 : Blo 822348 925519 := bstep (se 1 (by rfl) ⟨694139, by rfl⟩ : syracuseStep 925519 = 1388279) B1388279
theorem B7905185 : Blo 822348 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B925915 : Blo 822348 925915 := bstep (se 1 (by rfl) ⟨694436, by rfl⟩ : syracuseStep 925915 = 1388873) B1388873
theorem B3514715 : Blo 822348 3514715 := bstep (se 1 (by rfl) ⟨2636036, by rfl⟩ : syracuseStep 3514715 = 5272073) B5272073
theorem B4170203 : Blo 822348 4170203 := bstep (se 1 (by rfl) ⟨3127652, by rfl⟩ : syracuseStep 4170203 = 6255305) B6255305
theorem B926203 : Blo 822348 926203 := bstep (se 1 (by rfl) ⟨694652, by rfl⟩ : syracuseStep 926203 = 1389305) B1389305
theorem B926383 : Blo 822348 926383 := bstep (se 1 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 926383 = 1389575) B1389575
theorem B1876879 : Blo 822348 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B1319851 : Blo 822348 1319851 := bstep (se 1 (by rfl) ⟨989888, by rfl⟩ : syracuseStep 1319851 = 1979777) B1979777
theorem B4170689 : Blo 822348 4170689 := bstep (se 2 (by rfl) ⟨1564008, by rfl⟩ : syracuseStep 4170689 = 3128017) B3128017
theorem B926671 : Blo 822348 926671 := bstep (se 1 (by rfl) ⟨695003, by rfl⟩ : syracuseStep 926671 = 1390007) B1390007
theorem B10003445 : Blo 822348 10003445 := bstep (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) B937823
theorem B3515399 : Blo 822348 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B6267941 : Blo 822348 6267941 := bstep (se 4 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 6267941 = 1175239) B1175239
theorem B927067 : Blo 822348 927067 := bstep (se 1 (by rfl) ⟨695300, by rfl⟩ : syracuseStep 927067 = 1390601) B1390601
theorem B7054715 : Blo 822348 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B927175 : Blo 822348 927175 := bstep (se 1 (by rfl) ⟨695381, by rfl⟩ : syracuseStep 927175 = 1390763) B1390763
theorem B927535 : Blo 822348 927535 := bstep (se 1 (by rfl) ⟨695651, by rfl⟩ : syracuseStep 927535 = 1391303) B1391303
theorem B1320761 : Blo 822348 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B7153541 : Blo 822348 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B927643 : Blo 822348 927643 := bstep (se 1 (by rfl) ⟨695732, by rfl⟩ : syracuseStep 927643 = 1391465) B1391465
theorem B1484905 : Blo 822348 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B928039 : Blo 822348 928039 := bstep (se 1 (by rfl) ⟨696029, by rfl⟩ : syracuseStep 928039 = 1392059) B1392059
theorem B7907645 : Blo 822348 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B928111 : Blo 822348 928111 := bstep (se 1 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 928111 = 1392167) B1392167
theorem B928327 : Blo 822348 928327 := bstep (se 1 (by rfl) ⟨696245, by rfl⟩ : syracuseStep 928327 = 1392491) B1392491
theorem B3517175 : Blo 822348 3517175 := bstep (se 1 (by rfl) ⟨2637881, by rfl⟩ : syracuseStep 3517175 = 5275763) B5275763
theorem B1387739 : Blo 822348 1387739 := bstep (se 1 (by rfl) ⟨1040804, by rfl⟩ : syracuseStep 1387739 = 2081609) B2081609
theorem B929191 : Blo 822348 929191 := bstep (se 1 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 929191 = 1393787) B1393787
theorem B1387975 : Blo 822348 1387975 := bstep (se 1 (by rfl) ⟨1040981, by rfl⟩ : syracuseStep 1387975 = 2081963) B2081963
theorem B1388495 : Blo 822348 1388495 := bstep (se 1 (by rfl) ⟨1041371, by rfl⟩ : syracuseStep 1388495 = 2082743) B2082743
theorem B3518473 : Blo 822348 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B4173929 : Blo 822348 4173929 := bstep (se 2 (by rfl) ⟨1565223, by rfl⟩ : syracuseStep 4173929 = 3130447) B3130447
theorem B4698587 : Blo 822348 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B1389163 : Blo 822348 1389163 := bstep (se 1 (by rfl) ⟨1041872, by rfl⟩ : syracuseStep 1389163 = 2083745) B2083745
theorem B2011895 : Blo 822348 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B1389467 : Blo 822348 1389467 := bstep (se 1 (by rfl) ⟨1042100, by rfl⟩ : syracuseStep 1389467 = 2084201) B2084201
theorem B2634743 : Blo 822348 2634743 := bstep (se 1 (by rfl) ⟨1976057, by rfl⟩ : syracuseStep 2634743 = 3952115) B3952115
theorem B3519703 : Blo 822348 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B4175063 : Blo 822348 4175063 := bstep (se 1 (by rfl) ⟨3131297, by rfl⟩ : syracuseStep 4175063 = 6262595) B6262595
theorem B2635051 : Blo 822348 2635051 := bstep (se 1 (by rfl) ⟨1976288, by rfl⟩ : syracuseStep 2635051 = 3952577) B3952577
theorem B1783379 : Blo 822348 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B1980065 : Blo 822348 1980065 := bstep (se 2 (by rfl) ⟨742524, by rfl⟩ : syracuseStep 1980065 = 1485049) B1485049
theorem B2505143 : Blo 822348 2505143 := bstep (se 1 (by rfl) ⟨1878857, by rfl⟩ : syracuseStep 2505143 = 3757715) B3757715
theorem B1981007 : Blo 822348 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B3128003 : Blo 822348 3128003 := bstep (se 1 (by rfl) ⟨2346002, by rfl⟩ : syracuseStep 3128003 = 4692005) B4692005
theorem B6273773 : Blo 822348 6273773 := bstep (se 3 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 6273773 = 2352665) B2352665
theorem B2964215 : Blo 822348 2964215 := bstep (se 1 (by rfl) ⟨2223161, by rfl⟩ : syracuseStep 2964215 = 4446323) B4446323
theorem B2342027 : Blo 822348 2342027 := bstep (se 1 (by rfl) ⟨1756520, by rfl⟩ : syracuseStep 2342027 = 3513041) B3513041
theorem B4767113 : Blo 822348 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B1588729 : Blo 822348 1588729 := bstep (se 2 (by rfl) ⟨595773, by rfl⟩ : syracuseStep 1588729 = 1191547) B1191547
theorem B2342483 : Blo 822348 2342483 := bstep (se 1 (by rfl) ⟨1756862, by rfl⟩ : syracuseStep 2342483 = 3513725) B3513725
theorem B1850975 : Blo 822348 1850975 := bstep (se 1 (by rfl) ⟨1388231, by rfl⟩ : syracuseStep 1850975 = 2776463) B2776463
theorem B4701959 : Blo 822348 4701959 := bstep (se 1 (by rfl) ⟨3526469, by rfl⟩ : syracuseStep 4701959 = 7052939) B7052939
theorem B1851191 : Blo 822348 1851191 := bstep (se 1 (by rfl) ⟨1388393, by rfl⟩ : syracuseStep 1851191 = 2776787) B2776787
theorem B2637625 : Blo 822348 2637625 := bstep (se 2 (by rfl) ⟨989109, by rfl⟩ : syracuseStep 2637625 = 1978219) B1978219
theorem B8011649 : Blo 822348 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B835535 : Blo 822348 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B4177979 : Blo 822348 4177979 := bstep (se 1 (by rfl) ⟨3133484, by rfl⟩ : syracuseStep 4177979 = 6266969) B6266969
theorem B1851497 : Blo 822348 1851497 := bstep (se 2 (by rfl) ⟨694311, by rfl⟩ : syracuseStep 1851497 = 1388623) B1388623
theorem B1786279 : Blo 822348 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B1851983 : Blo 822348 1851983 := bstep (se 1 (by rfl) ⟨1388987, by rfl⟩ : syracuseStep 1851983 = 2777975) B2777975
theorem B1983055 : Blo 822348 1983055 := bstep (se 1 (by rfl) ⟨1487291, by rfl⟩ : syracuseStep 1983055 = 2974583) B2974583
theorem B7914185 : Blo 822348 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B1852127 : Blo 822348 1852127 := bstep (se 1 (by rfl) ⟨1389095, by rfl⟩ : syracuseStep 1852127 = 2778191) B2778191
theorem B1393375 : Blo 822348 1393375 := bstep (se 1 (by rfl) ⟨1045031, by rfl⟩ : syracuseStep 1393375 = 2090063) B2090063
theorem B5948153 : Blo 822348 5948153 := bstep (se 2 (by rfl) ⟨2230557, by rfl⟩ : syracuseStep 5948153 = 4461115) B4461115
theorem B1426331 : Blo 822348 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B23774147 : Blo 822348 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B1852379 : Blo 822348 1852379 := bstep (se 1 (by rfl) ⟨1389284, by rfl⟩ : syracuseStep 1852379 = 2778569) B2778569
theorem B4178951 : Blo 822348 4178951 := bstep (se 1 (by rfl) ⟨3134213, by rfl⟩ : syracuseStep 4178951 = 6268427) B6268427
theorem B1852559 : Blo 822348 1852559 := bstep (se 1 (by rfl) ⟨1389419, by rfl⟩ : syracuseStep 1852559 = 2778839) B2778839
theorem B1393807 : Blo 822348 1393807 := bstep (se 1 (by rfl) ⟨1045355, by rfl⟩ : syracuseStep 1393807 = 2090711) B2090711
theorem B1852649 : Blo 822348 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B1852703 : Blo 822348 1852703 := bstep (se 1 (by rfl) ⟨1389527, by rfl⟩ : syracuseStep 1852703 = 2779055) B2779055
theorem B2082145 : Blo 822348 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B1394057 : Blo 822348 1394057 := bstep (se 2 (by rfl) ⟨522771, by rfl⟩ : syracuseStep 1394057 = 1045543) B1045543
theorem B3524077 : Blo 822348 3524077 := bstep (se 3 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 3524077 = 1321529) B1321529
theorem B4179437 : Blo 822348 4179437 := bstep (se 3 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 4179437 = 1567289) B1567289
theorem B7914995 : Blo 822348 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B1853225 : Blo 822348 1853225 := bstep (se 2 (by rfl) ⟨694959, by rfl⟩ : syracuseStep 1853225 = 1389919) B1389919
theorem B4180247 : Blo 822348 4180247 := bstep (se 1 (by rfl) ⟨3135185, by rfl⟩ : syracuseStep 4180247 = 6270371) B6270371
theorem B2083097 : Blo 822348 2083097 := bstep (se 2 (by rfl) ⟨781161, by rfl⟩ : syracuseStep 2083097 = 1562323) B1562323
theorem B7031069 : Blo 822348 7031069 := bstep (se 3 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 7031069 = 2636651) B2636651
theorem B2345399 : Blo 822348 2345399 := bstep (se 1 (by rfl) ⟨1759049, by rfl⟩ : syracuseStep 2345399 = 3518099) B3518099
theorem B2083391 : Blo 822348 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B2083603 : Blo 822348 2083603 := bstep (se 1 (by rfl) ⟨1562702, by rfl⟩ : syracuseStep 2083603 = 3125405) B3125405
theorem B3132179 : Blo 822348 3132179 := bstep (se 1 (by rfl) ⟨2349134, by rfl⟩ : syracuseStep 3132179 = 4698269) B4698269
theorem B1854287 : Blo 822348 1854287 := bstep (se 1 (by rfl) ⟨1390715, by rfl⟩ : syracuseStep 1854287 = 2781431) B2781431
theorem B1854503 : Blo 822348 1854503 := bstep (se 1 (by rfl) ⟨1390877, by rfl⟩ : syracuseStep 1854503 = 2781755) B2781755
theorem B2084039 : Blo 822348 2084039 := bstep (se 1 (by rfl) ⟨1563029, by rfl⟩ : syracuseStep 2084039 = 3126059) B3126059
theorem B1854683 : Blo 822348 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B2084089 : Blo 822348 2084089 := bstep (se 2 (by rfl) ⟨781533, by rfl⟩ : syracuseStep 2084089 = 1563067) B1563067
theorem B7032095 : Blo 822348 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B1854881 : Blo 822348 1854881 := bstep (se 2 (by rfl) ⟨695580, by rfl⟩ : syracuseStep 1854881 = 1391161) B1391161
theorem B2379223 : Blo 822348 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B2674291 : Blo 822348 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B4706059 : Blo 822348 4706059 := bstep (se 1 (by rfl) ⟨3529544, by rfl⟩ : syracuseStep 4706059 = 7059089) B7059089
theorem B4181867 : Blo 822348 4181867 := bstep (se 1 (by rfl) ⟨3136400, by rfl⟩ : syracuseStep 4181867 = 6272801) B6272801
theorem B2084737 : Blo 822348 2084737 := bstep (se 2 (by rfl) ⟨781776, by rfl⟩ : syracuseStep 2084737 = 1563553) B1563553
theorem B1855439 : Blo 822348 1855439 := bstep (se 1 (by rfl) ⟨1391579, by rfl⟩ : syracuseStep 1855439 = 2783159) B2783159
theorem B2117657 : Blo 822348 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B1855817 : Blo 822348 1855817 := bstep (se 2 (by rfl) ⟨695931, by rfl⟩ : syracuseStep 1855817 = 1391863) B1391863
theorem B1855835 : Blo 822348 1855835 := bstep (se 1 (by rfl) ⟨1391876, by rfl⟩ : syracuseStep 1855835 = 2783753) B2783753
theorem B3166571 : Blo 822348 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B938407 : Blo 822348 938407 := bstep (se 1 (by rfl) ⟨703805, by rfl⟩ : syracuseStep 938407 = 1407611) B1407611
theorem B17814005 : Blo 822348 17814005 := bstep (se 5 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 17814005 = 1670063) B1670063
theorem B2085497 : Blo 822348 2085497 := bstep (se 2 (by rfl) ⟨782061, by rfl⟩ : syracuseStep 2085497 = 1564123) B1564123
theorem B2085547 : Blo 822348 2085547 := bstep (se 1 (by rfl) ⟨1564160, by rfl⟩ : syracuseStep 2085547 = 3128321) B3128321
theorem B3134123 : Blo 822348 3134123 := bstep (se 1 (by rfl) ⟨2350592, by rfl⟩ : syracuseStep 3134123 = 4701185) B4701185
theorem B1233743 : Blo 822348 1233743 := bstep (se 1 (by rfl) ⟨925307, by rfl⟩ : syracuseStep 1233743 = 1850615) B1850615
theorem B1856411 : Blo 822348 1856411 := bstep (se 1 (by rfl) ⟨1392308, by rfl⟩ : syracuseStep 1856411 = 2784617) B2784617
theorem B2085851 : Blo 822348 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B2511847 : Blo 822348 2511847 := bstep (se 1 (by rfl) ⟨1883885, by rfl⟩ : syracuseStep 2511847 = 3767771) B3767771
theorem B1856609 : Blo 822348 1856609 := bstep (se 2 (by rfl) ⟨696228, by rfl⟩ : syracuseStep 1856609 = 1392457) B1392457
theorem B7918717 : Blo 822348 7918717 := bstep (se 3 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 7918717 = 2969519) B2969519
theorem B3527837 : Blo 822348 3527837 := bstep (se 3 (by rfl) ⟨661469, by rfl⟩ : syracuseStep 3527837 = 1322939) B1322939
theorem B16897241 : Blo 822348 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B1234139 : Blo 822348 1234139 := bstep (se 1 (by rfl) ⟨925604, by rfl⟩ : syracuseStep 1234139 = 1851209) B1851209
theorem B2643187 : Blo 822348 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B2086175 : Blo 822348 2086175 := bstep (se 1 (by rfl) ⟨1564631, by rfl⟩ : syracuseStep 2086175 = 3129263) B3129263
theorem B1758503 : Blo 822348 1758503 := bstep (se 1 (by rfl) ⟨1318877, by rfl⟩ : syracuseStep 1758503 = 2637755) B2637755
theorem B1856807 : Blo 822348 1856807 := bstep (se 1 (by rfl) ⟨1392605, by rfl⟩ : syracuseStep 1856807 = 2785211) B2785211
theorem B1234313 : Blo 822348 1234313 := bstep (se 2 (by rfl) ⟨462867, by rfl⟩ : syracuseStep 1234313 = 925735) B925735
theorem B2971019 : Blo 822348 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B1857185 : Blo 822348 1857185 := bstep (se 2 (by rfl) ⟨696444, by rfl⟩ : syracuseStep 1857185 = 1392889) B1392889
theorem B1234667 : Blo 822348 1234667 := bstep (se 1 (by rfl) ⟨926000, by rfl⟩ : syracuseStep 1234667 = 1852001) B1852001
theorem B1234895 : Blo 822348 1234895 := bstep (se 1 (by rfl) ⟨926171, by rfl⟩ : syracuseStep 1234895 = 1852343) B1852343
theorem B1857545 : Blo 822348 1857545 := bstep (se 2 (by rfl) ⟨696579, by rfl⟩ : syracuseStep 1857545 = 1393159) B1393159
theorem B7919947 : Blo 822348 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B1235291 : Blo 822348 1235291 := bstep (se 1 (by rfl) ⟨926468, by rfl⟩ : syracuseStep 1235291 = 1852937) B1852937
theorem B2087279 : Blo 822348 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B1857959 : Blo 822348 1857959 := bstep (se 1 (by rfl) ⟨1393469, by rfl⟩ : syracuseStep 1857959 = 2786939) B2786939
theorem B940487 : Blo 822348 940487 := bstep (se 1 (by rfl) ⟨705365, by rfl⟩ : syracuseStep 940487 = 1410731) B1410731
theorem B1858067 : Blo 822348 1858067 := bstep (se 1 (by rfl) ⟨1393550, by rfl⟩ : syracuseStep 1858067 = 2787101) B2787101
theorem B1235519 : Blo 822348 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B1858121 : Blo 822348 1858121 := bstep (se 2 (by rfl) ⟨696795, by rfl⟩ : syracuseStep 1858121 = 1393591) B1393591
theorem B10050155 : Blo 822348 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B1235639 : Blo 822348 1235639 := bstep (se 1 (by rfl) ⟨926729, by rfl⟩ : syracuseStep 1235639 = 1853459) B1853459
theorem B1760143 : Blo 822348 1760143 := bstep (se 1 (by rfl) ⟨1320107, by rfl⟩ : syracuseStep 1760143 = 2640215) B2640215
theorem B1235867 : Blo 822348 1235867 := bstep (se 1 (by rfl) ⟨926900, by rfl⟩ : syracuseStep 1235867 = 1853801) B1853801
theorem B7035821 : Blo 822348 7035821 := bstep (se 3 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 7035821 = 2638433) B2638433
theorem B1858535 : Blo 822348 1858535 := bstep (se 1 (by rfl) ⟨1393901, by rfl⟩ : syracuseStep 1858535 = 2787803) B2787803
theorem B2087927 : Blo 822348 2087927 := bstep (se 1 (by rfl) ⟨1565945, by rfl⟩ : syracuseStep 2087927 = 3131891) B3131891
theorem B5954723 : Blo 822348 5954723 := bstep (se 1 (by rfl) ⟨4466042, by rfl⟩ : syracuseStep 5954723 = 8932085) B8932085
theorem B3169469 : Blo 822348 3169469 := bstep (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) B1188551
theorem B9526493 : Blo 822348 9526493 := bstep (se 3 (by rfl) ⟨1786217, by rfl⟩ : syracuseStep 9526493 = 3572435) B3572435
theorem B1236263 : Blo 822348 1236263 := bstep (se 1 (by rfl) ⟨927197, by rfl⟩ : syracuseStep 1236263 = 1854395) B1854395
theorem B2350433 : Blo 822348 2350433 := bstep (se 2 (by rfl) ⟨881412, by rfl⟩ : syracuseStep 2350433 = 1762825) B1762825
theorem B1858913 : Blo 822348 1858913 := bstep (se 2 (by rfl) ⟨697092, by rfl⟩ : syracuseStep 1858913 = 1394185) B1394185
theorem B1236347 : Blo 822348 1236347 := bstep (se 1 (by rfl) ⟨927260, by rfl⟩ : syracuseStep 1236347 = 1854521) B1854521
theorem B1859003 : Blo 822348 1859003 := bstep (se 1 (by rfl) ⟨1394252, by rfl⟩ : syracuseStep 1859003 = 2788505) B2788505
theorem B1236473 : Blo 822348 1236473 := bstep (se 2 (by rfl) ⟨463677, by rfl⟩ : syracuseStep 1236473 = 927355) B927355
theorem B3137039 : Blo 822348 3137039 := bstep (se 1 (by rfl) ⟨2352779, by rfl⟩ : syracuseStep 3137039 = 4705559) B4705559
theorem B1859129 : Blo 822348 1859129 := bstep (se 2 (by rfl) ⟨697173, by rfl⟩ : syracuseStep 1859129 = 1394347) B1394347
theorem B1236575 : Blo 822348 1236575 := bstep (se 1 (by rfl) ⟨927431, by rfl⟩ : syracuseStep 1236575 = 1854863) B1854863
theorem B11296351 : Blo 822348 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B10542707 : Blo 822348 10542707 := bstep (se 1 (by rfl) ⟨7907030, by rfl⟩ : syracuseStep 10542707 = 15814061) B15814061
theorem B1761031 : Blo 822348 1761031 := bstep (se 1 (by rfl) ⟨1320773, by rfl⟩ : syracuseStep 1761031 = 2641547) B2641547
theorem B2350889 : Blo 822348 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B1236791 : Blo 822348 1236791 := bstep (se 1 (by rfl) ⟨927593, by rfl⟩ : syracuseStep 1236791 = 1855187) B1855187
theorem B1237097 : Blo 822348 1237097 := bstep (se 2 (by rfl) ⟨463911, by rfl⟩ : syracuseStep 1237097 = 927823) B927823
theorem B17817731 : Blo 822348 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B2777435 : Blo 822348 2777435 := bstep (se 1 (by rfl) ⟨2083076, by rfl⟩ : syracuseStep 2777435 = 4166153) B4166153
theorem B1565095 : Blo 822348 1565095 := bstep (se 1 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 1565095 = 2347643) B2347643
theorem B1237415 : Blo 822348 1237415 := bstep (se 1 (by rfl) ⟨928061, by rfl⟩ : syracuseStep 1237415 = 1856123) B1856123
theorem B1237499 : Blo 822348 1237499 := bstep (se 1 (by rfl) ⟨928124, by rfl⟩ : syracuseStep 1237499 = 1856249) B1856249
theorem B2974279 : Blo 822348 2974279 := bstep (se 1 (by rfl) ⟨2230709, by rfl⟩ : syracuseStep 2974279 = 4461419) B4461419
theorem B1237625 : Blo 822348 1237625 := bstep (se 2 (by rfl) ⟨464109, by rfl⟩ : syracuseStep 1237625 = 928219) B928219
theorem B1237679 : Blo 822348 1237679 := bstep (se 1 (by rfl) ⟨928259, by rfl⟩ : syracuseStep 1237679 = 1856519) B1856519
theorem B1237727 : Blo 822348 1237727 := bstep (se 1 (by rfl) ⟨928295, by rfl⟩ : syracuseStep 1237727 = 1856591) B1856591
theorem B1073899 : Blo 822348 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B2089871 : Blo 822348 2089871 := bstep (se 1 (by rfl) ⟨1567403, by rfl⟩ : syracuseStep 2089871 = 3134807) B3134807
theorem B1237991 : Blo 822348 1237991 := bstep (se 1 (by rfl) ⟨928493, by rfl⟩ : syracuseStep 1237991 = 1856987) B1856987
theorem B7529705 : Blo 822348 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B1238249 : Blo 822348 1238249 := bstep (se 2 (by rfl) ⟨464343, by rfl⟩ : syracuseStep 1238249 = 928687) B928687
theorem B1565983 : Blo 822348 1565983 := bstep (se 1 (by rfl) ⟨1174487, by rfl⟩ : syracuseStep 1565983 = 2348975) B2348975
theorem B1238303 : Blo 822348 1238303 := bstep (se 1 (by rfl) ⟨928727, by rfl⟩ : syracuseStep 1238303 = 1857455) B1857455
theorem B2778407 : Blo 822348 2778407 := bstep (se 1 (by rfl) ⟨2083805, by rfl⟩ : syracuseStep 2778407 = 4167611) B4167611
theorem B1238471 : Blo 822348 1238471 := bstep (se 1 (by rfl) ⟨928853, by rfl⟩ : syracuseStep 1238471 = 1857707) B1857707
theorem B878303 : Blo 822348 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B2090731 : Blo 822348 2090731 := bstep (se 1 (by rfl) ⟨1568048, by rfl⟩ : syracuseStep 2090731 = 3136097) B3136097
theorem B1238825 : Blo 822348 1238825 := bstep (se 2 (by rfl) ⟨464559, by rfl⟩ : syracuseStep 1238825 = 929119) B929119
theorem B1238831 : Blo 822348 1238831 := bstep (se 1 (by rfl) ⟨929123, by rfl⟩ : syracuseStep 1238831 = 1858247) B1858247
theorem B2779271 : Blo 822348 2779271 := bstep (se 1 (by rfl) ⟨2084453, by rfl⟩ : syracuseStep 2779271 = 4168907) B4168907
theorem B1239305 : Blo 822348 1239305 := bstep (se 2 (by rfl) ⟨464739, by rfl⟩ : syracuseStep 1239305 = 929479) B929479
theorem B1239407 : Blo 822348 1239407 := bstep (se 1 (by rfl) ⟨929555, by rfl⟩ : syracuseStep 1239407 = 1859111) B1859111
theorem B1174123 : Blo 822348 1174123 := bstep (se 1 (by rfl) ⟨880592, by rfl⟩ : syracuseStep 1174123 = 1761185) B1761185
theorem B5270305 : Blo 822348 5270305 := bstep (se 2 (by rfl) ⟨1976364, by rfl⟩ : syracuseStep 5270305 = 3952729) B3952729
theorem B1174351 : Blo 822348 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1764175 : Blo 822348 1764175 := bstep (se 1 (by rfl) ⟨1323131, by rfl⟩ : syracuseStep 1764175 = 2646263) B2646263
theorem B30043025 : Blo 822348 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B1338587 : Blo 822348 1338587 := bstep (se 1 (by rfl) ⟨1003940, by rfl⟩ : syracuseStep 1338587 = 2007881) B2007881
theorem B2780513 : Blo 822348 2780513 := bstep (se 2 (by rfl) ⟨1042692, by rfl⟩ : syracuseStep 2780513 = 2085385) B2085385
theorem B5271149 : Blo 822348 5271149 := bstep (se 3 (by rfl) ⟨988340, by rfl⟩ : syracuseStep 5271149 = 1976681) B1976681
theorem B1044191 : Blo 822348 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B3764029 : Blo 822348 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B9531341 : Blo 822348 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B17854667 : Blo 822348 17854667 := bstep (se 1 (by rfl) ⟨13391000, by rfl⟩ : syracuseStep 17854667 = 26782001) B26782001
theorem B10711601 : Blo 822348 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B881327 : Blo 822348 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B1176287 : Blo 822348 1176287 := bstep (se 1 (by rfl) ⟨882215, by rfl⟩ : syracuseStep 1176287 = 1764431) B1764431
theorem B3961819 : Blo 822348 3961819 := bstep (se 1 (by rfl) ⟨2971364, by rfl⟩ : syracuseStep 3961819 = 5942729) B5942729
theorem B3765491 : Blo 822348 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B2782457 : Blo 822348 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B15857117 : Blo 822348 15857117 := bstep (se 3 (by rfl) ⟨2973209, by rfl⟩ : syracuseStep 15857117 = 5946419) B5946419
theorem B2782727 : Blo 822348 2782727 := bstep (se 1 (by rfl) ⟨2087045, by rfl⟩ : syracuseStep 2782727 = 4174091) B4174091
theorem B14088653 : Blo 822348 14088653 := bstep (se 3 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 14088653 = 5283245) B5283245
theorem B2783699 : Blo 822348 2783699 := bstep (se 1 (by rfl) ⟨2087774, by rfl⟩ : syracuseStep 2783699 = 4175549) B4175549
theorem B4454885 : Blo 822348 4454885 := bstep (se 4 (by rfl) ⟨417645, by rfl⟩ : syracuseStep 4454885 = 835291) B835291
theorem B2783807 : Blo 822348 2783807 := bstep (se 1 (by rfl) ⟨2087855, by rfl⟩ : syracuseStep 2783807 = 4175711) B4175711
theorem B4684463 : Blo 822348 4684463 := bstep (se 1 (by rfl) ⟨3513347, by rfl⟩ : syracuseStep 4684463 = 7026695) B7026695
theorem B1112987 : Blo 822348 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B32046245 : Blo 822348 32046245 := bstep (se 4 (by rfl) ⟨3004335, by rfl⟩ : syracuseStep 32046245 = 6008671) B6008671
theorem B1604827 : Blo 822348 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B30080393 : Blo 822348 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B1146475 : Blo 822348 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B2785319 : Blo 822348 2785319 := bstep (se 1 (by rfl) ⟨2088989, by rfl⟩ : syracuseStep 2785319 = 4177979) B4177979
theorem B5276123 : Blo 822348 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B3965435 : Blo 822348 3965435 := bstep (se 1 (by rfl) ⟨2974076, by rfl⟩ : syracuseStep 3965435 = 5948153) B5948153
theorem B950887 : Blo 822348 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B2785967 : Blo 822348 2785967 := bstep (se 1 (by rfl) ⟨2089475, by rfl⟩ : syracuseStep 2785967 = 4178951) B4178951
theorem B3965705 : Blo 822348 3965705 := bstep (se 2 (by rfl) ⟨1487139, by rfl⟩ : syracuseStep 3965705 = 2974279) B2974279
theorem B2786291 : Blo 822348 2786291 := bstep (se 1 (by rfl) ⟨2089718, by rfl⟩ : syracuseStep 2786291 = 4179437) B4179437
theorem B5276663 : Blo 822348 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B2786831 : Blo 822348 2786831 := bstep (se 1 (by rfl) ⟨2090123, by rfl⟩ : syracuseStep 2786831 = 4180247) B4180247
theorem B4687379 : Blo 822348 4687379 := bstep (se 1 (by rfl) ⟨3515534, by rfl⟩ : syracuseStep 4687379 = 7031069) B7031069
theorem B4688063 : Blo 822348 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B2787641 : Blo 822348 2787641 := bstep (se 2 (by rfl) ⟨1045365, by rfl⟩ : syracuseStep 2787641 = 2090731) B2090731
theorem B2787911 : Blo 822348 2787911 := bstep (se 1 (by rfl) ⟨2090933, by rfl⟩ : syracuseStep 2787911 = 4181867) B4181867
theorem B1411771 : Blo 822348 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B9374939 : Blo 822348 9374939 := bstep (se 1 (by rfl) ⟨7031204, by rfl⟩ : syracuseStep 9374939 = 14062409) B14062409
theorem B822495 : Blo 822348 822495 := bstep (se 1 (by rfl) ⟨616871, by rfl⟩ : syracuseStep 822495 = 1233743) B1233743
theorem B822759 : Blo 822348 822759 := bstep (se 1 (by rfl) ⟨617069, by rfl⟩ : syracuseStep 822759 = 1234139) B1234139
theorem B822875 : Blo 822348 822875 := bstep (se 1 (by rfl) ⟨617156, by rfl⟩ : syracuseStep 822875 = 1234313) B1234313
theorem B823111 : Blo 822348 823111 := bstep (se 1 (by rfl) ⟨617333, by rfl⟩ : syracuseStep 823111 = 1234667) B1234667
theorem B823263 : Blo 822348 823263 := bstep (se 1 (by rfl) ⟨617447, by rfl⟩ : syracuseStep 823263 = 1234895) B1234895
theorem B2232287 : Blo 822348 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B823527 : Blo 822348 823527 := bstep (se 1 (by rfl) ⟨617645, by rfl⟩ : syracuseStep 823527 = 1235291) B1235291
theorem B823679 : Blo 822348 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B823759 : Blo 822348 823759 := bstep (se 1 (by rfl) ⟨617819, by rfl⟩ : syracuseStep 823759 = 1235639) B1235639
theorem B823911 : Blo 822348 823911 := bstep (se 1 (by rfl) ⟨617933, by rfl⟩ : syracuseStep 823911 = 1235867) B1235867
theorem B4690547 : Blo 822348 4690547 := bstep (se 1 (by rfl) ⟨3517910, by rfl⟩ : syracuseStep 4690547 = 7035821) B7035821
theorem B3969815 : Blo 822348 3969815 := bstep (se 1 (by rfl) ⟨2977361, by rfl⟩ : syracuseStep 3969815 = 5954723) B5954723
theorem B11899709 : Blo 822348 11899709 := bstep (se 3 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 11899709 = 4462391) B4462391
theorem B824175 : Blo 822348 824175 := bstep (se 1 (by rfl) ⟨618131, by rfl⟩ : syracuseStep 824175 = 1236263) B1236263
theorem B824231 : Blo 822348 824231 := bstep (se 1 (by rfl) ⟨618173, by rfl⟩ : syracuseStep 824231 = 1236347) B1236347
theorem B824315 : Blo 822348 824315 := bstep (se 1 (by rfl) ⟨618236, by rfl⟩ : syracuseStep 824315 = 1236473) B1236473
theorem B824383 : Blo 822348 824383 := bstep (se 1 (by rfl) ⟨618287, by rfl⟩ : syracuseStep 824383 = 1236575) B1236575
theorem B5018705 : Blo 822348 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B824527 : Blo 822348 824527 := bstep (se 1 (by rfl) ⟨618395, by rfl⟩ : syracuseStep 824527 = 1236791) B1236791
theorem B4691297 : Blo 822348 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B824731 : Blo 822348 824731 := bstep (se 1 (by rfl) ⟨618548, by rfl⟩ : syracuseStep 824731 = 1237097) B1237097
theorem B824943 : Blo 822348 824943 := bstep (se 1 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 824943 = 1237415) B1237415
theorem B824999 : Blo 822348 824999 := bstep (se 1 (by rfl) ⟨618749, by rfl⟩ : syracuseStep 824999 = 1237499) B1237499
theorem B825083 : Blo 822348 825083 := bstep (se 1 (by rfl) ⟨618812, by rfl⟩ : syracuseStep 825083 = 1237625) B1237625
theorem B825119 : Blo 822348 825119 := bstep (se 1 (by rfl) ⟨618839, by rfl⟩ : syracuseStep 825119 = 1237679) B1237679
theorem B825151 : Blo 822348 825151 := bstep (se 1 (by rfl) ⟨618863, by rfl⟩ : syracuseStep 825151 = 1237727) B1237727
theorem B1251209 : Blo 822348 1251209 := bstep (se 2 (by rfl) ⟨469203, by rfl⟩ : syracuseStep 1251209 = 938407) B938407
theorem B825327 : Blo 822348 825327 := bstep (se 1 (by rfl) ⟨618995, by rfl⟩ : syracuseStep 825327 = 1237991) B1237991
theorem B5019803 : Blo 822348 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B825499 : Blo 822348 825499 := bstep (se 1 (by rfl) ⟨619124, by rfl⟩ : syracuseStep 825499 = 1238249) B1238249
theorem B825535 : Blo 822348 825535 := bstep (se 1 (by rfl) ⟨619151, by rfl⟩ : syracuseStep 825535 = 1238303) B1238303
theorem B825647 : Blo 822348 825647 := bstep (se 1 (by rfl) ⟨619235, by rfl⟩ : syracuseStep 825647 = 1238471) B1238471
theorem B825883 : Blo 822348 825883 := bstep (se 1 (by rfl) ⟨619412, by rfl⟩ : syracuseStep 825883 = 1238825) B1238825
theorem B825887 : Blo 822348 825887 := bstep (se 1 (by rfl) ⟨619415, by rfl⟩ : syracuseStep 825887 = 1238831) B1238831
theorem B5282425 : Blo 822348 5282425 := bstep (se 2 (by rfl) ⟨1980909, by rfl⟩ : syracuseStep 5282425 = 3961819) B3961819
theorem B3349129 : Blo 822348 3349129 := bstep (se 2 (by rfl) ⟨1255923, by rfl⟩ : syracuseStep 3349129 = 2511847) B2511847
theorem B10558289 : Blo 822348 10558289 := bstep (se 2 (by rfl) ⟨3959358, by rfl⟩ : syracuseStep 10558289 = 7918717) B7918717
theorem B826203 : Blo 822348 826203 := bstep (se 1 (by rfl) ⟨619652, by rfl⟩ : syracuseStep 826203 = 1239305) B1239305
theorem B826271 : Blo 822348 826271 := bstep (se 1 (by rfl) ⟨619703, by rfl⟩ : syracuseStep 826271 = 1239407) B1239407
theorem B4692937 : Blo 822348 4692937 := bstep (se 2 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 4692937 = 3519703) B3519703
theorem B3513401 : Blo 822348 3513401 := bstep (se 2 (by rfl) ⟨1317525, by rfl⟩ : syracuseStep 3513401 = 2635051) B2635051
theorem B20028683 : Blo 822348 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B1318313 : Blo 822348 1318313 := bstep (se 2 (by rfl) ⟨494367, by rfl⟩ : syracuseStep 1318313 = 988735) B988735
theorem B925159 : Blo 822348 925159 := bstep (se 1 (by rfl) ⟨693869, by rfl⟩ : syracuseStep 925159 = 1387739) B1387739
theorem B892391 : Blo 822348 892391 := bstep (se 1 (by rfl) ⟨669293, by rfl⟩ : syracuseStep 892391 = 1338587) B1338587
theorem B3514099 : Blo 822348 3514099 := bstep (se 1 (by rfl) ⟨2635574, by rfl⟩ : syracuseStep 3514099 = 5271149) B5271149
theorem B925663 : Blo 822348 925663 := bstep (se 1 (by rfl) ⟨694247, by rfl⟩ : syracuseStep 925663 = 1388495) B1388495
theorem B11903111 : Blo 822348 11903111 := bstep (se 1 (by rfl) ⟨8927333, by rfl⟩ : syracuseStep 11903111 = 17854667) B17854667
theorem B10559929 : Blo 822348 10559929 := bstep (se 2 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 10559929 = 7919947) B7919947
theorem B926311 : Blo 822348 926311 := bstep (se 1 (by rfl) ⟨694733, by rfl⟩ : syracuseStep 926311 = 1389467) B1389467
theorem B1188919 : Blo 822348 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B1320043 : Blo 822348 1320043 := bstep (se 1 (by rfl) ⟨990032, by rfl⟩ : syracuseStep 1320043 = 1980065) B1980065
theorem B2139769 : Blo 822348 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B1320671 : Blo 822348 1320671 := bstep (se 1 (by rfl) ⟨990503, by rfl⟩ : syracuseStep 1320671 = 1981007) B1981007
theorem B3122975 : Blo 822348 3122975 := bstep (se 1 (by rfl) ⟨2342231, by rfl⟩ : syracuseStep 3122975 = 4684463) B4684463
theorem B1976143 : Blo 822348 1976143 := bstep (se 1 (by rfl) ⟨1482107, by rfl⟩ : syracuseStep 1976143 = 2964215) B2964215
theorem B1321273 : Blo 822348 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B3516833 : Blo 822348 3516833 := bstep (se 2 (by rfl) ⟨1318812, by rfl⟩ : syracuseStep 3516833 = 2637625) B2637625
theorem B4172471 : Blo 822348 4172471 := bstep (se 1 (by rfl) ⟨3129353, by rfl⟩ : syracuseStep 4172471 = 6258707) B6258707
theorem B929371 : Blo 822348 929371 := bstep (se 1 (by rfl) ⟨697028, by rfl⟩ : syracuseStep 929371 = 1394057) B1394057
theorem B2502505 : Blo 822348 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B5025665 : Blo 822348 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B1388731 : Blo 822348 1388731 := bstep (se 1 (by rfl) ⟨1041548, by rfl⟩ : syracuseStep 1388731 = 2083097) B2083097
theorem B1388927 : Blo 822348 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B4698769 : Blo 822348 4698769 := bstep (se 2 (by rfl) ⟨1762038, by rfl⟩ : syracuseStep 4698769 = 3524077) B3524077
theorem B1389359 : Blo 822348 1389359 := bstep (se 1 (by rfl) ⟨1042019, by rfl⟩ : syracuseStep 1389359 = 2084039) B2084039
theorem B1979873 : Blo 822348 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B11876003 : Blo 822348 11876003 := bstep (se 1 (by rfl) ⟨8907002, by rfl⟩ : syracuseStep 11876003 = 17814005) B17814005
theorem B1390331 : Blo 822348 1390331 := bstep (se 1 (by rfl) ⟨1042748, by rfl⟩ : syracuseStep 1390331 = 2085497) B2085497
theorem B1390567 : Blo 822348 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B1390783 : Blo 822348 1390783 := bstep (se 1 (by rfl) ⟨1043087, by rfl⟩ : syracuseStep 1390783 = 2086175) B2086175
theorem B5290217 : Blo 822348 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B7027073 : Blo 822348 7027073 := bstep (se 2 (by rfl) ⟨2635152, by rfl⟩ : syracuseStep 7027073 = 5270305) B5270305
theorem B11909855 : Blo 822348 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B1391519 : Blo 822348 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B9026599 : Blo 822348 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B6700103 : Blo 822348 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B3128503 : Blo 822348 3128503 := bstep (se 1 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 3128503 = 4692755) B4692755
theorem B2342141 : Blo 822348 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B1850633 : Blo 822348 1850633 := bstep (se 2 (by rfl) ⟨693987, by rfl⟩ : syracuseStep 1850633 = 1387975) B1387975
theorem B1391951 : Blo 822348 1391951 := bstep (se 1 (by rfl) ⟨1043963, by rfl⟩ : syracuseStep 1391951 = 2087927) B2087927
theorem B2112979 : Blo 822348 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B3128975 : Blo 822348 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B6274745 : Blo 822348 6274745 := bstep (se 2 (by rfl) ⟨2353029, by rfl⟩ : syracuseStep 6274745 = 4706059) B4706059
theorem B7028471 : Blo 822348 7028471 := bstep (se 1 (by rfl) ⟨5271353, by rfl⟩ : syracuseStep 7028471 = 10542707) B10542707
theorem B4177655 : Blo 822348 4177655 := bstep (se 1 (by rfl) ⟨3133241, by rfl⟩ : syracuseStep 4177655 = 6266483) B6266483
theorem B11878487 : Blo 822348 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B2343143 : Blo 822348 2343143 := bstep (se 1 (by rfl) ⟨1757357, by rfl⟩ : syracuseStep 2343143 = 3514715) B3514715
theorem B1851623 : Blo 822348 1851623 := bstep (se 1 (by rfl) ⟨1388717, by rfl⟩ : syracuseStep 1851623 = 2777435) B2777435
theorem B1393247 : Blo 822348 1393247 := bstep (se 1 (by rfl) ⟨1044935, by rfl⟩ : syracuseStep 1393247 = 2089871) B2089871
theorem B6668963 : Blo 822348 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B2343599 : Blo 822348 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B4178627 : Blo 822348 4178627 := bstep (se 1 (by rfl) ⟨3133970, by rfl⟩ : syracuseStep 4178627 = 6267941) B6267941
theorem B1852217 : Blo 822348 1852217 := bstep (se 2 (by rfl) ⟨694581, by rfl⟩ : syracuseStep 1852217 = 1389163) B1389163
theorem B21087053 : Blo 822348 21087053 := bstep (se 3 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 21087053 = 7907645) B7907645
theorem B1852271 : Blo 822348 1852271 := bstep (se 1 (by rfl) ⟨1389203, by rfl⟩ : syracuseStep 1852271 = 2778407) B2778407
theorem B4703143 : Blo 822348 4703143 := bstep (se 1 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 4703143 = 7054715) B7054715
theorem B5292985 : Blo 822348 5292985 := bstep (se 2 (by rfl) ⟨1984869, by rfl⟩ : syracuseStep 5292985 = 3969739) B3969739
theorem B2507965 : Blo 822348 2507965 := bstep (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) B940487
theorem B4769027 : Blo 822348 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B11879693 : Blo 822348 11879693 := bstep (se 3 (by rfl) ⟨2227442, by rfl⟩ : syracuseStep 11879693 = 4454885) B4454885
theorem B1852847 : Blo 822348 1852847 := bstep (se 1 (by rfl) ⟨1389635, by rfl⟩ : syracuseStep 1852847 = 2779271) B2779271
theorem B3524249 : Blo 822348 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B2344783 : Blo 822348 2344783 := bstep (se 1 (by rfl) ⟨1758587, by rfl⟩ : syracuseStep 2344783 = 3517175) B3517175
theorem B1853675 : Blo 822348 1853675 := bstep (se 1 (by rfl) ⟨1390256, by rfl⟩ : syracuseStep 1853675 = 2780513) B2780513
theorem B2967965 : Blo 822348 2967965 := bstep (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) B1112987
theorem B3132391 : Blo 822348 3132391 := bstep (se 1 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 3132391 = 4698587) B4698587
theorem B1756495 : Blo 822348 1756495 := bstep (se 1 (by rfl) ⟨1317371, by rfl⟩ : syracuseStep 1756495 = 2634743) B2634743
theorem B2510327 : Blo 822348 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B1854971 : Blo 822348 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B10571411 : Blo 822348 10571411 := bstep (se 1 (by rfl) ⟨7928558, by rfl⟩ : syracuseStep 10571411 = 15857117) B15857117
theorem B1855151 : Blo 822348 1855151 := bstep (se 1 (by rfl) ⟨1391363, by rfl⟩ : syracuseStep 1855151 = 2782727) B2782727
theorem B2346857 : Blo 822348 2346857 := bstep (se 2 (by rfl) ⟨880071, by rfl⟩ : syracuseStep 2346857 = 1760143) B1760143
theorem B9392435 : Blo 822348 9392435 := bstep (se 1 (by rfl) ⟨7044326, by rfl⟩ : syracuseStep 9392435 = 14088653) B14088653
theorem B1855799 : Blo 822348 1855799 := bstep (se 1 (by rfl) ⟨1391849, by rfl⟩ : syracuseStep 1855799 = 2783699) B2783699
theorem B1855871 : Blo 822348 1855871 := bstep (se 1 (by rfl) ⟨1391903, by rfl⟩ : syracuseStep 1855871 = 2783807) B2783807
theorem B2085335 : Blo 822348 2085335 := bstep (se 1 (by rfl) ⟨1564001, by rfl⟩ : syracuseStep 2085335 = 3128003) B3128003
theorem B4182515 : Blo 822348 4182515 := bstep (se 1 (by rfl) ⟨3136886, by rfl⟩ : syracuseStep 4182515 = 6273773) B6273773
theorem B2118305 : Blo 822348 2118305 := bstep (se 2 (by rfl) ⟨794364, by rfl⟩ : syracuseStep 2118305 = 1588729) B1588729
theorem B5001917 : Blo 822348 5001917 := bstep (se 3 (by rfl) ⟨937859, by rfl⟩ : syracuseStep 5001917 = 1875719) B1875719
theorem B1561351 : Blo 822348 1561351 := bstep (se 1 (by rfl) ⟨1171013, by rfl⟩ : syracuseStep 1561351 = 2342027) B2342027
theorem B15061801 : Blo 822348 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B1528633 : Blo 822348 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B2348041 : Blo 822348 2348041 := bstep (se 2 (by rfl) ⟨880515, by rfl⟩ : syracuseStep 2348041 = 1761031) B1761031
theorem B1561655 : Blo 822348 1561655 := bstep (se 1 (by rfl) ⟨1171241, by rfl⟩ : syracuseStep 1561655 = 2342483) B2342483
theorem B1233983 : Blo 822348 1233983 := bstep (se 1 (by rfl) ⟨925487, by rfl⟩ : syracuseStep 1233983 = 1850975) B1850975
theorem B1234025 : Blo 822348 1234025 := bstep (se 2 (by rfl) ⟨462759, by rfl⟩ : syracuseStep 1234025 = 925519) B925519
theorem B3134639 : Blo 822348 3134639 := bstep (se 1 (by rfl) ⟨2350979, by rfl⟩ : syracuseStep 3134639 = 4701959) B4701959
theorem B1234127 : Blo 822348 1234127 := bstep (se 1 (by rfl) ⟨925595, by rfl⟩ : syracuseStep 1234127 = 1851191) B1851191
theorem B1234331 : Blo 822348 1234331 := bstep (se 1 (by rfl) ⟨925748, by rfl⟩ : syracuseStep 1234331 = 1851497) B1851497
theorem B23811509 : Blo 822348 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B2971079 : Blo 822348 2971079 := bstep (se 1 (by rfl) ⟨2228309, by rfl⟩ : syracuseStep 2971079 = 4456619) B4456619
theorem B1857095 : Blo 822348 1857095 := bstep (se 1 (by rfl) ⟨1392821, by rfl⟩ : syracuseStep 1857095 = 2785643) B2785643
theorem B1234553 : Blo 822348 1234553 := bstep (se 2 (by rfl) ⟨462957, by rfl⟩ : syracuseStep 1234553 = 925915) B925915
theorem B1234655 : Blo 822348 1234655 := bstep (se 1 (by rfl) ⟨925991, by rfl⟩ : syracuseStep 1234655 = 1851983) B1851983
theorem B1857275 : Blo 822348 1857275 := bstep (se 1 (by rfl) ⟨1392956, by rfl⟩ : syracuseStep 1857275 = 2785913) B2785913
theorem B1234751 : Blo 822348 1234751 := bstep (se 1 (by rfl) ⟨926063, by rfl⟩ : syracuseStep 1234751 = 1852127) B1852127
theorem B7034759 : Blo 822348 7034759 := bstep (se 1 (by rfl) ⟨5276069, by rfl⟩ : syracuseStep 7034759 = 10552139) B10552139
theorem B2086793 : Blo 822348 2086793 := bstep (se 2 (by rfl) ⟨782547, by rfl⟩ : syracuseStep 2086793 = 1565095) B1565095
theorem B2381705 : Blo 822348 2381705 := bstep (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) B1786279
theorem B15849431 : Blo 822348 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B1234919 : Blo 822348 1234919 := bstep (se 1 (by rfl) ⟨926189, by rfl⟩ : syracuseStep 1234919 = 1852379) B1852379
theorem B1234937 : Blo 822348 1234937 := bstep (se 2 (by rfl) ⟨463101, by rfl⟩ : syracuseStep 1234937 = 926203) B926203
theorem B1235039 : Blo 822348 1235039 := bstep (se 1 (by rfl) ⟨926279, by rfl⟩ : syracuseStep 1235039 = 1852559) B1852559
theorem B2644073 : Blo 822348 2644073 := bstep (se 2 (by rfl) ⟨991527, by rfl⟩ : syracuseStep 2644073 = 1983055) B1983055
theorem B1235099 : Blo 822348 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B1235135 : Blo 822348 1235135 := bstep (se 1 (by rfl) ⟨926351, by rfl⟩ : syracuseStep 1235135 = 1852703) B1852703
theorem B1235177 : Blo 822348 1235177 := bstep (se 2 (by rfl) ⟨463191, by rfl⟩ : syracuseStep 1235177 = 926383) B926383
theorem B8444189 : Blo 822348 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1857833 : Blo 822348 1857833 := bstep (se 2 (by rfl) ⟨696687, by rfl⟩ : syracuseStep 1857833 = 1393375) B1393375
theorem B1431865 : Blo 822348 1431865 := bstep (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) B1073899
theorem B1235483 : Blo 822348 1235483 := bstep (se 1 (by rfl) ⟨926612, by rfl⟩ : syracuseStep 1235483 = 1853225) B1853225
theorem B1759801 : Blo 822348 1759801 := bstep (se 2 (by rfl) ⟨659925, by rfl⟩ : syracuseStep 1759801 = 1319851) B1319851
theorem B1235561 : Blo 822348 1235561 := bstep (se 2 (by rfl) ⟨463335, by rfl⟩ : syracuseStep 1235561 = 926671) B926671
theorem B3955499 : Blo 822348 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B23780141 : Blo 822348 23780141 := bstep (se 3 (by rfl) ⟨4458776, by rfl⟩ : syracuseStep 23780141 = 8917553) B8917553
theorem B1858409 : Blo 822348 1858409 := bstep (se 2 (by rfl) ⟨696903, by rfl⟩ : syracuseStep 1858409 = 1393807) B1393807
theorem B1858463 : Blo 822348 1858463 := bstep (se 1 (by rfl) ⟨1393847, by rfl⟩ : syracuseStep 1858463 = 2787695) B2787695
theorem B1563599 : Blo 822348 1563599 := bstep (se 1 (by rfl) ⟨1172699, by rfl⟩ : syracuseStep 1563599 = 2345399) B2345399
theorem B2087977 : Blo 822348 2087977 := bstep (se 2 (by rfl) ⟨782991, by rfl⟩ : syracuseStep 2087977 = 1565983) B1565983
theorem B1236089 : Blo 822348 1236089 := bstep (se 2 (by rfl) ⟨463533, by rfl⟩ : syracuseStep 1236089 = 927067) B927067
theorem B2350205 : Blo 822348 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B2776193 : Blo 822348 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B2776247 : Blo 822348 2776247 := bstep (se 1 (by rfl) ⟨2082185, by rfl⟩ : syracuseStep 2776247 = 4164371) B4164371
theorem B2088119 : Blo 822348 2088119 := bstep (se 1 (by rfl) ⟨1566089, by rfl⟩ : syracuseStep 2088119 = 3132179) B3132179
theorem B1236191 : Blo 822348 1236191 := bstep (se 1 (by rfl) ⟨927143, by rfl⟩ : syracuseStep 1236191 = 1854287) B1854287
theorem B3136765 : Blo 822348 3136765 := bstep (se 3 (by rfl) ⟨588143, by rfl⟩ : syracuseStep 3136765 = 1176287) B1176287
theorem B1236233 : Blo 822348 1236233 := bstep (se 2 (by rfl) ⟨463587, by rfl⟩ : syracuseStep 1236233 = 927175) B927175
theorem B1236335 : Blo 822348 1236335 := bstep (se 1 (by rfl) ⟨927251, by rfl⟩ : syracuseStep 1236335 = 1854503) B1854503
theorem B1236455 : Blo 822348 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B1236587 : Blo 822348 1236587 := bstep (se 1 (by rfl) ⟨927440, by rfl⟩ : syracuseStep 1236587 = 1854881) B1854881
theorem B1236713 : Blo 822348 1236713 := bstep (se 2 (by rfl) ⟨463767, by rfl⟩ : syracuseStep 1236713 = 927535) B927535
theorem B1236857 : Blo 822348 1236857 := bstep (se 2 (by rfl) ⟨463821, by rfl⟩ : syracuseStep 1236857 = 927643) B927643
theorem B2777003 : Blo 822348 2777003 := bstep (se 1 (by rfl) ⟨2082752, by rfl⟩ : syracuseStep 2777003 = 4165505) B4165505
theorem B1236959 : Blo 822348 1236959 := bstep (se 1 (by rfl) ⟨927719, by rfl⟩ : syracuseStep 1236959 = 1855439) B1855439
theorem B1237211 : Blo 822348 1237211 := bstep (se 1 (by rfl) ⟨927908, by rfl⟩ : syracuseStep 1237211 = 1855817) B1855817
theorem B1237223 : Blo 822348 1237223 := bstep (se 1 (by rfl) ⟨927917, by rfl⟩ : syracuseStep 1237223 = 1855835) B1855835
theorem B2646391 : Blo 822348 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B1237385 : Blo 822348 1237385 := bstep (se 2 (by rfl) ⟨464019, by rfl⟩ : syracuseStep 1237385 = 928039) B928039
theorem B2777543 : Blo 822348 2777543 := bstep (se 1 (by rfl) ⟨2083157, by rfl⟩ : syracuseStep 2777543 = 4166315) B4166315
theorem B2089415 : Blo 822348 2089415 := bstep (se 1 (by rfl) ⟨1567061, by rfl⟩ : syracuseStep 2089415 = 3134123) B3134123
theorem B1237481 : Blo 822348 1237481 := bstep (se 2 (by rfl) ⟨464055, by rfl⟩ : syracuseStep 1237481 = 928111) B928111
theorem B1237607 : Blo 822348 1237607 := bstep (se 1 (by rfl) ⟨928205, by rfl⟩ : syracuseStep 1237607 = 1856411) B1856411
theorem B1237739 : Blo 822348 1237739 := bstep (se 1 (by rfl) ⟨928304, by rfl⟩ : syracuseStep 1237739 = 1856609) B1856609
theorem B1237769 : Blo 822348 1237769 := bstep (se 2 (by rfl) ⟨464163, by rfl⟩ : syracuseStep 1237769 = 928327) B928327
theorem B2777867 : Blo 822348 2777867 := bstep (se 1 (by rfl) ⟨2083400, by rfl⟩ : syracuseStep 2777867 = 4166801) B4166801
theorem B2351891 : Blo 822348 2351891 := bstep (se 1 (by rfl) ⟨1763918, by rfl⟩ : syracuseStep 2351891 = 3527837) B3527837
theorem B1565497 : Blo 822348 1565497 := bstep (se 2 (by rfl) ⟨587061, by rfl⟩ : syracuseStep 1565497 = 1174123) B1174123
theorem B11264827 : Blo 822348 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B1172335 : Blo 822348 1172335 := bstep (se 1 (by rfl) ⟨879251, by rfl⟩ : syracuseStep 1172335 = 1758503) B1758503
theorem B1237871 : Blo 822348 1237871 := bstep (se 1 (by rfl) ⟨928403, by rfl⟩ : syracuseStep 1237871 = 1856807) B1856807
theorem B2778137 : Blo 822348 2778137 := bstep (se 2 (by rfl) ⟨1041801, by rfl⟩ : syracuseStep 2778137 = 2083603) B2083603
theorem B7922717 : Blo 822348 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B1565801 : Blo 822348 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B2352233 : Blo 822348 2352233 := bstep (se 2 (by rfl) ⟨882087, by rfl⟩ : syracuseStep 2352233 = 1764175) B1764175
theorem B1238123 : Blo 822348 1238123 := bstep (se 1 (by rfl) ⟨928592, by rfl⟩ : syracuseStep 1238123 = 1857185) B1857185
theorem B1238363 : Blo 822348 1238363 := bstep (se 1 (by rfl) ⟨928772, by rfl⟩ : syracuseStep 1238363 = 1857545) B1857545
theorem B1238639 : Blo 822348 1238639 := bstep (se 1 (by rfl) ⟨928979, by rfl⟩ : syracuseStep 1238639 = 1857959) B1857959
theorem B2778785 : Blo 822348 2778785 := bstep (se 2 (by rfl) ⟨1042044, by rfl⟩ : syracuseStep 2778785 = 2084089) B2084089
theorem B1238711 : Blo 822348 1238711 := bstep (se 1 (by rfl) ⟨929033, by rfl⟩ : syracuseStep 1238711 = 1858067) B1858067
theorem B1238747 : Blo 822348 1238747 := bstep (se 1 (by rfl) ⟨929060, by rfl⟩ : syracuseStep 1238747 = 1858121) B1858121
theorem B1238921 : Blo 822348 1238921 := bstep (se 2 (by rfl) ⟨464595, by rfl⟩ : syracuseStep 1238921 = 929191) B929191
theorem B3172297 : Blo 822348 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B1239023 : Blo 822348 1239023 := bstep (se 1 (by rfl) ⟨929267, by rfl⟩ : syracuseStep 1239023 = 1858535) B1858535
theorem B6350995 : Blo 822348 6350995 := bstep (se 1 (by rfl) ⟨4763246, by rfl⟩ : syracuseStep 6350995 = 9526493) B9526493
theorem B3565721 : Blo 822348 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B878747 : Blo 822348 878747 := bstep (se 1 (by rfl) ⟨659060, by rfl⟩ : syracuseStep 878747 = 1318121) B1318121
theorem B1206463 : Blo 822348 1206463 := bstep (se 1 (by rfl) ⟨904847, by rfl⟩ : syracuseStep 1206463 = 1809695) B1809695
theorem B1566955 : Blo 822348 1566955 := bstep (se 1 (by rfl) ⟨1175216, by rfl⟩ : syracuseStep 1566955 = 2350433) B2350433
theorem B1239275 : Blo 822348 1239275 := bstep (se 1 (by rfl) ⟨929456, by rfl⟩ : syracuseStep 1239275 = 1858913) B1858913
theorem B1239335 : Blo 822348 1239335 := bstep (se 1 (by rfl) ⟨929501, by rfl⟩ : syracuseStep 1239335 = 1859003) B1859003
theorem B2779487 : Blo 822348 2779487 := bstep (se 1 (by rfl) ⟨2084615, by rfl⟩ : syracuseStep 2779487 = 4169231) B4169231
theorem B2091359 : Blo 822348 2091359 := bstep (se 1 (by rfl) ⟨1568519, by rfl⟩ : syracuseStep 2091359 = 3137039) B3137039
theorem B1239419 : Blo 822348 1239419 := bstep (se 1 (by rfl) ⟨929564, by rfl⟩ : syracuseStep 1239419 = 1859129) B1859129
theorem B2779649 : Blo 822348 2779649 := bstep (se 2 (by rfl) ⟨1042368, by rfl⟩ : syracuseStep 2779649 = 2084737) B2084737
theorem B1567259 : Blo 822348 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B5270123 : Blo 822348 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B2780135 : Blo 822348 2780135 := bstep (se 1 (by rfl) ⟨2085101, by rfl⟩ : syracuseStep 2780135 = 4170203) B4170203
theorem B2780459 : Blo 822348 2780459 := bstep (se 1 (by rfl) ⟨2085344, by rfl⟩ : syracuseStep 2780459 = 4170689) B4170689
theorem B2780729 : Blo 822348 2780729 := bstep (se 2 (by rfl) ⟨1042773, by rfl⟩ : syracuseStep 2780729 = 2085547) B2085547
theorem B880507 : Blo 822348 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B6354227 : Blo 822348 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B2782619 : Blo 822348 2782619 := bstep (se 1 (by rfl) ⟨2086964, by rfl⟩ : syracuseStep 2782619 = 4173929) B4173929
theorem B7141067 : Blo 822348 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B1341263 : Blo 822348 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B2783375 : Blo 822348 2783375 := bstep (se 1 (by rfl) ⟨2087531, by rfl⟩ : syracuseStep 2783375 = 4175063) B4175063
theorem B12712301 : Blo 822348 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B1670095 : Blo 822348 1670095 := bstep (se 1 (by rfl) ⟨1252571, by rfl⟩ : syracuseStep 1670095 = 2505143) B2505143
theorem B2784509 : Blo 822348 2784509 := bstep (se 3 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 2784509 = 1044191) B1044191
theorem B21364163 : Blo 822348 21364163 := bstep (se 1 (by rfl) ⟨16023122, by rfl⟩ : syracuseStep 21364163 = 32046245) B32046245
theorem B20053595 : Blo 822348 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B2228093 : Blo 822348 2228093 := bstep (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) B835535
theorem B5341099 : Blo 822348 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B2785751 : Blo 822348 2785751 := bstep (se 1 (by rfl) ⟨2089313, by rfl⟩ : syracuseStep 2785751 = 4178627) B4178627
theorem B14058035 : Blo 822348 14058035 := bstep (se 1 (by rfl) ⟨10543526, by rfl⟩ : syracuseStep 14058035 = 21087053) B21087053
theorem B3179351 : Blo 822348 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B13338445 : Blo 822348 13338445 := bstep (se 3 (by rfl) ⟨2500958, by rfl⟩ : syracuseStep 13338445 = 5001917) B5001917
theorem B10586173 : Blo 822348 10586173 := bstep (se 3 (by rfl) ⟨1984907, by rfl⟩ : syracuseStep 10586173 = 3969815) B3969815
theorem B2853025 : Blo 822348 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B1673551 : Blo 822348 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B7047607 : Blo 822348 7047607 := bstep (se 1 (by rfl) ⟨5285705, by rfl⟩ : syracuseStep 7047607 = 10571411) B10571411
theorem B4229729 : Blo 822348 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B6261623 : Blo 822348 6261623 := bstep (se 1 (by rfl) ⟨4696217, by rfl⟩ : syracuseStep 6261623 = 9392435) B9392435
theorem B1608617 : Blo 822348 1608617 := bstep (se 2 (by rfl) ⟨603231, by rfl⟩ : syracuseStep 1608617 = 1206463) B1206463
theorem B2788343 : Blo 822348 2788343 := bstep (se 1 (by rfl) ⟨2091257, by rfl⟩ : syracuseStep 2788343 = 4182515) B4182515
theorem B1412203 : Blo 822348 1412203 := bstep (se 1 (by rfl) ⟨1059152, by rfl⟩ : syracuseStep 1412203 = 2118305) B2118305
theorem B7933139 : Blo 822348 7933139 := bstep (se 1 (by rfl) ⟨5949854, by rfl⟩ : syracuseStep 7933139 = 11899709) B11899709
theorem B822655 : Blo 822348 822655 := bstep (se 1 (by rfl) ⟨616991, by rfl⟩ : syracuseStep 822655 = 1233983) B1233983
theorem B3345803 : Blo 822348 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B822683 : Blo 822348 822683 := bstep (se 1 (by rfl) ⟨617012, by rfl⟩ : syracuseStep 822683 = 1234025) B1234025
theorem B822751 : Blo 822348 822751 := bstep (se 1 (by rfl) ⟨617063, by rfl⟩ : syracuseStep 822751 = 1234127) B1234127
theorem B822887 : Blo 822348 822887 := bstep (se 1 (by rfl) ⟨617165, by rfl⟩ : syracuseStep 822887 = 1234331) B1234331
theorem B823035 : Blo 822348 823035 := bstep (se 1 (by rfl) ⟨617276, by rfl⟩ : syracuseStep 823035 = 1234553) B1234553
theorem B823103 : Blo 822348 823103 := bstep (se 1 (by rfl) ⟨617327, by rfl⟩ : syracuseStep 823103 = 1234655) B1234655
theorem B823167 : Blo 822348 823167 := bstep (se 1 (by rfl) ⟨617375, by rfl⟩ : syracuseStep 823167 = 1234751) B1234751
theorem B4689839 : Blo 822348 4689839 := bstep (se 1 (by rfl) ⟨3517379, by rfl⟩ : syracuseStep 4689839 = 7034759) B7034759
theorem B823279 : Blo 822348 823279 := bstep (se 1 (by rfl) ⟨617459, by rfl⟩ : syracuseStep 823279 = 1234919) B1234919
theorem B823291 : Blo 822348 823291 := bstep (se 1 (by rfl) ⟨617468, by rfl⟩ : syracuseStep 823291 = 1234937) B1234937
theorem B823359 : Blo 822348 823359 := bstep (se 1 (by rfl) ⟨617519, by rfl⟩ : syracuseStep 823359 = 1235039) B1235039
theorem B823399 : Blo 822348 823399 := bstep (se 1 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 823399 = 1235099) B1235099
theorem B3346535 : Blo 822348 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B823423 : Blo 822348 823423 := bstep (se 1 (by rfl) ⟨617567, by rfl⟩ : syracuseStep 823423 = 1235135) B1235135
theorem B823451 : Blo 822348 823451 := bstep (se 1 (by rfl) ⟨617588, by rfl⟩ : syracuseStep 823451 = 1235177) B1235177
theorem B823655 : Blo 822348 823655 := bstep (se 1 (by rfl) ⟨617741, by rfl⟩ : syracuseStep 823655 = 1235483) B1235483
theorem B823707 : Blo 822348 823707 := bstep (se 1 (by rfl) ⟨617780, by rfl⟩ : syracuseStep 823707 = 1235561) B1235561
theorem B824059 : Blo 822348 824059 := bstep (se 1 (by rfl) ⟨618044, by rfl⟩ : syracuseStep 824059 = 1236089) B1236089
theorem B824127 : Blo 822348 824127 := bstep (se 1 (by rfl) ⟨618095, by rfl⟩ : syracuseStep 824127 = 1236191) B1236191
theorem B824155 : Blo 822348 824155 := bstep (se 1 (by rfl) ⟨618116, by rfl⟩ : syracuseStep 824155 = 1236233) B1236233
theorem B824223 : Blo 822348 824223 := bstep (se 1 (by rfl) ⟨618167, by rfl⟩ : syracuseStep 824223 = 1236335) B1236335
theorem B824303 : Blo 822348 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B824391 : Blo 822348 824391 := bstep (se 1 (by rfl) ⟨618293, by rfl⟩ : syracuseStep 824391 = 1236587) B1236587
theorem B824475 : Blo 822348 824475 := bstep (se 1 (by rfl) ⟨618356, by rfl⟩ : syracuseStep 824475 = 1236713) B1236713
theorem B824571 : Blo 822348 824571 := bstep (se 1 (by rfl) ⟨618428, by rfl⟩ : syracuseStep 824571 = 1236857) B1236857
theorem B824639 : Blo 822348 824639 := bstep (se 1 (by rfl) ⟨618479, by rfl⟩ : syracuseStep 824639 = 1236959) B1236959
theorem B7935407 : Blo 822348 7935407 := bstep (se 1 (by rfl) ⟨5951555, by rfl⟩ : syracuseStep 7935407 = 11903111) B11903111
theorem B824807 : Blo 822348 824807 := bstep (se 1 (by rfl) ⟨618605, by rfl⟩ : syracuseStep 824807 = 1237211) B1237211
theorem B824815 : Blo 822348 824815 := bstep (se 1 (by rfl) ⟨618611, by rfl⟩ : syracuseStep 824815 = 1237223) B1237223
theorem B824923 : Blo 822348 824923 := bstep (se 1 (by rfl) ⟨618692, by rfl⟩ : syracuseStep 824923 = 1237385) B1237385
theorem B824987 : Blo 822348 824987 := bstep (se 1 (by rfl) ⟨618740, by rfl⟩ : syracuseStep 824987 = 1237481) B1237481
theorem B825071 : Blo 822348 825071 := bstep (se 1 (by rfl) ⟨618803, by rfl⟩ : syracuseStep 825071 = 1237607) B1237607
theorem B825159 : Blo 822348 825159 := bstep (se 1 (by rfl) ⟨618869, by rfl⟩ : syracuseStep 825159 = 1237739) B1237739
theorem B825179 : Blo 822348 825179 := bstep (se 1 (by rfl) ⟨618884, by rfl⟩ : syracuseStep 825179 = 1237769) B1237769
theorem B825247 : Blo 822348 825247 := bstep (se 1 (by rfl) ⟨618935, by rfl⟩ : syracuseStep 825247 = 1237871) B1237871
theorem B5281811 : Blo 822348 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B825415 : Blo 822348 825415 := bstep (se 1 (by rfl) ⟨619061, by rfl⟩ : syracuseStep 825415 = 1238123) B1238123
theorem B6265025 : Blo 822348 6265025 := bstep (se 2 (by rfl) ⟨2349384, by rfl⟩ : syracuseStep 6265025 = 4698769) B4698769
theorem B825575 : Blo 822348 825575 := bstep (se 1 (by rfl) ⟨619181, by rfl⟩ : syracuseStep 825575 = 1238363) B1238363
theorem B13375813 : Blo 822348 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B825759 : Blo 822348 825759 := bstep (se 1 (by rfl) ⟨619319, by rfl⟩ : syracuseStep 825759 = 1238639) B1238639
theorem B825807 : Blo 822348 825807 := bstep (se 1 (by rfl) ⟨619355, by rfl⟩ : syracuseStep 825807 = 1238711) B1238711
theorem B825831 : Blo 822348 825831 := bstep (se 1 (by rfl) ⟨619373, by rfl⟩ : syracuseStep 825831 = 1238747) B1238747
theorem B825947 : Blo 822348 825947 := bstep (se 1 (by rfl) ⟨619460, by rfl⟩ : syracuseStep 825947 = 1238921) B1238921
theorem B826015 : Blo 822348 826015 := bstep (se 1 (by rfl) ⟨619511, by rfl⟩ : syracuseStep 826015 = 1239023) B1239023
theorem B826183 : Blo 822348 826183 := bstep (se 1 (by rfl) ⟨619637, by rfl⟩ : syracuseStep 826183 = 1239275) B1239275
theorem B826223 : Blo 822348 826223 := bstep (se 1 (by rfl) ⟨619667, by rfl⟩ : syracuseStep 826223 = 1239335) B1239335
theorem B826279 : Blo 822348 826279 := bstep (se 1 (by rfl) ⟨619709, by rfl⟩ : syracuseStep 826279 = 1239419) B1239419
theorem B3350443 : Blo 822348 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B925951 : Blo 822348 925951 := bstep (se 1 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 925951 = 1388927) B1388927
theorem B1909153 : Blo 822348 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B926239 : Blo 822348 926239 := bstep (se 1 (by rfl) ⟨694679, by rfl⟩ : syracuseStep 926239 = 1389359) B1389359
theorem B4465505 : Blo 822348 4465505 := bstep (se 2 (by rfl) ⟨1674564, by rfl⟩ : syracuseStep 4465505 = 3349129) B3349129
theorem B4236151 : Blo 822348 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1319915 : Blo 822348 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B3515501 : Blo 822348 3515501 := bstep (se 3 (by rfl) ⟨659156, by rfl⟩ : syracuseStep 3515501 = 1318313) B1318313
theorem B4760711 : Blo 822348 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B926887 : Blo 822348 926887 := bstep (se 1 (by rfl) ⟨695165, by rfl⟩ : syracuseStep 926887 = 1390331) B1390331
theorem B894175 : Blo 822348 894175 := bstep (se 1 (by rfl) ⟨670631, by rfl⟩ : syracuseStep 894175 = 1341263) B1341263
theorem B12035465 : Blo 822348 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B25404853 : Blo 822348 25404853 := bstep (se 5 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 25404853 = 2381705) B2381705
theorem B4171337 : Blo 822348 4171337 := bstep (se 2 (by rfl) ⟨1564251, by rfl⟩ : syracuseStep 4171337 = 3128503) B3128503
theorem B7939903 : Blo 822348 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B13346693 : Blo 822348 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B927679 : Blo 822348 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B4466735 : Blo 822348 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B927967 : Blo 822348 927967 := bstep (se 1 (by rfl) ⟨695975, by rfl⟩ : syracuseStep 927967 = 1391951) B1391951
theorem B7121465 : Blo 822348 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B1485395 : Blo 822348 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B3517415 : Blo 822348 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B928831 : Blo 822348 928831 := bstep (se 1 (by rfl) ⟨696623, by rfl⟩ : syracuseStep 928831 = 1393247) B1393247
theorem B3517775 : Blo 822348 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B3124919 : Blo 822348 3124919 := bstep (se 1 (by rfl) ⟨2343689, by rfl⟩ : syracuseStep 3124919 = 4687379) B4687379
theorem B15019769 : Blo 822348 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B6270857 : Blo 822348 6270857 := bstep (se 2 (by rfl) ⟨2351571, by rfl⟩ : syracuseStep 6270857 = 4703143) B4703143
theorem B7057313 : Blo 822348 7057313 := bstep (se 2 (by rfl) ⟨2646492, by rfl⟩ : syracuseStep 7057313 = 5292985) B5292985
theorem B1585225 : Blo 822348 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B3125375 : Blo 822348 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B1978643 : Blo 822348 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B2634857 : Blo 822348 2634857 := bstep (se 2 (by rfl) ⟨988071, by rfl⟩ : syracuseStep 2634857 = 1976143) B1976143
theorem B3126377 : Blo 822348 3126377 := bstep (se 2 (by rfl) ⟨1172391, by rfl⟩ : syracuseStep 3126377 = 2344783) B2344783
theorem B1488191 : Blo 822348 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B8467993 : Blo 822348 8467993 := bstep (se 2 (by rfl) ⟨3175497, by rfl⟩ : syracuseStep 8467993 = 6350995) B6350995
theorem B1390223 : Blo 822348 1390223 := bstep (se 1 (by rfl) ⟨1042667, by rfl⟩ : syracuseStep 1390223 = 2085335) B2085335
theorem B3127031 : Blo 822348 3127031 := bstep (se 1 (by rfl) ⟨2345273, by rfl⟩ : syracuseStep 3127031 = 4690547) B4690547
theorem B3127531 : Blo 822348 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B1882361 : Blo 822348 1882361 := bstep (se 2 (by rfl) ⟨705885, by rfl⟩ : syracuseStep 1882361 = 1411771) B1411771
theorem B15874339 : Blo 822348 15874339 := bstep (se 1 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 15874339 = 23811509) B23811509
theorem B1980719 : Blo 822348 1980719 := bstep (se 1 (by rfl) ⟨1485539, by rfl⟩ : syracuseStep 1980719 = 2971079) B2971079
theorem B1391195 : Blo 822348 1391195 := bstep (se 1 (by rfl) ⟨1043396, by rfl⟩ : syracuseStep 1391195 = 2086793) B2086793
theorem B4176521 : Blo 822348 4176521 := bstep (se 2 (by rfl) ⟨1566195, by rfl⟩ : syracuseStep 4176521 = 3132391) B3132391
theorem B10566287 : Blo 822348 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B2341993 : Blo 822348 2341993 := bstep (se 2 (by rfl) ⟨878247, by rfl⟩ : syracuseStep 2341993 = 1756495) B1756495
theorem B2636999 : Blo 822348 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B3521789 : Blo 822348 3521789 := bstep (se 3 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 3521789 = 1320671) B1320671
theorem B2342267 : Blo 822348 2342267 := bstep (se 1 (by rfl) ⟨1756700, by rfl⟩ : syracuseStep 2342267 = 3513401) B3513401
theorem B1850795 : Blo 822348 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B1850831 : Blo 822348 1850831 := bstep (se 1 (by rfl) ⟨1388123, by rfl⟩ : syracuseStep 1850831 = 2776247) B2776247
theorem B1392079 : Blo 822348 1392079 := bstep (se 1 (by rfl) ⟨1044059, by rfl⟩ : syracuseStep 1392079 = 2088119) B2088119
theorem B13352455 : Blo 822348 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B1851335 : Blo 822348 1851335 := bstep (se 1 (by rfl) ⟨1388501, by rfl⟩ : syracuseStep 1851335 = 2777003) B2777003
theorem B1851641 : Blo 822348 1851641 := bstep (se 2 (by rfl) ⟨694365, by rfl⟩ : syracuseStep 1851641 = 1388731) B1388731
theorem B1851695 : Blo 822348 1851695 := bstep (se 1 (by rfl) ⟨1388771, by rfl⟩ : syracuseStep 1851695 = 2777543) B2777543
theorem B1392943 : Blo 822348 1392943 := bstep (se 1 (by rfl) ⟨1044707, by rfl⟩ : syracuseStep 1392943 = 2089415) B2089415
theorem B2343325 : Blo 822348 2343325 := bstep (se 3 (by rfl) ⟨439373, by rfl⟩ : syracuseStep 2343325 = 878747) B878747
theorem B1851911 : Blo 822348 1851911 := bstep (se 1 (by rfl) ⟨1388933, by rfl⟩ : syracuseStep 1851911 = 2777867) B2777867
theorem B1852091 : Blo 822348 1852091 := bstep (se 1 (by rfl) ⟨1389068, by rfl⟩ : syracuseStep 1852091 = 2778137) B2778137
theorem B2081801 : Blo 822348 2081801 := bstep (se 2 (by rfl) ⟨780675, by rfl⟩ : syracuseStep 2081801 = 1561351) B1561351
theorem B1852523 : Blo 822348 1852523 := bstep (se 1 (by rfl) ⟨1389392, by rfl⟩ : syracuseStep 1852523 = 2778785) B2778785
theorem B2081983 : Blo 822348 2081983 := bstep (se 1 (by rfl) ⟨1561487, by rfl⟩ : syracuseStep 2081983 = 3122975) B3122975
theorem B3130721 : Blo 822348 3130721 := bstep (se 2 (by rfl) ⟨1174020, by rfl⟩ : syracuseStep 3130721 = 2348041) B2348041
theorem B2377147 : Blo 822348 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B1852991 : Blo 822348 1852991 := bstep (se 1 (by rfl) ⟨1389743, by rfl⟩ : syracuseStep 1852991 = 2779487) B2779487
theorem B1394239 : Blo 822348 1394239 := bstep (se 1 (by rfl) ⟨1045679, by rfl⟩ : syracuseStep 1394239 = 2091359) B2091359
theorem B2344555 : Blo 822348 2344555 := bstep (se 1 (by rfl) ⟨1758416, by rfl⟩ : syracuseStep 2344555 = 3516833) B3516833
theorem B1853099 : Blo 822348 1853099 := bstep (se 1 (by rfl) ⟨1389824, by rfl⟩ : syracuseStep 1853099 = 2779649) B2779649
theorem B1853423 : Blo 822348 1853423 := bstep (se 1 (by rfl) ⟨1390067, by rfl⟩ : syracuseStep 1853423 = 2780135) B2780135
theorem B1853639 : Blo 822348 1853639 := bstep (se 1 (by rfl) ⟨1390229, by rfl⟩ : syracuseStep 1853639 = 2780459) B2780459
theorem B1853819 : Blo 822348 1853819 := bstep (se 1 (by rfl) ⟨1390364, by rfl⟩ : syracuseStep 1853819 = 2780729) B2780729
theorem B1854089 : Blo 822348 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B1854377 : Blo 822348 1854377 := bstep (se 2 (by rfl) ⟨695391, by rfl⟩ : syracuseStep 1854377 = 1390783) B1390783
theorem B2346401 : Blo 822348 2346401 := bstep (se 2 (by rfl) ⟨879900, by rfl⟩ : syracuseStep 2346401 = 1759801) B1759801
theorem B1855079 : Blo 822348 1855079 := bstep (se 1 (by rfl) ⟨1391309, by rfl⟩ : syracuseStep 1855079 = 2782619) B2782619
theorem B7917335 : Blo 822348 7917335 := bstep (se 1 (by rfl) ⟨5938001, by rfl⟩ : syracuseStep 7917335 = 11876003) B11876003
theorem B2379709 : Blo 822348 2379709 := bstep (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) B892391
theorem B1855583 : Blo 822348 1855583 := bstep (se 1 (by rfl) ⟨1391687, by rfl⟩ : syracuseStep 1855583 = 2783375) B2783375
theorem B3526811 : Blo 822348 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B8474867 : Blo 822348 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B4182353 : Blo 822348 4182353 := bstep (se 2 (by rfl) ⟨1568382, by rfl⟩ : syracuseStep 4182353 = 3136765) B3136765
theorem B1233545 : Blo 822348 1233545 := bstep (se 2 (by rfl) ⟨462579, by rfl⟩ : syracuseStep 1233545 = 925159) B925159
theorem B1561427 : Blo 822348 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1856339 : Blo 822348 1856339 := bstep (se 1 (by rfl) ⟨1392254, by rfl⟩ : syracuseStep 1856339 = 2784509) B2784509
theorem B1233755 : Blo 822348 1233755 := bstep (se 1 (by rfl) ⟨925316, by rfl⟩ : syracuseStep 1233755 = 1850633) B1850633
theorem B14242775 : Blo 822348 14242775 := bstep (se 1 (by rfl) ⟨10682081, by rfl⟩ : syracuseStep 14242775 = 21364163) B21364163
theorem B2085983 : Blo 822348 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B4183163 : Blo 822348 4183163 := bstep (se 1 (by rfl) ⟨3137372, by rfl⟩ : syracuseStep 4183163 = 6274745) B6274745
theorem B1234217 : Blo 822348 1234217 := bstep (se 2 (by rfl) ⟨462831, by rfl⟩ : syracuseStep 1234217 = 925663) B925663
theorem B1856879 : Blo 822348 1856879 := bstep (se 1 (by rfl) ⟨1392659, by rfl⟩ : syracuseStep 1856879 = 2785319) B2785319
theorem B7918991 : Blo 822348 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B1562095 : Blo 822348 1562095 := bstep (se 1 (by rfl) ⟨1171571, by rfl⟩ : syracuseStep 1562095 = 2343143) B2343143
theorem B1234415 : Blo 822348 1234415 := bstep (se 1 (by rfl) ⟨925811, by rfl⟩ : syracuseStep 1234415 = 1851623) B1851623
theorem B2643623 : Blo 822348 2643623 := bstep (se 1 (by rfl) ⟨1982717, by rfl⟩ : syracuseStep 2643623 = 3965435) B3965435
theorem B4445975 : Blo 822348 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B1857311 : Blo 822348 1857311 := bstep (se 1 (by rfl) ⟨1392983, by rfl⟩ : syracuseStep 1857311 = 2785967) B2785967
theorem B1562399 : Blo 822348 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B3528521 : Blo 822348 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B2643803 : Blo 822348 2643803 := bstep (se 1 (by rfl) ⟨1982852, by rfl⟩ : syracuseStep 2643803 = 3965705) B3965705
theorem B1234811 : Blo 822348 1234811 := bstep (se 1 (by rfl) ⟨926108, by rfl⟩ : syracuseStep 1234811 = 1852217) B1852217
theorem B1234847 : Blo 822348 1234847 := bstep (se 1 (by rfl) ⟨926135, by rfl⟩ : syracuseStep 1234847 = 1852271) B1852271
theorem B14079905 : Blo 822348 14079905 := bstep (se 2 (by rfl) ⟨5279964, by rfl⟩ : syracuseStep 14079905 = 10559929) B10559929
theorem B1857527 : Blo 822348 1857527 := bstep (se 1 (by rfl) ⟨1393145, by rfl⟩ : syracuseStep 1857527 = 2786291) B2786291
theorem B1267849 : Blo 822348 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B1235081 : Blo 822348 1235081 := bstep (se 2 (by rfl) ⟨463155, by rfl⟩ : syracuseStep 1235081 = 926311) B926311
theorem B7919795 : Blo 822348 7919795 := bstep (se 1 (by rfl) ⟨5939846, by rfl⟩ : syracuseStep 7919795 = 11879693) B11879693
theorem B1235231 : Blo 822348 1235231 := bstep (se 1 (by rfl) ⟨926423, by rfl⟩ : syracuseStep 1235231 = 1852847) B1852847
theorem B1857887 : Blo 822348 1857887 := bstep (se 1 (by rfl) ⟨1393415, by rfl⟩ : syracuseStep 1857887 = 2786831) B2786831
theorem B2087329 : Blo 822348 2087329 := bstep (se 2 (by rfl) ⟨782748, by rfl⟩ : syracuseStep 2087329 = 1565497) B1565497
theorem B2349499 : Blo 822348 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B1563113 : Blo 822348 1563113 := bstep (se 2 (by rfl) ⟨586167, by rfl⟩ : syracuseStep 1563113 = 1172335) B1172335
theorem B1760057 : Blo 822348 1760057 := bstep (se 2 (by rfl) ⟨660021, by rfl⟩ : syracuseStep 1760057 = 1320043) B1320043
theorem B1235783 : Blo 822348 1235783 := bstep (se 1 (by rfl) ⟨926837, by rfl⟩ : syracuseStep 1235783 = 1853675) B1853675
theorem B1858427 : Blo 822348 1858427 := bstep (se 1 (by rfl) ⟨1393820, by rfl⟩ : syracuseStep 1858427 = 2787641) B2787641
theorem B1858607 : Blo 822348 1858607 := bstep (se 1 (by rfl) ⟨1393955, by rfl⟩ : syracuseStep 1858607 = 2787911) B2787911
theorem B6249959 : Blo 822348 6249959 := bstep (se 1 (by rfl) ⟨4687469, by rfl⟩ : syracuseStep 6249959 = 9374939) B9374939
theorem B1236647 : Blo 822348 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B1236767 : Blo 822348 1236767 := bstep (se 1 (by rfl) ⟨927575, by rfl⟩ : syracuseStep 1236767 = 1855151) B1855151
theorem B1564571 : Blo 822348 1564571 := bstep (se 1 (by rfl) ⟨1173428, by rfl⟩ : syracuseStep 1564571 = 2346857) B2346857
theorem B1237199 : Blo 822348 1237199 := bstep (se 1 (by rfl) ⟨927899, by rfl⟩ : syracuseStep 1237199 = 1855799) B1855799
theorem B1237247 : Blo 822348 1237247 := bstep (se 1 (by rfl) ⟨927935, by rfl⟩ : syracuseStep 1237247 = 1855871) B1855871
theorem B2089273 : Blo 822348 2089273 := bstep (se 2 (by rfl) ⟨783477, by rfl⟩ : syracuseStep 2089273 = 1566955) B1566955
theorem B1761697 : Blo 822348 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B1041103 : Blo 822348 1041103 := bstep (se 1 (by rfl) ⟨780827, by rfl⟩ : syracuseStep 1041103 = 1561655) B1561655
theorem B2089759 : Blo 822348 2089759 := bstep (se 1 (by rfl) ⟨1567319, by rfl⟩ : syracuseStep 2089759 = 3134639) B3134639
theorem B1238063 : Blo 822348 1238063 := bstep (se 1 (by rfl) ⟨928547, by rfl⟩ : syracuseStep 1238063 = 1857095) B1857095
theorem B1238183 : Blo 822348 1238183 := bstep (se 1 (by rfl) ⟨928637, by rfl⟩ : syracuseStep 1238183 = 1857275) B1857275
theorem B1762715 : Blo 822348 1762715 := bstep (se 1 (by rfl) ⟨1322036, by rfl⟩ : syracuseStep 1762715 = 2644073) B2644073
theorem B5629459 : Blo 822348 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B1238555 : Blo 822348 1238555 := bstep (se 1 (by rfl) ⟨928916, by rfl⟩ : syracuseStep 1238555 = 1857833) B1857833
theorem B8152709 : Blo 822348 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B15853427 : Blo 822348 15853427 := bstep (se 1 (by rfl) ⟨11890070, by rfl⟩ : syracuseStep 15853427 = 23780141) B23780141
theorem B7038859 : Blo 822348 7038859 := bstep (se 1 (by rfl) ⟨5279144, by rfl⟩ : syracuseStep 7038859 = 10558289) B10558289
theorem B1238939 : Blo 822348 1238939 := bstep (se 1 (by rfl) ⟨929204, by rfl⟩ : syracuseStep 1238939 = 1858409) B1858409
theorem B1238975 : Blo 822348 1238975 := bstep (se 1 (by rfl) ⟨929231, by rfl⟩ : syracuseStep 1238975 = 1858463) B1858463
theorem B1042399 : Blo 822348 1042399 := bstep (se 1 (by rfl) ⟨781799, by rfl⟩ : syracuseStep 1042399 = 1563599) B1563599
theorem B1566803 : Blo 822348 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1239161 : Blo 822348 1239161 := bstep (se 2 (by rfl) ⟨464685, by rfl⟩ : syracuseStep 1239161 = 929371) B929371
theorem B3336557 : Blo 822348 3336557 := bstep (se 3 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 3336557 = 1251209) B1251209
theorem B8907173 : Blo 822348 8907173 := bstep (se 4 (by rfl) ⟨835047, by rfl⟩ : syracuseStep 8907173 = 1670095) B1670095
theorem B1174009 : Blo 822348 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B1567927 : Blo 822348 1567927 := bstep (se 1 (by rfl) ⟨1175945, by rfl⟩ : syracuseStep 1567927 = 2351891) B2351891
theorem B1043867 : Blo 822348 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B1568155 : Blo 822348 1568155 := bstep (se 1 (by rfl) ⟨1176116, by rfl⟩ : syracuseStep 1568155 = 2352233) B2352233
theorem B20082401 : Blo 822348 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B14053661 : Blo 822348 14053661 := bstep (se 3 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 14053661 = 5270123) B5270123
theorem B1044839 : Blo 822348 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B2781647 : Blo 822348 2781647 := bstep (se 1 (by rfl) ⟨2086235, by rfl⟩ : syracuseStep 2781647 = 4172471) B4172471
theorem B7043233 : Blo 822348 7043233 := bstep (se 2 (by rfl) ⟨2641212, by rfl⟩ : syracuseStep 7043233 = 5282425) B5282425
theorem B6257249 : Blo 822348 6257249 := bstep (se 2 (by rfl) ⟨2346468, by rfl⟩ : syracuseStep 6257249 = 4692937) B4692937
theorem B2783969 : Blo 822348 2783969 := bstep (se 2 (by rfl) ⟨1043988, by rfl⟩ : syracuseStep 2783969 = 2087977) B2087977
theorem B4684715 : Blo 822348 4684715 := bstep (se 1 (by rfl) ⟨3513536, by rfl⟩ : syracuseStep 4684715 = 7027073) B7027073
theorem B2817305 : Blo 822348 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B4685465 : Blo 822348 4685465 := bstep (se 2 (by rfl) ⟨1757049, by rfl⟩ : syracuseStep 4685465 = 3514099) B3514099
theorem B13369063 : Blo 822348 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B4685647 : Blo 822348 4685647 := bstep (se 1 (by rfl) ⟨3514235, by rfl⟩ : syracuseStep 4685647 = 7028471) B7028471
theorem B2785103 : Blo 822348 2785103 := bstep (se 1 (by rfl) ⟨2088827, by rfl⟩ : syracuseStep 2785103 = 4177655) B4177655
theorem B9372023 : Blo 822348 9372023 := bstep (se 1 (by rfl) ⟨7029017, by rfl⟩ : syracuseStep 9372023 = 14058035) B14058035
theorem B2785697 : Blo 822348 2785697 := bstep (se 2 (by rfl) ⟨1044636, by rfl⟩ : syracuseStep 2785697 = 2089273) B2089273
theorem B2786237 : Blo 822348 2786237 := bstep (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) B1044839
theorem B2786345 : Blo 822348 2786345 := bstep (se 2 (by rfl) ⟨1044879, by rfl⟩ : syracuseStep 2786345 = 2089759) B2089759
theorem B2819819 : Blo 822348 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B7505945 : Blo 822348 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B2230535 : Blo 822348 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B10586537 : Blo 822348 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B5278223 : Blo 822348 5278223 := bstep (se 1 (by rfl) ⟨3958667, by rfl⟩ : syracuseStep 5278223 = 7917335) B7917335
theorem B37980733 : Blo 822348 37980733 := bstep (se 3 (by rfl) ⟨7121387, by rfl⟩ : syracuseStep 37980733 = 14242775) B14242775
theorem B2231023 : Blo 822348 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B2788235 : Blo 822348 2788235 := bstep (se 1 (by rfl) ⟨2091176, by rfl⟩ : syracuseStep 2788235 = 4182353) B4182353
theorem B822363 : Blo 822348 822363 := bstep (se 1 (by rfl) ⟨616772, by rfl⟩ : syracuseStep 822363 = 1233545) B1233545
theorem B2231401 : Blo 822348 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B822503 : Blo 822348 822503 := bstep (se 1 (by rfl) ⟨616877, by rfl⟩ : syracuseStep 822503 = 1233755) B1233755
theorem B2788775 : Blo 822348 2788775 := bstep (se 1 (by rfl) ⟨2091581, by rfl⟩ : syracuseStep 2788775 = 4183163) B4183163
theorem B3968509 : Blo 822348 3968509 := bstep (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) B1488191
theorem B822811 : Blo 822348 822811 := bstep (se 1 (by rfl) ⟨617108, by rfl⟩ : syracuseStep 822811 = 1234217) B1234217
theorem B5279327 : Blo 822348 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B822943 : Blo 822348 822943 := bstep (se 1 (by rfl) ⟨617207, by rfl⟩ : syracuseStep 822943 = 1234415) B1234415
theorem B35589941 : Blo 822348 35589941 := bstep (se 5 (by rfl) ⟨1668278, by rfl⟩ : syracuseStep 35589941 = 3336557) B3336557
theorem B823207 : Blo 822348 823207 := bstep (se 1 (by rfl) ⟨617405, by rfl⟩ : syracuseStep 823207 = 1234811) B1234811
theorem B823231 : Blo 822348 823231 := bstep (se 1 (by rfl) ⟨617423, by rfl⟩ : syracuseStep 823231 = 1234847) B1234847
theorem B823387 : Blo 822348 823387 := bstep (se 1 (by rfl) ⟨617540, by rfl⟩ : syracuseStep 823387 = 1235081) B1235081
theorem B5279863 : Blo 822348 5279863 := bstep (se 1 (by rfl) ⟨3959897, by rfl⟩ : syracuseStep 5279863 = 7919795) B7919795
theorem B823487 : Blo 822348 823487 := bstep (se 1 (by rfl) ⟨617615, by rfl⟩ : syracuseStep 823487 = 1235231) B1235231
theorem B823855 : Blo 822348 823855 := bstep (se 1 (by rfl) ⟨617891, by rfl⟩ : syracuseStep 823855 = 1235783) B1235783
theorem B19075733 : Blo 822348 19075733 := bstep (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) B894175
theorem B4166639 : Blo 822348 4166639 := bstep (se 1 (by rfl) ⟨3124979, by rfl⟩ : syracuseStep 4166639 = 6249959) B6249959
theorem B824431 : Blo 822348 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B824511 : Blo 822348 824511 := bstep (se 1 (by rfl) ⟨618383, by rfl⟩ : syracuseStep 824511 = 1236767) B1236767
theorem B824799 : Blo 822348 824799 := bstep (se 1 (by rfl) ⟨618599, by rfl⟩ : syracuseStep 824799 = 1237199) B1237199
theorem B824831 : Blo 822348 824831 := bstep (se 1 (by rfl) ⟨618623, by rfl⟩ : syracuseStep 824831 = 1237247) B1237247
theorem B825375 : Blo 822348 825375 := bstep (se 1 (by rfl) ⟨619031, by rfl⟩ : syracuseStep 825375 = 1238063) B1238063
theorem B825455 : Blo 822348 825455 := bstep (se 1 (by rfl) ⟨619091, by rfl⟩ : syracuseStep 825455 = 1238183) B1238183
theorem B825703 : Blo 822348 825703 := bstep (se 1 (by rfl) ⟨619277, by rfl⟩ : syracuseStep 825703 = 1238555) B1238555
theorem B825959 : Blo 822348 825959 := bstep (se 1 (by rfl) ⟨619469, by rfl⟩ : syracuseStep 825959 = 1238939) B1238939
theorem B825983 : Blo 822348 825983 := bstep (se 1 (by rfl) ⟨619487, by rfl⟩ : syracuseStep 825983 = 1238975) B1238975
theorem B826107 : Blo 822348 826107 := bstep (se 1 (by rfl) ⟨619580, by rfl⟩ : syracuseStep 826107 = 1239161) B1239161
theorem B5938115 : Blo 822348 5938115 := bstep (se 1 (by rfl) ⟨4453586, by rfl⟩ : syracuseStep 5938115 = 8907173) B8907173
theorem B990263 : Blo 822348 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B71213093 : Blo 822348 71213093 := bstep (se 4 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 71213093 = 13352455) B13352455
theorem B45162629 : Blo 822348 45162629 := bstep (se 4 (by rfl) ⟨4233996, by rfl⟩ : syracuseStep 45162629 = 8467993) B8467993
theorem B1319095 : Blo 822348 1319095 := bstep (se 1 (by rfl) ⟨989321, by rfl⟩ : syracuseStep 1319095 = 1978643) B1978643
theorem B4170041 : Blo 822348 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B17834417 : Blo 822348 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B926815 : Blo 822348 926815 := bstep (se 1 (by rfl) ⟨695111, by rfl⟩ : syracuseStep 926815 = 1390223) B1390223
theorem B3122657 : Blo 822348 3122657 := bstep (se 2 (by rfl) ⟨1170996, by rfl⟩ : syracuseStep 3122657 = 2341993) B2341993
theorem B1254907 : Blo 822348 1254907 := bstep (se 1 (by rfl) ⟨941180, by rfl⟩ : syracuseStep 1254907 = 1882361) B1882361
theorem B1320479 : Blo 822348 1320479 := bstep (se 1 (by rfl) ⟨990359, by rfl⟩ : syracuseStep 1320479 = 1980719) B1980719
theorem B927463 : Blo 822348 927463 := bstep (se 1 (by rfl) ⟨695597, by rfl⟩ : syracuseStep 927463 = 1391195) B1391195
theorem B4171499 : Blo 822348 4171499 := bstep (se 1 (by rfl) ⟨3128624, by rfl⟩ : syracuseStep 4171499 = 6257249) B6257249
theorem B3123143 : Blo 822348 3123143 := bstep (se 1 (by rfl) ⟨2342357, by rfl⟩ : syracuseStep 3123143 = 4684715) B4684715
theorem B1878203 : Blo 822348 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B3123643 : Blo 822348 3123643 := bstep (se 1 (by rfl) ⟨2342732, by rfl⟩ : syracuseStep 3123643 = 4685465) B4685465
theorem B4467257 : Blo 822348 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B3124433 : Blo 822348 3124433 := bstep (se 2 (by rfl) ⟨1171662, by rfl⟩ : syracuseStep 3124433 = 2343325) B2343325
theorem B1387867 : Blo 822348 1387867 := bstep (se 1 (by rfl) ⟨1040900, by rfl⟩ : syracuseStep 1387867 = 2081801) B2081801
theorem B6761861 : Blo 822348 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B15216133 : Blo 822348 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B1388137 : Blo 822348 1388137 := bstep (se 2 (by rfl) ⟨520551, by rfl⟩ : syracuseStep 1388137 = 1041103) B1041103
theorem B5648201 : Blo 822348 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B4174415 : Blo 822348 4174415 := bstep (se 1 (by rfl) ⟨3130811, by rfl⟩ : syracuseStep 4174415 = 6261623) B6261623
theorem B5288759 : Blo 822348 5288759 := bstep (se 1 (by rfl) ⟨3966569, by rfl⟩ : syracuseStep 5288759 = 7933139) B7933139
theorem B3126073 : Blo 822348 3126073 := bstep (se 2 (by rfl) ⟨1172277, by rfl⟩ : syracuseStep 3126073 = 2344555) B2344555
theorem B9385145 : Blo 822348 9385145 := bstep (se 2 (by rfl) ⟨3519429, by rfl⟩ : syracuseStep 9385145 = 7038859) B7038859
theorem B3519773 : Blo 822348 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B3126559 : Blo 822348 3126559 := bstep (se 1 (by rfl) ⟨2344919, by rfl⟩ : syracuseStep 3126559 = 4689839) B4689839
theorem B1389865 : Blo 822348 1389865 := bstep (se 2 (by rfl) ⟨521199, by rfl⟩ : syracuseStep 1389865 = 1042399) B1042399
theorem B5649911 : Blo 822348 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B1390655 : Blo 822348 1390655 := bstep (se 1 (by rfl) ⟨1042991, by rfl⟩ : syracuseStep 1390655 = 2085983) B2085983
theorem B5290271 : Blo 822348 5290271 := bstep (se 1 (by rfl) ⟨3967703, by rfl⟩ : syracuseStep 5290271 = 7935407) B7935407
theorem B9386603 : Blo 822348 9386603 := bstep (se 1 (by rfl) ⟨7039952, by rfl⟩ : syracuseStep 9386603 = 14079905) B14079905
theorem B3521207 : Blo 822348 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B4176683 : Blo 822348 4176683 := bstep (se 1 (by rfl) ⟨3132512, by rfl⟩ : syracuseStep 4176683 = 6265025) B6265025
theorem B1882937 : Blo 822348 1882937 := bstep (se 2 (by rfl) ⟨706101, by rfl⟩ : syracuseStep 1882937 = 1412203) B1412203
theorem B21740557 : Blo 822348 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B2113633 : Blo 822348 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B4178141 : Blo 822348 4178141 := bstep (se 3 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 4178141 = 1566803) B1566803
theorem B2343667 : Blo 822348 2343667 := bstep (se 1 (by rfl) ⟨1757750, by rfl⟩ : syracuseStep 2343667 = 3515501) B3515501
theorem B10568951 : Blo 822348 10568951 := bstep (se 1 (by rfl) ⟨7926713, by rfl⟩ : syracuseStep 10568951 = 15853427) B15853427
theorem B8897795 : Blo 822348 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B2082793 : Blo 822348 2082793 := bstep (se 2 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 2082793 = 1562095) B1562095
theorem B2344943 : Blo 822348 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B2345183 : Blo 822348 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B2083279 : Blo 822348 2083279 := bstep (se 1 (by rfl) ⟨1562459, by rfl⟩ : syracuseStep 2083279 = 3124919) B3124919
theorem B13388267 : Blo 822348 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B10013179 : Blo 822348 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B4180571 : Blo 822348 4180571 := bstep (se 1 (by rfl) ⟨3135428, by rfl⟩ : syracuseStep 4180571 = 6270857) B6270857
theorem B4704875 : Blo 822348 4704875 := bstep (se 1 (by rfl) ⟨3528656, by rfl⟩ : syracuseStep 4704875 = 7057313) B7057313
theorem B2083583 : Blo 822348 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B9390977 : Blo 822348 9390977 := bstep (se 2 (by rfl) ⟨3521616, by rfl⟩ : syracuseStep 9390977 = 7043233) B7043233
theorem B1854431 : Blo 822348 1854431 := bstep (se 1 (by rfl) ⟨1390823, by rfl⟩ : syracuseStep 1854431 = 2781647) B2781647
theorem B3132665 : Blo 822348 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B1756571 : Blo 822348 1756571 := bstep (se 1 (by rfl) ⟨1317428, by rfl⟩ : syracuseStep 1756571 = 2634857) B2634857
theorem B2084251 : Blo 822348 2084251 := bstep (se 1 (by rfl) ⟨1563188, by rfl⟩ : syracuseStep 2084251 = 3126377) B3126377
theorem B2084687 : Blo 822348 2084687 := bstep (se 1 (by rfl) ⟨1563515, by rfl⟩ : syracuseStep 2084687 = 3127031) B3127031
theorem B1855979 : Blo 822348 1855979 := bstep (se 1 (by rfl) ⟨1391984, by rfl⟩ : syracuseStep 1855979 = 2783969) B2783969
theorem B1856105 : Blo 822348 1856105 := bstep (se 2 (by rfl) ⟨696039, by rfl⟩ : syracuseStep 1856105 = 1392079) B1392079
theorem B1757999 : Blo 822348 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B2347859 : Blo 822348 2347859 := bstep (se 1 (by rfl) ⟨1760894, by rfl⟩ : syracuseStep 2347859 = 3521789) B3521789
theorem B1561511 : Blo 822348 1561511 := bstep (se 1 (by rfl) ⟨1171133, by rfl⟩ : syracuseStep 1561511 = 2342267) B2342267
theorem B1233863 : Blo 822348 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B1233887 : Blo 822348 1233887 := bstep (se 1 (by rfl) ⟨925415, by rfl⟩ : syracuseStep 1233887 = 1850831) B1850831
theorem B6247529 : Blo 822348 6247529 := bstep (se 2 (by rfl) ⟨2342823, by rfl⟩ : syracuseStep 6247529 = 4685647) B4685647
theorem B1856735 : Blo 822348 1856735 := bstep (se 1 (by rfl) ⟨1392551, by rfl⟩ : syracuseStep 1856735 = 2785103) B2785103
theorem B1234223 : Blo 822348 1234223 := bstep (se 1 (by rfl) ⟨925667, by rfl⟩ : syracuseStep 1234223 = 1851335) B1851335
theorem B1234427 : Blo 822348 1234427 := bstep (se 1 (by rfl) ⟨925820, by rfl⟩ : syracuseStep 1234427 = 1851641) B1851641
theorem B1234463 : Blo 822348 1234463 := bstep (se 1 (by rfl) ⟨925847, by rfl⟩ : syracuseStep 1234463 = 1851695) B1851695
theorem B1857167 : Blo 822348 1857167 := bstep (se 1 (by rfl) ⟨1392875, by rfl⟩ : syracuseStep 1857167 = 2785751) B2785751
theorem B1234601 : Blo 822348 1234601 := bstep (se 2 (by rfl) ⟨462975, by rfl⟩ : syracuseStep 1234601 = 925951) B925951
theorem B1234607 : Blo 822348 1234607 := bstep (se 1 (by rfl) ⟨925955, by rfl⟩ : syracuseStep 1234607 = 1851911) B1851911
theorem B1857257 : Blo 822348 1857257 := bstep (se 2 (by rfl) ⟨696471, by rfl⟩ : syracuseStep 1857257 = 1392943) B1392943
theorem B1234727 : Blo 822348 1234727 := bstep (se 1 (by rfl) ⟨926045, by rfl⟩ : syracuseStep 1234727 = 1852091) B1852091
theorem B2348929 : Blo 822348 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B2545537 : Blo 822348 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B2119567 : Blo 822348 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B1234985 : Blo 822348 1234985 := bstep (se 2 (by rfl) ⟨463119, by rfl⟩ : syracuseStep 1234985 = 926239) B926239
theorem B1235015 : Blo 822348 1235015 := bstep (se 1 (by rfl) ⟨926261, by rfl⟩ : syracuseStep 1235015 = 1852523) B1852523
theorem B2087147 : Blo 822348 2087147 := bstep (se 1 (by rfl) ⟨1565360, by rfl⟩ : syracuseStep 2087147 = 3130721) B3130721
theorem B1235327 : Blo 822348 1235327 := bstep (se 1 (by rfl) ⟨926495, by rfl⟩ : syracuseStep 1235327 = 1852991) B1852991
theorem B1235399 : Blo 822348 1235399 := bstep (se 1 (by rfl) ⟨926549, by rfl⟩ : syracuseStep 1235399 = 1853099) B1853099
theorem B1235615 : Blo 822348 1235615 := bstep (se 1 (by rfl) ⟨926711, by rfl⟩ : syracuseStep 1235615 = 1853423) B1853423
theorem B1235759 : Blo 822348 1235759 := bstep (se 1 (by rfl) ⟨926819, by rfl⟩ : syracuseStep 1235759 = 1853639) B1853639
theorem B1235849 : Blo 822348 1235849 := bstep (se 2 (by rfl) ⟨463443, by rfl⟩ : syracuseStep 1235849 = 926887) B926887
theorem B1235879 : Blo 822348 1235879 := bstep (se 1 (by rfl) ⟨926909, by rfl⟩ : syracuseStep 1235879 = 1853819) B1853819
theorem B2775977 : Blo 822348 2775977 := bstep (se 2 (by rfl) ⟨1040991, by rfl⟩ : syracuseStep 2775977 = 2081983) B2081983
theorem B1236059 : Blo 822348 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B33873137 : Blo 822348 33873137 := bstep (se 2 (by rfl) ⟨12702426, by rfl⟩ : syracuseStep 33873137 = 25404853) B25404853
theorem B3169529 : Blo 822348 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B1236251 : Blo 822348 1236251 := bstep (se 1 (by rfl) ⟨927188, by rfl⟩ : syracuseStep 1236251 = 1854377) B1854377
theorem B1858895 : Blo 822348 1858895 := bstep (se 1 (by rfl) ⟨1394171, by rfl⟩ : syracuseStep 1858895 = 2788343) B2788343
theorem B1858985 : Blo 822348 1858985 := bstep (se 2 (by rfl) ⟨697119, by rfl⟩ : syracuseStep 1858985 = 1394239) B1394239
theorem B1564267 : Blo 822348 1564267 := bstep (se 1 (by rfl) ⟨1173200, by rfl⟩ : syracuseStep 1564267 = 2346401) B2346401
theorem B1236719 : Blo 822348 1236719 := bstep (se 1 (by rfl) ⟨927539, by rfl⟩ : syracuseStep 1236719 = 1855079) B1855079
theorem B17784593 : Blo 822348 17784593 := bstep (se 2 (by rfl) ⟨6669222, by rfl⟩ : syracuseStep 17784593 = 13338445) B13338445
theorem B1236905 : Blo 822348 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B1237055 : Blo 822348 1237055 := bstep (se 1 (by rfl) ⟨927791, by rfl⟩ : syracuseStep 1237055 = 1855583) B1855583
theorem B14114897 : Blo 822348 14114897 := bstep (se 2 (by rfl) ⟨5293086, by rfl⟩ : syracuseStep 14114897 = 10586173) B10586173
theorem B2351207 : Blo 822348 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B1237289 : Blo 822348 1237289 := bstep (se 2 (by rfl) ⟨463983, by rfl⟩ : syracuseStep 1237289 = 927967) B927967
theorem B1040951 : Blo 822348 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B1237559 : Blo 822348 1237559 := bstep (se 1 (by rfl) ⟨928169, by rfl⟩ : syracuseStep 1237559 = 1856339) B1856339
theorem B9396809 : Blo 822348 9396809 := bstep (se 2 (by rfl) ⟨3523803, by rfl⟩ : syracuseStep 9396809 = 7047607) B7047607
theorem B1565345 : Blo 822348 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B1237919 : Blo 822348 1237919 := bstep (se 1 (by rfl) ⟨928439, by rfl⟩ : syracuseStep 1237919 = 1856879) B1856879
theorem B1762415 : Blo 822348 1762415 := bstep (se 1 (by rfl) ⟨1321811, by rfl⟩ : syracuseStep 1762415 = 2643623) B2643623
theorem B1041599 : Blo 822348 1041599 := bstep (se 1 (by rfl) ⟨781199, by rfl⟩ : syracuseStep 1041599 = 1562399) B1562399
theorem B1238207 : Blo 822348 1238207 := bstep (se 1 (by rfl) ⟨928655, by rfl⟩ : syracuseStep 1238207 = 1857311) B1857311
theorem B2352347 : Blo 822348 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B1762535 : Blo 822348 1762535 := bstep (se 1 (by rfl) ⟨1321901, by rfl⟩ : syracuseStep 1762535 = 2643803) B2643803
theorem B1238351 : Blo 822348 1238351 := bstep (se 1 (by rfl) ⟨928763, by rfl⟩ : syracuseStep 1238351 = 1857527) B1857527
theorem B1238441 : Blo 822348 1238441 := bstep (se 2 (by rfl) ⟨464415, by rfl⟩ : syracuseStep 1238441 = 928831) B928831
theorem B1238591 : Blo 822348 1238591 := bstep (se 1 (by rfl) ⟨928943, by rfl⟩ : syracuseStep 1238591 = 1857887) B1857887
theorem B2090569 : Blo 822348 2090569 := bstep (se 2 (by rfl) ⟨783963, by rfl⟩ : syracuseStep 2090569 = 1567927) B1567927
theorem B1042075 : Blo 822348 1042075 := bstep (se 1 (by rfl) ⟨781556, by rfl⟩ : syracuseStep 1042075 = 1563113) B1563113
theorem B2090873 : Blo 822348 2090873 := bstep (se 2 (by rfl) ⟨784077, by rfl⟩ : syracuseStep 2090873 = 1568155) B1568155
theorem B1173371 : Blo 822348 1173371 := bstep (se 1 (by rfl) ⟨880028, by rfl⟩ : syracuseStep 1173371 = 1760057) B1760057
theorem B1238951 : Blo 822348 1238951 := bstep (se 1 (by rfl) ⟨929213, by rfl⟩ : syracuseStep 1238951 = 1858427) B1858427
theorem B1239071 : Blo 822348 1239071 := bstep (se 1 (by rfl) ⟨929303, by rfl⟩ : syracuseStep 1239071 = 1858607) B1858607
theorem B11855933 : Blo 822348 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B3172945 : Blo 822348 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B1043047 : Blo 822348 1043047 := bstep (se 1 (by rfl) ⟨782285, by rfl⟩ : syracuseStep 1043047 = 1564571) B1564571
theorem B2977003 : Blo 822348 2977003 := bstep (se 1 (by rfl) ⟨2232752, by rfl⟩ : syracuseStep 2977003 = 4465505) B4465505
theorem B3173807 : Blo 822348 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B8023643 : Blo 822348 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B1175143 : Blo 822348 1175143 := bstep (se 1 (by rfl) ⟨881357, by rfl⟩ : syracuseStep 1175143 = 1762715) B1762715
theorem B2780891 : Blo 822348 2780891 := bstep (se 1 (by rfl) ⟨2085668, by rfl⟩ : syracuseStep 2780891 = 4171337) B4171337
theorem B2977823 : Blo 822348 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B4747643 : Blo 822348 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B4289645 : Blo 822348 4289645 := bstep (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) B1608617
theorem B9369107 : Blo 822348 9369107 := bstep (se 1 (by rfl) ⟨7026830, by rfl⟩ : syracuseStep 9369107 = 14053661) B14053661
theorem B21165785 : Blo 822348 21165785 := bstep (se 2 (by rfl) ⟨7937169, by rfl⟩ : syracuseStep 21165785 = 15874339) B15874339
theorem B2783105 : Blo 822348 2783105 := bstep (se 2 (by rfl) ⟨1043664, by rfl⟩ : syracuseStep 2783105 = 2087329) B2087329
theorem B2783645 : Blo 822348 2783645 := bstep (se 3 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 2783645 = 1043867) B1043867
theorem B2784347 : Blo 822348 2784347 := bstep (se 1 (by rfl) ⟨2088260, by rfl⟩ : syracuseStep 2784347 = 4176521) B4176521
theorem B7044191 : Blo 822348 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B17825417 : Blo 822348 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B2785427 : Blo 822348 2785427 := bstep (se 1 (by rfl) ⟨2089070, by rfl⟩ : syracuseStep 2785427 = 4178141) B4178141
theorem B11272709 : Blo 822348 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B7045967 : Blo 822348 7045967 := bstep (se 1 (by rfl) ⟨5284475, by rfl⟩ : syracuseStep 7045967 = 10568951) B10568951
theorem B5931863 : Blo 822348 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B2787047 : Blo 822348 2787047 := bstep (se 1 (by rfl) ⟨2090285, by rfl⟩ : syracuseStep 2787047 = 4180571) B4180571
theorem B6260651 : Blo 822348 6260651 := bstep (se 1 (by rfl) ⟨4695488, by rfl⟩ : syracuseStep 6260651 = 9390977) B9390977
theorem B1673209 : Blo 822348 1673209 := bstep (se 2 (by rfl) ⟨627453, by rfl⟩ : syracuseStep 1673209 = 1254907) B1254907
theorem B2787425 : Blo 822348 2787425 := bstep (se 2 (by rfl) ⟨1045284, by rfl⟩ : syracuseStep 2787425 = 2090569) B2090569
theorem B23726627 : Blo 822348 23726627 := bstep (se 1 (by rfl) ⟨17794970, by rfl⟩ : syracuseStep 23726627 = 35589941) B35589941
theorem B11439053 : Blo 822348 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B12717155 : Blo 822348 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B4164857 : Blo 822348 4164857 := bstep (se 2 (by rfl) ⟨1561821, by rfl⟩ : syracuseStep 4164857 = 3123643) B3123643
theorem B822575 : Blo 822348 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B822591 : Blo 822348 822591 := bstep (se 1 (by rfl) ⟨616943, by rfl⟩ : syracuseStep 822591 = 1233887) B1233887
theorem B4165019 : Blo 822348 4165019 := bstep (se 1 (by rfl) ⟨3123764, by rfl⟩ : syracuseStep 4165019 = 6247529) B6247529
theorem B4230593 : Blo 822348 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B822815 : Blo 822348 822815 := bstep (se 1 (by rfl) ⟨617111, by rfl⟩ : syracuseStep 822815 = 1234223) B1234223
theorem B822951 : Blo 822348 822951 := bstep (se 1 (by rfl) ⟨617213, by rfl⟩ : syracuseStep 822951 = 1234427) B1234427
theorem B822975 : Blo 822348 822975 := bstep (se 1 (by rfl) ⟨617231, by rfl⟩ : syracuseStep 822975 = 1234463) B1234463
theorem B823067 : Blo 822348 823067 := bstep (se 1 (by rfl) ⟨617300, by rfl⟩ : syracuseStep 823067 = 1234601) B1234601
theorem B823071 : Blo 822348 823071 := bstep (se 1 (by rfl) ⟨617303, by rfl⟩ : syracuseStep 823071 = 1234607) B1234607
theorem B823151 : Blo 822348 823151 := bstep (se 1 (by rfl) ⟨617363, by rfl⟩ : syracuseStep 823151 = 1234727) B1234727
theorem B823323 : Blo 822348 823323 := bstep (se 1 (by rfl) ⟨617492, by rfl⟩ : syracuseStep 823323 = 1234985) B1234985
theorem B823343 : Blo 822348 823343 := bstep (se 1 (by rfl) ⟨617507, by rfl⟩ : syracuseStep 823343 = 1235015) B1235015
theorem B823551 : Blo 822348 823551 := bstep (se 1 (by rfl) ⟨617663, by rfl⟩ : syracuseStep 823551 = 1235327) B1235327
theorem B823599 : Blo 822348 823599 := bstep (se 1 (by rfl) ⟨617699, by rfl⟩ : syracuseStep 823599 = 1235399) B1235399
theorem B3969337 : Blo 822348 3969337 := bstep (se 2 (by rfl) ⟨1488501, by rfl⟩ : syracuseStep 3969337 = 2977003) B2977003
theorem B823743 : Blo 822348 823743 := bstep (se 1 (by rfl) ⟨617807, by rfl⟩ : syracuseStep 823743 = 1235615) B1235615
theorem B823839 : Blo 822348 823839 := bstep (se 1 (by rfl) ⟨617879, by rfl⟩ : syracuseStep 823839 = 1235759) B1235759
theorem B823899 : Blo 822348 823899 := bstep (se 1 (by rfl) ⟨617924, by rfl⟩ : syracuseStep 823899 = 1235849) B1235849
theorem B823919 : Blo 822348 823919 := bstep (se 1 (by rfl) ⟨617939, by rfl⟩ : syracuseStep 823919 = 1235879) B1235879
theorem B20288177 : Blo 822348 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B824039 : Blo 822348 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B22582091 : Blo 822348 22582091 := bstep (se 1 (by rfl) ⟨16936568, by rfl⟩ : syracuseStep 22582091 = 33873137) B33873137
theorem B824167 : Blo 822348 824167 := bstep (se 1 (by rfl) ⟨618125, by rfl⟩ : syracuseStep 824167 = 1236251) B1236251
theorem B824479 : Blo 822348 824479 := bstep (se 1 (by rfl) ⟨618359, by rfl⟩ : syracuseStep 824479 = 1236719) B1236719
theorem B824603 : Blo 822348 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B824703 : Blo 822348 824703 := bstep (se 1 (by rfl) ⟨618527, by rfl⟩ : syracuseStep 824703 = 1237055) B1237055
theorem B9409931 : Blo 822348 9409931 := bstep (se 1 (by rfl) ⟨7057448, by rfl⟩ : syracuseStep 9409931 = 14114897) B14114897
theorem B824859 : Blo 822348 824859 := bstep (se 1 (by rfl) ⟨618644, by rfl⟩ : syracuseStep 824859 = 1237289) B1237289
theorem B825039 : Blo 822348 825039 := bstep (se 1 (by rfl) ⟨618779, by rfl⟩ : syracuseStep 825039 = 1237559) B1237559
theorem B6264539 : Blo 822348 6264539 := bstep (se 1 (by rfl) ⟨4698404, by rfl⟩ : syracuseStep 6264539 = 9396809) B9396809
theorem B825279 : Blo 822348 825279 := bstep (se 1 (by rfl) ⟨618959, by rfl⟩ : syracuseStep 825279 = 1237919) B1237919
theorem B825471 : Blo 822348 825471 := bstep (se 1 (by rfl) ⟨619103, by rfl⟩ : syracuseStep 825471 = 1238207) B1238207
theorem B825567 : Blo 822348 825567 := bstep (se 1 (by rfl) ⟨619175, by rfl⟩ : syracuseStep 825567 = 1238351) B1238351
theorem B825627 : Blo 822348 825627 := bstep (se 1 (by rfl) ⟨619220, by rfl⟩ : syracuseStep 825627 = 1238441) B1238441
theorem B825727 : Blo 822348 825727 := bstep (se 1 (by rfl) ⟨619295, by rfl⟩ : syracuseStep 825727 = 1238591) B1238591
theorem B4168097 : Blo 822348 4168097 := bstep (se 2 (by rfl) ⟨1563036, by rfl⟩ : syracuseStep 4168097 = 3126073) B3126073
theorem B825967 : Blo 822348 825967 := bstep (se 1 (by rfl) ⟨619475, by rfl⟩ : syracuseStep 825967 = 1238951) B1238951
theorem B826047 : Blo 822348 826047 := bstep (se 1 (by rfl) ⟨619535, by rfl⟩ : syracuseStep 826047 = 1239071) B1239071
theorem B7903955 : Blo 822348 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B1252135 : Blo 822348 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B4168745 : Blo 822348 4168745 := bstep (se 2 (by rfl) ⟨1563279, by rfl⟩ : syracuseStep 4168745 = 3126559) B3126559
theorem B5021165 : Blo 822348 5021165 := bstep (se 3 (by rfl) ⟨941468, by rfl⟩ : syracuseStep 5021165 = 1882937) B1882937
theorem B5349095 : Blo 822348 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B15834973 : Blo 822348 15834973 := bstep (se 3 (by rfl) ⟨2969057, by rfl⟩ : syracuseStep 15834973 = 5938115) B5938115
theorem B2826089 : Blo 822348 2826089 := bstep (se 2 (by rfl) ⟨1059783, by rfl⟩ : syracuseStep 2826089 = 2119567) B2119567
theorem B8463485 : Blo 822348 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B927103 : Blo 822348 927103 := bstep (se 1 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 927103 = 1390655) B1390655
theorem B4696127 : Blo 822348 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B7940861 : Blo 822348 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B6269885 : Blo 822348 6269885 := bstep (se 3 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 6269885 = 2351207) B2351207
theorem B3124889 : Blo 822348 3124889 := bstep (se 2 (by rfl) ⟨1171833, by rfl⟩ : syracuseStep 3124889 = 2343667) B2343667
theorem B7057691 : Blo 822348 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B3518815 : Blo 822348 3518815 := bstep (se 1 (by rfl) ⟨2639111, by rfl⟩ : syracuseStep 3518815 = 5278223) B5278223
theorem B4174253 : Blo 822348 4174253 := bstep (se 3 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 4174253 = 1565345) B1565345
theorem B1389055 : Blo 822348 1389055 := bstep (se 1 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 1389055 = 2083583) B2083583
theorem B1389433 : Blo 822348 1389433 := bstep (se 2 (by rfl) ⟨521037, by rfl⟩ : syracuseStep 1389433 = 1042075) B1042075
theorem B3519551 : Blo 822348 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B1389791 : Blo 822348 1389791 := bstep (se 1 (by rfl) ⟨1042343, by rfl⟩ : syracuseStep 1389791 = 2084687) B2084687
theorem B13350905 : Blo 822348 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B50640977 : Blo 822348 50640977 := bstep (se 2 (by rfl) ⟨18990366, by rfl⟩ : syracuseStep 50640977 = 37980733) B37980733
theorem B1390729 : Blo 822348 1390729 := bstep (se 2 (by rfl) ⟨521523, by rfl⟩ : syracuseStep 1390729 = 1043047) B1043047
theorem B1391431 : Blo 822348 1391431 := bstep (se 1 (by rfl) ⟨1043573, by rfl⟩ : syracuseStep 1391431 = 2087147) B2087147
theorem B1850489 : Blo 822348 1850489 := bstep (se 2 (by rfl) ⟨693933, by rfl⟩ : syracuseStep 1850489 = 1387867) B1387867
theorem B1850651 : Blo 822348 1850651 := bstep (se 1 (by rfl) ⟨1387988, by rfl⟩ : syracuseStep 1850651 = 2775977) B2775977
theorem B7519517 : Blo 822348 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B5291345 : Blo 822348 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B1850849 : Blo 822348 1850849 := bstep (se 2 (by rfl) ⟨694068, by rfl⟩ : syracuseStep 1850849 = 1388137) B1388137
theorem B2113019 : Blo 822348 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B3128989 : Blo 822348 3128989 := bstep (se 3 (by rfl) ⟨586685, by rfl⟩ : syracuseStep 3128989 = 1173371) B1173371
theorem B5948093 : Blo 822348 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B2081771 : Blo 822348 2081771 := bstep (se 1 (by rfl) ⟨1561328, by rfl⟩ : syracuseStep 2081771 = 3122657) B3122657
theorem B1393915 : Blo 822348 1393915 := bstep (se 1 (by rfl) ⟨1045436, by rfl⟩ : syracuseStep 1393915 = 2090873) B2090873
theorem B35702045 : Blo 822348 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B2082095 : Blo 822348 2082095 := bstep (se 1 (by rfl) ⟨1561571, by rfl⟩ : syracuseStep 2082095 = 3123143) B3123143
theorem B1853153 : Blo 822348 1853153 := bstep (se 2 (by rfl) ⟨694932, by rfl⟩ : syracuseStep 1853153 = 1389865) B1389865
theorem B2082955 : Blo 822348 2082955 := bstep (se 1 (by rfl) ⟨1562216, by rfl⟩ : syracuseStep 2082955 = 3124433) B3124433
theorem B4507907 : Blo 822348 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B1853927 : Blo 822348 1853927 := bstep (se 1 (by rfl) ⟨1390445, by rfl⟩ : syracuseStep 1853927 = 2780891) B2780891
theorem B3131905 : Blo 822348 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B3394049 : Blo 822348 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B2640701 : Blo 822348 2640701 := bstep (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) B990263
theorem B3165095 : Blo 822348 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B3525839 : Blo 822348 3525839 := bstep (se 1 (by rfl) ⟨2644379, by rfl⟩ : syracuseStep 3525839 = 5288759) B5288759
theorem B2346515 : Blo 822348 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B6246071 : Blo 822348 6246071 := bstep (se 1 (by rfl) ⟨4684553, by rfl⟩ : syracuseStep 6246071 = 9369107) B9369107
theorem B14110523 : Blo 822348 14110523 := bstep (se 1 (by rfl) ⟨10582892, by rfl⟩ : syracuseStep 14110523 = 21165785) B21165785
theorem B1855403 : Blo 822348 1855403 := bstep (se 1 (by rfl) ⟨1391552, by rfl⟩ : syracuseStep 1855403 = 2783105) B2783105
theorem B28987409 : Blo 822348 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B3526847 : Blo 822348 3526847 := bstep (se 1 (by rfl) ⟨2645135, by rfl⟩ : syracuseStep 3526847 = 5290271) B5290271
theorem B1855763 : Blo 822348 1855763 := bstep (se 1 (by rfl) ⟨1391822, by rfl⟩ : syracuseStep 1855763 = 2783645) B2783645
theorem B2347471 : Blo 822348 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B1856231 : Blo 822348 1856231 := bstep (se 1 (by rfl) ⟨1392173, by rfl⟩ : syracuseStep 1856231 = 2784347) B2784347
theorem B2085689 : Blo 822348 2085689 := bstep (se 2 (by rfl) ⟨782133, by rfl⟩ : syracuseStep 2085689 = 1564267) B1564267
theorem B11883611 : Blo 822348 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B1758793 : Blo 822348 1758793 := bstep (se 2 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 1758793 = 1319095) B1319095
theorem B6248015 : Blo 822348 6248015 := bstep (se 1 (by rfl) ⟨4686011, by rfl⟩ : syracuseStep 6248015 = 9372023) B9372023
theorem B1857131 : Blo 822348 1857131 := bstep (se 1 (by rfl) ⟨1392848, by rfl⟩ : syracuseStep 1857131 = 2785697) B2785697
theorem B1857491 : Blo 822348 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B1857563 : Blo 822348 1857563 := bstep (se 1 (by rfl) ⟨1393172, by rfl⟩ : syracuseStep 1857563 = 2786345) B2786345
theorem B1563295 : Blo 822348 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B5003963 : Blo 822348 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B1235753 : Blo 822348 1235753 := bstep (se 2 (by rfl) ⟨463407, by rfl⟩ : syracuseStep 1235753 = 926815) B926815
theorem B2775869 : Blo 822348 2775869 := bstep (se 3 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 2775869 = 1040951) B1040951
theorem B1563455 : Blo 822348 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B3136583 : Blo 822348 3136583 := bstep (se 1 (by rfl) ⟨2352437, by rfl⟩ : syracuseStep 3136583 = 4704875) B4704875
theorem B1858823 : Blo 822348 1858823 := bstep (se 1 (by rfl) ⟨1394117, by rfl⟩ : syracuseStep 1858823 = 2788235) B2788235
theorem B1236287 : Blo 822348 1236287 := bstep (se 1 (by rfl) ⟨927215, by rfl⟩ : syracuseStep 1236287 = 1854431) B1854431
theorem B2088443 : Blo 822348 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B1859183 : Blo 822348 1859183 := bstep (se 1 (by rfl) ⟨1394387, by rfl⟩ : syracuseStep 1859183 = 2788775) B2788775
theorem B1236617 : Blo 822348 1236617 := bstep (se 2 (by rfl) ⟨463731, by rfl⟩ : syracuseStep 1236617 = 927463) B927463
theorem B2777057 : Blo 822348 2777057 := bstep (se 2 (by rfl) ⟨1041396, by rfl⟩ : syracuseStep 2777057 = 2082793) B2082793
theorem B1237319 : Blo 822348 1237319 := bstep (se 1 (by rfl) ⟨927989, by rfl⟩ : syracuseStep 1237319 = 1855979) B1855979
theorem B1237403 : Blo 822348 1237403 := bstep (se 1 (by rfl) ⟨928052, by rfl⟩ : syracuseStep 1237403 = 1856105) B1856105
theorem B2777597 : Blo 822348 2777597 := bstep (se 3 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 2777597 = 1041599) B1041599
theorem B1171999 : Blo 822348 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B1565239 : Blo 822348 1565239 := bstep (se 1 (by rfl) ⟨1173929, by rfl⟩ : syracuseStep 1565239 = 2347859) B2347859
theorem B2777705 : Blo 822348 2777705 := bstep (se 2 (by rfl) ⟨1041639, by rfl⟩ : syracuseStep 2777705 = 2083279) B2083279
theorem B1041007 : Blo 822348 1041007 := bstep (se 1 (by rfl) ⟨780755, by rfl⟩ : syracuseStep 1041007 = 1561511) B1561511
theorem B2777759 : Blo 822348 2777759 := bstep (se 1 (by rfl) ⟨2083319, by rfl⟩ : syracuseStep 2777759 = 4166639) B4166639
theorem B1237823 : Blo 822348 1237823 := bstep (se 1 (by rfl) ⟨928367, by rfl⟩ : syracuseStep 1237823 = 1856735) B1856735
theorem B2974697 : Blo 822348 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B1238111 : Blo 822348 1238111 := bstep (se 1 (by rfl) ⟨928583, by rfl⟩ : syracuseStep 1238111 = 1857167) B1857167
theorem B1238171 : Blo 822348 1238171 := bstep (se 1 (by rfl) ⟨928628, by rfl⟩ : syracuseStep 1238171 = 1857257) B1857257
theorem B2975201 : Blo 822348 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B2779001 : Blo 822348 2779001 := bstep (se 2 (by rfl) ⟨1042125, by rfl⟩ : syracuseStep 2779001 = 2084251) B2084251
theorem B1566857 : Blo 822348 1566857 := bstep (se 2 (by rfl) ⟨587571, by rfl⟩ : syracuseStep 1566857 = 1175143) B1175143
theorem B1239263 : Blo 822348 1239263 := bstep (se 1 (by rfl) ⟨929447, by rfl⟩ : syracuseStep 1239263 = 1858895) B1858895
theorem B1239323 : Blo 822348 1239323 := bstep (se 1 (by rfl) ⟨929492, by rfl⟩ : syracuseStep 1239323 = 1858985) B1858985
theorem B11856395 : Blo 822348 11856395 := bstep (se 1 (by rfl) ⟨8892296, by rfl⟩ : syracuseStep 11856395 = 17784593) B17784593
theorem B47475395 : Blo 822348 47475395 := bstep (se 1 (by rfl) ⟨35606546, by rfl⟩ : syracuseStep 47475395 = 71213093) B71213093
theorem B30108419 : Blo 822348 30108419 := bstep (se 1 (by rfl) ⟨22581314, by rfl⟩ : syracuseStep 30108419 = 45162629) B45162629
theorem B7039817 : Blo 822348 7039817 := bstep (se 2 (by rfl) ⟨2639931, by rfl⟩ : syracuseStep 7039817 = 5279863) B5279863
theorem B2780027 : Blo 822348 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B11889611 : Blo 822348 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B1174943 : Blo 822348 1174943 := bstep (se 1 (by rfl) ⟨881207, by rfl⟩ : syracuseStep 1174943 = 1762415) B1762415
theorem B1568231 : Blo 822348 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B1175023 : Blo 822348 1175023 := bstep (se 1 (by rfl) ⟨881267, by rfl⟩ : syracuseStep 1175023 = 1762535) B1762535
theorem B880319 : Blo 822348 880319 := bstep (se 1 (by rfl) ⟨660239, by rfl⟩ : syracuseStep 880319 = 1320479) B1320479
theorem B2780999 : Blo 822348 2780999 := bstep (se 1 (by rfl) ⟨2085749, by rfl⟩ : syracuseStep 2780999 = 4171499) B4171499
theorem B2978171 : Blo 822348 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B3765467 : Blo 822348 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B2782943 : Blo 822348 2782943 := bstep (se 1 (by rfl) ⟨2087207, by rfl⟩ : syracuseStep 2782943 = 4174415) B4174415
theorem B6256763 : Blo 822348 6256763 := bstep (se 1 (by rfl) ⟨4692572, by rfl⟩ : syracuseStep 6256763 = 9385145) B9385145
theorem B3766607 : Blo 822348 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B4684189 : Blo 822348 4684189 := bstep (se 3 (by rfl) ⟨878285, by rfl⟩ : syracuseStep 4684189 = 1756571) B1756571
theorem B6257735 : Blo 822348 6257735 := bstep (se 1 (by rfl) ⟨4693301, by rfl⟩ : syracuseStep 6257735 = 9386603) B9386603
theorem B2784455 : Blo 822348 2784455 := bstep (se 1 (by rfl) ⟨2088341, by rfl⟩ : syracuseStep 2784455 = 4176683) B4176683
theorem B77299757 : Blo 822348 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B15861581 : Blo 822348 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B2820395 : Blo 822348 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B4164047 : Blo 822348 4164047 := bstep (se 1 (by rfl) ⟨3123035, by rfl⟩ : syracuseStep 4164047 = 6246071) B6246071
theorem B9407015 : Blo 822348 9407015 := bstep (se 1 (by rfl) ⟨7055261, by rfl⟩ : syracuseStep 9407015 = 14110523) B14110523
theorem B2230945 : Blo 822348 2230945 := bstep (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) B1673209
theorem B31689629 : Blo 822348 31689629 := bstep (se 3 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 31689629 = 11883611) B11883611
theorem B4165343 : Blo 822348 4165343 := bstep (se 1 (by rfl) ⟨3124007, by rfl⟩ : syracuseStep 4165343 = 6248015) B6248015
theorem B823835 : Blo 822348 823835 := bstep (se 1 (by rfl) ⟨617876, by rfl⟩ : syracuseStep 823835 = 1235753) B1235753
theorem B824191 : Blo 822348 824191 := bstep (se 1 (by rfl) ⟨618143, by rfl⟩ : syracuseStep 824191 = 1236287) B1236287
theorem B3347443 : Blo 822348 3347443 := bstep (se 1 (by rfl) ⟨2510582, by rfl⟩ : syracuseStep 3347443 = 5021165) B5021165
theorem B824411 : Blo 822348 824411 := bstep (se 1 (by rfl) ⟨618308, by rfl⟩ : syracuseStep 824411 = 1236617) B1236617
theorem B824879 : Blo 822348 824879 := bstep (se 1 (by rfl) ⟨618659, by rfl⟩ : syracuseStep 824879 = 1237319) B1237319
theorem B824935 : Blo 822348 824935 := bstep (se 1 (by rfl) ⟨618701, by rfl⟩ : syracuseStep 824935 = 1237403) B1237403
theorem B4691753 : Blo 822348 4691753 := bstep (se 2 (by rfl) ⟨1759407, by rfl⟩ : syracuseStep 4691753 = 3518815) B3518815
theorem B825215 : Blo 822348 825215 := bstep (se 1 (by rfl) ⟨618911, by rfl⟩ : syracuseStep 825215 = 1237823) B1237823
theorem B825407 : Blo 822348 825407 := bstep (se 1 (by rfl) ⟨619055, by rfl⟩ : syracuseStep 825407 = 1238111) B1238111
theorem B825447 : Blo 822348 825447 := bstep (se 1 (by rfl) ⟨619085, by rfl⟩ : syracuseStep 825447 = 1238171) B1238171
theorem B9050797 : Blo 822348 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B826175 : Blo 822348 826175 := bstep (se 1 (by rfl) ⟨619631, by rfl⟩ : syracuseStep 826175 = 1239263) B1239263
theorem B826215 : Blo 822348 826215 := bstep (se 1 (by rfl) ⟨619661, by rfl⟩ : syracuseStep 826215 = 1239323) B1239323
theorem B7904263 : Blo 822348 7904263 := bstep (se 1 (by rfl) ⟨5928197, by rfl⟩ : syracuseStep 7904263 = 11856395) B11856395
theorem B4693211 : Blo 822348 4693211 := bstep (se 1 (by rfl) ⟨3519908, by rfl⟩ : syracuseStep 4693211 = 7039817) B7039817
theorem B926527 : Blo 822348 926527 := bstep (se 1 (by rfl) ⟨694895, by rfl⟩ : syracuseStep 926527 = 1389791) B1389791
theorem B33760651 : Blo 822348 33760651 := bstep (se 1 (by rfl) ⟨25320488, by rfl⟩ : syracuseStep 33760651 = 50640977) B50640977
theorem B4171175 : Blo 822348 4171175 := bstep (se 1 (by rfl) ⟨3128381, by rfl⟩ : syracuseStep 4171175 = 6256763) B6256763
theorem B4171823 : Blo 822348 4171823 := bstep (se 1 (by rfl) ⟨3128867, by rfl⟩ : syracuseStep 4171823 = 6257735) B6257735
theorem B4171985 : Blo 822348 4171985 := bstep (se 2 (by rfl) ⟨1564494, by rfl⟩ : syracuseStep 4171985 = 3128989) B3128989
theorem B21113297 : Blo 822348 21113297 := bstep (se 2 (by rfl) ⟨7917486, by rfl⟩ : syracuseStep 21113297 = 15834973) B15834973
theorem B4697311 : Blo 822348 4697311 := bstep (se 1 (by rfl) ⟨3522983, by rfl⟩ : syracuseStep 4697311 = 7045967) B7045967
theorem B1387847 : Blo 822348 1387847 := bstep (se 1 (by rfl) ⟨1040885, by rfl⟩ : syracuseStep 1387847 = 2081771) B2081771
theorem B1388009 : Blo 822348 1388009 := bstep (se 2 (by rfl) ⟨520503, by rfl⟩ : syracuseStep 1388009 = 1041007) B1041007
theorem B23801363 : Blo 822348 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B1388063 : Blo 822348 1388063 := bstep (se 1 (by rfl) ⟨1041047, by rfl⟩ : syracuseStep 1388063 = 2082095) B2082095
theorem B4173767 : Blo 822348 4173767 := bstep (se 1 (by rfl) ⟨3130325, by rfl⟩ : syracuseStep 4173767 = 6260651) B6260651
theorem B30060557 : Blo 822348 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B2110063 : Blo 822348 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B1390459 : Blo 822348 1390459 := bstep (se 1 (by rfl) ⟨1042844, by rfl⟩ : syracuseStep 1390459 = 2085689) B2085689
theorem B10041245 : Blo 822348 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B4175873 : Blo 822348 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B6273287 : Blo 822348 6273287 := bstep (se 1 (by rfl) ⟨4704965, by rfl⟩ : syracuseStep 6273287 = 9409931) B9409931
theorem B4176359 : Blo 822348 4176359 := bstep (se 1 (by rfl) ⟨3132269, by rfl⟩ : syracuseStep 4176359 = 6264539) B6264539
theorem B1850579 : Blo 822348 1850579 := bstep (se 1 (by rfl) ⟨1387934, by rfl⟩ : syracuseStep 1850579 = 2775869) B2775869
theorem B1392295 : Blo 822348 1392295 := bstep (se 1 (by rfl) ⟨1044221, by rfl⟩ : syracuseStep 1392295 = 2088443) B2088443
theorem B1884059 : Blo 822348 1884059 := bstep (se 1 (by rfl) ⟨1413044, by rfl⟩ : syracuseStep 1884059 = 2826089) B2826089
theorem B1851371 : Blo 822348 1851371 := bstep (se 1 (by rfl) ⟨1388528, by rfl⟩ : syracuseStep 1851371 = 2777057) B2777057
theorem B1851731 : Blo 822348 1851731 := bstep (se 1 (by rfl) ⟨1388798, by rfl⟩ : syracuseStep 1851731 = 2777597) B2777597
theorem B1851803 : Blo 822348 1851803 := bstep (se 1 (by rfl) ⟨1388852, by rfl⟩ : syracuseStep 1851803 = 2777705) B2777705
theorem B5292449 : Blo 822348 5292449 := bstep (se 2 (by rfl) ⟨1984668, by rfl⟩ : syracuseStep 5292449 = 3969337) B3969337
theorem B1851839 : Blo 822348 1851839 := bstep (se 1 (by rfl) ⟨1388879, by rfl⟩ : syracuseStep 1851839 = 2777759) B2777759
theorem B3129961 : Blo 822348 3129961 := bstep (se 2 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 3129961 = 2347471) B2347471
theorem B1983131 : Blo 822348 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B1852073 : Blo 822348 1852073 := bstep (se 2 (by rfl) ⟨694527, by rfl⟩ : syracuseStep 1852073 = 1389055) B1389055
theorem B1983467 : Blo 822348 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B1852577 : Blo 822348 1852577 := bstep (se 2 (by rfl) ⟨694716, by rfl⟩ : syracuseStep 1852577 = 1389433) B1389433
theorem B1852667 : Blo 822348 1852667 := bstep (se 1 (by rfl) ⟨1389500, by rfl⟩ : syracuseStep 1852667 = 2779001) B2779001
theorem B3130751 : Blo 822348 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B5293907 : Blo 822348 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B20072279 : Blo 822348 20072279 := bstep (se 1 (by rfl) ⟨15054209, by rfl⟩ : syracuseStep 20072279 = 30108419) B30108419
theorem B1853351 : Blo 822348 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B4179923 : Blo 822348 4179923 := bstep (se 1 (by rfl) ⟨3134942, by rfl⟩ : syracuseStep 4179923 = 6269885) B6269885
theorem B2345057 : Blo 822348 2345057 := bstep (se 2 (by rfl) ⟨879396, by rfl⟩ : syracuseStep 2345057 = 1758793) B1758793
theorem B2083259 : Blo 822348 2083259 := bstep (se 1 (by rfl) ⟨1562444, by rfl⟩ : syracuseStep 2083259 = 3124889) B3124889
theorem B1853999 : Blo 822348 1853999 := bstep (se 1 (by rfl) ⟨1390499, by rfl⟩ : syracuseStep 1853999 = 2780999) B2780999
theorem B1854305 : Blo 822348 1854305 := bstep (se 2 (by rfl) ⟨695364, by rfl⟩ : syracuseStep 1854305 = 1390729) B1390729
theorem B4705127 : Blo 822348 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1985447 : Blo 822348 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B6245585 : Blo 822348 6245585 := bstep (se 2 (by rfl) ⟨2342094, by rfl⟩ : syracuseStep 6245585 = 4684189) B4684189
theorem B2346367 : Blo 822348 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B2084393 : Blo 822348 2084393 := bstep (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) B1563295
theorem B3133181 : Blo 822348 3133181 := bstep (se 3 (by rfl) ⟨587471, by rfl⟩ : syracuseStep 3133181 = 1174943) B1174943
theorem B1855241 : Blo 822348 1855241 := bstep (se 2 (by rfl) ⟨695715, by rfl⟩ : syracuseStep 1855241 = 1391431) B1391431
theorem B1855295 : Blo 822348 1855295 := bstep (se 1 (by rfl) ⟨1391471, by rfl⟩ : syracuseStep 1855295 = 2782943) B2782943
theorem B8900603 : Blo 822348 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B2511071 : Blo 822348 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B2347517 : Blo 822348 2347517 := bstep (se 3 (by rfl) ⟨440159, by rfl⟩ : syracuseStep 2347517 = 880319) B880319
theorem B1233659 : Blo 822348 1233659 := bstep (se 1 (by rfl) ⟨925244, by rfl⟩ : syracuseStep 1233659 = 1850489) B1850489
theorem B1856303 : Blo 822348 1856303 := bstep (se 1 (by rfl) ⟨1392227, by rfl⟩ : syracuseStep 1856303 = 2784455) B2784455
theorem B1233767 : Blo 822348 1233767 := bstep (se 1 (by rfl) ⟨925325, by rfl⟩ : syracuseStep 1233767 = 1850651) B1850651
theorem B3527563 : Blo 822348 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B1233899 : Blo 822348 1233899 := bstep (se 1 (by rfl) ⟨925424, by rfl⟩ : syracuseStep 1233899 = 1850849) B1850849
theorem B1856951 : Blo 822348 1856951 := bstep (se 1 (by rfl) ⟨1392713, by rfl⟩ : syracuseStep 1856951 = 2785427) B2785427
theorem B3954575 : Blo 822348 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B1562665 : Blo 822348 1562665 := bstep (se 2 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 1562665 = 1171999) B1171999
theorem B2086985 : Blo 822348 2086985 := bstep (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) B1565239
theorem B1235435 : Blo 822348 1235435 := bstep (se 1 (by rfl) ⟨926576, by rfl⟩ : syracuseStep 1235435 = 1853153) B1853153
theorem B1858031 : Blo 822348 1858031 := bstep (se 1 (by rfl) ⟨1393523, by rfl⟩ : syracuseStep 1858031 = 2787047) B2787047
theorem B1858283 : Blo 822348 1858283 := bstep (se 1 (by rfl) ⟨1393712, by rfl⟩ : syracuseStep 1858283 = 2787425) B2787425
theorem B1235951 : Blo 822348 1235951 := bstep (se 1 (by rfl) ⟨926963, by rfl⟩ : syracuseStep 1235951 = 1853927) B1853927
theorem B1858553 : Blo 822348 1858553 := bstep (se 2 (by rfl) ⟨696957, by rfl⟩ : syracuseStep 1858553 = 1393915) B1393915
theorem B15817751 : Blo 822348 15817751 := bstep (se 1 (by rfl) ⟨11863313, by rfl⟩ : syracuseStep 15817751 = 23726627) B23726627
theorem B1236137 : Blo 822348 1236137 := bstep (se 2 (by rfl) ⟨463551, by rfl⟩ : syracuseStep 1236137 = 927103) B927103
theorem B1760467 : Blo 822348 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B7626035 : Blo 822348 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B8478103 : Blo 822348 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B2350559 : Blo 822348 2350559 := bstep (se 1 (by rfl) ⟨1762919, by rfl⟩ : syracuseStep 2350559 = 3525839) B3525839
theorem B2776571 : Blo 822348 2776571 := bstep (se 1 (by rfl) ⟨2082428, by rfl⟩ : syracuseStep 2776571 = 4164857) B4164857
theorem B60218909 : Blo 822348 60218909 := bstep (se 3 (by rfl) ⟨11291045, by rfl⟩ : syracuseStep 60218909 = 22582091) B22582091
theorem B2776679 : Blo 822348 2776679 := bstep (se 1 (by rfl) ⟨2082509, by rfl⟩ : syracuseStep 2776679 = 4165019) B4165019
theorem B1564343 : Blo 822348 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B1236935 : Blo 822348 1236935 := bstep (se 1 (by rfl) ⟨927701, by rfl⟩ : syracuseStep 1236935 = 1855403) B1855403
theorem B2351231 : Blo 822348 2351231 := bstep (se 1 (by rfl) ⟨1763423, by rfl⟩ : syracuseStep 2351231 = 3526847) B3526847
theorem B1237175 : Blo 822348 1237175 := bstep (se 1 (by rfl) ⟨927881, by rfl⟩ : syracuseStep 1237175 = 1855763) B1855763
theorem B2777273 : Blo 822348 2777273 := bstep (se 2 (by rfl) ⟨1041477, by rfl⟩ : syracuseStep 2777273 = 2082955) B2082955
theorem B22569293 : Blo 822348 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B13525451 : Blo 822348 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B1237487 : Blo 822348 1237487 := bstep (se 1 (by rfl) ⟨928115, by rfl⟩ : syracuseStep 1237487 = 1856231) B1856231
theorem B1238087 : Blo 822348 1238087 := bstep (se 1 (by rfl) ⟨928565, by rfl⟩ : syracuseStep 1238087 = 1857131) B1857131
theorem B1238327 : Blo 822348 1238327 := bstep (se 1 (by rfl) ⟨928745, by rfl⟩ : syracuseStep 1238327 = 1857491) B1857491
theorem B1238375 : Blo 822348 1238375 := bstep (se 1 (by rfl) ⟨928781, by rfl⟩ : syracuseStep 1238375 = 1857563) B1857563
theorem B2778731 : Blo 822348 2778731 := bstep (se 1 (by rfl) ⟨2084048, by rfl⟩ : syracuseStep 2778731 = 4168097) B4168097
theorem B3335975 : Blo 822348 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B5269303 : Blo 822348 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B1042303 : Blo 822348 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B1566697 : Blo 822348 1566697 := bstep (se 2 (by rfl) ⟨587511, by rfl⟩ : syracuseStep 1566697 = 1175023) B1175023
theorem B2779163 : Blo 822348 2779163 := bstep (se 1 (by rfl) ⟨2084372, by rfl⟩ : syracuseStep 2779163 = 4168745) B4168745
theorem B2091055 : Blo 822348 2091055 := bstep (se 1 (by rfl) ⟨1568291, by rfl⟩ : syracuseStep 2091055 = 3136583) B3136583
theorem B1239215 : Blo 822348 1239215 := bstep (se 1 (by rfl) ⟨929411, by rfl⟩ : syracuseStep 1239215 = 1858823) B1858823
theorem B1239455 : Blo 822348 1239455 := bstep (se 1 (by rfl) ⟨929591, by rfl⟩ : syracuseStep 1239455 = 1859183) B1859183
theorem B3566063 : Blo 822348 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B12021085 : Blo 822348 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B1044571 : Blo 822348 1044571 := bstep (se 1 (by rfl) ⟨783428, by rfl⟩ : syracuseStep 1044571 = 1566857) B1566857
theorem B31650263 : Blo 822348 31650263 := bstep (se 1 (by rfl) ⟨23737697, by rfl⟩ : syracuseStep 31650263 = 47475395) B47475395
theorem B7926407 : Blo 822348 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B1045487 : Blo 822348 1045487 := bstep (se 1 (by rfl) ⟨784115, by rfl⟩ : syracuseStep 1045487 = 1568231) B1568231
theorem B2782835 : Blo 822348 2782835 := bstep (se 1 (by rfl) ⟨2087126, by rfl⟩ : syracuseStep 2782835 = 4174253) B4174253
theorem B1669513 : Blo 822348 1669513 := bstep (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) B1252135
theorem B5013011 : Blo 822348 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B1408679 : Blo 822348 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B2786615 : Blo 822348 2786615 := bstep (se 1 (by rfl) ⟨2089961, by rfl⟩ : syracuseStep 2786615 = 4179923) B4179923
theorem B4163723 : Blo 822348 4163723 := bstep (se 1 (by rfl) ⟨3122792, by rfl⟩ : syracuseStep 4163723 = 6245585) B6245585
theorem B2787965 : Blo 822348 2787965 := bstep (se 3 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 2787965 = 1045487) B1045487
theorem B5933735 : Blo 822348 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B2788073 : Blo 822348 2788073 := bstep (se 2 (by rfl) ⟨1045527, by rfl⟩ : syracuseStep 2788073 = 2091055) B2091055
theorem B1674047 : Blo 822348 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B822439 : Blo 822348 822439 := bstep (se 1 (by rfl) ⟨616829, by rfl⟩ : syracuseStep 822439 = 1233659) B1233659
theorem B822511 : Blo 822348 822511 := bstep (se 1 (by rfl) ⟨616883, by rfl⟩ : syracuseStep 822511 = 1233767) B1233767
theorem B822599 : Blo 822348 822599 := bstep (se 1 (by rfl) ⟨616949, by rfl⟩ : syracuseStep 822599 = 1233899) B1233899
theorem B48270917 : Blo 822348 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B6263081 : Blo 822348 6263081 := bstep (se 2 (by rfl) ⟨2348655, by rfl⟩ : syracuseStep 6263081 = 4697311) B4697311
theorem B823623 : Blo 822348 823623 := bstep (se 1 (by rfl) ⟨617717, by rfl⟩ : syracuseStep 823623 = 1235435) B1235435
theorem B16028113 : Blo 822348 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B823967 : Blo 822348 823967 := bstep (se 1 (by rfl) ⟨617975, by rfl⟩ : syracuseStep 823967 = 1235951) B1235951
theorem B824091 : Blo 822348 824091 := bstep (se 1 (by rfl) ⟨618068, by rfl⟩ : syracuseStep 824091 = 1236137) B1236137
theorem B40145939 : Blo 822348 40145939 := bstep (se 1 (by rfl) ⟨30109454, by rfl⟩ : syracuseStep 40145939 = 60218909) B60218909
theorem B824623 : Blo 822348 824623 := bstep (se 1 (by rfl) ⟨618467, by rfl⟩ : syracuseStep 824623 = 1236935) B1236935
theorem B824783 : Blo 822348 824783 := bstep (se 1 (by rfl) ⟨618587, by rfl⟩ : syracuseStep 824783 = 1237175) B1237175
theorem B15046195 : Blo 822348 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B9016967 : Blo 822348 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B824991 : Blo 822348 824991 := bstep (se 1 (by rfl) ⟨618743, by rfl⟩ : syracuseStep 824991 = 1237487) B1237487
theorem B825391 : Blo 822348 825391 := bstep (se 1 (by rfl) ⟨619043, by rfl⟩ : syracuseStep 825391 = 1238087) B1238087
theorem B825551 : Blo 822348 825551 := bstep (se 1 (by rfl) ⟨619163, by rfl⟩ : syracuseStep 825551 = 1238327) B1238327
theorem B825583 : Blo 822348 825583 := bstep (se 1 (by rfl) ⟨619187, by rfl⟩ : syracuseStep 825583 = 1238375) B1238375
theorem B9509501 : Blo 822348 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B4463257 : Blo 822348 4463257 := bstep (se 2 (by rfl) ⟨1673721, by rfl⟩ : syracuseStep 4463257 = 3347443) B3347443
theorem B826143 : Blo 822348 826143 := bstep (se 1 (by rfl) ⟨619607, by rfl⟩ : syracuseStep 826143 = 1239215) B1239215
theorem B826303 : Blo 822348 826303 := bstep (se 1 (by rfl) ⟨619727, by rfl⟩ : syracuseStep 826303 = 1239455) B1239455
theorem B925231 : Blo 822348 925231 := bstep (se 1 (by rfl) ⟨693923, by rfl⟩ : syracuseStep 925231 = 1387847) B1387847
theorem B925339 : Blo 822348 925339 := bstep (se 1 (by rfl) ⟨694004, by rfl⟩ : syracuseStep 925339 = 1388009) B1388009
theorem B15867575 : Blo 822348 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B925375 : Blo 822348 925375 := bstep (se 1 (by rfl) ⟨694031, by rfl⟩ : syracuseStep 925375 = 1388063) B1388063
theorem B5284271 : Blo 822348 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B6694163 : Blo 822348 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B1256039 : Blo 822348 1256039 := bstep (se 1 (by rfl) ⟨942029, by rfl⟩ : syracuseStep 1256039 = 1884059) B1884059
theorem B1322087 : Blo 822348 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B4173281 : Blo 822348 4173281 := bstep (se 2 (by rfl) ⟨1564980, by rfl⟩ : syracuseStep 4173281 = 3129961) B3129961
theorem B13381519 : Blo 822348 13381519 := bstep (se 1 (by rfl) ⟨10036139, by rfl⟩ : syracuseStep 13381519 = 20072279) B20072279
theorem B1880263 : Blo 822348 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B1388839 : Blo 822348 1388839 := bstep (se 1 (by rfl) ⟨1041629, by rfl⟩ : syracuseStep 1388839 = 2083259) B2083259
theorem B6271343 : Blo 822348 6271343 := bstep (se 1 (by rfl) ⟨4703507, by rfl⟩ : syracuseStep 6271343 = 9407015) B9407015
theorem B1323631 : Blo 822348 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B1389595 : Blo 822348 1389595 := bstep (se 1 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 1389595 = 2084393) B2084393
theorem B7025737 : Blo 822348 7025737 := bstep (se 2 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 7025737 = 5269303) B5269303
theorem B1389737 : Blo 822348 1389737 := bstep (se 2 (by rfl) ⟨521151, by rfl⟩ : syracuseStep 1389737 = 1042303) B1042303
theorem B5289245 : Blo 822348 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B47593493 : Blo 822348 47593493 := bstep (se 6 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 47593493 = 2230945) B2230945
theorem B3127835 : Blo 822348 3127835 := bstep (se 1 (by rfl) ⟨2345876, by rfl⟩ : syracuseStep 3127835 = 4691753) B4691753
theorem B2636383 : Blo 822348 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B1391323 : Blo 822348 1391323 := bstep (se 1 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 1391323 = 2086985) B2086985
theorem B3128489 : Blo 822348 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B3128807 : Blo 822348 3128807 := bstep (se 1 (by rfl) ⟨2346605, by rfl⟩ : syracuseStep 3128807 = 4693211) B4693211
theorem B1851047 : Blo 822348 1851047 := bstep (se 1 (by rfl) ⟨1388285, by rfl⟩ : syracuseStep 1851047 = 2776571) B2776571
theorem B1851119 : Blo 822348 1851119 := bstep (se 1 (by rfl) ⟨1388339, by rfl⟩ : syracuseStep 1851119 = 2776679) B2776679
theorem B1392761 : Blo 822348 1392761 := bstep (se 2 (by rfl) ⟨522285, by rfl⟩ : syracuseStep 1392761 = 1044571) B1044571
theorem B1851515 : Blo 822348 1851515 := bstep (se 1 (by rfl) ⟨1388636, by rfl⟩ : syracuseStep 1851515 = 2777273) B2777273
theorem B1852487 : Blo 822348 1852487 := bstep (se 1 (by rfl) ⟨1389365, by rfl⟩ : syracuseStep 1852487 = 2778731) B2778731
theorem B4703417 : Blo 822348 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B1852775 : Blo 822348 1852775 := bstep (se 1 (by rfl) ⟨1389581, by rfl⟩ : syracuseStep 1852775 = 2779163) B2779163
theorem B14075531 : Blo 822348 14075531 := bstep (se 1 (by rfl) ⟨10556648, by rfl⟩ : syracuseStep 14075531 = 21113297) B21113297
theorem B1853945 : Blo 822348 1853945 := bstep (se 2 (by rfl) ⟨695229, by rfl⟩ : syracuseStep 1853945 = 1390459) B1390459
theorem B20040371 : Blo 822348 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B2083553 : Blo 822348 2083553 := bstep (se 2 (by rfl) ⟨781332, by rfl⟩ : syracuseStep 2083553 = 1562665) B1562665
theorem B20336093 : Blo 822348 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B1855223 : Blo 822348 1855223 := bstep (se 1 (by rfl) ⟨1391417, by rfl⟩ : syracuseStep 1855223 = 2782835) B2782835
theorem B10539017 : Blo 822348 10539017 := bstep (se 2 (by rfl) ⟨3952131, by rfl⟩ : syracuseStep 10539017 = 7904263) B7904263
theorem B4182191 : Blo 822348 4182191 := bstep (se 1 (by rfl) ⟨3136643, by rfl⟩ : syracuseStep 4182191 = 6273287) B6273287
theorem B2347289 : Blo 822348 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B1233719 : Blo 822348 1233719 := bstep (se 1 (by rfl) ⟨925289, by rfl⟩ : syracuseStep 1233719 = 1850579) B1850579
theorem B1856393 : Blo 822348 1856393 := bstep (se 2 (by rfl) ⟨696147, by rfl⟩ : syracuseStep 1856393 = 1392295) B1392295
theorem B939119 : Blo 822348 939119 := bstep (se 1 (by rfl) ⟨704339, by rfl⟩ : syracuseStep 939119 = 1408679) B1408679
theorem B1234247 : Blo 822348 1234247 := bstep (se 1 (by rfl) ⟨925685, by rfl⟩ : syracuseStep 1234247 = 1851371) B1851371
theorem B51533171 : Blo 822348 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B1234487 : Blo 822348 1234487 := bstep (se 1 (by rfl) ⟨925865, by rfl⟩ : syracuseStep 1234487 = 1851731) B1851731
theorem B1234535 : Blo 822348 1234535 := bstep (se 1 (by rfl) ⟨925901, by rfl⟩ : syracuseStep 1234535 = 1851803) B1851803
theorem B3528299 : Blo 822348 3528299 := bstep (se 1 (by rfl) ⟨2646224, by rfl⟩ : syracuseStep 3528299 = 5292449) B5292449
theorem B1234559 : Blo 822348 1234559 := bstep (se 1 (by rfl) ⟨925919, by rfl⟩ : syracuseStep 1234559 = 1851839) B1851839
theorem B1234715 : Blo 822348 1234715 := bstep (se 1 (by rfl) ⟨926036, by rfl⟩ : syracuseStep 1234715 = 1852073) B1852073
theorem B1235051 : Blo 822348 1235051 := bstep (se 1 (by rfl) ⟨926288, by rfl⟩ : syracuseStep 1235051 = 1852577) B1852577
theorem B1235111 : Blo 822348 1235111 := bstep (se 1 (by rfl) ⟨926333, by rfl⟩ : syracuseStep 1235111 = 1852667) B1852667
theorem B2087167 : Blo 822348 2087167 := bstep (se 1 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 2087167 = 3130751) B3130751
theorem B1235369 : Blo 822348 1235369 := bstep (se 2 (by rfl) ⟨463263, by rfl⟩ : syracuseStep 1235369 = 926527) B926527
theorem B10574387 : Blo 822348 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B3529271 : Blo 822348 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B1235567 : Blo 822348 1235567 := bstep (se 1 (by rfl) ⟨926675, by rfl⟩ : syracuseStep 1235567 = 1853351) B1853351
theorem B1563371 : Blo 822348 1563371 := bstep (se 1 (by rfl) ⟨1172528, by rfl⟩ : syracuseStep 1563371 = 2345057) B2345057
theorem B2776031 : Blo 822348 2776031 := bstep (se 1 (by rfl) ⟨2082023, by rfl⟩ : syracuseStep 2776031 = 4164047) B4164047
theorem B1235999 : Blo 822348 1235999 := bstep (se 1 (by rfl) ⟨926999, by rfl⟩ : syracuseStep 1235999 = 1853999) B1853999
theorem B45014201 : Blo 822348 45014201 := bstep (se 2 (by rfl) ⟨16880325, by rfl⟩ : syracuseStep 45014201 = 33760651) B33760651
theorem B1236203 : Blo 822348 1236203 := bstep (se 1 (by rfl) ⟨927152, by rfl⟩ : syracuseStep 1236203 = 1854305) B1854305
theorem B3136751 : Blo 822348 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B21126419 : Blo 822348 21126419 := bstep (se 1 (by rfl) ⟨15844814, by rfl⟩ : syracuseStep 21126419 = 31689629) B31689629
theorem B2776895 : Blo 822348 2776895 := bstep (se 1 (by rfl) ⟨2082671, by rfl⟩ : syracuseStep 2776895 = 4165343) B4165343
theorem B2088787 : Blo 822348 2088787 := bstep (se 1 (by rfl) ⟨1566590, by rfl⟩ : syracuseStep 2088787 = 3133181) B3133181
theorem B1236827 : Blo 822348 1236827 := bstep (se 1 (by rfl) ⟨927620, by rfl⟩ : syracuseStep 1236827 = 1855241) B1855241
theorem B1236863 : Blo 822348 1236863 := bstep (se 1 (by rfl) ⟨927647, by rfl⟩ : syracuseStep 1236863 = 1855295) B1855295
theorem B2088929 : Blo 822348 2088929 := bstep (se 2 (by rfl) ⟨783348, by rfl⟩ : syracuseStep 2088929 = 1566697) B1566697
theorem B1565011 : Blo 822348 1565011 := bstep (se 1 (by rfl) ⟨1173758, by rfl⟩ : syracuseStep 1565011 = 2347517) B2347517
theorem B1237535 : Blo 822348 1237535 := bstep (se 1 (by rfl) ⟨928151, by rfl⟩ : syracuseStep 1237535 = 1856303) B1856303
theorem B1237967 : Blo 822348 1237967 := bstep (se 1 (by rfl) ⟨928475, by rfl⟩ : syracuseStep 1237967 = 1856951) B1856951
theorem B1238687 : Blo 822348 1238687 := bstep (se 1 (by rfl) ⟨929015, by rfl⟩ : syracuseStep 1238687 = 1858031) B1858031
theorem B1238855 : Blo 822348 1238855 := bstep (se 1 (by rfl) ⟨929141, by rfl⟩ : syracuseStep 1238855 = 1858283) B1858283
theorem B1239035 : Blo 822348 1239035 := bstep (se 1 (by rfl) ⟨929276, by rfl⟩ : syracuseStep 1239035 = 1858553) B1858553
theorem B10545167 : Blo 822348 10545167 := bstep (se 1 (by rfl) ⟨7908875, by rfl⟩ : syracuseStep 10545167 = 15817751) B15817751
theorem B1567039 : Blo 822348 1567039 := bstep (se 1 (by rfl) ⟨1175279, by rfl⟩ : syracuseStep 1567039 = 2350559) B2350559
theorem B1042895 : Blo 822348 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B1567487 : Blo 822348 1567487 := bstep (se 1 (by rfl) ⟨1175615, by rfl⟩ : syracuseStep 1567487 = 2351231) B2351231
theorem B2813417 : Blo 822348 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B2780783 : Blo 822348 2780783 := bstep (se 1 (by rfl) ⟨2085587, by rfl⟩ : syracuseStep 2780783 = 4171175) B4171175
theorem B2223983 : Blo 822348 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B2781215 : Blo 822348 2781215 := bstep (se 1 (by rfl) ⟨2085911, by rfl⟩ : syracuseStep 2781215 = 4171823) B4171823
theorem B2781323 : Blo 822348 2781323 := bstep (se 1 (by rfl) ⟨2085992, by rfl⟩ : syracuseStep 2781323 = 4171985) B4171985
theorem B2782511 : Blo 822348 2782511 := bstep (se 1 (by rfl) ⟨2086883, by rfl⟩ : syracuseStep 2782511 = 4173767) B4173767
theorem B21100175 : Blo 822348 21100175 := bstep (se 1 (by rfl) ⟨15825131, by rfl⟩ : syracuseStep 21100175 = 31650263) B31650263
theorem B2226017 : Blo 822348 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B2783915 : Blo 822348 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B2784239 : Blo 822348 2784239 := bstep (se 1 (by rfl) ⟨2088179, by rfl⟩ : syracuseStep 2784239 = 4176359) B4176359
theorem B11304137 : Blo 822348 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B3342007 : Blo 822348 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B10028069 : Blo 822348 10028069 := bstep (se 4 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 10028069 = 1880263) B1880263
theorem B1116031 : Blo 822348 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B2788127 : Blo 822348 2788127 := bstep (se 1 (by rfl) ⟨2091095, by rfl⟩ : syracuseStep 2788127 = 4182191) B4182191
theorem B822479 : Blo 822348 822479 := bstep (se 1 (by rfl) ⟨616859, by rfl⟩ : syracuseStep 822479 = 1233719) B1233719
theorem B822831 : Blo 822348 822831 := bstep (se 1 (by rfl) ⟨617123, by rfl⟩ : syracuseStep 822831 = 1234247) B1234247
theorem B822991 : Blo 822348 822991 := bstep (se 1 (by rfl) ⟨617243, by rfl⟩ : syracuseStep 822991 = 1234487) B1234487
theorem B823023 : Blo 822348 823023 := bstep (se 1 (by rfl) ⟨617267, by rfl⟩ : syracuseStep 823023 = 1234535) B1234535
theorem B823039 : Blo 822348 823039 := bstep (se 1 (by rfl) ⟨617279, by rfl⟩ : syracuseStep 823039 = 1234559) B1234559
theorem B823143 : Blo 822348 823143 := bstep (se 1 (by rfl) ⟨617357, by rfl⟩ : syracuseStep 823143 = 1234715) B1234715
theorem B823367 : Blo 822348 823367 := bstep (se 1 (by rfl) ⟨617525, by rfl⟩ : syracuseStep 823367 = 1235051) B1235051
theorem B823407 : Blo 822348 823407 := bstep (se 1 (by rfl) ⟨617555, by rfl⟩ : syracuseStep 823407 = 1235111) B1235111
theorem B823579 : Blo 822348 823579 := bstep (se 1 (by rfl) ⟨617684, by rfl⟩ : syracuseStep 823579 = 1235369) B1235369
theorem B7049591 : Blo 822348 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B823711 : Blo 822348 823711 := bstep (se 1 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 823711 = 1235567) B1235567
theorem B823999 : Blo 822348 823999 := bstep (se 1 (by rfl) ⟨617999, by rfl⟩ : syracuseStep 823999 = 1235999) B1235999
theorem B824135 : Blo 822348 824135 := bstep (se 1 (by rfl) ⟨618101, by rfl⟩ : syracuseStep 824135 = 1236203) B1236203
theorem B824551 : Blo 822348 824551 := bstep (se 1 (by rfl) ⟨618413, by rfl⟩ : syracuseStep 824551 = 1236827) B1236827
theorem B824575 : Blo 822348 824575 := bstep (se 1 (by rfl) ⟨618431, by rfl⟩ : syracuseStep 824575 = 1236863) B1236863
theorem B825023 : Blo 822348 825023 := bstep (se 1 (by rfl) ⟨618767, by rfl⟩ : syracuseStep 825023 = 1237535) B1237535
theorem B21370817 : Blo 822348 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B825311 : Blo 822348 825311 := bstep (se 1 (by rfl) ⟨618983, by rfl⟩ : syracuseStep 825311 = 1237967) B1237967
theorem B4462775 : Blo 822348 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B825791 : Blo 822348 825791 := bstep (se 1 (by rfl) ⟨619343, by rfl⟩ : syracuseStep 825791 = 1238687) B1238687
theorem B825903 : Blo 822348 825903 := bstep (se 1 (by rfl) ⟨619427, by rfl⟩ : syracuseStep 825903 = 1238855) B1238855
theorem B826023 : Blo 822348 826023 := bstep (se 1 (by rfl) ⟨619517, by rfl⟩ : syracuseStep 826023 = 1239035) B1239035
theorem B9411389 : Blo 822348 9411389 := bstep (se 3 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 9411389 = 3529271) B3529271
theorem B20061593 : Blo 822348 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B1875611 : Blo 822348 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B926491 : Blo 822348 926491 := bstep (se 1 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 926491 = 1389737) B1389737
theorem B3515177 : Blo 822348 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B14066783 : Blo 822348 14066783 := bstep (se 1 (by rfl) ⟨10550087, by rfl⟩ : syracuseStep 14066783 = 21100175) B21100175
theorem B1484011 : Blo 822348 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B31728995 : Blo 822348 31728995 := bstep (se 1 (by rfl) ⟨23796746, by rfl⟩ : syracuseStep 31728995 = 47593493) B47593493
theorem B128722445 : Blo 822348 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B928507 : Blo 822348 928507 := bstep (se 1 (by rfl) ⟨696380, by rfl⟩ : syracuseStep 928507 = 1392761) B1392761
theorem B9383687 : Blo 822348 9383687 := bstep (se 1 (by rfl) ⟨7037765, by rfl⟩ : syracuseStep 9383687 = 14075531) B14075531
theorem B1389035 : Blo 822348 1389035 := bstep (se 1 (by rfl) ⟨1041776, by rfl⟩ : syracuseStep 1389035 = 2083553) B2083553
theorem B7026011 : Blo 822348 7026011 := bstep (se 1 (by rfl) ⟨5269508, by rfl⟩ : syracuseStep 7026011 = 10539017) B10539017
theorem B4175387 : Blo 822348 4175387 := bstep (se 1 (by rfl) ⟨3131540, by rfl⟩ : syracuseStep 4175387 = 6263081) B6263081
theorem B2504317 : Blo 822348 2504317 := bstep (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) B939119
theorem B34355447 : Blo 822348 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B6339667 : Blo 822348 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B1850687 : Blo 822348 1850687 := bstep (se 1 (by rfl) ⟨1388015, by rfl⟩ : syracuseStep 1850687 = 2776031) B2776031
theorem B17842025 : Blo 822348 17842025 := bstep (se 2 (by rfl) ⟨6690759, by rfl⟩ : syracuseStep 17842025 = 13381519) B13381519
theorem B1851263 : Blo 822348 1851263 := bstep (se 1 (by rfl) ⟨1388447, by rfl⟩ : syracuseStep 1851263 = 2776895) B2776895
theorem B1392619 : Blo 822348 1392619 := bstep (se 1 (by rfl) ⟨1044464, by rfl⟩ : syracuseStep 1392619 = 2088929) B2088929
theorem B3522847 : Blo 822348 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B1851785 : Blo 822348 1851785 := bstep (se 2 (by rfl) ⟨694419, by rfl⟩ : syracuseStep 1851785 = 1388839) B1388839
theorem B7030111 : Blo 822348 7030111 := bstep (se 1 (by rfl) ⟨5272583, by rfl⟩ : syracuseStep 7030111 = 10545167) B10545167
theorem B1852793 : Blo 822348 1852793 := bstep (se 2 (by rfl) ⟨694797, by rfl⟩ : syracuseStep 1852793 = 1389595) B1389595
theorem B837359 : Blo 822348 837359 := bstep (se 1 (by rfl) ⟨628019, by rfl⟩ : syracuseStep 837359 = 1256039) B1256039
theorem B1853855 : Blo 822348 1853855 := bstep (se 1 (by rfl) ⟨1390391, by rfl⟩ : syracuseStep 1853855 = 2780783) B2780783
theorem B1854143 : Blo 822348 1854143 := bstep (se 1 (by rfl) ⟨1390607, by rfl⟩ : syracuseStep 1854143 = 2781215) B2781215
theorem B1854215 : Blo 822348 1854215 := bstep (se 1 (by rfl) ⟨1390661, by rfl⟩ : syracuseStep 1854215 = 2781323) B2781323
theorem B4180895 : Blo 822348 4180895 := bstep (se 1 (by rfl) ⟨3135671, by rfl⟩ : syracuseStep 4180895 = 6271343) B6271343
theorem B3525565 : Blo 822348 3525565 := bstep (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) B1322087
theorem B3526163 : Blo 822348 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B1855007 : Blo 822348 1855007 := bstep (se 1 (by rfl) ⟨1391255, by rfl⟩ : syracuseStep 1855007 = 2782511) B2782511
theorem B5951009 : Blo 822348 5951009 := bstep (se 2 (by rfl) ⟨2231628, by rfl⟩ : syracuseStep 5951009 = 4463257) B4463257
theorem B1855097 : Blo 822348 1855097 := bstep (se 2 (by rfl) ⟨695661, by rfl⟩ : syracuseStep 1855097 = 1391323) B1391323
theorem B2085223 : Blo 822348 2085223 := bstep (se 1 (by rfl) ⟨1563917, by rfl⟩ : syracuseStep 2085223 = 3127835) B3127835
theorem B1855943 : Blo 822348 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B1856159 : Blo 822348 1856159 := bstep (se 1 (by rfl) ⟨1392119, by rfl⟩ : syracuseStep 1856159 = 2784239) B2784239
theorem B1233641 : Blo 822348 1233641 := bstep (se 2 (by rfl) ⟨462615, by rfl⟩ : syracuseStep 1233641 = 925231) B925231
theorem B2085659 : Blo 822348 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B1233785 : Blo 822348 1233785 := bstep (se 2 (by rfl) ⟨462669, by rfl⟩ : syracuseStep 1233785 = 925339) B925339
theorem B1233833 : Blo 822348 1233833 := bstep (se 2 (by rfl) ⟨462687, by rfl⟩ : syracuseStep 1233833 = 925375) B925375
theorem B2085871 : Blo 822348 2085871 := bstep (se 1 (by rfl) ⟨1564403, by rfl⟩ : syracuseStep 2085871 = 3128807) B3128807
theorem B1234031 : Blo 822348 1234031 := bstep (se 1 (by rfl) ⟨925523, by rfl⟩ : syracuseStep 1234031 = 1851047) B1851047
theorem B1234079 : Blo 822348 1234079 := bstep (se 1 (by rfl) ⟨925559, by rfl⟩ : syracuseStep 1234079 = 1851119) B1851119
theorem B1234343 : Blo 822348 1234343 := bstep (se 1 (by rfl) ⟨925757, by rfl⟩ : syracuseStep 1234343 = 1851515) B1851515
theorem B2086681 : Blo 822348 2086681 := bstep (se 2 (by rfl) ⟨782505, by rfl⟩ : syracuseStep 2086681 = 1565011) B1565011
theorem B1234991 : Blo 822348 1234991 := bstep (se 1 (by rfl) ⟨926243, by rfl⟩ : syracuseStep 1234991 = 1852487) B1852487
theorem B3135611 : Blo 822348 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B1857743 : Blo 822348 1857743 := bstep (se 1 (by rfl) ⟨1393307, by rfl⟩ : syracuseStep 1857743 = 2786615) B2786615
theorem B1235183 : Blo 822348 1235183 := bstep (se 1 (by rfl) ⟨926387, by rfl⟩ : syracuseStep 1235183 = 1852775) B1852775
theorem B2775815 : Blo 822348 2775815 := bstep (se 1 (by rfl) ⟨2081861, by rfl⟩ : syracuseStep 2775815 = 4163723) B4163723
theorem B1235963 : Blo 822348 1235963 := bstep (se 1 (by rfl) ⟨926972, by rfl⟩ : syracuseStep 1235963 = 1853945) B1853945
theorem B1858643 : Blo 822348 1858643 := bstep (se 1 (by rfl) ⟨1393982, by rfl⟩ : syracuseStep 1858643 = 2787965) B2787965
theorem B3955823 : Blo 822348 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B13360247 : Blo 822348 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B1858715 : Blo 822348 1858715 := bstep (se 1 (by rfl) ⟨1394036, by rfl⟩ : syracuseStep 1858715 = 2788073) B2788073
theorem B13557395 : Blo 822348 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B1236815 : Blo 822348 1236815 := bstep (se 1 (by rfl) ⟨927611, by rfl⟩ : syracuseStep 1236815 = 1855223) B1855223
theorem B1564859 : Blo 822348 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B2089385 : Blo 822348 2089385 := bstep (se 2 (by rfl) ⟨783519, by rfl⟩ : syracuseStep 2089385 = 1567039) B1567039
theorem B1237595 : Blo 822348 1237595 := bstep (se 1 (by rfl) ⟨928196, by rfl⟩ : syracuseStep 1237595 = 1856393) B1856393
theorem B26763959 : Blo 822348 26763959 := bstep (se 1 (by rfl) ⟨20072969, by rfl⟩ : syracuseStep 26763959 = 40145939) B40145939
theorem B2352199 : Blo 822348 2352199 := bstep (se 1 (by rfl) ⟨1764149, by rfl⟩ : syracuseStep 2352199 = 3528299) B3528299
theorem B24045245 : Blo 822348 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B1042247 : Blo 822348 1042247 := bstep (se 1 (by rfl) ⟨781685, by rfl⟩ : syracuseStep 1042247 = 1563371) B1563371
theorem B30009467 : Blo 822348 30009467 := bstep (se 1 (by rfl) ⟨22507100, by rfl⟩ : syracuseStep 30009467 = 45014201) B45014201
theorem B2091167 : Blo 822348 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B14084279 : Blo 822348 14084279 := bstep (se 1 (by rfl) ⟨10563209, by rfl⟩ : syracuseStep 14084279 = 21126419) B21126419
theorem B10578383 : Blo 822348 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B1764841 : Blo 822348 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B2781053 : Blo 822348 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B9367649 : Blo 822348 9367649 := bstep (se 2 (by rfl) ⟨3512868, by rfl⟩ : syracuseStep 9367649 = 7025737) B7025737
theorem B1044991 : Blo 822348 1044991 := bstep (se 1 (by rfl) ⟨783743, by rfl⟩ : syracuseStep 1044991 = 1567487) B1567487
theorem B2782187 : Blo 822348 2782187 := bstep (se 1 (by rfl) ⟨2086640, by rfl⟩ : syracuseStep 2782187 = 4173281) B4173281
theorem B2782889 : Blo 822348 2782889 := bstep (se 2 (by rfl) ⟨1043583, by rfl⟩ : syracuseStep 2782889 = 2087167) B2087167
theorem B7536091 : Blo 822348 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B4456009 : Blo 822348 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B5930621 : Blo 822348 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B2785049 : Blo 822348 2785049 := bstep (se 2 (by rfl) ⟨1044393, by rfl⟩ : syracuseStep 2785049 = 2088787) B2088787
theorem B6685379 : Blo 822348 6685379 := bstep (se 1 (by rfl) ⟨5014034, by rfl⟩ : syracuseStep 6685379 = 10028069) B10028069
theorem B9373481 : Blo 822348 9373481 := bstep (se 2 (by rfl) ⟨3515055, by rfl⟩ : syracuseStep 9373481 = 7030111) B7030111
theorem B2787263 : Blo 822348 2787263 := bstep (se 1 (by rfl) ⟨2090447, by rfl⟩ : syracuseStep 2787263 = 4180895) B4180895
theorem B3967339 : Blo 822348 3967339 := bstep (se 1 (by rfl) ⟨2975504, by rfl⟩ : syracuseStep 3967339 = 5951009) B5951009
theorem B822427 : Blo 822348 822427 := bstep (se 1 (by rfl) ⟨616820, by rfl⟩ : syracuseStep 822427 = 1233641) B1233641
theorem B822523 : Blo 822348 822523 := bstep (se 1 (by rfl) ⟨616892, by rfl⟩ : syracuseStep 822523 = 1233785) B1233785
theorem B822555 : Blo 822348 822555 := bstep (se 1 (by rfl) ⟨616916, by rfl⟩ : syracuseStep 822555 = 1233833) B1233833
theorem B822687 : Blo 822348 822687 := bstep (se 1 (by rfl) ⟨617015, by rfl⟩ : syracuseStep 822687 = 1234031) B1234031
theorem B822719 : Blo 822348 822719 := bstep (se 1 (by rfl) ⟨617039, by rfl⟩ : syracuseStep 822719 = 1234079) B1234079
theorem B822895 : Blo 822348 822895 := bstep (se 1 (by rfl) ⟨617171, by rfl⟩ : syracuseStep 822895 = 1234343) B1234343
theorem B823327 : Blo 822348 823327 := bstep (se 1 (by rfl) ⟨617495, by rfl⟩ : syracuseStep 823327 = 1234991) B1234991
theorem B823455 : Blo 822348 823455 := bstep (se 1 (by rfl) ⟨617591, by rfl⟩ : syracuseStep 823455 = 1235183) B1235183
theorem B823975 : Blo 822348 823975 := bstep (se 1 (by rfl) ⟨617981, by rfl⟩ : syracuseStep 823975 = 1235963) B1235963
theorem B13374395 : Blo 822348 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B1250407 : Blo 822348 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B56988845 : Blo 822348 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B824543 : Blo 822348 824543 := bstep (se 1 (by rfl) ⟨618407, by rfl⟩ : syracuseStep 824543 = 1236815) B1236815
theorem B825063 : Blo 822348 825063 := bstep (se 1 (by rfl) ⟨618797, by rfl⟩ : syracuseStep 825063 = 1237595) B1237595
theorem B9377855 : Blo 822348 9377855 := bstep (se 1 (by rfl) ⟨7033391, by rfl⟩ : syracuseStep 9377855 = 14066783) B14066783
theorem B16030163 : Blo 822348 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B7052255 : Blo 822348 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B926023 : Blo 822348 926023 := bstep (se 1 (by rfl) ⟨694517, by rfl⟩ : syracuseStep 926023 = 1389035) B1389035
theorem B5941345 : Blo 822348 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B4697129 : Blo 822348 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B4172957 : Blo 822348 4172957 := bstep (se 3 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 4172957 = 1564859) B1564859
theorem B1978681 : Blo 822348 1978681 := bstep (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) B1484011
theorem B1488041 : Blo 822348 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B4699727 : Blo 822348 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B1390439 : Blo 822348 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B4700753 : Blo 822348 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B1850543 : Blo 822348 1850543 := bstep (se 1 (by rfl) ⟨1387907, by rfl⟩ : syracuseStep 1850543 = 2775815) B2775815
theorem B6274259 : Blo 822348 6274259 := bstep (se 1 (by rfl) ⟨4705694, by rfl⟩ : syracuseStep 6274259 = 9411389) B9411389
theorem B2637215 : Blo 822348 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B1392923 : Blo 822348 1392923 := bstep (se 1 (by rfl) ⟨1044692, by rfl⟩ : syracuseStep 1392923 = 2089385) B2089385
theorem B17842639 : Blo 822348 17842639 := bstep (se 1 (by rfl) ⟨13381979, by rfl⟩ : syracuseStep 17842639 = 26763959) B26763959
theorem B2343451 : Blo 822348 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B1393321 : Blo 822348 1393321 := bstep (se 2 (by rfl) ⟨522495, by rfl⟩ : syracuseStep 1393321 = 1044991) B1044991
theorem B21152663 : Blo 822348 21152663 := bstep (se 1 (by rfl) ⟨15864497, by rfl⟩ : syracuseStep 21152663 = 31728995) B31728995
theorem B20006311 : Blo 822348 20006311 := bstep (se 1 (by rfl) ⟨15004733, by rfl⟩ : syracuseStep 20006311 = 30009467) B30009467
theorem B1394111 : Blo 822348 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B9389519 : Blo 822348 9389519 := bstep (se 1 (by rfl) ⟨7042139, by rfl⟩ : syracuseStep 9389519 = 14084279) B14084279
theorem B8931829 : Blo 822348 8931829 := bstep (se 5 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 8931829 = 837359) B837359
theorem B1854035 : Blo 822348 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B6245099 : Blo 822348 6245099 := bstep (se 1 (by rfl) ⟨4683824, by rfl⟩ : syracuseStep 6245099 = 9367649) B9367649
theorem B1854791 : Blo 822348 1854791 := bstep (se 1 (by rfl) ⟨1391093, by rfl⟩ : syracuseStep 1854791 = 2782187) B2782187
theorem B1855259 : Blo 822348 1855259 := bstep (se 1 (by rfl) ⟨1391444, by rfl⟩ : syracuseStep 1855259 = 2782889) B2782889
theorem B10048121 : Blo 822348 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B1233791 : Blo 822348 1233791 := bstep (se 1 (by rfl) ⟨925343, by rfl⟩ : syracuseStep 1233791 = 1850687) B1850687
theorem B3953747 : Blo 822348 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B1856699 : Blo 822348 1856699 := bstep (se 1 (by rfl) ⟨1392524, by rfl⟩ : syracuseStep 1856699 = 2785049) B2785049
theorem B1234175 : Blo 822348 1234175 := bstep (se 1 (by rfl) ⟨925631, by rfl⟩ : syracuseStep 1234175 = 1851263) B1851263
theorem B1856825 : Blo 822348 1856825 := bstep (se 2 (by rfl) ⟨696309, by rfl⟩ : syracuseStep 1856825 = 1392619) B1392619
theorem B1234523 : Blo 822348 1234523 := bstep (se 1 (by rfl) ⟨925892, by rfl⟩ : syracuseStep 1234523 = 1851785) B1851785
theorem B1235195 : Blo 822348 1235195 := bstep (se 1 (by rfl) ⟨926396, by rfl⟩ : syracuseStep 1235195 = 1852793) B1852793
theorem B1235321 : Blo 822348 1235321 := bstep (se 2 (by rfl) ⟨463245, by rfl⟩ : syracuseStep 1235321 = 926491) B926491
theorem B3136265 : Blo 822348 3136265 := bstep (se 2 (by rfl) ⟨1176099, by rfl⟩ : syracuseStep 3136265 = 2352199) B2352199
theorem B1235903 : Blo 822348 1235903 := bstep (se 1 (by rfl) ⟨926927, by rfl⟩ : syracuseStep 1235903 = 1853855) B1853855
theorem B1236095 : Blo 822348 1236095 := bstep (se 1 (by rfl) ⟨927071, by rfl⟩ : syracuseStep 1236095 = 1854143) B1854143
theorem B1236143 : Blo 822348 1236143 := bstep (se 1 (by rfl) ⟨927107, by rfl⟩ : syracuseStep 1236143 = 1854215) B1854215
theorem B1858751 : Blo 822348 1858751 := bstep (se 1 (by rfl) ⟨1394063, by rfl⟩ : syracuseStep 1858751 = 2788127) B2788127
theorem B2350775 : Blo 822348 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B1236671 : Blo 822348 1236671 := bstep (se 1 (by rfl) ⟨927503, by rfl⟩ : syracuseStep 1236671 = 1855007) B1855007
theorem B1236731 : Blo 822348 1236731 := bstep (se 1 (by rfl) ⟨927548, by rfl⟩ : syracuseStep 1236731 = 1855097) B1855097
theorem B1237295 : Blo 822348 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B1237439 : Blo 822348 1237439 := bstep (se 1 (by rfl) ⟨928079, by rfl⟩ : syracuseStep 1237439 = 1856159) B1856159
theorem B1238009 : Blo 822348 1238009 := bstep (se 2 (by rfl) ⟨464253, by rfl⟩ : syracuseStep 1238009 = 928507) B928507
theorem B2090407 : Blo 822348 2090407 := bstep (se 1 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 2090407 = 3135611) B3135611
theorem B2975183 : Blo 822348 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B1238495 : Blo 822348 1238495 := bstep (se 1 (by rfl) ⟨928871, by rfl⟩ : syracuseStep 1238495 = 1857743) B1857743
theorem B2353121 : Blo 822348 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B1239095 : Blo 822348 1239095 := bstep (se 1 (by rfl) ⟨929321, by rfl⟩ : syracuseStep 1239095 = 1858643) B1858643
theorem B8906831 : Blo 822348 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B1239143 : Blo 822348 1239143 := bstep (se 1 (by rfl) ⟨929357, by rfl⟩ : syracuseStep 1239143 = 1858715) B1858715
theorem B2779325 : Blo 822348 2779325 := bstep (se 3 (by rfl) ⟨521123, by rfl⟩ : syracuseStep 2779325 = 1042247) B1042247
theorem B9038263 : Blo 822348 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B2780297 : Blo 822348 2780297 := bstep (se 2 (by rfl) ⟨1042611, by rfl⟩ : syracuseStep 2780297 = 2085223) B2085223
theorem B85814963 : Blo 822348 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B2781161 : Blo 822348 2781161 := bstep (se 2 (by rfl) ⟨1042935, by rfl⟩ : syracuseStep 2781161 = 2085871) B2085871
theorem B3339089 : Blo 822348 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B2782241 : Blo 822348 2782241 := bstep (se 2 (by rfl) ⟨1043340, by rfl⟩ : syracuseStep 2782241 = 2086681) B2086681
theorem B6255791 : Blo 822348 6255791 := bstep (se 1 (by rfl) ⟨4691843, by rfl⟩ : syracuseStep 6255791 = 9383687) B9383687
theorem B4684007 : Blo 822348 4684007 := bstep (se 1 (by rfl) ⟨3513005, by rfl⟩ : syracuseStep 4684007 = 7026011) B7026011
theorem B2783591 : Blo 822348 2783591 := bstep (se 1 (by rfl) ⟨2087693, by rfl⟩ : syracuseStep 2783591 = 4175387) B4175387
theorem B8452889 : Blo 822348 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B22903631 : Blo 822348 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B11894683 : Blo 822348 11894683 := bstep (se 1 (by rfl) ⟨8921012, by rfl⟩ : syracuseStep 11894683 = 17842025) B17842025
theorem B4456919 : Blo 822348 4456919 := bstep (se 1 (by rfl) ⟨3342689, by rfl⟩ : syracuseStep 4456919 = 6685379) B6685379
theorem B23790185 : Blo 822348 23790185 := bstep (se 2 (by rfl) ⟨8921319, by rfl⟩ : syracuseStep 23790185 = 17842639) B17842639
theorem B6259679 : Blo 822348 6259679 := bstep (se 1 (by rfl) ⟨4694759, by rfl⟩ : syracuseStep 6259679 = 9389519) B9389519
theorem B4163399 : Blo 822348 4163399 := bstep (se 1 (by rfl) ⟨3122549, by rfl⟩ : syracuseStep 4163399 = 6245099) B6245099
theorem B26675081 : Blo 822348 26675081 := bstep (se 2 (by rfl) ⟨10003155, by rfl⟩ : syracuseStep 26675081 = 20006311) B20006311
theorem B2787209 : Blo 822348 2787209 := bstep (se 2 (by rfl) ⟨1045203, by rfl⟩ : syracuseStep 2787209 = 2090407) B2090407
theorem B822527 : Blo 822348 822527 := bstep (se 1 (by rfl) ⟨616895, by rfl⟩ : syracuseStep 822527 = 1233791) B1233791
theorem B8916263 : Blo 822348 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B822783 : Blo 822348 822783 := bstep (se 1 (by rfl) ⟨617087, by rfl⟩ : syracuseStep 822783 = 1234175) B1234175
theorem B823015 : Blo 822348 823015 := bstep (se 1 (by rfl) ⟨617261, by rfl⟩ : syracuseStep 823015 = 1234523) B1234523
theorem B823463 : Blo 822348 823463 := bstep (se 1 (by rfl) ⟨617597, by rfl⟩ : syracuseStep 823463 = 1235195) B1235195
theorem B823547 : Blo 822348 823547 := bstep (se 1 (by rfl) ⟨617660, by rfl⟩ : syracuseStep 823547 = 1235321) B1235321
theorem B823935 : Blo 822348 823935 := bstep (se 1 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 823935 = 1235903) B1235903
theorem B824063 : Blo 822348 824063 := bstep (se 1 (by rfl) ⟨618047, by rfl⟩ : syracuseStep 824063 = 1236095) B1236095
theorem B824095 : Blo 822348 824095 := bstep (se 1 (by rfl) ⟨618071, by rfl⟩ : syracuseStep 824095 = 1236143) B1236143
theorem B824447 : Blo 822348 824447 := bstep (se 1 (by rfl) ⟨618335, by rfl⟩ : syracuseStep 824447 = 1236671) B1236671
theorem B824487 : Blo 822348 824487 := bstep (se 1 (by rfl) ⟨618365, by rfl⟩ : syracuseStep 824487 = 1236731) B1236731
theorem B824863 : Blo 822348 824863 := bstep (se 1 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 824863 = 1237295) B1237295
theorem B824959 : Blo 822348 824959 := bstep (se 1 (by rfl) ⟨618719, by rfl⟩ : syracuseStep 824959 = 1237439) B1237439
theorem B825339 : Blo 822348 825339 := bstep (se 1 (by rfl) ⟨619004, by rfl⟩ : syracuseStep 825339 = 1238009) B1238009
theorem B825663 : Blo 822348 825663 := bstep (se 1 (by rfl) ⟨619247, by rfl⟩ : syracuseStep 825663 = 1238495) B1238495
theorem B826063 : Blo 822348 826063 := bstep (se 1 (by rfl) ⟨619547, by rfl⟩ : syracuseStep 826063 = 1239095) B1239095
theorem B5937887 : Blo 822348 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B826095 : Blo 822348 826095 := bstep (se 1 (by rfl) ⟨619571, by rfl⟩ : syracuseStep 826095 = 1239143) B1239143
theorem B992027 : Blo 822348 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B4170527 : Blo 822348 4170527 := bstep (se 1 (by rfl) ⟨3127895, by rfl⟩ : syracuseStep 4170527 = 6255791) B6255791
theorem B926959 : Blo 822348 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B3122671 : Blo 822348 3122671 := bstep (se 1 (by rfl) ⟨2342003, by rfl⟩ : syracuseStep 3122671 = 4684007) B4684007
theorem B928615 : Blo 822348 928615 := bstep (se 1 (by rfl) ⟨696461, by rfl⟩ : syracuseStep 928615 = 1392923) B1392923
theorem B14101775 : Blo 822348 14101775 := bstep (se 1 (by rfl) ⟨10576331, by rfl⟩ : syracuseStep 14101775 = 21152663) B21152663
theorem B3124601 : Blo 822348 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B929407 : Blo 822348 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B6698747 : Blo 822348 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B5289785 : Blo 822348 5289785 := bstep (se 2 (by rfl) ⟨1983669, by rfl⟩ : syracuseStep 5289785 = 3967339) B3967339
theorem B11909105 : Blo 822348 11909105 := bstep (se 2 (by rfl) ⟨4465914, by rfl⟩ : syracuseStep 11909105 = 8931829) B8931829
theorem B2635831 : Blo 822348 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B37992563 : Blo 822348 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B4701503 : Blo 822348 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B2638241 : Blo 822348 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B6668837 : Blo 822348 6668837 := bstep (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) B1250407
theorem B1983455 : Blo 822348 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B42747101 : Blo 822348 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B1852883 : Blo 822348 1852883 := bstep (se 1 (by rfl) ⟨1389662, by rfl⟩ : syracuseStep 1852883 = 2779325) B2779325
theorem B3131419 : Blo 822348 3131419 := bstep (se 1 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 3131419 = 4697129) B4697129
theorem B1853531 : Blo 822348 1853531 := bstep (se 1 (by rfl) ⟨1390148, by rfl⟩ : syracuseStep 1853531 = 2780297) B2780297
theorem B1854107 : Blo 822348 1854107 := bstep (se 1 (by rfl) ⟨1390580, by rfl⟩ : syracuseStep 1854107 = 2781161) B2781161
theorem B1854827 : Blo 822348 1854827 := bstep (se 1 (by rfl) ⟨1391120, by rfl⟩ : syracuseStep 1854827 = 2782241) B2782241
theorem B3133151 : Blo 822348 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B1855727 : Blo 822348 1855727 := bstep (se 1 (by rfl) ⟨1391795, by rfl⟩ : syracuseStep 1855727 = 2783591) B2783591
theorem B3133835 : Blo 822348 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B1233695 : Blo 822348 1233695 := bstep (se 1 (by rfl) ⟨925271, by rfl⟩ : syracuseStep 1233695 = 1850543) B1850543
theorem B4182839 : Blo 822348 4182839 := bstep (se 1 (by rfl) ⟨3137129, by rfl⟩ : syracuseStep 4182839 = 6274259) B6274259
theorem B1758143 : Blo 822348 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B1234697 : Blo 822348 1234697 := bstep (se 2 (by rfl) ⟨463011, by rfl⟩ : syracuseStep 1234697 = 926023) B926023
theorem B1857761 : Blo 822348 1857761 := bstep (se 2 (by rfl) ⟨696660, by rfl⟩ : syracuseStep 1857761 = 1393321) B1393321
theorem B6248987 : Blo 822348 6248987 := bstep (se 1 (by rfl) ⟨4686740, by rfl⟩ : syracuseStep 6248987 = 9373481) B9373481
theorem B1858175 : Blo 822348 1858175 := bstep (se 1 (by rfl) ⟨1393631, by rfl⟩ : syracuseStep 1858175 = 2787263) B2787263
theorem B1236023 : Blo 822348 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B1236527 : Blo 822348 1236527 := bstep (se 1 (by rfl) ⟨927395, by rfl⟩ : syracuseStep 1236527 = 1854791) B1854791
theorem B1236839 : Blo 822348 1236839 := bstep (se 1 (by rfl) ⟨927629, by rfl⟩ : syracuseStep 1236839 = 1855259) B1855259
theorem B7921793 : Blo 822348 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B12051017 : Blo 822348 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B1237799 : Blo 822348 1237799 := bstep (se 1 (by rfl) ⟨928349, by rfl⟩ : syracuseStep 1237799 = 1856699) B1856699
theorem B1237883 : Blo 822348 1237883 := bstep (se 1 (by rfl) ⟨928412, by rfl⟩ : syracuseStep 1237883 = 1856825) B1856825
theorem B6251903 : Blo 822348 6251903 := bstep (se 1 (by rfl) ⟨4688927, by rfl⟩ : syracuseStep 6251903 = 9377855) B9377855
theorem B2090843 : Blo 822348 2090843 := bstep (se 1 (by rfl) ⟨1568132, by rfl⟩ : syracuseStep 2090843 = 3136265) B3136265
theorem B1239167 : Blo 822348 1239167 := bstep (se 1 (by rfl) ⟨929375, by rfl⟩ : syracuseStep 1239167 = 1858751) B1858751
theorem B1567183 : Blo 822348 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B1568747 : Blo 822348 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B2781971 : Blo 822348 2781971 := bstep (se 1 (by rfl) ⟨2086478, by rfl⟩ : syracuseStep 2781971 = 4172957) B4172957
theorem B57209975 : Blo 822348 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B2226059 : Blo 822348 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B5635259 : Blo 822348 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B15269087 : Blo 822348 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B15859577 : Blo 822348 15859577 := bstep (se 2 (by rfl) ⟨5947341, by rfl⟩ : syracuseStep 15859577 = 11894683) B11894683
theorem B15860123 : Blo 822348 15860123 := bstep (se 1 (by rfl) ⟨11895092, by rfl⟩ : syracuseStep 15860123 = 23790185) B23790185
theorem B4163561 : Blo 822348 4163561 := bstep (se 2 (by rfl) ⟨1561335, by rfl⟩ : syracuseStep 4163561 = 3122671) B3122671
theorem B4688381 : Blo 822348 4688381 := bstep (se 3 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 4688381 = 1758143) B1758143
theorem B822463 : Blo 822348 822463 := bstep (se 1 (by rfl) ⟨616847, by rfl⟩ : syracuseStep 822463 = 1233695) B1233695
theorem B2788559 : Blo 822348 2788559 := bstep (se 1 (by rfl) ⟨2091419, by rfl⟩ : syracuseStep 2788559 = 4182839) B4182839
theorem B823131 : Blo 822348 823131 := bstep (se 1 (by rfl) ⟨617348, by rfl⟩ : syracuseStep 823131 = 1234697) B1234697
theorem B4165991 : Blo 822348 4165991 := bstep (se 1 (by rfl) ⟨3124493, by rfl⟩ : syracuseStep 4165991 = 6248987) B6248987
theorem B17863325 : Blo 822348 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B824015 : Blo 822348 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B824351 : Blo 822348 824351 := bstep (se 1 (by rfl) ⟨618263, by rfl⟩ : syracuseStep 824351 = 1236527) B1236527
theorem B824559 : Blo 822348 824559 := bstep (se 1 (by rfl) ⟨618419, by rfl⟩ : syracuseStep 824559 = 1236839) B1236839
theorem B5281195 : Blo 822348 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B8034011 : Blo 822348 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B825199 : Blo 822348 825199 := bstep (se 1 (by rfl) ⟨618899, by rfl⟩ : syracuseStep 825199 = 1237799) B1237799
theorem B825255 : Blo 822348 825255 := bstep (se 1 (by rfl) ⟨618941, by rfl⟩ : syracuseStep 825255 = 1237883) B1237883
theorem B4167935 : Blo 822348 4167935 := bstep (se 1 (by rfl) ⟨3125951, by rfl⟩ : syracuseStep 4167935 = 6251903) B6251903
theorem B826111 : Blo 822348 826111 := bstep (se 1 (by rfl) ⟨619583, by rfl⟩ : syracuseStep 826111 = 1239167) B1239167
theorem B3514441 : Blo 822348 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B1484039 : Blo 822348 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B7939403 : Blo 822348 7939403 := bstep (se 1 (by rfl) ⟨5954552, by rfl⟩ : syracuseStep 7939403 = 11909105) B11909105
theorem B1322303 : Blo 822348 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B4173119 : Blo 822348 4173119 := bstep (se 1 (by rfl) ⟨3129839, by rfl⟩ : syracuseStep 4173119 = 6259679) B6259679
theorem B5944175 : Blo 822348 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B4175225 : Blo 822348 4175225 := bstep (se 2 (by rfl) ⟨1565709, by rfl⟩ : syracuseStep 4175225 = 3131419) B3131419
theorem B1393895 : Blo 822348 1393895 := bstep (se 1 (by rfl) ⟨1045421, by rfl⟩ : syracuseStep 1393895 = 2090843) B2090843
theorem B2083067 : Blo 822348 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B1854647 : Blo 822348 1854647 := bstep (se 1 (by rfl) ⟨1390985, by rfl⟩ : syracuseStep 1854647 = 2781971) B2781971
theorem B40717565 : Blo 822348 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B3526523 : Blo 822348 3526523 := bstep (se 1 (by rfl) ⟨2644892, by rfl⟩ : syracuseStep 3526523 = 5289785) B5289785
theorem B3756839 : Blo 822348 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B3134335 : Blo 822348 3134335 := bstep (se 1 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 3134335 = 4701503) B4701503
theorem B10573051 : Blo 822348 10573051 := bstep (se 1 (by rfl) ⟨7929788, by rfl⟩ : syracuseStep 10573051 = 15859577) B15859577
theorem B4183325 : Blo 822348 4183325 := bstep (se 3 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 4183325 = 1568747) B1568747
theorem B1758827 : Blo 822348 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B2971279 : Blo 822348 2971279 := bstep (se 1 (by rfl) ⟨2228459, by rfl⟩ : syracuseStep 2971279 = 4456919) B4456919
theorem B4445891 : Blo 822348 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B28498067 : Blo 822348 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B1235255 : Blo 822348 1235255 := bstep (se 1 (by rfl) ⟨926441, by rfl⟩ : syracuseStep 1235255 = 1852883) B1852883
theorem B2775599 : Blo 822348 2775599 := bstep (se 1 (by rfl) ⟨2081699, by rfl⟩ : syracuseStep 2775599 = 4163399) B4163399
theorem B17783387 : Blo 822348 17783387 := bstep (se 1 (by rfl) ⟨13337540, by rfl⟩ : syracuseStep 17783387 = 26675081) B26675081
theorem B1858139 : Blo 822348 1858139 := bstep (se 1 (by rfl) ⟨1393604, by rfl⟩ : syracuseStep 1858139 = 2787209) B2787209
theorem B1235687 : Blo 822348 1235687 := bstep (se 1 (by rfl) ⟨926765, by rfl⟩ : syracuseStep 1235687 = 1853531) B1853531
theorem B1235945 : Blo 822348 1235945 := bstep (se 2 (by rfl) ⟨463479, by rfl⟩ : syracuseStep 1235945 = 926959) B926959
theorem B1236071 : Blo 822348 1236071 := bstep (se 1 (by rfl) ⟨927053, by rfl⟩ : syracuseStep 1236071 = 1854107) B1854107
theorem B2645405 : Blo 822348 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B1236551 : Blo 822348 1236551 := bstep (se 1 (by rfl) ⟨927413, by rfl⟩ : syracuseStep 1236551 = 1854827) B1854827
theorem B2088767 : Blo 822348 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B1237151 : Blo 822348 1237151 := bstep (se 1 (by rfl) ⟨927863, by rfl⟩ : syracuseStep 1237151 = 1855727) B1855727
theorem B2089223 : Blo 822348 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B2089577 : Blo 822348 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B1238153 : Blo 822348 1238153 := bstep (se 2 (by rfl) ⟨464307, by rfl⟩ : syracuseStep 1238153 = 928615) B928615
theorem B1238507 : Blo 822348 1238507 := bstep (se 1 (by rfl) ⟨928880, by rfl⟩ : syracuseStep 1238507 = 1857761) B1857761
theorem B1238783 : Blo 822348 1238783 := bstep (se 1 (by rfl) ⟨929087, by rfl⟩ : syracuseStep 1238783 = 1858175) B1858175
theorem B3958591 : Blo 822348 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B1239209 : Blo 822348 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B2780351 : Blo 822348 2780351 := bstep (se 1 (by rfl) ⟨2085263, by rfl⟩ : syracuseStep 2780351 = 4170527) B4170527
theorem B9401183 : Blo 822348 9401183 := bstep (se 1 (by rfl) ⟨7050887, by rfl⟩ : syracuseStep 9401183 = 14101775) B14101775
theorem B38139983 : Blo 822348 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B25328375 : Blo 822348 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B4685921 : Blo 822348 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B5278121 : Blo 822348 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B2788883 : Blo 822348 2788883 := bstep (se 1 (by rfl) ⟨2091662, by rfl⟩ : syracuseStep 2788883 = 4183325) B4183325
theorem B823503 : Blo 822348 823503 := bstep (se 1 (by rfl) ⟨617627, by rfl⟩ : syracuseStep 823503 = 1235255) B1235255
theorem B823791 : Blo 822348 823791 := bstep (se 1 (by rfl) ⟨617843, by rfl⟩ : syracuseStep 823791 = 1235687) B1235687
theorem B823963 : Blo 822348 823963 := bstep (se 1 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 823963 = 1235945) B1235945
theorem B824047 : Blo 822348 824047 := bstep (se 1 (by rfl) ⟨618035, by rfl⟩ : syracuseStep 824047 = 1236071) B1236071
theorem B824367 : Blo 822348 824367 := bstep (se 1 (by rfl) ⟨618275, by rfl⟩ : syracuseStep 824367 = 1236551) B1236551
theorem B824767 : Blo 822348 824767 := bstep (se 1 (by rfl) ⟨618575, by rfl⟩ : syracuseStep 824767 = 1237151) B1237151
theorem B825435 : Blo 822348 825435 := bstep (se 1 (by rfl) ⟨619076, by rfl⟩ : syracuseStep 825435 = 1238153) B1238153
theorem B825671 : Blo 822348 825671 := bstep (se 1 (by rfl) ⟨619253, by rfl⟩ : syracuseStep 825671 = 1238507) B1238507
theorem B825855 : Blo 822348 825855 := bstep (se 1 (by rfl) ⟨619391, by rfl⟩ : syracuseStep 825855 = 1238783) B1238783
theorem B826139 : Blo 822348 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B14097401 : Blo 822348 14097401 := bstep (se 2 (by rfl) ⟨5286525, by rfl⟩ : syracuseStep 14097401 = 10573051) B10573051
theorem B6267455 : Blo 822348 6267455 := bstep (se 1 (by rfl) ⟨4700591, by rfl⟩ : syracuseStep 6267455 = 9401183) B9401183
theorem B16885583 : Blo 822348 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B929263 : Blo 822348 929263 := bstep (se 1 (by rfl) ⟨696947, by rfl⟩ : syracuseStep 929263 = 1393895) B1393895
theorem B1388711 : Blo 822348 1388711 := bstep (se 1 (by rfl) ⟨1041533, by rfl⟩ : syracuseStep 1388711 = 2083067) B2083067
theorem B3125587 : Blo 822348 3125587 := bstep (se 1 (by rfl) ⟨2344190, by rfl⟩ : syracuseStep 3125587 = 4688381) B4688381
theorem B27145043 : Blo 822348 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B11908883 : Blo 822348 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B2963927 : Blo 822348 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B5356007 : Blo 822348 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B1850399 : Blo 822348 1850399 := bstep (se 1 (by rfl) ⟨1387799, by rfl⟩ : syracuseStep 1850399 = 2775599) B2775599
theorem B1392511 : Blo 822348 1392511 := bstep (se 1 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 1392511 = 2088767) B2088767
theorem B1392815 : Blo 822348 1392815 := bstep (se 1 (by rfl) ⟨1044611, by rfl⟩ : syracuseStep 1392815 = 2089223) B2089223
theorem B1393051 : Blo 822348 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B5292935 : Blo 822348 5292935 := bstep (se 1 (by rfl) ⟨3969701, by rfl⟩ : syracuseStep 5292935 = 7939403) B7939403
theorem B4179113 : Blo 822348 4179113 := bstep (se 2 (by rfl) ⟨1567167, by rfl⟩ : syracuseStep 4179113 = 3134335) B3134335
theorem B1853567 : Blo 822348 1853567 := bstep (se 1 (by rfl) ⟨1390175, by rfl⟩ : syracuseStep 1853567 = 2780351) B2780351
theorem B3526141 : Blo 822348 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B10573415 : Blo 822348 10573415 := bstep (se 1 (by rfl) ⟨7930061, by rfl⟩ : syracuseStep 10573415 = 15860123) B15860123
theorem B2775707 : Blo 822348 2775707 := bstep (se 1 (by rfl) ⟨2081780, by rfl⟩ : syracuseStep 2775707 = 4163561) B4163561
theorem B10018237 : Blo 822348 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B1236431 : Blo 822348 1236431 := bstep (se 1 (by rfl) ⟨927323, by rfl⟩ : syracuseStep 1236431 = 1854647) B1854647
theorem B1859039 : Blo 822348 1859039 := bstep (se 1 (by rfl) ⟨1394279, by rfl⟩ : syracuseStep 1859039 = 2788559) B2788559
theorem B2351015 : Blo 822348 2351015 := bstep (se 1 (by rfl) ⟨1763261, by rfl⟩ : syracuseStep 2351015 = 3526523) B3526523
theorem B2777327 : Blo 822348 2777327 := bstep (se 1 (by rfl) ⟨2082995, by rfl⟩ : syracuseStep 2777327 = 4165991) B4165991
theorem B3957437 : Blo 822348 3957437 := bstep (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) B1484039
theorem B1172551 : Blo 822348 1172551 := bstep (se 1 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 1172551 = 1758827) B1758827
theorem B18998711 : Blo 822348 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B2778623 : Blo 822348 2778623 := bstep (se 1 (by rfl) ⟨2083967, by rfl⟩ : syracuseStep 2778623 = 4167935) B4167935
theorem B11855591 : Blo 822348 11855591 := bstep (se 1 (by rfl) ⟨8891693, by rfl⟩ : syracuseStep 11855591 = 17783387) B17783387
theorem B1238759 : Blo 822348 1238759 := bstep (se 1 (by rfl) ⟨929069, by rfl⟩ : syracuseStep 1238759 = 1858139) B1858139
theorem B1763603 : Blo 822348 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B7041593 : Blo 822348 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B3961705 : Blo 822348 3961705 := bstep (se 2 (by rfl) ⟨1485639, by rfl⟩ : syracuseStep 3961705 = 2971279) B2971279
theorem B2782079 : Blo 822348 2782079 := bstep (se 1 (by rfl) ⟨2086559, by rfl⟩ : syracuseStep 2782079 = 4173119) B4173119
theorem B3962783 : Blo 822348 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B2783483 : Blo 822348 2783483 := bstep (se 1 (by rfl) ⟨2087612, by rfl⟩ : syracuseStep 2783483 = 4175225) B4175225
theorem B25426655 : Blo 822348 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B2786075 : Blo 822348 2786075 := bstep (se 1 (by rfl) ⟨2089556, by rfl⟩ : syracuseStep 2786075 = 4179113) B4179113
theorem B10553165 : Blo 822348 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B7048943 : Blo 822348 7048943 := bstep (se 1 (by rfl) ⟨5286707, by rfl⟩ : syracuseStep 7048943 = 10573415) B10573415
theorem B824287 : Blo 822348 824287 := bstep (se 1 (by rfl) ⟨618215, by rfl⟩ : syracuseStep 824287 = 1236431) B1236431
theorem B4167449 : Blo 822348 4167449 := bstep (se 2 (by rfl) ⟨1562793, by rfl⟩ : syracuseStep 4167449 = 3125587) B3125587
theorem B5282273 : Blo 822348 5282273 := bstep (se 2 (by rfl) ⟨1980852, by rfl⟩ : syracuseStep 5282273 = 3961705) B3961705
theorem B7903727 : Blo 822348 7903727 := bstep (se 1 (by rfl) ⟨5927795, by rfl⟩ : syracuseStep 7903727 = 11855591) B11855591
theorem B825839 : Blo 822348 825839 := bstep (se 1 (by rfl) ⟨619379, by rfl⟩ : syracuseStep 825839 = 1238759) B1238759
theorem B925807 : Blo 822348 925807 := bstep (se 1 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 925807 = 1388711) B1388711
theorem B4694395 : Blo 822348 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B18096695 : Blo 822348 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B7939255 : Blo 822348 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B1975951 : Blo 822348 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B16951103 : Blo 822348 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B3123947 : Blo 822348 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B928543 : Blo 822348 928543 := bstep (se 1 (by rfl) ⟨696407, by rfl⟩ : syracuseStep 928543 = 1392815) B1392815
theorem B3518747 : Blo 822348 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B1850471 : Blo 822348 1850471 := bstep (se 1 (by rfl) ⟨1387853, by rfl⟩ : syracuseStep 1850471 = 2775707) B2775707
theorem B4701521 : Blo 822348 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B1851551 : Blo 822348 1851551 := bstep (se 1 (by rfl) ⟨1388663, by rfl⟩ : syracuseStep 1851551 = 2777327) B2777327
theorem B4178303 : Blo 822348 4178303 := bstep (se 1 (by rfl) ⟨3133727, by rfl⟩ : syracuseStep 4178303 = 6267455) B6267455
theorem B12665807 : Blo 822348 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B1852415 : Blo 822348 1852415 := bstep (se 1 (by rfl) ⟨1389311, by rfl⟩ : syracuseStep 1852415 = 2778623) B2778623
theorem B11257055 : Blo 822348 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B1854719 : Blo 822348 1854719 := bstep (se 1 (by rfl) ⟨1391039, by rfl⟩ : syracuseStep 1854719 = 2782079) B2782079
theorem B2641855 : Blo 822348 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B1855655 : Blo 822348 1855655 := bstep (se 1 (by rfl) ⟨1391741, by rfl⟩ : syracuseStep 1855655 = 2783483) B2783483
theorem B13357649 : Blo 822348 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B1233599 : Blo 822348 1233599 := bstep (se 1 (by rfl) ⟨925199, by rfl⟩ : syracuseStep 1233599 = 1850399) B1850399
theorem B1856681 : Blo 822348 1856681 := bstep (se 2 (by rfl) ⟨696255, by rfl⟩ : syracuseStep 1856681 = 1392511) B1392511
theorem B1857401 : Blo 822348 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B3528623 : Blo 822348 3528623 := bstep (se 1 (by rfl) ⟨2646467, by rfl⟩ : syracuseStep 3528623 = 5292935) B5292935
theorem B1235711 : Blo 822348 1235711 := bstep (se 1 (by rfl) ⟨926783, by rfl⟩ : syracuseStep 1235711 = 1853567) B1853567
theorem B1563401 : Blo 822348 1563401 := bstep (se 2 (by rfl) ⟨586275, by rfl⟩ : syracuseStep 1563401 = 1172551) B1172551
theorem B1859255 : Blo 822348 1859255 := bstep (se 1 (by rfl) ⟨1394441, by rfl⟩ : syracuseStep 1859255 = 2788883) B2788883
theorem B1239017 : Blo 822348 1239017 := bstep (se 2 (by rfl) ⟨464631, by rfl⟩ : syracuseStep 1239017 = 929263) B929263
theorem B9398267 : Blo 822348 9398267 := bstep (se 1 (by rfl) ⟨7048700, by rfl⟩ : syracuseStep 9398267 = 14097401) B14097401
theorem B1239359 : Blo 822348 1239359 := bstep (se 1 (by rfl) ⟨929519, by rfl⟩ : syracuseStep 1239359 = 1859039) B1859039
theorem B1567343 : Blo 822348 1567343 := bstep (se 1 (by rfl) ⟨1175507, by rfl⟩ : syracuseStep 1567343 = 2351015) B2351015
theorem B1175735 : Blo 822348 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B3570671 : Blo 822348 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B2785535 : Blo 822348 2785535 := bstep (se 1 (by rfl) ⟨2089151, by rfl⟩ : syracuseStep 2785535 = 4178303) B4178303
theorem B6259193 : Blo 822348 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B7504703 : Blo 822348 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B10585673 : Blo 822348 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B822399 : Blo 822348 822399 := bstep (se 1 (by rfl) ⟨616799, by rfl⟩ : syracuseStep 822399 = 1233599) B1233599
theorem B823807 : Blo 822348 823807 := bstep (se 1 (by rfl) ⟨617855, by rfl⟩ : syracuseStep 823807 = 1235711) B1235711
theorem B12064463 : Blo 822348 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B826011 : Blo 822348 826011 := bstep (se 1 (by rfl) ⟨619508, by rfl⟩ : syracuseStep 826011 = 1239017) B1239017
theorem B6265511 : Blo 822348 6265511 := bstep (se 1 (by rfl) ⟨4699133, by rfl⟩ : syracuseStep 6265511 = 9398267) B9398267
theorem B826239 : Blo 822348 826239 := bstep (se 1 (by rfl) ⟨619679, by rfl⟩ : syracuseStep 826239 = 1239359) B1239359
theorem B4169069 : Blo 822348 4169069 := bstep (se 3 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 4169069 = 1563401) B1563401
theorem B2634601 : Blo 822348 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B4699295 : Blo 822348 4699295 := bstep (se 1 (by rfl) ⟨3524471, by rfl⟩ : syracuseStep 4699295 = 7048943) B7048943
theorem B3521515 : Blo 822348 3521515 := bstep (se 1 (by rfl) ⟨2641136, by rfl⟩ : syracuseStep 3521515 = 5282273) B5282273
theorem B3522473 : Blo 822348 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B2082631 : Blo 822348 2082631 := bstep (se 1 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 2082631 = 3123947) B3123947
theorem B2345831 : Blo 822348 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B12537389 : Blo 822348 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B2380447 : Blo 822348 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B1233647 : Blo 822348 1233647 := bstep (se 1 (by rfl) ⟨925235, by rfl⟩ : syracuseStep 1233647 = 1850471) B1850471
theorem B1234367 : Blo 822348 1234367 := bstep (se 1 (by rfl) ⟨925775, by rfl⟩ : syracuseStep 1234367 = 1851551) B1851551
theorem B1234409 : Blo 822348 1234409 := bstep (se 2 (by rfl) ⟨462903, by rfl⟩ : syracuseStep 1234409 = 925807) B925807
theorem B3135293 : Blo 822348 3135293 := bstep (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) B1175735
theorem B1857383 : Blo 822348 1857383 := bstep (se 1 (by rfl) ⟨1393037, by rfl⟩ : syracuseStep 1857383 = 2786075) B2786075
theorem B8443871 : Blo 822348 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B1234943 : Blo 822348 1234943 := bstep (se 1 (by rfl) ⟨926207, by rfl⟩ : syracuseStep 1234943 = 1852415) B1852415
theorem B7035443 : Blo 822348 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B1236479 : Blo 822348 1236479 := bstep (se 1 (by rfl) ⟨927359, by rfl⟩ : syracuseStep 1236479 = 1854719) B1854719
theorem B1237103 : Blo 822348 1237103 := bstep (se 1 (by rfl) ⟨927827, by rfl⟩ : syracuseStep 1237103 = 1855655) B1855655
theorem B8905099 : Blo 822348 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B1237787 : Blo 822348 1237787 := bstep (se 1 (by rfl) ⟨928340, by rfl⟩ : syracuseStep 1237787 = 1856681) B1856681
theorem B1238057 : Blo 822348 1238057 := bstep (se 2 (by rfl) ⟨464271, by rfl⟩ : syracuseStep 1238057 = 928543) B928543
theorem B2778299 : Blo 822348 2778299 := bstep (se 1 (by rfl) ⟨2083724, by rfl⟩ : syracuseStep 2778299 = 4167449) B4167449
theorem B1238267 : Blo 822348 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B2352415 : Blo 822348 2352415 := bstep (se 1 (by rfl) ⟨1764311, by rfl⟩ : syracuseStep 2352415 = 3528623) B3528623
theorem B5269151 : Blo 822348 5269151 := bstep (se 1 (by rfl) ⟨3951863, by rfl⟩ : syracuseStep 5269151 = 7903727) B7903727
theorem B1239503 : Blo 822348 1239503 := bstep (se 1 (by rfl) ⟨929627, by rfl⟩ : syracuseStep 1239503 = 1859255) B1859255
theorem B11300735 : Blo 822348 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B1044895 : Blo 822348 1044895 := bstep (se 1 (by rfl) ⟨783671, by rfl⟩ : syracuseStep 1044895 = 1567343) B1567343
theorem B822431 : Blo 822348 822431 := bstep (se 1 (by rfl) ⟨616823, by rfl⟩ : syracuseStep 822431 = 1233647) B1233647
theorem B822911 : Blo 822348 822911 := bstep (se 1 (by rfl) ⟨617183, by rfl⟩ : syracuseStep 822911 = 1234367) B1234367
theorem B822939 : Blo 822348 822939 := bstep (se 1 (by rfl) ⟨617204, by rfl⟩ : syracuseStep 822939 = 1234409) B1234409
theorem B823295 : Blo 822348 823295 := bstep (se 1 (by rfl) ⟨617471, by rfl⟩ : syracuseStep 823295 = 1234943) B1234943
theorem B4690295 : Blo 822348 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B824319 : Blo 822348 824319 := bstep (se 1 (by rfl) ⟨618239, by rfl⟩ : syracuseStep 824319 = 1236479) B1236479
theorem B824735 : Blo 822348 824735 := bstep (se 1 (by rfl) ⟨618551, by rfl⟩ : syracuseStep 824735 = 1237103) B1237103
theorem B825191 : Blo 822348 825191 := bstep (se 1 (by rfl) ⟨618893, by rfl⟩ : syracuseStep 825191 = 1237787) B1237787
theorem B825371 : Blo 822348 825371 := bstep (se 1 (by rfl) ⟨619028, by rfl⟩ : syracuseStep 825371 = 1238057) B1238057
theorem B825511 : Blo 822348 825511 := bstep (se 1 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 825511 = 1238267) B1238267
theorem B3512767 : Blo 822348 3512767 := bstep (se 1 (by rfl) ⟨2634575, by rfl⟩ : syracuseStep 3512767 = 5269151) B5269151
theorem B3512801 : Blo 822348 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B826335 : Blo 822348 826335 := bstep (se 1 (by rfl) ⟨619751, by rfl⟩ : syracuseStep 826335 = 1239503) B1239503
theorem B4695353 : Blo 822348 4695353 := bstep (se 2 (by rfl) ⟨1760757, by rfl⟩ : syracuseStep 4695353 = 3521515) B3521515
theorem B33433037 : Blo 822348 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B4172795 : Blo 822348 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B11873465 : Blo 822348 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B7057115 : Blo 822348 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B12695717 : Blo 822348 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B8042975 : Blo 822348 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B4177007 : Blo 822348 4177007 := bstep (se 1 (by rfl) ⟨3132755, by rfl⟩ : syracuseStep 4177007 = 6265511) B6265511
theorem B1393193 : Blo 822348 1393193 := bstep (se 2 (by rfl) ⟨522447, by rfl⟩ : syracuseStep 1393193 = 1044895) B1044895
theorem B1852199 : Blo 822348 1852199 := bstep (se 1 (by rfl) ⟨1389149, by rfl⟩ : syracuseStep 1852199 = 2778299) B2778299
theorem B3132863 : Blo 822348 3132863 := bstep (se 1 (by rfl) ⟨2349647, by rfl⟩ : syracuseStep 3132863 = 4699295) B4699295
theorem B2348315 : Blo 822348 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B1857023 : Blo 822348 1857023 := bstep (se 1 (by rfl) ⟨1392767, by rfl⟩ : syracuseStep 1857023 = 2785535) B2785535
theorem B5003135 : Blo 822348 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B3136553 : Blo 822348 3136553 := bstep (se 2 (by rfl) ⟨1176207, by rfl⟩ : syracuseStep 3136553 = 2352415) B2352415
theorem B1563887 : Blo 822348 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B2776841 : Blo 822348 2776841 := bstep (se 2 (by rfl) ⟨1041315, by rfl⟩ : syracuseStep 2776841 = 2082631) B2082631
theorem B2090195 : Blo 822348 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B1238255 : Blo 822348 1238255 := bstep (se 1 (by rfl) ⟨928691, by rfl⟩ : syracuseStep 1238255 = 1857383) B1857383
theorem B5629247 : Blo 822348 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B2779379 : Blo 822348 2779379 := bstep (se 1 (by rfl) ⟨2084534, by rfl⟩ : syracuseStep 2779379 = 4169069) B4169069
theorem B7533823 : Blo 822348 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B825503 : Blo 822348 825503 := bstep (se 1 (by rfl) ⟨619127, by rfl⟩ : syracuseStep 825503 = 1238255) B1238255
theorem B22288691 : Blo 822348 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B4170365 : Blo 822348 4170365 := bstep (se 3 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 4170365 = 1563887) B1563887
theorem B8463811 : Blo 822348 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B928795 : Blo 822348 928795 := bstep (se 1 (by rfl) ⟨696596, by rfl⟩ : syracuseStep 928795 = 1393193) B1393193
theorem B3126863 : Blo 822348 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B2341867 : Blo 822348 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B1851227 : Blo 822348 1851227 := bstep (se 1 (by rfl) ⟨1388420, by rfl⟩ : syracuseStep 1851227 = 2776841) B2776841
theorem B1393463 : Blo 822348 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B3130235 : Blo 822348 3130235 := bstep (se 1 (by rfl) ⟨2347676, by rfl⟩ : syracuseStep 3130235 = 4695353) B4695353
theorem B3752831 : Blo 822348 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B1852919 : Blo 822348 1852919 := bstep (se 1 (by rfl) ⟨1389689, by rfl⟩ : syracuseStep 1852919 = 2779379) B2779379
theorem B10045097 : Blo 822348 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B7915643 : Blo 822348 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B4704743 : Blo 822348 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B5361983 : Blo 822348 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B1234799 : Blo 822348 1234799 := bstep (se 1 (by rfl) ⟨926099, by rfl⟩ : syracuseStep 1234799 = 1852199) B1852199
theorem B2088575 : Blo 822348 2088575 := bstep (se 1 (by rfl) ⟨1566431, by rfl⟩ : syracuseStep 2088575 = 3132863) B3132863
theorem B1565543 : Blo 822348 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B1238015 : Blo 822348 1238015 := bstep (se 1 (by rfl) ⟨928511, by rfl⟩ : syracuseStep 1238015 = 1857023) B1857023
theorem B3335423 : Blo 822348 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B2091035 : Blo 822348 2091035 := bstep (se 1 (by rfl) ⟨1568276, by rfl⟩ : syracuseStep 2091035 = 3136553) B3136553
theorem B2781863 : Blo 822348 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B4683689 : Blo 822348 4683689 := bstep (se 2 (by rfl) ⟨1756383, by rfl⟩ : syracuseStep 4683689 = 3512767) B3512767
theorem B2784671 : Blo 822348 2784671 := bstep (se 1 (by rfl) ⟨2088503, by rfl⟩ : syracuseStep 2784671 = 4177007) B4177007
theorem B5277095 : Blo 822348 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B3574655 : Blo 822348 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B823199 : Blo 822348 823199 := bstep (se 1 (by rfl) ⟨617399, by rfl⟩ : syracuseStep 823199 = 1234799) B1234799
theorem B825343 : Blo 822348 825343 := bstep (se 1 (by rfl) ⟨619007, by rfl⟩ : syracuseStep 825343 = 1238015) B1238015
theorem B3122459 : Blo 822348 3122459 := bstep (se 1 (by rfl) ⟨2341844, by rfl⟩ : syracuseStep 3122459 = 4683689) B4683689
theorem B3122489 : Blo 822348 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B928975 : Blo 822348 928975 := bstep (se 1 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 928975 = 1393463) B1393463
theorem B2501887 : Blo 822348 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B6696731 : Blo 822348 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B11285081 : Blo 822348 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B8894461 : Blo 822348 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B1392383 : Blo 822348 1392383 := bstep (se 1 (by rfl) ⟨1044287, by rfl⟩ : syracuseStep 1392383 = 2088575) B2088575
theorem B1394023 : Blo 822348 1394023 := bstep (se 1 (by rfl) ⟨1045517, by rfl⟩ : syracuseStep 1394023 = 2091035) B2091035
theorem B1854575 : Blo 822348 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B2084575 : Blo 822348 2084575 := bstep (se 1 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 2084575 = 3126863) B3126863
theorem B1856447 : Blo 822348 1856447 := bstep (se 1 (by rfl) ⟨1392335, by rfl⟩ : syracuseStep 1856447 = 2784671) B2784671
theorem B1234151 : Blo 822348 1234151 := bstep (se 1 (by rfl) ⟨925613, by rfl⟩ : syracuseStep 1234151 = 1851227) B1851227
theorem B2086823 : Blo 822348 2086823 := bstep (se 1 (by rfl) ⟨1565117, by rfl⟩ : syracuseStep 2086823 = 3130235) B3130235
theorem B1235279 : Blo 822348 1235279 := bstep (se 1 (by rfl) ⟨926459, by rfl⟩ : syracuseStep 1235279 = 1852919) B1852919
theorem B3136495 : Blo 822348 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B1238393 : Blo 822348 1238393 := bstep (se 2 (by rfl) ⟨464397, by rfl⟩ : syracuseStep 1238393 = 928795) B928795
theorem B2780243 : Blo 822348 2780243 := bstep (se 1 (by rfl) ⟨2085182, by rfl⟩ : syracuseStep 2780243 = 4170365) B4170365
theorem B1043695 : Blo 822348 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B59436509 : Blo 822348 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B822767 : Blo 822348 822767 := bstep (se 1 (by rfl) ⟨617075, by rfl⟩ : syracuseStep 822767 = 1234151) B1234151
theorem B823519 : Blo 822348 823519 := bstep (se 1 (by rfl) ⟨617639, by rfl⟩ : syracuseStep 823519 = 1235279) B1235279
theorem B825595 : Blo 822348 825595 := bstep (se 1 (by rfl) ⟨619196, by rfl⟩ : syracuseStep 825595 = 1238393) B1238393
theorem B4464487 : Blo 822348 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B928255 : Blo 822348 928255 := bstep (se 1 (by rfl) ⟨696191, by rfl⟩ : syracuseStep 928255 = 1392383) B1392383
theorem B3518063 : Blo 822348 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B1391215 : Blo 822348 1391215 := bstep (se 1 (by rfl) ⟨1043411, by rfl⟩ : syracuseStep 1391215 = 2086823) B2086823
theorem B1391593 : Blo 822348 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B2081639 : Blo 822348 2081639 := bstep (se 1 (by rfl) ⟨1561229, by rfl⟩ : syracuseStep 2081639 = 3122459) B3122459
theorem B2081659 : Blo 822348 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B1853495 : Blo 822348 1853495 := bstep (se 1 (by rfl) ⟨1390121, by rfl⟩ : syracuseStep 1853495 = 2780243) B2780243
theorem B7523387 : Blo 822348 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B4181993 : Blo 822348 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B1858697 : Blo 822348 1858697 := bstep (se 2 (by rfl) ⟨697011, by rfl⟩ : syracuseStep 1858697 = 1394023) B1394023
theorem B2383103 : Blo 822348 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B1236383 : Blo 822348 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B1237631 : Blo 822348 1237631 := bstep (se 1 (by rfl) ⟨928223, by rfl⟩ : syracuseStep 1237631 = 1856447) B1856447
theorem B1238633 : Blo 822348 1238633 := bstep (se 2 (by rfl) ⟨464487, by rfl⟩ : syracuseStep 1238633 = 928975) B928975
theorem B3335849 : Blo 822348 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B2779433 : Blo 822348 2779433 := bstep (se 2 (by rfl) ⟨1042287, by rfl⟩ : syracuseStep 2779433 = 2084575) B2084575
theorem B11859281 : Blo 822348 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B158497357 : Blo 822348 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B5015591 : Blo 822348 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B2787995 : Blo 822348 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B824255 : Blo 822348 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B825087 : Blo 822348 825087 := bstep (se 1 (by rfl) ⟨618815, by rfl⟩ : syracuseStep 825087 = 1237631) B1237631
theorem B825755 : Blo 822348 825755 := bstep (se 1 (by rfl) ⟨619316, by rfl⟩ : syracuseStep 825755 = 1238633) B1238633
theorem B211329809 : Blo 822348 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B7906187 : Blo 822348 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B1387759 : Blo 822348 1387759 := bstep (se 1 (by rfl) ⟨1040819, by rfl⟩ : syracuseStep 1387759 = 2081639) B2081639
theorem B1588735 : Blo 822348 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B1852955 : Blo 822348 1852955 := bstep (se 1 (by rfl) ⟨1389716, by rfl⟩ : syracuseStep 1852955 = 2779433) B2779433
theorem B2345375 : Blo 822348 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B1854953 : Blo 822348 1854953 := bstep (se 2 (by rfl) ⟨695607, by rfl⟩ : syracuseStep 1854953 = 1391215) B1391215
theorem B1855457 : Blo 822348 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B5952649 : Blo 822348 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B2775545 : Blo 822348 2775545 := bstep (se 2 (by rfl) ⟨1040829, by rfl⟩ : syracuseStep 2775545 = 2081659) B2081659
theorem B1235663 : Blo 822348 1235663 := bstep (se 1 (by rfl) ⟨926747, by rfl⟩ : syracuseStep 1235663 = 1853495) B1853495
theorem B1237673 : Blo 822348 1237673 := bstep (se 2 (by rfl) ⟨464127, by rfl⟩ : syracuseStep 1237673 = 928255) B928255
theorem B1239131 : Blo 822348 1239131 := bstep (se 1 (by rfl) ⟨929348, by rfl⟩ : syracuseStep 1239131 = 1858697) B1858697
theorem B2223899 : Blo 822348 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B3343727 : Blo 822348 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B823775 : Blo 822348 823775 := bstep (se 1 (by rfl) ⟨617831, by rfl⟩ : syracuseStep 823775 = 1235663) B1235663
theorem B825115 : Blo 822348 825115 := bstep (se 1 (by rfl) ⟨618836, by rfl⟩ : syracuseStep 825115 = 1237673) B1237673
theorem B826087 : Blo 822348 826087 := bstep (se 1 (by rfl) ⟨619565, by rfl⟩ : syracuseStep 826087 = 1239131) B1239131
theorem B7936865 : Blo 822348 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B1482599 : Blo 822348 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B1850345 : Blo 822348 1850345 := bstep (se 2 (by rfl) ⟨693879, by rfl⟩ : syracuseStep 1850345 = 1387759) B1387759
theorem B1850363 : Blo 822348 1850363 := bstep (se 1 (by rfl) ⟨1387772, by rfl⟩ : syracuseStep 1850363 = 2775545) B2775545
theorem B140886539 : Blo 822348 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B2118313 : Blo 822348 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B1235303 : Blo 822348 1235303 := bstep (se 1 (by rfl) ⟨926477, by rfl⟩ : syracuseStep 1235303 = 1852955) B1852955
theorem B1858663 : Blo 822348 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B1236635 : Blo 822348 1236635 := bstep (se 1 (by rfl) ⟨927476, by rfl⟩ : syracuseStep 1236635 = 1854953) B1854953
theorem B1236971 : Blo 822348 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B5270791 : Blo 822348 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B6254333 : Blo 822348 6254333 := bstep (se 3 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 6254333 = 2345375) B2345375
theorem B8916605 : Blo 822348 8916605 := bstep (se 3 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 8916605 = 3343727) B3343727
theorem B823535 : Blo 822348 823535 := bstep (se 1 (by rfl) ⟨617651, by rfl⟩ : syracuseStep 823535 = 1235303) B1235303
theorem B824423 : Blo 822348 824423 := bstep (se 1 (by rfl) ⟨618317, by rfl⟩ : syracuseStep 824423 = 1236635) B1236635
theorem B988399 : Blo 822348 988399 := bstep (se 1 (by rfl) ⟨741299, by rfl⟩ : syracuseStep 988399 = 1482599) B1482599
theorem B824647 : Blo 822348 824647 := bstep (se 1 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 824647 = 1236971) B1236971
theorem B2824417 : Blo 822348 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B4169555 : Blo 822348 4169555 := bstep (se 1 (by rfl) ⟨3127166, by rfl⟩ : syracuseStep 4169555 = 6254333) B6254333
theorem B93924359 : Blo 822348 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B7027721 : Blo 822348 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B5291243 : Blo 822348 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B2478217 : Blo 822348 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B1233563 : Blo 822348 1233563 := bstep (se 1 (by rfl) ⟨925172, by rfl⟩ : syracuseStep 1233563 = 1850345) B1850345
theorem B1233575 : Blo 822348 1233575 := bstep (se 1 (by rfl) ⟨925181, by rfl⟩ : syracuseStep 1233575 = 1850363) B1850363
theorem B822375 : Blo 822348 822375 := bstep (se 1 (by rfl) ⟨616781, by rfl⟩ : syracuseStep 822375 = 1233563) B1233563
theorem B822383 : Blo 822348 822383 := bstep (se 1 (by rfl) ⟨616787, by rfl⟩ : syracuseStep 822383 = 1233575) B1233575
theorem B1317865 : Blo 822348 1317865 := bstep (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) B988399
theorem B5944403 : Blo 822348 5944403 := bstep (se 1 (by rfl) ⟨4458302, by rfl⟩ : syracuseStep 5944403 = 8916605) B8916605
theorem B52868629 : Blo 822348 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B3527495 : Blo 822348 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B2779703 : Blo 822348 2779703 := bstep (se 1 (by rfl) ⟨2084777, by rfl⟩ : syracuseStep 2779703 = 4169555) B4169555
theorem B62616239 : Blo 822348 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B3765889 : Blo 822348 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B4685147 : Blo 822348 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B70491505 : Blo 822348 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B5021185 : Blo 822348 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B3123431 : Blo 822348 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B1853135 : Blo 822348 1853135 := bstep (se 1 (by rfl) ⟨1389851, by rfl⟩ : syracuseStep 1853135 = 2779703) B2779703
theorem B1757153 : Blo 822348 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B2351663 : Blo 822348 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B41744159 : Blo 822348 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B3962935 : Blo 822348 3962935 := bstep (se 1 (by rfl) ⟨2972201, by rfl⟩ : syracuseStep 3962935 = 5944403) B5944403
theorem B5283913 : Blo 822348 5283913 := bstep (se 2 (by rfl) ⟨1981467, by rfl⟩ : syracuseStep 5283913 = 3962935) B3962935
theorem B27829439 : Blo 822348 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B93988673 : Blo 822348 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B6694913 : Blo 822348 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B2082287 : Blo 822348 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B1235423 : Blo 822348 1235423 := bstep (se 1 (by rfl) ⟨926567, by rfl⟩ : syracuseStep 1235423 = 1853135) B1853135
theorem B1171435 : Blo 822348 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B1567775 : Blo 822348 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B7045217 : Blo 822348 7045217 := bstep (se 2 (by rfl) ⟨2641956, by rfl⟩ : syracuseStep 7045217 = 5283913) B5283913
theorem B823615 : Blo 822348 823615 := bstep (se 1 (by rfl) ⟨617711, by rfl⟩ : syracuseStep 823615 = 1235423) B1235423
theorem B18552959 : Blo 822348 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B62659115 : Blo 822348 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B4463275 : Blo 822348 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B1388191 : Blo 822348 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B4180733 : Blo 822348 4180733 := bstep (se 3 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 4180733 = 1567775) B1567775
theorem B1561913 : Blo 822348 1561913 := bstep (se 2 (by rfl) ⟨585717, by rfl⟩ : syracuseStep 1561913 = 1171435) B1171435
theorem B2787155 : Blo 822348 2787155 := bstep (se 1 (by rfl) ⟨2090366, by rfl⟩ : syracuseStep 2787155 = 4180733) B4180733
theorem B4696811 : Blo 822348 4696811 := bstep (se 1 (by rfl) ⟨3522608, by rfl⟩ : syracuseStep 4696811 = 7045217) B7045217
theorem B12368639 : Blo 822348 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B1850921 : Blo 822348 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B5951033 : Blo 822348 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B1041275 : Blo 822348 1041275 := bstep (se 1 (by rfl) ⟨780956, by rfl⟩ : syracuseStep 1041275 = 1561913) B1561913
theorem B41772743 : Blo 822348 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B3967355 : Blo 822348 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B3131207 : Blo 822348 3131207 := bstep (se 1 (by rfl) ⟨2348405, by rfl⟩ : syracuseStep 3131207 = 4696811) B4696811
theorem B32983037 : Blo 822348 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B1233947 : Blo 822348 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B1858103 : Blo 822348 1858103 := bstep (se 1 (by rfl) ⟨1393577, by rfl⟩ : syracuseStep 1858103 = 2787155) B2787155
theorem B2776733 : Blo 822348 2776733 := bstep (se 3 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 2776733 = 1041275) B1041275
theorem B27848495 : Blo 822348 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B21988691 : Blo 822348 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B822631 : Blo 822348 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B74262653 : Blo 822348 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B1851155 : Blo 822348 1851155 := bstep (se 1 (by rfl) ⟨1388366, by rfl⟩ : syracuseStep 1851155 = 2776733) B2776733
theorem B2087471 : Blo 822348 2087471 := bstep (se 1 (by rfl) ⟨1565603, by rfl⟩ : syracuseStep 2087471 = 3131207) B3131207
theorem B2644903 : Blo 822348 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B1238735 : Blo 822348 1238735 := bstep (se 1 (by rfl) ⟨929051, by rfl⟩ : syracuseStep 1238735 = 1858103) B1858103
theorem B825823 : Blo 822348 825823 := bstep (se 1 (by rfl) ⟨619367, by rfl⟩ : syracuseStep 825823 = 1238735) B1238735
theorem B14659127 : Blo 822348 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B1391647 : Blo 822348 1391647 := bstep (se 1 (by rfl) ⟨1043735, by rfl⟩ : syracuseStep 1391647 = 2087471) B2087471
theorem B14106149 : Blo 822348 14106149 := bstep (se 4 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 14106149 = 2644903) B2644903
theorem B1234103 : Blo 822348 1234103 := bstep (se 1 (by rfl) ⟨925577, by rfl⟩ : syracuseStep 1234103 = 1851155) B1851155
theorem B49508435 : Blo 822348 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B132022493 : Blo 822348 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B822735 : Blo 822348 822735 := bstep (se 1 (by rfl) ⟨617051, by rfl⟩ : syracuseStep 822735 = 1234103) B1234103
theorem B9772751 : Blo 822348 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B1855529 : Blo 822348 1855529 := bstep (se 2 (by rfl) ⟨695823, by rfl⟩ : syracuseStep 1855529 = 1391647) B1391647
theorem B9404099 : Blo 822348 9404099 := bstep (se 1 (by rfl) ⟨7053074, by rfl⟩ : syracuseStep 9404099 = 14106149) B14106149
theorem B88014995 : Blo 822348 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B26060669 : Blo 822348 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B6269399 : Blo 822348 6269399 := bstep (se 1 (by rfl) ⟨4702049, by rfl⟩ : syracuseStep 6269399 = 9404099) B9404099
theorem B1237019 : Blo 822348 1237019 := bstep (se 1 (by rfl) ⟨927764, by rfl⟩ : syracuseStep 1237019 = 1855529) B1855529
theorem B824679 : Blo 822348 824679 := bstep (se 1 (by rfl) ⟨618509, by rfl⟩ : syracuseStep 824679 = 1237019) B1237019
theorem B17373779 : Blo 822348 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B4179599 : Blo 822348 4179599 := bstep (se 1 (by rfl) ⟨3134699, by rfl⟩ : syracuseStep 4179599 = 6269399) B6269399
theorem B58676663 : Blo 822348 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B2786399 : Blo 822348 2786399 := bstep (se 1 (by rfl) ⟨2089799, by rfl⟩ : syracuseStep 2786399 = 4179599) B4179599
theorem B11582519 : Blo 822348 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B39117775 : Blo 822348 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B123546869 : Blo 822348 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B1857599 : Blo 822348 1857599 := bstep (se 1 (by rfl) ⟨1393199, by rfl⟩ : syracuseStep 1857599 = 2786399) B2786399
theorem B52157033 : Blo 822348 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B34771355 : Blo 822348 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B82364579 : Blo 822348 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B1238399 : Blo 822348 1238399 := bstep (se 1 (by rfl) ⟨928799, by rfl⟩ : syracuseStep 1238399 = 1857599) B1857599
theorem B825599 : Blo 822348 825599 := bstep (se 1 (by rfl) ⟨619199, by rfl⟩ : syracuseStep 825599 = 1238399) B1238399
theorem B23180903 : Blo 822348 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B54909719 : Blo 822348 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B36606479 : Blo 822348 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B15453935 : Blo 822348 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B97617277 : Blo 822348 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B10302623 : Blo 822348 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B520625477 : Blo 822348 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B6868415 : Blo 822348 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B347083651 : Blo 822348 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B18315773 : Blo 822348 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B12210515 : Blo 822348 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B462778201 : Blo 822348 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B8140343 : Blo 822348 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B617037601 : Blo 822348 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B822716801 : Blo 822348 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B86830325 : Blo 822348 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B548477867 : Blo 822348 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B57886883 : Blo 822348 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B38591255 : Blo 822348 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B365651911 : Blo 822348 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B25727503 : Blo 822348 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B487535881 : Blo 822348 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B34303337 : Blo 822348 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B650047841 : Blo 822348 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 822348 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B22868891 : Blo 822348 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B15245927 : Blo 822348 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B288910151 : Blo 822348 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B10163951 : Blo 822348 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B192606767 : Blo 822348 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B128404511 : Blo 822348 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B6775967 : Blo 822348 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B85603007 : Blo 822348 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B18069245 : Blo 822348 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B57068671 : Blo 822348 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B12046163 : Blo 822348 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B76091561 : Blo 822348 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B32123101 : Blo 822348 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B50727707 : Blo 822348 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B42830801 : Blo 822348 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B33818471 : Blo 822348 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B28553867 : Blo 822348 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B22545647 : Blo 822348 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B19035911 : Blo 822348 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B12690607 : Blo 822348 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B15030431 : Blo 822348 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B16920809 : Blo 822348 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B10020287 : Blo 822348 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B11280539 : Blo 822348 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B6680191 : Blo 822348 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B7520359 : Blo 822348 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B8906921 : Blo 822348 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B10027145 : Blo 822348 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B5937947 : Blo 822348 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B6684763 : Blo 822348 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B3958631 : Blo 822348 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B8913017 : Blo 822348 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B2639087 : Blo 822348 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B5942011 : Blo 822348 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B1759391 : Blo 822348 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B7922681 : Blo 822348 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B1172927 : Blo 822348 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B5281787 : Blo 822348 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B3127805 : Blo 822348 3127805 := bstep (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) B1172927
theorem B3521191 : Blo 822348 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B2085203 : Blo 822348 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B4694921 : Blo 822348 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B1390135 : Blo 822348 1390135 := bstep (se 1 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 1390135 = 2085203) B2085203
theorem B3129947 : Blo 822348 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B1853513 : Blo 822348 1853513 := bstep (se 2 (by rfl) ⟨695067, by rfl⟩ : syracuseStep 1853513 = 1390135) B1390135
theorem B2086631 : Blo 822348 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B1235675 : Blo 822348 1235675 := bstep (se 1 (by rfl) ⟨926756, by rfl⟩ : syracuseStep 1235675 = 1853513) B1853513
theorem B823783 : Blo 822348 823783 := bstep (se 1 (by rfl) ⟨617837, by rfl⟩ : syracuseStep 823783 = 1235675) B1235675
theorem B1391087 : Blo 822348 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631
theorem B927391 : Blo 822348 927391 := bstep (se 1 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 927391 = 1391087) B1391087
theorem B1236521 : Blo 822348 1236521 := bstep (se 2 (by rfl) ⟨463695, by rfl⟩ : syracuseStep 1236521 = 927391) B927391
theorem B824347 : Blo 822348 824347 := bstep (se 1 (by rfl) ⟨618260, by rfl⟩ : syracuseStep 824347 = 1236521) B1236521

theorem C0 (j : ℕ) (h1 : 205587 ≤ j) (h2 : j ≤ 206286) : Blo 822348 (4 * j + 3) := by
  interval_cases j
  · exact B822351
  · exact B822355
  · exact B822359
  · exact B822363
  · exact B822367
  · exact B822371
  · exact B822375
  · exact B822379
  · exact B822383
  · exact B822387
  · exact B822391
  · exact B822395
  · exact B822399
  · exact B822403
  · exact B822407
  · exact B822411
  · exact B822415
  · exact B822419
  · exact B822423
  · exact B822427
  · exact B822431
  · exact B822435
  · exact B822439
  · exact B822443
  · exact B822447
  · exact B822451
  · exact B822455
  · exact B822459
  · exact B822463
  · exact B822467
  · exact B822471
  · exact B822475
  · exact B822479
  · exact B822483
  · exact B822487
  · exact B822491
  · exact B822495
  · exact B822499
  · exact B822503
  · exact B822507
  · exact B822511
  · exact B822515
  · exact B822519
  · exact B822523
  · exact B822527
  · exact B822531
  · exact B822535
  · exact B822539
  · exact B822543
  · exact B822547
  · exact B822551
  · exact B822555
  · exact B822559
  · exact B822563
  · exact B822567
  · exact B822571
  · exact B822575
  · exact B822579
  · exact B822583
  · exact B822587
  · exact B822591
  · exact B822595
  · exact B822599
  · exact B822603
  · exact B822607
  · exact B822611
  · exact B822615
  · exact B822619
  · exact B822623
  · exact B822627
  · exact B822631
  · exact B822635
  · exact B822639
  · exact B822643
  · exact B822647
  · exact B822651
  · exact B822655
  · exact B822659
  · exact B822663
  · exact B822667
  · exact B822671
  · exact B822675
  · exact B822679
  · exact B822683
  · exact B822687
  · exact B822691
  · exact B822695
  · exact B822699
  · exact B822703
  · exact B822707
  · exact B822711
  · exact B822715
  · exact B822719
  · exact B822723
  · exact B822727
  · exact B822731
  · exact B822735
  · exact B822739
  · exact B822743
  · exact B822747
  · exact B822751
  · exact B822755
  · exact B822759
  · exact B822763
  · exact B822767
  · exact B822771
  · exact B822775
  · exact B822779
  · exact B822783
  · exact B822787
  · exact B822791
  · exact B822795
  · exact B822799
  · exact B822803
  · exact B822807
  · exact B822811
  · exact B822815
  · exact B822819
  · exact B822823
  · exact B822827
  · exact B822831
  · exact B822835
  · exact B822839
  · exact B822843
  · exact B822847
  · exact B822851
  · exact B822855
  · exact B822859
  · exact B822863
  · exact B822867
  · exact B822871
  · exact B822875
  · exact B822879
  · exact B822883
  · exact B822887
  · exact B822891
  · exact B822895
  · exact B822899
  · exact B822903
  · exact B822907
  · exact B822911
  · exact B822915
  · exact B822919
  · exact B822923
  · exact B822927
  · exact B822931
  · exact B822935
  · exact B822939
  · exact B822943
  · exact B822947
  · exact B822951
  · exact B822955
  · exact B822959
  · exact B822963
  · exact B822967
  · exact B822971
  · exact B822975
  · exact B822979
  · exact B822983
  · exact B822987
  · exact B822991
  · exact B822995
  · exact B822999
  · exact B823003
  · exact B823007
  · exact B823011
  · exact B823015
  · exact B823019
  · exact B823023
  · exact B823027
  · exact B823031
  · exact B823035
  · exact B823039
  · exact B823043
  · exact B823047
  · exact B823051
  · exact B823055
  · exact B823059
  · exact B823063
  · exact B823067
  · exact B823071
  · exact B823075
  · exact B823079
  · exact B823083
  · exact B823087
  · exact B823091
  · exact B823095
  · exact B823099
  · exact B823103
  · exact B823107
  · exact B823111
  · exact B823115
  · exact B823119
  · exact B823123
  · exact B823127
  · exact B823131
  · exact B823135
  · exact B823139
  · exact B823143
  · exact B823147
  · exact B823151
  · exact B823155
  · exact B823159
  · exact B823163
  · exact B823167
  · exact B823171
  · exact B823175
  · exact B823179
  · exact B823183
  · exact B823187
  · exact B823191
  · exact B823195
  · exact B823199
  · exact B823203
  · exact B823207
  · exact B823211
  · exact B823215
  · exact B823219
  · exact B823223
  · exact B823227
  · exact B823231
  · exact B823235
  · exact B823239
  · exact B823243
  · exact B823247
  · exact B823251
  · exact B823255
  · exact B823259
  · exact B823263
  · exact B823267
  · exact B823271
  · exact B823275
  · exact B823279
  · exact B823283
  · exact B823287
  · exact B823291
  · exact B823295
  · exact B823299
  · exact B823303
  · exact B823307
  · exact B823311
  · exact B823315
  · exact B823319
  · exact B823323
  · exact B823327
  · exact B823331
  · exact B823335
  · exact B823339
  · exact B823343
  · exact B823347
  · exact B823351
  · exact B823355
  · exact B823359
  · exact B823363
  · exact B823367
  · exact B823371
  · exact B823375
  · exact B823379
  · exact B823383
  · exact B823387
  · exact B823391
  · exact B823395
  · exact B823399
  · exact B823403
  · exact B823407
  · exact B823411
  · exact B823415
  · exact B823419
  · exact B823423
  · exact B823427
  · exact B823431
  · exact B823435
  · exact B823439
  · exact B823443
  · exact B823447
  · exact B823451
  · exact B823455
  · exact B823459
  · exact B823463
  · exact B823467
  · exact B823471
  · exact B823475
  · exact B823479
  · exact B823483
  · exact B823487
  · exact B823491
  · exact B823495
  · exact B823499
  · exact B823503
  · exact B823507
  · exact B823511
  · exact B823515
  · exact B823519
  · exact B823523
  · exact B823527
  · exact B823531
  · exact B823535
  · exact B823539
  · exact B823543
  · exact B823547
  · exact B823551
  · exact B823555
  · exact B823559
  · exact B823563
  · exact B823567
  · exact B823571
  · exact B823575
  · exact B823579
  · exact B823583
  · exact B823587
  · exact B823591
  · exact B823595
  · exact B823599
  · exact B823603
  · exact B823607
  · exact B823611
  · exact B823615
  · exact B823619
  · exact B823623
  · exact B823627
  · exact B823631
  · exact B823635
  · exact B823639
  · exact B823643
  · exact B823647
  · exact B823651
  · exact B823655
  · exact B823659
  · exact B823663
  · exact B823667
  · exact B823671
  · exact B823675
  · exact B823679
  · exact B823683
  · exact B823687
  · exact B823691
  · exact B823695
  · exact B823699
  · exact B823703
  · exact B823707
  · exact B823711
  · exact B823715
  · exact B823719
  · exact B823723
  · exact B823727
  · exact B823731
  · exact B823735
  · exact B823739
  · exact B823743
  · exact B823747
  · exact B823751
  · exact B823755
  · exact B823759
  · exact B823763
  · exact B823767
  · exact B823771
  · exact B823775
  · exact B823779
  · exact B823783
  · exact B823787
  · exact B823791
  · exact B823795
  · exact B823799
  · exact B823803
  · exact B823807
  · exact B823811
  · exact B823815
  · exact B823819
  · exact B823823
  · exact B823827
  · exact B823831
  · exact B823835
  · exact B823839
  · exact B823843
  · exact B823847
  · exact B823851
  · exact B823855
  · exact B823859
  · exact B823863
  · exact B823867
  · exact B823871
  · exact B823875
  · exact B823879
  · exact B823883
  · exact B823887
  · exact B823891
  · exact B823895
  · exact B823899
  · exact B823903
  · exact B823907
  · exact B823911
  · exact B823915
  · exact B823919
  · exact B823923
  · exact B823927
  · exact B823931
  · exact B823935
  · exact B823939
  · exact B823943
  · exact B823947
  · exact B823951
  · exact B823955
  · exact B823959
  · exact B823963
  · exact B823967
  · exact B823971
  · exact B823975
  · exact B823979
  · exact B823983
  · exact B823987
  · exact B823991
  · exact B823995
  · exact B823999
  · exact B824003
  · exact B824007
  · exact B824011
  · exact B824015
  · exact B824019
  · exact B824023
  · exact B824027
  · exact B824031
  · exact B824035
  · exact B824039
  · exact B824043
  · exact B824047
  · exact B824051
  · exact B824055
  · exact B824059
  · exact B824063
  · exact B824067
  · exact B824071
  · exact B824075
  · exact B824079
  · exact B824083
  · exact B824087
  · exact B824091
  · exact B824095
  · exact B824099
  · exact B824103
  · exact B824107
  · exact B824111
  · exact B824115
  · exact B824119
  · exact B824123
  · exact B824127
  · exact B824131
  · exact B824135
  · exact B824139
  · exact B824143
  · exact B824147
  · exact B824151
  · exact B824155
  · exact B824159
  · exact B824163
  · exact B824167
  · exact B824171
  · exact B824175
  · exact B824179
  · exact B824183
  · exact B824187
  · exact B824191
  · exact B824195
  · exact B824199
  · exact B824203
  · exact B824207
  · exact B824211
  · exact B824215
  · exact B824219
  · exact B824223
  · exact B824227
  · exact B824231
  · exact B824235
  · exact B824239
  · exact B824243
  · exact B824247
  · exact B824251
  · exact B824255
  · exact B824259
  · exact B824263
  · exact B824267
  · exact B824271
  · exact B824275
  · exact B824279
  · exact B824283
  · exact B824287
  · exact B824291
  · exact B824295
  · exact B824299
  · exact B824303
  · exact B824307
  · exact B824311
  · exact B824315
  · exact B824319
  · exact B824323
  · exact B824327
  · exact B824331
  · exact B824335
  · exact B824339
  · exact B824343
  · exact B824347
  · exact B824351
  · exact B824355
  · exact B824359
  · exact B824363
  · exact B824367
  · exact B824371
  · exact B824375
  · exact B824379
  · exact B824383
  · exact B824387
  · exact B824391
  · exact B824395
  · exact B824399
  · exact B824403
  · exact B824407
  · exact B824411
  · exact B824415
  · exact B824419
  · exact B824423
  · exact B824427
  · exact B824431
  · exact B824435
  · exact B824439
  · exact B824443
  · exact B824447
  · exact B824451
  · exact B824455
  · exact B824459
  · exact B824463
  · exact B824467
  · exact B824471
  · exact B824475
  · exact B824479
  · exact B824483
  · exact B824487
  · exact B824491
  · exact B824495
  · exact B824499
  · exact B824503
  · exact B824507
  · exact B824511
  · exact B824515
  · exact B824519
  · exact B824523
  · exact B824527
  · exact B824531
  · exact B824535
  · exact B824539
  · exact B824543
  · exact B824547
  · exact B824551
  · exact B824555
  · exact B824559
  · exact B824563
  · exact B824567
  · exact B824571
  · exact B824575
  · exact B824579
  · exact B824583
  · exact B824587
  · exact B824591
  · exact B824595
  · exact B824599
  · exact B824603
  · exact B824607
  · exact B824611
  · exact B824615
  · exact B824619
  · exact B824623
  · exact B824627
  · exact B824631
  · exact B824635
  · exact B824639
  · exact B824643
  · exact B824647
  · exact B824651
  · exact B824655
  · exact B824659
  · exact B824663
  · exact B824667
  · exact B824671
  · exact B824675
  · exact B824679
  · exact B824683
  · exact B824687
  · exact B824691
  · exact B824695
  · exact B824699
  · exact B824703
  · exact B824707
  · exact B824711
  · exact B824715
  · exact B824719
  · exact B824723
  · exact B824727
  · exact B824731
  · exact B824735
  · exact B824739
  · exact B824743
  · exact B824747
  · exact B824751
  · exact B824755
  · exact B824759
  · exact B824763
  · exact B824767
  · exact B824771
  · exact B824775
  · exact B824779
  · exact B824783
  · exact B824787
  · exact B824791
  · exact B824795
  · exact B824799
  · exact B824803
  · exact B824807
  · exact B824811
  · exact B824815
  · exact B824819
  · exact B824823
  · exact B824827
  · exact B824831
  · exact B824835
  · exact B824839
  · exact B824843
  · exact B824847
  · exact B824851
  · exact B824855
  · exact B824859
  · exact B824863
  · exact B824867
  · exact B824871
  · exact B824875
  · exact B824879
  · exact B824883
  · exact B824887
  · exact B824891
  · exact B824895
  · exact B824899
  · exact B824903
  · exact B824907
  · exact B824911
  · exact B824915
  · exact B824919
  · exact B824923
  · exact B824927
  · exact B824931
  · exact B824935
  · exact B824939
  · exact B824943
  · exact B824947
  · exact B824951
  · exact B824955
  · exact B824959
  · exact B824963
  · exact B824967
  · exact B824971
  · exact B824975
  · exact B824979
  · exact B824983
  · exact B824987
  · exact B824991
  · exact B824995
  · exact B824999
  · exact B825003
  · exact B825007
  · exact B825011
  · exact B825015
  · exact B825019
  · exact B825023
  · exact B825027
  · exact B825031
  · exact B825035
  · exact B825039
  · exact B825043
  · exact B825047
  · exact B825051
  · exact B825055
  · exact B825059
  · exact B825063
  · exact B825067
  · exact B825071
  · exact B825075
  · exact B825079
  · exact B825083
  · exact B825087
  · exact B825091
  · exact B825095
  · exact B825099
  · exact B825103
  · exact B825107
  · exact B825111
  · exact B825115
  · exact B825119
  · exact B825123
  · exact B825127
  · exact B825131
  · exact B825135
  · exact B825139
  · exact B825143
  · exact B825147

theorem C1 (j : ℕ) (h1 : 206287 ≤ j) (h2 : j ≤ 206586) : Blo 822348 (4 * j + 3) := by
  interval_cases j
  · exact B825151
  · exact B825155
  · exact B825159
  · exact B825163
  · exact B825167
  · exact B825171
  · exact B825175
  · exact B825179
  · exact B825183
  · exact B825187
  · exact B825191
  · exact B825195
  · exact B825199
  · exact B825203
  · exact B825207
  · exact B825211
  · exact B825215
  · exact B825219
  · exact B825223
  · exact B825227
  · exact B825231
  · exact B825235
  · exact B825239
  · exact B825243
  · exact B825247
  · exact B825251
  · exact B825255
  · exact B825259
  · exact B825263
  · exact B825267
  · exact B825271
  · exact B825275
  · exact B825279
  · exact B825283
  · exact B825287
  · exact B825291
  · exact B825295
  · exact B825299
  · exact B825303
  · exact B825307
  · exact B825311
  · exact B825315
  · exact B825319
  · exact B825323
  · exact B825327
  · exact B825331
  · exact B825335
  · exact B825339
  · exact B825343
  · exact B825347
  · exact B825351
  · exact B825355
  · exact B825359
  · exact B825363
  · exact B825367
  · exact B825371
  · exact B825375
  · exact B825379
  · exact B825383
  · exact B825387
  · exact B825391
  · exact B825395
  · exact B825399
  · exact B825403
  · exact B825407
  · exact B825411
  · exact B825415
  · exact B825419
  · exact B825423
  · exact B825427
  · exact B825431
  · exact B825435
  · exact B825439
  · exact B825443
  · exact B825447
  · exact B825451
  · exact B825455
  · exact B825459
  · exact B825463
  · exact B825467
  · exact B825471
  · exact B825475
  · exact B825479
  · exact B825483
  · exact B825487
  · exact B825491
  · exact B825495
  · exact B825499
  · exact B825503
  · exact B825507
  · exact B825511
  · exact B825515
  · exact B825519
  · exact B825523
  · exact B825527
  · exact B825531
  · exact B825535
  · exact B825539
  · exact B825543
  · exact B825547
  · exact B825551
  · exact B825555
  · exact B825559
  · exact B825563
  · exact B825567
  · exact B825571
  · exact B825575
  · exact B825579
  · exact B825583
  · exact B825587
  · exact B825591
  · exact B825595
  · exact B825599
  · exact B825603
  · exact B825607
  · exact B825611
  · exact B825615
  · exact B825619
  · exact B825623
  · exact B825627
  · exact B825631
  · exact B825635
  · exact B825639
  · exact B825643
  · exact B825647
  · exact B825651
  · exact B825655
  · exact B825659
  · exact B825663
  · exact B825667
  · exact B825671
  · exact B825675
  · exact B825679
  · exact B825683
  · exact B825687
  · exact B825691
  · exact B825695
  · exact B825699
  · exact B825703
  · exact B825707
  · exact B825711
  · exact B825715
  · exact B825719
  · exact B825723
  · exact B825727
  · exact B825731
  · exact B825735
  · exact B825739
  · exact B825743
  · exact B825747
  · exact B825751
  · exact B825755
  · exact B825759
  · exact B825763
  · exact B825767
  · exact B825771
  · exact B825775
  · exact B825779
  · exact B825783
  · exact B825787
  · exact B825791
  · exact B825795
  · exact B825799
  · exact B825803
  · exact B825807
  · exact B825811
  · exact B825815
  · exact B825819
  · exact B825823
  · exact B825827
  · exact B825831
  · exact B825835
  · exact B825839
  · exact B825843
  · exact B825847
  · exact B825851
  · exact B825855
  · exact B825859
  · exact B825863
  · exact B825867
  · exact B825871
  · exact B825875
  · exact B825879
  · exact B825883
  · exact B825887
  · exact B825891
  · exact B825895
  · exact B825899
  · exact B825903
  · exact B825907
  · exact B825911
  · exact B825915
  · exact B825919
  · exact B825923
  · exact B825927
  · exact B825931
  · exact B825935
  · exact B825939
  · exact B825943
  · exact B825947
  · exact B825951
  · exact B825955
  · exact B825959
  · exact B825963
  · exact B825967
  · exact B825971
  · exact B825975
  · exact B825979
  · exact B825983
  · exact B825987
  · exact B825991
  · exact B825995
  · exact B825999
  · exact B826003
  · exact B826007
  · exact B826011
  · exact B826015
  · exact B826019
  · exact B826023
  · exact B826027
  · exact B826031
  · exact B826035
  · exact B826039
  · exact B826043
  · exact B826047
  · exact B826051
  · exact B826055
  · exact B826059
  · exact B826063
  · exact B826067
  · exact B826071
  · exact B826075
  · exact B826079
  · exact B826083
  · exact B826087
  · exact B826091
  · exact B826095
  · exact B826099
  · exact B826103
  · exact B826107
  · exact B826111
  · exact B826115
  · exact B826119
  · exact B826123
  · exact B826127
  · exact B826131
  · exact B826135
  · exact B826139
  · exact B826143
  · exact B826147
  · exact B826151
  · exact B826155
  · exact B826159
  · exact B826163
  · exact B826167
  · exact B826171
  · exact B826175
  · exact B826179
  · exact B826183
  · exact B826187
  · exact B826191
  · exact B826195
  · exact B826199
  · exact B826203
  · exact B826207
  · exact B826211
  · exact B826215
  · exact B826219
  · exact B826223
  · exact B826227
  · exact B826231
  · exact B826235
  · exact B826239
  · exact B826243
  · exact B826247
  · exact B826251
  · exact B826255
  · exact B826259
  · exact B826263
  · exact B826267
  · exact B826271
  · exact B826275
  · exact B826279
  · exact B826283
  · exact B826287
  · exact B826291
  · exact B826295
  · exact B826299
  · exact B826303
  · exact B826307
  · exact B826311
  · exact B826315
  · exact B826319
  · exact B826323
  · exact B826327
  · exact B826331
  · exact B826335
  · exact B826339
  · exact B826343
  · exact B826347

theorem solution (m : ℕ) (hlo : 822348 ≤ m) (hhi : m ≤ 826348) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 205587 ≤ j := by omega
    have hj2 : j ≤ 206586 := by omega
    have hb : Blo 822348 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 206287 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
