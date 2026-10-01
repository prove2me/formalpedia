-- Prove2me | solution 1 for syracuse_descends_range_2219435_2221435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:38.041504+00:00
-- url     : https://prove2.me/submissions/e7682221-5d13-4054-b54f-c8d6dcf6e3b6

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

theorem B2496865 : Blo 2219435 2496865 := bbase (se 2 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 2496865 = 1872649) (by norm_num)
theorem B3329153 : Blo 2219435 3329153 := bstep (se 2 (by rfl) ⟨1248432, by rfl⟩ : syracuseStep 3329153 = 2496865) B2496865
theorem B2219435 : Blo 2219435 2219435 := bstep (se 1 (by rfl) ⟨1664576, by rfl⟩ : syracuseStep 2219435 = 3329153) B3329153
theorem B5617957 : Blo 2219435 5617957 := bbase (se 4 (by rfl) ⟨526683, by rfl⟩ : syracuseStep 5617957 = 1053367) (by norm_num)
theorem B7490609 : Blo 2219435 7490609 := bstep (se 2 (by rfl) ⟨2808978, by rfl⟩ : syracuseStep 7490609 = 5617957) B5617957
theorem B4993739 : Blo 2219435 4993739 := bstep (se 1 (by rfl) ⟨3745304, by rfl⟩ : syracuseStep 4993739 = 7490609) B7490609
theorem B3329159 : Blo 2219435 3329159 := bstep (se 1 (by rfl) ⟨2496869, by rfl⟩ : syracuseStep 3329159 = 4993739) B4993739
theorem B2219439 : Blo 2219435 2219439 := bstep (se 1 (by rfl) ⟨1664579, by rfl⟩ : syracuseStep 2219439 = 3329159) B3329159
theorem B3329165 : Blo 2219435 3329165 := bbase (se 3 (by rfl) ⟨624218, by rfl⟩ : syracuseStep 3329165 = 1248437) (by norm_num)
theorem B2219443 : Blo 2219435 2219443 := bstep (se 1 (by rfl) ⟨1664582, by rfl⟩ : syracuseStep 2219443 = 3329165) B3329165
theorem B4993757 : Blo 2219435 4993757 := bbase (se 3 (by rfl) ⟨936329, by rfl⟩ : syracuseStep 4993757 = 1872659) (by norm_num)
theorem B3329171 : Blo 2219435 3329171 := bstep (se 1 (by rfl) ⟨2496878, by rfl⟩ : syracuseStep 3329171 = 4993757) B4993757
theorem B2219447 : Blo 2219435 2219447 := bstep (se 1 (by rfl) ⟨1664585, by rfl⟩ : syracuseStep 2219447 = 3329171) B3329171
theorem B3745325 : Blo 2219435 3745325 := bbase (se 3 (by rfl) ⟨702248, by rfl⟩ : syracuseStep 3745325 = 1404497) (by norm_num)
theorem B2496883 : Blo 2219435 2496883 := bstep (se 1 (by rfl) ⟨1872662, by rfl⟩ : syracuseStep 2496883 = 3745325) B3745325
theorem B3329177 : Blo 2219435 3329177 := bstep (se 2 (by rfl) ⟨1248441, by rfl⟩ : syracuseStep 3329177 = 2496883) B2496883
theorem B2219451 : Blo 2219435 2219451 := bstep (se 1 (by rfl) ⟨1664588, by rfl⟩ : syracuseStep 2219451 = 3329177) B3329177
theorem B2402429 : Blo 2219435 2402429 := bbase (se 3 (by rfl) ⟨450455, by rfl⟩ : syracuseStep 2402429 = 900911) (by norm_num)
theorem B25625909 : Blo 2219435 25625909 := bstep (se 5 (by rfl) ⟨1201214, by rfl⟩ : syracuseStep 25625909 = 2402429) B2402429
theorem B17083939 : Blo 2219435 17083939 := bstep (se 1 (by rfl) ⟨12812954, by rfl⟩ : syracuseStep 17083939 = 25625909) B25625909
theorem B22778585 : Blo 2219435 22778585 := bstep (se 2 (by rfl) ⟨8541969, by rfl⟩ : syracuseStep 22778585 = 17083939) B17083939
theorem B15185723 : Blo 2219435 15185723 := bstep (se 1 (by rfl) ⟨11389292, by rfl⟩ : syracuseStep 15185723 = 22778585) B22778585
theorem B161981045 : Blo 2219435 161981045 := bstep (se 5 (by rfl) ⟨7592861, by rfl⟩ : syracuseStep 161981045 = 15185723) B15185723
theorem B107987363 : Blo 2219435 107987363 := bstep (se 1 (by rfl) ⟨80990522, by rfl⟩ : syracuseStep 107987363 = 161981045) B161981045
theorem B71991575 : Blo 2219435 71991575 := bstep (se 1 (by rfl) ⟨53993681, by rfl⟩ : syracuseStep 71991575 = 107987363) B107987363
theorem B47994383 : Blo 2219435 47994383 := bstep (se 1 (by rfl) ⟨35995787, by rfl⟩ : syracuseStep 47994383 = 71991575) B71991575
theorem B31996255 : Blo 2219435 31996255 := bstep (se 1 (by rfl) ⟨23997191, by rfl⟩ : syracuseStep 31996255 = 47994383) B47994383
theorem B42661673 : Blo 2219435 42661673 := bstep (se 2 (by rfl) ⟨15998127, by rfl⟩ : syracuseStep 42661673 = 31996255) B31996255
theorem B28441115 : Blo 2219435 28441115 := bstep (se 1 (by rfl) ⟨21330836, by rfl⟩ : syracuseStep 28441115 = 42661673) B42661673
theorem B18960743 : Blo 2219435 18960743 := bstep (se 1 (by rfl) ⟨14220557, by rfl⟩ : syracuseStep 18960743 = 28441115) B28441115
theorem B12640495 : Blo 2219435 12640495 := bstep (se 1 (by rfl) ⟨9480371, by rfl⟩ : syracuseStep 12640495 = 18960743) B18960743
theorem B16853993 : Blo 2219435 16853993 := bstep (se 2 (by rfl) ⟨6320247, by rfl⟩ : syracuseStep 16853993 = 12640495) B12640495
theorem B11235995 : Blo 2219435 11235995 := bstep (se 1 (by rfl) ⟨8426996, by rfl⟩ : syracuseStep 11235995 = 16853993) B16853993
theorem B7490663 : Blo 2219435 7490663 := bstep (se 1 (by rfl) ⟨5617997, by rfl⟩ : syracuseStep 7490663 = 11235995) B11235995
theorem B4993775 : Blo 2219435 4993775 := bstep (se 1 (by rfl) ⟨3745331, by rfl⟩ : syracuseStep 4993775 = 7490663) B7490663
theorem B3329183 : Blo 2219435 3329183 := bstep (se 1 (by rfl) ⟨2496887, by rfl⟩ : syracuseStep 3329183 = 4993775) B4993775
theorem B2219455 : Blo 2219435 2219455 := bstep (se 1 (by rfl) ⟨1664591, by rfl⟩ : syracuseStep 2219455 = 3329183) B3329183
theorem B3329189 : Blo 2219435 3329189 := bbase (se 4 (by rfl) ⟨312111, by rfl⟩ : syracuseStep 3329189 = 624223) (by norm_num)
theorem B2219459 : Blo 2219435 2219459 := bstep (se 1 (by rfl) ⟨1664594, by rfl⟩ : syracuseStep 2219459 = 3329189) B3329189
theorem B2809009 : Blo 2219435 2809009 := bbase (se 2 (by rfl) ⟨1053378, by rfl⟩ : syracuseStep 2809009 = 2106757) (by norm_num)
theorem B3745345 : Blo 2219435 3745345 := bstep (se 2 (by rfl) ⟨1404504, by rfl⟩ : syracuseStep 3745345 = 2809009) B2809009
theorem B4993793 : Blo 2219435 4993793 := bstep (se 2 (by rfl) ⟨1872672, by rfl⟩ : syracuseStep 4993793 = 3745345) B3745345
theorem B3329195 : Blo 2219435 3329195 := bstep (se 1 (by rfl) ⟨2496896, by rfl⟩ : syracuseStep 3329195 = 4993793) B4993793
theorem B2219463 : Blo 2219435 2219463 := bstep (se 1 (by rfl) ⟨1664597, by rfl⟩ : syracuseStep 2219463 = 3329195) B3329195
theorem B2496901 : Blo 2219435 2496901 := bbase (se 4 (by rfl) ⟨234084, by rfl⟩ : syracuseStep 2496901 = 468169) (by norm_num)
theorem B3329201 : Blo 2219435 3329201 := bstep (se 2 (by rfl) ⟨1248450, by rfl⟩ : syracuseStep 3329201 = 2496901) B2496901
theorem B2219467 : Blo 2219435 2219467 := bstep (se 1 (by rfl) ⟨1664600, by rfl⟩ : syracuseStep 2219467 = 3329201) B3329201
theorem B4740221 : Blo 2219435 4740221 := bbase (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) (by norm_num)
theorem B3160147 : Blo 2219435 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B4213529 : Blo 2219435 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B2809019 : Blo 2219435 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B7490717 : Blo 2219435 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B4993811 : Blo 2219435 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B3329207 : Blo 2219435 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B2219471 : Blo 2219435 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B3329213 : Blo 2219435 3329213 := bbase (se 3 (by rfl) ⟨624227, by rfl⟩ : syracuseStep 3329213 = 1248455) (by norm_num)
theorem B2219475 : Blo 2219435 2219475 := bstep (se 1 (by rfl) ⟨1664606, by rfl⟩ : syracuseStep 2219475 = 3329213) B3329213
theorem B4993829 : Blo 2219435 4993829 := bbase (se 4 (by rfl) ⟨468171, by rfl⟩ : syracuseStep 4993829 = 936343) (by norm_num)
theorem B3329219 : Blo 2219435 3329219 := bstep (se 1 (by rfl) ⟨2496914, by rfl⟩ : syracuseStep 3329219 = 4993829) B4993829
theorem B2219479 : Blo 2219435 2219479 := bstep (se 1 (by rfl) ⟨1664609, by rfl⟩ : syracuseStep 2219479 = 3329219) B3329219
theorem B5618069 : Blo 2219435 5618069 := bbase (se 6 (by rfl) ⟨131673, by rfl⟩ : syracuseStep 5618069 = 263347) (by norm_num)
theorem B3745379 : Blo 2219435 3745379 := bstep (se 1 (by rfl) ⟨2809034, by rfl⟩ : syracuseStep 3745379 = 5618069) B5618069
theorem B2496919 : Blo 2219435 2496919 := bstep (se 1 (by rfl) ⟨1872689, by rfl⟩ : syracuseStep 2496919 = 3745379) B3745379
theorem B3329225 : Blo 2219435 3329225 := bstep (se 2 (by rfl) ⟨1248459, by rfl⟩ : syracuseStep 3329225 = 2496919) B2496919
theorem B2219483 : Blo 2219435 2219483 := bstep (se 1 (by rfl) ⟨1664612, by rfl⟩ : syracuseStep 2219483 = 3329225) B3329225
theorem B2999693 : Blo 2219435 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B7999181 : Blo 2219435 7999181 := bstep (se 3 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 7999181 = 2999693) B2999693
theorem B5332787 : Blo 2219435 5332787 := bstep (se 1 (by rfl) ⟨3999590, by rfl⟩ : syracuseStep 5332787 = 7999181) B7999181
theorem B3555191 : Blo 2219435 3555191 := bstep (se 1 (by rfl) ⟨2666393, by rfl⟩ : syracuseStep 3555191 = 5332787) B5332787
theorem B9480509 : Blo 2219435 9480509 := bstep (se 3 (by rfl) ⟨1777595, by rfl⟩ : syracuseStep 9480509 = 3555191) B3555191
theorem B6320339 : Blo 2219435 6320339 := bstep (se 1 (by rfl) ⟨4740254, by rfl⟩ : syracuseStep 6320339 = 9480509) B9480509
theorem B4213559 : Blo 2219435 4213559 := bstep (se 1 (by rfl) ⟨3160169, by rfl⟩ : syracuseStep 4213559 = 6320339) B6320339
theorem B11236157 : Blo 2219435 11236157 := bstep (se 3 (by rfl) ⟨2106779, by rfl⟩ : syracuseStep 11236157 = 4213559) B4213559
theorem B7490771 : Blo 2219435 7490771 := bstep (se 1 (by rfl) ⟨5618078, by rfl⟩ : syracuseStep 7490771 = 11236157) B11236157
theorem B4993847 : Blo 2219435 4993847 := bstep (se 1 (by rfl) ⟨3745385, by rfl⟩ : syracuseStep 4993847 = 7490771) B7490771
theorem B3329231 : Blo 2219435 3329231 := bstep (se 1 (by rfl) ⟨2496923, by rfl⟩ : syracuseStep 3329231 = 4993847) B4993847
theorem B2219487 : Blo 2219435 2219487 := bstep (se 1 (by rfl) ⟨1664615, by rfl⟩ : syracuseStep 2219487 = 3329231) B3329231
theorem B3329237 : Blo 2219435 3329237 := bbase (se 7 (by rfl) ⟨39014, by rfl⟩ : syracuseStep 3329237 = 78029) (by norm_num)
theorem B2219491 : Blo 2219435 2219491 := bstep (se 1 (by rfl) ⟨1664618, by rfl⟩ : syracuseStep 2219491 = 3329237) B3329237
theorem B3160181 : Blo 2219435 3160181 := bbase (se 5 (by rfl) ⟨148133, by rfl⟩ : syracuseStep 3160181 = 296267) (by norm_num)
theorem B8427149 : Blo 2219435 8427149 := bstep (se 3 (by rfl) ⟨1580090, by rfl⟩ : syracuseStep 8427149 = 3160181) B3160181
theorem B5618099 : Blo 2219435 5618099 := bstep (se 1 (by rfl) ⟨4213574, by rfl⟩ : syracuseStep 5618099 = 8427149) B8427149
theorem B3745399 : Blo 2219435 3745399 := bstep (se 1 (by rfl) ⟨2809049, by rfl⟩ : syracuseStep 3745399 = 5618099) B5618099
theorem B4993865 : Blo 2219435 4993865 := bstep (se 2 (by rfl) ⟨1872699, by rfl⟩ : syracuseStep 4993865 = 3745399) B3745399
theorem B3329243 : Blo 2219435 3329243 := bstep (se 1 (by rfl) ⟨2496932, by rfl⟩ : syracuseStep 3329243 = 4993865) B4993865
theorem B2219495 : Blo 2219435 2219495 := bstep (se 1 (by rfl) ⟨1664621, by rfl⟩ : syracuseStep 2219495 = 3329243) B3329243
theorem B2496937 : Blo 2219435 2496937 := bbase (se 2 (by rfl) ⟨936351, by rfl⟩ : syracuseStep 2496937 = 1872703) (by norm_num)
theorem B3329249 : Blo 2219435 3329249 := bstep (se 2 (by rfl) ⟨1248468, by rfl⟩ : syracuseStep 3329249 = 2496937) B2496937
theorem B2219499 : Blo 2219435 2219499 := bstep (se 1 (by rfl) ⟨1664624, by rfl⟩ : syracuseStep 2219499 = 3329249) B3329249
theorem B5999429 : Blo 2219435 5999429 := bbase (se 4 (by rfl) ⟨562446, by rfl⟩ : syracuseStep 5999429 = 1124893) (by norm_num)
theorem B3999619 : Blo 2219435 3999619 := bstep (se 1 (by rfl) ⟨2999714, by rfl⟩ : syracuseStep 3999619 = 5999429) B5999429
theorem B5332825 : Blo 2219435 5332825 := bstep (se 2 (by rfl) ⟨1999809, by rfl⟩ : syracuseStep 5332825 = 3999619) B3999619
theorem B7110433 : Blo 2219435 7110433 := bstep (se 2 (by rfl) ⟨2666412, by rfl⟩ : syracuseStep 7110433 = 5332825) B5332825
theorem B9480577 : Blo 2219435 9480577 := bstep (se 2 (by rfl) ⟨3555216, by rfl⟩ : syracuseStep 9480577 = 7110433) B7110433
theorem B12640769 : Blo 2219435 12640769 := bstep (se 2 (by rfl) ⟨4740288, by rfl⟩ : syracuseStep 12640769 = 9480577) B9480577
theorem B8427179 : Blo 2219435 8427179 := bstep (se 1 (by rfl) ⟨6320384, by rfl⟩ : syracuseStep 8427179 = 12640769) B12640769
theorem B5618119 : Blo 2219435 5618119 := bstep (se 1 (by rfl) ⟨4213589, by rfl⟩ : syracuseStep 5618119 = 8427179) B8427179
theorem B7490825 : Blo 2219435 7490825 := bstep (se 2 (by rfl) ⟨2809059, by rfl⟩ : syracuseStep 7490825 = 5618119) B5618119
theorem B4993883 : Blo 2219435 4993883 := bstep (se 1 (by rfl) ⟨3745412, by rfl⟩ : syracuseStep 4993883 = 7490825) B7490825
theorem B3329255 : Blo 2219435 3329255 := bstep (se 1 (by rfl) ⟨2496941, by rfl⟩ : syracuseStep 3329255 = 4993883) B4993883
theorem B2219503 : Blo 2219435 2219503 := bstep (se 1 (by rfl) ⟨1664627, by rfl⟩ : syracuseStep 2219503 = 3329255) B3329255
theorem B3329261 : Blo 2219435 3329261 := bbase (se 3 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 3329261 = 1248473) (by norm_num)
theorem B2219507 : Blo 2219435 2219507 := bstep (se 1 (by rfl) ⟨1664630, by rfl⟩ : syracuseStep 2219507 = 3329261) B3329261
theorem B4993901 : Blo 2219435 4993901 := bbase (se 3 (by rfl) ⟨936356, by rfl⟩ : syracuseStep 4993901 = 1872713) (by norm_num)
theorem B3329267 : Blo 2219435 3329267 := bstep (se 1 (by rfl) ⟨2496950, by rfl⟩ : syracuseStep 3329267 = 4993901) B4993901
theorem B2219511 : Blo 2219435 2219511 := bstep (se 1 (by rfl) ⟨1664633, by rfl⟩ : syracuseStep 2219511 = 3329267) B3329267
theorem B4213613 : Blo 2219435 4213613 := bbase (se 3 (by rfl) ⟨790052, by rfl⟩ : syracuseStep 4213613 = 1580105) (by norm_num)
theorem B2809075 : Blo 2219435 2809075 := bstep (se 1 (by rfl) ⟨2106806, by rfl⟩ : syracuseStep 2809075 = 4213613) B4213613
theorem B3745433 : Blo 2219435 3745433 := bstep (se 2 (by rfl) ⟨1404537, by rfl⟩ : syracuseStep 3745433 = 2809075) B2809075
theorem B2496955 : Blo 2219435 2496955 := bstep (se 1 (by rfl) ⟨1872716, by rfl⟩ : syracuseStep 2496955 = 3745433) B3745433
theorem B3329273 : Blo 2219435 3329273 := bstep (se 2 (by rfl) ⟨1248477, by rfl⟩ : syracuseStep 3329273 = 2496955) B2496955
theorem B2219515 : Blo 2219435 2219515 := bstep (se 1 (by rfl) ⟨1664636, by rfl⟩ : syracuseStep 2219515 = 3329273) B3329273
theorem B11389621 : Blo 2219435 11389621 := bbase (se 5 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 11389621 = 1067777) (by norm_num)
theorem B15186161 : Blo 2219435 15186161 := bstep (se 2 (by rfl) ⟨5694810, by rfl⟩ : syracuseStep 15186161 = 11389621) B11389621
theorem B40496429 : Blo 2219435 40496429 := bstep (se 3 (by rfl) ⟨7593080, by rfl⟩ : syracuseStep 40496429 = 15186161) B15186161
theorem B26997619 : Blo 2219435 26997619 := bstep (se 1 (by rfl) ⟨20248214, by rfl⟩ : syracuseStep 26997619 = 40496429) B40496429
theorem B35996825 : Blo 2219435 35996825 := bstep (se 2 (by rfl) ⟨13498809, by rfl⟩ : syracuseStep 35996825 = 26997619) B26997619
theorem B23997883 : Blo 2219435 23997883 := bstep (se 1 (by rfl) ⟨17998412, by rfl⟩ : syracuseStep 23997883 = 35996825) B35996825
theorem B31997177 : Blo 2219435 31997177 := bstep (se 2 (by rfl) ⟨11998941, by rfl⟩ : syracuseStep 31997177 = 23997883) B23997883
theorem B21331451 : Blo 2219435 21331451 := bstep (se 1 (by rfl) ⟨15998588, by rfl⟩ : syracuseStep 21331451 = 31997177) B31997177
theorem B56883869 : Blo 2219435 56883869 := bstep (se 3 (by rfl) ⟨10665725, by rfl⟩ : syracuseStep 56883869 = 21331451) B21331451
theorem B37922579 : Blo 2219435 37922579 := bstep (se 1 (by rfl) ⟨28441934, by rfl⟩ : syracuseStep 37922579 = 56883869) B56883869
theorem B25281719 : Blo 2219435 25281719 := bstep (se 1 (by rfl) ⟨18961289, by rfl⟩ : syracuseStep 25281719 = 37922579) B37922579
theorem B16854479 : Blo 2219435 16854479 := bstep (se 1 (by rfl) ⟨12640859, by rfl⟩ : syracuseStep 16854479 = 25281719) B25281719
theorem B11236319 : Blo 2219435 11236319 := bstep (se 1 (by rfl) ⟨8427239, by rfl⟩ : syracuseStep 11236319 = 16854479) B16854479
theorem B7490879 : Blo 2219435 7490879 := bstep (se 1 (by rfl) ⟨5618159, by rfl⟩ : syracuseStep 7490879 = 11236319) B11236319
theorem B4993919 : Blo 2219435 4993919 := bstep (se 1 (by rfl) ⟨3745439, by rfl⟩ : syracuseStep 4993919 = 7490879) B7490879
theorem B3329279 : Blo 2219435 3329279 := bstep (se 1 (by rfl) ⟨2496959, by rfl⟩ : syracuseStep 3329279 = 4993919) B4993919
theorem B2219519 : Blo 2219435 2219519 := bstep (se 1 (by rfl) ⟨1664639, by rfl⟩ : syracuseStep 2219519 = 3329279) B3329279
theorem B3329285 : Blo 2219435 3329285 := bbase (se 4 (by rfl) ⟨312120, by rfl⟩ : syracuseStep 3329285 = 624241) (by norm_num)
theorem B2219523 : Blo 2219435 2219523 := bstep (se 1 (by rfl) ⟨1664642, by rfl⟩ : syracuseStep 2219523 = 3329285) B3329285
theorem B3745453 : Blo 2219435 3745453 := bbase (se 3 (by rfl) ⟨702272, by rfl⟩ : syracuseStep 3745453 = 1404545) (by norm_num)
theorem B4993937 : Blo 2219435 4993937 := bstep (se 2 (by rfl) ⟨1872726, by rfl⟩ : syracuseStep 4993937 = 3745453) B3745453
theorem B3329291 : Blo 2219435 3329291 := bstep (se 1 (by rfl) ⟨2496968, by rfl⟩ : syracuseStep 3329291 = 4993937) B4993937
theorem B2219527 : Blo 2219435 2219527 := bstep (se 1 (by rfl) ⟨1664645, by rfl⟩ : syracuseStep 2219527 = 3329291) B3329291
theorem B2496973 : Blo 2219435 2496973 := bbase (se 3 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 2496973 = 936365) (by norm_num)
theorem B3329297 : Blo 2219435 3329297 := bstep (se 2 (by rfl) ⟨1248486, by rfl⟩ : syracuseStep 3329297 = 2496973) B2496973
theorem B2219531 : Blo 2219435 2219531 := bstep (se 1 (by rfl) ⟨1664648, by rfl⟩ : syracuseStep 2219531 = 3329297) B3329297
theorem B7490933 : Blo 2219435 7490933 := bbase (se 5 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 7490933 = 702275) (by norm_num)
theorem B4993955 : Blo 2219435 4993955 := bstep (se 1 (by rfl) ⟨3745466, by rfl⟩ : syracuseStep 4993955 = 7490933) B7490933
theorem B3329303 : Blo 2219435 3329303 := bstep (se 1 (by rfl) ⟨2496977, by rfl⟩ : syracuseStep 3329303 = 4993955) B4993955
theorem B2219535 : Blo 2219435 2219535 := bstep (se 1 (by rfl) ⟨1664651, by rfl⟩ : syracuseStep 2219535 = 3329303) B3329303
theorem B3329309 : Blo 2219435 3329309 := bbase (se 3 (by rfl) ⟨624245, by rfl⟩ : syracuseStep 3329309 = 1248491) (by norm_num)
theorem B2219539 : Blo 2219435 2219539 := bstep (se 1 (by rfl) ⟨1664654, by rfl⟩ : syracuseStep 2219539 = 3329309) B3329309
theorem B4993973 : Blo 2219435 4993973 := bbase (se 5 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 4993973 = 468185) (by norm_num)
theorem B3329315 : Blo 2219435 3329315 := bstep (se 1 (by rfl) ⟨2496986, by rfl⟩ : syracuseStep 3329315 = 4993973) B4993973
theorem B2219543 : Blo 2219435 2219543 := bstep (se 1 (by rfl) ⟨1664657, by rfl⟩ : syracuseStep 2219543 = 3329315) B3329315
theorem B17998645 : Blo 2219435 17998645 := bbase (se 5 (by rfl) ⟨843686, by rfl⟩ : syracuseStep 17998645 = 1687373) (by norm_num)
theorem B23998193 : Blo 2219435 23998193 := bstep (se 2 (by rfl) ⟨8999322, by rfl⟩ : syracuseStep 23998193 = 17998645) B17998645
theorem B15998795 : Blo 2219435 15998795 := bstep (se 1 (by rfl) ⟨11999096, by rfl⟩ : syracuseStep 15998795 = 23998193) B23998193
theorem B10665863 : Blo 2219435 10665863 := bstep (se 1 (by rfl) ⟨7999397, by rfl⟩ : syracuseStep 10665863 = 15998795) B15998795
theorem B7110575 : Blo 2219435 7110575 := bstep (se 1 (by rfl) ⟨5332931, by rfl⟩ : syracuseStep 7110575 = 10665863) B10665863
theorem B4740383 : Blo 2219435 4740383 := bstep (se 1 (by rfl) ⟨3555287, by rfl⟩ : syracuseStep 4740383 = 7110575) B7110575
theorem B12641021 : Blo 2219435 12641021 := bstep (se 3 (by rfl) ⟨2370191, by rfl⟩ : syracuseStep 12641021 = 4740383) B4740383
theorem B8427347 : Blo 2219435 8427347 := bstep (se 1 (by rfl) ⟨6320510, by rfl⟩ : syracuseStep 8427347 = 12641021) B12641021
theorem B5618231 : Blo 2219435 5618231 := bstep (se 1 (by rfl) ⟨4213673, by rfl⟩ : syracuseStep 5618231 = 8427347) B8427347
theorem B3745487 : Blo 2219435 3745487 := bstep (se 1 (by rfl) ⟨2809115, by rfl⟩ : syracuseStep 3745487 = 5618231) B5618231
theorem B2496991 : Blo 2219435 2496991 := bstep (se 1 (by rfl) ⟨1872743, by rfl⟩ : syracuseStep 2496991 = 3745487) B3745487
theorem B3329321 : Blo 2219435 3329321 := bstep (se 2 (by rfl) ⟨1248495, by rfl⟩ : syracuseStep 3329321 = 2496991) B2496991
theorem B2219547 : Blo 2219435 2219547 := bstep (se 1 (by rfl) ⟨1664660, by rfl⟩ : syracuseStep 2219547 = 3329321) B3329321
theorem B4499669 : Blo 2219435 4499669 := bbase (se 7 (by rfl) ⟨52730, by rfl⟩ : syracuseStep 4499669 = 105461) (by norm_num)
theorem B11999117 : Blo 2219435 11999117 := bstep (se 3 (by rfl) ⟨2249834, by rfl⟩ : syracuseStep 11999117 = 4499669) B4499669
theorem B7999411 : Blo 2219435 7999411 := bstep (se 1 (by rfl) ⟨5999558, by rfl⟩ : syracuseStep 7999411 = 11999117) B11999117
theorem B10665881 : Blo 2219435 10665881 := bstep (se 2 (by rfl) ⟨3999705, by rfl⟩ : syracuseStep 10665881 = 7999411) B7999411
theorem B7110587 : Blo 2219435 7110587 := bstep (se 1 (by rfl) ⟨5332940, by rfl⟩ : syracuseStep 7110587 = 10665881) B10665881
theorem B4740391 : Blo 2219435 4740391 := bstep (se 1 (by rfl) ⟨3555293, by rfl⟩ : syracuseStep 4740391 = 7110587) B7110587
theorem B6320521 : Blo 2219435 6320521 := bstep (se 2 (by rfl) ⟨2370195, by rfl⟩ : syracuseStep 6320521 = 4740391) B4740391
theorem B8427361 : Blo 2219435 8427361 := bstep (se 2 (by rfl) ⟨3160260, by rfl⟩ : syracuseStep 8427361 = 6320521) B6320521
theorem B11236481 : Blo 2219435 11236481 := bstep (se 2 (by rfl) ⟨4213680, by rfl⟩ : syracuseStep 11236481 = 8427361) B8427361
theorem B7490987 : Blo 2219435 7490987 := bstep (se 1 (by rfl) ⟨5618240, by rfl⟩ : syracuseStep 7490987 = 11236481) B11236481
theorem B4993991 : Blo 2219435 4993991 := bstep (se 1 (by rfl) ⟨3745493, by rfl⟩ : syracuseStep 4993991 = 7490987) B7490987
theorem B3329327 : Blo 2219435 3329327 := bstep (se 1 (by rfl) ⟨2496995, by rfl⟩ : syracuseStep 3329327 = 4993991) B4993991
theorem B2219551 : Blo 2219435 2219551 := bstep (se 1 (by rfl) ⟨1664663, by rfl⟩ : syracuseStep 2219551 = 3329327) B3329327
theorem B3329333 : Blo 2219435 3329333 := bbase (se 5 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 3329333 = 312125) (by norm_num)
theorem B2219555 : Blo 2219435 2219555 := bstep (se 1 (by rfl) ⟨1664666, by rfl⟩ : syracuseStep 2219555 = 3329333) B3329333
theorem B5618261 : Blo 2219435 5618261 := bbase (se 8 (by rfl) ⟨32919, by rfl⟩ : syracuseStep 5618261 = 65839) (by norm_num)
theorem B3745507 : Blo 2219435 3745507 := bstep (se 1 (by rfl) ⟨2809130, by rfl⟩ : syracuseStep 3745507 = 5618261) B5618261
theorem B4994009 : Blo 2219435 4994009 := bstep (se 2 (by rfl) ⟨1872753, by rfl⟩ : syracuseStep 4994009 = 3745507) B3745507
theorem B3329339 : Blo 2219435 3329339 := bstep (se 1 (by rfl) ⟨2497004, by rfl⟩ : syracuseStep 3329339 = 4994009) B4994009
theorem B2219559 : Blo 2219435 2219559 := bstep (se 1 (by rfl) ⟨1664669, by rfl⟩ : syracuseStep 2219559 = 3329339) B3329339
theorem B2497009 : Blo 2219435 2497009 := bbase (se 2 (by rfl) ⟨936378, by rfl⟩ : syracuseStep 2497009 = 1872757) (by norm_num)
theorem B3329345 : Blo 2219435 3329345 := bstep (se 2 (by rfl) ⟨1248504, by rfl⟩ : syracuseStep 3329345 = 2497009) B2497009
theorem B2219563 : Blo 2219435 2219563 := bstep (se 1 (by rfl) ⟨1664672, by rfl⟩ : syracuseStep 2219563 = 3329345) B3329345
theorem B2847469 : Blo 2219435 2847469 := bbase (se 3 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 2847469 = 1067801) (by norm_num)
theorem B3796625 : Blo 2219435 3796625 := bstep (se 2 (by rfl) ⟨1423734, by rfl⟩ : syracuseStep 3796625 = 2847469) B2847469
theorem B2531083 : Blo 2219435 2531083 := bstep (se 1 (by rfl) ⟨1898312, by rfl⟩ : syracuseStep 2531083 = 3796625) B3796625
theorem B3374777 : Blo 2219435 3374777 := bstep (se 2 (by rfl) ⟨1265541, by rfl⟩ : syracuseStep 3374777 = 2531083) B2531083
theorem B2249851 : Blo 2219435 2249851 := bstep (se 1 (by rfl) ⟨1687388, by rfl⟩ : syracuseStep 2249851 = 3374777) B3374777
theorem B2999801 : Blo 2219435 2999801 := bstep (se 2 (by rfl) ⟨1124925, by rfl⟩ : syracuseStep 2999801 = 2249851) B2249851
theorem B7999469 : Blo 2219435 7999469 := bstep (se 3 (by rfl) ⟨1499900, by rfl⟩ : syracuseStep 7999469 = 2999801) B2999801
theorem B5332979 : Blo 2219435 5332979 := bstep (se 1 (by rfl) ⟨3999734, by rfl⟩ : syracuseStep 5332979 = 7999469) B7999469
theorem B14221277 : Blo 2219435 14221277 := bstep (se 3 (by rfl) ⟨2666489, by rfl⟩ : syracuseStep 14221277 = 5332979) B5332979
theorem B9480851 : Blo 2219435 9480851 := bstep (se 1 (by rfl) ⟨7110638, by rfl⟩ : syracuseStep 9480851 = 14221277) B14221277
theorem B6320567 : Blo 2219435 6320567 := bstep (se 1 (by rfl) ⟨4740425, by rfl⟩ : syracuseStep 6320567 = 9480851) B9480851
theorem B4213711 : Blo 2219435 4213711 := bstep (se 1 (by rfl) ⟨3160283, by rfl⟩ : syracuseStep 4213711 = 6320567) B6320567
theorem B5618281 : Blo 2219435 5618281 := bstep (se 2 (by rfl) ⟨2106855, by rfl⟩ : syracuseStep 5618281 = 4213711) B4213711
theorem B7491041 : Blo 2219435 7491041 := bstep (se 2 (by rfl) ⟨2809140, by rfl⟩ : syracuseStep 7491041 = 5618281) B5618281
theorem B4994027 : Blo 2219435 4994027 := bstep (se 1 (by rfl) ⟨3745520, by rfl⟩ : syracuseStep 4994027 = 7491041) B7491041
theorem B3329351 : Blo 2219435 3329351 := bstep (se 1 (by rfl) ⟨2497013, by rfl⟩ : syracuseStep 3329351 = 4994027) B4994027
theorem B2219567 : Blo 2219435 2219567 := bstep (se 1 (by rfl) ⟨1664675, by rfl⟩ : syracuseStep 2219567 = 3329351) B3329351
theorem B3329357 : Blo 2219435 3329357 := bbase (se 3 (by rfl) ⟨624254, by rfl⟩ : syracuseStep 3329357 = 1248509) (by norm_num)
theorem B2219571 : Blo 2219435 2219571 := bstep (se 1 (by rfl) ⟨1664678, by rfl⟩ : syracuseStep 2219571 = 3329357) B3329357
theorem B4994045 : Blo 2219435 4994045 := bbase (se 3 (by rfl) ⟨936383, by rfl⟩ : syracuseStep 4994045 = 1872767) (by norm_num)
theorem B3329363 : Blo 2219435 3329363 := bstep (se 1 (by rfl) ⟨2497022, by rfl⟩ : syracuseStep 3329363 = 4994045) B4994045
theorem B2219575 : Blo 2219435 2219575 := bstep (se 1 (by rfl) ⟨1664681, by rfl⟩ : syracuseStep 2219575 = 3329363) B3329363
theorem B3745541 : Blo 2219435 3745541 := bbase (se 4 (by rfl) ⟨351144, by rfl⟩ : syracuseStep 3745541 = 702289) (by norm_num)
theorem B2497027 : Blo 2219435 2497027 := bstep (se 1 (by rfl) ⟨1872770, by rfl⟩ : syracuseStep 2497027 = 3745541) B3745541
theorem B3329369 : Blo 2219435 3329369 := bstep (se 2 (by rfl) ⟨1248513, by rfl⟩ : syracuseStep 3329369 = 2497027) B2497027
theorem B2219579 : Blo 2219435 2219579 := bstep (se 1 (by rfl) ⟨1664684, by rfl⟩ : syracuseStep 2219579 = 3329369) B3329369
theorem B16854965 : Blo 2219435 16854965 := bbase (se 5 (by rfl) ⟨790076, by rfl⟩ : syracuseStep 16854965 = 1580153) (by norm_num)
theorem B11236643 : Blo 2219435 11236643 := bstep (se 1 (by rfl) ⟨8427482, by rfl⟩ : syracuseStep 11236643 = 16854965) B16854965
theorem B7491095 : Blo 2219435 7491095 := bstep (se 1 (by rfl) ⟨5618321, by rfl⟩ : syracuseStep 7491095 = 11236643) B11236643
theorem B4994063 : Blo 2219435 4994063 := bstep (se 1 (by rfl) ⟨3745547, by rfl⟩ : syracuseStep 4994063 = 7491095) B7491095
theorem B3329375 : Blo 2219435 3329375 := bstep (se 1 (by rfl) ⟨2497031, by rfl⟩ : syracuseStep 3329375 = 4994063) B4994063
theorem B2219583 : Blo 2219435 2219583 := bstep (se 1 (by rfl) ⟨1664687, by rfl⟩ : syracuseStep 2219583 = 3329375) B3329375
theorem B3329381 : Blo 2219435 3329381 := bbase (se 4 (by rfl) ⟨312129, by rfl⟩ : syracuseStep 3329381 = 624259) (by norm_num)
theorem B2219587 : Blo 2219435 2219587 := bstep (se 1 (by rfl) ⟨1664690, by rfl⟩ : syracuseStep 2219587 = 3329381) B3329381
theorem B4213757 : Blo 2219435 4213757 := bbase (se 3 (by rfl) ⟨790079, by rfl⟩ : syracuseStep 4213757 = 1580159) (by norm_num)
theorem B2809171 : Blo 2219435 2809171 := bstep (se 1 (by rfl) ⟨2106878, by rfl⟩ : syracuseStep 2809171 = 4213757) B4213757
theorem B3745561 : Blo 2219435 3745561 := bstep (se 2 (by rfl) ⟨1404585, by rfl⟩ : syracuseStep 3745561 = 2809171) B2809171
theorem B4994081 : Blo 2219435 4994081 := bstep (se 2 (by rfl) ⟨1872780, by rfl⟩ : syracuseStep 4994081 = 3745561) B3745561
theorem B3329387 : Blo 2219435 3329387 := bstep (se 1 (by rfl) ⟨2497040, by rfl⟩ : syracuseStep 3329387 = 4994081) B4994081
theorem B2219591 : Blo 2219435 2219591 := bstep (se 1 (by rfl) ⟨1664693, by rfl⟩ : syracuseStep 2219591 = 3329387) B3329387
theorem B2497045 : Blo 2219435 2497045 := bbase (se 6 (by rfl) ⟨58524, by rfl⟩ : syracuseStep 2497045 = 117049) (by norm_num)
theorem B3329393 : Blo 2219435 3329393 := bstep (se 2 (by rfl) ⟨1248522, by rfl⟩ : syracuseStep 3329393 = 2497045) B2497045
theorem B2219595 : Blo 2219435 2219595 := bstep (se 1 (by rfl) ⟨1664696, by rfl⟩ : syracuseStep 2219595 = 3329393) B3329393
theorem B2809181 : Blo 2219435 2809181 := bbase (se 3 (by rfl) ⟨526721, by rfl⟩ : syracuseStep 2809181 = 1053443) (by norm_num)
theorem B7491149 : Blo 2219435 7491149 := bstep (se 3 (by rfl) ⟨1404590, by rfl⟩ : syracuseStep 7491149 = 2809181) B2809181
theorem B4994099 : Blo 2219435 4994099 := bstep (se 1 (by rfl) ⟨3745574, by rfl⟩ : syracuseStep 4994099 = 7491149) B7491149
theorem B3329399 : Blo 2219435 3329399 := bstep (se 1 (by rfl) ⟨2497049, by rfl⟩ : syracuseStep 3329399 = 4994099) B4994099
theorem B2219599 : Blo 2219435 2219599 := bstep (se 1 (by rfl) ⟨1664699, by rfl⟩ : syracuseStep 2219599 = 3329399) B3329399
theorem B3329405 : Blo 2219435 3329405 := bbase (se 3 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 3329405 = 1248527) (by norm_num)
theorem B2219603 : Blo 2219435 2219603 := bstep (se 1 (by rfl) ⟨1664702, by rfl⟩ : syracuseStep 2219603 = 3329405) B3329405
theorem B4994117 : Blo 2219435 4994117 := bbase (se 4 (by rfl) ⟨468198, by rfl⟩ : syracuseStep 4994117 = 936397) (by norm_num)
theorem B3329411 : Blo 2219435 3329411 := bstep (se 1 (by rfl) ⟨2497058, by rfl⟩ : syracuseStep 3329411 = 4994117) B4994117
theorem B2219607 : Blo 2219435 2219607 := bstep (se 1 (by rfl) ⟨1664705, by rfl⟩ : syracuseStep 2219607 = 3329411) B3329411
theorem B6320693 : Blo 2219435 6320693 := bbase (se 5 (by rfl) ⟨296282, by rfl⟩ : syracuseStep 6320693 = 592565) (by norm_num)
theorem B4213795 : Blo 2219435 4213795 := bstep (se 1 (by rfl) ⟨3160346, by rfl⟩ : syracuseStep 4213795 = 6320693) B6320693
theorem B5618393 : Blo 2219435 5618393 := bstep (se 2 (by rfl) ⟨2106897, by rfl⟩ : syracuseStep 5618393 = 4213795) B4213795
theorem B3745595 : Blo 2219435 3745595 := bstep (se 1 (by rfl) ⟨2809196, by rfl⟩ : syracuseStep 3745595 = 5618393) B5618393
theorem B2497063 : Blo 2219435 2497063 := bstep (se 1 (by rfl) ⟨1872797, by rfl⟩ : syracuseStep 2497063 = 3745595) B3745595
theorem B3329417 : Blo 2219435 3329417 := bstep (se 2 (by rfl) ⟨1248531, by rfl⟩ : syracuseStep 3329417 = 2497063) B2497063
theorem B2219611 : Blo 2219435 2219611 := bstep (se 1 (by rfl) ⟨1664708, by rfl⟩ : syracuseStep 2219611 = 3329417) B3329417
theorem B11236805 : Blo 2219435 11236805 := bbase (se 4 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 11236805 = 2106901) (by norm_num)
theorem B7491203 : Blo 2219435 7491203 := bstep (se 1 (by rfl) ⟨5618402, by rfl⟩ : syracuseStep 7491203 = 11236805) B11236805
theorem B4994135 : Blo 2219435 4994135 := bstep (se 1 (by rfl) ⟨3745601, by rfl⟩ : syracuseStep 4994135 = 7491203) B7491203
theorem B3329423 : Blo 2219435 3329423 := bstep (se 1 (by rfl) ⟨2497067, by rfl⟩ : syracuseStep 3329423 = 4994135) B4994135
theorem B2219615 : Blo 2219435 2219615 := bstep (se 1 (by rfl) ⟨1664711, by rfl⟩ : syracuseStep 2219615 = 3329423) B3329423
theorem B3329429 : Blo 2219435 3329429 := bbase (se 6 (by rfl) ⟨78033, by rfl⟩ : syracuseStep 3329429 = 156067) (by norm_num)
theorem B2219619 : Blo 2219435 2219619 := bstep (se 1 (by rfl) ⟨1664714, by rfl⟩ : syracuseStep 2219619 = 3329429) B3329429
theorem B2666557 : Blo 2219435 2666557 := bbase (se 3 (by rfl) ⟨499979, by rfl⟩ : syracuseStep 2666557 = 999959) (by norm_num)
theorem B3555409 : Blo 2219435 3555409 := bstep (se 2 (by rfl) ⟨1333278, by rfl⟩ : syracuseStep 3555409 = 2666557) B2666557
theorem B4740545 : Blo 2219435 4740545 := bstep (se 2 (by rfl) ⟨1777704, by rfl⟩ : syracuseStep 4740545 = 3555409) B3555409
theorem B12641453 : Blo 2219435 12641453 := bstep (se 3 (by rfl) ⟨2370272, by rfl⟩ : syracuseStep 12641453 = 4740545) B4740545
theorem B8427635 : Blo 2219435 8427635 := bstep (se 1 (by rfl) ⟨6320726, by rfl⟩ : syracuseStep 8427635 = 12641453) B12641453
theorem B5618423 : Blo 2219435 5618423 := bstep (se 1 (by rfl) ⟨4213817, by rfl⟩ : syracuseStep 5618423 = 8427635) B8427635
theorem B3745615 : Blo 2219435 3745615 := bstep (se 1 (by rfl) ⟨2809211, by rfl⟩ : syracuseStep 3745615 = 5618423) B5618423
theorem B4994153 : Blo 2219435 4994153 := bstep (se 2 (by rfl) ⟨1872807, by rfl⟩ : syracuseStep 4994153 = 3745615) B3745615
theorem B3329435 : Blo 2219435 3329435 := bstep (se 1 (by rfl) ⟨2497076, by rfl⟩ : syracuseStep 3329435 = 4994153) B4994153
theorem B2219623 : Blo 2219435 2219623 := bstep (se 1 (by rfl) ⟨1664717, by rfl⟩ : syracuseStep 2219623 = 3329435) B3329435
theorem B2497081 : Blo 2219435 2497081 := bbase (se 2 (by rfl) ⟨936405, by rfl⟩ : syracuseStep 2497081 = 1872811) (by norm_num)
theorem B3329441 : Blo 2219435 3329441 := bstep (se 2 (by rfl) ⟨1248540, by rfl⟩ : syracuseStep 3329441 = 2497081) B2497081
theorem B2219627 : Blo 2219435 2219627 := bstep (se 1 (by rfl) ⟨1664720, by rfl⟩ : syracuseStep 2219627 = 3329441) B3329441
theorem B2370281 : Blo 2219435 2370281 := bbase (se 2 (by rfl) ⟨888855, by rfl⟩ : syracuseStep 2370281 = 1777711) (by norm_num)
theorem B6320749 : Blo 2219435 6320749 := bstep (se 3 (by rfl) ⟨1185140, by rfl⟩ : syracuseStep 6320749 = 2370281) B2370281
theorem B8427665 : Blo 2219435 8427665 := bstep (se 2 (by rfl) ⟨3160374, by rfl⟩ : syracuseStep 8427665 = 6320749) B6320749
theorem B5618443 : Blo 2219435 5618443 := bstep (se 1 (by rfl) ⟨4213832, by rfl⟩ : syracuseStep 5618443 = 8427665) B8427665
theorem B7491257 : Blo 2219435 7491257 := bstep (se 2 (by rfl) ⟨2809221, by rfl⟩ : syracuseStep 7491257 = 5618443) B5618443
theorem B4994171 : Blo 2219435 4994171 := bstep (se 1 (by rfl) ⟨3745628, by rfl⟩ : syracuseStep 4994171 = 7491257) B7491257
theorem B3329447 : Blo 2219435 3329447 := bstep (se 1 (by rfl) ⟨2497085, by rfl⟩ : syracuseStep 3329447 = 4994171) B4994171
theorem B2219631 : Blo 2219435 2219631 := bstep (se 1 (by rfl) ⟨1664723, by rfl⟩ : syracuseStep 2219631 = 3329447) B3329447
theorem B3329453 : Blo 2219435 3329453 := bbase (se 3 (by rfl) ⟨624272, by rfl⟩ : syracuseStep 3329453 = 1248545) (by norm_num)
theorem B2219635 : Blo 2219435 2219635 := bstep (se 1 (by rfl) ⟨1664726, by rfl⟩ : syracuseStep 2219635 = 3329453) B3329453
theorem B4994189 : Blo 2219435 4994189 := bbase (se 3 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 4994189 = 1872821) (by norm_num)
theorem B3329459 : Blo 2219435 3329459 := bstep (se 1 (by rfl) ⟨2497094, by rfl⟩ : syracuseStep 3329459 = 4994189) B4994189
theorem B2219639 : Blo 2219435 2219639 := bstep (se 1 (by rfl) ⟨1664729, by rfl⟩ : syracuseStep 2219639 = 3329459) B3329459
theorem B2809237 : Blo 2219435 2809237 := bbase (se 6 (by rfl) ⟨65841, by rfl⟩ : syracuseStep 2809237 = 131683) (by norm_num)
theorem B3745649 : Blo 2219435 3745649 := bstep (se 2 (by rfl) ⟨1404618, by rfl⟩ : syracuseStep 3745649 = 2809237) B2809237
theorem B2497099 : Blo 2219435 2497099 := bstep (se 1 (by rfl) ⟨1872824, by rfl⟩ : syracuseStep 2497099 = 3745649) B3745649
theorem B3329465 : Blo 2219435 3329465 := bstep (se 2 (by rfl) ⟨1248549, by rfl⟩ : syracuseStep 3329465 = 2497099) B2497099
theorem B2219643 : Blo 2219435 2219643 := bstep (se 1 (by rfl) ⟨1664732, by rfl⟩ : syracuseStep 2219643 = 3329465) B3329465
theorem B2531173 : Blo 2219435 2531173 := bbase (se 4 (by rfl) ⟨237297, by rfl⟩ : syracuseStep 2531173 = 474595) (by norm_num)
theorem B3374897 : Blo 2219435 3374897 := bstep (se 2 (by rfl) ⟨1265586, by rfl⟩ : syracuseStep 3374897 = 2531173) B2531173
theorem B35998901 : Blo 2219435 35998901 := bstep (se 5 (by rfl) ⟨1687448, by rfl⟩ : syracuseStep 35998901 = 3374897) B3374897
theorem B23999267 : Blo 2219435 23999267 := bstep (se 1 (by rfl) ⟨17999450, by rfl⟩ : syracuseStep 23999267 = 35998901) B35998901
theorem B63998045 : Blo 2219435 63998045 := bstep (se 3 (by rfl) ⟨11999633, by rfl⟩ : syracuseStep 63998045 = 23999267) B23999267
theorem B42665363 : Blo 2219435 42665363 := bstep (se 1 (by rfl) ⟨31999022, by rfl⟩ : syracuseStep 42665363 = 63998045) B63998045
theorem B28443575 : Blo 2219435 28443575 := bstep (se 1 (by rfl) ⟨21332681, by rfl⟩ : syracuseStep 28443575 = 42665363) B42665363
theorem B18962383 : Blo 2219435 18962383 := bstep (se 1 (by rfl) ⟨14221787, by rfl⟩ : syracuseStep 18962383 = 28443575) B28443575
theorem B25283177 : Blo 2219435 25283177 := bstep (se 2 (by rfl) ⟨9481191, by rfl⟩ : syracuseStep 25283177 = 18962383) B18962383
theorem B16855451 : Blo 2219435 16855451 := bstep (se 1 (by rfl) ⟨12641588, by rfl⟩ : syracuseStep 16855451 = 25283177) B25283177
theorem B11236967 : Blo 2219435 11236967 := bstep (se 1 (by rfl) ⟨8427725, by rfl⟩ : syracuseStep 11236967 = 16855451) B16855451
theorem B7491311 : Blo 2219435 7491311 := bstep (se 1 (by rfl) ⟨5618483, by rfl⟩ : syracuseStep 7491311 = 11236967) B11236967
theorem B4994207 : Blo 2219435 4994207 := bstep (se 1 (by rfl) ⟨3745655, by rfl⟩ : syracuseStep 4994207 = 7491311) B7491311
theorem B3329471 : Blo 2219435 3329471 := bstep (se 1 (by rfl) ⟨2497103, by rfl⟩ : syracuseStep 3329471 = 4994207) B4994207
theorem B2219647 : Blo 2219435 2219647 := bstep (se 1 (by rfl) ⟨1664735, by rfl⟩ : syracuseStep 2219647 = 3329471) B3329471
theorem B3329477 : Blo 2219435 3329477 := bbase (se 4 (by rfl) ⟨312138, by rfl⟩ : syracuseStep 3329477 = 624277) (by norm_num)
theorem B2219651 : Blo 2219435 2219651 := bstep (se 1 (by rfl) ⟨1664738, by rfl⟩ : syracuseStep 2219651 = 3329477) B3329477
theorem B3745669 : Blo 2219435 3745669 := bbase (se 4 (by rfl) ⟨351156, by rfl⟩ : syracuseStep 3745669 = 702313) (by norm_num)
theorem B4994225 : Blo 2219435 4994225 := bstep (se 2 (by rfl) ⟨1872834, by rfl⟩ : syracuseStep 4994225 = 3745669) B3745669
theorem B3329483 : Blo 2219435 3329483 := bstep (se 1 (by rfl) ⟨2497112, by rfl⟩ : syracuseStep 3329483 = 4994225) B4994225
theorem B2219655 : Blo 2219435 2219655 := bstep (se 1 (by rfl) ⟨1664741, by rfl⟩ : syracuseStep 2219655 = 3329483) B3329483
theorem B2497117 : Blo 2219435 2497117 := bbase (se 3 (by rfl) ⟨468209, by rfl⟩ : syracuseStep 2497117 = 936419) (by norm_num)
theorem B3329489 : Blo 2219435 3329489 := bstep (se 2 (by rfl) ⟨1248558, by rfl⟩ : syracuseStep 3329489 = 2497117) B2497117
theorem B2219659 : Blo 2219435 2219659 := bstep (se 1 (by rfl) ⟨1664744, by rfl⟩ : syracuseStep 2219659 = 3329489) B3329489
theorem B7491365 : Blo 2219435 7491365 := bbase (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) (by norm_num)
theorem B4994243 : Blo 2219435 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B3329495 : Blo 2219435 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B2219663 : Blo 2219435 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B3329501 : Blo 2219435 3329501 := bbase (se 3 (by rfl) ⟨624281, by rfl⟩ : syracuseStep 3329501 = 1248563) (by norm_num)
theorem B2219667 : Blo 2219435 2219667 := bstep (se 1 (by rfl) ⟨1664750, by rfl⟩ : syracuseStep 2219667 = 3329501) B3329501
theorem B4994261 : Blo 2219435 4994261 := bbase (se 7 (by rfl) ⟨58526, by rfl⟩ : syracuseStep 4994261 = 117053) (by norm_num)
theorem B3329507 : Blo 2219435 3329507 := bstep (se 1 (by rfl) ⟨2497130, by rfl⟩ : syracuseStep 3329507 = 4994261) B4994261
theorem B2219671 : Blo 2219435 2219671 := bstep (se 1 (by rfl) ⟨1664753, by rfl⟩ : syracuseStep 2219671 = 3329507) B3329507
theorem B3374941 : Blo 2219435 3374941 := bbase (se 3 (by rfl) ⟨632801, by rfl⟩ : syracuseStep 3374941 = 1265603) (by norm_num)
theorem B4499921 : Blo 2219435 4499921 := bstep (se 2 (by rfl) ⟨1687470, by rfl⟩ : syracuseStep 4499921 = 3374941) B3374941
theorem B11999789 : Blo 2219435 11999789 := bstep (se 3 (by rfl) ⟨2249960, by rfl⟩ : syracuseStep 11999789 = 4499921) B4499921
theorem B7999859 : Blo 2219435 7999859 := bstep (se 1 (by rfl) ⟨5999894, by rfl⟩ : syracuseStep 7999859 = 11999789) B11999789
theorem B5333239 : Blo 2219435 5333239 := bstep (se 1 (by rfl) ⟨3999929, by rfl⟩ : syracuseStep 5333239 = 7999859) B7999859
theorem B7110985 : Blo 2219435 7110985 := bstep (se 2 (by rfl) ⟨2666619, by rfl⟩ : syracuseStep 7110985 = 5333239) B5333239
theorem B9481313 : Blo 2219435 9481313 := bstep (se 2 (by rfl) ⟨3555492, by rfl⟩ : syracuseStep 9481313 = 7110985) B7110985
theorem B6320875 : Blo 2219435 6320875 := bstep (se 1 (by rfl) ⟨4740656, by rfl⟩ : syracuseStep 6320875 = 9481313) B9481313
theorem B8427833 : Blo 2219435 8427833 := bstep (se 2 (by rfl) ⟨3160437, by rfl⟩ : syracuseStep 8427833 = 6320875) B6320875
theorem B5618555 : Blo 2219435 5618555 := bstep (se 1 (by rfl) ⟨4213916, by rfl⟩ : syracuseStep 5618555 = 8427833) B8427833
theorem B3745703 : Blo 2219435 3745703 := bstep (se 1 (by rfl) ⟨2809277, by rfl⟩ : syracuseStep 3745703 = 5618555) B5618555
theorem B2497135 : Blo 2219435 2497135 := bstep (se 1 (by rfl) ⟨1872851, by rfl⟩ : syracuseStep 2497135 = 3745703) B3745703
theorem B3329513 : Blo 2219435 3329513 := bstep (se 2 (by rfl) ⟨1248567, by rfl⟩ : syracuseStep 3329513 = 2497135) B2497135
theorem B2219675 : Blo 2219435 2219675 := bstep (se 1 (by rfl) ⟨1664756, by rfl⟩ : syracuseStep 2219675 = 3329513) B3329513
theorem B7306357 : Blo 2219435 7306357 := bbase (se 5 (by rfl) ⟨342485, by rfl⟩ : syracuseStep 7306357 = 684971) (by norm_num)
theorem B9741809 : Blo 2219435 9741809 := bstep (se 2 (by rfl) ⟨3653178, by rfl⟩ : syracuseStep 9741809 = 7306357) B7306357
theorem B25978157 : Blo 2219435 25978157 := bstep (se 3 (by rfl) ⟨4870904, by rfl⟩ : syracuseStep 25978157 = 9741809) B9741809
theorem B17318771 : Blo 2219435 17318771 := bstep (se 1 (by rfl) ⟨12989078, by rfl⟩ : syracuseStep 17318771 = 25978157) B25978157
theorem B11545847 : Blo 2219435 11545847 := bstep (se 1 (by rfl) ⟨8659385, by rfl⟩ : syracuseStep 11545847 = 17318771) B17318771
theorem B7697231 : Blo 2219435 7697231 := bstep (se 1 (by rfl) ⟨5772923, by rfl⟩ : syracuseStep 7697231 = 11545847) B11545847
theorem B5131487 : Blo 2219435 5131487 := bstep (se 1 (by rfl) ⟨3848615, by rfl⟩ : syracuseStep 5131487 = 7697231) B7697231
theorem B218943445 : Blo 2219435 218943445 := bstep (se 7 (by rfl) ⟨2565743, by rfl⟩ : syracuseStep 218943445 = 5131487) B5131487
theorem B291924593 : Blo 2219435 291924593 := bstep (se 2 (by rfl) ⟨109471722, by rfl⟩ : syracuseStep 291924593 = 218943445) B218943445
theorem B194616395 : Blo 2219435 194616395 := bstep (se 1 (by rfl) ⟨145962296, by rfl⟩ : syracuseStep 194616395 = 291924593) B291924593
theorem B129744263 : Blo 2219435 129744263 := bstep (se 1 (by rfl) ⟨97308197, by rfl⟩ : syracuseStep 129744263 = 194616395) B194616395
theorem B86496175 : Blo 2219435 86496175 := bstep (se 1 (by rfl) ⟨64872131, by rfl⟩ : syracuseStep 86496175 = 129744263) B129744263
theorem B115328233 : Blo 2219435 115328233 := bstep (se 2 (by rfl) ⟨43248087, by rfl⟩ : syracuseStep 115328233 = 86496175) B86496175
theorem B153770977 : Blo 2219435 153770977 := bstep (se 2 (by rfl) ⟨57664116, by rfl⟩ : syracuseStep 153770977 = 115328233) B115328233
theorem B205027969 : Blo 2219435 205027969 := bstep (se 2 (by rfl) ⟨76885488, by rfl⟩ : syracuseStep 205027969 = 153770977) B153770977
theorem B273370625 : Blo 2219435 273370625 := bstep (se 2 (by rfl) ⟨102513984, by rfl⟩ : syracuseStep 273370625 = 205027969) B205027969
theorem B182247083 : Blo 2219435 182247083 := bstep (se 1 (by rfl) ⟨136685312, by rfl⟩ : syracuseStep 182247083 = 273370625) B273370625
theorem B121498055 : Blo 2219435 121498055 := bstep (se 1 (by rfl) ⟨91123541, by rfl⟩ : syracuseStep 121498055 = 182247083) B182247083
theorem B80998703 : Blo 2219435 80998703 := bstep (se 1 (by rfl) ⟨60749027, by rfl⟩ : syracuseStep 80998703 = 121498055) B121498055
theorem B53999135 : Blo 2219435 53999135 := bstep (se 1 (by rfl) ⟨40499351, by rfl⟩ : syracuseStep 53999135 = 80998703) B80998703
theorem B35999423 : Blo 2219435 35999423 := bstep (se 1 (by rfl) ⟨26999567, by rfl⟩ : syracuseStep 35999423 = 53999135) B53999135
theorem B23999615 : Blo 2219435 23999615 := bstep (se 1 (by rfl) ⟨17999711, by rfl⟩ : syracuseStep 23999615 = 35999423) B35999423
theorem B15999743 : Blo 2219435 15999743 := bstep (se 1 (by rfl) ⟨11999807, by rfl⟩ : syracuseStep 15999743 = 23999615) B23999615
theorem B10666495 : Blo 2219435 10666495 := bstep (se 1 (by rfl) ⟨7999871, by rfl⟩ : syracuseStep 10666495 = 15999743) B15999743
theorem B14221993 : Blo 2219435 14221993 := bstep (se 2 (by rfl) ⟨5333247, by rfl⟩ : syracuseStep 14221993 = 10666495) B10666495
theorem B18962657 : Blo 2219435 18962657 := bstep (se 2 (by rfl) ⟨7110996, by rfl⟩ : syracuseStep 18962657 = 14221993) B14221993
theorem B12641771 : Blo 2219435 12641771 := bstep (se 1 (by rfl) ⟨9481328, by rfl⟩ : syracuseStep 12641771 = 18962657) B18962657
theorem B8427847 : Blo 2219435 8427847 := bstep (se 1 (by rfl) ⟨6320885, by rfl⟩ : syracuseStep 8427847 = 12641771) B12641771
theorem B11237129 : Blo 2219435 11237129 := bstep (se 2 (by rfl) ⟨4213923, by rfl⟩ : syracuseStep 11237129 = 8427847) B8427847
theorem B7491419 : Blo 2219435 7491419 := bstep (se 1 (by rfl) ⟨5618564, by rfl⟩ : syracuseStep 7491419 = 11237129) B11237129
theorem B4994279 : Blo 2219435 4994279 := bstep (se 1 (by rfl) ⟨3745709, by rfl⟩ : syracuseStep 4994279 = 7491419) B7491419
theorem B3329519 : Blo 2219435 3329519 := bstep (se 1 (by rfl) ⟨2497139, by rfl⟩ : syracuseStep 3329519 = 4994279) B4994279
theorem B2219679 : Blo 2219435 2219679 := bstep (se 1 (by rfl) ⟨1664759, by rfl⟩ : syracuseStep 2219679 = 3329519) B3329519
theorem B3329525 : Blo 2219435 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B2219683 : Blo 2219435 2219683 := bstep (se 1 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 2219683 = 3329525) B3329525
theorem B2370341 : Blo 2219435 2370341 := bbase (se 4 (by rfl) ⟨222219, by rfl⟩ : syracuseStep 2370341 = 444439) (by norm_num)
theorem B6320909 : Blo 2219435 6320909 := bstep (se 3 (by rfl) ⟨1185170, by rfl⟩ : syracuseStep 6320909 = 2370341) B2370341
theorem B4213939 : Blo 2219435 4213939 := bstep (se 1 (by rfl) ⟨3160454, by rfl⟩ : syracuseStep 4213939 = 6320909) B6320909
theorem B5618585 : Blo 2219435 5618585 := bstep (se 2 (by rfl) ⟨2106969, by rfl⟩ : syracuseStep 5618585 = 4213939) B4213939
theorem B3745723 : Blo 2219435 3745723 := bstep (se 1 (by rfl) ⟨2809292, by rfl⟩ : syracuseStep 3745723 = 5618585) B5618585
theorem B4994297 : Blo 2219435 4994297 := bstep (se 2 (by rfl) ⟨1872861, by rfl⟩ : syracuseStep 4994297 = 3745723) B3745723
theorem B3329531 : Blo 2219435 3329531 := bstep (se 1 (by rfl) ⟨2497148, by rfl⟩ : syracuseStep 3329531 = 4994297) B4994297
theorem B2219687 : Blo 2219435 2219687 := bstep (se 1 (by rfl) ⟨1664765, by rfl⟩ : syracuseStep 2219687 = 3329531) B3329531
theorem B2497153 : Blo 2219435 2497153 := bbase (se 2 (by rfl) ⟨936432, by rfl⟩ : syracuseStep 2497153 = 1872865) (by norm_num)
theorem B3329537 : Blo 2219435 3329537 := bstep (se 2 (by rfl) ⟨1248576, by rfl⟩ : syracuseStep 3329537 = 2497153) B2497153
theorem B2219691 : Blo 2219435 2219691 := bstep (se 1 (by rfl) ⟨1664768, by rfl⟩ : syracuseStep 2219691 = 3329537) B3329537
theorem B5618605 : Blo 2219435 5618605 := bbase (se 3 (by rfl) ⟨1053488, by rfl⟩ : syracuseStep 5618605 = 2106977) (by norm_num)
theorem B7491473 : Blo 2219435 7491473 := bstep (se 2 (by rfl) ⟨2809302, by rfl⟩ : syracuseStep 7491473 = 5618605) B5618605
theorem B4994315 : Blo 2219435 4994315 := bstep (se 1 (by rfl) ⟨3745736, by rfl⟩ : syracuseStep 4994315 = 7491473) B7491473
theorem B3329543 : Blo 2219435 3329543 := bstep (se 1 (by rfl) ⟨2497157, by rfl⟩ : syracuseStep 3329543 = 4994315) B4994315
theorem B2219695 : Blo 2219435 2219695 := bstep (se 1 (by rfl) ⟨1664771, by rfl⟩ : syracuseStep 2219695 = 3329543) B3329543
theorem B3329549 : Blo 2219435 3329549 := bbase (se 3 (by rfl) ⟨624290, by rfl⟩ : syracuseStep 3329549 = 1248581) (by norm_num)
theorem B2219699 : Blo 2219435 2219699 := bstep (se 1 (by rfl) ⟨1664774, by rfl⟩ : syracuseStep 2219699 = 3329549) B3329549
theorem B4994333 : Blo 2219435 4994333 := bbase (se 3 (by rfl) ⟨936437, by rfl⟩ : syracuseStep 4994333 = 1872875) (by norm_num)
theorem B3329555 : Blo 2219435 3329555 := bstep (se 1 (by rfl) ⟨2497166, by rfl⟩ : syracuseStep 3329555 = 4994333) B4994333
theorem B2219703 : Blo 2219435 2219703 := bstep (se 1 (by rfl) ⟨1664777, by rfl⟩ : syracuseStep 2219703 = 3329555) B3329555
theorem B3745757 : Blo 2219435 3745757 := bbase (se 3 (by rfl) ⟨702329, by rfl⟩ : syracuseStep 3745757 = 1404659) (by norm_num)
theorem B2497171 : Blo 2219435 2497171 := bstep (se 1 (by rfl) ⟨1872878, by rfl⟩ : syracuseStep 2497171 = 3745757) B3745757
theorem B3329561 : Blo 2219435 3329561 := bstep (se 2 (by rfl) ⟨1248585, by rfl⟩ : syracuseStep 3329561 = 2497171) B2497171
theorem B2219707 : Blo 2219435 2219707 := bstep (se 1 (by rfl) ⟨1664780, by rfl⟩ : syracuseStep 2219707 = 3329561) B3329561
theorem B5062493 : Blo 2219435 5062493 := bbase (se 3 (by rfl) ⟨949217, by rfl⟩ : syracuseStep 5062493 = 1898435) (by norm_num)
theorem B3374995 : Blo 2219435 3374995 := bstep (se 1 (by rfl) ⟨2531246, by rfl⟩ : syracuseStep 3374995 = 5062493) B5062493
theorem B4499993 : Blo 2219435 4499993 := bstep (se 2 (by rfl) ⟨1687497, by rfl⟩ : syracuseStep 4499993 = 3374995) B3374995
theorem B11999981 : Blo 2219435 11999981 := bstep (se 3 (by rfl) ⟨2249996, by rfl⟩ : syracuseStep 11999981 = 4499993) B4499993
theorem B7999987 : Blo 2219435 7999987 := bstep (se 1 (by rfl) ⟨5999990, by rfl⟩ : syracuseStep 7999987 = 11999981) B11999981
theorem B10666649 : Blo 2219435 10666649 := bstep (se 2 (by rfl) ⟨3999993, by rfl⟩ : syracuseStep 10666649 = 7999987) B7999987
theorem B7111099 : Blo 2219435 7111099 := bstep (se 1 (by rfl) ⟨5333324, by rfl⟩ : syracuseStep 7111099 = 10666649) B10666649
theorem B9481465 : Blo 2219435 9481465 := bstep (se 2 (by rfl) ⟨3555549, by rfl⟩ : syracuseStep 9481465 = 7111099) B7111099
theorem B12641953 : Blo 2219435 12641953 := bstep (se 2 (by rfl) ⟨4740732, by rfl⟩ : syracuseStep 12641953 = 9481465) B9481465
theorem B16855937 : Blo 2219435 16855937 := bstep (se 2 (by rfl) ⟨6320976, by rfl⟩ : syracuseStep 16855937 = 12641953) B12641953
theorem B11237291 : Blo 2219435 11237291 := bstep (se 1 (by rfl) ⟨8427968, by rfl⟩ : syracuseStep 11237291 = 16855937) B16855937
theorem B7491527 : Blo 2219435 7491527 := bstep (se 1 (by rfl) ⟨5618645, by rfl⟩ : syracuseStep 7491527 = 11237291) B11237291
theorem B4994351 : Blo 2219435 4994351 := bstep (se 1 (by rfl) ⟨3745763, by rfl⟩ : syracuseStep 4994351 = 7491527) B7491527
theorem B3329567 : Blo 2219435 3329567 := bstep (se 1 (by rfl) ⟨2497175, by rfl⟩ : syracuseStep 3329567 = 4994351) B4994351
theorem B2219711 : Blo 2219435 2219711 := bstep (se 1 (by rfl) ⟨1664783, by rfl⟩ : syracuseStep 2219711 = 3329567) B3329567
theorem B3329573 : Blo 2219435 3329573 := bbase (se 4 (by rfl) ⟨312147, by rfl⟩ : syracuseStep 3329573 = 624295) (by norm_num)
theorem B2219715 : Blo 2219435 2219715 := bstep (se 1 (by rfl) ⟨1664786, by rfl⟩ : syracuseStep 2219715 = 3329573) B3329573
theorem B2809333 : Blo 2219435 2809333 := bbase (se 5 (by rfl) ⟨131687, by rfl⟩ : syracuseStep 2809333 = 263375) (by norm_num)
theorem B3745777 : Blo 2219435 3745777 := bstep (se 2 (by rfl) ⟨1404666, by rfl⟩ : syracuseStep 3745777 = 2809333) B2809333
theorem B4994369 : Blo 2219435 4994369 := bstep (se 2 (by rfl) ⟨1872888, by rfl⟩ : syracuseStep 4994369 = 3745777) B3745777
theorem B3329579 : Blo 2219435 3329579 := bstep (se 1 (by rfl) ⟨2497184, by rfl⟩ : syracuseStep 3329579 = 4994369) B4994369
theorem B2219719 : Blo 2219435 2219719 := bstep (se 1 (by rfl) ⟨1664789, by rfl⟩ : syracuseStep 2219719 = 3329579) B3329579
theorem B2497189 : Blo 2219435 2497189 := bbase (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) (by norm_num)
theorem B3329585 : Blo 2219435 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B2219723 : Blo 2219435 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B72982741 : Blo 2219435 72982741 := bbase (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) (by norm_num)
theorem B97310321 : Blo 2219435 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B64873547 : Blo 2219435 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B43249031 : Blo 2219435 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B28832687 : Blo 2219435 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B19221791 : Blo 2219435 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B51258109 : Blo 2219435 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B68344145 : Blo 2219435 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B45562763 : Blo 2219435 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B30375175 : Blo 2219435 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B40500233 : Blo 2219435 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B27000155 : Blo 2219435 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B72000413 : Blo 2219435 72000413 := bstep (se 3 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 72000413 = 27000155) B27000155
theorem B48000275 : Blo 2219435 48000275 := bstep (se 1 (by rfl) ⟨36000206, by rfl⟩ : syracuseStep 48000275 = 72000413) B72000413
theorem B32000183 : Blo 2219435 32000183 := bstep (se 1 (by rfl) ⟨24000137, by rfl⟩ : syracuseStep 32000183 = 48000275) B48000275
theorem B21333455 : Blo 2219435 21333455 := bstep (se 1 (by rfl) ⟨16000091, by rfl⟩ : syracuseStep 21333455 = 32000183) B32000183
theorem B14222303 : Blo 2219435 14222303 := bstep (se 1 (by rfl) ⟨10666727, by rfl⟩ : syracuseStep 14222303 = 21333455) B21333455
theorem B9481535 : Blo 2219435 9481535 := bstep (se 1 (by rfl) ⟨7111151, by rfl⟩ : syracuseStep 9481535 = 14222303) B14222303
theorem B6321023 : Blo 2219435 6321023 := bstep (se 1 (by rfl) ⟨4740767, by rfl⟩ : syracuseStep 6321023 = 9481535) B9481535
theorem B4214015 : Blo 2219435 4214015 := bstep (se 1 (by rfl) ⟨3160511, by rfl⟩ : syracuseStep 4214015 = 6321023) B6321023
theorem B2809343 : Blo 2219435 2809343 := bstep (se 1 (by rfl) ⟨2107007, by rfl⟩ : syracuseStep 2809343 = 4214015) B4214015
theorem B7491581 : Blo 2219435 7491581 := bstep (se 3 (by rfl) ⟨1404671, by rfl⟩ : syracuseStep 7491581 = 2809343) B2809343
theorem B4994387 : Blo 2219435 4994387 := bstep (se 1 (by rfl) ⟨3745790, by rfl⟩ : syracuseStep 4994387 = 7491581) B7491581
theorem B3329591 : Blo 2219435 3329591 := bstep (se 1 (by rfl) ⟨2497193, by rfl⟩ : syracuseStep 3329591 = 4994387) B4994387
theorem B2219727 : Blo 2219435 2219727 := bstep (se 1 (by rfl) ⟨1664795, by rfl⟩ : syracuseStep 2219727 = 3329591) B3329591
theorem B3329597 : Blo 2219435 3329597 := bbase (se 3 (by rfl) ⟨624299, by rfl⟩ : syracuseStep 3329597 = 1248599) (by norm_num)
theorem B2219731 : Blo 2219435 2219731 := bstep (se 1 (by rfl) ⟨1664798, by rfl⟩ : syracuseStep 2219731 = 3329597) B3329597
theorem B4994405 : Blo 2219435 4994405 := bbase (se 4 (by rfl) ⟨468225, by rfl⟩ : syracuseStep 4994405 = 936451) (by norm_num)
theorem B3329603 : Blo 2219435 3329603 := bstep (se 1 (by rfl) ⟨2497202, by rfl⟩ : syracuseStep 3329603 = 4994405) B4994405
theorem B2219735 : Blo 2219435 2219735 := bstep (se 1 (by rfl) ⟨1664801, by rfl⟩ : syracuseStep 2219735 = 3329603) B3329603
theorem B5618717 : Blo 2219435 5618717 := bbase (se 3 (by rfl) ⟨1053509, by rfl⟩ : syracuseStep 5618717 = 2107019) (by norm_num)
theorem B3745811 : Blo 2219435 3745811 := bstep (se 1 (by rfl) ⟨2809358, by rfl⟩ : syracuseStep 3745811 = 5618717) B5618717
theorem B2497207 : Blo 2219435 2497207 := bstep (se 1 (by rfl) ⟨1872905, by rfl⟩ : syracuseStep 2497207 = 3745811) B3745811
theorem B3329609 : Blo 2219435 3329609 := bstep (se 2 (by rfl) ⟨1248603, by rfl⟩ : syracuseStep 3329609 = 2497207) B2497207
theorem B2219739 : Blo 2219435 2219739 := bstep (se 1 (by rfl) ⟨1664804, by rfl⟩ : syracuseStep 2219739 = 3329609) B3329609
theorem B4214045 : Blo 2219435 4214045 := bbase (se 3 (by rfl) ⟨790133, by rfl⟩ : syracuseStep 4214045 = 1580267) (by norm_num)
theorem B11237453 : Blo 2219435 11237453 := bstep (se 3 (by rfl) ⟨2107022, by rfl⟩ : syracuseStep 11237453 = 4214045) B4214045
theorem B7491635 : Blo 2219435 7491635 := bstep (se 1 (by rfl) ⟨5618726, by rfl⟩ : syracuseStep 7491635 = 11237453) B11237453
theorem B4994423 : Blo 2219435 4994423 := bstep (se 1 (by rfl) ⟨3745817, by rfl⟩ : syracuseStep 4994423 = 7491635) B7491635
theorem B3329615 : Blo 2219435 3329615 := bstep (se 1 (by rfl) ⟨2497211, by rfl⟩ : syracuseStep 3329615 = 4994423) B4994423
theorem B2219743 : Blo 2219435 2219743 := bstep (se 1 (by rfl) ⟨1664807, by rfl⟩ : syracuseStep 2219743 = 3329615) B3329615
theorem B3329621 : Blo 2219435 3329621 := bbase (se 8 (by rfl) ⟨19509, by rfl⟩ : syracuseStep 3329621 = 39019) (by norm_num)
theorem B2219747 : Blo 2219435 2219747 := bstep (se 1 (by rfl) ⟨1664810, by rfl⟩ : syracuseStep 2219747 = 3329621) B3329621
theorem B9481637 : Blo 2219435 9481637 := bbase (se 4 (by rfl) ⟨888903, by rfl⟩ : syracuseStep 9481637 = 1777807) (by norm_num)
theorem B6321091 : Blo 2219435 6321091 := bstep (se 1 (by rfl) ⟨4740818, by rfl⟩ : syracuseStep 6321091 = 9481637) B9481637
theorem B8428121 : Blo 2219435 8428121 := bstep (se 2 (by rfl) ⟨3160545, by rfl⟩ : syracuseStep 8428121 = 6321091) B6321091
theorem B5618747 : Blo 2219435 5618747 := bstep (se 1 (by rfl) ⟨4214060, by rfl⟩ : syracuseStep 5618747 = 8428121) B8428121
theorem B3745831 : Blo 2219435 3745831 := bstep (se 1 (by rfl) ⟨2809373, by rfl⟩ : syracuseStep 3745831 = 5618747) B5618747
theorem B4994441 : Blo 2219435 4994441 := bstep (se 2 (by rfl) ⟨1872915, by rfl⟩ : syracuseStep 4994441 = 3745831) B3745831
theorem B3329627 : Blo 2219435 3329627 := bstep (se 1 (by rfl) ⟨2497220, by rfl⟩ : syracuseStep 3329627 = 4994441) B4994441
theorem B2219751 : Blo 2219435 2219751 := bstep (se 1 (by rfl) ⟨1664813, by rfl⟩ : syracuseStep 2219751 = 3329627) B3329627
theorem B2497225 : Blo 2219435 2497225 := bbase (se 2 (by rfl) ⟨936459, by rfl⟩ : syracuseStep 2497225 = 1872919) (by norm_num)
theorem B3329633 : Blo 2219435 3329633 := bstep (se 2 (by rfl) ⟨1248612, by rfl⟩ : syracuseStep 3329633 = 2497225) B2497225
theorem B2219755 : Blo 2219435 2219755 := bstep (se 1 (by rfl) ⟨1664816, by rfl⟩ : syracuseStep 2219755 = 3329633) B3329633
theorem B7111253 : Blo 2219435 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B18963341 : Blo 2219435 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B12642227 : Blo 2219435 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B8428151 : Blo 2219435 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B5618767 : Blo 2219435 5618767 := bstep (se 1 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 5618767 = 8428151) B8428151
theorem B7491689 : Blo 2219435 7491689 := bstep (se 2 (by rfl) ⟨2809383, by rfl⟩ : syracuseStep 7491689 = 5618767) B5618767
theorem B4994459 : Blo 2219435 4994459 := bstep (se 1 (by rfl) ⟨3745844, by rfl⟩ : syracuseStep 4994459 = 7491689) B7491689
theorem B3329639 : Blo 2219435 3329639 := bstep (se 1 (by rfl) ⟨2497229, by rfl⟩ : syracuseStep 3329639 = 4994459) B4994459
theorem B2219759 : Blo 2219435 2219759 := bstep (se 1 (by rfl) ⟨1664819, by rfl⟩ : syracuseStep 2219759 = 3329639) B3329639
theorem B3329645 : Blo 2219435 3329645 := bbase (se 3 (by rfl) ⟨624308, by rfl⟩ : syracuseStep 3329645 = 1248617) (by norm_num)
theorem B2219763 : Blo 2219435 2219763 := bstep (se 1 (by rfl) ⟨1664822, by rfl⟩ : syracuseStep 2219763 = 3329645) B3329645
theorem B4994477 : Blo 2219435 4994477 := bbase (se 3 (by rfl) ⟨936464, by rfl⟩ : syracuseStep 4994477 = 1872929) (by norm_num)
theorem B3329651 : Blo 2219435 3329651 := bstep (se 1 (by rfl) ⟨2497238, by rfl⟩ : syracuseStep 3329651 = 4994477) B4994477
theorem B2219767 : Blo 2219435 2219767 := bstep (se 1 (by rfl) ⟨1664825, by rfl⟩ : syracuseStep 2219767 = 3329651) B3329651
theorem B9875141 : Blo 2219435 9875141 := bbase (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) (by norm_num)
theorem B6583427 : Blo 2219435 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B4388951 : Blo 2219435 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B2925967 : Blo 2219435 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B3901289 : Blo 2219435 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B41613749 : Blo 2219435 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B27742499 : Blo 2219435 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B18494999 : Blo 2219435 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B12329999 : Blo 2219435 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B8219999 : Blo 2219435 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B21919997 : Blo 2219435 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B58453325 : Blo 2219435 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B38968883 : Blo 2219435 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B25979255 : Blo 2219435 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B17319503 : Blo 2219435 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B11546335 : Blo 2219435 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B15395113 : Blo 2219435 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B20526817 : Blo 2219435 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B27369089 : Blo 2219435 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B18246059 : Blo 2219435 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B12164039 : Blo 2219435 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B8109359 : Blo 2219435 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B5406239 : Blo 2219435 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B3604159 : Blo 2219435 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B19222181 : Blo 2219435 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B12814787 : Blo 2219435 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B34172765 : Blo 2219435 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B22781843 : Blo 2219435 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B15187895 : Blo 2219435 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B10125263 : Blo 2219435 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B27000701 : Blo 2219435 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B18000467 : Blo 2219435 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B12000311 : Blo 2219435 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B8000207 : Blo 2219435 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B5333471 : Blo 2219435 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B3555647 : Blo 2219435 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B2370431 : Blo 2219435 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B6321149 : Blo 2219435 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B4214099 : Blo 2219435 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B2809399 : Blo 2219435 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B3745865 : Blo 2219435 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B2497243 : Blo 2219435 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B3329657 : Blo 2219435 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B2219771 : Blo 2219435 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B81002197 : Blo 2219435 81002197 := bbase (se 7 (by rfl) ⟨949244, by rfl⟩ : syracuseStep 81002197 = 1898489) (by norm_num)
theorem B108002929 : Blo 2219435 108002929 := bstep (se 2 (by rfl) ⟨40501098, by rfl⟩ : syracuseStep 108002929 = 81002197) B81002197
theorem B144003905 : Blo 2219435 144003905 := bstep (se 2 (by rfl) ⟨54001464, by rfl⟩ : syracuseStep 144003905 = 108002929) B108002929
theorem B96002603 : Blo 2219435 96002603 := bstep (se 1 (by rfl) ⟨72001952, by rfl⟩ : syracuseStep 96002603 = 144003905) B144003905
theorem B64001735 : Blo 2219435 64001735 := bstep (se 1 (by rfl) ⟨48001301, by rfl⟩ : syracuseStep 64001735 = 96002603) B96002603
theorem B42667823 : Blo 2219435 42667823 := bstep (se 1 (by rfl) ⟨32000867, by rfl⟩ : syracuseStep 42667823 = 64001735) B64001735
theorem B28445215 : Blo 2219435 28445215 := bstep (se 1 (by rfl) ⟨21333911, by rfl⟩ : syracuseStep 28445215 = 42667823) B42667823
theorem B37926953 : Blo 2219435 37926953 := bstep (se 2 (by rfl) ⟨14222607, by rfl⟩ : syracuseStep 37926953 = 28445215) B28445215
theorem B25284635 : Blo 2219435 25284635 := bstep (se 1 (by rfl) ⟨18963476, by rfl⟩ : syracuseStep 25284635 = 37926953) B37926953
theorem B16856423 : Blo 2219435 16856423 := bstep (se 1 (by rfl) ⟨12642317, by rfl⟩ : syracuseStep 16856423 = 25284635) B25284635
theorem B11237615 : Blo 2219435 11237615 := bstep (se 1 (by rfl) ⟨8428211, by rfl⟩ : syracuseStep 11237615 = 16856423) B16856423
theorem B7491743 : Blo 2219435 7491743 := bstep (se 1 (by rfl) ⟨5618807, by rfl⟩ : syracuseStep 7491743 = 11237615) B11237615
theorem B4994495 : Blo 2219435 4994495 := bstep (se 1 (by rfl) ⟨3745871, by rfl⟩ : syracuseStep 4994495 = 7491743) B7491743
theorem B3329663 : Blo 2219435 3329663 := bstep (se 1 (by rfl) ⟨2497247, by rfl⟩ : syracuseStep 3329663 = 4994495) B4994495
theorem B2219775 : Blo 2219435 2219775 := bstep (se 1 (by rfl) ⟨1664831, by rfl⟩ : syracuseStep 2219775 = 3329663) B3329663
theorem B3329669 : Blo 2219435 3329669 := bbase (se 4 (by rfl) ⟨312156, by rfl⟩ : syracuseStep 3329669 = 624313) (by norm_num)
theorem B2219779 : Blo 2219435 2219779 := bstep (se 1 (by rfl) ⟨1664834, by rfl⟩ : syracuseStep 2219779 = 3329669) B3329669
theorem B3745885 : Blo 2219435 3745885 := bbase (se 3 (by rfl) ⟨702353, by rfl⟩ : syracuseStep 3745885 = 1404707) (by norm_num)
theorem B4994513 : Blo 2219435 4994513 := bstep (se 2 (by rfl) ⟨1872942, by rfl⟩ : syracuseStep 4994513 = 3745885) B3745885
theorem B3329675 : Blo 2219435 3329675 := bstep (se 1 (by rfl) ⟨2497256, by rfl⟩ : syracuseStep 3329675 = 4994513) B4994513
theorem B2219783 : Blo 2219435 2219783 := bstep (se 1 (by rfl) ⟨1664837, by rfl⟩ : syracuseStep 2219783 = 3329675) B3329675
theorem B2497261 : Blo 2219435 2497261 := bbase (se 3 (by rfl) ⟨468236, by rfl⟩ : syracuseStep 2497261 = 936473) (by norm_num)
theorem B3329681 : Blo 2219435 3329681 := bstep (se 2 (by rfl) ⟨1248630, by rfl⟩ : syracuseStep 3329681 = 2497261) B2497261
theorem B2219787 : Blo 2219435 2219787 := bstep (se 1 (by rfl) ⟨1664840, by rfl⟩ : syracuseStep 2219787 = 3329681) B3329681
theorem B7491797 : Blo 2219435 7491797 := bbase (se 7 (by rfl) ⟨87794, by rfl⟩ : syracuseStep 7491797 = 175589) (by norm_num)
theorem B4994531 : Blo 2219435 4994531 := bstep (se 1 (by rfl) ⟨3745898, by rfl⟩ : syracuseStep 4994531 = 7491797) B7491797
theorem B3329687 : Blo 2219435 3329687 := bstep (se 1 (by rfl) ⟨2497265, by rfl⟩ : syracuseStep 3329687 = 4994531) B4994531
theorem B2219791 : Blo 2219435 2219791 := bstep (se 1 (by rfl) ⟨1664843, by rfl⟩ : syracuseStep 2219791 = 3329687) B3329687
theorem B3329693 : Blo 2219435 3329693 := bbase (se 3 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 3329693 = 1248635) (by norm_num)
theorem B2219795 : Blo 2219435 2219795 := bstep (se 1 (by rfl) ⟨1664846, by rfl⟩ : syracuseStep 2219795 = 3329693) B3329693
theorem B4994549 : Blo 2219435 4994549 := bbase (se 5 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 4994549 = 468239) (by norm_num)
theorem B3329699 : Blo 2219435 3329699 := bstep (se 1 (by rfl) ⟨2497274, by rfl⟩ : syracuseStep 3329699 = 4994549) B4994549
theorem B2219799 : Blo 2219435 2219799 := bstep (se 1 (by rfl) ⟨1664849, by rfl⟩ : syracuseStep 2219799 = 3329699) B3329699
theorem B10812629 : Blo 2219435 10812629 := bbase (se 7 (by rfl) ⟨126710, by rfl⟩ : syracuseStep 10812629 = 253421) (by norm_num)
theorem B7208419 : Blo 2219435 7208419 := bstep (se 1 (by rfl) ⟨5406314, by rfl⟩ : syracuseStep 7208419 = 10812629) B10812629
theorem B9611225 : Blo 2219435 9611225 := bstep (se 2 (by rfl) ⟨3604209, by rfl⟩ : syracuseStep 9611225 = 7208419) B7208419
theorem B6407483 : Blo 2219435 6407483 := bstep (se 1 (by rfl) ⟨4805612, by rfl⟩ : syracuseStep 6407483 = 9611225) B9611225
theorem B17086621 : Blo 2219435 17086621 := bstep (se 3 (by rfl) ⟨3203741, by rfl⟩ : syracuseStep 17086621 = 6407483) B6407483
theorem B22782161 : Blo 2219435 22782161 := bstep (se 2 (by rfl) ⟨8543310, by rfl⟩ : syracuseStep 22782161 = 17086621) B17086621
theorem B60752429 : Blo 2219435 60752429 := bstep (se 3 (by rfl) ⟨11391080, by rfl⟩ : syracuseStep 60752429 = 22782161) B22782161
theorem B40501619 : Blo 2219435 40501619 := bstep (se 1 (by rfl) ⟨30376214, by rfl⟩ : syracuseStep 40501619 = 60752429) B60752429
theorem B27001079 : Blo 2219435 27001079 := bstep (se 1 (by rfl) ⟨20250809, by rfl⟩ : syracuseStep 27001079 = 40501619) B40501619
theorem B18000719 : Blo 2219435 18000719 := bstep (se 1 (by rfl) ⟨13500539, by rfl⟩ : syracuseStep 18000719 = 27001079) B27001079
theorem B12000479 : Blo 2219435 12000479 := bstep (se 1 (by rfl) ⟨9000359, by rfl⟩ : syracuseStep 12000479 = 18000719) B18000719
theorem B32001277 : Blo 2219435 32001277 := bstep (se 3 (by rfl) ⟨6000239, by rfl⟩ : syracuseStep 32001277 = 12000479) B12000479
theorem B42668369 : Blo 2219435 42668369 := bstep (se 2 (by rfl) ⟨16000638, by rfl⟩ : syracuseStep 42668369 = 32001277) B32001277
theorem B28445579 : Blo 2219435 28445579 := bstep (se 1 (by rfl) ⟨21334184, by rfl⟩ : syracuseStep 28445579 = 42668369) B42668369
theorem B18963719 : Blo 2219435 18963719 := bstep (se 1 (by rfl) ⟨14222789, by rfl⟩ : syracuseStep 18963719 = 28445579) B28445579
theorem B12642479 : Blo 2219435 12642479 := bstep (se 1 (by rfl) ⟨9481859, by rfl⟩ : syracuseStep 12642479 = 18963719) B18963719
theorem B8428319 : Blo 2219435 8428319 := bstep (se 1 (by rfl) ⟨6321239, by rfl⟩ : syracuseStep 8428319 = 12642479) B12642479
theorem B5618879 : Blo 2219435 5618879 := bstep (se 1 (by rfl) ⟨4214159, by rfl⟩ : syracuseStep 5618879 = 8428319) B8428319
theorem B3745919 : Blo 2219435 3745919 := bstep (se 1 (by rfl) ⟨2809439, by rfl⟩ : syracuseStep 3745919 = 5618879) B5618879
theorem B2497279 : Blo 2219435 2497279 := bstep (se 1 (by rfl) ⟨1872959, by rfl⟩ : syracuseStep 2497279 = 3745919) B3745919
theorem B3329705 : Blo 2219435 3329705 := bstep (se 2 (by rfl) ⟨1248639, by rfl⟩ : syracuseStep 3329705 = 2497279) B2497279
theorem B2219803 : Blo 2219435 2219803 := bstep (se 1 (by rfl) ⟨1664852, by rfl⟩ : syracuseStep 2219803 = 3329705) B3329705
theorem B2370469 : Blo 2219435 2370469 := bbase (se 4 (by rfl) ⟨222231, by rfl⟩ : syracuseStep 2370469 = 444463) (by norm_num)
theorem B3160625 : Blo 2219435 3160625 := bstep (se 2 (by rfl) ⟨1185234, by rfl⟩ : syracuseStep 3160625 = 2370469) B2370469
theorem B8428333 : Blo 2219435 8428333 := bstep (se 3 (by rfl) ⟨1580312, by rfl⟩ : syracuseStep 8428333 = 3160625) B3160625
theorem B11237777 : Blo 2219435 11237777 := bstep (se 2 (by rfl) ⟨4214166, by rfl⟩ : syracuseStep 11237777 = 8428333) B8428333
theorem B7491851 : Blo 2219435 7491851 := bstep (se 1 (by rfl) ⟨5618888, by rfl⟩ : syracuseStep 7491851 = 11237777) B11237777
theorem B4994567 : Blo 2219435 4994567 := bstep (se 1 (by rfl) ⟨3745925, by rfl⟩ : syracuseStep 4994567 = 7491851) B7491851
theorem B3329711 : Blo 2219435 3329711 := bstep (se 1 (by rfl) ⟨2497283, by rfl⟩ : syracuseStep 3329711 = 4994567) B4994567
theorem B2219807 : Blo 2219435 2219807 := bstep (se 1 (by rfl) ⟨1664855, by rfl⟩ : syracuseStep 2219807 = 3329711) B3329711
theorem B3329717 : Blo 2219435 3329717 := bbase (se 5 (by rfl) ⟨156080, by rfl⟩ : syracuseStep 3329717 = 312161) (by norm_num)
theorem B2219811 : Blo 2219435 2219811 := bstep (se 1 (by rfl) ⟨1664858, by rfl⟩ : syracuseStep 2219811 = 3329717) B3329717
theorem B5618909 : Blo 2219435 5618909 := bbase (se 3 (by rfl) ⟨1053545, by rfl⟩ : syracuseStep 5618909 = 2107091) (by norm_num)
theorem B3745939 : Blo 2219435 3745939 := bstep (se 1 (by rfl) ⟨2809454, by rfl⟩ : syracuseStep 3745939 = 5618909) B5618909
theorem B4994585 : Blo 2219435 4994585 := bstep (se 2 (by rfl) ⟨1872969, by rfl⟩ : syracuseStep 4994585 = 3745939) B3745939
theorem B3329723 : Blo 2219435 3329723 := bstep (se 1 (by rfl) ⟨2497292, by rfl⟩ : syracuseStep 3329723 = 4994585) B4994585
theorem B2219815 : Blo 2219435 2219815 := bstep (se 1 (by rfl) ⟨1664861, by rfl⟩ : syracuseStep 2219815 = 3329723) B3329723
theorem B2497297 : Blo 2219435 2497297 := bbase (se 2 (by rfl) ⟨936486, by rfl⟩ : syracuseStep 2497297 = 1872973) (by norm_num)
theorem B3329729 : Blo 2219435 3329729 := bstep (se 2 (by rfl) ⟨1248648, by rfl⟩ : syracuseStep 3329729 = 2497297) B2497297
theorem B2219819 : Blo 2219435 2219819 := bstep (se 1 (by rfl) ⟨1664864, by rfl⟩ : syracuseStep 2219819 = 3329729) B3329729
theorem B4214197 : Blo 2219435 4214197 := bbase (se 5 (by rfl) ⟨197540, by rfl⟩ : syracuseStep 4214197 = 395081) (by norm_num)
theorem B5618929 : Blo 2219435 5618929 := bstep (se 2 (by rfl) ⟨2107098, by rfl⟩ : syracuseStep 5618929 = 4214197) B4214197
theorem B7491905 : Blo 2219435 7491905 := bstep (se 2 (by rfl) ⟨2809464, by rfl⟩ : syracuseStep 7491905 = 5618929) B5618929
theorem B4994603 : Blo 2219435 4994603 := bstep (se 1 (by rfl) ⟨3745952, by rfl⟩ : syracuseStep 4994603 = 7491905) B7491905
theorem B3329735 : Blo 2219435 3329735 := bstep (se 1 (by rfl) ⟨2497301, by rfl⟩ : syracuseStep 3329735 = 4994603) B4994603
theorem B2219823 : Blo 2219435 2219823 := bstep (se 1 (by rfl) ⟨1664867, by rfl⟩ : syracuseStep 2219823 = 3329735) B3329735
theorem B3329741 : Blo 2219435 3329741 := bbase (se 3 (by rfl) ⟨624326, by rfl⟩ : syracuseStep 3329741 = 1248653) (by norm_num)
theorem B2219827 : Blo 2219435 2219827 := bstep (se 1 (by rfl) ⟨1664870, by rfl⟩ : syracuseStep 2219827 = 3329741) B3329741
theorem B4994621 : Blo 2219435 4994621 := bbase (se 3 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 4994621 = 1872983) (by norm_num)
theorem B3329747 : Blo 2219435 3329747 := bstep (se 1 (by rfl) ⟨2497310, by rfl⟩ : syracuseStep 3329747 = 4994621) B4994621
theorem B2219831 : Blo 2219435 2219831 := bstep (se 1 (by rfl) ⟨1664873, by rfl⟩ : syracuseStep 2219831 = 3329747) B3329747
theorem B3745973 : Blo 2219435 3745973 := bbase (se 5 (by rfl) ⟨175592, by rfl⟩ : syracuseStep 3745973 = 351185) (by norm_num)
theorem B2497315 : Blo 2219435 2497315 := bstep (se 1 (by rfl) ⟨1872986, by rfl⟩ : syracuseStep 2497315 = 3745973) B3745973
theorem B3329753 : Blo 2219435 3329753 := bstep (se 2 (by rfl) ⟨1248657, by rfl⟩ : syracuseStep 3329753 = 2497315) B2497315
theorem B2219835 : Blo 2219435 2219835 := bstep (se 1 (by rfl) ⟨1664876, by rfl⟩ : syracuseStep 2219835 = 3329753) B3329753
theorem B7594181 : Blo 2219435 7594181 := bbase (se 4 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 7594181 = 1423909) (by norm_num)
theorem B5062787 : Blo 2219435 5062787 := bstep (se 1 (by rfl) ⟨3797090, by rfl⟩ : syracuseStep 5062787 = 7594181) B7594181
theorem B3375191 : Blo 2219435 3375191 := bstep (se 1 (by rfl) ⟨2531393, by rfl⟩ : syracuseStep 3375191 = 5062787) B5062787
theorem B2250127 : Blo 2219435 2250127 := bstep (se 1 (by rfl) ⟨1687595, by rfl⟩ : syracuseStep 2250127 = 3375191) B3375191
theorem B3000169 : Blo 2219435 3000169 := bstep (se 2 (by rfl) ⟨1125063, by rfl⟩ : syracuseStep 3000169 = 2250127) B2250127
theorem B4000225 : Blo 2219435 4000225 := bstep (se 2 (by rfl) ⟨1500084, by rfl⟩ : syracuseStep 4000225 = 3000169) B3000169
theorem B5333633 : Blo 2219435 5333633 := bstep (se 2 (by rfl) ⟨2000112, by rfl⟩ : syracuseStep 5333633 = 4000225) B4000225
theorem B3555755 : Blo 2219435 3555755 := bstep (se 1 (by rfl) ⟨2666816, by rfl⟩ : syracuseStep 3555755 = 5333633) B5333633
theorem B2370503 : Blo 2219435 2370503 := bstep (se 1 (by rfl) ⟨1777877, by rfl⟩ : syracuseStep 2370503 = 3555755) B3555755
theorem B6321341 : Blo 2219435 6321341 := bstep (se 3 (by rfl) ⟨1185251, by rfl⟩ : syracuseStep 6321341 = 2370503) B2370503
theorem B16856909 : Blo 2219435 16856909 := bstep (se 3 (by rfl) ⟨3160670, by rfl⟩ : syracuseStep 16856909 = 6321341) B6321341
theorem B11237939 : Blo 2219435 11237939 := bstep (se 1 (by rfl) ⟨8428454, by rfl⟩ : syracuseStep 11237939 = 16856909) B16856909
theorem B7491959 : Blo 2219435 7491959 := bstep (se 1 (by rfl) ⟨5618969, by rfl⟩ : syracuseStep 7491959 = 11237939) B11237939
theorem B4994639 : Blo 2219435 4994639 := bstep (se 1 (by rfl) ⟨3745979, by rfl⟩ : syracuseStep 4994639 = 7491959) B7491959
theorem B3329759 : Blo 2219435 3329759 := bstep (se 1 (by rfl) ⟨2497319, by rfl⟩ : syracuseStep 3329759 = 4994639) B4994639
theorem B2219839 : Blo 2219435 2219839 := bstep (se 1 (by rfl) ⟨1664879, by rfl⟩ : syracuseStep 2219839 = 3329759) B3329759
theorem B3329765 : Blo 2219435 3329765 := bbase (se 4 (by rfl) ⟨312165, by rfl⟩ : syracuseStep 3329765 = 624331) (by norm_num)
theorem B2219843 : Blo 2219435 2219843 := bstep (se 1 (by rfl) ⟨1664882, by rfl⟩ : syracuseStep 2219843 = 3329765) B3329765
theorem B6321365 : Blo 2219435 6321365 := bbase (se 7 (by rfl) ⟨74078, by rfl⟩ : syracuseStep 6321365 = 148157) (by norm_num)
theorem B4214243 : Blo 2219435 4214243 := bstep (se 1 (by rfl) ⟨3160682, by rfl⟩ : syracuseStep 4214243 = 6321365) B6321365
theorem B2809495 : Blo 2219435 2809495 := bstep (se 1 (by rfl) ⟨2107121, by rfl⟩ : syracuseStep 2809495 = 4214243) B4214243
theorem B3745993 : Blo 2219435 3745993 := bstep (se 2 (by rfl) ⟨1404747, by rfl⟩ : syracuseStep 3745993 = 2809495) B2809495
theorem B4994657 : Blo 2219435 4994657 := bstep (se 2 (by rfl) ⟨1872996, by rfl⟩ : syracuseStep 4994657 = 3745993) B3745993
theorem B3329771 : Blo 2219435 3329771 := bstep (se 1 (by rfl) ⟨2497328, by rfl⟩ : syracuseStep 3329771 = 4994657) B4994657
theorem B2219847 : Blo 2219435 2219847 := bstep (se 1 (by rfl) ⟨1664885, by rfl⟩ : syracuseStep 2219847 = 3329771) B3329771
theorem B2497333 : Blo 2219435 2497333 := bbase (se 5 (by rfl) ⟨117062, by rfl⟩ : syracuseStep 2497333 = 234125) (by norm_num)
theorem B3329777 : Blo 2219435 3329777 := bstep (se 2 (by rfl) ⟨1248666, by rfl⟩ : syracuseStep 3329777 = 2497333) B2497333
theorem B2219851 : Blo 2219435 2219851 := bstep (se 1 (by rfl) ⟨1664888, by rfl⟩ : syracuseStep 2219851 = 3329777) B3329777
theorem B2809505 : Blo 2219435 2809505 := bbase (se 2 (by rfl) ⟨1053564, by rfl⟩ : syracuseStep 2809505 = 2107129) (by norm_num)
theorem B7492013 : Blo 2219435 7492013 := bstep (se 3 (by rfl) ⟨1404752, by rfl⟩ : syracuseStep 7492013 = 2809505) B2809505
theorem B4994675 : Blo 2219435 4994675 := bstep (se 1 (by rfl) ⟨3746006, by rfl⟩ : syracuseStep 4994675 = 7492013) B7492013
theorem B3329783 : Blo 2219435 3329783 := bstep (se 1 (by rfl) ⟨2497337, by rfl⟩ : syracuseStep 3329783 = 4994675) B4994675
theorem B2219855 : Blo 2219435 2219855 := bstep (se 1 (by rfl) ⟨1664891, by rfl⟩ : syracuseStep 2219855 = 3329783) B3329783
theorem B3329789 : Blo 2219435 3329789 := bbase (se 3 (by rfl) ⟨624335, by rfl⟩ : syracuseStep 3329789 = 1248671) (by norm_num)
theorem B2219859 : Blo 2219435 2219859 := bstep (se 1 (by rfl) ⟨1664894, by rfl⟩ : syracuseStep 2219859 = 3329789) B3329789
theorem B4994693 : Blo 2219435 4994693 := bbase (se 4 (by rfl) ⟨468252, by rfl⟩ : syracuseStep 4994693 = 936505) (by norm_num)
theorem B3329795 : Blo 2219435 3329795 := bstep (se 1 (by rfl) ⟨2497346, by rfl⟩ : syracuseStep 3329795 = 4994693) B4994693
theorem B2219863 : Blo 2219435 2219863 := bstep (se 1 (by rfl) ⟨1664897, by rfl⟩ : syracuseStep 2219863 = 3329795) B3329795
theorem B5333701 : Blo 2219435 5333701 := bbase (se 4 (by rfl) ⟨500034, by rfl⟩ : syracuseStep 5333701 = 1000069) (by norm_num)
theorem B7111601 : Blo 2219435 7111601 := bstep (se 2 (by rfl) ⟨2666850, by rfl⟩ : syracuseStep 7111601 = 5333701) B5333701
theorem B4741067 : Blo 2219435 4741067 := bstep (se 1 (by rfl) ⟨3555800, by rfl⟩ : syracuseStep 4741067 = 7111601) B7111601
theorem B3160711 : Blo 2219435 3160711 := bstep (se 1 (by rfl) ⟨2370533, by rfl⟩ : syracuseStep 3160711 = 4741067) B4741067
theorem B4214281 : Blo 2219435 4214281 := bstep (se 2 (by rfl) ⟨1580355, by rfl⟩ : syracuseStep 4214281 = 3160711) B3160711
theorem B5619041 : Blo 2219435 5619041 := bstep (se 2 (by rfl) ⟨2107140, by rfl⟩ : syracuseStep 5619041 = 4214281) B4214281
theorem B3746027 : Blo 2219435 3746027 := bstep (se 1 (by rfl) ⟨2809520, by rfl⟩ : syracuseStep 3746027 = 5619041) B5619041
theorem B2497351 : Blo 2219435 2497351 := bstep (se 1 (by rfl) ⟨1873013, by rfl⟩ : syracuseStep 2497351 = 3746027) B3746027
theorem B3329801 : Blo 2219435 3329801 := bstep (se 2 (by rfl) ⟨1248675, by rfl⟩ : syracuseStep 3329801 = 2497351) B2497351
theorem B2219867 : Blo 2219435 2219867 := bstep (se 1 (by rfl) ⟨1664900, by rfl⟩ : syracuseStep 2219867 = 3329801) B3329801
theorem B11238101 : Blo 2219435 11238101 := bbase (se 7 (by rfl) ⟨131696, by rfl⟩ : syracuseStep 11238101 = 263393) (by norm_num)
theorem B7492067 : Blo 2219435 7492067 := bstep (se 1 (by rfl) ⟨5619050, by rfl⟩ : syracuseStep 7492067 = 11238101) B11238101
theorem B4994711 : Blo 2219435 4994711 := bstep (se 1 (by rfl) ⟨3746033, by rfl⟩ : syracuseStep 4994711 = 7492067) B7492067
theorem B3329807 : Blo 2219435 3329807 := bstep (se 1 (by rfl) ⟨2497355, by rfl⟩ : syracuseStep 3329807 = 4994711) B4994711
theorem B2219871 : Blo 2219435 2219871 := bstep (se 1 (by rfl) ⟨1664903, by rfl⟩ : syracuseStep 2219871 = 3329807) B3329807
theorem B3329813 : Blo 2219435 3329813 := bbase (se 6 (by rfl) ⟨78042, by rfl⟩ : syracuseStep 3329813 = 156085) (by norm_num)
theorem B2219875 : Blo 2219435 2219875 := bstep (se 1 (by rfl) ⟨1664906, by rfl⟩ : syracuseStep 2219875 = 3329813) B3329813
theorem B3604333 : Blo 2219435 3604333 := bbase (se 3 (by rfl) ⟨675812, by rfl⟩ : syracuseStep 3604333 = 1351625) (by norm_num)
theorem B4805777 : Blo 2219435 4805777 := bstep (se 2 (by rfl) ⟨1802166, by rfl⟩ : syracuseStep 4805777 = 3604333) B3604333
theorem B12815405 : Blo 2219435 12815405 := bstep (se 3 (by rfl) ⟨2402888, by rfl⟩ : syracuseStep 12815405 = 4805777) B4805777
theorem B8543603 : Blo 2219435 8543603 := bstep (se 1 (by rfl) ⟨6407702, by rfl⟩ : syracuseStep 8543603 = 12815405) B12815405
theorem B22782941 : Blo 2219435 22782941 := bstep (se 3 (by rfl) ⟨4271801, by rfl⟩ : syracuseStep 22782941 = 8543603) B8543603
theorem B15188627 : Blo 2219435 15188627 := bstep (se 1 (by rfl) ⟨11391470, by rfl⟩ : syracuseStep 15188627 = 22782941) B22782941
theorem B10125751 : Blo 2219435 10125751 := bstep (se 1 (by rfl) ⟨7594313, by rfl⟩ : syracuseStep 10125751 = 15188627) B15188627
theorem B13501001 : Blo 2219435 13501001 := bstep (se 2 (by rfl) ⟨5062875, by rfl⟩ : syracuseStep 13501001 = 10125751) B10125751
theorem B9000667 : Blo 2219435 9000667 := bstep (se 1 (by rfl) ⟨6750500, by rfl⟩ : syracuseStep 9000667 = 13501001) B13501001
theorem B12000889 : Blo 2219435 12000889 := bstep (se 2 (by rfl) ⟨4500333, by rfl⟩ : syracuseStep 12000889 = 9000667) B9000667
theorem B64004741 : Blo 2219435 64004741 := bstep (se 4 (by rfl) ⟨6000444, by rfl⟩ : syracuseStep 64004741 = 12000889) B12000889
theorem B42669827 : Blo 2219435 42669827 := bstep (se 1 (by rfl) ⟨32002370, by rfl⟩ : syracuseStep 42669827 = 64004741) B64004741
theorem B28446551 : Blo 2219435 28446551 := bstep (se 1 (by rfl) ⟨21334913, by rfl⟩ : syracuseStep 28446551 = 42669827) B42669827
theorem B18964367 : Blo 2219435 18964367 := bstep (se 1 (by rfl) ⟨14223275, by rfl⟩ : syracuseStep 18964367 = 28446551) B28446551
theorem B12642911 : Blo 2219435 12642911 := bstep (se 1 (by rfl) ⟨9482183, by rfl⟩ : syracuseStep 12642911 = 18964367) B18964367
theorem B8428607 : Blo 2219435 8428607 := bstep (se 1 (by rfl) ⟨6321455, by rfl⟩ : syracuseStep 8428607 = 12642911) B12642911
theorem B5619071 : Blo 2219435 5619071 := bstep (se 1 (by rfl) ⟨4214303, by rfl⟩ : syracuseStep 5619071 = 8428607) B8428607
theorem B3746047 : Blo 2219435 3746047 := bstep (se 1 (by rfl) ⟨2809535, by rfl⟩ : syracuseStep 3746047 = 5619071) B5619071
theorem B4994729 : Blo 2219435 4994729 := bstep (se 2 (by rfl) ⟨1873023, by rfl⟩ : syracuseStep 4994729 = 3746047) B3746047
theorem B3329819 : Blo 2219435 3329819 := bstep (se 1 (by rfl) ⟨2497364, by rfl⟩ : syracuseStep 3329819 = 4994729) B4994729
theorem B2219879 : Blo 2219435 2219879 := bstep (se 1 (by rfl) ⟨1664909, by rfl⟩ : syracuseStep 2219879 = 3329819) B3329819
theorem B2497369 : Blo 2219435 2497369 := bbase (se 2 (by rfl) ⟨936513, by rfl⟩ : syracuseStep 2497369 = 1873027) (by norm_num)
theorem B3329825 : Blo 2219435 3329825 := bstep (se 2 (by rfl) ⟨1248684, by rfl⟩ : syracuseStep 3329825 = 2497369) B2497369
theorem B2219883 : Blo 2219435 2219883 := bstep (se 1 (by rfl) ⟨1664912, by rfl⟩ : syracuseStep 2219883 = 3329825) B3329825
theorem B4741109 : Blo 2219435 4741109 := bbase (se 5 (by rfl) ⟨222239, by rfl⟩ : syracuseStep 4741109 = 444479) (by norm_num)
theorem B3160739 : Blo 2219435 3160739 := bstep (se 1 (by rfl) ⟨2370554, by rfl⟩ : syracuseStep 3160739 = 4741109) B4741109
theorem B8428637 : Blo 2219435 8428637 := bstep (se 3 (by rfl) ⟨1580369, by rfl⟩ : syracuseStep 8428637 = 3160739) B3160739
theorem B5619091 : Blo 2219435 5619091 := bstep (se 1 (by rfl) ⟨4214318, by rfl⟩ : syracuseStep 5619091 = 8428637) B8428637
theorem B7492121 : Blo 2219435 7492121 := bstep (se 2 (by rfl) ⟨2809545, by rfl⟩ : syracuseStep 7492121 = 5619091) B5619091
theorem B4994747 : Blo 2219435 4994747 := bstep (se 1 (by rfl) ⟨3746060, by rfl⟩ : syracuseStep 4994747 = 7492121) B7492121
theorem B3329831 : Blo 2219435 3329831 := bstep (se 1 (by rfl) ⟨2497373, by rfl⟩ : syracuseStep 3329831 = 4994747) B4994747
theorem B2219887 : Blo 2219435 2219887 := bstep (se 1 (by rfl) ⟨1664915, by rfl⟩ : syracuseStep 2219887 = 3329831) B3329831
theorem B3329837 : Blo 2219435 3329837 := bbase (se 3 (by rfl) ⟨624344, by rfl⟩ : syracuseStep 3329837 = 1248689) (by norm_num)
theorem B2219891 : Blo 2219435 2219891 := bstep (se 1 (by rfl) ⟨1664918, by rfl⟩ : syracuseStep 2219891 = 3329837) B3329837
theorem B4994765 : Blo 2219435 4994765 := bbase (se 3 (by rfl) ⟨936518, by rfl⟩ : syracuseStep 4994765 = 1873037) (by norm_num)
theorem B3329843 : Blo 2219435 3329843 := bstep (se 1 (by rfl) ⟨2497382, by rfl⟩ : syracuseStep 3329843 = 4994765) B4994765
theorem B2219895 : Blo 2219435 2219895 := bstep (se 1 (by rfl) ⟨1664921, by rfl⟩ : syracuseStep 2219895 = 3329843) B3329843
theorem B2809561 : Blo 2219435 2809561 := bbase (se 2 (by rfl) ⟨1053585, by rfl⟩ : syracuseStep 2809561 = 2107171) (by norm_num)
theorem B3746081 : Blo 2219435 3746081 := bstep (se 2 (by rfl) ⟨1404780, by rfl⟩ : syracuseStep 3746081 = 2809561) B2809561
theorem B2497387 : Blo 2219435 2497387 := bstep (se 1 (by rfl) ⟨1873040, by rfl⟩ : syracuseStep 2497387 = 3746081) B3746081
theorem B3329849 : Blo 2219435 3329849 := bstep (se 2 (by rfl) ⟨1248693, by rfl⟩ : syracuseStep 3329849 = 2497387) B2497387
theorem B2219899 : Blo 2219435 2219899 := bstep (se 1 (by rfl) ⟨1664924, by rfl⟩ : syracuseStep 2219899 = 3329849) B3329849
theorem B2666893 : Blo 2219435 2666893 := bbase (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) (by norm_num)
theorem B3555857 : Blo 2219435 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B9482285 : Blo 2219435 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B25286093 : Blo 2219435 25286093 := bstep (se 3 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 25286093 = 9482285) B9482285
theorem B16857395 : Blo 2219435 16857395 := bstep (se 1 (by rfl) ⟨12643046, by rfl⟩ : syracuseStep 16857395 = 25286093) B25286093
theorem B11238263 : Blo 2219435 11238263 := bstep (se 1 (by rfl) ⟨8428697, by rfl⟩ : syracuseStep 11238263 = 16857395) B16857395
theorem B7492175 : Blo 2219435 7492175 := bstep (se 1 (by rfl) ⟨5619131, by rfl⟩ : syracuseStep 7492175 = 11238263) B11238263
theorem B4994783 : Blo 2219435 4994783 := bstep (se 1 (by rfl) ⟨3746087, by rfl⟩ : syracuseStep 4994783 = 7492175) B7492175
theorem B3329855 : Blo 2219435 3329855 := bstep (se 1 (by rfl) ⟨2497391, by rfl⟩ : syracuseStep 3329855 = 4994783) B4994783
theorem B2219903 : Blo 2219435 2219903 := bstep (se 1 (by rfl) ⟨1664927, by rfl⟩ : syracuseStep 2219903 = 3329855) B3329855
theorem B3329861 : Blo 2219435 3329861 := bbase (se 4 (by rfl) ⟨312174, by rfl⟩ : syracuseStep 3329861 = 624349) (by norm_num)
theorem B2219907 : Blo 2219435 2219907 := bstep (se 1 (by rfl) ⟨1664930, by rfl⟩ : syracuseStep 2219907 = 3329861) B3329861
theorem B3746101 : Blo 2219435 3746101 := bbase (se 5 (by rfl) ⟨175598, by rfl⟩ : syracuseStep 3746101 = 351197) (by norm_num)
theorem B4994801 : Blo 2219435 4994801 := bstep (se 2 (by rfl) ⟨1873050, by rfl⟩ : syracuseStep 4994801 = 3746101) B3746101
theorem B3329867 : Blo 2219435 3329867 := bstep (se 1 (by rfl) ⟨2497400, by rfl⟩ : syracuseStep 3329867 = 4994801) B4994801
theorem B2219911 : Blo 2219435 2219911 := bstep (se 1 (by rfl) ⟨1664933, by rfl⟩ : syracuseStep 2219911 = 3329867) B3329867
theorem B2497405 : Blo 2219435 2497405 := bbase (se 3 (by rfl) ⟨468263, by rfl⟩ : syracuseStep 2497405 = 936527) (by norm_num)
theorem B3329873 : Blo 2219435 3329873 := bstep (se 2 (by rfl) ⟨1248702, by rfl⟩ : syracuseStep 3329873 = 2497405) B2497405
theorem B2219915 : Blo 2219435 2219915 := bstep (se 1 (by rfl) ⟨1664936, by rfl⟩ : syracuseStep 2219915 = 3329873) B3329873
theorem B7492229 : Blo 2219435 7492229 := bbase (se 4 (by rfl) ⟨702396, by rfl⟩ : syracuseStep 7492229 = 1404793) (by norm_num)
theorem B4994819 : Blo 2219435 4994819 := bstep (se 1 (by rfl) ⟨3746114, by rfl⟩ : syracuseStep 4994819 = 7492229) B7492229
theorem B3329879 : Blo 2219435 3329879 := bstep (se 1 (by rfl) ⟨2497409, by rfl⟩ : syracuseStep 3329879 = 4994819) B4994819
theorem B2219919 : Blo 2219435 2219919 := bstep (se 1 (by rfl) ⟨1664939, by rfl⟩ : syracuseStep 2219919 = 3329879) B3329879
theorem B3329885 : Blo 2219435 3329885 := bbase (se 3 (by rfl) ⟨624353, by rfl⟩ : syracuseStep 3329885 = 1248707) (by norm_num)
theorem B2219923 : Blo 2219435 2219923 := bstep (se 1 (by rfl) ⟨1664942, by rfl⟩ : syracuseStep 2219923 = 3329885) B3329885
theorem B4994837 : Blo 2219435 4994837 := bbase (se 6 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 4994837 = 234133) (by norm_num)
theorem B3329891 : Blo 2219435 3329891 := bstep (se 1 (by rfl) ⟨2497418, by rfl⟩ : syracuseStep 3329891 = 4994837) B4994837
theorem B2219927 : Blo 2219435 2219927 := bstep (se 1 (by rfl) ⟨1664945, by rfl⟩ : syracuseStep 2219927 = 3329891) B3329891
theorem B8428805 : Blo 2219435 8428805 := bbase (se 4 (by rfl) ⟨790200, by rfl⟩ : syracuseStep 8428805 = 1580401) (by norm_num)
theorem B5619203 : Blo 2219435 5619203 := bstep (se 1 (by rfl) ⟨4214402, by rfl⟩ : syracuseStep 5619203 = 8428805) B8428805
theorem B3746135 : Blo 2219435 3746135 := bstep (se 1 (by rfl) ⟨2809601, by rfl⟩ : syracuseStep 3746135 = 5619203) B5619203
theorem B2497423 : Blo 2219435 2497423 := bstep (se 1 (by rfl) ⟨1873067, by rfl⟩ : syracuseStep 2497423 = 3746135) B3746135
theorem B3329897 : Blo 2219435 3329897 := bstep (se 2 (by rfl) ⟨1248711, by rfl⟩ : syracuseStep 3329897 = 2497423) B2497423
theorem B2219931 : Blo 2219435 2219931 := bstep (se 1 (by rfl) ⟨1664948, by rfl⟩ : syracuseStep 2219931 = 3329897) B3329897
theorem B3247645 : Blo 2219435 3247645 := bbase (se 3 (by rfl) ⟨608933, by rfl⟩ : syracuseStep 3247645 = 1217867) (by norm_num)
theorem B4330193 : Blo 2219435 4330193 := bstep (se 2 (by rfl) ⟨1623822, by rfl⟩ : syracuseStep 4330193 = 3247645) B3247645
theorem B11547181 : Blo 2219435 11547181 := bstep (se 3 (by rfl) ⟨2165096, by rfl⟩ : syracuseStep 11547181 = 4330193) B4330193
theorem B15396241 : Blo 2219435 15396241 := bstep (se 2 (by rfl) ⟨5773590, by rfl⟩ : syracuseStep 15396241 = 11547181) B11547181
theorem B20528321 : Blo 2219435 20528321 := bstep (se 2 (by rfl) ⟨7698120, by rfl⟩ : syracuseStep 20528321 = 15396241) B15396241
theorem B54742189 : Blo 2219435 54742189 := bstep (se 3 (by rfl) ⟨10264160, by rfl⟩ : syracuseStep 54742189 = 20528321) B20528321
theorem B72989585 : Blo 2219435 72989585 := bstep (se 2 (by rfl) ⟨27371094, by rfl⟩ : syracuseStep 72989585 = 54742189) B54742189
theorem B48659723 : Blo 2219435 48659723 := bstep (se 1 (by rfl) ⟨36494792, by rfl⟩ : syracuseStep 48659723 = 72989585) B72989585
theorem B32439815 : Blo 2219435 32439815 := bstep (se 1 (by rfl) ⟨24329861, by rfl⟩ : syracuseStep 32439815 = 48659723) B48659723
theorem B21626543 : Blo 2219435 21626543 := bstep (se 1 (by rfl) ⟨16219907, by rfl⟩ : syracuseStep 21626543 = 32439815) B32439815
theorem B14417695 : Blo 2219435 14417695 := bstep (se 1 (by rfl) ⟨10813271, by rfl⟩ : syracuseStep 14417695 = 21626543) B21626543
theorem B76894373 : Blo 2219435 76894373 := bstep (se 4 (by rfl) ⟨7208847, by rfl⟩ : syracuseStep 76894373 = 14417695) B14417695
theorem B51262915 : Blo 2219435 51262915 := bstep (se 1 (by rfl) ⟨38447186, by rfl⟩ : syracuseStep 51262915 = 76894373) B76894373
theorem B68350553 : Blo 2219435 68350553 := bstep (se 2 (by rfl) ⟨25631457, by rfl⟩ : syracuseStep 68350553 = 51262915) B51262915
theorem B45567035 : Blo 2219435 45567035 := bstep (se 1 (by rfl) ⟨34175276, by rfl⟩ : syracuseStep 45567035 = 68350553) B68350553
theorem B30378023 : Blo 2219435 30378023 := bstep (se 1 (by rfl) ⟨22783517, by rfl⟩ : syracuseStep 30378023 = 45567035) B45567035
theorem B20252015 : Blo 2219435 20252015 := bstep (se 1 (by rfl) ⟨15189011, by rfl⟩ : syracuseStep 20252015 = 30378023) B30378023
theorem B13501343 : Blo 2219435 13501343 := bstep (se 1 (by rfl) ⟨10126007, by rfl⟩ : syracuseStep 13501343 = 20252015) B20252015
theorem B9000895 : Blo 2219435 9000895 := bstep (se 1 (by rfl) ⟨6750671, by rfl⟩ : syracuseStep 9000895 = 13501343) B13501343
theorem B12001193 : Blo 2219435 12001193 := bstep (se 2 (by rfl) ⟨4500447, by rfl⟩ : syracuseStep 12001193 = 9000895) B9000895
theorem B8000795 : Blo 2219435 8000795 := bstep (se 1 (by rfl) ⟨6000596, by rfl⟩ : syracuseStep 8000795 = 12001193) B12001193
theorem B5333863 : Blo 2219435 5333863 := bstep (se 1 (by rfl) ⟨4000397, by rfl⟩ : syracuseStep 5333863 = 8000795) B8000795
theorem B7111817 : Blo 2219435 7111817 := bstep (se 2 (by rfl) ⟨2666931, by rfl⟩ : syracuseStep 7111817 = 5333863) B5333863
theorem B4741211 : Blo 2219435 4741211 := bstep (se 1 (by rfl) ⟨3555908, by rfl⟩ : syracuseStep 4741211 = 7111817) B7111817
theorem B12643229 : Blo 2219435 12643229 := bstep (se 3 (by rfl) ⟨2370605, by rfl⟩ : syracuseStep 12643229 = 4741211) B4741211
theorem B8428819 : Blo 2219435 8428819 := bstep (se 1 (by rfl) ⟨6321614, by rfl⟩ : syracuseStep 8428819 = 12643229) B12643229
theorem B11238425 : Blo 2219435 11238425 := bstep (se 2 (by rfl) ⟨4214409, by rfl⟩ : syracuseStep 11238425 = 8428819) B8428819
theorem B7492283 : Blo 2219435 7492283 := bstep (se 1 (by rfl) ⟨5619212, by rfl⟩ : syracuseStep 7492283 = 11238425) B11238425
theorem B4994855 : Blo 2219435 4994855 := bstep (se 1 (by rfl) ⟨3746141, by rfl⟩ : syracuseStep 4994855 = 7492283) B7492283
theorem B3329903 : Blo 2219435 3329903 := bstep (se 1 (by rfl) ⟨2497427, by rfl⟩ : syracuseStep 3329903 = 4994855) B4994855
theorem B2219935 : Blo 2219435 2219935 := bstep (se 1 (by rfl) ⟨1664951, by rfl⟩ : syracuseStep 2219935 = 3329903) B3329903
theorem B3329909 : Blo 2219435 3329909 := bbase (se 5 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 3329909 = 312179) (by norm_num)
theorem B2219939 : Blo 2219435 2219939 := bstep (se 1 (by rfl) ⟨1664954, by rfl⟩ : syracuseStep 2219939 = 3329909) B3329909
theorem B4741229 : Blo 2219435 4741229 := bbase (se 3 (by rfl) ⟨888980, by rfl⟩ : syracuseStep 4741229 = 1777961) (by norm_num)
theorem B3160819 : Blo 2219435 3160819 := bstep (se 1 (by rfl) ⟨2370614, by rfl⟩ : syracuseStep 3160819 = 4741229) B4741229
theorem B4214425 : Blo 2219435 4214425 := bstep (se 2 (by rfl) ⟨1580409, by rfl⟩ : syracuseStep 4214425 = 3160819) B3160819
theorem B5619233 : Blo 2219435 5619233 := bstep (se 2 (by rfl) ⟨2107212, by rfl⟩ : syracuseStep 5619233 = 4214425) B4214425
theorem B3746155 : Blo 2219435 3746155 := bstep (se 1 (by rfl) ⟨2809616, by rfl⟩ : syracuseStep 3746155 = 5619233) B5619233
theorem B4994873 : Blo 2219435 4994873 := bstep (se 2 (by rfl) ⟨1873077, by rfl⟩ : syracuseStep 4994873 = 3746155) B3746155
theorem B3329915 : Blo 2219435 3329915 := bstep (se 1 (by rfl) ⟨2497436, by rfl⟩ : syracuseStep 3329915 = 4994873) B4994873
theorem B2219943 : Blo 2219435 2219943 := bstep (se 1 (by rfl) ⟨1664957, by rfl⟩ : syracuseStep 2219943 = 3329915) B3329915
theorem B2497441 : Blo 2219435 2497441 := bbase (se 2 (by rfl) ⟨936540, by rfl⟩ : syracuseStep 2497441 = 1873081) (by norm_num)
theorem B3329921 : Blo 2219435 3329921 := bstep (se 2 (by rfl) ⟨1248720, by rfl⟩ : syracuseStep 3329921 = 2497441) B2497441
theorem B2219947 : Blo 2219435 2219947 := bstep (se 1 (by rfl) ⟨1664960, by rfl⟩ : syracuseStep 2219947 = 3329921) B3329921
theorem B5619253 : Blo 2219435 5619253 := bbase (se 5 (by rfl) ⟨263402, by rfl⟩ : syracuseStep 5619253 = 526805) (by norm_num)
theorem B7492337 : Blo 2219435 7492337 := bstep (se 2 (by rfl) ⟨2809626, by rfl⟩ : syracuseStep 7492337 = 5619253) B5619253
theorem B4994891 : Blo 2219435 4994891 := bstep (se 1 (by rfl) ⟨3746168, by rfl⟩ : syracuseStep 4994891 = 7492337) B7492337
theorem B3329927 : Blo 2219435 3329927 := bstep (se 1 (by rfl) ⟨2497445, by rfl⟩ : syracuseStep 3329927 = 4994891) B4994891
theorem B2219951 : Blo 2219435 2219951 := bstep (se 1 (by rfl) ⟨1664963, by rfl⟩ : syracuseStep 2219951 = 3329927) B3329927
theorem B3329933 : Blo 2219435 3329933 := bbase (se 3 (by rfl) ⟨624362, by rfl⟩ : syracuseStep 3329933 = 1248725) (by norm_num)
theorem B2219955 : Blo 2219435 2219955 := bstep (se 1 (by rfl) ⟨1664966, by rfl⟩ : syracuseStep 2219955 = 3329933) B3329933
theorem B4994909 : Blo 2219435 4994909 := bbase (se 3 (by rfl) ⟨936545, by rfl⟩ : syracuseStep 4994909 = 1873091) (by norm_num)
theorem B3329939 : Blo 2219435 3329939 := bstep (se 1 (by rfl) ⟨2497454, by rfl⟩ : syracuseStep 3329939 = 4994909) B4994909
theorem B2219959 : Blo 2219435 2219959 := bstep (se 1 (by rfl) ⟨1664969, by rfl⟩ : syracuseStep 2219959 = 3329939) B3329939
theorem B3746189 : Blo 2219435 3746189 := bbase (se 3 (by rfl) ⟨702410, by rfl⟩ : syracuseStep 3746189 = 1404821) (by norm_num)
theorem B2497459 : Blo 2219435 2497459 := bstep (se 1 (by rfl) ⟨1873094, by rfl⟩ : syracuseStep 2497459 = 3746189) B3746189
theorem B3329945 : Blo 2219435 3329945 := bstep (se 2 (by rfl) ⟨1248729, by rfl⟩ : syracuseStep 3329945 = 2497459) B2497459
theorem B2219963 : Blo 2219435 2219963 := bstep (se 1 (by rfl) ⟨1664972, by rfl⟩ : syracuseStep 2219963 = 3329945) B3329945
theorem B2740241 : Blo 2219435 2740241 := bbase (se 2 (by rfl) ⟨1027590, by rfl⟩ : syracuseStep 2740241 = 2055181) (by norm_num)
theorem B7307309 : Blo 2219435 7307309 := bstep (se 3 (by rfl) ⟨1370120, by rfl⟩ : syracuseStep 7307309 = 2740241) B2740241
theorem B4871539 : Blo 2219435 4871539 := bstep (se 1 (by rfl) ⟨3653654, by rfl⟩ : syracuseStep 4871539 = 7307309) B7307309
theorem B6495385 : Blo 2219435 6495385 := bstep (se 2 (by rfl) ⟨2435769, by rfl⟩ : syracuseStep 6495385 = 4871539) B4871539
theorem B8660513 : Blo 2219435 8660513 := bstep (se 2 (by rfl) ⟨3247692, by rfl⟩ : syracuseStep 8660513 = 6495385) B6495385
theorem B5773675 : Blo 2219435 5773675 := bstep (se 1 (by rfl) ⟨4330256, by rfl⟩ : syracuseStep 5773675 = 8660513) B8660513
theorem B7698233 : Blo 2219435 7698233 := bstep (se 2 (by rfl) ⟨2886837, by rfl⟩ : syracuseStep 7698233 = 5773675) B5773675
theorem B5132155 : Blo 2219435 5132155 := bstep (se 1 (by rfl) ⟨3849116, by rfl⟩ : syracuseStep 5132155 = 7698233) B7698233
theorem B6842873 : Blo 2219435 6842873 := bstep (se 2 (by rfl) ⟨2566077, by rfl⟩ : syracuseStep 6842873 = 5132155) B5132155
theorem B4561915 : Blo 2219435 4561915 := bstep (se 1 (by rfl) ⟨3421436, by rfl⟩ : syracuseStep 4561915 = 6842873) B6842873
theorem B6082553 : Blo 2219435 6082553 := bstep (se 2 (by rfl) ⟨2280957, by rfl⟩ : syracuseStep 6082553 = 4561915) B4561915
theorem B4055035 : Blo 2219435 4055035 := bstep (se 1 (by rfl) ⟨3041276, by rfl⟩ : syracuseStep 4055035 = 6082553) B6082553
theorem B5406713 : Blo 2219435 5406713 := bstep (se 2 (by rfl) ⟨2027517, by rfl⟩ : syracuseStep 5406713 = 4055035) B4055035
theorem B3604475 : Blo 2219435 3604475 := bstep (se 1 (by rfl) ⟨2703356, by rfl⟩ : syracuseStep 3604475 = 5406713) B5406713
theorem B153790933 : Blo 2219435 153790933 := bstep (se 7 (by rfl) ⟨1802237, by rfl⟩ : syracuseStep 153790933 = 3604475) B3604475
theorem B205054577 : Blo 2219435 205054577 := bstep (se 2 (by rfl) ⟨76895466, by rfl⟩ : syracuseStep 205054577 = 153790933) B153790933
theorem B136703051 : Blo 2219435 136703051 := bstep (se 1 (by rfl) ⟨102527288, by rfl⟩ : syracuseStep 136703051 = 205054577) B205054577
theorem B91135367 : Blo 2219435 91135367 := bstep (se 1 (by rfl) ⟨68351525, by rfl⟩ : syracuseStep 91135367 = 136703051) B136703051
theorem B60756911 : Blo 2219435 60756911 := bstep (se 1 (by rfl) ⟨45567683, by rfl⟩ : syracuseStep 60756911 = 91135367) B91135367
theorem B40504607 : Blo 2219435 40504607 := bstep (se 1 (by rfl) ⟨30378455, by rfl⟩ : syracuseStep 40504607 = 60756911) B60756911
theorem B27003071 : Blo 2219435 27003071 := bstep (se 1 (by rfl) ⟨20252303, by rfl⟩ : syracuseStep 27003071 = 40504607) B40504607
theorem B18002047 : Blo 2219435 18002047 := bstep (se 1 (by rfl) ⟨13501535, by rfl⟩ : syracuseStep 18002047 = 27003071) B27003071
theorem B24002729 : Blo 2219435 24002729 := bstep (se 2 (by rfl) ⟨9001023, by rfl⟩ : syracuseStep 24002729 = 18002047) B18002047
theorem B16001819 : Blo 2219435 16001819 := bstep (se 1 (by rfl) ⟨12001364, by rfl⟩ : syracuseStep 16001819 = 24002729) B24002729
theorem B10667879 : Blo 2219435 10667879 := bstep (se 1 (by rfl) ⟨8000909, by rfl⟩ : syracuseStep 10667879 = 16001819) B16001819
theorem B7111919 : Blo 2219435 7111919 := bstep (se 1 (by rfl) ⟨5333939, by rfl⟩ : syracuseStep 7111919 = 10667879) B10667879
theorem B18965117 : Blo 2219435 18965117 := bstep (se 3 (by rfl) ⟨3555959, by rfl⟩ : syracuseStep 18965117 = 7111919) B7111919
theorem B12643411 : Blo 2219435 12643411 := bstep (se 1 (by rfl) ⟨9482558, by rfl⟩ : syracuseStep 12643411 = 18965117) B18965117
theorem B16857881 : Blo 2219435 16857881 := bstep (se 2 (by rfl) ⟨6321705, by rfl⟩ : syracuseStep 16857881 = 12643411) B12643411
theorem B11238587 : Blo 2219435 11238587 := bstep (se 1 (by rfl) ⟨8428940, by rfl⟩ : syracuseStep 11238587 = 16857881) B16857881
theorem B7492391 : Blo 2219435 7492391 := bstep (se 1 (by rfl) ⟨5619293, by rfl⟩ : syracuseStep 7492391 = 11238587) B11238587
theorem B4994927 : Blo 2219435 4994927 := bstep (se 1 (by rfl) ⟨3746195, by rfl⟩ : syracuseStep 4994927 = 7492391) B7492391
theorem B3329951 : Blo 2219435 3329951 := bstep (se 1 (by rfl) ⟨2497463, by rfl⟩ : syracuseStep 3329951 = 4994927) B4994927
theorem B2219967 : Blo 2219435 2219967 := bstep (se 1 (by rfl) ⟨1664975, by rfl⟩ : syracuseStep 2219967 = 3329951) B3329951
theorem B3329957 : Blo 2219435 3329957 := bbase (se 4 (by rfl) ⟨312183, by rfl⟩ : syracuseStep 3329957 = 624367) (by norm_num)
theorem B2219971 : Blo 2219435 2219971 := bstep (se 1 (by rfl) ⟨1664978, by rfl⟩ : syracuseStep 2219971 = 3329957) B3329957
theorem B2809657 : Blo 2219435 2809657 := bbase (se 2 (by rfl) ⟨1053621, by rfl⟩ : syracuseStep 2809657 = 2107243) (by norm_num)
theorem B3746209 : Blo 2219435 3746209 := bstep (se 2 (by rfl) ⟨1404828, by rfl⟩ : syracuseStep 3746209 = 2809657) B2809657
theorem B4994945 : Blo 2219435 4994945 := bstep (se 2 (by rfl) ⟨1873104, by rfl⟩ : syracuseStep 4994945 = 3746209) B3746209
theorem B3329963 : Blo 2219435 3329963 := bstep (se 1 (by rfl) ⟨2497472, by rfl⟩ : syracuseStep 3329963 = 4994945) B4994945
theorem B2219975 : Blo 2219435 2219975 := bstep (se 1 (by rfl) ⟨1664981, by rfl⟩ : syracuseStep 2219975 = 3329963) B3329963
theorem B2497477 : Blo 2219435 2497477 := bbase (se 4 (by rfl) ⟨234138, by rfl⟩ : syracuseStep 2497477 = 468277) (by norm_num)
theorem B3329969 : Blo 2219435 3329969 := bstep (se 2 (by rfl) ⟨1248738, by rfl⟩ : syracuseStep 3329969 = 2497477) B2497477
theorem B2219979 : Blo 2219435 2219979 := bstep (se 1 (by rfl) ⟨1664984, by rfl⟩ : syracuseStep 2219979 = 3329969) B3329969
theorem B4214501 : Blo 2219435 4214501 := bbase (se 4 (by rfl) ⟨395109, by rfl⟩ : syracuseStep 4214501 = 790219) (by norm_num)
theorem B2809667 : Blo 2219435 2809667 := bstep (se 1 (by rfl) ⟨2107250, by rfl⟩ : syracuseStep 2809667 = 4214501) B4214501
theorem B7492445 : Blo 2219435 7492445 := bstep (se 3 (by rfl) ⟨1404833, by rfl⟩ : syracuseStep 7492445 = 2809667) B2809667
theorem B4994963 : Blo 2219435 4994963 := bstep (se 1 (by rfl) ⟨3746222, by rfl⟩ : syracuseStep 4994963 = 7492445) B7492445
theorem B3329975 : Blo 2219435 3329975 := bstep (se 1 (by rfl) ⟨2497481, by rfl⟩ : syracuseStep 3329975 = 4994963) B4994963
theorem B2219983 : Blo 2219435 2219983 := bstep (se 1 (by rfl) ⟨1664987, by rfl⟩ : syracuseStep 2219983 = 3329975) B3329975
theorem B3329981 : Blo 2219435 3329981 := bbase (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) (by norm_num)
theorem B2219987 : Blo 2219435 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B4994981 : Blo 2219435 4994981 := bbase (se 4 (by rfl) ⟨468279, by rfl⟩ : syracuseStep 4994981 = 936559) (by norm_num)
theorem B3329987 : Blo 2219435 3329987 := bstep (se 1 (by rfl) ⟨2497490, by rfl⟩ : syracuseStep 3329987 = 4994981) B4994981
theorem B2219991 : Blo 2219435 2219991 := bstep (se 1 (by rfl) ⟨1664993, by rfl⟩ : syracuseStep 2219991 = 3329987) B3329987
theorem B5619365 : Blo 2219435 5619365 := bbase (se 4 (by rfl) ⟨526815, by rfl⟩ : syracuseStep 5619365 = 1053631) (by norm_num)
theorem B3746243 : Blo 2219435 3746243 := bstep (se 1 (by rfl) ⟨2809682, by rfl⟩ : syracuseStep 3746243 = 5619365) B5619365
theorem B2497495 : Blo 2219435 2497495 := bstep (se 1 (by rfl) ⟨1873121, by rfl⟩ : syracuseStep 2497495 = 3746243) B3746243
theorem B3329993 : Blo 2219435 3329993 := bstep (se 2 (by rfl) ⟨1248747, by rfl⟩ : syracuseStep 3329993 = 2497495) B2497495
theorem B2219995 : Blo 2219435 2219995 := bstep (se 1 (by rfl) ⟨1664996, by rfl⟩ : syracuseStep 2219995 = 3329993) B3329993
theorem B6321797 : Blo 2219435 6321797 := bbase (se 4 (by rfl) ⟨592668, by rfl⟩ : syracuseStep 6321797 = 1185337) (by norm_num)
theorem B4214531 : Blo 2219435 4214531 := bstep (se 1 (by rfl) ⟨3160898, by rfl⟩ : syracuseStep 4214531 = 6321797) B6321797
theorem B11238749 : Blo 2219435 11238749 := bstep (se 3 (by rfl) ⟨2107265, by rfl⟩ : syracuseStep 11238749 = 4214531) B4214531
theorem B7492499 : Blo 2219435 7492499 := bstep (se 1 (by rfl) ⟨5619374, by rfl⟩ : syracuseStep 7492499 = 11238749) B11238749
theorem B4994999 : Blo 2219435 4994999 := bstep (se 1 (by rfl) ⟨3746249, by rfl⟩ : syracuseStep 4994999 = 7492499) B7492499
theorem B3329999 : Blo 2219435 3329999 := bstep (se 1 (by rfl) ⟨2497499, by rfl⟩ : syracuseStep 3329999 = 4994999) B4994999
theorem B2219999 : Blo 2219435 2219999 := bstep (se 1 (by rfl) ⟨1664999, by rfl⟩ : syracuseStep 2219999 = 3329999) B3329999
theorem B3330005 : Blo 2219435 3330005 := bbase (se 7 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 3330005 = 78047) (by norm_num)
theorem B2220003 : Blo 2219435 2220003 := bstep (se 1 (by rfl) ⟨1665002, by rfl⟩ : syracuseStep 2220003 = 3330005) B3330005
theorem B8429093 : Blo 2219435 8429093 := bbase (se 4 (by rfl) ⟨790227, by rfl⟩ : syracuseStep 8429093 = 1580455) (by norm_num)
theorem B5619395 : Blo 2219435 5619395 := bstep (se 1 (by rfl) ⟨4214546, by rfl⟩ : syracuseStep 5619395 = 8429093) B8429093
theorem B3746263 : Blo 2219435 3746263 := bstep (se 1 (by rfl) ⟨2809697, by rfl⟩ : syracuseStep 3746263 = 5619395) B5619395
theorem B4995017 : Blo 2219435 4995017 := bstep (se 2 (by rfl) ⟨1873131, by rfl⟩ : syracuseStep 4995017 = 3746263) B3746263
theorem B3330011 : Blo 2219435 3330011 := bstep (se 1 (by rfl) ⟨2497508, by rfl⟩ : syracuseStep 3330011 = 4995017) B4995017
theorem B2220007 : Blo 2219435 2220007 := bstep (se 1 (by rfl) ⟨1665005, by rfl⟩ : syracuseStep 2220007 = 3330011) B3330011
theorem B2497513 : Blo 2219435 2497513 := bbase (se 2 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 2497513 = 1873135) (by norm_num)
theorem B3330017 : Blo 2219435 3330017 := bstep (se 2 (by rfl) ⟨1248756, by rfl⟩ : syracuseStep 3330017 = 2497513) B2497513
theorem B2220011 : Blo 2219435 2220011 := bstep (se 1 (by rfl) ⟨1665008, by rfl⟩ : syracuseStep 2220011 = 3330017) B3330017
theorem B3556037 : Blo 2219435 3556037 := bbase (se 4 (by rfl) ⟨333378, by rfl⟩ : syracuseStep 3556037 = 666757) (by norm_num)
theorem B2370691 : Blo 2219435 2370691 := bstep (se 1 (by rfl) ⟨1778018, by rfl⟩ : syracuseStep 2370691 = 3556037) B3556037
theorem B12643685 : Blo 2219435 12643685 := bstep (se 4 (by rfl) ⟨1185345, by rfl⟩ : syracuseStep 12643685 = 2370691) B2370691
theorem B8429123 : Blo 2219435 8429123 := bstep (se 1 (by rfl) ⟨6321842, by rfl⟩ : syracuseStep 8429123 = 12643685) B12643685
theorem B5619415 : Blo 2219435 5619415 := bstep (se 1 (by rfl) ⟨4214561, by rfl⟩ : syracuseStep 5619415 = 8429123) B8429123
theorem B7492553 : Blo 2219435 7492553 := bstep (se 2 (by rfl) ⟨2809707, by rfl⟩ : syracuseStep 7492553 = 5619415) B5619415
theorem B4995035 : Blo 2219435 4995035 := bstep (se 1 (by rfl) ⟨3746276, by rfl⟩ : syracuseStep 4995035 = 7492553) B7492553
theorem B3330023 : Blo 2219435 3330023 := bstep (se 1 (by rfl) ⟨2497517, by rfl⟩ : syracuseStep 3330023 = 4995035) B4995035
theorem B2220015 : Blo 2219435 2220015 := bstep (se 1 (by rfl) ⟨1665011, by rfl⟩ : syracuseStep 2220015 = 3330023) B3330023
theorem B3330029 : Blo 2219435 3330029 := bbase (se 3 (by rfl) ⟨624380, by rfl⟩ : syracuseStep 3330029 = 1248761) (by norm_num)
theorem B2220019 : Blo 2219435 2220019 := bstep (se 1 (by rfl) ⟨1665014, by rfl⟩ : syracuseStep 2220019 = 3330029) B3330029
theorem B4995053 : Blo 2219435 4995053 := bbase (se 3 (by rfl) ⟨936572, by rfl⟩ : syracuseStep 4995053 = 1873145) (by norm_num)
theorem B3330035 : Blo 2219435 3330035 := bstep (se 1 (by rfl) ⟨2497526, by rfl⟩ : syracuseStep 3330035 = 4995053) B4995053
theorem B2220023 : Blo 2219435 2220023 := bstep (se 1 (by rfl) ⟨1665017, by rfl⟩ : syracuseStep 2220023 = 3330035) B3330035
theorem B4000565 : Blo 2219435 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B2667043 : Blo 2219435 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B3556057 : Blo 2219435 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B4741409 : Blo 2219435 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B3160939 : Blo 2219435 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B4214585 : Blo 2219435 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B2809723 : Blo 2219435 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B3746297 : Blo 2219435 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B2497531 : Blo 2219435 2497531 := bstep (se 1 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 2497531 = 3746297) B3746297
theorem B3330041 : Blo 2219435 3330041 := bstep (se 2 (by rfl) ⟨1248765, by rfl⟩ : syracuseStep 3330041 = 2497531) B2497531
theorem B2220027 : Blo 2219435 2220027 := bstep (se 1 (by rfl) ⟨1665020, by rfl⟩ : syracuseStep 2220027 = 3330041) B3330041
theorem B4871677 : Blo 2219435 4871677 := bbase (se 3 (by rfl) ⟨913439, by rfl⟩ : syracuseStep 4871677 = 1826879) (by norm_num)
theorem B6495569 : Blo 2219435 6495569 := bstep (se 2 (by rfl) ⟨2435838, by rfl⟩ : syracuseStep 6495569 = 4871677) B4871677
theorem B4330379 : Blo 2219435 4330379 := bstep (se 1 (by rfl) ⟨3247784, by rfl⟩ : syracuseStep 4330379 = 6495569) B6495569
theorem B11547677 : Blo 2219435 11547677 := bstep (se 3 (by rfl) ⟨2165189, by rfl⟩ : syracuseStep 11547677 = 4330379) B4330379
theorem B7698451 : Blo 2219435 7698451 := bstep (se 1 (by rfl) ⟨5773838, by rfl⟩ : syracuseStep 7698451 = 11547677) B11547677
theorem B10264601 : Blo 2219435 10264601 := bstep (se 2 (by rfl) ⟨3849225, by rfl⟩ : syracuseStep 10264601 = 7698451) B7698451
theorem B6843067 : Blo 2219435 6843067 := bstep (se 1 (by rfl) ⟨5132300, by rfl⟩ : syracuseStep 6843067 = 10264601) B10264601
theorem B145985429 : Blo 2219435 145985429 := bstep (se 6 (by rfl) ⟨3421533, by rfl⟩ : syracuseStep 145985429 = 6843067) B6843067
theorem B97323619 : Blo 2219435 97323619 := bstep (se 1 (by rfl) ⟨72992714, by rfl⟩ : syracuseStep 97323619 = 145985429) B145985429
theorem B129764825 : Blo 2219435 129764825 := bstep (se 2 (by rfl) ⟨48661809, by rfl⟩ : syracuseStep 129764825 = 97323619) B97323619
theorem B86509883 : Blo 2219435 86509883 := bstep (se 1 (by rfl) ⟨64882412, by rfl⟩ : syracuseStep 86509883 = 129764825) B129764825
theorem B57673255 : Blo 2219435 57673255 := bstep (se 1 (by rfl) ⟨43254941, by rfl⟩ : syracuseStep 57673255 = 86509883) B86509883
theorem B76897673 : Blo 2219435 76897673 := bstep (se 2 (by rfl) ⟨28836627, by rfl⟩ : syracuseStep 76897673 = 57673255) B57673255
theorem B51265115 : Blo 2219435 51265115 := bstep (se 1 (by rfl) ⟨38448836, by rfl⟩ : syracuseStep 51265115 = 76897673) B76897673
theorem B34176743 : Blo 2219435 34176743 := bstep (se 1 (by rfl) ⟨25632557, by rfl⟩ : syracuseStep 34176743 = 51265115) B51265115
theorem B22784495 : Blo 2219435 22784495 := bstep (se 1 (by rfl) ⟨17088371, by rfl⟩ : syracuseStep 22784495 = 34176743) B34176743
theorem B243034613 : Blo 2219435 243034613 := bstep (se 5 (by rfl) ⟨11392247, by rfl⟩ : syracuseStep 243034613 = 22784495) B22784495
theorem B162023075 : Blo 2219435 162023075 := bstep (se 1 (by rfl) ⟨121517306, by rfl⟩ : syracuseStep 162023075 = 243034613) B243034613
theorem B108015383 : Blo 2219435 108015383 := bstep (se 1 (by rfl) ⟨81011537, by rfl⟩ : syracuseStep 108015383 = 162023075) B162023075
theorem B288041021 : Blo 2219435 288041021 := bstep (se 3 (by rfl) ⟨54007691, by rfl⟩ : syracuseStep 288041021 = 108015383) B108015383
theorem B192027347 : Blo 2219435 192027347 := bstep (se 1 (by rfl) ⟨144020510, by rfl⟩ : syracuseStep 192027347 = 288041021) B288041021
theorem B128018231 : Blo 2219435 128018231 := bstep (se 1 (by rfl) ⟨96013673, by rfl⟩ : syracuseStep 128018231 = 192027347) B192027347
theorem B85345487 : Blo 2219435 85345487 := bstep (se 1 (by rfl) ⟨64009115, by rfl⟩ : syracuseStep 85345487 = 128018231) B128018231
theorem B56896991 : Blo 2219435 56896991 := bstep (se 1 (by rfl) ⟨42672743, by rfl⟩ : syracuseStep 56896991 = 85345487) B85345487
theorem B37931327 : Blo 2219435 37931327 := bstep (se 1 (by rfl) ⟨28448495, by rfl⟩ : syracuseStep 37931327 = 56896991) B56896991
theorem B25287551 : Blo 2219435 25287551 := bstep (se 1 (by rfl) ⟨18965663, by rfl⟩ : syracuseStep 25287551 = 37931327) B37931327
theorem B16858367 : Blo 2219435 16858367 := bstep (se 1 (by rfl) ⟨12643775, by rfl⟩ : syracuseStep 16858367 = 25287551) B25287551
theorem B11238911 : Blo 2219435 11238911 := bstep (se 1 (by rfl) ⟨8429183, by rfl⟩ : syracuseStep 11238911 = 16858367) B16858367
theorem B7492607 : Blo 2219435 7492607 := bstep (se 1 (by rfl) ⟨5619455, by rfl⟩ : syracuseStep 7492607 = 11238911) B11238911
theorem B4995071 : Blo 2219435 4995071 := bstep (se 1 (by rfl) ⟨3746303, by rfl⟩ : syracuseStep 4995071 = 7492607) B7492607
theorem B3330047 : Blo 2219435 3330047 := bstep (se 1 (by rfl) ⟨2497535, by rfl⟩ : syracuseStep 3330047 = 4995071) B4995071
theorem B2220031 : Blo 2219435 2220031 := bstep (se 1 (by rfl) ⟨1665023, by rfl⟩ : syracuseStep 2220031 = 3330047) B3330047
theorem B3330053 : Blo 2219435 3330053 := bbase (se 4 (by rfl) ⟨312192, by rfl⟩ : syracuseStep 3330053 = 624385) (by norm_num)
theorem B2220035 : Blo 2219435 2220035 := bstep (se 1 (by rfl) ⟨1665026, by rfl⟩ : syracuseStep 2220035 = 3330053) B3330053
theorem B3746317 : Blo 2219435 3746317 := bbase (se 3 (by rfl) ⟨702434, by rfl⟩ : syracuseStep 3746317 = 1404869) (by norm_num)
theorem B4995089 : Blo 2219435 4995089 := bstep (se 2 (by rfl) ⟨1873158, by rfl⟩ : syracuseStep 4995089 = 3746317) B3746317
theorem B3330059 : Blo 2219435 3330059 := bstep (se 1 (by rfl) ⟨2497544, by rfl⟩ : syracuseStep 3330059 = 4995089) B4995089
theorem B2220039 : Blo 2219435 2220039 := bstep (se 1 (by rfl) ⟨1665029, by rfl⟩ : syracuseStep 2220039 = 3330059) B3330059
theorem B2497549 : Blo 2219435 2497549 := bbase (se 3 (by rfl) ⟨468290, by rfl⟩ : syracuseStep 2497549 = 936581) (by norm_num)
theorem B3330065 : Blo 2219435 3330065 := bstep (se 2 (by rfl) ⟨1248774, by rfl⟩ : syracuseStep 3330065 = 2497549) B2497549
theorem B2220043 : Blo 2219435 2220043 := bstep (se 1 (by rfl) ⟨1665032, by rfl⟩ : syracuseStep 2220043 = 3330065) B3330065
theorem B7492661 : Blo 2219435 7492661 := bbase (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) (by norm_num)
theorem B4995107 : Blo 2219435 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B3330071 : Blo 2219435 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B2220047 : Blo 2219435 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B3330077 : Blo 2219435 3330077 := bbase (se 3 (by rfl) ⟨624389, by rfl⟩ : syracuseStep 3330077 = 1248779) (by norm_num)
theorem B2220051 : Blo 2219435 2220051 := bstep (se 1 (by rfl) ⟨1665038, by rfl⟩ : syracuseStep 2220051 = 3330077) B3330077
theorem B4995125 : Blo 2219435 4995125 := bbase (se 5 (by rfl) ⟨234146, by rfl⟩ : syracuseStep 4995125 = 468293) (by norm_num)
theorem B3330083 : Blo 2219435 3330083 := bstep (se 1 (by rfl) ⟨2497562, by rfl⟩ : syracuseStep 3330083 = 4995125) B4995125
theorem B2220055 : Blo 2219435 2220055 := bstep (se 1 (by rfl) ⟨1665041, by rfl⟩ : syracuseStep 2220055 = 3330083) B3330083
theorem B16002485 : Blo 2219435 16002485 := bbase (se 5 (by rfl) ⟨750116, by rfl⟩ : syracuseStep 16002485 = 1500233) (by norm_num)
theorem B10668323 : Blo 2219435 10668323 := bstep (se 1 (by rfl) ⟨8001242, by rfl⟩ : syracuseStep 10668323 = 16002485) B16002485
theorem B7112215 : Blo 2219435 7112215 := bstep (se 1 (by rfl) ⟨5334161, by rfl⟩ : syracuseStep 7112215 = 10668323) B10668323
theorem B9482953 : Blo 2219435 9482953 := bstep (se 2 (by rfl) ⟨3556107, by rfl⟩ : syracuseStep 9482953 = 7112215) B7112215
theorem B12643937 : Blo 2219435 12643937 := bstep (se 2 (by rfl) ⟨4741476, by rfl⟩ : syracuseStep 12643937 = 9482953) B9482953
theorem B8429291 : Blo 2219435 8429291 := bstep (se 1 (by rfl) ⟨6321968, by rfl⟩ : syracuseStep 8429291 = 12643937) B12643937
theorem B5619527 : Blo 2219435 5619527 := bstep (se 1 (by rfl) ⟨4214645, by rfl⟩ : syracuseStep 5619527 = 8429291) B8429291
theorem B3746351 : Blo 2219435 3746351 := bstep (se 1 (by rfl) ⟨2809763, by rfl⟩ : syracuseStep 3746351 = 5619527) B5619527
theorem B2497567 : Blo 2219435 2497567 := bstep (se 1 (by rfl) ⟨1873175, by rfl⟩ : syracuseStep 2497567 = 3746351) B3746351
theorem B3330089 : Blo 2219435 3330089 := bstep (se 2 (by rfl) ⟨1248783, by rfl⟩ : syracuseStep 3330089 = 2497567) B2497567
theorem B2220059 : Blo 2219435 2220059 := bstep (se 1 (by rfl) ⟨1665044, by rfl⟩ : syracuseStep 2220059 = 3330089) B3330089
theorem B10668341 : Blo 2219435 10668341 := bbase (se 5 (by rfl) ⟨500078, by rfl⟩ : syracuseStep 10668341 = 1000157) (by norm_num)
theorem B7112227 : Blo 2219435 7112227 := bstep (se 1 (by rfl) ⟨5334170, by rfl⟩ : syracuseStep 7112227 = 10668341) B10668341
theorem B9482969 : Blo 2219435 9482969 := bstep (se 2 (by rfl) ⟨3556113, by rfl⟩ : syracuseStep 9482969 = 7112227) B7112227
theorem B6321979 : Blo 2219435 6321979 := bstep (se 1 (by rfl) ⟨4741484, by rfl⟩ : syracuseStep 6321979 = 9482969) B9482969
theorem B8429305 : Blo 2219435 8429305 := bstep (se 2 (by rfl) ⟨3160989, by rfl⟩ : syracuseStep 8429305 = 6321979) B6321979
theorem B11239073 : Blo 2219435 11239073 := bstep (se 2 (by rfl) ⟨4214652, by rfl⟩ : syracuseStep 11239073 = 8429305) B8429305
theorem B7492715 : Blo 2219435 7492715 := bstep (se 1 (by rfl) ⟨5619536, by rfl⟩ : syracuseStep 7492715 = 11239073) B11239073
theorem B4995143 : Blo 2219435 4995143 := bstep (se 1 (by rfl) ⟨3746357, by rfl⟩ : syracuseStep 4995143 = 7492715) B7492715
theorem B3330095 : Blo 2219435 3330095 := bstep (se 1 (by rfl) ⟨2497571, by rfl⟩ : syracuseStep 3330095 = 4995143) B4995143
theorem B2220063 : Blo 2219435 2220063 := bstep (se 1 (by rfl) ⟨1665047, by rfl⟩ : syracuseStep 2220063 = 3330095) B3330095
theorem B3330101 : Blo 2219435 3330101 := bbase (se 5 (by rfl) ⟨156098, by rfl⟩ : syracuseStep 3330101 = 312197) (by norm_num)
theorem B2220067 : Blo 2219435 2220067 := bstep (se 1 (by rfl) ⟨1665050, by rfl⟩ : syracuseStep 2220067 = 3330101) B3330101
theorem B5619557 : Blo 2219435 5619557 := bbase (se 4 (by rfl) ⟨526833, by rfl⟩ : syracuseStep 5619557 = 1053667) (by norm_num)
theorem B3746371 : Blo 2219435 3746371 := bstep (se 1 (by rfl) ⟨2809778, by rfl⟩ : syracuseStep 3746371 = 5619557) B5619557
theorem B4995161 : Blo 2219435 4995161 := bstep (se 2 (by rfl) ⟨1873185, by rfl⟩ : syracuseStep 4995161 = 3746371) B3746371
theorem B3330107 : Blo 2219435 3330107 := bstep (se 1 (by rfl) ⟨2497580, by rfl⟩ : syracuseStep 3330107 = 4995161) B4995161
theorem B2220071 : Blo 2219435 2220071 := bstep (se 1 (by rfl) ⟨1665053, by rfl⟩ : syracuseStep 2220071 = 3330107) B3330107
theorem B2497585 : Blo 2219435 2497585 := bbase (se 2 (by rfl) ⟨936594, by rfl⟩ : syracuseStep 2497585 = 1873189) (by norm_num)
theorem B3330113 : Blo 2219435 3330113 := bstep (se 2 (by rfl) ⟨1248792, by rfl⟩ : syracuseStep 3330113 = 2497585) B2497585
theorem B2220075 : Blo 2219435 2220075 := bstep (se 1 (by rfl) ⟨1665056, by rfl⟩ : syracuseStep 2220075 = 3330113) B3330113
theorem B3000493 : Blo 2219435 3000493 := bbase (se 3 (by rfl) ⟨562592, by rfl⟩ : syracuseStep 3000493 = 1125185) (by norm_num)
theorem B16002629 : Blo 2219435 16002629 := bstep (se 4 (by rfl) ⟨1500246, by rfl⟩ : syracuseStep 16002629 = 3000493) B3000493
theorem B10668419 : Blo 2219435 10668419 := bstep (se 1 (by rfl) ⟨8001314, by rfl⟩ : syracuseStep 10668419 = 16002629) B16002629
theorem B7112279 : Blo 2219435 7112279 := bstep (se 1 (by rfl) ⟨5334209, by rfl⟩ : syracuseStep 7112279 = 10668419) B10668419
theorem B4741519 : Blo 2219435 4741519 := bstep (se 1 (by rfl) ⟨3556139, by rfl⟩ : syracuseStep 4741519 = 7112279) B7112279
theorem B6322025 : Blo 2219435 6322025 := bstep (se 2 (by rfl) ⟨2370759, by rfl⟩ : syracuseStep 6322025 = 4741519) B4741519
theorem B4214683 : Blo 2219435 4214683 := bstep (se 1 (by rfl) ⟨3161012, by rfl⟩ : syracuseStep 4214683 = 6322025) B6322025
theorem B5619577 : Blo 2219435 5619577 := bstep (se 2 (by rfl) ⟨2107341, by rfl⟩ : syracuseStep 5619577 = 4214683) B4214683
theorem B7492769 : Blo 2219435 7492769 := bstep (se 2 (by rfl) ⟨2809788, by rfl⟩ : syracuseStep 7492769 = 5619577) B5619577
theorem B4995179 : Blo 2219435 4995179 := bstep (se 1 (by rfl) ⟨3746384, by rfl⟩ : syracuseStep 4995179 = 7492769) B7492769
theorem B3330119 : Blo 2219435 3330119 := bstep (se 1 (by rfl) ⟨2497589, by rfl⟩ : syracuseStep 3330119 = 4995179) B4995179
theorem B2220079 : Blo 2219435 2220079 := bstep (se 1 (by rfl) ⟨1665059, by rfl⟩ : syracuseStep 2220079 = 3330119) B3330119
theorem B3330125 : Blo 2219435 3330125 := bbase (se 3 (by rfl) ⟨624398, by rfl⟩ : syracuseStep 3330125 = 1248797) (by norm_num)
theorem B2220083 : Blo 2219435 2220083 := bstep (se 1 (by rfl) ⟨1665062, by rfl⟩ : syracuseStep 2220083 = 3330125) B3330125
theorem B4995197 : Blo 2219435 4995197 := bbase (se 3 (by rfl) ⟨936599, by rfl⟩ : syracuseStep 4995197 = 1873199) (by norm_num)
theorem B3330131 : Blo 2219435 3330131 := bstep (se 1 (by rfl) ⟨2497598, by rfl⟩ : syracuseStep 3330131 = 4995197) B4995197
theorem B2220087 : Blo 2219435 2220087 := bstep (se 1 (by rfl) ⟨1665065, by rfl⟩ : syracuseStep 2220087 = 3330131) B3330131
theorem B3746405 : Blo 2219435 3746405 := bbase (se 4 (by rfl) ⟨351225, by rfl⟩ : syracuseStep 3746405 = 702451) (by norm_num)
theorem B2497603 : Blo 2219435 2497603 := bstep (se 1 (by rfl) ⟨1873202, by rfl⟩ : syracuseStep 2497603 = 3746405) B3746405
theorem B3330137 : Blo 2219435 3330137 := bstep (se 2 (by rfl) ⟨1248801, by rfl⟩ : syracuseStep 3330137 = 2497603) B2497603
theorem B2220091 : Blo 2219435 2220091 := bstep (se 1 (by rfl) ⟨1665068, by rfl⟩ : syracuseStep 2220091 = 3330137) B3330137
theorem B3556165 : Blo 2219435 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B4741553 : Blo 2219435 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B3161035 : Blo 2219435 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B16858853 : Blo 2219435 16858853 := bstep (se 4 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 16858853 = 3161035) B3161035
theorem B11239235 : Blo 2219435 11239235 := bstep (se 1 (by rfl) ⟨8429426, by rfl⟩ : syracuseStep 11239235 = 16858853) B16858853
theorem B7492823 : Blo 2219435 7492823 := bstep (se 1 (by rfl) ⟨5619617, by rfl⟩ : syracuseStep 7492823 = 11239235) B11239235
theorem B4995215 : Blo 2219435 4995215 := bstep (se 1 (by rfl) ⟨3746411, by rfl⟩ : syracuseStep 4995215 = 7492823) B7492823
theorem B3330143 : Blo 2219435 3330143 := bstep (se 1 (by rfl) ⟨2497607, by rfl⟩ : syracuseStep 3330143 = 4995215) B4995215
theorem B2220095 : Blo 2219435 2220095 := bstep (se 1 (by rfl) ⟨1665071, by rfl⟩ : syracuseStep 2220095 = 3330143) B3330143
theorem B3330149 : Blo 2219435 3330149 := bbase (se 4 (by rfl) ⟨312201, by rfl⟩ : syracuseStep 3330149 = 624403) (by norm_num)
theorem B2220099 : Blo 2219435 2220099 := bstep (se 1 (by rfl) ⟨1665074, by rfl⟩ : syracuseStep 2220099 = 3330149) B3330149
theorem B7112357 : Blo 2219435 7112357 := bbase (se 4 (by rfl) ⟨666783, by rfl⟩ : syracuseStep 7112357 = 1333567) (by norm_num)
theorem B4741571 : Blo 2219435 4741571 := bstep (se 1 (by rfl) ⟨3556178, by rfl⟩ : syracuseStep 4741571 = 7112357) B7112357
theorem B3161047 : Blo 2219435 3161047 := bstep (se 1 (by rfl) ⟨2370785, by rfl⟩ : syracuseStep 3161047 = 4741571) B4741571
theorem B4214729 : Blo 2219435 4214729 := bstep (se 2 (by rfl) ⟨1580523, by rfl⟩ : syracuseStep 4214729 = 3161047) B3161047
theorem B2809819 : Blo 2219435 2809819 := bstep (se 1 (by rfl) ⟨2107364, by rfl⟩ : syracuseStep 2809819 = 4214729) B4214729
theorem B3746425 : Blo 2219435 3746425 := bstep (se 2 (by rfl) ⟨1404909, by rfl⟩ : syracuseStep 3746425 = 2809819) B2809819
theorem B4995233 : Blo 2219435 4995233 := bstep (se 2 (by rfl) ⟨1873212, by rfl⟩ : syracuseStep 4995233 = 3746425) B3746425
theorem B3330155 : Blo 2219435 3330155 := bstep (se 1 (by rfl) ⟨2497616, by rfl⟩ : syracuseStep 3330155 = 4995233) B4995233
theorem B2220103 : Blo 2219435 2220103 := bstep (se 1 (by rfl) ⟨1665077, by rfl⟩ : syracuseStep 2220103 = 3330155) B3330155
theorem B2497621 : Blo 2219435 2497621 := bbase (se 8 (by rfl) ⟨14634, by rfl⟩ : syracuseStep 2497621 = 29269) (by norm_num)
theorem B3330161 : Blo 2219435 3330161 := bstep (se 2 (by rfl) ⟨1248810, by rfl⟩ : syracuseStep 3330161 = 2497621) B2497621
theorem B2220107 : Blo 2219435 2220107 := bstep (se 1 (by rfl) ⟨1665080, by rfl⟩ : syracuseStep 2220107 = 3330161) B3330161
theorem B2809829 : Blo 2219435 2809829 := bbase (se 4 (by rfl) ⟨263421, by rfl⟩ : syracuseStep 2809829 = 526843) (by norm_num)
theorem B7492877 : Blo 2219435 7492877 := bstep (se 3 (by rfl) ⟨1404914, by rfl⟩ : syracuseStep 7492877 = 2809829) B2809829
theorem B4995251 : Blo 2219435 4995251 := bstep (se 1 (by rfl) ⟨3746438, by rfl⟩ : syracuseStep 4995251 = 7492877) B7492877
theorem B3330167 : Blo 2219435 3330167 := bstep (se 1 (by rfl) ⟨2497625, by rfl⟩ : syracuseStep 3330167 = 4995251) B4995251
theorem B2220111 : Blo 2219435 2220111 := bstep (se 1 (by rfl) ⟨1665083, by rfl⟩ : syracuseStep 2220111 = 3330167) B3330167
theorem B3330173 : Blo 2219435 3330173 := bbase (se 3 (by rfl) ⟨624407, by rfl⟩ : syracuseStep 3330173 = 1248815) (by norm_num)
theorem B2220115 : Blo 2219435 2220115 := bstep (se 1 (by rfl) ⟨1665086, by rfl⟩ : syracuseStep 2220115 = 3330173) B3330173
theorem B4995269 : Blo 2219435 4995269 := bbase (se 4 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 4995269 = 936613) (by norm_num)
theorem B3330179 : Blo 2219435 3330179 := bstep (se 1 (by rfl) ⟨2497634, by rfl⟩ : syracuseStep 3330179 = 4995269) B4995269
theorem B2220119 : Blo 2219435 2220119 := bstep (se 1 (by rfl) ⟨1665089, by rfl⟩ : syracuseStep 2220119 = 3330179) B3330179
theorem B4500829 : Blo 2219435 4500829 := bbase (se 3 (by rfl) ⟨843905, by rfl⟩ : syracuseStep 4500829 = 1687811) (by norm_num)
theorem B24004421 : Blo 2219435 24004421 := bstep (se 4 (by rfl) ⟨2250414, by rfl⟩ : syracuseStep 24004421 = 4500829) B4500829
theorem B16002947 : Blo 2219435 16002947 := bstep (se 1 (by rfl) ⟨12002210, by rfl⟩ : syracuseStep 16002947 = 24004421) B24004421
theorem B10668631 : Blo 2219435 10668631 := bstep (se 1 (by rfl) ⟨8001473, by rfl⟩ : syracuseStep 10668631 = 16002947) B16002947
theorem B14224841 : Blo 2219435 14224841 := bstep (se 2 (by rfl) ⟨5334315, by rfl⟩ : syracuseStep 14224841 = 10668631) B10668631
theorem B9483227 : Blo 2219435 9483227 := bstep (se 1 (by rfl) ⟨7112420, by rfl⟩ : syracuseStep 9483227 = 14224841) B14224841
theorem B6322151 : Blo 2219435 6322151 := bstep (se 1 (by rfl) ⟨4741613, by rfl⟩ : syracuseStep 6322151 = 9483227) B9483227
theorem B4214767 : Blo 2219435 4214767 := bstep (se 1 (by rfl) ⟨3161075, by rfl⟩ : syracuseStep 4214767 = 6322151) B6322151
theorem B5619689 : Blo 2219435 5619689 := bstep (se 2 (by rfl) ⟨2107383, by rfl⟩ : syracuseStep 5619689 = 4214767) B4214767
theorem B3746459 : Blo 2219435 3746459 := bstep (se 1 (by rfl) ⟨2809844, by rfl⟩ : syracuseStep 3746459 = 5619689) B5619689
theorem B2497639 : Blo 2219435 2497639 := bstep (se 1 (by rfl) ⟨1873229, by rfl⟩ : syracuseStep 2497639 = 3746459) B3746459
theorem B3330185 : Blo 2219435 3330185 := bstep (se 2 (by rfl) ⟨1248819, by rfl⟩ : syracuseStep 3330185 = 2497639) B2497639
theorem B2220123 : Blo 2219435 2220123 := bstep (se 1 (by rfl) ⟨1665092, by rfl⟩ : syracuseStep 2220123 = 3330185) B3330185
theorem B11239397 : Blo 2219435 11239397 := bbase (se 4 (by rfl) ⟨1053693, by rfl⟩ : syracuseStep 11239397 = 2107387) (by norm_num)
theorem B7492931 : Blo 2219435 7492931 := bstep (se 1 (by rfl) ⟨5619698, by rfl⟩ : syracuseStep 7492931 = 11239397) B11239397
theorem B4995287 : Blo 2219435 4995287 := bstep (se 1 (by rfl) ⟨3746465, by rfl⟩ : syracuseStep 4995287 = 7492931) B7492931
theorem B3330191 : Blo 2219435 3330191 := bstep (se 1 (by rfl) ⟨2497643, by rfl⟩ : syracuseStep 3330191 = 4995287) B4995287
theorem B2220127 : Blo 2219435 2220127 := bstep (se 1 (by rfl) ⟨1665095, by rfl⟩ : syracuseStep 2220127 = 3330191) B3330191
theorem B3330197 : Blo 2219435 3330197 := bbase (se 6 (by rfl) ⟨78051, by rfl⟩ : syracuseStep 3330197 = 156103) (by norm_num)
theorem B2220131 : Blo 2219435 2220131 := bstep (se 1 (by rfl) ⟨1665098, by rfl⟩ : syracuseStep 2220131 = 3330197) B3330197
theorem B3556229 : Blo 2219435 3556229 := bbase (se 4 (by rfl) ⟨333396, by rfl⟩ : syracuseStep 3556229 = 666793) (by norm_num)
theorem B9483277 : Blo 2219435 9483277 := bstep (se 3 (by rfl) ⟨1778114, by rfl⟩ : syracuseStep 9483277 = 3556229) B3556229
theorem B12644369 : Blo 2219435 12644369 := bstep (se 2 (by rfl) ⟨4741638, by rfl⟩ : syracuseStep 12644369 = 9483277) B9483277
theorem B8429579 : Blo 2219435 8429579 := bstep (se 1 (by rfl) ⟨6322184, by rfl⟩ : syracuseStep 8429579 = 12644369) B12644369
theorem B5619719 : Blo 2219435 5619719 := bstep (se 1 (by rfl) ⟨4214789, by rfl⟩ : syracuseStep 5619719 = 8429579) B8429579
theorem B3746479 : Blo 2219435 3746479 := bstep (se 1 (by rfl) ⟨2809859, by rfl⟩ : syracuseStep 3746479 = 5619719) B5619719
theorem B4995305 : Blo 2219435 4995305 := bstep (se 2 (by rfl) ⟨1873239, by rfl⟩ : syracuseStep 4995305 = 3746479) B3746479
theorem B3330203 : Blo 2219435 3330203 := bstep (se 1 (by rfl) ⟨2497652, by rfl⟩ : syracuseStep 3330203 = 4995305) B4995305
theorem B2220135 : Blo 2219435 2220135 := bstep (se 1 (by rfl) ⟨1665101, by rfl⟩ : syracuseStep 2220135 = 3330203) B3330203
theorem B2497657 : Blo 2219435 2497657 := bbase (se 2 (by rfl) ⟨936621, by rfl⟩ : syracuseStep 2497657 = 1873243) (by norm_num)
theorem B3330209 : Blo 2219435 3330209 := bstep (se 2 (by rfl) ⟨1248828, by rfl⟩ : syracuseStep 3330209 = 2497657) B2497657
theorem B2220139 : Blo 2219435 2220139 := bstep (se 1 (by rfl) ⟨1665104, by rfl⟩ : syracuseStep 2220139 = 3330209) B3330209
theorem B4055357 : Blo 2219435 4055357 := bbase (se 3 (by rfl) ⟨760379, by rfl⟩ : syracuseStep 4055357 = 1520759) (by norm_num)
theorem B10814285 : Blo 2219435 10814285 := bstep (se 3 (by rfl) ⟨2027678, by rfl⟩ : syracuseStep 10814285 = 4055357) B4055357
theorem B7209523 : Blo 2219435 7209523 := bstep (se 1 (by rfl) ⟨5407142, by rfl⟩ : syracuseStep 7209523 = 10814285) B10814285
theorem B9612697 : Blo 2219435 9612697 := bstep (se 2 (by rfl) ⟨3604761, by rfl⟩ : syracuseStep 9612697 = 7209523) B7209523
theorem B12816929 : Blo 2219435 12816929 := bstep (se 2 (by rfl) ⟨4806348, by rfl⟩ : syracuseStep 12816929 = 9612697) B9612697
theorem B8544619 : Blo 2219435 8544619 := bstep (se 1 (by rfl) ⟨6408464, by rfl⟩ : syracuseStep 8544619 = 12816929) B12816929
theorem B11392825 : Blo 2219435 11392825 := bstep (se 2 (by rfl) ⟨4272309, by rfl⟩ : syracuseStep 11392825 = 8544619) B8544619
theorem B15190433 : Blo 2219435 15190433 := bstep (se 2 (by rfl) ⟨5696412, by rfl⟩ : syracuseStep 15190433 = 11392825) B11392825
theorem B10126955 : Blo 2219435 10126955 := bstep (se 1 (by rfl) ⟨7595216, by rfl⟩ : syracuseStep 10126955 = 15190433) B15190433
theorem B27005213 : Blo 2219435 27005213 := bstep (se 3 (by rfl) ⟨5063477, by rfl⟩ : syracuseStep 27005213 = 10126955) B10126955
theorem B18003475 : Blo 2219435 18003475 := bstep (se 1 (by rfl) ⟨13502606, by rfl⟩ : syracuseStep 18003475 = 27005213) B27005213
theorem B24004633 : Blo 2219435 24004633 := bstep (se 2 (by rfl) ⟨9001737, by rfl⟩ : syracuseStep 24004633 = 18003475) B18003475
theorem B32006177 : Blo 2219435 32006177 := bstep (se 2 (by rfl) ⟨12002316, by rfl⟩ : syracuseStep 32006177 = 24004633) B24004633
theorem B21337451 : Blo 2219435 21337451 := bstep (se 1 (by rfl) ⟨16003088, by rfl⟩ : syracuseStep 21337451 = 32006177) B32006177
theorem B14224967 : Blo 2219435 14224967 := bstep (se 1 (by rfl) ⟨10668725, by rfl⟩ : syracuseStep 14224967 = 21337451) B21337451
theorem B9483311 : Blo 2219435 9483311 := bstep (se 1 (by rfl) ⟨7112483, by rfl⟩ : syracuseStep 9483311 = 14224967) B14224967
theorem B6322207 : Blo 2219435 6322207 := bstep (se 1 (by rfl) ⟨4741655, by rfl⟩ : syracuseStep 6322207 = 9483311) B9483311
theorem B8429609 : Blo 2219435 8429609 := bstep (se 2 (by rfl) ⟨3161103, by rfl⟩ : syracuseStep 8429609 = 6322207) B6322207
theorem B5619739 : Blo 2219435 5619739 := bstep (se 1 (by rfl) ⟨4214804, by rfl⟩ : syracuseStep 5619739 = 8429609) B8429609
theorem B7492985 : Blo 2219435 7492985 := bstep (se 2 (by rfl) ⟨2809869, by rfl⟩ : syracuseStep 7492985 = 5619739) B5619739
theorem B4995323 : Blo 2219435 4995323 := bstep (se 1 (by rfl) ⟨3746492, by rfl⟩ : syracuseStep 4995323 = 7492985) B7492985
theorem B3330215 : Blo 2219435 3330215 := bstep (se 1 (by rfl) ⟨2497661, by rfl⟩ : syracuseStep 3330215 = 4995323) B4995323
theorem B2220143 : Blo 2219435 2220143 := bstep (se 1 (by rfl) ⟨1665107, by rfl⟩ : syracuseStep 2220143 = 3330215) B3330215
theorem B3330221 : Blo 2219435 3330221 := bbase (se 3 (by rfl) ⟨624416, by rfl⟩ : syracuseStep 3330221 = 1248833) (by norm_num)
theorem B2220147 : Blo 2219435 2220147 := bstep (se 1 (by rfl) ⟨1665110, by rfl⟩ : syracuseStep 2220147 = 3330221) B3330221
theorem B4995341 : Blo 2219435 4995341 := bbase (se 3 (by rfl) ⟨936626, by rfl⟩ : syracuseStep 4995341 = 1873253) (by norm_num)
theorem B3330227 : Blo 2219435 3330227 := bstep (se 1 (by rfl) ⟨2497670, by rfl⟩ : syracuseStep 3330227 = 4995341) B4995341
theorem B2220151 : Blo 2219435 2220151 := bstep (se 1 (by rfl) ⟨1665113, by rfl⟩ : syracuseStep 2220151 = 3330227) B3330227
theorem B2809885 : Blo 2219435 2809885 := bbase (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) (by norm_num)
theorem B3746513 : Blo 2219435 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B2497675 : Blo 2219435 2497675 := bstep (se 1 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 2497675 = 3746513) B3746513
theorem B3330233 : Blo 2219435 3330233 := bstep (se 2 (by rfl) ⟨1248837, by rfl⟩ : syracuseStep 3330233 = 2497675) B2497675
theorem B2220155 : Blo 2219435 2220155 := bstep (se 1 (by rfl) ⟨1665116, by rfl⟩ : syracuseStep 2220155 = 3330233) B3330233
theorem B3375677 : Blo 2219435 3375677 := bbase (se 3 (by rfl) ⟨632939, by rfl⟩ : syracuseStep 3375677 = 1265879) (by norm_num)
theorem B2250451 : Blo 2219435 2250451 := bstep (se 1 (by rfl) ⟨1687838, by rfl⟩ : syracuseStep 2250451 = 3375677) B3375677
theorem B3000601 : Blo 2219435 3000601 := bstep (se 2 (by rfl) ⟨1125225, by rfl⟩ : syracuseStep 3000601 = 2250451) B2250451
theorem B4000801 : Blo 2219435 4000801 := bstep (se 2 (by rfl) ⟨1500300, by rfl⟩ : syracuseStep 4000801 = 3000601) B3000601
theorem B5334401 : Blo 2219435 5334401 := bstep (se 2 (by rfl) ⟨2000400, by rfl⟩ : syracuseStep 5334401 = 4000801) B4000801
theorem B3556267 : Blo 2219435 3556267 := bstep (se 1 (by rfl) ⟨2667200, by rfl⟩ : syracuseStep 3556267 = 5334401) B5334401
theorem B18966757 : Blo 2219435 18966757 := bstep (se 4 (by rfl) ⟨1778133, by rfl⟩ : syracuseStep 18966757 = 3556267) B3556267
theorem B25289009 : Blo 2219435 25289009 := bstep (se 2 (by rfl) ⟨9483378, by rfl⟩ : syracuseStep 25289009 = 18966757) B18966757
theorem B16859339 : Blo 2219435 16859339 := bstep (se 1 (by rfl) ⟨12644504, by rfl⟩ : syracuseStep 16859339 = 25289009) B25289009
theorem B11239559 : Blo 2219435 11239559 := bstep (se 1 (by rfl) ⟨8429669, by rfl⟩ : syracuseStep 11239559 = 16859339) B16859339
theorem B7493039 : Blo 2219435 7493039 := bstep (se 1 (by rfl) ⟨5619779, by rfl⟩ : syracuseStep 7493039 = 11239559) B11239559
theorem B4995359 : Blo 2219435 4995359 := bstep (se 1 (by rfl) ⟨3746519, by rfl⟩ : syracuseStep 4995359 = 7493039) B7493039
theorem B3330239 : Blo 2219435 3330239 := bstep (se 1 (by rfl) ⟨2497679, by rfl⟩ : syracuseStep 3330239 = 4995359) B4995359
theorem B2220159 : Blo 2219435 2220159 := bstep (se 1 (by rfl) ⟨1665119, by rfl⟩ : syracuseStep 2220159 = 3330239) B3330239
theorem B3330245 : Blo 2219435 3330245 := bbase (se 4 (by rfl) ⟨312210, by rfl⟩ : syracuseStep 3330245 = 624421) (by norm_num)
theorem B2220163 : Blo 2219435 2220163 := bstep (se 1 (by rfl) ⟨1665122, by rfl⟩ : syracuseStep 2220163 = 3330245) B3330245
theorem B3746533 : Blo 2219435 3746533 := bbase (se 4 (by rfl) ⟨351237, by rfl⟩ : syracuseStep 3746533 = 702475) (by norm_num)
theorem B4995377 : Blo 2219435 4995377 := bstep (se 2 (by rfl) ⟨1873266, by rfl⟩ : syracuseStep 4995377 = 3746533) B3746533
theorem B3330251 : Blo 2219435 3330251 := bstep (se 1 (by rfl) ⟨2497688, by rfl⟩ : syracuseStep 3330251 = 4995377) B4995377
theorem B2220167 : Blo 2219435 2220167 := bstep (se 1 (by rfl) ⟨1665125, by rfl⟩ : syracuseStep 2220167 = 3330251) B3330251
theorem B2497693 : Blo 2219435 2497693 := bbase (se 3 (by rfl) ⟨468317, by rfl⟩ : syracuseStep 2497693 = 936635) (by norm_num)
theorem B3330257 : Blo 2219435 3330257 := bstep (se 2 (by rfl) ⟨1248846, by rfl⟩ : syracuseStep 3330257 = 2497693) B2497693
theorem B2220171 : Blo 2219435 2220171 := bstep (se 1 (by rfl) ⟨1665128, by rfl⟩ : syracuseStep 2220171 = 3330257) B3330257
theorem B7493093 : Blo 2219435 7493093 := bbase (se 4 (by rfl) ⟨702477, by rfl⟩ : syracuseStep 7493093 = 1404955) (by norm_num)
theorem B4995395 : Blo 2219435 4995395 := bstep (se 1 (by rfl) ⟨3746546, by rfl⟩ : syracuseStep 4995395 = 7493093) B7493093
theorem B3330263 : Blo 2219435 3330263 := bstep (se 1 (by rfl) ⟨2497697, by rfl⟩ : syracuseStep 3330263 = 4995395) B4995395
theorem B2220175 : Blo 2219435 2220175 := bstep (se 1 (by rfl) ⟨1665131, by rfl⟩ : syracuseStep 2220175 = 3330263) B3330263
theorem B3330269 : Blo 2219435 3330269 := bbase (se 3 (by rfl) ⟨624425, by rfl⟩ : syracuseStep 3330269 = 1248851) (by norm_num)
theorem B2220179 : Blo 2219435 2220179 := bstep (se 1 (by rfl) ⟨1665134, by rfl⟩ : syracuseStep 2220179 = 3330269) B3330269
theorem B4995413 : Blo 2219435 4995413 := bbase (se 10 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 4995413 = 14635) (by norm_num)
theorem B3330275 : Blo 2219435 3330275 := bstep (se 1 (by rfl) ⟨2497706, by rfl⟩ : syracuseStep 3330275 = 4995413) B4995413
theorem B2220183 : Blo 2219435 2220183 := bstep (se 1 (by rfl) ⟨1665137, by rfl⟩ : syracuseStep 2220183 = 3330275) B3330275
theorem B4000853 : Blo 2219435 4000853 := bbase (se 8 (by rfl) ⟨23442, by rfl⟩ : syracuseStep 4000853 = 46885) (by norm_num)
theorem B2667235 : Blo 2219435 2667235 := bstep (se 1 (by rfl) ⟨2000426, by rfl⟩ : syracuseStep 2667235 = 4000853) B4000853
theorem B3556313 : Blo 2219435 3556313 := bstep (se 2 (by rfl) ⟨1333617, by rfl⟩ : syracuseStep 3556313 = 2667235) B2667235
theorem B2370875 : Blo 2219435 2370875 := bstep (se 1 (by rfl) ⟨1778156, by rfl⟩ : syracuseStep 2370875 = 3556313) B3556313
theorem B6322333 : Blo 2219435 6322333 := bstep (se 3 (by rfl) ⟨1185437, by rfl⟩ : syracuseStep 6322333 = 2370875) B2370875
theorem B8429777 : Blo 2219435 8429777 := bstep (se 2 (by rfl) ⟨3161166, by rfl⟩ : syracuseStep 8429777 = 6322333) B6322333
theorem B5619851 : Blo 2219435 5619851 := bstep (se 1 (by rfl) ⟨4214888, by rfl⟩ : syracuseStep 5619851 = 8429777) B8429777
theorem B3746567 : Blo 2219435 3746567 := bstep (se 1 (by rfl) ⟨2809925, by rfl⟩ : syracuseStep 3746567 = 5619851) B5619851
theorem B2497711 : Blo 2219435 2497711 := bstep (se 1 (by rfl) ⟨1873283, by rfl⟩ : syracuseStep 2497711 = 3746567) B3746567
theorem B3330281 : Blo 2219435 3330281 := bstep (se 2 (by rfl) ⟨1248855, by rfl⟩ : syracuseStep 3330281 = 2497711) B2497711
theorem B2220187 : Blo 2219435 2220187 := bstep (se 1 (by rfl) ⟨1665140, by rfl⟩ : syracuseStep 2220187 = 3330281) B3330281
theorem B40508693 : Blo 2219435 40508693 := bbase (se 6 (by rfl) ⟨949422, by rfl⟩ : syracuseStep 40508693 = 1898845) (by norm_num)
theorem B27005795 : Blo 2219435 27005795 := bstep (se 1 (by rfl) ⟨20254346, by rfl⟩ : syracuseStep 27005795 = 40508693) B40508693
theorem B18003863 : Blo 2219435 18003863 := bstep (se 1 (by rfl) ⟨13502897, by rfl⟩ : syracuseStep 18003863 = 27005795) B27005795
theorem B12002575 : Blo 2219435 12002575 := bstep (se 1 (by rfl) ⟨9001931, by rfl⟩ : syracuseStep 12002575 = 18003863) B18003863
theorem B16003433 : Blo 2219435 16003433 := bstep (se 2 (by rfl) ⟨6001287, by rfl⟩ : syracuseStep 16003433 = 12002575) B12002575
theorem B42675821 : Blo 2219435 42675821 := bstep (se 3 (by rfl) ⟨8001716, by rfl⟩ : syracuseStep 42675821 = 16003433) B16003433
theorem B28450547 : Blo 2219435 28450547 := bstep (se 1 (by rfl) ⟨21337910, by rfl⟩ : syracuseStep 28450547 = 42675821) B42675821
theorem B18967031 : Blo 2219435 18967031 := bstep (se 1 (by rfl) ⟨14225273, by rfl⟩ : syracuseStep 18967031 = 28450547) B28450547
theorem B12644687 : Blo 2219435 12644687 := bstep (se 1 (by rfl) ⟨9483515, by rfl⟩ : syracuseStep 12644687 = 18967031) B18967031
theorem B8429791 : Blo 2219435 8429791 := bstep (se 1 (by rfl) ⟨6322343, by rfl⟩ : syracuseStep 8429791 = 12644687) B12644687
theorem B11239721 : Blo 2219435 11239721 := bstep (se 2 (by rfl) ⟨4214895, by rfl⟩ : syracuseStep 11239721 = 8429791) B8429791
theorem B7493147 : Blo 2219435 7493147 := bstep (se 1 (by rfl) ⟨5619860, by rfl⟩ : syracuseStep 7493147 = 11239721) B11239721
theorem B4995431 : Blo 2219435 4995431 := bstep (se 1 (by rfl) ⟨3746573, by rfl⟩ : syracuseStep 4995431 = 7493147) B7493147
theorem B3330287 : Blo 2219435 3330287 := bstep (se 1 (by rfl) ⟨2497715, by rfl⟩ : syracuseStep 3330287 = 4995431) B4995431
theorem B2220191 : Blo 2219435 2220191 := bstep (se 1 (by rfl) ⟨1665143, by rfl⟩ : syracuseStep 2220191 = 3330287) B3330287
theorem B3330293 : Blo 2219435 3330293 := bbase (se 5 (by rfl) ⟨156107, by rfl⟩ : syracuseStep 3330293 = 312215) (by norm_num)
theorem B2220195 : Blo 2219435 2220195 := bstep (se 1 (by rfl) ⟨1665146, by rfl⟩ : syracuseStep 2220195 = 3330293) B3330293
theorem B6408629 : Blo 2219435 6408629 := bbase (se 5 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 6408629 = 600809) (by norm_num)
theorem B4272419 : Blo 2219435 4272419 := bstep (se 1 (by rfl) ⟨3204314, by rfl⟩ : syracuseStep 4272419 = 6408629) B6408629
theorem B2848279 : Blo 2219435 2848279 := bstep (se 1 (by rfl) ⟨2136209, by rfl⟩ : syracuseStep 2848279 = 4272419) B4272419
theorem B3797705 : Blo 2219435 3797705 := bstep (se 2 (by rfl) ⟨1424139, by rfl⟩ : syracuseStep 3797705 = 2848279) B2848279
theorem B2531803 : Blo 2219435 2531803 := bstep (se 1 (by rfl) ⟨1898852, by rfl⟩ : syracuseStep 2531803 = 3797705) B3797705
theorem B3375737 : Blo 2219435 3375737 := bstep (se 2 (by rfl) ⟨1265901, by rfl⟩ : syracuseStep 3375737 = 2531803) B2531803
theorem B36007861 : Blo 2219435 36007861 := bstep (se 5 (by rfl) ⟨1687868, by rfl⟩ : syracuseStep 36007861 = 3375737) B3375737
theorem B48010481 : Blo 2219435 48010481 := bstep (se 2 (by rfl) ⟨18003930, by rfl⟩ : syracuseStep 48010481 = 36007861) B36007861
theorem B32006987 : Blo 2219435 32006987 := bstep (se 1 (by rfl) ⟨24005240, by rfl⟩ : syracuseStep 32006987 = 48010481) B48010481
theorem B21337991 : Blo 2219435 21337991 := bstep (se 1 (by rfl) ⟨16003493, by rfl⟩ : syracuseStep 21337991 = 32006987) B32006987
theorem B14225327 : Blo 2219435 14225327 := bstep (se 1 (by rfl) ⟨10668995, by rfl⟩ : syracuseStep 14225327 = 21337991) B21337991
theorem B9483551 : Blo 2219435 9483551 := bstep (se 1 (by rfl) ⟨7112663, by rfl⟩ : syracuseStep 9483551 = 14225327) B14225327
theorem B6322367 : Blo 2219435 6322367 := bstep (se 1 (by rfl) ⟨4741775, by rfl⟩ : syracuseStep 6322367 = 9483551) B9483551
theorem B4214911 : Blo 2219435 4214911 := bstep (se 1 (by rfl) ⟨3161183, by rfl⟩ : syracuseStep 4214911 = 6322367) B6322367
theorem B5619881 : Blo 2219435 5619881 := bstep (se 2 (by rfl) ⟨2107455, by rfl⟩ : syracuseStep 5619881 = 4214911) B4214911
theorem B3746587 : Blo 2219435 3746587 := bstep (se 1 (by rfl) ⟨2809940, by rfl⟩ : syracuseStep 3746587 = 5619881) B5619881
theorem B4995449 : Blo 2219435 4995449 := bstep (se 2 (by rfl) ⟨1873293, by rfl⟩ : syracuseStep 4995449 = 3746587) B3746587
theorem B3330299 : Blo 2219435 3330299 := bstep (se 1 (by rfl) ⟨2497724, by rfl⟩ : syracuseStep 3330299 = 4995449) B4995449
theorem B2220199 : Blo 2219435 2220199 := bstep (se 1 (by rfl) ⟨1665149, by rfl⟩ : syracuseStep 2220199 = 3330299) B3330299
theorem B2497729 : Blo 2219435 2497729 := bbase (se 2 (by rfl) ⟨936648, by rfl⟩ : syracuseStep 2497729 = 1873297) (by norm_num)
theorem B3330305 : Blo 2219435 3330305 := bstep (se 2 (by rfl) ⟨1248864, by rfl⟩ : syracuseStep 3330305 = 2497729) B2497729
theorem B2220203 : Blo 2219435 2220203 := bstep (se 1 (by rfl) ⟨1665152, by rfl⟩ : syracuseStep 2220203 = 3330305) B3330305
theorem B5619901 : Blo 2219435 5619901 := bbase (se 3 (by rfl) ⟨1053731, by rfl⟩ : syracuseStep 5619901 = 2107463) (by norm_num)
theorem B7493201 : Blo 2219435 7493201 := bstep (se 2 (by rfl) ⟨2809950, by rfl⟩ : syracuseStep 7493201 = 5619901) B5619901
theorem B4995467 : Blo 2219435 4995467 := bstep (se 1 (by rfl) ⟨3746600, by rfl⟩ : syracuseStep 4995467 = 7493201) B7493201
theorem B3330311 : Blo 2219435 3330311 := bstep (se 1 (by rfl) ⟨2497733, by rfl⟩ : syracuseStep 3330311 = 4995467) B4995467
theorem B2220207 : Blo 2219435 2220207 := bstep (se 1 (by rfl) ⟨1665155, by rfl⟩ : syracuseStep 2220207 = 3330311) B3330311
theorem B3330317 : Blo 2219435 3330317 := bbase (se 3 (by rfl) ⟨624434, by rfl⟩ : syracuseStep 3330317 = 1248869) (by norm_num)
theorem B2220211 : Blo 2219435 2220211 := bstep (se 1 (by rfl) ⟨1665158, by rfl⟩ : syracuseStep 2220211 = 3330317) B3330317
theorem B4995485 : Blo 2219435 4995485 := bbase (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) (by norm_num)
theorem B3330323 : Blo 2219435 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B2220215 : Blo 2219435 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B3746621 : Blo 2219435 3746621 := bbase (se 3 (by rfl) ⟨702491, by rfl⟩ : syracuseStep 3746621 = 1404983) (by norm_num)
theorem B2497747 : Blo 2219435 2497747 := bstep (se 1 (by rfl) ⟨1873310, by rfl⟩ : syracuseStep 2497747 = 3746621) B3746621
theorem B3330329 : Blo 2219435 3330329 := bstep (se 2 (by rfl) ⟨1248873, by rfl⟩ : syracuseStep 3330329 = 2497747) B2497747
theorem B2220219 : Blo 2219435 2220219 := bstep (se 1 (by rfl) ⟨1665164, by rfl⟩ : syracuseStep 2220219 = 3330329) B3330329
theorem B2370913 : Blo 2219435 2370913 := bbase (se 2 (by rfl) ⟨889092, by rfl⟩ : syracuseStep 2370913 = 1778185) (by norm_num)
theorem B12644869 : Blo 2219435 12644869 := bstep (se 4 (by rfl) ⟨1185456, by rfl⟩ : syracuseStep 12644869 = 2370913) B2370913
theorem B16859825 : Blo 2219435 16859825 := bstep (se 2 (by rfl) ⟨6322434, by rfl⟩ : syracuseStep 16859825 = 12644869) B12644869
theorem B11239883 : Blo 2219435 11239883 := bstep (se 1 (by rfl) ⟨8429912, by rfl⟩ : syracuseStep 11239883 = 16859825) B16859825
theorem B7493255 : Blo 2219435 7493255 := bstep (se 1 (by rfl) ⟨5619941, by rfl⟩ : syracuseStep 7493255 = 11239883) B11239883
theorem B4995503 : Blo 2219435 4995503 := bstep (se 1 (by rfl) ⟨3746627, by rfl⟩ : syracuseStep 4995503 = 7493255) B7493255
theorem B3330335 : Blo 2219435 3330335 := bstep (se 1 (by rfl) ⟨2497751, by rfl⟩ : syracuseStep 3330335 = 4995503) B4995503
theorem B2220223 : Blo 2219435 2220223 := bstep (se 1 (by rfl) ⟨1665167, by rfl⟩ : syracuseStep 2220223 = 3330335) B3330335
theorem B3330341 : Blo 2219435 3330341 := bbase (se 4 (by rfl) ⟨312219, by rfl⟩ : syracuseStep 3330341 = 624439) (by norm_num)
theorem B2220227 : Blo 2219435 2220227 := bstep (se 1 (by rfl) ⟨1665170, by rfl⟩ : syracuseStep 2220227 = 3330341) B3330341
theorem B2809981 : Blo 2219435 2809981 := bbase (se 3 (by rfl) ⟨526871, by rfl⟩ : syracuseStep 2809981 = 1053743) (by norm_num)
theorem B3746641 : Blo 2219435 3746641 := bstep (se 2 (by rfl) ⟨1404990, by rfl⟩ : syracuseStep 3746641 = 2809981) B2809981
theorem B4995521 : Blo 2219435 4995521 := bstep (se 2 (by rfl) ⟨1873320, by rfl⟩ : syracuseStep 4995521 = 3746641) B3746641
theorem B3330347 : Blo 2219435 3330347 := bstep (se 1 (by rfl) ⟨2497760, by rfl⟩ : syracuseStep 3330347 = 4995521) B4995521
theorem B2220231 : Blo 2219435 2220231 := bstep (se 1 (by rfl) ⟨1665173, by rfl⟩ : syracuseStep 2220231 = 3330347) B3330347
theorem B2497765 : Blo 2219435 2497765 := bbase (se 4 (by rfl) ⟨234165, by rfl⟩ : syracuseStep 2497765 = 468331) (by norm_num)
theorem B3330353 : Blo 2219435 3330353 := bstep (se 2 (by rfl) ⟨1248882, by rfl⟩ : syracuseStep 3330353 = 2497765) B2497765
theorem B2220235 : Blo 2219435 2220235 := bstep (se 1 (by rfl) ⟨1665176, by rfl⟩ : syracuseStep 2220235 = 3330353) B3330353
theorem B4741861 : Blo 2219435 4741861 := bbase (se 4 (by rfl) ⟨444549, by rfl⟩ : syracuseStep 4741861 = 889099) (by norm_num)
theorem B6322481 : Blo 2219435 6322481 := bstep (se 2 (by rfl) ⟨2370930, by rfl⟩ : syracuseStep 6322481 = 4741861) B4741861
theorem B4214987 : Blo 2219435 4214987 := bstep (se 1 (by rfl) ⟨3161240, by rfl⟩ : syracuseStep 4214987 = 6322481) B6322481
theorem B2809991 : Blo 2219435 2809991 := bstep (se 1 (by rfl) ⟨2107493, by rfl⟩ : syracuseStep 2809991 = 4214987) B4214987
theorem B7493309 : Blo 2219435 7493309 := bstep (se 3 (by rfl) ⟨1404995, by rfl⟩ : syracuseStep 7493309 = 2809991) B2809991
theorem B4995539 : Blo 2219435 4995539 := bstep (se 1 (by rfl) ⟨3746654, by rfl⟩ : syracuseStep 4995539 = 7493309) B7493309
theorem B3330359 : Blo 2219435 3330359 := bstep (se 1 (by rfl) ⟨2497769, by rfl⟩ : syracuseStep 3330359 = 4995539) B4995539
theorem B2220239 : Blo 2219435 2220239 := bstep (se 1 (by rfl) ⟨1665179, by rfl⟩ : syracuseStep 2220239 = 3330359) B3330359
theorem B3330365 : Blo 2219435 3330365 := bbase (se 3 (by rfl) ⟨624443, by rfl⟩ : syracuseStep 3330365 = 1248887) (by norm_num)
theorem B2220243 : Blo 2219435 2220243 := bstep (se 1 (by rfl) ⟨1665182, by rfl⟩ : syracuseStep 2220243 = 3330365) B3330365
theorem B4995557 : Blo 2219435 4995557 := bbase (se 4 (by rfl) ⟨468333, by rfl⟩ : syracuseStep 4995557 = 936667) (by norm_num)
theorem B3330371 : Blo 2219435 3330371 := bstep (se 1 (by rfl) ⟨2497778, by rfl⟩ : syracuseStep 3330371 = 4995557) B4995557
theorem B2220247 : Blo 2219435 2220247 := bstep (se 1 (by rfl) ⟨1665185, by rfl⟩ : syracuseStep 2220247 = 3330371) B3330371
theorem B5620013 : Blo 2219435 5620013 := bbase (se 3 (by rfl) ⟨1053752, by rfl⟩ : syracuseStep 5620013 = 2107505) (by norm_num)
theorem B3746675 : Blo 2219435 3746675 := bstep (se 1 (by rfl) ⟨2810006, by rfl⟩ : syracuseStep 3746675 = 5620013) B5620013
theorem B2497783 : Blo 2219435 2497783 := bstep (se 1 (by rfl) ⟨1873337, by rfl⟩ : syracuseStep 2497783 = 3746675) B3746675
theorem B3330377 : Blo 2219435 3330377 := bstep (se 2 (by rfl) ⟨1248891, by rfl⟩ : syracuseStep 3330377 = 2497783) B2497783
theorem B2220251 : Blo 2219435 2220251 := bstep (se 1 (by rfl) ⟨1665188, by rfl⟩ : syracuseStep 2220251 = 3330377) B3330377
theorem B2703709 : Blo 2219435 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B14419781 : Blo 2219435 14419781 := bstep (se 4 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 14419781 = 2703709) B2703709
theorem B9613187 : Blo 2219435 9613187 := bstep (se 1 (by rfl) ⟨7209890, by rfl⟩ : syracuseStep 9613187 = 14419781) B14419781
theorem B6408791 : Blo 2219435 6408791 := bstep (se 1 (by rfl) ⟨4806593, by rfl⟩ : syracuseStep 6408791 = 9613187) B9613187
theorem B4272527 : Blo 2219435 4272527 := bstep (se 1 (by rfl) ⟨3204395, by rfl⟩ : syracuseStep 4272527 = 6408791) B6408791
theorem B11393405 : Blo 2219435 11393405 := bstep (se 3 (by rfl) ⟨2136263, by rfl⟩ : syracuseStep 11393405 = 4272527) B4272527
theorem B7595603 : Blo 2219435 7595603 := bstep (se 1 (by rfl) ⟨5696702, by rfl⟩ : syracuseStep 7595603 = 11393405) B11393405
theorem B5063735 : Blo 2219435 5063735 := bstep (se 1 (by rfl) ⟨3797801, by rfl⟩ : syracuseStep 5063735 = 7595603) B7595603
theorem B3375823 : Blo 2219435 3375823 := bstep (se 1 (by rfl) ⟨2531867, by rfl⟩ : syracuseStep 3375823 = 5063735) B5063735
theorem B4501097 : Blo 2219435 4501097 := bstep (se 2 (by rfl) ⟨1687911, by rfl⟩ : syracuseStep 4501097 = 3375823) B3375823
theorem B3000731 : Blo 2219435 3000731 := bstep (se 1 (by rfl) ⟨2250548, by rfl⟩ : syracuseStep 3000731 = 4501097) B4501097
theorem B8001949 : Blo 2219435 8001949 := bstep (se 3 (by rfl) ⟨1500365, by rfl⟩ : syracuseStep 8001949 = 3000731) B3000731
theorem B10669265 : Blo 2219435 10669265 := bstep (se 2 (by rfl) ⟨4000974, by rfl⟩ : syracuseStep 10669265 = 8001949) B8001949
theorem B7112843 : Blo 2219435 7112843 := bstep (se 1 (by rfl) ⟨5334632, by rfl⟩ : syracuseStep 7112843 = 10669265) B10669265
theorem B4741895 : Blo 2219435 4741895 := bstep (se 1 (by rfl) ⟨3556421, by rfl⟩ : syracuseStep 4741895 = 7112843) B7112843
theorem B3161263 : Blo 2219435 3161263 := bstep (se 1 (by rfl) ⟨2370947, by rfl⟩ : syracuseStep 3161263 = 4741895) B4741895
theorem B4215017 : Blo 2219435 4215017 := bstep (se 2 (by rfl) ⟨1580631, by rfl⟩ : syracuseStep 4215017 = 3161263) B3161263
theorem B11240045 : Blo 2219435 11240045 := bstep (se 3 (by rfl) ⟨2107508, by rfl⟩ : syracuseStep 11240045 = 4215017) B4215017
theorem B7493363 : Blo 2219435 7493363 := bstep (se 1 (by rfl) ⟨5620022, by rfl⟩ : syracuseStep 7493363 = 11240045) B11240045
theorem B4995575 : Blo 2219435 4995575 := bstep (se 1 (by rfl) ⟨3746681, by rfl⟩ : syracuseStep 4995575 = 7493363) B7493363
theorem B3330383 : Blo 2219435 3330383 := bstep (se 1 (by rfl) ⟨2497787, by rfl⟩ : syracuseStep 3330383 = 4995575) B4995575
theorem B2220255 : Blo 2219435 2220255 := bstep (se 1 (by rfl) ⟨1665191, by rfl⟩ : syracuseStep 2220255 = 3330383) B3330383
theorem B3330389 : Blo 2219435 3330389 := bbase (se 10 (by rfl) ⟨4878, by rfl⟩ : syracuseStep 3330389 = 9757) (by norm_num)
theorem B2220259 : Blo 2219435 2220259 := bstep (se 1 (by rfl) ⟨1665194, by rfl⟩ : syracuseStep 2220259 = 3330389) B3330389
theorem B6322549 : Blo 2219435 6322549 := bbase (se 5 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 6322549 = 592739) (by norm_num)
theorem B8430065 : Blo 2219435 8430065 := bstep (se 2 (by rfl) ⟨3161274, by rfl⟩ : syracuseStep 8430065 = 6322549) B6322549
theorem B5620043 : Blo 2219435 5620043 := bstep (se 1 (by rfl) ⟨4215032, by rfl⟩ : syracuseStep 5620043 = 8430065) B8430065
theorem B3746695 : Blo 2219435 3746695 := bstep (se 1 (by rfl) ⟨2810021, by rfl⟩ : syracuseStep 3746695 = 5620043) B5620043
theorem B4995593 : Blo 2219435 4995593 := bstep (se 2 (by rfl) ⟨1873347, by rfl⟩ : syracuseStep 4995593 = 3746695) B3746695
theorem B3330395 : Blo 2219435 3330395 := bstep (se 1 (by rfl) ⟨2497796, by rfl⟩ : syracuseStep 3330395 = 4995593) B4995593
theorem B2220263 : Blo 2219435 2220263 := bstep (se 1 (by rfl) ⟨1665197, by rfl⟩ : syracuseStep 2220263 = 3330395) B3330395
theorem B2497801 : Blo 2219435 2497801 := bbase (se 2 (by rfl) ⟨936675, by rfl⟩ : syracuseStep 2497801 = 1873351) (by norm_num)
theorem B3330401 : Blo 2219435 3330401 := bstep (se 2 (by rfl) ⟨1248900, by rfl⟩ : syracuseStep 3330401 = 2497801) B2497801
theorem B2220267 : Blo 2219435 2220267 := bstep (se 1 (by rfl) ⟨1665200, by rfl⟩ : syracuseStep 2220267 = 3330401) B3330401
theorem B8661701 : Blo 2219435 8661701 := bbase (se 4 (by rfl) ⟨812034, by rfl⟩ : syracuseStep 8661701 = 1624069) (by norm_num)
theorem B23097869 : Blo 2219435 23097869 := bstep (se 3 (by rfl) ⟨4330850, by rfl⟩ : syracuseStep 23097869 = 8661701) B8661701
theorem B15398579 : Blo 2219435 15398579 := bstep (se 1 (by rfl) ⟨11548934, by rfl⟩ : syracuseStep 15398579 = 23097869) B23097869
theorem B10265719 : Blo 2219435 10265719 := bstep (se 1 (by rfl) ⟨7699289, by rfl⟩ : syracuseStep 10265719 = 15398579) B15398579
theorem B13687625 : Blo 2219435 13687625 := bstep (se 2 (by rfl) ⟨5132859, by rfl⟩ : syracuseStep 13687625 = 10265719) B10265719
theorem B9125083 : Blo 2219435 9125083 := bstep (se 1 (by rfl) ⟨6843812, by rfl⟩ : syracuseStep 9125083 = 13687625) B13687625
theorem B12166777 : Blo 2219435 12166777 := bstep (se 2 (by rfl) ⟨4562541, by rfl⟩ : syracuseStep 12166777 = 9125083) B9125083
theorem B16222369 : Blo 2219435 16222369 := bstep (se 2 (by rfl) ⟨6083388, by rfl⟩ : syracuseStep 16222369 = 12166777) B12166777
theorem B21629825 : Blo 2219435 21629825 := bstep (se 2 (by rfl) ⟨8111184, by rfl⟩ : syracuseStep 21629825 = 16222369) B16222369
theorem B14419883 : Blo 2219435 14419883 := bstep (se 1 (by rfl) ⟨10814912, by rfl⟩ : syracuseStep 14419883 = 21629825) B21629825
theorem B9613255 : Blo 2219435 9613255 := bstep (se 1 (by rfl) ⟨7209941, by rfl⟩ : syracuseStep 9613255 = 14419883) B14419883
theorem B12817673 : Blo 2219435 12817673 := bstep (se 2 (by rfl) ⟨4806627, by rfl⟩ : syracuseStep 12817673 = 9613255) B9613255
theorem B8545115 : Blo 2219435 8545115 := bstep (se 1 (by rfl) ⟨6408836, by rfl⟩ : syracuseStep 8545115 = 12817673) B12817673
theorem B5696743 : Blo 2219435 5696743 := bstep (se 1 (by rfl) ⟨4272557, by rfl⟩ : syracuseStep 5696743 = 8545115) B8545115
theorem B7595657 : Blo 2219435 7595657 := bstep (se 2 (by rfl) ⟨2848371, by rfl⟩ : syracuseStep 7595657 = 5696743) B5696743
theorem B5063771 : Blo 2219435 5063771 := bstep (se 1 (by rfl) ⟨3797828, by rfl⟩ : syracuseStep 5063771 = 7595657) B7595657
theorem B3375847 : Blo 2219435 3375847 := bstep (se 1 (by rfl) ⟨2531885, by rfl⟩ : syracuseStep 3375847 = 5063771) B5063771
theorem B4501129 : Blo 2219435 4501129 := bstep (se 2 (by rfl) ⟨1687923, by rfl⟩ : syracuseStep 4501129 = 3375847) B3375847
theorem B6001505 : Blo 2219435 6001505 := bstep (se 2 (by rfl) ⟨2250564, by rfl⟩ : syracuseStep 6001505 = 4501129) B4501129
theorem B4001003 : Blo 2219435 4001003 := bstep (se 1 (by rfl) ⟨3000752, by rfl⟩ : syracuseStep 4001003 = 6001505) B6001505
theorem B2667335 : Blo 2219435 2667335 := bstep (se 1 (by rfl) ⟨2000501, by rfl⟩ : syracuseStep 2667335 = 4001003) B4001003
theorem B28451573 : Blo 2219435 28451573 := bstep (se 5 (by rfl) ⟨1333667, by rfl⟩ : syracuseStep 28451573 = 2667335) B2667335
theorem B18967715 : Blo 2219435 18967715 := bstep (se 1 (by rfl) ⟨14225786, by rfl⟩ : syracuseStep 18967715 = 28451573) B28451573
theorem B12645143 : Blo 2219435 12645143 := bstep (se 1 (by rfl) ⟨9483857, by rfl⟩ : syracuseStep 12645143 = 18967715) B18967715
theorem B8430095 : Blo 2219435 8430095 := bstep (se 1 (by rfl) ⟨6322571, by rfl⟩ : syracuseStep 8430095 = 12645143) B12645143
theorem B5620063 : Blo 2219435 5620063 := bstep (se 1 (by rfl) ⟨4215047, by rfl⟩ : syracuseStep 5620063 = 8430095) B8430095
theorem B7493417 : Blo 2219435 7493417 := bstep (se 2 (by rfl) ⟨2810031, by rfl⟩ : syracuseStep 7493417 = 5620063) B5620063
theorem B4995611 : Blo 2219435 4995611 := bstep (se 1 (by rfl) ⟨3746708, by rfl⟩ : syracuseStep 4995611 = 7493417) B7493417
theorem B3330407 : Blo 2219435 3330407 := bstep (se 1 (by rfl) ⟨2497805, by rfl⟩ : syracuseStep 3330407 = 4995611) B4995611
theorem B2220271 : Blo 2219435 2220271 := bstep (se 1 (by rfl) ⟨1665203, by rfl⟩ : syracuseStep 2220271 = 3330407) B3330407
theorem B3330413 : Blo 2219435 3330413 := bbase (se 3 (by rfl) ⟨624452, by rfl⟩ : syracuseStep 3330413 = 1248905) (by norm_num)
theorem B2220275 : Blo 2219435 2220275 := bstep (se 1 (by rfl) ⟨1665206, by rfl⟩ : syracuseStep 2220275 = 3330413) B3330413
theorem B4995629 : Blo 2219435 4995629 := bbase (se 3 (by rfl) ⟨936680, by rfl⟩ : syracuseStep 4995629 = 1873361) (by norm_num)
theorem B3330419 : Blo 2219435 3330419 := bstep (se 1 (by rfl) ⟨2497814, by rfl⟩ : syracuseStep 3330419 = 4995629) B4995629
theorem B2220279 : Blo 2219435 2220279 := bstep (se 1 (by rfl) ⟨1665209, by rfl⟩ : syracuseStep 2220279 = 3330419) B3330419
theorem B2250577 : Blo 2219435 2250577 := bbase (se 2 (by rfl) ⟨843966, by rfl⟩ : syracuseStep 2250577 = 1687933) (by norm_num)
theorem B3000769 : Blo 2219435 3000769 := bstep (se 2 (by rfl) ⟨1125288, by rfl⟩ : syracuseStep 3000769 = 2250577) B2250577
theorem B16004101 : Blo 2219435 16004101 := bstep (se 4 (by rfl) ⟨1500384, by rfl⟩ : syracuseStep 16004101 = 3000769) B3000769
theorem B21338801 : Blo 2219435 21338801 := bstep (se 2 (by rfl) ⟨8002050, by rfl⟩ : syracuseStep 21338801 = 16004101) B16004101
theorem B14225867 : Blo 2219435 14225867 := bstep (se 1 (by rfl) ⟨10669400, by rfl⟩ : syracuseStep 14225867 = 21338801) B21338801
theorem B9483911 : Blo 2219435 9483911 := bstep (se 1 (by rfl) ⟨7112933, by rfl⟩ : syracuseStep 9483911 = 14225867) B14225867
theorem B6322607 : Blo 2219435 6322607 := bstep (se 1 (by rfl) ⟨4741955, by rfl⟩ : syracuseStep 6322607 = 9483911) B9483911
theorem B4215071 : Blo 2219435 4215071 := bstep (se 1 (by rfl) ⟨3161303, by rfl⟩ : syracuseStep 4215071 = 6322607) B6322607
theorem B2810047 : Blo 2219435 2810047 := bstep (se 1 (by rfl) ⟨2107535, by rfl⟩ : syracuseStep 2810047 = 4215071) B4215071
theorem B3746729 : Blo 2219435 3746729 := bstep (se 2 (by rfl) ⟨1405023, by rfl⟩ : syracuseStep 3746729 = 2810047) B2810047
theorem B2497819 : Blo 2219435 2497819 := bstep (se 1 (by rfl) ⟨1873364, by rfl⟩ : syracuseStep 2497819 = 3746729) B3746729
theorem B3330425 : Blo 2219435 3330425 := bstep (se 2 (by rfl) ⟨1248909, by rfl⟩ : syracuseStep 3330425 = 2497819) B2497819
theorem B2220283 : Blo 2219435 2220283 := bstep (se 1 (by rfl) ⟨1665212, by rfl⟩ : syracuseStep 2220283 = 3330425) B3330425
theorem B37935701 : Blo 2219435 37935701 := bbase (se 8 (by rfl) ⟨222279, by rfl⟩ : syracuseStep 37935701 = 444559) (by norm_num)
theorem B25290467 : Blo 2219435 25290467 := bstep (se 1 (by rfl) ⟨18967850, by rfl⟩ : syracuseStep 25290467 = 37935701) B37935701
theorem B16860311 : Blo 2219435 16860311 := bstep (se 1 (by rfl) ⟨12645233, by rfl⟩ : syracuseStep 16860311 = 25290467) B25290467
theorem B11240207 : Blo 2219435 11240207 := bstep (se 1 (by rfl) ⟨8430155, by rfl⟩ : syracuseStep 11240207 = 16860311) B16860311
theorem B7493471 : Blo 2219435 7493471 := bstep (se 1 (by rfl) ⟨5620103, by rfl⟩ : syracuseStep 7493471 = 11240207) B11240207
theorem B4995647 : Blo 2219435 4995647 := bstep (se 1 (by rfl) ⟨3746735, by rfl⟩ : syracuseStep 4995647 = 7493471) B7493471
theorem B3330431 : Blo 2219435 3330431 := bstep (se 1 (by rfl) ⟨2497823, by rfl⟩ : syracuseStep 3330431 = 4995647) B4995647
theorem B2220287 : Blo 2219435 2220287 := bstep (se 1 (by rfl) ⟨1665215, by rfl⟩ : syracuseStep 2220287 = 3330431) B3330431
theorem B3330437 : Blo 2219435 3330437 := bbase (se 4 (by rfl) ⟨312228, by rfl⟩ : syracuseStep 3330437 = 624457) (by norm_num)
theorem B2220291 : Blo 2219435 2220291 := bstep (se 1 (by rfl) ⟨1665218, by rfl⟩ : syracuseStep 2220291 = 3330437) B3330437
theorem B3746749 : Blo 2219435 3746749 := bbase (se 3 (by rfl) ⟨702515, by rfl⟩ : syracuseStep 3746749 = 1405031) (by norm_num)
theorem B4995665 : Blo 2219435 4995665 := bstep (se 2 (by rfl) ⟨1873374, by rfl⟩ : syracuseStep 4995665 = 3746749) B3746749
theorem B3330443 : Blo 2219435 3330443 := bstep (se 1 (by rfl) ⟨2497832, by rfl⟩ : syracuseStep 3330443 = 4995665) B4995665
theorem B2220295 : Blo 2219435 2220295 := bstep (se 1 (by rfl) ⟨1665221, by rfl⟩ : syracuseStep 2220295 = 3330443) B3330443
theorem B2497837 : Blo 2219435 2497837 := bbase (se 3 (by rfl) ⟨468344, by rfl⟩ : syracuseStep 2497837 = 936689) (by norm_num)
theorem B3330449 : Blo 2219435 3330449 := bstep (se 2 (by rfl) ⟨1248918, by rfl⟩ : syracuseStep 3330449 = 2497837) B2497837
theorem B2220299 : Blo 2219435 2220299 := bstep (se 1 (by rfl) ⟨1665224, by rfl⟩ : syracuseStep 2220299 = 3330449) B3330449
theorem B7493525 : Blo 2219435 7493525 := bbase (se 6 (by rfl) ⟨175629, by rfl⟩ : syracuseStep 7493525 = 351259) (by norm_num)
theorem B4995683 : Blo 2219435 4995683 := bstep (se 1 (by rfl) ⟨3746762, by rfl⟩ : syracuseStep 4995683 = 7493525) B7493525
theorem B3330455 : Blo 2219435 3330455 := bstep (se 1 (by rfl) ⟨2497841, by rfl⟩ : syracuseStep 3330455 = 4995683) B4995683
theorem B2220303 : Blo 2219435 2220303 := bstep (se 1 (by rfl) ⟨1665227, by rfl⟩ : syracuseStep 2220303 = 3330455) B3330455
theorem B3330461 : Blo 2219435 3330461 := bbase (se 3 (by rfl) ⟨624461, by rfl⟩ : syracuseStep 3330461 = 1248923) (by norm_num)
theorem B2220307 : Blo 2219435 2220307 := bstep (se 1 (by rfl) ⟨1665230, by rfl⟩ : syracuseStep 2220307 = 3330461) B3330461
theorem B4995701 : Blo 2219435 4995701 := bbase (se 5 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 4995701 = 468347) (by norm_num)
theorem B3330467 : Blo 2219435 3330467 := bstep (se 1 (by rfl) ⟨2497850, by rfl⟩ : syracuseStep 3330467 = 4995701) B4995701
theorem B2220311 : Blo 2219435 2220311 := bstep (se 1 (by rfl) ⟨1665233, by rfl⟩ : syracuseStep 2220311 = 3330467) B3330467
theorem B8002165 : Blo 2219435 8002165 := bbase (se 5 (by rfl) ⟨375101, by rfl⟩ : syracuseStep 8002165 = 750203) (by norm_num)
theorem B10669553 : Blo 2219435 10669553 := bstep (se 2 (by rfl) ⟨4001082, by rfl⟩ : syracuseStep 10669553 = 8002165) B8002165
theorem B7113035 : Blo 2219435 7113035 := bstep (se 1 (by rfl) ⟨5334776, by rfl⟩ : syracuseStep 7113035 = 10669553) B10669553
theorem B18968093 : Blo 2219435 18968093 := bstep (se 3 (by rfl) ⟨3556517, by rfl⟩ : syracuseStep 18968093 = 7113035) B7113035
theorem B12645395 : Blo 2219435 12645395 := bstep (se 1 (by rfl) ⟨9484046, by rfl⟩ : syracuseStep 12645395 = 18968093) B18968093
theorem B8430263 : Blo 2219435 8430263 := bstep (se 1 (by rfl) ⟨6322697, by rfl⟩ : syracuseStep 8430263 = 12645395) B12645395
theorem B5620175 : Blo 2219435 5620175 := bstep (se 1 (by rfl) ⟨4215131, by rfl⟩ : syracuseStep 5620175 = 8430263) B8430263
theorem B3746783 : Blo 2219435 3746783 := bstep (se 1 (by rfl) ⟨2810087, by rfl⟩ : syracuseStep 3746783 = 5620175) B5620175
theorem B2497855 : Blo 2219435 2497855 := bstep (se 1 (by rfl) ⟨1873391, by rfl⟩ : syracuseStep 2497855 = 3746783) B3746783
theorem B3330473 : Blo 2219435 3330473 := bstep (se 2 (by rfl) ⟨1248927, by rfl⟩ : syracuseStep 3330473 = 2497855) B2497855
theorem B2220315 : Blo 2219435 2220315 := bstep (se 1 (by rfl) ⟨1665236, by rfl⟩ : syracuseStep 2220315 = 3330473) B3330473
theorem B8430277 : Blo 2219435 8430277 := bbase (se 4 (by rfl) ⟨790338, by rfl⟩ : syracuseStep 8430277 = 1580677) (by norm_num)
theorem B11240369 : Blo 2219435 11240369 := bstep (se 2 (by rfl) ⟨4215138, by rfl⟩ : syracuseStep 11240369 = 8430277) B8430277
theorem B7493579 : Blo 2219435 7493579 := bstep (se 1 (by rfl) ⟨5620184, by rfl⟩ : syracuseStep 7493579 = 11240369) B11240369
theorem B4995719 : Blo 2219435 4995719 := bstep (se 1 (by rfl) ⟨3746789, by rfl⟩ : syracuseStep 4995719 = 7493579) B7493579
theorem B3330479 : Blo 2219435 3330479 := bstep (se 1 (by rfl) ⟨2497859, by rfl⟩ : syracuseStep 3330479 = 4995719) B4995719
theorem B2220319 : Blo 2219435 2220319 := bstep (se 1 (by rfl) ⟨1665239, by rfl⟩ : syracuseStep 2220319 = 3330479) B3330479
theorem B3330485 : Blo 2219435 3330485 := bbase (se 5 (by rfl) ⟨156116, by rfl⟩ : syracuseStep 3330485 = 312233) (by norm_num)
theorem B2220323 : Blo 2219435 2220323 := bstep (se 1 (by rfl) ⟨1665242, by rfl⟩ : syracuseStep 2220323 = 3330485) B3330485
theorem B5620205 : Blo 2219435 5620205 := bbase (se 3 (by rfl) ⟨1053788, by rfl⟩ : syracuseStep 5620205 = 2107577) (by norm_num)
theorem B3746803 : Blo 2219435 3746803 := bstep (se 1 (by rfl) ⟨2810102, by rfl⟩ : syracuseStep 3746803 = 5620205) B5620205
theorem B4995737 : Blo 2219435 4995737 := bstep (se 2 (by rfl) ⟨1873401, by rfl⟩ : syracuseStep 4995737 = 3746803) B3746803
theorem B3330491 : Blo 2219435 3330491 := bstep (se 1 (by rfl) ⟨2497868, by rfl⟩ : syracuseStep 3330491 = 4995737) B4995737
theorem B2220327 : Blo 2219435 2220327 := bstep (se 1 (by rfl) ⟨1665245, by rfl⟩ : syracuseStep 2220327 = 3330491) B3330491
theorem B2497873 : Blo 2219435 2497873 := bbase (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) (by norm_num)
theorem B3330497 : Blo 2219435 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B2220331 : Blo 2219435 2220331 := bstep (se 1 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 2220331 = 3330497) B3330497
theorem B2371033 : Blo 2219435 2371033 := bbase (se 2 (by rfl) ⟨889137, by rfl⟩ : syracuseStep 2371033 = 1778275) (by norm_num)
theorem B3161377 : Blo 2219435 3161377 := bstep (se 2 (by rfl) ⟨1185516, by rfl⟩ : syracuseStep 3161377 = 2371033) B2371033
theorem B4215169 : Blo 2219435 4215169 := bstep (se 2 (by rfl) ⟨1580688, by rfl⟩ : syracuseStep 4215169 = 3161377) B3161377
theorem B5620225 : Blo 2219435 5620225 := bstep (se 2 (by rfl) ⟨2107584, by rfl⟩ : syracuseStep 5620225 = 4215169) B4215169
theorem B7493633 : Blo 2219435 7493633 := bstep (se 2 (by rfl) ⟨2810112, by rfl⟩ : syracuseStep 7493633 = 5620225) B5620225
theorem B4995755 : Blo 2219435 4995755 := bstep (se 1 (by rfl) ⟨3746816, by rfl⟩ : syracuseStep 4995755 = 7493633) B7493633
theorem B3330503 : Blo 2219435 3330503 := bstep (se 1 (by rfl) ⟨2497877, by rfl⟩ : syracuseStep 3330503 = 4995755) B4995755
theorem B2220335 : Blo 2219435 2220335 := bstep (se 1 (by rfl) ⟨1665251, by rfl⟩ : syracuseStep 2220335 = 3330503) B3330503
theorem B3330509 : Blo 2219435 3330509 := bbase (se 3 (by rfl) ⟨624470, by rfl⟩ : syracuseStep 3330509 = 1248941) (by norm_num)
theorem B2220339 : Blo 2219435 2220339 := bstep (se 1 (by rfl) ⟨1665254, by rfl⟩ : syracuseStep 2220339 = 3330509) B3330509
theorem B4995773 : Blo 2219435 4995773 := bbase (se 3 (by rfl) ⟨936707, by rfl⟩ : syracuseStep 4995773 = 1873415) (by norm_num)
theorem B3330515 : Blo 2219435 3330515 := bstep (se 1 (by rfl) ⟨2497886, by rfl⟩ : syracuseStep 3330515 = 4995773) B4995773
theorem B2220343 : Blo 2219435 2220343 := bstep (se 1 (by rfl) ⟨1665257, by rfl⟩ : syracuseStep 2220343 = 3330515) B3330515
theorem B3746837 : Blo 2219435 3746837 := bbase (se 6 (by rfl) ⟨87816, by rfl⟩ : syracuseStep 3746837 = 175633) (by norm_num)
theorem B2497891 : Blo 2219435 2497891 := bstep (se 1 (by rfl) ⟨1873418, by rfl⟩ : syracuseStep 2497891 = 3746837) B3746837
theorem B3330521 : Blo 2219435 3330521 := bstep (se 2 (by rfl) ⟨1248945, by rfl⟩ : syracuseStep 3330521 = 2497891) B2497891
theorem B2220347 : Blo 2219435 2220347 := bstep (se 1 (by rfl) ⟨1665260, by rfl⟩ : syracuseStep 2220347 = 3330521) B3330521
theorem B28840789 : Blo 2219435 28840789 := bbase (se 9 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 28840789 = 168989) (by norm_num)
theorem B153817541 : Blo 2219435 153817541 := bstep (se 4 (by rfl) ⟨14420394, by rfl⟩ : syracuseStep 153817541 = 28840789) B28840789
theorem B102545027 : Blo 2219435 102545027 := bstep (se 1 (by rfl) ⟨76908770, by rfl⟩ : syracuseStep 102545027 = 153817541) B153817541
theorem B68363351 : Blo 2219435 68363351 := bstep (se 1 (by rfl) ⟨51272513, by rfl⟩ : syracuseStep 68363351 = 102545027) B102545027
theorem B45575567 : Blo 2219435 45575567 := bstep (se 1 (by rfl) ⟨34181675, by rfl⟩ : syracuseStep 45575567 = 68363351) B68363351
theorem B30383711 : Blo 2219435 30383711 := bstep (se 1 (by rfl) ⟨22787783, by rfl⟩ : syracuseStep 30383711 = 45575567) B45575567
theorem B20255807 : Blo 2219435 20255807 := bstep (se 1 (by rfl) ⟨15191855, by rfl⟩ : syracuseStep 20255807 = 30383711) B30383711
theorem B13503871 : Blo 2219435 13503871 := bstep (se 1 (by rfl) ⟨10127903, by rfl⟩ : syracuseStep 13503871 = 20255807) B20255807
theorem B18005161 : Blo 2219435 18005161 := bstep (se 2 (by rfl) ⟨6751935, by rfl⟩ : syracuseStep 18005161 = 13503871) B13503871
theorem B24006881 : Blo 2219435 24006881 := bstep (se 2 (by rfl) ⟨9002580, by rfl⟩ : syracuseStep 24006881 = 18005161) B18005161
theorem B16004587 : Blo 2219435 16004587 := bstep (se 1 (by rfl) ⟨12003440, by rfl⟩ : syracuseStep 16004587 = 24006881) B24006881
theorem B21339449 : Blo 2219435 21339449 := bstep (se 2 (by rfl) ⟨8002293, by rfl⟩ : syracuseStep 21339449 = 16004587) B16004587
theorem B14226299 : Blo 2219435 14226299 := bstep (se 1 (by rfl) ⟨10669724, by rfl⟩ : syracuseStep 14226299 = 21339449) B21339449
theorem B9484199 : Blo 2219435 9484199 := bstep (se 1 (by rfl) ⟨7113149, by rfl⟩ : syracuseStep 9484199 = 14226299) B14226299
theorem B6322799 : Blo 2219435 6322799 := bstep (se 1 (by rfl) ⟨4742099, by rfl⟩ : syracuseStep 6322799 = 9484199) B9484199
theorem B16860797 : Blo 2219435 16860797 := bstep (se 3 (by rfl) ⟨3161399, by rfl⟩ : syracuseStep 16860797 = 6322799) B6322799
theorem B11240531 : Blo 2219435 11240531 := bstep (se 1 (by rfl) ⟨8430398, by rfl⟩ : syracuseStep 11240531 = 16860797) B16860797
theorem B7493687 : Blo 2219435 7493687 := bstep (se 1 (by rfl) ⟨5620265, by rfl⟩ : syracuseStep 7493687 = 11240531) B11240531
theorem B4995791 : Blo 2219435 4995791 := bstep (se 1 (by rfl) ⟨3746843, by rfl⟩ : syracuseStep 4995791 = 7493687) B7493687
theorem B3330527 : Blo 2219435 3330527 := bstep (se 1 (by rfl) ⟨2497895, by rfl⟩ : syracuseStep 3330527 = 4995791) B4995791
theorem B2220351 : Blo 2219435 2220351 := bstep (se 1 (by rfl) ⟨1665263, by rfl⟩ : syracuseStep 2220351 = 3330527) B3330527
theorem B3330533 : Blo 2219435 3330533 := bbase (se 4 (by rfl) ⟨312237, by rfl⟩ : syracuseStep 3330533 = 624475) (by norm_num)
theorem B2220355 : Blo 2219435 2220355 := bstep (se 1 (by rfl) ⟨1665266, by rfl⟩ : syracuseStep 2220355 = 3330533) B3330533
theorem B10669765 : Blo 2219435 10669765 := bbase (se 4 (by rfl) ⟨1000290, by rfl⟩ : syracuseStep 10669765 = 2000581) (by norm_num)
theorem B14226353 : Blo 2219435 14226353 := bstep (se 2 (by rfl) ⟨5334882, by rfl⟩ : syracuseStep 14226353 = 10669765) B10669765
theorem B9484235 : Blo 2219435 9484235 := bstep (se 1 (by rfl) ⟨7113176, by rfl⟩ : syracuseStep 9484235 = 14226353) B14226353
theorem B6322823 : Blo 2219435 6322823 := bstep (se 1 (by rfl) ⟨4742117, by rfl⟩ : syracuseStep 6322823 = 9484235) B9484235
theorem B4215215 : Blo 2219435 4215215 := bstep (se 1 (by rfl) ⟨3161411, by rfl⟩ : syracuseStep 4215215 = 6322823) B6322823
theorem B2810143 : Blo 2219435 2810143 := bstep (se 1 (by rfl) ⟨2107607, by rfl⟩ : syracuseStep 2810143 = 4215215) B4215215
theorem B3746857 : Blo 2219435 3746857 := bstep (se 2 (by rfl) ⟨1405071, by rfl⟩ : syracuseStep 3746857 = 2810143) B2810143
theorem B4995809 : Blo 2219435 4995809 := bstep (se 2 (by rfl) ⟨1873428, by rfl⟩ : syracuseStep 4995809 = 3746857) B3746857
theorem B3330539 : Blo 2219435 3330539 := bstep (se 1 (by rfl) ⟨2497904, by rfl⟩ : syracuseStep 3330539 = 4995809) B4995809
theorem B2220359 : Blo 2219435 2220359 := bstep (se 1 (by rfl) ⟨1665269, by rfl⟩ : syracuseStep 2220359 = 3330539) B3330539
theorem B2497909 : Blo 2219435 2497909 := bbase (se 5 (by rfl) ⟨117089, by rfl⟩ : syracuseStep 2497909 = 234179) (by norm_num)
theorem B3330545 : Blo 2219435 3330545 := bstep (se 2 (by rfl) ⟨1248954, by rfl⟩ : syracuseStep 3330545 = 2497909) B2497909
theorem B2220363 : Blo 2219435 2220363 := bstep (se 1 (by rfl) ⟨1665272, by rfl⟩ : syracuseStep 2220363 = 3330545) B3330545
theorem B2810153 : Blo 2219435 2810153 := bbase (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) (by norm_num)
theorem B7493741 : Blo 2219435 7493741 := bstep (se 3 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 7493741 = 2810153) B2810153
theorem B4995827 : Blo 2219435 4995827 := bstep (se 1 (by rfl) ⟨3746870, by rfl⟩ : syracuseStep 4995827 = 7493741) B7493741
theorem B3330551 : Blo 2219435 3330551 := bstep (se 1 (by rfl) ⟨2497913, by rfl⟩ : syracuseStep 3330551 = 4995827) B4995827
theorem B2220367 : Blo 2219435 2220367 := bstep (se 1 (by rfl) ⟨1665275, by rfl⟩ : syracuseStep 2220367 = 3330551) B3330551
theorem B3330557 : Blo 2219435 3330557 := bbase (se 3 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 3330557 = 1248959) (by norm_num)
theorem B2220371 : Blo 2219435 2220371 := bstep (se 1 (by rfl) ⟨1665278, by rfl⟩ : syracuseStep 2220371 = 3330557) B3330557
theorem B4995845 : Blo 2219435 4995845 := bbase (se 4 (by rfl) ⟨468360, by rfl⟩ : syracuseStep 4995845 = 936721) (by norm_num)
theorem B3330563 : Blo 2219435 3330563 := bstep (se 1 (by rfl) ⟨2497922, by rfl⟩ : syracuseStep 3330563 = 4995845) B4995845
theorem B2220375 : Blo 2219435 2220375 := bstep (se 1 (by rfl) ⟨1665281, by rfl⟩ : syracuseStep 2220375 = 3330563) B3330563
theorem B4215253 : Blo 2219435 4215253 := bbase (se 7 (by rfl) ⟨49397, by rfl⟩ : syracuseStep 4215253 = 98795) (by norm_num)
theorem B5620337 : Blo 2219435 5620337 := bstep (se 2 (by rfl) ⟨2107626, by rfl⟩ : syracuseStep 5620337 = 4215253) B4215253
theorem B3746891 : Blo 2219435 3746891 := bstep (se 1 (by rfl) ⟨2810168, by rfl⟩ : syracuseStep 3746891 = 5620337) B5620337
theorem B2497927 : Blo 2219435 2497927 := bstep (se 1 (by rfl) ⟨1873445, by rfl⟩ : syracuseStep 2497927 = 3746891) B3746891
theorem B3330569 : Blo 2219435 3330569 := bstep (se 2 (by rfl) ⟨1248963, by rfl⟩ : syracuseStep 3330569 = 2497927) B2497927
theorem B2220379 : Blo 2219435 2220379 := bstep (se 1 (by rfl) ⟨1665284, by rfl⟩ : syracuseStep 2220379 = 3330569) B3330569
theorem B11240693 : Blo 2219435 11240693 := bbase (se 5 (by rfl) ⟨526907, by rfl⟩ : syracuseStep 11240693 = 1053815) (by norm_num)
theorem B7493795 : Blo 2219435 7493795 := bstep (se 1 (by rfl) ⟨5620346, by rfl⟩ : syracuseStep 7493795 = 11240693) B11240693
theorem B4995863 : Blo 2219435 4995863 := bstep (se 1 (by rfl) ⟨3746897, by rfl⟩ : syracuseStep 4995863 = 7493795) B7493795
theorem B3330575 : Blo 2219435 3330575 := bstep (se 1 (by rfl) ⟨2497931, by rfl⟩ : syracuseStep 3330575 = 4995863) B4995863
theorem B2220383 : Blo 2219435 2220383 := bstep (se 1 (by rfl) ⟨1665287, by rfl⟩ : syracuseStep 2220383 = 3330575) B3330575
theorem B3330581 : Blo 2219435 3330581 := bbase (se 6 (by rfl) ⟨78060, by rfl⟩ : syracuseStep 3330581 = 156121) (by norm_num)
theorem B2220387 : Blo 2219435 2220387 := bstep (se 1 (by rfl) ⟨1665290, by rfl⟩ : syracuseStep 2220387 = 3330581) B3330581
theorem B13504117 : Blo 2219435 13504117 := bbase (se 5 (by rfl) ⟨633005, by rfl⟩ : syracuseStep 13504117 = 1266011) (by norm_num)
theorem B18005489 : Blo 2219435 18005489 := bstep (se 2 (by rfl) ⟨6752058, by rfl⟩ : syracuseStep 18005489 = 13504117) B13504117
theorem B12003659 : Blo 2219435 12003659 := bstep (se 1 (by rfl) ⟨9002744, by rfl⟩ : syracuseStep 12003659 = 18005489) B18005489
theorem B8002439 : Blo 2219435 8002439 := bstep (se 1 (by rfl) ⟨6001829, by rfl⟩ : syracuseStep 8002439 = 12003659) B12003659
theorem B5334959 : Blo 2219435 5334959 := bstep (se 1 (by rfl) ⟨4001219, by rfl⟩ : syracuseStep 5334959 = 8002439) B8002439
theorem B3556639 : Blo 2219435 3556639 := bstep (se 1 (by rfl) ⟨2667479, by rfl⟩ : syracuseStep 3556639 = 5334959) B5334959
theorem B18968741 : Blo 2219435 18968741 := bstep (se 4 (by rfl) ⟨1778319, by rfl⟩ : syracuseStep 18968741 = 3556639) B3556639
theorem B12645827 : Blo 2219435 12645827 := bstep (se 1 (by rfl) ⟨9484370, by rfl⟩ : syracuseStep 12645827 = 18968741) B18968741
theorem B8430551 : Blo 2219435 8430551 := bstep (se 1 (by rfl) ⟨6322913, by rfl⟩ : syracuseStep 8430551 = 12645827) B12645827
theorem B5620367 : Blo 2219435 5620367 := bstep (se 1 (by rfl) ⟨4215275, by rfl⟩ : syracuseStep 5620367 = 8430551) B8430551
theorem B3746911 : Blo 2219435 3746911 := bstep (se 1 (by rfl) ⟨2810183, by rfl⟩ : syracuseStep 3746911 = 5620367) B5620367
theorem B4995881 : Blo 2219435 4995881 := bstep (se 2 (by rfl) ⟨1873455, by rfl⟩ : syracuseStep 4995881 = 3746911) B3746911
theorem B3330587 : Blo 2219435 3330587 := bstep (se 1 (by rfl) ⟨2497940, by rfl⟩ : syracuseStep 3330587 = 4995881) B4995881
theorem B2220391 : Blo 2219435 2220391 := bstep (se 1 (by rfl) ⟨1665293, by rfl⟩ : syracuseStep 2220391 = 3330587) B3330587
theorem B2497945 : Blo 2219435 2497945 := bbase (se 2 (by rfl) ⟨936729, by rfl⟩ : syracuseStep 2497945 = 1873459) (by norm_num)
theorem B3330593 : Blo 2219435 3330593 := bstep (se 2 (by rfl) ⟨1248972, by rfl⟩ : syracuseStep 3330593 = 2497945) B2497945
theorem B2220395 : Blo 2219435 2220395 := bstep (se 1 (by rfl) ⟨1665296, by rfl⟩ : syracuseStep 2220395 = 3330593) B3330593
theorem B8430581 : Blo 2219435 8430581 := bbase (se 5 (by rfl) ⟨395183, by rfl⟩ : syracuseStep 8430581 = 790367) (by norm_num)
theorem B5620387 : Blo 2219435 5620387 := bstep (se 1 (by rfl) ⟨4215290, by rfl⟩ : syracuseStep 5620387 = 8430581) B8430581
theorem B7493849 : Blo 2219435 7493849 := bstep (se 2 (by rfl) ⟨2810193, by rfl⟩ : syracuseStep 7493849 = 5620387) B5620387
theorem B4995899 : Blo 2219435 4995899 := bstep (se 1 (by rfl) ⟨3746924, by rfl⟩ : syracuseStep 4995899 = 7493849) B7493849
theorem B3330599 : Blo 2219435 3330599 := bstep (se 1 (by rfl) ⟨2497949, by rfl⟩ : syracuseStep 3330599 = 4995899) B4995899
theorem B2220399 : Blo 2219435 2220399 := bstep (se 1 (by rfl) ⟨1665299, by rfl⟩ : syracuseStep 2220399 = 3330599) B3330599
theorem B3330605 : Blo 2219435 3330605 := bbase (se 3 (by rfl) ⟨624488, by rfl⟩ : syracuseStep 3330605 = 1248977) (by norm_num)
theorem B2220403 : Blo 2219435 2220403 := bstep (se 1 (by rfl) ⟨1665302, by rfl⟩ : syracuseStep 2220403 = 3330605) B3330605
theorem B4995917 : Blo 2219435 4995917 := bbase (se 3 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 4995917 = 1873469) (by norm_num)
theorem B3330611 : Blo 2219435 3330611 := bstep (se 1 (by rfl) ⟨2497958, by rfl⟩ : syracuseStep 3330611 = 4995917) B4995917
theorem B2220407 : Blo 2219435 2220407 := bstep (se 1 (by rfl) ⟨1665305, by rfl⟩ : syracuseStep 2220407 = 3330611) B3330611
theorem B2810209 : Blo 2219435 2810209 := bbase (se 2 (by rfl) ⟨1053828, by rfl⟩ : syracuseStep 2810209 = 2107657) (by norm_num)
theorem B3746945 : Blo 2219435 3746945 := bstep (se 2 (by rfl) ⟨1405104, by rfl⟩ : syracuseStep 3746945 = 2810209) B2810209
theorem B2497963 : Blo 2219435 2497963 := bstep (se 1 (by rfl) ⟨1873472, by rfl⟩ : syracuseStep 2497963 = 3746945) B3746945
theorem B3330617 : Blo 2219435 3330617 := bstep (se 2 (by rfl) ⟨1248981, by rfl⟩ : syracuseStep 3330617 = 2497963) B2497963
theorem B2220411 : Blo 2219435 2220411 := bstep (se 1 (by rfl) ⟨1665308, by rfl⟩ : syracuseStep 2220411 = 3330617) B3330617
theorem B25291925 : Blo 2219435 25291925 := bbase (se 6 (by rfl) ⟨592779, by rfl⟩ : syracuseStep 25291925 = 1185559) (by norm_num)
theorem B16861283 : Blo 2219435 16861283 := bstep (se 1 (by rfl) ⟨12645962, by rfl⟩ : syracuseStep 16861283 = 25291925) B25291925
theorem B11240855 : Blo 2219435 11240855 := bstep (se 1 (by rfl) ⟨8430641, by rfl⟩ : syracuseStep 11240855 = 16861283) B16861283
theorem B7493903 : Blo 2219435 7493903 := bstep (se 1 (by rfl) ⟨5620427, by rfl⟩ : syracuseStep 7493903 = 11240855) B11240855
theorem B4995935 : Blo 2219435 4995935 := bstep (se 1 (by rfl) ⟨3746951, by rfl⟩ : syracuseStep 4995935 = 7493903) B7493903
theorem B3330623 : Blo 2219435 3330623 := bstep (se 1 (by rfl) ⟨2497967, by rfl⟩ : syracuseStep 3330623 = 4995935) B4995935
theorem B2220415 : Blo 2219435 2220415 := bstep (se 1 (by rfl) ⟨1665311, by rfl⟩ : syracuseStep 2220415 = 3330623) B3330623
theorem B3330629 : Blo 2219435 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B2220419 : Blo 2219435 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B3746965 : Blo 2219435 3746965 := bbase (se 6 (by rfl) ⟨87819, by rfl⟩ : syracuseStep 3746965 = 175639) (by norm_num)
theorem B4995953 : Blo 2219435 4995953 := bstep (se 2 (by rfl) ⟨1873482, by rfl⟩ : syracuseStep 4995953 = 3746965) B3746965
theorem B3330635 : Blo 2219435 3330635 := bstep (se 1 (by rfl) ⟨2497976, by rfl⟩ : syracuseStep 3330635 = 4995953) B4995953
theorem B2220423 : Blo 2219435 2220423 := bstep (se 1 (by rfl) ⟨1665317, by rfl⟩ : syracuseStep 2220423 = 3330635) B3330635
theorem B2497981 : Blo 2219435 2497981 := bbase (se 3 (by rfl) ⟨468371, by rfl⟩ : syracuseStep 2497981 = 936743) (by norm_num)
theorem B3330641 : Blo 2219435 3330641 := bstep (se 2 (by rfl) ⟨1248990, by rfl⟩ : syracuseStep 3330641 = 2497981) B2497981
theorem B2220427 : Blo 2219435 2220427 := bstep (se 1 (by rfl) ⟨1665320, by rfl⟩ : syracuseStep 2220427 = 3330641) B3330641
theorem B7493957 : Blo 2219435 7493957 := bbase (se 4 (by rfl) ⟨702558, by rfl⟩ : syracuseStep 7493957 = 1405117) (by norm_num)
theorem B4995971 : Blo 2219435 4995971 := bstep (se 1 (by rfl) ⟨3746978, by rfl⟩ : syracuseStep 4995971 = 7493957) B7493957
theorem B3330647 : Blo 2219435 3330647 := bstep (se 1 (by rfl) ⟨2497985, by rfl⟩ : syracuseStep 3330647 = 4995971) B4995971
theorem B2220431 : Blo 2219435 2220431 := bstep (se 1 (by rfl) ⟨1665323, by rfl⟩ : syracuseStep 2220431 = 3330647) B3330647
theorem B3330653 : Blo 2219435 3330653 := bbase (se 3 (by rfl) ⟨624497, by rfl⟩ : syracuseStep 3330653 = 1248995) (by norm_num)
theorem B2220435 : Blo 2219435 2220435 := bstep (se 1 (by rfl) ⟨1665326, by rfl⟩ : syracuseStep 2220435 = 3330653) B3330653
theorem B4995989 : Blo 2219435 4995989 := bbase (se 6 (by rfl) ⟨117093, by rfl⟩ : syracuseStep 4995989 = 234187) (by norm_num)
theorem B3330659 : Blo 2219435 3330659 := bstep (se 1 (by rfl) ⟨2497994, by rfl⟩ : syracuseStep 3330659 = 4995989) B4995989
theorem B2220439 : Blo 2219435 2220439 := bstep (se 1 (by rfl) ⟨1665329, by rfl⟩ : syracuseStep 2220439 = 3330659) B3330659
theorem B5335085 : Blo 2219435 5335085 := bbase (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) (by norm_num)
theorem B3556723 : Blo 2219435 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B4742297 : Blo 2219435 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B3161531 : Blo 2219435 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B8430749 : Blo 2219435 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B5620499 : Blo 2219435 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B3746999 : Blo 2219435 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B2497999 : Blo 2219435 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B3330665 : Blo 2219435 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B2220443 : Blo 2219435 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B5335093 : Blo 2219435 5335093 := bbase (se 5 (by rfl) ⟨250082, by rfl⟩ : syracuseStep 5335093 = 500165) (by norm_num)
theorem B7113457 : Blo 2219435 7113457 := bstep (se 2 (by rfl) ⟨2667546, by rfl⟩ : syracuseStep 7113457 = 5335093) B5335093
theorem B9484609 : Blo 2219435 9484609 := bstep (se 2 (by rfl) ⟨3556728, by rfl⟩ : syracuseStep 9484609 = 7113457) B7113457
theorem B12646145 : Blo 2219435 12646145 := bstep (se 2 (by rfl) ⟨4742304, by rfl⟩ : syracuseStep 12646145 = 9484609) B9484609
theorem B8430763 : Blo 2219435 8430763 := bstep (se 1 (by rfl) ⟨6323072, by rfl⟩ : syracuseStep 8430763 = 12646145) B12646145
theorem B11241017 : Blo 2219435 11241017 := bstep (se 2 (by rfl) ⟨4215381, by rfl⟩ : syracuseStep 11241017 = 8430763) B8430763
theorem B7494011 : Blo 2219435 7494011 := bstep (se 1 (by rfl) ⟨5620508, by rfl⟩ : syracuseStep 7494011 = 11241017) B11241017
theorem B4996007 : Blo 2219435 4996007 := bstep (se 1 (by rfl) ⟨3747005, by rfl⟩ : syracuseStep 4996007 = 7494011) B7494011
theorem B3330671 : Blo 2219435 3330671 := bstep (se 1 (by rfl) ⟨2498003, by rfl⟩ : syracuseStep 3330671 = 4996007) B4996007
theorem B2220447 : Blo 2219435 2220447 := bstep (se 1 (by rfl) ⟨1665335, by rfl⟩ : syracuseStep 2220447 = 3330671) B3330671
theorem B3330677 : Blo 2219435 3330677 := bbase (se 5 (by rfl) ⟨156125, by rfl⟩ : syracuseStep 3330677 = 312251) (by norm_num)
theorem B2220451 : Blo 2219435 2220451 := bstep (se 1 (by rfl) ⟨1665338, by rfl⟩ : syracuseStep 2220451 = 3330677) B3330677
theorem B4215397 : Blo 2219435 4215397 := bbase (se 4 (by rfl) ⟨395193, by rfl⟩ : syracuseStep 4215397 = 790387) (by norm_num)
theorem B5620529 : Blo 2219435 5620529 := bstep (se 2 (by rfl) ⟨2107698, by rfl⟩ : syracuseStep 5620529 = 4215397) B4215397
theorem B3747019 : Blo 2219435 3747019 := bstep (se 1 (by rfl) ⟨2810264, by rfl⟩ : syracuseStep 3747019 = 5620529) B5620529
theorem B4996025 : Blo 2219435 4996025 := bstep (se 2 (by rfl) ⟨1873509, by rfl⟩ : syracuseStep 4996025 = 3747019) B3747019
theorem B3330683 : Blo 2219435 3330683 := bstep (se 1 (by rfl) ⟨2498012, by rfl⟩ : syracuseStep 3330683 = 4996025) B4996025
theorem B2220455 : Blo 2219435 2220455 := bstep (se 1 (by rfl) ⟨1665341, by rfl⟩ : syracuseStep 2220455 = 3330683) B3330683
theorem B2498017 : Blo 2219435 2498017 := bbase (se 2 (by rfl) ⟨936756, by rfl⟩ : syracuseStep 2498017 = 1873513) (by norm_num)
theorem B3330689 : Blo 2219435 3330689 := bstep (se 2 (by rfl) ⟨1249008, by rfl⟩ : syracuseStep 3330689 = 2498017) B2498017
theorem B2220459 : Blo 2219435 2220459 := bstep (se 1 (by rfl) ⟨1665344, by rfl⟩ : syracuseStep 2220459 = 3330689) B3330689
theorem B5620549 : Blo 2219435 5620549 := bbase (se 4 (by rfl) ⟨526926, by rfl⟩ : syracuseStep 5620549 = 1053853) (by norm_num)
theorem B7494065 : Blo 2219435 7494065 := bstep (se 2 (by rfl) ⟨2810274, by rfl⟩ : syracuseStep 7494065 = 5620549) B5620549
theorem B4996043 : Blo 2219435 4996043 := bstep (se 1 (by rfl) ⟨3747032, by rfl⟩ : syracuseStep 4996043 = 7494065) B7494065
theorem B3330695 : Blo 2219435 3330695 := bstep (se 1 (by rfl) ⟨2498021, by rfl⟩ : syracuseStep 3330695 = 4996043) B4996043
theorem B2220463 : Blo 2219435 2220463 := bstep (se 1 (by rfl) ⟨1665347, by rfl⟩ : syracuseStep 2220463 = 3330695) B3330695
theorem B3330701 : Blo 2219435 3330701 := bbase (se 3 (by rfl) ⟨624506, by rfl⟩ : syracuseStep 3330701 = 1249013) (by norm_num)
theorem B2220467 : Blo 2219435 2220467 := bstep (se 1 (by rfl) ⟨1665350, by rfl⟩ : syracuseStep 2220467 = 3330701) B3330701
theorem B4996061 : Blo 2219435 4996061 := bbase (se 3 (by rfl) ⟨936761, by rfl⟩ : syracuseStep 4996061 = 1873523) (by norm_num)
theorem B3330707 : Blo 2219435 3330707 := bstep (se 1 (by rfl) ⟨2498030, by rfl⟩ : syracuseStep 3330707 = 4996061) B4996061
theorem B2220471 : Blo 2219435 2220471 := bstep (se 1 (by rfl) ⟨1665353, by rfl⟩ : syracuseStep 2220471 = 3330707) B3330707
theorem B3747053 : Blo 2219435 3747053 := bbase (se 3 (by rfl) ⟨702572, by rfl⟩ : syracuseStep 3747053 = 1405145) (by norm_num)
theorem B2498035 : Blo 2219435 2498035 := bstep (se 1 (by rfl) ⟨1873526, by rfl⟩ : syracuseStep 2498035 = 3747053) B3747053
theorem B3330713 : Blo 2219435 3330713 := bstep (se 2 (by rfl) ⟨1249017, by rfl⟩ : syracuseStep 3330713 = 2498035) B2498035
theorem B2220475 : Blo 2219435 2220475 := bstep (se 1 (by rfl) ⟨1665356, by rfl⟩ : syracuseStep 2220475 = 3330713) B3330713
theorem B5064245 : Blo 2219435 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B3376163 : Blo 2219435 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B2250775 : Blo 2219435 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B3001033 : Blo 2219435 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B16005509 : Blo 2219435 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B10670339 : Blo 2219435 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B28454237 : Blo 2219435 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B18969491 : Blo 2219435 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B12646327 : Blo 2219435 12646327 := bstep (se 1 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 12646327 = 18969491) B18969491
theorem B16861769 : Blo 2219435 16861769 := bstep (se 2 (by rfl) ⟨6323163, by rfl⟩ : syracuseStep 16861769 = 12646327) B12646327
theorem B11241179 : Blo 2219435 11241179 := bstep (se 1 (by rfl) ⟨8430884, by rfl⟩ : syracuseStep 11241179 = 16861769) B16861769
theorem B7494119 : Blo 2219435 7494119 := bstep (se 1 (by rfl) ⟨5620589, by rfl⟩ : syracuseStep 7494119 = 11241179) B11241179
theorem B4996079 : Blo 2219435 4996079 := bstep (se 1 (by rfl) ⟨3747059, by rfl⟩ : syracuseStep 4996079 = 7494119) B7494119
theorem B3330719 : Blo 2219435 3330719 := bstep (se 1 (by rfl) ⟨2498039, by rfl⟩ : syracuseStep 3330719 = 4996079) B4996079
theorem B2220479 : Blo 2219435 2220479 := bstep (se 1 (by rfl) ⟨1665359, by rfl⟩ : syracuseStep 2220479 = 3330719) B3330719
theorem B3330725 : Blo 2219435 3330725 := bbase (se 4 (by rfl) ⟨312255, by rfl⟩ : syracuseStep 3330725 = 624511) (by norm_num)
theorem B2220483 : Blo 2219435 2220483 := bstep (se 1 (by rfl) ⟨1665362, by rfl⟩ : syracuseStep 2220483 = 3330725) B3330725
theorem B2810305 : Blo 2219435 2810305 := bbase (se 2 (by rfl) ⟨1053864, by rfl⟩ : syracuseStep 2810305 = 2107729) (by norm_num)
theorem B3747073 : Blo 2219435 3747073 := bstep (se 2 (by rfl) ⟨1405152, by rfl⟩ : syracuseStep 3747073 = 2810305) B2810305
theorem B4996097 : Blo 2219435 4996097 := bstep (se 2 (by rfl) ⟨1873536, by rfl⟩ : syracuseStep 4996097 = 3747073) B3747073
theorem B3330731 : Blo 2219435 3330731 := bstep (se 1 (by rfl) ⟨2498048, by rfl⟩ : syracuseStep 3330731 = 4996097) B4996097
theorem B2220487 : Blo 2219435 2220487 := bstep (se 1 (by rfl) ⟨1665365, by rfl⟩ : syracuseStep 2220487 = 3330731) B3330731
theorem B2498053 : Blo 2219435 2498053 := bbase (se 4 (by rfl) ⟨234192, by rfl⟩ : syracuseStep 2498053 = 468385) (by norm_num)
theorem B3330737 : Blo 2219435 3330737 := bstep (se 2 (by rfl) ⟨1249026, by rfl⟩ : syracuseStep 3330737 = 2498053) B2498053
theorem B2220491 : Blo 2219435 2220491 := bstep (se 1 (by rfl) ⟨1665368, by rfl⟩ : syracuseStep 2220491 = 3330737) B3330737
theorem B3161605 : Blo 2219435 3161605 := bbase (se 4 (by rfl) ⟨296400, by rfl⟩ : syracuseStep 3161605 = 592801) (by norm_num)
theorem B4215473 : Blo 2219435 4215473 := bstep (se 2 (by rfl) ⟨1580802, by rfl⟩ : syracuseStep 4215473 = 3161605) B3161605
theorem B2810315 : Blo 2219435 2810315 := bstep (se 1 (by rfl) ⟨2107736, by rfl⟩ : syracuseStep 2810315 = 4215473) B4215473
theorem B7494173 : Blo 2219435 7494173 := bstep (se 3 (by rfl) ⟨1405157, by rfl⟩ : syracuseStep 7494173 = 2810315) B2810315
theorem B4996115 : Blo 2219435 4996115 := bstep (se 1 (by rfl) ⟨3747086, by rfl⟩ : syracuseStep 4996115 = 7494173) B7494173
theorem B3330743 : Blo 2219435 3330743 := bstep (se 1 (by rfl) ⟨2498057, by rfl⟩ : syracuseStep 3330743 = 4996115) B4996115
theorem B2220495 : Blo 2219435 2220495 := bstep (se 1 (by rfl) ⟨1665371, by rfl⟩ : syracuseStep 2220495 = 3330743) B3330743
theorem B3330749 : Blo 2219435 3330749 := bbase (se 3 (by rfl) ⟨624515, by rfl⟩ : syracuseStep 3330749 = 1249031) (by norm_num)
theorem B2220499 : Blo 2219435 2220499 := bstep (se 1 (by rfl) ⟨1665374, by rfl⟩ : syracuseStep 2220499 = 3330749) B3330749
theorem B4996133 : Blo 2219435 4996133 := bbase (se 4 (by rfl) ⟨468387, by rfl⟩ : syracuseStep 4996133 = 936775) (by norm_num)
theorem B3330755 : Blo 2219435 3330755 := bstep (se 1 (by rfl) ⟨2498066, by rfl⟩ : syracuseStep 3330755 = 4996133) B4996133
theorem B2220503 : Blo 2219435 2220503 := bstep (se 1 (by rfl) ⟨1665377, by rfl⟩ : syracuseStep 2220503 = 3330755) B3330755
theorem B5620661 : Blo 2219435 5620661 := bbase (se 5 (by rfl) ⟨263468, by rfl⟩ : syracuseStep 5620661 = 526937) (by norm_num)
theorem B3747107 : Blo 2219435 3747107 := bstep (se 1 (by rfl) ⟨2810330, by rfl⟩ : syracuseStep 3747107 = 5620661) B5620661
theorem B2498071 : Blo 2219435 2498071 := bstep (se 1 (by rfl) ⟨1873553, by rfl⟩ : syracuseStep 2498071 = 3747107) B3747107
theorem B3330761 : Blo 2219435 3330761 := bstep (se 2 (by rfl) ⟨1249035, by rfl⟩ : syracuseStep 3330761 = 2498071) B2498071
theorem B2220507 : Blo 2219435 2220507 := bstep (se 1 (by rfl) ⟨1665380, by rfl⟩ : syracuseStep 2220507 = 3330761) B3330761
theorem B4331317 : Blo 2219435 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B5775089 : Blo 2219435 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B61600949 : Blo 2219435 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B41067299 : Blo 2219435 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B27378199 : Blo 2219435 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B36504265 : Blo 2219435 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B48672353 : Blo 2219435 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B32448235 : Blo 2219435 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B43264313 : Blo 2219435 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B28842875 : Blo 2219435 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B19228583 : Blo 2219435 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B12819055 : Blo 2219435 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B17092073 : Blo 2219435 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B11394715 : Blo 2219435 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B15192953 : Blo 2219435 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B10128635 : Blo 2219435 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B6752423 : Blo 2219435 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B18006461 : Blo 2219435 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B12004307 : Blo 2219435 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B8002871 : Blo 2219435 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B5335247 : Blo 2219435 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B14227325 : Blo 2219435 14227325 := bstep (se 3 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 14227325 = 5335247) B5335247
theorem B9484883 : Blo 2219435 9484883 := bstep (se 1 (by rfl) ⟨7113662, by rfl⟩ : syracuseStep 9484883 = 14227325) B14227325
theorem B6323255 : Blo 2219435 6323255 := bstep (se 1 (by rfl) ⟨4742441, by rfl⟩ : syracuseStep 6323255 = 9484883) B9484883
theorem B4215503 : Blo 2219435 4215503 := bstep (se 1 (by rfl) ⟨3161627, by rfl⟩ : syracuseStep 4215503 = 6323255) B6323255
theorem B11241341 : Blo 2219435 11241341 := bstep (se 3 (by rfl) ⟨2107751, by rfl⟩ : syracuseStep 11241341 = 4215503) B4215503
theorem B7494227 : Blo 2219435 7494227 := bstep (se 1 (by rfl) ⟨5620670, by rfl⟩ : syracuseStep 7494227 = 11241341) B11241341
theorem B4996151 : Blo 2219435 4996151 := bstep (se 1 (by rfl) ⟨3747113, by rfl⟩ : syracuseStep 4996151 = 7494227) B7494227
theorem B3330767 : Blo 2219435 3330767 := bstep (se 1 (by rfl) ⟨2498075, by rfl⟩ : syracuseStep 3330767 = 4996151) B4996151
theorem B2220511 : Blo 2219435 2220511 := bstep (se 1 (by rfl) ⟨1665383, by rfl⟩ : syracuseStep 2220511 = 3330767) B3330767
theorem B3330773 : Blo 2219435 3330773 := bbase (se 7 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 3330773 = 78065) (by norm_num)
theorem B2220515 : Blo 2219435 2220515 := bstep (se 1 (by rfl) ⟨1665386, by rfl⟩ : syracuseStep 2220515 = 3330773) B3330773
theorem B8002901 : Blo 2219435 8002901 := bbase (se 11 (by rfl) ⟨5861, by rfl⟩ : syracuseStep 8002901 = 11723) (by norm_num)
theorem B5335267 : Blo 2219435 5335267 := bstep (se 1 (by rfl) ⟨4001450, by rfl⟩ : syracuseStep 5335267 = 8002901) B8002901
theorem B7113689 : Blo 2219435 7113689 := bstep (se 2 (by rfl) ⟨2667633, by rfl⟩ : syracuseStep 7113689 = 5335267) B5335267
theorem B4742459 : Blo 2219435 4742459 := bstep (se 1 (by rfl) ⟨3556844, by rfl⟩ : syracuseStep 4742459 = 7113689) B7113689
theorem B3161639 : Blo 2219435 3161639 := bstep (se 1 (by rfl) ⟨2371229, by rfl⟩ : syracuseStep 3161639 = 4742459) B4742459
theorem B8431037 : Blo 2219435 8431037 := bstep (se 3 (by rfl) ⟨1580819, by rfl⟩ : syracuseStep 8431037 = 3161639) B3161639
theorem B5620691 : Blo 2219435 5620691 := bstep (se 1 (by rfl) ⟨4215518, by rfl⟩ : syracuseStep 5620691 = 8431037) B8431037
theorem B3747127 : Blo 2219435 3747127 := bstep (se 1 (by rfl) ⟨2810345, by rfl⟩ : syracuseStep 3747127 = 5620691) B5620691
theorem B4996169 : Blo 2219435 4996169 := bstep (se 2 (by rfl) ⟨1873563, by rfl⟩ : syracuseStep 4996169 = 3747127) B3747127
theorem B3330779 : Blo 2219435 3330779 := bstep (se 1 (by rfl) ⟨2498084, by rfl⟩ : syracuseStep 3330779 = 4996169) B4996169
theorem B2220519 : Blo 2219435 2220519 := bstep (se 1 (by rfl) ⟨1665389, by rfl⟩ : syracuseStep 2220519 = 3330779) B3330779
theorem B2498089 : Blo 2219435 2498089 := bbase (se 2 (by rfl) ⟨936783, by rfl⟩ : syracuseStep 2498089 = 1873567) (by norm_num)
theorem B3330785 : Blo 2219435 3330785 := bstep (se 2 (by rfl) ⟨1249044, by rfl⟩ : syracuseStep 3330785 = 2498089) B2498089
theorem B2220523 : Blo 2219435 2220523 := bstep (se 1 (by rfl) ⟨1665392, by rfl⟩ : syracuseStep 2220523 = 3330785) B3330785
theorem B21341141 : Blo 2219435 21341141 := bbase (se 7 (by rfl) ⟨250091, by rfl⟩ : syracuseStep 21341141 = 500183) (by norm_num)
theorem B14227427 : Blo 2219435 14227427 := bstep (se 1 (by rfl) ⟨10670570, by rfl⟩ : syracuseStep 14227427 = 21341141) B21341141
theorem B9484951 : Blo 2219435 9484951 := bstep (se 1 (by rfl) ⟨7113713, by rfl⟩ : syracuseStep 9484951 = 14227427) B14227427
theorem B12646601 : Blo 2219435 12646601 := bstep (se 2 (by rfl) ⟨4742475, by rfl⟩ : syracuseStep 12646601 = 9484951) B9484951
theorem B8431067 : Blo 2219435 8431067 := bstep (se 1 (by rfl) ⟨6323300, by rfl⟩ : syracuseStep 8431067 = 12646601) B12646601
theorem B5620711 : Blo 2219435 5620711 := bstep (se 1 (by rfl) ⟨4215533, by rfl⟩ : syracuseStep 5620711 = 8431067) B8431067
theorem B7494281 : Blo 2219435 7494281 := bstep (se 2 (by rfl) ⟨2810355, by rfl⟩ : syracuseStep 7494281 = 5620711) B5620711
theorem B4996187 : Blo 2219435 4996187 := bstep (se 1 (by rfl) ⟨3747140, by rfl⟩ : syracuseStep 4996187 = 7494281) B7494281
theorem B3330791 : Blo 2219435 3330791 := bstep (se 1 (by rfl) ⟨2498093, by rfl⟩ : syracuseStep 3330791 = 4996187) B4996187
theorem B2220527 : Blo 2219435 2220527 := bstep (se 1 (by rfl) ⟨1665395, by rfl⟩ : syracuseStep 2220527 = 3330791) B3330791
theorem B3330797 : Blo 2219435 3330797 := bbase (se 3 (by rfl) ⟨624524, by rfl⟩ : syracuseStep 3330797 = 1249049) (by norm_num)
theorem B2220531 : Blo 2219435 2220531 := bstep (se 1 (by rfl) ⟨1665398, by rfl⟩ : syracuseStep 2220531 = 3330797) B3330797
theorem B4996205 : Blo 2219435 4996205 := bbase (se 3 (by rfl) ⟨936788, by rfl⟩ : syracuseStep 4996205 = 1873577) (by norm_num)
theorem B3330803 : Blo 2219435 3330803 := bstep (se 1 (by rfl) ⟨2498102, by rfl⟩ : syracuseStep 3330803 = 4996205) B4996205
theorem B2220535 : Blo 2219435 2220535 := bstep (se 1 (by rfl) ⟨1665401, by rfl⟩ : syracuseStep 2220535 = 3330803) B3330803
theorem B4215557 : Blo 2219435 4215557 := bbase (se 4 (by rfl) ⟨395208, by rfl⟩ : syracuseStep 4215557 = 790417) (by norm_num)
theorem B2810371 : Blo 2219435 2810371 := bstep (se 1 (by rfl) ⟨2107778, by rfl⟩ : syracuseStep 2810371 = 4215557) B4215557
theorem B3747161 : Blo 2219435 3747161 := bstep (se 2 (by rfl) ⟨1405185, by rfl⟩ : syracuseStep 3747161 = 2810371) B2810371
theorem B2498107 : Blo 2219435 2498107 := bstep (se 1 (by rfl) ⟨1873580, by rfl⟩ : syracuseStep 2498107 = 3747161) B3747161
theorem B3330809 : Blo 2219435 3330809 := bstep (se 2 (by rfl) ⟨1249053, by rfl⟩ : syracuseStep 3330809 = 2498107) B2498107
theorem B2220539 : Blo 2219435 2220539 := bstep (se 1 (by rfl) ⟨1665404, by rfl⟩ : syracuseStep 2220539 = 3330809) B3330809
theorem B5408117 : Blo 2219435 5408117 := bbase (se 5 (by rfl) ⟨253505, by rfl⟩ : syracuseStep 5408117 = 507011) (by norm_num)
theorem B3605411 : Blo 2219435 3605411 := bstep (se 1 (by rfl) ⟨2704058, by rfl⟩ : syracuseStep 3605411 = 5408117) B5408117
theorem B9614429 : Blo 2219435 9614429 := bstep (se 3 (by rfl) ⟨1802705, by rfl⟩ : syracuseStep 9614429 = 3605411) B3605411
theorem B6409619 : Blo 2219435 6409619 := bstep (se 1 (by rfl) ⟨4807214, by rfl⟩ : syracuseStep 6409619 = 9614429) B9614429
theorem B4273079 : Blo 2219435 4273079 := bstep (se 1 (by rfl) ⟨3204809, by rfl⟩ : syracuseStep 4273079 = 6409619) B6409619
theorem B11394877 : Blo 2219435 11394877 := bstep (se 3 (by rfl) ⟨2136539, by rfl⟩ : syracuseStep 11394877 = 4273079) B4273079
theorem B15193169 : Blo 2219435 15193169 := bstep (se 2 (by rfl) ⟨5697438, by rfl⟩ : syracuseStep 15193169 = 11394877) B11394877
theorem B10128779 : Blo 2219435 10128779 := bstep (se 1 (by rfl) ⟨7596584, by rfl⟩ : syracuseStep 10128779 = 15193169) B15193169
theorem B6752519 : Blo 2219435 6752519 := bstep (se 1 (by rfl) ⟨5064389, by rfl⟩ : syracuseStep 6752519 = 10128779) B10128779
theorem B4501679 : Blo 2219435 4501679 := bstep (se 1 (by rfl) ⟨3376259, by rfl⟩ : syracuseStep 4501679 = 6752519) B6752519
theorem B48017909 : Blo 2219435 48017909 := bstep (se 5 (by rfl) ⟨2250839, by rfl⟩ : syracuseStep 48017909 = 4501679) B4501679
theorem B32011939 : Blo 2219435 32011939 := bstep (se 1 (by rfl) ⟨24008954, by rfl⟩ : syracuseStep 32011939 = 48017909) B48017909
theorem B42682585 : Blo 2219435 42682585 := bstep (se 2 (by rfl) ⟨16005969, by rfl⟩ : syracuseStep 42682585 = 32011939) B32011939
theorem B56910113 : Blo 2219435 56910113 := bstep (se 2 (by rfl) ⟨21341292, by rfl⟩ : syracuseStep 56910113 = 42682585) B42682585
theorem B37940075 : Blo 2219435 37940075 := bstep (se 1 (by rfl) ⟨28455056, by rfl⟩ : syracuseStep 37940075 = 56910113) B56910113
theorem B25293383 : Blo 2219435 25293383 := bstep (se 1 (by rfl) ⟨18970037, by rfl⟩ : syracuseStep 25293383 = 37940075) B37940075
theorem B16862255 : Blo 2219435 16862255 := bstep (se 1 (by rfl) ⟨12646691, by rfl⟩ : syracuseStep 16862255 = 25293383) B25293383
theorem B11241503 : Blo 2219435 11241503 := bstep (se 1 (by rfl) ⟨8431127, by rfl⟩ : syracuseStep 11241503 = 16862255) B16862255
theorem B7494335 : Blo 2219435 7494335 := bstep (se 1 (by rfl) ⟨5620751, by rfl⟩ : syracuseStep 7494335 = 11241503) B11241503
theorem B4996223 : Blo 2219435 4996223 := bstep (se 1 (by rfl) ⟨3747167, by rfl⟩ : syracuseStep 4996223 = 7494335) B7494335
theorem B3330815 : Blo 2219435 3330815 := bstep (se 1 (by rfl) ⟨2498111, by rfl⟩ : syracuseStep 3330815 = 4996223) B4996223
theorem B2220543 : Blo 2219435 2220543 := bstep (se 1 (by rfl) ⟨1665407, by rfl⟩ : syracuseStep 2220543 = 3330815) B3330815
theorem B3330821 : Blo 2219435 3330821 := bbase (se 4 (by rfl) ⟨312264, by rfl⟩ : syracuseStep 3330821 = 624529) (by norm_num)
theorem B2220547 : Blo 2219435 2220547 := bstep (se 1 (by rfl) ⟨1665410, by rfl⟩ : syracuseStep 2220547 = 3330821) B3330821
theorem B3747181 : Blo 2219435 3747181 := bbase (se 3 (by rfl) ⟨702596, by rfl⟩ : syracuseStep 3747181 = 1405193) (by norm_num)
theorem B4996241 : Blo 2219435 4996241 := bstep (se 2 (by rfl) ⟨1873590, by rfl⟩ : syracuseStep 4996241 = 3747181) B3747181
theorem B3330827 : Blo 2219435 3330827 := bstep (se 1 (by rfl) ⟨2498120, by rfl⟩ : syracuseStep 3330827 = 4996241) B4996241
theorem B2220551 : Blo 2219435 2220551 := bstep (se 1 (by rfl) ⟨1665413, by rfl⟩ : syracuseStep 2220551 = 3330827) B3330827
theorem B2498125 : Blo 2219435 2498125 := bbase (se 3 (by rfl) ⟨468398, by rfl⟩ : syracuseStep 2498125 = 936797) (by norm_num)
theorem B3330833 : Blo 2219435 3330833 := bstep (se 2 (by rfl) ⟨1249062, by rfl⟩ : syracuseStep 3330833 = 2498125) B2498125
theorem B2220555 : Blo 2219435 2220555 := bstep (se 1 (by rfl) ⟨1665416, by rfl⟩ : syracuseStep 2220555 = 3330833) B3330833
theorem B7494389 : Blo 2219435 7494389 := bbase (se 5 (by rfl) ⟨351299, by rfl⟩ : syracuseStep 7494389 = 702599) (by norm_num)
theorem B4996259 : Blo 2219435 4996259 := bstep (se 1 (by rfl) ⟨3747194, by rfl⟩ : syracuseStep 4996259 = 7494389) B7494389
theorem B3330839 : Blo 2219435 3330839 := bstep (se 1 (by rfl) ⟨2498129, by rfl⟩ : syracuseStep 3330839 = 4996259) B4996259
theorem B2220559 : Blo 2219435 2220559 := bstep (se 1 (by rfl) ⟨1665419, by rfl⟩ : syracuseStep 2220559 = 3330839) B3330839
theorem B3330845 : Blo 2219435 3330845 := bbase (se 3 (by rfl) ⟨624533, by rfl⟩ : syracuseStep 3330845 = 1249067) (by norm_num)
theorem B2220563 : Blo 2219435 2220563 := bstep (se 1 (by rfl) ⟨1665422, by rfl⟩ : syracuseStep 2220563 = 3330845) B3330845
theorem B4996277 : Blo 2219435 4996277 := bbase (se 5 (by rfl) ⟨234200, by rfl⟩ : syracuseStep 4996277 = 468401) (by norm_num)
theorem B3330851 : Blo 2219435 3330851 := bstep (se 1 (by rfl) ⟨2498138, by rfl⟩ : syracuseStep 3330851 = 4996277) B4996277
theorem B2220567 : Blo 2219435 2220567 := bstep (se 1 (by rfl) ⟨1665425, by rfl⟩ : syracuseStep 2220567 = 3330851) B3330851
theorem B2371285 : Blo 2219435 2371285 := bbase (se 7 (by rfl) ⟨27788, by rfl⟩ : syracuseStep 2371285 = 55577) (by norm_num)
theorem B12646853 : Blo 2219435 12646853 := bstep (se 4 (by rfl) ⟨1185642, by rfl⟩ : syracuseStep 12646853 = 2371285) B2371285
theorem B8431235 : Blo 2219435 8431235 := bstep (se 1 (by rfl) ⟨6323426, by rfl⟩ : syracuseStep 8431235 = 12646853) B12646853
theorem B5620823 : Blo 2219435 5620823 := bstep (se 1 (by rfl) ⟨4215617, by rfl⟩ : syracuseStep 5620823 = 8431235) B8431235
theorem B3747215 : Blo 2219435 3747215 := bstep (se 1 (by rfl) ⟨2810411, by rfl⟩ : syracuseStep 3747215 = 5620823) B5620823
theorem B2498143 : Blo 2219435 2498143 := bstep (se 1 (by rfl) ⟨1873607, by rfl⟩ : syracuseStep 2498143 = 3747215) B3747215
theorem B3330857 : Blo 2219435 3330857 := bstep (se 2 (by rfl) ⟨1249071, by rfl⟩ : syracuseStep 3330857 = 2498143) B2498143
theorem B2220571 : Blo 2219435 2220571 := bstep (se 1 (by rfl) ⟨1665428, by rfl⟩ : syracuseStep 2220571 = 3330857) B3330857
theorem B2371289 : Blo 2219435 2371289 := bbase (se 2 (by rfl) ⟨889233, by rfl⟩ : syracuseStep 2371289 = 1778467) (by norm_num)
theorem B6323437 : Blo 2219435 6323437 := bstep (se 3 (by rfl) ⟨1185644, by rfl⟩ : syracuseStep 6323437 = 2371289) B2371289
theorem B8431249 : Blo 2219435 8431249 := bstep (se 2 (by rfl) ⟨3161718, by rfl⟩ : syracuseStep 8431249 = 6323437) B6323437
theorem B11241665 : Blo 2219435 11241665 := bstep (se 2 (by rfl) ⟨4215624, by rfl⟩ : syracuseStep 11241665 = 8431249) B8431249
theorem B7494443 : Blo 2219435 7494443 := bstep (se 1 (by rfl) ⟨5620832, by rfl⟩ : syracuseStep 7494443 = 11241665) B11241665
theorem B4996295 : Blo 2219435 4996295 := bstep (se 1 (by rfl) ⟨3747221, by rfl⟩ : syracuseStep 4996295 = 7494443) B7494443
theorem B3330863 : Blo 2219435 3330863 := bstep (se 1 (by rfl) ⟨2498147, by rfl⟩ : syracuseStep 3330863 = 4996295) B4996295
theorem B2220575 : Blo 2219435 2220575 := bstep (se 1 (by rfl) ⟨1665431, by rfl⟩ : syracuseStep 2220575 = 3330863) B3330863
theorem B3330869 : Blo 2219435 3330869 := bbase (se 5 (by rfl) ⟨156134, by rfl⟩ : syracuseStep 3330869 = 312269) (by norm_num)
theorem B2220579 : Blo 2219435 2220579 := bstep (se 1 (by rfl) ⟨1665434, by rfl⟩ : syracuseStep 2220579 = 3330869) B3330869
theorem B5620853 : Blo 2219435 5620853 := bbase (se 5 (by rfl) ⟨263477, by rfl⟩ : syracuseStep 5620853 = 526955) (by norm_num)
theorem B3747235 : Blo 2219435 3747235 := bstep (se 1 (by rfl) ⟨2810426, by rfl⟩ : syracuseStep 3747235 = 5620853) B5620853
theorem B4996313 : Blo 2219435 4996313 := bstep (se 2 (by rfl) ⟨1873617, by rfl⟩ : syracuseStep 4996313 = 3747235) B3747235
theorem B3330875 : Blo 2219435 3330875 := bstep (se 1 (by rfl) ⟨2498156, by rfl⟩ : syracuseStep 3330875 = 4996313) B4996313
theorem B2220583 : Blo 2219435 2220583 := bstep (se 1 (by rfl) ⟨1665437, by rfl⟩ : syracuseStep 2220583 = 3330875) B3330875
theorem B2498161 : Blo 2219435 2498161 := bbase (se 2 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 2498161 = 1873621) (by norm_num)
theorem B3330881 : Blo 2219435 3330881 := bstep (se 2 (by rfl) ⟨1249080, by rfl⟩ : syracuseStep 3330881 = 2498161) B2498161
theorem B2220587 : Blo 2219435 2220587 := bstep (se 1 (by rfl) ⟨1665440, by rfl⟩ : syracuseStep 2220587 = 3330881) B3330881
theorem B3248605 : Blo 2219435 3248605 := bbase (se 3 (by rfl) ⟨609113, by rfl⟩ : syracuseStep 3248605 = 1218227) (by norm_num)
theorem B17325893 : Blo 2219435 17325893 := bstep (se 4 (by rfl) ⟨1624302, by rfl⟩ : syracuseStep 17325893 = 3248605) B3248605
theorem B11550595 : Blo 2219435 11550595 := bstep (se 1 (by rfl) ⟨8662946, by rfl⟩ : syracuseStep 11550595 = 17325893) B17325893
theorem B15400793 : Blo 2219435 15400793 := bstep (se 2 (by rfl) ⟨5775297, by rfl⟩ : syracuseStep 15400793 = 11550595) B11550595
theorem B10267195 : Blo 2219435 10267195 := bstep (se 1 (by rfl) ⟨7700396, by rfl⟩ : syracuseStep 10267195 = 15400793) B15400793
theorem B13689593 : Blo 2219435 13689593 := bstep (se 2 (by rfl) ⟨5133597, by rfl⟩ : syracuseStep 13689593 = 10267195) B10267195
theorem B9126395 : Blo 2219435 9126395 := bstep (se 1 (by rfl) ⟨6844796, by rfl⟩ : syracuseStep 9126395 = 13689593) B13689593
theorem B6084263 : Blo 2219435 6084263 := bstep (se 1 (by rfl) ⟨4563197, by rfl⟩ : syracuseStep 6084263 = 9126395) B9126395
theorem B4056175 : Blo 2219435 4056175 := bstep (se 1 (by rfl) ⟨3042131, by rfl⟩ : syracuseStep 4056175 = 6084263) B6084263
theorem B21632933 : Blo 2219435 21632933 := bstep (se 4 (by rfl) ⟨2028087, by rfl⟩ : syracuseStep 21632933 = 4056175) B4056175
theorem B57687821 : Blo 2219435 57687821 := bstep (se 3 (by rfl) ⟨10816466, by rfl⟩ : syracuseStep 57687821 = 21632933) B21632933
theorem B38458547 : Blo 2219435 38458547 := bstep (se 1 (by rfl) ⟨28843910, by rfl⟩ : syracuseStep 38458547 = 57687821) B57687821
theorem B25639031 : Blo 2219435 25639031 := bstep (se 1 (by rfl) ⟨19229273, by rfl⟩ : syracuseStep 25639031 = 38458547) B38458547
theorem B17092687 : Blo 2219435 17092687 := bstep (se 1 (by rfl) ⟨12819515, by rfl⟩ : syracuseStep 17092687 = 25639031) B25639031
theorem B22790249 : Blo 2219435 22790249 := bstep (se 2 (by rfl) ⟨8546343, by rfl⟩ : syracuseStep 22790249 = 17092687) B17092687
theorem B15193499 : Blo 2219435 15193499 := bstep (se 1 (by rfl) ⟨11395124, by rfl⟩ : syracuseStep 15193499 = 22790249) B22790249
theorem B40515997 : Blo 2219435 40515997 := bstep (se 3 (by rfl) ⟨7596749, by rfl⟩ : syracuseStep 40515997 = 15193499) B15193499
theorem B54021329 : Blo 2219435 54021329 := bstep (se 2 (by rfl) ⟨20257998, by rfl⟩ : syracuseStep 54021329 = 40515997) B40515997
theorem B36014219 : Blo 2219435 36014219 := bstep (se 1 (by rfl) ⟨27010664, by rfl⟩ : syracuseStep 36014219 = 54021329) B54021329
theorem B24009479 : Blo 2219435 24009479 := bstep (se 1 (by rfl) ⟨18007109, by rfl⟩ : syracuseStep 24009479 = 36014219) B36014219
theorem B16006319 : Blo 2219435 16006319 := bstep (se 1 (by rfl) ⟨12004739, by rfl⟩ : syracuseStep 16006319 = 24009479) B24009479
theorem B10670879 : Blo 2219435 10670879 := bstep (se 1 (by rfl) ⟨8003159, by rfl⟩ : syracuseStep 10670879 = 16006319) B16006319
theorem B7113919 : Blo 2219435 7113919 := bstep (se 1 (by rfl) ⟨5335439, by rfl⟩ : syracuseStep 7113919 = 10670879) B10670879
theorem B9485225 : Blo 2219435 9485225 := bstep (se 2 (by rfl) ⟨3556959, by rfl⟩ : syracuseStep 9485225 = 7113919) B7113919
theorem B6323483 : Blo 2219435 6323483 := bstep (se 1 (by rfl) ⟨4742612, by rfl⟩ : syracuseStep 6323483 = 9485225) B9485225
theorem B4215655 : Blo 2219435 4215655 := bstep (se 1 (by rfl) ⟨3161741, by rfl⟩ : syracuseStep 4215655 = 6323483) B6323483
theorem B5620873 : Blo 2219435 5620873 := bstep (se 2 (by rfl) ⟨2107827, by rfl⟩ : syracuseStep 5620873 = 4215655) B4215655
theorem B7494497 : Blo 2219435 7494497 := bstep (se 2 (by rfl) ⟨2810436, by rfl⟩ : syracuseStep 7494497 = 5620873) B5620873
theorem B4996331 : Blo 2219435 4996331 := bstep (se 1 (by rfl) ⟨3747248, by rfl⟩ : syracuseStep 4996331 = 7494497) B7494497
theorem B3330887 : Blo 2219435 3330887 := bstep (se 1 (by rfl) ⟨2498165, by rfl⟩ : syracuseStep 3330887 = 4996331) B4996331
theorem B2220591 : Blo 2219435 2220591 := bstep (se 1 (by rfl) ⟨1665443, by rfl⟩ : syracuseStep 2220591 = 3330887) B3330887
theorem B3330893 : Blo 2219435 3330893 := bbase (se 3 (by rfl) ⟨624542, by rfl⟩ : syracuseStep 3330893 = 1249085) (by norm_num)
theorem B2220595 : Blo 2219435 2220595 := bstep (se 1 (by rfl) ⟨1665446, by rfl⟩ : syracuseStep 2220595 = 3330893) B3330893
theorem B4996349 : Blo 2219435 4996349 := bbase (se 3 (by rfl) ⟨936815, by rfl⟩ : syracuseStep 4996349 = 1873631) (by norm_num)
theorem B3330899 : Blo 2219435 3330899 := bstep (se 1 (by rfl) ⟨2498174, by rfl⟩ : syracuseStep 3330899 = 4996349) B4996349
theorem B2220599 : Blo 2219435 2220599 := bstep (se 1 (by rfl) ⟨1665449, by rfl⟩ : syracuseStep 2220599 = 3330899) B3330899
theorem B3747269 : Blo 2219435 3747269 := bbase (se 4 (by rfl) ⟨351306, by rfl⟩ : syracuseStep 3747269 = 702613) (by norm_num)
theorem B2498179 : Blo 2219435 2498179 := bstep (se 1 (by rfl) ⟨1873634, by rfl⟩ : syracuseStep 2498179 = 3747269) B3747269
theorem B3330905 : Blo 2219435 3330905 := bstep (se 2 (by rfl) ⟨1249089, by rfl⟩ : syracuseStep 3330905 = 2498179) B2498179
theorem B2220603 : Blo 2219435 2220603 := bstep (se 1 (by rfl) ⟨1665452, by rfl⟩ : syracuseStep 2220603 = 3330905) B3330905
theorem B16862741 : Blo 2219435 16862741 := bbase (se 6 (by rfl) ⟨395220, by rfl⟩ : syracuseStep 16862741 = 790441) (by norm_num)
theorem B11241827 : Blo 2219435 11241827 := bstep (se 1 (by rfl) ⟨8431370, by rfl⟩ : syracuseStep 11241827 = 16862741) B16862741
theorem B7494551 : Blo 2219435 7494551 := bstep (se 1 (by rfl) ⟨5620913, by rfl⟩ : syracuseStep 7494551 = 11241827) B11241827
theorem B4996367 : Blo 2219435 4996367 := bstep (se 1 (by rfl) ⟨3747275, by rfl⟩ : syracuseStep 4996367 = 7494551) B7494551
theorem B3330911 : Blo 2219435 3330911 := bstep (se 1 (by rfl) ⟨2498183, by rfl⟩ : syracuseStep 3330911 = 4996367) B4996367
theorem B2220607 : Blo 2219435 2220607 := bstep (se 1 (by rfl) ⟨1665455, by rfl⟩ : syracuseStep 2220607 = 3330911) B3330911
theorem B3330917 : Blo 2219435 3330917 := bbase (se 4 (by rfl) ⟨312273, by rfl⟩ : syracuseStep 3330917 = 624547) (by norm_num)
theorem B2220611 : Blo 2219435 2220611 := bstep (se 1 (by rfl) ⟨1665458, by rfl⟩ : syracuseStep 2220611 = 3330917) B3330917
theorem B4215701 : Blo 2219435 4215701 := bbase (se 6 (by rfl) ⟨98805, by rfl⟩ : syracuseStep 4215701 = 197611) (by norm_num)
theorem B2810467 : Blo 2219435 2810467 := bstep (se 1 (by rfl) ⟨2107850, by rfl⟩ : syracuseStep 2810467 = 4215701) B4215701
theorem B3747289 : Blo 2219435 3747289 := bstep (se 2 (by rfl) ⟨1405233, by rfl⟩ : syracuseStep 3747289 = 2810467) B2810467
theorem B4996385 : Blo 2219435 4996385 := bstep (se 2 (by rfl) ⟨1873644, by rfl⟩ : syracuseStep 4996385 = 3747289) B3747289
theorem B3330923 : Blo 2219435 3330923 := bstep (se 1 (by rfl) ⟨2498192, by rfl⟩ : syracuseStep 3330923 = 4996385) B4996385
theorem B2220615 : Blo 2219435 2220615 := bstep (se 1 (by rfl) ⟨1665461, by rfl⟩ : syracuseStep 2220615 = 3330923) B3330923
theorem B2498197 : Blo 2219435 2498197 := bbase (se 6 (by rfl) ⟨58551, by rfl⟩ : syracuseStep 2498197 = 117103) (by norm_num)
theorem B3330929 : Blo 2219435 3330929 := bstep (se 2 (by rfl) ⟨1249098, by rfl⟩ : syracuseStep 3330929 = 2498197) B2498197
theorem B2220619 : Blo 2219435 2220619 := bstep (se 1 (by rfl) ⟨1665464, by rfl⟩ : syracuseStep 2220619 = 3330929) B3330929
theorem B2810477 : Blo 2219435 2810477 := bbase (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) (by norm_num)
theorem B7494605 : Blo 2219435 7494605 := bstep (se 3 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 7494605 = 2810477) B2810477
theorem B4996403 : Blo 2219435 4996403 := bstep (se 1 (by rfl) ⟨3747302, by rfl⟩ : syracuseStep 4996403 = 7494605) B7494605
theorem B3330935 : Blo 2219435 3330935 := bstep (se 1 (by rfl) ⟨2498201, by rfl⟩ : syracuseStep 3330935 = 4996403) B4996403
theorem B2220623 : Blo 2219435 2220623 := bstep (se 1 (by rfl) ⟨1665467, by rfl⟩ : syracuseStep 2220623 = 3330935) B3330935
theorem B3330941 : Blo 2219435 3330941 := bbase (se 3 (by rfl) ⟨624551, by rfl⟩ : syracuseStep 3330941 = 1249103) (by norm_num)
theorem B2220627 : Blo 2219435 2220627 := bstep (se 1 (by rfl) ⟨1665470, by rfl⟩ : syracuseStep 2220627 = 3330941) B3330941
theorem B4996421 : Blo 2219435 4996421 := bbase (se 4 (by rfl) ⟨468414, by rfl⟩ : syracuseStep 4996421 = 936829) (by norm_num)
theorem B3330947 : Blo 2219435 3330947 := bstep (se 1 (by rfl) ⟨2498210, by rfl⟩ : syracuseStep 3330947 = 4996421) B4996421
theorem B2220631 : Blo 2219435 2220631 := bstep (se 1 (by rfl) ⟨1665473, by rfl⟩ : syracuseStep 2220631 = 3330947) B3330947
theorem B2667773 : Blo 2219435 2667773 := bbase (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) (by norm_num)
theorem B7114061 : Blo 2219435 7114061 := bstep (se 3 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 7114061 = 2667773) B2667773
theorem B4742707 : Blo 2219435 4742707 := bstep (se 1 (by rfl) ⟨3557030, by rfl⟩ : syracuseStep 4742707 = 7114061) B7114061
theorem B6323609 : Blo 2219435 6323609 := bstep (se 2 (by rfl) ⟨2371353, by rfl⟩ : syracuseStep 6323609 = 4742707) B4742707
theorem B4215739 : Blo 2219435 4215739 := bstep (se 1 (by rfl) ⟨3161804, by rfl⟩ : syracuseStep 4215739 = 6323609) B6323609
theorem B5620985 : Blo 2219435 5620985 := bstep (se 2 (by rfl) ⟨2107869, by rfl⟩ : syracuseStep 5620985 = 4215739) B4215739
theorem B3747323 : Blo 2219435 3747323 := bstep (se 1 (by rfl) ⟨2810492, by rfl⟩ : syracuseStep 3747323 = 5620985) B5620985
theorem B2498215 : Blo 2219435 2498215 := bstep (se 1 (by rfl) ⟨1873661, by rfl⟩ : syracuseStep 2498215 = 3747323) B3747323
theorem B3330953 : Blo 2219435 3330953 := bstep (se 2 (by rfl) ⟨1249107, by rfl⟩ : syracuseStep 3330953 = 2498215) B2498215
theorem B2220635 : Blo 2219435 2220635 := bstep (se 1 (by rfl) ⟨1665476, by rfl⟩ : syracuseStep 2220635 = 3330953) B3330953
theorem B11241989 : Blo 2219435 11241989 := bbase (se 4 (by rfl) ⟨1053936, by rfl⟩ : syracuseStep 11241989 = 2107873) (by norm_num)
theorem B7494659 : Blo 2219435 7494659 := bstep (se 1 (by rfl) ⟨5620994, by rfl⟩ : syracuseStep 7494659 = 11241989) B11241989
theorem B4996439 : Blo 2219435 4996439 := bstep (se 1 (by rfl) ⟨3747329, by rfl⟩ : syracuseStep 4996439 = 7494659) B7494659
theorem B3330959 : Blo 2219435 3330959 := bstep (se 1 (by rfl) ⟨2498219, by rfl⟩ : syracuseStep 3330959 = 4996439) B4996439
theorem B2220639 : Blo 2219435 2220639 := bstep (se 1 (by rfl) ⟨1665479, by rfl⟩ : syracuseStep 2220639 = 3330959) B3330959
theorem B3330965 : Blo 2219435 3330965 := bbase (se 6 (by rfl) ⟨78069, by rfl⟩ : syracuseStep 3330965 = 156139) (by norm_num)
theorem B2220643 : Blo 2219435 2220643 := bstep (se 1 (by rfl) ⟨1665482, by rfl⟩ : syracuseStep 2220643 = 3330965) B3330965
theorem B12647285 : Blo 2219435 12647285 := bbase (se 5 (by rfl) ⟨592841, by rfl⟩ : syracuseStep 12647285 = 1185683) (by norm_num)
theorem B8431523 : Blo 2219435 8431523 := bstep (se 1 (by rfl) ⟨6323642, by rfl⟩ : syracuseStep 8431523 = 12647285) B12647285
theorem B5621015 : Blo 2219435 5621015 := bstep (se 1 (by rfl) ⟨4215761, by rfl⟩ : syracuseStep 5621015 = 8431523) B8431523
theorem B3747343 : Blo 2219435 3747343 := bstep (se 1 (by rfl) ⟨2810507, by rfl⟩ : syracuseStep 3747343 = 5621015) B5621015
theorem B4996457 : Blo 2219435 4996457 := bstep (se 2 (by rfl) ⟨1873671, by rfl⟩ : syracuseStep 4996457 = 3747343) B3747343
theorem B3330971 : Blo 2219435 3330971 := bstep (se 1 (by rfl) ⟨2498228, by rfl⟩ : syracuseStep 3330971 = 4996457) B4996457
theorem B2220647 : Blo 2219435 2220647 := bstep (se 1 (by rfl) ⟨1665485, by rfl⟩ : syracuseStep 2220647 = 3330971) B3330971
theorem B2498233 : Blo 2219435 2498233 := bbase (se 2 (by rfl) ⟨936837, by rfl⟩ : syracuseStep 2498233 = 1873675) (by norm_num)
theorem B3330977 : Blo 2219435 3330977 := bstep (se 2 (by rfl) ⟨1249116, by rfl⟩ : syracuseStep 3330977 = 2498233) B2498233
theorem B2220651 : Blo 2219435 2220651 := bstep (se 1 (by rfl) ⟨1665488, by rfl⟩ : syracuseStep 2220651 = 3330977) B3330977
theorem B4742749 : Blo 2219435 4742749 := bbase (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) (by norm_num)
theorem B6323665 : Blo 2219435 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B8431553 : Blo 2219435 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B5621035 : Blo 2219435 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B7494713 : Blo 2219435 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B4996475 : Blo 2219435 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B3330983 : Blo 2219435 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B2220655 : Blo 2219435 2220655 := bstep (se 1 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 2220655 = 3330983) B3330983
theorem B3330989 : Blo 2219435 3330989 := bbase (se 3 (by rfl) ⟨624560, by rfl⟩ : syracuseStep 3330989 = 1249121) (by norm_num)
theorem B2220659 : Blo 2219435 2220659 := bstep (se 1 (by rfl) ⟨1665494, by rfl⟩ : syracuseStep 2220659 = 3330989) B3330989
theorem B4996493 : Blo 2219435 4996493 := bbase (se 3 (by rfl) ⟨936842, by rfl⟩ : syracuseStep 4996493 = 1873685) (by norm_num)
theorem B3330995 : Blo 2219435 3330995 := bstep (se 1 (by rfl) ⟨2498246, by rfl⟩ : syracuseStep 3330995 = 4996493) B4996493
theorem B2220663 : Blo 2219435 2220663 := bstep (se 1 (by rfl) ⟨1665497, by rfl⟩ : syracuseStep 2220663 = 3330995) B3330995
theorem B2810533 : Blo 2219435 2810533 := bbase (se 4 (by rfl) ⟨263487, by rfl⟩ : syracuseStep 2810533 = 526975) (by norm_num)
theorem B3747377 : Blo 2219435 3747377 := bstep (se 2 (by rfl) ⟨1405266, by rfl⟩ : syracuseStep 3747377 = 2810533) B2810533
theorem B2498251 : Blo 2219435 2498251 := bstep (se 1 (by rfl) ⟨1873688, by rfl⟩ : syracuseStep 2498251 = 3747377) B3747377
theorem B3331001 : Blo 2219435 3331001 := bstep (se 2 (by rfl) ⟨1249125, by rfl⟩ : syracuseStep 3331001 = 2498251) B2498251
theorem B2220667 : Blo 2219435 2220667 := bstep (se 1 (by rfl) ⟨1665500, by rfl⟩ : syracuseStep 2220667 = 3331001) B3331001
theorem B36015509 : Blo 2219435 36015509 := bbase (se 6 (by rfl) ⟨844113, by rfl⟩ : syracuseStep 36015509 = 1688227) (by norm_num)
theorem B24010339 : Blo 2219435 24010339 := bstep (se 1 (by rfl) ⟨18007754, by rfl⟩ : syracuseStep 24010339 = 36015509) B36015509
theorem B32013785 : Blo 2219435 32013785 := bstep (se 2 (by rfl) ⟨12005169, by rfl⟩ : syracuseStep 32013785 = 24010339) B24010339
theorem B21342523 : Blo 2219435 21342523 := bstep (se 1 (by rfl) ⟨16006892, by rfl⟩ : syracuseStep 21342523 = 32013785) B32013785
theorem B28456697 : Blo 2219435 28456697 := bstep (se 2 (by rfl) ⟨10671261, by rfl⟩ : syracuseStep 28456697 = 21342523) B21342523
theorem B18971131 : Blo 2219435 18971131 := bstep (se 1 (by rfl) ⟨14228348, by rfl⟩ : syracuseStep 18971131 = 28456697) B28456697
theorem B25294841 : Blo 2219435 25294841 := bstep (se 2 (by rfl) ⟨9485565, by rfl⟩ : syracuseStep 25294841 = 18971131) B18971131
theorem B16863227 : Blo 2219435 16863227 := bstep (se 1 (by rfl) ⟨12647420, by rfl⟩ : syracuseStep 16863227 = 25294841) B25294841
theorem B11242151 : Blo 2219435 11242151 := bstep (se 1 (by rfl) ⟨8431613, by rfl⟩ : syracuseStep 11242151 = 16863227) B16863227
theorem B7494767 : Blo 2219435 7494767 := bstep (se 1 (by rfl) ⟨5621075, by rfl⟩ : syracuseStep 7494767 = 11242151) B11242151
theorem B4996511 : Blo 2219435 4996511 := bstep (se 1 (by rfl) ⟨3747383, by rfl⟩ : syracuseStep 4996511 = 7494767) B7494767
theorem B3331007 : Blo 2219435 3331007 := bstep (se 1 (by rfl) ⟨2498255, by rfl⟩ : syracuseStep 3331007 = 4996511) B4996511
theorem B2220671 : Blo 2219435 2220671 := bstep (se 1 (by rfl) ⟨1665503, by rfl⟩ : syracuseStep 2220671 = 3331007) B3331007
theorem B3331013 : Blo 2219435 3331013 := bbase (se 4 (by rfl) ⟨312282, by rfl⟩ : syracuseStep 3331013 = 624565) (by norm_num)
theorem B2220675 : Blo 2219435 2220675 := bstep (se 1 (by rfl) ⟨1665506, by rfl⟩ : syracuseStep 2220675 = 3331013) B3331013
theorem B3747397 : Blo 2219435 3747397 := bbase (se 4 (by rfl) ⟨351318, by rfl⟩ : syracuseStep 3747397 = 702637) (by norm_num)
theorem B4996529 : Blo 2219435 4996529 := bstep (se 2 (by rfl) ⟨1873698, by rfl⟩ : syracuseStep 4996529 = 3747397) B3747397
theorem B3331019 : Blo 2219435 3331019 := bstep (se 1 (by rfl) ⟨2498264, by rfl⟩ : syracuseStep 3331019 = 4996529) B4996529
theorem B2220679 : Blo 2219435 2220679 := bstep (se 1 (by rfl) ⟨1665509, by rfl⟩ : syracuseStep 2220679 = 3331019) B3331019
theorem B2498269 : Blo 2219435 2498269 := bbase (se 3 (by rfl) ⟨468425, by rfl⟩ : syracuseStep 2498269 = 936851) (by norm_num)
theorem B3331025 : Blo 2219435 3331025 := bstep (se 2 (by rfl) ⟨1249134, by rfl⟩ : syracuseStep 3331025 = 2498269) B2498269
theorem B2220683 : Blo 2219435 2220683 := bstep (se 1 (by rfl) ⟨1665512, by rfl⟩ : syracuseStep 2220683 = 3331025) B3331025
theorem B7494821 : Blo 2219435 7494821 := bbase (se 4 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 7494821 = 1405279) (by norm_num)
theorem B4996547 : Blo 2219435 4996547 := bstep (se 1 (by rfl) ⟨3747410, by rfl⟩ : syracuseStep 4996547 = 7494821) B7494821
theorem B3331031 : Blo 2219435 3331031 := bstep (se 1 (by rfl) ⟨2498273, by rfl⟩ : syracuseStep 3331031 = 4996547) B4996547
theorem B2220687 : Blo 2219435 2220687 := bstep (se 1 (by rfl) ⟨1665515, by rfl⟩ : syracuseStep 2220687 = 3331031) B3331031
theorem B3331037 : Blo 2219435 3331037 := bbase (se 3 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 3331037 = 1249139) (by norm_num)
theorem B2220691 : Blo 2219435 2220691 := bstep (se 1 (by rfl) ⟨1665518, by rfl⟩ : syracuseStep 2220691 = 3331037) B3331037
theorem B4996565 : Blo 2219435 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B3331043 : Blo 2219435 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B2220695 : Blo 2219435 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B4501997 : Blo 2219435 4501997 := bbase (se 3 (by rfl) ⟨844124, by rfl⟩ : syracuseStep 4501997 = 1688249) (by norm_num)
theorem B3001331 : Blo 2219435 3001331 := bstep (se 1 (by rfl) ⟨2250998, by rfl⟩ : syracuseStep 3001331 = 4501997) B4501997
theorem B8003549 : Blo 2219435 8003549 := bstep (se 3 (by rfl) ⟨1500665, by rfl⟩ : syracuseStep 8003549 = 3001331) B3001331
theorem B21342797 : Blo 2219435 21342797 := bstep (se 3 (by rfl) ⟨4001774, by rfl⟩ : syracuseStep 21342797 = 8003549) B8003549
theorem B14228531 : Blo 2219435 14228531 := bstep (se 1 (by rfl) ⟨10671398, by rfl⟩ : syracuseStep 14228531 = 21342797) B21342797
theorem B9485687 : Blo 2219435 9485687 := bstep (se 1 (by rfl) ⟨7114265, by rfl⟩ : syracuseStep 9485687 = 14228531) B14228531
theorem B6323791 : Blo 2219435 6323791 := bstep (se 1 (by rfl) ⟨4742843, by rfl⟩ : syracuseStep 6323791 = 9485687) B9485687
theorem B8431721 : Blo 2219435 8431721 := bstep (se 2 (by rfl) ⟨3161895, by rfl⟩ : syracuseStep 8431721 = 6323791) B6323791
theorem B5621147 : Blo 2219435 5621147 := bstep (se 1 (by rfl) ⟨4215860, by rfl⟩ : syracuseStep 5621147 = 8431721) B8431721
theorem B3747431 : Blo 2219435 3747431 := bstep (se 1 (by rfl) ⟨2810573, by rfl⟩ : syracuseStep 3747431 = 5621147) B5621147
theorem B2498287 : Blo 2219435 2498287 := bstep (se 1 (by rfl) ⟨1873715, by rfl⟩ : syracuseStep 2498287 = 3747431) B3747431
theorem B3331049 : Blo 2219435 3331049 := bstep (se 2 (by rfl) ⟨1249143, by rfl⟩ : syracuseStep 3331049 = 2498287) B2498287
theorem B2220699 : Blo 2219435 2220699 := bstep (se 1 (by rfl) ⟨1665524, by rfl⟩ : syracuseStep 2220699 = 3331049) B3331049
theorem B7114277 : Blo 2219435 7114277 := bbase (se 4 (by rfl) ⟨666963, by rfl⟩ : syracuseStep 7114277 = 1333927) (by norm_num)
theorem B18971405 : Blo 2219435 18971405 := bstep (se 3 (by rfl) ⟨3557138, by rfl⟩ : syracuseStep 18971405 = 7114277) B7114277
theorem B12647603 : Blo 2219435 12647603 := bstep (se 1 (by rfl) ⟨9485702, by rfl⟩ : syracuseStep 12647603 = 18971405) B18971405
theorem B8431735 : Blo 2219435 8431735 := bstep (se 1 (by rfl) ⟨6323801, by rfl⟩ : syracuseStep 8431735 = 12647603) B12647603
theorem B11242313 : Blo 2219435 11242313 := bstep (se 2 (by rfl) ⟨4215867, by rfl⟩ : syracuseStep 11242313 = 8431735) B8431735
theorem B7494875 : Blo 2219435 7494875 := bstep (se 1 (by rfl) ⟨5621156, by rfl⟩ : syracuseStep 7494875 = 11242313) B11242313
theorem B4996583 : Blo 2219435 4996583 := bstep (se 1 (by rfl) ⟨3747437, by rfl⟩ : syracuseStep 4996583 = 7494875) B7494875
theorem B3331055 : Blo 2219435 3331055 := bstep (se 1 (by rfl) ⟨2498291, by rfl⟩ : syracuseStep 3331055 = 4996583) B4996583
theorem B2220703 : Blo 2219435 2220703 := bstep (se 1 (by rfl) ⟨1665527, by rfl⟩ : syracuseStep 2220703 = 3331055) B3331055
theorem B3331061 : Blo 2219435 3331061 := bbase (se 5 (by rfl) ⟨156143, by rfl⟩ : syracuseStep 3331061 = 312287) (by norm_num)
theorem B2220707 : Blo 2219435 2220707 := bstep (se 1 (by rfl) ⟨1665530, by rfl⟩ : syracuseStep 2220707 = 3331061) B3331061
theorem B4742869 : Blo 2219435 4742869 := bbase (se 7 (by rfl) ⟨55580, by rfl⟩ : syracuseStep 4742869 = 111161) (by norm_num)
theorem B6323825 : Blo 2219435 6323825 := bstep (se 2 (by rfl) ⟨2371434, by rfl⟩ : syracuseStep 6323825 = 4742869) B4742869
theorem B4215883 : Blo 2219435 4215883 := bstep (se 1 (by rfl) ⟨3161912, by rfl⟩ : syracuseStep 4215883 = 6323825) B6323825
theorem B5621177 : Blo 2219435 5621177 := bstep (se 2 (by rfl) ⟨2107941, by rfl⟩ : syracuseStep 5621177 = 4215883) B4215883
theorem B3747451 : Blo 2219435 3747451 := bstep (se 1 (by rfl) ⟨2810588, by rfl⟩ : syracuseStep 3747451 = 5621177) B5621177
theorem B4996601 : Blo 2219435 4996601 := bstep (se 2 (by rfl) ⟨1873725, by rfl⟩ : syracuseStep 4996601 = 3747451) B3747451
theorem B3331067 : Blo 2219435 3331067 := bstep (se 1 (by rfl) ⟨2498300, by rfl⟩ : syracuseStep 3331067 = 4996601) B4996601
theorem B2220711 : Blo 2219435 2220711 := bstep (se 1 (by rfl) ⟨1665533, by rfl⟩ : syracuseStep 2220711 = 3331067) B3331067
theorem B2498305 : Blo 2219435 2498305 := bbase (se 2 (by rfl) ⟨936864, by rfl⟩ : syracuseStep 2498305 = 1873729) (by norm_num)
theorem B3331073 : Blo 2219435 3331073 := bstep (se 2 (by rfl) ⟨1249152, by rfl⟩ : syracuseStep 3331073 = 2498305) B2498305
theorem B2220715 : Blo 2219435 2220715 := bstep (se 1 (by rfl) ⟨1665536, by rfl⟩ : syracuseStep 2220715 = 3331073) B3331073
theorem B5621197 : Blo 2219435 5621197 := bbase (se 3 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 5621197 = 2107949) (by norm_num)
theorem B7494929 : Blo 2219435 7494929 := bstep (se 2 (by rfl) ⟨2810598, by rfl⟩ : syracuseStep 7494929 = 5621197) B5621197
theorem B4996619 : Blo 2219435 4996619 := bstep (se 1 (by rfl) ⟨3747464, by rfl⟩ : syracuseStep 4996619 = 7494929) B7494929
theorem B3331079 : Blo 2219435 3331079 := bstep (se 1 (by rfl) ⟨2498309, by rfl⟩ : syracuseStep 3331079 = 4996619) B4996619
theorem B2220719 : Blo 2219435 2220719 := bstep (se 1 (by rfl) ⟨1665539, by rfl⟩ : syracuseStep 2220719 = 3331079) B3331079
theorem B3331085 : Blo 2219435 3331085 := bbase (se 3 (by rfl) ⟨624578, by rfl⟩ : syracuseStep 3331085 = 1249157) (by norm_num)
theorem B2220723 : Blo 2219435 2220723 := bstep (se 1 (by rfl) ⟨1665542, by rfl⟩ : syracuseStep 2220723 = 3331085) B3331085
theorem B4996637 : Blo 2219435 4996637 := bbase (se 3 (by rfl) ⟨936869, by rfl⟩ : syracuseStep 4996637 = 1873739) (by norm_num)
theorem B3331091 : Blo 2219435 3331091 := bstep (se 1 (by rfl) ⟨2498318, by rfl⟩ : syracuseStep 3331091 = 4996637) B4996637
theorem B2220727 : Blo 2219435 2220727 := bstep (se 1 (by rfl) ⟨1665545, by rfl⟩ : syracuseStep 2220727 = 3331091) B3331091
theorem B3747485 : Blo 2219435 3747485 := bbase (se 3 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 3747485 = 1405307) (by norm_num)
theorem B2498323 : Blo 2219435 2498323 := bstep (se 1 (by rfl) ⟨1873742, by rfl⟩ : syracuseStep 2498323 = 3747485) B3747485
theorem B3331097 : Blo 2219435 3331097 := bstep (se 2 (by rfl) ⟨1249161, by rfl⟩ : syracuseStep 3331097 = 2498323) B2498323
theorem B2220731 : Blo 2219435 2220731 := bstep (se 1 (by rfl) ⟨1665548, by rfl⟩ : syracuseStep 2220731 = 3331097) B3331097
theorem B4502069 : Blo 2219435 4502069 := bbase (se 5 (by rfl) ⟨211034, by rfl⟩ : syracuseStep 4502069 = 422069) (by norm_num)
theorem B3001379 : Blo 2219435 3001379 := bstep (se 1 (by rfl) ⟨2251034, by rfl⟩ : syracuseStep 3001379 = 4502069) B4502069
theorem B32014709 : Blo 2219435 32014709 := bstep (se 5 (by rfl) ⟨1500689, by rfl⟩ : syracuseStep 32014709 = 3001379) B3001379
theorem B21343139 : Blo 2219435 21343139 := bstep (se 1 (by rfl) ⟨16007354, by rfl⟩ : syracuseStep 21343139 = 32014709) B32014709
theorem B14228759 : Blo 2219435 14228759 := bstep (se 1 (by rfl) ⟨10671569, by rfl⟩ : syracuseStep 14228759 = 21343139) B21343139
theorem B9485839 : Blo 2219435 9485839 := bstep (se 1 (by rfl) ⟨7114379, by rfl⟩ : syracuseStep 9485839 = 14228759) B14228759
theorem B12647785 : Blo 2219435 12647785 := bstep (se 2 (by rfl) ⟨4742919, by rfl⟩ : syracuseStep 12647785 = 9485839) B9485839
theorem B16863713 : Blo 2219435 16863713 := bstep (se 2 (by rfl) ⟨6323892, by rfl⟩ : syracuseStep 16863713 = 12647785) B12647785
theorem B11242475 : Blo 2219435 11242475 := bstep (se 1 (by rfl) ⟨8431856, by rfl⟩ : syracuseStep 11242475 = 16863713) B16863713
theorem B7494983 : Blo 2219435 7494983 := bstep (se 1 (by rfl) ⟨5621237, by rfl⟩ : syracuseStep 7494983 = 11242475) B11242475
theorem B4996655 : Blo 2219435 4996655 := bstep (se 1 (by rfl) ⟨3747491, by rfl⟩ : syracuseStep 4996655 = 7494983) B7494983
theorem B3331103 : Blo 2219435 3331103 := bstep (se 1 (by rfl) ⟨2498327, by rfl⟩ : syracuseStep 3331103 = 4996655) B4996655
theorem B2220735 : Blo 2219435 2220735 := bstep (se 1 (by rfl) ⟨1665551, by rfl⟩ : syracuseStep 2220735 = 3331103) B3331103
theorem B3331109 : Blo 2219435 3331109 := bbase (se 4 (by rfl) ⟨312291, by rfl⟩ : syracuseStep 3331109 = 624583) (by norm_num)
theorem B2220739 : Blo 2219435 2220739 := bstep (se 1 (by rfl) ⟨1665554, by rfl⟩ : syracuseStep 2220739 = 3331109) B3331109
theorem B2810629 : Blo 2219435 2810629 := bbase (se 4 (by rfl) ⟨263496, by rfl⟩ : syracuseStep 2810629 = 526993) (by norm_num)
theorem B3747505 : Blo 2219435 3747505 := bstep (se 2 (by rfl) ⟨1405314, by rfl⟩ : syracuseStep 3747505 = 2810629) B2810629
theorem B4996673 : Blo 2219435 4996673 := bstep (se 2 (by rfl) ⟨1873752, by rfl⟩ : syracuseStep 4996673 = 3747505) B3747505
theorem B3331115 : Blo 2219435 3331115 := bstep (se 1 (by rfl) ⟨2498336, by rfl⟩ : syracuseStep 3331115 = 4996673) B4996673
theorem B2220743 : Blo 2219435 2220743 := bstep (se 1 (by rfl) ⟨1665557, by rfl⟩ : syracuseStep 2220743 = 3331115) B3331115
theorem B2498341 : Blo 2219435 2498341 := bbase (se 4 (by rfl) ⟨234219, by rfl⟩ : syracuseStep 2498341 = 468439) (by norm_num)
theorem B3331121 : Blo 2219435 3331121 := bstep (se 2 (by rfl) ⟨1249170, by rfl⟩ : syracuseStep 3331121 = 2498341) B2498341
theorem B2220747 : Blo 2219435 2220747 := bstep (se 1 (by rfl) ⟨1665560, by rfl⟩ : syracuseStep 2220747 = 3331121) B3331121
theorem B9485909 : Blo 2219435 9485909 := bbase (se 8 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 9485909 = 111163) (by norm_num)
theorem B6323939 : Blo 2219435 6323939 := bstep (se 1 (by rfl) ⟨4742954, by rfl⟩ : syracuseStep 6323939 = 9485909) B9485909
theorem B4215959 : Blo 2219435 4215959 := bstep (se 1 (by rfl) ⟨3161969, by rfl⟩ : syracuseStep 4215959 = 6323939) B6323939
theorem B2810639 : Blo 2219435 2810639 := bstep (se 1 (by rfl) ⟨2107979, by rfl⟩ : syracuseStep 2810639 = 4215959) B4215959
theorem B7495037 : Blo 2219435 7495037 := bstep (se 3 (by rfl) ⟨1405319, by rfl⟩ : syracuseStep 7495037 = 2810639) B2810639
theorem B4996691 : Blo 2219435 4996691 := bstep (se 1 (by rfl) ⟨3747518, by rfl⟩ : syracuseStep 4996691 = 7495037) B7495037
theorem B3331127 : Blo 2219435 3331127 := bstep (se 1 (by rfl) ⟨2498345, by rfl⟩ : syracuseStep 3331127 = 4996691) B4996691
theorem B2220751 : Blo 2219435 2220751 := bstep (se 1 (by rfl) ⟨1665563, by rfl⟩ : syracuseStep 2220751 = 3331127) B3331127
theorem B3331133 : Blo 2219435 3331133 := bbase (se 3 (by rfl) ⟨624587, by rfl⟩ : syracuseStep 3331133 = 1249175) (by norm_num)
theorem B2220755 : Blo 2219435 2220755 := bstep (se 1 (by rfl) ⟨1665566, by rfl⟩ : syracuseStep 2220755 = 3331133) B3331133
theorem B4996709 : Blo 2219435 4996709 := bbase (se 4 (by rfl) ⟨468441, by rfl⟩ : syracuseStep 4996709 = 936883) (by norm_num)
theorem B3331139 : Blo 2219435 3331139 := bstep (se 1 (by rfl) ⟨2498354, by rfl⟩ : syracuseStep 3331139 = 4996709) B4996709
theorem B2220759 : Blo 2219435 2220759 := bstep (se 1 (by rfl) ⟨1665569, by rfl⟩ : syracuseStep 2220759 = 3331139) B3331139
theorem B5621309 : Blo 2219435 5621309 := bbase (se 3 (by rfl) ⟨1053995, by rfl⟩ : syracuseStep 5621309 = 2107991) (by norm_num)
theorem B3747539 : Blo 2219435 3747539 := bstep (se 1 (by rfl) ⟨2810654, by rfl⟩ : syracuseStep 3747539 = 5621309) B5621309
theorem B2498359 : Blo 2219435 2498359 := bstep (se 1 (by rfl) ⟨1873769, by rfl⟩ : syracuseStep 2498359 = 3747539) B3747539
theorem B3331145 : Blo 2219435 3331145 := bstep (se 2 (by rfl) ⟨1249179, by rfl⟩ : syracuseStep 3331145 = 2498359) B2498359
theorem B2220763 : Blo 2219435 2220763 := bstep (se 1 (by rfl) ⟨1665572, by rfl⟩ : syracuseStep 2220763 = 3331145) B3331145
theorem B4215989 : Blo 2219435 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B11242637 : Blo 2219435 11242637 := bstep (se 3 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 11242637 = 4215989) B4215989
theorem B7495091 : Blo 2219435 7495091 := bstep (se 1 (by rfl) ⟨5621318, by rfl⟩ : syracuseStep 7495091 = 11242637) B11242637
theorem B4996727 : Blo 2219435 4996727 := bstep (se 1 (by rfl) ⟨3747545, by rfl⟩ : syracuseStep 4996727 = 7495091) B7495091
theorem B3331151 : Blo 2219435 3331151 := bstep (se 1 (by rfl) ⟨2498363, by rfl⟩ : syracuseStep 3331151 = 4996727) B4996727
theorem B2220767 : Blo 2219435 2220767 := bstep (se 1 (by rfl) ⟨1665575, by rfl⟩ : syracuseStep 2220767 = 3331151) B3331151
theorem B3331157 : Blo 2219435 3331157 := bbase (se 8 (by rfl) ⟨19518, by rfl⟩ : syracuseStep 3331157 = 39037) (by norm_num)
theorem B2220771 : Blo 2219435 2220771 := bstep (se 1 (by rfl) ⟨1665578, by rfl⟩ : syracuseStep 2220771 = 3331157) B3331157
theorem B3376613 : Blo 2219435 3376613 := bbase (se 4 (by rfl) ⟨316557, by rfl⟩ : syracuseStep 3376613 = 633115) (by norm_num)
theorem B9004301 : Blo 2219435 9004301 := bstep (se 3 (by rfl) ⟨1688306, by rfl⟩ : syracuseStep 9004301 = 3376613) B3376613
theorem B6002867 : Blo 2219435 6002867 := bstep (se 1 (by rfl) ⟨4502150, by rfl⟩ : syracuseStep 6002867 = 9004301) B9004301
theorem B16007645 : Blo 2219435 16007645 := bstep (se 3 (by rfl) ⟨3001433, by rfl⟩ : syracuseStep 16007645 = 6002867) B6002867
theorem B10671763 : Blo 2219435 10671763 := bstep (se 1 (by rfl) ⟨8003822, by rfl⟩ : syracuseStep 10671763 = 16007645) B16007645
theorem B14229017 : Blo 2219435 14229017 := bstep (se 2 (by rfl) ⟨5335881, by rfl⟩ : syracuseStep 14229017 = 10671763) B10671763
theorem B9486011 : Blo 2219435 9486011 := bstep (se 1 (by rfl) ⟨7114508, by rfl⟩ : syracuseStep 9486011 = 14229017) B14229017
theorem B6324007 : Blo 2219435 6324007 := bstep (se 1 (by rfl) ⟨4743005, by rfl⟩ : syracuseStep 6324007 = 9486011) B9486011
theorem B8432009 : Blo 2219435 8432009 := bstep (se 2 (by rfl) ⟨3162003, by rfl⟩ : syracuseStep 8432009 = 6324007) B6324007
theorem B5621339 : Blo 2219435 5621339 := bstep (se 1 (by rfl) ⟨4216004, by rfl⟩ : syracuseStep 5621339 = 8432009) B8432009
theorem B3747559 : Blo 2219435 3747559 := bstep (se 1 (by rfl) ⟨2810669, by rfl⟩ : syracuseStep 3747559 = 5621339) B5621339
theorem B4996745 : Blo 2219435 4996745 := bstep (se 2 (by rfl) ⟨1873779, by rfl⟩ : syracuseStep 4996745 = 3747559) B3747559
theorem B3331163 : Blo 2219435 3331163 := bstep (se 1 (by rfl) ⟨2498372, by rfl⟩ : syracuseStep 3331163 = 4996745) B4996745
theorem B2220775 : Blo 2219435 2220775 := bstep (se 1 (by rfl) ⟨1665581, by rfl⟩ : syracuseStep 2220775 = 3331163) B3331163
theorem B2498377 : Blo 2219435 2498377 := bbase (se 2 (by rfl) ⟨936891, by rfl⟩ : syracuseStep 2498377 = 1873783) (by norm_num)
theorem B3331169 : Blo 2219435 3331169 := bstep (se 2 (by rfl) ⟨1249188, by rfl⟩ : syracuseStep 3331169 = 2498377) B2498377
theorem B2220779 : Blo 2219435 2220779 := bstep (se 1 (by rfl) ⟨1665584, by rfl⟩ : syracuseStep 2220779 = 3331169) B3331169
theorem B16007701 : Blo 2219435 16007701 := bbase (se 6 (by rfl) ⟨375180, by rfl⟩ : syracuseStep 16007701 = 750361) (by norm_num)
theorem B21343601 : Blo 2219435 21343601 := bstep (se 2 (by rfl) ⟨8003850, by rfl⟩ : syracuseStep 21343601 = 16007701) B16007701
theorem B14229067 : Blo 2219435 14229067 := bstep (se 1 (by rfl) ⟨10671800, by rfl⟩ : syracuseStep 14229067 = 21343601) B21343601
theorem B18972089 : Blo 2219435 18972089 := bstep (se 2 (by rfl) ⟨7114533, by rfl⟩ : syracuseStep 18972089 = 14229067) B14229067
theorem B12648059 : Blo 2219435 12648059 := bstep (se 1 (by rfl) ⟨9486044, by rfl⟩ : syracuseStep 12648059 = 18972089) B18972089
theorem B8432039 : Blo 2219435 8432039 := bstep (se 1 (by rfl) ⟨6324029, by rfl⟩ : syracuseStep 8432039 = 12648059) B12648059
theorem B5621359 : Blo 2219435 5621359 := bstep (se 1 (by rfl) ⟨4216019, by rfl⟩ : syracuseStep 5621359 = 8432039) B8432039
theorem B7495145 : Blo 2219435 7495145 := bstep (se 2 (by rfl) ⟨2810679, by rfl⟩ : syracuseStep 7495145 = 5621359) B5621359
theorem B4996763 : Blo 2219435 4996763 := bstep (se 1 (by rfl) ⟨3747572, by rfl⟩ : syracuseStep 4996763 = 7495145) B7495145
theorem B3331175 : Blo 2219435 3331175 := bstep (se 1 (by rfl) ⟨2498381, by rfl⟩ : syracuseStep 3331175 = 4996763) B4996763
theorem B2220783 : Blo 2219435 2220783 := bstep (se 1 (by rfl) ⟨1665587, by rfl⟩ : syracuseStep 2220783 = 3331175) B3331175
theorem B3331181 : Blo 2219435 3331181 := bbase (se 3 (by rfl) ⟨624596, by rfl⟩ : syracuseStep 3331181 = 1249193) (by norm_num)
theorem B2220787 : Blo 2219435 2220787 := bstep (se 1 (by rfl) ⟨1665590, by rfl⟩ : syracuseStep 2220787 = 3331181) B3331181
theorem B4996781 : Blo 2219435 4996781 := bbase (se 3 (by rfl) ⟨936896, by rfl⟩ : syracuseStep 4996781 = 1873793) (by norm_num)
theorem B3331187 : Blo 2219435 3331187 := bstep (se 1 (by rfl) ⟨2498390, by rfl⟩ : syracuseStep 3331187 = 4996781) B4996781
theorem B2220791 : Blo 2219435 2220791 := bstep (se 1 (by rfl) ⟨1665593, by rfl⟩ : syracuseStep 2220791 = 3331187) B3331187
theorem B6497813 : Blo 2219435 6497813 := bbase (se 6 (by rfl) ⟨152292, by rfl⟩ : syracuseStep 6497813 = 304585) (by norm_num)
theorem B4331875 : Blo 2219435 4331875 := bstep (se 1 (by rfl) ⟨3248906, by rfl⟩ : syracuseStep 4331875 = 6497813) B6497813
theorem B5775833 : Blo 2219435 5775833 := bstep (se 2 (by rfl) ⟨2165937, by rfl⟩ : syracuseStep 5775833 = 4331875) B4331875
theorem B15402221 : Blo 2219435 15402221 := bstep (se 3 (by rfl) ⟨2887916, by rfl⟩ : syracuseStep 15402221 = 5775833) B5775833
theorem B10268147 : Blo 2219435 10268147 := bstep (se 1 (by rfl) ⟨7701110, by rfl⟩ : syracuseStep 10268147 = 15402221) B15402221
theorem B6845431 : Blo 2219435 6845431 := bstep (se 1 (by rfl) ⟨5134073, by rfl⟩ : syracuseStep 6845431 = 10268147) B10268147
theorem B9127241 : Blo 2219435 9127241 := bstep (se 2 (by rfl) ⟨3422715, by rfl⟩ : syracuseStep 9127241 = 6845431) B6845431
theorem B6084827 : Blo 2219435 6084827 := bstep (se 1 (by rfl) ⟨4563620, by rfl⟩ : syracuseStep 6084827 = 9127241) B9127241
theorem B4056551 : Blo 2219435 4056551 := bstep (se 1 (by rfl) ⟨3042413, by rfl⟩ : syracuseStep 4056551 = 6084827) B6084827
theorem B2704367 : Blo 2219435 2704367 := bstep (se 1 (by rfl) ⟨2028275, by rfl⟩ : syracuseStep 2704367 = 4056551) B4056551
theorem B7211645 : Blo 2219435 7211645 := bstep (se 3 (by rfl) ⟨1352183, by rfl⟩ : syracuseStep 7211645 = 2704367) B2704367
theorem B4807763 : Blo 2219435 4807763 := bstep (se 1 (by rfl) ⟨3605822, by rfl⟩ : syracuseStep 4807763 = 7211645) B7211645
theorem B3205175 : Blo 2219435 3205175 := bstep (se 1 (by rfl) ⟨2403881, by rfl⟩ : syracuseStep 3205175 = 4807763) B4807763
theorem B8547133 : Blo 2219435 8547133 := bstep (se 3 (by rfl) ⟨1602587, by rfl⟩ : syracuseStep 8547133 = 3205175) B3205175
theorem B11396177 : Blo 2219435 11396177 := bstep (se 2 (by rfl) ⟨4273566, by rfl⟩ : syracuseStep 11396177 = 8547133) B8547133
theorem B7597451 : Blo 2219435 7597451 := bstep (se 1 (by rfl) ⟨5698088, by rfl⟩ : syracuseStep 7597451 = 11396177) B11396177
theorem B5064967 : Blo 2219435 5064967 := bstep (se 1 (by rfl) ⟨3798725, by rfl⟩ : syracuseStep 5064967 = 7597451) B7597451
theorem B6753289 : Blo 2219435 6753289 := bstep (se 2 (by rfl) ⟨2532483, by rfl⟩ : syracuseStep 6753289 = 5064967) B5064967
theorem B9004385 : Blo 2219435 9004385 := bstep (se 2 (by rfl) ⟨3376644, by rfl⟩ : syracuseStep 9004385 = 6753289) B6753289
theorem B6002923 : Blo 2219435 6002923 := bstep (se 1 (by rfl) ⟨4502192, by rfl⟩ : syracuseStep 6002923 = 9004385) B9004385
theorem B8003897 : Blo 2219435 8003897 := bstep (se 2 (by rfl) ⟨3001461, by rfl⟩ : syracuseStep 8003897 = 6002923) B6002923
theorem B5335931 : Blo 2219435 5335931 := bstep (se 1 (by rfl) ⟨4001948, by rfl⟩ : syracuseStep 5335931 = 8003897) B8003897
theorem B3557287 : Blo 2219435 3557287 := bstep (se 1 (by rfl) ⟨2667965, by rfl⟩ : syracuseStep 3557287 = 5335931) B5335931
theorem B4743049 : Blo 2219435 4743049 := bstep (se 2 (by rfl) ⟨1778643, by rfl⟩ : syracuseStep 4743049 = 3557287) B3557287
theorem B6324065 : Blo 2219435 6324065 := bstep (se 2 (by rfl) ⟨2371524, by rfl⟩ : syracuseStep 6324065 = 4743049) B4743049
theorem B4216043 : Blo 2219435 4216043 := bstep (se 1 (by rfl) ⟨3162032, by rfl⟩ : syracuseStep 4216043 = 6324065) B6324065
theorem B2810695 : Blo 2219435 2810695 := bstep (se 1 (by rfl) ⟨2108021, by rfl⟩ : syracuseStep 2810695 = 4216043) B4216043
theorem B3747593 : Blo 2219435 3747593 := bstep (se 2 (by rfl) ⟨1405347, by rfl⟩ : syracuseStep 3747593 = 2810695) B2810695
theorem B2498395 : Blo 2219435 2498395 := bstep (se 1 (by rfl) ⟨1873796, by rfl⟩ : syracuseStep 2498395 = 3747593) B3747593
theorem B3331193 : Blo 2219435 3331193 := bstep (se 2 (by rfl) ⟨1249197, by rfl⟩ : syracuseStep 3331193 = 2498395) B2498395
theorem B2220795 : Blo 2219435 2220795 := bstep (se 1 (by rfl) ⟨1665596, by rfl⟩ : syracuseStep 2220795 = 3331193) B3331193
theorem B5064973 : Blo 2219435 5064973 := bbase (se 3 (by rfl) ⟨949682, by rfl⟩ : syracuseStep 5064973 = 1899365) (by norm_num)
theorem B27013189 : Blo 2219435 27013189 := bstep (se 4 (by rfl) ⟨2532486, by rfl⟩ : syracuseStep 27013189 = 5064973) B5064973
theorem B36017585 : Blo 2219435 36017585 := bstep (se 2 (by rfl) ⟨13506594, by rfl⟩ : syracuseStep 36017585 = 27013189) B27013189
theorem B24011723 : Blo 2219435 24011723 := bstep (se 1 (by rfl) ⟨18008792, by rfl⟩ : syracuseStep 24011723 = 36017585) B36017585
theorem B16007815 : Blo 2219435 16007815 := bstep (se 1 (by rfl) ⟨12005861, by rfl⟩ : syracuseStep 16007815 = 24011723) B24011723
theorem B21343753 : Blo 2219435 21343753 := bstep (se 2 (by rfl) ⟨8003907, by rfl⟩ : syracuseStep 21343753 = 16007815) B16007815
theorem B28458337 : Blo 2219435 28458337 := bstep (se 2 (by rfl) ⟨10671876, by rfl⟩ : syracuseStep 28458337 = 21343753) B21343753
theorem B37944449 : Blo 2219435 37944449 := bstep (se 2 (by rfl) ⟨14229168, by rfl⟩ : syracuseStep 37944449 = 28458337) B28458337
theorem B25296299 : Blo 2219435 25296299 := bstep (se 1 (by rfl) ⟨18972224, by rfl⟩ : syracuseStep 25296299 = 37944449) B37944449
theorem B16864199 : Blo 2219435 16864199 := bstep (se 1 (by rfl) ⟨12648149, by rfl⟩ : syracuseStep 16864199 = 25296299) B25296299
theorem B11242799 : Blo 2219435 11242799 := bstep (se 1 (by rfl) ⟨8432099, by rfl⟩ : syracuseStep 11242799 = 16864199) B16864199
theorem B7495199 : Blo 2219435 7495199 := bstep (se 1 (by rfl) ⟨5621399, by rfl⟩ : syracuseStep 7495199 = 11242799) B11242799
theorem B4996799 : Blo 2219435 4996799 := bstep (se 1 (by rfl) ⟨3747599, by rfl⟩ : syracuseStep 4996799 = 7495199) B7495199
theorem B3331199 : Blo 2219435 3331199 := bstep (se 1 (by rfl) ⟨2498399, by rfl⟩ : syracuseStep 3331199 = 4996799) B4996799
theorem B2220799 : Blo 2219435 2220799 := bstep (se 1 (by rfl) ⟨1665599, by rfl⟩ : syracuseStep 2220799 = 3331199) B3331199
theorem B3331205 : Blo 2219435 3331205 := bbase (se 4 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 3331205 = 624601) (by norm_num)
theorem B2220803 : Blo 2219435 2220803 := bstep (se 1 (by rfl) ⟨1665602, by rfl⟩ : syracuseStep 2220803 = 3331205) B3331205
theorem B3747613 : Blo 2219435 3747613 := bbase (se 3 (by rfl) ⟨702677, by rfl⟩ : syracuseStep 3747613 = 1405355) (by norm_num)
theorem B4996817 : Blo 2219435 4996817 := bstep (se 2 (by rfl) ⟨1873806, by rfl⟩ : syracuseStep 4996817 = 3747613) B3747613
theorem B3331211 : Blo 2219435 3331211 := bstep (se 1 (by rfl) ⟨2498408, by rfl⟩ : syracuseStep 3331211 = 4996817) B4996817
theorem B2220807 : Blo 2219435 2220807 := bstep (se 1 (by rfl) ⟨1665605, by rfl⟩ : syracuseStep 2220807 = 3331211) B3331211
theorem B2498413 : Blo 2219435 2498413 := bbase (se 3 (by rfl) ⟨468452, by rfl⟩ : syracuseStep 2498413 = 936905) (by norm_num)
theorem B3331217 : Blo 2219435 3331217 := bstep (se 2 (by rfl) ⟨1249206, by rfl⟩ : syracuseStep 3331217 = 2498413) B2498413
theorem B2220811 : Blo 2219435 2220811 := bstep (se 1 (by rfl) ⟨1665608, by rfl⟩ : syracuseStep 2220811 = 3331217) B3331217
theorem B7495253 : Blo 2219435 7495253 := bbase (se 8 (by rfl) ⟨43917, by rfl⟩ : syracuseStep 7495253 = 87835) (by norm_num)
theorem B4996835 : Blo 2219435 4996835 := bstep (se 1 (by rfl) ⟨3747626, by rfl⟩ : syracuseStep 4996835 = 7495253) B7495253
theorem B3331223 : Blo 2219435 3331223 := bstep (se 1 (by rfl) ⟨2498417, by rfl⟩ : syracuseStep 3331223 = 4996835) B4996835
theorem B2220815 : Blo 2219435 2220815 := bstep (se 1 (by rfl) ⟨1665611, by rfl⟩ : syracuseStep 2220815 = 3331223) B3331223
theorem B3331229 : Blo 2219435 3331229 := bbase (se 3 (by rfl) ⟨624605, by rfl⟩ : syracuseStep 3331229 = 1249211) (by norm_num)
theorem B2220819 : Blo 2219435 2220819 := bstep (se 1 (by rfl) ⟨1665614, by rfl⟩ : syracuseStep 2220819 = 3331229) B3331229
theorem B4996853 : Blo 2219435 4996853 := bbase (se 5 (by rfl) ⟨234227, by rfl⟩ : syracuseStep 4996853 = 468455) (by norm_num)
theorem B3331235 : Blo 2219435 3331235 := bstep (se 1 (by rfl) ⟨2498426, by rfl⟩ : syracuseStep 3331235 = 4996853) B4996853
theorem B2220823 : Blo 2219435 2220823 := bstep (se 1 (by rfl) ⟨1665617, by rfl⟩ : syracuseStep 2220823 = 3331235) B3331235
theorem B4002005 : Blo 2219435 4002005 := bbase (se 7 (by rfl) ⟨46898, by rfl⟩ : syracuseStep 4002005 = 93797) (by norm_num)
theorem B10672013 : Blo 2219435 10672013 := bstep (se 3 (by rfl) ⟨2001002, by rfl⟩ : syracuseStep 10672013 = 4002005) B4002005
theorem B28458701 : Blo 2219435 28458701 := bstep (se 3 (by rfl) ⟨5336006, by rfl⟩ : syracuseStep 28458701 = 10672013) B10672013
theorem B18972467 : Blo 2219435 18972467 := bstep (se 1 (by rfl) ⟨14229350, by rfl⟩ : syracuseStep 18972467 = 28458701) B28458701
theorem B12648311 : Blo 2219435 12648311 := bstep (se 1 (by rfl) ⟨9486233, by rfl⟩ : syracuseStep 12648311 = 18972467) B18972467
theorem B8432207 : Blo 2219435 8432207 := bstep (se 1 (by rfl) ⟨6324155, by rfl⟩ : syracuseStep 8432207 = 12648311) B12648311
theorem B5621471 : Blo 2219435 5621471 := bstep (se 1 (by rfl) ⟨4216103, by rfl⟩ : syracuseStep 5621471 = 8432207) B8432207
theorem B3747647 : Blo 2219435 3747647 := bstep (se 1 (by rfl) ⟨2810735, by rfl⟩ : syracuseStep 3747647 = 5621471) B5621471
theorem B2498431 : Blo 2219435 2498431 := bstep (se 1 (by rfl) ⟨1873823, by rfl⟩ : syracuseStep 2498431 = 3747647) B3747647
theorem B3331241 : Blo 2219435 3331241 := bstep (se 2 (by rfl) ⟨1249215, by rfl⟩ : syracuseStep 3331241 = 2498431) B2498431
theorem B2220827 : Blo 2219435 2220827 := bstep (se 1 (by rfl) ⟨1665620, by rfl⟩ : syracuseStep 2220827 = 3331241) B3331241
theorem B4743125 : Blo 2219435 4743125 := bbase (se 7 (by rfl) ⟨55583, by rfl⟩ : syracuseStep 4743125 = 111167) (by norm_num)
theorem B3162083 : Blo 2219435 3162083 := bstep (se 1 (by rfl) ⟨2371562, by rfl⟩ : syracuseStep 3162083 = 4743125) B4743125
theorem B8432221 : Blo 2219435 8432221 := bstep (se 3 (by rfl) ⟨1581041, by rfl⟩ : syracuseStep 8432221 = 3162083) B3162083
theorem B11242961 : Blo 2219435 11242961 := bstep (se 2 (by rfl) ⟨4216110, by rfl⟩ : syracuseStep 11242961 = 8432221) B8432221
theorem B7495307 : Blo 2219435 7495307 := bstep (se 1 (by rfl) ⟨5621480, by rfl⟩ : syracuseStep 7495307 = 11242961) B11242961
theorem B4996871 : Blo 2219435 4996871 := bstep (se 1 (by rfl) ⟨3747653, by rfl⟩ : syracuseStep 4996871 = 7495307) B7495307
theorem B3331247 : Blo 2219435 3331247 := bstep (se 1 (by rfl) ⟨2498435, by rfl⟩ : syracuseStep 3331247 = 4996871) B4996871
theorem B2220831 : Blo 2219435 2220831 := bstep (se 1 (by rfl) ⟨1665623, by rfl⟩ : syracuseStep 2220831 = 3331247) B3331247
theorem B3331253 : Blo 2219435 3331253 := bbase (se 5 (by rfl) ⟨156152, by rfl⟩ : syracuseStep 3331253 = 312305) (by norm_num)
theorem B2220835 : Blo 2219435 2220835 := bstep (se 1 (by rfl) ⟨1665626, by rfl⟩ : syracuseStep 2220835 = 3331253) B3331253
theorem B5621501 : Blo 2219435 5621501 := bbase (se 3 (by rfl) ⟨1054031, by rfl⟩ : syracuseStep 5621501 = 2108063) (by norm_num)
theorem B3747667 : Blo 2219435 3747667 := bstep (se 1 (by rfl) ⟨2810750, by rfl⟩ : syracuseStep 3747667 = 5621501) B5621501
theorem B4996889 : Blo 2219435 4996889 := bstep (se 2 (by rfl) ⟨1873833, by rfl⟩ : syracuseStep 4996889 = 3747667) B3747667
theorem B3331259 : Blo 2219435 3331259 := bstep (se 1 (by rfl) ⟨2498444, by rfl⟩ : syracuseStep 3331259 = 4996889) B4996889
theorem B2220839 : Blo 2219435 2220839 := bstep (se 1 (by rfl) ⟨1665629, by rfl⟩ : syracuseStep 2220839 = 3331259) B3331259
theorem B2498449 : Blo 2219435 2498449 := bbase (se 2 (by rfl) ⟨936918, by rfl⟩ : syracuseStep 2498449 = 1873837) (by norm_num)
theorem B3331265 : Blo 2219435 3331265 := bstep (se 2 (by rfl) ⟨1249224, by rfl⟩ : syracuseStep 3331265 = 2498449) B2498449
theorem B2220843 : Blo 2219435 2220843 := bstep (se 1 (by rfl) ⟨1665632, by rfl⟩ : syracuseStep 2220843 = 3331265) B3331265
theorem B4216141 : Blo 2219435 4216141 := bbase (se 3 (by rfl) ⟨790526, by rfl⟩ : syracuseStep 4216141 = 1581053) (by norm_num)
theorem B5621521 : Blo 2219435 5621521 := bstep (se 2 (by rfl) ⟨2108070, by rfl⟩ : syracuseStep 5621521 = 4216141) B4216141
theorem B7495361 : Blo 2219435 7495361 := bstep (se 2 (by rfl) ⟨2810760, by rfl⟩ : syracuseStep 7495361 = 5621521) B5621521
theorem B4996907 : Blo 2219435 4996907 := bstep (se 1 (by rfl) ⟨3747680, by rfl⟩ : syracuseStep 4996907 = 7495361) B7495361
theorem B3331271 : Blo 2219435 3331271 := bstep (se 1 (by rfl) ⟨2498453, by rfl⟩ : syracuseStep 3331271 = 4996907) B4996907
theorem B2220847 : Blo 2219435 2220847 := bstep (se 1 (by rfl) ⟨1665635, by rfl⟩ : syracuseStep 2220847 = 3331271) B3331271
theorem B3331277 : Blo 2219435 3331277 := bbase (se 3 (by rfl) ⟨624614, by rfl⟩ : syracuseStep 3331277 = 1249229) (by norm_num)
theorem B2220851 : Blo 2219435 2220851 := bstep (se 1 (by rfl) ⟨1665638, by rfl⟩ : syracuseStep 2220851 = 3331277) B3331277
theorem B4996925 : Blo 2219435 4996925 := bbase (se 3 (by rfl) ⟨936923, by rfl⟩ : syracuseStep 4996925 = 1873847) (by norm_num)
theorem B3331283 : Blo 2219435 3331283 := bstep (se 1 (by rfl) ⟨2498462, by rfl⟩ : syracuseStep 3331283 = 4996925) B4996925
theorem B2220855 : Blo 2219435 2220855 := bstep (se 1 (by rfl) ⟨1665641, by rfl⟩ : syracuseStep 2220855 = 3331283) B3331283
theorem B3747701 : Blo 2219435 3747701 := bbase (se 5 (by rfl) ⟨175673, by rfl⟩ : syracuseStep 3747701 = 351347) (by norm_num)
theorem B2498467 : Blo 2219435 2498467 := bstep (se 1 (by rfl) ⟨1873850, by rfl⟩ : syracuseStep 2498467 = 3747701) B3747701
theorem B3331289 : Blo 2219435 3331289 := bstep (se 2 (by rfl) ⟨1249233, by rfl⟩ : syracuseStep 3331289 = 2498467) B2498467
theorem B2220859 : Blo 2219435 2220859 := bstep (se 1 (by rfl) ⟨1665644, by rfl⟩ : syracuseStep 2220859 = 3331289) B3331289
theorem B5336093 : Blo 2219435 5336093 := bbase (se 3 (by rfl) ⟨1000517, by rfl⟩ : syracuseStep 5336093 = 2001035) (by norm_num)
theorem B3557395 : Blo 2219435 3557395 := bstep (se 1 (by rfl) ⟨2668046, by rfl⟩ : syracuseStep 3557395 = 5336093) B5336093
theorem B4743193 : Blo 2219435 4743193 := bstep (se 2 (by rfl) ⟨1778697, by rfl⟩ : syracuseStep 4743193 = 3557395) B3557395
theorem B6324257 : Blo 2219435 6324257 := bstep (se 2 (by rfl) ⟨2371596, by rfl⟩ : syracuseStep 6324257 = 4743193) B4743193
theorem B16864685 : Blo 2219435 16864685 := bstep (se 3 (by rfl) ⟨3162128, by rfl⟩ : syracuseStep 16864685 = 6324257) B6324257
theorem B11243123 : Blo 2219435 11243123 := bstep (se 1 (by rfl) ⟨8432342, by rfl⟩ : syracuseStep 11243123 = 16864685) B16864685
theorem B7495415 : Blo 2219435 7495415 := bstep (se 1 (by rfl) ⟨5621561, by rfl⟩ : syracuseStep 7495415 = 11243123) B11243123
theorem B4996943 : Blo 2219435 4996943 := bstep (se 1 (by rfl) ⟨3747707, by rfl⟩ : syracuseStep 4996943 = 7495415) B7495415
theorem B3331295 : Blo 2219435 3331295 := bstep (se 1 (by rfl) ⟨2498471, by rfl⟩ : syracuseStep 3331295 = 4996943) B4996943
theorem B2220863 : Blo 2219435 2220863 := bstep (se 1 (by rfl) ⟨1665647, by rfl⟩ : syracuseStep 2220863 = 3331295) B3331295
theorem B3331301 : Blo 2219435 3331301 := bbase (se 4 (by rfl) ⟨312309, by rfl⟩ : syracuseStep 3331301 = 624619) (by norm_num)
theorem B2220867 : Blo 2219435 2220867 := bstep (se 1 (by rfl) ⟨1665650, by rfl⟩ : syracuseStep 2220867 = 3331301) B3331301
theorem B4002085 : Blo 2219435 4002085 := bbase (se 4 (by rfl) ⟨375195, by rfl⟩ : syracuseStep 4002085 = 750391) (by norm_num)
theorem B5336113 : Blo 2219435 5336113 := bstep (se 2 (by rfl) ⟨2001042, by rfl⟩ : syracuseStep 5336113 = 4002085) B4002085
theorem B7114817 : Blo 2219435 7114817 := bstep (se 2 (by rfl) ⟨2668056, by rfl⟩ : syracuseStep 7114817 = 5336113) B5336113
theorem B4743211 : Blo 2219435 4743211 := bstep (se 1 (by rfl) ⟨3557408, by rfl⟩ : syracuseStep 4743211 = 7114817) B7114817
theorem B6324281 : Blo 2219435 6324281 := bstep (se 2 (by rfl) ⟨2371605, by rfl⟩ : syracuseStep 6324281 = 4743211) B4743211
theorem B4216187 : Blo 2219435 4216187 := bstep (se 1 (by rfl) ⟨3162140, by rfl⟩ : syracuseStep 4216187 = 6324281) B6324281
theorem B2810791 : Blo 2219435 2810791 := bstep (se 1 (by rfl) ⟨2108093, by rfl⟩ : syracuseStep 2810791 = 4216187) B4216187
theorem B3747721 : Blo 2219435 3747721 := bstep (se 2 (by rfl) ⟨1405395, by rfl⟩ : syracuseStep 3747721 = 2810791) B2810791
theorem B4996961 : Blo 2219435 4996961 := bstep (se 2 (by rfl) ⟨1873860, by rfl⟩ : syracuseStep 4996961 = 3747721) B3747721
theorem B3331307 : Blo 2219435 3331307 := bstep (se 1 (by rfl) ⟨2498480, by rfl⟩ : syracuseStep 3331307 = 4996961) B4996961
theorem B2220871 : Blo 2219435 2220871 := bstep (se 1 (by rfl) ⟨1665653, by rfl⟩ : syracuseStep 2220871 = 3331307) B3331307
theorem B2498485 : Blo 2219435 2498485 := bbase (se 5 (by rfl) ⟨117116, by rfl⟩ : syracuseStep 2498485 = 234233) (by norm_num)
theorem B3331313 : Blo 2219435 3331313 := bstep (se 2 (by rfl) ⟨1249242, by rfl⟩ : syracuseStep 3331313 = 2498485) B2498485
theorem B2220875 : Blo 2219435 2220875 := bstep (se 1 (by rfl) ⟨1665656, by rfl⟩ : syracuseStep 2220875 = 3331313) B3331313
theorem B2810801 : Blo 2219435 2810801 := bbase (se 2 (by rfl) ⟨1054050, by rfl⟩ : syracuseStep 2810801 = 2108101) (by norm_num)
theorem B7495469 : Blo 2219435 7495469 := bstep (se 3 (by rfl) ⟨1405400, by rfl⟩ : syracuseStep 7495469 = 2810801) B2810801
theorem B4996979 : Blo 2219435 4996979 := bstep (se 1 (by rfl) ⟨3747734, by rfl⟩ : syracuseStep 4996979 = 7495469) B7495469
theorem B3331319 : Blo 2219435 3331319 := bstep (se 1 (by rfl) ⟨2498489, by rfl⟩ : syracuseStep 3331319 = 4996979) B4996979
theorem B2220879 : Blo 2219435 2220879 := bstep (se 1 (by rfl) ⟨1665659, by rfl⟩ : syracuseStep 2220879 = 3331319) B3331319
theorem B3331325 : Blo 2219435 3331325 := bbase (se 3 (by rfl) ⟨624623, by rfl⟩ : syracuseStep 3331325 = 1249247) (by norm_num)
theorem B2220883 : Blo 2219435 2220883 := bstep (se 1 (by rfl) ⟨1665662, by rfl⟩ : syracuseStep 2220883 = 3331325) B3331325
theorem B4996997 : Blo 2219435 4996997 := bbase (se 4 (by rfl) ⟨468468, by rfl⟩ : syracuseStep 4996997 = 936937) (by norm_num)
theorem B3331331 : Blo 2219435 3331331 := bstep (se 1 (by rfl) ⟨2498498, by rfl⟩ : syracuseStep 3331331 = 4996997) B4996997
theorem B2220887 : Blo 2219435 2220887 := bstep (se 1 (by rfl) ⟨1665665, by rfl⟩ : syracuseStep 2220887 = 3331331) B3331331
theorem B2668081 : Blo 2219435 2668081 := bbase (se 2 (by rfl) ⟨1000530, by rfl⟩ : syracuseStep 2668081 = 2001061) (by norm_num)
theorem B3557441 : Blo 2219435 3557441 := bstep (se 2 (by rfl) ⟨1334040, by rfl⟩ : syracuseStep 3557441 = 2668081) B2668081
theorem B2371627 : Blo 2219435 2371627 := bstep (se 1 (by rfl) ⟨1778720, by rfl⟩ : syracuseStep 2371627 = 3557441) B3557441
theorem B3162169 : Blo 2219435 3162169 := bstep (se 2 (by rfl) ⟨1185813, by rfl⟩ : syracuseStep 3162169 = 2371627) B2371627
theorem B4216225 : Blo 2219435 4216225 := bstep (se 2 (by rfl) ⟨1581084, by rfl⟩ : syracuseStep 4216225 = 3162169) B3162169
theorem B5621633 : Blo 2219435 5621633 := bstep (se 2 (by rfl) ⟨2108112, by rfl⟩ : syracuseStep 5621633 = 4216225) B4216225
theorem B3747755 : Blo 2219435 3747755 := bstep (se 1 (by rfl) ⟨2810816, by rfl⟩ : syracuseStep 3747755 = 5621633) B5621633
theorem B2498503 : Blo 2219435 2498503 := bstep (se 1 (by rfl) ⟨1873877, by rfl⟩ : syracuseStep 2498503 = 3747755) B3747755
theorem B3331337 : Blo 2219435 3331337 := bstep (se 2 (by rfl) ⟨1249251, by rfl⟩ : syracuseStep 3331337 = 2498503) B2498503
theorem B2220891 : Blo 2219435 2220891 := bstep (se 1 (by rfl) ⟨1665668, by rfl⟩ : syracuseStep 2220891 = 3331337) B3331337
theorem B11243285 : Blo 2219435 11243285 := bbase (se 6 (by rfl) ⟨263514, by rfl⟩ : syracuseStep 11243285 = 527029) (by norm_num)
theorem B7495523 : Blo 2219435 7495523 := bstep (se 1 (by rfl) ⟨5621642, by rfl⟩ : syracuseStep 7495523 = 11243285) B11243285
theorem B4997015 : Blo 2219435 4997015 := bstep (se 1 (by rfl) ⟨3747761, by rfl⟩ : syracuseStep 4997015 = 7495523) B7495523
theorem B3331343 : Blo 2219435 3331343 := bstep (se 1 (by rfl) ⟨2498507, by rfl⟩ : syracuseStep 3331343 = 4997015) B4997015
theorem B2220895 : Blo 2219435 2220895 := bstep (se 1 (by rfl) ⟨1665671, by rfl⟩ : syracuseStep 2220895 = 3331343) B3331343
theorem B3331349 : Blo 2219435 3331349 := bbase (se 6 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 3331349 = 156157) (by norm_num)
theorem B2220899 : Blo 2219435 2220899 := bstep (se 1 (by rfl) ⟨1665674, by rfl⟩ : syracuseStep 2220899 = 3331349) B3331349
theorem B9615989 : Blo 2219435 9615989 := bbase (se 5 (by rfl) ⟨450749, by rfl⟩ : syracuseStep 9615989 = 901499) (by norm_num)
theorem B6410659 : Blo 2219435 6410659 := bstep (se 1 (by rfl) ⟨4807994, by rfl⟩ : syracuseStep 6410659 = 9615989) B9615989
theorem B8547545 : Blo 2219435 8547545 := bstep (se 2 (by rfl) ⟨3205329, by rfl⟩ : syracuseStep 8547545 = 6410659) B6410659
theorem B5698363 : Blo 2219435 5698363 := bstep (se 1 (by rfl) ⟨4273772, by rfl⟩ : syracuseStep 5698363 = 8547545) B8547545
theorem B7597817 : Blo 2219435 7597817 := bstep (se 2 (by rfl) ⟨2849181, by rfl⟩ : syracuseStep 7597817 = 5698363) B5698363
theorem B5065211 : Blo 2219435 5065211 := bstep (se 1 (by rfl) ⟨3798908, by rfl⟩ : syracuseStep 5065211 = 7597817) B7597817
theorem B13507229 : Blo 2219435 13507229 := bstep (se 3 (by rfl) ⟨2532605, by rfl⟩ : syracuseStep 13507229 = 5065211) B5065211
theorem B9004819 : Blo 2219435 9004819 := bstep (se 1 (by rfl) ⟨6753614, by rfl⟩ : syracuseStep 9004819 = 13507229) B13507229
theorem B12006425 : Blo 2219435 12006425 := bstep (se 2 (by rfl) ⟨4502409, by rfl⟩ : syracuseStep 12006425 = 9004819) B9004819
theorem B32017133 : Blo 2219435 32017133 := bstep (se 3 (by rfl) ⟨6003212, by rfl⟩ : syracuseStep 32017133 = 12006425) B12006425
theorem B21344755 : Blo 2219435 21344755 := bstep (se 1 (by rfl) ⟨16008566, by rfl⟩ : syracuseStep 21344755 = 32017133) B32017133
theorem B28459673 : Blo 2219435 28459673 := bstep (se 2 (by rfl) ⟨10672377, by rfl⟩ : syracuseStep 28459673 = 21344755) B21344755
theorem B18973115 : Blo 2219435 18973115 := bstep (se 1 (by rfl) ⟨14229836, by rfl⟩ : syracuseStep 18973115 = 28459673) B28459673
theorem B12648743 : Blo 2219435 12648743 := bstep (se 1 (by rfl) ⟨9486557, by rfl⟩ : syracuseStep 12648743 = 18973115) B18973115
theorem B8432495 : Blo 2219435 8432495 := bstep (se 1 (by rfl) ⟨6324371, by rfl⟩ : syracuseStep 8432495 = 12648743) B12648743
theorem B5621663 : Blo 2219435 5621663 := bstep (se 1 (by rfl) ⟨4216247, by rfl⟩ : syracuseStep 5621663 = 8432495) B8432495
theorem B3747775 : Blo 2219435 3747775 := bstep (se 1 (by rfl) ⟨2810831, by rfl⟩ : syracuseStep 3747775 = 5621663) B5621663
theorem B4997033 : Blo 2219435 4997033 := bstep (se 2 (by rfl) ⟨1873887, by rfl⟩ : syracuseStep 4997033 = 3747775) B3747775
theorem B3331355 : Blo 2219435 3331355 := bstep (se 1 (by rfl) ⟨2498516, by rfl⟩ : syracuseStep 3331355 = 4997033) B4997033
theorem B2220903 : Blo 2219435 2220903 := bstep (se 1 (by rfl) ⟨1665677, by rfl⟩ : syracuseStep 2220903 = 3331355) B3331355
theorem B2498521 : Blo 2219435 2498521 := bbase (se 2 (by rfl) ⟨936945, by rfl⟩ : syracuseStep 2498521 = 1873891) (by norm_num)
theorem B3331361 : Blo 2219435 3331361 := bstep (se 2 (by rfl) ⟨1249260, by rfl⟩ : syracuseStep 3331361 = 2498521) B2498521
theorem B2220907 : Blo 2219435 2220907 := bstep (se 1 (by rfl) ⟨1665680, by rfl⟩ : syracuseStep 2220907 = 3331361) B3331361
theorem B3162197 : Blo 2219435 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B8432525 : Blo 2219435 8432525 := bstep (se 3 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 8432525 = 3162197) B3162197
theorem B5621683 : Blo 2219435 5621683 := bstep (se 1 (by rfl) ⟨4216262, by rfl⟩ : syracuseStep 5621683 = 8432525) B8432525
theorem B7495577 : Blo 2219435 7495577 := bstep (se 2 (by rfl) ⟨2810841, by rfl⟩ : syracuseStep 7495577 = 5621683) B5621683
theorem B4997051 : Blo 2219435 4997051 := bstep (se 1 (by rfl) ⟨3747788, by rfl⟩ : syracuseStep 4997051 = 7495577) B7495577
theorem B3331367 : Blo 2219435 3331367 := bstep (se 1 (by rfl) ⟨2498525, by rfl⟩ : syracuseStep 3331367 = 4997051) B4997051
theorem B2220911 : Blo 2219435 2220911 := bstep (se 1 (by rfl) ⟨1665683, by rfl⟩ : syracuseStep 2220911 = 3331367) B3331367
theorem B3331373 : Blo 2219435 3331373 := bbase (se 3 (by rfl) ⟨624632, by rfl⟩ : syracuseStep 3331373 = 1249265) (by norm_num)
theorem B2220915 : Blo 2219435 2220915 := bstep (se 1 (by rfl) ⟨1665686, by rfl⟩ : syracuseStep 2220915 = 3331373) B3331373
theorem B4997069 : Blo 2219435 4997069 := bbase (se 3 (by rfl) ⟨936950, by rfl⟩ : syracuseStep 4997069 = 1873901) (by norm_num)
theorem B3331379 : Blo 2219435 3331379 := bstep (se 1 (by rfl) ⟨2498534, by rfl⟩ : syracuseStep 3331379 = 4997069) B4997069
theorem B2220919 : Blo 2219435 2220919 := bstep (se 1 (by rfl) ⟨1665689, by rfl⟩ : syracuseStep 2220919 = 3331379) B3331379
theorem B2810857 : Blo 2219435 2810857 := bbase (se 2 (by rfl) ⟨1054071, by rfl⟩ : syracuseStep 2810857 = 2108143) (by norm_num)
theorem B3747809 : Blo 2219435 3747809 := bstep (se 2 (by rfl) ⟨1405428, by rfl⟩ : syracuseStep 3747809 = 2810857) B2810857
theorem B2498539 : Blo 2219435 2498539 := bstep (se 1 (by rfl) ⟨1873904, by rfl⟩ : syracuseStep 2498539 = 3747809) B3747809
theorem B3331385 : Blo 2219435 3331385 := bstep (se 2 (by rfl) ⟨1249269, by rfl⟩ : syracuseStep 3331385 = 2498539) B2498539
theorem B2220923 : Blo 2219435 2220923 := bstep (se 1 (by rfl) ⟨1665692, by rfl⟩ : syracuseStep 2220923 = 3331385) B3331385
theorem B2849213 : Blo 2219435 2849213 := bbase (se 3 (by rfl) ⟨534227, by rfl⟩ : syracuseStep 2849213 = 1068455) (by norm_num)
theorem B7597901 : Blo 2219435 7597901 := bstep (se 3 (by rfl) ⟨1424606, by rfl⟩ : syracuseStep 7597901 = 2849213) B2849213
theorem B5065267 : Blo 2219435 5065267 := bstep (se 1 (by rfl) ⟨3798950, by rfl⟩ : syracuseStep 5065267 = 7597901) B7597901
theorem B6753689 : Blo 2219435 6753689 := bstep (se 2 (by rfl) ⟨2532633, by rfl⟩ : syracuseStep 6753689 = 5065267) B5065267
theorem B4502459 : Blo 2219435 4502459 := bstep (se 1 (by rfl) ⟨3376844, by rfl⟩ : syracuseStep 4502459 = 6753689) B6753689
theorem B3001639 : Blo 2219435 3001639 := bstep (se 1 (by rfl) ⟨2251229, by rfl⟩ : syracuseStep 3001639 = 4502459) B4502459
theorem B4002185 : Blo 2219435 4002185 := bstep (se 2 (by rfl) ⟨1500819, by rfl⟩ : syracuseStep 4002185 = 3001639) B3001639
theorem B2668123 : Blo 2219435 2668123 := bstep (se 1 (by rfl) ⟨2001092, by rfl⟩ : syracuseStep 2668123 = 4002185) B4002185
theorem B14229989 : Blo 2219435 14229989 := bstep (se 4 (by rfl) ⟨1334061, by rfl⟩ : syracuseStep 14229989 = 2668123) B2668123
theorem B9486659 : Blo 2219435 9486659 := bstep (se 1 (by rfl) ⟨7114994, by rfl⟩ : syracuseStep 9486659 = 14229989) B14229989
theorem B25297757 : Blo 2219435 25297757 := bstep (se 3 (by rfl) ⟨4743329, by rfl⟩ : syracuseStep 25297757 = 9486659) B9486659
theorem B16865171 : Blo 2219435 16865171 := bstep (se 1 (by rfl) ⟨12648878, by rfl⟩ : syracuseStep 16865171 = 25297757) B25297757
theorem B11243447 : Blo 2219435 11243447 := bstep (se 1 (by rfl) ⟨8432585, by rfl⟩ : syracuseStep 11243447 = 16865171) B16865171
theorem B7495631 : Blo 2219435 7495631 := bstep (se 1 (by rfl) ⟨5621723, by rfl⟩ : syracuseStep 7495631 = 11243447) B11243447
theorem B4997087 : Blo 2219435 4997087 := bstep (se 1 (by rfl) ⟨3747815, by rfl⟩ : syracuseStep 4997087 = 7495631) B7495631
theorem B3331391 : Blo 2219435 3331391 := bstep (se 1 (by rfl) ⟨2498543, by rfl⟩ : syracuseStep 3331391 = 4997087) B4997087
theorem B2220927 : Blo 2219435 2220927 := bstep (se 1 (by rfl) ⟨1665695, by rfl⟩ : syracuseStep 2220927 = 3331391) B3331391
theorem B3331397 : Blo 2219435 3331397 := bbase (se 4 (by rfl) ⟨312318, by rfl⟩ : syracuseStep 3331397 = 624637) (by norm_num)
theorem B2220931 : Blo 2219435 2220931 := bstep (se 1 (by rfl) ⟨1665698, by rfl⟩ : syracuseStep 2220931 = 3331397) B3331397
theorem B3747829 : Blo 2219435 3747829 := bbase (se 5 (by rfl) ⟨175679, by rfl⟩ : syracuseStep 3747829 = 351359) (by norm_num)
theorem B4997105 : Blo 2219435 4997105 := bstep (se 2 (by rfl) ⟨1873914, by rfl⟩ : syracuseStep 4997105 = 3747829) B3747829
theorem B3331403 : Blo 2219435 3331403 := bstep (se 1 (by rfl) ⟨2498552, by rfl⟩ : syracuseStep 3331403 = 4997105) B4997105
theorem B2220935 : Blo 2219435 2220935 := bstep (se 1 (by rfl) ⟨1665701, by rfl⟩ : syracuseStep 2220935 = 3331403) B3331403
theorem B2498557 : Blo 2219435 2498557 := bbase (se 3 (by rfl) ⟨468479, by rfl⟩ : syracuseStep 2498557 = 936959) (by norm_num)
theorem B3331409 : Blo 2219435 3331409 := bstep (se 2 (by rfl) ⟨1249278, by rfl⟩ : syracuseStep 3331409 = 2498557) B2498557
theorem B2220939 : Blo 2219435 2220939 := bstep (se 1 (by rfl) ⟨1665704, by rfl⟩ : syracuseStep 2220939 = 3331409) B3331409
theorem B7495685 : Blo 2219435 7495685 := bbase (se 4 (by rfl) ⟨702720, by rfl⟩ : syracuseStep 7495685 = 1405441) (by norm_num)
theorem B4997123 : Blo 2219435 4997123 := bstep (se 1 (by rfl) ⟨3747842, by rfl⟩ : syracuseStep 4997123 = 7495685) B7495685
theorem B3331415 : Blo 2219435 3331415 := bstep (se 1 (by rfl) ⟨2498561, by rfl⟩ : syracuseStep 3331415 = 4997123) B4997123
theorem B2220943 : Blo 2219435 2220943 := bstep (se 1 (by rfl) ⟨1665707, by rfl⟩ : syracuseStep 2220943 = 3331415) B3331415
theorem B3331421 : Blo 2219435 3331421 := bbase (se 3 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 3331421 = 1249283) (by norm_num)
theorem B2220947 : Blo 2219435 2220947 := bstep (se 1 (by rfl) ⟨1665710, by rfl⟩ : syracuseStep 2220947 = 3331421) B3331421
theorem B4997141 : Blo 2219435 4997141 := bbase (se 6 (by rfl) ⟨117120, by rfl⟩ : syracuseStep 4997141 = 234241) (by norm_num)
theorem B3331427 : Blo 2219435 3331427 := bstep (se 1 (by rfl) ⟨2498570, by rfl⟩ : syracuseStep 3331427 = 4997141) B4997141
theorem B2220951 : Blo 2219435 2220951 := bstep (se 1 (by rfl) ⟨1665713, by rfl⟩ : syracuseStep 2220951 = 3331427) B3331427
theorem B8432693 : Blo 2219435 8432693 := bbase (se 5 (by rfl) ⟨395282, by rfl⟩ : syracuseStep 8432693 = 790565) (by norm_num)
theorem B5621795 : Blo 2219435 5621795 := bstep (se 1 (by rfl) ⟨4216346, by rfl⟩ : syracuseStep 5621795 = 8432693) B8432693
theorem B3747863 : Blo 2219435 3747863 := bstep (se 1 (by rfl) ⟨2810897, by rfl⟩ : syracuseStep 3747863 = 5621795) B5621795
theorem B2498575 : Blo 2219435 2498575 := bstep (se 1 (by rfl) ⟨1873931, by rfl⟩ : syracuseStep 2498575 = 3747863) B3747863
theorem B3331433 : Blo 2219435 3331433 := bstep (se 2 (by rfl) ⟨1249287, by rfl⟩ : syracuseStep 3331433 = 2498575) B2498575
theorem B2220955 : Blo 2219435 2220955 := bstep (se 1 (by rfl) ⟨1665716, by rfl⟩ : syracuseStep 2220955 = 3331433) B3331433
theorem B3557549 : Blo 2219435 3557549 := bbase (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) (by norm_num)
theorem B2371699 : Blo 2219435 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B12649061 : Blo 2219435 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B8432707 : Blo 2219435 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B11243609 : Blo 2219435 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B7495739 : Blo 2219435 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B4997159 : Blo 2219435 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B3331439 : Blo 2219435 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B2220959 : Blo 2219435 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B3331445 : Blo 2219435 3331445 := bbase (se 5 (by rfl) ⟨156161, by rfl⟩ : syracuseStep 3331445 = 312323) (by norm_num)
theorem B2220963 : Blo 2219435 2220963 := bstep (se 1 (by rfl) ⟨1665722, by rfl⟩ : syracuseStep 2220963 = 3331445) B3331445
theorem B3162277 : Blo 2219435 3162277 := bbase (se 4 (by rfl) ⟨296463, by rfl⟩ : syracuseStep 3162277 = 592927) (by norm_num)
theorem B4216369 : Blo 2219435 4216369 := bstep (se 2 (by rfl) ⟨1581138, by rfl⟩ : syracuseStep 4216369 = 3162277) B3162277
theorem B5621825 : Blo 2219435 5621825 := bstep (se 2 (by rfl) ⟨2108184, by rfl⟩ : syracuseStep 5621825 = 4216369) B4216369
theorem B3747883 : Blo 2219435 3747883 := bstep (se 1 (by rfl) ⟨2810912, by rfl⟩ : syracuseStep 3747883 = 5621825) B5621825
theorem B4997177 : Blo 2219435 4997177 := bstep (se 2 (by rfl) ⟨1873941, by rfl⟩ : syracuseStep 4997177 = 3747883) B3747883
theorem B3331451 : Blo 2219435 3331451 := bstep (se 1 (by rfl) ⟨2498588, by rfl⟩ : syracuseStep 3331451 = 4997177) B4997177
theorem B2220967 : Blo 2219435 2220967 := bstep (se 1 (by rfl) ⟨1665725, by rfl⟩ : syracuseStep 2220967 = 3331451) B3331451
theorem B2498593 : Blo 2219435 2498593 := bbase (se 2 (by rfl) ⟨936972, by rfl⟩ : syracuseStep 2498593 = 1873945) (by norm_num)
theorem B3331457 : Blo 2219435 3331457 := bstep (se 2 (by rfl) ⟨1249296, by rfl⟩ : syracuseStep 3331457 = 2498593) B2498593
theorem B2220971 : Blo 2219435 2220971 := bstep (se 1 (by rfl) ⟨1665728, by rfl⟩ : syracuseStep 2220971 = 3331457) B3331457
theorem B5621845 : Blo 2219435 5621845 := bbase (se 8 (by rfl) ⟨32940, by rfl⟩ : syracuseStep 5621845 = 65881) (by norm_num)
theorem B7495793 : Blo 2219435 7495793 := bstep (se 2 (by rfl) ⟨2810922, by rfl⟩ : syracuseStep 7495793 = 5621845) B5621845
theorem B4997195 : Blo 2219435 4997195 := bstep (se 1 (by rfl) ⟨3747896, by rfl⟩ : syracuseStep 4997195 = 7495793) B7495793
theorem B3331463 : Blo 2219435 3331463 := bstep (se 1 (by rfl) ⟨2498597, by rfl⟩ : syracuseStep 3331463 = 4997195) B4997195
theorem B2220975 : Blo 2219435 2220975 := bstep (se 1 (by rfl) ⟨1665731, by rfl⟩ : syracuseStep 2220975 = 3331463) B3331463
theorem B3331469 : Blo 2219435 3331469 := bbase (se 3 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 3331469 = 1249301) (by norm_num)
theorem B2220979 : Blo 2219435 2220979 := bstep (se 1 (by rfl) ⟨1665734, by rfl⟩ : syracuseStep 2220979 = 3331469) B3331469
theorem B4997213 : Blo 2219435 4997213 := bbase (se 3 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 4997213 = 1873955) (by norm_num)
theorem B3331475 : Blo 2219435 3331475 := bstep (se 1 (by rfl) ⟨2498606, by rfl⟩ : syracuseStep 3331475 = 4997213) B4997213
theorem B2220983 : Blo 2219435 2220983 := bstep (se 1 (by rfl) ⟨1665737, by rfl⟩ : syracuseStep 2220983 = 3331475) B3331475
theorem B3747917 : Blo 2219435 3747917 := bbase (se 3 (by rfl) ⟨702734, by rfl⟩ : syracuseStep 3747917 = 1405469) (by norm_num)
theorem B2498611 : Blo 2219435 2498611 := bstep (se 1 (by rfl) ⟨1873958, by rfl⟩ : syracuseStep 2498611 = 3747917) B3747917
theorem B3331481 : Blo 2219435 3331481 := bstep (se 2 (by rfl) ⟨1249305, by rfl⟩ : syracuseStep 3331481 = 2498611) B2498611
theorem B2220987 : Blo 2219435 2220987 := bstep (se 1 (by rfl) ⟨1665740, by rfl⟩ : syracuseStep 2220987 = 3331481) B3331481
theorem B30807125 : Blo 2219435 30807125 := bbase (se 8 (by rfl) ⟨180510, by rfl⟩ : syracuseStep 30807125 = 361021) (by norm_num)
theorem B20538083 : Blo 2219435 20538083 := bstep (se 1 (by rfl) ⟨15403562, by rfl⟩ : syracuseStep 20538083 = 30807125) B30807125
theorem B54768221 : Blo 2219435 54768221 := bstep (se 3 (by rfl) ⟨10269041, by rfl⟩ : syracuseStep 54768221 = 20538083) B20538083
theorem B36512147 : Blo 2219435 36512147 := bstep (se 1 (by rfl) ⟨27384110, by rfl⟩ : syracuseStep 36512147 = 54768221) B54768221
theorem B24341431 : Blo 2219435 24341431 := bstep (se 1 (by rfl) ⟨18256073, by rfl⟩ : syracuseStep 24341431 = 36512147) B36512147
theorem B32455241 : Blo 2219435 32455241 := bstep (se 2 (by rfl) ⟨12170715, by rfl⟩ : syracuseStep 32455241 = 24341431) B24341431
theorem B21636827 : Blo 2219435 21636827 := bstep (se 1 (by rfl) ⟨16227620, by rfl⟩ : syracuseStep 21636827 = 32455241) B32455241
theorem B14424551 : Blo 2219435 14424551 := bstep (se 1 (by rfl) ⟨10818413, by rfl⟩ : syracuseStep 14424551 = 21636827) B21636827
theorem B9616367 : Blo 2219435 9616367 := bstep (se 1 (by rfl) ⟨7212275, by rfl⟩ : syracuseStep 9616367 = 14424551) B14424551
theorem B6410911 : Blo 2219435 6410911 := bstep (se 1 (by rfl) ⟨4808183, by rfl⟩ : syracuseStep 6410911 = 9616367) B9616367
theorem B8547881 : Blo 2219435 8547881 := bstep (se 2 (by rfl) ⟨3205455, by rfl⟩ : syracuseStep 8547881 = 6410911) B6410911
theorem B91177397 : Blo 2219435 91177397 := bstep (se 5 (by rfl) ⟨4273940, by rfl⟩ : syracuseStep 91177397 = 8547881) B8547881
theorem B60784931 : Blo 2219435 60784931 := bstep (se 1 (by rfl) ⟨45588698, by rfl⟩ : syracuseStep 60784931 = 91177397) B91177397
theorem B162093149 : Blo 2219435 162093149 := bstep (se 3 (by rfl) ⟨30392465, by rfl⟩ : syracuseStep 162093149 = 60784931) B60784931
theorem B108062099 : Blo 2219435 108062099 := bstep (se 1 (by rfl) ⟨81046574, by rfl⟩ : syracuseStep 108062099 = 162093149) B162093149
theorem B72041399 : Blo 2219435 72041399 := bstep (se 1 (by rfl) ⟨54031049, by rfl⟩ : syracuseStep 72041399 = 108062099) B108062099
theorem B48027599 : Blo 2219435 48027599 := bstep (se 1 (by rfl) ⟨36020699, by rfl⟩ : syracuseStep 48027599 = 72041399) B72041399
theorem B32018399 : Blo 2219435 32018399 := bstep (se 1 (by rfl) ⟨24013799, by rfl⟩ : syracuseStep 32018399 = 48027599) B48027599
theorem B21345599 : Blo 2219435 21345599 := bstep (se 1 (by rfl) ⟨16009199, by rfl⟩ : syracuseStep 21345599 = 32018399) B32018399
theorem B14230399 : Blo 2219435 14230399 := bstep (se 1 (by rfl) ⟨10672799, by rfl⟩ : syracuseStep 14230399 = 21345599) B21345599
theorem B18973865 : Blo 2219435 18973865 := bstep (se 2 (by rfl) ⟨7115199, by rfl⟩ : syracuseStep 18973865 = 14230399) B14230399
theorem B12649243 : Blo 2219435 12649243 := bstep (se 1 (by rfl) ⟨9486932, by rfl⟩ : syracuseStep 12649243 = 18973865) B18973865
theorem B16865657 : Blo 2219435 16865657 := bstep (se 2 (by rfl) ⟨6324621, by rfl⟩ : syracuseStep 16865657 = 12649243) B12649243
theorem B11243771 : Blo 2219435 11243771 := bstep (se 1 (by rfl) ⟨8432828, by rfl⟩ : syracuseStep 11243771 = 16865657) B16865657
theorem B7495847 : Blo 2219435 7495847 := bstep (se 1 (by rfl) ⟨5621885, by rfl⟩ : syracuseStep 7495847 = 11243771) B11243771
theorem B4997231 : Blo 2219435 4997231 := bstep (se 1 (by rfl) ⟨3747923, by rfl⟩ : syracuseStep 4997231 = 7495847) B7495847
theorem B3331487 : Blo 2219435 3331487 := bstep (se 1 (by rfl) ⟨2498615, by rfl⟩ : syracuseStep 3331487 = 4997231) B4997231
theorem B2220991 : Blo 2219435 2220991 := bstep (se 1 (by rfl) ⟨1665743, by rfl⟩ : syracuseStep 2220991 = 3331487) B3331487
theorem B3331493 : Blo 2219435 3331493 := bbase (se 4 (by rfl) ⟨312327, by rfl⟩ : syracuseStep 3331493 = 624655) (by norm_num)
theorem B2220995 : Blo 2219435 2220995 := bstep (se 1 (by rfl) ⟨1665746, by rfl⟩ : syracuseStep 2220995 = 3331493) B3331493
theorem B2810953 : Blo 2219435 2810953 := bbase (se 2 (by rfl) ⟨1054107, by rfl⟩ : syracuseStep 2810953 = 2108215) (by norm_num)
theorem B3747937 : Blo 2219435 3747937 := bstep (se 2 (by rfl) ⟨1405476, by rfl⟩ : syracuseStep 3747937 = 2810953) B2810953
theorem B4997249 : Blo 2219435 4997249 := bstep (se 2 (by rfl) ⟨1873968, by rfl⟩ : syracuseStep 4997249 = 3747937) B3747937
theorem B3331499 : Blo 2219435 3331499 := bstep (se 1 (by rfl) ⟨2498624, by rfl⟩ : syracuseStep 3331499 = 4997249) B4997249
theorem B2220999 : Blo 2219435 2220999 := bstep (se 1 (by rfl) ⟨1665749, by rfl⟩ : syracuseStep 2220999 = 3331499) B3331499
theorem B2498629 : Blo 2219435 2498629 := bbase (se 4 (by rfl) ⟨234246, by rfl⟩ : syracuseStep 2498629 = 468493) (by norm_num)
theorem B3331505 : Blo 2219435 3331505 := bstep (se 2 (by rfl) ⟨1249314, by rfl⟩ : syracuseStep 3331505 = 2498629) B2498629
theorem B2221003 : Blo 2219435 2221003 := bstep (se 1 (by rfl) ⟨1665752, by rfl⟩ : syracuseStep 2221003 = 3331505) B3331505
theorem B4216445 : Blo 2219435 4216445 := bbase (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) (by norm_num)
theorem B2810963 : Blo 2219435 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B7495901 : Blo 2219435 7495901 := bstep (se 3 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 7495901 = 2810963) B2810963
theorem B4997267 : Blo 2219435 4997267 := bstep (se 1 (by rfl) ⟨3747950, by rfl⟩ : syracuseStep 4997267 = 7495901) B7495901
theorem B3331511 : Blo 2219435 3331511 := bstep (se 1 (by rfl) ⟨2498633, by rfl⟩ : syracuseStep 3331511 = 4997267) B4997267
theorem B2221007 : Blo 2219435 2221007 := bstep (se 1 (by rfl) ⟨1665755, by rfl⟩ : syracuseStep 2221007 = 3331511) B3331511
theorem B3331517 : Blo 2219435 3331517 := bbase (se 3 (by rfl) ⟨624659, by rfl⟩ : syracuseStep 3331517 = 1249319) (by norm_num)
theorem B2221011 : Blo 2219435 2221011 := bstep (se 1 (by rfl) ⟨1665758, by rfl⟩ : syracuseStep 2221011 = 3331517) B3331517
theorem B4997285 : Blo 2219435 4997285 := bbase (se 4 (by rfl) ⟨468495, by rfl⟩ : syracuseStep 4997285 = 936991) (by norm_num)
theorem B3331523 : Blo 2219435 3331523 := bstep (se 1 (by rfl) ⟨2498642, by rfl⟩ : syracuseStep 3331523 = 4997285) B4997285
theorem B2221015 : Blo 2219435 2221015 := bstep (se 1 (by rfl) ⟨1665761, by rfl⟩ : syracuseStep 2221015 = 3331523) B3331523
theorem B5621957 : Blo 2219435 5621957 := bbase (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) (by norm_num)
theorem B3747971 : Blo 2219435 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B2498647 : Blo 2219435 2498647 := bstep (se 1 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 2498647 = 3747971) B3747971
theorem B3331529 : Blo 2219435 3331529 := bstep (se 2 (by rfl) ⟨1249323, by rfl⟩ : syracuseStep 3331529 = 2498647) B2498647
theorem B2221019 : Blo 2219435 2221019 := bstep (se 1 (by rfl) ⟨1665764, by rfl⟩ : syracuseStep 2221019 = 3331529) B3331529
theorem B18010613 : Blo 2219435 18010613 := bbase (se 5 (by rfl) ⟨844247, by rfl⟩ : syracuseStep 18010613 = 1688495) (by norm_num)
theorem B12007075 : Blo 2219435 12007075 := bstep (se 1 (by rfl) ⟨9005306, by rfl⟩ : syracuseStep 12007075 = 18010613) B18010613
theorem B16009433 : Blo 2219435 16009433 := bstep (se 2 (by rfl) ⟨6003537, by rfl⟩ : syracuseStep 16009433 = 12007075) B12007075
theorem B10672955 : Blo 2219435 10672955 := bstep (se 1 (by rfl) ⟨8004716, by rfl⟩ : syracuseStep 10672955 = 16009433) B16009433
theorem B7115303 : Blo 2219435 7115303 := bstep (se 1 (by rfl) ⟨5336477, by rfl⟩ : syracuseStep 7115303 = 10672955) B10672955
theorem B4743535 : Blo 2219435 4743535 := bstep (se 1 (by rfl) ⟨3557651, by rfl⟩ : syracuseStep 4743535 = 7115303) B7115303
theorem B6324713 : Blo 2219435 6324713 := bstep (se 2 (by rfl) ⟨2371767, by rfl⟩ : syracuseStep 6324713 = 4743535) B4743535
theorem B4216475 : Blo 2219435 4216475 := bstep (se 1 (by rfl) ⟨3162356, by rfl⟩ : syracuseStep 4216475 = 6324713) B6324713
theorem B11243933 : Blo 2219435 11243933 := bstep (se 3 (by rfl) ⟨2108237, by rfl⟩ : syracuseStep 11243933 = 4216475) B4216475
theorem B7495955 : Blo 2219435 7495955 := bstep (se 1 (by rfl) ⟨5621966, by rfl⟩ : syracuseStep 7495955 = 11243933) B11243933
theorem B4997303 : Blo 2219435 4997303 := bstep (se 1 (by rfl) ⟨3747977, by rfl⟩ : syracuseStep 4997303 = 7495955) B7495955
theorem B3331535 : Blo 2219435 3331535 := bstep (se 1 (by rfl) ⟨2498651, by rfl⟩ : syracuseStep 3331535 = 4997303) B4997303
theorem B2221023 : Blo 2219435 2221023 := bstep (se 1 (by rfl) ⟨1665767, by rfl⟩ : syracuseStep 2221023 = 3331535) B3331535
theorem B3331541 : Blo 2219435 3331541 := bbase (se 7 (by rfl) ⟨39041, by rfl⟩ : syracuseStep 3331541 = 78083) (by norm_num)
theorem B2221027 : Blo 2219435 2221027 := bstep (se 1 (by rfl) ⟨1665770, by rfl⟩ : syracuseStep 2221027 = 3331541) B3331541
theorem B8432981 : Blo 2219435 8432981 := bbase (se 11 (by rfl) ⟨6176, by rfl⟩ : syracuseStep 8432981 = 12353) (by norm_num)
theorem B5621987 : Blo 2219435 5621987 := bstep (se 1 (by rfl) ⟨4216490, by rfl⟩ : syracuseStep 5621987 = 8432981) B8432981
theorem B3747991 : Blo 2219435 3747991 := bstep (se 1 (by rfl) ⟨2810993, by rfl⟩ : syracuseStep 3747991 = 5621987) B5621987
theorem B4997321 : Blo 2219435 4997321 := bstep (se 2 (by rfl) ⟨1873995, by rfl⟩ : syracuseStep 4997321 = 3747991) B3747991
theorem B3331547 : Blo 2219435 3331547 := bstep (se 1 (by rfl) ⟨2498660, by rfl⟩ : syracuseStep 3331547 = 4997321) B4997321
theorem B2221031 : Blo 2219435 2221031 := bstep (se 1 (by rfl) ⟨1665773, by rfl⟩ : syracuseStep 2221031 = 3331547) B3331547
theorem B2498665 : Blo 2219435 2498665 := bbase (se 2 (by rfl) ⟨936999, by rfl⟩ : syracuseStep 2498665 = 1873999) (by norm_num)
theorem B3331553 : Blo 2219435 3331553 := bstep (se 2 (by rfl) ⟨1249332, by rfl⟩ : syracuseStep 3331553 = 2498665) B2498665
theorem B2221035 : Blo 2219435 2221035 := bstep (se 1 (by rfl) ⟨1665776, by rfl⟩ : syracuseStep 2221035 = 3331553) B3331553
theorem B3557677 : Blo 2219435 3557677 := bbase (se 3 (by rfl) ⟨667064, by rfl⟩ : syracuseStep 3557677 = 1334129) (by norm_num)
theorem B4743569 : Blo 2219435 4743569 := bstep (se 2 (by rfl) ⟨1778838, by rfl⟩ : syracuseStep 4743569 = 3557677) B3557677
theorem B12649517 : Blo 2219435 12649517 := bstep (se 3 (by rfl) ⟨2371784, by rfl⟩ : syracuseStep 12649517 = 4743569) B4743569
theorem B8433011 : Blo 2219435 8433011 := bstep (se 1 (by rfl) ⟨6324758, by rfl⟩ : syracuseStep 8433011 = 12649517) B12649517
theorem B5622007 : Blo 2219435 5622007 := bstep (se 1 (by rfl) ⟨4216505, by rfl⟩ : syracuseStep 5622007 = 8433011) B8433011
theorem B7496009 : Blo 2219435 7496009 := bstep (se 2 (by rfl) ⟨2811003, by rfl⟩ : syracuseStep 7496009 = 5622007) B5622007
theorem B4997339 : Blo 2219435 4997339 := bstep (se 1 (by rfl) ⟨3748004, by rfl⟩ : syracuseStep 4997339 = 7496009) B7496009
theorem B3331559 : Blo 2219435 3331559 := bstep (se 1 (by rfl) ⟨2498669, by rfl⟩ : syracuseStep 3331559 = 4997339) B4997339
theorem B2221039 : Blo 2219435 2221039 := bstep (se 1 (by rfl) ⟨1665779, by rfl⟩ : syracuseStep 2221039 = 3331559) B3331559
theorem B3331565 : Blo 2219435 3331565 := bbase (se 3 (by rfl) ⟨624668, by rfl⟩ : syracuseStep 3331565 = 1249337) (by norm_num)
theorem B2221043 : Blo 2219435 2221043 := bstep (se 1 (by rfl) ⟨1665782, by rfl⟩ : syracuseStep 2221043 = 3331565) B3331565
theorem B4997357 : Blo 2219435 4997357 := bbase (se 3 (by rfl) ⟨937004, by rfl⟩ : syracuseStep 4997357 = 1874009) (by norm_num)
theorem B3331571 : Blo 2219435 3331571 := bstep (se 1 (by rfl) ⟨2498678, by rfl⟩ : syracuseStep 3331571 = 4997357) B4997357
theorem B2221047 : Blo 2219435 2221047 := bstep (se 1 (by rfl) ⟨1665785, by rfl⟩ : syracuseStep 2221047 = 3331571) B3331571
theorem B3162397 : Blo 2219435 3162397 := bbase (se 3 (by rfl) ⟨592949, by rfl⟩ : syracuseStep 3162397 = 1185899) (by norm_num)
theorem B4216529 : Blo 2219435 4216529 := bstep (se 2 (by rfl) ⟨1581198, by rfl⟩ : syracuseStep 4216529 = 3162397) B3162397
theorem B2811019 : Blo 2219435 2811019 := bstep (se 1 (by rfl) ⟨2108264, by rfl⟩ : syracuseStep 2811019 = 4216529) B4216529
theorem B3748025 : Blo 2219435 3748025 := bstep (se 2 (by rfl) ⟨1405509, by rfl⟩ : syracuseStep 3748025 = 2811019) B2811019
theorem B2498683 : Blo 2219435 2498683 := bstep (se 1 (by rfl) ⟨1874012, by rfl⟩ : syracuseStep 2498683 = 3748025) B3748025
theorem B3331577 : Blo 2219435 3331577 := bstep (se 2 (by rfl) ⟨1249341, by rfl⟩ : syracuseStep 3331577 = 2498683) B2498683
theorem B2221051 : Blo 2219435 2221051 := bstep (se 1 (by rfl) ⟨1665788, by rfl⟩ : syracuseStep 2221051 = 3331577) B3331577
theorem B7212485 : Blo 2219435 7212485 := bbase (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) (by norm_num)
theorem B4808323 : Blo 2219435 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B6411097 : Blo 2219435 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B8548129 : Blo 2219435 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B11397505 : Blo 2219435 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B15196673 : Blo 2219435 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B10131115 : Blo 2219435 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B13508153 : Blo 2219435 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B9005435 : Blo 2219435 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B6003623 : Blo 2219435 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B4002415 : Blo 2219435 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B85384853 : Blo 2219435 85384853 := bstep (se 6 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 85384853 = 4002415) B4002415
theorem B56923235 : Blo 2219435 56923235 := bstep (se 1 (by rfl) ⟨42692426, by rfl⟩ : syracuseStep 56923235 = 85384853) B85384853
theorem B37948823 : Blo 2219435 37948823 := bstep (se 1 (by rfl) ⟨28461617, by rfl⟩ : syracuseStep 37948823 = 56923235) B56923235
theorem B25299215 : Blo 2219435 25299215 := bstep (se 1 (by rfl) ⟨18974411, by rfl⟩ : syracuseStep 25299215 = 37948823) B37948823
theorem B16866143 : Blo 2219435 16866143 := bstep (se 1 (by rfl) ⟨12649607, by rfl⟩ : syracuseStep 16866143 = 25299215) B25299215
theorem B11244095 : Blo 2219435 11244095 := bstep (se 1 (by rfl) ⟨8433071, by rfl⟩ : syracuseStep 11244095 = 16866143) B16866143
theorem B7496063 : Blo 2219435 7496063 := bstep (se 1 (by rfl) ⟨5622047, by rfl⟩ : syracuseStep 7496063 = 11244095) B11244095
theorem B4997375 : Blo 2219435 4997375 := bstep (se 1 (by rfl) ⟨3748031, by rfl⟩ : syracuseStep 4997375 = 7496063) B7496063
theorem B3331583 : Blo 2219435 3331583 := bstep (se 1 (by rfl) ⟨2498687, by rfl⟩ : syracuseStep 3331583 = 4997375) B4997375
theorem B2221055 : Blo 2219435 2221055 := bstep (se 1 (by rfl) ⟨1665791, by rfl⟩ : syracuseStep 2221055 = 3331583) B3331583
theorem B3331589 : Blo 2219435 3331589 := bbase (se 4 (by rfl) ⟨312336, by rfl⟩ : syracuseStep 3331589 = 624673) (by norm_num)
theorem B2221059 : Blo 2219435 2221059 := bstep (se 1 (by rfl) ⟨1665794, by rfl⟩ : syracuseStep 2221059 = 3331589) B3331589
theorem B3748045 : Blo 2219435 3748045 := bbase (se 3 (by rfl) ⟨702758, by rfl⟩ : syracuseStep 3748045 = 1405517) (by norm_num)
theorem B4997393 : Blo 2219435 4997393 := bstep (se 2 (by rfl) ⟨1874022, by rfl⟩ : syracuseStep 4997393 = 3748045) B3748045
theorem B3331595 : Blo 2219435 3331595 := bstep (se 1 (by rfl) ⟨2498696, by rfl⟩ : syracuseStep 3331595 = 4997393) B4997393
theorem B2221063 : Blo 2219435 2221063 := bstep (se 1 (by rfl) ⟨1665797, by rfl⟩ : syracuseStep 2221063 = 3331595) B3331595
theorem B2498701 : Blo 2219435 2498701 := bbase (se 3 (by rfl) ⟨468506, by rfl⟩ : syracuseStep 2498701 = 937013) (by norm_num)
theorem B3331601 : Blo 2219435 3331601 := bstep (se 2 (by rfl) ⟨1249350, by rfl⟩ : syracuseStep 3331601 = 2498701) B2498701
theorem B2221067 : Blo 2219435 2221067 := bstep (se 1 (by rfl) ⟨1665800, by rfl⟩ : syracuseStep 2221067 = 3331601) B3331601
theorem B7496117 : Blo 2219435 7496117 := bbase (se 5 (by rfl) ⟨351380, by rfl⟩ : syracuseStep 7496117 = 702761) (by norm_num)
theorem B4997411 : Blo 2219435 4997411 := bstep (se 1 (by rfl) ⟨3748058, by rfl⟩ : syracuseStep 4997411 = 7496117) B7496117
theorem B3331607 : Blo 2219435 3331607 := bstep (se 1 (by rfl) ⟨2498705, by rfl⟩ : syracuseStep 3331607 = 4997411) B4997411
theorem B2221071 : Blo 2219435 2221071 := bstep (se 1 (by rfl) ⟨1665803, by rfl⟩ : syracuseStep 2221071 = 3331607) B3331607
theorem B3331613 : Blo 2219435 3331613 := bbase (se 3 (by rfl) ⟨624677, by rfl⟩ : syracuseStep 3331613 = 1249355) (by norm_num)
theorem B2221075 : Blo 2219435 2221075 := bstep (se 1 (by rfl) ⟨1665806, by rfl⟩ : syracuseStep 2221075 = 3331613) B3331613
theorem B4997429 : Blo 2219435 4997429 := bbase (se 5 (by rfl) ⟨234254, by rfl⟩ : syracuseStep 4997429 = 468509) (by norm_num)
theorem B3331619 : Blo 2219435 3331619 := bstep (se 1 (by rfl) ⟨2498714, by rfl⟩ : syracuseStep 3331619 = 4997429) B4997429
theorem B2221079 : Blo 2219435 2221079 := bstep (se 1 (by rfl) ⟨1665809, by rfl⟩ : syracuseStep 2221079 = 3331619) B3331619
theorem B3205589 : Blo 2219435 3205589 := bbase (se 7 (by rfl) ⟨37565, by rfl⟩ : syracuseStep 3205589 = 75131) (by norm_num)
theorem B8548237 : Blo 2219435 8548237 := bstep (se 3 (by rfl) ⟨1602794, by rfl⟩ : syracuseStep 8548237 = 3205589) B3205589
theorem B45590597 : Blo 2219435 45590597 := bstep (se 4 (by rfl) ⟨4274118, by rfl⟩ : syracuseStep 45590597 = 8548237) B8548237
theorem B30393731 : Blo 2219435 30393731 := bstep (se 1 (by rfl) ⟨22795298, by rfl⟩ : syracuseStep 30393731 = 45590597) B45590597
theorem B20262487 : Blo 2219435 20262487 := bstep (se 1 (by rfl) ⟨15196865, by rfl⟩ : syracuseStep 20262487 = 30393731) B30393731
theorem B27016649 : Blo 2219435 27016649 := bstep (se 2 (by rfl) ⟨10131243, by rfl⟩ : syracuseStep 27016649 = 20262487) B20262487
theorem B18011099 : Blo 2219435 18011099 := bstep (se 1 (by rfl) ⟨13508324, by rfl⟩ : syracuseStep 18011099 = 27016649) B27016649
theorem B48029597 : Blo 2219435 48029597 := bstep (se 3 (by rfl) ⟨9005549, by rfl⟩ : syracuseStep 48029597 = 18011099) B18011099
theorem B32019731 : Blo 2219435 32019731 := bstep (se 1 (by rfl) ⟨24014798, by rfl⟩ : syracuseStep 32019731 = 48029597) B48029597
theorem B21346487 : Blo 2219435 21346487 := bstep (se 1 (by rfl) ⟨16009865, by rfl⟩ : syracuseStep 21346487 = 32019731) B32019731
theorem B14230991 : Blo 2219435 14230991 := bstep (se 1 (by rfl) ⟨10673243, by rfl⟩ : syracuseStep 14230991 = 21346487) B21346487
theorem B9487327 : Blo 2219435 9487327 := bstep (se 1 (by rfl) ⟨7115495, by rfl⟩ : syracuseStep 9487327 = 14230991) B14230991
theorem B12649769 : Blo 2219435 12649769 := bstep (se 2 (by rfl) ⟨4743663, by rfl⟩ : syracuseStep 12649769 = 9487327) B9487327
theorem B8433179 : Blo 2219435 8433179 := bstep (se 1 (by rfl) ⟨6324884, by rfl⟩ : syracuseStep 8433179 = 12649769) B12649769
theorem B5622119 : Blo 2219435 5622119 := bstep (se 1 (by rfl) ⟨4216589, by rfl⟩ : syracuseStep 5622119 = 8433179) B8433179
theorem B3748079 : Blo 2219435 3748079 := bstep (se 1 (by rfl) ⟨2811059, by rfl⟩ : syracuseStep 3748079 = 5622119) B5622119
theorem B2498719 : Blo 2219435 2498719 := bstep (se 1 (by rfl) ⟨1874039, by rfl⟩ : syracuseStep 2498719 = 3748079) B3748079
theorem B3331625 : Blo 2219435 3331625 := bstep (se 2 (by rfl) ⟨1249359, by rfl⟩ : syracuseStep 3331625 = 2498719) B2498719
theorem B2221083 : Blo 2219435 2221083 := bstep (se 1 (by rfl) ⟨1665812, by rfl⟩ : syracuseStep 2221083 = 3331625) B3331625
theorem B6085621 : Blo 2219435 6085621 := bbase (se 5 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 6085621 = 570527) (by norm_num)
theorem B32456645 : Blo 2219435 32456645 := bstep (se 4 (by rfl) ⟨3042810, by rfl⟩ : syracuseStep 32456645 = 6085621) B6085621
theorem B21637763 : Blo 2219435 21637763 := bstep (se 1 (by rfl) ⟨16228322, by rfl⟩ : syracuseStep 21637763 = 32456645) B32456645
theorem B14425175 : Blo 2219435 14425175 := bstep (se 1 (by rfl) ⟨10818881, by rfl⟩ : syracuseStep 14425175 = 21637763) B21637763
theorem B38467133 : Blo 2219435 38467133 := bstep (se 3 (by rfl) ⟨7212587, by rfl⟩ : syracuseStep 38467133 = 14425175) B14425175
theorem B25644755 : Blo 2219435 25644755 := bstep (se 1 (by rfl) ⟨19233566, by rfl⟩ : syracuseStep 25644755 = 38467133) B38467133
theorem B17096503 : Blo 2219435 17096503 := bstep (se 1 (by rfl) ⟨12822377, by rfl⟩ : syracuseStep 17096503 = 25644755) B25644755
theorem B22795337 : Blo 2219435 22795337 := bstep (se 2 (by rfl) ⟨8548251, by rfl⟩ : syracuseStep 22795337 = 17096503) B17096503
theorem B15196891 : Blo 2219435 15196891 := bstep (se 1 (by rfl) ⟨11397668, by rfl⟩ : syracuseStep 15196891 = 22795337) B22795337
theorem B20262521 : Blo 2219435 20262521 := bstep (se 2 (by rfl) ⟨7598445, by rfl⟩ : syracuseStep 20262521 = 15196891) B15196891
theorem B54033389 : Blo 2219435 54033389 := bstep (se 3 (by rfl) ⟨10131260, by rfl⟩ : syracuseStep 54033389 = 20262521) B20262521
theorem B36022259 : Blo 2219435 36022259 := bstep (se 1 (by rfl) ⟨27016694, by rfl⟩ : syracuseStep 36022259 = 54033389) B54033389
theorem B24014839 : Blo 2219435 24014839 := bstep (se 1 (by rfl) ⟨18011129, by rfl⟩ : syracuseStep 24014839 = 36022259) B36022259
theorem B32019785 : Blo 2219435 32019785 := bstep (se 2 (by rfl) ⟨12007419, by rfl⟩ : syracuseStep 32019785 = 24014839) B24014839
theorem B21346523 : Blo 2219435 21346523 := bstep (se 1 (by rfl) ⟨16009892, by rfl⟩ : syracuseStep 21346523 = 32019785) B32019785
theorem B14231015 : Blo 2219435 14231015 := bstep (se 1 (by rfl) ⟨10673261, by rfl⟩ : syracuseStep 14231015 = 21346523) B21346523
theorem B9487343 : Blo 2219435 9487343 := bstep (se 1 (by rfl) ⟨7115507, by rfl⟩ : syracuseStep 9487343 = 14231015) B14231015
theorem B6324895 : Blo 2219435 6324895 := bstep (se 1 (by rfl) ⟨4743671, by rfl⟩ : syracuseStep 6324895 = 9487343) B9487343
theorem B8433193 : Blo 2219435 8433193 := bstep (se 2 (by rfl) ⟨3162447, by rfl⟩ : syracuseStep 8433193 = 6324895) B6324895
theorem B11244257 : Blo 2219435 11244257 := bstep (se 2 (by rfl) ⟨4216596, by rfl⟩ : syracuseStep 11244257 = 8433193) B8433193
theorem B7496171 : Blo 2219435 7496171 := bstep (se 1 (by rfl) ⟨5622128, by rfl⟩ : syracuseStep 7496171 = 11244257) B11244257
theorem B4997447 : Blo 2219435 4997447 := bstep (se 1 (by rfl) ⟨3748085, by rfl⟩ : syracuseStep 4997447 = 7496171) B7496171
theorem B3331631 : Blo 2219435 3331631 := bstep (se 1 (by rfl) ⟨2498723, by rfl⟩ : syracuseStep 3331631 = 4997447) B4997447
theorem B2221087 : Blo 2219435 2221087 := bstep (se 1 (by rfl) ⟨1665815, by rfl⟩ : syracuseStep 2221087 = 3331631) B3331631
theorem B3331637 : Blo 2219435 3331637 := bbase (se 5 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 3331637 = 312341) (by norm_num)
theorem B2221091 : Blo 2219435 2221091 := bstep (se 1 (by rfl) ⟨1665818, by rfl⟩ : syracuseStep 2221091 = 3331637) B3331637
theorem B5622149 : Blo 2219435 5622149 := bbase (se 4 (by rfl) ⟨527076, by rfl⟩ : syracuseStep 5622149 = 1054153) (by norm_num)
theorem B3748099 : Blo 2219435 3748099 := bstep (se 1 (by rfl) ⟨2811074, by rfl⟩ : syracuseStep 3748099 = 5622149) B5622149
theorem B4997465 : Blo 2219435 4997465 := bstep (se 2 (by rfl) ⟨1874049, by rfl⟩ : syracuseStep 4997465 = 3748099) B3748099
theorem B3331643 : Blo 2219435 3331643 := bstep (se 1 (by rfl) ⟨2498732, by rfl⟩ : syracuseStep 3331643 = 4997465) B4997465
theorem B2221095 : Blo 2219435 2221095 := bstep (se 1 (by rfl) ⟨1665821, by rfl⟩ : syracuseStep 2221095 = 3331643) B3331643
theorem B2498737 : Blo 2219435 2498737 := bbase (se 2 (by rfl) ⟨937026, by rfl⟩ : syracuseStep 2498737 = 1874053) (by norm_num)
theorem B3331649 : Blo 2219435 3331649 := bstep (se 2 (by rfl) ⟨1249368, by rfl⟩ : syracuseStep 3331649 = 2498737) B2498737
theorem B2221099 : Blo 2219435 2221099 := bstep (se 1 (by rfl) ⟨1665824, by rfl⟩ : syracuseStep 2221099 = 3331649) B3331649
theorem B2371853 : Blo 2219435 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B6324941 : Blo 2219435 6324941 := bstep (se 3 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 6324941 = 2371853) B2371853
theorem B4216627 : Blo 2219435 4216627 := bstep (se 1 (by rfl) ⟨3162470, by rfl⟩ : syracuseStep 4216627 = 6324941) B6324941
theorem B5622169 : Blo 2219435 5622169 := bstep (se 2 (by rfl) ⟨2108313, by rfl⟩ : syracuseStep 5622169 = 4216627) B4216627
theorem B7496225 : Blo 2219435 7496225 := bstep (se 2 (by rfl) ⟨2811084, by rfl⟩ : syracuseStep 7496225 = 5622169) B5622169
theorem B4997483 : Blo 2219435 4997483 := bstep (se 1 (by rfl) ⟨3748112, by rfl⟩ : syracuseStep 4997483 = 7496225) B7496225
theorem B3331655 : Blo 2219435 3331655 := bstep (se 1 (by rfl) ⟨2498741, by rfl⟩ : syracuseStep 3331655 = 4997483) B4997483
theorem B2221103 : Blo 2219435 2221103 := bstep (se 1 (by rfl) ⟨1665827, by rfl⟩ : syracuseStep 2221103 = 3331655) B3331655
theorem B3331661 : Blo 2219435 3331661 := bbase (se 3 (by rfl) ⟨624686, by rfl⟩ : syracuseStep 3331661 = 1249373) (by norm_num)
theorem B2221107 : Blo 2219435 2221107 := bstep (se 1 (by rfl) ⟨1665830, by rfl⟩ : syracuseStep 2221107 = 3331661) B3331661
theorem B4997501 : Blo 2219435 4997501 := bbase (se 3 (by rfl) ⟨937031, by rfl⟩ : syracuseStep 4997501 = 1874063) (by norm_num)
theorem B3331667 : Blo 2219435 3331667 := bstep (se 1 (by rfl) ⟨2498750, by rfl⟩ : syracuseStep 3331667 = 4997501) B4997501
theorem B2221111 : Blo 2219435 2221111 := bstep (se 1 (by rfl) ⟨1665833, by rfl⟩ : syracuseStep 2221111 = 3331667) B3331667
theorem B3748133 : Blo 2219435 3748133 := bbase (se 4 (by rfl) ⟨351387, by rfl⟩ : syracuseStep 3748133 = 702775) (by norm_num)
theorem B2498755 : Blo 2219435 2498755 := bstep (se 1 (by rfl) ⟨1874066, by rfl⟩ : syracuseStep 2498755 = 3748133) B3748133
theorem B3331673 : Blo 2219435 3331673 := bstep (se 2 (by rfl) ⟨1249377, by rfl⟩ : syracuseStep 3331673 = 2498755) B2498755
theorem B2221115 : Blo 2219435 2221115 := bstep (se 1 (by rfl) ⟨1665836, by rfl⟩ : syracuseStep 2221115 = 3331673) B3331673
theorem B3162493 : Blo 2219435 3162493 := bbase (se 3 (by rfl) ⟨592967, by rfl⟩ : syracuseStep 3162493 = 1185935) (by norm_num)
theorem B16866629 : Blo 2219435 16866629 := bstep (se 4 (by rfl) ⟨1581246, by rfl⟩ : syracuseStep 16866629 = 3162493) B3162493
theorem B11244419 : Blo 2219435 11244419 := bstep (se 1 (by rfl) ⟨8433314, by rfl⟩ : syracuseStep 11244419 = 16866629) B16866629
theorem B7496279 : Blo 2219435 7496279 := bstep (se 1 (by rfl) ⟨5622209, by rfl⟩ : syracuseStep 7496279 = 11244419) B11244419
theorem B4997519 : Blo 2219435 4997519 := bstep (se 1 (by rfl) ⟨3748139, by rfl⟩ : syracuseStep 4997519 = 7496279) B7496279
theorem B3331679 : Blo 2219435 3331679 := bstep (se 1 (by rfl) ⟨2498759, by rfl⟩ : syracuseStep 3331679 = 4997519) B4997519
theorem B2221119 : Blo 2219435 2221119 := bstep (se 1 (by rfl) ⟨1665839, by rfl⟩ : syracuseStep 2221119 = 3331679) B3331679
theorem B3331685 : Blo 2219435 3331685 := bbase (se 4 (by rfl) ⟨312345, by rfl⟩ : syracuseStep 3331685 = 624691) (by norm_num)
theorem B2221123 : Blo 2219435 2221123 := bstep (se 1 (by rfl) ⟨1665842, by rfl⟩ : syracuseStep 2221123 = 3331685) B3331685
theorem B2251433 : Blo 2219435 2251433 := bbase (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) (by norm_num)
theorem B6003821 : Blo 2219435 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B4002547 : Blo 2219435 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B5336729 : Blo 2219435 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B3557819 : Blo 2219435 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B2371879 : Blo 2219435 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B3162505 : Blo 2219435 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B4216673 : Blo 2219435 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B2811115 : Blo 2219435 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B3748153 : Blo 2219435 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B4997537 : Blo 2219435 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B3331691 : Blo 2219435 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B2221127 : Blo 2219435 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B2498773 : Blo 2219435 2498773 := bbase (se 7 (by rfl) ⟨29282, by rfl⟩ : syracuseStep 2498773 = 58565) (by norm_num)
theorem B3331697 : Blo 2219435 3331697 := bstep (se 2 (by rfl) ⟨1249386, by rfl⟩ : syracuseStep 3331697 = 2498773) B2498773
theorem B2221131 : Blo 2219435 2221131 := bstep (se 1 (by rfl) ⟨1665848, by rfl⟩ : syracuseStep 2221131 = 3331697) B3331697
theorem B2811125 : Blo 2219435 2811125 := bbase (se 5 (by rfl) ⟨131771, by rfl⟩ : syracuseStep 2811125 = 263543) (by norm_num)
theorem B7496333 : Blo 2219435 7496333 := bstep (se 3 (by rfl) ⟨1405562, by rfl⟩ : syracuseStep 7496333 = 2811125) B2811125
theorem B4997555 : Blo 2219435 4997555 := bstep (se 1 (by rfl) ⟨3748166, by rfl⟩ : syracuseStep 4997555 = 7496333) B7496333
theorem B3331703 : Blo 2219435 3331703 := bstep (se 1 (by rfl) ⟨2498777, by rfl⟩ : syracuseStep 3331703 = 4997555) B4997555
theorem B2221135 : Blo 2219435 2221135 := bstep (se 1 (by rfl) ⟨1665851, by rfl⟩ : syracuseStep 2221135 = 3331703) B3331703
theorem B3331709 : Blo 2219435 3331709 := bbase (se 3 (by rfl) ⟨624695, by rfl⟩ : syracuseStep 3331709 = 1249391) (by norm_num)
theorem B2221139 : Blo 2219435 2221139 := bstep (se 1 (by rfl) ⟨1665854, by rfl⟩ : syracuseStep 2221139 = 3331709) B3331709
theorem B4997573 : Blo 2219435 4997573 := bbase (se 4 (by rfl) ⟨468522, by rfl⟩ : syracuseStep 4997573 = 937045) (by norm_num)
theorem B3331715 : Blo 2219435 3331715 := bstep (se 1 (by rfl) ⟨2498786, by rfl⟩ : syracuseStep 3331715 = 4997573) B4997573
theorem B2221143 : Blo 2219435 2221143 := bstep (se 1 (by rfl) ⟨1665857, by rfl⟩ : syracuseStep 2221143 = 3331715) B3331715
theorem B7115701 : Blo 2219435 7115701 := bbase (se 5 (by rfl) ⟨333548, by rfl⟩ : syracuseStep 7115701 = 667097) (by norm_num)
theorem B9487601 : Blo 2219435 9487601 := bstep (se 2 (by rfl) ⟨3557850, by rfl⟩ : syracuseStep 9487601 = 7115701) B7115701
theorem B6325067 : Blo 2219435 6325067 := bstep (se 1 (by rfl) ⟨4743800, by rfl⟩ : syracuseStep 6325067 = 9487601) B9487601
theorem B4216711 : Blo 2219435 4216711 := bstep (se 1 (by rfl) ⟨3162533, by rfl⟩ : syracuseStep 4216711 = 6325067) B6325067
theorem B5622281 : Blo 2219435 5622281 := bstep (se 2 (by rfl) ⟨2108355, by rfl⟩ : syracuseStep 5622281 = 4216711) B4216711
theorem B3748187 : Blo 2219435 3748187 := bstep (se 1 (by rfl) ⟨2811140, by rfl⟩ : syracuseStep 3748187 = 5622281) B5622281
theorem B2498791 : Blo 2219435 2498791 := bstep (se 1 (by rfl) ⟨1874093, by rfl⟩ : syracuseStep 2498791 = 3748187) B3748187
theorem B3331721 : Blo 2219435 3331721 := bstep (se 2 (by rfl) ⟨1249395, by rfl⟩ : syracuseStep 3331721 = 2498791) B2498791
theorem B2221147 : Blo 2219435 2221147 := bstep (se 1 (by rfl) ⟨1665860, by rfl⟩ : syracuseStep 2221147 = 3331721) B3331721
theorem B11244581 : Blo 2219435 11244581 := bbase (se 4 (by rfl) ⟨1054179, by rfl⟩ : syracuseStep 11244581 = 2108359) (by norm_num)
theorem B7496387 : Blo 2219435 7496387 := bstep (se 1 (by rfl) ⟨5622290, by rfl⟩ : syracuseStep 7496387 = 11244581) B11244581
theorem B4997591 : Blo 2219435 4997591 := bstep (se 1 (by rfl) ⟨3748193, by rfl⟩ : syracuseStep 4997591 = 7496387) B7496387
theorem B3331727 : Blo 2219435 3331727 := bstep (se 1 (by rfl) ⟨2498795, by rfl⟩ : syracuseStep 3331727 = 4997591) B4997591
theorem B2221151 : Blo 2219435 2221151 := bstep (se 1 (by rfl) ⟨1665863, by rfl⟩ : syracuseStep 2221151 = 3331727) B3331727
theorem B3331733 : Blo 2219435 3331733 := bbase (se 6 (by rfl) ⟨78087, by rfl⟩ : syracuseStep 3331733 = 156175) (by norm_num)
theorem B2221155 : Blo 2219435 2221155 := bstep (se 1 (by rfl) ⟨1665866, by rfl⟩ : syracuseStep 2221155 = 3331733) B3331733
theorem B14231477 : Blo 2219435 14231477 := bbase (se 5 (by rfl) ⟨667100, by rfl⟩ : syracuseStep 14231477 = 1334201) (by norm_num)
theorem B9487651 : Blo 2219435 9487651 := bstep (se 1 (by rfl) ⟨7115738, by rfl⟩ : syracuseStep 9487651 = 14231477) B14231477
theorem B12650201 : Blo 2219435 12650201 := bstep (se 2 (by rfl) ⟨4743825, by rfl⟩ : syracuseStep 12650201 = 9487651) B9487651
theorem B8433467 : Blo 2219435 8433467 := bstep (se 1 (by rfl) ⟨6325100, by rfl⟩ : syracuseStep 8433467 = 12650201) B12650201
theorem B5622311 : Blo 2219435 5622311 := bstep (se 1 (by rfl) ⟨4216733, by rfl⟩ : syracuseStep 5622311 = 8433467) B8433467
theorem B3748207 : Blo 2219435 3748207 := bstep (se 1 (by rfl) ⟨2811155, by rfl⟩ : syracuseStep 3748207 = 5622311) B5622311
theorem B4997609 : Blo 2219435 4997609 := bstep (se 2 (by rfl) ⟨1874103, by rfl⟩ : syracuseStep 4997609 = 3748207) B3748207
theorem B3331739 : Blo 2219435 3331739 := bstep (se 1 (by rfl) ⟨2498804, by rfl⟩ : syracuseStep 3331739 = 4997609) B4997609
theorem B2221159 : Blo 2219435 2221159 := bstep (se 1 (by rfl) ⟨1665869, by rfl⟩ : syracuseStep 2221159 = 3331739) B3331739
theorem B2498809 : Blo 2219435 2498809 := bbase (se 2 (by rfl) ⟨937053, by rfl⟩ : syracuseStep 2498809 = 1874107) (by norm_num)
theorem B3331745 : Blo 2219435 3331745 := bstep (se 2 (by rfl) ⟨1249404, by rfl⟩ : syracuseStep 3331745 = 2498809) B2498809
theorem B2221163 : Blo 2219435 2221163 := bstep (se 1 (by rfl) ⟨1665872, by rfl⟩ : syracuseStep 2221163 = 3331745) B3331745
theorem B9487685 : Blo 2219435 9487685 := bbase (se 4 (by rfl) ⟨889470, by rfl⟩ : syracuseStep 9487685 = 1778941) (by norm_num)
theorem B6325123 : Blo 2219435 6325123 := bstep (se 1 (by rfl) ⟨4743842, by rfl⟩ : syracuseStep 6325123 = 9487685) B9487685
theorem B8433497 : Blo 2219435 8433497 := bstep (se 2 (by rfl) ⟨3162561, by rfl⟩ : syracuseStep 8433497 = 6325123) B6325123
theorem B5622331 : Blo 2219435 5622331 := bstep (se 1 (by rfl) ⟨4216748, by rfl⟩ : syracuseStep 5622331 = 8433497) B8433497
theorem B7496441 : Blo 2219435 7496441 := bstep (se 2 (by rfl) ⟨2811165, by rfl⟩ : syracuseStep 7496441 = 5622331) B5622331
theorem B4997627 : Blo 2219435 4997627 := bstep (se 1 (by rfl) ⟨3748220, by rfl⟩ : syracuseStep 4997627 = 7496441) B7496441
theorem B3331751 : Blo 2219435 3331751 := bstep (se 1 (by rfl) ⟨2498813, by rfl⟩ : syracuseStep 3331751 = 4997627) B4997627
theorem B2221167 : Blo 2219435 2221167 := bstep (se 1 (by rfl) ⟨1665875, by rfl⟩ : syracuseStep 2221167 = 3331751) B3331751
theorem B3331757 : Blo 2219435 3331757 := bbase (se 3 (by rfl) ⟨624704, by rfl⟩ : syracuseStep 3331757 = 1249409) (by norm_num)
theorem B2221171 : Blo 2219435 2221171 := bstep (se 1 (by rfl) ⟨1665878, by rfl⟩ : syracuseStep 2221171 = 3331757) B3331757
theorem B4997645 : Blo 2219435 4997645 := bbase (se 3 (by rfl) ⟨937058, by rfl⟩ : syracuseStep 4997645 = 1874117) (by norm_num)
theorem B3331763 : Blo 2219435 3331763 := bstep (se 1 (by rfl) ⟨2498822, by rfl⟩ : syracuseStep 3331763 = 4997645) B4997645
theorem B2221175 : Blo 2219435 2221175 := bstep (se 1 (by rfl) ⟨1665881, by rfl⟩ : syracuseStep 2221175 = 3331763) B3331763
theorem B2811181 : Blo 2219435 2811181 := bbase (se 3 (by rfl) ⟨527096, by rfl⟩ : syracuseStep 2811181 = 1054193) (by norm_num)
theorem B3748241 : Blo 2219435 3748241 := bstep (se 2 (by rfl) ⟨1405590, by rfl⟩ : syracuseStep 3748241 = 2811181) B2811181
theorem B2498827 : Blo 2219435 2498827 := bstep (se 1 (by rfl) ⟨1874120, by rfl⟩ : syracuseStep 2498827 = 3748241) B3748241
theorem B3331769 : Blo 2219435 3331769 := bstep (se 2 (by rfl) ⟨1249413, by rfl⟩ : syracuseStep 3331769 = 2498827) B2498827
theorem B2221179 : Blo 2219435 2221179 := bstep (se 1 (by rfl) ⟨1665884, by rfl⟩ : syracuseStep 2221179 = 3331769) B3331769
theorem B5336861 : Blo 2219435 5336861 := bbase (se 3 (by rfl) ⟨1000661, by rfl⟩ : syracuseStep 5336861 = 2001323) (by norm_num)
theorem B14231629 : Blo 2219435 14231629 := bstep (se 3 (by rfl) ⟨2668430, by rfl⟩ : syracuseStep 14231629 = 5336861) B5336861
theorem B18975505 : Blo 2219435 18975505 := bstep (se 2 (by rfl) ⟨7115814, by rfl⟩ : syracuseStep 18975505 = 14231629) B14231629
theorem B25300673 : Blo 2219435 25300673 := bstep (se 2 (by rfl) ⟨9487752, by rfl⟩ : syracuseStep 25300673 = 18975505) B18975505
theorem B16867115 : Blo 2219435 16867115 := bstep (se 1 (by rfl) ⟨12650336, by rfl⟩ : syracuseStep 16867115 = 25300673) B25300673
theorem B11244743 : Blo 2219435 11244743 := bstep (se 1 (by rfl) ⟨8433557, by rfl⟩ : syracuseStep 11244743 = 16867115) B16867115
theorem B7496495 : Blo 2219435 7496495 := bstep (se 1 (by rfl) ⟨5622371, by rfl⟩ : syracuseStep 7496495 = 11244743) B11244743
theorem B4997663 : Blo 2219435 4997663 := bstep (se 1 (by rfl) ⟨3748247, by rfl⟩ : syracuseStep 4997663 = 7496495) B7496495
theorem B3331775 : Blo 2219435 3331775 := bstep (se 1 (by rfl) ⟨2498831, by rfl⟩ : syracuseStep 3331775 = 4997663) B4997663
theorem B2221183 : Blo 2219435 2221183 := bstep (se 1 (by rfl) ⟨1665887, by rfl⟩ : syracuseStep 2221183 = 3331775) B3331775
theorem B3331781 : Blo 2219435 3331781 := bbase (se 4 (by rfl) ⟨312354, by rfl⟩ : syracuseStep 3331781 = 624709) (by norm_num)
theorem B2221187 : Blo 2219435 2221187 := bstep (se 1 (by rfl) ⟨1665890, by rfl⟩ : syracuseStep 2221187 = 3331781) B3331781
theorem B3748261 : Blo 2219435 3748261 := bbase (se 4 (by rfl) ⟨351399, by rfl⟩ : syracuseStep 3748261 = 702799) (by norm_num)
theorem B4997681 : Blo 2219435 4997681 := bstep (se 2 (by rfl) ⟨1874130, by rfl⟩ : syracuseStep 4997681 = 3748261) B3748261
theorem B3331787 : Blo 2219435 3331787 := bstep (se 1 (by rfl) ⟨2498840, by rfl⟩ : syracuseStep 3331787 = 4997681) B4997681
theorem B2221191 : Blo 2219435 2221191 := bstep (se 1 (by rfl) ⟨1665893, by rfl⟩ : syracuseStep 2221191 = 3331787) B3331787
theorem B2498845 : Blo 2219435 2498845 := bbase (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) (by norm_num)
theorem B3331793 : Blo 2219435 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B2221195 : Blo 2219435 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B7496549 : Blo 2219435 7496549 := bbase (se 4 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 7496549 = 1405603) (by norm_num)
theorem B4997699 : Blo 2219435 4997699 := bstep (se 1 (by rfl) ⟨3748274, by rfl⟩ : syracuseStep 4997699 = 7496549) B7496549
theorem B3331799 : Blo 2219435 3331799 := bstep (se 1 (by rfl) ⟨2498849, by rfl⟩ : syracuseStep 3331799 = 4997699) B4997699
theorem B2221199 : Blo 2219435 2221199 := bstep (se 1 (by rfl) ⟨1665899, by rfl⟩ : syracuseStep 2221199 = 3331799) B3331799
theorem B3331805 : Blo 2219435 3331805 := bbase (se 3 (by rfl) ⟨624713, by rfl⟩ : syracuseStep 3331805 = 1249427) (by norm_num)
theorem B2221203 : Blo 2219435 2221203 := bstep (se 1 (by rfl) ⟨1665902, by rfl⟩ : syracuseStep 2221203 = 3331805) B3331805
theorem B4997717 : Blo 2219435 4997717 := bbase (se 8 (by rfl) ⟨29283, by rfl⟩ : syracuseStep 4997717 = 58567) (by norm_num)
theorem B3331811 : Blo 2219435 3331811 := bstep (se 1 (by rfl) ⟨2498858, by rfl⟩ : syracuseStep 3331811 = 4997717) B4997717
theorem B2221207 : Blo 2219435 2221207 := bstep (se 1 (by rfl) ⟨1665905, by rfl⟩ : syracuseStep 2221207 = 3331811) B3331811
theorem B2668465 : Blo 2219435 2668465 := bbase (se 2 (by rfl) ⟨1000674, by rfl⟩ : syracuseStep 2668465 = 2001349) (by norm_num)
theorem B3557953 : Blo 2219435 3557953 := bstep (se 2 (by rfl) ⟨1334232, by rfl⟩ : syracuseStep 3557953 = 2668465) B2668465
theorem B4743937 : Blo 2219435 4743937 := bstep (se 2 (by rfl) ⟨1778976, by rfl⟩ : syracuseStep 4743937 = 3557953) B3557953
theorem B6325249 : Blo 2219435 6325249 := bstep (se 2 (by rfl) ⟨2371968, by rfl⟩ : syracuseStep 6325249 = 4743937) B4743937
theorem B8433665 : Blo 2219435 8433665 := bstep (se 2 (by rfl) ⟨3162624, by rfl⟩ : syracuseStep 8433665 = 6325249) B6325249
theorem B5622443 : Blo 2219435 5622443 := bstep (se 1 (by rfl) ⟨4216832, by rfl⟩ : syracuseStep 5622443 = 8433665) B8433665
theorem B3748295 : Blo 2219435 3748295 := bstep (se 1 (by rfl) ⟨2811221, by rfl⟩ : syracuseStep 3748295 = 5622443) B5622443
theorem B2498863 : Blo 2219435 2498863 := bstep (se 1 (by rfl) ⟨1874147, by rfl⟩ : syracuseStep 2498863 = 3748295) B3748295
theorem B3331817 : Blo 2219435 3331817 := bstep (se 2 (by rfl) ⟨1249431, by rfl⟩ : syracuseStep 3331817 = 2498863) B2498863
theorem B2221211 : Blo 2219435 2221211 := bstep (se 1 (by rfl) ⟨1665908, by rfl⟩ : syracuseStep 2221211 = 3331817) B3331817
theorem B2668469 : Blo 2219435 2668469 := bbase (se 5 (by rfl) ⟨125084, by rfl⟩ : syracuseStep 2668469 = 250169) (by norm_num)
theorem B28463669 : Blo 2219435 28463669 := bstep (se 5 (by rfl) ⟨1334234, by rfl⟩ : syracuseStep 28463669 = 2668469) B2668469
theorem B18975779 : Blo 2219435 18975779 := bstep (se 1 (by rfl) ⟨14231834, by rfl⟩ : syracuseStep 18975779 = 28463669) B28463669
theorem B12650519 : Blo 2219435 12650519 := bstep (se 1 (by rfl) ⟨9487889, by rfl⟩ : syracuseStep 12650519 = 18975779) B18975779
theorem B8433679 : Blo 2219435 8433679 := bstep (se 1 (by rfl) ⟨6325259, by rfl⟩ : syracuseStep 8433679 = 12650519) B12650519
theorem B11244905 : Blo 2219435 11244905 := bstep (se 2 (by rfl) ⟨4216839, by rfl⟩ : syracuseStep 11244905 = 8433679) B8433679
theorem B7496603 : Blo 2219435 7496603 := bstep (se 1 (by rfl) ⟨5622452, by rfl⟩ : syracuseStep 7496603 = 11244905) B11244905
theorem B4997735 : Blo 2219435 4997735 := bstep (se 1 (by rfl) ⟨3748301, by rfl⟩ : syracuseStep 4997735 = 7496603) B7496603
theorem B3331823 : Blo 2219435 3331823 := bstep (se 1 (by rfl) ⟨2498867, by rfl⟩ : syracuseStep 3331823 = 4997735) B4997735
theorem B2221215 : Blo 2219435 2221215 := bstep (se 1 (by rfl) ⟨1665911, by rfl⟩ : syracuseStep 2221215 = 3331823) B3331823
theorem B3331829 : Blo 2219435 3331829 := bbase (se 5 (by rfl) ⟨156179, by rfl⟩ : syracuseStep 3331829 = 312359) (by norm_num)
theorem B2221219 : Blo 2219435 2221219 := bstep (se 1 (by rfl) ⟨1665914, by rfl⟩ : syracuseStep 2221219 = 3331829) B3331829
theorem B9487925 : Blo 2219435 9487925 := bbase (se 5 (by rfl) ⟨444746, by rfl⟩ : syracuseStep 9487925 = 889493) (by norm_num)
theorem B6325283 : Blo 2219435 6325283 := bstep (se 1 (by rfl) ⟨4743962, by rfl⟩ : syracuseStep 6325283 = 9487925) B9487925
theorem B4216855 : Blo 2219435 4216855 := bstep (se 1 (by rfl) ⟨3162641, by rfl⟩ : syracuseStep 4216855 = 6325283) B6325283
theorem B5622473 : Blo 2219435 5622473 := bstep (se 2 (by rfl) ⟨2108427, by rfl⟩ : syracuseStep 5622473 = 4216855) B4216855
theorem B3748315 : Blo 2219435 3748315 := bstep (se 1 (by rfl) ⟨2811236, by rfl⟩ : syracuseStep 3748315 = 5622473) B5622473
theorem B4997753 : Blo 2219435 4997753 := bstep (se 2 (by rfl) ⟨1874157, by rfl⟩ : syracuseStep 4997753 = 3748315) B3748315
theorem B3331835 : Blo 2219435 3331835 := bstep (se 1 (by rfl) ⟨2498876, by rfl⟩ : syracuseStep 3331835 = 4997753) B4997753
theorem B2221223 : Blo 2219435 2221223 := bstep (se 1 (by rfl) ⟨1665917, by rfl⟩ : syracuseStep 2221223 = 3331835) B3331835
theorem B2498881 : Blo 2219435 2498881 := bbase (se 2 (by rfl) ⟨937080, by rfl⟩ : syracuseStep 2498881 = 1874161) (by norm_num)
theorem B3331841 : Blo 2219435 3331841 := bstep (se 2 (by rfl) ⟨1249440, by rfl⟩ : syracuseStep 3331841 = 2498881) B2498881
theorem B2221227 : Blo 2219435 2221227 := bstep (se 1 (by rfl) ⟨1665920, by rfl⟩ : syracuseStep 2221227 = 3331841) B3331841
theorem B5622493 : Blo 2219435 5622493 := bbase (se 3 (by rfl) ⟨1054217, by rfl⟩ : syracuseStep 5622493 = 2108435) (by norm_num)
theorem B7496657 : Blo 2219435 7496657 := bstep (se 2 (by rfl) ⟨2811246, by rfl⟩ : syracuseStep 7496657 = 5622493) B5622493
theorem B4997771 : Blo 2219435 4997771 := bstep (se 1 (by rfl) ⟨3748328, by rfl⟩ : syracuseStep 4997771 = 7496657) B7496657
theorem B3331847 : Blo 2219435 3331847 := bstep (se 1 (by rfl) ⟨2498885, by rfl⟩ : syracuseStep 3331847 = 4997771) B4997771
theorem B2221231 : Blo 2219435 2221231 := bstep (se 1 (by rfl) ⟨1665923, by rfl⟩ : syracuseStep 2221231 = 3331847) B3331847
theorem B3331853 : Blo 2219435 3331853 := bbase (se 3 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 3331853 = 1249445) (by norm_num)
theorem B2221235 : Blo 2219435 2221235 := bstep (se 1 (by rfl) ⟨1665926, by rfl⟩ : syracuseStep 2221235 = 3331853) B3331853
theorem B4997789 : Blo 2219435 4997789 := bbase (se 3 (by rfl) ⟨937085, by rfl⟩ : syracuseStep 4997789 = 1874171) (by norm_num)
theorem B3331859 : Blo 2219435 3331859 := bstep (se 1 (by rfl) ⟨2498894, by rfl⟩ : syracuseStep 3331859 = 4997789) B4997789
theorem B2221239 : Blo 2219435 2221239 := bstep (se 1 (by rfl) ⟨1665929, by rfl⟩ : syracuseStep 2221239 = 3331859) B3331859
theorem B3748349 : Blo 2219435 3748349 := bbase (se 3 (by rfl) ⟨702815, by rfl⟩ : syracuseStep 3748349 = 1405631) (by norm_num)
theorem B2498899 : Blo 2219435 2498899 := bstep (se 1 (by rfl) ⟨1874174, by rfl⟩ : syracuseStep 2498899 = 3748349) B3748349
theorem B3331865 : Blo 2219435 3331865 := bstep (se 2 (by rfl) ⟨1249449, by rfl⟩ : syracuseStep 3331865 = 2498899) B2498899
theorem B2221243 : Blo 2219435 2221243 := bstep (se 1 (by rfl) ⟨1665932, by rfl⟩ : syracuseStep 2221243 = 3331865) B3331865
theorem B4744013 : Blo 2219435 4744013 := bbase (se 3 (by rfl) ⟨889502, by rfl⟩ : syracuseStep 4744013 = 1779005) (by norm_num)
theorem B12650701 : Blo 2219435 12650701 := bstep (se 3 (by rfl) ⟨2372006, by rfl⟩ : syracuseStep 12650701 = 4744013) B4744013
theorem B16867601 : Blo 2219435 16867601 := bstep (se 2 (by rfl) ⟨6325350, by rfl⟩ : syracuseStep 16867601 = 12650701) B12650701
theorem B11245067 : Blo 2219435 11245067 := bstep (se 1 (by rfl) ⟨8433800, by rfl⟩ : syracuseStep 11245067 = 16867601) B16867601
theorem B7496711 : Blo 2219435 7496711 := bstep (se 1 (by rfl) ⟨5622533, by rfl⟩ : syracuseStep 7496711 = 11245067) B11245067
theorem B4997807 : Blo 2219435 4997807 := bstep (se 1 (by rfl) ⟨3748355, by rfl⟩ : syracuseStep 4997807 = 7496711) B7496711
theorem B3331871 : Blo 2219435 3331871 := bstep (se 1 (by rfl) ⟨2498903, by rfl⟩ : syracuseStep 3331871 = 4997807) B4997807
theorem B2221247 : Blo 2219435 2221247 := bstep (se 1 (by rfl) ⟨1665935, by rfl⟩ : syracuseStep 2221247 = 3331871) B3331871
theorem B3331877 : Blo 2219435 3331877 := bbase (se 4 (by rfl) ⟨312363, by rfl⟩ : syracuseStep 3331877 = 624727) (by norm_num)
theorem B2221251 : Blo 2219435 2221251 := bstep (se 1 (by rfl) ⟨1665938, by rfl⟩ : syracuseStep 2221251 = 3331877) B3331877
theorem B2811277 : Blo 2219435 2811277 := bbase (se 3 (by rfl) ⟨527114, by rfl⟩ : syracuseStep 2811277 = 1054229) (by norm_num)
theorem B3748369 : Blo 2219435 3748369 := bstep (se 2 (by rfl) ⟨1405638, by rfl⟩ : syracuseStep 3748369 = 2811277) B2811277
theorem B4997825 : Blo 2219435 4997825 := bstep (se 2 (by rfl) ⟨1874184, by rfl⟩ : syracuseStep 4997825 = 3748369) B3748369
theorem B3331883 : Blo 2219435 3331883 := bstep (se 1 (by rfl) ⟨2498912, by rfl⟩ : syracuseStep 3331883 = 4997825) B4997825
theorem B2221255 : Blo 2219435 2221255 := bstep (se 1 (by rfl) ⟨1665941, by rfl⟩ : syracuseStep 2221255 = 3331883) B3331883
theorem B2498917 : Blo 2219435 2498917 := bbase (se 4 (by rfl) ⟨234273, by rfl⟩ : syracuseStep 2498917 = 468547) (by norm_num)
theorem B3331889 : Blo 2219435 3331889 := bstep (se 2 (by rfl) ⟨1249458, by rfl⟩ : syracuseStep 3331889 = 2498917) B2498917
theorem B2221259 : Blo 2219435 2221259 := bstep (se 1 (by rfl) ⟨1665944, by rfl⟩ : syracuseStep 2221259 = 3331889) B3331889
theorem B6325397 : Blo 2219435 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B4216931 : Blo 2219435 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2811287 : Blo 2219435 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B7496765 : Blo 2219435 7496765 := bstep (se 3 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 7496765 = 2811287) B2811287
theorem B4997843 : Blo 2219435 4997843 := bstep (se 1 (by rfl) ⟨3748382, by rfl⟩ : syracuseStep 4997843 = 7496765) B7496765
theorem B3331895 : Blo 2219435 3331895 := bstep (se 1 (by rfl) ⟨2498921, by rfl⟩ : syracuseStep 3331895 = 4997843) B4997843
theorem B2221263 : Blo 2219435 2221263 := bstep (se 1 (by rfl) ⟨1665947, by rfl⟩ : syracuseStep 2221263 = 3331895) B3331895
theorem B3331901 : Blo 2219435 3331901 := bbase (se 3 (by rfl) ⟨624731, by rfl⟩ : syracuseStep 3331901 = 1249463) (by norm_num)
theorem B2221267 : Blo 2219435 2221267 := bstep (se 1 (by rfl) ⟨1665950, by rfl⟩ : syracuseStep 2221267 = 3331901) B3331901
theorem B4997861 : Blo 2219435 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B3331907 : Blo 2219435 3331907 := bstep (se 1 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 3331907 = 4997861) B4997861
theorem B2221271 : Blo 2219435 2221271 := bstep (se 1 (by rfl) ⟨1665953, by rfl⟩ : syracuseStep 2221271 = 3331907) B3331907
theorem B5622605 : Blo 2219435 5622605 := bbase (se 3 (by rfl) ⟨1054238, by rfl⟩ : syracuseStep 5622605 = 2108477) (by norm_num)
theorem B3748403 : Blo 2219435 3748403 := bstep (se 1 (by rfl) ⟨2811302, by rfl⟩ : syracuseStep 3748403 = 5622605) B5622605
theorem B2498935 : Blo 2219435 2498935 := bstep (se 1 (by rfl) ⟨1874201, by rfl⟩ : syracuseStep 2498935 = 3748403) B3748403
theorem B3331913 : Blo 2219435 3331913 := bstep (se 2 (by rfl) ⟨1249467, by rfl⟩ : syracuseStep 3331913 = 2498935) B2498935
theorem B2221275 : Blo 2219435 2221275 := bstep (se 1 (by rfl) ⟨1665956, by rfl⟩ : syracuseStep 2221275 = 3331913) B3331913
theorem B2372041 : Blo 2219435 2372041 := bbase (se 2 (by rfl) ⟨889515, by rfl⟩ : syracuseStep 2372041 = 1779031) (by norm_num)
theorem B3162721 : Blo 2219435 3162721 := bstep (se 2 (by rfl) ⟨1186020, by rfl⟩ : syracuseStep 3162721 = 2372041) B2372041
theorem B4216961 : Blo 2219435 4216961 := bstep (se 2 (by rfl) ⟨1581360, by rfl⟩ : syracuseStep 4216961 = 3162721) B3162721
theorem B11245229 : Blo 2219435 11245229 := bstep (se 3 (by rfl) ⟨2108480, by rfl⟩ : syracuseStep 11245229 = 4216961) B4216961
theorem B7496819 : Blo 2219435 7496819 := bstep (se 1 (by rfl) ⟨5622614, by rfl⟩ : syracuseStep 7496819 = 11245229) B11245229
theorem B4997879 : Blo 2219435 4997879 := bstep (se 1 (by rfl) ⟨3748409, by rfl⟩ : syracuseStep 4997879 = 7496819) B7496819
theorem B3331919 : Blo 2219435 3331919 := bstep (se 1 (by rfl) ⟨2498939, by rfl⟩ : syracuseStep 3331919 = 4997879) B4997879
theorem B2221279 : Blo 2219435 2221279 := bstep (se 1 (by rfl) ⟨1665959, by rfl⟩ : syracuseStep 2221279 = 3331919) B3331919
theorem B3331925 : Blo 2219435 3331925 := bbase (se 9 (by rfl) ⟨9761, by rfl⟩ : syracuseStep 3331925 = 19523) (by norm_num)
theorem B2221283 : Blo 2219435 2221283 := bstep (se 1 (by rfl) ⟨1665962, by rfl⟩ : syracuseStep 2221283 = 3331925) B3331925
theorem B7116149 : Blo 2219435 7116149 := bbase (se 5 (by rfl) ⟨333569, by rfl⟩ : syracuseStep 7116149 = 667139) (by norm_num)
theorem B4744099 : Blo 2219435 4744099 := bstep (se 1 (by rfl) ⟨3558074, by rfl⟩ : syracuseStep 4744099 = 7116149) B7116149
theorem B6325465 : Blo 2219435 6325465 := bstep (se 2 (by rfl) ⟨2372049, by rfl⟩ : syracuseStep 6325465 = 4744099) B4744099
theorem B8433953 : Blo 2219435 8433953 := bstep (se 2 (by rfl) ⟨3162732, by rfl⟩ : syracuseStep 8433953 = 6325465) B6325465
theorem B5622635 : Blo 2219435 5622635 := bstep (se 1 (by rfl) ⟨4216976, by rfl⟩ : syracuseStep 5622635 = 8433953) B8433953
theorem B3748423 : Blo 2219435 3748423 := bstep (se 1 (by rfl) ⟨2811317, by rfl⟩ : syracuseStep 3748423 = 5622635) B5622635
theorem B4997897 : Blo 2219435 4997897 := bstep (se 2 (by rfl) ⟨1874211, by rfl⟩ : syracuseStep 4997897 = 3748423) B3748423
theorem B3331931 : Blo 2219435 3331931 := bstep (se 1 (by rfl) ⟨2498948, by rfl⟩ : syracuseStep 3331931 = 4997897) B4997897
theorem B2221287 : Blo 2219435 2221287 := bstep (se 1 (by rfl) ⟨1665965, by rfl⟩ : syracuseStep 2221287 = 3331931) B3331931
theorem B2498953 : Blo 2219435 2498953 := bbase (se 2 (by rfl) ⟨937107, by rfl⟩ : syracuseStep 2498953 = 1874215) (by norm_num)
theorem B3331937 : Blo 2219435 3331937 := bstep (se 2 (by rfl) ⟨1249476, by rfl⟩ : syracuseStep 3331937 = 2498953) B2498953
theorem B2221291 : Blo 2219435 2221291 := bstep (se 1 (by rfl) ⟨1665968, by rfl⟩ : syracuseStep 2221291 = 3331937) B3331937
theorem B4940957 : Blo 2219435 4940957 := bbase (se 3 (by rfl) ⟨926429, by rfl⟩ : syracuseStep 4940957 = 1852859) (by norm_num)
theorem B13175885 : Blo 2219435 13175885 := bstep (se 3 (by rfl) ⟨2470478, by rfl⟩ : syracuseStep 13175885 = 4940957) B4940957
theorem B8783923 : Blo 2219435 8783923 := bstep (se 1 (by rfl) ⟨6587942, by rfl⟩ : syracuseStep 8783923 = 13175885) B13175885
theorem B11711897 : Blo 2219435 11711897 := bstep (se 2 (by rfl) ⟨4391961, by rfl⟩ : syracuseStep 11711897 = 8783923) B8783923
theorem B7807931 : Blo 2219435 7807931 := bstep (se 1 (by rfl) ⟨5855948, by rfl⟩ : syracuseStep 7807931 = 11711897) B11711897
theorem B5205287 : Blo 2219435 5205287 := bstep (se 1 (by rfl) ⟨3903965, by rfl⟩ : syracuseStep 5205287 = 7807931) B7807931
theorem B3470191 : Blo 2219435 3470191 := bstep (se 1 (by rfl) ⟨2602643, by rfl⟩ : syracuseStep 3470191 = 5205287) B5205287
theorem B18507685 : Blo 2219435 18507685 := bstep (se 4 (by rfl) ⟨1735095, by rfl⟩ : syracuseStep 18507685 = 3470191) B3470191
theorem B24676913 : Blo 2219435 24676913 := bstep (se 2 (by rfl) ⟨9253842, by rfl⟩ : syracuseStep 24676913 = 18507685) B18507685
theorem B16451275 : Blo 2219435 16451275 := bstep (se 1 (by rfl) ⟨12338456, by rfl⟩ : syracuseStep 16451275 = 24676913) B24676913
theorem B21935033 : Blo 2219435 21935033 := bstep (se 2 (by rfl) ⟨8225637, by rfl⟩ : syracuseStep 21935033 = 16451275) B16451275
theorem B14623355 : Blo 2219435 14623355 := bstep (se 1 (by rfl) ⟨10967516, by rfl⟩ : syracuseStep 14623355 = 21935033) B21935033
theorem B38995613 : Blo 2219435 38995613 := bstep (se 3 (by rfl) ⟨7311677, by rfl⟩ : syracuseStep 38995613 = 14623355) B14623355
theorem B25997075 : Blo 2219435 25997075 := bstep (se 1 (by rfl) ⟨19497806, by rfl⟩ : syracuseStep 25997075 = 38995613) B38995613
theorem B17331383 : Blo 2219435 17331383 := bstep (se 1 (by rfl) ⟨12998537, by rfl⟩ : syracuseStep 17331383 = 25997075) B25997075
theorem B11554255 : Blo 2219435 11554255 := bstep (se 1 (by rfl) ⟨8665691, by rfl⟩ : syracuseStep 11554255 = 17331383) B17331383
theorem B15405673 : Blo 2219435 15405673 := bstep (se 2 (by rfl) ⟨5777127, by rfl⟩ : syracuseStep 15405673 = 11554255) B11554255
theorem B20540897 : Blo 2219435 20540897 := bstep (se 2 (by rfl) ⟨7702836, by rfl⟩ : syracuseStep 20540897 = 15405673) B15405673
theorem B13693931 : Blo 2219435 13693931 := bstep (se 1 (by rfl) ⟨10270448, by rfl⟩ : syracuseStep 13693931 = 20540897) B20540897
theorem B9129287 : Blo 2219435 9129287 := bstep (se 1 (by rfl) ⟨6846965, by rfl⟩ : syracuseStep 9129287 = 13693931) B13693931
theorem B6086191 : Blo 2219435 6086191 := bstep (se 1 (by rfl) ⟨4564643, by rfl⟩ : syracuseStep 6086191 = 9129287) B9129287
theorem B8114921 : Blo 2219435 8114921 := bstep (se 2 (by rfl) ⟨3043095, by rfl⟩ : syracuseStep 8114921 = 6086191) B6086191
theorem B5409947 : Blo 2219435 5409947 := bstep (se 1 (by rfl) ⟨4057460, by rfl⟩ : syracuseStep 5409947 = 8114921) B8114921
theorem B14426525 : Blo 2219435 14426525 := bstep (se 3 (by rfl) ⟨2704973, by rfl⟩ : syracuseStep 14426525 = 5409947) B5409947
theorem B9617683 : Blo 2219435 9617683 := bstep (se 1 (by rfl) ⟨7213262, by rfl⟩ : syracuseStep 9617683 = 14426525) B14426525
theorem B12823577 : Blo 2219435 12823577 := bstep (se 2 (by rfl) ⟨4808841, by rfl⟩ : syracuseStep 12823577 = 9617683) B9617683
theorem B136784821 : Blo 2219435 136784821 := bstep (se 5 (by rfl) ⟨6411788, by rfl⟩ : syracuseStep 136784821 = 12823577) B12823577
theorem B182379761 : Blo 2219435 182379761 := bstep (se 2 (by rfl) ⟨68392410, by rfl⟩ : syracuseStep 182379761 = 136784821) B136784821
theorem B121586507 : Blo 2219435 121586507 := bstep (se 1 (by rfl) ⟨91189880, by rfl⟩ : syracuseStep 121586507 = 182379761) B182379761
theorem B81057671 : Blo 2219435 81057671 := bstep (se 1 (by rfl) ⟨60793253, by rfl⟩ : syracuseStep 81057671 = 121586507) B121586507
theorem B54038447 : Blo 2219435 54038447 := bstep (se 1 (by rfl) ⟨40528835, by rfl⟩ : syracuseStep 54038447 = 81057671) B81057671
theorem B36025631 : Blo 2219435 36025631 := bstep (se 1 (by rfl) ⟨27019223, by rfl⟩ : syracuseStep 36025631 = 54038447) B54038447
theorem B24017087 : Blo 2219435 24017087 := bstep (se 1 (by rfl) ⟨18012815, by rfl⟩ : syracuseStep 24017087 = 36025631) B36025631
theorem B64045565 : Blo 2219435 64045565 := bstep (se 3 (by rfl) ⟨12008543, by rfl⟩ : syracuseStep 64045565 = 24017087) B24017087
theorem B42697043 : Blo 2219435 42697043 := bstep (se 1 (by rfl) ⟨32022782, by rfl⟩ : syracuseStep 42697043 = 64045565) B64045565
theorem B28464695 : Blo 2219435 28464695 := bstep (se 1 (by rfl) ⟨21348521, by rfl⟩ : syracuseStep 28464695 = 42697043) B42697043
theorem B18976463 : Blo 2219435 18976463 := bstep (se 1 (by rfl) ⟨14232347, by rfl⟩ : syracuseStep 18976463 = 28464695) B28464695
theorem B12650975 : Blo 2219435 12650975 := bstep (se 1 (by rfl) ⟨9488231, by rfl⟩ : syracuseStep 12650975 = 18976463) B18976463
theorem B8433983 : Blo 2219435 8433983 := bstep (se 1 (by rfl) ⟨6325487, by rfl⟩ : syracuseStep 8433983 = 12650975) B12650975
theorem B5622655 : Blo 2219435 5622655 := bstep (se 1 (by rfl) ⟨4216991, by rfl⟩ : syracuseStep 5622655 = 8433983) B8433983
theorem B7496873 : Blo 2219435 7496873 := bstep (se 2 (by rfl) ⟨2811327, by rfl⟩ : syracuseStep 7496873 = 5622655) B5622655
theorem B4997915 : Blo 2219435 4997915 := bstep (se 1 (by rfl) ⟨3748436, by rfl⟩ : syracuseStep 4997915 = 7496873) B7496873
theorem B3331943 : Blo 2219435 3331943 := bstep (se 1 (by rfl) ⟨2498957, by rfl⟩ : syracuseStep 3331943 = 4997915) B4997915
theorem B2221295 : Blo 2219435 2221295 := bstep (se 1 (by rfl) ⟨1665971, by rfl⟩ : syracuseStep 2221295 = 3331943) B3331943
theorem B3331949 : Blo 2219435 3331949 := bbase (se 3 (by rfl) ⟨624740, by rfl⟩ : syracuseStep 3331949 = 1249481) (by norm_num)
theorem B2221299 : Blo 2219435 2221299 := bstep (se 1 (by rfl) ⟨1665974, by rfl⟩ : syracuseStep 2221299 = 3331949) B3331949
theorem B4997933 : Blo 2219435 4997933 := bbase (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) (by norm_num)
theorem B3331955 : Blo 2219435 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B2221303 : Blo 2219435 2221303 := bstep (se 1 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 2221303 = 3331955) B3331955
theorem B11398805 : Blo 2219435 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B7599203 : Blo 2219435 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B5066135 : Blo 2219435 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B3377423 : Blo 2219435 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B9006461 : Blo 2219435 9006461 := bstep (se 3 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 9006461 = 3377423) B3377423
theorem B6004307 : Blo 2219435 6004307 := bstep (se 1 (by rfl) ⟨4503230, by rfl⟩ : syracuseStep 6004307 = 9006461) B9006461
theorem B4002871 : Blo 2219435 4002871 := bstep (se 1 (by rfl) ⟨3002153, by rfl⟩ : syracuseStep 4002871 = 6004307) B6004307
theorem B5337161 : Blo 2219435 5337161 := bstep (se 2 (by rfl) ⟨2001435, by rfl⟩ : syracuseStep 5337161 = 4002871) B4002871
theorem B3558107 : Blo 2219435 3558107 := bstep (se 1 (by rfl) ⟨2668580, by rfl⟩ : syracuseStep 3558107 = 5337161) B5337161
theorem B9488285 : Blo 2219435 9488285 := bstep (se 3 (by rfl) ⟨1779053, by rfl⟩ : syracuseStep 9488285 = 3558107) B3558107
theorem B6325523 : Blo 2219435 6325523 := bstep (se 1 (by rfl) ⟨4744142, by rfl⟩ : syracuseStep 6325523 = 9488285) B9488285
theorem B4217015 : Blo 2219435 4217015 := bstep (se 1 (by rfl) ⟨3162761, by rfl⟩ : syracuseStep 4217015 = 6325523) B6325523
theorem B2811343 : Blo 2219435 2811343 := bstep (se 1 (by rfl) ⟨2108507, by rfl⟩ : syracuseStep 2811343 = 4217015) B4217015
theorem B3748457 : Blo 2219435 3748457 := bstep (se 2 (by rfl) ⟨1405671, by rfl⟩ : syracuseStep 3748457 = 2811343) B2811343
theorem B2498971 : Blo 2219435 2498971 := bstep (se 1 (by rfl) ⟨1874228, by rfl⟩ : syracuseStep 2498971 = 3748457) B3748457
theorem B3331961 : Blo 2219435 3331961 := bstep (se 2 (by rfl) ⟨1249485, by rfl⟩ : syracuseStep 3331961 = 2498971) B2498971
theorem B2221307 : Blo 2219435 2221307 := bstep (se 1 (by rfl) ⟨1665980, by rfl⟩ : syracuseStep 2221307 = 3331961) B3331961
theorem B17098229 : Blo 2219435 17098229 := bbase (se 5 (by rfl) ⟨801479, by rfl⟩ : syracuseStep 17098229 = 1602959) (by norm_num)
theorem B11398819 : Blo 2219435 11398819 := bstep (se 1 (by rfl) ⟨8549114, by rfl⟩ : syracuseStep 11398819 = 17098229) B17098229
theorem B15198425 : Blo 2219435 15198425 := bstep (se 2 (by rfl) ⟨5699409, by rfl⟩ : syracuseStep 15198425 = 11398819) B11398819
theorem B10132283 : Blo 2219435 10132283 := bstep (se 1 (by rfl) ⟨7599212, by rfl⟩ : syracuseStep 10132283 = 15198425) B15198425
theorem B6754855 : Blo 2219435 6754855 := bstep (se 1 (by rfl) ⟨5066141, by rfl⟩ : syracuseStep 6754855 = 10132283) B10132283
theorem B9006473 : Blo 2219435 9006473 := bstep (se 2 (by rfl) ⟨3377427, by rfl⟩ : syracuseStep 9006473 = 6754855) B6754855
theorem B6004315 : Blo 2219435 6004315 := bstep (se 1 (by rfl) ⟨4503236, by rfl⟩ : syracuseStep 6004315 = 9006473) B9006473
theorem B8005753 : Blo 2219435 8005753 := bstep (se 2 (by rfl) ⟨3002157, by rfl⟩ : syracuseStep 8005753 = 6004315) B6004315
theorem B10674337 : Blo 2219435 10674337 := bstep (se 2 (by rfl) ⟨4002876, by rfl⟩ : syracuseStep 10674337 = 8005753) B8005753
theorem B14232449 : Blo 2219435 14232449 := bstep (se 2 (by rfl) ⟨5337168, by rfl⟩ : syracuseStep 14232449 = 10674337) B10674337
theorem B37953197 : Blo 2219435 37953197 := bstep (se 3 (by rfl) ⟨7116224, by rfl⟩ : syracuseStep 37953197 = 14232449) B14232449
theorem B25302131 : Blo 2219435 25302131 := bstep (se 1 (by rfl) ⟨18976598, by rfl⟩ : syracuseStep 25302131 = 37953197) B37953197
theorem B16868087 : Blo 2219435 16868087 := bstep (se 1 (by rfl) ⟨12651065, by rfl⟩ : syracuseStep 16868087 = 25302131) B25302131
theorem B11245391 : Blo 2219435 11245391 := bstep (se 1 (by rfl) ⟨8434043, by rfl⟩ : syracuseStep 11245391 = 16868087) B16868087
theorem B7496927 : Blo 2219435 7496927 := bstep (se 1 (by rfl) ⟨5622695, by rfl⟩ : syracuseStep 7496927 = 11245391) B11245391
theorem B4997951 : Blo 2219435 4997951 := bstep (se 1 (by rfl) ⟨3748463, by rfl⟩ : syracuseStep 4997951 = 7496927) B7496927
theorem B3331967 : Blo 2219435 3331967 := bstep (se 1 (by rfl) ⟨2498975, by rfl⟩ : syracuseStep 3331967 = 4997951) B4997951
theorem B2221311 : Blo 2219435 2221311 := bstep (se 1 (by rfl) ⟨1665983, by rfl⟩ : syracuseStep 2221311 = 3331967) B3331967
theorem B3331973 : Blo 2219435 3331973 := bbase (se 4 (by rfl) ⟨312372, by rfl⟩ : syracuseStep 3331973 = 624745) (by norm_num)
theorem B2221315 : Blo 2219435 2221315 := bstep (se 1 (by rfl) ⟨1665986, by rfl⟩ : syracuseStep 2221315 = 3331973) B3331973
theorem B3748477 : Blo 2219435 3748477 := bbase (se 3 (by rfl) ⟨702839, by rfl⟩ : syracuseStep 3748477 = 1405679) (by norm_num)
theorem B4997969 : Blo 2219435 4997969 := bstep (se 2 (by rfl) ⟨1874238, by rfl⟩ : syracuseStep 4997969 = 3748477) B3748477
theorem B3331979 : Blo 2219435 3331979 := bstep (se 1 (by rfl) ⟨2498984, by rfl⟩ : syracuseStep 3331979 = 4997969) B4997969
theorem B2221319 : Blo 2219435 2221319 := bstep (se 1 (by rfl) ⟨1665989, by rfl⟩ : syracuseStep 2221319 = 3331979) B3331979
theorem B2498989 : Blo 2219435 2498989 := bbase (se 3 (by rfl) ⟨468560, by rfl⟩ : syracuseStep 2498989 = 937121) (by norm_num)
theorem B3331985 : Blo 2219435 3331985 := bstep (se 2 (by rfl) ⟨1249494, by rfl⟩ : syracuseStep 3331985 = 2498989) B2498989
theorem B2221323 : Blo 2219435 2221323 := bstep (se 1 (by rfl) ⟨1665992, by rfl⟩ : syracuseStep 2221323 = 3331985) B3331985
theorem B7496981 : Blo 2219435 7496981 := bbase (se 6 (by rfl) ⟨175710, by rfl⟩ : syracuseStep 7496981 = 351421) (by norm_num)
theorem B4997987 : Blo 2219435 4997987 := bstep (se 1 (by rfl) ⟨3748490, by rfl⟩ : syracuseStep 4997987 = 7496981) B7496981
theorem B3331991 : Blo 2219435 3331991 := bstep (se 1 (by rfl) ⟨2498993, by rfl⟩ : syracuseStep 3331991 = 4997987) B4997987
theorem B2221327 : Blo 2219435 2221327 := bstep (se 1 (by rfl) ⟨1665995, by rfl⟩ : syracuseStep 2221327 = 3331991) B3331991
theorem B3331997 : Blo 2219435 3331997 := bbase (se 3 (by rfl) ⟨624749, by rfl⟩ : syracuseStep 3331997 = 1249499) (by norm_num)
theorem B2221331 : Blo 2219435 2221331 := bstep (se 1 (by rfl) ⟨1665998, by rfl⟩ : syracuseStep 2221331 = 3331997) B3331997
theorem B4998005 : Blo 2219435 4998005 := bbase (se 5 (by rfl) ⟨234281, by rfl⟩ : syracuseStep 4998005 = 468563) (by norm_num)
theorem B3332003 : Blo 2219435 3332003 := bstep (se 1 (by rfl) ⟨2499002, by rfl⟩ : syracuseStep 3332003 = 4998005) B4998005
theorem B2221335 : Blo 2219435 2221335 := bstep (se 1 (by rfl) ⟨1666001, by rfl⟩ : syracuseStep 2221335 = 3332003) B3332003
theorem B2404469 : Blo 2219435 2404469 := bbase (se 5 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 2404469 = 225419) (by norm_num)
theorem B6411917 : Blo 2219435 6411917 := bstep (se 3 (by rfl) ⟨1202234, by rfl⟩ : syracuseStep 6411917 = 2404469) B2404469
theorem B17098445 : Blo 2219435 17098445 := bstep (se 3 (by rfl) ⟨3205958, by rfl⟩ : syracuseStep 17098445 = 6411917) B6411917
theorem B11398963 : Blo 2219435 11398963 := bstep (se 1 (by rfl) ⟨8549222, by rfl⟩ : syracuseStep 11398963 = 17098445) B17098445
theorem B15198617 : Blo 2219435 15198617 := bstep (se 2 (by rfl) ⟨5699481, by rfl⟩ : syracuseStep 15198617 = 11398963) B11398963
theorem B40529645 : Blo 2219435 40529645 := bstep (se 3 (by rfl) ⟨7599308, by rfl⟩ : syracuseStep 40529645 = 15198617) B15198617
theorem B27019763 : Blo 2219435 27019763 := bstep (se 1 (by rfl) ⟨20264822, by rfl⟩ : syracuseStep 27019763 = 40529645) B40529645
theorem B18013175 : Blo 2219435 18013175 := bstep (se 1 (by rfl) ⟨13509881, by rfl⟩ : syracuseStep 18013175 = 27019763) B27019763
theorem B12008783 : Blo 2219435 12008783 := bstep (se 1 (by rfl) ⟨9006587, by rfl⟩ : syracuseStep 12008783 = 18013175) B18013175
theorem B32023421 : Blo 2219435 32023421 := bstep (se 3 (by rfl) ⟨6004391, by rfl⟩ : syracuseStep 32023421 = 12008783) B12008783
theorem B21348947 : Blo 2219435 21348947 := bstep (se 1 (by rfl) ⟨16011710, by rfl⟩ : syracuseStep 21348947 = 32023421) B32023421
theorem B14232631 : Blo 2219435 14232631 := bstep (se 1 (by rfl) ⟨10674473, by rfl⟩ : syracuseStep 14232631 = 21348947) B21348947
theorem B18976841 : Blo 2219435 18976841 := bstep (se 2 (by rfl) ⟨7116315, by rfl⟩ : syracuseStep 18976841 = 14232631) B14232631
theorem B12651227 : Blo 2219435 12651227 := bstep (se 1 (by rfl) ⟨9488420, by rfl⟩ : syracuseStep 12651227 = 18976841) B18976841
theorem B8434151 : Blo 2219435 8434151 := bstep (se 1 (by rfl) ⟨6325613, by rfl⟩ : syracuseStep 8434151 = 12651227) B12651227
theorem B5622767 : Blo 2219435 5622767 := bstep (se 1 (by rfl) ⟨4217075, by rfl⟩ : syracuseStep 5622767 = 8434151) B8434151
theorem B3748511 : Blo 2219435 3748511 := bstep (se 1 (by rfl) ⟨2811383, by rfl⟩ : syracuseStep 3748511 = 5622767) B5622767
theorem B2499007 : Blo 2219435 2499007 := bstep (se 1 (by rfl) ⟨1874255, by rfl⟩ : syracuseStep 2499007 = 3748511) B3748511
theorem B3332009 : Blo 2219435 3332009 := bstep (se 2 (by rfl) ⟨1249503, by rfl⟩ : syracuseStep 3332009 = 2499007) B2499007
theorem B2221339 : Blo 2219435 2221339 := bstep (se 1 (by rfl) ⟨1666004, by rfl⟩ : syracuseStep 2221339 = 3332009) B3332009
theorem B8434165 : Blo 2219435 8434165 := bbase (se 5 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 8434165 = 790703) (by norm_num)
theorem B11245553 : Blo 2219435 11245553 := bstep (se 2 (by rfl) ⟨4217082, by rfl⟩ : syracuseStep 11245553 = 8434165) B8434165
theorem B7497035 : Blo 2219435 7497035 := bstep (se 1 (by rfl) ⟨5622776, by rfl⟩ : syracuseStep 7497035 = 11245553) B11245553
theorem B4998023 : Blo 2219435 4998023 := bstep (se 1 (by rfl) ⟨3748517, by rfl⟩ : syracuseStep 4998023 = 7497035) B7497035
theorem B3332015 : Blo 2219435 3332015 := bstep (se 1 (by rfl) ⟨2499011, by rfl⟩ : syracuseStep 3332015 = 4998023) B4998023
theorem B2221343 : Blo 2219435 2221343 := bstep (se 1 (by rfl) ⟨1666007, by rfl⟩ : syracuseStep 2221343 = 3332015) B3332015
theorem B3332021 : Blo 2219435 3332021 := bbase (se 5 (by rfl) ⟨156188, by rfl⟩ : syracuseStep 3332021 = 312377) (by norm_num)
theorem B2221347 : Blo 2219435 2221347 := bstep (se 1 (by rfl) ⟨1666010, by rfl⟩ : syracuseStep 2221347 = 3332021) B3332021
theorem B5622797 : Blo 2219435 5622797 := bbase (se 3 (by rfl) ⟨1054274, by rfl⟩ : syracuseStep 5622797 = 2108549) (by norm_num)
theorem B3748531 : Blo 2219435 3748531 := bstep (se 1 (by rfl) ⟨2811398, by rfl⟩ : syracuseStep 3748531 = 5622797) B5622797
theorem B4998041 : Blo 2219435 4998041 := bstep (se 2 (by rfl) ⟨1874265, by rfl⟩ : syracuseStep 4998041 = 3748531) B3748531
theorem B3332027 : Blo 2219435 3332027 := bstep (se 1 (by rfl) ⟨2499020, by rfl⟩ : syracuseStep 3332027 = 4998041) B4998041
theorem B2221351 : Blo 2219435 2221351 := bstep (se 1 (by rfl) ⟨1666013, by rfl⟩ : syracuseStep 2221351 = 3332027) B3332027
theorem B2499025 : Blo 2219435 2499025 := bbase (se 2 (by rfl) ⟨937134, by rfl⟩ : syracuseStep 2499025 = 1874269) (by norm_num)
theorem B3332033 : Blo 2219435 3332033 := bstep (se 2 (by rfl) ⟨1249512, by rfl⟩ : syracuseStep 3332033 = 2499025) B2499025
theorem B2221355 : Blo 2219435 2221355 := bstep (se 1 (by rfl) ⟨1666016, by rfl⟩ : syracuseStep 2221355 = 3332033) B3332033
theorem B4744253 : Blo 2219435 4744253 := bbase (se 3 (by rfl) ⟨889547, by rfl⟩ : syracuseStep 4744253 = 1779095) (by norm_num)
theorem B3162835 : Blo 2219435 3162835 := bstep (se 1 (by rfl) ⟨2372126, by rfl⟩ : syracuseStep 3162835 = 4744253) B4744253
theorem B4217113 : Blo 2219435 4217113 := bstep (se 2 (by rfl) ⟨1581417, by rfl⟩ : syracuseStep 4217113 = 3162835) B3162835
theorem B5622817 : Blo 2219435 5622817 := bstep (se 2 (by rfl) ⟨2108556, by rfl⟩ : syracuseStep 5622817 = 4217113) B4217113
theorem B7497089 : Blo 2219435 7497089 := bstep (se 2 (by rfl) ⟨2811408, by rfl⟩ : syracuseStep 7497089 = 5622817) B5622817
theorem B4998059 : Blo 2219435 4998059 := bstep (se 1 (by rfl) ⟨3748544, by rfl⟩ : syracuseStep 4998059 = 7497089) B7497089
theorem B3332039 : Blo 2219435 3332039 := bstep (se 1 (by rfl) ⟨2499029, by rfl⟩ : syracuseStep 3332039 = 4998059) B4998059
theorem B2221359 : Blo 2219435 2221359 := bstep (se 1 (by rfl) ⟨1666019, by rfl⟩ : syracuseStep 2221359 = 3332039) B3332039
theorem B3332045 : Blo 2219435 3332045 := bbase (se 3 (by rfl) ⟨624758, by rfl⟩ : syracuseStep 3332045 = 1249517) (by norm_num)
theorem B2221363 : Blo 2219435 2221363 := bstep (se 1 (by rfl) ⟨1666022, by rfl⟩ : syracuseStep 2221363 = 3332045) B3332045
theorem B4998077 : Blo 2219435 4998077 := bbase (se 3 (by rfl) ⟨937139, by rfl⟩ : syracuseStep 4998077 = 1874279) (by norm_num)
theorem B3332051 : Blo 2219435 3332051 := bstep (se 1 (by rfl) ⟨2499038, by rfl⟩ : syracuseStep 3332051 = 4998077) B4998077
theorem B2221367 : Blo 2219435 2221367 := bstep (se 1 (by rfl) ⟨1666025, by rfl⟩ : syracuseStep 2221367 = 3332051) B3332051
theorem B3748565 : Blo 2219435 3748565 := bbase (se 7 (by rfl) ⟨43928, by rfl⟩ : syracuseStep 3748565 = 87857) (by norm_num)
theorem B2499043 : Blo 2219435 2499043 := bstep (se 1 (by rfl) ⟨1874282, by rfl⟩ : syracuseStep 2499043 = 3748565) B3748565
theorem B3332057 : Blo 2219435 3332057 := bstep (se 2 (by rfl) ⟨1249521, by rfl⟩ : syracuseStep 3332057 = 2499043) B2499043
theorem B2221371 : Blo 2219435 2221371 := bstep (se 1 (by rfl) ⟨1666028, by rfl⟩ : syracuseStep 2221371 = 3332057) B3332057
theorem B5135413 : Blo 2219435 5135413 := bbase (se 5 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 5135413 = 481445) (by norm_num)
theorem B6847217 : Blo 2219435 6847217 := bstep (se 2 (by rfl) ⟨2567706, by rfl⟩ : syracuseStep 6847217 = 5135413) B5135413
theorem B4564811 : Blo 2219435 4564811 := bstep (se 1 (by rfl) ⟨3423608, by rfl⟩ : syracuseStep 4564811 = 6847217) B6847217
theorem B3043207 : Blo 2219435 3043207 := bstep (se 1 (by rfl) ⟨2282405, by rfl⟩ : syracuseStep 3043207 = 4564811) B4564811
theorem B4057609 : Blo 2219435 4057609 := bstep (se 2 (by rfl) ⟨1521603, by rfl⟩ : syracuseStep 4057609 = 3043207) B3043207
theorem B5410145 : Blo 2219435 5410145 := bstep (se 2 (by rfl) ⟨2028804, by rfl⟩ : syracuseStep 5410145 = 4057609) B4057609
theorem B3606763 : Blo 2219435 3606763 := bstep (se 1 (by rfl) ⟨2705072, by rfl⟩ : syracuseStep 3606763 = 5410145) B5410145
theorem B4809017 : Blo 2219435 4809017 := bstep (se 2 (by rfl) ⟨1803381, by rfl⟩ : syracuseStep 4809017 = 3606763) B3606763
theorem B12824045 : Blo 2219435 12824045 := bstep (se 3 (by rfl) ⟨2404508, by rfl⟩ : syracuseStep 12824045 = 4809017) B4809017
theorem B8549363 : Blo 2219435 8549363 := bstep (se 1 (by rfl) ⟨6412022, by rfl⟩ : syracuseStep 8549363 = 12824045) B12824045
theorem B5699575 : Blo 2219435 5699575 := bstep (se 1 (by rfl) ⟨4274681, by rfl⟩ : syracuseStep 5699575 = 8549363) B8549363
theorem B7599433 : Blo 2219435 7599433 := bstep (se 2 (by rfl) ⟨2849787, by rfl⟩ : syracuseStep 7599433 = 5699575) B5699575
theorem B10132577 : Blo 2219435 10132577 := bstep (se 2 (by rfl) ⟨3799716, by rfl⟩ : syracuseStep 10132577 = 7599433) B7599433
theorem B6755051 : Blo 2219435 6755051 := bstep (se 1 (by rfl) ⟨5066288, by rfl⟩ : syracuseStep 6755051 = 10132577) B10132577
theorem B4503367 : Blo 2219435 4503367 := bstep (se 1 (by rfl) ⟨3377525, by rfl⟩ : syracuseStep 4503367 = 6755051) B6755051
theorem B6004489 : Blo 2219435 6004489 := bstep (se 2 (by rfl) ⟨2251683, by rfl⟩ : syracuseStep 6004489 = 4503367) B4503367
theorem B8005985 : Blo 2219435 8005985 := bstep (se 2 (by rfl) ⟨3002244, by rfl⟩ : syracuseStep 8005985 = 6004489) B6004489
theorem B5337323 : Blo 2219435 5337323 := bstep (se 1 (by rfl) ⟨4002992, by rfl⟩ : syracuseStep 5337323 = 8005985) B8005985
theorem B3558215 : Blo 2219435 3558215 := bstep (se 1 (by rfl) ⟨2668661, by rfl⟩ : syracuseStep 3558215 = 5337323) B5337323
theorem B9488573 : Blo 2219435 9488573 := bstep (se 3 (by rfl) ⟨1779107, by rfl⟩ : syracuseStep 9488573 = 3558215) B3558215
theorem B6325715 : Blo 2219435 6325715 := bstep (se 1 (by rfl) ⟨4744286, by rfl⟩ : syracuseStep 6325715 = 9488573) B9488573
theorem B16868573 : Blo 2219435 16868573 := bstep (se 3 (by rfl) ⟨3162857, by rfl⟩ : syracuseStep 16868573 = 6325715) B6325715
theorem B11245715 : Blo 2219435 11245715 := bstep (se 1 (by rfl) ⟨8434286, by rfl⟩ : syracuseStep 11245715 = 16868573) B16868573
theorem B7497143 : Blo 2219435 7497143 := bstep (se 1 (by rfl) ⟨5622857, by rfl⟩ : syracuseStep 7497143 = 11245715) B11245715
theorem B4998095 : Blo 2219435 4998095 := bstep (se 1 (by rfl) ⟨3748571, by rfl⟩ : syracuseStep 4998095 = 7497143) B7497143
theorem B3332063 : Blo 2219435 3332063 := bstep (se 1 (by rfl) ⟨2499047, by rfl⟩ : syracuseStep 3332063 = 4998095) B4998095
theorem B2221375 : Blo 2219435 2221375 := bstep (se 1 (by rfl) ⟨1666031, by rfl⟩ : syracuseStep 2221375 = 3332063) B3332063
theorem B3332069 : Blo 2219435 3332069 := bbase (se 4 (by rfl) ⟨312381, by rfl⟩ : syracuseStep 3332069 = 624763) (by norm_num)
theorem B2221379 : Blo 2219435 2221379 := bstep (se 1 (by rfl) ⟨1666034, by rfl⟩ : syracuseStep 2221379 = 3332069) B3332069
theorem B2404517 : Blo 2219435 2404517 := bbase (se 4 (by rfl) ⟨225423, by rfl⟩ : syracuseStep 2404517 = 450847) (by norm_num)
theorem B6412045 : Blo 2219435 6412045 := bstep (se 3 (by rfl) ⟨1202258, by rfl⟩ : syracuseStep 6412045 = 2404517) B2404517
theorem B8549393 : Blo 2219435 8549393 := bstep (se 2 (by rfl) ⟨3206022, by rfl⟩ : syracuseStep 8549393 = 6412045) B6412045
theorem B91193525 : Blo 2219435 91193525 := bstep (se 5 (by rfl) ⟨4274696, by rfl⟩ : syracuseStep 91193525 = 8549393) B8549393
theorem B60795683 : Blo 2219435 60795683 := bstep (se 1 (by rfl) ⟨45596762, by rfl⟩ : syracuseStep 60795683 = 91193525) B91193525
theorem B40530455 : Blo 2219435 40530455 := bstep (se 1 (by rfl) ⟨30397841, by rfl⟩ : syracuseStep 40530455 = 60795683) B60795683
theorem B27020303 : Blo 2219435 27020303 := bstep (se 1 (by rfl) ⟨20265227, by rfl⟩ : syracuseStep 27020303 = 40530455) B40530455
theorem B18013535 : Blo 2219435 18013535 := bstep (se 1 (by rfl) ⟨13510151, by rfl⟩ : syracuseStep 18013535 = 27020303) B27020303
theorem B12009023 : Blo 2219435 12009023 := bstep (se 1 (by rfl) ⟨9006767, by rfl⟩ : syracuseStep 12009023 = 18013535) B18013535
theorem B8006015 : Blo 2219435 8006015 := bstep (se 1 (by rfl) ⟨6004511, by rfl⟩ : syracuseStep 8006015 = 12009023) B12009023
theorem B5337343 : Blo 2219435 5337343 := bstep (se 1 (by rfl) ⟨4003007, by rfl⟩ : syracuseStep 5337343 = 8006015) B8006015
theorem B7116457 : Blo 2219435 7116457 := bstep (se 2 (by rfl) ⟨2668671, by rfl⟩ : syracuseStep 7116457 = 5337343) B5337343
theorem B9488609 : Blo 2219435 9488609 := bstep (se 2 (by rfl) ⟨3558228, by rfl⟩ : syracuseStep 9488609 = 7116457) B7116457
theorem B6325739 : Blo 2219435 6325739 := bstep (se 1 (by rfl) ⟨4744304, by rfl⟩ : syracuseStep 6325739 = 9488609) B9488609
theorem B4217159 : Blo 2219435 4217159 := bstep (se 1 (by rfl) ⟨3162869, by rfl⟩ : syracuseStep 4217159 = 6325739) B6325739
theorem B2811439 : Blo 2219435 2811439 := bstep (se 1 (by rfl) ⟨2108579, by rfl⟩ : syracuseStep 2811439 = 4217159) B4217159
theorem B3748585 : Blo 2219435 3748585 := bstep (se 2 (by rfl) ⟨1405719, by rfl⟩ : syracuseStep 3748585 = 2811439) B2811439
theorem B4998113 : Blo 2219435 4998113 := bstep (se 2 (by rfl) ⟨1874292, by rfl⟩ : syracuseStep 4998113 = 3748585) B3748585
theorem B3332075 : Blo 2219435 3332075 := bstep (se 1 (by rfl) ⟨2499056, by rfl⟩ : syracuseStep 3332075 = 4998113) B4998113
theorem B2221383 : Blo 2219435 2221383 := bstep (se 1 (by rfl) ⟨1666037, by rfl⟩ : syracuseStep 2221383 = 3332075) B3332075
theorem B2499061 : Blo 2219435 2499061 := bbase (se 5 (by rfl) ⟨117143, by rfl⟩ : syracuseStep 2499061 = 234287) (by norm_num)
theorem B3332081 : Blo 2219435 3332081 := bstep (se 2 (by rfl) ⟨1249530, by rfl⟩ : syracuseStep 3332081 = 2499061) B2499061
theorem B2221387 : Blo 2219435 2221387 := bstep (se 1 (by rfl) ⟨1666040, by rfl⟩ : syracuseStep 2221387 = 3332081) B3332081
theorem B2811449 : Blo 2219435 2811449 := bbase (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) (by norm_num)
theorem B7497197 : Blo 2219435 7497197 := bstep (se 3 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 7497197 = 2811449) B2811449
theorem B4998131 : Blo 2219435 4998131 := bstep (se 1 (by rfl) ⟨3748598, by rfl⟩ : syracuseStep 4998131 = 7497197) B7497197
theorem B3332087 : Blo 2219435 3332087 := bstep (se 1 (by rfl) ⟨2499065, by rfl⟩ : syracuseStep 3332087 = 4998131) B4998131
theorem B2221391 : Blo 2219435 2221391 := bstep (se 1 (by rfl) ⟨1666043, by rfl⟩ : syracuseStep 2221391 = 3332087) B3332087
theorem B3332093 : Blo 2219435 3332093 := bbase (se 3 (by rfl) ⟨624767, by rfl⟩ : syracuseStep 3332093 = 1249535) (by norm_num)
theorem B2221395 : Blo 2219435 2221395 := bstep (se 1 (by rfl) ⟨1666046, by rfl⟩ : syracuseStep 2221395 = 3332093) B3332093
theorem B4998149 : Blo 2219435 4998149 := bbase (se 4 (by rfl) ⟨468576, by rfl⟩ : syracuseStep 4998149 = 937153) (by norm_num)
theorem B3332099 : Blo 2219435 3332099 := bstep (se 1 (by rfl) ⟨2499074, by rfl⟩ : syracuseStep 3332099 = 4998149) B4998149
theorem B2221399 : Blo 2219435 2221399 := bstep (se 1 (by rfl) ⟨1666049, by rfl⟩ : syracuseStep 2221399 = 3332099) B3332099
theorem B4217197 : Blo 2219435 4217197 := bbase (se 3 (by rfl) ⟨790724, by rfl⟩ : syracuseStep 4217197 = 1581449) (by norm_num)
theorem B5622929 : Blo 2219435 5622929 := bstep (se 2 (by rfl) ⟨2108598, by rfl⟩ : syracuseStep 5622929 = 4217197) B4217197
theorem B3748619 : Blo 2219435 3748619 := bstep (se 1 (by rfl) ⟨2811464, by rfl⟩ : syracuseStep 3748619 = 5622929) B5622929
theorem B2499079 : Blo 2219435 2499079 := bstep (se 1 (by rfl) ⟨1874309, by rfl⟩ : syracuseStep 2499079 = 3748619) B3748619
theorem B3332105 : Blo 2219435 3332105 := bstep (se 2 (by rfl) ⟨1249539, by rfl⟩ : syracuseStep 3332105 = 2499079) B2499079
theorem B2221403 : Blo 2219435 2221403 := bstep (se 1 (by rfl) ⟨1666052, by rfl⟩ : syracuseStep 2221403 = 3332105) B3332105
theorem B11245877 : Blo 2219435 11245877 := bbase (se 5 (by rfl) ⟨527150, by rfl⟩ : syracuseStep 11245877 = 1054301) (by norm_num)
theorem B7497251 : Blo 2219435 7497251 := bstep (se 1 (by rfl) ⟨5622938, by rfl⟩ : syracuseStep 7497251 = 11245877) B11245877
theorem B4998167 : Blo 2219435 4998167 := bstep (se 1 (by rfl) ⟨3748625, by rfl⟩ : syracuseStep 4998167 = 7497251) B7497251
theorem B3332111 : Blo 2219435 3332111 := bstep (se 1 (by rfl) ⟨2499083, by rfl⟩ : syracuseStep 3332111 = 4998167) B4998167
theorem B2221407 : Blo 2219435 2221407 := bstep (se 1 (by rfl) ⟨1666055, by rfl⟩ : syracuseStep 2221407 = 3332111) B3332111
theorem B3332117 : Blo 2219435 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B2221411 : Blo 2219435 2221411 := bstep (se 1 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 2221411 = 3332117) B3332117
theorem B6004597 : Blo 2219435 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B8006129 : Blo 2219435 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B5337419 : Blo 2219435 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B14233117 : Blo 2219435 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B18977489 : Blo 2219435 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B12651659 : Blo 2219435 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B8434439 : Blo 2219435 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B5622959 : Blo 2219435 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B3748639 : Blo 2219435 3748639 := bstep (se 1 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 3748639 = 5622959) B5622959
theorem B4998185 : Blo 2219435 4998185 := bstep (se 2 (by rfl) ⟨1874319, by rfl⟩ : syracuseStep 4998185 = 3748639) B3748639
theorem B3332123 : Blo 2219435 3332123 := bstep (se 1 (by rfl) ⟨2499092, by rfl⟩ : syracuseStep 3332123 = 4998185) B4998185
theorem B2221415 : Blo 2219435 2221415 := bstep (se 1 (by rfl) ⟨1666061, by rfl⟩ : syracuseStep 2221415 = 3332123) B3332123
theorem B2499097 : Blo 2219435 2499097 := bbase (se 2 (by rfl) ⟨937161, by rfl⟩ : syracuseStep 2499097 = 1874323) (by norm_num)
theorem B3332129 : Blo 2219435 3332129 := bstep (se 2 (by rfl) ⟨1249548, by rfl⟩ : syracuseStep 3332129 = 2499097) B2499097
theorem B2221419 : Blo 2219435 2221419 := bstep (se 1 (by rfl) ⟨1666064, by rfl⟩ : syracuseStep 2221419 = 3332129) B3332129
theorem B8434469 : Blo 2219435 8434469 := bbase (se 4 (by rfl) ⟨790731, by rfl⟩ : syracuseStep 8434469 = 1581463) (by norm_num)
theorem B5622979 : Blo 2219435 5622979 := bstep (se 1 (by rfl) ⟨4217234, by rfl⟩ : syracuseStep 5622979 = 8434469) B8434469
theorem B7497305 : Blo 2219435 7497305 := bstep (se 2 (by rfl) ⟨2811489, by rfl⟩ : syracuseStep 7497305 = 5622979) B5622979
theorem B4998203 : Blo 2219435 4998203 := bstep (se 1 (by rfl) ⟨3748652, by rfl⟩ : syracuseStep 4998203 = 7497305) B7497305
theorem B3332135 : Blo 2219435 3332135 := bstep (se 1 (by rfl) ⟨2499101, by rfl⟩ : syracuseStep 3332135 = 4998203) B4998203
theorem B2221423 : Blo 2219435 2221423 := bstep (se 1 (by rfl) ⟨1666067, by rfl⟩ : syracuseStep 2221423 = 3332135) B3332135
theorem B3332141 : Blo 2219435 3332141 := bbase (se 3 (by rfl) ⟨624776, by rfl⟩ : syracuseStep 3332141 = 1249553) (by norm_num)
theorem B2221427 : Blo 2219435 2221427 := bstep (se 1 (by rfl) ⟨1666070, by rfl⟩ : syracuseStep 2221427 = 3332141) B3332141
theorem B4998221 : Blo 2219435 4998221 := bbase (se 3 (by rfl) ⟨937166, by rfl⟩ : syracuseStep 4998221 = 1874333) (by norm_num)
theorem B3332147 : Blo 2219435 3332147 := bstep (se 1 (by rfl) ⟨2499110, by rfl⟩ : syracuseStep 3332147 = 4998221) B4998221
theorem B2221431 : Blo 2219435 2221431 := bstep (se 1 (by rfl) ⟨1666073, by rfl⟩ : syracuseStep 2221431 = 3332147) B3332147
theorem B2811505 : Blo 2219435 2811505 := bbase (se 2 (by rfl) ⟨1054314, by rfl⟩ : syracuseStep 2811505 = 2108629) (by norm_num)
theorem B3748673 : Blo 2219435 3748673 := bstep (se 2 (by rfl) ⟨1405752, by rfl⟩ : syracuseStep 3748673 = 2811505) B2811505
theorem B2499115 : Blo 2219435 2499115 := bstep (se 1 (by rfl) ⟨1874336, by rfl⟩ : syracuseStep 2499115 = 3748673) B3748673
theorem B3332153 : Blo 2219435 3332153 := bstep (se 2 (by rfl) ⟨1249557, by rfl⟩ : syracuseStep 3332153 = 2499115) B2499115
theorem B2221435 : Blo 2219435 2221435 := bstep (se 1 (by rfl) ⟨1666076, by rfl⟩ : syracuseStep 2221435 = 3332153) B3332153
theorem C0 (j : ℕ) (h1 : 554858 ≤ j) (h2 : j ≤ 555358) : Blo 2219435 (4 * j + 3) := by
  interval_cases j
  · exact B2219435
  · exact B2219439
  · exact B2219443
  · exact B2219447
  · exact B2219451
  · exact B2219455
  · exact B2219459
  · exact B2219463
  · exact B2219467
  · exact B2219471
  · exact B2219475
  · exact B2219479
  · exact B2219483
  · exact B2219487
  · exact B2219491
  · exact B2219495
  · exact B2219499
  · exact B2219503
  · exact B2219507
  · exact B2219511
  · exact B2219515
  · exact B2219519
  · exact B2219523
  · exact B2219527
  · exact B2219531
  · exact B2219535
  · exact B2219539
  · exact B2219543
  · exact B2219547
  · exact B2219551
  · exact B2219555
  · exact B2219559
  · exact B2219563
  · exact B2219567
  · exact B2219571
  · exact B2219575
  · exact B2219579
  · exact B2219583
  · exact B2219587
  · exact B2219591
  · exact B2219595
  · exact B2219599
  · exact B2219603
  · exact B2219607
  · exact B2219611
  · exact B2219615
  · exact B2219619
  · exact B2219623
  · exact B2219627
  · exact B2219631
  · exact B2219635
  · exact B2219639
  · exact B2219643
  · exact B2219647
  · exact B2219651
  · exact B2219655
  · exact B2219659
  · exact B2219663
  · exact B2219667
  · exact B2219671
  · exact B2219675
  · exact B2219679
  · exact B2219683
  · exact B2219687
  · exact B2219691
  · exact B2219695
  · exact B2219699
  · exact B2219703
  · exact B2219707
  · exact B2219711
  · exact B2219715
  · exact B2219719
  · exact B2219723
  · exact B2219727
  · exact B2219731
  · exact B2219735
  · exact B2219739
  · exact B2219743
  · exact B2219747
  · exact B2219751
  · exact B2219755
  · exact B2219759
  · exact B2219763
  · exact B2219767
  · exact B2219771
  · exact B2219775
  · exact B2219779
  · exact B2219783
  · exact B2219787
  · exact B2219791
  · exact B2219795
  · exact B2219799
  · exact B2219803
  · exact B2219807
  · exact B2219811
  · exact B2219815
  · exact B2219819
  · exact B2219823
  · exact B2219827
  · exact B2219831
  · exact B2219835
  · exact B2219839
  · exact B2219843
  · exact B2219847
  · exact B2219851
  · exact B2219855
  · exact B2219859
  · exact B2219863
  · exact B2219867
  · exact B2219871
  · exact B2219875
  · exact B2219879
  · exact B2219883
  · exact B2219887
  · exact B2219891
  · exact B2219895
  · exact B2219899
  · exact B2219903
  · exact B2219907
  · exact B2219911
  · exact B2219915
  · exact B2219919
  · exact B2219923
  · exact B2219927
  · exact B2219931
  · exact B2219935
  · exact B2219939
  · exact B2219943
  · exact B2219947
  · exact B2219951
  · exact B2219955
  · exact B2219959
  · exact B2219963
  · exact B2219967
  · exact B2219971
  · exact B2219975
  · exact B2219979
  · exact B2219983
  · exact B2219987
  · exact B2219991
  · exact B2219995
  · exact B2219999
  · exact B2220003
  · exact B2220007
  · exact B2220011
  · exact B2220015
  · exact B2220019
  · exact B2220023
  · exact B2220027
  · exact B2220031
  · exact B2220035
  · exact B2220039
  · exact B2220043
  · exact B2220047
  · exact B2220051
  · exact B2220055
  · exact B2220059
  · exact B2220063
  · exact B2220067
  · exact B2220071
  · exact B2220075
  · exact B2220079
  · exact B2220083
  · exact B2220087
  · exact B2220091
  · exact B2220095
  · exact B2220099
  · exact B2220103
  · exact B2220107
  · exact B2220111
  · exact B2220115
  · exact B2220119
  · exact B2220123
  · exact B2220127
  · exact B2220131
  · exact B2220135
  · exact B2220139
  · exact B2220143
  · exact B2220147
  · exact B2220151
  · exact B2220155
  · exact B2220159
  · exact B2220163
  · exact B2220167
  · exact B2220171
  · exact B2220175
  · exact B2220179
  · exact B2220183
  · exact B2220187
  · exact B2220191
  · exact B2220195
  · exact B2220199
  · exact B2220203
  · exact B2220207
  · exact B2220211
  · exact B2220215
  · exact B2220219
  · exact B2220223
  · exact B2220227
  · exact B2220231
  · exact B2220235
  · exact B2220239
  · exact B2220243
  · exact B2220247
  · exact B2220251
  · exact B2220255
  · exact B2220259
  · exact B2220263
  · exact B2220267
  · exact B2220271
  · exact B2220275
  · exact B2220279
  · exact B2220283
  · exact B2220287
  · exact B2220291
  · exact B2220295
  · exact B2220299
  · exact B2220303
  · exact B2220307
  · exact B2220311
  · exact B2220315
  · exact B2220319
  · exact B2220323
  · exact B2220327
  · exact B2220331
  · exact B2220335
  · exact B2220339
  · exact B2220343
  · exact B2220347
  · exact B2220351
  · exact B2220355
  · exact B2220359
  · exact B2220363
  · exact B2220367
  · exact B2220371
  · exact B2220375
  · exact B2220379
  · exact B2220383
  · exact B2220387
  · exact B2220391
  · exact B2220395
  · exact B2220399
  · exact B2220403
  · exact B2220407
  · exact B2220411
  · exact B2220415
  · exact B2220419
  · exact B2220423
  · exact B2220427
  · exact B2220431
  · exact B2220435
  · exact B2220439
  · exact B2220443
  · exact B2220447
  · exact B2220451
  · exact B2220455
  · exact B2220459
  · exact B2220463
  · exact B2220467
  · exact B2220471
  · exact B2220475
  · exact B2220479
  · exact B2220483
  · exact B2220487
  · exact B2220491
  · exact B2220495
  · exact B2220499
  · exact B2220503
  · exact B2220507
  · exact B2220511
  · exact B2220515
  · exact B2220519
  · exact B2220523
  · exact B2220527
  · exact B2220531
  · exact B2220535
  · exact B2220539
  · exact B2220543
  · exact B2220547
  · exact B2220551
  · exact B2220555
  · exact B2220559
  · exact B2220563
  · exact B2220567
  · exact B2220571
  · exact B2220575
  · exact B2220579
  · exact B2220583
  · exact B2220587
  · exact B2220591
  · exact B2220595
  · exact B2220599
  · exact B2220603
  · exact B2220607
  · exact B2220611
  · exact B2220615
  · exact B2220619
  · exact B2220623
  · exact B2220627
  · exact B2220631
  · exact B2220635
  · exact B2220639
  · exact B2220643
  · exact B2220647
  · exact B2220651
  · exact B2220655
  · exact B2220659
  · exact B2220663
  · exact B2220667
  · exact B2220671
  · exact B2220675
  · exact B2220679
  · exact B2220683
  · exact B2220687
  · exact B2220691
  · exact B2220695
  · exact B2220699
  · exact B2220703
  · exact B2220707
  · exact B2220711
  · exact B2220715
  · exact B2220719
  · exact B2220723
  · exact B2220727
  · exact B2220731
  · exact B2220735
  · exact B2220739
  · exact B2220743
  · exact B2220747
  · exact B2220751
  · exact B2220755
  · exact B2220759
  · exact B2220763
  · exact B2220767
  · exact B2220771
  · exact B2220775
  · exact B2220779
  · exact B2220783
  · exact B2220787
  · exact B2220791
  · exact B2220795
  · exact B2220799
  · exact B2220803
  · exact B2220807
  · exact B2220811
  · exact B2220815
  · exact B2220819
  · exact B2220823
  · exact B2220827
  · exact B2220831
  · exact B2220835
  · exact B2220839
  · exact B2220843
  · exact B2220847
  · exact B2220851
  · exact B2220855
  · exact B2220859
  · exact B2220863
  · exact B2220867
  · exact B2220871
  · exact B2220875
  · exact B2220879
  · exact B2220883
  · exact B2220887
  · exact B2220891
  · exact B2220895
  · exact B2220899
  · exact B2220903
  · exact B2220907
  · exact B2220911
  · exact B2220915
  · exact B2220919
  · exact B2220923
  · exact B2220927
  · exact B2220931
  · exact B2220935
  · exact B2220939
  · exact B2220943
  · exact B2220947
  · exact B2220951
  · exact B2220955
  · exact B2220959
  · exact B2220963
  · exact B2220967
  · exact B2220971
  · exact B2220975
  · exact B2220979
  · exact B2220983
  · exact B2220987
  · exact B2220991
  · exact B2220995
  · exact B2220999
  · exact B2221003
  · exact B2221007
  · exact B2221011
  · exact B2221015
  · exact B2221019
  · exact B2221023
  · exact B2221027
  · exact B2221031
  · exact B2221035
  · exact B2221039
  · exact B2221043
  · exact B2221047
  · exact B2221051
  · exact B2221055
  · exact B2221059
  · exact B2221063
  · exact B2221067
  · exact B2221071
  · exact B2221075
  · exact B2221079
  · exact B2221083
  · exact B2221087
  · exact B2221091
  · exact B2221095
  · exact B2221099
  · exact B2221103
  · exact B2221107
  · exact B2221111
  · exact B2221115
  · exact B2221119
  · exact B2221123
  · exact B2221127
  · exact B2221131
  · exact B2221135
  · exact B2221139
  · exact B2221143
  · exact B2221147
  · exact B2221151
  · exact B2221155
  · exact B2221159
  · exact B2221163
  · exact B2221167
  · exact B2221171
  · exact B2221175
  · exact B2221179
  · exact B2221183
  · exact B2221187
  · exact B2221191
  · exact B2221195
  · exact B2221199
  · exact B2221203
  · exact B2221207
  · exact B2221211
  · exact B2221215
  · exact B2221219
  · exact B2221223
  · exact B2221227
  · exact B2221231
  · exact B2221235
  · exact B2221239
  · exact B2221243
  · exact B2221247
  · exact B2221251
  · exact B2221255
  · exact B2221259
  · exact B2221263
  · exact B2221267
  · exact B2221271
  · exact B2221275
  · exact B2221279
  · exact B2221283
  · exact B2221287
  · exact B2221291
  · exact B2221295
  · exact B2221299
  · exact B2221303
  · exact B2221307
  · exact B2221311
  · exact B2221315
  · exact B2221319
  · exact B2221323
  · exact B2221327
  · exact B2221331
  · exact B2221335
  · exact B2221339
  · exact B2221343
  · exact B2221347
  · exact B2221351
  · exact B2221355
  · exact B2221359
  · exact B2221363
  · exact B2221367
  · exact B2221371
  · exact B2221375
  · exact B2221379
  · exact B2221383
  · exact B2221387
  · exact B2221391
  · exact B2221395
  · exact B2221399
  · exact B2221403
  · exact B2221407
  · exact B2221411
  · exact B2221415
  · exact B2221419
  · exact B2221423
  · exact B2221427
  · exact B2221431
  · exact B2221435
theorem solution (m : ℕ) (hlo : 2219435 ≤ m) (hhi : m ≤ 2221435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 554858 ≤ j := by omega
    have hj2 : j ≤ 555358 := by omega
    have hb : Blo 2219435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
