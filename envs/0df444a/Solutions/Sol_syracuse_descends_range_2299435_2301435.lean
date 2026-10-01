-- Prove2me | solution 1 for syracuse_descends_range_2299435_2301435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:58.544998+00:00
-- url     : https://prove2.me/submissions/2fb2df24-dab4-4e29-8908-fb59e8156086

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

theorem B2586865 : Blo 2299435 2586865 := bbase (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) (by norm_num)
theorem B3449153 : Blo 2299435 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B2299435 : Blo 2299435 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B27969749 : Blo 2299435 27969749 := bbase (se 7 (by rfl) ⟨327770, by rfl⟩ : syracuseStep 27969749 = 655541) (by norm_num)
theorem B18646499 : Blo 2299435 18646499 := bstep (se 1 (by rfl) ⟨13984874, by rfl⟩ : syracuseStep 18646499 = 27969749) B27969749
theorem B12430999 : Blo 2299435 12430999 := bstep (se 1 (by rfl) ⟨9323249, by rfl⟩ : syracuseStep 12430999 = 18646499) B18646499
theorem B16574665 : Blo 2299435 16574665 := bstep (se 2 (by rfl) ⟨6215499, by rfl⟩ : syracuseStep 16574665 = 12430999) B12430999
theorem B22099553 : Blo 2299435 22099553 := bstep (se 2 (by rfl) ⟨8287332, by rfl⟩ : syracuseStep 22099553 = 16574665) B16574665
theorem B14733035 : Blo 2299435 14733035 := bstep (se 1 (by rfl) ⟨11049776, by rfl⟩ : syracuseStep 14733035 = 22099553) B22099553
theorem B9822023 : Blo 2299435 9822023 := bstep (se 1 (by rfl) ⟨7366517, by rfl⟩ : syracuseStep 9822023 = 14733035) B14733035
theorem B6548015 : Blo 2299435 6548015 := bstep (se 1 (by rfl) ⟨4911011, by rfl⟩ : syracuseStep 6548015 = 9822023) B9822023
theorem B4365343 : Blo 2299435 4365343 := bstep (se 1 (by rfl) ⟨3274007, by rfl⟩ : syracuseStep 4365343 = 6548015) B6548015
theorem B5820457 : Blo 2299435 5820457 := bstep (se 2 (by rfl) ⟨2182671, by rfl⟩ : syracuseStep 5820457 = 4365343) B4365343
theorem B7760609 : Blo 2299435 7760609 := bstep (se 2 (by rfl) ⟨2910228, by rfl⟩ : syracuseStep 7760609 = 5820457) B5820457
theorem B5173739 : Blo 2299435 5173739 := bstep (se 1 (by rfl) ⟨3880304, by rfl⟩ : syracuseStep 5173739 = 7760609) B7760609
theorem B3449159 : Blo 2299435 3449159 := bstep (se 1 (by rfl) ⟨2586869, by rfl⟩ : syracuseStep 3449159 = 5173739) B5173739
theorem B2299439 : Blo 2299435 2299439 := bstep (se 1 (by rfl) ⟨1724579, by rfl⟩ : syracuseStep 2299439 = 3449159) B3449159
theorem B3449165 : Blo 2299435 3449165 := bbase (se 3 (by rfl) ⟨646718, by rfl⟩ : syracuseStep 3449165 = 1293437) (by norm_num)
theorem B2299443 : Blo 2299435 2299443 := bstep (se 1 (by rfl) ⟨1724582, by rfl⟩ : syracuseStep 2299443 = 3449165) B3449165
theorem B5173757 : Blo 2299435 5173757 := bbase (se 3 (by rfl) ⟨970079, by rfl⟩ : syracuseStep 5173757 = 1940159) (by norm_num)
theorem B3449171 : Blo 2299435 3449171 := bstep (se 1 (by rfl) ⟨2586878, by rfl⟩ : syracuseStep 3449171 = 5173757) B5173757
theorem B2299447 : Blo 2299435 2299447 := bstep (se 1 (by rfl) ⟨1724585, by rfl⟩ : syracuseStep 2299447 = 3449171) B3449171
theorem B3880325 : Blo 2299435 3880325 := bbase (se 4 (by rfl) ⟨363780, by rfl⟩ : syracuseStep 3880325 = 727561) (by norm_num)
theorem B2586883 : Blo 2299435 2586883 := bstep (se 1 (by rfl) ⟨1940162, by rfl⟩ : syracuseStep 2586883 = 3880325) B3880325
theorem B3449177 : Blo 2299435 3449177 := bstep (se 2 (by rfl) ⟨1293441, by rfl⟩ : syracuseStep 3449177 = 2586883) B2586883
theorem B2299451 : Blo 2299435 2299451 := bstep (se 1 (by rfl) ⟨1724588, by rfl⟩ : syracuseStep 2299451 = 3449177) B3449177
theorem B17461493 : Blo 2299435 17461493 := bbase (se 5 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 17461493 = 1637015) (by norm_num)
theorem B11640995 : Blo 2299435 11640995 := bstep (se 1 (by rfl) ⟨8730746, by rfl⟩ : syracuseStep 11640995 = 17461493) B17461493
theorem B7760663 : Blo 2299435 7760663 := bstep (se 1 (by rfl) ⟨5820497, by rfl⟩ : syracuseStep 7760663 = 11640995) B11640995
theorem B5173775 : Blo 2299435 5173775 := bstep (se 1 (by rfl) ⟨3880331, by rfl⟩ : syracuseStep 5173775 = 7760663) B7760663
theorem B3449183 : Blo 2299435 3449183 := bstep (se 1 (by rfl) ⟨2586887, by rfl⟩ : syracuseStep 3449183 = 5173775) B5173775
theorem B2299455 : Blo 2299435 2299455 := bstep (se 1 (by rfl) ⟨1724591, by rfl⟩ : syracuseStep 2299455 = 3449183) B3449183
theorem B3449189 : Blo 2299435 3449189 := bbase (se 4 (by rfl) ⟨323361, by rfl⟩ : syracuseStep 3449189 = 646723) (by norm_num)
theorem B2299459 : Blo 2299435 2299459 := bstep (se 1 (by rfl) ⟨1724594, by rfl⟩ : syracuseStep 2299459 = 3449189) B3449189
theorem B4365389 : Blo 2299435 4365389 := bbase (se 3 (by rfl) ⟨818510, by rfl⟩ : syracuseStep 4365389 = 1637021) (by norm_num)
theorem B2910259 : Blo 2299435 2910259 := bstep (se 1 (by rfl) ⟨2182694, by rfl⟩ : syracuseStep 2910259 = 4365389) B4365389
theorem B3880345 : Blo 2299435 3880345 := bstep (se 2 (by rfl) ⟨1455129, by rfl⟩ : syracuseStep 3880345 = 2910259) B2910259
theorem B5173793 : Blo 2299435 5173793 := bstep (se 2 (by rfl) ⟨1940172, by rfl⟩ : syracuseStep 5173793 = 3880345) B3880345
theorem B3449195 : Blo 2299435 3449195 := bstep (se 1 (by rfl) ⟨2586896, by rfl⟩ : syracuseStep 3449195 = 5173793) B5173793
theorem B2299463 : Blo 2299435 2299463 := bstep (se 1 (by rfl) ⟨1724597, by rfl⟩ : syracuseStep 2299463 = 3449195) B3449195
theorem B2586901 : Blo 2299435 2586901 := bbase (se 6 (by rfl) ⟨60630, by rfl⟩ : syracuseStep 2586901 = 121261) (by norm_num)
theorem B3449201 : Blo 2299435 3449201 := bstep (se 2 (by rfl) ⟨1293450, by rfl⟩ : syracuseStep 3449201 = 2586901) B2586901
theorem B2299467 : Blo 2299435 2299467 := bstep (se 1 (by rfl) ⟨1724600, by rfl⟩ : syracuseStep 2299467 = 3449201) B3449201
theorem B2910269 : Blo 2299435 2910269 := bbase (se 3 (by rfl) ⟨545675, by rfl⟩ : syracuseStep 2910269 = 1091351) (by norm_num)
theorem B7760717 : Blo 2299435 7760717 := bstep (se 3 (by rfl) ⟨1455134, by rfl⟩ : syracuseStep 7760717 = 2910269) B2910269
theorem B5173811 : Blo 2299435 5173811 := bstep (se 1 (by rfl) ⟨3880358, by rfl⟩ : syracuseStep 5173811 = 7760717) B7760717
theorem B3449207 : Blo 2299435 3449207 := bstep (se 1 (by rfl) ⟨2586905, by rfl⟩ : syracuseStep 3449207 = 5173811) B5173811
theorem B2299471 : Blo 2299435 2299471 := bstep (se 1 (by rfl) ⟨1724603, by rfl⟩ : syracuseStep 2299471 = 3449207) B3449207
theorem B3449213 : Blo 2299435 3449213 := bbase (se 3 (by rfl) ⟨646727, by rfl⟩ : syracuseStep 3449213 = 1293455) (by norm_num)
theorem B2299475 : Blo 2299435 2299475 := bstep (se 1 (by rfl) ⟨1724606, by rfl⟩ : syracuseStep 2299475 = 3449213) B3449213
theorem B5173829 : Blo 2299435 5173829 := bbase (se 4 (by rfl) ⟨485046, by rfl⟩ : syracuseStep 5173829 = 970093) (by norm_num)
theorem B3449219 : Blo 2299435 3449219 := bstep (se 1 (by rfl) ⟨2586914, by rfl⟩ : syracuseStep 3449219 = 5173829) B5173829
theorem B2299479 : Blo 2299435 2299479 := bstep (se 1 (by rfl) ⟨1724609, by rfl⟩ : syracuseStep 2299479 = 3449219) B3449219
theorem B2455553 : Blo 2299435 2455553 := bbase (se 2 (by rfl) ⟨920832, by rfl⟩ : syracuseStep 2455553 = 1841665) (by norm_num)
theorem B6548141 : Blo 2299435 6548141 := bstep (se 3 (by rfl) ⟨1227776, by rfl⟩ : syracuseStep 6548141 = 2455553) B2455553
theorem B4365427 : Blo 2299435 4365427 := bstep (se 1 (by rfl) ⟨3274070, by rfl⟩ : syracuseStep 4365427 = 6548141) B6548141
theorem B5820569 : Blo 2299435 5820569 := bstep (se 2 (by rfl) ⟨2182713, by rfl⟩ : syracuseStep 5820569 = 4365427) B4365427
theorem B3880379 : Blo 2299435 3880379 := bstep (se 1 (by rfl) ⟨2910284, by rfl⟩ : syracuseStep 3880379 = 5820569) B5820569
theorem B2586919 : Blo 2299435 2586919 := bstep (se 1 (by rfl) ⟨1940189, by rfl⟩ : syracuseStep 2586919 = 3880379) B3880379
theorem B3449225 : Blo 2299435 3449225 := bstep (se 2 (by rfl) ⟨1293459, by rfl⟩ : syracuseStep 3449225 = 2586919) B2586919
theorem B2299483 : Blo 2299435 2299483 := bstep (se 1 (by rfl) ⟨1724612, by rfl⟩ : syracuseStep 2299483 = 3449225) B3449225
theorem B11641157 : Blo 2299435 11641157 := bbase (se 4 (by rfl) ⟨1091358, by rfl⟩ : syracuseStep 11641157 = 2182717) (by norm_num)
theorem B7760771 : Blo 2299435 7760771 := bstep (se 1 (by rfl) ⟨5820578, by rfl⟩ : syracuseStep 7760771 = 11641157) B11641157
theorem B5173847 : Blo 2299435 5173847 := bstep (se 1 (by rfl) ⟨3880385, by rfl⟩ : syracuseStep 5173847 = 7760771) B7760771
theorem B3449231 : Blo 2299435 3449231 := bstep (se 1 (by rfl) ⟨2586923, by rfl⟩ : syracuseStep 3449231 = 5173847) B5173847
theorem B2299487 : Blo 2299435 2299487 := bstep (se 1 (by rfl) ⟨1724615, by rfl⟩ : syracuseStep 2299487 = 3449231) B3449231
theorem B3449237 : Blo 2299435 3449237 := bbase (se 6 (by rfl) ⟨80841, by rfl⟩ : syracuseStep 3449237 = 161683) (by norm_num)
theorem B2299491 : Blo 2299435 2299491 := bstep (se 1 (by rfl) ⟨1724618, by rfl⟩ : syracuseStep 2299491 = 3449237) B3449237
theorem B29868821 : Blo 2299435 29868821 := bbase (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) (by norm_num)
theorem B19912547 : Blo 2299435 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B13275031 : Blo 2299435 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B17700041 : Blo 2299435 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B11800027 : Blo 2299435 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B15733369 : Blo 2299435 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B20977825 : Blo 2299435 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B27970433 : Blo 2299435 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B18646955 : Blo 2299435 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B12431303 : Blo 2299435 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B8287535 : Blo 2299435 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B5525023 : Blo 2299435 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B7366697 : Blo 2299435 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B4911131 : Blo 2299435 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B13096349 : Blo 2299435 13096349 := bstep (se 3 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 13096349 = 4911131) B4911131
theorem B8730899 : Blo 2299435 8730899 := bstep (se 1 (by rfl) ⟨6548174, by rfl⟩ : syracuseStep 8730899 = 13096349) B13096349
theorem B5820599 : Blo 2299435 5820599 := bstep (se 1 (by rfl) ⟨4365449, by rfl⟩ : syracuseStep 5820599 = 8730899) B8730899
theorem B3880399 : Blo 2299435 3880399 := bstep (se 1 (by rfl) ⟨2910299, by rfl⟩ : syracuseStep 3880399 = 5820599) B5820599
theorem B5173865 : Blo 2299435 5173865 := bstep (se 2 (by rfl) ⟨1940199, by rfl⟩ : syracuseStep 5173865 = 3880399) B3880399
theorem B3449243 : Blo 2299435 3449243 := bstep (se 1 (by rfl) ⟨2586932, by rfl⟩ : syracuseStep 3449243 = 5173865) B5173865
theorem B2299495 : Blo 2299435 2299495 := bstep (se 1 (by rfl) ⟨1724621, by rfl⟩ : syracuseStep 2299495 = 3449243) B3449243
theorem B2586937 : Blo 2299435 2586937 := bbase (se 2 (by rfl) ⟨970101, by rfl⟩ : syracuseStep 2586937 = 1940203) (by norm_num)
theorem B3449249 : Blo 2299435 3449249 := bstep (se 2 (by rfl) ⟨1293468, by rfl⟩ : syracuseStep 3449249 = 2586937) B2586937
theorem B2299499 : Blo 2299435 2299499 := bstep (se 1 (by rfl) ⟨1724624, by rfl⟩ : syracuseStep 2299499 = 3449249) B3449249
theorem B6548197 : Blo 2299435 6548197 := bbase (se 4 (by rfl) ⟨613893, by rfl⟩ : syracuseStep 6548197 = 1227787) (by norm_num)
theorem B8730929 : Blo 2299435 8730929 := bstep (se 2 (by rfl) ⟨3274098, by rfl⟩ : syracuseStep 8730929 = 6548197) B6548197
theorem B5820619 : Blo 2299435 5820619 := bstep (se 1 (by rfl) ⟨4365464, by rfl⟩ : syracuseStep 5820619 = 8730929) B8730929
theorem B7760825 : Blo 2299435 7760825 := bstep (se 2 (by rfl) ⟨2910309, by rfl⟩ : syracuseStep 7760825 = 5820619) B5820619
theorem B5173883 : Blo 2299435 5173883 := bstep (se 1 (by rfl) ⟨3880412, by rfl⟩ : syracuseStep 5173883 = 7760825) B7760825
theorem B3449255 : Blo 2299435 3449255 := bstep (se 1 (by rfl) ⟨2586941, by rfl⟩ : syracuseStep 3449255 = 5173883) B5173883
theorem B2299503 : Blo 2299435 2299503 := bstep (se 1 (by rfl) ⟨1724627, by rfl⟩ : syracuseStep 2299503 = 3449255) B3449255
theorem B3449261 : Blo 2299435 3449261 := bbase (se 3 (by rfl) ⟨646736, by rfl⟩ : syracuseStep 3449261 = 1293473) (by norm_num)
theorem B2299507 : Blo 2299435 2299507 := bstep (se 1 (by rfl) ⟨1724630, by rfl⟩ : syracuseStep 2299507 = 3449261) B3449261
theorem B5173901 : Blo 2299435 5173901 := bbase (se 3 (by rfl) ⟨970106, by rfl⟩ : syracuseStep 5173901 = 1940213) (by norm_num)
theorem B3449267 : Blo 2299435 3449267 := bstep (se 1 (by rfl) ⟨2586950, by rfl⟩ : syracuseStep 3449267 = 5173901) B5173901
theorem B2299511 : Blo 2299435 2299511 := bstep (se 1 (by rfl) ⟨1724633, by rfl⟩ : syracuseStep 2299511 = 3449267) B3449267
theorem B2910325 : Blo 2299435 2910325 := bbase (se 5 (by rfl) ⟨136421, by rfl⟩ : syracuseStep 2910325 = 272843) (by norm_num)
theorem B3880433 : Blo 2299435 3880433 := bstep (se 2 (by rfl) ⟨1455162, by rfl⟩ : syracuseStep 3880433 = 2910325) B2910325
theorem B2586955 : Blo 2299435 2586955 := bstep (se 1 (by rfl) ⟨1940216, by rfl⟩ : syracuseStep 2586955 = 3880433) B3880433
theorem B3449273 : Blo 2299435 3449273 := bstep (se 2 (by rfl) ⟨1293477, by rfl⟩ : syracuseStep 3449273 = 2586955) B2586955
theorem B2299515 : Blo 2299435 2299515 := bstep (se 1 (by rfl) ⟨1724636, by rfl⟩ : syracuseStep 2299515 = 3449273) B3449273
theorem B22401845 : Blo 2299435 22401845 := bbase (se 5 (by rfl) ⟨1050086, by rfl⟩ : syracuseStep 22401845 = 2100173) (by norm_num)
theorem B14934563 : Blo 2299435 14934563 := bstep (se 1 (by rfl) ⟨11200922, by rfl⟩ : syracuseStep 14934563 = 22401845) B22401845
theorem B9956375 : Blo 2299435 9956375 := bstep (se 1 (by rfl) ⟨7467281, by rfl⟩ : syracuseStep 9956375 = 14934563) B14934563
theorem B6637583 : Blo 2299435 6637583 := bstep (se 1 (by rfl) ⟨4978187, by rfl⟩ : syracuseStep 6637583 = 9956375) B9956375
theorem B17700221 : Blo 2299435 17700221 := bstep (se 3 (by rfl) ⟨3318791, by rfl⟩ : syracuseStep 17700221 = 6637583) B6637583
theorem B11800147 : Blo 2299435 11800147 := bstep (se 1 (by rfl) ⟨8850110, by rfl⟩ : syracuseStep 11800147 = 17700221) B17700221
theorem B15733529 : Blo 2299435 15733529 := bstep (se 2 (by rfl) ⟨5900073, by rfl⟩ : syracuseStep 15733529 = 11800147) B11800147
theorem B10489019 : Blo 2299435 10489019 := bstep (se 1 (by rfl) ⟨7866764, by rfl⟩ : syracuseStep 10489019 = 15733529) B15733529
theorem B27970717 : Blo 2299435 27970717 := bstep (se 3 (by rfl) ⟨5244509, by rfl⟩ : syracuseStep 27970717 = 10489019) B10489019
theorem B37294289 : Blo 2299435 37294289 := bstep (se 2 (by rfl) ⟨13985358, by rfl⟩ : syracuseStep 37294289 = 27970717) B27970717
theorem B24862859 : Blo 2299435 24862859 := bstep (se 1 (by rfl) ⟨18647144, by rfl⟩ : syracuseStep 24862859 = 37294289) B37294289
theorem B16575239 : Blo 2299435 16575239 := bstep (se 1 (by rfl) ⟨12431429, by rfl⟩ : syracuseStep 16575239 = 24862859) B24862859
theorem B44200637 : Blo 2299435 44200637 := bstep (se 3 (by rfl) ⟨8287619, by rfl⟩ : syracuseStep 44200637 = 16575239) B16575239
theorem B29467091 : Blo 2299435 29467091 := bstep (se 1 (by rfl) ⟨22100318, by rfl⟩ : syracuseStep 29467091 = 44200637) B44200637
theorem B19644727 : Blo 2299435 19644727 := bstep (se 1 (by rfl) ⟨14733545, by rfl⟩ : syracuseStep 19644727 = 29467091) B29467091
theorem B26192969 : Blo 2299435 26192969 := bstep (se 2 (by rfl) ⟨9822363, by rfl⟩ : syracuseStep 26192969 = 19644727) B19644727
theorem B17461979 : Blo 2299435 17461979 := bstep (se 1 (by rfl) ⟨13096484, by rfl⟩ : syracuseStep 17461979 = 26192969) B26192969
theorem B11641319 : Blo 2299435 11641319 := bstep (se 1 (by rfl) ⟨8730989, by rfl⟩ : syracuseStep 11641319 = 17461979) B17461979
theorem B7760879 : Blo 2299435 7760879 := bstep (se 1 (by rfl) ⟨5820659, by rfl⟩ : syracuseStep 7760879 = 11641319) B11641319
theorem B5173919 : Blo 2299435 5173919 := bstep (se 1 (by rfl) ⟨3880439, by rfl⟩ : syracuseStep 5173919 = 7760879) B7760879
theorem B3449279 : Blo 2299435 3449279 := bstep (se 1 (by rfl) ⟨2586959, by rfl⟩ : syracuseStep 3449279 = 5173919) B5173919
theorem B2299519 : Blo 2299435 2299519 := bstep (se 1 (by rfl) ⟨1724639, by rfl⟩ : syracuseStep 2299519 = 3449279) B3449279
theorem B3449285 : Blo 2299435 3449285 := bbase (se 4 (by rfl) ⟨323370, by rfl⟩ : syracuseStep 3449285 = 646741) (by norm_num)
theorem B2299523 : Blo 2299435 2299523 := bstep (se 1 (by rfl) ⟨1724642, by rfl⟩ : syracuseStep 2299523 = 3449285) B3449285
theorem B3880453 : Blo 2299435 3880453 := bbase (se 4 (by rfl) ⟨363792, by rfl⟩ : syracuseStep 3880453 = 727585) (by norm_num)
theorem B5173937 : Blo 2299435 5173937 := bstep (se 2 (by rfl) ⟨1940226, by rfl⟩ : syracuseStep 5173937 = 3880453) B3880453
theorem B3449291 : Blo 2299435 3449291 := bstep (se 1 (by rfl) ⟨2586968, by rfl⟩ : syracuseStep 3449291 = 5173937) B5173937
theorem B2299527 : Blo 2299435 2299527 := bstep (se 1 (by rfl) ⟨1724645, by rfl⟩ : syracuseStep 2299527 = 3449291) B3449291
theorem B2586973 : Blo 2299435 2586973 := bbase (se 3 (by rfl) ⟨485057, by rfl⟩ : syracuseStep 2586973 = 970115) (by norm_num)
theorem B3449297 : Blo 2299435 3449297 := bstep (se 2 (by rfl) ⟨1293486, by rfl⟩ : syracuseStep 3449297 = 2586973) B2586973
theorem B2299531 : Blo 2299435 2299531 := bstep (se 1 (by rfl) ⟨1724648, by rfl⟩ : syracuseStep 2299531 = 3449297) B3449297
theorem B7760933 : Blo 2299435 7760933 := bbase (se 4 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 7760933 = 1455175) (by norm_num)
theorem B5173955 : Blo 2299435 5173955 := bstep (se 1 (by rfl) ⟨3880466, by rfl⟩ : syracuseStep 5173955 = 7760933) B7760933
theorem B3449303 : Blo 2299435 3449303 := bstep (se 1 (by rfl) ⟨2586977, by rfl⟩ : syracuseStep 3449303 = 5173955) B5173955
theorem B2299535 : Blo 2299435 2299535 := bstep (se 1 (by rfl) ⟨1724651, by rfl⟩ : syracuseStep 2299535 = 3449303) B3449303
theorem B3449309 : Blo 2299435 3449309 := bbase (se 3 (by rfl) ⟨646745, by rfl⟩ : syracuseStep 3449309 = 1293491) (by norm_num)
theorem B2299539 : Blo 2299435 2299539 := bstep (se 1 (by rfl) ⟨1724654, by rfl⟩ : syracuseStep 2299539 = 3449309) B3449309
theorem B5173973 : Blo 2299435 5173973 := bbase (se 7 (by rfl) ⟨60632, by rfl⟩ : syracuseStep 5173973 = 121265) (by norm_num)
theorem B3449315 : Blo 2299435 3449315 := bstep (se 1 (by rfl) ⟨2586986, by rfl⟩ : syracuseStep 3449315 = 5173973) B5173973
theorem B2299543 : Blo 2299435 2299543 := bstep (se 1 (by rfl) ⟨1724657, by rfl⟩ : syracuseStep 2299543 = 3449315) B3449315
theorem B9822485 : Blo 2299435 9822485 := bbase (se 6 (by rfl) ⟨230214, by rfl⟩ : syracuseStep 9822485 = 460429) (by norm_num)
theorem B6548323 : Blo 2299435 6548323 := bstep (se 1 (by rfl) ⟨4911242, by rfl⟩ : syracuseStep 6548323 = 9822485) B9822485
theorem B8731097 : Blo 2299435 8731097 := bstep (se 2 (by rfl) ⟨3274161, by rfl⟩ : syracuseStep 8731097 = 6548323) B6548323
theorem B5820731 : Blo 2299435 5820731 := bstep (se 1 (by rfl) ⟨4365548, by rfl⟩ : syracuseStep 5820731 = 8731097) B8731097
theorem B3880487 : Blo 2299435 3880487 := bstep (se 1 (by rfl) ⟨2910365, by rfl⟩ : syracuseStep 3880487 = 5820731) B5820731
theorem B2586991 : Blo 2299435 2586991 := bstep (se 1 (by rfl) ⟨1940243, by rfl⟩ : syracuseStep 2586991 = 3880487) B3880487
theorem B3449321 : Blo 2299435 3449321 := bstep (se 2 (by rfl) ⟨1293495, by rfl⟩ : syracuseStep 3449321 = 2586991) B2586991
theorem B2299547 : Blo 2299435 2299547 := bstep (se 1 (by rfl) ⟨1724660, by rfl⟩ : syracuseStep 2299547 = 3449321) B3449321
theorem B14934773 : Blo 2299435 14934773 := bbase (se 5 (by rfl) ⟨700067, by rfl⟩ : syracuseStep 14934773 = 1400135) (by norm_num)
theorem B9956515 : Blo 2299435 9956515 := bstep (se 1 (by rfl) ⟨7467386, by rfl⟩ : syracuseStep 9956515 = 14934773) B14934773
theorem B13275353 : Blo 2299435 13275353 := bstep (se 2 (by rfl) ⟨4978257, by rfl⟩ : syracuseStep 13275353 = 9956515) B9956515
theorem B8850235 : Blo 2299435 8850235 := bstep (se 1 (by rfl) ⟨6637676, by rfl⟩ : syracuseStep 8850235 = 13275353) B13275353
theorem B11800313 : Blo 2299435 11800313 := bstep (se 2 (by rfl) ⟨4425117, by rfl⟩ : syracuseStep 11800313 = 8850235) B8850235
theorem B7866875 : Blo 2299435 7866875 := bstep (se 1 (by rfl) ⟨5900156, by rfl⟩ : syracuseStep 7866875 = 11800313) B11800313
theorem B5244583 : Blo 2299435 5244583 := bstep (se 1 (by rfl) ⟨3933437, by rfl⟩ : syracuseStep 5244583 = 7866875) B7866875
theorem B6992777 : Blo 2299435 6992777 := bstep (se 2 (by rfl) ⟨2622291, by rfl⟩ : syracuseStep 6992777 = 5244583) B5244583
theorem B18647405 : Blo 2299435 18647405 := bstep (se 3 (by rfl) ⟨3496388, by rfl⟩ : syracuseStep 18647405 = 6992777) B6992777
theorem B12431603 : Blo 2299435 12431603 := bstep (se 1 (by rfl) ⟨9323702, by rfl⟩ : syracuseStep 12431603 = 18647405) B18647405
theorem B33150941 : Blo 2299435 33150941 := bstep (se 3 (by rfl) ⟨6215801, by rfl⟩ : syracuseStep 33150941 = 12431603) B12431603
theorem B22100627 : Blo 2299435 22100627 := bstep (se 1 (by rfl) ⟨16575470, by rfl⟩ : syracuseStep 22100627 = 33150941) B33150941
theorem B14733751 : Blo 2299435 14733751 := bstep (se 1 (by rfl) ⟨11050313, by rfl⟩ : syracuseStep 14733751 = 22100627) B22100627
theorem B19645001 : Blo 2299435 19645001 := bstep (se 2 (by rfl) ⟨7366875, by rfl⟩ : syracuseStep 19645001 = 14733751) B14733751
theorem B13096667 : Blo 2299435 13096667 := bstep (se 1 (by rfl) ⟨9822500, by rfl⟩ : syracuseStep 13096667 = 19645001) B19645001
theorem B8731111 : Blo 2299435 8731111 := bstep (se 1 (by rfl) ⟨6548333, by rfl⟩ : syracuseStep 8731111 = 13096667) B13096667
theorem B11641481 : Blo 2299435 11641481 := bstep (se 2 (by rfl) ⟨4365555, by rfl⟩ : syracuseStep 11641481 = 8731111) B8731111
theorem B7760987 : Blo 2299435 7760987 := bstep (se 1 (by rfl) ⟨5820740, by rfl⟩ : syracuseStep 7760987 = 11641481) B11641481
theorem B5173991 : Blo 2299435 5173991 := bstep (se 1 (by rfl) ⟨3880493, by rfl⟩ : syracuseStep 5173991 = 7760987) B7760987
theorem B3449327 : Blo 2299435 3449327 := bstep (se 1 (by rfl) ⟨2586995, by rfl⟩ : syracuseStep 3449327 = 5173991) B5173991
theorem B2299551 : Blo 2299435 2299551 := bstep (se 1 (by rfl) ⟨1724663, by rfl⟩ : syracuseStep 2299551 = 3449327) B3449327
theorem B3449333 : Blo 2299435 3449333 := bbase (se 5 (by rfl) ⟨161687, by rfl⟩ : syracuseStep 3449333 = 323375) (by norm_num)
theorem B2299555 : Blo 2299435 2299555 := bstep (se 1 (by rfl) ⟨1724666, by rfl⟩ : syracuseStep 2299555 = 3449333) B3449333
theorem B6548357 : Blo 2299435 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B4365571 : Blo 2299435 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B5820761 : Blo 2299435 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B3880507 : Blo 2299435 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B5174009 : Blo 2299435 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B3449339 : Blo 2299435 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B2299559 : Blo 2299435 2299559 := bstep (se 1 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 2299559 = 3449339) B3449339
theorem B2587009 : Blo 2299435 2587009 := bbase (se 2 (by rfl) ⟨970128, by rfl⟩ : syracuseStep 2587009 = 1940257) (by norm_num)
theorem B3449345 : Blo 2299435 3449345 := bstep (se 2 (by rfl) ⟨1293504, by rfl⟩ : syracuseStep 3449345 = 2587009) B2587009
theorem B2299563 : Blo 2299435 2299563 := bstep (se 1 (by rfl) ⟨1724672, by rfl⟩ : syracuseStep 2299563 = 3449345) B3449345
theorem B5820781 : Blo 2299435 5820781 := bbase (se 3 (by rfl) ⟨1091396, by rfl⟩ : syracuseStep 5820781 = 2182793) (by norm_num)
theorem B7761041 : Blo 2299435 7761041 := bstep (se 2 (by rfl) ⟨2910390, by rfl⟩ : syracuseStep 7761041 = 5820781) B5820781
theorem B5174027 : Blo 2299435 5174027 := bstep (se 1 (by rfl) ⟨3880520, by rfl⟩ : syracuseStep 5174027 = 7761041) B7761041
theorem B3449351 : Blo 2299435 3449351 := bstep (se 1 (by rfl) ⟨2587013, by rfl⟩ : syracuseStep 3449351 = 5174027) B5174027
theorem B2299567 : Blo 2299435 2299567 := bstep (se 1 (by rfl) ⟨1724675, by rfl⟩ : syracuseStep 2299567 = 3449351) B3449351
theorem B3449357 : Blo 2299435 3449357 := bbase (se 3 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 3449357 = 1293509) (by norm_num)
theorem B2299571 : Blo 2299435 2299571 := bstep (se 1 (by rfl) ⟨1724678, by rfl⟩ : syracuseStep 2299571 = 3449357) B3449357
theorem B5174045 : Blo 2299435 5174045 := bbase (se 3 (by rfl) ⟨970133, by rfl⟩ : syracuseStep 5174045 = 1940267) (by norm_num)
theorem B3449363 : Blo 2299435 3449363 := bstep (se 1 (by rfl) ⟨2587022, by rfl⟩ : syracuseStep 3449363 = 5174045) B5174045
theorem B2299575 : Blo 2299435 2299575 := bstep (se 1 (by rfl) ⟨1724681, by rfl⟩ : syracuseStep 2299575 = 3449363) B3449363
theorem B3880541 : Blo 2299435 3880541 := bbase (se 3 (by rfl) ⟨727601, by rfl⟩ : syracuseStep 3880541 = 1455203) (by norm_num)
theorem B2587027 : Blo 2299435 2587027 := bstep (se 1 (by rfl) ⟨1940270, by rfl⟩ : syracuseStep 2587027 = 3880541) B3880541
theorem B3449369 : Blo 2299435 3449369 := bstep (se 2 (by rfl) ⟨1293513, by rfl⟩ : syracuseStep 3449369 = 2587027) B2587027
theorem B2299579 : Blo 2299435 2299579 := bstep (se 1 (by rfl) ⟨1724684, by rfl⟩ : syracuseStep 2299579 = 3449369) B3449369
theorem B2762617 : Blo 2299435 2762617 := bbase (se 2 (by rfl) ⟨1035981, by rfl⟩ : syracuseStep 2762617 = 2071963) (by norm_num)
theorem B3683489 : Blo 2299435 3683489 := bstep (se 2 (by rfl) ⟨1381308, by rfl⟩ : syracuseStep 3683489 = 2762617) B2762617
theorem B9822637 : Blo 2299435 9822637 := bstep (se 3 (by rfl) ⟨1841744, by rfl⟩ : syracuseStep 9822637 = 3683489) B3683489
theorem B13096849 : Blo 2299435 13096849 := bstep (se 2 (by rfl) ⟨4911318, by rfl⟩ : syracuseStep 13096849 = 9822637) B9822637
theorem B17462465 : Blo 2299435 17462465 := bstep (se 2 (by rfl) ⟨6548424, by rfl⟩ : syracuseStep 17462465 = 13096849) B13096849
theorem B11641643 : Blo 2299435 11641643 := bstep (se 1 (by rfl) ⟨8731232, by rfl⟩ : syracuseStep 11641643 = 17462465) B17462465
theorem B7761095 : Blo 2299435 7761095 := bstep (se 1 (by rfl) ⟨5820821, by rfl⟩ : syracuseStep 7761095 = 11641643) B11641643
theorem B5174063 : Blo 2299435 5174063 := bstep (se 1 (by rfl) ⟨3880547, by rfl⟩ : syracuseStep 5174063 = 7761095) B7761095
theorem B3449375 : Blo 2299435 3449375 := bstep (se 1 (by rfl) ⟨2587031, by rfl⟩ : syracuseStep 3449375 = 5174063) B5174063
theorem B2299583 : Blo 2299435 2299583 := bstep (se 1 (by rfl) ⟨1724687, by rfl⟩ : syracuseStep 2299583 = 3449375) B3449375
theorem B3449381 : Blo 2299435 3449381 := bbase (se 4 (by rfl) ⟨323379, by rfl⟩ : syracuseStep 3449381 = 646759) (by norm_num)
theorem B2299587 : Blo 2299435 2299587 := bstep (se 1 (by rfl) ⟨1724690, by rfl⟩ : syracuseStep 2299587 = 3449381) B3449381
theorem B2910421 : Blo 2299435 2910421 := bbase (se 7 (by rfl) ⟨34106, by rfl⟩ : syracuseStep 2910421 = 68213) (by norm_num)
theorem B3880561 : Blo 2299435 3880561 := bstep (se 2 (by rfl) ⟨1455210, by rfl⟩ : syracuseStep 3880561 = 2910421) B2910421
theorem B5174081 : Blo 2299435 5174081 := bstep (se 2 (by rfl) ⟨1940280, by rfl⟩ : syracuseStep 5174081 = 3880561) B3880561
theorem B3449387 : Blo 2299435 3449387 := bstep (se 1 (by rfl) ⟨2587040, by rfl⟩ : syracuseStep 3449387 = 5174081) B5174081
theorem B2299591 : Blo 2299435 2299591 := bstep (se 1 (by rfl) ⟨1724693, by rfl⟩ : syracuseStep 2299591 = 3449387) B3449387
theorem B2587045 : Blo 2299435 2587045 := bbase (se 4 (by rfl) ⟨242535, by rfl⟩ : syracuseStep 2587045 = 485071) (by norm_num)
theorem B3449393 : Blo 2299435 3449393 := bstep (se 2 (by rfl) ⟨1293522, by rfl⟩ : syracuseStep 3449393 = 2587045) B2587045
theorem B2299595 : Blo 2299435 2299595 := bstep (se 1 (by rfl) ⟨1724696, by rfl⟩ : syracuseStep 2299595 = 3449393) B3449393
theorem B11800565 : Blo 2299435 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B7867043 : Blo 2299435 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B5244695 : Blo 2299435 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B3496463 : Blo 2299435 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B2330975 : Blo 2299435 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B6215933 : Blo 2299435 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B4143955 : Blo 2299435 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B5525273 : Blo 2299435 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B14734061 : Blo 2299435 14734061 := bstep (se 3 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 14734061 = 5525273) B5525273
theorem B9822707 : Blo 2299435 9822707 := bstep (se 1 (by rfl) ⟨7367030, by rfl⟩ : syracuseStep 9822707 = 14734061) B14734061
theorem B6548471 : Blo 2299435 6548471 := bstep (se 1 (by rfl) ⟨4911353, by rfl⟩ : syracuseStep 6548471 = 9822707) B9822707
theorem B4365647 : Blo 2299435 4365647 := bstep (se 1 (by rfl) ⟨3274235, by rfl⟩ : syracuseStep 4365647 = 6548471) B6548471
theorem B2910431 : Blo 2299435 2910431 := bstep (se 1 (by rfl) ⟨2182823, by rfl⟩ : syracuseStep 2910431 = 4365647) B4365647
theorem B7761149 : Blo 2299435 7761149 := bstep (se 3 (by rfl) ⟨1455215, by rfl⟩ : syracuseStep 7761149 = 2910431) B2910431
theorem B5174099 : Blo 2299435 5174099 := bstep (se 1 (by rfl) ⟨3880574, by rfl⟩ : syracuseStep 5174099 = 7761149) B7761149
theorem B3449399 : Blo 2299435 3449399 := bstep (se 1 (by rfl) ⟨2587049, by rfl⟩ : syracuseStep 3449399 = 5174099) B5174099
theorem B2299599 : Blo 2299435 2299599 := bstep (se 1 (by rfl) ⟨1724699, by rfl⟩ : syracuseStep 2299599 = 3449399) B3449399
theorem B3449405 : Blo 2299435 3449405 := bbase (se 3 (by rfl) ⟨646763, by rfl⟩ : syracuseStep 3449405 = 1293527) (by norm_num)
theorem B2299603 : Blo 2299435 2299603 := bstep (se 1 (by rfl) ⟨1724702, by rfl⟩ : syracuseStep 2299603 = 3449405) B3449405
theorem B5174117 : Blo 2299435 5174117 := bbase (se 4 (by rfl) ⟨485073, by rfl⟩ : syracuseStep 5174117 = 970147) (by norm_num)
theorem B3449411 : Blo 2299435 3449411 := bstep (se 1 (by rfl) ⟨2587058, by rfl⟩ : syracuseStep 3449411 = 5174117) B5174117
theorem B2299607 : Blo 2299435 2299607 := bstep (se 1 (by rfl) ⟨1724705, by rfl⟩ : syracuseStep 2299607 = 3449411) B3449411
theorem B5820893 : Blo 2299435 5820893 := bbase (se 3 (by rfl) ⟨1091417, by rfl⟩ : syracuseStep 5820893 = 2182835) (by norm_num)
theorem B3880595 : Blo 2299435 3880595 := bstep (se 1 (by rfl) ⟨2910446, by rfl⟩ : syracuseStep 3880595 = 5820893) B5820893
theorem B2587063 : Blo 2299435 2587063 := bstep (se 1 (by rfl) ⟨1940297, by rfl⟩ : syracuseStep 2587063 = 3880595) B3880595
theorem B3449417 : Blo 2299435 3449417 := bstep (se 2 (by rfl) ⟨1293531, by rfl⟩ : syracuseStep 3449417 = 2587063) B2587063
theorem B2299611 : Blo 2299435 2299611 := bstep (se 1 (by rfl) ⟨1724708, by rfl⟩ : syracuseStep 2299611 = 3449417) B3449417
theorem B4365677 : Blo 2299435 4365677 := bbase (se 3 (by rfl) ⟨818564, by rfl⟩ : syracuseStep 4365677 = 1637129) (by norm_num)
theorem B11641805 : Blo 2299435 11641805 := bstep (se 3 (by rfl) ⟨2182838, by rfl⟩ : syracuseStep 11641805 = 4365677) B4365677
theorem B7761203 : Blo 2299435 7761203 := bstep (se 1 (by rfl) ⟨5820902, by rfl⟩ : syracuseStep 7761203 = 11641805) B11641805
theorem B5174135 : Blo 2299435 5174135 := bstep (se 1 (by rfl) ⟨3880601, by rfl⟩ : syracuseStep 5174135 = 7761203) B7761203
theorem B3449423 : Blo 2299435 3449423 := bstep (se 1 (by rfl) ⟨2587067, by rfl⟩ : syracuseStep 3449423 = 5174135) B5174135
theorem B2299615 : Blo 2299435 2299615 := bstep (se 1 (by rfl) ⟨1724711, by rfl⟩ : syracuseStep 2299615 = 3449423) B3449423
theorem B3449429 : Blo 2299435 3449429 := bbase (se 8 (by rfl) ⟨20211, by rfl⟩ : syracuseStep 3449429 = 40423) (by norm_num)
theorem B2299619 : Blo 2299435 2299619 := bstep (se 1 (by rfl) ⟨1724714, by rfl⟩ : syracuseStep 2299619 = 3449429) B3449429
theorem B11050661 : Blo 2299435 11050661 := bbase (se 4 (by rfl) ⟨1035999, by rfl⟩ : syracuseStep 11050661 = 2071999) (by norm_num)
theorem B7367107 : Blo 2299435 7367107 := bstep (se 1 (by rfl) ⟨5525330, by rfl⟩ : syracuseStep 7367107 = 11050661) B11050661
theorem B9822809 : Blo 2299435 9822809 := bstep (se 2 (by rfl) ⟨3683553, by rfl⟩ : syracuseStep 9822809 = 7367107) B7367107
theorem B6548539 : Blo 2299435 6548539 := bstep (se 1 (by rfl) ⟨4911404, by rfl⟩ : syracuseStep 6548539 = 9822809) B9822809
theorem B8731385 : Blo 2299435 8731385 := bstep (se 2 (by rfl) ⟨3274269, by rfl⟩ : syracuseStep 8731385 = 6548539) B6548539
theorem B5820923 : Blo 2299435 5820923 := bstep (se 1 (by rfl) ⟨4365692, by rfl⟩ : syracuseStep 5820923 = 8731385) B8731385
theorem B3880615 : Blo 2299435 3880615 := bstep (se 1 (by rfl) ⟨2910461, by rfl⟩ : syracuseStep 3880615 = 5820923) B5820923
theorem B5174153 : Blo 2299435 5174153 := bstep (se 2 (by rfl) ⟨1940307, by rfl⟩ : syracuseStep 5174153 = 3880615) B3880615
theorem B3449435 : Blo 2299435 3449435 := bstep (se 1 (by rfl) ⟨2587076, by rfl⟩ : syracuseStep 3449435 = 5174153) B5174153
theorem B2299623 : Blo 2299435 2299623 := bstep (se 1 (by rfl) ⟨1724717, by rfl⟩ : syracuseStep 2299623 = 3449435) B3449435
theorem B2587081 : Blo 2299435 2587081 := bbase (se 2 (by rfl) ⟨970155, by rfl⟩ : syracuseStep 2587081 = 1940311) (by norm_num)
theorem B3449441 : Blo 2299435 3449441 := bstep (se 2 (by rfl) ⟨1293540, by rfl⟩ : syracuseStep 3449441 = 2587081) B2587081
theorem B2299627 : Blo 2299435 2299627 := bstep (se 1 (by rfl) ⟨1724720, by rfl⟩ : syracuseStep 2299627 = 3449441) B3449441
theorem B19645685 : Blo 2299435 19645685 := bbase (se 5 (by rfl) ⟨920891, by rfl⟩ : syracuseStep 19645685 = 1841783) (by norm_num)
theorem B13097123 : Blo 2299435 13097123 := bstep (se 1 (by rfl) ⟨9822842, by rfl⟩ : syracuseStep 13097123 = 19645685) B19645685
theorem B8731415 : Blo 2299435 8731415 := bstep (se 1 (by rfl) ⟨6548561, by rfl⟩ : syracuseStep 8731415 = 13097123) B13097123
theorem B5820943 : Blo 2299435 5820943 := bstep (se 1 (by rfl) ⟨4365707, by rfl⟩ : syracuseStep 5820943 = 8731415) B8731415
theorem B7761257 : Blo 2299435 7761257 := bstep (se 2 (by rfl) ⟨2910471, by rfl⟩ : syracuseStep 7761257 = 5820943) B5820943
theorem B5174171 : Blo 2299435 5174171 := bstep (se 1 (by rfl) ⟨3880628, by rfl⟩ : syracuseStep 5174171 = 7761257) B7761257
theorem B3449447 : Blo 2299435 3449447 := bstep (se 1 (by rfl) ⟨2587085, by rfl⟩ : syracuseStep 3449447 = 5174171) B5174171
theorem B2299631 : Blo 2299435 2299631 := bstep (se 1 (by rfl) ⟨1724723, by rfl⟩ : syracuseStep 2299631 = 3449447) B3449447
theorem B3449453 : Blo 2299435 3449453 := bbase (se 3 (by rfl) ⟨646772, by rfl⟩ : syracuseStep 3449453 = 1293545) (by norm_num)
theorem B2299635 : Blo 2299435 2299635 := bstep (se 1 (by rfl) ⟨1724726, by rfl⟩ : syracuseStep 2299635 = 3449453) B3449453
theorem B5174189 : Blo 2299435 5174189 := bbase (se 3 (by rfl) ⟨970160, by rfl⟩ : syracuseStep 5174189 = 1940321) (by norm_num)
theorem B3449459 : Blo 2299435 3449459 := bstep (se 1 (by rfl) ⟨2587094, by rfl⟩ : syracuseStep 3449459 = 5174189) B5174189
theorem B2299639 : Blo 2299435 2299639 := bstep (se 1 (by rfl) ⟨1724729, by rfl⟩ : syracuseStep 2299639 = 3449459) B3449459
theorem B6548597 : Blo 2299435 6548597 := bbase (se 5 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 6548597 = 613931) (by norm_num)
theorem B4365731 : Blo 2299435 4365731 := bstep (se 1 (by rfl) ⟨3274298, by rfl⟩ : syracuseStep 4365731 = 6548597) B6548597
theorem B2910487 : Blo 2299435 2910487 := bstep (se 1 (by rfl) ⟨2182865, by rfl⟩ : syracuseStep 2910487 = 4365731) B4365731
theorem B3880649 : Blo 2299435 3880649 := bstep (se 2 (by rfl) ⟨1455243, by rfl⟩ : syracuseStep 3880649 = 2910487) B2910487
theorem B2587099 : Blo 2299435 2587099 := bstep (se 1 (by rfl) ⟨1940324, by rfl⟩ : syracuseStep 2587099 = 3880649) B3880649
theorem B3449465 : Blo 2299435 3449465 := bstep (se 2 (by rfl) ⟨1293549, by rfl⟩ : syracuseStep 3449465 = 2587099) B2587099
theorem B2299643 : Blo 2299435 2299643 := bstep (se 1 (by rfl) ⟨1724732, by rfl⟩ : syracuseStep 2299643 = 3449465) B3449465
theorem B2950201 : Blo 2299435 2950201 := bbase (se 2 (by rfl) ⟨1106325, by rfl⟩ : syracuseStep 2950201 = 2212651) (by norm_num)
theorem B15734405 : Blo 2299435 15734405 := bstep (se 4 (by rfl) ⟨1475100, by rfl⟩ : syracuseStep 15734405 = 2950201) B2950201
theorem B10489603 : Blo 2299435 10489603 := bstep (se 1 (by rfl) ⟨7867202, by rfl⟩ : syracuseStep 10489603 = 15734405) B15734405
theorem B13986137 : Blo 2299435 13986137 := bstep (se 2 (by rfl) ⟨5244801, by rfl⟩ : syracuseStep 13986137 = 10489603) B10489603
theorem B9324091 : Blo 2299435 9324091 := bstep (se 1 (by rfl) ⟨6993068, by rfl⟩ : syracuseStep 9324091 = 13986137) B13986137
theorem B49728485 : Blo 2299435 49728485 := bstep (se 4 (by rfl) ⟨4662045, by rfl⟩ : syracuseStep 49728485 = 9324091) B9324091
theorem B33152323 : Blo 2299435 33152323 := bstep (se 1 (by rfl) ⟨24864242, by rfl⟩ : syracuseStep 33152323 = 49728485) B49728485
theorem B44203097 : Blo 2299435 44203097 := bstep (se 2 (by rfl) ⟨16576161, by rfl⟩ : syracuseStep 44203097 = 33152323) B33152323
theorem B29468731 : Blo 2299435 29468731 := bstep (se 1 (by rfl) ⟨22101548, by rfl⟩ : syracuseStep 29468731 = 44203097) B44203097
theorem B39291641 : Blo 2299435 39291641 := bstep (se 2 (by rfl) ⟨14734365, by rfl⟩ : syracuseStep 39291641 = 29468731) B29468731
theorem B26194427 : Blo 2299435 26194427 := bstep (se 1 (by rfl) ⟨19645820, by rfl⟩ : syracuseStep 26194427 = 39291641) B39291641
theorem B17462951 : Blo 2299435 17462951 := bstep (se 1 (by rfl) ⟨13097213, by rfl⟩ : syracuseStep 17462951 = 26194427) B26194427
theorem B11641967 : Blo 2299435 11641967 := bstep (se 1 (by rfl) ⟨8731475, by rfl⟩ : syracuseStep 11641967 = 17462951) B17462951
theorem B7761311 : Blo 2299435 7761311 := bstep (se 1 (by rfl) ⟨5820983, by rfl⟩ : syracuseStep 7761311 = 11641967) B11641967
theorem B5174207 : Blo 2299435 5174207 := bstep (se 1 (by rfl) ⟨3880655, by rfl⟩ : syracuseStep 5174207 = 7761311) B7761311
theorem B3449471 : Blo 2299435 3449471 := bstep (se 1 (by rfl) ⟨2587103, by rfl⟩ : syracuseStep 3449471 = 5174207) B5174207
theorem B2299647 : Blo 2299435 2299647 := bstep (se 1 (by rfl) ⟨1724735, by rfl⟩ : syracuseStep 2299647 = 3449471) B3449471
theorem B3449477 : Blo 2299435 3449477 := bbase (se 4 (by rfl) ⟨323388, by rfl⟩ : syracuseStep 3449477 = 646777) (by norm_num)
theorem B2299651 : Blo 2299435 2299651 := bstep (se 1 (by rfl) ⟨1724738, by rfl⟩ : syracuseStep 2299651 = 3449477) B3449477
theorem B3880669 : Blo 2299435 3880669 := bbase (se 3 (by rfl) ⟨727625, by rfl⟩ : syracuseStep 3880669 = 1455251) (by norm_num)
theorem B5174225 : Blo 2299435 5174225 := bstep (se 2 (by rfl) ⟨1940334, by rfl⟩ : syracuseStep 5174225 = 3880669) B3880669
theorem B3449483 : Blo 2299435 3449483 := bstep (se 1 (by rfl) ⟨2587112, by rfl⟩ : syracuseStep 3449483 = 5174225) B5174225
theorem B2299655 : Blo 2299435 2299655 := bstep (se 1 (by rfl) ⟨1724741, by rfl⟩ : syracuseStep 2299655 = 3449483) B3449483
theorem B2587117 : Blo 2299435 2587117 := bbase (se 3 (by rfl) ⟨485084, by rfl⟩ : syracuseStep 2587117 = 970169) (by norm_num)
theorem B3449489 : Blo 2299435 3449489 := bstep (se 2 (by rfl) ⟨1293558, by rfl⟩ : syracuseStep 3449489 = 2587117) B2587117
theorem B2299659 : Blo 2299435 2299659 := bstep (se 1 (by rfl) ⟨1724744, by rfl⟩ : syracuseStep 2299659 = 3449489) B3449489
theorem B7761365 : Blo 2299435 7761365 := bbase (se 7 (by rfl) ⟨90953, by rfl⟩ : syracuseStep 7761365 = 181907) (by norm_num)
theorem B5174243 : Blo 2299435 5174243 := bstep (se 1 (by rfl) ⟨3880682, by rfl⟩ : syracuseStep 5174243 = 7761365) B7761365
theorem B3449495 : Blo 2299435 3449495 := bstep (se 1 (by rfl) ⟨2587121, by rfl⟩ : syracuseStep 3449495 = 5174243) B5174243
theorem B2299663 : Blo 2299435 2299663 := bstep (se 1 (by rfl) ⟨1724747, by rfl⟩ : syracuseStep 2299663 = 3449495) B3449495
theorem B3449501 : Blo 2299435 3449501 := bbase (se 3 (by rfl) ⟨646781, by rfl⟩ : syracuseStep 3449501 = 1293563) (by norm_num)
theorem B2299667 : Blo 2299435 2299667 := bstep (se 1 (by rfl) ⟨1724750, by rfl⟩ : syracuseStep 2299667 = 3449501) B3449501
theorem B5174261 : Blo 2299435 5174261 := bbase (se 5 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 5174261 = 485087) (by norm_num)
theorem B3449507 : Blo 2299435 3449507 := bstep (se 1 (by rfl) ⟨2587130, by rfl⟩ : syracuseStep 3449507 = 5174261) B5174261
theorem B2299671 : Blo 2299435 2299671 := bstep (se 1 (by rfl) ⟨1724753, by rfl⟩ : syracuseStep 2299671 = 3449507) B3449507
theorem B2622433 : Blo 2299435 2622433 := bbase (se 2 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 2622433 = 1966825) (by norm_num)
theorem B55945237 : Blo 2299435 55945237 := bstep (se 6 (by rfl) ⟨1311216, by rfl⟩ : syracuseStep 55945237 = 2622433) B2622433
theorem B74593649 : Blo 2299435 74593649 := bstep (se 2 (by rfl) ⟨27972618, by rfl⟩ : syracuseStep 74593649 = 55945237) B55945237
theorem B49729099 : Blo 2299435 49729099 := bstep (se 1 (by rfl) ⟨37296824, by rfl⟩ : syracuseStep 49729099 = 74593649) B74593649
theorem B66305465 : Blo 2299435 66305465 := bstep (se 2 (by rfl) ⟨24864549, by rfl⟩ : syracuseStep 66305465 = 49729099) B49729099
theorem B44203643 : Blo 2299435 44203643 := bstep (se 1 (by rfl) ⟨33152732, by rfl⟩ : syracuseStep 44203643 = 66305465) B66305465
theorem B29469095 : Blo 2299435 29469095 := bstep (se 1 (by rfl) ⟨22101821, by rfl⟩ : syracuseStep 29469095 = 44203643) B44203643
theorem B19646063 : Blo 2299435 19646063 := bstep (se 1 (by rfl) ⟨14734547, by rfl⟩ : syracuseStep 19646063 = 29469095) B29469095
theorem B13097375 : Blo 2299435 13097375 := bstep (se 1 (by rfl) ⟨9823031, by rfl⟩ : syracuseStep 13097375 = 19646063) B19646063
theorem B8731583 : Blo 2299435 8731583 := bstep (se 1 (by rfl) ⟨6548687, by rfl⟩ : syracuseStep 8731583 = 13097375) B13097375
theorem B5821055 : Blo 2299435 5821055 := bstep (se 1 (by rfl) ⟨4365791, by rfl⟩ : syracuseStep 5821055 = 8731583) B8731583
theorem B3880703 : Blo 2299435 3880703 := bstep (se 1 (by rfl) ⟨2910527, by rfl⟩ : syracuseStep 3880703 = 5821055) B5821055
theorem B2587135 : Blo 2299435 2587135 := bstep (se 1 (by rfl) ⟨1940351, by rfl⟩ : syracuseStep 2587135 = 3880703) B3880703
theorem B3449513 : Blo 2299435 3449513 := bstep (se 2 (by rfl) ⟨1293567, by rfl⟩ : syracuseStep 3449513 = 2587135) B2587135
theorem B2299675 : Blo 2299435 2299675 := bstep (se 1 (by rfl) ⟨1724756, by rfl⟩ : syracuseStep 2299675 = 3449513) B3449513
theorem B3274349 : Blo 2299435 3274349 := bbase (se 3 (by rfl) ⟨613940, by rfl⟩ : syracuseStep 3274349 = 1227881) (by norm_num)
theorem B8731597 : Blo 2299435 8731597 := bstep (se 3 (by rfl) ⟨1637174, by rfl⟩ : syracuseStep 8731597 = 3274349) B3274349
theorem B11642129 : Blo 2299435 11642129 := bstep (se 2 (by rfl) ⟨4365798, by rfl⟩ : syracuseStep 11642129 = 8731597) B8731597
theorem B7761419 : Blo 2299435 7761419 := bstep (se 1 (by rfl) ⟨5821064, by rfl⟩ : syracuseStep 7761419 = 11642129) B11642129
theorem B5174279 : Blo 2299435 5174279 := bstep (se 1 (by rfl) ⟨3880709, by rfl⟩ : syracuseStep 5174279 = 7761419) B7761419
theorem B3449519 : Blo 2299435 3449519 := bstep (se 1 (by rfl) ⟨2587139, by rfl⟩ : syracuseStep 3449519 = 5174279) B5174279
theorem B2299679 : Blo 2299435 2299679 := bstep (se 1 (by rfl) ⟨1724759, by rfl⟩ : syracuseStep 2299679 = 3449519) B3449519
theorem B3449525 : Blo 2299435 3449525 := bbase (se 5 (by rfl) ⟨161696, by rfl⟩ : syracuseStep 3449525 = 323393) (by norm_num)
theorem B2299683 : Blo 2299435 2299683 := bstep (se 1 (by rfl) ⟨1724762, by rfl⟩ : syracuseStep 2299683 = 3449525) B3449525
theorem B5821085 : Blo 2299435 5821085 := bbase (se 3 (by rfl) ⟨1091453, by rfl⟩ : syracuseStep 5821085 = 2182907) (by norm_num)
theorem B3880723 : Blo 2299435 3880723 := bstep (se 1 (by rfl) ⟨2910542, by rfl⟩ : syracuseStep 3880723 = 5821085) B5821085
theorem B5174297 : Blo 2299435 5174297 := bstep (se 2 (by rfl) ⟨1940361, by rfl⟩ : syracuseStep 5174297 = 3880723) B3880723
theorem B3449531 : Blo 2299435 3449531 := bstep (se 1 (by rfl) ⟨2587148, by rfl⟩ : syracuseStep 3449531 = 5174297) B5174297
theorem B2299687 : Blo 2299435 2299687 := bstep (se 1 (by rfl) ⟨1724765, by rfl⟩ : syracuseStep 2299687 = 3449531) B3449531
theorem B2587153 : Blo 2299435 2587153 := bbase (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) (by norm_num)
theorem B3449537 : Blo 2299435 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B2299691 : Blo 2299435 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B4365829 : Blo 2299435 4365829 := bbase (se 4 (by rfl) ⟨409296, by rfl⟩ : syracuseStep 4365829 = 818593) (by norm_num)
theorem B5821105 : Blo 2299435 5821105 := bstep (se 2 (by rfl) ⟨2182914, by rfl⟩ : syracuseStep 5821105 = 4365829) B4365829
theorem B7761473 : Blo 2299435 7761473 := bstep (se 2 (by rfl) ⟨2910552, by rfl⟩ : syracuseStep 7761473 = 5821105) B5821105
theorem B5174315 : Blo 2299435 5174315 := bstep (se 1 (by rfl) ⟨3880736, by rfl⟩ : syracuseStep 5174315 = 7761473) B7761473
theorem B3449543 : Blo 2299435 3449543 := bstep (se 1 (by rfl) ⟨2587157, by rfl⟩ : syracuseStep 3449543 = 5174315) B5174315
theorem B2299695 : Blo 2299435 2299695 := bstep (se 1 (by rfl) ⟨1724771, by rfl⟩ : syracuseStep 2299695 = 3449543) B3449543
theorem B3449549 : Blo 2299435 3449549 := bbase (se 3 (by rfl) ⟨646790, by rfl⟩ : syracuseStep 3449549 = 1293581) (by norm_num)
theorem B2299699 : Blo 2299435 2299699 := bstep (se 1 (by rfl) ⟨1724774, by rfl⟩ : syracuseStep 2299699 = 3449549) B3449549
theorem B5174333 : Blo 2299435 5174333 := bbase (se 3 (by rfl) ⟨970187, by rfl⟩ : syracuseStep 5174333 = 1940375) (by norm_num)
theorem B3449555 : Blo 2299435 3449555 := bstep (se 1 (by rfl) ⟨2587166, by rfl⟩ : syracuseStep 3449555 = 5174333) B5174333
theorem B2299703 : Blo 2299435 2299703 := bstep (se 1 (by rfl) ⟨1724777, by rfl⟩ : syracuseStep 2299703 = 3449555) B3449555
theorem B3880757 : Blo 2299435 3880757 := bbase (se 5 (by rfl) ⟨181910, by rfl⟩ : syracuseStep 3880757 = 363821) (by norm_num)
theorem B2587171 : Blo 2299435 2587171 := bstep (se 1 (by rfl) ⟨1940378, by rfl⟩ : syracuseStep 2587171 = 3880757) B3880757
theorem B3449561 : Blo 2299435 3449561 := bstep (se 2 (by rfl) ⟨1293585, by rfl⟩ : syracuseStep 3449561 = 2587171) B2587171
theorem B2299707 : Blo 2299435 2299707 := bstep (se 1 (by rfl) ⟨1724780, by rfl⟩ : syracuseStep 2299707 = 3449561) B3449561
theorem B6548789 : Blo 2299435 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B17463437 : Blo 2299435 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B11642291 : Blo 2299435 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B7761527 : Blo 2299435 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B5174351 : Blo 2299435 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B3449567 : Blo 2299435 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B2299711 : Blo 2299435 2299711 := bstep (se 1 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 2299711 = 3449567) B3449567
theorem B3449573 : Blo 2299435 3449573 := bbase (se 4 (by rfl) ⟨323397, by rfl⟩ : syracuseStep 3449573 = 646795) (by norm_num)
theorem B2299715 : Blo 2299435 2299715 := bstep (se 1 (by rfl) ⟨1724786, by rfl⟩ : syracuseStep 2299715 = 3449573) B3449573
theorem B2455805 : Blo 2299435 2455805 := bbase (se 3 (by rfl) ⟨460463, by rfl⟩ : syracuseStep 2455805 = 920927) (by norm_num)
theorem B6548813 : Blo 2299435 6548813 := bstep (se 3 (by rfl) ⟨1227902, by rfl⟩ : syracuseStep 6548813 = 2455805) B2455805
theorem B4365875 : Blo 2299435 4365875 := bstep (se 1 (by rfl) ⟨3274406, by rfl⟩ : syracuseStep 4365875 = 6548813) B6548813
theorem B2910583 : Blo 2299435 2910583 := bstep (se 1 (by rfl) ⟨2182937, by rfl⟩ : syracuseStep 2910583 = 4365875) B4365875
theorem B3880777 : Blo 2299435 3880777 := bstep (se 2 (by rfl) ⟨1455291, by rfl⟩ : syracuseStep 3880777 = 2910583) B2910583
theorem B5174369 : Blo 2299435 5174369 := bstep (se 2 (by rfl) ⟨1940388, by rfl⟩ : syracuseStep 5174369 = 3880777) B3880777
theorem B3449579 : Blo 2299435 3449579 := bstep (se 1 (by rfl) ⟨2587184, by rfl⟩ : syracuseStep 3449579 = 5174369) B5174369
theorem B2299719 : Blo 2299435 2299719 := bstep (se 1 (by rfl) ⟨1724789, by rfl⟩ : syracuseStep 2299719 = 3449579) B3449579
theorem B2587189 : Blo 2299435 2587189 := bbase (se 5 (by rfl) ⟨121274, by rfl⟩ : syracuseStep 2587189 = 242549) (by norm_num)
theorem B3449585 : Blo 2299435 3449585 := bstep (se 2 (by rfl) ⟨1293594, by rfl⟩ : syracuseStep 3449585 = 2587189) B2587189
theorem B2299723 : Blo 2299435 2299723 := bstep (se 1 (by rfl) ⟨1724792, by rfl⟩ : syracuseStep 2299723 = 3449585) B3449585
theorem B2910593 : Blo 2299435 2910593 := bbase (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) (by norm_num)
theorem B7761581 : Blo 2299435 7761581 := bstep (se 3 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 7761581 = 2910593) B2910593
theorem B5174387 : Blo 2299435 5174387 := bstep (se 1 (by rfl) ⟨3880790, by rfl⟩ : syracuseStep 5174387 = 7761581) B7761581
theorem B3449591 : Blo 2299435 3449591 := bstep (se 1 (by rfl) ⟨2587193, by rfl⟩ : syracuseStep 3449591 = 5174387) B5174387
theorem B2299727 : Blo 2299435 2299727 := bstep (se 1 (by rfl) ⟨1724795, by rfl⟩ : syracuseStep 2299727 = 3449591) B3449591
theorem B3449597 : Blo 2299435 3449597 := bbase (se 3 (by rfl) ⟨646799, by rfl⟩ : syracuseStep 3449597 = 1293599) (by norm_num)
theorem B2299731 : Blo 2299435 2299731 := bstep (se 1 (by rfl) ⟨1724798, by rfl⟩ : syracuseStep 2299731 = 3449597) B3449597
theorem B5174405 : Blo 2299435 5174405 := bbase (se 4 (by rfl) ⟨485100, by rfl⟩ : syracuseStep 5174405 = 970201) (by norm_num)
theorem B3449603 : Blo 2299435 3449603 := bstep (se 1 (by rfl) ⟨2587202, by rfl⟩ : syracuseStep 3449603 = 5174405) B5174405
theorem B2299735 : Blo 2299435 2299735 := bstep (se 1 (by rfl) ⟨1724801, by rfl⟩ : syracuseStep 2299735 = 3449603) B3449603
theorem B4911653 : Blo 2299435 4911653 := bbase (se 4 (by rfl) ⟨460467, by rfl⟩ : syracuseStep 4911653 = 920935) (by norm_num)
theorem B3274435 : Blo 2299435 3274435 := bstep (se 1 (by rfl) ⟨2455826, by rfl⟩ : syracuseStep 3274435 = 4911653) B4911653
theorem B4365913 : Blo 2299435 4365913 := bstep (se 2 (by rfl) ⟨1637217, by rfl⟩ : syracuseStep 4365913 = 3274435) B3274435
theorem B5821217 : Blo 2299435 5821217 := bstep (se 2 (by rfl) ⟨2182956, by rfl⟩ : syracuseStep 5821217 = 4365913) B4365913
theorem B3880811 : Blo 2299435 3880811 := bstep (se 1 (by rfl) ⟨2910608, by rfl⟩ : syracuseStep 3880811 = 5821217) B5821217
theorem B2587207 : Blo 2299435 2587207 := bstep (se 1 (by rfl) ⟨1940405, by rfl⟩ : syracuseStep 2587207 = 3880811) B3880811
theorem B3449609 : Blo 2299435 3449609 := bstep (se 2 (by rfl) ⟨1293603, by rfl⟩ : syracuseStep 3449609 = 2587207) B2587207
theorem B2299739 : Blo 2299435 2299739 := bstep (se 1 (by rfl) ⟨1724804, by rfl⟩ : syracuseStep 2299739 = 3449609) B3449609
theorem B11642453 : Blo 2299435 11642453 := bbase (se 8 (by rfl) ⟨68217, by rfl⟩ : syracuseStep 11642453 = 136435) (by norm_num)
theorem B7761635 : Blo 2299435 7761635 := bstep (se 1 (by rfl) ⟨5821226, by rfl⟩ : syracuseStep 7761635 = 11642453) B11642453
theorem B5174423 : Blo 2299435 5174423 := bstep (se 1 (by rfl) ⟨3880817, by rfl⟩ : syracuseStep 5174423 = 7761635) B7761635
theorem B3449615 : Blo 2299435 3449615 := bstep (se 1 (by rfl) ⟨2587211, by rfl⟩ : syracuseStep 3449615 = 5174423) B5174423
theorem B2299743 : Blo 2299435 2299743 := bstep (se 1 (by rfl) ⟨1724807, by rfl⟩ : syracuseStep 2299743 = 3449615) B3449615
theorem B3449621 : Blo 2299435 3449621 := bbase (se 6 (by rfl) ⟨80850, by rfl⟩ : syracuseStep 3449621 = 161701) (by norm_num)
theorem B2299747 : Blo 2299435 2299747 := bstep (se 1 (by rfl) ⟨1724810, by rfl⟩ : syracuseStep 2299747 = 3449621) B3449621
theorem B3496693 : Blo 2299435 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B4662257 : Blo 2299435 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B12432685 : Blo 2299435 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B16576913 : Blo 2299435 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B44205101 : Blo 2299435 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B29470067 : Blo 2299435 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B19646711 : Blo 2299435 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B13097807 : Blo 2299435 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B8731871 : Blo 2299435 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B5821247 : Blo 2299435 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B3880831 : Blo 2299435 3880831 := bstep (se 1 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 3880831 = 5821247) B5821247
theorem B5174441 : Blo 2299435 5174441 := bstep (se 2 (by rfl) ⟨1940415, by rfl⟩ : syracuseStep 5174441 = 3880831) B3880831
theorem B3449627 : Blo 2299435 3449627 := bstep (se 1 (by rfl) ⟨2587220, by rfl⟩ : syracuseStep 3449627 = 5174441) B5174441
theorem B2299751 : Blo 2299435 2299751 := bstep (se 1 (by rfl) ⟨1724813, by rfl⟩ : syracuseStep 2299751 = 3449627) B3449627
theorem B2587225 : Blo 2299435 2587225 := bbase (se 2 (by rfl) ⟨970209, by rfl⟩ : syracuseStep 2587225 = 1940419) (by norm_num)
theorem B3449633 : Blo 2299435 3449633 := bstep (se 2 (by rfl) ⟨1293612, by rfl⟩ : syracuseStep 3449633 = 2587225) B2587225
theorem B2299755 : Blo 2299435 2299755 := bstep (se 1 (by rfl) ⟨1724816, by rfl⟩ : syracuseStep 2299755 = 3449633) B3449633
theorem B2331137 : Blo 2299435 2331137 := bbase (se 2 (by rfl) ⟨874176, by rfl⟩ : syracuseStep 2331137 = 1748353) (by norm_num)
theorem B6216365 : Blo 2299435 6216365 := bstep (se 3 (by rfl) ⟨1165568, by rfl⟩ : syracuseStep 6216365 = 2331137) B2331137
theorem B16576973 : Blo 2299435 16576973 := bstep (se 3 (by rfl) ⟨3108182, by rfl⟩ : syracuseStep 16576973 = 6216365) B6216365
theorem B11051315 : Blo 2299435 11051315 := bstep (se 1 (by rfl) ⟨8288486, by rfl⟩ : syracuseStep 11051315 = 16576973) B16576973
theorem B7367543 : Blo 2299435 7367543 := bstep (se 1 (by rfl) ⟨5525657, by rfl⟩ : syracuseStep 7367543 = 11051315) B11051315
theorem B4911695 : Blo 2299435 4911695 := bstep (se 1 (by rfl) ⟨3683771, by rfl⟩ : syracuseStep 4911695 = 7367543) B7367543
theorem B3274463 : Blo 2299435 3274463 := bstep (se 1 (by rfl) ⟨2455847, by rfl⟩ : syracuseStep 3274463 = 4911695) B4911695
theorem B8731901 : Blo 2299435 8731901 := bstep (se 3 (by rfl) ⟨1637231, by rfl⟩ : syracuseStep 8731901 = 3274463) B3274463
theorem B5821267 : Blo 2299435 5821267 := bstep (se 1 (by rfl) ⟨4365950, by rfl⟩ : syracuseStep 5821267 = 8731901) B8731901
theorem B7761689 : Blo 2299435 7761689 := bstep (se 2 (by rfl) ⟨2910633, by rfl⟩ : syracuseStep 7761689 = 5821267) B5821267
theorem B5174459 : Blo 2299435 5174459 := bstep (se 1 (by rfl) ⟨3880844, by rfl⟩ : syracuseStep 5174459 = 7761689) B7761689
theorem B3449639 : Blo 2299435 3449639 := bstep (se 1 (by rfl) ⟨2587229, by rfl⟩ : syracuseStep 3449639 = 5174459) B5174459
theorem B2299759 : Blo 2299435 2299759 := bstep (se 1 (by rfl) ⟨1724819, by rfl⟩ : syracuseStep 2299759 = 3449639) B3449639
theorem B3449645 : Blo 2299435 3449645 := bbase (se 3 (by rfl) ⟨646808, by rfl⟩ : syracuseStep 3449645 = 1293617) (by norm_num)
theorem B2299763 : Blo 2299435 2299763 := bstep (se 1 (by rfl) ⟨1724822, by rfl⟩ : syracuseStep 2299763 = 3449645) B3449645
theorem B5174477 : Blo 2299435 5174477 := bbase (se 3 (by rfl) ⟨970214, by rfl⟩ : syracuseStep 5174477 = 1940429) (by norm_num)
theorem B3449651 : Blo 2299435 3449651 := bstep (se 1 (by rfl) ⟨2587238, by rfl⟩ : syracuseStep 3449651 = 5174477) B5174477
theorem B2299767 : Blo 2299435 2299767 := bstep (se 1 (by rfl) ⟨1724825, by rfl⟩ : syracuseStep 2299767 = 3449651) B3449651
theorem B2910649 : Blo 2299435 2910649 := bbase (se 2 (by rfl) ⟨1091493, by rfl⟩ : syracuseStep 2910649 = 2182987) (by norm_num)
theorem B3880865 : Blo 2299435 3880865 := bstep (se 2 (by rfl) ⟨1455324, by rfl⟩ : syracuseStep 3880865 = 2910649) B2910649
theorem B2587243 : Blo 2299435 2587243 := bstep (se 1 (by rfl) ⟨1940432, by rfl⟩ : syracuseStep 2587243 = 3880865) B3880865
theorem B3449657 : Blo 2299435 3449657 := bstep (se 2 (by rfl) ⟨1293621, by rfl⟩ : syracuseStep 3449657 = 2587243) B2587243
theorem B2299771 : Blo 2299435 2299771 := bstep (se 1 (by rfl) ⟨1724828, by rfl⟩ : syracuseStep 2299771 = 3449657) B3449657
theorem B15949973 : Blo 2299435 15949973 := bbase (se 6 (by rfl) ⟨373827, by rfl⟩ : syracuseStep 15949973 = 747655) (by norm_num)
theorem B10633315 : Blo 2299435 10633315 := bstep (se 1 (by rfl) ⟨7974986, by rfl⟩ : syracuseStep 10633315 = 15949973) B15949973
theorem B14177753 : Blo 2299435 14177753 := bstep (se 2 (by rfl) ⟨5316657, by rfl⟩ : syracuseStep 14177753 = 10633315) B10633315
theorem B9451835 : Blo 2299435 9451835 := bstep (se 1 (by rfl) ⟨7088876, by rfl⟩ : syracuseStep 9451835 = 14177753) B14177753
theorem B6301223 : Blo 2299435 6301223 := bstep (se 1 (by rfl) ⟨4725917, by rfl⟩ : syracuseStep 6301223 = 9451835) B9451835
theorem B4200815 : Blo 2299435 4200815 := bstep (se 1 (by rfl) ⟨3150611, by rfl⟩ : syracuseStep 4200815 = 6301223) B6301223
theorem B2800543 : Blo 2299435 2800543 := bstep (se 1 (by rfl) ⟨2100407, by rfl⟩ : syracuseStep 2800543 = 4200815) B4200815
theorem B3734057 : Blo 2299435 3734057 := bstep (se 2 (by rfl) ⟨1400271, by rfl⟩ : syracuseStep 3734057 = 2800543) B2800543
theorem B9957485 : Blo 2299435 9957485 := bstep (se 3 (by rfl) ⟨1867028, by rfl⟩ : syracuseStep 9957485 = 3734057) B3734057
theorem B6638323 : Blo 2299435 6638323 := bstep (se 1 (by rfl) ⟨4978742, by rfl⟩ : syracuseStep 6638323 = 9957485) B9957485
theorem B8851097 : Blo 2299435 8851097 := bstep (se 2 (by rfl) ⟨3319161, by rfl⟩ : syracuseStep 8851097 = 6638323) B6638323
theorem B5900731 : Blo 2299435 5900731 := bstep (se 1 (by rfl) ⟨4425548, by rfl⟩ : syracuseStep 5900731 = 8851097) B8851097
theorem B31470565 : Blo 2299435 31470565 := bstep (se 4 (by rfl) ⟨2950365, by rfl⟩ : syracuseStep 31470565 = 5900731) B5900731
theorem B41960753 : Blo 2299435 41960753 := bstep (se 2 (by rfl) ⟨15735282, by rfl⟩ : syracuseStep 41960753 = 31470565) B31470565
theorem B27973835 : Blo 2299435 27973835 := bstep (se 1 (by rfl) ⟨20980376, by rfl⟩ : syracuseStep 27973835 = 41960753) B41960753
theorem B18649223 : Blo 2299435 18649223 := bstep (se 1 (by rfl) ⟨13986917, by rfl⟩ : syracuseStep 18649223 = 27973835) B27973835
theorem B12432815 : Blo 2299435 12432815 := bstep (se 1 (by rfl) ⟨9324611, by rfl⟩ : syracuseStep 12432815 = 18649223) B18649223
theorem B8288543 : Blo 2299435 8288543 := bstep (se 1 (by rfl) ⟨6216407, by rfl⟩ : syracuseStep 8288543 = 12432815) B12432815
theorem B5525695 : Blo 2299435 5525695 := bstep (se 1 (by rfl) ⟨4144271, by rfl⟩ : syracuseStep 5525695 = 8288543) B8288543
theorem B7367593 : Blo 2299435 7367593 := bstep (se 2 (by rfl) ⟨2762847, by rfl⟩ : syracuseStep 7367593 = 5525695) B5525695
theorem B9823457 : Blo 2299435 9823457 := bstep (se 2 (by rfl) ⟨3683796, by rfl⟩ : syracuseStep 9823457 = 7367593) B7367593
theorem B26195885 : Blo 2299435 26195885 := bstep (se 3 (by rfl) ⟨4911728, by rfl⟩ : syracuseStep 26195885 = 9823457) B9823457
theorem B17463923 : Blo 2299435 17463923 := bstep (se 1 (by rfl) ⟨13097942, by rfl⟩ : syracuseStep 17463923 = 26195885) B26195885
theorem B11642615 : Blo 2299435 11642615 := bstep (se 1 (by rfl) ⟨8731961, by rfl⟩ : syracuseStep 11642615 = 17463923) B17463923
theorem B7761743 : Blo 2299435 7761743 := bstep (se 1 (by rfl) ⟨5821307, by rfl⟩ : syracuseStep 7761743 = 11642615) B11642615
theorem B5174495 : Blo 2299435 5174495 := bstep (se 1 (by rfl) ⟨3880871, by rfl⟩ : syracuseStep 5174495 = 7761743) B7761743
theorem B3449663 : Blo 2299435 3449663 := bstep (se 1 (by rfl) ⟨2587247, by rfl⟩ : syracuseStep 3449663 = 5174495) B5174495
theorem B2299775 : Blo 2299435 2299775 := bstep (se 1 (by rfl) ⟨1724831, by rfl⟩ : syracuseStep 2299775 = 3449663) B3449663
theorem B3449669 : Blo 2299435 3449669 := bbase (se 4 (by rfl) ⟨323406, by rfl⟩ : syracuseStep 3449669 = 646813) (by norm_num)
theorem B2299779 : Blo 2299435 2299779 := bstep (se 1 (by rfl) ⟨1724834, by rfl⟩ : syracuseStep 2299779 = 3449669) B3449669
theorem B3880885 : Blo 2299435 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B5174513 : Blo 2299435 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B3449675 : Blo 2299435 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B2299783 : Blo 2299435 2299783 := bstep (se 1 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 2299783 = 3449675) B3449675
theorem B2587261 : Blo 2299435 2587261 := bbase (se 3 (by rfl) ⟨485111, by rfl⟩ : syracuseStep 2587261 = 970223) (by norm_num)
theorem B3449681 : Blo 2299435 3449681 := bstep (se 2 (by rfl) ⟨1293630, by rfl⟩ : syracuseStep 3449681 = 2587261) B2587261
theorem B2299787 : Blo 2299435 2299787 := bstep (se 1 (by rfl) ⟨1724840, by rfl⟩ : syracuseStep 2299787 = 3449681) B3449681
theorem B7761797 : Blo 2299435 7761797 := bbase (se 4 (by rfl) ⟨727668, by rfl⟩ : syracuseStep 7761797 = 1455337) (by norm_num)
theorem B5174531 : Blo 2299435 5174531 := bstep (se 1 (by rfl) ⟨3880898, by rfl⟩ : syracuseStep 5174531 = 7761797) B7761797
theorem B3449687 : Blo 2299435 3449687 := bstep (se 1 (by rfl) ⟨2587265, by rfl⟩ : syracuseStep 3449687 = 5174531) B5174531
theorem B2299791 : Blo 2299435 2299791 := bstep (se 1 (by rfl) ⟨1724843, by rfl⟩ : syracuseStep 2299791 = 3449687) B3449687
theorem B3449693 : Blo 2299435 3449693 := bbase (se 3 (by rfl) ⟨646817, by rfl⟩ : syracuseStep 3449693 = 1293635) (by norm_num)
theorem B2299795 : Blo 2299435 2299795 := bstep (se 1 (by rfl) ⟨1724846, by rfl⟩ : syracuseStep 2299795 = 3449693) B3449693
theorem B5174549 : Blo 2299435 5174549 := bbase (se 6 (by rfl) ⟨121278, by rfl⟩ : syracuseStep 5174549 = 242557) (by norm_num)
theorem B3449699 : Blo 2299435 3449699 := bstep (se 1 (by rfl) ⟨2587274, by rfl⟩ : syracuseStep 3449699 = 5174549) B5174549
theorem B2299799 : Blo 2299435 2299799 := bstep (se 1 (by rfl) ⟨1724849, by rfl⟩ : syracuseStep 2299799 = 3449699) B3449699
theorem B8732069 : Blo 2299435 8732069 := bbase (se 4 (by rfl) ⟨818631, by rfl⟩ : syracuseStep 8732069 = 1637263) (by norm_num)
theorem B5821379 : Blo 2299435 5821379 := bstep (se 1 (by rfl) ⟨4366034, by rfl⟩ : syracuseStep 5821379 = 8732069) B8732069
theorem B3880919 : Blo 2299435 3880919 := bstep (se 1 (by rfl) ⟨2910689, by rfl⟩ : syracuseStep 3880919 = 5821379) B5821379
theorem B2587279 : Blo 2299435 2587279 := bstep (se 1 (by rfl) ⟨1940459, by rfl⟩ : syracuseStep 2587279 = 3880919) B3880919
theorem B3449705 : Blo 2299435 3449705 := bstep (se 2 (by rfl) ⟨1293639, by rfl⟩ : syracuseStep 3449705 = 2587279) B2587279
theorem B2299803 : Blo 2299435 2299803 := bstep (se 1 (by rfl) ⟨1724852, by rfl⟩ : syracuseStep 2299803 = 3449705) B3449705
theorem B4911797 : Blo 2299435 4911797 := bbase (se 5 (by rfl) ⟨230240, by rfl⟩ : syracuseStep 4911797 = 460481) (by norm_num)
theorem B13098125 : Blo 2299435 13098125 := bstep (se 3 (by rfl) ⟨2455898, by rfl⟩ : syracuseStep 13098125 = 4911797) B4911797
theorem B8732083 : Blo 2299435 8732083 := bstep (se 1 (by rfl) ⟨6549062, by rfl⟩ : syracuseStep 8732083 = 13098125) B13098125
theorem B11642777 : Blo 2299435 11642777 := bstep (se 2 (by rfl) ⟨4366041, by rfl⟩ : syracuseStep 11642777 = 8732083) B8732083
theorem B7761851 : Blo 2299435 7761851 := bstep (se 1 (by rfl) ⟨5821388, by rfl⟩ : syracuseStep 7761851 = 11642777) B11642777
theorem B5174567 : Blo 2299435 5174567 := bstep (se 1 (by rfl) ⟨3880925, by rfl⟩ : syracuseStep 5174567 = 7761851) B7761851
theorem B3449711 : Blo 2299435 3449711 := bstep (se 1 (by rfl) ⟨2587283, by rfl⟩ : syracuseStep 3449711 = 5174567) B5174567
theorem B2299807 : Blo 2299435 2299807 := bstep (se 1 (by rfl) ⟨1724855, by rfl⟩ : syracuseStep 2299807 = 3449711) B3449711
theorem B3449717 : Blo 2299435 3449717 := bbase (se 5 (by rfl) ⟨161705, by rfl⟩ : syracuseStep 3449717 = 323411) (by norm_num)
theorem B2299811 : Blo 2299435 2299811 := bstep (se 1 (by rfl) ⟨1724858, by rfl⟩ : syracuseStep 2299811 = 3449717) B3449717
theorem B6216517 : Blo 2299435 6216517 := bbase (se 4 (by rfl) ⟨582798, by rfl⟩ : syracuseStep 6216517 = 1165597) (by norm_num)
theorem B8288689 : Blo 2299435 8288689 := bstep (se 2 (by rfl) ⟨3108258, by rfl⟩ : syracuseStep 8288689 = 6216517) B6216517
theorem B11051585 : Blo 2299435 11051585 := bstep (se 2 (by rfl) ⟨4144344, by rfl⟩ : syracuseStep 11051585 = 8288689) B8288689
theorem B7367723 : Blo 2299435 7367723 := bstep (se 1 (by rfl) ⟨5525792, by rfl⟩ : syracuseStep 7367723 = 11051585) B11051585
theorem B4911815 : Blo 2299435 4911815 := bstep (se 1 (by rfl) ⟨3683861, by rfl⟩ : syracuseStep 4911815 = 7367723) B7367723
theorem B3274543 : Blo 2299435 3274543 := bstep (se 1 (by rfl) ⟨2455907, by rfl⟩ : syracuseStep 3274543 = 4911815) B4911815
theorem B4366057 : Blo 2299435 4366057 := bstep (se 2 (by rfl) ⟨1637271, by rfl⟩ : syracuseStep 4366057 = 3274543) B3274543
theorem B5821409 : Blo 2299435 5821409 := bstep (se 2 (by rfl) ⟨2183028, by rfl⟩ : syracuseStep 5821409 = 4366057) B4366057
theorem B3880939 : Blo 2299435 3880939 := bstep (se 1 (by rfl) ⟨2910704, by rfl⟩ : syracuseStep 3880939 = 5821409) B5821409
theorem B5174585 : Blo 2299435 5174585 := bstep (se 2 (by rfl) ⟨1940469, by rfl⟩ : syracuseStep 5174585 = 3880939) B3880939
theorem B3449723 : Blo 2299435 3449723 := bstep (se 1 (by rfl) ⟨2587292, by rfl⟩ : syracuseStep 3449723 = 5174585) B5174585
theorem B2299815 : Blo 2299435 2299815 := bstep (se 1 (by rfl) ⟨1724861, by rfl⟩ : syracuseStep 2299815 = 3449723) B3449723
theorem B2587297 : Blo 2299435 2587297 := bbase (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) (by norm_num)
theorem B3449729 : Blo 2299435 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B2299819 : Blo 2299435 2299819 := bstep (se 1 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 2299819 = 3449729) B3449729
theorem B5821429 : Blo 2299435 5821429 := bbase (se 5 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 5821429 = 545759) (by norm_num)
theorem B7761905 : Blo 2299435 7761905 := bstep (se 2 (by rfl) ⟨2910714, by rfl⟩ : syracuseStep 7761905 = 5821429) B5821429
theorem B5174603 : Blo 2299435 5174603 := bstep (se 1 (by rfl) ⟨3880952, by rfl⟩ : syracuseStep 5174603 = 7761905) B7761905
theorem B3449735 : Blo 2299435 3449735 := bstep (se 1 (by rfl) ⟨2587301, by rfl⟩ : syracuseStep 3449735 = 5174603) B5174603
theorem B2299823 : Blo 2299435 2299823 := bstep (se 1 (by rfl) ⟨1724867, by rfl⟩ : syracuseStep 2299823 = 3449735) B3449735
theorem B3449741 : Blo 2299435 3449741 := bbase (se 3 (by rfl) ⟨646826, by rfl⟩ : syracuseStep 3449741 = 1293653) (by norm_num)
theorem B2299827 : Blo 2299435 2299827 := bstep (se 1 (by rfl) ⟨1724870, by rfl⟩ : syracuseStep 2299827 = 3449741) B3449741
theorem B5174621 : Blo 2299435 5174621 := bbase (se 3 (by rfl) ⟨970241, by rfl⟩ : syracuseStep 5174621 = 1940483) (by norm_num)
theorem B3449747 : Blo 2299435 3449747 := bstep (se 1 (by rfl) ⟨2587310, by rfl⟩ : syracuseStep 3449747 = 5174621) B5174621
theorem B2299831 : Blo 2299435 2299831 := bstep (se 1 (by rfl) ⟨1724873, by rfl⟩ : syracuseStep 2299831 = 3449747) B3449747
theorem B3880973 : Blo 2299435 3880973 := bbase (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) (by norm_num)
theorem B2587315 : Blo 2299435 2587315 := bstep (se 1 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 2587315 = 3880973) B3880973
theorem B3449753 : Blo 2299435 3449753 := bstep (se 2 (by rfl) ⟨1293657, by rfl⟩ : syracuseStep 3449753 = 2587315) B2587315
theorem B2299835 : Blo 2299435 2299835 := bstep (se 1 (by rfl) ⟨1724876, by rfl⟩ : syracuseStep 2299835 = 3449753) B3449753
theorem B6216581 : Blo 2299435 6216581 := bbase (se 4 (by rfl) ⟨582804, by rfl⟩ : syracuseStep 6216581 = 1165609) (by norm_num)
theorem B4144387 : Blo 2299435 4144387 := bstep (se 1 (by rfl) ⟨3108290, by rfl⟩ : syracuseStep 4144387 = 6216581) B6216581
theorem B5525849 : Blo 2299435 5525849 := bstep (se 2 (by rfl) ⟨2072193, by rfl⟩ : syracuseStep 5525849 = 4144387) B4144387
theorem B3683899 : Blo 2299435 3683899 := bstep (se 1 (by rfl) ⟨2762924, by rfl⟩ : syracuseStep 3683899 = 5525849) B5525849
theorem B19647461 : Blo 2299435 19647461 := bstep (se 4 (by rfl) ⟨1841949, by rfl⟩ : syracuseStep 19647461 = 3683899) B3683899
theorem B13098307 : Blo 2299435 13098307 := bstep (se 1 (by rfl) ⟨9823730, by rfl⟩ : syracuseStep 13098307 = 19647461) B19647461
theorem B17464409 : Blo 2299435 17464409 := bstep (se 2 (by rfl) ⟨6549153, by rfl⟩ : syracuseStep 17464409 = 13098307) B13098307
theorem B11642939 : Blo 2299435 11642939 := bstep (se 1 (by rfl) ⟨8732204, by rfl⟩ : syracuseStep 11642939 = 17464409) B17464409
theorem B7761959 : Blo 2299435 7761959 := bstep (se 1 (by rfl) ⟨5821469, by rfl⟩ : syracuseStep 7761959 = 11642939) B11642939
theorem B5174639 : Blo 2299435 5174639 := bstep (se 1 (by rfl) ⟨3880979, by rfl⟩ : syracuseStep 5174639 = 7761959) B7761959
theorem B3449759 : Blo 2299435 3449759 := bstep (se 1 (by rfl) ⟨2587319, by rfl⟩ : syracuseStep 3449759 = 5174639) B5174639
theorem B2299839 : Blo 2299435 2299839 := bstep (se 1 (by rfl) ⟨1724879, by rfl⟩ : syracuseStep 2299839 = 3449759) B3449759
theorem B3449765 : Blo 2299435 3449765 := bbase (se 4 (by rfl) ⟨323415, by rfl⟩ : syracuseStep 3449765 = 646831) (by norm_num)
theorem B2299843 : Blo 2299435 2299843 := bstep (se 1 (by rfl) ⟨1724882, by rfl⟩ : syracuseStep 2299843 = 3449765) B3449765
theorem B2910745 : Blo 2299435 2910745 := bbase (se 2 (by rfl) ⟨1091529, by rfl⟩ : syracuseStep 2910745 = 2183059) (by norm_num)
theorem B3880993 : Blo 2299435 3880993 := bstep (se 2 (by rfl) ⟨1455372, by rfl⟩ : syracuseStep 3880993 = 2910745) B2910745
theorem B5174657 : Blo 2299435 5174657 := bstep (se 2 (by rfl) ⟨1940496, by rfl⟩ : syracuseStep 5174657 = 3880993) B3880993
theorem B3449771 : Blo 2299435 3449771 := bstep (se 1 (by rfl) ⟨2587328, by rfl⟩ : syracuseStep 3449771 = 5174657) B5174657
theorem B2299847 : Blo 2299435 2299847 := bstep (se 1 (by rfl) ⟨1724885, by rfl⟩ : syracuseStep 2299847 = 3449771) B3449771
theorem B2587333 : Blo 2299435 2587333 := bbase (se 4 (by rfl) ⟨242562, by rfl⟩ : syracuseStep 2587333 = 485125) (by norm_num)
theorem B3449777 : Blo 2299435 3449777 := bstep (se 2 (by rfl) ⟨1293666, by rfl⟩ : syracuseStep 3449777 = 2587333) B2587333
theorem B2299851 : Blo 2299435 2299851 := bstep (se 1 (by rfl) ⟨1724888, by rfl⟩ : syracuseStep 2299851 = 3449777) B3449777
theorem B4366133 : Blo 2299435 4366133 := bbase (se 5 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 4366133 = 409325) (by norm_num)
theorem B2910755 : Blo 2299435 2910755 := bstep (se 1 (by rfl) ⟨2183066, by rfl⟩ : syracuseStep 2910755 = 4366133) B4366133
theorem B7762013 : Blo 2299435 7762013 := bstep (se 3 (by rfl) ⟨1455377, by rfl⟩ : syracuseStep 7762013 = 2910755) B2910755
theorem B5174675 : Blo 2299435 5174675 := bstep (se 1 (by rfl) ⟨3881006, by rfl⟩ : syracuseStep 5174675 = 7762013) B7762013
theorem B3449783 : Blo 2299435 3449783 := bstep (se 1 (by rfl) ⟨2587337, by rfl⟩ : syracuseStep 3449783 = 5174675) B5174675
theorem B2299855 : Blo 2299435 2299855 := bstep (se 1 (by rfl) ⟨1724891, by rfl⟩ : syracuseStep 2299855 = 3449783) B3449783
theorem B3449789 : Blo 2299435 3449789 := bbase (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) (by norm_num)
theorem B2299859 : Blo 2299435 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B5174693 : Blo 2299435 5174693 := bbase (se 4 (by rfl) ⟨485127, by rfl⟩ : syracuseStep 5174693 = 970255) (by norm_num)
theorem B3449795 : Blo 2299435 3449795 := bstep (se 1 (by rfl) ⟨2587346, by rfl⟩ : syracuseStep 3449795 = 5174693) B5174693
theorem B2299863 : Blo 2299435 2299863 := bstep (se 1 (by rfl) ⟨1724897, by rfl⟩ : syracuseStep 2299863 = 3449795) B3449795
theorem B5821541 : Blo 2299435 5821541 := bbase (se 4 (by rfl) ⟨545769, by rfl⟩ : syracuseStep 5821541 = 1091539) (by norm_num)
theorem B3881027 : Blo 2299435 3881027 := bstep (se 1 (by rfl) ⟨2910770, by rfl⟩ : syracuseStep 3881027 = 5821541) B5821541
theorem B2587351 : Blo 2299435 2587351 := bstep (se 1 (by rfl) ⟨1940513, by rfl⟩ : syracuseStep 2587351 = 3881027) B3881027
theorem B3449801 : Blo 2299435 3449801 := bstep (se 2 (by rfl) ⟨1293675, by rfl⟩ : syracuseStep 3449801 = 2587351) B2587351
theorem B2299867 : Blo 2299435 2299867 := bstep (se 1 (by rfl) ⟨1724900, by rfl⟩ : syracuseStep 2299867 = 3449801) B3449801
theorem B10490629 : Blo 2299435 10490629 := bbase (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) (by norm_num)
theorem B13987505 : Blo 2299435 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B9325003 : Blo 2299435 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B12433337 : Blo 2299435 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B8288891 : Blo 2299435 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B5525927 : Blo 2299435 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B3683951 : Blo 2299435 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B2455967 : Blo 2299435 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B6549245 : Blo 2299435 6549245 := bstep (se 3 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 6549245 = 2455967) B2455967
theorem B4366163 : Blo 2299435 4366163 := bstep (se 1 (by rfl) ⟨3274622, by rfl⟩ : syracuseStep 4366163 = 6549245) B6549245
theorem B11643101 : Blo 2299435 11643101 := bstep (se 3 (by rfl) ⟨2183081, by rfl⟩ : syracuseStep 11643101 = 4366163) B4366163
theorem B7762067 : Blo 2299435 7762067 := bstep (se 1 (by rfl) ⟨5821550, by rfl⟩ : syracuseStep 7762067 = 11643101) B11643101
theorem B5174711 : Blo 2299435 5174711 := bstep (se 1 (by rfl) ⟨3881033, by rfl⟩ : syracuseStep 5174711 = 7762067) B7762067
theorem B3449807 : Blo 2299435 3449807 := bstep (se 1 (by rfl) ⟨2587355, by rfl⟩ : syracuseStep 3449807 = 5174711) B5174711
theorem B2299871 : Blo 2299435 2299871 := bstep (se 1 (by rfl) ⟨1724903, by rfl⟩ : syracuseStep 2299871 = 3449807) B3449807
theorem B3449813 : Blo 2299435 3449813 := bbase (se 7 (by rfl) ⟨40427, by rfl⟩ : syracuseStep 3449813 = 80855) (by norm_num)
theorem B2299875 : Blo 2299435 2299875 := bstep (se 1 (by rfl) ⟨1724906, by rfl⟩ : syracuseStep 2299875 = 3449813) B3449813
theorem B8732357 : Blo 2299435 8732357 := bbase (se 4 (by rfl) ⟨818658, by rfl⟩ : syracuseStep 8732357 = 1637317) (by norm_num)
theorem B5821571 : Blo 2299435 5821571 := bstep (se 1 (by rfl) ⟨4366178, by rfl⟩ : syracuseStep 5821571 = 8732357) B8732357
theorem B3881047 : Blo 2299435 3881047 := bstep (se 1 (by rfl) ⟨2910785, by rfl⟩ : syracuseStep 3881047 = 5821571) B5821571
theorem B5174729 : Blo 2299435 5174729 := bstep (se 2 (by rfl) ⟨1940523, by rfl⟩ : syracuseStep 5174729 = 3881047) B3881047
theorem B3449819 : Blo 2299435 3449819 := bstep (se 1 (by rfl) ⟨2587364, by rfl⟩ : syracuseStep 3449819 = 5174729) B5174729
theorem B2299879 : Blo 2299435 2299879 := bstep (se 1 (by rfl) ⟨1724909, by rfl⟩ : syracuseStep 2299879 = 3449819) B3449819
theorem B2587369 : Blo 2299435 2587369 := bbase (se 2 (by rfl) ⟨970263, by rfl⟩ : syracuseStep 2587369 = 1940527) (by norm_num)
theorem B3449825 : Blo 2299435 3449825 := bstep (se 2 (by rfl) ⟨1293684, by rfl⟩ : syracuseStep 3449825 = 2587369) B2587369
theorem B2299883 : Blo 2299435 2299883 := bstep (se 1 (by rfl) ⟨1724912, by rfl⟩ : syracuseStep 2299883 = 3449825) B3449825
theorem B13098581 : Blo 2299435 13098581 := bbase (se 8 (by rfl) ⟨76749, by rfl⟩ : syracuseStep 13098581 = 153499) (by norm_num)
theorem B8732387 : Blo 2299435 8732387 := bstep (se 1 (by rfl) ⟨6549290, by rfl⟩ : syracuseStep 8732387 = 13098581) B13098581
theorem B5821591 : Blo 2299435 5821591 := bstep (se 1 (by rfl) ⟨4366193, by rfl⟩ : syracuseStep 5821591 = 8732387) B8732387
theorem B7762121 : Blo 2299435 7762121 := bstep (se 2 (by rfl) ⟨2910795, by rfl⟩ : syracuseStep 7762121 = 5821591) B5821591
theorem B5174747 : Blo 2299435 5174747 := bstep (se 1 (by rfl) ⟨3881060, by rfl⟩ : syracuseStep 5174747 = 7762121) B7762121
theorem B3449831 : Blo 2299435 3449831 := bstep (se 1 (by rfl) ⟨2587373, by rfl⟩ : syracuseStep 3449831 = 5174747) B5174747
theorem B2299887 : Blo 2299435 2299887 := bstep (se 1 (by rfl) ⟨1724915, by rfl⟩ : syracuseStep 2299887 = 3449831) B3449831
theorem B3449837 : Blo 2299435 3449837 := bbase (se 3 (by rfl) ⟨646844, by rfl⟩ : syracuseStep 3449837 = 1293689) (by norm_num)
theorem B2299891 : Blo 2299435 2299891 := bstep (se 1 (by rfl) ⟨1724918, by rfl⟩ : syracuseStep 2299891 = 3449837) B3449837
theorem B5174765 : Blo 2299435 5174765 := bbase (se 3 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 5174765 = 1940537) (by norm_num)
theorem B3449843 : Blo 2299435 3449843 := bstep (se 1 (by rfl) ⟨2587382, by rfl⟩ : syracuseStep 3449843 = 5174765) B5174765
theorem B2299895 : Blo 2299435 2299895 := bstep (se 1 (by rfl) ⟨1724921, by rfl⟩ : syracuseStep 2299895 = 3449843) B3449843
theorem B17703157 : Blo 2299435 17703157 := bbase (se 5 (by rfl) ⟨829835, by rfl⟩ : syracuseStep 17703157 = 1659671) (by norm_num)
theorem B23604209 : Blo 2299435 23604209 := bstep (se 2 (by rfl) ⟨8851578, by rfl⟩ : syracuseStep 23604209 = 17703157) B17703157
theorem B15736139 : Blo 2299435 15736139 := bstep (se 1 (by rfl) ⟨11802104, by rfl⟩ : syracuseStep 15736139 = 23604209) B23604209
theorem B10490759 : Blo 2299435 10490759 := bstep (se 1 (by rfl) ⟨7868069, by rfl⟩ : syracuseStep 10490759 = 15736139) B15736139
theorem B6993839 : Blo 2299435 6993839 := bstep (se 1 (by rfl) ⟨5245379, by rfl⟩ : syracuseStep 6993839 = 10490759) B10490759
theorem B4662559 : Blo 2299435 4662559 := bstep (se 1 (by rfl) ⟨3496919, by rfl⟩ : syracuseStep 4662559 = 6993839) B6993839
theorem B6216745 : Blo 2299435 6216745 := bstep (se 2 (by rfl) ⟨2331279, by rfl⟩ : syracuseStep 6216745 = 4662559) B4662559
theorem B8288993 : Blo 2299435 8288993 := bstep (se 2 (by rfl) ⟨3108372, by rfl⟩ : syracuseStep 8288993 = 6216745) B6216745
theorem B5525995 : Blo 2299435 5525995 := bstep (se 1 (by rfl) ⟨4144496, by rfl⟩ : syracuseStep 5525995 = 8288993) B8288993
theorem B7367993 : Blo 2299435 7367993 := bstep (se 2 (by rfl) ⟨2762997, by rfl⟩ : syracuseStep 7367993 = 5525995) B5525995
theorem B4911995 : Blo 2299435 4911995 := bstep (se 1 (by rfl) ⟨3683996, by rfl⟩ : syracuseStep 4911995 = 7367993) B7367993
theorem B3274663 : Blo 2299435 3274663 := bstep (se 1 (by rfl) ⟨2455997, by rfl⟩ : syracuseStep 3274663 = 4911995) B4911995
theorem B4366217 : Blo 2299435 4366217 := bstep (se 2 (by rfl) ⟨1637331, by rfl⟩ : syracuseStep 4366217 = 3274663) B3274663
theorem B2910811 : Blo 2299435 2910811 := bstep (se 1 (by rfl) ⟨2183108, by rfl⟩ : syracuseStep 2910811 = 4366217) B4366217
theorem B3881081 : Blo 2299435 3881081 := bstep (se 2 (by rfl) ⟨1455405, by rfl⟩ : syracuseStep 3881081 = 2910811) B2910811
theorem B2587387 : Blo 2299435 2587387 := bstep (se 1 (by rfl) ⟨1940540, by rfl⟩ : syracuseStep 2587387 = 3881081) B3881081
theorem B3449849 : Blo 2299435 3449849 := bstep (se 2 (by rfl) ⟨1293693, by rfl⟩ : syracuseStep 3449849 = 2587387) B2587387
theorem B2299899 : Blo 2299435 2299899 := bstep (se 1 (by rfl) ⟨1724924, by rfl⟩ : syracuseStep 2299899 = 3449849) B3449849
theorem B8851589 : Blo 2299435 8851589 := bbase (se 4 (by rfl) ⟨829836, by rfl⟩ : syracuseStep 8851589 = 1659673) (by norm_num)
theorem B5901059 : Blo 2299435 5901059 := bstep (se 1 (by rfl) ⟨4425794, by rfl⟩ : syracuseStep 5901059 = 8851589) B8851589
theorem B15736157 : Blo 2299435 15736157 := bstep (se 3 (by rfl) ⟨2950529, by rfl⟩ : syracuseStep 15736157 = 5901059) B5901059
theorem B10490771 : Blo 2299435 10490771 := bstep (se 1 (by rfl) ⟨7868078, by rfl⟩ : syracuseStep 10490771 = 15736157) B15736157
theorem B6993847 : Blo 2299435 6993847 := bstep (se 1 (by rfl) ⟨5245385, by rfl⟩ : syracuseStep 6993847 = 10490771) B10490771
theorem B9325129 : Blo 2299435 9325129 := bstep (se 2 (by rfl) ⟨3496923, by rfl⟩ : syracuseStep 9325129 = 6993847) B6993847
theorem B12433505 : Blo 2299435 12433505 := bstep (se 2 (by rfl) ⟨4662564, by rfl⟩ : syracuseStep 12433505 = 9325129) B9325129
theorem B132624053 : Blo 2299435 132624053 := bstep (se 5 (by rfl) ⟨6216752, by rfl⟩ : syracuseStep 132624053 = 12433505) B12433505
theorem B88416035 : Blo 2299435 88416035 := bstep (se 1 (by rfl) ⟨66312026, by rfl⟩ : syracuseStep 88416035 = 132624053) B132624053
theorem B58944023 : Blo 2299435 58944023 := bstep (se 1 (by rfl) ⟨44208017, by rfl⟩ : syracuseStep 58944023 = 88416035) B88416035
theorem B39296015 : Blo 2299435 39296015 := bstep (se 1 (by rfl) ⟨29472011, by rfl⟩ : syracuseStep 39296015 = 58944023) B58944023
theorem B26197343 : Blo 2299435 26197343 := bstep (se 1 (by rfl) ⟨19648007, by rfl⟩ : syracuseStep 26197343 = 39296015) B39296015
theorem B17464895 : Blo 2299435 17464895 := bstep (se 1 (by rfl) ⟨13098671, by rfl⟩ : syracuseStep 17464895 = 26197343) B26197343
theorem B11643263 : Blo 2299435 11643263 := bstep (se 1 (by rfl) ⟨8732447, by rfl⟩ : syracuseStep 11643263 = 17464895) B17464895
theorem B7762175 : Blo 2299435 7762175 := bstep (se 1 (by rfl) ⟨5821631, by rfl⟩ : syracuseStep 7762175 = 11643263) B11643263
theorem B5174783 : Blo 2299435 5174783 := bstep (se 1 (by rfl) ⟨3881087, by rfl⟩ : syracuseStep 5174783 = 7762175) B7762175
theorem B3449855 : Blo 2299435 3449855 := bstep (se 1 (by rfl) ⟨2587391, by rfl⟩ : syracuseStep 3449855 = 5174783) B5174783
theorem B2299903 : Blo 2299435 2299903 := bstep (se 1 (by rfl) ⟨1724927, by rfl⟩ : syracuseStep 2299903 = 3449855) B3449855
theorem B3449861 : Blo 2299435 3449861 := bbase (se 4 (by rfl) ⟨323424, by rfl⟩ : syracuseStep 3449861 = 646849) (by norm_num)
theorem B2299907 : Blo 2299435 2299907 := bstep (se 1 (by rfl) ⟨1724930, by rfl⟩ : syracuseStep 2299907 = 3449861) B3449861
theorem B3881101 : Blo 2299435 3881101 := bbase (se 3 (by rfl) ⟨727706, by rfl⟩ : syracuseStep 3881101 = 1455413) (by norm_num)
theorem B5174801 : Blo 2299435 5174801 := bstep (se 2 (by rfl) ⟨1940550, by rfl⟩ : syracuseStep 5174801 = 3881101) B3881101
theorem B3449867 : Blo 2299435 3449867 := bstep (se 1 (by rfl) ⟨2587400, by rfl⟩ : syracuseStep 3449867 = 5174801) B5174801
theorem B2299911 : Blo 2299435 2299911 := bstep (se 1 (by rfl) ⟨1724933, by rfl⟩ : syracuseStep 2299911 = 3449867) B3449867
theorem B2587405 : Blo 2299435 2587405 := bbase (se 3 (by rfl) ⟨485138, by rfl⟩ : syracuseStep 2587405 = 970277) (by norm_num)
theorem B3449873 : Blo 2299435 3449873 := bstep (se 2 (by rfl) ⟨1293702, by rfl⟩ : syracuseStep 3449873 = 2587405) B2587405
theorem B2299915 : Blo 2299435 2299915 := bstep (se 1 (by rfl) ⟨1724936, by rfl⟩ : syracuseStep 2299915 = 3449873) B3449873
theorem B7762229 : Blo 2299435 7762229 := bbase (se 5 (by rfl) ⟨363854, by rfl⟩ : syracuseStep 7762229 = 727709) (by norm_num)
theorem B5174819 : Blo 2299435 5174819 := bstep (se 1 (by rfl) ⟨3881114, by rfl⟩ : syracuseStep 5174819 = 7762229) B7762229
theorem B3449879 : Blo 2299435 3449879 := bstep (se 1 (by rfl) ⟨2587409, by rfl⟩ : syracuseStep 3449879 = 5174819) B5174819
theorem B2299919 : Blo 2299435 2299919 := bstep (se 1 (by rfl) ⟨1724939, by rfl⟩ : syracuseStep 2299919 = 3449879) B3449879
theorem B3449885 : Blo 2299435 3449885 := bbase (se 3 (by rfl) ⟨646853, by rfl⟩ : syracuseStep 3449885 = 1293707) (by norm_num)
theorem B2299923 : Blo 2299435 2299923 := bstep (se 1 (by rfl) ⟨1724942, by rfl⟩ : syracuseStep 2299923 = 3449885) B3449885
theorem B5174837 : Blo 2299435 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B3449891 : Blo 2299435 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B2299927 : Blo 2299435 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B23604533 : Blo 2299435 23604533 := bbase (se 5 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 23604533 = 2212925) (by norm_num)
theorem B15736355 : Blo 2299435 15736355 := bstep (se 1 (by rfl) ⟨11802266, by rfl⟩ : syracuseStep 15736355 = 23604533) B23604533
theorem B10490903 : Blo 2299435 10490903 := bstep (se 1 (by rfl) ⟨7868177, by rfl⟩ : syracuseStep 10490903 = 15736355) B15736355
theorem B6993935 : Blo 2299435 6993935 := bstep (se 1 (by rfl) ⟨5245451, by rfl⟩ : syracuseStep 6993935 = 10490903) B10490903
theorem B4662623 : Blo 2299435 4662623 := bstep (se 1 (by rfl) ⟨3496967, by rfl⟩ : syracuseStep 4662623 = 6993935) B6993935
theorem B12433661 : Blo 2299435 12433661 := bstep (se 3 (by rfl) ⟨2331311, by rfl⟩ : syracuseStep 12433661 = 4662623) B4662623
theorem B8289107 : Blo 2299435 8289107 := bstep (se 1 (by rfl) ⟨6216830, by rfl⟩ : syracuseStep 8289107 = 12433661) B12433661
theorem B5526071 : Blo 2299435 5526071 := bstep (se 1 (by rfl) ⟨4144553, by rfl⟩ : syracuseStep 5526071 = 8289107) B8289107
theorem B3684047 : Blo 2299435 3684047 := bstep (se 1 (by rfl) ⟨2763035, by rfl⟩ : syracuseStep 3684047 = 5526071) B5526071
theorem B9824125 : Blo 2299435 9824125 := bstep (se 3 (by rfl) ⟨1842023, by rfl⟩ : syracuseStep 9824125 = 3684047) B3684047
theorem B13098833 : Blo 2299435 13098833 := bstep (se 2 (by rfl) ⟨4912062, by rfl⟩ : syracuseStep 13098833 = 9824125) B9824125
theorem B8732555 : Blo 2299435 8732555 := bstep (se 1 (by rfl) ⟨6549416, by rfl⟩ : syracuseStep 8732555 = 13098833) B13098833
theorem B5821703 : Blo 2299435 5821703 := bstep (se 1 (by rfl) ⟨4366277, by rfl⟩ : syracuseStep 5821703 = 8732555) B8732555
theorem B3881135 : Blo 2299435 3881135 := bstep (se 1 (by rfl) ⟨2910851, by rfl⟩ : syracuseStep 3881135 = 5821703) B5821703
theorem B2587423 : Blo 2299435 2587423 := bstep (se 1 (by rfl) ⟨1940567, by rfl⟩ : syracuseStep 2587423 = 3881135) B3881135
theorem B3449897 : Blo 2299435 3449897 := bstep (se 2 (by rfl) ⟨1293711, by rfl⟩ : syracuseStep 3449897 = 2587423) B2587423
theorem B2299931 : Blo 2299435 2299931 := bstep (se 1 (by rfl) ⟨1724948, by rfl⟩ : syracuseStep 2299931 = 3449897) B3449897
theorem B3684053 : Blo 2299435 3684053 := bbase (se 7 (by rfl) ⟨43172, by rfl⟩ : syracuseStep 3684053 = 86345) (by norm_num)
theorem B9824141 : Blo 2299435 9824141 := bstep (se 3 (by rfl) ⟨1842026, by rfl⟩ : syracuseStep 9824141 = 3684053) B3684053
theorem B6549427 : Blo 2299435 6549427 := bstep (se 1 (by rfl) ⟨4912070, by rfl⟩ : syracuseStep 6549427 = 9824141) B9824141
theorem B8732569 : Blo 2299435 8732569 := bstep (se 2 (by rfl) ⟨3274713, by rfl⟩ : syracuseStep 8732569 = 6549427) B6549427
theorem B11643425 : Blo 2299435 11643425 := bstep (se 2 (by rfl) ⟨4366284, by rfl⟩ : syracuseStep 11643425 = 8732569) B8732569
theorem B7762283 : Blo 2299435 7762283 := bstep (se 1 (by rfl) ⟨5821712, by rfl⟩ : syracuseStep 7762283 = 11643425) B11643425
theorem B5174855 : Blo 2299435 5174855 := bstep (se 1 (by rfl) ⟨3881141, by rfl⟩ : syracuseStep 5174855 = 7762283) B7762283
theorem B3449903 : Blo 2299435 3449903 := bstep (se 1 (by rfl) ⟨2587427, by rfl⟩ : syracuseStep 3449903 = 5174855) B5174855
theorem B2299935 : Blo 2299435 2299935 := bstep (se 1 (by rfl) ⟨1724951, by rfl⟩ : syracuseStep 2299935 = 3449903) B3449903
theorem B3449909 : Blo 2299435 3449909 := bbase (se 5 (by rfl) ⟨161714, by rfl⟩ : syracuseStep 3449909 = 323429) (by norm_num)
theorem B2299939 : Blo 2299435 2299939 := bstep (se 1 (by rfl) ⟨1724954, by rfl⟩ : syracuseStep 2299939 = 3449909) B3449909
theorem B5821733 : Blo 2299435 5821733 := bbase (se 4 (by rfl) ⟨545787, by rfl⟩ : syracuseStep 5821733 = 1091575) (by norm_num)
theorem B3881155 : Blo 2299435 3881155 := bstep (se 1 (by rfl) ⟨2910866, by rfl⟩ : syracuseStep 3881155 = 5821733) B5821733
theorem B5174873 : Blo 2299435 5174873 := bstep (se 2 (by rfl) ⟨1940577, by rfl⟩ : syracuseStep 5174873 = 3881155) B3881155
theorem B3449915 : Blo 2299435 3449915 := bstep (se 1 (by rfl) ⟨2587436, by rfl⟩ : syracuseStep 3449915 = 5174873) B5174873
theorem B2299943 : Blo 2299435 2299943 := bstep (se 1 (by rfl) ⟨1724957, by rfl⟩ : syracuseStep 2299943 = 3449915) B3449915
theorem B2587441 : Blo 2299435 2587441 := bbase (se 2 (by rfl) ⟨970290, by rfl⟩ : syracuseStep 2587441 = 1940581) (by norm_num)
theorem B3449921 : Blo 2299435 3449921 := bstep (se 2 (by rfl) ⟨1293720, by rfl⟩ : syracuseStep 3449921 = 2587441) B2587441
theorem B2299947 : Blo 2299435 2299947 := bstep (se 1 (by rfl) ⟨1724960, by rfl⟩ : syracuseStep 2299947 = 3449921) B3449921
theorem B31472981 : Blo 2299435 31472981 := bbase (se 11 (by rfl) ⟨23051, by rfl⟩ : syracuseStep 31472981 = 46103) (by norm_num)
theorem B20981987 : Blo 2299435 20981987 := bstep (se 1 (by rfl) ⟨15736490, by rfl⟩ : syracuseStep 20981987 = 31472981) B31472981
theorem B13987991 : Blo 2299435 13987991 := bstep (se 1 (by rfl) ⟨10490993, by rfl⟩ : syracuseStep 13987991 = 20981987) B20981987
theorem B9325327 : Blo 2299435 9325327 := bstep (se 1 (by rfl) ⟨6993995, by rfl⟩ : syracuseStep 9325327 = 13987991) B13987991
theorem B12433769 : Blo 2299435 12433769 := bstep (se 2 (by rfl) ⟨4662663, by rfl⟩ : syracuseStep 12433769 = 9325327) B9325327
theorem B8289179 : Blo 2299435 8289179 := bstep (se 1 (by rfl) ⟨6216884, by rfl⟩ : syracuseStep 8289179 = 12433769) B12433769
theorem B5526119 : Blo 2299435 5526119 := bstep (se 1 (by rfl) ⟨4144589, by rfl⟩ : syracuseStep 5526119 = 8289179) B8289179
theorem B3684079 : Blo 2299435 3684079 := bstep (se 1 (by rfl) ⟨2763059, by rfl⟩ : syracuseStep 3684079 = 5526119) B5526119
theorem B4912105 : Blo 2299435 4912105 := bstep (se 2 (by rfl) ⟨1842039, by rfl⟩ : syracuseStep 4912105 = 3684079) B3684079
theorem B6549473 : Blo 2299435 6549473 := bstep (se 2 (by rfl) ⟨2456052, by rfl⟩ : syracuseStep 6549473 = 4912105) B4912105
theorem B4366315 : Blo 2299435 4366315 := bstep (se 1 (by rfl) ⟨3274736, by rfl⟩ : syracuseStep 4366315 = 6549473) B6549473
theorem B5821753 : Blo 2299435 5821753 := bstep (se 2 (by rfl) ⟨2183157, by rfl⟩ : syracuseStep 5821753 = 4366315) B4366315
theorem B7762337 : Blo 2299435 7762337 := bstep (se 2 (by rfl) ⟨2910876, by rfl⟩ : syracuseStep 7762337 = 5821753) B5821753
theorem B5174891 : Blo 2299435 5174891 := bstep (se 1 (by rfl) ⟨3881168, by rfl⟩ : syracuseStep 5174891 = 7762337) B7762337
theorem B3449927 : Blo 2299435 3449927 := bstep (se 1 (by rfl) ⟨2587445, by rfl⟩ : syracuseStep 3449927 = 5174891) B5174891
theorem B2299951 : Blo 2299435 2299951 := bstep (se 1 (by rfl) ⟨1724963, by rfl⟩ : syracuseStep 2299951 = 3449927) B3449927
theorem B3449933 : Blo 2299435 3449933 := bbase (se 3 (by rfl) ⟨646862, by rfl⟩ : syracuseStep 3449933 = 1293725) (by norm_num)
theorem B2299955 : Blo 2299435 2299955 := bstep (se 1 (by rfl) ⟨1724966, by rfl⟩ : syracuseStep 2299955 = 3449933) B3449933
theorem B5174909 : Blo 2299435 5174909 := bbase (se 3 (by rfl) ⟨970295, by rfl⟩ : syracuseStep 5174909 = 1940591) (by norm_num)
theorem B3449939 : Blo 2299435 3449939 := bstep (se 1 (by rfl) ⟨2587454, by rfl⟩ : syracuseStep 3449939 = 5174909) B5174909
theorem B2299959 : Blo 2299435 2299959 := bstep (se 1 (by rfl) ⟨1724969, by rfl⟩ : syracuseStep 2299959 = 3449939) B3449939
theorem B3881189 : Blo 2299435 3881189 := bbase (se 4 (by rfl) ⟨363861, by rfl⟩ : syracuseStep 3881189 = 727723) (by norm_num)
theorem B2587459 : Blo 2299435 2587459 := bstep (se 1 (by rfl) ⟨1940594, by rfl⟩ : syracuseStep 2587459 = 3881189) B3881189
theorem B3449945 : Blo 2299435 3449945 := bstep (se 2 (by rfl) ⟨1293729, by rfl⟩ : syracuseStep 3449945 = 2587459) B2587459
theorem B2299963 : Blo 2299435 2299963 := bstep (se 1 (by rfl) ⟨1724972, by rfl⟩ : syracuseStep 2299963 = 3449945) B3449945
theorem B5526157 : Blo 2299435 5526157 := bbase (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) (by norm_num)
theorem B7368209 : Blo 2299435 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B4912139 : Blo 2299435 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B3274759 : Blo 2299435 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B17465381 : Blo 2299435 17465381 := bstep (se 4 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 17465381 = 3274759) B3274759
theorem B11643587 : Blo 2299435 11643587 := bstep (se 1 (by rfl) ⟨8732690, by rfl⟩ : syracuseStep 11643587 = 17465381) B17465381
theorem B7762391 : Blo 2299435 7762391 := bstep (se 1 (by rfl) ⟨5821793, by rfl⟩ : syracuseStep 7762391 = 11643587) B11643587
theorem B5174927 : Blo 2299435 5174927 := bstep (se 1 (by rfl) ⟨3881195, by rfl⟩ : syracuseStep 5174927 = 7762391) B7762391
theorem B3449951 : Blo 2299435 3449951 := bstep (se 1 (by rfl) ⟨2587463, by rfl⟩ : syracuseStep 3449951 = 5174927) B5174927
theorem B2299967 : Blo 2299435 2299967 := bstep (se 1 (by rfl) ⟨1724975, by rfl⟩ : syracuseStep 2299967 = 3449951) B3449951
theorem B3449957 : Blo 2299435 3449957 := bbase (se 4 (by rfl) ⟨323433, by rfl⟩ : syracuseStep 3449957 = 646867) (by norm_num)
theorem B2299971 : Blo 2299435 2299971 := bstep (se 1 (by rfl) ⟨1724978, by rfl⟩ : syracuseStep 2299971 = 3449957) B3449957
theorem B4912157 : Blo 2299435 4912157 := bbase (se 3 (by rfl) ⟨921029, by rfl⟩ : syracuseStep 4912157 = 1842059) (by norm_num)
theorem B3274771 : Blo 2299435 3274771 := bstep (se 1 (by rfl) ⟨2456078, by rfl⟩ : syracuseStep 3274771 = 4912157) B4912157
theorem B4366361 : Blo 2299435 4366361 := bstep (se 2 (by rfl) ⟨1637385, by rfl⟩ : syracuseStep 4366361 = 3274771) B3274771
theorem B2910907 : Blo 2299435 2910907 := bstep (se 1 (by rfl) ⟨2183180, by rfl⟩ : syracuseStep 2910907 = 4366361) B4366361
theorem B3881209 : Blo 2299435 3881209 := bstep (se 2 (by rfl) ⟨1455453, by rfl⟩ : syracuseStep 3881209 = 2910907) B2910907
theorem B5174945 : Blo 2299435 5174945 := bstep (se 2 (by rfl) ⟨1940604, by rfl⟩ : syracuseStep 5174945 = 3881209) B3881209
theorem B3449963 : Blo 2299435 3449963 := bstep (se 1 (by rfl) ⟨2587472, by rfl⟩ : syracuseStep 3449963 = 5174945) B5174945
theorem B2299975 : Blo 2299435 2299975 := bstep (se 1 (by rfl) ⟨1724981, by rfl⟩ : syracuseStep 2299975 = 3449963) B3449963
theorem B2587477 : Blo 2299435 2587477 := bbase (se 9 (by rfl) ⟨7580, by rfl⟩ : syracuseStep 2587477 = 15161) (by norm_num)
theorem B3449969 : Blo 2299435 3449969 := bstep (se 2 (by rfl) ⟨1293738, by rfl⟩ : syracuseStep 3449969 = 2587477) B2587477
theorem B2299979 : Blo 2299435 2299979 := bstep (se 1 (by rfl) ⟨1724984, by rfl⟩ : syracuseStep 2299979 = 3449969) B3449969
theorem B2910917 : Blo 2299435 2910917 := bbase (se 4 (by rfl) ⟨272898, by rfl⟩ : syracuseStep 2910917 = 545797) (by norm_num)
theorem B7762445 : Blo 2299435 7762445 := bstep (se 3 (by rfl) ⟨1455458, by rfl⟩ : syracuseStep 7762445 = 2910917) B2910917
theorem B5174963 : Blo 2299435 5174963 := bstep (se 1 (by rfl) ⟨3881222, by rfl⟩ : syracuseStep 5174963 = 7762445) B7762445
theorem B3449975 : Blo 2299435 3449975 := bstep (se 1 (by rfl) ⟨2587481, by rfl⟩ : syracuseStep 3449975 = 5174963) B5174963
theorem B2299983 : Blo 2299435 2299983 := bstep (se 1 (by rfl) ⟨1724987, by rfl⟩ : syracuseStep 2299983 = 3449975) B3449975
theorem B3449981 : Blo 2299435 3449981 := bbase (se 3 (by rfl) ⟨646871, by rfl⟩ : syracuseStep 3449981 = 1293743) (by norm_num)
theorem B2299987 : Blo 2299435 2299987 := bstep (se 1 (by rfl) ⟨1724990, by rfl⟩ : syracuseStep 2299987 = 3449981) B3449981
theorem B5174981 : Blo 2299435 5174981 := bbase (se 4 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 5174981 = 970309) (by norm_num)
theorem B3449987 : Blo 2299435 3449987 := bstep (se 1 (by rfl) ⟨2587490, by rfl⟩ : syracuseStep 3449987 = 5174981) B5174981
theorem B2299991 : Blo 2299435 2299991 := bstep (se 1 (by rfl) ⟨1724993, by rfl⟩ : syracuseStep 2299991 = 3449987) B3449987
theorem B5245597 : Blo 2299435 5245597 := bbase (se 3 (by rfl) ⟨983549, by rfl⟩ : syracuseStep 5245597 = 1967099) (by norm_num)
theorem B6994129 : Blo 2299435 6994129 := bstep (se 2 (by rfl) ⟨2622798, by rfl⟩ : syracuseStep 6994129 = 5245597) B5245597
theorem B9325505 : Blo 2299435 9325505 := bstep (se 2 (by rfl) ⟨3497064, by rfl⟩ : syracuseStep 9325505 = 6994129) B6994129
theorem B6217003 : Blo 2299435 6217003 := bstep (se 1 (by rfl) ⟨4662752, by rfl⟩ : syracuseStep 6217003 = 9325505) B9325505
theorem B33157349 : Blo 2299435 33157349 := bstep (se 4 (by rfl) ⟨3108501, by rfl⟩ : syracuseStep 33157349 = 6217003) B6217003
theorem B22104899 : Blo 2299435 22104899 := bstep (se 1 (by rfl) ⟨16578674, by rfl⟩ : syracuseStep 22104899 = 33157349) B33157349
theorem B14736599 : Blo 2299435 14736599 := bstep (se 1 (by rfl) ⟨11052449, by rfl⟩ : syracuseStep 14736599 = 22104899) B22104899
theorem B9824399 : Blo 2299435 9824399 := bstep (se 1 (by rfl) ⟨7368299, by rfl⟩ : syracuseStep 9824399 = 14736599) B14736599
theorem B6549599 : Blo 2299435 6549599 := bstep (se 1 (by rfl) ⟨4912199, by rfl⟩ : syracuseStep 6549599 = 9824399) B9824399
theorem B4366399 : Blo 2299435 4366399 := bstep (se 1 (by rfl) ⟨3274799, by rfl⟩ : syracuseStep 4366399 = 6549599) B6549599
theorem B5821865 : Blo 2299435 5821865 := bstep (se 2 (by rfl) ⟨2183199, by rfl⟩ : syracuseStep 5821865 = 4366399) B4366399
theorem B3881243 : Blo 2299435 3881243 := bstep (se 1 (by rfl) ⟨2910932, by rfl⟩ : syracuseStep 3881243 = 5821865) B5821865
theorem B2587495 : Blo 2299435 2587495 := bstep (se 1 (by rfl) ⟨1940621, by rfl⟩ : syracuseStep 2587495 = 3881243) B3881243
theorem B3449993 : Blo 2299435 3449993 := bstep (se 2 (by rfl) ⟨1293747, by rfl⟩ : syracuseStep 3449993 = 2587495) B2587495
theorem B2299995 : Blo 2299435 2299995 := bstep (se 1 (by rfl) ⟨1724996, by rfl⟩ : syracuseStep 2299995 = 3449993) B3449993
theorem B11643749 : Blo 2299435 11643749 := bbase (se 4 (by rfl) ⟨1091601, by rfl⟩ : syracuseStep 11643749 = 2183203) (by norm_num)
theorem B7762499 : Blo 2299435 7762499 := bstep (se 1 (by rfl) ⟨5821874, by rfl⟩ : syracuseStep 7762499 = 11643749) B11643749
theorem B5174999 : Blo 2299435 5174999 := bstep (se 1 (by rfl) ⟨3881249, by rfl⟩ : syracuseStep 5174999 = 7762499) B7762499
theorem B3449999 : Blo 2299435 3449999 := bstep (se 1 (by rfl) ⟨2587499, by rfl⟩ : syracuseStep 3449999 = 5174999) B5174999
theorem B2299999 : Blo 2299435 2299999 := bstep (se 1 (by rfl) ⟨1724999, by rfl⟩ : syracuseStep 2299999 = 3449999) B3449999
theorem B3450005 : Blo 2299435 3450005 := bbase (se 6 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 3450005 = 161719) (by norm_num)
theorem B2300003 : Blo 2299435 2300003 := bstep (se 1 (by rfl) ⟨1725002, by rfl⟩ : syracuseStep 2300003 = 3450005) B3450005
theorem B5526253 : Blo 2299435 5526253 := bbase (se 3 (by rfl) ⟨1036172, by rfl⟩ : syracuseStep 5526253 = 2072345) (by norm_num)
theorem B7368337 : Blo 2299435 7368337 := bstep (se 2 (by rfl) ⟨2763126, by rfl⟩ : syracuseStep 7368337 = 5526253) B5526253
theorem B9824449 : Blo 2299435 9824449 := bstep (se 2 (by rfl) ⟨3684168, by rfl⟩ : syracuseStep 9824449 = 7368337) B7368337
theorem B13099265 : Blo 2299435 13099265 := bstep (se 2 (by rfl) ⟨4912224, by rfl⟩ : syracuseStep 13099265 = 9824449) B9824449
theorem B8732843 : Blo 2299435 8732843 := bstep (se 1 (by rfl) ⟨6549632, by rfl⟩ : syracuseStep 8732843 = 13099265) B13099265
theorem B5821895 : Blo 2299435 5821895 := bstep (se 1 (by rfl) ⟨4366421, by rfl⟩ : syracuseStep 5821895 = 8732843) B8732843
theorem B3881263 : Blo 2299435 3881263 := bstep (se 1 (by rfl) ⟨2910947, by rfl⟩ : syracuseStep 3881263 = 5821895) B5821895
theorem B5175017 : Blo 2299435 5175017 := bstep (se 2 (by rfl) ⟨1940631, by rfl⟩ : syracuseStep 5175017 = 3881263) B3881263
theorem B3450011 : Blo 2299435 3450011 := bstep (se 1 (by rfl) ⟨2587508, by rfl⟩ : syracuseStep 3450011 = 5175017) B5175017
theorem B2300007 : Blo 2299435 2300007 := bstep (se 1 (by rfl) ⟨1725005, by rfl⟩ : syracuseStep 2300007 = 3450011) B3450011
theorem B2587513 : Blo 2299435 2587513 := bbase (se 2 (by rfl) ⟨970317, by rfl⟩ : syracuseStep 2587513 = 1940635) (by norm_num)
theorem B3450017 : Blo 2299435 3450017 := bstep (se 2 (by rfl) ⟨1293756, by rfl⟩ : syracuseStep 3450017 = 2587513) B2587513
theorem B2300011 : Blo 2299435 2300011 := bstep (se 1 (by rfl) ⟨1725008, by rfl⟩ : syracuseStep 2300011 = 3450017) B3450017
theorem B14736725 : Blo 2299435 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B9824483 : Blo 2299435 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B6549655 : Blo 2299435 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B8732873 : Blo 2299435 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B5821915 : Blo 2299435 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B7762553 : Blo 2299435 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B5175035 : Blo 2299435 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B3450023 : Blo 2299435 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B2300015 : Blo 2299435 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B3450029 : Blo 2299435 3450029 := bbase (se 3 (by rfl) ⟨646880, by rfl⟩ : syracuseStep 3450029 = 1293761) (by norm_num)
theorem B2300019 : Blo 2299435 2300019 := bstep (se 1 (by rfl) ⟨1725014, by rfl⟩ : syracuseStep 2300019 = 3450029) B3450029
theorem B5175053 : Blo 2299435 5175053 := bbase (se 3 (by rfl) ⟨970322, by rfl⟩ : syracuseStep 5175053 = 1940645) (by norm_num)
theorem B3450035 : Blo 2299435 3450035 := bstep (se 1 (by rfl) ⟨2587526, by rfl⟩ : syracuseStep 3450035 = 5175053) B5175053
theorem B2300023 : Blo 2299435 2300023 := bstep (se 1 (by rfl) ⟨1725017, by rfl⟩ : syracuseStep 2300023 = 3450035) B3450035
theorem B2910973 : Blo 2299435 2910973 := bbase (se 3 (by rfl) ⟨545807, by rfl⟩ : syracuseStep 2910973 = 1091615) (by norm_num)
theorem B3881297 : Blo 2299435 3881297 := bstep (se 2 (by rfl) ⟨1455486, by rfl⟩ : syracuseStep 3881297 = 2910973) B2910973
theorem B2587531 : Blo 2299435 2587531 := bstep (se 1 (by rfl) ⟨1940648, by rfl⟩ : syracuseStep 2587531 = 3881297) B3881297
theorem B3450041 : Blo 2299435 3450041 := bstep (se 2 (by rfl) ⟨1293765, by rfl⟩ : syracuseStep 3450041 = 2587531) B2587531
theorem B2300027 : Blo 2299435 2300027 := bstep (se 1 (by rfl) ⟨1725020, by rfl⟩ : syracuseStep 2300027 = 3450041) B3450041
theorem B4144733 : Blo 2299435 4144733 := bbase (se 3 (by rfl) ⟨777137, by rfl⟩ : syracuseStep 4144733 = 1554275) (by norm_num)
theorem B2763155 : Blo 2299435 2763155 := bstep (se 1 (by rfl) ⟨2072366, by rfl⟩ : syracuseStep 2763155 = 4144733) B4144733
theorem B7368413 : Blo 2299435 7368413 := bstep (se 3 (by rfl) ⟨1381577, by rfl⟩ : syracuseStep 7368413 = 2763155) B2763155
theorem B19649101 : Blo 2299435 19649101 := bstep (se 3 (by rfl) ⟨3684206, by rfl⟩ : syracuseStep 19649101 = 7368413) B7368413
theorem B26198801 : Blo 2299435 26198801 := bstep (se 2 (by rfl) ⟨9824550, by rfl⟩ : syracuseStep 26198801 = 19649101) B19649101
theorem B17465867 : Blo 2299435 17465867 := bstep (se 1 (by rfl) ⟨13099400, by rfl⟩ : syracuseStep 17465867 = 26198801) B26198801
theorem B11643911 : Blo 2299435 11643911 := bstep (se 1 (by rfl) ⟨8732933, by rfl⟩ : syracuseStep 11643911 = 17465867) B17465867
theorem B7762607 : Blo 2299435 7762607 := bstep (se 1 (by rfl) ⟨5821955, by rfl⟩ : syracuseStep 7762607 = 11643911) B11643911
theorem B5175071 : Blo 2299435 5175071 := bstep (se 1 (by rfl) ⟨3881303, by rfl⟩ : syracuseStep 5175071 = 7762607) B7762607
theorem B3450047 : Blo 2299435 3450047 := bstep (se 1 (by rfl) ⟨2587535, by rfl⟩ : syracuseStep 3450047 = 5175071) B5175071
theorem B2300031 : Blo 2299435 2300031 := bstep (se 1 (by rfl) ⟨1725023, by rfl⟩ : syracuseStep 2300031 = 3450047) B3450047
theorem B3450053 : Blo 2299435 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B2300035 : Blo 2299435 2300035 := bstep (se 1 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 2300035 = 3450053) B3450053
theorem B3881317 : Blo 2299435 3881317 := bbase (se 4 (by rfl) ⟨363873, by rfl⟩ : syracuseStep 3881317 = 727747) (by norm_num)
theorem B5175089 : Blo 2299435 5175089 := bstep (se 2 (by rfl) ⟨1940658, by rfl⟩ : syracuseStep 5175089 = 3881317) B3881317
theorem B3450059 : Blo 2299435 3450059 := bstep (se 1 (by rfl) ⟨2587544, by rfl⟩ : syracuseStep 3450059 = 5175089) B5175089
theorem B2300039 : Blo 2299435 2300039 := bstep (se 1 (by rfl) ⟨1725029, by rfl⟩ : syracuseStep 2300039 = 3450059) B3450059
theorem B2587549 : Blo 2299435 2587549 := bbase (se 3 (by rfl) ⟨485165, by rfl⟩ : syracuseStep 2587549 = 970331) (by norm_num)
theorem B3450065 : Blo 2299435 3450065 := bstep (se 2 (by rfl) ⟨1293774, by rfl⟩ : syracuseStep 3450065 = 2587549) B2587549
theorem B2300043 : Blo 2299435 2300043 := bstep (se 1 (by rfl) ⟨1725032, by rfl⟩ : syracuseStep 2300043 = 3450065) B3450065
theorem B7762661 : Blo 2299435 7762661 := bbase (se 4 (by rfl) ⟨727749, by rfl⟩ : syracuseStep 7762661 = 1455499) (by norm_num)
theorem B5175107 : Blo 2299435 5175107 := bstep (se 1 (by rfl) ⟨3881330, by rfl⟩ : syracuseStep 5175107 = 7762661) B7762661
theorem B3450071 : Blo 2299435 3450071 := bstep (se 1 (by rfl) ⟨2587553, by rfl⟩ : syracuseStep 3450071 = 5175107) B5175107
theorem B2300047 : Blo 2299435 2300047 := bstep (se 1 (by rfl) ⟨1725035, by rfl⟩ : syracuseStep 2300047 = 3450071) B3450071
theorem B3450077 : Blo 2299435 3450077 := bbase (se 3 (by rfl) ⟨646889, by rfl⟩ : syracuseStep 3450077 = 1293779) (by norm_num)
theorem B2300051 : Blo 2299435 2300051 := bstep (se 1 (by rfl) ⟨1725038, by rfl⟩ : syracuseStep 2300051 = 3450077) B3450077
theorem B5175125 : Blo 2299435 5175125 := bbase (se 9 (by rfl) ⟨15161, by rfl⟩ : syracuseStep 5175125 = 30323) (by norm_num)
theorem B3450083 : Blo 2299435 3450083 := bstep (se 1 (by rfl) ⟨2587562, by rfl⟩ : syracuseStep 3450083 = 5175125) B5175125
theorem B2300055 : Blo 2299435 2300055 := bstep (se 1 (by rfl) ⟨1725041, by rfl⟩ : syracuseStep 2300055 = 3450083) B3450083
theorem B6549781 : Blo 2299435 6549781 := bbase (se 6 (by rfl) ⟨153510, by rfl⟩ : syracuseStep 6549781 = 307021) (by norm_num)
theorem B8733041 : Blo 2299435 8733041 := bstep (se 2 (by rfl) ⟨3274890, by rfl⟩ : syracuseStep 8733041 = 6549781) B6549781
theorem B5822027 : Blo 2299435 5822027 := bstep (se 1 (by rfl) ⟨4366520, by rfl⟩ : syracuseStep 5822027 = 8733041) B8733041
theorem B3881351 : Blo 2299435 3881351 := bstep (se 1 (by rfl) ⟨2911013, by rfl⟩ : syracuseStep 3881351 = 5822027) B5822027
theorem B2587567 : Blo 2299435 2587567 := bstep (se 1 (by rfl) ⟨1940675, by rfl⟩ : syracuseStep 2587567 = 3881351) B3881351
theorem B3450089 : Blo 2299435 3450089 := bstep (se 2 (by rfl) ⟨1293783, by rfl⟩ : syracuseStep 3450089 = 2587567) B2587567
theorem B2300059 : Blo 2299435 2300059 := bstep (se 1 (by rfl) ⟨1725044, by rfl⟩ : syracuseStep 2300059 = 3450089) B3450089
theorem B3734525 : Blo 2299435 3734525 := bbase (se 3 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 3734525 = 1400447) (by norm_num)
theorem B9958733 : Blo 2299435 9958733 := bstep (se 3 (by rfl) ⟨1867262, by rfl⟩ : syracuseStep 9958733 = 3734525) B3734525
theorem B6639155 : Blo 2299435 6639155 := bstep (se 1 (by rfl) ⟨4979366, by rfl⟩ : syracuseStep 6639155 = 9958733) B9958733
theorem B4426103 : Blo 2299435 4426103 := bstep (se 1 (by rfl) ⟨3319577, by rfl⟩ : syracuseStep 4426103 = 6639155) B6639155
theorem B11802941 : Blo 2299435 11802941 := bstep (se 3 (by rfl) ⟨2213051, by rfl⟩ : syracuseStep 11802941 = 4426103) B4426103
theorem B7868627 : Blo 2299435 7868627 := bstep (se 1 (by rfl) ⟨5901470, by rfl⟩ : syracuseStep 7868627 = 11802941) B11802941
theorem B5245751 : Blo 2299435 5245751 := bstep (se 1 (by rfl) ⟨3934313, by rfl⟩ : syracuseStep 5245751 = 7868627) B7868627
theorem B3497167 : Blo 2299435 3497167 := bstep (se 1 (by rfl) ⟨2622875, by rfl⟩ : syracuseStep 3497167 = 5245751) B5245751
theorem B4662889 : Blo 2299435 4662889 := bstep (se 2 (by rfl) ⟨1748583, by rfl⟩ : syracuseStep 4662889 = 3497167) B3497167
theorem B99474965 : Blo 2299435 99474965 := bstep (se 6 (by rfl) ⟨2331444, by rfl⟩ : syracuseStep 99474965 = 4662889) B4662889
theorem B66316643 : Blo 2299435 66316643 := bstep (se 1 (by rfl) ⟨49737482, by rfl⟩ : syracuseStep 66316643 = 99474965) B99474965
theorem B44211095 : Blo 2299435 44211095 := bstep (se 1 (by rfl) ⟨33158321, by rfl⟩ : syracuseStep 44211095 = 66316643) B66316643
theorem B29474063 : Blo 2299435 29474063 := bstep (se 1 (by rfl) ⟨22105547, by rfl⟩ : syracuseStep 29474063 = 44211095) B44211095
theorem B19649375 : Blo 2299435 19649375 := bstep (se 1 (by rfl) ⟨14737031, by rfl⟩ : syracuseStep 19649375 = 29474063) B29474063
theorem B13099583 : Blo 2299435 13099583 := bstep (se 1 (by rfl) ⟨9824687, by rfl⟩ : syracuseStep 13099583 = 19649375) B19649375
theorem B8733055 : Blo 2299435 8733055 := bstep (se 1 (by rfl) ⟨6549791, by rfl⟩ : syracuseStep 8733055 = 13099583) B13099583
theorem B11644073 : Blo 2299435 11644073 := bstep (se 2 (by rfl) ⟨4366527, by rfl⟩ : syracuseStep 11644073 = 8733055) B8733055
theorem B7762715 : Blo 2299435 7762715 := bstep (se 1 (by rfl) ⟨5822036, by rfl⟩ : syracuseStep 7762715 = 11644073) B11644073
theorem B5175143 : Blo 2299435 5175143 := bstep (se 1 (by rfl) ⟨3881357, by rfl⟩ : syracuseStep 5175143 = 7762715) B7762715
theorem B3450095 : Blo 2299435 3450095 := bstep (se 1 (by rfl) ⟨2587571, by rfl⟩ : syracuseStep 3450095 = 5175143) B5175143
theorem B2300063 : Blo 2299435 2300063 := bstep (se 1 (by rfl) ⟨1725047, by rfl⟩ : syracuseStep 2300063 = 3450095) B3450095
theorem B3450101 : Blo 2299435 3450101 := bbase (se 5 (by rfl) ⟨161723, by rfl⟩ : syracuseStep 3450101 = 323447) (by norm_num)
theorem B2300067 : Blo 2299435 2300067 := bstep (se 1 (by rfl) ⟨1725050, by rfl⟩ : syracuseStep 2300067 = 3450101) B3450101
theorem B9325813 : Blo 2299435 9325813 := bbase (se 5 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 9325813 = 874295) (by norm_num)
theorem B12434417 : Blo 2299435 12434417 := bstep (se 2 (by rfl) ⟨4662906, by rfl⟩ : syracuseStep 12434417 = 9325813) B9325813
theorem B8289611 : Blo 2299435 8289611 := bstep (se 1 (by rfl) ⟨6217208, by rfl⟩ : syracuseStep 8289611 = 12434417) B12434417
theorem B5526407 : Blo 2299435 5526407 := bstep (se 1 (by rfl) ⟨4144805, by rfl⟩ : syracuseStep 5526407 = 8289611) B8289611
theorem B14737085 : Blo 2299435 14737085 := bstep (se 3 (by rfl) ⟨2763203, by rfl⟩ : syracuseStep 14737085 = 5526407) B5526407
theorem B9824723 : Blo 2299435 9824723 := bstep (se 1 (by rfl) ⟨7368542, by rfl⟩ : syracuseStep 9824723 = 14737085) B14737085
theorem B6549815 : Blo 2299435 6549815 := bstep (se 1 (by rfl) ⟨4912361, by rfl⟩ : syracuseStep 6549815 = 9824723) B9824723
theorem B4366543 : Blo 2299435 4366543 := bstep (se 1 (by rfl) ⟨3274907, by rfl⟩ : syracuseStep 4366543 = 6549815) B6549815
theorem B5822057 : Blo 2299435 5822057 := bstep (se 2 (by rfl) ⟨2183271, by rfl⟩ : syracuseStep 5822057 = 4366543) B4366543
theorem B3881371 : Blo 2299435 3881371 := bstep (se 1 (by rfl) ⟨2911028, by rfl⟩ : syracuseStep 3881371 = 5822057) B5822057
theorem B5175161 : Blo 2299435 5175161 := bstep (se 2 (by rfl) ⟨1940685, by rfl⟩ : syracuseStep 5175161 = 3881371) B3881371
theorem B3450107 : Blo 2299435 3450107 := bstep (se 1 (by rfl) ⟨2587580, by rfl⟩ : syracuseStep 3450107 = 5175161) B5175161
theorem B2300071 : Blo 2299435 2300071 := bstep (se 1 (by rfl) ⟨1725053, by rfl⟩ : syracuseStep 2300071 = 3450107) B3450107
theorem B2587585 : Blo 2299435 2587585 := bbase (se 2 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 2587585 = 1940689) (by norm_num)
theorem B3450113 : Blo 2299435 3450113 := bstep (se 2 (by rfl) ⟨1293792, by rfl⟩ : syracuseStep 3450113 = 2587585) B2587585
theorem B2300075 : Blo 2299435 2300075 := bstep (se 1 (by rfl) ⟨1725056, by rfl⟩ : syracuseStep 2300075 = 3450113) B3450113
theorem B5822077 : Blo 2299435 5822077 := bbase (se 3 (by rfl) ⟨1091639, by rfl⟩ : syracuseStep 5822077 = 2183279) (by norm_num)
theorem B7762769 : Blo 2299435 7762769 := bstep (se 2 (by rfl) ⟨2911038, by rfl⟩ : syracuseStep 7762769 = 5822077) B5822077
theorem B5175179 : Blo 2299435 5175179 := bstep (se 1 (by rfl) ⟨3881384, by rfl⟩ : syracuseStep 5175179 = 7762769) B7762769
theorem B3450119 : Blo 2299435 3450119 := bstep (se 1 (by rfl) ⟨2587589, by rfl⟩ : syracuseStep 3450119 = 5175179) B5175179
theorem B2300079 : Blo 2299435 2300079 := bstep (se 1 (by rfl) ⟨1725059, by rfl⟩ : syracuseStep 2300079 = 3450119) B3450119
theorem B3450125 : Blo 2299435 3450125 := bbase (se 3 (by rfl) ⟨646898, by rfl⟩ : syracuseStep 3450125 = 1293797) (by norm_num)
theorem B2300083 : Blo 2299435 2300083 := bstep (se 1 (by rfl) ⟨1725062, by rfl⟩ : syracuseStep 2300083 = 3450125) B3450125
theorem B5175197 : Blo 2299435 5175197 := bbase (se 3 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 5175197 = 1940699) (by norm_num)
theorem B3450131 : Blo 2299435 3450131 := bstep (se 1 (by rfl) ⟨2587598, by rfl⟩ : syracuseStep 3450131 = 5175197) B5175197
theorem B2300087 : Blo 2299435 2300087 := bstep (se 1 (by rfl) ⟨1725065, by rfl⟩ : syracuseStep 2300087 = 3450131) B3450131
theorem B3881405 : Blo 2299435 3881405 := bbase (se 3 (by rfl) ⟨727763, by rfl⟩ : syracuseStep 3881405 = 1455527) (by norm_num)
theorem B2587603 : Blo 2299435 2587603 := bstep (se 1 (by rfl) ⟨1940702, by rfl⟩ : syracuseStep 2587603 = 3881405) B3881405
theorem B3450137 : Blo 2299435 3450137 := bstep (se 2 (by rfl) ⟨1293801, by rfl⟩ : syracuseStep 3450137 = 2587603) B2587603
theorem B2300091 : Blo 2299435 2300091 := bstep (se 1 (by rfl) ⟨1725068, by rfl⟩ : syracuseStep 2300091 = 3450137) B3450137
theorem B13099765 : Blo 2299435 13099765 := bbase (se 5 (by rfl) ⟨614051, by rfl⟩ : syracuseStep 13099765 = 1228103) (by norm_num)
theorem B17466353 : Blo 2299435 17466353 := bstep (se 2 (by rfl) ⟨6549882, by rfl⟩ : syracuseStep 17466353 = 13099765) B13099765
theorem B11644235 : Blo 2299435 11644235 := bstep (se 1 (by rfl) ⟨8733176, by rfl⟩ : syracuseStep 11644235 = 17466353) B17466353
theorem B7762823 : Blo 2299435 7762823 := bstep (se 1 (by rfl) ⟨5822117, by rfl⟩ : syracuseStep 7762823 = 11644235) B11644235
theorem B5175215 : Blo 2299435 5175215 := bstep (se 1 (by rfl) ⟨3881411, by rfl⟩ : syracuseStep 5175215 = 7762823) B7762823
theorem B3450143 : Blo 2299435 3450143 := bstep (se 1 (by rfl) ⟨2587607, by rfl⟩ : syracuseStep 3450143 = 5175215) B5175215
theorem B2300095 : Blo 2299435 2300095 := bstep (se 1 (by rfl) ⟨1725071, by rfl⟩ : syracuseStep 2300095 = 3450143) B3450143
theorem B3450149 : Blo 2299435 3450149 := bbase (se 4 (by rfl) ⟨323451, by rfl⟩ : syracuseStep 3450149 = 646903) (by norm_num)
theorem B2300099 : Blo 2299435 2300099 := bstep (se 1 (by rfl) ⟨1725074, by rfl⟩ : syracuseStep 2300099 = 3450149) B3450149
theorem B2911069 : Blo 2299435 2911069 := bbase (se 3 (by rfl) ⟨545825, by rfl⟩ : syracuseStep 2911069 = 1091651) (by norm_num)
theorem B3881425 : Blo 2299435 3881425 := bstep (se 2 (by rfl) ⟨1455534, by rfl⟩ : syracuseStep 3881425 = 2911069) B2911069
theorem B5175233 : Blo 2299435 5175233 := bstep (se 2 (by rfl) ⟨1940712, by rfl⟩ : syracuseStep 5175233 = 3881425) B3881425
theorem B3450155 : Blo 2299435 3450155 := bstep (se 1 (by rfl) ⟨2587616, by rfl⟩ : syracuseStep 3450155 = 5175233) B5175233
theorem B2300103 : Blo 2299435 2300103 := bstep (se 1 (by rfl) ⟨1725077, by rfl⟩ : syracuseStep 2300103 = 3450155) B3450155
theorem B2587621 : Blo 2299435 2587621 := bbase (se 4 (by rfl) ⟨242589, by rfl⟩ : syracuseStep 2587621 = 485179) (by norm_num)
theorem B3450161 : Blo 2299435 3450161 := bstep (se 2 (by rfl) ⟨1293810, by rfl⟩ : syracuseStep 3450161 = 2587621) B2587621
theorem B2300107 : Blo 2299435 2300107 := bstep (se 1 (by rfl) ⟨1725080, by rfl⟩ : syracuseStep 2300107 = 3450161) B3450161
theorem B20983445 : Blo 2299435 20983445 := bbase (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) (by norm_num)
theorem B13988963 : Blo 2299435 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B37303901 : Blo 2299435 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B24869267 : Blo 2299435 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B16579511 : Blo 2299435 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B11053007 : Blo 2299435 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B7368671 : Blo 2299435 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B4912447 : Blo 2299435 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B6549929 : Blo 2299435 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B4366619 : Blo 2299435 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B2911079 : Blo 2299435 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B7762877 : Blo 2299435 7762877 := bstep (se 3 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 7762877 = 2911079) B2911079
theorem B5175251 : Blo 2299435 5175251 := bstep (se 1 (by rfl) ⟨3881438, by rfl⟩ : syracuseStep 5175251 = 7762877) B7762877
theorem B3450167 : Blo 2299435 3450167 := bstep (se 1 (by rfl) ⟨2587625, by rfl⟩ : syracuseStep 3450167 = 5175251) B5175251
theorem B2300111 : Blo 2299435 2300111 := bstep (se 1 (by rfl) ⟨1725083, by rfl⟩ : syracuseStep 2300111 = 3450167) B3450167
theorem B3450173 : Blo 2299435 3450173 := bbase (se 3 (by rfl) ⟨646907, by rfl⟩ : syracuseStep 3450173 = 1293815) (by norm_num)
theorem B2300115 : Blo 2299435 2300115 := bstep (se 1 (by rfl) ⟨1725086, by rfl⟩ : syracuseStep 2300115 = 3450173) B3450173
theorem B5175269 : Blo 2299435 5175269 := bbase (se 4 (by rfl) ⟨485181, by rfl⟩ : syracuseStep 5175269 = 970363) (by norm_num)
theorem B3450179 : Blo 2299435 3450179 := bstep (se 1 (by rfl) ⟨2587634, by rfl⟩ : syracuseStep 3450179 = 5175269) B5175269
theorem B2300119 : Blo 2299435 2300119 := bstep (se 1 (by rfl) ⟨1725089, by rfl⟩ : syracuseStep 2300119 = 3450179) B3450179
theorem B5822189 : Blo 2299435 5822189 := bbase (se 3 (by rfl) ⟨1091660, by rfl⟩ : syracuseStep 5822189 = 2183321) (by norm_num)
theorem B3881459 : Blo 2299435 3881459 := bstep (se 1 (by rfl) ⟨2911094, by rfl⟩ : syracuseStep 3881459 = 5822189) B5822189
theorem B2587639 : Blo 2299435 2587639 := bstep (se 1 (by rfl) ⟨1940729, by rfl⟩ : syracuseStep 2587639 = 3881459) B3881459
theorem B3450185 : Blo 2299435 3450185 := bstep (se 2 (by rfl) ⟨1293819, by rfl⟩ : syracuseStep 3450185 = 2587639) B2587639
theorem B2300123 : Blo 2299435 2300123 := bstep (se 1 (by rfl) ⟨1725092, by rfl⟩ : syracuseStep 2300123 = 3450185) B3450185
theorem B4663021 : Blo 2299435 4663021 := bbase (se 3 (by rfl) ⟨874316, by rfl⟩ : syracuseStep 4663021 = 1748633) (by norm_num)
theorem B6217361 : Blo 2299435 6217361 := bstep (se 2 (by rfl) ⟨2331510, by rfl⟩ : syracuseStep 6217361 = 4663021) B4663021
theorem B4144907 : Blo 2299435 4144907 := bstep (se 1 (by rfl) ⟨3108680, by rfl⟩ : syracuseStep 4144907 = 6217361) B6217361
theorem B2763271 : Blo 2299435 2763271 := bstep (se 1 (by rfl) ⟨2072453, by rfl⟩ : syracuseStep 2763271 = 4144907) B4144907
theorem B3684361 : Blo 2299435 3684361 := bstep (se 2 (by rfl) ⟨1381635, by rfl⟩ : syracuseStep 3684361 = 2763271) B2763271
theorem B4912481 : Blo 2299435 4912481 := bstep (se 2 (by rfl) ⟨1842180, by rfl⟩ : syracuseStep 4912481 = 3684361) B3684361
theorem B3274987 : Blo 2299435 3274987 := bstep (se 1 (by rfl) ⟨2456240, by rfl⟩ : syracuseStep 3274987 = 4912481) B4912481
theorem B4366649 : Blo 2299435 4366649 := bstep (se 2 (by rfl) ⟨1637493, by rfl⟩ : syracuseStep 4366649 = 3274987) B3274987
theorem B11644397 : Blo 2299435 11644397 := bstep (se 3 (by rfl) ⟨2183324, by rfl⟩ : syracuseStep 11644397 = 4366649) B4366649
theorem B7762931 : Blo 2299435 7762931 := bstep (se 1 (by rfl) ⟨5822198, by rfl⟩ : syracuseStep 7762931 = 11644397) B11644397
theorem B5175287 : Blo 2299435 5175287 := bstep (se 1 (by rfl) ⟨3881465, by rfl⟩ : syracuseStep 5175287 = 7762931) B7762931
theorem B3450191 : Blo 2299435 3450191 := bstep (se 1 (by rfl) ⟨2587643, by rfl⟩ : syracuseStep 3450191 = 5175287) B5175287
theorem B2300127 : Blo 2299435 2300127 := bstep (se 1 (by rfl) ⟨1725095, by rfl⟩ : syracuseStep 2300127 = 3450191) B3450191
theorem B3450197 : Blo 2299435 3450197 := bbase (se 12 (by rfl) ⟨1263, by rfl⟩ : syracuseStep 3450197 = 2527) (by norm_num)
theorem B2300131 : Blo 2299435 2300131 := bstep (se 1 (by rfl) ⟨1725098, by rfl⟩ : syracuseStep 2300131 = 3450197) B3450197
theorem B2456249 : Blo 2299435 2456249 := bbase (se 2 (by rfl) ⟨921093, by rfl⟩ : syracuseStep 2456249 = 1842187) (by norm_num)
theorem B6549997 : Blo 2299435 6549997 := bstep (se 3 (by rfl) ⟨1228124, by rfl⟩ : syracuseStep 6549997 = 2456249) B2456249
theorem B8733329 : Blo 2299435 8733329 := bstep (se 2 (by rfl) ⟨3274998, by rfl⟩ : syracuseStep 8733329 = 6549997) B6549997
theorem B5822219 : Blo 2299435 5822219 := bstep (se 1 (by rfl) ⟨4366664, by rfl⟩ : syracuseStep 5822219 = 8733329) B8733329
theorem B3881479 : Blo 2299435 3881479 := bstep (se 1 (by rfl) ⟨2911109, by rfl⟩ : syracuseStep 3881479 = 5822219) B5822219
theorem B5175305 : Blo 2299435 5175305 := bstep (se 2 (by rfl) ⟨1940739, by rfl⟩ : syracuseStep 5175305 = 3881479) B3881479
theorem B3450203 : Blo 2299435 3450203 := bstep (se 1 (by rfl) ⟨2587652, by rfl⟩ : syracuseStep 3450203 = 5175305) B5175305
theorem B2300135 : Blo 2299435 2300135 := bstep (se 1 (by rfl) ⟨1725101, by rfl⟩ : syracuseStep 2300135 = 3450203) B3450203
theorem B2587657 : Blo 2299435 2587657 := bbase (se 2 (by rfl) ⟨970371, by rfl⟩ : syracuseStep 2587657 = 1940743) (by norm_num)
theorem B3450209 : Blo 2299435 3450209 := bstep (se 2 (by rfl) ⟨1293828, by rfl⟩ : syracuseStep 3450209 = 2587657) B2587657
theorem B2300139 : Blo 2299435 2300139 := bstep (se 1 (by rfl) ⟨1725104, by rfl⟩ : syracuseStep 2300139 = 3450209) B3450209
theorem B3108701 : Blo 2299435 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B8289869 : Blo 2299435 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B22106317 : Blo 2299435 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B29475089 : Blo 2299435 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B19650059 : Blo 2299435 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B13100039 : Blo 2299435 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B8733359 : Blo 2299435 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B5822239 : Blo 2299435 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B7762985 : Blo 2299435 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B5175323 : Blo 2299435 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B3450215 : Blo 2299435 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B2300143 : Blo 2299435 2300143 := bstep (se 1 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 2300143 = 3450215) B3450215
theorem B3450221 : Blo 2299435 3450221 := bbase (se 3 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 3450221 = 1293833) (by norm_num)
theorem B2300147 : Blo 2299435 2300147 := bstep (se 1 (by rfl) ⟨1725110, by rfl⟩ : syracuseStep 2300147 = 3450221) B3450221
theorem B5175341 : Blo 2299435 5175341 := bbase (se 3 (by rfl) ⟨970376, by rfl⟩ : syracuseStep 5175341 = 1940753) (by norm_num)
theorem B3450227 : Blo 2299435 3450227 := bstep (se 1 (by rfl) ⟨2587670, by rfl⟩ : syracuseStep 3450227 = 5175341) B5175341
theorem B2300151 : Blo 2299435 2300151 := bstep (se 1 (by rfl) ⟨1725113, by rfl⟩ : syracuseStep 2300151 = 3450227) B3450227
theorem B16579829 : Blo 2299435 16579829 := bbase (se 5 (by rfl) ⟨777179, by rfl⟩ : syracuseStep 16579829 = 1554359) (by norm_num)
theorem B11053219 : Blo 2299435 11053219 := bstep (se 1 (by rfl) ⟨8289914, by rfl⟩ : syracuseStep 11053219 = 16579829) B16579829
theorem B14737625 : Blo 2299435 14737625 := bstep (se 2 (by rfl) ⟨5526609, by rfl⟩ : syracuseStep 14737625 = 11053219) B11053219
theorem B9825083 : Blo 2299435 9825083 := bstep (se 1 (by rfl) ⟨7368812, by rfl⟩ : syracuseStep 9825083 = 14737625) B14737625
theorem B6550055 : Blo 2299435 6550055 := bstep (se 1 (by rfl) ⟨4912541, by rfl⟩ : syracuseStep 6550055 = 9825083) B9825083
theorem B4366703 : Blo 2299435 4366703 := bstep (se 1 (by rfl) ⟨3275027, by rfl⟩ : syracuseStep 4366703 = 6550055) B6550055
theorem B2911135 : Blo 2299435 2911135 := bstep (se 1 (by rfl) ⟨2183351, by rfl⟩ : syracuseStep 2911135 = 4366703) B4366703
theorem B3881513 : Blo 2299435 3881513 := bstep (se 2 (by rfl) ⟨1455567, by rfl⟩ : syracuseStep 3881513 = 2911135) B2911135
theorem B2587675 : Blo 2299435 2587675 := bstep (se 1 (by rfl) ⟨1940756, by rfl⟩ : syracuseStep 2587675 = 3881513) B3881513
theorem B3450233 : Blo 2299435 3450233 := bstep (se 2 (by rfl) ⟨1293837, by rfl⟩ : syracuseStep 3450233 = 2587675) B2587675
theorem B2300155 : Blo 2299435 2300155 := bstep (se 1 (by rfl) ⟨1725116, by rfl⟩ : syracuseStep 2300155 = 3450233) B3450233
theorem B6217445 : Blo 2299435 6217445 := bbase (se 4 (by rfl) ⟨582885, by rfl⟩ : syracuseStep 6217445 = 1165771) (by norm_num)
theorem B16579853 : Blo 2299435 16579853 := bstep (se 3 (by rfl) ⟨3108722, by rfl⟩ : syracuseStep 16579853 = 6217445) B6217445
theorem B11053235 : Blo 2299435 11053235 := bstep (se 1 (by rfl) ⟨8289926, by rfl⟩ : syracuseStep 11053235 = 16579853) B16579853
theorem B7368823 : Blo 2299435 7368823 := bstep (se 1 (by rfl) ⟨5526617, by rfl⟩ : syracuseStep 7368823 = 11053235) B11053235
theorem B39300389 : Blo 2299435 39300389 := bstep (se 4 (by rfl) ⟨3684411, by rfl⟩ : syracuseStep 39300389 = 7368823) B7368823
theorem B26200259 : Blo 2299435 26200259 := bstep (se 1 (by rfl) ⟨19650194, by rfl⟩ : syracuseStep 26200259 = 39300389) B39300389
theorem B17466839 : Blo 2299435 17466839 := bstep (se 1 (by rfl) ⟨13100129, by rfl⟩ : syracuseStep 17466839 = 26200259) B26200259
theorem B11644559 : Blo 2299435 11644559 := bstep (se 1 (by rfl) ⟨8733419, by rfl⟩ : syracuseStep 11644559 = 17466839) B17466839
theorem B7763039 : Blo 2299435 7763039 := bstep (se 1 (by rfl) ⟨5822279, by rfl⟩ : syracuseStep 7763039 = 11644559) B11644559
theorem B5175359 : Blo 2299435 5175359 := bstep (se 1 (by rfl) ⟨3881519, by rfl⟩ : syracuseStep 5175359 = 7763039) B7763039
theorem B3450239 : Blo 2299435 3450239 := bstep (se 1 (by rfl) ⟨2587679, by rfl⟩ : syracuseStep 3450239 = 5175359) B5175359
theorem B2300159 : Blo 2299435 2300159 := bstep (se 1 (by rfl) ⟨1725119, by rfl⟩ : syracuseStep 2300159 = 3450239) B3450239
theorem B3450245 : Blo 2299435 3450245 := bbase (se 4 (by rfl) ⟨323460, by rfl⟩ : syracuseStep 3450245 = 646921) (by norm_num)
theorem B2300163 : Blo 2299435 2300163 := bstep (se 1 (by rfl) ⟨1725122, by rfl⟩ : syracuseStep 2300163 = 3450245) B3450245
theorem B3881533 : Blo 2299435 3881533 := bbase (se 3 (by rfl) ⟨727787, by rfl⟩ : syracuseStep 3881533 = 1455575) (by norm_num)
theorem B5175377 : Blo 2299435 5175377 := bstep (se 2 (by rfl) ⟨1940766, by rfl⟩ : syracuseStep 5175377 = 3881533) B3881533
theorem B3450251 : Blo 2299435 3450251 := bstep (se 1 (by rfl) ⟨2587688, by rfl⟩ : syracuseStep 3450251 = 5175377) B5175377
theorem B2300167 : Blo 2299435 2300167 := bstep (se 1 (by rfl) ⟨1725125, by rfl⟩ : syracuseStep 2300167 = 3450251) B3450251
theorem B2587693 : Blo 2299435 2587693 := bbase (se 3 (by rfl) ⟨485192, by rfl⟩ : syracuseStep 2587693 = 970385) (by norm_num)
theorem B3450257 : Blo 2299435 3450257 := bstep (se 2 (by rfl) ⟨1293846, by rfl⟩ : syracuseStep 3450257 = 2587693) B2587693
theorem B2300171 : Blo 2299435 2300171 := bstep (se 1 (by rfl) ⟨1725128, by rfl⟩ : syracuseStep 2300171 = 3450257) B3450257
theorem B7763093 : Blo 2299435 7763093 := bbase (se 6 (by rfl) ⟨181947, by rfl⟩ : syracuseStep 7763093 = 363895) (by norm_num)
theorem B5175395 : Blo 2299435 5175395 := bstep (se 1 (by rfl) ⟨3881546, by rfl⟩ : syracuseStep 5175395 = 7763093) B7763093
theorem B3450263 : Blo 2299435 3450263 := bstep (se 1 (by rfl) ⟨2587697, by rfl⟩ : syracuseStep 3450263 = 5175395) B5175395
theorem B2300175 : Blo 2299435 2300175 := bstep (se 1 (by rfl) ⟨1725131, by rfl⟩ : syracuseStep 2300175 = 3450263) B3450263
theorem B3450269 : Blo 2299435 3450269 := bbase (se 3 (by rfl) ⟨646925, by rfl⟩ : syracuseStep 3450269 = 1293851) (by norm_num)
theorem B2300179 : Blo 2299435 2300179 := bstep (se 1 (by rfl) ⟨1725134, by rfl⟩ : syracuseStep 2300179 = 3450269) B3450269
theorem B5175413 : Blo 2299435 5175413 := bbase (se 5 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 5175413 = 485195) (by norm_num)
theorem B3450275 : Blo 2299435 3450275 := bstep (se 1 (by rfl) ⟨2587706, by rfl⟩ : syracuseStep 3450275 = 5175413) B5175413
theorem B2300183 : Blo 2299435 2300183 := bstep (se 1 (by rfl) ⟨1725137, by rfl⟩ : syracuseStep 2300183 = 3450275) B3450275
theorem B3497357 : Blo 2299435 3497357 := bbase (se 3 (by rfl) ⟨655754, by rfl⟩ : syracuseStep 3497357 = 1311509) (by norm_num)
theorem B9326285 : Blo 2299435 9326285 := bstep (se 3 (by rfl) ⟨1748678, by rfl⟩ : syracuseStep 9326285 = 3497357) B3497357
theorem B6217523 : Blo 2299435 6217523 := bstep (se 1 (by rfl) ⟨4663142, by rfl⟩ : syracuseStep 6217523 = 9326285) B9326285
theorem B4145015 : Blo 2299435 4145015 := bstep (se 1 (by rfl) ⟨3108761, by rfl⟩ : syracuseStep 4145015 = 6217523) B6217523
theorem B2763343 : Blo 2299435 2763343 := bstep (se 1 (by rfl) ⟨2072507, by rfl⟩ : syracuseStep 2763343 = 4145015) B4145015
theorem B3684457 : Blo 2299435 3684457 := bstep (se 2 (by rfl) ⟨1381671, by rfl⟩ : syracuseStep 3684457 = 2763343) B2763343
theorem B19650437 : Blo 2299435 19650437 := bstep (se 4 (by rfl) ⟨1842228, by rfl⟩ : syracuseStep 19650437 = 3684457) B3684457
theorem B13100291 : Blo 2299435 13100291 := bstep (se 1 (by rfl) ⟨9825218, by rfl⟩ : syracuseStep 13100291 = 19650437) B19650437
theorem B8733527 : Blo 2299435 8733527 := bstep (se 1 (by rfl) ⟨6550145, by rfl⟩ : syracuseStep 8733527 = 13100291) B13100291
theorem B5822351 : Blo 2299435 5822351 := bstep (se 1 (by rfl) ⟨4366763, by rfl⟩ : syracuseStep 5822351 = 8733527) B8733527
theorem B3881567 : Blo 2299435 3881567 := bstep (se 1 (by rfl) ⟨2911175, by rfl⟩ : syracuseStep 3881567 = 5822351) B5822351
theorem B2587711 : Blo 2299435 2587711 := bstep (se 1 (by rfl) ⟨1940783, by rfl⟩ : syracuseStep 2587711 = 3881567) B3881567
theorem B3450281 : Blo 2299435 3450281 := bstep (se 2 (by rfl) ⟨1293855, by rfl⟩ : syracuseStep 3450281 = 2587711) B2587711
theorem B2300187 : Blo 2299435 2300187 := bstep (se 1 (by rfl) ⟨1725140, by rfl⟩ : syracuseStep 2300187 = 3450281) B3450281
theorem B8733541 : Blo 2299435 8733541 := bbase (se 4 (by rfl) ⟨818769, by rfl⟩ : syracuseStep 8733541 = 1637539) (by norm_num)
theorem B11644721 : Blo 2299435 11644721 := bstep (se 2 (by rfl) ⟨4366770, by rfl⟩ : syracuseStep 11644721 = 8733541) B8733541
theorem B7763147 : Blo 2299435 7763147 := bstep (se 1 (by rfl) ⟨5822360, by rfl⟩ : syracuseStep 7763147 = 11644721) B11644721
theorem B5175431 : Blo 2299435 5175431 := bstep (se 1 (by rfl) ⟨3881573, by rfl⟩ : syracuseStep 5175431 = 7763147) B7763147
theorem B3450287 : Blo 2299435 3450287 := bstep (se 1 (by rfl) ⟨2587715, by rfl⟩ : syracuseStep 3450287 = 5175431) B5175431
theorem B2300191 : Blo 2299435 2300191 := bstep (se 1 (by rfl) ⟨1725143, by rfl⟩ : syracuseStep 2300191 = 3450287) B3450287
theorem B3450293 : Blo 2299435 3450293 := bbase (se 5 (by rfl) ⟨161732, by rfl⟩ : syracuseStep 3450293 = 323465) (by norm_num)
theorem B2300195 : Blo 2299435 2300195 := bstep (se 1 (by rfl) ⟨1725146, by rfl⟩ : syracuseStep 2300195 = 3450293) B3450293
theorem B5822381 : Blo 2299435 5822381 := bbase (se 3 (by rfl) ⟨1091696, by rfl⟩ : syracuseStep 5822381 = 2183393) (by norm_num)
theorem B3881587 : Blo 2299435 3881587 := bstep (se 1 (by rfl) ⟨2911190, by rfl⟩ : syracuseStep 3881587 = 5822381) B5822381
theorem B5175449 : Blo 2299435 5175449 := bstep (se 2 (by rfl) ⟨1940793, by rfl⟩ : syracuseStep 5175449 = 3881587) B3881587
theorem B3450299 : Blo 2299435 3450299 := bstep (se 1 (by rfl) ⟨2587724, by rfl⟩ : syracuseStep 3450299 = 5175449) B5175449
theorem B2300199 : Blo 2299435 2300199 := bstep (se 1 (by rfl) ⟨1725149, by rfl⟩ : syracuseStep 2300199 = 3450299) B3450299
theorem B2587729 : Blo 2299435 2587729 := bbase (se 2 (by rfl) ⟨970398, by rfl⟩ : syracuseStep 2587729 = 1940797) (by norm_num)
theorem B3450305 : Blo 2299435 3450305 := bstep (se 2 (by rfl) ⟨1293864, by rfl⟩ : syracuseStep 3450305 = 2587729) B2587729
theorem B2300203 : Blo 2299435 2300203 := bstep (se 1 (by rfl) ⟨1725152, by rfl⟩ : syracuseStep 2300203 = 3450305) B3450305
theorem B3275101 : Blo 2299435 3275101 := bbase (se 3 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 3275101 = 1228163) (by norm_num)
theorem B4366801 : Blo 2299435 4366801 := bstep (se 2 (by rfl) ⟨1637550, by rfl⟩ : syracuseStep 4366801 = 3275101) B3275101
theorem B5822401 : Blo 2299435 5822401 := bstep (se 2 (by rfl) ⟨2183400, by rfl⟩ : syracuseStep 5822401 = 4366801) B4366801
theorem B7763201 : Blo 2299435 7763201 := bstep (se 2 (by rfl) ⟨2911200, by rfl⟩ : syracuseStep 7763201 = 5822401) B5822401
theorem B5175467 : Blo 2299435 5175467 := bstep (se 1 (by rfl) ⟨3881600, by rfl⟩ : syracuseStep 5175467 = 7763201) B7763201
theorem B3450311 : Blo 2299435 3450311 := bstep (se 1 (by rfl) ⟨2587733, by rfl⟩ : syracuseStep 3450311 = 5175467) B5175467
theorem B2300207 : Blo 2299435 2300207 := bstep (se 1 (by rfl) ⟨1725155, by rfl⟩ : syracuseStep 2300207 = 3450311) B3450311
theorem B3450317 : Blo 2299435 3450317 := bbase (se 3 (by rfl) ⟨646934, by rfl⟩ : syracuseStep 3450317 = 1293869) (by norm_num)
theorem B2300211 : Blo 2299435 2300211 := bstep (se 1 (by rfl) ⟨1725158, by rfl⟩ : syracuseStep 2300211 = 3450317) B3450317
theorem B5175485 : Blo 2299435 5175485 := bbase (se 3 (by rfl) ⟨970403, by rfl⟩ : syracuseStep 5175485 = 1940807) (by norm_num)
theorem B3450323 : Blo 2299435 3450323 := bstep (se 1 (by rfl) ⟨2587742, by rfl⟩ : syracuseStep 3450323 = 5175485) B5175485
theorem B2300215 : Blo 2299435 2300215 := bstep (se 1 (by rfl) ⟨1725161, by rfl⟩ : syracuseStep 2300215 = 3450323) B3450323
theorem B3881621 : Blo 2299435 3881621 := bbase (se 6 (by rfl) ⟨90975, by rfl⟩ : syracuseStep 3881621 = 181951) (by norm_num)
theorem B2587747 : Blo 2299435 2587747 := bstep (se 1 (by rfl) ⟨1940810, by rfl⟩ : syracuseStep 2587747 = 3881621) B3881621
theorem B3450329 : Blo 2299435 3450329 := bstep (se 2 (by rfl) ⟨1293873, by rfl⟩ : syracuseStep 3450329 = 2587747) B2587747
theorem B2300219 : Blo 2299435 2300219 := bstep (se 1 (by rfl) ⟨1725164, by rfl⟩ : syracuseStep 2300219 = 3450329) B3450329
theorem B1552389461 : Blo 2299435 1552389461 := bbase (se 14 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 1552389461 = 284251) (by norm_num)
theorem B1034926307 : Blo 2299435 1034926307 := bstep (se 1 (by rfl) ⟨776194730, by rfl⟩ : syracuseStep 1034926307 = 1552389461) B1552389461
theorem B689950871 : Blo 2299435 689950871 := bstep (se 1 (by rfl) ⟨517463153, by rfl⟩ : syracuseStep 689950871 = 1034926307) B1034926307
theorem B459967247 : Blo 2299435 459967247 := bstep (se 1 (by rfl) ⟨344975435, by rfl⟩ : syracuseStep 459967247 = 689950871) B689950871
theorem B306644831 : Blo 2299435 306644831 := bstep (se 1 (by rfl) ⟨229983623, by rfl⟩ : syracuseStep 306644831 = 459967247) B459967247
theorem B204429887 : Blo 2299435 204429887 := bstep (se 1 (by rfl) ⟨153322415, by rfl⟩ : syracuseStep 204429887 = 306644831) B306644831
theorem B2180585461 : Blo 2299435 2180585461 := bstep (se 5 (by rfl) ⟨102214943, by rfl⟩ : syracuseStep 2180585461 = 204429887) B204429887
theorem B2907447281 : Blo 2299435 2907447281 := bstep (se 2 (by rfl) ⟨1090292730, by rfl⟩ : syracuseStep 2907447281 = 2180585461) B2180585461
theorem B1938298187 : Blo 2299435 1938298187 := bstep (se 1 (by rfl) ⟨1453723640, by rfl⟩ : syracuseStep 1938298187 = 2907447281) B2907447281
theorem B1292198791 : Blo 2299435 1292198791 := bstep (se 1 (by rfl) ⟨969149093, by rfl⟩ : syracuseStep 1292198791 = 1938298187) B1938298187
theorem B1722931721 : Blo 2299435 1722931721 := bstep (se 2 (by rfl) ⟨646099395, by rfl⟩ : syracuseStep 1722931721 = 1292198791) B1292198791
theorem B1148621147 : Blo 2299435 1148621147 := bstep (se 1 (by rfl) ⟨861465860, by rfl⟩ : syracuseStep 1148621147 = 1722931721) B1722931721
theorem B765747431 : Blo 2299435 765747431 := bstep (se 1 (by rfl) ⟨574310573, by rfl⟩ : syracuseStep 765747431 = 1148621147) B1148621147
theorem B510498287 : Blo 2299435 510498287 := bstep (se 1 (by rfl) ⟨382873715, by rfl⟩ : syracuseStep 510498287 = 765747431) B765747431
theorem B340332191 : Blo 2299435 340332191 := bstep (se 1 (by rfl) ⟨255249143, by rfl⟩ : syracuseStep 340332191 = 510498287) B510498287
theorem B226888127 : Blo 2299435 226888127 := bstep (se 1 (by rfl) ⟨170166095, by rfl⟩ : syracuseStep 226888127 = 340332191) B340332191
theorem B151258751 : Blo 2299435 151258751 := bstep (se 1 (by rfl) ⟨113444063, by rfl⟩ : syracuseStep 151258751 = 226888127) B226888127
theorem B100839167 : Blo 2299435 100839167 := bstep (se 1 (by rfl) ⟨75629375, by rfl⟩ : syracuseStep 100839167 = 151258751) B151258751
theorem B67226111 : Blo 2299435 67226111 := bstep (se 1 (by rfl) ⟨50419583, by rfl⟩ : syracuseStep 67226111 = 100839167) B100839167
theorem B44817407 : Blo 2299435 44817407 := bstep (se 1 (by rfl) ⟨33613055, by rfl⟩ : syracuseStep 44817407 = 67226111) B67226111
theorem B29878271 : Blo 2299435 29878271 := bstep (se 1 (by rfl) ⟨22408703, by rfl⟩ : syracuseStep 29878271 = 44817407) B44817407
theorem B19918847 : Blo 2299435 19918847 := bstep (se 1 (by rfl) ⟨14939135, by rfl⟩ : syracuseStep 19918847 = 29878271) B29878271
theorem B13279231 : Blo 2299435 13279231 := bstep (se 1 (by rfl) ⟨9959423, by rfl⟩ : syracuseStep 13279231 = 19918847) B19918847
theorem B17705641 : Blo 2299435 17705641 := bstep (se 2 (by rfl) ⟨6639615, by rfl⟩ : syracuseStep 17705641 = 13279231) B13279231
theorem B23607521 : Blo 2299435 23607521 := bstep (se 2 (by rfl) ⟨8852820, by rfl⟩ : syracuseStep 23607521 = 17705641) B17705641
theorem B15738347 : Blo 2299435 15738347 := bstep (se 1 (by rfl) ⟨11803760, by rfl⟩ : syracuseStep 15738347 = 23607521) B23607521
theorem B41968925 : Blo 2299435 41968925 := bstep (se 3 (by rfl) ⟨7869173, by rfl⟩ : syracuseStep 41968925 = 15738347) B15738347
theorem B27979283 : Blo 2299435 27979283 := bstep (se 1 (by rfl) ⟨20984462, by rfl⟩ : syracuseStep 27979283 = 41968925) B41968925
theorem B18652855 : Blo 2299435 18652855 := bstep (se 1 (by rfl) ⟨13989641, by rfl⟩ : syracuseStep 18652855 = 27979283) B27979283
theorem B24870473 : Blo 2299435 24870473 := bstep (se 2 (by rfl) ⟨9326427, by rfl⟩ : syracuseStep 24870473 = 18652855) B18652855
theorem B16580315 : Blo 2299435 16580315 := bstep (se 1 (by rfl) ⟨12435236, by rfl⟩ : syracuseStep 16580315 = 24870473) B24870473
theorem B11053543 : Blo 2299435 11053543 := bstep (se 1 (by rfl) ⟨8290157, by rfl⟩ : syracuseStep 11053543 = 16580315) B16580315
theorem B14738057 : Blo 2299435 14738057 := bstep (se 2 (by rfl) ⟨5526771, by rfl⟩ : syracuseStep 14738057 = 11053543) B11053543
theorem B9825371 : Blo 2299435 9825371 := bstep (se 1 (by rfl) ⟨7369028, by rfl⟩ : syracuseStep 9825371 = 14738057) B14738057
theorem B6550247 : Blo 2299435 6550247 := bstep (se 1 (by rfl) ⟨4912685, by rfl⟩ : syracuseStep 6550247 = 9825371) B9825371
theorem B17467325 : Blo 2299435 17467325 := bstep (se 3 (by rfl) ⟨3275123, by rfl⟩ : syracuseStep 17467325 = 6550247) B6550247
theorem B11644883 : Blo 2299435 11644883 := bstep (se 1 (by rfl) ⟨8733662, by rfl⟩ : syracuseStep 11644883 = 17467325) B17467325
theorem B7763255 : Blo 2299435 7763255 := bstep (se 1 (by rfl) ⟨5822441, by rfl⟩ : syracuseStep 7763255 = 11644883) B11644883
theorem B5175503 : Blo 2299435 5175503 := bstep (se 1 (by rfl) ⟨3881627, by rfl⟩ : syracuseStep 5175503 = 7763255) B7763255
theorem B3450335 : Blo 2299435 3450335 := bstep (se 1 (by rfl) ⟨2587751, by rfl⟩ : syracuseStep 3450335 = 5175503) B5175503
theorem B2300223 : Blo 2299435 2300223 := bstep (se 1 (by rfl) ⟨1725167, by rfl⟩ : syracuseStep 2300223 = 3450335) B3450335
theorem B3450341 : Blo 2299435 3450341 := bbase (se 4 (by rfl) ⟨323469, by rfl⟩ : syracuseStep 3450341 = 646939) (by norm_num)
theorem B2300227 : Blo 2299435 2300227 := bstep (se 1 (by rfl) ⟨1725170, by rfl⟩ : syracuseStep 2300227 = 3450341) B3450341
theorem B5678629 : Blo 2299435 5678629 := bbase (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) (by norm_num)
theorem B30286021 : Blo 2299435 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B40381361 : Blo 2299435 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B26920907 : Blo 2299435 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B17947271 : Blo 2299435 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B11964847 : Blo 2299435 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B15953129 : Blo 2299435 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B10635419 : Blo 2299435 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B28361117 : Blo 2299435 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B18907411 : Blo 2299435 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B25209881 : Blo 2299435 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B16806587 : Blo 2299435 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B44817565 : Blo 2299435 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B59756753 : Blo 2299435 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B39837835 : Blo 2299435 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B212468453 : Blo 2299435 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B141645635 : Blo 2299435 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B94430423 : Blo 2299435 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B62953615 : Blo 2299435 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B83938153 : Blo 2299435 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B111917537 : Blo 2299435 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B74611691 : Blo 2299435 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B49741127 : Blo 2299435 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B33160751 : Blo 2299435 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B22107167 : Blo 2299435 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B14738111 : Blo 2299435 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B9825407 : Blo 2299435 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B6550271 : Blo 2299435 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B4366847 : Blo 2299435 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B2911231 : Blo 2299435 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B3881641 : Blo 2299435 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B5175521 : Blo 2299435 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B3450347 : Blo 2299435 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B2300231 : Blo 2299435 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B2587765 : Blo 2299435 2587765 := bbase (se 5 (by rfl) ⟨121301, by rfl⟩ : syracuseStep 2587765 = 242603) (by norm_num)
theorem B3450353 : Blo 2299435 3450353 := bstep (se 2 (by rfl) ⟨1293882, by rfl⟩ : syracuseStep 3450353 = 2587765) B2587765
theorem B2300235 : Blo 2299435 2300235 := bstep (se 1 (by rfl) ⟨1725176, by rfl⟩ : syracuseStep 2300235 = 3450353) B3450353
theorem B2911241 : Blo 2299435 2911241 := bbase (se 2 (by rfl) ⟨1091715, by rfl⟩ : syracuseStep 2911241 = 2183431) (by norm_num)
theorem B7763309 : Blo 2299435 7763309 := bstep (se 3 (by rfl) ⟨1455620, by rfl⟩ : syracuseStep 7763309 = 2911241) B2911241
theorem B5175539 : Blo 2299435 5175539 := bstep (se 1 (by rfl) ⟨3881654, by rfl⟩ : syracuseStep 5175539 = 7763309) B7763309
theorem B3450359 : Blo 2299435 3450359 := bstep (se 1 (by rfl) ⟨2587769, by rfl⟩ : syracuseStep 3450359 = 5175539) B5175539
theorem B2300239 : Blo 2299435 2300239 := bstep (se 1 (by rfl) ⟨1725179, by rfl⟩ : syracuseStep 2300239 = 3450359) B3450359
theorem B3450365 : Blo 2299435 3450365 := bbase (se 3 (by rfl) ⟨646943, by rfl⟩ : syracuseStep 3450365 = 1293887) (by norm_num)
theorem B2300243 : Blo 2299435 2300243 := bstep (se 1 (by rfl) ⟨1725182, by rfl⟩ : syracuseStep 2300243 = 3450365) B3450365
theorem B5175557 : Blo 2299435 5175557 := bbase (se 4 (by rfl) ⟨485208, by rfl⟩ : syracuseStep 5175557 = 970417) (by norm_num)
theorem B3450371 : Blo 2299435 3450371 := bstep (se 1 (by rfl) ⟨2587778, by rfl⟩ : syracuseStep 3450371 = 5175557) B5175557
theorem B2300247 : Blo 2299435 2300247 := bstep (se 1 (by rfl) ⟨1725185, by rfl⟩ : syracuseStep 2300247 = 3450371) B3450371
theorem B4366885 : Blo 2299435 4366885 := bbase (se 4 (by rfl) ⟨409395, by rfl⟩ : syracuseStep 4366885 = 818791) (by norm_num)
theorem B5822513 : Blo 2299435 5822513 := bstep (se 2 (by rfl) ⟨2183442, by rfl⟩ : syracuseStep 5822513 = 4366885) B4366885
theorem B3881675 : Blo 2299435 3881675 := bstep (se 1 (by rfl) ⟨2911256, by rfl⟩ : syracuseStep 3881675 = 5822513) B5822513
theorem B2587783 : Blo 2299435 2587783 := bstep (se 1 (by rfl) ⟨1940837, by rfl⟩ : syracuseStep 2587783 = 3881675) B3881675
theorem B3450377 : Blo 2299435 3450377 := bstep (se 2 (by rfl) ⟨1293891, by rfl⟩ : syracuseStep 3450377 = 2587783) B2587783
theorem B2300251 : Blo 2299435 2300251 := bstep (se 1 (by rfl) ⟨1725188, by rfl⟩ : syracuseStep 2300251 = 3450377) B3450377
theorem B11645045 : Blo 2299435 11645045 := bbase (se 5 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 11645045 = 1091723) (by norm_num)
theorem B7763363 : Blo 2299435 7763363 := bstep (se 1 (by rfl) ⟨5822522, by rfl⟩ : syracuseStep 7763363 = 11645045) B11645045
theorem B5175575 : Blo 2299435 5175575 := bstep (se 1 (by rfl) ⟨3881681, by rfl⟩ : syracuseStep 5175575 = 7763363) B7763363
theorem B3450383 : Blo 2299435 3450383 := bstep (se 1 (by rfl) ⟨2587787, by rfl⟩ : syracuseStep 3450383 = 5175575) B5175575
theorem B2300255 : Blo 2299435 2300255 := bstep (se 1 (by rfl) ⟨1725191, by rfl⟩ : syracuseStep 2300255 = 3450383) B3450383
theorem B3450389 : Blo 2299435 3450389 := bbase (se 6 (by rfl) ⟨80868, by rfl⟩ : syracuseStep 3450389 = 161737) (by norm_num)
theorem B2300259 : Blo 2299435 2300259 := bstep (se 1 (by rfl) ⟨1725194, by rfl⟩ : syracuseStep 2300259 = 3450389) B3450389
theorem B7369157 : Blo 2299435 7369157 := bbase (se 4 (by rfl) ⟨690858, by rfl⟩ : syracuseStep 7369157 = 1381717) (by norm_num)
theorem B19651085 : Blo 2299435 19651085 := bstep (se 3 (by rfl) ⟨3684578, by rfl⟩ : syracuseStep 19651085 = 7369157) B7369157
theorem B13100723 : Blo 2299435 13100723 := bstep (se 1 (by rfl) ⟨9825542, by rfl⟩ : syracuseStep 13100723 = 19651085) B19651085
theorem B8733815 : Blo 2299435 8733815 := bstep (se 1 (by rfl) ⟨6550361, by rfl⟩ : syracuseStep 8733815 = 13100723) B13100723
theorem B5822543 : Blo 2299435 5822543 := bstep (se 1 (by rfl) ⟨4366907, by rfl⟩ : syracuseStep 5822543 = 8733815) B8733815
theorem B3881695 : Blo 2299435 3881695 := bstep (se 1 (by rfl) ⟨2911271, by rfl⟩ : syracuseStep 3881695 = 5822543) B5822543
theorem B5175593 : Blo 2299435 5175593 := bstep (se 2 (by rfl) ⟨1940847, by rfl⟩ : syracuseStep 5175593 = 3881695) B3881695
theorem B3450395 : Blo 2299435 3450395 := bstep (se 1 (by rfl) ⟨2587796, by rfl⟩ : syracuseStep 3450395 = 5175593) B5175593
theorem B2300263 : Blo 2299435 2300263 := bstep (se 1 (by rfl) ⟨1725197, by rfl⟩ : syracuseStep 2300263 = 3450395) B3450395
theorem B2587801 : Blo 2299435 2587801 := bbase (se 2 (by rfl) ⟨970425, by rfl⟩ : syracuseStep 2587801 = 1940851) (by norm_num)
theorem B3450401 : Blo 2299435 3450401 := bstep (se 2 (by rfl) ⟨1293900, by rfl⟩ : syracuseStep 3450401 = 2587801) B2587801
theorem B2300267 : Blo 2299435 2300267 := bstep (se 1 (by rfl) ⟨1725200, by rfl⟩ : syracuseStep 2300267 = 3450401) B3450401
theorem B8733845 : Blo 2299435 8733845 := bbase (se 6 (by rfl) ⟨204699, by rfl⟩ : syracuseStep 8733845 = 409399) (by norm_num)
theorem B5822563 : Blo 2299435 5822563 := bstep (se 1 (by rfl) ⟨4366922, by rfl⟩ : syracuseStep 5822563 = 8733845) B8733845
theorem B7763417 : Blo 2299435 7763417 := bstep (se 2 (by rfl) ⟨2911281, by rfl⟩ : syracuseStep 7763417 = 5822563) B5822563
theorem B5175611 : Blo 2299435 5175611 := bstep (se 1 (by rfl) ⟨3881708, by rfl⟩ : syracuseStep 5175611 = 7763417) B7763417
theorem B3450407 : Blo 2299435 3450407 := bstep (se 1 (by rfl) ⟨2587805, by rfl⟩ : syracuseStep 3450407 = 5175611) B5175611
theorem B2300271 : Blo 2299435 2300271 := bstep (se 1 (by rfl) ⟨1725203, by rfl⟩ : syracuseStep 2300271 = 3450407) B3450407
theorem B3450413 : Blo 2299435 3450413 := bbase (se 3 (by rfl) ⟨646952, by rfl⟩ : syracuseStep 3450413 = 1293905) (by norm_num)
theorem B2300275 : Blo 2299435 2300275 := bstep (se 1 (by rfl) ⟨1725206, by rfl⟩ : syracuseStep 2300275 = 3450413) B3450413
theorem B5175629 : Blo 2299435 5175629 := bbase (se 3 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 5175629 = 1940861) (by norm_num)
theorem B3450419 : Blo 2299435 3450419 := bstep (se 1 (by rfl) ⟨2587814, by rfl⟩ : syracuseStep 3450419 = 5175629) B5175629
theorem B2300279 : Blo 2299435 2300279 := bstep (se 1 (by rfl) ⟨1725209, by rfl⟩ : syracuseStep 2300279 = 3450419) B3450419
theorem B2911297 : Blo 2299435 2911297 := bbase (se 2 (by rfl) ⟨1091736, by rfl⟩ : syracuseStep 2911297 = 2183473) (by norm_num)
theorem B3881729 : Blo 2299435 3881729 := bstep (se 2 (by rfl) ⟨1455648, by rfl⟩ : syracuseStep 3881729 = 2911297) B2911297
theorem B2587819 : Blo 2299435 2587819 := bstep (se 1 (by rfl) ⟨1940864, by rfl⟩ : syracuseStep 2587819 = 3881729) B3881729
theorem B3450425 : Blo 2299435 3450425 := bstep (se 2 (by rfl) ⟨1293909, by rfl⟩ : syracuseStep 3450425 = 2587819) B2587819
theorem B2300283 : Blo 2299435 2300283 := bstep (se 1 (by rfl) ⟨1725212, by rfl⟩ : syracuseStep 2300283 = 3450425) B3450425
theorem B3497509 : Blo 2299435 3497509 := bbase (se 4 (by rfl) ⟨327891, by rfl⟩ : syracuseStep 3497509 = 655783) (by norm_num)
theorem B4663345 : Blo 2299435 4663345 := bstep (se 2 (by rfl) ⟨1748754, by rfl⟩ : syracuseStep 4663345 = 3497509) B3497509
theorem B6217793 : Blo 2299435 6217793 := bstep (se 2 (by rfl) ⟨2331672, by rfl⟩ : syracuseStep 6217793 = 4663345) B4663345
theorem B4145195 : Blo 2299435 4145195 := bstep (se 1 (by rfl) ⟨3108896, by rfl⟩ : syracuseStep 4145195 = 6217793) B6217793
theorem B2763463 : Blo 2299435 2763463 := bstep (se 1 (by rfl) ⟨2072597, by rfl⟩ : syracuseStep 2763463 = 4145195) B4145195
theorem B3684617 : Blo 2299435 3684617 := bstep (se 2 (by rfl) ⟨1381731, by rfl⟩ : syracuseStep 3684617 = 2763463) B2763463
theorem B2456411 : Blo 2299435 2456411 := bstep (se 1 (by rfl) ⟨1842308, by rfl⟩ : syracuseStep 2456411 = 3684617) B3684617
theorem B26201717 : Blo 2299435 26201717 := bstep (se 5 (by rfl) ⟨1228205, by rfl⟩ : syracuseStep 26201717 = 2456411) B2456411
theorem B17467811 : Blo 2299435 17467811 := bstep (se 1 (by rfl) ⟨13100858, by rfl⟩ : syracuseStep 17467811 = 26201717) B26201717
theorem B11645207 : Blo 2299435 11645207 := bstep (se 1 (by rfl) ⟨8733905, by rfl⟩ : syracuseStep 11645207 = 17467811) B17467811
theorem B7763471 : Blo 2299435 7763471 := bstep (se 1 (by rfl) ⟨5822603, by rfl⟩ : syracuseStep 7763471 = 11645207) B11645207
theorem B5175647 : Blo 2299435 5175647 := bstep (se 1 (by rfl) ⟨3881735, by rfl⟩ : syracuseStep 5175647 = 7763471) B7763471
theorem B3450431 : Blo 2299435 3450431 := bstep (se 1 (by rfl) ⟨2587823, by rfl⟩ : syracuseStep 3450431 = 5175647) B5175647
theorem B2300287 : Blo 2299435 2300287 := bstep (se 1 (by rfl) ⟨1725215, by rfl⟩ : syracuseStep 2300287 = 3450431) B3450431
theorem B3450437 : Blo 2299435 3450437 := bbase (se 4 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 3450437 = 646957) (by norm_num)
theorem B2300291 : Blo 2299435 2300291 := bstep (se 1 (by rfl) ⟨1725218, by rfl⟩ : syracuseStep 2300291 = 3450437) B3450437
theorem B3881749 : Blo 2299435 3881749 := bbase (se 6 (by rfl) ⟨90978, by rfl⟩ : syracuseStep 3881749 = 181957) (by norm_num)
theorem B5175665 : Blo 2299435 5175665 := bstep (se 2 (by rfl) ⟨1940874, by rfl⟩ : syracuseStep 5175665 = 3881749) B3881749
theorem B3450443 : Blo 2299435 3450443 := bstep (se 1 (by rfl) ⟨2587832, by rfl⟩ : syracuseStep 3450443 = 5175665) B5175665
theorem B2300295 : Blo 2299435 2300295 := bstep (se 1 (by rfl) ⟨1725221, by rfl⟩ : syracuseStep 2300295 = 3450443) B3450443
theorem B2587837 : Blo 2299435 2587837 := bbase (se 3 (by rfl) ⟨485219, by rfl⟩ : syracuseStep 2587837 = 970439) (by norm_num)
theorem B3450449 : Blo 2299435 3450449 := bstep (se 2 (by rfl) ⟨1293918, by rfl⟩ : syracuseStep 3450449 = 2587837) B2587837
theorem B2300299 : Blo 2299435 2300299 := bstep (se 1 (by rfl) ⟨1725224, by rfl⟩ : syracuseStep 2300299 = 3450449) B3450449
theorem B7763525 : Blo 2299435 7763525 := bbase (se 4 (by rfl) ⟨727830, by rfl⟩ : syracuseStep 7763525 = 1455661) (by norm_num)
theorem B5175683 : Blo 2299435 5175683 := bstep (se 1 (by rfl) ⟨3881762, by rfl⟩ : syracuseStep 5175683 = 7763525) B7763525
theorem B3450455 : Blo 2299435 3450455 := bstep (se 1 (by rfl) ⟨2587841, by rfl⟩ : syracuseStep 3450455 = 5175683) B5175683
theorem B2300303 : Blo 2299435 2300303 := bstep (se 1 (by rfl) ⟨1725227, by rfl⟩ : syracuseStep 2300303 = 3450455) B3450455
theorem B3450461 : Blo 2299435 3450461 := bbase (se 3 (by rfl) ⟨646961, by rfl⟩ : syracuseStep 3450461 = 1293923) (by norm_num)
theorem B2300307 : Blo 2299435 2300307 := bstep (se 1 (by rfl) ⟨1725230, by rfl⟩ : syracuseStep 2300307 = 3450461) B3450461
theorem B5175701 : Blo 2299435 5175701 := bbase (se 6 (by rfl) ⟨121305, by rfl⟩ : syracuseStep 5175701 = 242611) (by norm_num)
theorem B3450467 : Blo 2299435 3450467 := bstep (se 1 (by rfl) ⟨2587850, by rfl⟩ : syracuseStep 3450467 = 5175701) B5175701
theorem B2300311 : Blo 2299435 2300311 := bstep (se 1 (by rfl) ⟨1725233, by rfl⟩ : syracuseStep 2300311 = 3450467) B3450467
theorem B2763497 : Blo 2299435 2763497 := bbase (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) (by norm_num)
theorem B7369325 : Blo 2299435 7369325 := bstep (se 3 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 7369325 = 2763497) B2763497
theorem B4912883 : Blo 2299435 4912883 := bstep (se 1 (by rfl) ⟨3684662, by rfl⟩ : syracuseStep 4912883 = 7369325) B7369325
theorem B3275255 : Blo 2299435 3275255 := bstep (se 1 (by rfl) ⟨2456441, by rfl⟩ : syracuseStep 3275255 = 4912883) B4912883
theorem B8734013 : Blo 2299435 8734013 := bstep (se 3 (by rfl) ⟨1637627, by rfl⟩ : syracuseStep 8734013 = 3275255) B3275255
theorem B5822675 : Blo 2299435 5822675 := bstep (se 1 (by rfl) ⟨4367006, by rfl⟩ : syracuseStep 5822675 = 8734013) B8734013
theorem B3881783 : Blo 2299435 3881783 := bstep (se 1 (by rfl) ⟨2911337, by rfl⟩ : syracuseStep 3881783 = 5822675) B5822675
theorem B2587855 : Blo 2299435 2587855 := bstep (se 1 (by rfl) ⟨1940891, by rfl⟩ : syracuseStep 2587855 = 3881783) B3881783
theorem B3450473 : Blo 2299435 3450473 := bstep (se 2 (by rfl) ⟨1293927, by rfl⟩ : syracuseStep 3450473 = 2587855) B2587855
theorem B2300315 : Blo 2299435 2300315 := bstep (se 1 (by rfl) ⟨1725236, by rfl⟩ : syracuseStep 2300315 = 3450473) B3450473
theorem B9825781 : Blo 2299435 9825781 := bbase (se 5 (by rfl) ⟨460583, by rfl⟩ : syracuseStep 9825781 = 921167) (by norm_num)
theorem B13101041 : Blo 2299435 13101041 := bstep (se 2 (by rfl) ⟨4912890, by rfl⟩ : syracuseStep 13101041 = 9825781) B9825781
theorem B8734027 : Blo 2299435 8734027 := bstep (se 1 (by rfl) ⟨6550520, by rfl⟩ : syracuseStep 8734027 = 13101041) B13101041
theorem B11645369 : Blo 2299435 11645369 := bstep (se 2 (by rfl) ⟨4367013, by rfl⟩ : syracuseStep 11645369 = 8734027) B8734027
theorem B7763579 : Blo 2299435 7763579 := bstep (se 1 (by rfl) ⟨5822684, by rfl⟩ : syracuseStep 7763579 = 11645369) B11645369
theorem B5175719 : Blo 2299435 5175719 := bstep (se 1 (by rfl) ⟨3881789, by rfl⟩ : syracuseStep 5175719 = 7763579) B7763579
theorem B3450479 : Blo 2299435 3450479 := bstep (se 1 (by rfl) ⟨2587859, by rfl⟩ : syracuseStep 3450479 = 5175719) B5175719
theorem B2300319 : Blo 2299435 2300319 := bstep (se 1 (by rfl) ⟨1725239, by rfl⟩ : syracuseStep 2300319 = 3450479) B3450479
theorem B3450485 : Blo 2299435 3450485 := bbase (se 5 (by rfl) ⟨161741, by rfl⟩ : syracuseStep 3450485 = 323483) (by norm_num)
theorem B2300323 : Blo 2299435 2300323 := bstep (se 1 (by rfl) ⟨1725242, by rfl⟩ : syracuseStep 2300323 = 3450485) B3450485
theorem B4367029 : Blo 2299435 4367029 := bbase (se 5 (by rfl) ⟨204704, by rfl⟩ : syracuseStep 4367029 = 409409) (by norm_num)
theorem B5822705 : Blo 2299435 5822705 := bstep (se 2 (by rfl) ⟨2183514, by rfl⟩ : syracuseStep 5822705 = 4367029) B4367029
theorem B3881803 : Blo 2299435 3881803 := bstep (se 1 (by rfl) ⟨2911352, by rfl⟩ : syracuseStep 3881803 = 5822705) B5822705
theorem B5175737 : Blo 2299435 5175737 := bstep (se 2 (by rfl) ⟨1940901, by rfl⟩ : syracuseStep 5175737 = 3881803) B3881803
theorem B3450491 : Blo 2299435 3450491 := bstep (se 1 (by rfl) ⟨2587868, by rfl⟩ : syracuseStep 3450491 = 5175737) B5175737
theorem B2300327 : Blo 2299435 2300327 := bstep (se 1 (by rfl) ⟨1725245, by rfl⟩ : syracuseStep 2300327 = 3450491) B3450491
theorem B2587873 : Blo 2299435 2587873 := bbase (se 2 (by rfl) ⟨970452, by rfl⟩ : syracuseStep 2587873 = 1940905) (by norm_num)
theorem B3450497 : Blo 2299435 3450497 := bstep (se 2 (by rfl) ⟨1293936, by rfl⟩ : syracuseStep 3450497 = 2587873) B2587873
theorem B2300331 : Blo 2299435 2300331 := bstep (se 1 (by rfl) ⟨1725248, by rfl⟩ : syracuseStep 2300331 = 3450497) B3450497
theorem B5822725 : Blo 2299435 5822725 := bbase (se 4 (by rfl) ⟨545880, by rfl⟩ : syracuseStep 5822725 = 1091761) (by norm_num)
theorem B7763633 : Blo 2299435 7763633 := bstep (se 2 (by rfl) ⟨2911362, by rfl⟩ : syracuseStep 7763633 = 5822725) B5822725
theorem B5175755 : Blo 2299435 5175755 := bstep (se 1 (by rfl) ⟨3881816, by rfl⟩ : syracuseStep 5175755 = 7763633) B7763633
theorem B3450503 : Blo 2299435 3450503 := bstep (se 1 (by rfl) ⟨2587877, by rfl⟩ : syracuseStep 3450503 = 5175755) B5175755
theorem B2300335 : Blo 2299435 2300335 := bstep (se 1 (by rfl) ⟨1725251, by rfl⟩ : syracuseStep 2300335 = 3450503) B3450503
theorem B3450509 : Blo 2299435 3450509 := bbase (se 3 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 3450509 = 1293941) (by norm_num)
theorem B2300339 : Blo 2299435 2300339 := bstep (se 1 (by rfl) ⟨1725254, by rfl⟩ : syracuseStep 2300339 = 3450509) B3450509
theorem B5175773 : Blo 2299435 5175773 := bbase (se 3 (by rfl) ⟨970457, by rfl⟩ : syracuseStep 5175773 = 1940915) (by norm_num)
theorem B3450515 : Blo 2299435 3450515 := bstep (se 1 (by rfl) ⟨2587886, by rfl⟩ : syracuseStep 3450515 = 5175773) B5175773
theorem B2300343 : Blo 2299435 2300343 := bstep (se 1 (by rfl) ⟨1725257, by rfl⟩ : syracuseStep 2300343 = 3450515) B3450515
theorem B3881837 : Blo 2299435 3881837 := bbase (se 3 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 3881837 = 1455689) (by norm_num)
theorem B2587891 : Blo 2299435 2587891 := bstep (se 1 (by rfl) ⟨1940918, by rfl⟩ : syracuseStep 2587891 = 3881837) B3881837
theorem B3450521 : Blo 2299435 3450521 := bstep (se 2 (by rfl) ⟨1293945, by rfl⟩ : syracuseStep 3450521 = 2587891) B2587891
theorem B2300347 : Blo 2299435 2300347 := bstep (se 1 (by rfl) ⟨1725260, by rfl⟩ : syracuseStep 2300347 = 3450521) B3450521
theorem B62956885 : Blo 2299435 62956885 := bbase (se 12 (by rfl) ⟨23055, by rfl⟩ : syracuseStep 62956885 = 46111) (by norm_num)
theorem B83942513 : Blo 2299435 83942513 := bstep (se 2 (by rfl) ⟨31478442, by rfl⟩ : syracuseStep 83942513 = 62956885) B62956885
theorem B55961675 : Blo 2299435 55961675 := bstep (se 1 (by rfl) ⟨41971256, by rfl⟩ : syracuseStep 55961675 = 83942513) B83942513
theorem B37307783 : Blo 2299435 37307783 := bstep (se 1 (by rfl) ⟨27980837, by rfl⟩ : syracuseStep 37307783 = 55961675) B55961675
theorem B24871855 : Blo 2299435 24871855 := bstep (se 1 (by rfl) ⟨18653891, by rfl⟩ : syracuseStep 24871855 = 37307783) B37307783
theorem B33162473 : Blo 2299435 33162473 := bstep (se 2 (by rfl) ⟨12435927, by rfl⟩ : syracuseStep 33162473 = 24871855) B24871855
theorem B22108315 : Blo 2299435 22108315 := bstep (se 1 (by rfl) ⟨16581236, by rfl⟩ : syracuseStep 22108315 = 33162473) B33162473
theorem B29477753 : Blo 2299435 29477753 := bstep (se 2 (by rfl) ⟨11054157, by rfl⟩ : syracuseStep 29477753 = 22108315) B22108315
theorem B19651835 : Blo 2299435 19651835 := bstep (se 1 (by rfl) ⟨14738876, by rfl⟩ : syracuseStep 19651835 = 29477753) B29477753
theorem B13101223 : Blo 2299435 13101223 := bstep (se 1 (by rfl) ⟨9825917, by rfl⟩ : syracuseStep 13101223 = 19651835) B19651835
theorem B17468297 : Blo 2299435 17468297 := bstep (se 2 (by rfl) ⟨6550611, by rfl⟩ : syracuseStep 17468297 = 13101223) B13101223
theorem B11645531 : Blo 2299435 11645531 := bstep (se 1 (by rfl) ⟨8734148, by rfl⟩ : syracuseStep 11645531 = 17468297) B17468297
theorem B7763687 : Blo 2299435 7763687 := bstep (se 1 (by rfl) ⟨5822765, by rfl⟩ : syracuseStep 7763687 = 11645531) B11645531
theorem B5175791 : Blo 2299435 5175791 := bstep (se 1 (by rfl) ⟨3881843, by rfl⟩ : syracuseStep 5175791 = 7763687) B7763687
theorem B3450527 : Blo 2299435 3450527 := bstep (se 1 (by rfl) ⟨2587895, by rfl⟩ : syracuseStep 3450527 = 5175791) B5175791
theorem B2300351 : Blo 2299435 2300351 := bstep (se 1 (by rfl) ⟨1725263, by rfl⟩ : syracuseStep 2300351 = 3450527) B3450527
theorem B3450533 : Blo 2299435 3450533 := bbase (se 4 (by rfl) ⟨323487, by rfl⟩ : syracuseStep 3450533 = 646975) (by norm_num)
theorem B2300355 : Blo 2299435 2300355 := bstep (se 1 (by rfl) ⟨1725266, by rfl⟩ : syracuseStep 2300355 = 3450533) B3450533
theorem B2911393 : Blo 2299435 2911393 := bbase (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) (by norm_num)
theorem B3881857 : Blo 2299435 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B5175809 : Blo 2299435 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B3450539 : Blo 2299435 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B2300359 : Blo 2299435 2300359 := bstep (se 1 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 2300359 = 3450539) B3450539
theorem B2587909 : Blo 2299435 2587909 := bbase (se 4 (by rfl) ⟨242616, by rfl⟩ : syracuseStep 2587909 = 485233) (by norm_num)
theorem B3450545 : Blo 2299435 3450545 := bstep (se 2 (by rfl) ⟨1293954, by rfl⟩ : syracuseStep 3450545 = 2587909) B2587909
theorem B2300363 : Blo 2299435 2300363 := bstep (se 1 (by rfl) ⟨1725272, by rfl⟩ : syracuseStep 2300363 = 3450545) B3450545
theorem B2456497 : Blo 2299435 2456497 := bbase (se 2 (by rfl) ⟨921186, by rfl⟩ : syracuseStep 2456497 = 1842373) (by norm_num)
theorem B3275329 : Blo 2299435 3275329 := bstep (se 2 (by rfl) ⟨1228248, by rfl⟩ : syracuseStep 3275329 = 2456497) B2456497
theorem B4367105 : Blo 2299435 4367105 := bstep (se 2 (by rfl) ⟨1637664, by rfl⟩ : syracuseStep 4367105 = 3275329) B3275329
theorem B2911403 : Blo 2299435 2911403 := bstep (se 1 (by rfl) ⟨2183552, by rfl⟩ : syracuseStep 2911403 = 4367105) B4367105
theorem B7763741 : Blo 2299435 7763741 := bstep (se 3 (by rfl) ⟨1455701, by rfl⟩ : syracuseStep 7763741 = 2911403) B2911403
theorem B5175827 : Blo 2299435 5175827 := bstep (se 1 (by rfl) ⟨3881870, by rfl⟩ : syracuseStep 5175827 = 7763741) B7763741
theorem B3450551 : Blo 2299435 3450551 := bstep (se 1 (by rfl) ⟨2587913, by rfl⟩ : syracuseStep 3450551 = 5175827) B5175827
theorem B2300367 : Blo 2299435 2300367 := bstep (se 1 (by rfl) ⟨1725275, by rfl⟩ : syracuseStep 2300367 = 3450551) B3450551
theorem B3450557 : Blo 2299435 3450557 := bbase (se 3 (by rfl) ⟨646979, by rfl⟩ : syracuseStep 3450557 = 1293959) (by norm_num)
theorem B2300371 : Blo 2299435 2300371 := bstep (se 1 (by rfl) ⟨1725278, by rfl⟩ : syracuseStep 2300371 = 3450557) B3450557
theorem B5175845 : Blo 2299435 5175845 := bbase (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) (by norm_num)
theorem B3450563 : Blo 2299435 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B2300375 : Blo 2299435 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B5822837 : Blo 2299435 5822837 := bbase (se 5 (by rfl) ⟨272945, by rfl⟩ : syracuseStep 5822837 = 545891) (by norm_num)
theorem B3881891 : Blo 2299435 3881891 := bstep (se 1 (by rfl) ⟨2911418, by rfl⟩ : syracuseStep 3881891 = 5822837) B5822837
theorem B2587927 : Blo 2299435 2587927 := bstep (se 1 (by rfl) ⟨1940945, by rfl⟩ : syracuseStep 2587927 = 3881891) B3881891
theorem B3450569 : Blo 2299435 3450569 := bstep (se 2 (by rfl) ⟨1293963, by rfl⟩ : syracuseStep 3450569 = 2587927) B2587927
theorem B2300379 : Blo 2299435 2300379 := bstep (se 1 (by rfl) ⟨1725284, by rfl⟩ : syracuseStep 2300379 = 3450569) B3450569
theorem B9327077 : Blo 2299435 9327077 := bbase (se 4 (by rfl) ⟨874413, by rfl⟩ : syracuseStep 9327077 = 1748827) (by norm_num)
theorem B6218051 : Blo 2299435 6218051 := bstep (se 1 (by rfl) ⟨4663538, by rfl⟩ : syracuseStep 6218051 = 9327077) B9327077
theorem B16581469 : Blo 2299435 16581469 := bstep (se 3 (by rfl) ⟨3109025, by rfl⟩ : syracuseStep 16581469 = 6218051) B6218051
theorem B22108625 : Blo 2299435 22108625 := bstep (se 2 (by rfl) ⟨8290734, by rfl⟩ : syracuseStep 22108625 = 16581469) B16581469
theorem B14739083 : Blo 2299435 14739083 := bstep (se 1 (by rfl) ⟨11054312, by rfl⟩ : syracuseStep 14739083 = 22108625) B22108625
theorem B9826055 : Blo 2299435 9826055 := bstep (se 1 (by rfl) ⟨7369541, by rfl⟩ : syracuseStep 9826055 = 14739083) B14739083
theorem B6550703 : Blo 2299435 6550703 := bstep (se 1 (by rfl) ⟨4913027, by rfl⟩ : syracuseStep 6550703 = 9826055) B9826055
theorem B4367135 : Blo 2299435 4367135 := bstep (se 1 (by rfl) ⟨3275351, by rfl⟩ : syracuseStep 4367135 = 6550703) B6550703
theorem B11645693 : Blo 2299435 11645693 := bstep (se 3 (by rfl) ⟨2183567, by rfl⟩ : syracuseStep 11645693 = 4367135) B4367135
theorem B7763795 : Blo 2299435 7763795 := bstep (se 1 (by rfl) ⟨5822846, by rfl⟩ : syracuseStep 7763795 = 11645693) B11645693
theorem B5175863 : Blo 2299435 5175863 := bstep (se 1 (by rfl) ⟨3881897, by rfl⟩ : syracuseStep 5175863 = 7763795) B7763795
theorem B3450575 : Blo 2299435 3450575 := bstep (se 1 (by rfl) ⟨2587931, by rfl⟩ : syracuseStep 3450575 = 5175863) B5175863
theorem B2300383 : Blo 2299435 2300383 := bstep (se 1 (by rfl) ⟨1725287, by rfl⟩ : syracuseStep 2300383 = 3450575) B3450575
theorem B3450581 : Blo 2299435 3450581 := bbase (se 7 (by rfl) ⟨40436, by rfl⟩ : syracuseStep 3450581 = 80873) (by norm_num)
theorem B2300387 : Blo 2299435 2300387 := bstep (se 1 (by rfl) ⟨1725290, by rfl⟩ : syracuseStep 2300387 = 3450581) B3450581
theorem B4913045 : Blo 2299435 4913045 := bbase (se 6 (by rfl) ⟨115149, by rfl⟩ : syracuseStep 4913045 = 230299) (by norm_num)
theorem B3275363 : Blo 2299435 3275363 := bstep (se 1 (by rfl) ⟨2456522, by rfl⟩ : syracuseStep 3275363 = 4913045) B4913045
theorem B8734301 : Blo 2299435 8734301 := bstep (se 3 (by rfl) ⟨1637681, by rfl⟩ : syracuseStep 8734301 = 3275363) B3275363
theorem B5822867 : Blo 2299435 5822867 := bstep (se 1 (by rfl) ⟨4367150, by rfl⟩ : syracuseStep 5822867 = 8734301) B8734301
theorem B3881911 : Blo 2299435 3881911 := bstep (se 1 (by rfl) ⟨2911433, by rfl⟩ : syracuseStep 3881911 = 5822867) B5822867
theorem B5175881 : Blo 2299435 5175881 := bstep (se 2 (by rfl) ⟨1940955, by rfl⟩ : syracuseStep 5175881 = 3881911) B3881911
theorem B3450587 : Blo 2299435 3450587 := bstep (se 1 (by rfl) ⟨2587940, by rfl⟩ : syracuseStep 3450587 = 5175881) B5175881
theorem B2300391 : Blo 2299435 2300391 := bstep (se 1 (by rfl) ⟨1725293, by rfl⟩ : syracuseStep 2300391 = 3450587) B3450587
theorem B2587945 : Blo 2299435 2587945 := bbase (se 2 (by rfl) ⟨970479, by rfl⟩ : syracuseStep 2587945 = 1940959) (by norm_num)
theorem B3450593 : Blo 2299435 3450593 := bstep (se 2 (by rfl) ⟨1293972, by rfl⟩ : syracuseStep 3450593 = 2587945) B2587945
theorem B2300395 : Blo 2299435 2300395 := bstep (se 1 (by rfl) ⟨1725296, by rfl⟩ : syracuseStep 2300395 = 3450593) B3450593
theorem B11054389 : Blo 2299435 11054389 := bbase (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) (by norm_num)
theorem B14739185 : Blo 2299435 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B9826123 : Blo 2299435 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B13101497 : Blo 2299435 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B8734331 : Blo 2299435 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B5822887 : Blo 2299435 5822887 := bstep (se 1 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 5822887 = 8734331) B8734331
theorem B7763849 : Blo 2299435 7763849 := bstep (se 2 (by rfl) ⟨2911443, by rfl⟩ : syracuseStep 7763849 = 5822887) B5822887
theorem B5175899 : Blo 2299435 5175899 := bstep (se 1 (by rfl) ⟨3881924, by rfl⟩ : syracuseStep 5175899 = 7763849) B7763849
theorem B3450599 : Blo 2299435 3450599 := bstep (se 1 (by rfl) ⟨2587949, by rfl⟩ : syracuseStep 3450599 = 5175899) B5175899
theorem B2300399 : Blo 2299435 2300399 := bstep (se 1 (by rfl) ⟨1725299, by rfl⟩ : syracuseStep 2300399 = 3450599) B3450599
theorem B3450605 : Blo 2299435 3450605 := bbase (se 3 (by rfl) ⟨646988, by rfl⟩ : syracuseStep 3450605 = 1293977) (by norm_num)
theorem B2300403 : Blo 2299435 2300403 := bstep (se 1 (by rfl) ⟨1725302, by rfl⟩ : syracuseStep 2300403 = 3450605) B3450605
theorem B5175917 : Blo 2299435 5175917 := bbase (se 3 (by rfl) ⟨970484, by rfl⟩ : syracuseStep 5175917 = 1940969) (by norm_num)
theorem B3450611 : Blo 2299435 3450611 := bstep (se 1 (by rfl) ⟨2587958, by rfl⟩ : syracuseStep 3450611 = 5175917) B5175917
theorem B2300407 : Blo 2299435 2300407 := bstep (se 1 (by rfl) ⟨1725305, by rfl⟩ : syracuseStep 2300407 = 3450611) B3450611
theorem B4367189 : Blo 2299435 4367189 := bbase (se 9 (by rfl) ⟨12794, by rfl⟩ : syracuseStep 4367189 = 25589) (by norm_num)
theorem B2911459 : Blo 2299435 2911459 := bstep (se 1 (by rfl) ⟨2183594, by rfl⟩ : syracuseStep 2911459 = 4367189) B4367189
theorem B3881945 : Blo 2299435 3881945 := bstep (se 2 (by rfl) ⟨1455729, by rfl⟩ : syracuseStep 3881945 = 2911459) B2911459
theorem B2587963 : Blo 2299435 2587963 := bstep (se 1 (by rfl) ⟨1940972, by rfl⟩ : syracuseStep 2587963 = 3881945) B3881945
theorem B3450617 : Blo 2299435 3450617 := bstep (se 2 (by rfl) ⟨1293981, by rfl⟩ : syracuseStep 3450617 = 2587963) B2587963
theorem B2300411 : Blo 2299435 2300411 := bstep (se 1 (by rfl) ⟨1725308, by rfl⟩ : syracuseStep 2300411 = 3450617) B3450617
theorem B9327205 : Blo 2299435 9327205 := bbase (se 4 (by rfl) ⟨874425, by rfl⟩ : syracuseStep 9327205 = 1748851) (by norm_num)
theorem B12436273 : Blo 2299435 12436273 := bstep (se 2 (by rfl) ⟨4663602, by rfl⟩ : syracuseStep 12436273 = 9327205) B9327205
theorem B66326789 : Blo 2299435 66326789 := bstep (se 4 (by rfl) ⟨6218136, by rfl⟩ : syracuseStep 66326789 = 12436273) B12436273
theorem B44217859 : Blo 2299435 44217859 := bstep (se 1 (by rfl) ⟨33163394, by rfl⟩ : syracuseStep 44217859 = 66326789) B66326789
theorem B58957145 : Blo 2299435 58957145 := bstep (se 2 (by rfl) ⟨22108929, by rfl⟩ : syracuseStep 58957145 = 44217859) B44217859
theorem B39304763 : Blo 2299435 39304763 := bstep (se 1 (by rfl) ⟨29478572, by rfl⟩ : syracuseStep 39304763 = 58957145) B58957145
theorem B26203175 : Blo 2299435 26203175 := bstep (se 1 (by rfl) ⟨19652381, by rfl⟩ : syracuseStep 26203175 = 39304763) B39304763
theorem B17468783 : Blo 2299435 17468783 := bstep (se 1 (by rfl) ⟨13101587, by rfl⟩ : syracuseStep 17468783 = 26203175) B26203175
theorem B11645855 : Blo 2299435 11645855 := bstep (se 1 (by rfl) ⟨8734391, by rfl⟩ : syracuseStep 11645855 = 17468783) B17468783
theorem B7763903 : Blo 2299435 7763903 := bstep (se 1 (by rfl) ⟨5822927, by rfl⟩ : syracuseStep 7763903 = 11645855) B11645855
theorem B5175935 : Blo 2299435 5175935 := bstep (se 1 (by rfl) ⟨3881951, by rfl⟩ : syracuseStep 5175935 = 7763903) B7763903
theorem B3450623 : Blo 2299435 3450623 := bstep (se 1 (by rfl) ⟨2587967, by rfl⟩ : syracuseStep 3450623 = 5175935) B5175935
theorem B2300415 : Blo 2299435 2300415 := bstep (se 1 (by rfl) ⟨1725311, by rfl⟩ : syracuseStep 2300415 = 3450623) B3450623
theorem B3450629 : Blo 2299435 3450629 := bbase (se 4 (by rfl) ⟨323496, by rfl⟩ : syracuseStep 3450629 = 646993) (by norm_num)
theorem B2300419 : Blo 2299435 2300419 := bstep (se 1 (by rfl) ⟨1725314, by rfl⟩ : syracuseStep 2300419 = 3450629) B3450629
theorem B3881965 : Blo 2299435 3881965 := bbase (se 3 (by rfl) ⟨727868, by rfl⟩ : syracuseStep 3881965 = 1455737) (by norm_num)
theorem B5175953 : Blo 2299435 5175953 := bstep (se 2 (by rfl) ⟨1940982, by rfl⟩ : syracuseStep 5175953 = 3881965) B3881965
theorem B3450635 : Blo 2299435 3450635 := bstep (se 1 (by rfl) ⟨2587976, by rfl⟩ : syracuseStep 3450635 = 5175953) B5175953
theorem B2300423 : Blo 2299435 2300423 := bstep (se 1 (by rfl) ⟨1725317, by rfl⟩ : syracuseStep 2300423 = 3450635) B3450635
theorem B2587981 : Blo 2299435 2587981 := bbase (se 3 (by rfl) ⟨485246, by rfl⟩ : syracuseStep 2587981 = 970493) (by norm_num)
theorem B3450641 : Blo 2299435 3450641 := bstep (se 2 (by rfl) ⟨1293990, by rfl⟩ : syracuseStep 3450641 = 2587981) B2587981
theorem B2300427 : Blo 2299435 2300427 := bstep (se 1 (by rfl) ⟨1725320, by rfl⟩ : syracuseStep 2300427 = 3450641) B3450641
theorem B7763957 : Blo 2299435 7763957 := bbase (se 5 (by rfl) ⟨363935, by rfl⟩ : syracuseStep 7763957 = 727871) (by norm_num)
theorem B5175971 : Blo 2299435 5175971 := bstep (se 1 (by rfl) ⟨3881978, by rfl⟩ : syracuseStep 5175971 = 7763957) B7763957
theorem B3450647 : Blo 2299435 3450647 := bstep (se 1 (by rfl) ⟨2587985, by rfl⟩ : syracuseStep 3450647 = 5175971) B5175971
theorem B2300431 : Blo 2299435 2300431 := bstep (se 1 (by rfl) ⟨1725323, by rfl⟩ : syracuseStep 2300431 = 3450647) B3450647
theorem B3450653 : Blo 2299435 3450653 := bbase (se 3 (by rfl) ⟨646997, by rfl⟩ : syracuseStep 3450653 = 1293995) (by norm_num)
theorem B2300435 : Blo 2299435 2300435 := bstep (se 1 (by rfl) ⟨1725326, by rfl⟩ : syracuseStep 2300435 = 3450653) B3450653
theorem B5175989 : Blo 2299435 5175989 := bbase (se 5 (by rfl) ⟨242624, by rfl⟩ : syracuseStep 5175989 = 485249) (by norm_num)
theorem B3450659 : Blo 2299435 3450659 := bstep (se 1 (by rfl) ⟨2587994, by rfl⟩ : syracuseStep 3450659 = 5175989) B5175989
theorem B2300439 : Blo 2299435 2300439 := bstep (se 1 (by rfl) ⟨1725329, by rfl⟩ : syracuseStep 2300439 = 3450659) B3450659
theorem B13101749 : Blo 2299435 13101749 := bbase (se 5 (by rfl) ⟨614144, by rfl⟩ : syracuseStep 13101749 = 1228289) (by norm_num)
theorem B8734499 : Blo 2299435 8734499 := bstep (se 1 (by rfl) ⟨6550874, by rfl⟩ : syracuseStep 8734499 = 13101749) B13101749
theorem B5822999 : Blo 2299435 5822999 := bstep (se 1 (by rfl) ⟨4367249, by rfl⟩ : syracuseStep 5822999 = 8734499) B8734499
theorem B3881999 : Blo 2299435 3881999 := bstep (se 1 (by rfl) ⟨2911499, by rfl⟩ : syracuseStep 3881999 = 5822999) B5822999
theorem B2587999 : Blo 2299435 2587999 := bstep (se 1 (by rfl) ⟨1940999, by rfl⟩ : syracuseStep 2587999 = 3881999) B3881999
theorem B3450665 : Blo 2299435 3450665 := bstep (se 2 (by rfl) ⟨1293999, by rfl⟩ : syracuseStep 3450665 = 2587999) B2587999
theorem B2300443 : Blo 2299435 2300443 := bstep (se 1 (by rfl) ⟨1725332, by rfl⟩ : syracuseStep 2300443 = 3450665) B3450665
theorem B6550885 : Blo 2299435 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B8734513 : Blo 2299435 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B11646017 : Blo 2299435 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B7764011 : Blo 2299435 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B5176007 : Blo 2299435 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B3450671 : Blo 2299435 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B2300447 : Blo 2299435 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B3450677 : Blo 2299435 3450677 := bbase (se 5 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 3450677 = 323501) (by norm_num)
theorem B2300451 : Blo 2299435 2300451 := bstep (se 1 (by rfl) ⟨1725338, by rfl⟩ : syracuseStep 2300451 = 3450677) B3450677
theorem B5823029 : Blo 2299435 5823029 := bbase (se 5 (by rfl) ⟨272954, by rfl⟩ : syracuseStep 5823029 = 545909) (by norm_num)
theorem B3882019 : Blo 2299435 3882019 := bstep (se 1 (by rfl) ⟨2911514, by rfl⟩ : syracuseStep 3882019 = 5823029) B5823029
theorem B5176025 : Blo 2299435 5176025 := bstep (se 2 (by rfl) ⟨1941009, by rfl⟩ : syracuseStep 5176025 = 3882019) B3882019
theorem B3450683 : Blo 2299435 3450683 := bstep (se 1 (by rfl) ⟨2588012, by rfl⟩ : syracuseStep 3450683 = 5176025) B5176025
theorem B2300455 : Blo 2299435 2300455 := bstep (se 1 (by rfl) ⟨1725341, by rfl⟩ : syracuseStep 2300455 = 3450683) B3450683
theorem B2588017 : Blo 2299435 2588017 := bbase (se 2 (by rfl) ⟨970506, by rfl⟩ : syracuseStep 2588017 = 1941013) (by norm_num)
theorem B3450689 : Blo 2299435 3450689 := bstep (se 2 (by rfl) ⟨1294008, by rfl⟩ : syracuseStep 3450689 = 2588017) B2588017
theorem B2300459 : Blo 2299435 2300459 := bstep (se 1 (by rfl) ⟨1725344, by rfl⟩ : syracuseStep 2300459 = 3450689) B3450689
theorem B5527349 : Blo 2299435 5527349 := bbase (se 5 (by rfl) ⟨259094, by rfl⟩ : syracuseStep 5527349 = 518189) (by norm_num)
theorem B3684899 : Blo 2299435 3684899 := bstep (se 1 (by rfl) ⟨2763674, by rfl⟩ : syracuseStep 3684899 = 5527349) B5527349
theorem B9826397 : Blo 2299435 9826397 := bstep (se 3 (by rfl) ⟨1842449, by rfl⟩ : syracuseStep 9826397 = 3684899) B3684899
theorem B6550931 : Blo 2299435 6550931 := bstep (se 1 (by rfl) ⟨4913198, by rfl⟩ : syracuseStep 6550931 = 9826397) B9826397
theorem B4367287 : Blo 2299435 4367287 := bstep (se 1 (by rfl) ⟨3275465, by rfl⟩ : syracuseStep 4367287 = 6550931) B6550931
theorem B5823049 : Blo 2299435 5823049 := bstep (se 2 (by rfl) ⟨2183643, by rfl⟩ : syracuseStep 5823049 = 4367287) B4367287
theorem B7764065 : Blo 2299435 7764065 := bstep (se 2 (by rfl) ⟨2911524, by rfl⟩ : syracuseStep 7764065 = 5823049) B5823049
theorem B5176043 : Blo 2299435 5176043 := bstep (se 1 (by rfl) ⟨3882032, by rfl⟩ : syracuseStep 5176043 = 7764065) B7764065
theorem B3450695 : Blo 2299435 3450695 := bstep (se 1 (by rfl) ⟨2588021, by rfl⟩ : syracuseStep 3450695 = 5176043) B5176043
theorem B2300463 : Blo 2299435 2300463 := bstep (se 1 (by rfl) ⟨1725347, by rfl⟩ : syracuseStep 2300463 = 3450695) B3450695
theorem B3450701 : Blo 2299435 3450701 := bbase (se 3 (by rfl) ⟨647006, by rfl⟩ : syracuseStep 3450701 = 1294013) (by norm_num)
theorem B2300467 : Blo 2299435 2300467 := bstep (se 1 (by rfl) ⟨1725350, by rfl⟩ : syracuseStep 2300467 = 3450701) B3450701
theorem B5176061 : Blo 2299435 5176061 := bbase (se 3 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 5176061 = 1941023) (by norm_num)
theorem B3450707 : Blo 2299435 3450707 := bstep (se 1 (by rfl) ⟨2588030, by rfl⟩ : syracuseStep 3450707 = 5176061) B5176061
theorem B2300471 : Blo 2299435 2300471 := bstep (se 1 (by rfl) ⟨1725353, by rfl⟩ : syracuseStep 2300471 = 3450707) B3450707
theorem B3882053 : Blo 2299435 3882053 := bbase (se 4 (by rfl) ⟨363942, by rfl⟩ : syracuseStep 3882053 = 727885) (by norm_num)
theorem B2588035 : Blo 2299435 2588035 := bstep (se 1 (by rfl) ⟨1941026, by rfl⟩ : syracuseStep 2588035 = 3882053) B3882053
theorem B3450713 : Blo 2299435 3450713 := bstep (se 2 (by rfl) ⟨1294017, by rfl⟩ : syracuseStep 3450713 = 2588035) B2588035
theorem B2300475 : Blo 2299435 2300475 := bstep (se 1 (by rfl) ⟨1725356, by rfl⟩ : syracuseStep 2300475 = 3450713) B3450713
theorem B17469269 : Blo 2299435 17469269 := bbase (se 9 (by rfl) ⟨51179, by rfl⟩ : syracuseStep 17469269 = 102359) (by norm_num)
theorem B11646179 : Blo 2299435 11646179 := bstep (se 1 (by rfl) ⟨8734634, by rfl⟩ : syracuseStep 11646179 = 17469269) B17469269
theorem B7764119 : Blo 2299435 7764119 := bstep (se 1 (by rfl) ⟨5823089, by rfl⟩ : syracuseStep 7764119 = 11646179) B11646179
theorem B5176079 : Blo 2299435 5176079 := bstep (se 1 (by rfl) ⟨3882059, by rfl⟩ : syracuseStep 5176079 = 7764119) B7764119
theorem B3450719 : Blo 2299435 3450719 := bstep (se 1 (by rfl) ⟨2588039, by rfl⟩ : syracuseStep 3450719 = 5176079) B5176079
theorem B2300479 : Blo 2299435 2300479 := bstep (se 1 (by rfl) ⟨1725359, by rfl⟩ : syracuseStep 2300479 = 3450719) B3450719
theorem B3450725 : Blo 2299435 3450725 := bbase (se 4 (by rfl) ⟨323505, by rfl⟩ : syracuseStep 3450725 = 647011) (by norm_num)
theorem B2300483 : Blo 2299435 2300483 := bstep (se 1 (by rfl) ⟨1725362, by rfl⟩ : syracuseStep 2300483 = 3450725) B3450725
theorem B4367333 : Blo 2299435 4367333 := bbase (se 4 (by rfl) ⟨409437, by rfl⟩ : syracuseStep 4367333 = 818875) (by norm_num)
theorem B2911555 : Blo 2299435 2911555 := bstep (se 1 (by rfl) ⟨2183666, by rfl⟩ : syracuseStep 2911555 = 4367333) B4367333
theorem B3882073 : Blo 2299435 3882073 := bstep (se 2 (by rfl) ⟨1455777, by rfl⟩ : syracuseStep 3882073 = 2911555) B2911555
theorem B5176097 : Blo 2299435 5176097 := bstep (se 2 (by rfl) ⟨1941036, by rfl⟩ : syracuseStep 5176097 = 3882073) B3882073
theorem B3450731 : Blo 2299435 3450731 := bstep (se 1 (by rfl) ⟨2588048, by rfl⟩ : syracuseStep 3450731 = 5176097) B5176097
theorem B2300487 : Blo 2299435 2300487 := bstep (se 1 (by rfl) ⟨1725365, by rfl⟩ : syracuseStep 2300487 = 3450731) B3450731
theorem B2588053 : Blo 2299435 2588053 := bbase (se 6 (by rfl) ⟨60657, by rfl⟩ : syracuseStep 2588053 = 121315) (by norm_num)
theorem B3450737 : Blo 2299435 3450737 := bstep (se 2 (by rfl) ⟨1294026, by rfl⟩ : syracuseStep 3450737 = 2588053) B2588053
theorem B2300491 : Blo 2299435 2300491 := bstep (se 1 (by rfl) ⟨1725368, by rfl⟩ : syracuseStep 2300491 = 3450737) B3450737
theorem B2911565 : Blo 2299435 2911565 := bbase (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) (by norm_num)
theorem B7764173 : Blo 2299435 7764173 := bstep (se 3 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 7764173 = 2911565) B2911565
theorem B5176115 : Blo 2299435 5176115 := bstep (se 1 (by rfl) ⟨3882086, by rfl⟩ : syracuseStep 5176115 = 7764173) B7764173
theorem B3450743 : Blo 2299435 3450743 := bstep (se 1 (by rfl) ⟨2588057, by rfl⟩ : syracuseStep 3450743 = 5176115) B5176115
theorem B2300495 : Blo 2299435 2300495 := bstep (se 1 (by rfl) ⟨1725371, by rfl⟩ : syracuseStep 2300495 = 3450743) B3450743
theorem B3450749 : Blo 2299435 3450749 := bbase (se 3 (by rfl) ⟨647015, by rfl⟩ : syracuseStep 3450749 = 1294031) (by norm_num)
theorem B2300499 : Blo 2299435 2300499 := bstep (se 1 (by rfl) ⟨1725374, by rfl⟩ : syracuseStep 2300499 = 3450749) B3450749
theorem B5176133 : Blo 2299435 5176133 := bbase (se 4 (by rfl) ⟨485262, by rfl⟩ : syracuseStep 5176133 = 970525) (by norm_num)
theorem B3450755 : Blo 2299435 3450755 := bstep (se 1 (by rfl) ⟨2588066, by rfl⟩ : syracuseStep 3450755 = 5176133) B5176133
theorem B2300503 : Blo 2299435 2300503 := bstep (se 1 (by rfl) ⟨1725377, by rfl⟩ : syracuseStep 2300503 = 3450755) B3450755
theorem B4913293 : Blo 2299435 4913293 := bbase (se 3 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 4913293 = 1842485) (by norm_num)
theorem B6551057 : Blo 2299435 6551057 := bstep (se 2 (by rfl) ⟨2456646, by rfl⟩ : syracuseStep 6551057 = 4913293) B4913293
theorem B4367371 : Blo 2299435 4367371 := bstep (se 1 (by rfl) ⟨3275528, by rfl⟩ : syracuseStep 4367371 = 6551057) B6551057
theorem B5823161 : Blo 2299435 5823161 := bstep (se 2 (by rfl) ⟨2183685, by rfl⟩ : syracuseStep 5823161 = 4367371) B4367371
theorem B3882107 : Blo 2299435 3882107 := bstep (se 1 (by rfl) ⟨2911580, by rfl⟩ : syracuseStep 3882107 = 5823161) B5823161
theorem B2588071 : Blo 2299435 2588071 := bstep (se 1 (by rfl) ⟨1941053, by rfl⟩ : syracuseStep 2588071 = 3882107) B3882107
theorem B3450761 : Blo 2299435 3450761 := bstep (se 2 (by rfl) ⟨1294035, by rfl⟩ : syracuseStep 3450761 = 2588071) B2588071
theorem B2300507 : Blo 2299435 2300507 := bstep (se 1 (by rfl) ⟨1725380, by rfl⟩ : syracuseStep 2300507 = 3450761) B3450761
theorem B11646341 : Blo 2299435 11646341 := bbase (se 4 (by rfl) ⟨1091844, by rfl⟩ : syracuseStep 11646341 = 2183689) (by norm_num)
theorem B7764227 : Blo 2299435 7764227 := bstep (se 1 (by rfl) ⟨5823170, by rfl⟩ : syracuseStep 7764227 = 11646341) B11646341
theorem B5176151 : Blo 2299435 5176151 := bstep (se 1 (by rfl) ⟨3882113, by rfl⟩ : syracuseStep 5176151 = 7764227) B7764227
theorem B3450767 : Blo 2299435 3450767 := bstep (se 1 (by rfl) ⟨2588075, by rfl⟩ : syracuseStep 3450767 = 5176151) B5176151
theorem B2300511 : Blo 2299435 2300511 := bstep (se 1 (by rfl) ⟨1725383, by rfl⟩ : syracuseStep 2300511 = 3450767) B3450767
theorem B3450773 : Blo 2299435 3450773 := bbase (se 6 (by rfl) ⟨80877, by rfl⟩ : syracuseStep 3450773 = 161755) (by norm_num)
theorem B2300515 : Blo 2299435 2300515 := bstep (se 1 (by rfl) ⟨1725386, by rfl⟩ : syracuseStep 2300515 = 3450773) B3450773
theorem B3684989 : Blo 2299435 3684989 := bbase (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) (by norm_num)
theorem B2456659 : Blo 2299435 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B13102181 : Blo 2299435 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B8734787 : Blo 2299435 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B5823191 : Blo 2299435 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B3882127 : Blo 2299435 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B5176169 : Blo 2299435 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B3450779 : Blo 2299435 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B2300519 : Blo 2299435 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B2588089 : Blo 2299435 2588089 := bbase (se 2 (by rfl) ⟨970533, by rfl⟩ : syracuseStep 2588089 = 1941067) (by norm_num)
theorem B3450785 : Blo 2299435 3450785 := bstep (se 2 (by rfl) ⟨1294044, by rfl⟩ : syracuseStep 3450785 = 2588089) B2588089
theorem B2300523 : Blo 2299435 2300523 := bstep (se 1 (by rfl) ⟨1725392, by rfl⟩ : syracuseStep 2300523 = 3450785) B3450785
theorem B10493621 : Blo 2299435 10493621 := bbase (se 5 (by rfl) ⟨491888, by rfl⟩ : syracuseStep 10493621 = 983777) (by norm_num)
theorem B6995747 : Blo 2299435 6995747 := bstep (se 1 (by rfl) ⟨5246810, by rfl⟩ : syracuseStep 6995747 = 10493621) B10493621
theorem B4663831 : Blo 2299435 4663831 := bstep (se 1 (by rfl) ⟨3497873, by rfl⟩ : syracuseStep 4663831 = 6995747) B6995747
theorem B6218441 : Blo 2299435 6218441 := bstep (se 2 (by rfl) ⟨2331915, by rfl⟩ : syracuseStep 6218441 = 4663831) B4663831
theorem B4145627 : Blo 2299435 4145627 := bstep (se 1 (by rfl) ⟨3109220, by rfl⟩ : syracuseStep 4145627 = 6218441) B6218441
theorem B11055005 : Blo 2299435 11055005 := bstep (se 3 (by rfl) ⟨2072813, by rfl⟩ : syracuseStep 11055005 = 4145627) B4145627
theorem B7370003 : Blo 2299435 7370003 := bstep (se 1 (by rfl) ⟨5527502, by rfl⟩ : syracuseStep 7370003 = 11055005) B11055005
theorem B4913335 : Blo 2299435 4913335 := bstep (se 1 (by rfl) ⟨3685001, by rfl⟩ : syracuseStep 4913335 = 7370003) B7370003
theorem B6551113 : Blo 2299435 6551113 := bstep (se 2 (by rfl) ⟨2456667, by rfl⟩ : syracuseStep 6551113 = 4913335) B4913335
theorem B8734817 : Blo 2299435 8734817 := bstep (se 2 (by rfl) ⟨3275556, by rfl⟩ : syracuseStep 8734817 = 6551113) B6551113
theorem B5823211 : Blo 2299435 5823211 := bstep (se 1 (by rfl) ⟨4367408, by rfl⟩ : syracuseStep 5823211 = 8734817) B8734817
theorem B7764281 : Blo 2299435 7764281 := bstep (se 2 (by rfl) ⟨2911605, by rfl⟩ : syracuseStep 7764281 = 5823211) B5823211
theorem B5176187 : Blo 2299435 5176187 := bstep (se 1 (by rfl) ⟨3882140, by rfl⟩ : syracuseStep 5176187 = 7764281) B7764281
theorem B3450791 : Blo 2299435 3450791 := bstep (se 1 (by rfl) ⟨2588093, by rfl⟩ : syracuseStep 3450791 = 5176187) B5176187
theorem B2300527 : Blo 2299435 2300527 := bstep (se 1 (by rfl) ⟨1725395, by rfl⟩ : syracuseStep 2300527 = 3450791) B3450791
theorem B3450797 : Blo 2299435 3450797 := bbase (se 3 (by rfl) ⟨647024, by rfl⟩ : syracuseStep 3450797 = 1294049) (by norm_num)
theorem B2300531 : Blo 2299435 2300531 := bstep (se 1 (by rfl) ⟨1725398, by rfl⟩ : syracuseStep 2300531 = 3450797) B3450797
theorem B5176205 : Blo 2299435 5176205 := bbase (se 3 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 5176205 = 1941077) (by norm_num)
theorem B3450803 : Blo 2299435 3450803 := bstep (se 1 (by rfl) ⟨2588102, by rfl⟩ : syracuseStep 3450803 = 5176205) B5176205
theorem B2300535 : Blo 2299435 2300535 := bstep (se 1 (by rfl) ⟨1725401, by rfl⟩ : syracuseStep 2300535 = 3450803) B3450803
theorem B2911621 : Blo 2299435 2911621 := bbase (se 4 (by rfl) ⟨272964, by rfl⟩ : syracuseStep 2911621 = 545929) (by norm_num)
theorem B3882161 : Blo 2299435 3882161 := bstep (se 2 (by rfl) ⟨1455810, by rfl⟩ : syracuseStep 3882161 = 2911621) B2911621
theorem B2588107 : Blo 2299435 2588107 := bstep (se 1 (by rfl) ⟨1941080, by rfl⟩ : syracuseStep 2588107 = 3882161) B3882161
theorem B3450809 : Blo 2299435 3450809 := bstep (se 2 (by rfl) ⟨1294053, by rfl⟩ : syracuseStep 3450809 = 2588107) B2588107
theorem B2300539 : Blo 2299435 2300539 := bstep (se 1 (by rfl) ⟨1725404, by rfl⟩ : syracuseStep 2300539 = 3450809) B3450809
theorem B29480213 : Blo 2299435 29480213 := bbase (se 6 (by rfl) ⟨690942, by rfl⟩ : syracuseStep 29480213 = 1381885) (by norm_num)
theorem B19653475 : Blo 2299435 19653475 := bstep (se 1 (by rfl) ⟨14740106, by rfl⟩ : syracuseStep 19653475 = 29480213) B29480213
theorem B26204633 : Blo 2299435 26204633 := bstep (se 2 (by rfl) ⟨9826737, by rfl⟩ : syracuseStep 26204633 = 19653475) B19653475
theorem B17469755 : Blo 2299435 17469755 := bstep (se 1 (by rfl) ⟨13102316, by rfl⟩ : syracuseStep 17469755 = 26204633) B26204633
theorem B11646503 : Blo 2299435 11646503 := bstep (se 1 (by rfl) ⟨8734877, by rfl⟩ : syracuseStep 11646503 = 17469755) B17469755
theorem B7764335 : Blo 2299435 7764335 := bstep (se 1 (by rfl) ⟨5823251, by rfl⟩ : syracuseStep 7764335 = 11646503) B11646503
theorem B5176223 : Blo 2299435 5176223 := bstep (se 1 (by rfl) ⟨3882167, by rfl⟩ : syracuseStep 5176223 = 7764335) B7764335
theorem B3450815 : Blo 2299435 3450815 := bstep (se 1 (by rfl) ⟨2588111, by rfl⟩ : syracuseStep 3450815 = 5176223) B5176223
theorem B2300543 : Blo 2299435 2300543 := bstep (se 1 (by rfl) ⟨1725407, by rfl⟩ : syracuseStep 2300543 = 3450815) B3450815
theorem B3450821 : Blo 2299435 3450821 := bbase (se 4 (by rfl) ⟨323514, by rfl⟩ : syracuseStep 3450821 = 647029) (by norm_num)
theorem B2300547 : Blo 2299435 2300547 := bstep (se 1 (by rfl) ⟨1725410, by rfl⟩ : syracuseStep 2300547 = 3450821) B3450821
theorem B3882181 : Blo 2299435 3882181 := bbase (se 4 (by rfl) ⟨363954, by rfl⟩ : syracuseStep 3882181 = 727909) (by norm_num)
theorem B5176241 : Blo 2299435 5176241 := bstep (se 2 (by rfl) ⟨1941090, by rfl⟩ : syracuseStep 5176241 = 3882181) B3882181
theorem B3450827 : Blo 2299435 3450827 := bstep (se 1 (by rfl) ⟨2588120, by rfl⟩ : syracuseStep 3450827 = 5176241) B5176241
theorem B2300551 : Blo 2299435 2300551 := bstep (se 1 (by rfl) ⟨1725413, by rfl⟩ : syracuseStep 2300551 = 3450827) B3450827
theorem B2588125 : Blo 2299435 2588125 := bbase (se 3 (by rfl) ⟨485273, by rfl⟩ : syracuseStep 2588125 = 970547) (by norm_num)
theorem B3450833 : Blo 2299435 3450833 := bstep (se 2 (by rfl) ⟨1294062, by rfl⟩ : syracuseStep 3450833 = 2588125) B2588125
theorem B2300555 : Blo 2299435 2300555 := bstep (se 1 (by rfl) ⟨1725416, by rfl⟩ : syracuseStep 2300555 = 3450833) B3450833
theorem B7764389 : Blo 2299435 7764389 := bbase (se 4 (by rfl) ⟨727911, by rfl⟩ : syracuseStep 7764389 = 1455823) (by norm_num)
theorem B5176259 : Blo 2299435 5176259 := bstep (se 1 (by rfl) ⟨3882194, by rfl⟩ : syracuseStep 5176259 = 7764389) B7764389
theorem B3450839 : Blo 2299435 3450839 := bstep (se 1 (by rfl) ⟨2588129, by rfl⟩ : syracuseStep 3450839 = 5176259) B5176259
theorem B2300559 : Blo 2299435 2300559 := bstep (se 1 (by rfl) ⟨1725419, by rfl⟩ : syracuseStep 2300559 = 3450839) B3450839
theorem B3450845 : Blo 2299435 3450845 := bbase (se 3 (by rfl) ⟨647033, by rfl⟩ : syracuseStep 3450845 = 1294067) (by norm_num)
theorem B2300563 : Blo 2299435 2300563 := bstep (se 1 (by rfl) ⟨1725422, by rfl⟩ : syracuseStep 2300563 = 3450845) B3450845
theorem B5176277 : Blo 2299435 5176277 := bbase (se 7 (by rfl) ⟨60659, by rfl⟩ : syracuseStep 5176277 = 121319) (by norm_num)
theorem B3450851 : Blo 2299435 3450851 := bstep (se 1 (by rfl) ⟨2588138, by rfl⟩ : syracuseStep 3450851 = 5176277) B5176277
theorem B2300567 : Blo 2299435 2300567 := bstep (se 1 (by rfl) ⟨1725425, by rfl⟩ : syracuseStep 2300567 = 3450851) B3450851
theorem B8291413 : Blo 2299435 8291413 := bbase (se 8 (by rfl) ⟨48582, by rfl⟩ : syracuseStep 8291413 = 97165) (by norm_num)
theorem B11055217 : Blo 2299435 11055217 := bstep (se 2 (by rfl) ⟨4145706, by rfl⟩ : syracuseStep 11055217 = 8291413) B8291413
theorem B14740289 : Blo 2299435 14740289 := bstep (se 2 (by rfl) ⟨5527608, by rfl⟩ : syracuseStep 14740289 = 11055217) B11055217
theorem B9826859 : Blo 2299435 9826859 := bstep (se 1 (by rfl) ⟨7370144, by rfl⟩ : syracuseStep 9826859 = 14740289) B14740289
theorem B6551239 : Blo 2299435 6551239 := bstep (se 1 (by rfl) ⟨4913429, by rfl⟩ : syracuseStep 6551239 = 9826859) B9826859
theorem B8734985 : Blo 2299435 8734985 := bstep (se 2 (by rfl) ⟨3275619, by rfl⟩ : syracuseStep 8734985 = 6551239) B6551239
theorem B5823323 : Blo 2299435 5823323 := bstep (se 1 (by rfl) ⟨4367492, by rfl⟩ : syracuseStep 5823323 = 8734985) B8734985
theorem B3882215 : Blo 2299435 3882215 := bstep (se 1 (by rfl) ⟨2911661, by rfl⟩ : syracuseStep 3882215 = 5823323) B5823323
theorem B2588143 : Blo 2299435 2588143 := bstep (se 1 (by rfl) ⟨1941107, by rfl⟩ : syracuseStep 2588143 = 3882215) B3882215
theorem B3450857 : Blo 2299435 3450857 := bstep (se 2 (by rfl) ⟨1294071, by rfl⟩ : syracuseStep 3450857 = 2588143) B2588143
theorem B2300571 : Blo 2299435 2300571 := bstep (se 1 (by rfl) ⟨1725428, by rfl⟩ : syracuseStep 2300571 = 3450857) B3450857
theorem B19653749 : Blo 2299435 19653749 := bbase (se 5 (by rfl) ⟨921269, by rfl⟩ : syracuseStep 19653749 = 1842539) (by norm_num)
theorem B13102499 : Blo 2299435 13102499 := bstep (se 1 (by rfl) ⟨9826874, by rfl⟩ : syracuseStep 13102499 = 19653749) B19653749
theorem B8734999 : Blo 2299435 8734999 := bstep (se 1 (by rfl) ⟨6551249, by rfl⟩ : syracuseStep 8734999 = 13102499) B13102499
theorem B11646665 : Blo 2299435 11646665 := bstep (se 2 (by rfl) ⟨4367499, by rfl⟩ : syracuseStep 11646665 = 8734999) B8734999
theorem B7764443 : Blo 2299435 7764443 := bstep (se 1 (by rfl) ⟨5823332, by rfl⟩ : syracuseStep 7764443 = 11646665) B11646665
theorem B5176295 : Blo 2299435 5176295 := bstep (se 1 (by rfl) ⟨3882221, by rfl⟩ : syracuseStep 5176295 = 7764443) B7764443
theorem B3450863 : Blo 2299435 3450863 := bstep (se 1 (by rfl) ⟨2588147, by rfl⟩ : syracuseStep 3450863 = 5176295) B5176295
theorem B2300575 : Blo 2299435 2300575 := bstep (se 1 (by rfl) ⟨1725431, by rfl⟩ : syracuseStep 2300575 = 3450863) B3450863
theorem B3450869 : Blo 2299435 3450869 := bbase (se 5 (by rfl) ⟨161759, by rfl⟩ : syracuseStep 3450869 = 323519) (by norm_num)
theorem B2300579 : Blo 2299435 2300579 := bstep (se 1 (by rfl) ⟨1725434, by rfl⟩ : syracuseStep 2300579 = 3450869) B3450869
theorem B2623469 : Blo 2299435 2623469 := bbase (se 3 (by rfl) ⟨491900, by rfl⟩ : syracuseStep 2623469 = 983801) (by norm_num)
theorem B6995917 : Blo 2299435 6995917 := bstep (se 3 (by rfl) ⟨1311734, by rfl⟩ : syracuseStep 6995917 = 2623469) B2623469
theorem B9327889 : Blo 2299435 9327889 := bstep (se 2 (by rfl) ⟨3497958, by rfl⟩ : syracuseStep 9327889 = 6995917) B6995917
theorem B12437185 : Blo 2299435 12437185 := bstep (se 2 (by rfl) ⟨4663944, by rfl⟩ : syracuseStep 12437185 = 9327889) B9327889
theorem B16582913 : Blo 2299435 16582913 := bstep (se 2 (by rfl) ⟨6218592, by rfl⟩ : syracuseStep 16582913 = 12437185) B12437185
theorem B11055275 : Blo 2299435 11055275 := bstep (se 1 (by rfl) ⟨8291456, by rfl⟩ : syracuseStep 11055275 = 16582913) B16582913
theorem B7370183 : Blo 2299435 7370183 := bstep (se 1 (by rfl) ⟨5527637, by rfl⟩ : syracuseStep 7370183 = 11055275) B11055275
theorem B4913455 : Blo 2299435 4913455 := bstep (se 1 (by rfl) ⟨3685091, by rfl⟩ : syracuseStep 4913455 = 7370183) B7370183
theorem B6551273 : Blo 2299435 6551273 := bstep (se 2 (by rfl) ⟨2456727, by rfl⟩ : syracuseStep 6551273 = 4913455) B4913455
theorem B4367515 : Blo 2299435 4367515 := bstep (se 1 (by rfl) ⟨3275636, by rfl⟩ : syracuseStep 4367515 = 6551273) B6551273
theorem B5823353 : Blo 2299435 5823353 := bstep (se 2 (by rfl) ⟨2183757, by rfl⟩ : syracuseStep 5823353 = 4367515) B4367515
theorem B3882235 : Blo 2299435 3882235 := bstep (se 1 (by rfl) ⟨2911676, by rfl⟩ : syracuseStep 3882235 = 5823353) B5823353
theorem B5176313 : Blo 2299435 5176313 := bstep (se 2 (by rfl) ⟨1941117, by rfl⟩ : syracuseStep 5176313 = 3882235) B3882235
theorem B3450875 : Blo 2299435 3450875 := bstep (se 1 (by rfl) ⟨2588156, by rfl⟩ : syracuseStep 3450875 = 5176313) B5176313
theorem B2300583 : Blo 2299435 2300583 := bstep (se 1 (by rfl) ⟨1725437, by rfl⟩ : syracuseStep 2300583 = 3450875) B3450875
theorem B2588161 : Blo 2299435 2588161 := bbase (se 2 (by rfl) ⟨970560, by rfl⟩ : syracuseStep 2588161 = 1941121) (by norm_num)
theorem B3450881 : Blo 2299435 3450881 := bstep (se 2 (by rfl) ⟨1294080, by rfl⟩ : syracuseStep 3450881 = 2588161) B2588161
theorem B2300587 : Blo 2299435 2300587 := bstep (se 1 (by rfl) ⟨1725440, by rfl⟩ : syracuseStep 2300587 = 3450881) B3450881
theorem B5823373 : Blo 2299435 5823373 := bbase (se 3 (by rfl) ⟨1091882, by rfl⟩ : syracuseStep 5823373 = 2183765) (by norm_num)
theorem B7764497 : Blo 2299435 7764497 := bstep (se 2 (by rfl) ⟨2911686, by rfl⟩ : syracuseStep 7764497 = 5823373) B5823373
theorem B5176331 : Blo 2299435 5176331 := bstep (se 1 (by rfl) ⟨3882248, by rfl⟩ : syracuseStep 5176331 = 7764497) B7764497
theorem B3450887 : Blo 2299435 3450887 := bstep (se 1 (by rfl) ⟨2588165, by rfl⟩ : syracuseStep 3450887 = 5176331) B5176331
theorem B2300591 : Blo 2299435 2300591 := bstep (se 1 (by rfl) ⟨1725443, by rfl⟩ : syracuseStep 2300591 = 3450887) B3450887
theorem B3450893 : Blo 2299435 3450893 := bbase (se 3 (by rfl) ⟨647042, by rfl⟩ : syracuseStep 3450893 = 1294085) (by norm_num)
theorem B2300595 : Blo 2299435 2300595 := bstep (se 1 (by rfl) ⟨1725446, by rfl⟩ : syracuseStep 2300595 = 3450893) B3450893
theorem B5176349 : Blo 2299435 5176349 := bbase (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) (by norm_num)
theorem B3450899 : Blo 2299435 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B2300599 : Blo 2299435 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B3882269 : Blo 2299435 3882269 := bbase (se 3 (by rfl) ⟨727925, by rfl⟩ : syracuseStep 3882269 = 1455851) (by norm_num)
theorem B2588179 : Blo 2299435 2588179 := bstep (se 1 (by rfl) ⟨1941134, by rfl⟩ : syracuseStep 2588179 = 3882269) B3882269
theorem B3450905 : Blo 2299435 3450905 := bstep (se 2 (by rfl) ⟨1294089, by rfl⟩ : syracuseStep 3450905 = 2588179) B2588179
theorem B2300603 : Blo 2299435 2300603 := bstep (se 1 (by rfl) ⟨1725452, by rfl⟩ : syracuseStep 2300603 = 3450905) B3450905
theorem B3935245 : Blo 2299435 3935245 := bbase (se 3 (by rfl) ⟨737858, by rfl⟩ : syracuseStep 3935245 = 1475717) (by norm_num)
theorem B5246993 : Blo 2299435 5246993 := bstep (se 2 (by rfl) ⟨1967622, by rfl⟩ : syracuseStep 5246993 = 3935245) B3935245
theorem B3497995 : Blo 2299435 3497995 := bstep (se 1 (by rfl) ⟨2623496, by rfl⟩ : syracuseStep 3497995 = 5246993) B5246993
theorem B4663993 : Blo 2299435 4663993 := bstep (se 2 (by rfl) ⟨1748997, by rfl⟩ : syracuseStep 4663993 = 3497995) B3497995
theorem B6218657 : Blo 2299435 6218657 := bstep (se 2 (by rfl) ⟨2331996, by rfl⟩ : syracuseStep 6218657 = 4663993) B4663993
theorem B4145771 : Blo 2299435 4145771 := bstep (se 1 (by rfl) ⟨3109328, by rfl⟩ : syracuseStep 4145771 = 6218657) B6218657
theorem B2763847 : Blo 2299435 2763847 := bstep (se 1 (by rfl) ⟨2072885, by rfl⟩ : syracuseStep 2763847 = 4145771) B4145771
theorem B14740517 : Blo 2299435 14740517 := bstep (se 4 (by rfl) ⟨1381923, by rfl⟩ : syracuseStep 14740517 = 2763847) B2763847
theorem B9827011 : Blo 2299435 9827011 := bstep (se 1 (by rfl) ⟨7370258, by rfl⟩ : syracuseStep 9827011 = 14740517) B14740517
theorem B13102681 : Blo 2299435 13102681 := bstep (se 2 (by rfl) ⟨4913505, by rfl⟩ : syracuseStep 13102681 = 9827011) B9827011
theorem B17470241 : Blo 2299435 17470241 := bstep (se 2 (by rfl) ⟨6551340, by rfl⟩ : syracuseStep 17470241 = 13102681) B13102681
theorem B11646827 : Blo 2299435 11646827 := bstep (se 1 (by rfl) ⟨8735120, by rfl⟩ : syracuseStep 11646827 = 17470241) B17470241
theorem B7764551 : Blo 2299435 7764551 := bstep (se 1 (by rfl) ⟨5823413, by rfl⟩ : syracuseStep 7764551 = 11646827) B11646827
theorem B5176367 : Blo 2299435 5176367 := bstep (se 1 (by rfl) ⟨3882275, by rfl⟩ : syracuseStep 5176367 = 7764551) B7764551
theorem B3450911 : Blo 2299435 3450911 := bstep (se 1 (by rfl) ⟨2588183, by rfl⟩ : syracuseStep 3450911 = 5176367) B5176367
theorem B2300607 : Blo 2299435 2300607 := bstep (se 1 (by rfl) ⟨1725455, by rfl⟩ : syracuseStep 2300607 = 3450911) B3450911
theorem B3450917 : Blo 2299435 3450917 := bbase (se 4 (by rfl) ⟨323523, by rfl⟩ : syracuseStep 3450917 = 647047) (by norm_num)
theorem B2300611 : Blo 2299435 2300611 := bstep (se 1 (by rfl) ⟨1725458, by rfl⟩ : syracuseStep 2300611 = 3450917) B3450917
theorem B2911717 : Blo 2299435 2911717 := bbase (se 4 (by rfl) ⟨272973, by rfl⟩ : syracuseStep 2911717 = 545947) (by norm_num)
theorem B3882289 : Blo 2299435 3882289 := bstep (se 2 (by rfl) ⟨1455858, by rfl⟩ : syracuseStep 3882289 = 2911717) B2911717
theorem B5176385 : Blo 2299435 5176385 := bstep (se 2 (by rfl) ⟨1941144, by rfl⟩ : syracuseStep 5176385 = 3882289) B3882289
theorem B3450923 : Blo 2299435 3450923 := bstep (se 1 (by rfl) ⟨2588192, by rfl⟩ : syracuseStep 3450923 = 5176385) B5176385
theorem B2300615 : Blo 2299435 2300615 := bstep (se 1 (by rfl) ⟨1725461, by rfl⟩ : syracuseStep 2300615 = 3450923) B3450923
theorem B2588197 : Blo 2299435 2588197 := bbase (se 4 (by rfl) ⟨242643, by rfl⟩ : syracuseStep 2588197 = 485287) (by norm_num)
theorem B3450929 : Blo 2299435 3450929 := bstep (se 2 (by rfl) ⟨1294098, by rfl⟩ : syracuseStep 3450929 = 2588197) B2588197
theorem B2300619 : Blo 2299435 2300619 := bstep (se 1 (by rfl) ⟨1725464, by rfl⟩ : syracuseStep 2300619 = 3450929) B3450929
theorem B5247029 : Blo 2299435 5247029 := bbase (se 5 (by rfl) ⟨245954, by rfl⟩ : syracuseStep 5247029 = 491909) (by norm_num)
theorem B13992077 : Blo 2299435 13992077 := bstep (se 3 (by rfl) ⟨2623514, by rfl⟩ : syracuseStep 13992077 = 5247029) B5247029
theorem B9328051 : Blo 2299435 9328051 := bstep (se 1 (by rfl) ⟨6996038, by rfl⟩ : syracuseStep 9328051 = 13992077) B13992077
theorem B12437401 : Blo 2299435 12437401 := bstep (se 2 (by rfl) ⟨4664025, by rfl⟩ : syracuseStep 12437401 = 9328051) B9328051
theorem B16583201 : Blo 2299435 16583201 := bstep (se 2 (by rfl) ⟨6218700, by rfl⟩ : syracuseStep 16583201 = 12437401) B12437401
theorem B11055467 : Blo 2299435 11055467 := bstep (se 1 (by rfl) ⟨8291600, by rfl⟩ : syracuseStep 11055467 = 16583201) B16583201
theorem B7370311 : Blo 2299435 7370311 := bstep (se 1 (by rfl) ⟨5527733, by rfl⟩ : syracuseStep 7370311 = 11055467) B11055467
theorem B9827081 : Blo 2299435 9827081 := bstep (se 2 (by rfl) ⟨3685155, by rfl⟩ : syracuseStep 9827081 = 7370311) B7370311
theorem B6551387 : Blo 2299435 6551387 := bstep (se 1 (by rfl) ⟨4913540, by rfl⟩ : syracuseStep 6551387 = 9827081) B9827081
theorem B4367591 : Blo 2299435 4367591 := bstep (se 1 (by rfl) ⟨3275693, by rfl⟩ : syracuseStep 4367591 = 6551387) B6551387
theorem B2911727 : Blo 2299435 2911727 := bstep (se 1 (by rfl) ⟨2183795, by rfl⟩ : syracuseStep 2911727 = 4367591) B4367591
theorem B7764605 : Blo 2299435 7764605 := bstep (se 3 (by rfl) ⟨1455863, by rfl⟩ : syracuseStep 7764605 = 2911727) B2911727
theorem B5176403 : Blo 2299435 5176403 := bstep (se 1 (by rfl) ⟨3882302, by rfl⟩ : syracuseStep 5176403 = 7764605) B7764605
theorem B3450935 : Blo 2299435 3450935 := bstep (se 1 (by rfl) ⟨2588201, by rfl⟩ : syracuseStep 3450935 = 5176403) B5176403
theorem B2300623 : Blo 2299435 2300623 := bstep (se 1 (by rfl) ⟨1725467, by rfl⟩ : syracuseStep 2300623 = 3450935) B3450935
theorem B3450941 : Blo 2299435 3450941 := bbase (se 3 (by rfl) ⟨647051, by rfl⟩ : syracuseStep 3450941 = 1294103) (by norm_num)
theorem B2300627 : Blo 2299435 2300627 := bstep (se 1 (by rfl) ⟨1725470, by rfl⟩ : syracuseStep 2300627 = 3450941) B3450941
theorem B5176421 : Blo 2299435 5176421 := bbase (se 4 (by rfl) ⟨485289, by rfl⟩ : syracuseStep 5176421 = 970579) (by norm_num)
theorem B3450947 : Blo 2299435 3450947 := bstep (se 1 (by rfl) ⟨2588210, by rfl⟩ : syracuseStep 3450947 = 5176421) B5176421
theorem B2300631 : Blo 2299435 2300631 := bstep (se 1 (by rfl) ⟨1725473, by rfl⟩ : syracuseStep 2300631 = 3450947) B3450947
theorem B5823485 : Blo 2299435 5823485 := bbase (se 3 (by rfl) ⟨1091903, by rfl⟩ : syracuseStep 5823485 = 2183807) (by norm_num)
theorem B3882323 : Blo 2299435 3882323 := bstep (se 1 (by rfl) ⟨2911742, by rfl⟩ : syracuseStep 3882323 = 5823485) B5823485
theorem B2588215 : Blo 2299435 2588215 := bstep (se 1 (by rfl) ⟨1941161, by rfl⟩ : syracuseStep 2588215 = 3882323) B3882323
theorem B3450953 : Blo 2299435 3450953 := bstep (se 2 (by rfl) ⟨1294107, by rfl⟩ : syracuseStep 3450953 = 2588215) B2588215
theorem B2300635 : Blo 2299435 2300635 := bstep (se 1 (by rfl) ⟨1725476, by rfl⟩ : syracuseStep 2300635 = 3450953) B3450953
theorem B4367621 : Blo 2299435 4367621 := bbase (se 4 (by rfl) ⟨409464, by rfl⟩ : syracuseStep 4367621 = 818929) (by norm_num)
theorem B11646989 : Blo 2299435 11646989 := bstep (se 3 (by rfl) ⟨2183810, by rfl⟩ : syracuseStep 11646989 = 4367621) B4367621
theorem B7764659 : Blo 2299435 7764659 := bstep (se 1 (by rfl) ⟨5823494, by rfl⟩ : syracuseStep 7764659 = 11646989) B11646989
theorem B5176439 : Blo 2299435 5176439 := bstep (se 1 (by rfl) ⟨3882329, by rfl⟩ : syracuseStep 5176439 = 7764659) B7764659
theorem B3450959 : Blo 2299435 3450959 := bstep (se 1 (by rfl) ⟨2588219, by rfl⟩ : syracuseStep 3450959 = 5176439) B5176439
theorem B2300639 : Blo 2299435 2300639 := bstep (se 1 (by rfl) ⟨1725479, by rfl⟩ : syracuseStep 2300639 = 3450959) B3450959
theorem B3450965 : Blo 2299435 3450965 := bbase (se 8 (by rfl) ⟨20220, by rfl⟩ : syracuseStep 3450965 = 40441) (by norm_num)
theorem B2300643 : Blo 2299435 2300643 := bstep (se 1 (by rfl) ⟨1725482, by rfl⟩ : syracuseStep 2300643 = 3450965) B3450965
theorem B11206421 : Blo 2299435 11206421 := bbase (se 6 (by rfl) ⟨262650, by rfl⟩ : syracuseStep 11206421 = 525301) (by norm_num)
theorem B7470947 : Blo 2299435 7470947 := bstep (se 1 (by rfl) ⟨5603210, by rfl⟩ : syracuseStep 7470947 = 11206421) B11206421
theorem B4980631 : Blo 2299435 4980631 := bstep (se 1 (by rfl) ⟨3735473, by rfl⟩ : syracuseStep 4980631 = 7470947) B7470947
theorem B6640841 : Blo 2299435 6640841 := bstep (se 2 (by rfl) ⟨2490315, by rfl⟩ : syracuseStep 6640841 = 4980631) B4980631
theorem B4427227 : Blo 2299435 4427227 := bstep (se 1 (by rfl) ⟨3320420, by rfl⟩ : syracuseStep 4427227 = 6640841) B6640841
theorem B5902969 : Blo 2299435 5902969 := bstep (se 2 (by rfl) ⟨2213613, by rfl⟩ : syracuseStep 5902969 = 4427227) B4427227
theorem B7870625 : Blo 2299435 7870625 := bstep (se 2 (by rfl) ⟨2951484, by rfl⟩ : syracuseStep 7870625 = 5902969) B5902969
theorem B5247083 : Blo 2299435 5247083 := bstep (se 1 (by rfl) ⟨3935312, by rfl⟩ : syracuseStep 5247083 = 7870625) B7870625
theorem B13992221 : Blo 2299435 13992221 := bstep (se 3 (by rfl) ⟨2623541, by rfl⟩ : syracuseStep 13992221 = 5247083) B5247083
theorem B37312589 : Blo 2299435 37312589 := bstep (se 3 (by rfl) ⟨6996110, by rfl⟩ : syracuseStep 37312589 = 13992221) B13992221
theorem B24875059 : Blo 2299435 24875059 := bstep (se 1 (by rfl) ⟨18656294, by rfl⟩ : syracuseStep 24875059 = 37312589) B37312589
theorem B33166745 : Blo 2299435 33166745 := bstep (se 2 (by rfl) ⟨12437529, by rfl⟩ : syracuseStep 33166745 = 24875059) B24875059
theorem B22111163 : Blo 2299435 22111163 := bstep (se 1 (by rfl) ⟨16583372, by rfl⟩ : syracuseStep 22111163 = 33166745) B33166745
theorem B14740775 : Blo 2299435 14740775 := bstep (se 1 (by rfl) ⟨11055581, by rfl⟩ : syracuseStep 14740775 = 22111163) B22111163
theorem B9827183 : Blo 2299435 9827183 := bstep (se 1 (by rfl) ⟨7370387, by rfl⟩ : syracuseStep 9827183 = 14740775) B14740775
theorem B6551455 : Blo 2299435 6551455 := bstep (se 1 (by rfl) ⟨4913591, by rfl⟩ : syracuseStep 6551455 = 9827183) B9827183
theorem B8735273 : Blo 2299435 8735273 := bstep (se 2 (by rfl) ⟨3275727, by rfl⟩ : syracuseStep 8735273 = 6551455) B6551455
theorem B5823515 : Blo 2299435 5823515 := bstep (se 1 (by rfl) ⟨4367636, by rfl⟩ : syracuseStep 5823515 = 8735273) B8735273
theorem B3882343 : Blo 2299435 3882343 := bstep (se 1 (by rfl) ⟨2911757, by rfl⟩ : syracuseStep 3882343 = 5823515) B5823515
theorem B5176457 : Blo 2299435 5176457 := bstep (se 2 (by rfl) ⟨1941171, by rfl⟩ : syracuseStep 5176457 = 3882343) B3882343
theorem B3450971 : Blo 2299435 3450971 := bstep (se 1 (by rfl) ⟨2588228, by rfl⟩ : syracuseStep 3450971 = 5176457) B5176457
theorem B2300647 : Blo 2299435 2300647 := bstep (se 1 (by rfl) ⟨1725485, by rfl⟩ : syracuseStep 2300647 = 3450971) B3450971
theorem B2588233 : Blo 2299435 2588233 := bbase (se 2 (by rfl) ⟨970587, by rfl⟩ : syracuseStep 2588233 = 1941175) (by norm_num)
theorem B3450977 : Blo 2299435 3450977 := bstep (se 2 (by rfl) ⟨1294116, by rfl⟩ : syracuseStep 3450977 = 2588233) B2588233
theorem B2300651 : Blo 2299435 2300651 := bstep (se 1 (by rfl) ⟨1725488, by rfl⟩ : syracuseStep 2300651 = 3450977) B3450977
theorem B2332045 : Blo 2299435 2332045 := bbase (se 3 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 2332045 = 874517) (by norm_num)
theorem B3109393 : Blo 2299435 3109393 := bstep (se 2 (by rfl) ⟨1166022, by rfl⟩ : syracuseStep 3109393 = 2332045) B2332045
theorem B16583429 : Blo 2299435 16583429 := bstep (se 4 (by rfl) ⟨1554696, by rfl⟩ : syracuseStep 16583429 = 3109393) B3109393
theorem B11055619 : Blo 2299435 11055619 := bstep (se 1 (by rfl) ⟨8291714, by rfl⟩ : syracuseStep 11055619 = 16583429) B16583429
theorem B14740825 : Blo 2299435 14740825 := bstep (se 2 (by rfl) ⟨5527809, by rfl⟩ : syracuseStep 14740825 = 11055619) B11055619
theorem B19654433 : Blo 2299435 19654433 := bstep (se 2 (by rfl) ⟨7370412, by rfl⟩ : syracuseStep 19654433 = 14740825) B14740825
theorem B13102955 : Blo 2299435 13102955 := bstep (se 1 (by rfl) ⟨9827216, by rfl⟩ : syracuseStep 13102955 = 19654433) B19654433
theorem B8735303 : Blo 2299435 8735303 := bstep (se 1 (by rfl) ⟨6551477, by rfl⟩ : syracuseStep 8735303 = 13102955) B13102955
theorem B5823535 : Blo 2299435 5823535 := bstep (se 1 (by rfl) ⟨4367651, by rfl⟩ : syracuseStep 5823535 = 8735303) B8735303
theorem B7764713 : Blo 2299435 7764713 := bstep (se 2 (by rfl) ⟨2911767, by rfl⟩ : syracuseStep 7764713 = 5823535) B5823535
theorem B5176475 : Blo 2299435 5176475 := bstep (se 1 (by rfl) ⟨3882356, by rfl⟩ : syracuseStep 5176475 = 7764713) B7764713
theorem B3450983 : Blo 2299435 3450983 := bstep (se 1 (by rfl) ⟨2588237, by rfl⟩ : syracuseStep 3450983 = 5176475) B5176475
theorem B2300655 : Blo 2299435 2300655 := bstep (se 1 (by rfl) ⟨1725491, by rfl⟩ : syracuseStep 2300655 = 3450983) B3450983
theorem B3450989 : Blo 2299435 3450989 := bbase (se 3 (by rfl) ⟨647060, by rfl⟩ : syracuseStep 3450989 = 1294121) (by norm_num)
theorem B2300659 : Blo 2299435 2300659 := bstep (se 1 (by rfl) ⟨1725494, by rfl⟩ : syracuseStep 2300659 = 3450989) B3450989
theorem B5176493 : Blo 2299435 5176493 := bbase (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) (by norm_num)
theorem B3450995 : Blo 2299435 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B2300663 : Blo 2299435 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B7370453 : Blo 2299435 7370453 := bbase (se 7 (by rfl) ⟨86372, by rfl⟩ : syracuseStep 7370453 = 172745) (by norm_num)
theorem B4913635 : Blo 2299435 4913635 := bstep (se 1 (by rfl) ⟨3685226, by rfl⟩ : syracuseStep 4913635 = 7370453) B7370453
theorem B6551513 : Blo 2299435 6551513 := bstep (se 2 (by rfl) ⟨2456817, by rfl⟩ : syracuseStep 6551513 = 4913635) B4913635
theorem B4367675 : Blo 2299435 4367675 := bstep (se 1 (by rfl) ⟨3275756, by rfl⟩ : syracuseStep 4367675 = 6551513) B6551513
theorem B2911783 : Blo 2299435 2911783 := bstep (se 1 (by rfl) ⟨2183837, by rfl⟩ : syracuseStep 2911783 = 4367675) B4367675
theorem B3882377 : Blo 2299435 3882377 := bstep (se 2 (by rfl) ⟨1455891, by rfl⟩ : syracuseStep 3882377 = 2911783) B2911783
theorem B2588251 : Blo 2299435 2588251 := bstep (se 1 (by rfl) ⟨1941188, by rfl⟩ : syracuseStep 2588251 = 3882377) B3882377
theorem B3451001 : Blo 2299435 3451001 := bstep (se 2 (by rfl) ⟨1294125, by rfl⟩ : syracuseStep 3451001 = 2588251) B2588251
theorem B2300667 : Blo 2299435 2300667 := bstep (se 1 (by rfl) ⟨1725500, by rfl⟩ : syracuseStep 2300667 = 3451001) B3451001
theorem B5603269 : Blo 2299435 5603269 := bbase (se 4 (by rfl) ⟨525306, by rfl⟩ : syracuseStep 5603269 = 1050613) (by norm_num)
theorem B7471025 : Blo 2299435 7471025 := bstep (se 2 (by rfl) ⟨2801634, by rfl⟩ : syracuseStep 7471025 = 5603269) B5603269
theorem B4980683 : Blo 2299435 4980683 := bstep (se 1 (by rfl) ⟨3735512, by rfl⟩ : syracuseStep 4980683 = 7471025) B7471025
theorem B3320455 : Blo 2299435 3320455 := bstep (se 1 (by rfl) ⟨2490341, by rfl⟩ : syracuseStep 3320455 = 4980683) B4980683
theorem B4427273 : Blo 2299435 4427273 := bstep (se 2 (by rfl) ⟨1660227, by rfl⟩ : syracuseStep 4427273 = 3320455) B3320455
theorem B2951515 : Blo 2299435 2951515 := bstep (se 1 (by rfl) ⟨2213636, by rfl⟩ : syracuseStep 2951515 = 4427273) B4427273
theorem B3935353 : Blo 2299435 3935353 := bstep (se 2 (by rfl) ⟨1475757, by rfl⟩ : syracuseStep 3935353 = 2951515) B2951515
theorem B5247137 : Blo 2299435 5247137 := bstep (se 2 (by rfl) ⟨1967676, by rfl⟩ : syracuseStep 5247137 = 3935353) B3935353
theorem B13992365 : Blo 2299435 13992365 := bstep (se 3 (by rfl) ⟨2623568, by rfl⟩ : syracuseStep 13992365 = 5247137) B5247137
theorem B37312973 : Blo 2299435 37312973 := bstep (se 3 (by rfl) ⟨6996182, by rfl⟩ : syracuseStep 37312973 = 13992365) B13992365
theorem B24875315 : Blo 2299435 24875315 := bstep (se 1 (by rfl) ⟨18656486, by rfl⟩ : syracuseStep 24875315 = 37312973) B37312973
theorem B16583543 : Blo 2299435 16583543 := bstep (se 1 (by rfl) ⟨12437657, by rfl⟩ : syracuseStep 16583543 = 24875315) B24875315
theorem B11055695 : Blo 2299435 11055695 := bstep (se 1 (by rfl) ⟨8291771, by rfl⟩ : syracuseStep 11055695 = 16583543) B16583543
theorem B29481853 : Blo 2299435 29481853 := bstep (se 3 (by rfl) ⟨5527847, by rfl⟩ : syracuseStep 29481853 = 11055695) B11055695
theorem B39309137 : Blo 2299435 39309137 := bstep (se 2 (by rfl) ⟨14740926, by rfl⟩ : syracuseStep 39309137 = 29481853) B29481853
theorem B26206091 : Blo 2299435 26206091 := bstep (se 1 (by rfl) ⟨19654568, by rfl⟩ : syracuseStep 26206091 = 39309137) B39309137
theorem B17470727 : Blo 2299435 17470727 := bstep (se 1 (by rfl) ⟨13103045, by rfl⟩ : syracuseStep 17470727 = 26206091) B26206091
theorem B11647151 : Blo 2299435 11647151 := bstep (se 1 (by rfl) ⟨8735363, by rfl⟩ : syracuseStep 11647151 = 17470727) B17470727
theorem B7764767 : Blo 2299435 7764767 := bstep (se 1 (by rfl) ⟨5823575, by rfl⟩ : syracuseStep 7764767 = 11647151) B11647151
theorem B5176511 : Blo 2299435 5176511 := bstep (se 1 (by rfl) ⟨3882383, by rfl⟩ : syracuseStep 5176511 = 7764767) B7764767
theorem B3451007 : Blo 2299435 3451007 := bstep (se 1 (by rfl) ⟨2588255, by rfl⟩ : syracuseStep 3451007 = 5176511) B5176511
theorem B2300671 : Blo 2299435 2300671 := bstep (se 1 (by rfl) ⟨1725503, by rfl⟩ : syracuseStep 2300671 = 3451007) B3451007
theorem B3451013 : Blo 2299435 3451013 := bbase (se 4 (by rfl) ⟨323532, by rfl⟩ : syracuseStep 3451013 = 647065) (by norm_num)
theorem B2300675 : Blo 2299435 2300675 := bstep (se 1 (by rfl) ⟨1725506, by rfl⟩ : syracuseStep 2300675 = 3451013) B3451013
theorem B3882397 : Blo 2299435 3882397 := bbase (se 3 (by rfl) ⟨727949, by rfl⟩ : syracuseStep 3882397 = 1455899) (by norm_num)
theorem B5176529 : Blo 2299435 5176529 := bstep (se 2 (by rfl) ⟨1941198, by rfl⟩ : syracuseStep 5176529 = 3882397) B3882397
theorem B3451019 : Blo 2299435 3451019 := bstep (se 1 (by rfl) ⟨2588264, by rfl⟩ : syracuseStep 3451019 = 5176529) B5176529
theorem B2300679 : Blo 2299435 2300679 := bstep (se 1 (by rfl) ⟨1725509, by rfl⟩ : syracuseStep 2300679 = 3451019) B3451019
theorem B2588269 : Blo 2299435 2588269 := bbase (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) (by norm_num)
theorem B3451025 : Blo 2299435 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B2300683 : Blo 2299435 2300683 := bstep (se 1 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 2300683 = 3451025) B3451025
theorem B7764821 : Blo 2299435 7764821 := bbase (se 9 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 7764821 = 45497) (by norm_num)
theorem B5176547 : Blo 2299435 5176547 := bstep (se 1 (by rfl) ⟨3882410, by rfl⟩ : syracuseStep 5176547 = 7764821) B7764821
theorem B3451031 : Blo 2299435 3451031 := bstep (se 1 (by rfl) ⟨2588273, by rfl⟩ : syracuseStep 3451031 = 5176547) B5176547
theorem B2300687 : Blo 2299435 2300687 := bstep (se 1 (by rfl) ⟨1725515, by rfl⟩ : syracuseStep 2300687 = 3451031) B3451031
theorem B3451037 : Blo 2299435 3451037 := bbase (se 3 (by rfl) ⟨647069, by rfl⟩ : syracuseStep 3451037 = 1294139) (by norm_num)
theorem B2300691 : Blo 2299435 2300691 := bstep (se 1 (by rfl) ⟨1725518, by rfl⟩ : syracuseStep 2300691 = 3451037) B3451037
theorem B5176565 : Blo 2299435 5176565 := bbase (se 5 (by rfl) ⟨242651, by rfl⟩ : syracuseStep 5176565 = 485303) (by norm_num)
theorem B3451043 : Blo 2299435 3451043 := bstep (se 1 (by rfl) ⟨2588282, by rfl⟩ : syracuseStep 3451043 = 5176565) B5176565
theorem B2300695 : Blo 2299435 2300695 := bstep (se 1 (by rfl) ⟨1725521, by rfl⟩ : syracuseStep 2300695 = 3451043) B3451043
theorem B3151877 : Blo 2299435 3151877 := bbase (se 4 (by rfl) ⟨295488, by rfl⟩ : syracuseStep 3151877 = 590977) (by norm_num)
theorem B33620021 : Blo 2299435 33620021 := bstep (se 5 (by rfl) ⟨1575938, by rfl⟩ : syracuseStep 33620021 = 3151877) B3151877
theorem B22413347 : Blo 2299435 22413347 := bstep (se 1 (by rfl) ⟨16810010, by rfl⟩ : syracuseStep 22413347 = 33620021) B33620021
theorem B14942231 : Blo 2299435 14942231 := bstep (se 1 (by rfl) ⟨11206673, by rfl⟩ : syracuseStep 14942231 = 22413347) B22413347
theorem B9961487 : Blo 2299435 9961487 := bstep (se 1 (by rfl) ⟨7471115, by rfl⟩ : syracuseStep 9961487 = 14942231) B14942231
theorem B6640991 : Blo 2299435 6640991 := bstep (se 1 (by rfl) ⟨4980743, by rfl⟩ : syracuseStep 6640991 = 9961487) B9961487
theorem B4427327 : Blo 2299435 4427327 := bstep (se 1 (by rfl) ⟨3320495, by rfl⟩ : syracuseStep 4427327 = 6640991) B6640991
theorem B2951551 : Blo 2299435 2951551 := bstep (se 1 (by rfl) ⟨2213663, by rfl⟩ : syracuseStep 2951551 = 4427327) B4427327
theorem B15741605 : Blo 2299435 15741605 := bstep (se 4 (by rfl) ⟨1475775, by rfl⟩ : syracuseStep 15741605 = 2951551) B2951551
theorem B10494403 : Blo 2299435 10494403 := bstep (se 1 (by rfl) ⟨7870802, by rfl⟩ : syracuseStep 10494403 = 15741605) B15741605
theorem B55970149 : Blo 2299435 55970149 := bstep (se 4 (by rfl) ⟨5247201, by rfl⟩ : syracuseStep 55970149 = 10494403) B10494403
theorem B74626865 : Blo 2299435 74626865 := bstep (se 2 (by rfl) ⟨27985074, by rfl⟩ : syracuseStep 74626865 = 55970149) B55970149
theorem B49751243 : Blo 2299435 49751243 := bstep (se 1 (by rfl) ⟨37313432, by rfl⟩ : syracuseStep 49751243 = 74626865) B74626865
theorem B33167495 : Blo 2299435 33167495 := bstep (se 1 (by rfl) ⟨24875621, by rfl⟩ : syracuseStep 33167495 = 49751243) B49751243
theorem B22111663 : Blo 2299435 22111663 := bstep (se 1 (by rfl) ⟨16583747, by rfl⟩ : syracuseStep 22111663 = 33167495) B33167495
theorem B29482217 : Blo 2299435 29482217 := bstep (se 2 (by rfl) ⟨11055831, by rfl⟩ : syracuseStep 29482217 = 22111663) B22111663
theorem B19654811 : Blo 2299435 19654811 := bstep (se 1 (by rfl) ⟨14741108, by rfl⟩ : syracuseStep 19654811 = 29482217) B29482217
theorem B13103207 : Blo 2299435 13103207 := bstep (se 1 (by rfl) ⟨9827405, by rfl⟩ : syracuseStep 13103207 = 19654811) B19654811
theorem B8735471 : Blo 2299435 8735471 := bstep (se 1 (by rfl) ⟨6551603, by rfl⟩ : syracuseStep 8735471 = 13103207) B13103207
theorem B5823647 : Blo 2299435 5823647 := bstep (se 1 (by rfl) ⟨4367735, by rfl⟩ : syracuseStep 5823647 = 8735471) B8735471
theorem B3882431 : Blo 2299435 3882431 := bstep (se 1 (by rfl) ⟨2911823, by rfl⟩ : syracuseStep 3882431 = 5823647) B5823647
theorem B2588287 : Blo 2299435 2588287 := bstep (se 1 (by rfl) ⟨1941215, by rfl⟩ : syracuseStep 2588287 = 3882431) B3882431
theorem B3451049 : Blo 2299435 3451049 := bstep (se 2 (by rfl) ⟨1294143, by rfl⟩ : syracuseStep 3451049 = 2588287) B2588287
theorem B2300699 : Blo 2299435 2300699 := bstep (se 1 (by rfl) ⟨1725524, by rfl⟩ : syracuseStep 2300699 = 3451049) B3451049
theorem B3545869 : Blo 2299435 3545869 := bbase (se 3 (by rfl) ⟨664850, by rfl⟩ : syracuseStep 3545869 = 1329701) (by norm_num)
theorem B4727825 : Blo 2299435 4727825 := bstep (se 2 (by rfl) ⟨1772934, by rfl⟩ : syracuseStep 4727825 = 3545869) B3545869
theorem B3151883 : Blo 2299435 3151883 := bstep (se 1 (by rfl) ⟨2363912, by rfl⟩ : syracuseStep 3151883 = 4727825) B4727825
theorem B8405021 : Blo 2299435 8405021 := bstep (se 3 (by rfl) ⟨1575941, by rfl⟩ : syracuseStep 8405021 = 3151883) B3151883
theorem B5603347 : Blo 2299435 5603347 := bstep (se 1 (by rfl) ⟨4202510, by rfl⟩ : syracuseStep 5603347 = 8405021) B8405021
theorem B7471129 : Blo 2299435 7471129 := bstep (se 2 (by rfl) ⟨2801673, by rfl⟩ : syracuseStep 7471129 = 5603347) B5603347
theorem B9961505 : Blo 2299435 9961505 := bstep (se 2 (by rfl) ⟨3735564, by rfl⟩ : syracuseStep 9961505 = 7471129) B7471129
theorem B6641003 : Blo 2299435 6641003 := bstep (se 1 (by rfl) ⟨4980752, by rfl⟩ : syracuseStep 6641003 = 9961505) B9961505
theorem B4427335 : Blo 2299435 4427335 := bstep (se 1 (by rfl) ⟨3320501, by rfl⟩ : syracuseStep 4427335 = 6641003) B6641003
theorem B5903113 : Blo 2299435 5903113 := bstep (se 2 (by rfl) ⟨2213667, by rfl⟩ : syracuseStep 5903113 = 4427335) B4427335
theorem B7870817 : Blo 2299435 7870817 := bstep (se 2 (by rfl) ⟨2951556, by rfl⟩ : syracuseStep 7870817 = 5903113) B5903113
theorem B20988845 : Blo 2299435 20988845 := bstep (se 3 (by rfl) ⟨3935408, by rfl⟩ : syracuseStep 20988845 = 7870817) B7870817
theorem B13992563 : Blo 2299435 13992563 := bstep (se 1 (by rfl) ⟨10494422, by rfl⟩ : syracuseStep 13992563 = 20988845) B20988845
theorem B9328375 : Blo 2299435 9328375 := bstep (se 1 (by rfl) ⟨6996281, by rfl⟩ : syracuseStep 9328375 = 13992563) B13992563
theorem B12437833 : Blo 2299435 12437833 := bstep (se 2 (by rfl) ⟨4664187, by rfl⟩ : syracuseStep 12437833 = 9328375) B9328375
theorem B16583777 : Blo 2299435 16583777 := bstep (se 2 (by rfl) ⟨6218916, by rfl⟩ : syracuseStep 16583777 = 12437833) B12437833
theorem B11055851 : Blo 2299435 11055851 := bstep (se 1 (by rfl) ⟨8291888, by rfl⟩ : syracuseStep 11055851 = 16583777) B16583777
theorem B7370567 : Blo 2299435 7370567 := bstep (se 1 (by rfl) ⟨5527925, by rfl⟩ : syracuseStep 7370567 = 11055851) B11055851
theorem B4913711 : Blo 2299435 4913711 := bstep (se 1 (by rfl) ⟨3685283, by rfl⟩ : syracuseStep 4913711 = 7370567) B7370567
theorem B3275807 : Blo 2299435 3275807 := bstep (se 1 (by rfl) ⟨2456855, by rfl⟩ : syracuseStep 3275807 = 4913711) B4913711
theorem B8735485 : Blo 2299435 8735485 := bstep (se 3 (by rfl) ⟨1637903, by rfl⟩ : syracuseStep 8735485 = 3275807) B3275807
theorem B11647313 : Blo 2299435 11647313 := bstep (se 2 (by rfl) ⟨4367742, by rfl⟩ : syracuseStep 11647313 = 8735485) B8735485
theorem B7764875 : Blo 2299435 7764875 := bstep (se 1 (by rfl) ⟨5823656, by rfl⟩ : syracuseStep 7764875 = 11647313) B11647313
theorem B5176583 : Blo 2299435 5176583 := bstep (se 1 (by rfl) ⟨3882437, by rfl⟩ : syracuseStep 5176583 = 7764875) B7764875
theorem B3451055 : Blo 2299435 3451055 := bstep (se 1 (by rfl) ⟨2588291, by rfl⟩ : syracuseStep 3451055 = 5176583) B5176583
theorem B2300703 : Blo 2299435 2300703 := bstep (se 1 (by rfl) ⟨1725527, by rfl⟩ : syracuseStep 2300703 = 3451055) B3451055
theorem B3451061 : Blo 2299435 3451061 := bbase (se 5 (by rfl) ⟨161768, by rfl⟩ : syracuseStep 3451061 = 323537) (by norm_num)
theorem B2300707 : Blo 2299435 2300707 := bstep (se 1 (by rfl) ⟨1725530, by rfl⟩ : syracuseStep 2300707 = 3451061) B3451061
theorem B5823677 : Blo 2299435 5823677 := bbase (se 3 (by rfl) ⟨1091939, by rfl⟩ : syracuseStep 5823677 = 2183879) (by norm_num)
theorem B3882451 : Blo 2299435 3882451 := bstep (se 1 (by rfl) ⟨2911838, by rfl⟩ : syracuseStep 3882451 = 5823677) B5823677
theorem B5176601 : Blo 2299435 5176601 := bstep (se 2 (by rfl) ⟨1941225, by rfl⟩ : syracuseStep 5176601 = 3882451) B3882451
theorem B3451067 : Blo 2299435 3451067 := bstep (se 1 (by rfl) ⟨2588300, by rfl⟩ : syracuseStep 3451067 = 5176601) B5176601
theorem B2300711 : Blo 2299435 2300711 := bstep (se 1 (by rfl) ⟨1725533, by rfl⟩ : syracuseStep 2300711 = 3451067) B3451067
theorem B2588305 : Blo 2299435 2588305 := bbase (se 2 (by rfl) ⟨970614, by rfl⟩ : syracuseStep 2588305 = 1941229) (by norm_num)
theorem B3451073 : Blo 2299435 3451073 := bstep (se 2 (by rfl) ⟨1294152, by rfl⟩ : syracuseStep 3451073 = 2588305) B2588305
theorem B2300715 : Blo 2299435 2300715 := bstep (se 1 (by rfl) ⟨1725536, by rfl⟩ : syracuseStep 2300715 = 3451073) B3451073
theorem B4367773 : Blo 2299435 4367773 := bbase (se 3 (by rfl) ⟨818957, by rfl⟩ : syracuseStep 4367773 = 1637915) (by norm_num)
theorem B5823697 : Blo 2299435 5823697 := bstep (se 2 (by rfl) ⟨2183886, by rfl⟩ : syracuseStep 5823697 = 4367773) B4367773
theorem B7764929 : Blo 2299435 7764929 := bstep (se 2 (by rfl) ⟨2911848, by rfl⟩ : syracuseStep 7764929 = 5823697) B5823697
theorem B5176619 : Blo 2299435 5176619 := bstep (se 1 (by rfl) ⟨3882464, by rfl⟩ : syracuseStep 5176619 = 7764929) B7764929
theorem B3451079 : Blo 2299435 3451079 := bstep (se 1 (by rfl) ⟨2588309, by rfl⟩ : syracuseStep 3451079 = 5176619) B5176619
theorem B2300719 : Blo 2299435 2300719 := bstep (se 1 (by rfl) ⟨1725539, by rfl⟩ : syracuseStep 2300719 = 3451079) B3451079
theorem B3451085 : Blo 2299435 3451085 := bbase (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) (by norm_num)
theorem B2300723 : Blo 2299435 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B5176637 : Blo 2299435 5176637 := bbase (se 3 (by rfl) ⟨970619, by rfl⟩ : syracuseStep 5176637 = 1941239) (by norm_num)
theorem B3451091 : Blo 2299435 3451091 := bstep (se 1 (by rfl) ⟨2588318, by rfl⟩ : syracuseStep 3451091 = 5176637) B5176637
theorem B2300727 : Blo 2299435 2300727 := bstep (se 1 (by rfl) ⟨1725545, by rfl⟩ : syracuseStep 2300727 = 3451091) B3451091
theorem B3882485 : Blo 2299435 3882485 := bbase (se 5 (by rfl) ⟨181991, by rfl⟩ : syracuseStep 3882485 = 363983) (by norm_num)
theorem B2588323 : Blo 2299435 2588323 := bstep (se 1 (by rfl) ⟨1941242, by rfl⟩ : syracuseStep 2588323 = 3882485) B3882485
theorem B3451097 : Blo 2299435 3451097 := bstep (se 2 (by rfl) ⟨1294161, by rfl⟩ : syracuseStep 3451097 = 2588323) B2588323
theorem B2300731 : Blo 2299435 2300731 := bstep (se 1 (by rfl) ⟨1725548, by rfl⟩ : syracuseStep 2300731 = 3451097) B3451097
theorem B2764001 : Blo 2299435 2764001 := bbase (se 2 (by rfl) ⟨1036500, by rfl⟩ : syracuseStep 2764001 = 2073001) (by norm_num)
theorem B7370669 : Blo 2299435 7370669 := bstep (se 3 (by rfl) ⟨1382000, by rfl⟩ : syracuseStep 7370669 = 2764001) B2764001
theorem B4913779 : Blo 2299435 4913779 := bstep (se 1 (by rfl) ⟨3685334, by rfl⟩ : syracuseStep 4913779 = 7370669) B7370669
theorem B6551705 : Blo 2299435 6551705 := bstep (se 2 (by rfl) ⟨2456889, by rfl⟩ : syracuseStep 6551705 = 4913779) B4913779
theorem B17471213 : Blo 2299435 17471213 := bstep (se 3 (by rfl) ⟨3275852, by rfl⟩ : syracuseStep 17471213 = 6551705) B6551705
theorem B11647475 : Blo 2299435 11647475 := bstep (se 1 (by rfl) ⟨8735606, by rfl⟩ : syracuseStep 11647475 = 17471213) B17471213
theorem B7764983 : Blo 2299435 7764983 := bstep (se 1 (by rfl) ⟨5823737, by rfl⟩ : syracuseStep 7764983 = 11647475) B11647475
theorem B5176655 : Blo 2299435 5176655 := bstep (se 1 (by rfl) ⟨3882491, by rfl⟩ : syracuseStep 5176655 = 7764983) B7764983
theorem B3451103 : Blo 2299435 3451103 := bstep (se 1 (by rfl) ⟨2588327, by rfl⟩ : syracuseStep 3451103 = 5176655) B5176655
theorem B2300735 : Blo 2299435 2300735 := bstep (se 1 (by rfl) ⟨1725551, by rfl⟩ : syracuseStep 2300735 = 3451103) B3451103
theorem B3451109 : Blo 2299435 3451109 := bbase (se 4 (by rfl) ⟨323541, by rfl⟩ : syracuseStep 3451109 = 647083) (by norm_num)
theorem B2300739 : Blo 2299435 2300739 := bstep (se 1 (by rfl) ⟨1725554, by rfl⟩ : syracuseStep 2300739 = 3451109) B3451109
theorem B4913797 : Blo 2299435 4913797 := bbase (se 4 (by rfl) ⟨460668, by rfl⟩ : syracuseStep 4913797 = 921337) (by norm_num)
theorem B6551729 : Blo 2299435 6551729 := bstep (se 2 (by rfl) ⟨2456898, by rfl⟩ : syracuseStep 6551729 = 4913797) B4913797
theorem B4367819 : Blo 2299435 4367819 := bstep (se 1 (by rfl) ⟨3275864, by rfl⟩ : syracuseStep 4367819 = 6551729) B6551729
theorem B2911879 : Blo 2299435 2911879 := bstep (se 1 (by rfl) ⟨2183909, by rfl⟩ : syracuseStep 2911879 = 4367819) B4367819
theorem B3882505 : Blo 2299435 3882505 := bstep (se 2 (by rfl) ⟨1455939, by rfl⟩ : syracuseStep 3882505 = 2911879) B2911879
theorem B5176673 : Blo 2299435 5176673 := bstep (se 2 (by rfl) ⟨1941252, by rfl⟩ : syracuseStep 5176673 = 3882505) B3882505
theorem B3451115 : Blo 2299435 3451115 := bstep (se 1 (by rfl) ⟨2588336, by rfl⟩ : syracuseStep 3451115 = 5176673) B5176673
theorem B2300743 : Blo 2299435 2300743 := bstep (se 1 (by rfl) ⟨1725557, by rfl⟩ : syracuseStep 2300743 = 3451115) B3451115
theorem B2588341 : Blo 2299435 2588341 := bbase (se 5 (by rfl) ⟨121328, by rfl⟩ : syracuseStep 2588341 = 242657) (by norm_num)
theorem B3451121 : Blo 2299435 3451121 := bstep (se 2 (by rfl) ⟨1294170, by rfl⟩ : syracuseStep 3451121 = 2588341) B2588341
theorem B2300747 : Blo 2299435 2300747 := bstep (se 1 (by rfl) ⟨1725560, by rfl⟩ : syracuseStep 2300747 = 3451121) B3451121
theorem B2911889 : Blo 2299435 2911889 := bbase (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) (by norm_num)
theorem B7765037 : Blo 2299435 7765037 := bstep (se 3 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 7765037 = 2911889) B2911889
theorem B5176691 : Blo 2299435 5176691 := bstep (se 1 (by rfl) ⟨3882518, by rfl⟩ : syracuseStep 5176691 = 7765037) B7765037
theorem B3451127 : Blo 2299435 3451127 := bstep (se 1 (by rfl) ⟨2588345, by rfl⟩ : syracuseStep 3451127 = 5176691) B5176691
theorem B2300751 : Blo 2299435 2300751 := bstep (se 1 (by rfl) ⟨1725563, by rfl⟩ : syracuseStep 2300751 = 3451127) B3451127
theorem B3451133 : Blo 2299435 3451133 := bbase (se 3 (by rfl) ⟨647087, by rfl⟩ : syracuseStep 3451133 = 1294175) (by norm_num)
theorem B2300755 : Blo 2299435 2300755 := bstep (se 1 (by rfl) ⟨1725566, by rfl⟩ : syracuseStep 2300755 = 3451133) B3451133
theorem B5176709 : Blo 2299435 5176709 := bbase (se 4 (by rfl) ⟨485316, by rfl⟩ : syracuseStep 5176709 = 970633) (by norm_num)
theorem B3451139 : Blo 2299435 3451139 := bstep (se 1 (by rfl) ⟨2588354, by rfl⟩ : syracuseStep 3451139 = 5176709) B5176709
theorem B2300759 : Blo 2299435 2300759 := bstep (se 1 (by rfl) ⟨1725569, by rfl⟩ : syracuseStep 2300759 = 3451139) B3451139
theorem B3275893 : Blo 2299435 3275893 := bbase (se 5 (by rfl) ⟨153557, by rfl⟩ : syracuseStep 3275893 = 307115) (by norm_num)
theorem B4367857 : Blo 2299435 4367857 := bstep (se 2 (by rfl) ⟨1637946, by rfl⟩ : syracuseStep 4367857 = 3275893) B3275893
theorem B5823809 : Blo 2299435 5823809 := bstep (se 2 (by rfl) ⟨2183928, by rfl⟩ : syracuseStep 5823809 = 4367857) B4367857
theorem B3882539 : Blo 2299435 3882539 := bstep (se 1 (by rfl) ⟨2911904, by rfl⟩ : syracuseStep 3882539 = 5823809) B5823809
theorem B2588359 : Blo 2299435 2588359 := bstep (se 1 (by rfl) ⟨1941269, by rfl⟩ : syracuseStep 2588359 = 3882539) B3882539
theorem B3451145 : Blo 2299435 3451145 := bstep (se 2 (by rfl) ⟨1294179, by rfl⟩ : syracuseStep 3451145 = 2588359) B2588359
theorem B2300763 : Blo 2299435 2300763 := bstep (se 1 (by rfl) ⟨1725572, by rfl⟩ : syracuseStep 2300763 = 3451145) B3451145
theorem B11647637 : Blo 2299435 11647637 := bbase (se 6 (by rfl) ⟨272991, by rfl⟩ : syracuseStep 11647637 = 545983) (by norm_num)
theorem B7765091 : Blo 2299435 7765091 := bstep (se 1 (by rfl) ⟨5823818, by rfl⟩ : syracuseStep 7765091 = 11647637) B11647637
theorem B5176727 : Blo 2299435 5176727 := bstep (se 1 (by rfl) ⟨3882545, by rfl⟩ : syracuseStep 5176727 = 7765091) B7765091
theorem B3451151 : Blo 2299435 3451151 := bstep (se 1 (by rfl) ⟨2588363, by rfl⟩ : syracuseStep 3451151 = 5176727) B5176727
theorem B2300767 : Blo 2299435 2300767 := bstep (se 1 (by rfl) ⟨1725575, by rfl⟩ : syracuseStep 2300767 = 3451151) B3451151
theorem B3451157 : Blo 2299435 3451157 := bbase (se 6 (by rfl) ⟨80886, by rfl⟩ : syracuseStep 3451157 = 161773) (by norm_num)
theorem B2300771 : Blo 2299435 2300771 := bstep (se 1 (by rfl) ⟨1725578, by rfl⟩ : syracuseStep 2300771 = 3451157) B3451157
theorem B2764049 : Blo 2299435 2764049 := bbase (se 2 (by rfl) ⟨1036518, by rfl⟩ : syracuseStep 2764049 = 2073037) (by norm_num)
theorem B29483189 : Blo 2299435 29483189 := bstep (se 5 (by rfl) ⟨1382024, by rfl⟩ : syracuseStep 29483189 = 2764049) B2764049
theorem B19655459 : Blo 2299435 19655459 := bstep (se 1 (by rfl) ⟨14741594, by rfl⟩ : syracuseStep 19655459 = 29483189) B29483189
theorem B13103639 : Blo 2299435 13103639 := bstep (se 1 (by rfl) ⟨9827729, by rfl⟩ : syracuseStep 13103639 = 19655459) B19655459
theorem B8735759 : Blo 2299435 8735759 := bstep (se 1 (by rfl) ⟨6551819, by rfl⟩ : syracuseStep 8735759 = 13103639) B13103639
theorem B5823839 : Blo 2299435 5823839 := bstep (se 1 (by rfl) ⟨4367879, by rfl⟩ : syracuseStep 5823839 = 8735759) B8735759
theorem B3882559 : Blo 2299435 3882559 := bstep (se 1 (by rfl) ⟨2911919, by rfl⟩ : syracuseStep 3882559 = 5823839) B5823839
theorem B5176745 : Blo 2299435 5176745 := bstep (se 2 (by rfl) ⟨1941279, by rfl⟩ : syracuseStep 5176745 = 3882559) B3882559
theorem B3451163 : Blo 2299435 3451163 := bstep (se 1 (by rfl) ⟨2588372, by rfl⟩ : syracuseStep 3451163 = 5176745) B5176745
theorem B2300775 : Blo 2299435 2300775 := bstep (se 1 (by rfl) ⟨1725581, by rfl⟩ : syracuseStep 2300775 = 3451163) B3451163
theorem B2588377 : Blo 2299435 2588377 := bbase (se 2 (by rfl) ⟨970641, by rfl⟩ : syracuseStep 2588377 = 1941283) (by norm_num)
theorem B3451169 : Blo 2299435 3451169 := bstep (se 2 (by rfl) ⟨1294188, by rfl⟩ : syracuseStep 3451169 = 2588377) B2588377
theorem B2300779 : Blo 2299435 2300779 := bstep (se 1 (by rfl) ⟨1725584, by rfl⟩ : syracuseStep 2300779 = 3451169) B3451169
theorem B2456941 : Blo 2299435 2456941 := bbase (se 3 (by rfl) ⟨460676, by rfl⟩ : syracuseStep 2456941 = 921353) (by norm_num)
theorem B3275921 : Blo 2299435 3275921 := bstep (se 2 (by rfl) ⟨1228470, by rfl⟩ : syracuseStep 3275921 = 2456941) B2456941
theorem B8735789 : Blo 2299435 8735789 := bstep (se 3 (by rfl) ⟨1637960, by rfl⟩ : syracuseStep 8735789 = 3275921) B3275921
theorem B5823859 : Blo 2299435 5823859 := bstep (se 1 (by rfl) ⟨4367894, by rfl⟩ : syracuseStep 5823859 = 8735789) B8735789
theorem B7765145 : Blo 2299435 7765145 := bstep (se 2 (by rfl) ⟨2911929, by rfl⟩ : syracuseStep 7765145 = 5823859) B5823859
theorem B5176763 : Blo 2299435 5176763 := bstep (se 1 (by rfl) ⟨3882572, by rfl⟩ : syracuseStep 5176763 = 7765145) B7765145
theorem B3451175 : Blo 2299435 3451175 := bstep (se 1 (by rfl) ⟨2588381, by rfl⟩ : syracuseStep 3451175 = 5176763) B5176763
theorem B2300783 : Blo 2299435 2300783 := bstep (se 1 (by rfl) ⟨1725587, by rfl⟩ : syracuseStep 2300783 = 3451175) B3451175
theorem B3451181 : Blo 2299435 3451181 := bbase (se 3 (by rfl) ⟨647096, by rfl⟩ : syracuseStep 3451181 = 1294193) (by norm_num)
theorem B2300787 : Blo 2299435 2300787 := bstep (se 1 (by rfl) ⟨1725590, by rfl⟩ : syracuseStep 2300787 = 3451181) B3451181
theorem B5176781 : Blo 2299435 5176781 := bbase (se 3 (by rfl) ⟨970646, by rfl⟩ : syracuseStep 5176781 = 1941293) (by norm_num)
theorem B3451187 : Blo 2299435 3451187 := bstep (se 1 (by rfl) ⟨2588390, by rfl⟩ : syracuseStep 3451187 = 5176781) B5176781
theorem B2300791 : Blo 2299435 2300791 := bstep (se 1 (by rfl) ⟨1725593, by rfl⟩ : syracuseStep 2300791 = 3451187) B3451187
theorem B2911945 : Blo 2299435 2911945 := bbase (se 2 (by rfl) ⟨1091979, by rfl⟩ : syracuseStep 2911945 = 2183959) (by norm_num)
theorem B3882593 : Blo 2299435 3882593 := bstep (se 2 (by rfl) ⟨1455972, by rfl⟩ : syracuseStep 3882593 = 2911945) B2911945
theorem B2588395 : Blo 2299435 2588395 := bstep (se 1 (by rfl) ⟨1941296, by rfl⟩ : syracuseStep 2588395 = 3882593) B3882593
theorem B3451193 : Blo 2299435 3451193 := bstep (se 2 (by rfl) ⟨1294197, by rfl⟩ : syracuseStep 3451193 = 2588395) B2588395
theorem B2300795 : Blo 2299435 2300795 := bstep (se 1 (by rfl) ⟨1725596, by rfl⟩ : syracuseStep 2300795 = 3451193) B3451193
theorem B4549157 : Blo 2299435 4549157 := bbase (se 4 (by rfl) ⟨426483, by rfl⟩ : syracuseStep 4549157 = 852967) (by norm_num)
theorem B3032771 : Blo 2299435 3032771 := bstep (se 1 (by rfl) ⟨2274578, by rfl⟩ : syracuseStep 3032771 = 4549157) B4549157
theorem B32349557 : Blo 2299435 32349557 := bstep (se 5 (by rfl) ⟨1516385, by rfl⟩ : syracuseStep 32349557 = 3032771) B3032771
theorem B21566371 : Blo 2299435 21566371 := bstep (se 1 (by rfl) ⟨16174778, by rfl⟩ : syracuseStep 21566371 = 32349557) B32349557
theorem B28755161 : Blo 2299435 28755161 := bstep (se 2 (by rfl) ⟨10783185, by rfl⟩ : syracuseStep 28755161 = 21566371) B21566371
theorem B19170107 : Blo 2299435 19170107 := bstep (se 1 (by rfl) ⟨14377580, by rfl⟩ : syracuseStep 19170107 = 28755161) B28755161
theorem B12780071 : Blo 2299435 12780071 := bstep (se 1 (by rfl) ⟨9585053, by rfl⟩ : syracuseStep 12780071 = 19170107) B19170107
theorem B8520047 : Blo 2299435 8520047 := bstep (se 1 (by rfl) ⟨6390035, by rfl⟩ : syracuseStep 8520047 = 12780071) B12780071
theorem B90880501 : Blo 2299435 90880501 := bstep (se 5 (by rfl) ⟨4260023, by rfl⟩ : syracuseStep 90880501 = 8520047) B8520047
theorem B121174001 : Blo 2299435 121174001 := bstep (se 2 (by rfl) ⟨45440250, by rfl⟩ : syracuseStep 121174001 = 90880501) B90880501
theorem B80782667 : Blo 2299435 80782667 := bstep (se 1 (by rfl) ⟨60587000, by rfl⟩ : syracuseStep 80782667 = 121174001) B121174001
theorem B53855111 : Blo 2299435 53855111 := bstep (se 1 (by rfl) ⟨40391333, by rfl⟩ : syracuseStep 53855111 = 80782667) B80782667
theorem B35903407 : Blo 2299435 35903407 := bstep (se 1 (by rfl) ⟨26927555, by rfl⟩ : syracuseStep 35903407 = 53855111) B53855111
theorem B47871209 : Blo 2299435 47871209 := bstep (se 2 (by rfl) ⟨17951703, by rfl⟩ : syracuseStep 47871209 = 35903407) B35903407
theorem B127656557 : Blo 2299435 127656557 := bstep (se 3 (by rfl) ⟨23935604, by rfl⟩ : syracuseStep 127656557 = 47871209) B47871209
theorem B85104371 : Blo 2299435 85104371 := bstep (se 1 (by rfl) ⟨63828278, by rfl⟩ : syracuseStep 85104371 = 127656557) B127656557
theorem B56736247 : Blo 2299435 56736247 := bstep (se 1 (by rfl) ⟨42552185, by rfl⟩ : syracuseStep 56736247 = 85104371) B85104371
theorem B75648329 : Blo 2299435 75648329 := bstep (se 2 (by rfl) ⟨28368123, by rfl⟩ : syracuseStep 75648329 = 56736247) B56736247
theorem B50432219 : Blo 2299435 50432219 := bstep (se 1 (by rfl) ⟨37824164, by rfl⟩ : syracuseStep 50432219 = 75648329) B75648329
theorem B33621479 : Blo 2299435 33621479 := bstep (se 1 (by rfl) ⟨25216109, by rfl⟩ : syracuseStep 33621479 = 50432219) B50432219
theorem B22414319 : Blo 2299435 22414319 := bstep (se 1 (by rfl) ⟨16810739, by rfl⟩ : syracuseStep 22414319 = 33621479) B33621479
theorem B14942879 : Blo 2299435 14942879 := bstep (se 1 (by rfl) ⟨11207159, by rfl⟩ : syracuseStep 14942879 = 22414319) B22414319
theorem B9961919 : Blo 2299435 9961919 := bstep (se 1 (by rfl) ⟨7471439, by rfl⟩ : syracuseStep 9961919 = 14942879) B14942879
theorem B6641279 : Blo 2299435 6641279 := bstep (se 1 (by rfl) ⟨4980959, by rfl⟩ : syracuseStep 6641279 = 9961919) B9961919
theorem B4427519 : Blo 2299435 4427519 := bstep (se 1 (by rfl) ⟨3320639, by rfl⟩ : syracuseStep 4427519 = 6641279) B6641279
theorem B11806717 : Blo 2299435 11806717 := bstep (se 3 (by rfl) ⟨2213759, by rfl⟩ : syracuseStep 11806717 = 4427519) B4427519
theorem B15742289 : Blo 2299435 15742289 := bstep (se 2 (by rfl) ⟨5903358, by rfl⟩ : syracuseStep 15742289 = 11806717) B11806717
theorem B10494859 : Blo 2299435 10494859 := bstep (se 1 (by rfl) ⟨7871144, by rfl⟩ : syracuseStep 10494859 = 15742289) B15742289
theorem B13993145 : Blo 2299435 13993145 := bstep (se 2 (by rfl) ⟨5247429, by rfl⟩ : syracuseStep 13993145 = 10494859) B10494859
theorem B9328763 : Blo 2299435 9328763 := bstep (se 1 (by rfl) ⟨6996572, by rfl⟩ : syracuseStep 9328763 = 13993145) B13993145
theorem B6219175 : Blo 2299435 6219175 := bstep (se 1 (by rfl) ⟨4664381, by rfl⟩ : syracuseStep 6219175 = 9328763) B9328763
theorem B8292233 : Blo 2299435 8292233 := bstep (se 2 (by rfl) ⟨3109587, by rfl⟩ : syracuseStep 8292233 = 6219175) B6219175
theorem B22112621 : Blo 2299435 22112621 := bstep (se 3 (by rfl) ⟨4146116, by rfl⟩ : syracuseStep 22112621 = 8292233) B8292233
theorem B14741747 : Blo 2299435 14741747 := bstep (se 1 (by rfl) ⟨11056310, by rfl⟩ : syracuseStep 14741747 = 22112621) B22112621
theorem B9827831 : Blo 2299435 9827831 := bstep (se 1 (by rfl) ⟨7370873, by rfl⟩ : syracuseStep 9827831 = 14741747) B14741747
theorem B26207549 : Blo 2299435 26207549 := bstep (se 3 (by rfl) ⟨4913915, by rfl⟩ : syracuseStep 26207549 = 9827831) B9827831
theorem B17471699 : Blo 2299435 17471699 := bstep (se 1 (by rfl) ⟨13103774, by rfl⟩ : syracuseStep 17471699 = 26207549) B26207549
theorem B11647799 : Blo 2299435 11647799 := bstep (se 1 (by rfl) ⟨8735849, by rfl⟩ : syracuseStep 11647799 = 17471699) B17471699
theorem B7765199 : Blo 2299435 7765199 := bstep (se 1 (by rfl) ⟨5823899, by rfl⟩ : syracuseStep 7765199 = 11647799) B11647799
theorem B5176799 : Blo 2299435 5176799 := bstep (se 1 (by rfl) ⟨3882599, by rfl⟩ : syracuseStep 5176799 = 7765199) B7765199
theorem B3451199 : Blo 2299435 3451199 := bstep (se 1 (by rfl) ⟨2588399, by rfl⟩ : syracuseStep 3451199 = 5176799) B5176799
theorem B2300799 : Blo 2299435 2300799 := bstep (se 1 (by rfl) ⟨1725599, by rfl⟩ : syracuseStep 2300799 = 3451199) B3451199
theorem B3451205 : Blo 2299435 3451205 := bbase (se 4 (by rfl) ⟨323550, by rfl⟩ : syracuseStep 3451205 = 647101) (by norm_num)
theorem B2300803 : Blo 2299435 2300803 := bstep (se 1 (by rfl) ⟨1725602, by rfl⟩ : syracuseStep 2300803 = 3451205) B3451205
theorem B3882613 : Blo 2299435 3882613 := bbase (se 5 (by rfl) ⟨181997, by rfl⟩ : syracuseStep 3882613 = 363995) (by norm_num)
theorem B5176817 : Blo 2299435 5176817 := bstep (se 2 (by rfl) ⟨1941306, by rfl⟩ : syracuseStep 5176817 = 3882613) B3882613
theorem B3451211 : Blo 2299435 3451211 := bstep (se 1 (by rfl) ⟨2588408, by rfl⟩ : syracuseStep 3451211 = 5176817) B5176817
theorem B2300807 : Blo 2299435 2300807 := bstep (se 1 (by rfl) ⟨1725605, by rfl⟩ : syracuseStep 2300807 = 3451211) B3451211
theorem B2588413 : Blo 2299435 2588413 := bbase (se 3 (by rfl) ⟨485327, by rfl⟩ : syracuseStep 2588413 = 970655) (by norm_num)
theorem B3451217 : Blo 2299435 3451217 := bstep (se 2 (by rfl) ⟨1294206, by rfl⟩ : syracuseStep 3451217 = 2588413) B2588413
theorem B2300811 : Blo 2299435 2300811 := bstep (se 1 (by rfl) ⟨1725608, by rfl⟩ : syracuseStep 2300811 = 3451217) B3451217
theorem B7765253 : Blo 2299435 7765253 := bbase (se 4 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 7765253 = 1455985) (by norm_num)
theorem B5176835 : Blo 2299435 5176835 := bstep (se 1 (by rfl) ⟨3882626, by rfl⟩ : syracuseStep 5176835 = 7765253) B7765253
theorem B3451223 : Blo 2299435 3451223 := bstep (se 1 (by rfl) ⟨2588417, by rfl⟩ : syracuseStep 3451223 = 5176835) B5176835
theorem B2300815 : Blo 2299435 2300815 := bstep (se 1 (by rfl) ⟨1725611, by rfl⟩ : syracuseStep 2300815 = 3451223) B3451223
theorem B3451229 : Blo 2299435 3451229 := bbase (se 3 (by rfl) ⟨647105, by rfl⟩ : syracuseStep 3451229 = 1294211) (by norm_num)
theorem B2300819 : Blo 2299435 2300819 := bstep (se 1 (by rfl) ⟨1725614, by rfl⟩ : syracuseStep 2300819 = 3451229) B3451229
theorem B5176853 : Blo 2299435 5176853 := bbase (se 6 (by rfl) ⟨121332, by rfl⟩ : syracuseStep 5176853 = 242665) (by norm_num)
theorem B3451235 : Blo 2299435 3451235 := bstep (se 1 (by rfl) ⟨2588426, by rfl⟩ : syracuseStep 3451235 = 5176853) B5176853
theorem B2300823 : Blo 2299435 2300823 := bstep (se 1 (by rfl) ⟨1725617, by rfl⟩ : syracuseStep 2300823 = 3451235) B3451235
theorem B8735957 : Blo 2299435 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B5823971 : Blo 2299435 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B3882647 : Blo 2299435 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B2588431 : Blo 2299435 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B3451241 : Blo 2299435 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B2300827 : Blo 2299435 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B13103957 : Blo 2299435 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B8735971 : Blo 2299435 8735971 := bstep (se 1 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 8735971 = 13103957) B13103957
theorem B11647961 : Blo 2299435 11647961 := bstep (se 2 (by rfl) ⟨4367985, by rfl⟩ : syracuseStep 11647961 = 8735971) B8735971
theorem B7765307 : Blo 2299435 7765307 := bstep (se 1 (by rfl) ⟨5823980, by rfl⟩ : syracuseStep 7765307 = 11647961) B11647961
theorem B5176871 : Blo 2299435 5176871 := bstep (se 1 (by rfl) ⟨3882653, by rfl⟩ : syracuseStep 5176871 = 7765307) B7765307
theorem B3451247 : Blo 2299435 3451247 := bstep (se 1 (by rfl) ⟨2588435, by rfl⟩ : syracuseStep 3451247 = 5176871) B5176871
theorem B2300831 : Blo 2299435 2300831 := bstep (se 1 (by rfl) ⟨1725623, by rfl⟩ : syracuseStep 2300831 = 3451247) B3451247
theorem B3451253 : Blo 2299435 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B2300835 : Blo 2299435 2300835 := bstep (se 1 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 2300835 = 3451253) B3451253
theorem B2457001 : Blo 2299435 2457001 := bbase (se 2 (by rfl) ⟨921375, by rfl⟩ : syracuseStep 2457001 = 1842751) (by norm_num)
theorem B3276001 : Blo 2299435 3276001 := bstep (se 2 (by rfl) ⟨1228500, by rfl⟩ : syracuseStep 3276001 = 2457001) B2457001
theorem B4368001 : Blo 2299435 4368001 := bstep (se 2 (by rfl) ⟨1638000, by rfl⟩ : syracuseStep 4368001 = 3276001) B3276001
theorem B5824001 : Blo 2299435 5824001 := bstep (se 2 (by rfl) ⟨2184000, by rfl⟩ : syracuseStep 5824001 = 4368001) B4368001
theorem B3882667 : Blo 2299435 3882667 := bstep (se 1 (by rfl) ⟨2912000, by rfl⟩ : syracuseStep 3882667 = 5824001) B5824001
theorem B5176889 : Blo 2299435 5176889 := bstep (se 2 (by rfl) ⟨1941333, by rfl⟩ : syracuseStep 5176889 = 3882667) B3882667
theorem B3451259 : Blo 2299435 3451259 := bstep (se 1 (by rfl) ⟨2588444, by rfl⟩ : syracuseStep 3451259 = 5176889) B5176889
theorem B2300839 : Blo 2299435 2300839 := bstep (se 1 (by rfl) ⟨1725629, by rfl⟩ : syracuseStep 2300839 = 3451259) B3451259
theorem B2588449 : Blo 2299435 2588449 := bbase (se 2 (by rfl) ⟨970668, by rfl⟩ : syracuseStep 2588449 = 1941337) (by norm_num)
theorem B3451265 : Blo 2299435 3451265 := bstep (se 2 (by rfl) ⟨1294224, by rfl⟩ : syracuseStep 3451265 = 2588449) B2588449
theorem B2300843 : Blo 2299435 2300843 := bstep (se 1 (by rfl) ⟨1725632, by rfl⟩ : syracuseStep 2300843 = 3451265) B3451265
theorem B5824021 : Blo 2299435 5824021 := bbase (se 6 (by rfl) ⟨136500, by rfl⟩ : syracuseStep 5824021 = 273001) (by norm_num)
theorem B7765361 : Blo 2299435 7765361 := bstep (se 2 (by rfl) ⟨2912010, by rfl⟩ : syracuseStep 7765361 = 5824021) B5824021
theorem B5176907 : Blo 2299435 5176907 := bstep (se 1 (by rfl) ⟨3882680, by rfl⟩ : syracuseStep 5176907 = 7765361) B7765361
theorem B3451271 : Blo 2299435 3451271 := bstep (se 1 (by rfl) ⟨2588453, by rfl⟩ : syracuseStep 3451271 = 5176907) B5176907
theorem B2300847 : Blo 2299435 2300847 := bstep (se 1 (by rfl) ⟨1725635, by rfl⟩ : syracuseStep 2300847 = 3451271) B3451271
theorem B3451277 : Blo 2299435 3451277 := bbase (se 3 (by rfl) ⟨647114, by rfl⟩ : syracuseStep 3451277 = 1294229) (by norm_num)
theorem B2300851 : Blo 2299435 2300851 := bstep (se 1 (by rfl) ⟨1725638, by rfl⟩ : syracuseStep 2300851 = 3451277) B3451277
theorem B5176925 : Blo 2299435 5176925 := bbase (se 3 (by rfl) ⟨970673, by rfl⟩ : syracuseStep 5176925 = 1941347) (by norm_num)
theorem B3451283 : Blo 2299435 3451283 := bstep (se 1 (by rfl) ⟨2588462, by rfl⟩ : syracuseStep 3451283 = 5176925) B5176925
theorem B2300855 : Blo 2299435 2300855 := bstep (se 1 (by rfl) ⟨1725641, by rfl⟩ : syracuseStep 2300855 = 3451283) B3451283
theorem B3882701 : Blo 2299435 3882701 := bbase (se 3 (by rfl) ⟨728006, by rfl⟩ : syracuseStep 3882701 = 1456013) (by norm_num)
theorem B2588467 : Blo 2299435 2588467 := bstep (se 1 (by rfl) ⟨1941350, by rfl⟩ : syracuseStep 2588467 = 3882701) B3882701
theorem B3451289 : Blo 2299435 3451289 := bstep (se 2 (by rfl) ⟨1294233, by rfl⟩ : syracuseStep 3451289 = 2588467) B2588467
theorem B2300859 : Blo 2299435 2300859 := bstep (se 1 (by rfl) ⟨1725644, by rfl⟩ : syracuseStep 2300859 = 3451289) B3451289
theorem B5528309 : Blo 2299435 5528309 := bbase (se 5 (by rfl) ⟨259139, by rfl⟩ : syracuseStep 5528309 = 518279) (by norm_num)
theorem B14742157 : Blo 2299435 14742157 := bstep (se 3 (by rfl) ⟨2764154, by rfl⟩ : syracuseStep 14742157 = 5528309) B5528309
theorem B19656209 : Blo 2299435 19656209 := bstep (se 2 (by rfl) ⟨7371078, by rfl⟩ : syracuseStep 19656209 = 14742157) B14742157
theorem B13104139 : Blo 2299435 13104139 := bstep (se 1 (by rfl) ⟨9828104, by rfl⟩ : syracuseStep 13104139 = 19656209) B19656209
theorem B17472185 : Blo 2299435 17472185 := bstep (se 2 (by rfl) ⟨6552069, by rfl⟩ : syracuseStep 17472185 = 13104139) B13104139
theorem B11648123 : Blo 2299435 11648123 := bstep (se 1 (by rfl) ⟨8736092, by rfl⟩ : syracuseStep 11648123 = 17472185) B17472185
theorem B7765415 : Blo 2299435 7765415 := bstep (se 1 (by rfl) ⟨5824061, by rfl⟩ : syracuseStep 7765415 = 11648123) B11648123
theorem B5176943 : Blo 2299435 5176943 := bstep (se 1 (by rfl) ⟨3882707, by rfl⟩ : syracuseStep 5176943 = 7765415) B7765415
theorem B3451295 : Blo 2299435 3451295 := bstep (se 1 (by rfl) ⟨2588471, by rfl⟩ : syracuseStep 3451295 = 5176943) B5176943
theorem B2300863 : Blo 2299435 2300863 := bstep (se 1 (by rfl) ⟨1725647, by rfl⟩ : syracuseStep 2300863 = 3451295) B3451295
theorem B3451301 : Blo 2299435 3451301 := bbase (se 4 (by rfl) ⟨323559, by rfl⟩ : syracuseStep 3451301 = 647119) (by norm_num)
theorem B2300867 : Blo 2299435 2300867 := bstep (se 1 (by rfl) ⟨1725650, by rfl⟩ : syracuseStep 2300867 = 3451301) B3451301
theorem B2912041 : Blo 2299435 2912041 := bbase (se 2 (by rfl) ⟨1092015, by rfl⟩ : syracuseStep 2912041 = 2184031) (by norm_num)
theorem B3882721 : Blo 2299435 3882721 := bstep (se 2 (by rfl) ⟨1456020, by rfl⟩ : syracuseStep 3882721 = 2912041) B2912041
theorem B5176961 : Blo 2299435 5176961 := bstep (se 2 (by rfl) ⟨1941360, by rfl⟩ : syracuseStep 5176961 = 3882721) B3882721
theorem B3451307 : Blo 2299435 3451307 := bstep (se 1 (by rfl) ⟨2588480, by rfl⟩ : syracuseStep 3451307 = 5176961) B5176961
theorem B2300871 : Blo 2299435 2300871 := bstep (se 1 (by rfl) ⟨1725653, by rfl⟩ : syracuseStep 2300871 = 3451307) B3451307
theorem B2588485 : Blo 2299435 2588485 := bbase (se 4 (by rfl) ⟨242670, by rfl⟩ : syracuseStep 2588485 = 485341) (by norm_num)
theorem B3451313 : Blo 2299435 3451313 := bstep (se 2 (by rfl) ⟨1294242, by rfl⟩ : syracuseStep 3451313 = 2588485) B2588485
theorem B2300875 : Blo 2299435 2300875 := bstep (se 1 (by rfl) ⟨1725656, by rfl⟩ : syracuseStep 2300875 = 3451313) B3451313
theorem B4368077 : Blo 2299435 4368077 := bbase (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) (by norm_num)
theorem B2912051 : Blo 2299435 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B7765469 : Blo 2299435 7765469 := bstep (se 3 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 7765469 = 2912051) B2912051
theorem B5176979 : Blo 2299435 5176979 := bstep (se 1 (by rfl) ⟨3882734, by rfl⟩ : syracuseStep 5176979 = 7765469) B7765469
theorem B3451319 : Blo 2299435 3451319 := bstep (se 1 (by rfl) ⟨2588489, by rfl⟩ : syracuseStep 3451319 = 5176979) B5176979
theorem B2300879 : Blo 2299435 2300879 := bstep (se 1 (by rfl) ⟨1725659, by rfl⟩ : syracuseStep 2300879 = 3451319) B3451319
theorem B3451325 : Blo 2299435 3451325 := bbase (se 3 (by rfl) ⟨647123, by rfl⟩ : syracuseStep 3451325 = 1294247) (by norm_num)
theorem B2300883 : Blo 2299435 2300883 := bstep (se 1 (by rfl) ⟨1725662, by rfl⟩ : syracuseStep 2300883 = 3451325) B3451325
theorem B5176997 : Blo 2299435 5176997 := bbase (se 4 (by rfl) ⟨485343, by rfl⟩ : syracuseStep 5176997 = 970687) (by norm_num)
theorem B3451331 : Blo 2299435 3451331 := bstep (se 1 (by rfl) ⟨2588498, by rfl⟩ : syracuseStep 3451331 = 5176997) B5176997
theorem B2300887 : Blo 2299435 2300887 := bstep (se 1 (by rfl) ⟨1725665, by rfl⟩ : syracuseStep 2300887 = 3451331) B3451331
theorem B5824133 : Blo 2299435 5824133 := bbase (se 4 (by rfl) ⟨546012, by rfl⟩ : syracuseStep 5824133 = 1092025) (by norm_num)
theorem B3882755 : Blo 2299435 3882755 := bstep (se 1 (by rfl) ⟨2912066, by rfl⟩ : syracuseStep 3882755 = 5824133) B5824133
theorem B2588503 : Blo 2299435 2588503 := bstep (se 1 (by rfl) ⟨1941377, by rfl⟩ : syracuseStep 2588503 = 3882755) B3882755
theorem B3451337 : Blo 2299435 3451337 := bstep (se 2 (by rfl) ⟨1294251, by rfl⟩ : syracuseStep 3451337 = 2588503) B2588503
theorem B2300891 : Blo 2299435 2300891 := bstep (se 1 (by rfl) ⟨1725668, by rfl⟩ : syracuseStep 2300891 = 3451337) B3451337
theorem B8292581 : Blo 2299435 8292581 := bbase (se 4 (by rfl) ⟨777429, by rfl⟩ : syracuseStep 8292581 = 1554859) (by norm_num)
theorem B5528387 : Blo 2299435 5528387 := bstep (se 1 (by rfl) ⟨4146290, by rfl⟩ : syracuseStep 5528387 = 8292581) B8292581
theorem B3685591 : Blo 2299435 3685591 := bstep (se 1 (by rfl) ⟨2764193, by rfl⟩ : syracuseStep 3685591 = 5528387) B5528387
theorem B4914121 : Blo 2299435 4914121 := bstep (se 2 (by rfl) ⟨1842795, by rfl⟩ : syracuseStep 4914121 = 3685591) B3685591
theorem B6552161 : Blo 2299435 6552161 := bstep (se 2 (by rfl) ⟨2457060, by rfl⟩ : syracuseStep 6552161 = 4914121) B4914121
theorem B4368107 : Blo 2299435 4368107 := bstep (se 1 (by rfl) ⟨3276080, by rfl⟩ : syracuseStep 4368107 = 6552161) B6552161
theorem B11648285 : Blo 2299435 11648285 := bstep (se 3 (by rfl) ⟨2184053, by rfl⟩ : syracuseStep 11648285 = 4368107) B4368107
theorem B7765523 : Blo 2299435 7765523 := bstep (se 1 (by rfl) ⟨5824142, by rfl⟩ : syracuseStep 7765523 = 11648285) B11648285
theorem B5177015 : Blo 2299435 5177015 := bstep (se 1 (by rfl) ⟨3882761, by rfl⟩ : syracuseStep 5177015 = 7765523) B7765523
theorem B3451343 : Blo 2299435 3451343 := bstep (se 1 (by rfl) ⟨2588507, by rfl⟩ : syracuseStep 3451343 = 5177015) B5177015
theorem B2300895 : Blo 2299435 2300895 := bstep (se 1 (by rfl) ⟨1725671, by rfl⟩ : syracuseStep 2300895 = 3451343) B3451343
theorem B3451349 : Blo 2299435 3451349 := bbase (se 7 (by rfl) ⟨40445, by rfl⟩ : syracuseStep 3451349 = 80891) (by norm_num)
theorem B2300899 : Blo 2299435 2300899 := bstep (se 1 (by rfl) ⟨1725674, by rfl⟩ : syracuseStep 2300899 = 3451349) B3451349
theorem B8736245 : Blo 2299435 8736245 := bbase (se 5 (by rfl) ⟨409511, by rfl⟩ : syracuseStep 8736245 = 819023) (by norm_num)
theorem B5824163 : Blo 2299435 5824163 := bstep (se 1 (by rfl) ⟨4368122, by rfl⟩ : syracuseStep 5824163 = 8736245) B8736245
theorem B3882775 : Blo 2299435 3882775 := bstep (se 1 (by rfl) ⟨2912081, by rfl⟩ : syracuseStep 3882775 = 5824163) B5824163
theorem B5177033 : Blo 2299435 5177033 := bstep (se 2 (by rfl) ⟨1941387, by rfl⟩ : syracuseStep 5177033 = 3882775) B3882775
theorem B3451355 : Blo 2299435 3451355 := bstep (se 1 (by rfl) ⟨2588516, by rfl⟩ : syracuseStep 3451355 = 5177033) B5177033
theorem B2300903 : Blo 2299435 2300903 := bstep (se 1 (by rfl) ⟨1725677, by rfl⟩ : syracuseStep 2300903 = 3451355) B3451355
theorem B2588521 : Blo 2299435 2588521 := bbase (se 2 (by rfl) ⟨970695, by rfl⟩ : syracuseStep 2588521 = 1941391) (by norm_num)
theorem B3451361 : Blo 2299435 3451361 := bstep (se 2 (by rfl) ⟨1294260, by rfl⟩ : syracuseStep 3451361 = 2588521) B2588521
theorem B2300907 : Blo 2299435 2300907 := bstep (se 1 (by rfl) ⟨1725680, by rfl⟩ : syracuseStep 2300907 = 3451361) B3451361
theorem B3935765 : Blo 2299435 3935765 := bbase (se 6 (by rfl) ⟨92244, by rfl⟩ : syracuseStep 3935765 = 184489) (by norm_num)
theorem B2623843 : Blo 2299435 2623843 := bstep (se 1 (by rfl) ⟨1967882, by rfl⟩ : syracuseStep 2623843 = 3935765) B3935765
theorem B13993829 : Blo 2299435 13993829 := bstep (se 4 (by rfl) ⟨1311921, by rfl⟩ : syracuseStep 13993829 = 2623843) B2623843
theorem B9329219 : Blo 2299435 9329219 := bstep (se 1 (by rfl) ⟨6996914, by rfl⟩ : syracuseStep 9329219 = 13993829) B13993829
theorem B6219479 : Blo 2299435 6219479 := bstep (se 1 (by rfl) ⟨4664609, by rfl⟩ : syracuseStep 6219479 = 9329219) B9329219
theorem B4146319 : Blo 2299435 4146319 := bstep (se 1 (by rfl) ⟨3109739, by rfl⟩ : syracuseStep 4146319 = 6219479) B6219479
theorem B5528425 : Blo 2299435 5528425 := bstep (se 2 (by rfl) ⟨2073159, by rfl⟩ : syracuseStep 5528425 = 4146319) B4146319
theorem B7371233 : Blo 2299435 7371233 := bstep (se 2 (by rfl) ⟨2764212, by rfl⟩ : syracuseStep 7371233 = 5528425) B5528425
theorem B4914155 : Blo 2299435 4914155 := bstep (se 1 (by rfl) ⟨3685616, by rfl⟩ : syracuseStep 4914155 = 7371233) B7371233
theorem B13104413 : Blo 2299435 13104413 := bstep (se 3 (by rfl) ⟨2457077, by rfl⟩ : syracuseStep 13104413 = 4914155) B4914155
theorem B8736275 : Blo 2299435 8736275 := bstep (se 1 (by rfl) ⟨6552206, by rfl⟩ : syracuseStep 8736275 = 13104413) B13104413
theorem B5824183 : Blo 2299435 5824183 := bstep (se 1 (by rfl) ⟨4368137, by rfl⟩ : syracuseStep 5824183 = 8736275) B8736275
theorem B7765577 : Blo 2299435 7765577 := bstep (se 2 (by rfl) ⟨2912091, by rfl⟩ : syracuseStep 7765577 = 5824183) B5824183
theorem B5177051 : Blo 2299435 5177051 := bstep (se 1 (by rfl) ⟨3882788, by rfl⟩ : syracuseStep 5177051 = 7765577) B7765577
theorem B3451367 : Blo 2299435 3451367 := bstep (se 1 (by rfl) ⟨2588525, by rfl⟩ : syracuseStep 3451367 = 5177051) B5177051
theorem B2300911 : Blo 2299435 2300911 := bstep (se 1 (by rfl) ⟨1725683, by rfl⟩ : syracuseStep 2300911 = 3451367) B3451367
theorem B3451373 : Blo 2299435 3451373 := bbase (se 3 (by rfl) ⟨647132, by rfl⟩ : syracuseStep 3451373 = 1294265) (by norm_num)
theorem B2300915 : Blo 2299435 2300915 := bstep (se 1 (by rfl) ⟨1725686, by rfl⟩ : syracuseStep 2300915 = 3451373) B3451373
theorem B5177069 : Blo 2299435 5177069 := bbase (se 3 (by rfl) ⟨970700, by rfl⟩ : syracuseStep 5177069 = 1941401) (by norm_num)
theorem B3451379 : Blo 2299435 3451379 := bstep (se 1 (by rfl) ⟨2588534, by rfl⟩ : syracuseStep 3451379 = 5177069) B5177069
theorem B2300919 : Blo 2299435 2300919 := bstep (se 1 (by rfl) ⟨1725689, by rfl⟩ : syracuseStep 2300919 = 3451379) B3451379
theorem B3685637 : Blo 2299435 3685637 := bbase (se 4 (by rfl) ⟨345528, by rfl⟩ : syracuseStep 3685637 = 691057) (by norm_num)
theorem B2457091 : Blo 2299435 2457091 := bstep (se 1 (by rfl) ⟨1842818, by rfl⟩ : syracuseStep 2457091 = 3685637) B3685637
theorem B3276121 : Blo 2299435 3276121 := bstep (se 2 (by rfl) ⟨1228545, by rfl⟩ : syracuseStep 3276121 = 2457091) B2457091
theorem B4368161 : Blo 2299435 4368161 := bstep (se 2 (by rfl) ⟨1638060, by rfl⟩ : syracuseStep 4368161 = 3276121) B3276121
theorem B2912107 : Blo 2299435 2912107 := bstep (se 1 (by rfl) ⟨2184080, by rfl⟩ : syracuseStep 2912107 = 4368161) B4368161
theorem B3882809 : Blo 2299435 3882809 := bstep (se 2 (by rfl) ⟨1456053, by rfl⟩ : syracuseStep 3882809 = 2912107) B2912107
theorem B2588539 : Blo 2299435 2588539 := bstep (se 1 (by rfl) ⟨1941404, by rfl⟩ : syracuseStep 2588539 = 3882809) B3882809
theorem B3451385 : Blo 2299435 3451385 := bstep (se 2 (by rfl) ⟨1294269, by rfl⟩ : syracuseStep 3451385 = 2588539) B2588539
theorem B2300923 : Blo 2299435 2300923 := bstep (se 1 (by rfl) ⟨1725692, by rfl⟩ : syracuseStep 2300923 = 3451385) B3451385
theorem B2801945 : Blo 2299435 2801945 := bbase (se 2 (by rfl) ⟨1050729, by rfl⟩ : syracuseStep 2801945 = 2101459) (by norm_num)
theorem B7471853 : Blo 2299435 7471853 := bstep (se 3 (by rfl) ⟨1400972, by rfl⟩ : syracuseStep 7471853 = 2801945) B2801945
theorem B4981235 : Blo 2299435 4981235 := bstep (se 1 (by rfl) ⟨3735926, by rfl⟩ : syracuseStep 4981235 = 7471853) B7471853
theorem B13283293 : Blo 2299435 13283293 := bstep (se 3 (by rfl) ⟨2490617, by rfl⟩ : syracuseStep 13283293 = 4981235) B4981235
theorem B17711057 : Blo 2299435 17711057 := bstep (se 2 (by rfl) ⟨6641646, by rfl⟩ : syracuseStep 17711057 = 13283293) B13283293
theorem B11807371 : Blo 2299435 11807371 := bstep (se 1 (by rfl) ⟨8855528, by rfl⟩ : syracuseStep 11807371 = 17711057) B17711057
theorem B62972645 : Blo 2299435 62972645 := bstep (se 4 (by rfl) ⟨5903685, by rfl⟩ : syracuseStep 62972645 = 11807371) B11807371
theorem B167927053 : Blo 2299435 167927053 := bstep (se 3 (by rfl) ⟨31486322, by rfl⟩ : syracuseStep 167927053 = 62972645) B62972645
theorem B223902737 : Blo 2299435 223902737 := bstep (se 2 (by rfl) ⟨83963526, by rfl⟩ : syracuseStep 223902737 = 167927053) B167927053
theorem B149268491 : Blo 2299435 149268491 := bstep (se 1 (by rfl) ⟨111951368, by rfl⟩ : syracuseStep 149268491 = 223902737) B223902737
theorem B99512327 : Blo 2299435 99512327 := bstep (se 1 (by rfl) ⟨74634245, by rfl⟩ : syracuseStep 99512327 = 149268491) B149268491
theorem B66341551 : Blo 2299435 66341551 := bstep (se 1 (by rfl) ⟨49756163, by rfl⟩ : syracuseStep 66341551 = 99512327) B99512327
theorem B88455401 : Blo 2299435 88455401 := bstep (se 2 (by rfl) ⟨33170775, by rfl⟩ : syracuseStep 88455401 = 66341551) B66341551
theorem B58970267 : Blo 2299435 58970267 := bstep (se 1 (by rfl) ⟨44227700, by rfl⟩ : syracuseStep 58970267 = 88455401) B88455401
theorem B39313511 : Blo 2299435 39313511 := bstep (se 1 (by rfl) ⟨29485133, by rfl⟩ : syracuseStep 39313511 = 58970267) B58970267
theorem B26209007 : Blo 2299435 26209007 := bstep (se 1 (by rfl) ⟨19656755, by rfl⟩ : syracuseStep 26209007 = 39313511) B39313511
theorem B17472671 : Blo 2299435 17472671 := bstep (se 1 (by rfl) ⟨13104503, by rfl⟩ : syracuseStep 17472671 = 26209007) B26209007
theorem B11648447 : Blo 2299435 11648447 := bstep (se 1 (by rfl) ⟨8736335, by rfl⟩ : syracuseStep 11648447 = 17472671) B17472671
theorem B7765631 : Blo 2299435 7765631 := bstep (se 1 (by rfl) ⟨5824223, by rfl⟩ : syracuseStep 7765631 = 11648447) B11648447
theorem B5177087 : Blo 2299435 5177087 := bstep (se 1 (by rfl) ⟨3882815, by rfl⟩ : syracuseStep 5177087 = 7765631) B7765631
theorem B3451391 : Blo 2299435 3451391 := bstep (se 1 (by rfl) ⟨2588543, by rfl⟩ : syracuseStep 3451391 = 5177087) B5177087
theorem B2300927 : Blo 2299435 2300927 := bstep (se 1 (by rfl) ⟨1725695, by rfl⟩ : syracuseStep 2300927 = 3451391) B3451391
theorem B3451397 : Blo 2299435 3451397 := bbase (se 4 (by rfl) ⟨323568, by rfl⟩ : syracuseStep 3451397 = 647137) (by norm_num)
theorem B2300931 : Blo 2299435 2300931 := bstep (se 1 (by rfl) ⟨1725698, by rfl⟩ : syracuseStep 2300931 = 3451397) B3451397
theorem B3882829 : Blo 2299435 3882829 := bbase (se 3 (by rfl) ⟨728030, by rfl⟩ : syracuseStep 3882829 = 1456061) (by norm_num)
theorem B5177105 : Blo 2299435 5177105 := bstep (se 2 (by rfl) ⟨1941414, by rfl⟩ : syracuseStep 5177105 = 3882829) B3882829
theorem B3451403 : Blo 2299435 3451403 := bstep (se 1 (by rfl) ⟨2588552, by rfl⟩ : syracuseStep 3451403 = 5177105) B5177105
theorem B2300935 : Blo 2299435 2300935 := bstep (se 1 (by rfl) ⟨1725701, by rfl⟩ : syracuseStep 2300935 = 3451403) B3451403
theorem B2588557 : Blo 2299435 2588557 := bbase (se 3 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 2588557 = 970709) (by norm_num)
theorem B3451409 : Blo 2299435 3451409 := bstep (se 2 (by rfl) ⟨1294278, by rfl⟩ : syracuseStep 3451409 = 2588557) B2588557
theorem B2300939 : Blo 2299435 2300939 := bstep (se 1 (by rfl) ⟨1725704, by rfl⟩ : syracuseStep 2300939 = 3451409) B3451409
theorem B7765685 : Blo 2299435 7765685 := bbase (se 5 (by rfl) ⟨364016, by rfl⟩ : syracuseStep 7765685 = 728033) (by norm_num)
theorem B5177123 : Blo 2299435 5177123 := bstep (se 1 (by rfl) ⟨3882842, by rfl⟩ : syracuseStep 5177123 = 7765685) B7765685
theorem B3451415 : Blo 2299435 3451415 := bstep (se 1 (by rfl) ⟨2588561, by rfl⟩ : syracuseStep 3451415 = 5177123) B5177123
theorem B2300943 : Blo 2299435 2300943 := bstep (se 1 (by rfl) ⟨1725707, by rfl⟩ : syracuseStep 2300943 = 3451415) B3451415
theorem B3451421 : Blo 2299435 3451421 := bbase (se 3 (by rfl) ⟨647141, by rfl⟩ : syracuseStep 3451421 = 1294283) (by norm_num)
theorem B2300947 : Blo 2299435 2300947 := bstep (se 1 (by rfl) ⟨1725710, by rfl⟩ : syracuseStep 2300947 = 3451421) B3451421
theorem B5177141 : Blo 2299435 5177141 := bbase (se 5 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 5177141 = 485357) (by norm_num)
theorem B3451427 : Blo 2299435 3451427 := bstep (se 1 (by rfl) ⟨2588570, by rfl⟩ : syracuseStep 3451427 = 5177141) B5177141
theorem B2300951 : Blo 2299435 2300951 := bstep (se 1 (by rfl) ⟨1725713, by rfl⟩ : syracuseStep 2300951 = 3451427) B3451427
theorem B4427821 : Blo 2299435 4427821 := bbase (se 3 (by rfl) ⟨830216, by rfl⟩ : syracuseStep 4427821 = 1660433) (by norm_num)
theorem B5903761 : Blo 2299435 5903761 := bstep (se 2 (by rfl) ⟨2213910, by rfl⟩ : syracuseStep 5903761 = 4427821) B4427821
theorem B7871681 : Blo 2299435 7871681 := bstep (se 2 (by rfl) ⟨2951880, by rfl⟩ : syracuseStep 7871681 = 5903761) B5903761
theorem B5247787 : Blo 2299435 5247787 := bstep (se 1 (by rfl) ⟨3935840, by rfl⟩ : syracuseStep 5247787 = 7871681) B7871681
theorem B6997049 : Blo 2299435 6997049 := bstep (se 2 (by rfl) ⟨2623893, by rfl⟩ : syracuseStep 6997049 = 5247787) B5247787
theorem B4664699 : Blo 2299435 4664699 := bstep (se 1 (by rfl) ⟨3498524, by rfl⟩ : syracuseStep 4664699 = 6997049) B6997049
theorem B3109799 : Blo 2299435 3109799 := bstep (se 1 (by rfl) ⟨2332349, by rfl⟩ : syracuseStep 3109799 = 4664699) B4664699
theorem B8292797 : Blo 2299435 8292797 := bstep (se 3 (by rfl) ⟨1554899, by rfl⟩ : syracuseStep 8292797 = 3109799) B3109799
theorem B5528531 : Blo 2299435 5528531 := bstep (se 1 (by rfl) ⟨4146398, by rfl⟩ : syracuseStep 5528531 = 8292797) B8292797
theorem B14742749 : Blo 2299435 14742749 := bstep (se 3 (by rfl) ⟨2764265, by rfl⟩ : syracuseStep 14742749 = 5528531) B5528531
theorem B9828499 : Blo 2299435 9828499 := bstep (se 1 (by rfl) ⟨7371374, by rfl⟩ : syracuseStep 9828499 = 14742749) B14742749
theorem B13104665 : Blo 2299435 13104665 := bstep (se 2 (by rfl) ⟨4914249, by rfl⟩ : syracuseStep 13104665 = 9828499) B9828499
theorem B8736443 : Blo 2299435 8736443 := bstep (se 1 (by rfl) ⟨6552332, by rfl⟩ : syracuseStep 8736443 = 13104665) B13104665
theorem B5824295 : Blo 2299435 5824295 := bstep (se 1 (by rfl) ⟨4368221, by rfl⟩ : syracuseStep 5824295 = 8736443) B8736443
theorem B3882863 : Blo 2299435 3882863 := bstep (se 1 (by rfl) ⟨2912147, by rfl⟩ : syracuseStep 3882863 = 5824295) B5824295
theorem B2588575 : Blo 2299435 2588575 := bstep (se 1 (by rfl) ⟨1941431, by rfl⟩ : syracuseStep 2588575 = 3882863) B3882863
theorem B3451433 : Blo 2299435 3451433 := bstep (se 2 (by rfl) ⟨1294287, by rfl⟩ : syracuseStep 3451433 = 2588575) B2588575
theorem B2300955 : Blo 2299435 2300955 := bstep (se 1 (by rfl) ⟨1725716, by rfl⟩ : syracuseStep 2300955 = 3451433) B3451433
theorem B14742773 : Blo 2299435 14742773 := bbase (se 5 (by rfl) ⟨691067, by rfl⟩ : syracuseStep 14742773 = 1382135) (by norm_num)
theorem B9828515 : Blo 2299435 9828515 := bstep (se 1 (by rfl) ⟨7371386, by rfl⟩ : syracuseStep 9828515 = 14742773) B14742773
theorem B6552343 : Blo 2299435 6552343 := bstep (se 1 (by rfl) ⟨4914257, by rfl⟩ : syracuseStep 6552343 = 9828515) B9828515
theorem B8736457 : Blo 2299435 8736457 := bstep (se 2 (by rfl) ⟨3276171, by rfl⟩ : syracuseStep 8736457 = 6552343) B6552343
theorem B11648609 : Blo 2299435 11648609 := bstep (se 2 (by rfl) ⟨4368228, by rfl⟩ : syracuseStep 11648609 = 8736457) B8736457
theorem B7765739 : Blo 2299435 7765739 := bstep (se 1 (by rfl) ⟨5824304, by rfl⟩ : syracuseStep 7765739 = 11648609) B11648609
theorem B5177159 : Blo 2299435 5177159 := bstep (se 1 (by rfl) ⟨3882869, by rfl⟩ : syracuseStep 5177159 = 7765739) B7765739
theorem B3451439 : Blo 2299435 3451439 := bstep (se 1 (by rfl) ⟨2588579, by rfl⟩ : syracuseStep 3451439 = 5177159) B5177159
theorem B2300959 : Blo 2299435 2300959 := bstep (se 1 (by rfl) ⟨1725719, by rfl⟩ : syracuseStep 2300959 = 3451439) B3451439
theorem B3451445 : Blo 2299435 3451445 := bbase (se 5 (by rfl) ⟨161786, by rfl⟩ : syracuseStep 3451445 = 323573) (by norm_num)
theorem B2300963 : Blo 2299435 2300963 := bstep (se 1 (by rfl) ⟨1725722, by rfl⟩ : syracuseStep 2300963 = 3451445) B3451445
theorem B5824325 : Blo 2299435 5824325 := bbase (se 4 (by rfl) ⟨546030, by rfl⟩ : syracuseStep 5824325 = 1092061) (by norm_num)
theorem B3882883 : Blo 2299435 3882883 := bstep (se 1 (by rfl) ⟨2912162, by rfl⟩ : syracuseStep 3882883 = 5824325) B5824325
theorem B5177177 : Blo 2299435 5177177 := bstep (se 2 (by rfl) ⟨1941441, by rfl⟩ : syracuseStep 5177177 = 3882883) B3882883
theorem B3451451 : Blo 2299435 3451451 := bstep (se 1 (by rfl) ⟨2588588, by rfl⟩ : syracuseStep 3451451 = 5177177) B5177177
theorem B2300967 : Blo 2299435 2300967 := bstep (se 1 (by rfl) ⟨1725725, by rfl⟩ : syracuseStep 2300967 = 3451451) B3451451
theorem B2588593 : Blo 2299435 2588593 := bbase (se 2 (by rfl) ⟨970722, by rfl⟩ : syracuseStep 2588593 = 1941445) (by norm_num)
theorem B3451457 : Blo 2299435 3451457 := bstep (se 2 (by rfl) ⟨1294296, by rfl⟩ : syracuseStep 3451457 = 2588593) B2588593
theorem B2300971 : Blo 2299435 2300971 := bstep (se 1 (by rfl) ⟨1725728, by rfl⟩ : syracuseStep 2300971 = 3451457) B3451457
theorem B6552389 : Blo 2299435 6552389 := bbase (se 4 (by rfl) ⟨614286, by rfl⟩ : syracuseStep 6552389 = 1228573) (by norm_num)
theorem B4368259 : Blo 2299435 4368259 := bstep (se 1 (by rfl) ⟨3276194, by rfl⟩ : syracuseStep 4368259 = 6552389) B6552389
theorem B5824345 : Blo 2299435 5824345 := bstep (se 2 (by rfl) ⟨2184129, by rfl⟩ : syracuseStep 5824345 = 4368259) B4368259
theorem B7765793 : Blo 2299435 7765793 := bstep (se 2 (by rfl) ⟨2912172, by rfl⟩ : syracuseStep 7765793 = 5824345) B5824345
theorem B5177195 : Blo 2299435 5177195 := bstep (se 1 (by rfl) ⟨3882896, by rfl⟩ : syracuseStep 5177195 = 7765793) B7765793
theorem B3451463 : Blo 2299435 3451463 := bstep (se 1 (by rfl) ⟨2588597, by rfl⟩ : syracuseStep 3451463 = 5177195) B5177195
theorem B2300975 : Blo 2299435 2300975 := bstep (se 1 (by rfl) ⟨1725731, by rfl⟩ : syracuseStep 2300975 = 3451463) B3451463
theorem B3451469 : Blo 2299435 3451469 := bbase (se 3 (by rfl) ⟨647150, by rfl⟩ : syracuseStep 3451469 = 1294301) (by norm_num)
theorem B2300979 : Blo 2299435 2300979 := bstep (se 1 (by rfl) ⟨1725734, by rfl⟩ : syracuseStep 2300979 = 3451469) B3451469
theorem B5177213 : Blo 2299435 5177213 := bbase (se 3 (by rfl) ⟨970727, by rfl⟩ : syracuseStep 5177213 = 1941455) (by norm_num)
theorem B3451475 : Blo 2299435 3451475 := bstep (se 1 (by rfl) ⟨2588606, by rfl⟩ : syracuseStep 3451475 = 5177213) B5177213
theorem B2300983 : Blo 2299435 2300983 := bstep (se 1 (by rfl) ⟨1725737, by rfl⟩ : syracuseStep 2300983 = 3451475) B3451475
theorem B3882917 : Blo 2299435 3882917 := bbase (se 4 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 3882917 = 728047) (by norm_num)
theorem B2588611 : Blo 2299435 2588611 := bstep (se 1 (by rfl) ⟨1941458, by rfl⟩ : syracuseStep 2588611 = 3882917) B3882917
theorem B3451481 : Blo 2299435 3451481 := bstep (se 2 (by rfl) ⟨1294305, by rfl⟩ : syracuseStep 3451481 = 2588611) B2588611
theorem B2300987 : Blo 2299435 2300987 := bstep (se 1 (by rfl) ⟨1725740, by rfl⟩ : syracuseStep 2300987 = 3451481) B3451481
theorem B2764309 : Blo 2299435 2764309 := bbase (se 6 (by rfl) ⟨64788, by rfl⟩ : syracuseStep 2764309 = 129577) (by norm_num)
theorem B3685745 : Blo 2299435 3685745 := bstep (se 2 (by rfl) ⟨1382154, by rfl⟩ : syracuseStep 3685745 = 2764309) B2764309
theorem B2457163 : Blo 2299435 2457163 := bstep (se 1 (by rfl) ⟨1842872, by rfl⟩ : syracuseStep 2457163 = 3685745) B3685745
theorem B3276217 : Blo 2299435 3276217 := bstep (se 2 (by rfl) ⟨1228581, by rfl⟩ : syracuseStep 3276217 = 2457163) B2457163
theorem B17473157 : Blo 2299435 17473157 := bstep (se 4 (by rfl) ⟨1638108, by rfl⟩ : syracuseStep 17473157 = 3276217) B3276217
theorem B11648771 : Blo 2299435 11648771 := bstep (se 1 (by rfl) ⟨8736578, by rfl⟩ : syracuseStep 11648771 = 17473157) B17473157
theorem B7765847 : Blo 2299435 7765847 := bstep (se 1 (by rfl) ⟨5824385, by rfl⟩ : syracuseStep 7765847 = 11648771) B11648771
theorem B5177231 : Blo 2299435 5177231 := bstep (se 1 (by rfl) ⟨3882923, by rfl⟩ : syracuseStep 5177231 = 7765847) B7765847
theorem B3451487 : Blo 2299435 3451487 := bstep (se 1 (by rfl) ⟨2588615, by rfl⟩ : syracuseStep 3451487 = 5177231) B5177231
theorem B2300991 : Blo 2299435 2300991 := bstep (se 1 (by rfl) ⟨1725743, by rfl⟩ : syracuseStep 2300991 = 3451487) B3451487
theorem B3451493 : Blo 2299435 3451493 := bbase (se 4 (by rfl) ⟨323577, by rfl⟩ : syracuseStep 3451493 = 647155) (by norm_num)
theorem B2300995 : Blo 2299435 2300995 := bstep (se 1 (by rfl) ⟨1725746, by rfl⟩ : syracuseStep 2300995 = 3451493) B3451493
theorem B3276229 : Blo 2299435 3276229 := bbase (se 4 (by rfl) ⟨307146, by rfl⟩ : syracuseStep 3276229 = 614293) (by norm_num)
theorem B4368305 : Blo 2299435 4368305 := bstep (se 2 (by rfl) ⟨1638114, by rfl⟩ : syracuseStep 4368305 = 3276229) B3276229
theorem B2912203 : Blo 2299435 2912203 := bstep (se 1 (by rfl) ⟨2184152, by rfl⟩ : syracuseStep 2912203 = 4368305) B4368305
theorem B3882937 : Blo 2299435 3882937 := bstep (se 2 (by rfl) ⟨1456101, by rfl⟩ : syracuseStep 3882937 = 2912203) B2912203
theorem B5177249 : Blo 2299435 5177249 := bstep (se 2 (by rfl) ⟨1941468, by rfl⟩ : syracuseStep 5177249 = 3882937) B3882937
theorem B3451499 : Blo 2299435 3451499 := bstep (se 1 (by rfl) ⟨2588624, by rfl⟩ : syracuseStep 3451499 = 5177249) B5177249
theorem B2300999 : Blo 2299435 2300999 := bstep (se 1 (by rfl) ⟨1725749, by rfl⟩ : syracuseStep 2300999 = 3451499) B3451499
theorem B2588629 : Blo 2299435 2588629 := bbase (se 7 (by rfl) ⟨30335, by rfl⟩ : syracuseStep 2588629 = 60671) (by norm_num)
theorem B3451505 : Blo 2299435 3451505 := bstep (se 2 (by rfl) ⟨1294314, by rfl⟩ : syracuseStep 3451505 = 2588629) B2588629
theorem B2301003 : Blo 2299435 2301003 := bstep (se 1 (by rfl) ⟨1725752, by rfl⟩ : syracuseStep 2301003 = 3451505) B3451505
theorem B2912213 : Blo 2299435 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B7765901 : Blo 2299435 7765901 := bstep (se 3 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 7765901 = 2912213) B2912213
theorem B5177267 : Blo 2299435 5177267 := bstep (se 1 (by rfl) ⟨3882950, by rfl⟩ : syracuseStep 5177267 = 7765901) B7765901
theorem B3451511 : Blo 2299435 3451511 := bstep (se 1 (by rfl) ⟨2588633, by rfl⟩ : syracuseStep 3451511 = 5177267) B5177267
theorem B2301007 : Blo 2299435 2301007 := bstep (se 1 (by rfl) ⟨1725755, by rfl⟩ : syracuseStep 2301007 = 3451511) B3451511
theorem B3451517 : Blo 2299435 3451517 := bbase (se 3 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 3451517 = 1294319) (by norm_num)
theorem B2301011 : Blo 2299435 2301011 := bstep (se 1 (by rfl) ⟨1725758, by rfl⟩ : syracuseStep 2301011 = 3451517) B3451517
theorem B5177285 : Blo 2299435 5177285 := bbase (se 4 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 5177285 = 970741) (by norm_num)
theorem B3451523 : Blo 2299435 3451523 := bstep (se 1 (by rfl) ⟨2588642, by rfl⟩ : syracuseStep 3451523 = 5177285) B5177285
theorem B2301015 : Blo 2299435 2301015 := bstep (se 1 (by rfl) ⟨1725761, by rfl⟩ : syracuseStep 2301015 = 3451523) B3451523
theorem B9828773 : Blo 2299435 9828773 := bbase (se 4 (by rfl) ⟨921447, by rfl⟩ : syracuseStep 9828773 = 1842895) (by norm_num)
theorem B6552515 : Blo 2299435 6552515 := bstep (se 1 (by rfl) ⟨4914386, by rfl⟩ : syracuseStep 6552515 = 9828773) B9828773
theorem B4368343 : Blo 2299435 4368343 := bstep (se 1 (by rfl) ⟨3276257, by rfl⟩ : syracuseStep 4368343 = 6552515) B6552515
theorem B5824457 : Blo 2299435 5824457 := bstep (se 2 (by rfl) ⟨2184171, by rfl⟩ : syracuseStep 5824457 = 4368343) B4368343
theorem B3882971 : Blo 2299435 3882971 := bstep (se 1 (by rfl) ⟨2912228, by rfl⟩ : syracuseStep 3882971 = 5824457) B5824457
theorem B2588647 : Blo 2299435 2588647 := bstep (se 1 (by rfl) ⟨1941485, by rfl⟩ : syracuseStep 2588647 = 3882971) B3882971
theorem B3451529 : Blo 2299435 3451529 := bstep (se 2 (by rfl) ⟨1294323, by rfl⟩ : syracuseStep 3451529 = 2588647) B2588647
theorem B2301019 : Blo 2299435 2301019 := bstep (se 1 (by rfl) ⟨1725764, by rfl⟩ : syracuseStep 2301019 = 3451529) B3451529
theorem B11648933 : Blo 2299435 11648933 := bbase (se 4 (by rfl) ⟨1092087, by rfl⟩ : syracuseStep 11648933 = 2184175) (by norm_num)
theorem B7765955 : Blo 2299435 7765955 := bstep (se 1 (by rfl) ⟨5824466, by rfl⟩ : syracuseStep 7765955 = 11648933) B11648933
theorem B5177303 : Blo 2299435 5177303 := bstep (se 1 (by rfl) ⟨3882977, by rfl⟩ : syracuseStep 5177303 = 7765955) B7765955
theorem B3451535 : Blo 2299435 3451535 := bstep (se 1 (by rfl) ⟨2588651, by rfl⟩ : syracuseStep 3451535 = 5177303) B5177303
theorem B2301023 : Blo 2299435 2301023 := bstep (se 1 (by rfl) ⟨1725767, by rfl⟩ : syracuseStep 2301023 = 3451535) B3451535
theorem B3451541 : Blo 2299435 3451541 := bbase (se 6 (by rfl) ⟨80895, by rfl⟩ : syracuseStep 3451541 = 161791) (by norm_num)
theorem B2301027 : Blo 2299435 2301027 := bstep (se 1 (by rfl) ⟨1725770, by rfl⟩ : syracuseStep 2301027 = 3451541) B3451541
theorem B2802073 : Blo 2299435 2802073 := bbase (se 2 (by rfl) ⟨1050777, by rfl⟩ : syracuseStep 2802073 = 2101555) (by norm_num)
theorem B3736097 : Blo 2299435 3736097 := bstep (se 2 (by rfl) ⟨1401036, by rfl⟩ : syracuseStep 3736097 = 2802073) B2802073
theorem B2490731 : Blo 2299435 2490731 := bstep (se 1 (by rfl) ⟨1868048, by rfl⟩ : syracuseStep 2490731 = 3736097) B3736097
theorem B26567797 : Blo 2299435 26567797 := bstep (se 5 (by rfl) ⟨1245365, by rfl⟩ : syracuseStep 26567797 = 2490731) B2490731
theorem B35423729 : Blo 2299435 35423729 := bstep (se 2 (by rfl) ⟨13283898, by rfl⟩ : syracuseStep 35423729 = 26567797) B26567797
theorem B23615819 : Blo 2299435 23615819 := bstep (se 1 (by rfl) ⟨17711864, by rfl⟩ : syracuseStep 23615819 = 35423729) B35423729
theorem B15743879 : Blo 2299435 15743879 := bstep (se 1 (by rfl) ⟨11807909, by rfl⟩ : syracuseStep 15743879 = 23615819) B23615819
theorem B10495919 : Blo 2299435 10495919 := bstep (se 1 (by rfl) ⟨7871939, by rfl⟩ : syracuseStep 10495919 = 15743879) B15743879
theorem B6997279 : Blo 2299435 6997279 := bstep (se 1 (by rfl) ⟨5247959, by rfl⟩ : syracuseStep 6997279 = 10495919) B10495919
theorem B9329705 : Blo 2299435 9329705 := bstep (se 2 (by rfl) ⟨3498639, by rfl⟩ : syracuseStep 9329705 = 6997279) B6997279
theorem B6219803 : Blo 2299435 6219803 := bstep (se 1 (by rfl) ⟨4664852, by rfl⟩ : syracuseStep 6219803 = 9329705) B9329705
theorem B4146535 : Blo 2299435 4146535 := bstep (se 1 (by rfl) ⟨3109901, by rfl⟩ : syracuseStep 4146535 = 6219803) B6219803
theorem B22114853 : Blo 2299435 22114853 := bstep (se 4 (by rfl) ⟨2073267, by rfl⟩ : syracuseStep 22114853 = 4146535) B4146535
theorem B14743235 : Blo 2299435 14743235 := bstep (se 1 (by rfl) ⟨11057426, by rfl⟩ : syracuseStep 14743235 = 22114853) B22114853
theorem B9828823 : Blo 2299435 9828823 := bstep (se 1 (by rfl) ⟨7371617, by rfl⟩ : syracuseStep 9828823 = 14743235) B14743235
theorem B13105097 : Blo 2299435 13105097 := bstep (se 2 (by rfl) ⟨4914411, by rfl⟩ : syracuseStep 13105097 = 9828823) B9828823
theorem B8736731 : Blo 2299435 8736731 := bstep (se 1 (by rfl) ⟨6552548, by rfl⟩ : syracuseStep 8736731 = 13105097) B13105097
theorem B5824487 : Blo 2299435 5824487 := bstep (se 1 (by rfl) ⟨4368365, by rfl⟩ : syracuseStep 5824487 = 8736731) B8736731
theorem B3882991 : Blo 2299435 3882991 := bstep (se 1 (by rfl) ⟨2912243, by rfl⟩ : syracuseStep 3882991 = 5824487) B5824487
theorem B5177321 : Blo 2299435 5177321 := bstep (se 2 (by rfl) ⟨1941495, by rfl⟩ : syracuseStep 5177321 = 3882991) B3882991
theorem B3451547 : Blo 2299435 3451547 := bstep (se 1 (by rfl) ⟨2588660, by rfl⟩ : syracuseStep 3451547 = 5177321) B5177321
theorem B2301031 : Blo 2299435 2301031 := bstep (se 1 (by rfl) ⟨1725773, by rfl⟩ : syracuseStep 2301031 = 3451547) B3451547
theorem B2588665 : Blo 2299435 2588665 := bbase (se 2 (by rfl) ⟨970749, by rfl⟩ : syracuseStep 2588665 = 1941499) (by norm_num)
theorem B3451553 : Blo 2299435 3451553 := bstep (se 2 (by rfl) ⟨1294332, by rfl⟩ : syracuseStep 3451553 = 2588665) B2588665
theorem B2301035 : Blo 2299435 2301035 := bstep (se 1 (by rfl) ⟨1725776, by rfl⟩ : syracuseStep 2301035 = 3451553) B3451553
theorem B4260469 : Blo 2299435 4260469 := bbase (se 5 (by rfl) ⟨199709, by rfl⟩ : syracuseStep 4260469 = 399419) (by norm_num)
theorem B5680625 : Blo 2299435 5680625 := bstep (se 2 (by rfl) ⟨2130234, by rfl⟩ : syracuseStep 5680625 = 4260469) B4260469
theorem B15148333 : Blo 2299435 15148333 := bstep (se 3 (by rfl) ⟨2840312, by rfl⟩ : syracuseStep 15148333 = 5680625) B5680625
theorem B20197777 : Blo 2299435 20197777 := bstep (se 2 (by rfl) ⟨7574166, by rfl⟩ : syracuseStep 20197777 = 15148333) B15148333
theorem B26930369 : Blo 2299435 26930369 := bstep (se 2 (by rfl) ⟨10098888, by rfl⟩ : syracuseStep 26930369 = 20197777) B20197777
theorem B17953579 : Blo 2299435 17953579 := bstep (se 1 (by rfl) ⟨13465184, by rfl⟩ : syracuseStep 17953579 = 26930369) B26930369
theorem B23938105 : Blo 2299435 23938105 := bstep (se 2 (by rfl) ⟨8976789, by rfl⟩ : syracuseStep 23938105 = 17953579) B17953579
theorem B31917473 : Blo 2299435 31917473 := bstep (se 2 (by rfl) ⟨11969052, by rfl⟩ : syracuseStep 31917473 = 23938105) B23938105
theorem B21278315 : Blo 2299435 21278315 := bstep (se 1 (by rfl) ⟨15958736, by rfl⟩ : syracuseStep 21278315 = 31917473) B31917473
theorem B14185543 : Blo 2299435 14185543 := bstep (se 1 (by rfl) ⟨10639157, by rfl⟩ : syracuseStep 14185543 = 21278315) B21278315
theorem B18914057 : Blo 2299435 18914057 := bstep (se 2 (by rfl) ⟨7092771, by rfl⟩ : syracuseStep 18914057 = 14185543) B14185543
theorem B12609371 : Blo 2299435 12609371 := bstep (se 1 (by rfl) ⟨9457028, by rfl⟩ : syracuseStep 12609371 = 18914057) B18914057
theorem B33624989 : Blo 2299435 33624989 := bstep (se 3 (by rfl) ⟨6304685, by rfl⟩ : syracuseStep 33624989 = 12609371) B12609371
theorem B22416659 : Blo 2299435 22416659 := bstep (se 1 (by rfl) ⟨16812494, by rfl⟩ : syracuseStep 22416659 = 33624989) B33624989
theorem B14944439 : Blo 2299435 14944439 := bstep (se 1 (by rfl) ⟨11208329, by rfl⟩ : syracuseStep 14944439 = 22416659) B22416659
theorem B9962959 : Blo 2299435 9962959 := bstep (se 1 (by rfl) ⟨7472219, by rfl⟩ : syracuseStep 9962959 = 14944439) B14944439
theorem B13283945 : Blo 2299435 13283945 := bstep (se 2 (by rfl) ⟨4981479, by rfl⟩ : syracuseStep 13283945 = 9962959) B9962959
theorem B8855963 : Blo 2299435 8855963 := bstep (se 1 (by rfl) ⟨6641972, by rfl⟩ : syracuseStep 8855963 = 13283945) B13283945
theorem B5903975 : Blo 2299435 5903975 := bstep (se 1 (by rfl) ⟨4427981, by rfl⟩ : syracuseStep 5903975 = 8855963) B8855963
theorem B15743933 : Blo 2299435 15743933 := bstep (se 3 (by rfl) ⟨2951987, by rfl⟩ : syracuseStep 15743933 = 5903975) B5903975
theorem B10495955 : Blo 2299435 10495955 := bstep (se 1 (by rfl) ⟨7871966, by rfl⟩ : syracuseStep 10495955 = 15743933) B15743933
theorem B6997303 : Blo 2299435 6997303 := bstep (se 1 (by rfl) ⟨5247977, by rfl⟩ : syracuseStep 6997303 = 10495955) B10495955
theorem B9329737 : Blo 2299435 9329737 := bstep (se 2 (by rfl) ⟨3498651, by rfl⟩ : syracuseStep 9329737 = 6997303) B6997303
theorem B12439649 : Blo 2299435 12439649 := bstep (se 2 (by rfl) ⟨4664868, by rfl⟩ : syracuseStep 12439649 = 9329737) B9329737
theorem B8293099 : Blo 2299435 8293099 := bstep (se 1 (by rfl) ⟨6219824, by rfl⟩ : syracuseStep 8293099 = 12439649) B12439649
theorem B11057465 : Blo 2299435 11057465 := bstep (se 2 (by rfl) ⟨4146549, by rfl⟩ : syracuseStep 11057465 = 8293099) B8293099
theorem B7371643 : Blo 2299435 7371643 := bstep (se 1 (by rfl) ⟨5528732, by rfl⟩ : syracuseStep 7371643 = 11057465) B11057465
theorem B9828857 : Blo 2299435 9828857 := bstep (se 2 (by rfl) ⟨3685821, by rfl⟩ : syracuseStep 9828857 = 7371643) B7371643
theorem B6552571 : Blo 2299435 6552571 := bstep (se 1 (by rfl) ⟨4914428, by rfl⟩ : syracuseStep 6552571 = 9828857) B9828857
theorem B8736761 : Blo 2299435 8736761 := bstep (se 2 (by rfl) ⟨3276285, by rfl⟩ : syracuseStep 8736761 = 6552571) B6552571
theorem B5824507 : Blo 2299435 5824507 := bstep (se 1 (by rfl) ⟨4368380, by rfl⟩ : syracuseStep 5824507 = 8736761) B8736761
theorem B7766009 : Blo 2299435 7766009 := bstep (se 2 (by rfl) ⟨2912253, by rfl⟩ : syracuseStep 7766009 = 5824507) B5824507
theorem B5177339 : Blo 2299435 5177339 := bstep (se 1 (by rfl) ⟨3883004, by rfl⟩ : syracuseStep 5177339 = 7766009) B7766009
theorem B3451559 : Blo 2299435 3451559 := bstep (se 1 (by rfl) ⟨2588669, by rfl⟩ : syracuseStep 3451559 = 5177339) B5177339
theorem B2301039 : Blo 2299435 2301039 := bstep (se 1 (by rfl) ⟨1725779, by rfl⟩ : syracuseStep 2301039 = 3451559) B3451559
theorem B3451565 : Blo 2299435 3451565 := bbase (se 3 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 3451565 = 1294337) (by norm_num)
theorem B2301043 : Blo 2299435 2301043 := bstep (se 1 (by rfl) ⟨1725782, by rfl⟩ : syracuseStep 2301043 = 3451565) B3451565
theorem B5177357 : Blo 2299435 5177357 := bbase (se 3 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 5177357 = 1941509) (by norm_num)
theorem B3451571 : Blo 2299435 3451571 := bstep (se 1 (by rfl) ⟨2588678, by rfl⟩ : syracuseStep 3451571 = 5177357) B5177357
theorem B2301047 : Blo 2299435 2301047 := bstep (se 1 (by rfl) ⟨1725785, by rfl⟩ : syracuseStep 2301047 = 3451571) B3451571
theorem B2912269 : Blo 2299435 2912269 := bbase (se 3 (by rfl) ⟨546050, by rfl⟩ : syracuseStep 2912269 = 1092101) (by norm_num)
theorem B3883025 : Blo 2299435 3883025 := bstep (se 2 (by rfl) ⟨1456134, by rfl⟩ : syracuseStep 3883025 = 2912269) B2912269
theorem B2588683 : Blo 2299435 2588683 := bstep (se 1 (by rfl) ⟨1941512, by rfl⟩ : syracuseStep 2588683 = 3883025) B3883025
theorem B3451577 : Blo 2299435 3451577 := bstep (se 2 (by rfl) ⟨1294341, by rfl⟩ : syracuseStep 3451577 = 2588683) B2588683
theorem B2301051 : Blo 2299435 2301051 := bstep (se 1 (by rfl) ⟨1725788, by rfl⟩ : syracuseStep 2301051 = 3451577) B3451577
theorem B7092821 : Blo 2299435 7092821 := bbase (se 8 (by rfl) ⟨41559, by rfl⟩ : syracuseStep 7092821 = 83119) (by norm_num)
theorem B4728547 : Blo 2299435 4728547 := bstep (se 1 (by rfl) ⟨3546410, by rfl⟩ : syracuseStep 4728547 = 7092821) B7092821
theorem B6304729 : Blo 2299435 6304729 := bstep (se 2 (by rfl) ⟨2364273, by rfl⟩ : syracuseStep 6304729 = 4728547) B4728547
theorem B8406305 : Blo 2299435 8406305 := bstep (se 2 (by rfl) ⟨3152364, by rfl⟩ : syracuseStep 8406305 = 6304729) B6304729
theorem B5604203 : Blo 2299435 5604203 := bstep (se 1 (by rfl) ⟨4203152, by rfl⟩ : syracuseStep 5604203 = 8406305) B8406305
theorem B3736135 : Blo 2299435 3736135 := bstep (se 1 (by rfl) ⟨2802101, by rfl⟩ : syracuseStep 3736135 = 5604203) B5604203
theorem B4981513 : Blo 2299435 4981513 := bstep (se 2 (by rfl) ⟨1868067, by rfl⟩ : syracuseStep 4981513 = 3736135) B3736135
theorem B6642017 : Blo 2299435 6642017 := bstep (se 2 (by rfl) ⟨2490756, by rfl⟩ : syracuseStep 6642017 = 4981513) B4981513
theorem B4428011 : Blo 2299435 4428011 := bstep (se 1 (by rfl) ⟨3321008, by rfl⟩ : syracuseStep 4428011 = 6642017) B6642017
theorem B11808029 : Blo 2299435 11808029 := bstep (se 3 (by rfl) ⟨2214005, by rfl⟩ : syracuseStep 11808029 = 4428011) B4428011
theorem B31488077 : Blo 2299435 31488077 := bstep (se 3 (by rfl) ⟨5904014, by rfl⟩ : syracuseStep 31488077 = 11808029) B11808029
theorem B20992051 : Blo 2299435 20992051 := bstep (se 1 (by rfl) ⟨15744038, by rfl⟩ : syracuseStep 20992051 = 31488077) B31488077
theorem B27989401 : Blo 2299435 27989401 := bstep (se 2 (by rfl) ⟨10496025, by rfl⟩ : syracuseStep 27989401 = 20992051) B20992051
theorem B37319201 : Blo 2299435 37319201 := bstep (se 2 (by rfl) ⟨13994700, by rfl⟩ : syracuseStep 37319201 = 27989401) B27989401
theorem B24879467 : Blo 2299435 24879467 := bstep (se 1 (by rfl) ⟨18659600, by rfl⟩ : syracuseStep 24879467 = 37319201) B37319201
theorem B16586311 : Blo 2299435 16586311 := bstep (se 1 (by rfl) ⟨12439733, by rfl⟩ : syracuseStep 16586311 = 24879467) B24879467
theorem B22115081 : Blo 2299435 22115081 := bstep (se 2 (by rfl) ⟨8293155, by rfl⟩ : syracuseStep 22115081 = 16586311) B16586311
theorem B14743387 : Blo 2299435 14743387 := bstep (se 1 (by rfl) ⟨11057540, by rfl⟩ : syracuseStep 14743387 = 22115081) B22115081
theorem B19657849 : Blo 2299435 19657849 := bstep (se 2 (by rfl) ⟨7371693, by rfl⟩ : syracuseStep 19657849 = 14743387) B14743387
theorem B26210465 : Blo 2299435 26210465 := bstep (se 2 (by rfl) ⟨9828924, by rfl⟩ : syracuseStep 26210465 = 19657849) B19657849
theorem B17473643 : Blo 2299435 17473643 := bstep (se 1 (by rfl) ⟨13105232, by rfl⟩ : syracuseStep 17473643 = 26210465) B26210465
theorem B11649095 : Blo 2299435 11649095 := bstep (se 1 (by rfl) ⟨8736821, by rfl⟩ : syracuseStep 11649095 = 17473643) B17473643
theorem B7766063 : Blo 2299435 7766063 := bstep (se 1 (by rfl) ⟨5824547, by rfl⟩ : syracuseStep 7766063 = 11649095) B11649095
theorem B5177375 : Blo 2299435 5177375 := bstep (se 1 (by rfl) ⟨3883031, by rfl⟩ : syracuseStep 5177375 = 7766063) B7766063
theorem B3451583 : Blo 2299435 3451583 := bstep (se 1 (by rfl) ⟨2588687, by rfl⟩ : syracuseStep 3451583 = 5177375) B5177375
theorem B2301055 : Blo 2299435 2301055 := bstep (se 1 (by rfl) ⟨1725791, by rfl⟩ : syracuseStep 2301055 = 3451583) B3451583
theorem B3451589 : Blo 2299435 3451589 := bbase (se 4 (by rfl) ⟨323586, by rfl⟩ : syracuseStep 3451589 = 647173) (by norm_num)
theorem B2301059 : Blo 2299435 2301059 := bstep (se 1 (by rfl) ⟨1725794, by rfl⟩ : syracuseStep 2301059 = 3451589) B3451589
theorem B3883045 : Blo 2299435 3883045 := bbase (se 4 (by rfl) ⟨364035, by rfl⟩ : syracuseStep 3883045 = 728071) (by norm_num)
theorem B5177393 : Blo 2299435 5177393 := bstep (se 2 (by rfl) ⟨1941522, by rfl⟩ : syracuseStep 5177393 = 3883045) B3883045
theorem B3451595 : Blo 2299435 3451595 := bstep (se 1 (by rfl) ⟨2588696, by rfl⟩ : syracuseStep 3451595 = 5177393) B5177393
theorem B2301063 : Blo 2299435 2301063 := bstep (se 1 (by rfl) ⟨1725797, by rfl⟩ : syracuseStep 2301063 = 3451595) B3451595
theorem B2588701 : Blo 2299435 2588701 := bbase (se 3 (by rfl) ⟨485381, by rfl⟩ : syracuseStep 2588701 = 970763) (by norm_num)
theorem B3451601 : Blo 2299435 3451601 := bstep (se 2 (by rfl) ⟨1294350, by rfl⟩ : syracuseStep 3451601 = 2588701) B2588701
theorem B2301067 : Blo 2299435 2301067 := bstep (se 1 (by rfl) ⟨1725800, by rfl⟩ : syracuseStep 2301067 = 3451601) B3451601
theorem B7766117 : Blo 2299435 7766117 := bbase (se 4 (by rfl) ⟨728073, by rfl⟩ : syracuseStep 7766117 = 1456147) (by norm_num)
theorem B5177411 : Blo 2299435 5177411 := bstep (se 1 (by rfl) ⟨3883058, by rfl⟩ : syracuseStep 5177411 = 7766117) B7766117
theorem B3451607 : Blo 2299435 3451607 := bstep (se 1 (by rfl) ⟨2588705, by rfl⟩ : syracuseStep 3451607 = 5177411) B5177411
theorem B2301071 : Blo 2299435 2301071 := bstep (se 1 (by rfl) ⟨1725803, by rfl⟩ : syracuseStep 2301071 = 3451607) B3451607
theorem B3451613 : Blo 2299435 3451613 := bbase (se 3 (by rfl) ⟨647177, by rfl⟩ : syracuseStep 3451613 = 1294355) (by norm_num)
theorem B2301075 : Blo 2299435 2301075 := bstep (se 1 (by rfl) ⟨1725806, by rfl⟩ : syracuseStep 2301075 = 3451613) B3451613
theorem B5177429 : Blo 2299435 5177429 := bbase (se 8 (by rfl) ⟨30336, by rfl⟩ : syracuseStep 5177429 = 60673) (by norm_num)
theorem B3451619 : Blo 2299435 3451619 := bstep (se 1 (by rfl) ⟨2588714, by rfl⟩ : syracuseStep 3451619 = 5177429) B5177429
theorem B2301079 : Blo 2299435 2301079 := bstep (se 1 (by rfl) ⟨1725809, by rfl⟩ : syracuseStep 2301079 = 3451619) B3451619
theorem B6642101 : Blo 2299435 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B17712269 : Blo 2299435 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B11808179 : Blo 2299435 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B7872119 : Blo 2299435 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B5248079 : Blo 2299435 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B3498719 : Blo 2299435 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B9329917 : Blo 2299435 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B12439889 : Blo 2299435 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B8293259 : Blo 2299435 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B5528839 : Blo 2299435 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B7371785 : Blo 2299435 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B4914523 : Blo 2299435 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B6552697 : Blo 2299435 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B8736929 : Blo 2299435 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B5824619 : Blo 2299435 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B3883079 : Blo 2299435 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B2588719 : Blo 2299435 2588719 := bstep (se 1 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 2588719 = 3883079) B3883079
theorem B3451625 : Blo 2299435 3451625 := bstep (se 2 (by rfl) ⟨1294359, by rfl⟩ : syracuseStep 3451625 = 2588719) B2588719
theorem B2301083 : Blo 2299435 2301083 := bstep (se 1 (by rfl) ⟨1725812, by rfl⟩ : syracuseStep 2301083 = 3451625) B3451625
theorem B18659861 : Blo 2299435 18659861 := bbase (se 6 (by rfl) ⟨437340, by rfl⟩ : syracuseStep 18659861 = 874681) (by norm_num)
theorem B12439907 : Blo 2299435 12439907 := bstep (se 1 (by rfl) ⟨9329930, by rfl⟩ : syracuseStep 12439907 = 18659861) B18659861
theorem B8293271 : Blo 2299435 8293271 := bstep (se 1 (by rfl) ⟨6219953, by rfl⟩ : syracuseStep 8293271 = 12439907) B12439907
theorem B22115389 : Blo 2299435 22115389 := bstep (se 3 (by rfl) ⟨4146635, by rfl⟩ : syracuseStep 22115389 = 8293271) B8293271
theorem B29487185 : Blo 2299435 29487185 := bstep (se 2 (by rfl) ⟨11057694, by rfl⟩ : syracuseStep 29487185 = 22115389) B22115389
theorem B19658123 : Blo 2299435 19658123 := bstep (se 1 (by rfl) ⟨14743592, by rfl⟩ : syracuseStep 19658123 = 29487185) B29487185
theorem B13105415 : Blo 2299435 13105415 := bstep (se 1 (by rfl) ⟨9829061, by rfl⟩ : syracuseStep 13105415 = 19658123) B19658123
theorem B8736943 : Blo 2299435 8736943 := bstep (se 1 (by rfl) ⟨6552707, by rfl⟩ : syracuseStep 8736943 = 13105415) B13105415
theorem B11649257 : Blo 2299435 11649257 := bstep (se 2 (by rfl) ⟨4368471, by rfl⟩ : syracuseStep 11649257 = 8736943) B8736943
theorem B7766171 : Blo 2299435 7766171 := bstep (se 1 (by rfl) ⟨5824628, by rfl⟩ : syracuseStep 7766171 = 11649257) B11649257
theorem B5177447 : Blo 2299435 5177447 := bstep (se 1 (by rfl) ⟨3883085, by rfl⟩ : syracuseStep 5177447 = 7766171) B7766171
theorem B3451631 : Blo 2299435 3451631 := bstep (se 1 (by rfl) ⟨2588723, by rfl⟩ : syracuseStep 3451631 = 5177447) B5177447
theorem B2301087 : Blo 2299435 2301087 := bstep (se 1 (by rfl) ⟨1725815, by rfl⟩ : syracuseStep 2301087 = 3451631) B3451631
theorem B3451637 : Blo 2299435 3451637 := bbase (se 5 (by rfl) ⟨161795, by rfl⟩ : syracuseStep 3451637 = 323591) (by norm_num)
theorem B2301091 : Blo 2299435 2301091 := bstep (se 1 (by rfl) ⟨1725818, by rfl⟩ : syracuseStep 2301091 = 3451637) B3451637
theorem B8977013 : Blo 2299435 8977013 := bbase (se 5 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 8977013 = 841595) (by norm_num)
theorem B5984675 : Blo 2299435 5984675 := bstep (se 1 (by rfl) ⟨4488506, by rfl⟩ : syracuseStep 5984675 = 8977013) B8977013
theorem B3989783 : Blo 2299435 3989783 := bstep (se 1 (by rfl) ⟨2992337, by rfl⟩ : syracuseStep 3989783 = 5984675) B5984675
theorem B10639421 : Blo 2299435 10639421 := bstep (se 3 (by rfl) ⟨1994891, by rfl⟩ : syracuseStep 10639421 = 3989783) B3989783
theorem B7092947 : Blo 2299435 7092947 := bstep (se 1 (by rfl) ⟨5319710, by rfl⟩ : syracuseStep 7092947 = 10639421) B10639421
theorem B4728631 : Blo 2299435 4728631 := bstep (se 1 (by rfl) ⟨3546473, by rfl⟩ : syracuseStep 4728631 = 7092947) B7092947
theorem B6304841 : Blo 2299435 6304841 := bstep (se 2 (by rfl) ⟨2364315, by rfl⟩ : syracuseStep 6304841 = 4728631) B4728631
theorem B4203227 : Blo 2299435 4203227 := bstep (se 1 (by rfl) ⟨3152420, by rfl⟩ : syracuseStep 4203227 = 6304841) B6304841
theorem B2802151 : Blo 2299435 2802151 := bstep (se 1 (by rfl) ⟨2101613, by rfl⟩ : syracuseStep 2802151 = 4203227) B4203227
theorem B3736201 : Blo 2299435 3736201 := bstep (se 2 (by rfl) ⟨1401075, by rfl⟩ : syracuseStep 3736201 = 2802151) B2802151
theorem B4981601 : Blo 2299435 4981601 := bstep (se 2 (by rfl) ⟨1868100, by rfl⟩ : syracuseStep 4981601 = 3736201) B3736201
theorem B13284269 : Blo 2299435 13284269 := bstep (se 3 (by rfl) ⟨2490800, by rfl⟩ : syracuseStep 13284269 = 4981601) B4981601
theorem B8856179 : Blo 2299435 8856179 := bstep (se 1 (by rfl) ⟨6642134, by rfl⟩ : syracuseStep 8856179 = 13284269) B13284269
theorem B5904119 : Blo 2299435 5904119 := bstep (se 1 (by rfl) ⟨4428089, by rfl⟩ : syracuseStep 5904119 = 8856179) B8856179
theorem B3936079 : Blo 2299435 3936079 := bstep (se 1 (by rfl) ⟨2952059, by rfl⟩ : syracuseStep 3936079 = 5904119) B5904119
theorem B20992421 : Blo 2299435 20992421 := bstep (se 4 (by rfl) ⟨1968039, by rfl⟩ : syracuseStep 20992421 = 3936079) B3936079
theorem B13994947 : Blo 2299435 13994947 := bstep (se 1 (by rfl) ⟨10496210, by rfl⟩ : syracuseStep 13994947 = 20992421) B20992421
theorem B18659929 : Blo 2299435 18659929 := bstep (se 2 (by rfl) ⟨6997473, by rfl⟩ : syracuseStep 18659929 = 13994947) B13994947
theorem B24879905 : Blo 2299435 24879905 := bstep (se 2 (by rfl) ⟨9329964, by rfl⟩ : syracuseStep 24879905 = 18659929) B18659929
theorem B16586603 : Blo 2299435 16586603 := bstep (se 1 (by rfl) ⟨12439952, by rfl⟩ : syracuseStep 16586603 = 24879905) B24879905
theorem B11057735 : Blo 2299435 11057735 := bstep (se 1 (by rfl) ⟨8293301, by rfl⟩ : syracuseStep 11057735 = 16586603) B16586603
theorem B7371823 : Blo 2299435 7371823 := bstep (se 1 (by rfl) ⟨5528867, by rfl⟩ : syracuseStep 7371823 = 11057735) B11057735
theorem B9829097 : Blo 2299435 9829097 := bstep (se 2 (by rfl) ⟨3685911, by rfl⟩ : syracuseStep 9829097 = 7371823) B7371823
theorem B6552731 : Blo 2299435 6552731 := bstep (se 1 (by rfl) ⟨4914548, by rfl⟩ : syracuseStep 6552731 = 9829097) B9829097
theorem B4368487 : Blo 2299435 4368487 := bstep (se 1 (by rfl) ⟨3276365, by rfl⟩ : syracuseStep 4368487 = 6552731) B6552731
theorem B5824649 : Blo 2299435 5824649 := bstep (se 2 (by rfl) ⟨2184243, by rfl⟩ : syracuseStep 5824649 = 4368487) B4368487
theorem B3883099 : Blo 2299435 3883099 := bstep (se 1 (by rfl) ⟨2912324, by rfl⟩ : syracuseStep 3883099 = 5824649) B5824649
theorem B5177465 : Blo 2299435 5177465 := bstep (se 2 (by rfl) ⟨1941549, by rfl⟩ : syracuseStep 5177465 = 3883099) B3883099
theorem B3451643 : Blo 2299435 3451643 := bstep (se 1 (by rfl) ⟨2588732, by rfl⟩ : syracuseStep 3451643 = 5177465) B5177465
theorem B2301095 : Blo 2299435 2301095 := bstep (se 1 (by rfl) ⟨1725821, by rfl⟩ : syracuseStep 2301095 = 3451643) B3451643
theorem B2588737 : Blo 2299435 2588737 := bbase (se 2 (by rfl) ⟨970776, by rfl⟩ : syracuseStep 2588737 = 1941553) (by norm_num)
theorem B3451649 : Blo 2299435 3451649 := bstep (se 2 (by rfl) ⟨1294368, by rfl⟩ : syracuseStep 3451649 = 2588737) B2588737
theorem B2301099 : Blo 2299435 2301099 := bstep (se 1 (by rfl) ⟨1725824, by rfl⟩ : syracuseStep 2301099 = 3451649) B3451649
theorem B5824669 : Blo 2299435 5824669 := bbase (se 3 (by rfl) ⟨1092125, by rfl⟩ : syracuseStep 5824669 = 2184251) (by norm_num)
theorem B7766225 : Blo 2299435 7766225 := bstep (se 2 (by rfl) ⟨2912334, by rfl⟩ : syracuseStep 7766225 = 5824669) B5824669
theorem B5177483 : Blo 2299435 5177483 := bstep (se 1 (by rfl) ⟨3883112, by rfl⟩ : syracuseStep 5177483 = 7766225) B7766225
theorem B3451655 : Blo 2299435 3451655 := bstep (se 1 (by rfl) ⟨2588741, by rfl⟩ : syracuseStep 3451655 = 5177483) B5177483
theorem B2301103 : Blo 2299435 2301103 := bstep (se 1 (by rfl) ⟨1725827, by rfl⟩ : syracuseStep 2301103 = 3451655) B3451655
theorem B3451661 : Blo 2299435 3451661 := bbase (se 3 (by rfl) ⟨647186, by rfl⟩ : syracuseStep 3451661 = 1294373) (by norm_num)
theorem B2301107 : Blo 2299435 2301107 := bstep (se 1 (by rfl) ⟨1725830, by rfl⟩ : syracuseStep 2301107 = 3451661) B3451661
theorem B5177501 : Blo 2299435 5177501 := bbase (se 3 (by rfl) ⟨970781, by rfl⟩ : syracuseStep 5177501 = 1941563) (by norm_num)
theorem B3451667 : Blo 2299435 3451667 := bstep (se 1 (by rfl) ⟨2588750, by rfl⟩ : syracuseStep 3451667 = 5177501) B5177501
theorem B2301111 : Blo 2299435 2301111 := bstep (se 1 (by rfl) ⟨1725833, by rfl⟩ : syracuseStep 2301111 = 3451667) B3451667
theorem B3883133 : Blo 2299435 3883133 := bbase (se 3 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 3883133 = 1456175) (by norm_num)
theorem B2588755 : Blo 2299435 2588755 := bstep (se 1 (by rfl) ⟨1941566, by rfl⟩ : syracuseStep 2588755 = 3883133) B3883133
theorem B3451673 : Blo 2299435 3451673 := bstep (se 2 (by rfl) ⟨1294377, by rfl⟩ : syracuseStep 3451673 = 2588755) B2588755
theorem B2301115 : Blo 2299435 2301115 := bstep (se 1 (by rfl) ⟨1725836, by rfl⟩ : syracuseStep 2301115 = 3451673) B3451673
theorem B3498773 : Blo 2299435 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B9330061 : Blo 2299435 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B12440081 : Blo 2299435 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B8293387 : Blo 2299435 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B11057849 : Blo 2299435 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B7371899 : Blo 2299435 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B4914599 : Blo 2299435 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B13105597 : Blo 2299435 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B17474129 : Blo 2299435 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B11649419 : Blo 2299435 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B7766279 : Blo 2299435 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B5177519 : Blo 2299435 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B3451679 : Blo 2299435 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B2301119 : Blo 2299435 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B3451685 : Blo 2299435 3451685 := bbase (se 4 (by rfl) ⟨323595, by rfl⟩ : syracuseStep 3451685 = 647191) (by norm_num)
theorem B2301123 : Blo 2299435 2301123 := bstep (se 1 (by rfl) ⟨1725842, by rfl⟩ : syracuseStep 2301123 = 3451685) B3451685
theorem B2912365 : Blo 2299435 2912365 := bbase (se 3 (by rfl) ⟨546068, by rfl⟩ : syracuseStep 2912365 = 1092137) (by norm_num)
theorem B3883153 : Blo 2299435 3883153 := bstep (se 2 (by rfl) ⟨1456182, by rfl⟩ : syracuseStep 3883153 = 2912365) B2912365
theorem B5177537 : Blo 2299435 5177537 := bstep (se 2 (by rfl) ⟨1941576, by rfl⟩ : syracuseStep 5177537 = 3883153) B3883153
theorem B3451691 : Blo 2299435 3451691 := bstep (se 1 (by rfl) ⟨2588768, by rfl⟩ : syracuseStep 3451691 = 5177537) B5177537
theorem B2301127 : Blo 2299435 2301127 := bstep (se 1 (by rfl) ⟨1725845, by rfl⟩ : syracuseStep 2301127 = 3451691) B3451691
theorem B2588773 : Blo 2299435 2588773 := bbase (se 4 (by rfl) ⟨242697, by rfl⟩ : syracuseStep 2588773 = 485395) (by norm_num)
theorem B3451697 : Blo 2299435 3451697 := bstep (se 2 (by rfl) ⟨1294386, by rfl⟩ : syracuseStep 3451697 = 2588773) B2588773
theorem B2301131 : Blo 2299435 2301131 := bstep (se 1 (by rfl) ⟨1725848, by rfl⟩ : syracuseStep 2301131 = 3451697) B3451697
theorem B2457317 : Blo 2299435 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B6552845 : Blo 2299435 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B4368563 : Blo 2299435 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B2912375 : Blo 2299435 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B7766333 : Blo 2299435 7766333 := bstep (se 3 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 7766333 = 2912375) B2912375
theorem B5177555 : Blo 2299435 5177555 := bstep (se 1 (by rfl) ⟨3883166, by rfl⟩ : syracuseStep 5177555 = 7766333) B7766333
theorem B3451703 : Blo 2299435 3451703 := bstep (se 1 (by rfl) ⟨2588777, by rfl⟩ : syracuseStep 3451703 = 5177555) B5177555
theorem B2301135 : Blo 2299435 2301135 := bstep (se 1 (by rfl) ⟨1725851, by rfl⟩ : syracuseStep 2301135 = 3451703) B3451703
theorem B3451709 : Blo 2299435 3451709 := bbase (se 3 (by rfl) ⟨647195, by rfl⟩ : syracuseStep 3451709 = 1294391) (by norm_num)
theorem B2301139 : Blo 2299435 2301139 := bstep (se 1 (by rfl) ⟨1725854, by rfl⟩ : syracuseStep 2301139 = 3451709) B3451709
theorem B5177573 : Blo 2299435 5177573 := bbase (se 4 (by rfl) ⟨485397, by rfl⟩ : syracuseStep 5177573 = 970795) (by norm_num)
theorem B3451715 : Blo 2299435 3451715 := bstep (se 1 (by rfl) ⟨2588786, by rfl⟩ : syracuseStep 3451715 = 5177573) B5177573
theorem B2301143 : Blo 2299435 2301143 := bstep (se 1 (by rfl) ⟨1725857, by rfl⟩ : syracuseStep 2301143 = 3451715) B3451715
theorem B5824781 : Blo 2299435 5824781 := bbase (se 3 (by rfl) ⟨1092146, by rfl⟩ : syracuseStep 5824781 = 2184293) (by norm_num)
theorem B3883187 : Blo 2299435 3883187 := bstep (se 1 (by rfl) ⟨2912390, by rfl⟩ : syracuseStep 3883187 = 5824781) B5824781
theorem B2588791 : Blo 2299435 2588791 := bstep (se 1 (by rfl) ⟨1941593, by rfl⟩ : syracuseStep 2588791 = 3883187) B3883187
theorem B3451721 : Blo 2299435 3451721 := bstep (se 2 (by rfl) ⟨1294395, by rfl⟩ : syracuseStep 3451721 = 2588791) B2588791
theorem B2301147 : Blo 2299435 2301147 := bstep (se 1 (by rfl) ⟨1725860, by rfl⟩ : syracuseStep 2301147 = 3451721) B3451721
theorem B3276445 : Blo 2299435 3276445 := bbase (se 3 (by rfl) ⟨614333, by rfl⟩ : syracuseStep 3276445 = 1228667) (by norm_num)
theorem B4368593 : Blo 2299435 4368593 := bstep (se 2 (by rfl) ⟨1638222, by rfl⟩ : syracuseStep 4368593 = 3276445) B3276445
theorem B11649581 : Blo 2299435 11649581 := bstep (se 3 (by rfl) ⟨2184296, by rfl⟩ : syracuseStep 11649581 = 4368593) B4368593
theorem B7766387 : Blo 2299435 7766387 := bstep (se 1 (by rfl) ⟨5824790, by rfl⟩ : syracuseStep 7766387 = 11649581) B11649581
theorem B5177591 : Blo 2299435 5177591 := bstep (se 1 (by rfl) ⟨3883193, by rfl⟩ : syracuseStep 5177591 = 7766387) B7766387
theorem B3451727 : Blo 2299435 3451727 := bstep (se 1 (by rfl) ⟨2588795, by rfl⟩ : syracuseStep 3451727 = 5177591) B5177591
theorem B2301151 : Blo 2299435 2301151 := bstep (se 1 (by rfl) ⟨1725863, by rfl⟩ : syracuseStep 2301151 = 3451727) B3451727
theorem B3451733 : Blo 2299435 3451733 := bbase (se 9 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 3451733 = 20225) (by norm_num)
theorem B2301155 : Blo 2299435 2301155 := bstep (se 1 (by rfl) ⟨1725866, by rfl⟩ : syracuseStep 2301155 = 3451733) B3451733
theorem B4914685 : Blo 2299435 4914685 := bbase (se 3 (by rfl) ⟨921503, by rfl⟩ : syracuseStep 4914685 = 1843007) (by norm_num)
theorem B6552913 : Blo 2299435 6552913 := bstep (se 2 (by rfl) ⟨2457342, by rfl⟩ : syracuseStep 6552913 = 4914685) B4914685
theorem B8737217 : Blo 2299435 8737217 := bstep (se 2 (by rfl) ⟨3276456, by rfl⟩ : syracuseStep 8737217 = 6552913) B6552913
theorem B5824811 : Blo 2299435 5824811 := bstep (se 1 (by rfl) ⟨4368608, by rfl⟩ : syracuseStep 5824811 = 8737217) B8737217
theorem B3883207 : Blo 2299435 3883207 := bstep (se 1 (by rfl) ⟨2912405, by rfl⟩ : syracuseStep 3883207 = 5824811) B5824811
theorem B5177609 : Blo 2299435 5177609 := bstep (se 2 (by rfl) ⟨1941603, by rfl⟩ : syracuseStep 5177609 = 3883207) B3883207
theorem B3451739 : Blo 2299435 3451739 := bstep (se 1 (by rfl) ⟨2588804, by rfl⟩ : syracuseStep 3451739 = 5177609) B5177609
theorem B2301159 : Blo 2299435 2301159 := bstep (se 1 (by rfl) ⟨1725869, by rfl⟩ : syracuseStep 2301159 = 3451739) B3451739
theorem B2588809 : Blo 2299435 2588809 := bbase (se 2 (by rfl) ⟨970803, by rfl⟩ : syracuseStep 2588809 = 1941607) (by norm_num)
theorem B3451745 : Blo 2299435 3451745 := bstep (se 2 (by rfl) ⟨1294404, by rfl⟩ : syracuseStep 3451745 = 2588809) B2588809
theorem B2301163 : Blo 2299435 2301163 := bstep (se 1 (by rfl) ⟨1725872, by rfl⟩ : syracuseStep 2301163 = 3451745) B3451745
theorem B6642341 : Blo 2299435 6642341 := bbase (se 4 (by rfl) ⟨622719, by rfl⟩ : syracuseStep 6642341 = 1245439) (by norm_num)
theorem B4428227 : Blo 2299435 4428227 := bstep (se 1 (by rfl) ⟨3321170, by rfl⟩ : syracuseStep 4428227 = 6642341) B6642341
theorem B2952151 : Blo 2299435 2952151 := bstep (se 1 (by rfl) ⟨2214113, by rfl⟩ : syracuseStep 2952151 = 4428227) B4428227
theorem B62979221 : Blo 2299435 62979221 := bstep (se 6 (by rfl) ⟨1476075, by rfl⟩ : syracuseStep 62979221 = 2952151) B2952151
theorem B41986147 : Blo 2299435 41986147 := bstep (se 1 (by rfl) ⟨31489610, by rfl⟩ : syracuseStep 41986147 = 62979221) B62979221
theorem B55981529 : Blo 2299435 55981529 := bstep (se 2 (by rfl) ⟨20993073, by rfl⟩ : syracuseStep 55981529 = 41986147) B41986147
theorem B37321019 : Blo 2299435 37321019 := bstep (se 1 (by rfl) ⟨27990764, by rfl⟩ : syracuseStep 37321019 = 55981529) B55981529
theorem B24880679 : Blo 2299435 24880679 := bstep (se 1 (by rfl) ⟨18660509, by rfl⟩ : syracuseStep 24880679 = 37321019) B37321019
theorem B16587119 : Blo 2299435 16587119 := bstep (se 1 (by rfl) ⟨12440339, by rfl⟩ : syracuseStep 16587119 = 24880679) B24880679
theorem B44232317 : Blo 2299435 44232317 := bstep (se 3 (by rfl) ⟨8293559, by rfl⟩ : syracuseStep 44232317 = 16587119) B16587119
theorem B29488211 : Blo 2299435 29488211 := bstep (se 1 (by rfl) ⟨22116158, by rfl⟩ : syracuseStep 29488211 = 44232317) B44232317
theorem B19658807 : Blo 2299435 19658807 := bstep (se 1 (by rfl) ⟨14744105, by rfl⟩ : syracuseStep 19658807 = 29488211) B29488211
theorem B13105871 : Blo 2299435 13105871 := bstep (se 1 (by rfl) ⟨9829403, by rfl⟩ : syracuseStep 13105871 = 19658807) B19658807
theorem B8737247 : Blo 2299435 8737247 := bstep (se 1 (by rfl) ⟨6552935, by rfl⟩ : syracuseStep 8737247 = 13105871) B13105871
theorem B5824831 : Blo 2299435 5824831 := bstep (se 1 (by rfl) ⟨4368623, by rfl⟩ : syracuseStep 5824831 = 8737247) B8737247
theorem B7766441 : Blo 2299435 7766441 := bstep (se 2 (by rfl) ⟨2912415, by rfl⟩ : syracuseStep 7766441 = 5824831) B5824831
theorem B5177627 : Blo 2299435 5177627 := bstep (se 1 (by rfl) ⟨3883220, by rfl⟩ : syracuseStep 5177627 = 7766441) B7766441
theorem B3451751 : Blo 2299435 3451751 := bstep (se 1 (by rfl) ⟨2588813, by rfl⟩ : syracuseStep 3451751 = 5177627) B5177627
theorem B2301167 : Blo 2299435 2301167 := bstep (se 1 (by rfl) ⟨1725875, by rfl⟩ : syracuseStep 2301167 = 3451751) B3451751
theorem B3451757 : Blo 2299435 3451757 := bbase (se 3 (by rfl) ⟨647204, by rfl⟩ : syracuseStep 3451757 = 1294409) (by norm_num)
theorem B2301171 : Blo 2299435 2301171 := bstep (se 1 (by rfl) ⟨1725878, by rfl⟩ : syracuseStep 2301171 = 3451757) B3451757
theorem B5177645 : Blo 2299435 5177645 := bbase (se 3 (by rfl) ⟨970808, by rfl⟩ : syracuseStep 5177645 = 1941617) (by norm_num)
theorem B3451763 : Blo 2299435 3451763 := bstep (se 1 (by rfl) ⟨2588822, by rfl⟩ : syracuseStep 3451763 = 5177645) B5177645
theorem B2301175 : Blo 2299435 2301175 := bstep (se 1 (by rfl) ⟨1725881, by rfl⟩ : syracuseStep 2301175 = 3451763) B3451763
theorem B2332577 : Blo 2299435 2332577 := bbase (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) (by norm_num)
theorem B6220205 : Blo 2299435 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B4146803 : Blo 2299435 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B2764535 : Blo 2299435 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B7372093 : Blo 2299435 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B9829457 : Blo 2299435 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B6552971 : Blo 2299435 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B4368647 : Blo 2299435 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B2912431 : Blo 2299435 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B3883241 : Blo 2299435 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B2588827 : Blo 2299435 2588827 := bstep (se 1 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 2588827 = 3883241) B3883241
theorem B3451769 : Blo 2299435 3451769 := bstep (se 2 (by rfl) ⟨1294413, by rfl⟩ : syracuseStep 3451769 = 2588827) B2588827
theorem B2301179 : Blo 2299435 2301179 := bstep (se 1 (by rfl) ⟨1725884, by rfl⟩ : syracuseStep 2301179 = 3451769) B3451769
theorem B8406773 : Blo 2299435 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B5604515 : Blo 2299435 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B3736343 : Blo 2299435 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B2490895 : Blo 2299435 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B13284773 : Blo 2299435 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B8856515 : Blo 2299435 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B5904343 : Blo 2299435 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B31489829 : Blo 2299435 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B20993219 : Blo 2299435 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B13995479 : Blo 2299435 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B9330319 : Blo 2299435 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B49761701 : Blo 2299435 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B33174467 : Blo 2299435 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B22116311 : Blo 2299435 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B14744207 : Blo 2299435 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B39317885 : Blo 2299435 39317885 := bstep (se 3 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 39317885 = 14744207) B14744207
theorem B26211923 : Blo 2299435 26211923 := bstep (se 1 (by rfl) ⟨19658942, by rfl⟩ : syracuseStep 26211923 = 39317885) B39317885
theorem B17474615 : Blo 2299435 17474615 := bstep (se 1 (by rfl) ⟨13105961, by rfl⟩ : syracuseStep 17474615 = 26211923) B26211923
theorem B11649743 : Blo 2299435 11649743 := bstep (se 1 (by rfl) ⟨8737307, by rfl⟩ : syracuseStep 11649743 = 17474615) B17474615
theorem B7766495 : Blo 2299435 7766495 := bstep (se 1 (by rfl) ⟨5824871, by rfl⟩ : syracuseStep 7766495 = 11649743) B11649743
theorem B5177663 : Blo 2299435 5177663 := bstep (se 1 (by rfl) ⟨3883247, by rfl⟩ : syracuseStep 5177663 = 7766495) B7766495
theorem B3451775 : Blo 2299435 3451775 := bstep (se 1 (by rfl) ⟨2588831, by rfl⟩ : syracuseStep 3451775 = 5177663) B5177663
theorem B2301183 : Blo 2299435 2301183 := bstep (se 1 (by rfl) ⟨1725887, by rfl⟩ : syracuseStep 2301183 = 3451775) B3451775
theorem B3451781 : Blo 2299435 3451781 := bbase (se 4 (by rfl) ⟨323604, by rfl⟩ : syracuseStep 3451781 = 647209) (by norm_num)
theorem B2301187 : Blo 2299435 2301187 := bstep (se 1 (by rfl) ⟨1725890, by rfl⟩ : syracuseStep 2301187 = 3451781) B3451781
theorem B3883261 : Blo 2299435 3883261 := bbase (se 3 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 3883261 = 1456223) (by norm_num)
theorem B5177681 : Blo 2299435 5177681 := bstep (se 2 (by rfl) ⟨1941630, by rfl⟩ : syracuseStep 5177681 = 3883261) B3883261
theorem B3451787 : Blo 2299435 3451787 := bstep (se 1 (by rfl) ⟨2588840, by rfl⟩ : syracuseStep 3451787 = 5177681) B5177681
theorem B2301191 : Blo 2299435 2301191 := bstep (se 1 (by rfl) ⟨1725893, by rfl⟩ : syracuseStep 2301191 = 3451787) B3451787
theorem B2588845 : Blo 2299435 2588845 := bbase (se 3 (by rfl) ⟨485408, by rfl⟩ : syracuseStep 2588845 = 970817) (by norm_num)
theorem B3451793 : Blo 2299435 3451793 := bstep (se 2 (by rfl) ⟨1294422, by rfl⟩ : syracuseStep 3451793 = 2588845) B2588845
theorem B2301195 : Blo 2299435 2301195 := bstep (se 1 (by rfl) ⟨1725896, by rfl⟩ : syracuseStep 2301195 = 3451793) B3451793
theorem B7766549 : Blo 2299435 7766549 := bbase (se 6 (by rfl) ⟨182028, by rfl⟩ : syracuseStep 7766549 = 364057) (by norm_num)
theorem B5177699 : Blo 2299435 5177699 := bstep (se 1 (by rfl) ⟨3883274, by rfl⟩ : syracuseStep 5177699 = 7766549) B7766549
theorem B3451799 : Blo 2299435 3451799 := bstep (se 1 (by rfl) ⟨2588849, by rfl⟩ : syracuseStep 3451799 = 5177699) B5177699
theorem B2301199 : Blo 2299435 2301199 := bstep (se 1 (by rfl) ⟨1725899, by rfl⟩ : syracuseStep 2301199 = 3451799) B3451799
theorem B3451805 : Blo 2299435 3451805 := bbase (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) (by norm_num)
theorem B2301203 : Blo 2299435 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B5177717 : Blo 2299435 5177717 := bbase (se 5 (by rfl) ⟨242705, by rfl⟩ : syracuseStep 5177717 = 485411) (by norm_num)
theorem B3451811 : Blo 2299435 3451811 := bstep (se 1 (by rfl) ⟨2588858, by rfl⟩ : syracuseStep 3451811 = 5177717) B5177717
theorem B2301207 : Blo 2299435 2301207 := bstep (se 1 (by rfl) ⟨1725905, by rfl⟩ : syracuseStep 2301207 = 3451811) B3451811
theorem B2764573 : Blo 2299435 2764573 := bbase (se 3 (by rfl) ⟨518357, by rfl⟩ : syracuseStep 2764573 = 1036715) (by norm_num)
theorem B14744389 : Blo 2299435 14744389 := bstep (se 4 (by rfl) ⟨1382286, by rfl⟩ : syracuseStep 14744389 = 2764573) B2764573
theorem B19659185 : Blo 2299435 19659185 := bstep (se 2 (by rfl) ⟨7372194, by rfl⟩ : syracuseStep 19659185 = 14744389) B14744389
theorem B13106123 : Blo 2299435 13106123 := bstep (se 1 (by rfl) ⟨9829592, by rfl⟩ : syracuseStep 13106123 = 19659185) B19659185
theorem B8737415 : Blo 2299435 8737415 := bstep (se 1 (by rfl) ⟨6553061, by rfl⟩ : syracuseStep 8737415 = 13106123) B13106123
theorem B5824943 : Blo 2299435 5824943 := bstep (se 1 (by rfl) ⟨4368707, by rfl⟩ : syracuseStep 5824943 = 8737415) B8737415
theorem B3883295 : Blo 2299435 3883295 := bstep (se 1 (by rfl) ⟨2912471, by rfl⟩ : syracuseStep 3883295 = 5824943) B5824943
theorem B2588863 : Blo 2299435 2588863 := bstep (se 1 (by rfl) ⟨1941647, by rfl⟩ : syracuseStep 2588863 = 3883295) B3883295
theorem B3451817 : Blo 2299435 3451817 := bstep (se 2 (by rfl) ⟨1294431, by rfl⟩ : syracuseStep 3451817 = 2588863) B2588863
theorem B2301211 : Blo 2299435 2301211 := bstep (se 1 (by rfl) ⟨1725908, by rfl⟩ : syracuseStep 2301211 = 3451817) B3451817
theorem B8737429 : Blo 2299435 8737429 := bbase (se 6 (by rfl) ⟨204783, by rfl⟩ : syracuseStep 8737429 = 409567) (by norm_num)
theorem B11649905 : Blo 2299435 11649905 := bstep (se 2 (by rfl) ⟨4368714, by rfl⟩ : syracuseStep 11649905 = 8737429) B8737429
theorem B7766603 : Blo 2299435 7766603 := bstep (se 1 (by rfl) ⟨5824952, by rfl⟩ : syracuseStep 7766603 = 11649905) B11649905
theorem B5177735 : Blo 2299435 5177735 := bstep (se 1 (by rfl) ⟨3883301, by rfl⟩ : syracuseStep 5177735 = 7766603) B7766603
theorem B3451823 : Blo 2299435 3451823 := bstep (se 1 (by rfl) ⟨2588867, by rfl⟩ : syracuseStep 3451823 = 5177735) B5177735
theorem B2301215 : Blo 2299435 2301215 := bstep (se 1 (by rfl) ⟨1725911, by rfl⟩ : syracuseStep 2301215 = 3451823) B3451823
theorem B3451829 : Blo 2299435 3451829 := bbase (se 5 (by rfl) ⟨161804, by rfl⟩ : syracuseStep 3451829 = 323609) (by norm_num)
theorem B2301219 : Blo 2299435 2301219 := bstep (se 1 (by rfl) ⟨1725914, by rfl⟩ : syracuseStep 2301219 = 3451829) B3451829
theorem B5824973 : Blo 2299435 5824973 := bbase (se 3 (by rfl) ⟨1092182, by rfl⟩ : syracuseStep 5824973 = 2184365) (by norm_num)
theorem B3883315 : Blo 2299435 3883315 := bstep (se 1 (by rfl) ⟨2912486, by rfl⟩ : syracuseStep 3883315 = 5824973) B5824973
theorem B5177753 : Blo 2299435 5177753 := bstep (se 2 (by rfl) ⟨1941657, by rfl⟩ : syracuseStep 5177753 = 3883315) B3883315
theorem B3451835 : Blo 2299435 3451835 := bstep (se 1 (by rfl) ⟨2588876, by rfl⟩ : syracuseStep 3451835 = 5177753) B5177753
theorem B2301223 : Blo 2299435 2301223 := bstep (se 1 (by rfl) ⟨1725917, by rfl⟩ : syracuseStep 2301223 = 3451835) B3451835
theorem B2588881 : Blo 2299435 2588881 := bbase (se 2 (by rfl) ⟨970830, by rfl⟩ : syracuseStep 2588881 = 1941661) (by norm_num)
theorem B3451841 : Blo 2299435 3451841 := bstep (se 2 (by rfl) ⟨1294440, by rfl⟩ : syracuseStep 3451841 = 2588881) B2588881
theorem B2301227 : Blo 2299435 2301227 := bstep (se 1 (by rfl) ⟨1725920, by rfl⟩ : syracuseStep 2301227 = 3451841) B3451841
theorem B11058389 : Blo 2299435 11058389 := bbase (se 7 (by rfl) ⟨129590, by rfl⟩ : syracuseStep 11058389 = 259181) (by norm_num)
theorem B7372259 : Blo 2299435 7372259 := bstep (se 1 (by rfl) ⟨5529194, by rfl⟩ : syracuseStep 7372259 = 11058389) B11058389
theorem B4914839 : Blo 2299435 4914839 := bstep (se 1 (by rfl) ⟨3686129, by rfl⟩ : syracuseStep 4914839 = 7372259) B7372259
theorem B3276559 : Blo 2299435 3276559 := bstep (se 1 (by rfl) ⟨2457419, by rfl⟩ : syracuseStep 3276559 = 4914839) B4914839
theorem B4368745 : Blo 2299435 4368745 := bstep (se 2 (by rfl) ⟨1638279, by rfl⟩ : syracuseStep 4368745 = 3276559) B3276559
theorem B5824993 : Blo 2299435 5824993 := bstep (se 2 (by rfl) ⟨2184372, by rfl⟩ : syracuseStep 5824993 = 4368745) B4368745
theorem B7766657 : Blo 2299435 7766657 := bstep (se 2 (by rfl) ⟨2912496, by rfl⟩ : syracuseStep 7766657 = 5824993) B5824993
theorem B5177771 : Blo 2299435 5177771 := bstep (se 1 (by rfl) ⟨3883328, by rfl⟩ : syracuseStep 5177771 = 7766657) B7766657
theorem B3451847 : Blo 2299435 3451847 := bstep (se 1 (by rfl) ⟨2588885, by rfl⟩ : syracuseStep 3451847 = 5177771) B5177771
theorem B2301231 : Blo 2299435 2301231 := bstep (se 1 (by rfl) ⟨1725923, by rfl⟩ : syracuseStep 2301231 = 3451847) B3451847
theorem B3451853 : Blo 2299435 3451853 := bbase (se 3 (by rfl) ⟨647222, by rfl⟩ : syracuseStep 3451853 = 1294445) (by norm_num)
theorem B2301235 : Blo 2299435 2301235 := bstep (se 1 (by rfl) ⟨1725926, by rfl⟩ : syracuseStep 2301235 = 3451853) B3451853
theorem B5177789 : Blo 2299435 5177789 := bbase (se 3 (by rfl) ⟨970835, by rfl⟩ : syracuseStep 5177789 = 1941671) (by norm_num)
theorem B3451859 : Blo 2299435 3451859 := bstep (se 1 (by rfl) ⟨2588894, by rfl⟩ : syracuseStep 3451859 = 5177789) B5177789
theorem B2301239 : Blo 2299435 2301239 := bstep (se 1 (by rfl) ⟨1725929, by rfl⟩ : syracuseStep 2301239 = 3451859) B3451859
theorem B3883349 : Blo 2299435 3883349 := bbase (se 10 (by rfl) ⟨5688, by rfl⟩ : syracuseStep 3883349 = 11377) (by norm_num)
theorem B2588899 : Blo 2299435 2588899 := bstep (se 1 (by rfl) ⟨1941674, by rfl⟩ : syracuseStep 2588899 = 3883349) B3883349
theorem B3451865 : Blo 2299435 3451865 := bstep (se 2 (by rfl) ⟨1294449, by rfl⟩ : syracuseStep 3451865 = 2588899) B2588899
theorem B2301243 : Blo 2299435 2301243 := bstep (se 1 (by rfl) ⟨1725932, by rfl⟩ : syracuseStep 2301243 = 3451865) B3451865
theorem B7372309 : Blo 2299435 7372309 := bbase (se 6 (by rfl) ⟨172788, by rfl⟩ : syracuseStep 7372309 = 345577) (by norm_num)
theorem B9829745 : Blo 2299435 9829745 := bstep (se 2 (by rfl) ⟨3686154, by rfl⟩ : syracuseStep 9829745 = 7372309) B7372309
theorem B6553163 : Blo 2299435 6553163 := bstep (se 1 (by rfl) ⟨4914872, by rfl⟩ : syracuseStep 6553163 = 9829745) B9829745
theorem B17475101 : Blo 2299435 17475101 := bstep (se 3 (by rfl) ⟨3276581, by rfl⟩ : syracuseStep 17475101 = 6553163) B6553163
theorem B11650067 : Blo 2299435 11650067 := bstep (se 1 (by rfl) ⟨8737550, by rfl⟩ : syracuseStep 11650067 = 17475101) B17475101
theorem B7766711 : Blo 2299435 7766711 := bstep (se 1 (by rfl) ⟨5825033, by rfl⟩ : syracuseStep 7766711 = 11650067) B11650067
theorem B5177807 : Blo 2299435 5177807 := bstep (se 1 (by rfl) ⟨3883355, by rfl⟩ : syracuseStep 5177807 = 7766711) B7766711
theorem B3451871 : Blo 2299435 3451871 := bstep (se 1 (by rfl) ⟨2588903, by rfl⟩ : syracuseStep 3451871 = 5177807) B5177807
theorem B2301247 : Blo 2299435 2301247 := bstep (se 1 (by rfl) ⟨1725935, by rfl⟩ : syracuseStep 2301247 = 3451871) B3451871
theorem B3451877 : Blo 2299435 3451877 := bbase (se 4 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 3451877 = 647227) (by norm_num)
theorem B2301251 : Blo 2299435 2301251 := bstep (se 1 (by rfl) ⟨1725938, by rfl⟩ : syracuseStep 2301251 = 3451877) B3451877
theorem B9829781 : Blo 2299435 9829781 := bbase (se 6 (by rfl) ⟨230385, by rfl⟩ : syracuseStep 9829781 = 460771) (by norm_num)
theorem B6553187 : Blo 2299435 6553187 := bstep (se 1 (by rfl) ⟨4914890, by rfl⟩ : syracuseStep 6553187 = 9829781) B9829781
theorem B4368791 : Blo 2299435 4368791 := bstep (se 1 (by rfl) ⟨3276593, by rfl⟩ : syracuseStep 4368791 = 6553187) B6553187
theorem B2912527 : Blo 2299435 2912527 := bstep (se 1 (by rfl) ⟨2184395, by rfl⟩ : syracuseStep 2912527 = 4368791) B4368791
theorem B3883369 : Blo 2299435 3883369 := bstep (se 2 (by rfl) ⟨1456263, by rfl⟩ : syracuseStep 3883369 = 2912527) B2912527
theorem B5177825 : Blo 2299435 5177825 := bstep (se 2 (by rfl) ⟨1941684, by rfl⟩ : syracuseStep 5177825 = 3883369) B3883369
theorem B3451883 : Blo 2299435 3451883 := bstep (se 1 (by rfl) ⟨2588912, by rfl⟩ : syracuseStep 3451883 = 5177825) B5177825
theorem B2301255 : Blo 2299435 2301255 := bstep (se 1 (by rfl) ⟨1725941, by rfl⟩ : syracuseStep 2301255 = 3451883) B3451883
theorem B2588917 : Blo 2299435 2588917 := bbase (se 5 (by rfl) ⟨121355, by rfl⟩ : syracuseStep 2588917 = 242711) (by norm_num)
theorem B3451889 : Blo 2299435 3451889 := bstep (se 2 (by rfl) ⟨1294458, by rfl⟩ : syracuseStep 3451889 = 2588917) B2588917
theorem B2301259 : Blo 2299435 2301259 := bstep (se 1 (by rfl) ⟨1725944, by rfl⟩ : syracuseStep 2301259 = 3451889) B3451889
theorem B2912537 : Blo 2299435 2912537 := bbase (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) (by norm_num)
theorem B7766765 : Blo 2299435 7766765 := bstep (se 3 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 7766765 = 2912537) B2912537
theorem B5177843 : Blo 2299435 5177843 := bstep (se 1 (by rfl) ⟨3883382, by rfl⟩ : syracuseStep 5177843 = 7766765) B7766765
theorem B3451895 : Blo 2299435 3451895 := bstep (se 1 (by rfl) ⟨2588921, by rfl⟩ : syracuseStep 3451895 = 5177843) B5177843
theorem B2301263 : Blo 2299435 2301263 := bstep (se 1 (by rfl) ⟨1725947, by rfl⟩ : syracuseStep 2301263 = 3451895) B3451895
theorem B3451901 : Blo 2299435 3451901 := bbase (se 3 (by rfl) ⟨647231, by rfl⟩ : syracuseStep 3451901 = 1294463) (by norm_num)
theorem B2301267 : Blo 2299435 2301267 := bstep (se 1 (by rfl) ⟨1725950, by rfl⟩ : syracuseStep 2301267 = 3451901) B3451901
theorem B5177861 : Blo 2299435 5177861 := bbase (se 4 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 5177861 = 970849) (by norm_num)
theorem B3451907 : Blo 2299435 3451907 := bstep (se 1 (by rfl) ⟨2588930, by rfl⟩ : syracuseStep 3451907 = 5177861) B5177861
theorem B2301271 : Blo 2299435 2301271 := bstep (se 1 (by rfl) ⟨1725953, by rfl⟩ : syracuseStep 2301271 = 3451907) B3451907
theorem B4368829 : Blo 2299435 4368829 := bbase (se 3 (by rfl) ⟨819155, by rfl⟩ : syracuseStep 4368829 = 1638311) (by norm_num)
theorem B5825105 : Blo 2299435 5825105 := bstep (se 2 (by rfl) ⟨2184414, by rfl⟩ : syracuseStep 5825105 = 4368829) B4368829
theorem B3883403 : Blo 2299435 3883403 := bstep (se 1 (by rfl) ⟨2912552, by rfl⟩ : syracuseStep 3883403 = 5825105) B5825105
theorem B2588935 : Blo 2299435 2588935 := bstep (se 1 (by rfl) ⟨1941701, by rfl⟩ : syracuseStep 2588935 = 3883403) B3883403
theorem B3451913 : Blo 2299435 3451913 := bstep (se 2 (by rfl) ⟨1294467, by rfl⟩ : syracuseStep 3451913 = 2588935) B2588935
theorem B2301275 : Blo 2299435 2301275 := bstep (se 1 (by rfl) ⟨1725956, by rfl⟩ : syracuseStep 2301275 = 3451913) B3451913
theorem B11650229 : Blo 2299435 11650229 := bbase (se 5 (by rfl) ⟨546104, by rfl⟩ : syracuseStep 11650229 = 1092209) (by norm_num)
theorem B7766819 : Blo 2299435 7766819 := bstep (se 1 (by rfl) ⟨5825114, by rfl⟩ : syracuseStep 7766819 = 11650229) B11650229
theorem B5177879 : Blo 2299435 5177879 := bstep (se 1 (by rfl) ⟨3883409, by rfl⟩ : syracuseStep 5177879 = 7766819) B7766819
theorem B3451919 : Blo 2299435 3451919 := bstep (se 1 (by rfl) ⟨2588939, by rfl⟩ : syracuseStep 3451919 = 5177879) B5177879
theorem B2301279 : Blo 2299435 2301279 := bstep (se 1 (by rfl) ⟨1725959, by rfl⟩ : syracuseStep 2301279 = 3451919) B3451919
theorem B3451925 : Blo 2299435 3451925 := bbase (se 6 (by rfl) ⟨80904, by rfl⟩ : syracuseStep 3451925 = 161809) (by norm_num)
theorem B2301283 : Blo 2299435 2301283 := bstep (se 1 (by rfl) ⟨1725962, by rfl⟩ : syracuseStep 2301283 = 3451925) B3451925
theorem B6305365 : Blo 2299435 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B8407153 : Blo 2299435 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B11209537 : Blo 2299435 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B14946049 : Blo 2299435 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B19928065 : Blo 2299435 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B26570753 : Blo 2299435 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B17713835 : Blo 2299435 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B11809223 : Blo 2299435 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B7872815 : Blo 2299435 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B5248543 : Blo 2299435 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B6998057 : Blo 2299435 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B4665371 : Blo 2299435 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B12440989 : Blo 2299435 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B16587985 : Blo 2299435 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B22117313 : Blo 2299435 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B14744875 : Blo 2299435 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B19659833 : Blo 2299435 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B13106555 : Blo 2299435 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B8737703 : Blo 2299435 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B5825135 : Blo 2299435 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B3883423 : Blo 2299435 3883423 := bstep (se 1 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 3883423 = 5825135) B5825135
theorem B5177897 : Blo 2299435 5177897 := bstep (se 2 (by rfl) ⟨1941711, by rfl⟩ : syracuseStep 5177897 = 3883423) B3883423
theorem B3451931 : Blo 2299435 3451931 := bstep (se 1 (by rfl) ⟨2588948, by rfl⟩ : syracuseStep 3451931 = 5177897) B5177897
theorem B2301287 : Blo 2299435 2301287 := bstep (se 1 (by rfl) ⟨1725965, by rfl⟩ : syracuseStep 2301287 = 3451931) B3451931
theorem B2588953 : Blo 2299435 2588953 := bbase (se 2 (by rfl) ⟨970857, by rfl⟩ : syracuseStep 2588953 = 1941715) (by norm_num)
theorem B3451937 : Blo 2299435 3451937 := bstep (se 2 (by rfl) ⟨1294476, by rfl⟩ : syracuseStep 3451937 = 2588953) B2588953
theorem B2301291 : Blo 2299435 2301291 := bstep (se 1 (by rfl) ⟨1725968, by rfl⟩ : syracuseStep 2301291 = 3451937) B3451937
theorem B8737733 : Blo 2299435 8737733 := bbase (se 4 (by rfl) ⟨819162, by rfl⟩ : syracuseStep 8737733 = 1638325) (by norm_num)
theorem B5825155 : Blo 2299435 5825155 := bstep (se 1 (by rfl) ⟨4368866, by rfl⟩ : syracuseStep 5825155 = 8737733) B8737733
theorem B7766873 : Blo 2299435 7766873 := bstep (se 2 (by rfl) ⟨2912577, by rfl⟩ : syracuseStep 7766873 = 5825155) B5825155
theorem B5177915 : Blo 2299435 5177915 := bstep (se 1 (by rfl) ⟨3883436, by rfl⟩ : syracuseStep 5177915 = 7766873) B7766873
theorem B3451943 : Blo 2299435 3451943 := bstep (se 1 (by rfl) ⟨2588957, by rfl⟩ : syracuseStep 3451943 = 5177915) B5177915
theorem B2301295 : Blo 2299435 2301295 := bstep (se 1 (by rfl) ⟨1725971, by rfl⟩ : syracuseStep 2301295 = 3451943) B3451943
theorem B3451949 : Blo 2299435 3451949 := bbase (se 3 (by rfl) ⟨647240, by rfl⟩ : syracuseStep 3451949 = 1294481) (by norm_num)
theorem B2301299 : Blo 2299435 2301299 := bstep (se 1 (by rfl) ⟨1725974, by rfl⟩ : syracuseStep 2301299 = 3451949) B3451949
theorem B5177933 : Blo 2299435 5177933 := bbase (se 3 (by rfl) ⟨970862, by rfl⟩ : syracuseStep 5177933 = 1941725) (by norm_num)
theorem B3451955 : Blo 2299435 3451955 := bstep (se 1 (by rfl) ⟨2588966, by rfl⟩ : syracuseStep 3451955 = 5177933) B5177933
theorem B2301303 : Blo 2299435 2301303 := bstep (se 1 (by rfl) ⟨1725977, by rfl⟩ : syracuseStep 2301303 = 3451955) B3451955
theorem B2912593 : Blo 2299435 2912593 := bbase (se 2 (by rfl) ⟨1092222, by rfl⟩ : syracuseStep 2912593 = 2184445) (by norm_num)
theorem B3883457 : Blo 2299435 3883457 := bstep (se 2 (by rfl) ⟨1456296, by rfl⟩ : syracuseStep 3883457 = 2912593) B2912593
theorem B2588971 : Blo 2299435 2588971 := bstep (se 1 (by rfl) ⟨1941728, by rfl⟩ : syracuseStep 2588971 = 3883457) B3883457
theorem B3451961 : Blo 2299435 3451961 := bstep (se 2 (by rfl) ⟨1294485, by rfl⟩ : syracuseStep 3451961 = 2588971) B2588971
theorem B2301307 : Blo 2299435 2301307 := bstep (se 1 (by rfl) ⟨1725980, by rfl⟩ : syracuseStep 2301307 = 3451961) B3451961
theorem B2764693 : Blo 2299435 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B3686257 : Blo 2299435 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B4915009 : Blo 2299435 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B26213381 : Blo 2299435 26213381 := bstep (se 4 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 26213381 = 4915009) B4915009
theorem B17475587 : Blo 2299435 17475587 := bstep (se 1 (by rfl) ⟨13106690, by rfl⟩ : syracuseStep 17475587 = 26213381) B26213381
theorem B11650391 : Blo 2299435 11650391 := bstep (se 1 (by rfl) ⟨8737793, by rfl⟩ : syracuseStep 11650391 = 17475587) B17475587
theorem B7766927 : Blo 2299435 7766927 := bstep (se 1 (by rfl) ⟨5825195, by rfl⟩ : syracuseStep 7766927 = 11650391) B11650391
theorem B5177951 : Blo 2299435 5177951 := bstep (se 1 (by rfl) ⟨3883463, by rfl⟩ : syracuseStep 5177951 = 7766927) B7766927
theorem B3451967 : Blo 2299435 3451967 := bstep (se 1 (by rfl) ⟨2588975, by rfl⟩ : syracuseStep 3451967 = 5177951) B5177951
theorem B2301311 : Blo 2299435 2301311 := bstep (se 1 (by rfl) ⟨1725983, by rfl⟩ : syracuseStep 2301311 = 3451967) B3451967
theorem B3451973 : Blo 2299435 3451973 := bbase (se 4 (by rfl) ⟨323622, by rfl⟩ : syracuseStep 3451973 = 647245) (by norm_num)
theorem B2301315 : Blo 2299435 2301315 := bstep (se 1 (by rfl) ⟨1725986, by rfl⟩ : syracuseStep 2301315 = 3451973) B3451973
theorem B3883477 : Blo 2299435 3883477 := bbase (se 7 (by rfl) ⟨45509, by rfl⟩ : syracuseStep 3883477 = 91019) (by norm_num)
theorem B5177969 : Blo 2299435 5177969 := bstep (se 2 (by rfl) ⟨1941738, by rfl⟩ : syracuseStep 5177969 = 3883477) B3883477
theorem B3451979 : Blo 2299435 3451979 := bstep (se 1 (by rfl) ⟨2588984, by rfl⟩ : syracuseStep 3451979 = 5177969) B5177969
theorem B2301319 : Blo 2299435 2301319 := bstep (se 1 (by rfl) ⟨1725989, by rfl⟩ : syracuseStep 2301319 = 3451979) B3451979
theorem B2588989 : Blo 2299435 2588989 := bbase (se 3 (by rfl) ⟨485435, by rfl⟩ : syracuseStep 2588989 = 970871) (by norm_num)
theorem B3451985 : Blo 2299435 3451985 := bstep (se 2 (by rfl) ⟨1294494, by rfl⟩ : syracuseStep 3451985 = 2588989) B2588989
theorem B2301323 : Blo 2299435 2301323 := bstep (se 1 (by rfl) ⟨1725992, by rfl⟩ : syracuseStep 2301323 = 3451985) B3451985
theorem B7766981 : Blo 2299435 7766981 := bbase (se 4 (by rfl) ⟨728154, by rfl⟩ : syracuseStep 7766981 = 1456309) (by norm_num)
theorem B5177987 : Blo 2299435 5177987 := bstep (se 1 (by rfl) ⟨3883490, by rfl⟩ : syracuseStep 5177987 = 7766981) B7766981
theorem B3451991 : Blo 2299435 3451991 := bstep (se 1 (by rfl) ⟨2588993, by rfl⟩ : syracuseStep 3451991 = 5177987) B5177987
theorem B2301327 : Blo 2299435 2301327 := bstep (se 1 (by rfl) ⟨1725995, by rfl⟩ : syracuseStep 2301327 = 3451991) B3451991
theorem B3451997 : Blo 2299435 3451997 := bbase (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) (by norm_num)
theorem B2301331 : Blo 2299435 2301331 := bstep (se 1 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 2301331 = 3451997) B3451997
theorem B5178005 : Blo 2299435 5178005 := bbase (se 6 (by rfl) ⟨121359, by rfl⟩ : syracuseStep 5178005 = 242719) (by norm_num)
theorem B3452003 : Blo 2299435 3452003 := bstep (se 1 (by rfl) ⟨2589002, by rfl⟩ : syracuseStep 3452003 = 5178005) B5178005
theorem B2301335 : Blo 2299435 2301335 := bstep (se 1 (by rfl) ⟨1726001, by rfl⟩ : syracuseStep 2301335 = 3452003) B3452003
theorem B11809493 : Blo 2299435 11809493 := bbase (se 7 (by rfl) ⟨138392, by rfl⟩ : syracuseStep 11809493 = 276785) (by norm_num)
theorem B7872995 : Blo 2299435 7872995 := bstep (se 1 (by rfl) ⟨5904746, by rfl⟩ : syracuseStep 7872995 = 11809493) B11809493
theorem B20994653 : Blo 2299435 20994653 := bstep (se 3 (by rfl) ⟨3936497, by rfl⟩ : syracuseStep 20994653 = 7872995) B7872995
theorem B13996435 : Blo 2299435 13996435 := bstep (se 1 (by rfl) ⟨10497326, by rfl⟩ : syracuseStep 13996435 = 20994653) B20994653
theorem B18661913 : Blo 2299435 18661913 := bstep (se 2 (by rfl) ⟨6998217, by rfl⟩ : syracuseStep 18661913 = 13996435) B13996435
theorem B12441275 : Blo 2299435 12441275 := bstep (se 1 (by rfl) ⟨9330956, by rfl⟩ : syracuseStep 12441275 = 18661913) B18661913
theorem B8294183 : Blo 2299435 8294183 := bstep (se 1 (by rfl) ⟨6220637, by rfl⟩ : syracuseStep 8294183 = 12441275) B12441275
theorem B5529455 : Blo 2299435 5529455 := bstep (se 1 (by rfl) ⟨4147091, by rfl⟩ : syracuseStep 5529455 = 8294183) B8294183
theorem B3686303 : Blo 2299435 3686303 := bstep (se 1 (by rfl) ⟨2764727, by rfl⟩ : syracuseStep 3686303 = 5529455) B5529455
theorem B2457535 : Blo 2299435 2457535 := bstep (se 1 (by rfl) ⟨1843151, by rfl⟩ : syracuseStep 2457535 = 3686303) B3686303
theorem B3276713 : Blo 2299435 3276713 := bstep (se 2 (by rfl) ⟨1228767, by rfl⟩ : syracuseStep 3276713 = 2457535) B2457535
theorem B8737901 : Blo 2299435 8737901 := bstep (se 3 (by rfl) ⟨1638356, by rfl⟩ : syracuseStep 8737901 = 3276713) B3276713
theorem B5825267 : Blo 2299435 5825267 := bstep (se 1 (by rfl) ⟨4368950, by rfl⟩ : syracuseStep 5825267 = 8737901) B8737901
theorem B3883511 : Blo 2299435 3883511 := bstep (se 1 (by rfl) ⟨2912633, by rfl⟩ : syracuseStep 3883511 = 5825267) B5825267
theorem B2589007 : Blo 2299435 2589007 := bstep (se 1 (by rfl) ⟨1941755, by rfl⟩ : syracuseStep 2589007 = 3883511) B3883511
theorem B3452009 : Blo 2299435 3452009 := bstep (se 2 (by rfl) ⟨1294503, by rfl⟩ : syracuseStep 3452009 = 2589007) B2589007
theorem B2301339 : Blo 2299435 2301339 := bstep (se 1 (by rfl) ⟨1726004, by rfl⟩ : syracuseStep 2301339 = 3452009) B3452009
theorem B4665485 : Blo 2299435 4665485 := bbase (se 3 (by rfl) ⟨874778, by rfl⟩ : syracuseStep 4665485 = 1749557) (by norm_num)
theorem B3110323 : Blo 2299435 3110323 := bstep (se 1 (by rfl) ⟨2332742, by rfl⟩ : syracuseStep 3110323 = 4665485) B4665485
theorem B4147097 : Blo 2299435 4147097 := bstep (se 2 (by rfl) ⟨1555161, by rfl⟩ : syracuseStep 4147097 = 3110323) B3110323
theorem B11058925 : Blo 2299435 11058925 := bstep (se 3 (by rfl) ⟨2073548, by rfl⟩ : syracuseStep 11058925 = 4147097) B4147097
theorem B14745233 : Blo 2299435 14745233 := bstep (se 2 (by rfl) ⟨5529462, by rfl⟩ : syracuseStep 14745233 = 11058925) B11058925
theorem B9830155 : Blo 2299435 9830155 := bstep (se 1 (by rfl) ⟨7372616, by rfl⟩ : syracuseStep 9830155 = 14745233) B14745233
theorem B13106873 : Blo 2299435 13106873 := bstep (se 2 (by rfl) ⟨4915077, by rfl⟩ : syracuseStep 13106873 = 9830155) B9830155
theorem B8737915 : Blo 2299435 8737915 := bstep (se 1 (by rfl) ⟨6553436, by rfl⟩ : syracuseStep 8737915 = 13106873) B13106873
theorem B11650553 : Blo 2299435 11650553 := bstep (se 2 (by rfl) ⟨4368957, by rfl⟩ : syracuseStep 11650553 = 8737915) B8737915
theorem B7767035 : Blo 2299435 7767035 := bstep (se 1 (by rfl) ⟨5825276, by rfl⟩ : syracuseStep 7767035 = 11650553) B11650553
theorem B5178023 : Blo 2299435 5178023 := bstep (se 1 (by rfl) ⟨3883517, by rfl⟩ : syracuseStep 5178023 = 7767035) B7767035
theorem B3452015 : Blo 2299435 3452015 := bstep (se 1 (by rfl) ⟨2589011, by rfl⟩ : syracuseStep 3452015 = 5178023) B5178023
theorem B2301343 : Blo 2299435 2301343 := bstep (se 1 (by rfl) ⟨1726007, by rfl⟩ : syracuseStep 2301343 = 3452015) B3452015
theorem B3452021 : Blo 2299435 3452021 := bbase (se 5 (by rfl) ⟨161813, by rfl⟩ : syracuseStep 3452021 = 323627) (by norm_num)
theorem B2301347 : Blo 2299435 2301347 := bstep (se 1 (by rfl) ⟨1726010, by rfl⟩ : syracuseStep 2301347 = 3452021) B3452021
theorem B4368973 : Blo 2299435 4368973 := bbase (se 3 (by rfl) ⟨819182, by rfl⟩ : syracuseStep 4368973 = 1638365) (by norm_num)
theorem B5825297 : Blo 2299435 5825297 := bstep (se 2 (by rfl) ⟨2184486, by rfl⟩ : syracuseStep 5825297 = 4368973) B4368973
theorem B3883531 : Blo 2299435 3883531 := bstep (se 1 (by rfl) ⟨2912648, by rfl⟩ : syracuseStep 3883531 = 5825297) B5825297
theorem B5178041 : Blo 2299435 5178041 := bstep (se 2 (by rfl) ⟨1941765, by rfl⟩ : syracuseStep 5178041 = 3883531) B3883531
theorem B3452027 : Blo 2299435 3452027 := bstep (se 1 (by rfl) ⟨2589020, by rfl⟩ : syracuseStep 3452027 = 5178041) B5178041
theorem B2301351 : Blo 2299435 2301351 := bstep (se 1 (by rfl) ⟨1726013, by rfl⟩ : syracuseStep 2301351 = 3452027) B3452027
theorem B2589025 : Blo 2299435 2589025 := bbase (se 2 (by rfl) ⟨970884, by rfl⟩ : syracuseStep 2589025 = 1941769) (by norm_num)
theorem B3452033 : Blo 2299435 3452033 := bstep (se 2 (by rfl) ⟨1294512, by rfl⟩ : syracuseStep 3452033 = 2589025) B2589025
theorem B2301355 : Blo 2299435 2301355 := bstep (se 1 (by rfl) ⟨1726016, by rfl⟩ : syracuseStep 2301355 = 3452033) B3452033
theorem B5825317 : Blo 2299435 5825317 := bbase (se 4 (by rfl) ⟨546123, by rfl⟩ : syracuseStep 5825317 = 1092247) (by norm_num)
theorem B7767089 : Blo 2299435 7767089 := bstep (se 2 (by rfl) ⟨2912658, by rfl⟩ : syracuseStep 7767089 = 5825317) B5825317
theorem B5178059 : Blo 2299435 5178059 := bstep (se 1 (by rfl) ⟨3883544, by rfl⟩ : syracuseStep 5178059 = 7767089) B7767089
theorem B3452039 : Blo 2299435 3452039 := bstep (se 1 (by rfl) ⟨2589029, by rfl⟩ : syracuseStep 3452039 = 5178059) B5178059
theorem B2301359 : Blo 2299435 2301359 := bstep (se 1 (by rfl) ⟨1726019, by rfl⟩ : syracuseStep 2301359 = 3452039) B3452039
theorem B3452045 : Blo 2299435 3452045 := bbase (se 3 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 3452045 = 1294517) (by norm_num)
theorem B2301363 : Blo 2299435 2301363 := bstep (se 1 (by rfl) ⟨1726022, by rfl⟩ : syracuseStep 2301363 = 3452045) B3452045
theorem B5178077 : Blo 2299435 5178077 := bbase (se 3 (by rfl) ⟨970889, by rfl⟩ : syracuseStep 5178077 = 1941779) (by norm_num)
theorem B3452051 : Blo 2299435 3452051 := bstep (se 1 (by rfl) ⟨2589038, by rfl⟩ : syracuseStep 3452051 = 5178077) B5178077
theorem B2301367 : Blo 2299435 2301367 := bstep (se 1 (by rfl) ⟨1726025, by rfl⟩ : syracuseStep 2301367 = 3452051) B3452051
theorem B3883565 : Blo 2299435 3883565 := bbase (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) (by norm_num)
theorem B2589043 : Blo 2299435 2589043 := bstep (se 1 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 2589043 = 3883565) B3883565
theorem B3452057 : Blo 2299435 3452057 := bstep (se 2 (by rfl) ⟨1294521, by rfl⟩ : syracuseStep 3452057 = 2589043) B2589043
theorem B2301371 : Blo 2299435 2301371 := bstep (se 1 (by rfl) ⟨1726028, by rfl⟩ : syracuseStep 2301371 = 3452057) B3452057
theorem B3936557 : Blo 2299435 3936557 := bbase (se 3 (by rfl) ⟨738104, by rfl⟩ : syracuseStep 3936557 = 1476209) (by norm_num)
theorem B10497485 : Blo 2299435 10497485 := bstep (se 3 (by rfl) ⟨1968278, by rfl⟩ : syracuseStep 10497485 = 3936557) B3936557
theorem B27993293 : Blo 2299435 27993293 := bstep (se 3 (by rfl) ⟨5248742, by rfl⟩ : syracuseStep 27993293 = 10497485) B10497485
theorem B18662195 : Blo 2299435 18662195 := bstep (se 1 (by rfl) ⟨13996646, by rfl⟩ : syracuseStep 18662195 = 27993293) B27993293
theorem B49765853 : Blo 2299435 49765853 := bstep (se 3 (by rfl) ⟨9331097, by rfl⟩ : syracuseStep 49765853 = 18662195) B18662195
theorem B33177235 : Blo 2299435 33177235 := bstep (se 1 (by rfl) ⟨24882926, by rfl⟩ : syracuseStep 33177235 = 49765853) B49765853
theorem B44236313 : Blo 2299435 44236313 := bstep (se 2 (by rfl) ⟨16588617, by rfl⟩ : syracuseStep 44236313 = 33177235) B33177235
theorem B29490875 : Blo 2299435 29490875 := bstep (se 1 (by rfl) ⟨22118156, by rfl⟩ : syracuseStep 29490875 = 44236313) B44236313
theorem B19660583 : Blo 2299435 19660583 := bstep (se 1 (by rfl) ⟨14745437, by rfl⟩ : syracuseStep 19660583 = 29490875) B29490875
theorem B13107055 : Blo 2299435 13107055 := bstep (se 1 (by rfl) ⟨9830291, by rfl⟩ : syracuseStep 13107055 = 19660583) B19660583
theorem B17476073 : Blo 2299435 17476073 := bstep (se 2 (by rfl) ⟨6553527, by rfl⟩ : syracuseStep 17476073 = 13107055) B13107055
theorem B11650715 : Blo 2299435 11650715 := bstep (se 1 (by rfl) ⟨8738036, by rfl⟩ : syracuseStep 11650715 = 17476073) B17476073
theorem B7767143 : Blo 2299435 7767143 := bstep (se 1 (by rfl) ⟨5825357, by rfl⟩ : syracuseStep 7767143 = 11650715) B11650715
theorem B5178095 : Blo 2299435 5178095 := bstep (se 1 (by rfl) ⟨3883571, by rfl⟩ : syracuseStep 5178095 = 7767143) B7767143
theorem B3452063 : Blo 2299435 3452063 := bstep (se 1 (by rfl) ⟨2589047, by rfl⟩ : syracuseStep 3452063 = 5178095) B5178095
theorem B2301375 : Blo 2299435 2301375 := bstep (se 1 (by rfl) ⟨1726031, by rfl⟩ : syracuseStep 2301375 = 3452063) B3452063
theorem B3452069 : Blo 2299435 3452069 := bbase (se 4 (by rfl) ⟨323631, by rfl⟩ : syracuseStep 3452069 = 647263) (by norm_num)
theorem B2301379 : Blo 2299435 2301379 := bstep (se 1 (by rfl) ⟨1726034, by rfl⟩ : syracuseStep 2301379 = 3452069) B3452069
theorem B2912689 : Blo 2299435 2912689 := bbase (se 2 (by rfl) ⟨1092258, by rfl⟩ : syracuseStep 2912689 = 2184517) (by norm_num)
theorem B3883585 : Blo 2299435 3883585 := bstep (se 2 (by rfl) ⟨1456344, by rfl⟩ : syracuseStep 3883585 = 2912689) B2912689
theorem B5178113 : Blo 2299435 5178113 := bstep (se 2 (by rfl) ⟨1941792, by rfl⟩ : syracuseStep 5178113 = 3883585) B3883585
theorem B3452075 : Blo 2299435 3452075 := bstep (se 1 (by rfl) ⟨2589056, by rfl⟩ : syracuseStep 3452075 = 5178113) B5178113
theorem B2301383 : Blo 2299435 2301383 := bstep (se 1 (by rfl) ⟨1726037, by rfl⟩ : syracuseStep 2301383 = 3452075) B3452075
theorem B2589061 : Blo 2299435 2589061 := bbase (se 4 (by rfl) ⟨242724, by rfl⟩ : syracuseStep 2589061 = 485449) (by norm_num)
theorem B3452081 : Blo 2299435 3452081 := bstep (se 2 (by rfl) ⟨1294530, by rfl⟩ : syracuseStep 3452081 = 2589061) B2589061
theorem B2301387 : Blo 2299435 2301387 := bstep (se 1 (by rfl) ⟨1726040, by rfl⟩ : syracuseStep 2301387 = 3452081) B3452081
theorem B4915181 : Blo 2299435 4915181 := bbase (se 3 (by rfl) ⟨921596, by rfl⟩ : syracuseStep 4915181 = 1843193) (by norm_num)
theorem B3276787 : Blo 2299435 3276787 := bstep (se 1 (by rfl) ⟨2457590, by rfl⟩ : syracuseStep 3276787 = 4915181) B4915181
theorem B4369049 : Blo 2299435 4369049 := bstep (se 2 (by rfl) ⟨1638393, by rfl⟩ : syracuseStep 4369049 = 3276787) B3276787
theorem B2912699 : Blo 2299435 2912699 := bstep (se 1 (by rfl) ⟨2184524, by rfl⟩ : syracuseStep 2912699 = 4369049) B4369049
theorem B7767197 : Blo 2299435 7767197 := bstep (se 3 (by rfl) ⟨1456349, by rfl⟩ : syracuseStep 7767197 = 2912699) B2912699
theorem B5178131 : Blo 2299435 5178131 := bstep (se 1 (by rfl) ⟨3883598, by rfl⟩ : syracuseStep 5178131 = 7767197) B7767197
theorem B3452087 : Blo 2299435 3452087 := bstep (se 1 (by rfl) ⟨2589065, by rfl⟩ : syracuseStep 3452087 = 5178131) B5178131
theorem B2301391 : Blo 2299435 2301391 := bstep (se 1 (by rfl) ⟨1726043, by rfl⟩ : syracuseStep 2301391 = 3452087) B3452087
theorem B3452093 : Blo 2299435 3452093 := bbase (se 3 (by rfl) ⟨647267, by rfl⟩ : syracuseStep 3452093 = 1294535) (by norm_num)
theorem B2301395 : Blo 2299435 2301395 := bstep (se 1 (by rfl) ⟨1726046, by rfl⟩ : syracuseStep 2301395 = 3452093) B3452093
theorem B5178149 : Blo 2299435 5178149 := bbase (se 4 (by rfl) ⟨485451, by rfl⟩ : syracuseStep 5178149 = 970903) (by norm_num)
theorem B3452099 : Blo 2299435 3452099 := bstep (se 1 (by rfl) ⟨2589074, by rfl⟩ : syracuseStep 3452099 = 5178149) B5178149
theorem B2301399 : Blo 2299435 2301399 := bstep (se 1 (by rfl) ⟨1726049, by rfl⟩ : syracuseStep 2301399 = 3452099) B3452099
theorem B5825429 : Blo 2299435 5825429 := bbase (se 6 (by rfl) ⟨136533, by rfl⟩ : syracuseStep 5825429 = 273067) (by norm_num)
theorem B3883619 : Blo 2299435 3883619 := bstep (se 1 (by rfl) ⟨2912714, by rfl⟩ : syracuseStep 3883619 = 5825429) B5825429
theorem B2589079 : Blo 2299435 2589079 := bstep (se 1 (by rfl) ⟨1941809, by rfl⟩ : syracuseStep 2589079 = 3883619) B3883619
theorem B3452105 : Blo 2299435 3452105 := bstep (se 2 (by rfl) ⟨1294539, by rfl⟩ : syracuseStep 3452105 = 2589079) B2589079
theorem B2301403 : Blo 2299435 2301403 := bstep (se 1 (by rfl) ⟨1726052, by rfl⟩ : syracuseStep 2301403 = 3452105) B3452105
theorem B4147213 : Blo 2299435 4147213 := bbase (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) (by norm_num)
theorem B5529617 : Blo 2299435 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B3686411 : Blo 2299435 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B9830429 : Blo 2299435 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B6553619 : Blo 2299435 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B4369079 : Blo 2299435 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B11650877 : Blo 2299435 11650877 := bstep (se 3 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 11650877 = 4369079) B4369079
theorem B7767251 : Blo 2299435 7767251 := bstep (se 1 (by rfl) ⟨5825438, by rfl⟩ : syracuseStep 7767251 = 11650877) B11650877
theorem B5178167 : Blo 2299435 5178167 := bstep (se 1 (by rfl) ⟨3883625, by rfl⟩ : syracuseStep 5178167 = 7767251) B7767251
theorem B3452111 : Blo 2299435 3452111 := bstep (se 1 (by rfl) ⟨2589083, by rfl⟩ : syracuseStep 3452111 = 5178167) B5178167
theorem B2301407 : Blo 2299435 2301407 := bstep (se 1 (by rfl) ⟨1726055, by rfl⟩ : syracuseStep 2301407 = 3452111) B3452111
theorem B3452117 : Blo 2299435 3452117 := bbase (se 7 (by rfl) ⟨40454, by rfl⟩ : syracuseStep 3452117 = 80909) (by norm_num)
theorem B2301411 : Blo 2299435 2301411 := bstep (se 1 (by rfl) ⟨1726058, by rfl⟩ : syracuseStep 2301411 = 3452117) B3452117
theorem B3276821 : Blo 2299435 3276821 := bbase (se 6 (by rfl) ⟨76800, by rfl⟩ : syracuseStep 3276821 = 153601) (by norm_num)
theorem B8738189 : Blo 2299435 8738189 := bstep (se 3 (by rfl) ⟨1638410, by rfl⟩ : syracuseStep 8738189 = 3276821) B3276821
theorem B5825459 : Blo 2299435 5825459 := bstep (se 1 (by rfl) ⟨4369094, by rfl⟩ : syracuseStep 5825459 = 8738189) B8738189
theorem B3883639 : Blo 2299435 3883639 := bstep (se 1 (by rfl) ⟨2912729, by rfl⟩ : syracuseStep 3883639 = 5825459) B5825459
theorem B5178185 : Blo 2299435 5178185 := bstep (se 2 (by rfl) ⟨1941819, by rfl⟩ : syracuseStep 5178185 = 3883639) B3883639
theorem B3452123 : Blo 2299435 3452123 := bstep (se 1 (by rfl) ⟨2589092, by rfl⟩ : syracuseStep 3452123 = 5178185) B5178185
theorem B2301415 : Blo 2299435 2301415 := bstep (se 1 (by rfl) ⟨1726061, by rfl⟩ : syracuseStep 2301415 = 3452123) B3452123
theorem B2589097 : Blo 2299435 2589097 := bbase (se 2 (by rfl) ⟨970911, by rfl⟩ : syracuseStep 2589097 = 1941823) (by norm_num)
theorem B3452129 : Blo 2299435 3452129 := bstep (se 2 (by rfl) ⟨1294548, by rfl⟩ : syracuseStep 3452129 = 2589097) B2589097
theorem B2301419 : Blo 2299435 2301419 := bstep (se 1 (by rfl) ⟨1726064, by rfl⟩ : syracuseStep 2301419 = 3452129) B3452129
theorem B12611477 : Blo 2299435 12611477 := bbase (se 6 (by rfl) ⟨295581, by rfl⟩ : syracuseStep 12611477 = 591163) (by norm_num)
theorem B8407651 : Blo 2299435 8407651 := bstep (se 1 (by rfl) ⟨6305738, by rfl⟩ : syracuseStep 8407651 = 12611477) B12611477
theorem B11210201 : Blo 2299435 11210201 := bstep (se 2 (by rfl) ⟨4203825, by rfl⟩ : syracuseStep 11210201 = 8407651) B8407651
theorem B7473467 : Blo 2299435 7473467 := bstep (se 1 (by rfl) ⟨5605100, by rfl⟩ : syracuseStep 7473467 = 11210201) B11210201
theorem B4982311 : Blo 2299435 4982311 := bstep (se 1 (by rfl) ⟨3736733, by rfl⟩ : syracuseStep 4982311 = 7473467) B7473467
theorem B6643081 : Blo 2299435 6643081 := bstep (se 2 (by rfl) ⟨2491155, by rfl⟩ : syracuseStep 6643081 = 4982311) B4982311
theorem B8857441 : Blo 2299435 8857441 := bstep (se 2 (by rfl) ⟨3321540, by rfl⟩ : syracuseStep 8857441 = 6643081) B6643081
theorem B11809921 : Blo 2299435 11809921 := bstep (se 2 (by rfl) ⟨4428720, by rfl⟩ : syracuseStep 11809921 = 8857441) B8857441
theorem B15746561 : Blo 2299435 15746561 := bstep (se 2 (by rfl) ⟨5904960, by rfl⟩ : syracuseStep 15746561 = 11809921) B11809921
theorem B10497707 : Blo 2299435 10497707 := bstep (se 1 (by rfl) ⟨7873280, by rfl⟩ : syracuseStep 10497707 = 15746561) B15746561
theorem B6998471 : Blo 2299435 6998471 := bstep (se 1 (by rfl) ⟨5248853, by rfl⟩ : syracuseStep 6998471 = 10497707) B10497707
theorem B4665647 : Blo 2299435 4665647 := bstep (se 1 (by rfl) ⟨3499235, by rfl⟩ : syracuseStep 4665647 = 6998471) B6998471
theorem B12441725 : Blo 2299435 12441725 := bstep (se 3 (by rfl) ⟨2332823, by rfl⟩ : syracuseStep 12441725 = 4665647) B4665647
theorem B8294483 : Blo 2299435 8294483 := bstep (se 1 (by rfl) ⟨6220862, by rfl⟩ : syracuseStep 8294483 = 12441725) B12441725
theorem B5529655 : Blo 2299435 5529655 := bstep (se 1 (by rfl) ⟨4147241, by rfl⟩ : syracuseStep 5529655 = 8294483) B8294483
theorem B7372873 : Blo 2299435 7372873 := bstep (se 2 (by rfl) ⟨2764827, by rfl⟩ : syracuseStep 7372873 = 5529655) B5529655
theorem B9830497 : Blo 2299435 9830497 := bstep (se 2 (by rfl) ⟨3686436, by rfl⟩ : syracuseStep 9830497 = 7372873) B7372873
theorem B13107329 : Blo 2299435 13107329 := bstep (se 2 (by rfl) ⟨4915248, by rfl⟩ : syracuseStep 13107329 = 9830497) B9830497
theorem B8738219 : Blo 2299435 8738219 := bstep (se 1 (by rfl) ⟨6553664, by rfl⟩ : syracuseStep 8738219 = 13107329) B13107329
theorem B5825479 : Blo 2299435 5825479 := bstep (se 1 (by rfl) ⟨4369109, by rfl⟩ : syracuseStep 5825479 = 8738219) B8738219
theorem B7767305 : Blo 2299435 7767305 := bstep (se 2 (by rfl) ⟨2912739, by rfl⟩ : syracuseStep 7767305 = 5825479) B5825479
theorem B5178203 : Blo 2299435 5178203 := bstep (se 1 (by rfl) ⟨3883652, by rfl⟩ : syracuseStep 5178203 = 7767305) B7767305
theorem B3452135 : Blo 2299435 3452135 := bstep (se 1 (by rfl) ⟨2589101, by rfl⟩ : syracuseStep 3452135 = 5178203) B5178203
theorem B2301423 : Blo 2299435 2301423 := bstep (se 1 (by rfl) ⟨1726067, by rfl⟩ : syracuseStep 2301423 = 3452135) B3452135
theorem B3452141 : Blo 2299435 3452141 := bbase (se 3 (by rfl) ⟨647276, by rfl⟩ : syracuseStep 3452141 = 1294553) (by norm_num)
theorem B2301427 : Blo 2299435 2301427 := bstep (se 1 (by rfl) ⟨1726070, by rfl⟩ : syracuseStep 2301427 = 3452141) B3452141
theorem B5178221 : Blo 2299435 5178221 := bbase (se 3 (by rfl) ⟨970916, by rfl⟩ : syracuseStep 5178221 = 1941833) (by norm_num)
theorem B3452147 : Blo 2299435 3452147 := bstep (se 1 (by rfl) ⟨2589110, by rfl⟩ : syracuseStep 3452147 = 5178221) B5178221
theorem B2301431 : Blo 2299435 2301431 := bstep (se 1 (by rfl) ⟨1726073, by rfl⟩ : syracuseStep 2301431 = 3452147) B3452147
theorem B4369133 : Blo 2299435 4369133 := bbase (se 3 (by rfl) ⟨819212, by rfl⟩ : syracuseStep 4369133 = 1638425) (by norm_num)
theorem B2912755 : Blo 2299435 2912755 := bstep (se 1 (by rfl) ⟨2184566, by rfl⟩ : syracuseStep 2912755 = 4369133) B4369133
theorem B3883673 : Blo 2299435 3883673 := bstep (se 2 (by rfl) ⟨1456377, by rfl⟩ : syracuseStep 3883673 = 2912755) B2912755
theorem B2589115 : Blo 2299435 2589115 := bstep (se 1 (by rfl) ⟨1941836, by rfl⟩ : syracuseStep 2589115 = 3883673) B3883673
theorem B3452153 : Blo 2299435 3452153 := bstep (se 2 (by rfl) ⟨1294557, by rfl⟩ : syracuseStep 3452153 = 2589115) B2589115
theorem B2301435 : Blo 2299435 2301435 := bstep (se 1 (by rfl) ⟨1726076, by rfl⟩ : syracuseStep 2301435 = 3452153) B3452153
theorem C0 (j : ℕ) (h1 : 574858 ≤ j) (h2 : j ≤ 575358) : Blo 2299435 (4 * j + 3) := by
  interval_cases j
  · exact B2299435
  · exact B2299439
  · exact B2299443
  · exact B2299447
  · exact B2299451
  · exact B2299455
  · exact B2299459
  · exact B2299463
  · exact B2299467
  · exact B2299471
  · exact B2299475
  · exact B2299479
  · exact B2299483
  · exact B2299487
  · exact B2299491
  · exact B2299495
  · exact B2299499
  · exact B2299503
  · exact B2299507
  · exact B2299511
  · exact B2299515
  · exact B2299519
  · exact B2299523
  · exact B2299527
  · exact B2299531
  · exact B2299535
  · exact B2299539
  · exact B2299543
  · exact B2299547
  · exact B2299551
  · exact B2299555
  · exact B2299559
  · exact B2299563
  · exact B2299567
  · exact B2299571
  · exact B2299575
  · exact B2299579
  · exact B2299583
  · exact B2299587
  · exact B2299591
  · exact B2299595
  · exact B2299599
  · exact B2299603
  · exact B2299607
  · exact B2299611
  · exact B2299615
  · exact B2299619
  · exact B2299623
  · exact B2299627
  · exact B2299631
  · exact B2299635
  · exact B2299639
  · exact B2299643
  · exact B2299647
  · exact B2299651
  · exact B2299655
  · exact B2299659
  · exact B2299663
  · exact B2299667
  · exact B2299671
  · exact B2299675
  · exact B2299679
  · exact B2299683
  · exact B2299687
  · exact B2299691
  · exact B2299695
  · exact B2299699
  · exact B2299703
  · exact B2299707
  · exact B2299711
  · exact B2299715
  · exact B2299719
  · exact B2299723
  · exact B2299727
  · exact B2299731
  · exact B2299735
  · exact B2299739
  · exact B2299743
  · exact B2299747
  · exact B2299751
  · exact B2299755
  · exact B2299759
  · exact B2299763
  · exact B2299767
  · exact B2299771
  · exact B2299775
  · exact B2299779
  · exact B2299783
  · exact B2299787
  · exact B2299791
  · exact B2299795
  · exact B2299799
  · exact B2299803
  · exact B2299807
  · exact B2299811
  · exact B2299815
  · exact B2299819
  · exact B2299823
  · exact B2299827
  · exact B2299831
  · exact B2299835
  · exact B2299839
  · exact B2299843
  · exact B2299847
  · exact B2299851
  · exact B2299855
  · exact B2299859
  · exact B2299863
  · exact B2299867
  · exact B2299871
  · exact B2299875
  · exact B2299879
  · exact B2299883
  · exact B2299887
  · exact B2299891
  · exact B2299895
  · exact B2299899
  · exact B2299903
  · exact B2299907
  · exact B2299911
  · exact B2299915
  · exact B2299919
  · exact B2299923
  · exact B2299927
  · exact B2299931
  · exact B2299935
  · exact B2299939
  · exact B2299943
  · exact B2299947
  · exact B2299951
  · exact B2299955
  · exact B2299959
  · exact B2299963
  · exact B2299967
  · exact B2299971
  · exact B2299975
  · exact B2299979
  · exact B2299983
  · exact B2299987
  · exact B2299991
  · exact B2299995
  · exact B2299999
  · exact B2300003
  · exact B2300007
  · exact B2300011
  · exact B2300015
  · exact B2300019
  · exact B2300023
  · exact B2300027
  · exact B2300031
  · exact B2300035
  · exact B2300039
  · exact B2300043
  · exact B2300047
  · exact B2300051
  · exact B2300055
  · exact B2300059
  · exact B2300063
  · exact B2300067
  · exact B2300071
  · exact B2300075
  · exact B2300079
  · exact B2300083
  · exact B2300087
  · exact B2300091
  · exact B2300095
  · exact B2300099
  · exact B2300103
  · exact B2300107
  · exact B2300111
  · exact B2300115
  · exact B2300119
  · exact B2300123
  · exact B2300127
  · exact B2300131
  · exact B2300135
  · exact B2300139
  · exact B2300143
  · exact B2300147
  · exact B2300151
  · exact B2300155
  · exact B2300159
  · exact B2300163
  · exact B2300167
  · exact B2300171
  · exact B2300175
  · exact B2300179
  · exact B2300183
  · exact B2300187
  · exact B2300191
  · exact B2300195
  · exact B2300199
  · exact B2300203
  · exact B2300207
  · exact B2300211
  · exact B2300215
  · exact B2300219
  · exact B2300223
  · exact B2300227
  · exact B2300231
  · exact B2300235
  · exact B2300239
  · exact B2300243
  · exact B2300247
  · exact B2300251
  · exact B2300255
  · exact B2300259
  · exact B2300263
  · exact B2300267
  · exact B2300271
  · exact B2300275
  · exact B2300279
  · exact B2300283
  · exact B2300287
  · exact B2300291
  · exact B2300295
  · exact B2300299
  · exact B2300303
  · exact B2300307
  · exact B2300311
  · exact B2300315
  · exact B2300319
  · exact B2300323
  · exact B2300327
  · exact B2300331
  · exact B2300335
  · exact B2300339
  · exact B2300343
  · exact B2300347
  · exact B2300351
  · exact B2300355
  · exact B2300359
  · exact B2300363
  · exact B2300367
  · exact B2300371
  · exact B2300375
  · exact B2300379
  · exact B2300383
  · exact B2300387
  · exact B2300391
  · exact B2300395
  · exact B2300399
  · exact B2300403
  · exact B2300407
  · exact B2300411
  · exact B2300415
  · exact B2300419
  · exact B2300423
  · exact B2300427
  · exact B2300431
  · exact B2300435
  · exact B2300439
  · exact B2300443
  · exact B2300447
  · exact B2300451
  · exact B2300455
  · exact B2300459
  · exact B2300463
  · exact B2300467
  · exact B2300471
  · exact B2300475
  · exact B2300479
  · exact B2300483
  · exact B2300487
  · exact B2300491
  · exact B2300495
  · exact B2300499
  · exact B2300503
  · exact B2300507
  · exact B2300511
  · exact B2300515
  · exact B2300519
  · exact B2300523
  · exact B2300527
  · exact B2300531
  · exact B2300535
  · exact B2300539
  · exact B2300543
  · exact B2300547
  · exact B2300551
  · exact B2300555
  · exact B2300559
  · exact B2300563
  · exact B2300567
  · exact B2300571
  · exact B2300575
  · exact B2300579
  · exact B2300583
  · exact B2300587
  · exact B2300591
  · exact B2300595
  · exact B2300599
  · exact B2300603
  · exact B2300607
  · exact B2300611
  · exact B2300615
  · exact B2300619
  · exact B2300623
  · exact B2300627
  · exact B2300631
  · exact B2300635
  · exact B2300639
  · exact B2300643
  · exact B2300647
  · exact B2300651
  · exact B2300655
  · exact B2300659
  · exact B2300663
  · exact B2300667
  · exact B2300671
  · exact B2300675
  · exact B2300679
  · exact B2300683
  · exact B2300687
  · exact B2300691
  · exact B2300695
  · exact B2300699
  · exact B2300703
  · exact B2300707
  · exact B2300711
  · exact B2300715
  · exact B2300719
  · exact B2300723
  · exact B2300727
  · exact B2300731
  · exact B2300735
  · exact B2300739
  · exact B2300743
  · exact B2300747
  · exact B2300751
  · exact B2300755
  · exact B2300759
  · exact B2300763
  · exact B2300767
  · exact B2300771
  · exact B2300775
  · exact B2300779
  · exact B2300783
  · exact B2300787
  · exact B2300791
  · exact B2300795
  · exact B2300799
  · exact B2300803
  · exact B2300807
  · exact B2300811
  · exact B2300815
  · exact B2300819
  · exact B2300823
  · exact B2300827
  · exact B2300831
  · exact B2300835
  · exact B2300839
  · exact B2300843
  · exact B2300847
  · exact B2300851
  · exact B2300855
  · exact B2300859
  · exact B2300863
  · exact B2300867
  · exact B2300871
  · exact B2300875
  · exact B2300879
  · exact B2300883
  · exact B2300887
  · exact B2300891
  · exact B2300895
  · exact B2300899
  · exact B2300903
  · exact B2300907
  · exact B2300911
  · exact B2300915
  · exact B2300919
  · exact B2300923
  · exact B2300927
  · exact B2300931
  · exact B2300935
  · exact B2300939
  · exact B2300943
  · exact B2300947
  · exact B2300951
  · exact B2300955
  · exact B2300959
  · exact B2300963
  · exact B2300967
  · exact B2300971
  · exact B2300975
  · exact B2300979
  · exact B2300983
  · exact B2300987
  · exact B2300991
  · exact B2300995
  · exact B2300999
  · exact B2301003
  · exact B2301007
  · exact B2301011
  · exact B2301015
  · exact B2301019
  · exact B2301023
  · exact B2301027
  · exact B2301031
  · exact B2301035
  · exact B2301039
  · exact B2301043
  · exact B2301047
  · exact B2301051
  · exact B2301055
  · exact B2301059
  · exact B2301063
  · exact B2301067
  · exact B2301071
  · exact B2301075
  · exact B2301079
  · exact B2301083
  · exact B2301087
  · exact B2301091
  · exact B2301095
  · exact B2301099
  · exact B2301103
  · exact B2301107
  · exact B2301111
  · exact B2301115
  · exact B2301119
  · exact B2301123
  · exact B2301127
  · exact B2301131
  · exact B2301135
  · exact B2301139
  · exact B2301143
  · exact B2301147
  · exact B2301151
  · exact B2301155
  · exact B2301159
  · exact B2301163
  · exact B2301167
  · exact B2301171
  · exact B2301175
  · exact B2301179
  · exact B2301183
  · exact B2301187
  · exact B2301191
  · exact B2301195
  · exact B2301199
  · exact B2301203
  · exact B2301207
  · exact B2301211
  · exact B2301215
  · exact B2301219
  · exact B2301223
  · exact B2301227
  · exact B2301231
  · exact B2301235
  · exact B2301239
  · exact B2301243
  · exact B2301247
  · exact B2301251
  · exact B2301255
  · exact B2301259
  · exact B2301263
  · exact B2301267
  · exact B2301271
  · exact B2301275
  · exact B2301279
  · exact B2301283
  · exact B2301287
  · exact B2301291
  · exact B2301295
  · exact B2301299
  · exact B2301303
  · exact B2301307
  · exact B2301311
  · exact B2301315
  · exact B2301319
  · exact B2301323
  · exact B2301327
  · exact B2301331
  · exact B2301335
  · exact B2301339
  · exact B2301343
  · exact B2301347
  · exact B2301351
  · exact B2301355
  · exact B2301359
  · exact B2301363
  · exact B2301367
  · exact B2301371
  · exact B2301375
  · exact B2301379
  · exact B2301383
  · exact B2301387
  · exact B2301391
  · exact B2301395
  · exact B2301399
  · exact B2301403
  · exact B2301407
  · exact B2301411
  · exact B2301415
  · exact B2301419
  · exact B2301423
  · exact B2301427
  · exact B2301431
  · exact B2301435
theorem solution (m : ℕ) (hlo : 2299435 ≤ m) (hhi : m ≤ 2301435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 574858 ≤ j := by omega
    have hj2 : j ≤ 575358 := by omega
    have hb : Blo 2299435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
